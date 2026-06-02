#!/usr/bin/env python3
import argparse
import gzip
import json
import math
import os
import socket
import subprocess
import ssl
import sys
import threading
import time
from collections import OrderedDict, deque
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urlparse
from urllib.request import urlopen, Request

from skyfield.framelib import ecliptic_frame

ROOT_DIR = Path(__file__).resolve().parents[1]
STATIC_DIR = Path(__file__).resolve().parent / "static"
ASSETS_DIR = ROOT_DIR / "assets"
WEB_CONFIG_PATH = ROOT_DIR / "web_ui_config.json"
CERT_DIR = ROOT_DIR / ".web_certs"
ELEVATION_CACHE_PATH = ROOT_DIR / "data" / "cache" / "elevation_cache.json"
APP_VERSION = os.environ.get("ADSB_APP_VERSION", "1.4.1")
PROJECT_URL = "https://github.com/RealSeaberry/ADS-B-Transit-Predictor"
ELEVATION_RANGE_OPTIONS_NM = [5, 10, 25, 50, 100]
ELEVATION_PRECISION_STEPS_KM = {"low": 3.0, "medium": 1.5, "high": 0.5}
ELEVATION_BATCH_SIZE = 10
ELEVATION_BATCH_DELAY_SEC = 6.0
ELEVATION_RATE_LIMIT_WAIT_SEC = 600.0
sys.path.insert(0, str(ROOT_DIR))

import transit_finder as tf  # noqa: E402
import numpy as np  # noqa: E402


SERVER_START = datetime.now(timezone.utc)
THREADS_STARTED = False
GEODATA_READY = False
CONFIG_LOCK = threading.Lock()
STATE_CACHE_LOCK = threading.Lock()
VECTOR_GEODATA_CACHE_LOCK = threading.Lock()
TERRAIN_CONTOUR_CACHE_LOCK = threading.Lock()
TERRAIN_DOWNLOAD_LOCK = threading.Lock()
TERRAIN_DOWNLOAD_CANCEL_EVENT = threading.Event()
TERRAIN_DOWNLOAD_PAUSE_EVENT = threading.Event()
MAP_CACHE_EVENT = threading.Event()
HIGH_VECTOR_LOAD_LOCK = threading.Lock()
HIGH_VECTOR_LOAD_STARTED = False
METAR_FETCH_LOCK = threading.Lock()
METAR_MIN_FETCH_INTERVAL_SEC = 10 * 60
METAR_FORCE_MIN_FETCH_INTERVAL_SEC = 90
METAR_LAST_FETCH_ATTEMPT = {"icao": None, "monotonic": 0.0}
MAX_CLIENT_STATE_CACHES = 8
MAX_VECTOR_GEODATA_CACHE = 48
MAX_TERRAIN_CONTOUR_CACHE = 32
DEFAULT_CLIENT_ID = "default"
VECTOR_GEODATA_CACHE = OrderedDict()
TERRAIN_CONTOUR_CACHE = OrderedDict()
TERRAIN_DOWNLOAD_STATUS = {
    "running": False,
    "ok": True,
    "error": "",
    "message": "",
    "progress": 0.0,
    "radius_nm": None,
    "points_total": 0,
    "points_done": 0,
    "points_downloaded": 0,
    "points_cached": 0,
    "started": None,
    "updated": None,
    "result": None,
    "cancel_requested": False,
    "paused": False,
}


def new_state_cache():
    return {
        "map_signature": None,
        "transit_signature": None,
        "aircraft_signature": None,
        "map_updated": None,
        "transits_updated": None,
        "transits_updated_monotonic": 0.0,
        "aircraft_updated": None,
        "aircraft_updated_monotonic": 0.0,
        "events_updated": None,
        "events": [],
        "aircraft": [],
        "transits": [],
        "geodata": {"airports": [], "navaids": [], "runways": [], "vectors": []},
        "glideslopes": [],
        "celestial": None,
        "last_access": time.monotonic(),
    }


STATE_CACHE_REQUEST = {
    "range_km": tf.INITIAL_MAP_RANGE_KM,
    "center_lat": tf.USER_LAT,
    "center_lon": tf.USER_LON,
    "viewport_width": 1.0,
    "viewport_height": 1.0,
    "selected_icao": "",
    "transit_mode": "selected",
}
STATE_CACHE_REQUESTS = {DEFAULT_CLIENT_ID: STATE_CACHE_REQUEST.copy()}
STATE_CACHE = new_state_cache()
CLIENT_STATE_CACHES = {DEFAULT_CLIENT_ID: STATE_CACHE}
AIRCRAFT_LABEL_FIELDS = {
    "callsign", "icao", "distance", "altitude", "corrected_alt_asl",
    "altitude_factor", "altitude_offset", "speed", "track", "vs", "squawk",
}
DEV_AIRCRAFT_LABEL_FIELDS = {"altitude_factor", "altitude_offset"}
SUPPORTED_GEOID_MODELS = ["egm96-15", "egm96-5", "egm2008-5", "egm2008-2_5", "egm2008-1"]
QUICK_VECTOR_LAYERS = (
    "ne_10m_admin_0_boundary_lines_land",
    "ne_10m_lakes",
)
DEFAULT_WEB_CONFIG = {
    "visual_style": "cwp_classic",
    "aircraft_label_fields": ["callsign", "altitude", "speed", "vs"],
    "aircraft_label_lines": [["callsign"], ["altitude", "speed", "vs"]],
    "ils_style": "atc",
    "ils_length_nm": "10",
    "aircraft_label_color": "aircraft",
    "aircraft_label_size": "medium",
    "aircraft_label_3d_mode": "fade",
    "unit_distance": "km",
    "unit_speed": "kt",
    "unit_altitude": "ft",
    "aircraft_refresh_interval": "realtime",
    "trajectory_minutes": 2.0,
    "trajectory_display_mode": "altitude",
    "show_active_full_history": False,
    "show_grounded_aircraft": False,
    "show_geo_vectors": True,
    "show_background_grid": True,
    "show_event_range_ring": True,
    "show_event_aircraft_links": True,
    "active_glideslopes": [],
    "show_dev_options": False,
}


def utc_now():
    return datetime.now(timezone.utc)


def json_default(value):
    if isinstance(value, datetime):
        return value.isoformat()
    if isinstance(value, set):
        return list(value)
    return str(value)


def finite_float(value, fallback=None):
    try:
        value = float(value)
        if math.isfinite(value):
            return value
    except (TypeError, ValueError):
        pass
    return fallback


def safe_int(value, fallback):
    try:
        return int(value)
    except (TypeError, ValueError):
        return fallback


def installed_geoid_models():
    models = []
    for model in SUPPORTED_GEOID_MODELS:
        for path in tf._candidate_geoid_paths(model):
            if Path(path).is_file():
                models.append({"model": model, "path": str(path)})
                break
    return models


def load_web_config():
    config = DEFAULT_WEB_CONFIG.copy()
    try:
        with WEB_CONFIG_PATH.open("r", encoding="utf-8") as handle:
            loaded = json.load(handle)
        if isinstance(loaded, dict):
            config.update({key: loaded[key] for key in DEFAULT_WEB_CONFIG if key in loaded})
    except FileNotFoundError:
        save_web_config(config)
    except Exception as exc:
        print(f"[web] Could not load {WEB_CONFIG_PATH}: {exc}")
    if config["visual_style"] == "atc":
        config["visual_style"] = "cwp_classic"
    if config["visual_style"] not in {"current", "desktop", "cwp_classic", "cwp_approach", "cwp_enroute"}:
        config["visual_style"] = "cwp_classic"
    allowed_fields = AIRCRAFT_LABEL_FIELDS
    if not isinstance(config.get("aircraft_label_fields"), list):
        config["aircraft_label_fields"] = DEFAULT_WEB_CONFIG["aircraft_label_fields"][:]
    else:
        config["aircraft_label_fields"] = [field for field in config["aircraft_label_fields"] if field in allowed_fields]
        if not config["aircraft_label_fields"]:
            config["aircraft_label_fields"] = DEFAULT_WEB_CONFIG["aircraft_label_fields"][:]
    if not isinstance(config.get("aircraft_label_lines"), list):
        config["aircraft_label_lines"] = DEFAULT_WEB_CONFIG["aircraft_label_lines"][:]
    else:
        clean_lines = []
        seen = set()
        for line in config["aircraft_label_lines"]:
            if not isinstance(line, list):
                continue
            clean_line = []
            for field in line:
                if field in allowed_fields and field not in seen:
                    clean_line.append(field)
                    seen.add(field)
            if clean_line:
                clean_lines.append(clean_line)
        config["aircraft_label_lines"] = clean_lines[:4] or DEFAULT_WEB_CONFIG["aircraft_label_lines"][:]
    if config["ils_style"] not in {"atc", "desktop", "minimal"}:
        config["ils_style"] = "atc"
    if str(config["ils_length_nm"]) not in {"5", "7", "10", "15"}:
        config["ils_length_nm"] = "10"
    if config["aircraft_label_color"] not in {"aircraft", "green"}:
        config["aircraft_label_color"] = "aircraft"
    if config.get("aircraft_label_size") not in {"small", "medium", "large"}:
        config["aircraft_label_size"] = "medium"
    if config.get("aircraft_label_3d_mode") not in {"fade", "avoid"}:
        config["aircraft_label_3d_mode"] = "fade"
    if config["unit_distance"] not in {"km", "nm", "mi"}:
        config["unit_distance"] = "km"
    if config["unit_speed"] not in {"kt", "kmh", "mph"}:
        config["unit_speed"] = "kt"
    if config["unit_altitude"] not in {"ft", "m"}:
        config["unit_altitude"] = "ft"
    if str(config.get("aircraft_refresh_interval")) not in {"realtime", "1", "2", "5"}:
        config["aircraft_refresh_interval"] = "realtime"
    config["trajectory_minutes"] = finite_float(config.get("trajectory_minutes"), 2.0)
    if config["trajectory_minutes"] is None or config["trajectory_minutes"] <= 0:
        config["trajectory_minutes"] = 2.0
    if config.get("trajectory_display_mode") not in {"altitude", "points"}:
        config["trajectory_display_mode"] = "altitude"
    config["show_geo_vectors"] = bool(config.get("show_geo_vectors", True))
    config["show_background_grid"] = bool(config.get("show_background_grid", True))
    config["show_terrain_contours"] = False
    config["show_event_range_ring"] = bool(config.get("show_event_range_ring", True))
    config["show_event_aircraft_links"] = bool(config.get("show_event_aircraft_links", True))
    config["show_active_full_history"] = bool(config.get("show_active_full_history", False))
    config["show_grounded_aircraft"] = bool(config.get("show_grounded_aircraft", False))
    config["show_dev_options"] = bool(config.get("show_dev_options", False))
    if not isinstance(config.get("active_glideslopes"), list):
        config["active_glideslopes"] = []
    config["terrain_display_dataset"] = "all"
    return config


def save_web_config(config):
    clean = DEFAULT_WEB_CONFIG.copy()
    clean.update({key: config.get(key, clean[key]) for key in DEFAULT_WEB_CONFIG})
    with WEB_CONFIG_PATH.open("w", encoding="utf-8") as handle:
        json.dump(clean, handle, indent=4, sort_keys=True)
    return clean


def visible_aircraft_label_fields(config):
    fields = ["callsign", "icao", "distance", "altitude", "corrected_alt_asl", "speed", "track", "vs", "squawk"]
    if bool(config.get("gps_altitude_correction_enabled", False)):
        fields[5:5] = ["altitude_factor", "altitude_offset"]
    return fields


def filtered_web_config_for_runtime(web_config, config):
    if bool(config.get("gps_altitude_correction_enabled", False)):
        return web_config
    filtered = web_config.copy()
    filtered["aircraft_label_fields"] = [
        field for field in filtered.get("aircraft_label_fields", [])
        if field not in DEV_AIRCRAFT_LABEL_FIELDS
    ] or DEFAULT_WEB_CONFIG["aircraft_label_fields"][:]
    filtered["aircraft_label_lines"] = [
        [field for field in line if field not in DEV_AIRCRAFT_LABEL_FIELDS]
        for line in filtered.get("aircraft_label_lines", [])
        if isinstance(line, list)
    ]
    filtered["aircraft_label_lines"] = [line for line in filtered["aircraft_label_lines"] if line] or DEFAULT_WEB_CONFIG["aircraft_label_lines"][:]
    return filtered


def public_config():
    config = tf.load_config(tf.config_file_full_path)
    web_config = filtered_web_config_for_runtime(load_web_config(), config)
    local_geoids = installed_geoid_models()
    return {
        "config": config,
        "web": web_config,
        "about": {
            "name": "ADS-B Transit Predictor",
            "version": APP_VERSION,
            "project_url": PROJECT_URL,
            "icon_url": "/assets/icon.png",
            "dependencies": [
                "OurAirports airport, runway, and navaid data",
                "GSHHG coastline and land polygons",
                "Natural Earth vector map data",
                "dump1090 / dump1090-mutability / readsb or another SBS/BaseStation decoder",
                "RTL-SDR / rtl-sdr tools for RTL2832U receivers",
                "Skyfield astronomy and ephemeris calculations",
                "Optional EGM96/EGM2008 geoid grids from GeographicLib/NGA",
                "NumPy, pyshp, and Shapely geospatial processing",
                "Tailscale and usbipd-win are optional for remote WSL access",
            ],
        },
        "options": {
            "airport_types": tf.ALL_AIRPORT_TYPES,
            "navaid_types": tf.ALL_NAVAID_TYPES,
            "range_ring_spacing_nm": tf.RANGE_RING_OPTIONS_NM,
            "velocity_vector_minutes": tf.VELOCITY_VECTOR_OPTIONS_MIN,
            "vector_layers": {
                key: value.get("label", key)
                for key, value in tf.VECTOR_LAYER_CONFIGS.items()
            },
            "visual_styles": ["current", "desktop", "cwp_classic", "cwp_approach", "cwp_enroute"],
            "aircraft_label_fields": visible_aircraft_label_fields(config),
            "aircraft_label_line_numbers": ["1", "2", "3", "4"],
            "ils_styles": ["atc", "desktop", "minimal"],
            "ils_lengths_nm": ["5", "7", "10", "15"],
            "aircraft_label_colors": ["aircraft", "green"],
            "aircraft_label_sizes": ["small", "medium", "large"],
            "aircraft_label_3d_modes": ["fade", "avoid"],
            "unit_distances": ["km", "nm", "mi"],
            "unit_speeds": ["kt", "kmh", "mph"],
            "unit_altitudes": ["ft", "m"],
            "aircraft_refresh_intervals": ["realtime", "1", "2", "5"],
            "trajectory_minutes": [0.5, 1, 1.5, 2, 3, 5, 8, 10],
            "trajectory_display_modes": ["altitude", "points"],
            "geoid_models": [item["model"] for item in local_geoids],
            "installed_geoids": local_geoids,
        },
        "requires_restart_for": ["host", "port", "device_index", "gain"],
    }


def coerce_config_value(key, value, current):
    bool_keys = {
        "show_history",
        "show_events",
        "show_glideslope",
        "show_range_rings",
        "show_all_transit_strips",
        "show_velocity_vector",
        "show_geo_vectors",
        "show_event_range_ring",
        "geoid_correction_enabled",
        "gps_altitude_correction_enabled",
    }
    float_keys = {
        "lat",
        "lon",
        "alt_m",
        "aircraft_timeout",
        "pred_interval",
        "pred_horizon",
        "pred_step",
        "prediction_average_sec",
        "event_min_elevation_deg",
        "conflict_angle",
        "event_timeout",
        "conflict_radius_km",
        "history_minutes",
        "trajectory_minutes",
        "velocity_vector_minutes",
        "alt_correction_manual_temp_c",
        "alt_correction_manual_qnh_hpa",
        "metar_max_airport_km",
        "dump1090_json_interval_sec",
    }
    int_keys = {"port", "device_index", "max_range_rings"}
    list_keys = {"show_airport_types", "show_navaid_types"}

    if key in bool_keys:
        return bool(value)
    if key in float_keys:
        parsed = finite_float(value, current.get(key))
        return parsed
    if key in int_keys:
        return safe_int(value, current.get(key))
    if key in list_keys:
        return [str(item) for item in value] if isinstance(value, list) else current.get(key, [])
    if key == "vector_layers_visibility":
        if not isinstance(value, dict):
            return current.get(key, {})
        return {layer: bool(value.get(layer, False)) for layer in tf.VECTOR_LAYER_CONFIGS}
    if key == "aircraft_label_fields":
        allowed_fields = AIRCRAFT_LABEL_FIELDS
        return [str(item) for item in value if str(item) in allowed_fields] if isinstance(value, list) else current.get(key, DEFAULT_WEB_CONFIG["aircraft_label_fields"])
    if key == "aircraft_label_lines":
        allowed_fields = AIRCRAFT_LABEL_FIELDS
        if not isinstance(value, list):
            return current.get(key, DEFAULT_WEB_CONFIG["aircraft_label_lines"])
        lines = []
        seen = set()
        for line in value:
            if not isinstance(line, list):
                continue
            clean_line = []
            for item in line:
                field = str(item)
                if field in allowed_fields and field not in seen:
                    clean_line.append(field)
                    seen.add(field)
            if clean_line:
                lines.append(clean_line)
        return lines[:4] or current.get(key, DEFAULT_WEB_CONFIG["aircraft_label_lines"])
    if key in {"unit_distance", "unit_speed", "unit_altitude"}:
        return str(value)
    if key == "trajectory_minutes":
        parsed = finite_float(value, current.get(key, 2.0))
        return parsed if parsed is not None and parsed > 0 else current.get(key, 2.0)
    if key == "geoid_model":
        value = str(value)
        installed = {item["model"] for item in installed_geoid_models()}
        return value if value in installed else current.get(key, "egm96-15")
    if key in {"host", "gain", "range_ring_spacing_nm_str", "alt_correction_mode", "dump1090_json_url", "geoid_data_path"}:
        return str(value)
    return current.get(key, value)


def desired_history_minutes(config, web_config=None):
    if web_config is None:
        web_config = load_web_config()
    history_minutes = finite_float(config.get("history_minutes"), tf.DEFAULT_AIRCRAFT_HISTORY_MINUTES) or tf.DEFAULT_AIRCRAFT_HISTORY_MINUTES
    trajectory_minutes = finite_float(web_config.get("trajectory_minutes"), 2.0) or 2.0
    if web_config.get("show_active_full_history"):
        trajectory_minutes = max(trajectory_minutes, tf.DATA_RETENTION_SECONDS / 60.0)
    return max(history_minutes, trajectory_minutes)


def aircraft_refresh_seconds(web_config=None):
    if web_config is None:
        web_config = load_web_config()
    value = str(web_config.get("aircraft_refresh_interval", "realtime"))
    if value == "realtime":
        return 0.2
    parsed = finite_float(value, 1.0)
    return max(0.2, min(5.0, parsed or 1.0))


def apply_runtime_config(config, web_config=None, reload_geodata=True):
    global GEODATA_READY
    tf.HOST = config["host"]
    tf.PORT = config["port"]
    tf.DUMP1090_DEVICE_INDEX = config["device_index"]
    tf.DUMP1090_GAIN = config["gain"]
    tf.USER_LAT = config["lat"]
    tf.USER_LON = config["lon"]
    tf.USER_ALT = config["alt_m"]
    tf.USER_ALT_FT = tf.USER_ALT * 3.28084
    tf.TERRAIN_ALT_M = tf.USER_ALT
    tf.AIRCRAFT_TIMEOUT = config["aircraft_timeout"]
    tf.PREDICTION_INTERVAL = config["pred_interval"]
    tf.PREDICTION_HORIZON = config["pred_horizon"]
    tf.PREDICTION_STEP = config["pred_step"]
    tf.PREDICTION_AVERAGE_SEC = config.get("prediction_average_sec", tf.DEFAULT_PREDICTION_AVERAGE_SEC)
    tf.EVENT_MIN_ELEVATION_DEG = config.get("event_min_elevation_deg", tf.DEFAULT_EVENT_MIN_ELEVATION_DEG)
    tf.CONFLICT_ANGLE_DEG = config["conflict_angle"]
    tf.EVENT_TIMEOUT = config["event_timeout"]
    tf.CONFLICT_RADIUS_KM = config["conflict_radius_km"]
    tf.AIRCRAFT_HISTORY_MINUTES = desired_history_minutes(config, web_config)
    tf.SHOW_AIRPORT_TYPES = config["show_airport_types"]
    tf.SHOW_NAVAID_TYPES = config["show_navaid_types"]
    tf.SHOW_AIRCRAFT_HISTORY = config["show_history"]
    tf.SHOW_EVENT_LOCATIONS = config["show_events"]
    tf.SHOW_GLIDESLOPE = config["show_glideslope"]
    tf.SHOW_RANGE_RINGS = config["show_range_rings"]
    tf.RANGE_RING_SPACING_NM_STR = config["range_ring_spacing_nm_str"]
    tf.MAX_RANGE_RINGS = config["max_range_rings"]
    tf.SHOW_ALL_TRANSIT_STRIPS = config["show_all_transit_strips"]
    tf.VELOCITY_VECTOR_MINUTES = config["velocity_vector_minutes"]
    tf.VELOCITY_VECTOR_SECONDS = tf.VELOCITY_VECTOR_MINUTES * 60.0
    tf.SHOW_VELOCITY_VECTOR = config["show_velocity_vector"]
    tf.VECTOR_LAYERS_VISIBILITY = config["vector_layers_visibility"].copy()
    old_mode = tf.ALT_CORRECTION_MODE
    tf.ALT_CORRECTION_MODE = config.get("alt_correction_mode", "metar")
    tf.ALT_CORRECTION_MANUAL_TEMP_C = config.get("alt_correction_manual_temp_c", 15.0)
    tf.ALT_CORRECTION_MANUAL_QNH_HPA = config.get("alt_correction_manual_qnh_hpa", 1013.25)
    tf.METAR_MAX_AIRPORT_KM = config.get("metar_max_airport_km", 100.0)
    old_geoid = (tf.GEOID_CORRECTION_ENABLED, tf.GEOID_MODEL, tf.GEOID_DATA_PATH)
    tf.GEOID_CORRECTION_ENABLED = bool(config.get("geoid_correction_enabled", False))
    tf.GEOID_MODEL = str(config.get("geoid_model", "egm96-15") or "egm96-15")
    tf.GEOID_DATA_PATH = str(config.get("geoid_data_path", "") or "").strip()
    tf.GPS_ALTITUDE_CORRECTION_ENABLED = bool(config.get("gps_altitude_correction_enabled", False))
    if old_geoid != (tf.GEOID_CORRECTION_ENABLED, tf.GEOID_MODEL, tf.GEOID_DATA_PATH):
        tf.load_geoid_grid(force=True)
    tf.DUMP1090_JSON_URL = str(os.environ.get("ADSB_DUMP1090_JSON_URL", config.get("dump1090_json_url", tf.DEFAULT_DUMP1090_JSON_URL)) or "").strip()
    try:
        tf.DUMP1090_JSON_INTERVAL_SEC = max(0.2, min(10.0, float(os.environ.get("ADSB_DUMP1090_JSON_INTERVAL_SEC", config.get("dump1090_json_interval_sec", tf.DEFAULT_DUMP1090_JSON_INTERVAL_SEC)) or tf.DEFAULT_DUMP1090_JSON_INTERVAL_SEC)))
    except (TypeError, ValueError):
        tf.DUMP1090_JSON_INTERVAL_SEC = tf.DEFAULT_DUMP1090_JSON_INTERVAL_SEC
    if tf.ALT_CORRECTION_MODE == "metar" and old_mode != "metar":
        tf.METAR_REFRESH_EVENT.set()  # immediate fetch when switching to METAR mode
    history_maxlen = tf.aircraft_history_maxlen()
    with tf.lock:
        for ac in tf.aircraft_dict.values():
            history = ac.get("history")
            if history is not None and getattr(history, "maxlen", None) != history_maxlen:
                ac["history"] = deque(history, maxlen=history_maxlen)
    try:
        tf.RANGE_RING_SPACING_KM = float(tf.RANGE_RING_SPACING_NM_STR) * tf.NM_TO_KM
    except ValueError:
        tf.RANGE_RING_SPACING_NM_STR = tf.DEFAULT_RANGE_RING_SPACING_NM_STR
        tf.RANGE_RING_SPACING_KM = float(tf.RANGE_RING_SPACING_NM_STR) * tf.NM_TO_KM
    try:
        tf.observer_topos = tf.Topos(latitude_degrees=tf.USER_LAT, longitude_degrees=tf.USER_LON, elevation_m=tf.USER_ALT)
    except Exception as exc:
        print(f"[web] Could not update observer location: {exc}")
    tf.TERRAIN_ELEVATION_LOOKUP = None
    if reload_geodata:
        GEODATA_READY = False
        init_geodata()
    with VECTOR_GEODATA_CACHE_LOCK:
        VECTOR_GEODATA_CACHE.clear()
    with STATE_CACHE_LOCK:
        for cache in CLIENT_STATE_CACHES.values():
            if reload_geodata:
                cache["map_signature"] = None
            cache["transit_signature"] = None
            cache["aircraft_signature"] = None


def update_config_from_payload(payload):
    with CONFIG_LOCK:
        current = tf.load_config(tf.config_file_full_path)
        updated = current.copy()
        changed_config_keys = set()
        web_changed = False
        for key in current:
            if key in payload:
                new_value = coerce_config_value(key, payload[key], current)
                if new_value != current.get(key):
                    changed_config_keys.add(key)
                updated[key] = new_value
        if "web" in payload and isinstance(payload["web"], dict):
            web_current = load_web_config()
            web_updated = web_current.copy()
            for key in DEFAULT_WEB_CONFIG:
                if key in payload["web"]:
                    old_value = web_updated.get(key)
                    if key in {"show_geo_vectors", "show_background_grid", "show_terrain_contours", "show_event_range_ring", "show_event_aircraft_links", "show_active_full_history", "show_grounded_aircraft", "show_dev_options"}:
                        web_updated[key] = bool(payload["web"][key])
                    elif key == "active_glideslopes":
                        web_updated[key] = payload["web"][key] if isinstance(payload["web"][key], list) else []
                    elif key == "aircraft_label_fields":
                        web_updated[key] = payload["web"][key] if isinstance(payload["web"][key], list) else DEFAULT_WEB_CONFIG["aircraft_label_fields"][:]
                    elif key == "aircraft_label_lines":
                        web_updated[key] = coerce_config_value(key, payload["web"][key], web_current)
                    elif key in {"unit_distance", "unit_speed", "unit_altitude"}:
                        web_updated[key] = str(payload["web"][key])
                    elif key == "trajectory_minutes":
                        web_updated[key] = finite_float(payload["web"][key], web_current.get(key, 2.0)) or 2.0
                    elif key == "trajectory_display_mode":
                        web_updated[key] = str(payload["web"][key])
                    else:
                        web_updated[key] = str(payload["web"][key])
                    if web_updated.get(key) != old_value:
                        web_changed = True
            if not bool(web_updated.get("show_dev_options", False)):
                updated["gps_altitude_correction_enabled"] = False
                updated["geoid_correction_enabled"] = False
            save_web_config(web_updated)
        else:
            web_updated = None
        if not tf.save_config(tf.config_file_full_path, updated):
            raise RuntimeError("Could not save config.json")
        geodata_keys = {"lat", "lon", "alt_m", "show_airport_types", "show_navaid_types", "vector_layers_visibility"}
        reload_geodata = bool(changed_config_keys & geodata_keys)
        apply_runtime_config(updated, web_updated, reload_geodata=reload_geodata)
        if web_changed or "show_glideslope" in changed_config_keys:
            with STATE_CACHE_LOCK:
                STATE_CACHE["glideslopes"] = glideslope_snapshot()
                STATE_CACHE["map_updated"] = utc_now()
    return updated




def elevation_cache_key(lat, lon):
    return f"{round(float(lat), 5):.5f},{round(float(lon), 5):.5f}"


def load_elevation_cache():
    try:
        with ELEVATION_CACHE_PATH.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
        return data if isinstance(data, dict) else {}
    except FileNotFoundError:
        return {}
    except Exception as exc:
        print(f"[web] Could not load elevation cache: {exc}")
        return {}


def save_elevation_cache(cache):
    ELEVATION_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    with ELEVATION_CACHE_PATH.open("w", encoding="utf-8") as handle:
        json.dump(cache, handle, indent=2, sort_keys=True)
    clear_terrain_contour_cache()


def clear_terrain_contour_cache():
    with TERRAIN_CONTOUR_CACHE_LOCK:
        TERRAIN_CONTOUR_CACHE.clear()


def terrain_dataset_id(item):
    if item.get("download_id"):
        return str(item.get("download_id"))
    radius = item.get("radius_nm", "single")
    precision = item.get("precision", "point")
    step = finite_float(item.get("grid_step_km"))
    step_m = int(round(step * 1000)) if step else 0
    return f"{radius}|{precision}|{step_m}"


def terrain_item_matches_dataset(item, dataset_id):
    if not dataset_id or dataset_id == "all":
        return True
    return terrain_dataset_id(item) == dataset_id


def terrain_cache_summary():
    cache = load_elevation_cache()
    groups = OrderedDict()
    for key, item in cache.items():
        if not isinstance(item, dict) or item.get("alt_m") is None:
            continue
        dataset_id = terrain_dataset_id(item)
        group = groups.setdefault(dataset_id, {
            "id": dataset_id,
            "radius_nm": item.get("radius_nm"),
            "precision": item.get("precision"),
            "grid_step_km": item.get("grid_step_km"),
            "download_id": item.get("download_id"),
            "count": 0,
            "bytes": 0,
            "min_lat": None,
            "max_lat": None,
            "min_lon": None,
            "max_lon": None,
            "updated": "",
        })
        lat = finite_float(item.get("lat"))
        lon = finite_float(item.get("lon"))
        group["count"] += 1
        group["bytes"] += len(key) + len(json.dumps(item, default=json_default, separators=(",", ":")))
        if lat is not None:
            group["min_lat"] = lat if group["min_lat"] is None else min(group["min_lat"], lat)
            group["max_lat"] = lat if group["max_lat"] is None else max(group["max_lat"], lat)
        if lon is not None:
            group["min_lon"] = lon if group["min_lon"] is None else min(group["min_lon"], lon)
            group["max_lon"] = lon if group["max_lon"] is None else max(group["max_lon"], lon)
        updated = str(item.get("updated") or "")
        if updated > group["updated"]:
            group["updated"] = updated
    datasets = sorted(groups.values(), key=lambda row: (str(row.get("radius_nm")), str(row.get("precision")), row.get("updated") or ""), reverse=True)
    return {
        "path": str(ELEVATION_CACHE_PATH),
        "points": sum(row["count"] for row in datasets),
        "bytes": ELEVATION_CACHE_PATH.stat().st_size if ELEVATION_CACHE_PATH.exists() else 0,
        "datasets": datasets,
        "selected": load_web_config().get("terrain_display_dataset", "all"),
    }


def delete_terrain_dataset(dataset_id):
    dataset_id = str(dataset_id or "")
    if not dataset_id or dataset_id == "all":
        raise ValueError("Choose one downloaded terrain dataset to delete.")
    cache = load_elevation_cache()
    kept = {}
    removed = 0
    for key, item in cache.items():
        if isinstance(item, dict) and terrain_item_matches_dataset(item, dataset_id):
            removed += 1
            continue
        kept[key] = item
    save_elevation_cache(kept)
    install_terrain_lookup()
    return {"removed": removed, "cache": terrain_cache_summary()}


def select_terrain_dataset(dataset_id):
    dataset_id = str(dataset_id or "all")
    if dataset_id != "all":
        known = {row["id"] for row in terrain_cache_summary()["datasets"]}
        if dataset_id not in known:
            raise ValueError("Selected terrain dataset is not available.")
    config = load_web_config()
    config["terrain_display_dataset"] = dataset_id
    save_web_config(config)
    clear_terrain_contour_cache()
    return terrain_cache_summary()


def terrain_elevation_snapshot(lat, lon):
    lat = finite_float(lat)
    lon = finite_float(lon)
    if lat is None or lon is None or not (-90.0 <= lat <= 90.0) or not (-180.0 <= lon <= 180.0):
        raise ValueError("Valid latitude and longitude are required.")
    key = elevation_cache_key(lat, lon)
    cache = load_elevation_cache()
    cached = cache.get(key)
    if isinstance(cached, dict) and cached.get("alt_m") is not None:
        result = cached.copy()
        result["cached"] = True
        return result

    url = f"https://api.open-meteo.com/v1/elevation?latitude={lat:.7f}&longitude={lon:.7f}"
    with urlopen(url, timeout=8) as response:
        payload = json.loads(response.read().decode("utf-8"))
    elevations = payload.get("elevation")
    if not isinstance(elevations, list) or not elevations:
        raise ValueError("Elevation API did not return terrain altitude.")
    alt_m = finite_float(elevations[0])
    if alt_m is None:
        raise ValueError("Elevation API returned an invalid altitude.")
    item = {
        "lat": lat,
        "lon": lon,
        "alt_m": alt_m,
        "resolution_m": 90,
        "source": "Open-Meteo Elevation API / Copernicus DEM GLO-90",
        "cached": False,
        "updated": utc_now().isoformat(),
    }
    cache[key] = item.copy()
    save_elevation_cache(cache)
    return item


def terrain_points_snapshot(center_lat, center_lon, range_km, max_points=900):
    center_lat = finite_float(center_lat, tf.USER_LAT)
    center_lon = finite_float(center_lon, tf.USER_LON)
    range_km = max(1.0, min(250.0, finite_float(range_km, 50.0) or 50.0))
    if center_lat is None or center_lon is None:
        return {"points": []}
    lat_span = math.degrees(range_km / tf.EARTH_RADIUS_KM) * 1.15
    lon_factor = max(0.05, math.cos(math.radians(center_lat)))
    lon_span = math.degrees(range_km / (tf.EARTH_RADIUS_KM * lon_factor)) * 1.15
    min_lat, max_lat = center_lat - lat_span, center_lat + lat_span
    min_lon, max_lon = center_lon - lon_span, center_lon + lon_span
    dataset_id = load_web_config().get("terrain_display_dataset", "all")
    cache = load_elevation_cache()
    points = []
    for item in cache.values():
        if not isinstance(item, dict) or item.get("alt_m") is None:
            continue
        if not terrain_item_matches_dataset(item, dataset_id):
            continue
        lat = finite_float(item.get("lat"))
        lon = finite_float(item.get("lon"))
        alt = finite_float(item.get("alt_m"))
        if lat is None or lon is None or alt is None:
            continue
        if min_lat <= lat <= max_lat and min_lon <= lon <= max_lon:
            points.append({"lat": lat, "lon": lon, "alt_m": alt})
    if len(points) > max_points:
        stride = max(1, math.ceil(len(points) / max_points))
        points = points[::stride]
    return {"points": points, "dataset": dataset_id}


def cached_terrain_elevation_at(lat, lon, max_distance_km=None):
    lat = finite_float(lat)
    lon = finite_float(lon)
    if lat is None or lon is None:
        return None
    cache = load_elevation_cache()
    best = None
    for item in cache.values():
        if not isinstance(item, dict) or item.get("alt_m") is None:
            continue
        ilat = finite_float(item.get("lat"))
        ilon = finite_float(item.get("lon"))
        if ilat is None or ilon is None:
            continue
        item_step = finite_float(item.get("grid_step_km"), 1.5) or 1.5
        allowed_km = max_distance_km if max_distance_km is not None else max(2.0, item_step * 1.8)
        lat_window = allowed_km / 111.32
        lon_window = allowed_km / max(8.0, 111.32 * math.cos(math.radians(lat)))
        if abs(ilat - lat) > lat_window or abs(ilon - lon) > lon_window:
            continue
        dist = tf.haversine(lat, lon, ilat, ilon)
        if dist <= allowed_km and (best is None or dist < best[0]):
            best = (dist, finite_float(item.get("alt_m")))
    return best[1] if best else None


def terrain_contour_cache_key(min_lat, max_lat, min_lon, max_lon):
    lat_span = max(1e-6, max_lat - min_lat)
    lon_span = max(1e-6, max_lon - min_lon)
    lat_step = max(0.005, lat_span / 5.0)
    lon_step = max(0.005, lon_span / 5.0)
    bucket_min_lat = round(math.floor(min_lat / lat_step) * lat_step, 4)
    bucket_max_lat = round(math.ceil(max_lat / lat_step) * lat_step, 4)
    bucket_min_lon = round(math.floor(min_lon / lon_step) * lon_step, 4)
    bucket_max_lon = round(math.ceil(max_lon / lon_step) * lon_step, 4)
    dataset_id = load_web_config().get("terrain_display_dataset", "all")
    try:
        cache_stamp = (ELEVATION_CACHE_PATH.stat().st_mtime_ns, ELEVATION_CACHE_PATH.stat().st_size)
    except FileNotFoundError:
        cache_stamp = (0, 0)
    return (bucket_min_lat, bucket_max_lat, bucket_min_lon, bucket_max_lon, dataset_id, cache_stamp)


def cached_terrain_contours_snapshot(min_lat, max_lat, min_lon, max_lon):
    key = terrain_contour_cache_key(min_lat, max_lat, min_lon, max_lon)
    with TERRAIN_CONTOUR_CACHE_LOCK:
        cached = TERRAIN_CONTOUR_CACHE.get(key)
        if cached is not None:
            TERRAIN_CONTOUR_CACHE.move_to_end(key)
            return cached
    contours = terrain_contours_snapshot(key[0], key[1], key[2], key[3])
    with TERRAIN_CONTOUR_CACHE_LOCK:
        TERRAIN_CONTOUR_CACHE[key] = contours
        TERRAIN_CONTOUR_CACHE.move_to_end(key)
        while len(TERRAIN_CONTOUR_CACHE) > MAX_TERRAIN_CONTOUR_CACHE:
            TERRAIN_CONTOUR_CACHE.popitem(last=False)
    return contours


def terrain_contours_snapshot(min_lat, max_lat, min_lon, max_lon, max_points=520):
    lat_span = max_lat - min_lat
    lon_span = max_lon - min_lon
    if lat_span > 1.8 or lon_span > 2.6:
        return {"points": [], "segments": []}
    cache = load_elevation_cache()
    dataset_id = load_web_config().get("terrain_display_dataset", "all")
    points = []
    for item in cache.values():
        if not isinstance(item, dict) or item.get("alt_m") is None:
            continue
        if not terrain_item_matches_dataset(item, dataset_id):
            continue
        lat = finite_float(item.get("lat"))
        lon = finite_float(item.get("lon"))
        alt = finite_float(item.get("alt_m"))
        if lat is None or lon is None or alt is None:
            continue
        if min_lat <= lat <= max_lat and min_lon <= lon <= max_lon:
            points.append({"lat": lat, "lon": lon, "alt_m": alt, "grid_step_km": item.get("grid_step_km")})
    if len(points) < 4:
        return {"points": [], "segments": []}
    grid_steps = [finite_float(pt.get("grid_step_km")) for pt in points]
    grid_steps = [step for step in grid_steps if step is not None and step > 0]
    raw_grid_step_km = min(grid_steps) if grid_steps else 1.5
    visible_height_km = max(0.1, (max_lat - min_lat) * 111.32)
    visible_width_km = max(0.1, (max_lon - min_lon) * max(8.0, 111.32 * math.cos(math.radians((min_lat + max_lat) / 2.0))))
    if len(points) * (raw_grid_step_km ** 2) < visible_height_km * visible_width_km * 0.18:
        return {"points": [], "segments": []}
    if len(points) > max_points:
        stride = max(1, math.ceil(len(points) / max_points))
        points = points[::stride]
    alts = [pt["alt_m"] for pt in points]
    min_alt, max_alt = min(alts), max(alts)
    if max_alt - min_alt < 20:
        return {"points": [], "segments": []}
    level_step = 100 if max_alt - min_alt > 1200 else 50 if max_alt - min_alt > 450 else 25
    levels = list(range(int(math.ceil(min_alt / level_step) * level_step), int(max_alt) + 1, level_step))

    point_steps = [finite_float(pt.get("grid_step_km")) for pt in points if isinstance(pt, dict)]
    point_steps = [step for step in point_steps if step is not None and step > 0]
    grid_step_km = min(point_steps) if point_steps else raw_grid_step_km
    grid_step_km = max(0.75, min(5.0, grid_step_km))
    center_lat = (min_lat + max_lat) / 2.0
    lat_step = grid_step_km / 111.32
    lon_step = grid_step_km / max(8.0, 111.32 * math.cos(math.radians(center_lat)))
    lat_start = math.floor(min_lat / lat_step) * lat_step
    lat_end = math.ceil(max_lat / lat_step) * lat_step
    lon_start = math.floor(min_lon / lon_step) * lon_step
    lon_end = math.ceil(max_lon / lon_step) * lon_step
    lat_values = []
    value = lat_start
    while value <= lat_end + lat_step * 0.5 and len(lat_values) < 56:
        lat_values.append(value)
        value += lat_step
    lon_values = []
    value = lon_start
    while value <= lon_end + lon_step * 0.5 and len(lon_values) < 56:
        lon_values.append(value)
        value += lon_step
    search_lat = lat_step * 2.2
    search_lon = lon_step * 2.2
    grid = {}
    for lat_g in lat_values:
        for lon_g in lon_values:
            nearest = []
            for pt in points:
                dlat = abs(pt["lat"] - lat_g)
                dlon = abs(pt["lon"] - lon_g)
                if dlat <= search_lat and dlon <= search_lon:
                    dist2 = dlat * dlat + dlon * dlon
                    nearest.append((dist2, pt["alt_m"]))
            if not nearest:
                continue
            nearest.sort(key=lambda item: item[0])
            use = nearest[:6]
            weighted_sum = 0.0
            weight_total = 0.0
            for dist2, alt in use:
                weight = 1.0 / max(1e-10, dist2)
                weighted_sum += alt * weight
                weight_total += weight
            grid[(lat_g, lon_g)] = weighted_sum / weight_total

    def interp(a, b, level):
        lat1, lon1, z1 = a
        lat2, lon2, z2 = b
        if z1 == z2:
            t = 0.5
        else:
            t = max(0.0, min(1.0, (level - z1) / (z2 - z1)))
        return [lat1 + (lat2 - lat1) * t, lon1 + (lon2 - lon1) * t]

    segments = []
    for level in levels:
        for yi in range(len(lat_values) - 1):
            for xi in range(len(lon_values) - 1):
                sw_key = (lat_values[yi], lon_values[xi])
                se_key = (lat_values[yi], lon_values[xi + 1])
                ne_key = (lat_values[yi + 1], lon_values[xi + 1])
                nw_key = (lat_values[yi + 1], lon_values[xi])
                if not all(key in grid for key in (sw_key, se_key, ne_key, nw_key)):
                    continue
                sw = (sw_key[0], sw_key[1], grid[sw_key])
                se = (se_key[0], se_key[1], grid[se_key])
                ne = (ne_key[0], ne_key[1], grid[ne_key])
                nw = (nw_key[0], nw_key[1], grid[nw_key])
                crossings = []
                for p1, p2 in ((sw, se), (se, ne), (ne, nw), (nw, sw)):
                    z1, z2 = p1[2], p2[2]
                    if (z1 < level <= z2) or (z2 < level <= z1):
                        crossings.append(interp(p1, p2, level))
                if len(crossings) == 2:
                    segments.append({"level": level, "points": crossings})
                elif len(crossings) == 4:
                    segments.append({"level": level, "points": [crossings[0], crossings[1]]})
                    segments.append({"level": level, "points": [crossings[2], crossings[3]]})
                if len(segments) >= 900:
                    return {"points": [], "segments": segments}
    return {"points": [], "segments": segments}


def install_terrain_lookup():
    tf.TERRAIN_ELEVATION_LOOKUP = cached_terrain_elevation_at


def terrain_grid_step_km(radius_nm, precision="medium"):
    precision = str(precision or "medium").lower()
    if precision not in ELEVATION_PRECISION_STEPS_KM:
        precision = "medium"
    return ELEVATION_PRECISION_STEPS_KM[precision]


def elevation_grid_points(center_lat, center_lon, radius_nm, precision="medium"):
    radius_km = float(radius_nm) * tf.NM_TO_KM
    step_km = terrain_grid_step_km(radius_nm, precision)
    points = [(float(center_lat), float(center_lon))]
    n_steps = int(math.ceil(radius_km / step_km))
    for y in range(-n_steps, n_steps + 1):
        north_km = y * step_km
        for x in range(-n_steps, n_steps + 1):
            east_km = x * step_km
            dist_km = math.hypot(east_km, north_km)
            if dist_km <= 0.01 or dist_km > radius_km:
                continue
            lat, lon = tf.offset_surface_point(float(center_lat), float(center_lon), east_km, north_km)
            points.append((lat, lon))
    return points


def fetch_elevation_batch(points):
    elevations = []
    for idx in range(0, len(points), ELEVATION_BATCH_SIZE):
        if TERRAIN_DOWNLOAD_CANCEL_EVENT.is_set():
            raise RuntimeError("Terrain download cancelled.")
        wait_terrain_download_if_paused()
        chunk = points[idx:idx + ELEVATION_BATCH_SIZE]
        lat_q = ",".join(f"{lat:.7f}" for lat, _lon in chunk)
        lon_q = ",".join(f"{lon:.7f}" for _lat, lon in chunk)
        url = f"https://api.open-meteo.com/v1/elevation?latitude={lat_q}&longitude={lon_q}"
        payload = None
        network_attempt = 0
        while payload is None:
            if TERRAIN_DOWNLOAD_CANCEL_EVENT.is_set():
                raise RuntimeError("Terrain download cancelled.")
            wait_terrain_download_if_paused()
            try:
                with urlopen(url, timeout=20) as response:
                    payload = json.loads(response.read().decode("utf-8"))
                break
            except HTTPError as exc:
                if exc.code != 429:
                    raise
                retry_after = exc.headers.get("Retry-After") if getattr(exc, "headers", None) else None
                wait_sec = finite_float(retry_after, ELEVATION_RATE_LIMIT_WAIT_SEC) or ELEVATION_RATE_LIMIT_WAIT_SEC
                wait_sec = max(300.0, min(1800.0, wait_sec))
                update_terrain_status(message=f"Rate limited by elevation API; waiting {int(wait_sec)}s before continuing")
                sleep_terrain_download(wait_sec)
            except (URLError, ssl.SSLError, TimeoutError, OSError) as exc:
                network_attempt += 1
                if network_attempt > 8:
                    raise
                wait_sec = min(90.0, 3.0 * (2 ** (network_attempt - 1)))
                update_terrain_status(message=f"Elevation network error; retrying in {int(wait_sec)}s ({exc})")
                sleep_terrain_download(wait_sec)
        if payload is None:
            raise ValueError("Elevation API did not return data.")
        chunk_elev = payload.get("elevation")
        if not isinstance(chunk_elev, list) or len(chunk_elev) != len(chunk):
            raise ValueError("Elevation API returned an unexpected batch response.")
        elevations.extend(chunk_elev)
        if idx + ELEVATION_BATCH_SIZE < len(points):
            sleep_terrain_download(ELEVATION_BATCH_DELAY_SEC)
    return elevations


def terrain_status_snapshot():
    with TERRAIN_DOWNLOAD_LOCK:
        return json.loads(json.dumps(TERRAIN_DOWNLOAD_STATUS, default=json_default))


def update_terrain_status(**updates):
    with TERRAIN_DOWNLOAD_LOCK:
        TERRAIN_DOWNLOAD_STATUS.update(updates)
        TERRAIN_DOWNLOAD_STATUS["updated"] = utc_now().isoformat()


def wait_terrain_download_if_paused():
    while TERRAIN_DOWNLOAD_PAUSE_EVENT.is_set() and not TERRAIN_DOWNLOAD_CANCEL_EVENT.is_set():
        update_terrain_status(paused=True, message="Terrain download paused")
        time.sleep(0.25)
    if TERRAIN_DOWNLOAD_CANCEL_EVENT.is_set():
        raise RuntimeError("Terrain download cancelled.")
    update_terrain_status(paused=False)


def sleep_terrain_download(seconds):
    end_time = time.monotonic() + max(0.0, float(seconds or 0.0))
    while time.monotonic() < end_time:
        if TERRAIN_DOWNLOAD_CANCEL_EVENT.is_set():
            raise RuntimeError("Terrain download cancelled.")
        wait_terrain_download_if_paused()
        time.sleep(min(1.0, max(0.0, end_time - time.monotonic())))


def terrain_download_worker(lat, lon, radius_nm, precision):
    try:
        grid_step_km = terrain_grid_step_km(radius_nm, precision)
        download_id = f"{radius_nm}nm-{precision}-{int(round(grid_step_km * 1000))}m-{utc_now().strftime('%Y%m%d%H%M%S')}"
        points = elevation_grid_points(lat, lon, radius_nm, precision)
        cache = load_elevation_cache()
        missing = [point for point in points if elevation_cache_key(*point) not in cache]
        update_terrain_status(
            running=True,
            ok=True,
            error="",
            message=f"Downloading terrain {radius_nm} nm",
            radius_nm=radius_nm,
            precision=precision,
            grid_step_km=grid_step_km,
            points_total=len(points),
            points_done=len(points) - len(missing),
            points_downloaded=0,
            points_cached=len(points) - len(missing),
            progress=(len(points) - len(missing)) / max(1, len(points)),
            result=None,
            cancel_requested=False,
            paused=False,
        )
        downloaded = 0
        for idx in range(0, len(missing), ELEVATION_BATCH_SIZE):
            wait_terrain_download_if_paused()
            if TERRAIN_DOWNLOAD_CANCEL_EVENT.is_set():
                update_terrain_status(
                    running=False,
                    ok=False,
                    error="Terrain download cancelled.",
                    message="Terrain download cancelled",
                    cancel_requested=False,
                    paused=False,
                )
                return
            chunk = missing[idx:idx + ELEVATION_BATCH_SIZE]
            elevations = fetch_elevation_batch(chunk)
            for point, elevation in zip(chunk, elevations):
                alt_m = finite_float(elevation)
                if alt_m is None:
                    continue
                cache[elevation_cache_key(*point)] = {
                    "lat": point[0],
                    "lon": point[1],
                    "alt_m": alt_m,
                    "resolution_m": 90,
                    "source": "Open-Meteo Elevation API / Copernicus DEM GLO-90",
                    "radius_nm": radius_nm,
                    "precision": precision,
                    "grid_step_km": grid_step_km,
                    "download_id": download_id,
                    "updated": utc_now().isoformat(),
                }
            save_elevation_cache(cache)
            downloaded += len(chunk)
            done = len(points) - len(missing) + downloaded
            update_terrain_status(
                points_done=done,
                points_downloaded=downloaded,
                progress=done / max(1, len(points)),
                message=f"Downloading terrain {radius_nm} nm: {done}/{len(points)}",
            )
        save_elevation_cache(cache)
        install_terrain_lookup()
        center = terrain_elevation_snapshot(lat, lon)
        result = {
            "center": center,
            "radius_nm": radius_nm,
            "precision": precision,
            "grid_step_km": grid_step_km,
            "download_id": download_id,
            "points_total": len(points),
            "points_downloaded": len(missing),
            "points_cached": len(points) - len(missing),
            "source": "Open-Meteo Elevation API / Copernicus DEM GLO-90",
        }
        update_terrain_status(
            running=False,
            ok=True,
            message=f"Terrain {radius_nm} nm ready",
            progress=1.0,
            points_done=len(points),
            result=result,
            paused=False,
        )
    except Exception as exc:
        error_text = str(exc)
        if "cancelled" in error_text.lower():
            update_terrain_status(running=False, ok=False, error="Terrain download cancelled.", message="Terrain download cancelled", cancel_requested=False, paused=False)
            return
        if isinstance(exc, HTTPError) and exc.code == 429:
            error_text = "Elevation API rate limit reached. Wait a few minutes and start the same download again; cached points will be skipped."
        update_terrain_status(running=False, ok=False, error=error_text, message="Terrain download failed", cancel_requested=False, paused=False)


def start_terrain_download(lat, lon, radius_nm, precision="medium"):
    lat = finite_float(lat)
    lon = finite_float(lon)
    radius_nm = safe_int(radius_nm, 10)
    precision = str(precision or "medium").lower()
    if precision not in ELEVATION_PRECISION_STEPS_KM:
        raise ValueError("Terrain precision must be low, medium, or high.")
    if radius_nm not in ELEVATION_RANGE_OPTIONS_NM:
        raise ValueError("Elevation range must be one of 5, 10, 25, 50, or 100 nm.")
    if lat is None or lon is None or not (-90.0 <= lat <= 90.0) or not (-180.0 <= lon <= 180.0):
        raise ValueError("Valid latitude and longitude are required.")
    already_running = False
    with TERRAIN_DOWNLOAD_LOCK:
        if TERRAIN_DOWNLOAD_STATUS.get("running"):
            already_running = True
        else:
            TERRAIN_DOWNLOAD_CANCEL_EVENT.clear()
            TERRAIN_DOWNLOAD_PAUSE_EVENT.clear()
            TERRAIN_DOWNLOAD_STATUS.update({
                "running": True,
                "ok": True,
                "error": "",
                "message": f"Preparing terrain {radius_nm} nm",
                "progress": 0.0,
                "radius_nm": radius_nm,
                "precision": precision,
                "grid_step_km": terrain_grid_step_km(radius_nm, precision),
                "points_total": 0,
                "points_done": 0,
                "points_downloaded": 0,
                "points_cached": 0,
                "started": utc_now().isoformat(),
                "updated": utc_now().isoformat(),
                "result": None,
                "cancel_requested": False,
                "paused": False,
            })
    if already_running:
        return terrain_status_snapshot()
    thread = threading.Thread(target=terrain_download_worker, args=(lat, lon, radius_nm, precision), daemon=True)
    thread.start()
    return terrain_status_snapshot()


def cancel_terrain_download():
    with TERRAIN_DOWNLOAD_LOCK:
        running = bool(TERRAIN_DOWNLOAD_STATUS.get("running"))
        if running:
            TERRAIN_DOWNLOAD_STATUS["cancel_requested"] = True
            TERRAIN_DOWNLOAD_STATUS["message"] = "Stopping terrain download..."
            TERRAIN_DOWNLOAD_STATUS["paused"] = False
            TERRAIN_DOWNLOAD_STATUS["updated"] = utc_now().isoformat()
    if running:
        TERRAIN_DOWNLOAD_PAUSE_EVENT.clear()
        TERRAIN_DOWNLOAD_CANCEL_EVENT.set()
    return terrain_status_snapshot()


def pause_terrain_download(paused=True):
    paused = bool(paused)
    with TERRAIN_DOWNLOAD_LOCK:
        running = bool(TERRAIN_DOWNLOAD_STATUS.get("running"))
        if running:
            TERRAIN_DOWNLOAD_STATUS["paused"] = paused
            TERRAIN_DOWNLOAD_STATUS["message"] = "Terrain download paused" if paused else "Terrain download resumed"
            TERRAIN_DOWNLOAD_STATUS["updated"] = utc_now().isoformat()
    if running:
        if paused:
            TERRAIN_DOWNLOAD_PAUSE_EVENT.set()
        else:
            TERRAIN_DOWNLOAD_PAUSE_EVENT.clear()
    return terrain_status_snapshot()


def terrain_elevation_grid_snapshot(lat, lon, radius_nm, precision="medium"):
    lat = finite_float(lat)
    lon = finite_float(lon)
    radius_nm = safe_int(radius_nm, 10)
    precision = str(precision or "medium").lower()
    if precision not in ELEVATION_PRECISION_STEPS_KM:
        raise ValueError("Terrain precision must be low, medium, or high.")
    if radius_nm not in ELEVATION_RANGE_OPTIONS_NM:
        raise ValueError("Elevation range must be one of 5, 10, 25, 50, or 100 nm.")
    if lat is None or lon is None or not (-90.0 <= lat <= 90.0) or not (-180.0 <= lon <= 180.0):
        raise ValueError("Valid latitude and longitude are required.")
    grid_step_km = terrain_grid_step_km(radius_nm, precision)
    download_id = f"{radius_nm}nm-{precision}-{int(round(grid_step_km * 1000))}m-{utc_now().strftime('%Y%m%d%H%M%S')}"
    points = elevation_grid_points(lat, lon, radius_nm, precision)
    cache = load_elevation_cache()
    missing = []
    for point in points:
        if elevation_cache_key(*point) not in cache:
            missing.append(point)
    elevations = fetch_elevation_batch(missing) if missing else []
    for point, elevation in zip(missing, elevations):
        alt_m = finite_float(elevation)
        if alt_m is None:
            continue
        cache[elevation_cache_key(*point)] = {
            "lat": point[0],
            "lon": point[1],
            "alt_m": alt_m,
            "resolution_m": 90,
            "source": "Open-Meteo Elevation API / Copernicus DEM GLO-90",
            "radius_nm": radius_nm,
            "precision": precision,
            "grid_step_km": grid_step_km,
            "download_id": download_id,
            "updated": utc_now().isoformat(),
        }
    save_elevation_cache(cache)
    install_terrain_lookup()
    center = terrain_elevation_snapshot(lat, lon)
    return {
        "center": center,
        "radius_nm": radius_nm,
        "precision": precision,
        "grid_step_km": grid_step_km,
        "download_id": download_id,
        "points_total": len(points),
        "points_downloaded": len(missing),
        "points_cached": len(points) - len(missing),
        "source": "Open-Meteo Elevation API / Copernicus DEM GLO-90",
    }


def get_tailscale_ip():
    try:
        info = socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET)
        for item in info:
            ip = item[4][0]
            if ip.startswith("100."):
                return ip
    except OSError:
        pass
    return None


def ensure_self_signed_cert(certfile, keyfile):
    cert_path = Path(certfile)
    key_path = Path(keyfile)
    if cert_path.exists() and key_path.exists():
        return cert_path, key_path
    cert_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "openssl", "req", "-x509", "-newkey", "rsa:2048",
        "-keyout", str(key_path), "-out", str(cert_path),
        "-sha256", "-days", "825", "-nodes",
        "-subj", "/CN=adsb-transit.local",
        "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1",
    ]
    subprocess.run(cmd, check=True, capture_output=True, text=True)
    return cert_path, key_path


def init_ephemeris():
    if tf.eph and tf.ts and tf.observer_topos:
        return
    ephemeris_path = tf.resource_path(os.path.join("data", "de421.bsp"))
    try:
        tf.eph = tf.load(ephemeris_path)
        tf.ts = tf.load.timescale()
        tf.observer_topos = tf.Topos(
            latitude_degrees=tf.USER_LAT,
            longitude_degrees=tf.USER_LON,
            elevation_m=tf.USER_ALT,
        )
        print(f"[web] Loaded ephemeris: {ephemeris_path}")
    except Exception as exc:
        print(f"[web] Ephemeris unavailable: {exc}")


def init_geodata():
    global GEODATA_READY
    if GEODATA_READY:
        return
    try:
        tf.airports_data = tf.load_airports(
            filename=tf.AIRPORTS_CSV,
            types_to_show=tf.ALL_AIRPORT_TYPES,
        )
        airport_ids = {apt["ident"] for apt in tf.airports_data}
        tf.runways_data = tf.load_runways(
            filename=tf.RUNWAYS_CSV,
            airport_idents_to_load=airport_ids,
        )
        tf.navaids_data = tf.load_navaids(
            filename=tf.NAVAIDS_CSV,
            types_to_show=tf.SHOW_NAVAID_TYPES,
        )
        if tf.map_manager is None:
            tf.map_manager = tf.MapDataManager(os.path.join(tf.app_dir, "data"))
        GEODATA_READY = True
    except Exception as exc:
        print(f"[web] Geodata unavailable: {exc}")


def load_vector_layer(layer_key):
    if tf.map_manager is None:
        tf.map_manager = tf.MapDataManager(os.path.join(tf.app_dir, "data"))
    if layer_key not in tf.VECTOR_LAYER_CONFIGS or layer_key in tf.map_manager.layers_data:
        return
    layer_cfg = tf.VECTOR_LAYER_CONFIGS[layer_key]
    tf.map_manager.load_layer(layer_key, layer_cfg)
    layer_data = tf.map_manager.layers_data.get(layer_key, [])
    shp_name = layer_cfg.get("shp_filename", layer_key)
    source_layer = layer_cfg.get("source_layer", layer_key)
    shp_path = Path(tf.app_dir) / "data" / "map_vectors" / source_layer / f"{shp_name}.shp"
    if not layer_data and shp_path.exists():
        cache_path = Path(tf.map_manager.get_cache_path(layer_cfg.get("cache_key", layer_key)))
        try:
            cache_path.unlink(missing_ok=True)
        except Exception:
            pass
        tf.map_manager.load_layer(layer_key, layer_cfg)
        layer_data = tf.map_manager.layers_data.get(layer_key, [])
def ensure_quick_vector_layers_loaded():
    for layer_key in QUICK_VECTOR_LAYERS:
        load_vector_layer(layer_key)


def ensure_visible_vector_layers_loaded():
    visible_layers = [
        layer_key
        for layer_key, visible in tf.VECTOR_LAYERS_VISIBILITY.items()
        if visible and layer_key in tf.VECTOR_LAYER_CONFIGS
    ]
    for layer_key in [key for key in visible_layers if not key.startswith("gshhs_")]:
        load_vector_layer(layer_key)
    for layer_key in [key for key in visible_layers if key.startswith("gshhs_")]:
        load_vector_layer(layer_key)


def high_vector_layers_ready():
    if not tf.map_manager:
        return False
    visible_high_layers = [
        layer_key
        for layer_key, visible in tf.VECTOR_LAYERS_VISIBILITY.items()
        if visible and layer_key.startswith("gshhs_")
    ]
    if not visible_high_layers:
        return True
    return all(layer_key in tf.map_manager.layers_data for layer_key in visible_high_layers)


def start_high_vector_load():
    global HIGH_VECTOR_LOAD_STARTED
    if high_vector_layers_ready():
        return
    with HIGH_VECTOR_LOAD_LOCK:
        if HIGH_VECTOR_LOAD_STARTED or high_vector_layers_ready():
            return
        HIGH_VECTOR_LOAD_STARTED = True

    def _worker():
        global HIGH_VECTOR_LOAD_STARTED
        try:
            ensure_visible_vector_layers_loaded()
            with STATE_CACHE_LOCK:
                for cache in CLIENT_STATE_CACHES.values():
                    cache["map_signature"] = None
            MAP_CACHE_EVENT.set()
        except Exception as exc:
            print(f"[web] High-detail vector load failed: {exc}")
        finally:
            with HIGH_VECTOR_LOAD_LOCK:
                HIGH_VECTOR_LOAD_STARTED = False

    threading.Thread(target=_worker, daemon=True, name="HighVectorLoader").start()


def _parse_metar_time(raw, now=None):
    """Infer a UTC observation timestamp from the DDHHMMZ token in a METAR."""
    import re
    if not raw:
        return None
    if now is None:
        now = datetime.now(timezone.utc)
    m = re.search(r'\b(\d{2})(\d{2})(\d{2})Z\b', raw)
    if not m:
        return None
    day, hour, minute = (int(m.group(1)), int(m.group(2)), int(m.group(3)))
    candidates = []
    for month_delta in (-1, 0, 1):
        year = now.year
        month = now.month + month_delta
        while month < 1:
            month += 12
            year -= 1
        while month > 12:
            month -= 12
            year += 1
        try:
            candidates.append(datetime(year, month, day, hour, minute, tzinfo=timezone.utc))
        except ValueError:
            continue
    if not candidates:
        return None
    return min(candidates, key=lambda item: abs((now - item).total_seconds()))


def _parse_iso_datetime(value):
    if not value:
        return None
    try:
        return datetime.fromisoformat(str(value).replace("Z", "+00:00")).astimezone(timezone.utc)
    except Exception:
        return None


def _fetch_metar(icao, timeout=20):
    """Fetch latest METAR from aviationweather.gov. Returns dict or None."""
    url = f"https://aviationweather.gov/api/data/metar?ids={icao}&format=json&hours=2"
    try:
        req = Request(url, headers={"User-Agent": "ADSBTransitPredictor/1.5"})
        with urlopen(req, timeout=timeout) as resp:
            if resp.status == 204:
                return None
            text = resp.read().decode("utf-8", errors="ignore")
            rows = json.loads(text) if text.strip() else []
            if not rows:
                return None
            row = rows[0]
            raw = row.get("rawOb") or row.get("raw_text") or row.get("raw") or ""
            temp_c, qnh_hpa = _parse_metar_values(raw)
            if row.get("temp") is not None:
                try:
                    temp_c = float(row.get("temp"))
                except (TypeError, ValueError):
                    pass
            if row.get("altim") is not None:
                try:
                    altim = float(row.get("altim"))
                    qnh_hpa = round(altim * 33.8639, 1) if altim < 100.0 else round(altim, 1)
                except (TypeError, ValueError):
                    pass
            observed_at = (
                _parse_iso_datetime(row.get("obsTime"))
                or _parse_iso_datetime(row.get("reportTime"))
                or _parse_metar_time(raw)
            )
            return {"raw": raw, "temp_c": temp_c, "qnh_hpa": qnh_hpa, "observed_at": observed_at}
    except Exception as exc:
        print(f"[metar] Fetch error for {icao}: {exc}")
        return None


def _parse_metar_values(raw):
    """Extract (temp_c, qnh_hpa) from raw METAR string. Returns (None, None) on failure."""
    import re
    if not raw:
        return None, None
    temp_c, qnh_hpa = None, None
    m = re.search(r'\b(M?\d{2})/M?\d{2}\b', raw)
    if m:
        t = m.group(1)
        temp_c = -(int(t[1:])) if t.startswith('M') else int(t)
    m = re.search(r'\bQ(\d{4})\b', raw)
    if m:
        qnh_hpa = int(m.group(1))
    else:
        m = re.search(r'\bA(\d{4})\b', raw)
        if m:
            qnh_hpa = round(int(m.group(1)) / 100.0 * 33.8639)
    return temp_c, qnh_hpa


def _refresh_metar_once(force=False):
    """Single METAR fetch attempt. Updates tf.METAR_STATE. Returns True on success."""
    now = datetime.now(timezone.utc)
    apt, dist_km = tf.find_nearest_metar_airport(
        tf.USER_LAT, tf.USER_LON, max_km=tf.METAR_MAX_AIRPORT_KM
    )
    if apt is None:
        with tf.METAR_LOCK:
            tf.METAR_STATE.update({
                "valid": False, "warning": None, "fetched_at": now, "observed_at": None, "age_sec": None,
                "error": f"No airport within {tf.METAR_MAX_AIRPORT_KM:.0f} km",
            })
        print(f"[metar] No airport within {tf.METAR_MAX_AIRPORT_KM:.0f} km")
        return False
    icao = apt.get("ident", "")
    min_interval = METAR_FORCE_MIN_FETCH_INTERVAL_SEC if force else METAR_MIN_FETCH_INTERVAL_SEC
    mono_now = time.monotonic()
    with METAR_FETCH_LOCK:
        last_icao = METAR_LAST_FETCH_ATTEMPT.get("icao")
        last_mono = float(METAR_LAST_FETCH_ATTEMPT.get("monotonic") or 0.0)
        if last_icao == icao and mono_now - last_mono < min_interval:
            return bool(tf.METAR_STATE.get("valid"))
        METAR_LAST_FETCH_ATTEMPT["icao"] = icao
        METAR_LAST_FETCH_ATTEMPT["monotonic"] = mono_now
    metar = _fetch_metar(icao)
    raw = metar.get("raw") if metar else None
    temp_c = metar.get("temp_c") if metar else None
    qnh_hpa = metar.get("qnh_hpa") if metar else None
    observed_at = metar.get("observed_at") if metar else None
    if observed_at is None and raw:
        observed_at = _parse_metar_time(raw, now=now)
    age_sec = (now - observed_at).total_seconds() if observed_at is not None else None
    too_old = age_sec is not None and age_sec > tf.METAR_MAX_AGE_SEC
    warning = None
    if age_sec is not None and tf.METAR_WARN_AGE_SEC < age_sec <= tf.METAR_MAX_AGE_SEC:
        warning = "METAR is older than 90 minutes; still using it as degraded fallback"
    valid = raw is not None and temp_c is not None and qnh_hpa is not None and not too_old
    error = None
    if not valid:
        if too_old:
            error = "METAR expired (>120 min old); altitude correction disabled until refreshed or manual values are used"
        else:
            error = f"Could not fetch/parse METAR for {icao}"
    with tf.METAR_LOCK:
        previous_raw = tf.METAR_STATE.get("raw")
        tf.METAR_STATE.update({
            "airport_icao": icao,
            "airport_name": apt.get("name", ""),
            "airport_dist_km": dist_km,
            "raw": raw,
            "temp_c": temp_c,
            "qnh_hpa": qnh_hpa,
            "observed_at": observed_at,
            "fetched_at": now,
            "age_sec": round(age_sec) if age_sec is not None else None,
            "valid": valid,
            "warning": warning,
            "error": error,
        })
    if valid and raw != previous_raw:
        print(f"[metar] {icao} ({dist_km} km): {raw}")
    elif not valid:
        print(f"[metar] Failed for {icao}: raw={raw!r}")
    return valid


def metar_worker():
    """Always-running background thread. Keeps METAR fresh when mode='metar'.
    Continues retrying when stale or failed; stays dormant but alive in other modes."""
    REFRESH_SEC = 30 * 60
    RETRY_SEC   =  5 * 60
    POLL_SEC    = 30

    while True:
        triggered = tf.METAR_REFRESH_EVENT.wait(timeout=POLL_SEC)
        if triggered:
            tf.METAR_REFRESH_EVENT.clear()

        if tf.ALT_CORRECTION_MODE != "metar":
            continue

        try:
            # Update age and mark stale if expired
            with tf.METAR_LOCK:
                observed_at = tf.METAR_STATE.get("observed_at")
                was_valid  = tf.METAR_STATE.get("valid", False)
            if observed_at is not None:
                age_sec = (datetime.now(timezone.utc) - observed_at).total_seconds()
                with tf.METAR_LOCK:
                    tf.METAR_STATE["age_sec"] = round(age_sec)
                    if tf.METAR_WARN_AGE_SEC < age_sec <= tf.METAR_MAX_AGE_SEC and tf.METAR_STATE["valid"]:
                        tf.METAR_STATE["warning"] = "METAR is older than 90 minutes; still using it as degraded fallback"
                        tf.METAR_STATE["error"] = None
                    elif age_sec > tf.METAR_MAX_AGE_SEC and tf.METAR_STATE["valid"]:
                        tf.METAR_STATE["valid"] = False
                        tf.METAR_STATE["warning"] = None
                        tf.METAR_STATE["error"] = "METAR expired (>120 min old); altitude correction disabled until refreshed or manual values are used"
            else:
                age_sec = float("inf")

            # Fetch if triggered, or if overdue
            due_in = REFRESH_SEC if was_valid else RETRY_SEC
            if triggered or age_sec >= due_in:
                _refresh_metar_once(force=triggered)
        except Exception as exc:
            print(f"[metar] Worker error: {exc}")


def start_processing_threads(start_dump1090=False):
    global THREADS_STARTED
    if THREADS_STARTED:
        return
    tf.running = True
    tf.AIRCRAFT_HISTORY_MINUTES = desired_history_minutes(tf.load_config(tf.config_file_full_path), load_web_config())
    if start_dump1090:
        try:
            tf.start_dump1090_process()
        except FileNotFoundError as exc:
            print(f"[web] {exc}; continuing without dump1090 auto-start.")
        except Exception as exc:
            print(f"[web] Could not start dump1090: {exc}")

    init_ephemeris()
    init_geodata()
    tf.load_geoid_grid(force=True)

    workers = [
        threading.Thread(target=tf.start_listener, daemon=True, name="WebListener"),
        threading.Thread(target=tf.predict_conflicts, daemon=True, name="WebConflictPredictor"),
        threading.Thread(target=tf.clean_expired_events, daemon=True, name="WebEventCleaner"),
        threading.Thread(target=event_cache_worker, daemon=True, name="WebEventCache"),
        threading.Thread(target=map_cache_worker, daemon=True, name="WebMapCache"),
        threading.Thread(target=metar_worker, daemon=True, name="METARUpdater"),
    ]
    if tf.GPS_ALTITUDE_CORRECTION_ENABLED and tf.DUMP1090_JSON_URL:
        workers.append(threading.Thread(target=tf.dump1090_json_listener, daemon=True, name="Dump1090JsonListener"))
    if tf.eph:
        workers.append(
            threading.Thread(
                target=tf.predict_celestial_conflicts,
                daemon=True,
                name="WebCelestialPredictor",
            )
        )
    for worker in workers:
        worker.start()
    MAP_CACHE_EVENT.set()
    if tf.ALT_CORRECTION_MODE == "metar":
        tf.METAR_REFRESH_EVENT.set()
    THREADS_STARTED = True


def aircraft_snapshot(range_km, center_lat, center_lon, web_config=None, viewport_width=1.0, viewport_height=1.0):
    if web_config is None:
        web_config = load_web_config()
    lat_span, lon_span = viewport_spans(range_km, center_lat, viewport_width, viewport_height, padding=1.08)
    min_lat, max_lat = center_lat - lat_span, center_lat + lat_span
    min_lon, max_lon = center_lon - lon_span, center_lon + lon_span
    trajectory_minutes = finite_float(web_config.get("trajectory_minutes"), 2.0) or 2.0
    trajectory_seconds = max(15.0, trajectory_minutes * 60.0)
    if web_config.get("show_active_full_history"):
        trajectory_seconds = max(trajectory_seconds, float(tf.DATA_RETENTION_SECONDS))
    vector_seconds = max(5.0, float(getattr(tf, "VELOCITY_VECTOR_SECONDS", 60.0) or 60.0))
    now = utc_now()
    history_cutoff = now.timestamp() - trajectory_seconds
    aircraft = []
    with tf.lock:
        source = [ac.copy() for ac in tf.aircraft_dict.values()]
    for ac in source:
        age = (now - ac["timestamp"]).total_seconds()
        if age > tf.AIRCRAFT_TIMEOUT:
            continue
        grounded = tf.is_probably_landed_aircraft(ac, now)
        if grounded and not web_config.get("show_grounded_aircraft", False):
            continue
        if not grounded:
            ac = tf.prediction_aircraft_state(ac, now)
            grounded = tf.is_probably_landed_aircraft(ac, now)
            if grounded and not web_config.get("show_grounded_aircraft", False):
                continue
        if ac.get("approach_details") and ac.get("altitude") is not None:
            try:
                runway_elev = ac["approach_details"].get("runway_elevation_ft")
                if runway_elev is not None and float(ac["altitude"]) <= float(runway_elev) + tf.LANDED_ELEVATION_MARGIN_FT:
                    grounded = True
                    if not web_config.get("show_grounded_aircraft", False):
                        continue
            except (TypeError, ValueError):
                pass
        lat = ac.get("lat")
        lon = ac.get("lon")
        has_position = lat is not None and lon is not None
        distance_km = tf.haversine(tf.USER_LAT, tf.USER_LON, lat, lon) if has_position else None
        view_distance_km = tf.haversine(center_lat, center_lon, lat, lon) if has_position else None
        visible = has_position and min_lat <= lat <= max_lat and min_lon <= lon <= max_lon
        corrected_alt_asl = None
        altitude_factor = None
        altitude_offset = None
        if ac.get("altitude") is not None:
            try:
                altitude_factor = float(ac.get("geometry_altitude_factor", 1.0) or 1.0)
                altitude_offset = float(ac.get("geometry_altitude_offset_ft", 0.0) or 0.0)
                corrected_alt_asl = tf.aircraft_geometry_altitude_ft(ac, ac.get("altitude"))
            except (TypeError, ValueError):
                altitude_factor = None
                altitude_offset = None
                corrected_alt_asl = None
        history = []
        for point in list(ac.get("history", [])):
            t, hlat, hlon, halt = point
            if t.timestamp() < history_cutoff:
                continue
            history.append(
                {
                    "time": t.isoformat(),
                    "lat": hlat,
                    "lon": hlon,
                    "altitude": halt,
                    "corrected_alt_asl": tf.aircraft_geometry_altitude_ft(ac, halt),
                }
            )
        if has_position and ac.get("altitude") is not None:
            append_current = True
            if history:
                try:
                    last = history[-1]
                    last_time = datetime.fromisoformat(str(last.get("time")).replace("Z", "+00:00"))
                    last_dist = tf.haversine(last.get("lat"), last.get("lon"), lat, lon)
                    append_current = (now - last_time).total_seconds() >= 0.5 or last_dist >= 0.01
                except Exception:
                    append_current = True
            if append_current:
                history.append(
                    {
                        "time": now.isoformat(),
                        "lat": lat,
                        "lon": lon,
                        "altitude": ac.get("altitude"),
                        "corrected_alt_asl": corrected_alt_asl,
                        "extrapolated": True,
                    }
                )
        path = []
        if all(ac.get(k) is not None for k in ("lat", "lon", "altitude", "speed", "track", "vs")):
            for dt in range(0, int(vector_seconds) + 1, 5):
                plat, plon, palt = tf.predict_position(
                    ac["lat"],
                    ac["lon"],
                    ac["altitude"],
                    ac["speed"],
                    ac["track"],
                    dt,
                    ac["vs"],
                )
                if plat is None:
                    break
                path.append({
                    "dt": dt,
                    "lat": plat,
                    "lon": plon,
                    "altitude": palt,
                    "corrected_alt_asl": tf.aircraft_geometry_altitude_ft(ac, palt),
                })

        aircraft.append(
            {
                "icao": ac.get("icao"),
                "callsign": (ac.get("callsign") or "").strip(),
                "lat": lat,
                "lon": lon,
                "altitude": ac.get("altitude"),
                "corrected_alt_asl": corrected_alt_asl,
                "altitude_factor": altitude_factor,
                "altitude_offset": altitude_offset,
                "speed": ac.get("speed"),
                "track": ac.get("track"),
                "vs": ac.get("vs"),
                "squawk": ac.get("squawk"),
                "approach_status": ac.get("approach_status"),
                "grounded_airport": ac.get("grounded_airport"),
                "grounded_runway": ac.get("grounded_runway"),
                "age_sec": age,
                "distance_km": distance_km,
                "view_distance_km": view_distance_km,
                "conflict": ac.get("conflict"),
                "has_event": bool(ac.get("event_ids")),
                "grounded": grounded,
                "history": history,
                "path": path,
                "visible": visible,
            }
        )
    aircraft.sort(
        key=lambda item: (
            item["view_distance_km"] is None and item["distance_km"] is None,
            item["view_distance_km"] if item["view_distance_km"] is not None else item["distance_km"] or 999999,
        )
    )
    return aircraft


def events_snapshot():
    now = utc_now()
    events = []
    with tf.lock:
        source = list(tf.event_dict.items())
        aircraft_source = {icao: tf.prediction_aircraft_state(ac.copy(), now) for icao, ac in tf.aircraft_dict.items()}
    user_obs = None
    earth_obj = None
    sun_obj = None
    moon_obj = None
    if tf.eph and tf.observer_topos:
        try:
            earth_obj = tf.eph["earth"]
            user_obs = earth_obj + tf.observer_topos
            sun_obj = tf.eph["sun"]
            moon_obj = tf.eph["moon"]
        except Exception:
            pass

    def slant_distance_km(lat, lon, alt_ft):
        if lat is None or lon is None:
            return None
        ground_km = tf.haversine(tf.USER_LAT, tf.USER_LON, lat, lon)
        if alt_ft is None:
            return ground_km
        vertical_km = tf.feet_to_km(float(alt_ft) - tf.USER_ALT_FT)
        return math.hypot(ground_km, vertical_km)

    def moon_phase_for_event(ev_time):
        if not (tf.eph and tf.ts and isinstance(ev_time, datetime)):
            return None
        try:
            t_event = tf.ts.utc(ev_time)
            earth = tf.eph["earth"]
            sun_app = earth.at(t_event).observe(tf.eph["sun"]).apparent()
            moon_app = earth.at(t_event).observe(tf.eph["moon"]).apparent()
            return moon_phase_snapshot(t_event, sun_app, moon_app)
        except Exception:
            return None

    def current_metrics(ev_type, icaos):
        ac_distance_km = None
        current_dist_km = None
        current_angle = None
        if ev_type == "AC-AC" and len(icaos) >= 2:
            ac1 = aircraft_source.get(icaos[0], {})
            ac2 = aircraft_source.get(icaos[1], {})
            if all(ac1.get(k) is not None for k in ("lat", "lon")) and all(ac2.get(k) is not None for k in ("lat", "lon")):
                current_dist_km = tf.haversine(ac1["lat"], ac1["lon"], ac2["lat"], ac2["lon"])
                d1 = tf.haversine(tf.USER_LAT, tf.USER_LON, ac1["lat"], ac1["lon"])
                d2 = tf.haversine(tf.USER_LAT, tf.USER_LON, ac2["lat"], ac2["lon"])
                ac_distance_km = min(d1, d2)
            if all(ac1.get(k) is not None for k in ("lat", "lon", "altitude")) and all(ac2.get(k) is not None for k in ("lat", "lon", "altitude")):
                current_angle = tf.angle_between(
                    tf.USER_LAT, tf.USER_LON, tf.USER_ALT_FT,
                    ac1["lat"], ac1["lon"], ac1["altitude"],
                    ac2["lat"], ac2["lon"], ac2["altitude"],
                )
        elif icaos:
            ac = aircraft_source.get(icaos[0], {})
            if ac.get("lat") is not None and ac.get("lon") is not None:
                ac_distance_km = tf.haversine(tf.USER_LAT, tf.USER_LON, ac["lat"], ac["lon"])
            body = sun_obj if ev_type == "AC-Sun" else moon_obj if ev_type == "AC-Moon" else None
            if user_obs and earth_obj and body and all(ac.get(k) is not None for k in ("lat", "lon", "altitude")):
                try:
                    ac_pos = tf.wgs84.latlon(ac["lat"], ac["lon"], elevation_m=tf.feet_to_km(ac["altitude"]) * 1000.0)
                    t_now = tf.ts.utc(now)
                    ac_app = user_obs.at(t_now).observe(earth_obj + ac_pos).apparent()
                    body_app = user_obs.at(t_now).observe(body).apparent()
                    current_angle = body_app.separation_from(ac_app).degrees
                except Exception:
                    pass
        return ac_distance_km, current_dist_km, current_angle

    for eid, ev in source:
        ev_time = ev.get("time")
        eta = (ev_time - now).total_seconds() if isinstance(ev_time, datetime) else None
        icaos = [item for item in eid if isinstance(item, str) and item not in {"AC-AC", "AC-Sun", "AC-Moon"}] if isinstance(eid, tuple) else []
        ev_type = ev.get("type")
        ac_distance_km, current_dist_km, current_angle = current_metrics(ev_type, icaos)
        event_distance_km = tf.haversine(tf.USER_LAT, tf.USER_LON, ev.get("lat"), ev.get("lon")) if ev.get("lat") is not None and ev.get("lon") is not None else None
        event_slant_distance_km = slant_distance_km(ev.get("lat"), ev.get("lon"), ev.get("alt"))
        pov = dict(ev.get("pov", {}) or {})
        if ev_type == "AC-Moon" and pov.get("valid"):
            pov["moon_phase"] = moon_phase_for_event(ev_time)
        events.append(
            {
                "type": ev_type,
                "icaos": icaos,
                "callsigns": ev.get("callsigns", []),
                "time": ev_time.isoformat() if isinstance(ev_time, datetime) else None,
                "eta_sec": eta,
                "angle": ev.get("angle"),
                "min_dist_km": ev.get("min_dist_km"),
                "current_angle": current_angle,
                "current_dist_km": current_dist_km,
                "ac_distance_km": ac_distance_km,
                "event_distance_km": event_distance_km,
                "event_slant_distance_km": event_slant_distance_km,
                "lat": ev.get("lat"),
                "lon": ev.get("lon"),
                "alt": ev.get("alt"),
                "pov": pov,
            }
        )
    events.sort(key=lambda item: item["eta_sec"] if item["eta_sec"] is not None else 999999)
    return events


def _append_feature(features, layer_key, feature_type, pts_array, point_limit, max_features):
    stride = max(1, int(math.ceil(len(pts_array) / point_limit)))
    pts = np.round(pts_array[::stride], 5).tolist()
    if len(pts) > 1:
        src_last = np.round(pts_array[-1], 5).tolist()
        if pts[-1] != src_last:
            pts.append(src_last)
    if len(pts) < 2:
        return False
    features.append({
        "layer": layer_key,
        "type": feature_type,
        "points": pts,
    })
    return len(features) >= max_features


def _bbox_corners(min_lon, max_lon, min_lat, max_lat):
    return [
        (min_lon, min_lat),
        (max_lon, min_lat),
        (max_lon, max_lat),
        (min_lon, max_lat),
        (min_lon, min_lat),
    ]


def _point_in_polygon(lon, lat, pts_array):
    inside = False
    points = pts_array.tolist()
    if len(points) < 3:
        return False
    prev_lon, prev_lat = points[-1]
    for curr_lon, curr_lat in points:
        crosses = (curr_lat > lat) != (prev_lat > lat)
        if crosses:
            x_intersect = (prev_lon - curr_lon) * (lat - curr_lat) / ((prev_lat - curr_lat) or 1e-12) + curr_lon
            if lon < x_intersect:
                inside = not inside
        prev_lon, prev_lat = curr_lon, curr_lat
    return inside


def _clip_polygon_edge(points, inside_fn, intersect_fn):
    if not points:
        return []
    output = []
    prev = points[-1]
    prev_inside = inside_fn(prev)
    for curr in points:
        curr_inside = inside_fn(curr)
        if curr_inside:
            if not prev_inside:
                output.append(intersect_fn(prev, curr))
            output.append(curr)
        elif prev_inside:
            output.append(intersect_fn(prev, curr))
        prev, prev_inside = curr, curr_inside
    return output


def _clip_polygon_to_bbox(pts_array, min_lon, max_lon, min_lat, max_lat):
    points = [tuple(item) for item in pts_array.tolist()]
    if len(points) < 3:
        return []

    def intersect_vertical(lon_value):
        def _intersect(a, b):
            ax, ay = a
            bx, by = b
            t = (lon_value - ax) / ((bx - ax) or 1e-12)
            return (lon_value, ay + t * (by - ay))
        return _intersect

    def intersect_horizontal(lat_value):
        def _intersect(a, b):
            ax, ay = a
            bx, by = b
            t = (lat_value - ay) / ((by - ay) or 1e-12)
            return (ax + t * (bx - ax), lat_value)
        return _intersect

    clipped = points
    clipped = _clip_polygon_edge(clipped, lambda p: p[0] >= min_lon, intersect_vertical(min_lon))
    clipped = _clip_polygon_edge(clipped, lambda p: p[0] <= max_lon, intersect_vertical(max_lon))
    clipped = _clip_polygon_edge(clipped, lambda p: p[1] >= min_lat, intersect_horizontal(min_lat))
    clipped = _clip_polygon_edge(clipped, lambda p: p[1] <= max_lat, intersect_horizontal(max_lat))
    if len(clipped) >= 3:
        return clipped

    center_lon = (min_lon + max_lon) / 2.0
    center_lat = (min_lat + max_lat) / 2.0
    if _point_in_polygon(center_lon, center_lat, pts_array):
        return _bbox_corners(min_lon, max_lon, min_lat, max_lat)
    return []


def _append_clipped_polygon_feature(features, layer_key, pts_array, min_lon, max_lon, min_lat, max_lat, point_limit, max_features):
    clipped = _clip_polygon_to_bbox(pts_array, min_lon, max_lon, min_lat, max_lat)
    if len(clipped) < 3:
        return False
    clipped_array = np.array(clipped, dtype=float)
    return _append_feature(features, layer_key, "polygon", clipped_array, point_limit, max_features)


def _append_visible_gshhg_segments(features, layer_key, pts_array, min_lon, max_lon, min_lat, max_lat, point_limit, max_features):
    if len(pts_array) < 2:
        return False
    lon = pts_array[:, 0]
    lat = pts_array[:, 1]
    mask = (lon >= min_lon) & (lon <= max_lon) & (lat >= min_lat) & (lat <= max_lat)
    if len(mask) > 2:
        mask[1:] |= mask[:-1]
        mask[:-1] |= mask[1:]
    indices = np.flatnonzero(mask)
    if len(indices) == 0:
        return False

    breaks = np.where(np.diff(indices) > 1)[0] + 1
    for group in np.split(indices, breaks):
        if len(group) == 0:
            continue
        start = max(0, int(group[0]) - 2)
        end = min(len(pts_array), int(group[-1]) + 3)
        segment = pts_array[start:end]
        if len(segment) < 2:
            continue
        if _append_feature(features, layer_key, "line", segment, point_limit, max_features):
            return True
    return False


def viewport_spans(range_km, center_lat, viewport_width=1.0, viewport_height=1.0, padding=1.15):
    width = max(1.0, float(viewport_width or 1.0))
    height = max(1.0, float(viewport_height or 1.0))
    min_dim = max(1.0, min(width, height))
    horizontal_km = range_km * (width / min_dim)
    vertical_km = range_km * (height / min_dim)
    lat_span = math.degrees(vertical_km / tf.EARTH_RADIUS_KM) * padding
    lon_factor = max(0.05, math.cos(math.radians(center_lat)))
    lon_span = math.degrees(horizontal_km / (tf.EARTH_RADIUS_KM * lon_factor)) * padding
    return lat_span, lon_span


def vector_cache_bucket(range_km, center_lat, center_lon, viewport_width=1.0, viewport_height=1.0):
    lat_span, lon_span = viewport_spans(range_km, center_lat, viewport_width, viewport_height, padding=1.0)
    lat_step = max(0.01, lat_span / 4.0)
    lon_step = max(0.01, lon_span / 4.0)
    bucket_lat = round(round(center_lat / lat_step) * lat_step, 4)
    bucket_lon = round(round(center_lon / lon_step) * lon_step, 4)
    return bucket_lat, bucket_lon


def vector_cache_key(range_km, center_lat, center_lon, viewport_width=1.0, viewport_height=1.0, quick_fallback=False):
    bucket_lat, bucket_lon = vector_cache_bucket(range_km, center_lat, center_lon, viewport_width, viewport_height)
    layer_state = tuple(sorted((key, bool(value)) for key, value in tf.VECTOR_LAYERS_VISIBILITY.items()))
    return (
        round(float(range_km), 1),
        bucket_lat,
        bucket_lon,
        round(float(viewport_width or 1.0) / 100.0),
        round(float(viewport_height or 1.0) / 100.0),
        bool(quick_fallback),
        layer_state,
    )


def cached_vector_geodata(range_km, center_lat, center_lon, viewport_width=1.0, viewport_height=1.0, quick_fallback=False):
    key = vector_cache_key(range_km, center_lat, center_lon, viewport_width, viewport_height, quick_fallback)
    with VECTOR_GEODATA_CACHE_LOCK:
        cached = VECTOR_GEODATA_CACHE.get(key)
        if cached is not None:
            VECTOR_GEODATA_CACHE.move_to_end(key)
            return cached
    bucket_lat, bucket_lon = key[1], key[2]
    vectors = vector_geodata_uncached(range_km, bucket_lat, bucket_lon, viewport_width, viewport_height, quick_fallback)
    with VECTOR_GEODATA_CACHE_LOCK:
        VECTOR_GEODATA_CACHE[key] = vectors
        VECTOR_GEODATA_CACHE.move_to_end(key)
        while len(VECTOR_GEODATA_CACHE) > MAX_VECTOR_GEODATA_CACHE:
            VECTOR_GEODATA_CACHE.popitem(last=False)
    return vectors


def vector_geodata_uncached(range_km, center_lat, center_lon, viewport_width=1.0, viewport_height=1.0, quick_fallback=False):
    web_config = load_web_config()
    if not web_config.get("show_geo_vectors", True) or not tf.map_manager:
        return []
    high_detail_range_km = 100.0 * tf.NM_TO_KM
    overview_mode = range_km >= 700
    medium_overview_mode = high_detail_range_km < range_km < 420
    broad_overview_mode = 420 <= range_km < 700
    if overview_mode:
        max_features, max_points_per_feature = 620, 150
        coastline_points_per_feature = 180
        land_points_per_feature = 180
    elif medium_overview_mode:
        max_features, max_points_per_feature = 980, 220
        coastline_points_per_feature = 520
        land_points_per_feature = 340
    elif broad_overview_mode:
        max_features, max_points_per_feature = 620, 130
        coastline_points_per_feature = 180
        land_points_per_feature = 120
    elif range_km <= high_detail_range_km:
        max_features = 4200
        max_points_per_feature = 5200 if range_km <= 45 else 3600
        coastline_points_per_feature = 28000 if range_km <= 45 else 18000
        land_points_per_feature = 18000 if range_km <= 45 else 12000
    elif range_km <= 320:
        max_features, max_points_per_feature = 2600, 2200
        coastline_points_per_feature = 9000
        land_points_per_feature = 6800
    else:
        max_features, max_points_per_feature = 1600, 1100
        coastline_points_per_feature = 3600
        land_points_per_feature = 2800
    if quick_fallback:
        max_features = min(max_features, 700 if range_km <= 320 else 420)
        max_points_per_feature = min(max_points_per_feature, 450 if range_km <= 320 else 260)
        coastline_points_per_feature = min(coastline_points_per_feature, 900 if range_km <= 320 else 520)
        land_points_per_feature = min(land_points_per_feature, 500 if range_km <= 320 else 260)
    allow_land_fill = range_km <= high_detail_range_km or quick_fallback or overview_mode or medium_overview_mode or broad_overview_mode
    lat_span, lon_span = viewport_spans(range_km, center_lat, viewport_width, viewport_height, padding=2.8)
    min_lat, max_lat = center_lat - lat_span, center_lat + lat_span
    min_lon, max_lon = center_lon - lon_span, center_lon + lon_span
    segment_min_lat, segment_max_lat = center_lat - lat_span * 1.8, center_lat + lat_span * 1.8
    segment_min_lon, segment_max_lon = center_lon - lon_span * 1.8, center_lon + lon_span * 1.8
    fill_min_lat, fill_max_lat = center_lat - lat_span * 4.0, center_lat + lat_span * 4.0
    fill_min_lon, fill_max_lon = center_lon - lon_span * 4.0, center_lon + lon_span * 4.0
    features = []
    layer_feature_counts = {}
    layer_items = list(tf.VECTOR_LAYERS_VISIBILITY.items())
    urban_visible = bool(tf.VECTOR_LAYERS_VISIBILITY.get("ne_10m_urban_areas"))
    if urban_visible:
        load_vector_layer("ne_10m_urban_areas")
        if "ne_10m_urban_areas" in tf.map_manager.layers_data:
            layer_items = (
                [(key, visible) for key, visible in layer_items if key == "gshhs_h_land_fill"]
                + [("ne_10m_urban_areas", True)]
                + [
                    (key, visible)
                    for key, visible in layer_items
                    if key not in {"gshhs_h_land_fill", "ne_10m_urban_areas"}
                ]
            )
    if quick_fallback:
        quick_items = [(key, True) for key in QUICK_VECTOR_LAYERS if key in tf.map_manager.layers_data]
        seen = {key for key, _visible in quick_items}
        layer_items = quick_items + [
            (key, visible)
            for key, visible in layer_items
            if key not in seen and not key.startswith("gshhs_") and key != "ne_10m_urban_areas"
        ]
    elif overview_mode:
        overview_layers = (
            "gshhs_h_land_fill",
            "ne_10m_admin_0_boundary_lines_land",
            "ne_10m_lakes",
        )
        layer_items = [
            (key, True)
            for key in overview_layers
            if key in tf.map_manager.layers_data and (key != "ne_10m_urban_areas" or urban_visible)
        ]
    elif broad_overview_mode:
        overview_layers = (
            "gshhs_h_land_fill",
            "ne_10m_admin_0_boundary_lines_land",
            "ne_10m_lakes",
        )
        layer_items = [
            (key, True)
            for key in overview_layers
            if key in tf.map_manager.layers_data and (key != "ne_10m_urban_areas" or urban_visible)
        ]
    elif medium_overview_mode:
        overview_layers = (
            "gshhs_h_land_fill",
            "gshhs_h_coastline",
            "ne_10m_admin_0_boundary_lines_land",
            "ne_10m_lakes",
        )
        layer_items = [
            (key, True)
            for key in overview_layers
            if key in tf.map_manager.layers_data and (key != "ne_10m_urban_areas" or urban_visible)
        ]
    for layer_key, visible in layer_items:
        if not visible or layer_key not in tf.map_manager.layers_data:
            continue
        cfg = tf.VECTOR_LAYER_CONFIGS.get(layer_key, {})
        is_gshhg = layer_key.startswith("gshhs_")
        is_gshhg_fill = layer_key.endswith("_land_fill")
        is_gshhg_coastline = layer_key.endswith("_coastline")
        is_urban = layer_key == "ne_10m_urban_areas"
        layer_type = cfg.get("type", "line")
        if (quick_fallback or (overview_mode and not is_gshhg_fill)) and is_gshhg:
            continue
        if quick_fallback and layer_type == "polygon" and layer_key not in {"ne_10m_lakes"}:
            continue
        if layer_type == "polygon" and not allow_land_fill:
            continue
        for pts_array, bbox in tf.map_manager.layers_data[layer_key]:
            if is_gshhg_fill:
                if bbox[1] < fill_min_lon or bbox[0] > fill_max_lon or bbox[3] < fill_min_lat or bbox[2] > fill_max_lat:
                    continue
            elif is_gshhg_coastline:
                if bbox[1] < segment_min_lon or bbox[0] > segment_max_lon or bbox[3] < segment_min_lat or bbox[2] > segment_max_lat:
                    continue
            elif bbox[1] < min_lon or bbox[0] > max_lon or bbox[3] < min_lat or bbox[2] > max_lat:
                continue
            is_land_area = is_gshhg or any(token in layer_key for token in ("land", "ocean", "countries", "minor_islands", "geography_regions"))
            if "coastline" in layer_key or is_gshhg:
                point_limit = coastline_points_per_feature * (2 if is_gshhg and range_km <= high_detail_range_km else 1)
            elif quick_fallback and "boundary" in layer_key:
                point_limit = max(60, min(max_points_per_feature, 180 if range_km <= 320 else 110))
            elif is_land_area or is_urban:
                point_limit = land_points_per_feature
            else:
                point_limit = max_points_per_feature
            before_feature_count = len(features)
            if is_gshhg_fill:
                if layer_feature_counts.get(layer_key, 0) >= max_features // 2:
                    continue
                done = _append_clipped_polygon_feature(
                    features,
                    layer_key,
                    pts_array,
                    fill_min_lon,
                    fill_max_lon,
                    fill_min_lat,
                    fill_max_lat,
                    coastline_points_per_feature,
                    max_features,
                )
            elif is_gshhg_coastline:
                done = _append_visible_gshhg_segments(
                    features,
                    layer_key,
                    pts_array,
                    segment_min_lon,
                    segment_max_lon,
                    segment_min_lat,
                    segment_max_lat,
                    point_limit,
                    max_features,
                )
            elif is_gshhg:
                done = _append_visible_gshhg_segments(
                    features,
                    layer_key,
                    pts_array,
                    segment_min_lon,
                    segment_max_lon,
                    segment_min_lat,
                    segment_max_lat,
                    point_limit,
                    max_features,
                )
            else:
                done = _append_feature(features, layer_key, cfg.get("type", "line"), pts_array, point_limit, max_features)
            if len(features) > before_feature_count:
                layer_feature_counts[layer_key] = layer_feature_counts.get(layer_key, 0) + (len(features) - before_feature_count)
            if done:
                return features
            if len(features) >= max_features:
                return features
    return features


def nearby_geodata(range_km, center_lat, center_lon, viewport_width=1.0, viewport_height=1.0, max_items=350, include_vectors=True, quick_vector_fallback=False):
    web_config = load_web_config()
    lat_span, lon_span = viewport_spans(range_km, center_lat, viewport_width, viewport_height, padding=2.0)
    min_lat, max_lat = center_lat - lat_span, center_lat + lat_span
    min_lon, max_lon = center_lon - lon_span, center_lon + lon_span

    if range_km >= 700:
        airport_max_items = min(max_items, 70)
        airport_types = {"large_airport"}
        include_navaids = False
        include_runways = True
    elif range_km >= 420:
        airport_max_items = min(max_items, 110)
        airport_types = {"large_airport"}
        include_navaids = False
        include_runways = True
    elif range_km >= 260:
        airport_max_items = min(max_items, 220)
        airport_types = {"large_airport"}
        include_navaids = True
        include_runways = True
    else:
        airport_max_items = max_items
        airport_types = None
        include_navaids = True
        include_runways = True

    airports = [
        apt
        for apt in tf.airports_data
        if min_lat <= apt["lat"] <= max_lat
        and min_lon <= apt["lon"] <= max_lon
        and (airport_types is None or apt.get("type") in airport_types)
    ][:airport_max_items]
    navaids = [] if not include_navaids else [
        nav
        for nav in tf.navaids_data
        if min_lat <= nav["lat"] <= max_lat and min_lon <= nav["lon"] <= max_lon
    ][:max_items]
    runways = []
    if include_runways:
        for apt in airports[:120]:
            for idx, rwy in enumerate(tf.runways_data.get(apt["ident"], [])[:12]):
                runways.append({"airport": apt["ident"], "runway_index": idx, **rwy})
    return {
        "airports": airports,
        "navaids": navaids,
        "runways": runways,
        "vectors": cached_vector_geodata(range_km, center_lat, center_lon, viewport_width, viewport_height, quick_fallback=quick_vector_fallback) if include_vectors else [],
        "contours": [],
    }


def glideslope_snapshot():
    web_config = load_web_config()
    output = []
    length_km = float(web_config.get("ils_length_nm", "10")) * tf.NM_TO_KM
    for item in web_config.get("active_glideslopes", []):
        try:
            airport = item.get("airport")
            end = item.get("end")
            runway_index = int(item.get("runway_index", 0))
            airport_data = next((apt for apt in tf.airports_data if apt.get("ident") == airport), None)
            runway = tf.runways_data.get(airport, [])[runway_index]
            details = tf.calculate_glideslope_details(runway, end, airport_data.get("type") if airport_data else "medium_airport")
            if details:
                details["length_km"] = length_km
                details["end_lat"], details["end_lon"] = tf.destination_point(
                    details["start_lat"],
                    details["start_lon"],
                    details["bearing_deg"],
                    length_km,
                )
                output.append({"airport": airport, "runway_index": runway_index, **details})
        except Exception:
            continue
    return output


def moon_phase_name(phase_angle_deg):
    angle = phase_angle_deg % 360.0
    if angle < 22.5 or angle >= 337.5:
        return "New Moon"
    if angle < 67.5:
        return "Waxing Crescent"
    if angle < 112.5:
        return "First Quarter"
    if angle < 157.5:
        return "Waxing Gibbous"
    if angle < 202.5:
        return "Full Moon"
    if angle < 247.5:
        return "Waning Gibbous"
    if angle < 292.5:
        return "Last Quarter"
    return "Waning Crescent"


def moon_phase_snapshot(t_now, sun_app, moon_app):
    elongation_deg = sun_app.separation_from(moon_app).degrees
    illumination = (1.0 - math.cos(math.radians(elongation_deg))) / 2.0
    illumination = max(0.0, min(1.0, illumination))
    try:
        _, sun_lon, _ = sun_app.frame_latlon(ecliptic_frame)
        _, moon_lon, _ = moon_app.frame_latlon(ecliptic_frame)
        phase_angle_deg = (moon_lon.degrees - sun_lon.degrees) % 360.0
    except Exception:
        phase_angle_deg = elongation_deg
    synodic_month_days = 29.530588853
    return {
        "name": moon_phase_name(phase_angle_deg),
        "illumination": illumination,
        "illumination_percent": illumination * 100.0,
        "phase_angle_deg": phase_angle_deg,
        "elongation_deg": elongation_deg,
        "age_days": phase_angle_deg / 360.0 * synodic_month_days,
        "waxing": phase_angle_deg < 180.0,
    }


def transit_snapshot(mode, selected_icao, aircraft):
    if mode == "none" or not tf.eph:
        return []
    if mode == "all":
        icaos = [ac["icao"] for ac in aircraft if ac.get("visible") and not ac.get("grounded")][:20]
    elif selected_icao:
        icaos = [selected_icao]
    else:
        icaos = []

    output = []
    now = utc_now()
    for icao in icaos:
        try:
            data = tf.calculate_transit_rectangle_for_aircraft(icao, now)
        except Exception:
            continue
        for body in ("sun", "moon"):
            if data.get(body):
                output.append({"icao": icao, "body": body, **data[body]})
    return output


def celestial_snapshot():
    if not (tf.eph and tf.observer_topos and tf.ts):
        return None
    try:
        t_now = tf.ts.now()
        user_obs = tf.eph["earth"] + tf.observer_topos
        sun_app = user_obs.at(t_now).observe(tf.eph["sun"]).apparent()
        moon_app = user_obs.at(t_now).observe(tf.eph["moon"]).apparent()
        sun_alt, sun_az, _ = sun_app.altaz()
        moon_alt, moon_az, _ = moon_app.altaz()
        return {
            "sun": {"az": sun_az.degrees, "el": sun_alt.degrees},
            "moon": {
                "az": moon_az.degrees,
                "el": moon_alt.degrees,
                "phase": moon_phase_snapshot(t_now, sun_app, moon_app),
            },
        }
    except Exception:
        return None


def state_cache_signature(request):
    return (
        round(float(request["range_km"]), 3),
        round(float(request["center_lat"]), 5),
        round(float(request["center_lon"]), 5),
        round(float(request.get("viewport_width", 1.0)), 0),
        round(float(request.get("viewport_height", 1.0)), 0),
        request["selected_icao"],
        request["transit_mode"],
    )


def map_cache_signature(request):
    web_config = load_web_config()
    layer_state = tuple(sorted((key, bool(value)) for key, value in tf.VECTOR_LAYERS_VISIBILITY.items()))
    return (
        round(float(request["range_km"]), 3),
        round(float(request["center_lat"]), 5),
        round(float(request["center_lon"]), 5),
        round(float(request.get("viewport_width", 1.0)), 0),
        round(float(request.get("viewport_height", 1.0)), 0),
        bool(web_config.get("show_geo_vectors", True)),
        layer_state,
    )


def normalize_client_id(raw):
    value = str(raw or DEFAULT_CLIENT_ID)[:48]
    clean = "".join(ch for ch in value if ch.isalnum() or ch in ("-", "_"))
    return clean or DEFAULT_CLIENT_ID


def client_state_cache(client_id):
    cache = CLIENT_STATE_CACHES.get(client_id)
    if cache is None:
        cache = new_state_cache()
        CLIENT_STATE_CACHES[client_id] = cache
    cache["last_access"] = time.monotonic()
    if len(CLIENT_STATE_CACHES) > MAX_CLIENT_STATE_CACHES:
        stale_ids = sorted(
            (item for item in CLIENT_STATE_CACHES.items() if item[0] != DEFAULT_CLIENT_ID),
            key=lambda item: item[1].get("last_access", 0.0),
        )
        for stale_id, _cache in stale_ids[: max(0, len(CLIENT_STATE_CACHES) - MAX_CLIENT_STATE_CACHES)]:
            CLIENT_STATE_CACHES.pop(stale_id, None)
            STATE_CACHE_REQUESTS.pop(stale_id, None)
    return cache


def request_state_cache_update(client_id, range_km, center_lat, center_lon, viewport_width, viewport_height, selected_icao, transit_mode):
    with STATE_CACHE_LOCK:
        client_state_cache(client_id)
        STATE_CACHE_REQUESTS[client_id] = {
            "range_km": range_km,
            "center_lat": center_lat,
            "center_lon": center_lon,
            "viewport_width": viewport_width,
            "viewport_height": viewport_height,
            "selected_icao": selected_icao,
            "transit_mode": transit_mode,
        }
    MAP_CACHE_EVENT.set()


def cached_state_fields(signature, client_id=DEFAULT_CLIENT_ID, map_signature=None):
    if map_signature is None:
        map_signature = signature
    with STATE_CACHE_LOCK:
        client_cache = client_state_cache(client_id)
        cache = {
            "events": STATE_CACHE["events"],
            "transits": client_cache["transits"],
            "geodata": client_cache["geodata"],
            "glideslopes": client_cache["glideslopes"],
            "celestial": STATE_CACHE["celestial"],
            "cache": {
                "aircraft_pending": client_cache["aircraft_signature"] != signature,
                "map_pending": client_cache["map_signature"] != map_signature,
                "aircraft_updated": client_cache["aircraft_updated"].isoformat() if client_cache["aircraft_updated"] else None,
                "map_updated": client_cache["map_updated"].isoformat() if client_cache["map_updated"] else None,
                "transits_updated": client_cache["transits_updated"].isoformat() if client_cache["transits_updated"] else None,
                "events_updated": STATE_CACHE["events_updated"].isoformat() if STATE_CACHE["events_updated"] else None,
            },
        }
    return cache


def set_event_prediction_paused(paused):
    tf.EVENT_PREDICTION_PAUSED = bool(paused)
    return {
        "ok": True,
        "event_prediction_paused": tf.EVENT_PREDICTION_PAUSED,
    }


def event_cache_worker():
    last_event_refresh = 0.0
    while tf.running:
        if getattr(tf, "EVENT_PREDICTION_PAUSED", False):
            time.sleep(0.1)
            continue
        now_monotonic = time.monotonic()
        event_interval = max(0.2, float(getattr(tf, "PREDICTION_INTERVAL", 1.0) or 1.0))
        if now_monotonic - last_event_refresh >= event_interval:
            events = events_snapshot()
            celestial = celestial_snapshot()
            with STATE_CACHE_LOCK:
                STATE_CACHE["events"] = events
                STATE_CACHE["celestial"] = celestial
                STATE_CACHE["events_updated"] = utc_now()
            last_event_refresh = now_monotonic
        time.sleep(max(0.1, event_interval - (time.monotonic() - last_event_refresh)))


def map_cache_worker():
    while tf.running:
        MAP_CACHE_EVENT.wait(timeout=0.2)
        MAP_CACHE_EVENT.clear()
        with STATE_CACHE_LOCK:
            requests = list(STATE_CACHE_REQUESTS.items())
        for client_id, request in requests:
            with STATE_CACHE_LOCK:
                client_cache = client_state_cache(client_id)
                current_map_signature = client_cache["map_signature"]
                current_transit_signature = client_cache["transit_signature"]
                current_aircraft_signature = client_cache["aircraft_signature"]
                last_transit_update = client_cache["transits_updated_monotonic"]
                last_aircraft_update = client_cache["aircraft_updated_monotonic"]
            signature = state_cache_signature(request)
            map_signature = map_cache_signature(request)
            now_monotonic = time.monotonic()
            web_config = load_web_config()
            aircraft_interval = aircraft_refresh_seconds(web_config)
            aircraft = None
            if signature != current_aircraft_signature or now_monotonic - last_aircraft_update >= aircraft_interval:
                aircraft = aircraft_snapshot(
                    request["range_km"],
                    request["center_lat"],
                    request["center_lon"],
                    web_config,
                    request.get("viewport_width", 1.0),
                    request.get("viewport_height", 1.0),
                )
                with STATE_CACHE_LOCK:
                    client_cache = client_state_cache(client_id)
                    client_cache["aircraft_signature"] = signature
                    client_cache["aircraft"] = aircraft
                    client_cache["aircraft_updated"] = utc_now()
                    client_cache["aircraft_updated_monotonic"] = now_monotonic
            transit_interval = 0.75 if request["transit_mode"] == "all" else 0.35
            if map_signature != current_map_signature:
                if current_map_signature is None:
                    fast_geodata = nearby_geodata(
                        request["range_km"],
                        request["center_lat"],
                        request["center_lon"],
                        request.get("viewport_width", 1.0),
                        request.get("viewport_height", 1.0),
                        include_vectors=False,
                    )
                    fast_glideslopes = glideslope_snapshot()
                    with STATE_CACHE_LOCK:
                        client_cache = client_state_cache(client_id)
                        if client_cache["map_signature"] != map_signature:
                            client_cache["geodata"] = fast_geodata
                            client_cache["glideslopes"] = fast_glideslopes
                            client_cache["map_updated"] = utc_now()
                    ensure_quick_vector_layers_loaded()
                    quick_geodata = nearby_geodata(
                        request["range_km"],
                        request["center_lat"],
                        request["center_lon"],
                        request.get("viewport_width", 1.0),
                        request.get("viewport_height", 1.0),
                        quick_vector_fallback=True,
                    )
                    with STATE_CACHE_LOCK:
                        client_cache = client_state_cache(client_id)
                        if client_cache["map_signature"] != map_signature:
                            client_cache["geodata"] = quick_geodata
                            client_cache["glideslopes"] = fast_glideslopes
                            client_cache["map_updated"] = utc_now()
                start_high_vector_load()
                geodata = nearby_geodata(
                    request["range_km"],
                    request["center_lat"],
                    request["center_lon"],
                    request.get("viewport_width", 1.0),
                    request.get("viewport_height", 1.0),
                )
                glideslopes = glideslope_snapshot()
                with STATE_CACHE_LOCK:
                    client_cache = client_state_cache(client_id)
                    client_cache["map_signature"] = map_signature
                    client_cache["geodata"] = geodata
                    client_cache["glideslopes"] = glideslopes
                    client_cache["map_updated"] = utc_now()
            if (
                request["transit_mode"] != "none"
                and (
                    signature != current_transit_signature
                    or now_monotonic - last_transit_update >= transit_interval
                )
            ):
                if aircraft is None:
                    with STATE_CACHE_LOCK:
                        aircraft = list(client_state_cache(client_id)["aircraft"])
                transits = transit_snapshot(request["transit_mode"], request["selected_icao"], aircraft or [])
                with STATE_CACHE_LOCK:
                    client_cache = client_state_cache(client_id)
                    client_cache["transit_signature"] = signature
                    client_cache["transits"] = transits
                    client_cache["transits_updated"] = utc_now()
                    client_cache["transits_updated_monotonic"] = now_monotonic
            elif request["transit_mode"] == "none":
                with STATE_CACHE_LOCK:
                    client_cache = client_state_cache(client_id)
                    if client_cache["transits"]:
                        client_cache["transit_signature"] = signature
                        client_cache["transits"] = []
                        client_cache["transits_updated"] = utc_now()
                        client_cache["transits_updated_monotonic"] = now_monotonic


def build_state(query):
    config = tf.load_config(tf.config_file_full_path)
    web_config = filtered_web_config_for_runtime(load_web_config(), config)
    detail = query.get("detail", ["full"])[0]
    if detail not in {"full", "light"}:
        detail = "full"
    range_km = finite_float(query.get("range_km", [tf.INITIAL_MAP_RANGE_KM])[0], tf.INITIAL_MAP_RANGE_KM)
    range_km = max(tf.MIN_MAP_RANGE_KM, min(tf.MAX_MAP_RANGE_KM, range_km))
    center_lat = finite_float(query.get("center_lat", [tf.USER_LAT])[0], tf.USER_LAT)
    center_lon = finite_float(query.get("center_lon", [tf.USER_LON])[0], tf.USER_LON)
    viewport_width = max(1.0, finite_float(query.get("viewport_width", [1.0])[0], 1.0))
    viewport_height = max(1.0, finite_float(query.get("viewport_height", [1.0])[0], 1.0))
    selected_icao = (query.get("selected", [""])[0] or "").upper()[:6]
    transit_mode = query.get("transits", ["selected"])[0]
    client_id = normalize_client_id(query.get("client", [DEFAULT_CLIENT_ID])[0])
    if transit_mode not in {"none", "selected", "all"}:
        transit_mode = "selected"
    request_state_cache_update(client_id, range_km, center_lat, center_lon, viewport_width, viewport_height, selected_icao, transit_mode)
    cache_signature = state_cache_signature(
        {
            "range_km": range_km,
            "center_lat": center_lat,
            "center_lon": center_lon,
            "viewport_width": viewport_width,
            "viewport_height": viewport_height,
            "selected_icao": selected_icao,
            "transit_mode": transit_mode,
        }
    )
    map_signature = map_cache_signature(
        {
            "range_km": range_km,
            "center_lat": center_lat,
            "center_lon": center_lon,
            "viewport_width": viewport_width,
            "viewport_height": viewport_height,
        }
    )

    with STATE_CACHE_LOCK:
        client_cache = client_state_cache(client_id)
        cached_aircraft = list(client_cache["aircraft"])
        aircraft_pending = client_cache["aircraft_signature"] != cache_signature
        last_aircraft_update = client_cache["aircraft_updated_monotonic"]
    aircraft_cache_stale = time.monotonic() - last_aircraft_update >= aircraft_refresh_seconds(web_config)
    if detail == "light" and (aircraft_pending or aircraft_cache_stale):
        aircraft = aircraft_snapshot(range_km, center_lat, center_lon, web_config, viewport_width, viewport_height)
        with STATE_CACHE_LOCK:
            client_cache = client_state_cache(client_id)
            client_cache["aircraft_signature"] = cache_signature
            client_cache["aircraft"] = aircraft
            client_cache["aircraft_updated"] = utc_now()
            client_cache["aircraft_updated_monotonic"] = time.monotonic()
        aircraft_pending = False
    elif cached_aircraft:
        aircraft = cached_aircraft
    else:
        aircraft = aircraft_snapshot(range_km, center_lat, center_lon, web_config, viewport_width, viewport_height)
        aircraft_pending = False
    active_total = len(aircraft)
    active_no_pos = len([ac for ac in aircraft if ac["lat"] is None or ac["lon"] is None])

    state = {
        "server_time": utc_now().isoformat(),
        "runtime_sec": (utc_now() - SERVER_START).total_seconds(),
        "settings": {
            "dump1090_host": tf.HOST,
            "dump1090_port": tf.PORT,
            "dump1090_json_url": tf.DUMP1090_JSON_URL,
            "geoid": tf.GEOID_STATUS.copy(),
            "connected": tf.DUMP1090_CONNECTED,
            "user": {"lat": tf.USER_LAT, "lon": tf.USER_LON, "alt_m": tf.USER_ALT},
            "center": {"lat": center_lat, "lon": center_lon},
            "range_km": range_km,
            "conflict_angle_deg": tf.CONFLICT_ANGLE_DEG,
            "event_min_elevation_deg": tf.EVENT_MIN_ELEVATION_DEG,
            "prediction_interval_sec": tf.PREDICTION_INTERVAL,
            "prediction_horizon_sec": tf.PREDICTION_HORIZON,
            "prediction_average_sec": tf.PREDICTION_AVERAGE_SEC,
            "velocity_vector_minutes": tf.VELOCITY_VECTOR_MINUTES,
            "history_minutes": tf.AIRCRAFT_HISTORY_MINUTES,
            "show_history": tf.SHOW_AIRCRAFT_HISTORY,
            "show_events": tf.SHOW_EVENT_LOCATIONS,
            "show_glideslope": tf.SHOW_GLIDESLOPE,
            "show_range_rings": tf.SHOW_RANGE_RINGS,
            "range_ring_spacing_km": tf.RANGE_RING_SPACING_KM,
            "max_range_rings": tf.MAX_RANGE_RINGS,
            "show_velocity_vector": tf.SHOW_VELOCITY_VECTOR,
            "show_all_transit_strips": tf.SHOW_ALL_TRANSIT_STRIPS,
            "conflict_radius_km": tf.CONFLICT_RADIUS_KM,
            "web": web_config,
        },
        "counts": {
            "active_total": active_total,
            "active_no_pos": active_no_pos,
            "displayed": len([ac for ac in aircraft if ac.get("visible")]),
            "events": len(tf.event_dict),
            "history_events": tf.history_event_count,
        },
        "aircraft": aircraft,
        "events": [],
        "transits": [],
        "geodata": {"airports": [], "navaids": [], "runways": [], "vectors": []},
        "glideslopes": [],
        "celestial": None,
        "cache": {"aircraft_pending": aircraft_pending, "map_pending": detail == "full", "map_updated": None, "events_updated": None},
    }
    if detail == "full":
        state.update(cached_state_fields(cache_signature, client_id, map_signature=map_signature))
        if state["cache"].get("map_pending"):
            cached_geodata = state.get("geodata") or {}
            has_cached_map = any(isinstance(cached_geodata.get(key), list) and cached_geodata.get(key) for key in ("vectors", "airports", "navaids", "runways", "contours"))
            if not has_cached_map and range_km < 700:
                ensure_quick_vector_layers_loaded()
                state["geodata"] = nearby_geodata(
                    range_km,
                    center_lat,
                    center_lon,
                    viewport_width,
                    viewport_height,
                    quick_vector_fallback=True,
                )
        if transit_mode == "none" or (transit_mode == "selected" and not selected_icao):
            state["transits"] = []
        elif transit_mode == "selected" and selected_icao:
            state["transits"] = transit_snapshot("selected", selected_icao, aircraft)
            with STATE_CACHE_LOCK:
                client_cache = client_state_cache(client_id)
                client_cache["transit_signature"] = cache_signature
                client_cache["transits"] = state["transits"]
                client_cache["transits_updated"] = utc_now()
                client_cache["transits_updated_monotonic"] = time.monotonic()
    else:
        cached = cached_state_fields(cache_signature, client_id, map_signature=map_signature)
        state["events"] = cached["events"]
        state["celestial"] = cached["celestial"]
        state["transits"] = cached["transits"]
        state["cache"] = cached["cache"]
    return state


class WebHandler(BaseHTTPRequestHandler):
    server_version = "ADSBTransitWeb/0.1"

    def log_message(self, fmt, *args):
        print(f"[web] {self.address_string()} - {fmt % args}")

    def send_bytes(self, status, content_type, body, extra_headers=None):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        if extra_headers:
            for key, value in extra_headers.items():
                self.send_header(key, value)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, status, payload):
        body = json.dumps(payload, default=json_default, separators=(",", ":")).encode("utf-8")
        headers = None
        if len(body) > 4096 and "gzip" in self.headers.get("Accept-Encoding", ""):
            body = gzip.compress(body, compresslevel=5)
            headers = {"Content-Encoding": "gzip", "Vary": "Accept-Encoding"}
        self.send_bytes(status, "application/json; charset=utf-8", body, headers)

    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/api/state":
            self.send_json(200, build_state(parse_qs(parsed.query)))
            return
        if parsed.path == "/api/config":
            self.send_json(200, public_config())
            return
        if parsed.path == "/api/elevation":
            self.send_json(410, {"ok": False, "error": "Terrain and elevation API is disabled in this release build."})
            return
        if parsed.path == "/api/health":
            self.send_json(200, {"ok": True, "connected": tf.DUMP1090_CONNECTED})
            return

        if parsed.path == "/api/metar":
            with tf.METAR_LOCK:
                state = tf.METAR_STATE.copy()
            fetched_at = state.get("fetched_at")
            if fetched_at is not None:
                state["fetched_at"] = fetched_at.isoformat()
            observed_at = state.get("observed_at")
            if observed_at is not None:
                state["age_sec"] = round((datetime.now(timezone.utc) - observed_at).total_seconds())
                state["observed_at"] = observed_at.isoformat()
            state["mode"] = tf.ALT_CORRECTION_MODE
            state["manual_temp_c"] = tf.ALT_CORRECTION_MANUAL_TEMP_C
            state["manual_qnh_hpa"] = tf.ALT_CORRECTION_MANUAL_QNH_HPA
            state["max_airport_km"] = tf.METAR_MAX_AIRPORT_KM
            self.send_json(200, state)
            return

        if parsed.path.startswith("/assets/"):
            rel_path = parsed.path[len("/assets/"):]
            candidate = (ASSETS_DIR / rel_path).resolve()
            if not str(candidate).startswith(str(ASSETS_DIR.resolve())) or not candidate.is_file():
                self.send_json(404, {"error": "not found"})
                return
            content_type = "application/octet-stream"
            if candidate.suffix.lower() == ".png":
                content_type = "image/png"
            elif candidate.suffix.lower() in {".jpg", ".jpeg"}:
                content_type = "image/jpeg"
            elif candidate.suffix.lower() == ".svg":
                content_type = "image/svg+xml; charset=utf-8"
            self.send_bytes(200, content_type, candidate.read_bytes())
            return

        rel_path = "index.html" if parsed.path in {"/", ""} else parsed.path.lstrip("/")
        candidate = (STATIC_DIR / rel_path).resolve()
        if not str(candidate).startswith(str(STATIC_DIR.resolve())) or not candidate.is_file():
            self.send_json(404, {"error": "not found"})
            return
        content_type = "text/plain; charset=utf-8"
        if candidate.suffix == ".html":
            content_type = "text/html; charset=utf-8"
        elif candidate.suffix == ".css":
            content_type = "text/css; charset=utf-8"
        elif candidate.suffix == ".js":
            content_type = "application/javascript; charset=utf-8"
        self.send_bytes(200, content_type, candidate.read_bytes())

    def do_POST(self):
        parsed = urlparse(self.path)
        if parsed.path not in {"/api/config", "/api/interaction", "/api/metar"}:
            self.send_json(404, {"error": "not found"})
            return
        try:
            length = safe_int(self.headers.get("Content-Length"), 0)
            payload = json.loads(self.rfile.read(length).decode("utf-8")) if length else {}
            if parsed.path == "/api/interaction":
                self.send_json(200, set_event_prediction_paused(payload.get("pause_events", False)))
                return
            if parsed.path == "/api/metar":
                # Trigger immediate fetch in background worker, return instantly
                tf.METAR_REFRESH_EVENT.set()
                self.send_json(200, {"ok": True, "fetching": True})
                return
            update_config_from_payload(payload)
            response = public_config()
            response["ok"] = True
            self.send_json(200, response)
        except Exception as exc:
            self.send_json(400, {"ok": False, "error": str(exc)})


class QuietThreadingHTTPServer(ThreadingHTTPServer):
    def handle_error(self, request, client_address):
        exc_type, exc, _ = sys.exc_info()
        if exc_type and issubclass(exc_type, (ConnectionResetError, BrokenPipeError)):
            return
        if exc_type and issubclass(exc_type, ssl.SSLError):
            print(f"[web] {client_address[0]}:{client_address[1]} - TLS handshake closed: {exc}")
            return
        super().handle_error(request, client_address)


def main():
    parser = argparse.ArgumentParser(description="ADS-B Transit Predictor Web UI")
    parser.add_argument("--host", default="0.0.0.0", help="Bind address. Use 0.0.0.0 for Tailscale/LAN access.")
    parser.add_argument("--port", default=8080, type=int, help="HTTP port.")
    parser.add_argument("--https", action="store_true", help="Serve over HTTPS with a local certificate.")
    parser.add_argument("--certfile", default=str(CERT_DIR / "adsb-web.crt"), help="HTTPS certificate path.")
    parser.add_argument("--keyfile", default=str(CERT_DIR / "adsb-web.key"), help="HTTPS private key path.")
    parser.add_argument("--start-dump1090", action="store_true", help="Try to start bundled dump1090 before listening.")
    args = parser.parse_args()

    server = QuietThreadingHTTPServer((args.host, args.port), WebHandler)
    scheme = "https" if args.https else "http"
    if args.https:
        certfile, keyfile = ensure_self_signed_cert(args.certfile, args.keyfile)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(certfile=certfile, keyfile=keyfile)
        server.socket = context.wrap_socket(server.socket, server_side=True, do_handshake_on_connect=False)
    start_processing_threads(start_dump1090=args.start_dump1090)
    local_url = f"{scheme}://127.0.0.1:{args.port}/"
    bind_url = f"{scheme}://{args.host}:{args.port}/" if args.host != "0.0.0.0" else f"{scheme}://<tailscale-ip>:{args.port}/"
    tail_ip = get_tailscale_ip()
    print(f"[web] ADS-B Transit Web UI: {local_url}")
    print(f"[web] Remote URL: {scheme}://{tail_ip}:{args.port}/" if tail_ip else f"[web] Remote URL: {bind_url}")
    if args.https:
        print("[web] HTTPS uses a local self-signed certificate; accept the browser warning on first visit.")
    print("[web] Press Ctrl+C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        tf.running = False
        server.server_close()
        if tf.dump1090_process and tf.dump1090_process.poll() is None:
            tf.dump1090_process.terminate()


if __name__ == "__main__":
    main()
