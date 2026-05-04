#!/usr/bin/env python3
import argparse
import json
import math
import os
import socket
import subprocess
import ssl
import sys
import threading
import time
from collections import deque
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT_DIR = Path(__file__).resolve().parents[1]
STATIC_DIR = Path(__file__).resolve().parent / "static"
WEB_CONFIG_PATH = ROOT_DIR / "web_ui_config.json"
CERT_DIR = ROOT_DIR / ".web_certs"
sys.path.insert(0, str(ROOT_DIR))

import transit_finder as tf  # noqa: E402


SERVER_START = datetime.now(timezone.utc)
THREADS_STARTED = False
GEODATA_READY = False
CONFIG_LOCK = threading.Lock()
DEFAULT_WEB_CONFIG = {
    "visual_style": "current",
    "aircraft_label_fields": ["callsign", "altitude", "speed", "vs"],
    "aircraft_label_lines": [["callsign"], ["altitude", "speed", "vs"]],
    "ils_style": "atc",
    "ils_length_nm": "10",
    "aircraft_label_color": "aircraft",
    "unit_distance": "km",
    "unit_speed": "kt",
    "unit_altitude": "ft",
    "trajectory_minutes": 2.0,
    "trajectory_display_mode": "altitude",
    "show_geo_vectors": True,
    "show_event_range_ring": True,
    "active_glideslopes": [],
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
    if config["visual_style"] not in {"current", "desktop", "atc"}:
        config["visual_style"] = "current"
    allowed_fields = {"callsign", "icao", "distance", "altitude", "speed", "track", "vs", "squawk"}
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
    if config["unit_distance"] not in {"km", "nm", "mi"}:
        config["unit_distance"] = "km"
    if config["unit_speed"] not in {"kt", "kmh", "mph"}:
        config["unit_speed"] = "kt"
    if config["unit_altitude"] not in {"ft", "m"}:
        config["unit_altitude"] = "ft"
    config["trajectory_minutes"] = finite_float(config.get("trajectory_minutes"), 2.0)
    if config["trajectory_minutes"] is None or config["trajectory_minutes"] <= 0:
        config["trajectory_minutes"] = 2.0
    if config.get("trajectory_display_mode") not in {"altitude", "points"}:
        config["trajectory_display_mode"] = "altitude"
    config["show_geo_vectors"] = bool(config.get("show_geo_vectors", True))
    config["show_event_range_ring"] = bool(config.get("show_event_range_ring", True))
    if not isinstance(config.get("active_glideslopes"), list):
        config["active_glideslopes"] = []
    return config


def save_web_config(config):
    clean = DEFAULT_WEB_CONFIG.copy()
    clean.update({key: config.get(key, clean[key]) for key in DEFAULT_WEB_CONFIG})
    with WEB_CONFIG_PATH.open("w", encoding="utf-8") as handle:
        json.dump(clean, handle, indent=4, sort_keys=True)
    return clean


def public_config():
    config = tf.load_config(tf.config_file_full_path)
    web_config = load_web_config()
    return {
        "config": config,
        "web": web_config,
        "options": {
            "airport_types": tf.ALL_AIRPORT_TYPES,
            "navaid_types": tf.ALL_NAVAID_TYPES,
            "range_ring_spacing_nm": tf.RANGE_RING_OPTIONS_NM,
            "velocity_vector_minutes": tf.VELOCITY_VECTOR_OPTIONS_MIN,
            "vector_layers": {
                key: value.get("label", key)
                for key, value in tf.VECTOR_LAYER_CONFIGS.items()
            },
            "visual_styles": ["current", "desktop", "atc"],
            "aircraft_label_fields": ["callsign", "icao", "distance", "altitude", "speed", "track", "vs", "squawk"],
            "aircraft_label_line_numbers": ["1", "2", "3", "4"],
            "ils_styles": ["atc", "desktop", "minimal"],
            "ils_lengths_nm": ["5", "7", "10", "15"],
            "aircraft_label_colors": ["aircraft", "green"],
            "unit_distances": ["km", "nm", "mi"],
            "unit_speeds": ["kt", "kmh", "mph"],
            "unit_altitudes": ["ft", "m"],
            "trajectory_minutes": [0.5, 1, 1.5, 2, 3, 5, 8, 10],
            "trajectory_display_modes": ["altitude", "points"],
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
    }
    float_keys = {
        "lat",
        "lon",
        "alt_m",
        "aircraft_timeout",
        "pred_interval",
        "pred_horizon",
        "pred_step",
        "conflict_angle",
        "event_timeout",
        "conflict_radius_km",
        "history_minutes",
        "trajectory_minutes",
        "velocity_vector_minutes",
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
        allowed_fields = {"callsign", "icao", "distance", "altitude", "speed", "track", "vs", "squawk"}
        return [str(item) for item in value if str(item) in allowed_fields] if isinstance(value, list) else current.get(key, DEFAULT_WEB_CONFIG["aircraft_label_fields"])
    if key == "aircraft_label_lines":
        allowed_fields = {"callsign", "icao", "distance", "altitude", "speed", "track", "vs", "squawk"}
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
    if key in {"host", "gain", "range_ring_spacing_nm_str"}:
        return str(value)
    return current.get(key, value)


def apply_runtime_config(config):
    global GEODATA_READY
    tf.HOST = config["host"]
    tf.PORT = config["port"]
    tf.DUMP1090_DEVICE_INDEX = config["device_index"]
    tf.DUMP1090_GAIN = config["gain"]
    tf.USER_LAT = config["lat"]
    tf.USER_LON = config["lon"]
    tf.USER_ALT = config["alt_m"]
    tf.USER_ALT_FT = tf.USER_ALT * 3.28084
    tf.AIRCRAFT_TIMEOUT = config["aircraft_timeout"]
    tf.PREDICTION_INTERVAL = config["pred_interval"]
    tf.PREDICTION_HORIZON = config["pred_horizon"]
    tf.PREDICTION_STEP = config["pred_step"]
    tf.CONFLICT_ANGLE_DEG = config["conflict_angle"]
    tf.EVENT_TIMEOUT = config["event_timeout"]
    tf.CONFLICT_RADIUS_KM = config["conflict_radius_km"]
    tf.AIRCRAFT_HISTORY_MINUTES = config["history_minutes"]
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
    history_maxlen = min(
        max(int(tf.AIRCRAFT_HISTORY_MINUTES * 60 / max(tf.PREDICTION_INTERVAL, 0.1)) + 5, 50),
        tf.MAX_HISTORY_POINTS_PER_AC,
    )
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
    GEODATA_READY = False
    init_geodata()


def update_config_from_payload(payload):
    with CONFIG_LOCK:
        current = tf.load_config(tf.config_file_full_path)
        updated = current.copy()
        for key in current:
            if key in payload:
                updated[key] = coerce_config_value(key, payload[key], current)
        if "web" in payload and isinstance(payload["web"], dict):
            web_current = load_web_config()
            web_updated = web_current.copy()
            for key in DEFAULT_WEB_CONFIG:
                if key in payload["web"]:
                    if key in {"show_geo_vectors", "show_event_range_ring"}:
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
            save_web_config(web_updated)
        if not tf.save_config(tf.config_file_full_path, updated):
            raise RuntimeError("Could not save config.json")
        apply_runtime_config(updated)
    return updated


def windows_location_snapshot():
    powershell = "/mnt/c/Windows/System32/WindowsPowerShell/v1.0/powershell.exe"
    if not os.path.exists(powershell):
        raise RuntimeError("Windows PowerShell is not available from this WSL environment")
    script = (
        "Add-Type -AssemblyName System.Device;"
        "$w=New-Object System.Device.Location.GeoCoordinateWatcher([System.Device.Location.GeoPositionAccuracy]::High);"
        "$w.Start();"
        "$deadline=(Get-Date).AddSeconds(20);"
        "while($w.Status -eq 'Initializing' -and (Get-Date) -lt $deadline){Start-Sleep -Milliseconds 250};"
        "$loc=$w.Position.Location;"
        "if($loc.IsUnknown){throw 'Windows location is unavailable or permission is denied'};"
        "$alt=$null;"
        "if(-not [double]::IsNaN($loc.Altitude)){ $alt=$loc.Altitude };"
        "$obj=[ordered]@{lat=$loc.Latitude;lon=$loc.Longitude;alt_m=$alt;horizontal_accuracy_m=$loc.HorizontalAccuracy;vertical_accuracy_m=$loc.VerticalAccuracy};"
        "$obj | ConvertTo-Json -Compress"
    )
    result = subprocess.run(
        [powershell, "-NoProfile", "-Command", script],
        capture_output=True,
        text=True,
        timeout=25,
    )
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "Windows location failed").strip())
    return json.loads(result.stdout)


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
            types_to_show=tf.SHOW_AIRPORT_TYPES,
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
        for layer_key, visible in tf.VECTOR_LAYERS_VISIBILITY.items():
            if visible and layer_key in tf.VECTOR_LAYER_CONFIGS:
                tf.map_manager.load_layer(layer_key, tf.VECTOR_LAYER_CONFIGS[layer_key])
                layer_data = tf.map_manager.layers_data.get(layer_key, [])
                shp_path = Path(tf.app_dir) / "data" / "map_vectors" / layer_key / f"{layer_key}.shp"
                if not layer_data and shp_path.exists():
                    cache_path = Path(tf.map_manager.get_cache_path(layer_key))
                    try:
                        cache_path.unlink(missing_ok=True)
                    except Exception:
                        pass
                    tf.map_manager.load_layer(layer_key, tf.VECTOR_LAYER_CONFIGS[layer_key])
        GEODATA_READY = True
    except Exception as exc:
        print(f"[web] Geodata unavailable: {exc}")


def start_processing_threads(start_dump1090=False):
    global THREADS_STARTED
    if THREADS_STARTED:
        return
    tf.running = True
    if start_dump1090:
        try:
            tf.start_dump1090_process()
        except FileNotFoundError as exc:
            print(f"[web] {exc}; continuing without dump1090 auto-start.")
        except Exception as exc:
            print(f"[web] Could not start dump1090: {exc}")

    init_ephemeris()
    init_geodata()

    workers = [
        threading.Thread(target=tf.start_listener, daemon=True, name="WebListener"),
        threading.Thread(target=tf.predict_conflicts, daemon=True, name="WebConflictPredictor"),
        threading.Thread(target=tf.clean_expired_events, daemon=True, name="WebEventCleaner"),
    ]
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
    THREADS_STARTED = True


def aircraft_snapshot(range_km, center_lat, center_lon, web_config=None):
    if web_config is None:
        web_config = load_web_config()
    trajectory_minutes = finite_float(web_config.get("trajectory_minutes"), 2.0) or 2.0
    trajectory_seconds = max(15.0, trajectory_minutes * 60.0)
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
        lat = ac.get("lat")
        lon = ac.get("lon")
        distance_km = tf.haversine(tf.USER_LAT, tf.USER_LON, lat, lon) if lat and lon else None
        view_distance_km = tf.haversine(center_lat, center_lon, lat, lon) if lat and lon else None
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
                path.append({"dt": dt, "lat": plat, "lon": plon, "altitude": palt})

        aircraft.append(
            {
                "icao": ac.get("icao"),
                "callsign": (ac.get("callsign") or "").strip(),
                "lat": lat,
                "lon": lon,
                "altitude": ac.get("altitude"),
                "speed": ac.get("speed"),
                "track": ac.get("track"),
                "vs": ac.get("vs"),
                "squawk": ac.get("squawk"),
                "age_sec": age,
                "distance_km": distance_km,
                "view_distance_km": view_distance_km,
                "conflict": ac.get("conflict"),
                "has_event": bool(ac.get("event_ids")),
                "history": history,
                "path": path,
                "visible": view_distance_km is not None and view_distance_km <= range_km * 1.35,
            }
        )
    aircraft.sort(key=lambda item: (item["distance_km"] is None, item["distance_km"] or 999999))
    return aircraft


def events_snapshot():
    now = utc_now()
    events = []
    with tf.lock:
        source = list(tf.event_dict.items())
    for eid, ev in source:
        ev_time = ev.get("time")
        eta = (ev_time - now).total_seconds() if isinstance(ev_time, datetime) else None
        icaos = [item for item in eid if isinstance(item, str) and item not in {"AC-AC", "AC-Sun", "AC-Moon"}] if isinstance(eid, tuple) else []
        events.append(
            {
                "type": ev.get("type"),
                "icaos": icaos,
                "callsigns": ev.get("callsigns", []),
                "time": ev_time.isoformat() if isinstance(ev_time, datetime) else None,
                "eta_sec": eta,
                "angle": ev.get("angle"),
                "min_dist_km": ev.get("min_dist_km"),
                "lat": ev.get("lat"),
                "lon": ev.get("lon"),
                "alt": ev.get("alt"),
                "pov": ev.get("pov", {}),
            }
        )
    events.sort(key=lambda item: item["eta_sec"] if item["eta_sec"] is not None else 999999)
    return events


def vector_geodata(range_km, center_lat, center_lon):
    web_config = load_web_config()
    if not web_config.get("show_geo_vectors", True) or not tf.map_manager:
        return []
    if range_km <= 120:
        max_features, max_points_per_feature = 1100, 760
    elif range_km <= 320:
        max_features, max_points_per_feature = 900, 460
    else:
        max_features, max_points_per_feature = 700, 260
    lat_span = math.degrees(range_km / tf.EARTH_RADIUS_KM) * 1.35
    lon_factor = max(0.05, math.cos(math.radians(center_lat)))
    lon_span = math.degrees(range_km / (tf.EARTH_RADIUS_KM * lon_factor)) * 1.35
    min_lat, max_lat = center_lat - lat_span, center_lat + lat_span
    min_lon, max_lon = center_lon - lon_span, center_lon + lon_span
    features = []
    for layer_key, visible in tf.VECTOR_LAYERS_VISIBILITY.items():
        if not visible or layer_key not in tf.map_manager.layers_data:
            continue
        cfg = tf.VECTOR_LAYER_CONFIGS.get(layer_key, {})
        for pts_array, bbox in tf.map_manager.layers_data[layer_key]:
            if bbox[1] < min_lon or bbox[0] > max_lon or bbox[3] < min_lat or bbox[2] > max_lat:
                continue
            stride = max(1, int(math.ceil(len(pts_array) / max_points_per_feature)))
            pts = pts_array[::stride].tolist()
            if len(pts) >= 2:
                features.append({
                    "layer": layer_key,
                    "type": cfg.get("type", "line"),
                    "points": pts,
                })
            if len(features) >= max_features:
                return features
    return features


def nearby_geodata(range_km, center_lat, center_lon, max_items=350):
    lat_span = math.degrees(range_km / tf.EARTH_RADIUS_KM) * 1.3
    lon_factor = max(0.05, math.cos(math.radians(center_lat)))
    lon_span = math.degrees(range_km / (tf.EARTH_RADIUS_KM * lon_factor)) * 1.3
    min_lat, max_lat = center_lat - lat_span, center_lat + lat_span
    min_lon, max_lon = center_lon - lon_span, center_lon + lon_span

    airports = [
        apt
        for apt in tf.airports_data
        if min_lat <= apt["lat"] <= max_lat and min_lon <= apt["lon"] <= max_lon
    ][:max_items]
    navaids = [
        nav
        for nav in tf.navaids_data
        if min_lat <= nav["lat"] <= max_lat and min_lon <= nav["lon"] <= max_lon
    ][:max_items]
    runways = []
    for apt in airports[:120]:
        for idx, rwy in enumerate(tf.runways_data.get(apt["ident"], [])[:12]):
            runways.append({"airport": apt["ident"], "runway_index": idx, **rwy})
    return {"airports": airports, "navaids": navaids, "runways": runways, "vectors": vector_geodata(range_km, center_lat, center_lon)}


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


def transit_snapshot(mode, selected_icao, aircraft):
    if mode == "none" or not tf.eph:
        return []
    if mode == "all":
        icaos = [ac["icao"] for ac in aircraft if ac.get("visible")][:20]
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
            "moon": {"az": moon_az.degrees, "el": moon_alt.degrees},
        }
    except Exception:
        return None


def build_state(query):
    web_config = load_web_config()
    range_km = finite_float(query.get("range_km", [tf.INITIAL_MAP_RANGE_KM])[0], tf.INITIAL_MAP_RANGE_KM)
    range_km = max(tf.MIN_MAP_RANGE_KM, min(tf.MAX_MAP_RANGE_KM, range_km))
    center_lat = finite_float(query.get("center_lat", [tf.USER_LAT])[0], tf.USER_LAT)
    center_lon = finite_float(query.get("center_lon", [tf.USER_LON])[0], tf.USER_LON)
    selected_icao = (query.get("selected", [""])[0] or "").upper()[:6]
    transit_mode = query.get("transits", ["selected"])[0]
    if transit_mode not in {"none", "selected", "all"}:
        transit_mode = "selected"

    aircraft = aircraft_snapshot(range_km, center_lat, center_lon, web_config)
    active_total = len(aircraft)
    active_no_pos = len([ac for ac in aircraft if ac["lat"] is None or ac["lon"] is None])

    return {
        "server_time": utc_now().isoformat(),
        "runtime_sec": (utc_now() - SERVER_START).total_seconds(),
        "settings": {
            "dump1090_host": tf.HOST,
            "dump1090_port": tf.PORT,
            "connected": tf.DUMP1090_CONNECTED,
            "user": {"lat": tf.USER_LAT, "lon": tf.USER_LON, "alt_m": tf.USER_ALT},
            "center": {"lat": center_lat, "lon": center_lon},
            "range_km": range_km,
            "conflict_angle_deg": tf.CONFLICT_ANGLE_DEG,
            "prediction_horizon_sec": tf.PREDICTION_HORIZON,
            "velocity_vector_minutes": tf.VELOCITY_VECTOR_MINUTES,
            "history_minutes": tf.AIRCRAFT_HISTORY_MINUTES,
            "show_history": tf.SHOW_AIRCRAFT_HISTORY,
            "show_events": tf.SHOW_EVENT_LOCATIONS,
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
        },
        "aircraft": aircraft,
        "events": events_snapshot(),
        "transits": transit_snapshot(transit_mode, selected_icao, aircraft),
        "geodata": nearby_geodata(range_km, center_lat, center_lon),
        "glideslopes": glideslope_snapshot(),
        "celestial": celestial_snapshot(),
    }


class WebHandler(BaseHTTPRequestHandler):
    server_version = "ADSBTransitWeb/0.1"

    def log_message(self, fmt, *args):
        print(f"[web] {self.address_string()} - {fmt % args}")

    def send_bytes(self, status, content_type, body):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, status, payload):
        body = json.dumps(payload, default=json_default, separators=(",", ":")).encode("utf-8")
        self.send_bytes(status, "application/json; charset=utf-8", body)

    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/api/state":
            self.send_json(200, build_state(parse_qs(parsed.query)))
            return
        if parsed.path == "/api/config":
            self.send_json(200, public_config())
            return
        if parsed.path == "/api/location/windows":
            try:
                self.send_json(200, {"ok": True, "location": windows_location_snapshot()})
            except Exception as exc:
                self.send_json(400, {"ok": False, "error": str(exc)})
            return
        if parsed.path == "/api/health":
            self.send_json(200, {"ok": True, "connected": tf.DUMP1090_CONNECTED})
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
        if parsed.path != "/api/config":
            self.send_json(404, {"error": "not found"})
            return
        try:
            length = safe_int(self.headers.get("Content-Length"), 0)
            payload = json.loads(self.rfile.read(length).decode("utf-8")) if length else {}
            update_config_from_payload(payload)
            response = public_config()
            response["ok"] = True
            self.send_json(200, response)
        except Exception as exc:
            self.send_json(400, {"ok": False, "error": str(exc)})


class QuietThreadingHTTPServer(ThreadingHTTPServer):
    def handle_error(self, request, client_address):
        exc_type, exc, _ = sys.exc_info()
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

    start_processing_threads(start_dump1090=args.start_dump1090)

    server = QuietThreadingHTTPServer((args.host, args.port), WebHandler)
    scheme = "https" if args.https else "http"
    if args.https:
        certfile, keyfile = ensure_self_signed_cert(args.certfile, args.keyfile)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(certfile=certfile, keyfile=keyfile)
        server.socket = context.wrap_socket(server.socket, server_side=True, do_handshake_on_connect=False)
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
