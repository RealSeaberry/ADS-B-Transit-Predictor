import socket
import csv
import threading
import time
import numpy as np
from datetime import datetime, timedelta, timezone
# Corrected import for ceil
from math import radians, degrees, sin, cos, asin, atan2, acos, sqrt, hypot, ceil, tan
from skyfield.api import load, Topos  # 天体位置计算
import pygame  # 用于界面绘制
import subprocess
import sys # 用于退出
import os
import json
import tkinter as tk
import tkinter.ttk as ttk # <<< 导入 ttk
# from tkinter import messagebox # 不再需要 messagebox
import traceback
import collections
# import time # already imported
import shapefile
from shapely.geometry import LineString, Polygon

def resource_path(relative_path):
    try:
        # PyInstaller creates a temp folder and stores path in _MEIPASS
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

# --- Icon Path ---
ICON_FILENAME = "icon.ico" # Assume icon.ico is in the same directory or accessible via resource_path
try:
    # Use resource_path to handle running from script or bundled app
    ICON_PATH = resource_path(ICON_FILENAME)
    if not os.path.exists(ICON_PATH):
         print(f"Warning: Icon file not found at expected location: {ICON_PATH}")
         ICON_PATH = None # Set to None if not found
except Exception as e:
    print(f"Warning: Error determining icon path: {e}")
    ICON_PATH = None

# ---------------------------
# Configuration Loading / Defaults
# ---------------------------
CONFIG_FILENAME = "config.json"

# --- ADD Data File Paths ---
AIRPORTS_CSV = resource_path(os.path.join("data", "airports.csv"))
RUNWAYS_CSV = resource_path(os.path.join("data", "runways.csv"))
NAVAIDS_CSV = resource_path(os.path.join("data", "navaids.csv"))

# --- Default Configuration Values ---
DEFAULT_HOST = "127.0.0.1"; DEFAULT_PORT = 30003
DEFAULT_LAT_DEG = 51.471396; DEFAULT_LON_DEG = -0.460000; DEFAULT_ALT_M = 27 # User's specific altitude，in meter
DEFAULT_AIRCRAFT_TIMEOUT_SEC = 60; DEFAULT_PREDICTION_INTERVAL_SEC = 1.0
DEFAULT_PREDICTION_HORIZON_SEC = 120; DEFAULT_PREDICTION_STEP_SEC = 0.5
DEFAULT_CONFLICT_ANGLE_DEG = 2.0
DEFAULT_DUMP1090_DEVICE_INDEX = 0
DEFAULT_DUMP1090_GAIN = "-10"
DEFAULT_AIRCRAFT_HISTORY_MINUTES = 5.0
DEFAULT_SHOW_AIRCRAFT_HISTORY = True
DEFAULT_SHOW_EVENT_LOCATIONS = True
DEFAULT_SHOW_AIRPORT_TYPES = [ 'medium_airport', 'large_airport']
DEFAULT_SHOW_NAVAID_TYPES = ['VOR', 'VORDME', 'DME', 'NDB', 'TACAN', 'VORTAC', 'FIX', 'WAYPOINT','VOR-DME']
DEFAULT_SHOW_GLIDESLOPE = False
DEFAULT_SHOW_RANGE_RINGS = False
DEFAULT_RANGE_RING_SPACING_NM_STR = "10"
DEFAULT_MAX_RANGE_RINGS = 20
DEFAULT_SHOW_ALL_TRANSIT_STRIPS = False
DEFAULT_SHOW_VELOCITY_VECTOR = True

# --- Constants ---
EVENT_TIMEOUT = 10; CONFLICT_RADIUS_KM = 30
AIRPORT_LABEL_MIN_ZOOM_KM = 500
RUNWAY_MIN_ZOOM_KM = 120
NAVAID_LABEL_MIN_ZOOM_KM = 500
RUNWAY_LABEL_MIN_ZOOM_KM = 120
ALL_AIRPORT_TYPES = ['small_airport', 'medium_airport', 'large_airport', 'heliport', 'seaplane_base']
ALL_NAVAID_TYPES = ['VOR', 'VORDME', 'DME', 'NDB', 'TACAN', 'VORTAC', 'FIX', 'WAYPOINT','VOR-DME']
DISPLAY_NAVAID_TYPES = ['VOR', 'DME', 'NDB', 'TACAN', 'VORTAC', 'FIX', 'WAYPOINT', 'VOR-DME']
CONSOLIDATED_NAVAID_MAP = {'VOR-DME': ['VORDME', 'VOR-DME']}
HISTORY_POINT_SIZE = 2; HISTORY_ALPHA = 100; MAX_HISTORY_POINTS_PER_AC = 300
GLIDESLOPE_LENGTH_LARGE_KM = 18.52; GLIDESLOPE_LENGTH_MEDIUM_KM = 12.964; GLIDESLOPE_LENGTH_SMALL_KM = 9.26
GLIDESLOPE_TICK_INTERVAL_KM = 1.8519; GLIDESLOPE_TICK_HALF_LENGTH_PX = 4; GLIDESLOPE_COLOR = (180, 180, 255)
RUNWAY_CLICK_SENSITIVITY_PX = 10; EARTH_RADIUS_KM = 6371.0088
RANGE_RING_COLOR = (0, 80, 0); NM_TO_KM = 1.852; RANGE_RING_OPTIONS_NM = ["1", "2.5", "5", "10", "25", "50"]
SUN_ANGULAR_DIAMETER_DEG = 0.53; MOON_ANGULAR_DIAMETER_DEG = 0.50

# --- Global variables ---
active_glideslopes = {}; dialog_runway_end_result_storage = [None]; dialog_runway_end_thread = None
aircraft_dict = {}; event_dict = {}; history_event_count = 0
DUMP1090_CONNECTED = False; start_time = datetime.now(timezone.utc)
INITIAL_MAP_RANGE_KM = 30 * 2.0 # Default derived from conflict radius
MIN_MAP_RANGE_KM = 1.0; MAX_MAP_RANGE_KM = 1000.0; ZOOM_FACTOR = 1.25
lock = threading.Lock(); dialog_result_storage = [None]; dialog_thread = None
running = True

selected_aircraft_for_transit_icao = None; last_clicked_transit_coord = None; last_clicked_transit_time = 0

def get_application_path():
    if getattr(sys, 'frozen', False): application_path = sys._MEIPASS
    else:
        try: application_path = os.path.dirname(os.path.abspath(__file__))
        except NameError: application_path = os.path.abspath(".")
    return application_path

VELOCITY_VECTOR_OPTIONS_MIN = [0.5, 1.0, 1.5, 2]; DEFAULT_VELOCITY_VECTOR_MINUTES = 1.0

DEFAULT_VECTOR_LAYERS_VISIBILITY = {
    "coastline": True, "countries_borders": True, "countries_fill": False, "lakes": True,
    "rivers": False, "land_fill": False, "ocean_fill": False, "minor_islands_fill": False,
    "urban_areas_fill": False, "populated_places_points": False, "geography_regions_fill": False,
}
SHOW_ALL_TRANSIT_STRIPS = DEFAULT_SHOW_ALL_TRANSIT_STRIPS
VELOCITY_VECTOR_MINUTES = DEFAULT_VELOCITY_VECTOR_MINUTES
VELOCITY_VECTOR_SECONDS = DEFAULT_VELOCITY_VECTOR_MINUTES * 60.0
SHOW_VELOCITY_VECTOR = DEFAULT_SHOW_VELOCITY_VECTOR
VECTOR_LAYERS_VISIBILITY = DEFAULT_VECTOR_LAYERS_VISIBILITY.copy()
map_features_geodata = {}

VECTOR_LAYER_CONFIGS = {
    "ne_10m_coastline": {"type": "line", "color": (0, 60, 100), "default_on": True, "label": "Coastlines"},
    "ne_10m_admin_0_boundary_lines_land": {"type": "line", "color": (80, 80, 80), "default_on": True, "label": "Country Borders (Lines)"},
    "ne_10m_admin_0_countries": {"type": "polygon", "color": (70, 70, 70), "default_on": False, "label": "Countries (Fill)"},
    "ne_10m_lakes": {"type": "polygon", "color": (50, 80, 120), "default_on": True, "label": "Lakes (Fill)"},
    "ne_10m_rivers_lake_centerlines": {"type": "line", "color": (80, 120, 150), "default_on": False, "label": "Rivers"},
    "ne_10m_land": {"type": "polygon", "color": (40, 50, 30), "default_on": False, "label": "Land Areas (Fill)"},
    "ne_10m_ocean": {"type": "polygon", "color": (20, 30, 50), "default_on": False, "label": "Ocean Areas (Fill)"},
    "ne_10m_minor_islands": {"type": "polygon", "color": (50, 60, 40), "default_on": False, "label": "Minor Islands (Fill)"},
    "ne_10m_urban_areas": {"type": "polygon", "color": (60, 60, 60), "default_on": False, "label": "Urban Areas (Fill)"},
    "ne_10m_populated_places": {"type": "point", "color": (200, 200, 100), "default_on": False, "label": "Populated Places"},
    "ne_10m_geography_regions_polys": {"type": "polygon", "color": (80, 70, 60), "default_on": False, "label": "Geo Regions (Fill)"},
}
for layer_key, config_val in VECTOR_LAYER_CONFIGS.items():
    VECTOR_LAYERS_VISIBILITY[layer_key] = config_val.get("default_on", False)

# --- CONSTANT TOLERANCE FOR VECTOR MAPS ---
DEFAULT_SIMPLIFICATION_TOLERANCE_DEG = 0.005  # Fixed tolerance (degrees)
# Example values: 0.01 is quite coarse, 0.001 is finer. Adjust as needed for your data.

map_features_geodata = {key: [] for key in VECTOR_LAYER_CONFIGS.keys()} # Initialize

def load_config(config_path):
    global VELOCITY_VECTOR_MINUTES, VELOCITY_VECTOR_SECONDS, SHOW_VELOCITY_VECTOR, VECTOR_LAYERS_VISIBILITY
    default_vector_visibility = {key: conf.get("default_on", False) for key, conf in VECTOR_LAYER_CONFIGS.items()}
    default_config = {
        "host": DEFAULT_HOST, "port": DEFAULT_PORT, "device_index": DEFAULT_DUMP1090_DEVICE_INDEX,
        "gain": DEFAULT_DUMP1090_GAIN, "lat": DEFAULT_LAT_DEG, "lon": DEFAULT_LON_DEG, "alt_m": DEFAULT_ALT_M,
        "aircraft_timeout": DEFAULT_AIRCRAFT_TIMEOUT_SEC, "pred_interval": DEFAULT_PREDICTION_INTERVAL_SEC,
        "pred_horizon": DEFAULT_PREDICTION_HORIZON_SEC, "pred_step": DEFAULT_PREDICTION_STEP_SEC,
        "conflict_angle": DEFAULT_CONFLICT_ANGLE_DEG, "event_timeout": EVENT_TIMEOUT,
        "conflict_radius_km": CONFLICT_RADIUS_KM, "history_minutes": DEFAULT_AIRCRAFT_HISTORY_MINUTES,
        "show_airport_types": DEFAULT_SHOW_AIRPORT_TYPES, "show_navaid_types": DEFAULT_SHOW_NAVAID_TYPES,
        "show_history": DEFAULT_SHOW_AIRCRAFT_HISTORY, "show_events": DEFAULT_SHOW_EVENT_LOCATIONS,
        "show_glideslope": DEFAULT_SHOW_GLIDESLOPE, "show_range_rings": DEFAULT_SHOW_RANGE_RINGS,
        "range_ring_spacing_nm_str": DEFAULT_RANGE_RING_SPACING_NM_STR, "max_range_rings": DEFAULT_MAX_RANGE_RINGS,
        "show_all_transit_strips": DEFAULT_SHOW_ALL_TRANSIT_STRIPS,
        "velocity_vector_minutes": DEFAULT_VELOCITY_VECTOR_MINUTES,
        "show_velocity_vector": DEFAULT_SHOW_VELOCITY_VECTOR,
        "vector_layers_visibility": default_vector_visibility
    }
    config = default_config.copy()
    try:
        with open(config_path, 'r', encoding='utf-8') as f: loaded_data = json.load(f)
        print(f"Loaded configuration from {config_path}")
        for key, default_value in default_config.items():
            loaded_value = loaded_data.get(key)
            if loaded_value is not None:
                expected_type = type(default_value); actual_type = type(loaded_value)
                is_numeric_default = isinstance(default_value, (int, float)); is_numeric_actual = isinstance(loaded_value, (int, float))
                type_match = False
                if expected_type is int and actual_type is float and loaded_value == int(loaded_value): loaded_value = int(loaded_value); actual_type = int
                if is_numeric_default and is_numeric_actual: type_match = True
                elif actual_type is expected_type: type_match = True
                elif key == "gain" and isinstance(loaded_value, str): type_match = True
                elif key == "range_ring_spacing_nm_str" and isinstance(loaded_value, str): type_match = True
                elif key == "velocity_vector_minutes" and isinstance(loaded_value, (int, float)):
                    if float(loaded_value) in VELOCITY_VECTOR_OPTIONS_MIN: type_match = True
                    else: print(f"Warning: Invalid value '{loaded_value}' for 'velocity_vector_minutes'.")
                elif key == "vector_layers_visibility" and isinstance(loaded_value, dict): type_match = True
                if type_match:
                    if key in ["show_airport_types", "show_navaid_types"]:
                        if isinstance(loaded_value, list) and all(isinstance(item, str) for item in loaded_value): config[key] = loaded_value
                        else: print(f"Warning: Invalid format for '{key}' in config. Using default.")
                    elif key == "vector_layers_visibility":
                        current_visibility = default_vector_visibility.copy()
                        for layer_k, vis_val in loaded_value.items():
                            if layer_k in current_visibility: current_visibility[layer_k] = bool(vis_val)
                        config[key] = current_visibility
                    elif is_numeric_default or expected_type is int or key == "velocity_vector_minutes":
                         value_to_assign = loaded_value; valid = True
                         if key == "velocity_vector_minutes":
                             try:
                                 val_float = float(value_to_assign)
                                 if val_float not in VELOCITY_VECTOR_OPTIONS_MIN: valid = False
                                 else: value_to_assign = float(val_float)
                             except ValueError: valid = False
                         if valid: config[key] = value_to_assign
                         else:
                             print(f"Warning: Invalid value '{loaded_value}' for '{key}' in config. Using default: {default_value}")
                             if key == "velocity_vector_minutes": config[key] = DEFAULT_VELOCITY_VECTOR_MINUTES
                    elif isinstance(default_value, bool): config[key] = bool(loaded_value)
                    elif isinstance(default_value, str): config[key] = str(loaded_value)
                else:
                    print(f"Warning: Type mismatch for '{key}' in config. Expected {expected_type} or convertible, got {actual_type}. Using default: {default_value}")
                    if key == "velocity_vector_minutes": config[key] = DEFAULT_VELOCITY_VECTOR_MINUTES
                    if key == "show_velocity_vector": config[key] = DEFAULT_SHOW_VELOCITY_VECTOR
                    if key == "vector_layers_visibility": config[key] = default_vector_visibility.copy()
            else: print(f"Info: Config key '{key}' not found, using default: {default_value}"); config[key] = default_value
        if not isinstance(config.get("show_all_transit_strips"), bool): config["show_all_transit_strips"] = DEFAULT_SHOW_ALL_TRANSIT_STRIPS
        if not isinstance(config.get("show_velocity_vector"), bool): config["show_velocity_vector"] = DEFAULT_SHOW_VELOCITY_VECTOR
        vv_mins = config.get("velocity_vector_minutes", DEFAULT_VELOCITY_VECTOR_MINUTES)
        if not isinstance(vv_mins, (int, float)) or float(vv_mins) not in VELOCITY_VECTOR_OPTIONS_MIN: config["velocity_vector_minutes"] = DEFAULT_VELOCITY_VECTOR_MINUTES
        else: config["velocity_vector_minutes"] = float(vv_mins)
        loaded_vec_vis = config.get("vector_layers_visibility", default_vector_visibility.copy())
        if not isinstance(loaded_vec_vis, dict): config["vector_layers_visibility"] = default_vector_visibility.copy()
        else:
            final_vec_vis = default_vector_visibility.copy()
            for k, v_conf in VECTOR_LAYER_CONFIGS.items(): final_vec_vis[k] = bool(loaded_vec_vis.get(k, v_conf.get("default_on", False)))
            config["vector_layers_visibility"] = final_vec_vis
        VELOCITY_VECTOR_MINUTES = config["velocity_vector_minutes"]
        VELOCITY_VECTOR_SECONDS = VELOCITY_VECTOR_MINUTES * 60.0
        SHOW_VELOCITY_VECTOR = config["show_velocity_vector"]
        VECTOR_LAYERS_VISIBILITY = config["vector_layers_visibility"].copy()
    except FileNotFoundError:
        print(f"Warning: Config file '{config_path}' not found. Creating default.")
        VELOCITY_VECTOR_MINUTES = DEFAULT_VELOCITY_VECTOR_MINUTES; VELOCITY_VECTOR_SECONDS = VELOCITY_VECTOR_MINUTES * 60.0
        SHOW_VELOCITY_VECTOR = DEFAULT_SHOW_VELOCITY_VECTOR; VECTOR_LAYERS_VISIBILITY = default_vector_visibility.copy()
        save_config(config_path, config) # Save defaults
    except json.JSONDecodeError:
        print(f"Error: Could not decode JSON from '{config_path}'. Using defaults.")
        config = default_config.copy()
        VELOCITY_VECTOR_MINUTES = DEFAULT_VELOCITY_VECTOR_MINUTES; VELOCITY_VECTOR_SECONDS = VELOCITY_VECTOR_MINUTES * 60.0
        SHOW_VELOCITY_VECTOR = DEFAULT_SHOW_VELOCITY_VECTOR; VECTOR_LAYERS_VISIBILITY = default_vector_visibility.copy()
    except Exception as e:
        print(f"An unexpected error occurred loading config: {e}. Using defaults.")
        config = default_config.copy()
        VELOCITY_VECTOR_MINUTES = DEFAULT_VELOCITY_VECTOR_MINUTES; VELOCITY_VECTOR_SECONDS = VELOCITY_VECTOR_MINUTES * 60.0
        SHOW_VELOCITY_VECTOR = DEFAULT_SHOW_VELOCITY_VECTOR; VECTOR_LAYERS_VISIBILITY = default_vector_visibility.copy()
    return config

def save_config(config_path, config_data_dict):
    try:
        config_to_save = config_data_dict.copy(); config_to_save.pop('_requires_restart', None)
        if not isinstance(config_to_save.get("show_all_transit_strips"), bool): config_to_save["show_all_transit_strips"] = DEFAULT_SHOW_ALL_TRANSIT_STRIPS
        if not isinstance(config_to_save.get("show_velocity_vector"), bool): config_to_save["show_velocity_vector"] = DEFAULT_SHOW_VELOCITY_VECTOR
        vv_mins_save = config_to_save.get("velocity_vector_minutes", DEFAULT_VELOCITY_VECTOR_MINUTES)
        if not isinstance(vv_mins_save, (int, float)) or float(vv_mins_save) not in VELOCITY_VECTOR_OPTIONS_MIN: config_to_save["velocity_vector_minutes"] = DEFAULT_VELOCITY_VECTOR_MINUTES
        else: config_to_save["velocity_vector_minutes"] = float(vv_mins_save)
        vec_vis_to_save = config_to_save.get("vector_layers_visibility", {})
        if not isinstance(vec_vis_to_save, dict): vec_vis_to_save = {}
        sane_vec_vis = {}
        for key_conf in VECTOR_LAYER_CONFIGS.keys(): sane_vec_vis[key_conf] = bool(vec_vis_to_save.get(key_conf, VECTOR_LAYER_CONFIGS[key_conf].get("default_on", False)))
        config_to_save["vector_layers_visibility"] = sane_vec_vis
        with open(config_path, 'w', encoding='utf-8') as f: json.dump(config_to_save, f, indent=4, sort_keys=True)
        print(f"Configuration saved to {config_path}")
        return True
    except Exception as e: print(f"Error writing config file '{config_path}': {e}"); return False

app_dir = get_application_path()
config_file_full_path = os.path.join(app_dir, CONFIG_FILENAME)
loaded_settings = load_config(config_file_full_path)

HOST = loaded_settings["host"]; PORT = loaded_settings["port"]
DUMP1090_DEVICE_INDEX = loaded_settings["device_index"]; DUMP1090_GAIN = loaded_settings["gain"]
USER_LAT = loaded_settings["lat"]; USER_LON = loaded_settings["lon"]; USER_ALT = loaded_settings["alt_m"]
USER_ALT_FT = USER_ALT * 3.28084
AIRCRAFT_TIMEOUT = loaded_settings["aircraft_timeout"]; PREDICTION_INTERVAL = loaded_settings["pred_interval"]
PREDICTION_HORIZON = loaded_settings["pred_horizon"]; PREDICTION_STEP = loaded_settings["pred_step"]
CONFLICT_ANGLE_DEG = loaded_settings["conflict_angle"]; EVENT_TIMEOUT = loaded_settings["event_timeout"]
CONFLICT_RADIUS_KM = loaded_settings["conflict_radius_km"]; AIRCRAFT_HISTORY_MINUTES = loaded_settings["history_minutes"]
SHOW_AIRPORT_TYPES = loaded_settings["show_airport_types"]; SHOW_NAVAID_TYPES = loaded_settings["show_navaid_types"]
SHOW_AIRCRAFT_HISTORY = loaded_settings["show_history"]; SHOW_EVENT_LOCATIONS = loaded_settings["show_events"]
SHOW_GLIDESLOPE = loaded_settings["show_glideslope"]; SHOW_RANGE_RINGS = loaded_settings["show_range_rings"]
RANGE_RING_SPACING_NM_STR = loaded_settings["range_ring_spacing_nm_str"]; MAX_RANGE_RINGS = loaded_settings["max_range_rings"]
SHOW_ALL_TRANSIT_STRIPS = loaded_settings["show_all_transit_strips"]
VELOCITY_VECTOR_MINUTES = loaded_settings["velocity_vector_minutes"]
VELOCITY_VECTOR_SECONDS = VELOCITY_VECTOR_MINUTES * 60.0
SHOW_VELOCITY_VECTOR = loaded_settings["show_velocity_vector"]
VECTOR_LAYERS_VISIBILITY = loaded_settings["vector_layers_visibility"].copy()
try:
    RANGE_RING_SPACING_KM = float(RANGE_RING_SPACING_NM_STR) * NM_TO_KM
    INITIAL_MAP_RANGE_KM = loaded_settings.get("conflict_radius_km", CONFLICT_RADIUS_KM) * 2.0
except (ValueError, KeyError):
    print(f"Warning: Invalid range_ring_spacing_nm_str or conflict_radius_km. Defaulting spacing/initial range.")
    RANGE_RING_SPACING_NM_STR = DEFAULT_RANGE_RING_SPACING_NM_STR
    RANGE_RING_SPACING_KM = float(RANGE_RING_SPACING_NM_STR) * NM_TO_KM
    INITIAL_MAP_RANGE_KM = CONFLICT_RADIUS_KM * 2.0

print("-" * 20 + " Runtime Configuration " + "-" * 20)
# ... (omitting detailed printout for brevity, it's unchanged structurally)
print(f" Initial Map Range for Loading: {INITIAL_MAP_RANGE_KM:.1f} km")
print(f" Vector Map Simplification Tolerance: {DEFAULT_SIMPLIFICATION_TOLERANCE_DEG}° (Fixed)")
print("-" * (42 + len(" Runtime Configuration ")))


MIN_RIGHT_PANEL_WIDTH = 300; MIN_LEFT_PANEL_SIDE = 300
def calculate_panel_layout(screen_width, screen_height):
    h_constrained_side = screen_height; w_constrained_side = screen_width - MIN_RIGHT_PANEL_WIDTH
    left_panel_side = min(h_constrained_side, w_constrained_side)
    left_panel_side = max(MIN_LEFT_PANEL_SIDE, left_panel_side)
    panel_height = min(screen_height, left_panel_side); left_panel_side = min(left_panel_side, panel_height)
    left_width = left_panel_side; left_height = left_panel_side
    right_width = screen_width - left_width
    if right_width < MIN_RIGHT_PANEL_WIDTH and screen_width >= (MIN_LEFT_PANEL_SIDE + MIN_RIGHT_PANEL_WIDTH) :
         right_width = MIN_RIGHT_PANEL_WIDTH; left_width = screen_width - right_width
         left_height = min(left_height, left_width) # Ensure left panel remains square if possible
         # Also, panel_height should be constrained by the new left_width if it became smaller
         panel_height = min(panel_height, left_width)
         left_height = panel_height # Update left_height to new panel_height
    right_height = left_height; display_height = left_height # display_height is the effective square map area height
    # The returned Rects should use the calculated panel_height for their height
    return pygame.Rect(0, 0, left_width, panel_height), pygame.Rect(left_width, 0, right_width, panel_height), panel_height


dump1090_process = None
try:
    dump1090_executable_relative = os.path.join("dump1090", "dump1090.exe")
    dump1090_executable_absolute = os.path.join(app_dir, dump1090_executable_relative)
    if not os.path.isfile(dump1090_executable_absolute): raise FileNotFoundError(f"dump1090 not found: {dump1090_executable_absolute}")
    dump1090_cmd = [dump1090_executable_absolute, "--net", "--device-index", str(DUMP1090_DEVICE_INDEX), "--gain", str(DUMP1090_GAIN)]
    dump1090_creation_flags = 0
    if sys.platform == "win32": dump1090_creation_flags = subprocess.CREATE_NO_WINDOW
    print(f"Attempting to start dump1090: {' '.join(dump1090_cmd)}")
    dump1090_process = subprocess.Popen(dump1090_cmd, creationflags=dump1090_creation_flags)
    print("dump1090 process started (PID:", dump1090_process.pid, ")")
    time.sleep(2)
except FileNotFoundError as fnf_error: print(f"Error: {fnf_error}\nContinuing without dump1090 auto-start.")
except Exception as e: print(f"Error starting dump1090: {e}"); traceback.print_exc(); print("Continuing without dump1090 auto-start.")

eph = None; ts = None; observer_topos = None
A = 6378.137; F = 1 / 298.257223563; B = A * (1 - F)
airports_data = []; runways_data = collections.defaultdict(list); navaids_data = []
csv_headers = ['msg_type', 'icao', 'callsign', 'altitude', 'speed', 'track', 'lat', 'lon', 'vs', 'squawk', 'timestamp']
CSV_OUTPUT = False; CSV_FILENAME = 'adsb_data.csv'
def add_log(msg): print(f"[LOG] {datetime.now(timezone.utc).strftime('%H:%M:%S')} - {msg}")
def feet_to_km(feet): return feet * 0.3048 / 1000.0
def m_to_km(meters): return meters / 1000.0
def calculate_bearing(lat1_deg, lon1_deg, lat2_deg, lon2_deg):
    if abs(lat1_deg - lat2_deg) < 1e-9 and abs(lon1_deg - lon2_deg) < 1e-9: return 0.0
    lat1_rad,lon1_rad,lat2_rad,lon2_rad=map(radians,[lat1_deg,lon1_deg,lat2_deg,lon2_deg]);delta_lon=lon2_rad-lon1_rad
    y=sin(delta_lon)*cos(lat2_rad);x=cos(lat1_rad)*sin(lat2_rad)-sin(lat1_rad)*cos(lat2_rad)*cos(delta_lon)
    return (degrees(atan2(y,x))+360)%360
def destination_point(lat_deg, lon_deg, bearing_deg, distance_km):
    if distance_km==0:return lat_deg,lon_deg
    lat1_rad,lon1_rad,bearing_rad=radians(lat_deg),radians(lon_deg),radians(bearing_deg)
    ang_dist=distance_km/EARTH_RADIUS_KM;sin_lat1,cos_lat1=sin(lat1_rad),cos(lat1_rad)
    cos_ang,sin_ang=cos(ang_dist),sin(ang_dist)
    sin_lat2_arg=max(-1.0,min(1.0,sin_lat1*cos_ang+cos_lat1*sin_ang*cos(bearing_rad)));lat2_rad=asin(sin_lat2_arg)
    lon2_y=sin(bearing_rad)*sin_ang*cos_lat1;lon2_x=cos_ang-sin_lat1*sin(lat2_rad)
    delta_lon_rad=atan2(lon2_y,lon2_x)if not(abs(lon2_y)<1e-12 and abs(lon2_x)<1e-12)else 0.0
    lon2_rad=lon1_rad+delta_lon_rad;lat2_deg,lon2_deg=degrees(lat2_rad),degrees(lon2_rad)
    return lat2_deg,(lon2_deg+180)%360-180
def point_line_segment_distance(px, py, x1, y1, x2, y2):
    l_mag_sq=(x2-x1)**2+(y2-y1)**2;
    if l_mag_sq==0:return hypot(px-x1,py-y1)
    t=max(0,min(1,((px-x1)*(x2-x1)+(py-y1)*(y2-y1))/l_mag_sq))
    return hypot(px-(x1+t*(x2-x1)),py-(y1+t*(y2-y1)))
def parse_basestation_line(line):
    fields=line.strip().split(',')
    if len(fields)<22 or fields[0]!='MSG':return None
    try:
        msg_type,icao=fields[1],fields[4].upper();
        if not icao or len(icao)!=6:return None
        callsign=fields[10].strip()or None;altitude=int(fields[11])if fields[11]else None
        speed=float(fields[12])if fields[12]else None;track=float(fields[13])if fields[13]else None
        lat=float(fields[14])if fields[14]else None;lon=float(fields[15])if fields[15]else None
        vs=int(fields[16])if fields[16]else None;squawk=fields[17]if fields[17]else None
        timestamp=datetime.now(timezone.utc)
        if lat is not None and not(-90<=lat<=90):lat=None
        if lon is not None and not(-180<=lon<=180):lon=None
        vs_eff=0 if vs is not None and abs(vs)<64 else vs
        return{'msg_type':msg_type,'icao':icao,'callsign':callsign,'altitude':altitude,'speed':speed,'track':track,'lat':lat,'lon':lon,'vs':vs_eff,'squawk':squawk,'timestamp':timestamp,'conflict':None,'event_ids':set()}
    except(ValueError,IndexError):return None
def haversine(lat1, lon1, lat2, lon2):
    R=EARTH_RADIUS_KM;
    if None in[lat1,lon1,lat2,lon2]:return float('inf')
    lat1r,lon1r,lat2r,lon2r=map(radians,[lat1,lon1,lat2,lon2]);dlat=lat2r-lat1r;dlon=lon2r-lon1r
    a=sin(dlat/2)**2+cos(lat1r)*cos(lat2r)*sin(dlon/2)**2
    return R*2*atan2(sqrt(a),sqrt(1-a))
def effective_radius_at_lat(lat, altitude_ft_msl):
    lat_rad=radians(lat);cos_lat_sq=cos(lat_rad)**2;sin_lat_sq=sin(lat_rad)**2
    den=(A**2*cos_lat_sq+B**2*sin_lat_sq)
    R_local=B if den==0 else sqrt((A**4*cos_lat_sq+B**4*sin_lat_sq)/den)
    return R_local+feet_to_km(altitude_ft_msl if altitude_ft_msl is not None else 0)
def spherical_to_cartesian(lat, lon, altitude_ft):
    if None in[lat,lon,altitude_ft]:return None
    lat_r,lon_r,h=radians(lat),radians(lon),feet_to_km(altitude_ft)
    e2=2*F-F**2;sin_l,cos_l=sin(lat_r),cos(lat_r)
    N_den=sqrt(1-e2*sin_l**2);
    if N_den==0:return None
    N=A/N_den;X=(N+h)*cos_l*cos(lon_r);Y=(N+h)*cos_l*sin(lon_r);Z=(N*(1-e2)+h)*sin_l
    return(X,Y,Z)
def angle_between(user_lat, user_lon, user_alt_ft, lat1, lon1, alt1_ft, lat2, lon2, alt2_ft):
    u,a1,a2=spherical_to_cartesian(user_lat,user_lon,user_alt_ft),spherical_to_cartesian(lat1,lon1,alt1_ft),spherical_to_cartesian(lat2,lon2,alt2_ft)
    if None in[u,a1,a2]:return 180.0
    v1=(a1[0]-u[0],a1[1]-u[1],a1[2]-u[2]);v2=(a2[0]-u[0],a2[1]-u[1],a2[2]-u[2])
    m1_sq,m2_sq=sum(c*c for c in v1),sum(c*c for c in v2)
    if m1_sq==0 or m2_sq==0:return 180.0
    dot=sum(c1*c2 for c1,c2 in zip(v1,v2))
    return degrees(acos(max(-1.0,min(1.0,dot/(sqrt(m1_sq)*sqrt(m2_sq))))))
def predict_position(lat, lon, altitude_ft, speed_kts, track_deg, delta_t_sec, vs_fpm):
    if None in[lat,lon,altitude_ft,speed_kts,track_deg,vs_fpm]:return None,None,None
    vs_eff=0 if abs(vs_fpm)<64 else vs_fpm;alt_chg=(vs_eff/60.0)*delta_t_sec;new_alt=altitude_ft+alt_chg
    eff_rad=effective_radius_at_lat(lat,altitude_ft+alt_chg/2.0)
    if eff_rad<=0:return None,None,None
    dist_km=speed_kts*1.852/3600.0*delta_t_sec
    if dist_km==0:return lat,lon,new_alt
    lat_r,lon_r,brg_r=radians(lat),radians(lon),radians(track_deg);delta_a=dist_km/eff_rad
    s_l1,c_l1=sin(lat_r),cos(lat_r);c_d,s_d=cos(delta_a),sin(delta_a)
    s_l_new_arg=max(-1.0,min(1.0,s_l1*c_d+c_l1*s_d*cos(brg_r)));n_lat_r=asin(s_l_new_arg)
    l2_y=sin(brg_r)*s_d*c_l1;l2_x=c_d-s_l1*sin(n_lat_r)
    d_lon_r=atan2(l2_y,l2_x)if not(abs(l2_y)<1e-12 and abs(l2_x)<1e-12)else 0.0
    n_lon_r=lon_r+d_lon_r;n_lat,n_lon=degrees(n_lat_r),degrees(n_lon_r)
    return n_lat,(n_lon+180)%360-180,new_alt
def calculate_transit_rectangle_for_aircraft(icao_code, current_time_utc):
    global aircraft_dict, eph, ts, lock, PREDICTION_HORIZON, SUN_ANGULAR_DIAMETER_DEG, MOON_ANGULAR_DIAMETER_DEG
    transit_rect_data={'sun':None,'moon':None}
    if not eph or not ts:return transit_rect_data
    with lock:ac_data=aircraft_dict.get(icao_code)
    if not ac_data:return transit_rect_data
    ac_lat,ac_lon,ac_alt,ac_spd,ac_trk,ac_vs=(ac_data.get(k)for k in('lat','lon','altitude','speed','track','vs'))
    if None in[ac_lat,ac_lon,ac_alt,ac_spd,ac_trk,ac_vs]:return transit_rect_data
    lat_s,lon_s,alt_s=predict_position(ac_lat,ac_lon,ac_alt,ac_spd,ac_trk,0.0,ac_vs)
    lat_e,lon_e,alt_e=predict_position(ac_lat,ac_lon,ac_alt,ac_spd,ac_trk,PREDICTION_HORIZON,ac_vs)
    if lat_s is None or lat_e is None:return transit_rect_data
    lat_s_n,lon_s_n,_=predict_position(ac_lat,ac_lon,ac_alt,ac_spd,ac_trk,0.1,ac_vs)
    trk_s_eff=ac_trk;
    if lat_s_n is not None:trk_s_eff=calculate_bearing(lat_s,lon_s,lat_s_n,lon_s_n)
    lat_e_n,lon_e_n,_=predict_position(ac_lat,ac_lon,ac_alt,ac_spd,ac_trk,PREDICTION_HORIZON+0.1,ac_vs)
    trk_e_eff=trk_s_eff;
    if lat_e_n is not None:trk_e_eff=calculate_bearing(lat_e,lon_e,lat_e_n,lon_e_n)
    def get_clr(la,lo,al,tk,t_sky,body_n,ang_d):
        if al is None or feet_to_km(al)*1000.0<=0:
            return None,None,None
        h_m=feet_to_km(al)*1000.0
        g_obs=Topos(latitude_degrees=la,longitude_degrees=lo,elevation_m=0.0)
        try:
            app=(eph['earth']+g_obs).at(t_sky).observe(eph[body_n]).apparent()
            b_alt,b_az,_=app.altaz()
            if radians(0.1) < b_alt.radians < radians(89.8): 
                tan_alt = tan(b_alt.radians)
                if abs(tan_alt) > 1e-6:
                    off_m=h_m/tan_alt;c_b=(b_az.degrees+180)%360;c_g=destination_point(la,lo,c_b,m_to_km(off_m))
                    h_w_m=h_m*tan(radians(ang_d/2.0));l_g=destination_point(c_g[0],c_g[1],(tk-90+360)%360,m_to_km(h_w_m))
                    r_g=destination_point(c_g[0],c_g[1],(tk+90)%360,m_to_km(h_w_m))
                    return c_g,l_g,r_g
        except Exception: # Simplified exception handling
            pass # Fall through to return None, None, None
        return None, None, None
    C0s,L0s,R0s=get_clr(lat_s,lon_s,alt_s,trk_s_eff,ts.utc(current_time_utc),'sun',SUN_ANGULAR_DIAMETER_DEG)
    Ces,Les,Res=get_clr(lat_e,lon_e,alt_e,trk_e_eff,ts.utc(current_time_utc+timedelta(seconds=PREDICTION_HORIZON)),'sun',SUN_ANGULAR_DIAMETER_DEG)
    if C0s and Ces:transit_rect_data['sun']=[L0s,R0s,Res,Les,C0s,Ces]
    C0m,L0m,R0m=get_clr(lat_s,lon_s,alt_s,trk_s_eff,ts.utc(current_time_utc),'moon',MOON_ANGULAR_DIAMETER_DEG)
    Cem,Lem,Rem=get_clr(lat_e,lon_e,alt_e,trk_e_eff,ts.utc(current_time_utc+timedelta(seconds=PREDICTION_HORIZON)),'moon',MOON_ANGULAR_DIAMETER_DEG)
    if C0m and Cem:transit_rect_data['moon']=[L0m,R0m,Rem,Lem,C0m,Cem]
    return transit_rect_data
def load_airports(filename=AIRPORTS_CSV, types_to_show=None):
    if types_to_show is None: types_to_show=[]
    data,valid_types=[],set(types_to_show)
    try:
        with open(filename,mode='r',encoding='utf-8')as f:
            r=csv.DictReader(f);c,s=0,0
            for row in r:
                try:
                    ty,la,lo=row.get('type'),row.get('latitude_deg'),row.get('longitude_deg')
                    if ty in valid_types and la and lo:data.append({'ident':row['ident'],'type':ty,'name':row['name'],'lat':float(la),'lon':float(lo),'country':row.get('iso_country','')});c+=1
                    else:s+=1
                except(ValueError,TypeError,KeyError):s+=1
        print(f"Loaded {c} airports ({'/'.join(types_to_show)}) from {filename}. Skipped {s} rows.")
        return data
    except FileNotFoundError:print(f"Error: Airports file not found: {filename}");return[]
    except Exception as e:print(f"Error loading airports: {e}");traceback.print_exc();return[]
def load_runways(filename=RUNWAYS_CSV, airport_idents_to_load=None):
    if airport_idents_to_load is None:airport_idents_to_load=set()
    data=collections.defaultdict(list)
    if not airport_idents_to_load:print("Warning: No airport idents for runway load.");return data
    try:
        with open(filename,mode='r',encoding='utf-8')as f:
            r=csv.DictReader(f);c,s=0,0
            for row in r:
                try:
                    ap_id=row.get('airport_ident')
                    if ap_id in airport_idents_to_load:
                        le_lat,le_lon,he_lat,he_lon,le,wi=float(row['le_latitude_deg']),float(row['le_longitude_deg']),float(row['he_latitude_deg']),float(row['he_longitude_deg']),float(row.get('length_ft',0)),float(row.get('width_ft',0))
                        data[ap_id].append({'le_lat':le_lat,'le_lon':le_lon,'he_lat':he_lat,'he_lon':he_lon,'length_ft':le,'width_ft':wi,'le_ident':row.get('le_ident',''),'he_ident':row.get('he_ident','')});c+=1
                    else:s+=1
                except(ValueError,TypeError,KeyError):s+=1
        print(f"Loaded {c} runways for {len(airport_idents_to_load)} airport(s) from {filename}. Skipped {s} rows.")
        return data
    except FileNotFoundError:print(f"Error: Runways file not found: {filename}");return data
    except Exception as e:print(f"Error loading runways: {e}");traceback.print_exc();return data
def load_navaids(filename=NAVAIDS_CSV, types_to_show=None):
    if types_to_show is None:types_to_show=[]
    data,valid_types=[],set(types_to_show)
    try:
        with open(filename,mode='r',encoding='utf-8')as f:
            r=csv.DictReader(f);c,s=0,0
            for row in r:
                try:
                    ty,la,lo=row.get('type'),row.get('latitude_deg'),row.get('longitude_deg')
                    if ty in valid_types and la and lo:data.append({'ident':row['ident'],'type':ty,'name':row['name'],'lat':float(la),'lon':float(lo)});c+=1
                    else:s+=1
                except(ValueError,TypeError,KeyError):s+=1
        print(f"Loaded {c} navaids ({'/'.join(types_to_show)}) from {filename}. Skipped {s} rows.")
        return data
    except FileNotFoundError:print(f"Error: Navaids file not found: {filename}");return[]
    except Exception as e:print(f"Error loading navaids: {e}");traceback.print_exc();return[]
def calculate_glideslope_details(runway_info, selected_runway_end_ident, airport_type):
    gs_len=GLIDESLOPE_LENGTH_SMALL_KM
    if airport_type=='large_airport':gs_len=GLIDESLOPE_LENGTH_LARGE_KM
    elif airport_type=='medium_airport':gs_len=GLIDESLOPE_LENGTH_MEDIUM_KM
    s_lat,s_lon,app_brg=None,None,None
    le_id,he_id=runway_info.get('le_ident',''),runway_info.get('he_ident','')
    le_lat,le_lon,he_lat,he_lon=runway_info.get('le_lat'),runway_info.get('le_lon'),runway_info.get('he_lat'),runway_info.get('he_lon')
    if None in[le_lat,le_lon,he_lat,he_lon]:return None
    if selected_runway_end_ident==le_id and le_id:s_lat,s_lon,app_brg=le_lat,le_lon,calculate_bearing(he_lat,he_lon,le_lat,le_lon)
    elif selected_runway_end_ident==he_id and he_id:s_lat,s_lon,app_brg=he_lat,he_lon,calculate_bearing(le_lat,le_lon,he_lat,he_lon)
    else:return None
    if s_lat is None or app_brg is None:return None
    e_lat,e_lon=destination_point(s_lat,s_lon,app_brg,gs_len)
    return{'start_lat':s_lat,'start_lon':s_lon,'end_lat':e_lat,'end_lon':e_lon,'bearing_deg':app_brg,'length_km':gs_len,'runway_end_ident':selected_runway_end_ident}
def update_aircraft(data):
    with lock:
        icao,now,lat,lon,alt=data['icao'],data['timestamp'],data.get('lat'),data.get('lon'),data.get('altitude')
        if icao in aircraft_dict:
            entry=aircraft_dict[icao]
            ev_ids=entry.get('event_ids',set())
            for k,v in data.items():
                if v is not None:entry[k]=v
                elif k not in entry:entry[k]=None
            entry['timestamp'],entry['event_ids']=now,ev_ids
            if lat is not None and lon is not None and alt is not None:
                if'history'not in entry:entry['history']=collections.deque(maxlen=min(max(int(AIRCRAFT_HISTORY_MINUTES*60/PREDICTION_INTERVAL)+5,50),MAX_HISTORY_POINTS_PER_AC))
                entry['history'].append((now,lat,lon,alt))
        else:
            base={k:None for k in csv_headers if k!='timestamp'};base.update(data);base['timestamp'],base['event_ids']=now,set()
            base['history']=collections.deque(maxlen=min(max(int(AIRCRAFT_HISTORY_MINUTES*60/PREDICTION_INTERVAL)+5,50),MAX_HISTORY_POINTS_PER_AC))
            if lat is not None and lon is not None and alt is not None:base['history'].append((now,lat,lon,alt))
            aircraft_dict[icao]=base
def get_active_aircraft():
    now,active,expired=datetime.now(timezone.utc),[],[]
    with lock:
        all_icao=list(aircraft_dict.keys())
        for icao in all_icao:
            ac=aircraft_dict[icao]
            if(now-ac['timestamp']).total_seconds()>AIRCRAFT_TIMEOUT:expired.append(icao)
            elif all(ac.get(k)is not None for k in('lat','lon','altitude','speed','track','vs')):active.append(ac.copy())
        for icao in expired:
            ac=aircraft_dict.pop(icao,None)
            if ac:
                for eid in list(ac.get('event_ids',set())):
                    if eid in event_dict:
                        if event_dict[eid]['type']=='AC-AC':
                            pid=ac.get('callsign')or icao 
                            if pid and pid in event_dict[eid]['callsigns']:event_dict[eid]['callsigns'].remove(pid)
                            if len(event_dict[eid]['callsigns'])<2:del event_dict[eid]
                        else:del event_dict[eid]
            global selected_aircraft_for_transit_icao
            if selected_aircraft_for_transit_icao==icao:selected_aircraft_for_transit_icao=None
    active.sort(key=lambda x:x['icao']);return active
def predict_conflicts():
    while running:
        active_ac = get_active_aircraft()
        n_active = len(active_ac)
        now = datetime.now(timezone.utc)
        for i in range(n_active):
            for j in range(i + 1, n_active):
                ac1,ac2=active_ac[i],active_ac[j]
                ac1_lat,ac1_lon,ac2_lat,ac2_lon=ac1.get('lat'),ac1.get('lon'),ac2.get('lat'),ac2.get('lon')
                if None in[ac1_lat,ac1_lon,ac2_lat,ac2_lon]:continue
                if haversine(USER_LAT,USER_LON,ac1_lat,ac1_lon)>CONFLICT_RADIUS_KM or haversine(USER_LAT,USER_LON,ac2_lat,ac2_lon)>CONFLICT_RADIUS_KM:continue
                alt1,alt2=ac1.get('altitude'),ac2.get('altitude')
                if alt1 is not None and alt2 is not None:
                    if abs(alt1-alt2)>5000:continue
                else:continue
                conflict_found=False
                for dt in np.arange(0,PREDICTION_HORIZON+PREDICTION_STEP,PREDICTION_STEP):
                    p1=predict_position(ac1.get('lat'),ac1.get('lon'),alt1,ac1.get('speed'),ac1.get('track'),dt,ac1.get('vs'))
                    p2=predict_position(ac2.get('lat'),ac2.get('lon'),alt2,ac2.get('speed'),ac2.get('track'),dt,ac2.get('vs'))
                    if p1[0]is None or p2[0]is None:continue
                    ang=angle_between(USER_LAT,USER_LON,USER_ALT_FT,p1[0],p1[1],p1[2],p2[0],p2[1],p2[2])
                    if ang<=CONFLICT_ANGLE_DEG:
                        pt=now+timedelta(seconds=dt);eid=tuple(sorted((ac1['icao'],ac2['icao'])))+('AC-AC',)
                        cs=sorted([ac1.get('callsign')or ac1['icao'],ac2.get('callsign')or ac2['icao']])
                        el,en,ea=(p1[0]+p2[0])/2.0,(p1[1]+p2[1])/2.0,(p1[2]+p2[2])/2.0 if p1[2]is not None and p2[2]is not None else None
                        ed={'type':'AC-AC','callsigns':cs,'time':pt,'angle':ang,'last_update':now,'lat':el,'lon':en,'alt':ea}
                        with lock:
                            event_dict[eid]=ed;ac1m,ac2m=aircraft_dict.get(ac1['icao']),aircraft_dict.get(ac2['icao'])
                            if ac1m:ac1m.setdefault('event_ids',set()).add(eid);ac1m['conflict']=ac1m.get('conflict')or f"AC-AC: {cs[0]}/{cs[1]} @{pt.strftime('%H:%M:%S')} ({ang:.1f}°)"
                            if ac2m:ac2m.setdefault('event_ids',set()).add(eid);ac2m['conflict']=ac2m.get('conflict')or f"AC-AC: {cs[0]}/{cs[1]} @{pt.strftime('%H:%M:%S')} ({ang:.1f}°)"
                        if not conflict_found:add_log(f"Predicted AC-AC: {cs[0]}-{cs[1]} near {pt.strftime('%H:%M:%S')} ({ang:.1f}°)");conflict_found=True
                        break
        with lock:
            active_eids={eid[0]for eid,ev in event_dict.items()if ev['type']in['AC-Sun','AC-Moon']}|{eid[i]for eid,ev in event_dict.items()if ev['type']=='AC-AC'for i in range(2)}
            for icao,data in aircraft_dict.items():
                if icao not in active_eids:data['conflict']=None
        time.sleep(PREDICTION_INTERVAL)
    print("Conflict prediction thread exiting.")
def predict_celestial_conflicts():
    if eph is None or observer_topos is None:print("Celestial (user view) predictions disabled.");return
    while running:
        active_ac,now=get_active_aircraft(),datetime.now(timezone.utc)
        for ac in active_ac:
            icao=ac['icao']
            csign=ac.get('callsign')or icao;conflict_found=False
            lat,lon,alt,spd,trk,vs=(ac.get(k)for k in('lat','lon','altitude','speed','track','vs'))
            if None in[lat,lon,alt,spd,trk,vs]:continue
            for dt in np.arange(0,PREDICTION_HORIZON+PREDICTION_STEP,PREDICTION_STEP):
                pt=now+timedelta(seconds=dt);pl,pn,pa=predict_position(lat,lon,alt,spd,trk,dt,vs)
                if pl is None:continue
                try:
                    t_sky,user_obs_t=ts.utc(pt),eph['earth']+observer_topos
                    ac_topo=Topos(latitude_degrees=pl,longitude_degrees=pn,elevation_m=feet_to_km(pa)*1000)
                    ac_app=user_obs_t.at(t_sky).observe(eph['earth']+ac_topo).apparent()
                    try:
                        sun_app=user_obs_t.at(t_sky).observe(eph['sun']).apparent()
                        ang_s=sun_app.separation_from(ac_app).degrees
                        if ang_s<=CONFLICT_ANGLE_DEG:
                            eid=(icao,'AC-Sun');ed={'type':'AC-Sun','callsigns':[csign],'time':pt,'angle':ang_s,'last_update':now,'lat':pl,'lon':pn,'alt':pa}
                            with lock:event_dict[eid]=ed;ace=aircraft_dict.get(icao);ace.setdefault('event_ids',set()).add(eid);ace['conflict']=ace.get('conflict')or f"AC-Sun: {csign} @{pt.strftime('%H:%M:%S')} ({ang_s:.1f}°)"
                            if not conflict_found:add_log(f"Predicted AC-Sun (User View): {csign} @ {pt.strftime('%H:%M:%S')} ({ang_s:.1f}°)");conflict_found=True;break
                    except:pass
                    if conflict_found:continue
                    try:
                        moon_app=user_obs_t.at(t_sky).observe(eph['moon']).apparent()
                        ang_m=moon_app.separation_from(ac_app).degrees
                        if ang_m<=CONFLICT_ANGLE_DEG:
                            eid=(icao,'AC-Moon');ed={'type':'AC-Moon','callsigns':[csign],'time':pt,'angle':ang_m,'last_update':now,'lat':pl,'lon':pn,'alt':pa}
                            with lock:event_dict[eid]=ed;ace=aircraft_dict.get(icao);ace.setdefault('event_ids',set()).add(eid);ace['conflict']=ace.get('conflict')or f"AC-Moon: {csign} @{pt.strftime('%H:%M:%S')} ({ang_m:.1f}°)"
                            if not conflict_found:add_log(f"Predicted AC-Moon (User View): {csign} @ {pt.strftime('%H:%M:%S')} ({ang_m:.1f}°)");conflict_found=True;break
                    except:pass
                except:pass
        time.sleep(PREDICTION_INTERVAL)
    print("Celestial (user view) prediction thread exiting.")
def clean_expired_events():
    global history_event_count
    while running:
        now,to_remove=datetime.now(timezone.utc),[]
        with lock:
            all_eids=list(event_dict.keys())
            for eid in all_eids:
                ev=event_dict.get(eid)
                if ev and'last_update'in ev:
                    if(now-ev['last_update']).total_seconds()>EVENT_TIMEOUT:to_remove.append(eid)
                elif ev:to_remove.append(eid) # Should not happen if last_update is always set
            for eid in to_remove:
                ev_data_to_log = event_dict.pop(eid, None) # Pop first
                if ev_data_to_log: # Check if pop was successful
                    pt=ev_data_to_log.get('time')
                    et,ecs=ev_data_to_log.get('type','UNK'),ev_data_to_log.get('callsigns',[])
                    if pt and pt<=now:history_event_count+=1;add_log(f"Event Recorded: {et} involving {ecs} (Predicted @ {pt.strftime('%H:%M:%S')})")
                    else:add_log(f"Prediction Expired: {et} involving {ecs} (Was predicted @ {pt.strftime('%H:%M:%S')if pt else'N/A'})")
                    try:
                        if et=='AC-AC'and len(eid)==3:
                            i1,i2,_=eid;a1,a2=aircraft_dict.get(i1),aircraft_dict.get(i2)
                            if a1 and 'event_ids' in a1:a1['event_ids'].discard(eid)
                            if a2 and 'event_ids' in a2:a2['event_ids'].discard(eid)
                        elif et in['AC-Sun','AC-Moon']and len(eid)==2:
                            i,_=eid;ace=aircraft_dict.get(i)
                            if ace and 'event_ids' in ace:ace['event_ids'].discard(eid)
                    except Exception as e_d:print(f"Warn: Error discarding event ID {eid}: {e_d}")
            active_eids={eid[0]for eid,ev in event_dict.items()if ev['type']in['AC-Sun','AC-Moon']}|{eid[i]for eid,ev in event_dict.items()if ev['type']=='AC-AC'for i in range(2)}
            for icao,data in aircraft_dict.items():
                if icao not in active_eids:data['conflict']=None
        time.sleep(1)
    print("Event cleaner thread exiting.")
def start_listener():
    global DUMP1090_CONNECTED
    while running:
        print(f"[*] Connecting to dump1090 at {HOST}:{PORT}...")
        try:
            with socket.socket(socket.AF_INET,socket.SOCK_STREAM)as s:
                s.settimeout(10.0);s.connect((HOST,PORT));print("[*] Connected to dump1090.")
                with lock:DUMP1090_CONNECTED=True
                s.settimeout(None);buffer=''
                while running:
                    try:
                        data=s.recv(4096)
                        if not data:print("[!] Connection closed by remote host.");break
                        buffer+=data.decode('utf-8',errors='ignore')
                        while'\n'in buffer:
                            line,buffer=buffer.split('\n',1)
                            if not line.strip():continue
                            parsed=parse_basestation_line(line)
                            if parsed:update_aircraft(parsed)
                    except socket.timeout:print("[!] Socket read timeout (unexpected).");break
                    except OSError as e:print(f"[!] Socket error: {e}");break
                    except Exception as e:print(f"[!] Error processing data: {e}");traceback.print_exc();continue
        except socket.timeout:print(f"[*] Connection attempt timed out. Retrying...")
        except ConnectionRefusedError:print(f"[*] Connection refused by {HOST}:{PORT}. Is dump1090 running? Retrying...")
        except OSError as e:print(f"[*] OS Error connecting: {e}. Retrying...")
        except Exception as e:print(f"[*] Unexpected error connecting: {e}. Retrying...")
        with lock:DUMP1090_CONNECTED=False
        if running:print("[*] Waiting 5 seconds before retry...");time.sleep(5)
    print("Listener thread exiting.")

class ConfigDialog(tk.Toplevel): 
    def __init__(self, master, current_config, result_container):
        super().__init__(master); self.transient(master); self.title("Configuration Settings")
        if ICON_PATH:
            try: self.iconbitmap(ICON_PATH)
            except Exception as e: print(f"Warning: Failed to set ConfigDialog icon: {e}")
        self.result_container = result_container; self.result_container[:] = [None]; self.initial_config = current_config.copy()
        self.notebook = ttk.Notebook(self)
        self.frame_user = ttk.Frame(self.notebook, padding="10")
        self.frame_predict = ttk.Frame(self.notebook, padding="10")
        self.frame_display = ttk.Frame(self.notebook, padding="10")
        self.frame_vector_map = ttk.Frame(self.notebook, padding="10") 
        self.notebook.add(self.frame_user, text='User & Network')
        self.notebook.add(self.frame_predict, text='Prediction')
        self.notebook.add(self.frame_display, text='Display')
        self.notebook.add(self.frame_vector_map, text='Vector Map Layers')
        self.notebook.pack(expand=True, fill="both", padx=5, pady=5)
        self.entries={};self.airport_checkboxes={};self.navaid_checkboxes={};self.show_history_cb=None;self.show_events_cb=None;self.error_label=None;self.show_glideslope_cb=None;self.show_range_rings_cb=None;self.range_ring_spacing_combo=None;self.show_all_transit_cb=None;self.show_velocity_vector_cb=None;self.velocity_vector_combo=None;self.vector_layer_checkboxes={}
        self._create_user_widgets(current_config);self._create_predict_widgets(current_config);self._create_display_widgets(current_config);self._create_vector_map_widgets(current_config)
        button_frame=ttk.Frame(self);self.error_label=tk.Label(button_frame,text="",fg="red",justify=tk.LEFT,wraplength=350);self.error_label.pack(side=tk.LEFT,fill=tk.X,expand=True,padx=5)
        ok_button=ttk.Button(button_frame,text="OK",width=10,command=self.on_ok);ok_button.pack(side=tk.RIGHT,padx=5)
        cancel_button=ttk.Button(button_frame,text="Cancel",width=10,command=self.on_cancel);cancel_button.pack(side=tk.RIGHT,padx=5)
        button_frame.pack(fill="x",padx=10,pady=(5,10));self.protocol("WM_DELETE_WINDOW",self.on_cancel);self.update_idletasks();self.center_dialog()
    def center_dialog(self):
        try:
            self.update_idletasks();sw,sh=self.winfo_screenwidth(),self.winfo_screenheight();dw,dh=self.winfo_reqwidth(),self.winfo_reqheight()
            dw=max(dw,450);dh=max(dh,560);x,y=max(0,(sw//2)-(dw//2)),max(0,(sh//2)-(dh//2));self.geometry(f"{dw}x{dh}+{x}+{y}")
        except Exception as e:print(f"Warn: Could not center dialog: {e}");self.geometry("450x560+200+200")
    def _create_user_widgets(self,cfg):
        f,r=self.frame_user,0;df=ttk.LabelFrame(f,text="Dump1090 / Network",padding="5");df.grid(row=r,column=0,columnspan=3,sticky="ew",pady=5);r+=1
        tk.Label(df,text="Host:").grid(row=0,column=0,sticky="w",padx=5,pady=2);eh=tk.Entry(df,width=20);eh.grid(row=0,column=1,sticky="ew",padx=5,pady=2);eh.insert(0,str(cfg.get("host",DEFAULT_HOST)));self.entries["host"]=eh
        tk.Label(df,text="Port:").grid(row=1,column=0,sticky="w",padx=5,pady=2);ep=tk.Entry(df,width=8);ep.grid(row=1,column=1,sticky="w",padx=5,pady=2);ep.insert(0,str(cfg.get("port",DEFAULT_PORT)));self.entries["port"]=ep
        tk.Label(df,text="Device Index:").grid(row=2,column=0,sticky="w",padx=5,pady=2);edi=tk.Entry(df,width=5);edi.grid(row=2,column=1,sticky="w",padx=5,pady=2);edi.insert(0,str(cfg.get("device_index",DEFAULT_DUMP1090_DEVICE_INDEX)));self.entries["device_index"]=edi;tk.Label(df,text="(Restart Required)").grid(row=2,column=2,sticky="w",padx=5,pady=2)
        tk.Label(df,text="Gain:").grid(row=3,column=0,sticky="w",padx=5,pady=2);eg=tk.Entry(df,width=8);eg.grid(row=3,column=1,sticky="w",padx=5,pady=2);eg.insert(0,str(cfg.get("gain",DEFAULT_DUMP1090_GAIN)));self.entries["gain"]=eg;tk.Label(df,text="(e.g. 49.6, auto: -10) (Restart Required)").grid(row=3,column=2,sticky="w",padx=5,pady=2)
        lf=ttk.LabelFrame(f,text="User Location (Map Center & Conflicts View)",padding="5");lf.grid(row=r,column=0,columnspan=3,sticky="ew",pady=5);r+=1
        tk.Label(lf,text="Latitude (°):").grid(row=0,column=0,sticky="w",padx=5,pady=2);ela=tk.Entry(lf,width=15);ela.grid(row=0,column=1,sticky="ew",padx=5,pady=2);ela.insert(0,str(cfg.get("lat",DEFAULT_LAT_DEG)));self.entries["lat"]=ela
        tk.Label(lf,text="Longitude (°):").grid(row=1,column=0,sticky="w",padx=5,pady=2);elo=tk.Entry(lf,width=15);elo.grid(row=1,column=1,sticky="ew",padx=5,pady=2);elo.insert(0,str(cfg.get("lon",DEFAULT_LON_DEG)));self.entries["lon"]=elo
        tk.Label(lf,text="Altitude (m):").grid(row=2,column=0,sticky="w",padx=5,pady=2);eal=tk.Entry(lf,width=10);eal.grid(row=2,column=1,sticky="w",padx=5,pady=2);eal.insert(0,str(cfg.get("alt_m",DEFAULT_ALT_M)));self.entries["alt_m"]=eal;f.columnconfigure(1,weight=1)
    def _create_predict_widgets(self,cfg):
        f,r=self.frame_predict,0
        def add(l,k,d,w=8):nonlocal r;tk.Label(f,text=l).grid(row=r,column=0,sticky="w",padx=5,pady=2);e=tk.Entry(f,width=w);e.grid(row=r,column=1,sticky="w",padx=5,pady=2);e.insert(0,str(cfg.get(k,d)));self.entries[k]=e;r+=1
        add("Aircraft Timeout (s):","aircraft_timeout",DEFAULT_AIRCRAFT_TIMEOUT_SEC);add("Prediction Interval (s):","pred_interval",DEFAULT_PREDICTION_INTERVAL_SEC);add("Prediction Horizon (s):","pred_horizon",DEFAULT_PREDICTION_HORIZON_SEC);add("Prediction Step (s):","pred_step",DEFAULT_PREDICTION_STEP_SEC);add("Conflict Angle (°):","conflict_angle",DEFAULT_CONFLICT_ANGLE_DEG);add("Event Timeout (s):","event_timeout",cfg.get("event_timeout",EVENT_TIMEOUT));add("Conflict Radius (km):","conflict_radius_km",cfg.get("conflict_radius_km",CONFLICT_RADIUS_KM));f.columnconfigure(1,weight=1)
    def _create_display_widgets(self,cfg):
        f,dro=self.frame_display,0;gf=ttk.LabelFrame(f,text="General Map Display",padding="5");gf.grid(row=dro,column=0,columnspan=2,sticky="ew",pady=5);cr=0
        tk.Label(gf,text="Aircraft History (min):").grid(row=cr,column=0,sticky="w",padx=5,pady=2);ehm=tk.Entry(gf,width=8);ehm.grid(row=cr,column=1,sticky="w",padx=5,pady=2);ehm.insert(0,str(cfg.get("history_minutes",DEFAULT_AIRCRAFT_HISTORY_MINUTES)));self.entries["history_minutes"]=ehm;cr+=1
        self.show_history_cb=ttk.Checkbutton(gf,text="Show History Trails");self.show_history_cb.grid(row=cr,column=0,columnspan=2,sticky="w",padx=5,pady=2);cr+=1;self.show_history_cb.state(['selected'if cfg.get("show_history",DEFAULT_SHOW_AIRCRAFT_HISTORY)else'!selected','!alternate'])
        self.show_velocity_vector_cb=ttk.Checkbutton(gf,text="Show Velocity Vectors",command=self._toggle_velocity_vector_combo);self.show_velocity_vector_cb.grid(row=cr,column=0,columnspan=2,sticky="w",padx=5,pady=2);cr+=1;self.show_velocity_vector_cb.state(['selected'if cfg.get("show_velocity_vector",DEFAULT_SHOW_VELOCITY_VECTOR)else'!selected','!alternate'])
        tk.Label(gf,text="  Length:").grid(row=cr,column=0,sticky="w",padx=5,pady=2)
        self.velocity_vector_combo=ttk.Combobox(gf,values=[f"{v} min"for v in VELOCITY_VECTOR_OPTIONS_MIN],state="readonly",width=8);self.velocity_vector_combo.grid(row=cr,column=1,sticky="w",padx=5,pady=2);cr+=1
        try:self.velocity_vector_combo.current(VELOCITY_VECTOR_OPTIONS_MIN.index(float(cfg.get("velocity_vector_minutes",DEFAULT_VELOCITY_VECTOR_MINUTES))))
        except ValueError:self.velocity_vector_combo.current(VELOCITY_VECTOR_OPTIONS_MIN.index(DEFAULT_VELOCITY_VECTOR_MINUTES))
        self._toggle_velocity_vector_combo()
        self.show_events_cb=ttk.Checkbutton(gf,text="Show Event Locations");self.show_events_cb.grid(row=cr,column=0,columnspan=2,sticky="w",padx=5,pady=2);cr+=1;self.show_events_cb.state(['selected'if cfg.get("show_events",DEFAULT_SHOW_EVENT_LOCATIONS)else'!selected','!alternate'])
        self.show_glideslope_cb=ttk.Checkbutton(gf,text="Show Runway Glideslopes");self.show_glideslope_cb.grid(row=cr,column=0,columnspan=2,sticky="w",padx=5,pady=2);cr+=1;self.show_glideslope_cb.state(['selected'if cfg.get("show_glideslope",DEFAULT_SHOW_GLIDESLOPE)else'!selected','!alternate'])
        self.show_all_transit_cb=ttk.Checkbutton(gf,text="Show All Aircraft Transit Strips");self.show_all_transit_cb.grid(row=cr,column=0,columnspan=2,sticky="w",padx=5,pady=2);cr+=1;self.show_all_transit_cb.state(['selected'if cfg.get("show_all_transit_strips",DEFAULT_SHOW_ALL_TRANSIT_STRIPS)else'!selected','!alternate'])
        ttk.Separator(gf).grid(row=cr,column=0,columnspan=2,sticky="ew",pady=(10,5));cr+=1
        self.show_range_rings_cb=ttk.Checkbutton(gf,text="Show Range Rings");self.show_range_rings_cb.grid(row=cr,column=0,columnspan=2,sticky="w",padx=5,pady=2);cr+=1;self.show_range_rings_cb.state(['selected'if cfg.get("show_range_rings",DEFAULT_SHOW_RANGE_RINGS)else'!selected','!alternate'])
        tk.Label(gf,text="Range Ring Spacing:").grid(row=cr,column=0,sticky="w",padx=5,pady=2)
        self.range_ring_spacing_combo=ttk.Combobox(gf,values=[s+" NM"for s in RANGE_RING_OPTIONS_NM],state="readonly",width=8);self.range_ring_spacing_combo.grid(row=cr,column=1,sticky="w",padx=5,pady=2)
        try:self.range_ring_spacing_combo.current(RANGE_RING_OPTIONS_NM.index(cfg.get("range_ring_spacing_nm_str",DEFAULT_RANGE_RING_SPACING_NM_STR)))
        except ValueError:self.range_ring_spacing_combo.current(RANGE_RING_OPTIONS_NM.index(DEFAULT_RANGE_RING_SPACING_NM_STR))
        cr+=1;tk.Label(gf,text="Max Range Rings:").grid(row=cr,column=0,sticky="w",padx=5,pady=2);emr=tk.Entry(gf,width=5);emr.grid(row=cr,column=1,sticky="w",padx=5,pady=2);emr.insert(0,str(cfg.get("max_range_rings",DEFAULT_MAX_RANGE_RINGS)));self.entries["max_range_rings"]=emr
        dro+=1;aptf=ttk.LabelFrame(f,text="Show Airport Types",padding="5");aptf.grid(row=dro,column=0,sticky="nsew",pady=5,padx=5);self.airport_checkboxes={};cur_apt=set(cfg.get("show_airport_types",DEFAULT_SHOW_AIRPORT_TYPES))
        for i,at in enumerate(ALL_AIRPORT_TYPES):cb=ttk.Checkbutton(aptf,text=at.replace('_',' ').title());cb.grid(row=i,column=0,sticky="w");cb.state(['selected'if at in cur_apt else'!selected','!alternate']);self.airport_checkboxes[at]=cb
        navf=ttk.LabelFrame(f,text="Show Navaid Types",padding="5");navf.grid(row=dro,column=1,sticky="nsew",pady=5,padx=5);self.navaid_checkboxes={};cur_nav=set(cfg.get("show_navaid_types",DEFAULT_SHOW_NAVAID_TYPES))
        for i,ntd in enumerate(DISPLAY_NAVAID_TYPES):
            cb=ttk.Checkbutton(navf,text=ntd);cb.grid(row=i,column=0,sticky="w");chk=False
            if ntd in CONSOLIDATED_NAVAID_MAP:
                if any(t in cur_nav for t in CONSOLIDATED_NAVAID_MAP[ntd]):chk=True
            elif ntd in cur_nav:chk=True
            cb.state(['selected'if chk else'!selected','!alternate']);self.navaid_checkboxes[ntd]=cb
        f.columnconfigure(0,weight=1);f.columnconfigure(1,weight=1)

    def _create_vector_map_widgets(self,cfg):
        f = self.frame_vector_map 

        # Attempt to get a theme-appropriate background color for the canvas
        canvas_bg = "#f0f0f0" # Default fallback (a common light gray)
        try:
            style = ttk.Style()
            # 'TFrame' is a general style key for ttk.Frame background
            # The canvas is inside 'f' (self.frame_vector_map), which is a tab page (ttk.Frame).
            theme_lookup_bg = style.lookup('TFrame', 'background')
            if theme_lookup_bg:
                canvas_bg = theme_lookup_bg
            else:
                # Fallback: Get background of the parent frame 'f'
                # f.winfo_rgb returns (r,g,b) tuple with 0-65535 range. Convert to #rrggbb.
                rgb_tuple = f.winfo_rgb(f.cget('background')) # cget might give system color name
                # Ensure rgb_tuple components are valid before formatting
                if all(isinstance(val, int) for val in rgb_tuple):
                     canvas_bg = f"#{rgb_tuple[0]//256:02x}{rgb_tuple[1]//256:02x}{rgb_tuple[2]//256:02x}"
                else: # If cget returns a name like "SystemButtonFace" and winfo_rgb fails
                    # Try a more direct approach if possible or stick to fallback
                    pass # Stick to #f0f0f0 if complex conversion fails
        except (tk.TclError, Exception) as e_style:
            print(f"Warning: Could not determine ttk theme background for canvas, using fallback. Error: {e_style}")
            # canvas_bg remains "#f0f0f0"

        # Create the canvas with the determined background and no highlight border
        c = tk.Canvas(f, borderwidth=0, background=canvas_bg, highlightthickness=0)
        sb = ttk.Scrollbar(f, orient="vertical", command=c.yview)
        
        # sf is the scrollable frame *inside* the canvas. It's a ttk.Frame, so it should style itself.
        sf = ttk.Frame(c, padding="5") 

        sf.bind("<Configure>", lambda e: c.configure(scrollregion=c.bbox("all")))
        c.create_window((0, 0), window=sf, anchor="nw") # Place sf onto the canvas
        c.configure(yscrollcommand=sb.set)

        c.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        self.vector_layer_checkboxes = {}
        current_visibility = cfg.get("vector_layers_visibility", {}) # Use a clear variable name

        r = 0
        for layer_key, layer_config_val in VECTOR_LAYER_CONFIGS.items(): # Use clear variable names
            label_text = layer_config_val.get("label", layer_key.replace("_", " ").title())
            
            # BooleanVar should be parented to a widget that exists as long as the var is needed.
            # 'f' (the tab frame) or 'sf' (the scrollable frame) are good choices.
            var = tk.BooleanVar(sf) 
            var.set(current_visibility.get(layer_key, layer_config_val.get("default_on", False)))
            
            # Checkbuttons go into the scrollable frame 'sf'
            cb = ttk.Checkbutton(sf, text=label_text, variable=var) 
            cb.grid(row=r, column=0, sticky="w", padx=5, pady=2)
            self.vector_layer_checkboxes[layer_key] = var
            r += 1

    def _toggle_velocity_vector_combo(self):
        if hasattr(self,'show_velocity_vector_cb')and hasattr(self,'velocity_vector_combo'):self.velocity_vector_combo.config(state="readonly"if self.show_velocity_vector_cb.instate(['selected'])else"disabled")
    def validate_input(self):
        vc,err,ok={},[],True
        def get_val(k):w=self.entries.get(k);return w.get().strip()if w else""
        try:
            hs=get_val("host");
            if not hs:err.append("User & Network: Host cannot be empty.");ok=False
            else:vc["host"]=hs
            ps=get_val("port");
            try:p=int(ps);assert 0<p<65536;vc["port"]=p
            except:err.append("User & Network: Port must be 1-65535.");ok=False
            is_val=get_val("device_index"); # Renamed to avoid conflict
            try:di=int(is_val);assert di>=0;vc["device_index"]=di
            except:err.append("User & Network: Device Index must be >= 0.");ok=False
            gs=get_val("gain").lower()
            if gs!="agc"and gs!="-10"and gs:
                try:float(gs);vc["gain"]=gs
                except ValueError:err.append("User & Network: Gain must be numeric, 'agc', or '-10'.");ok=False
            else:vc["gain"]=gs
            las=get_val("lat");
            try:la=float(las);assert-90<=la<=90;vc["lat"]=la
            except:err.append("User & Network: Latitude must be -90 to 90.");ok=False
            los=get_val("lon");
            try:lo=float(los);assert-180<=lo<=180;vc["lon"]=lo
            except:err.append("User & Network: Longitude must be -180 to 180.");ok=False
            als=get_val("alt_m");
            try:vc["alt_m"]=float(als)
            except:err.append("User & Network: Altitude must be numeric.");ok=False
        except Exception as e:err.append(f"User & Network Tab Error: {e}");ok=False
        try:
            ts_val=get_val("aircraft_timeout"); 
            try:t=float(ts_val);assert t>0;vc["aircraft_timeout"]=t
            except:err.append("Prediction: Aircraft Timeout must be > 0.");ok=False
            is_val2=get_val("pred_interval"); 
            try:i_val=float(is_val2);assert i_val>0;vc["pred_interval"]=i_val 
            except:err.append("Prediction: Prediction Interval must be > 0.");ok=False
            hs_val=get_val("pred_horizon"); 
            try:h_val=float(hs_val);assert h_val>0;vc["pred_horizon"]=h_val 
            except:err.append("Prediction: Prediction Horizon must be > 0.");ok=False
            ss_val=get_val("pred_step") 
            try:
                s_val=float(ss_val);assert s_val>0; 
                if"pred_horizon"in vc and s_val>vc["pred_horizon"]:raise ValueError()
                vc["pred_step"]=s_val
            except:err.append("Prediction: Prediction Step must be > 0 and <= Horizon.");ok=False
            ans=get_val("conflict_angle");
            try:an=float(ans);assert 0<an<90;vc["conflict_angle"]=an
            except:err.append("Prediction: Conflict Angle must be > 0 and < 90.");ok=False
            ets=get_val("event_timeout");
            try:et=float(ets);assert et>0;vc["event_timeout"]=et
            except:err.append("Prediction: Event Timeout must be > 0.");ok=False
            rs=get_val("conflict_radius_km");
            try:r_val=float(rs);assert r_val>0;vc["conflict_radius_km"]=r_val 
            except:err.append("Prediction: Conflict Radius must be > 0.");ok=False
        except Exception as e:err.append(f"Prediction Tab Error: {e}");ok=False
        try:
            hms=get_val("history_minutes");
            try:hm=float(hms);assert hm>0;vc["history_minutes"]=hm
            except:err.append("Display: History Minutes must be > 0.");ok=False
            def is_sel(w):return w.instate(['selected'])if w and isinstance(w,ttk.Checkbutton)else False
            vc["show_history"]=is_sel(self.show_history_cb);vc["show_velocity_vector"]=is_sel(self.show_velocity_vector_cb)
            vc["show_events"]=is_sel(self.show_events_cb);vc["show_glideslope"]=is_sel(self.show_glideslope_cb)
            vc["show_all_transit_strips"]=is_sel(self.show_all_transit_cb);vc["show_range_rings"]=is_sel(self.show_range_rings_cb)
            svvd=self.velocity_vector_combo.get()
            try:
                svvs=svvd.split(" ")[0];svvf=float(svvs)
                if svvf in VELOCITY_VECTOR_OPTIONS_MIN:vc["velocity_vector_minutes"]=svvf
                else:err.append("Display: Invalid Velocity Vector Length.");ok=False
            except(ValueError,IndexError):err.append("Display: Invalid Velocity Vector Length format.");ok=False
            ssd=self.range_ring_spacing_combo.get();ssvs=ssd.split(" ")[0]
            if ssvs in RANGE_RING_OPTIONS_NM:vc["range_ring_spacing_nm_str"]=ssvs
            else:err.append("Display: Invalid Range Ring Spacing.");ok=False
            mrs=get_val("max_range_rings");
            try:mr=int(mrs);assert mr>0;vc["max_range_rings"]=mr
            except:err.append("Display: Max Range Rings must be int > 0.");ok=False
            vc["show_airport_types"]=[k for k,cb in self.airport_checkboxes.items()if is_sel(cb)]
            sdn=[k for k,cb in self.navaid_checkboxes.items()if is_sel(cb)];fnl=set()
            for dt_val in sdn: 
                if dt_val in CONSOLIDATED_NAVAID_MAP:fnl.update(CONSOLIDATED_NAVAID_MAP[dt_val])
                else:fnl.add(dt_val)
            vc["show_navaid_types"]=sorted(list(fnl))
        except Exception as e:err.append(f"Display Tab Error: {e}");ok=False
        try:
            vlv={};
            for lk,vt in self.vector_layer_checkboxes.items():vlv[lk]=vt.get()
            vc["vector_layers_visibility"]=vlv
        except Exception as e:err.append(f"Vector Map Layers Tab Error: {e}");ok=False
        if ok:return vc,[]
        else:return{},err
    def on_ok(self):
        if hasattr(self,'error_label')and self.error_label:self.error_label.config(text="")
        vd,err=self.validate_input()
        if err:
            if hasattr(self,'error_label')and self.error_label:self.error_label.config(text="\n".join(err))
        else:
            rs=False
            if str(vd.get("gain")).lower()!=str(self.initial_config.get("gain","")).lower():rs=True
            if str(vd.get("device_index"))!=str(self.initial_config.get("device_index")):rs=True
            vd["_requires_restart"]=rs
            try:self.result_container[:]=[vd]
            except Exception as se:print(f"CRITICAL: Failed to store result: {se}");return
            self.destroy_and_cleanup_master()
    def on_cancel(self):self.result_container[:]=[None];self.destroy_and_cleanup_master()
    def destroy_and_cleanup_master(self):
        try:self.destroy()
        except:pass
        refs=['entries','airport_checkboxes','navaid_checkboxes','show_history_cb','show_events_cb','show_glideslope_cb','show_range_rings_cb','range_ring_spacing_combo','show_all_transit_cb','velocity_vector_combo','show_velocity_vector_cb','vector_layer_checkboxes','error_label','frame_user','frame_predict','frame_display','frame_vector_map','notebook']
        for an in refs:
            if hasattr(self,an):
                av=getattr(self,an);
                if isinstance(av,dict):av.clear()
                delattr(self,an)
        try:
            if hasattr(self,'master')and self.master and self.master.winfo_exists():self.master.quit()
        except:pass
def config_dialog_thread_target(current_config, result_storage):
    root=None
    try:
        root=tk.Tk();root.geometry("+5000+5000");d=ConfigDialog(root,current_config,result_storage)
        try:d.update_idletasks();d.lift();d.grab_set();d.focus_set()
        except Exception as ef:print(f"Warn: Could not set focus/grab for config dialog: {ef}")
        root.mainloop()
    except Exception as e:print(f"ERROR in Tkinter config dialog thread: {e}");traceback.print_exc();result_storage[:]=[{"error":f"Config Dialog Thread Error: {e}\n{traceback.format_exc()}"}]
    finally:
        if root and root.winfo_exists():
            try:root.destroy()
            except:pass;time.sleep(0.1)
def open_config_dialog_threaded(current_config):
    global dialog_result_storage,dialog_thread
    if dialog_thread and dialog_thread.is_alive():print("Config dialog thread already running.");return
    dialog_result_storage[:]=[None]
    try:dialog_thread=threading.Thread(target=config_dialog_thread_target,args=(current_config,dialog_result_storage),daemon=True);dialog_thread.start()
    except Exception as e:print(f"Error starting config dialog thread: {e}");dialog_thread=None

class RunwayGlideslopeToggleDialog(tk.Toplevel): 
    def __init__(self, master, runway_details, result_container):
        super().__init__(master); self.transient(master); self.title("Toggle Runway Glideslopes")
        self.result_container = result_container; self.result_container[:] = [None]
        self.runway_info = runway_details['runway_data']; self.airport_ident = runway_details['airport_ident']
        self.end_vars = {}
        options_frame = ttk.Frame(self, padding="10"); options_frame.pack(expand=True, fill="both")
        ttk.Label(options_frame, text=f"Airport: {self.airport_ident}").pack(pady=2)
        le_ident_str, he_ident_str = self.runway_info.get('le_ident'), self.runway_info.get('he_ident')
        runway_display_name = "/".join(filter(None, [le_ident_str, he_ident_str])) or "Unknown Runway"
        ttk.Label(options_frame, text=f"Runway: {runway_display_name}").pack(pady=2)
        ttk.Separator(options_frame, orient='horizontal').pack(fill='x', pady=5)
        available_ends = [end for end in [le_ident_str, he_ident_str] if end]
        self.ok_button_enabled = bool(available_ends)
        if not available_ends: ttk.Label(options_frame, text="No runway end identifiers available.").pack(pady=10)
        else:
            for end_ident in available_ends:
                var = tk.BooleanVar(); glideslope_key = (self.airport_ident, end_ident)
                with lock: var.set(glideslope_key in active_glideslopes)
                self.end_vars[end_ident] = var
                cb = ttk.Checkbutton(options_frame, text=f"Show Glideslope for {end_ident}", variable=var); cb.pack(anchor=tk.W, padx=10, pady=2)
        button_frame = ttk.Frame(self)
        ok_button = ttk.Button(button_frame, text="OK", width=10, command=self.on_ok, state=tk.NORMAL if self.ok_button_enabled else tk.DISABLED); ok_button.pack(side=tk.RIGHT, padx=5)
        cancel_button = ttk.Button(button_frame, text="Cancel", width=10, command=self.on_cancel); cancel_button.pack(side=tk.RIGHT, padx=5)
        button_frame.pack(fill="x", padx=10, pady=(10, 10))
        self.protocol("WM_DELETE_WINDOW", self.on_cancel); self.update_idletasks(); self.center_dialog()
    def center_dialog(self):
        try:
            self.update_idletasks();sw,sh=self.winfo_screenwidth(),self.winfo_screenheight();dw,dh=self.winfo_reqwidth(),self.winfo_reqheight()
            dw=max(dw,280);dh=max(dh,150);x,y=max(0,(sw//2)-(dw//2)),max(0,(sh//2)-(dh//2));self.geometry(f"{dw}x{dh}+{x}+{y}")
        except: self.geometry("300x200+300+300")
    def on_ok(self): self.result_container[:] = [{k:v.get() for k,v in self.end_vars.items()}]; self.destroy_and_quit_master()
    def on_cancel(self): self.result_container[:] = [None]; self.destroy_and_quit_master()
    def destroy_and_quit_master(self):
        try: self.destroy()
        except: pass
        try:
            if hasattr(self,'master') and self.master and self.master.winfo_exists(): self.master.quit()
        except: pass
def runway_glideslope_toggle_dialog_thread_target(runway_details, result_storage): 
    root_rwy = None
    try:
        root_rwy = tk.Tk(); root_rwy.geometry("+5000+5000")
        dialog_rwy = RunwayGlideslopeToggleDialog(root_rwy, runway_details, result_storage)
        try: dialog_rwy.update_idletasks(); dialog_rwy.lift(); dialog_rwy.grab_set(); dialog_rwy.focus_set()
        except Exception as e_focus: print(f"Warning: Could not set focus/grab for runway dialog: {e_focus}")
        root_rwy.mainloop()
    except Exception as e: print(f"ERROR in Tkinter runway glideslope toggle dialog thread: {e}"); traceback.print_exc(); result_storage[:] = [{"error": f"Runway Dialog Error: {e}"}]
    finally:
        if root_rwy and root_rwy.winfo_exists():
            try: root_rwy.destroy()
            except: pass; time.sleep(0.1)
def open_runway_glideslope_toggle_dialog_threaded(runway_details, result_storage_list): 
    global dialog_runway_end_thread
    if dialog_runway_end_thread and dialog_runway_end_thread.is_alive(): print("Runway glideslope toggle dialog thread already running."); return
    result_storage_list[:] = [None]
    try: dialog_runway_end_thread = threading.Thread(target=runway_glideslope_toggle_dialog_thread_target, args=(runway_details, result_storage_list), daemon=True); dialog_runway_end_thread.start()
    except Exception as e: print(f"Error starting runway glideslope toggle dialog thread: {e}"); dialog_runway_end_thread = None

data_loading_thread = None; data_load_result = [None]
def reload_geographic_data_threaded_target(airport_filter_list, navaid_filter_list, result_container): 
    loaded_data = {'airports': [], 'runways': collections.defaultdict(list), 'navaids': []}
    try:
        current_airports = load_airports(types_to_show=airport_filter_list); loaded_data['airports'] = current_airports
        airport_idents = {apt['ident'] for apt in current_airports}; loaded_data['runways'] = load_runways(airport_idents_to_load=airport_idents)
        loaded_data['navaids'] = load_navaids(types_to_show=navaid_filter_list)
        result_container[:] = [loaded_data]
    except Exception as e: print(f"Data Load ERROR: {e}"); traceback.print_exc(); result_container[:] = [{"error": f"Data Load Error: {e}"}]

def is_point_in_polygon(point_x, point_y, polygon_vertices): 
    n = len(polygon_vertices); inside = False; px, py = point_x, point_y
    for i in range(n):
        p1x, p1y = polygon_vertices[i]; p2x, p2y = polygon_vertices[(i + 1) % n]
        if py > min(p1y, p2y) and py <= max(p1y, p2y) and px <= max(p1x, p2x) and p1y != p2y:
            if p1x == p2x or px <= (py - p1y) * (p2x - p1x) / (p2y - p1y) + p1x: inside = not inside
    return inside
def screen_to_geo(screen_x, screen_y, left_rect, scale, center_lat, center_lon): 
    if scale == 0: return None, None
    map_center_x = left_rect.left + left_rect.width // 2; map_center_y = left_rect.top + left_rect.height // 2
    dx_scaled = screen_x - map_center_x; dy_scaled = map_center_y - screen_y
    dx_km = dx_scaled / scale; dy_km = dy_scaled / scale
    local_rad = EARTH_RADIUS_KM; lon_fact = max(0.01, cos(radians(center_lat)))
    delta_lon_rad = dx_km / (local_rad * lon_fact); delta_lat_rad = dy_km / local_rad
    click_lon = (center_lon + degrees(delta_lon_rad) + 180) % 360 - 180
    click_lat = max(-90.0, min(90.0, center_lat + degrees(delta_lat_rad)))
    return click_lat, click_lon

# --- MODIFIED VECTOR DATA LOADING (uses fixed tolerance) ---
def load_specific_vector_layer_data(layer_key_to_load, config_for_layer, simplification_tolerance):
    global map_features_geodata
    map_features_geodata[layer_key_to_load] = []

    base_vector_path = resource_path(os.path.join("data", "map_vectors"))
    layer_dir_path = os.path.join(base_vector_path, layer_key_to_load)
    shapefile_name = config_for_layer.get("shp_filename", layer_key_to_load)
    shapefile_path = os.path.join(layer_dir_path, shapefile_name + ".shp")

    if os.path.exists(shapefile_path):
        try:
            with shapefile.Reader(shapefile_path) as sf:
                loaded_features_count = 0
                for shape_rec in sf.iterShapeRecords():
                    shape_type = shape_rec.shape.shapeType
                    if shape_type in [shapefile.POLYLINE, shapefile.POLYLINEZ, shapefile.POLYLINEM]:
                        for i in range(len(shape_rec.shape.parts)):
                            start_idx = shape_rec.shape.parts[i]
                            end_idx = shape_rec.shape.parts[i+1] if i < len(shape_rec.shape.parts) - 1 else len(shape_rec.shape.points)
                            segment_orig = [(lon, lat) for lon, lat in shape_rec.shape.points[start_idx:end_idx]]
                            if len(segment_orig) >= 2:
                                try:
                                    line_g = LineString(segment_orig)
                                    s_line = line_g.simplify(simplification_tolerance, preserve_topology=True)
                                    if s_line.geom_type == 'LineString': map_features_geodata[layer_key_to_load].append(list(s_line.coords)); loaded_features_count+=1
                                    elif s_line.geom_type == 'MultiLineString':
                                        for part in s_line.geoms: map_features_geodata[layer_key_to_load].append(list(part.coords)); loaded_features_count+=1
                                except Exception: map_features_geodata[layer_key_to_load].append(segment_orig); loaded_features_count+=1
                    elif shape_type in [shapefile.POLYGON, shapefile.POLYGONZ, shapefile.POLYGONM]:
                        s_poly_parts = []
                        for i in range(len(shape_rec.shape.parts)):
                            start_idx = shape_rec.shape.parts[i]
                            end_idx = shape_rec.shape.parts[i+1] if i < len(shape_rec.shape.parts) - 1 else len(shape_rec.shape.points)
                            ring_orig = [(lon, lat) for lon, lat in shape_rec.shape.points[start_idx:end_idx]]
                            if len(ring_orig) >= 3:
                                try:
                                    ring_line_g = LineString(ring_orig)
                                    s_ring_line = ring_line_g.simplify(simplification_tolerance, preserve_topology=True)
                                    if s_ring_line.geom_type == 'LineString': s_poly_parts.append(list(s_ring_line.coords))
                                    elif s_ring_line.geom_type == 'MultiLineString':
                                        for part in s_ring_line.geoms: s_poly_parts.append(list(part.coords))
                                except Exception: s_poly_parts.append(ring_orig)
                        if s_poly_parts: map_features_geodata[layer_key_to_load].append(s_poly_parts); loaded_features_count+=1
                    elif shape_type == shapefile.POINT and config_for_layer["type"] == "point":
                        map_features_geodata[layer_key_to_load].append(shape_rec.shape.points[0]); loaded_features_count+=1
        except shapefile.ShapefileException as e: print(f"Error reading shapefile {shapefile_path}: {e}")
        except Exception as e: print(f"Unexpected error loading layer {layer_key_to_load}: {e}")

# --- LOADING SCREEN FUNCTION ---
def show_loading_screen_and_load_data(screen, font, info_font):
    global running, airports_data, runways_data, navaids_data, eph, ts, observer_topos
    # Note: map_features_geodata is populated by load_specific_vector_layer_data

    loading_stages = [
        {"name": "Initializing Skyfield...", "action": "skyfield"},
        {"name": "Loading Airport Data...", "action": "airports"},
        {"name": "Loading Runway Data...", "action": "runways"},
        {"name": "Loading Navaid Data...", "action": "navaids"},
    ]
    for layer_key, config in VECTOR_LAYER_CONFIGS.items():
        loading_stages.append({
            "name": f"Loading Map: {config.get('label', layer_key)}...",
            "action": "vector_layer", "layer_key": layer_key, "layer_config": config
        })

    num_stages = len(loading_stages)
    progress_bar_width = screen.get_width() * 0.8
    progress_bar_height = 30
    progress_bar_x = (screen.get_width() - progress_bar_width) / 2
    progress_bar_y = screen.get_height() / 2 + 20
    title_y = screen.get_height() / 2 - 50

    DARK_BLUE_LOADING = (15, 18, 26); WHITE_LOADING = (220, 220, 220)
    GREEN_LOADING = (0, 180, 0); GREY_LOADING = (80, 80, 80)

    print(f"Using fixed vector map simplification tolerance: {DEFAULT_SIMPLIFICATION_TOLERANCE_DEG}°")

    for i, stage in enumerate(loading_stages):
        if not running: return False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                print("Loading aborted by user."); running = False; return False

        screen.fill(DARK_BLUE_LOADING)
        title_surf = font.render("ADS-B Transit Predictor", True, WHITE_LOADING)
        title_rect = title_surf.get_rect(center=(screen.get_width() / 2, title_y))
        screen.blit(title_surf, title_rect)
        msg_surface = info_font.render(stage["name"], True, WHITE_LOADING)
        msg_rect = msg_surface.get_rect(center=(screen.get_width() / 2, progress_bar_y - 30))
        screen.blit(msg_surface, msg_rect)
        progress = (i + 1) / num_stages
        current_progress_width = progress_bar_width * progress
        pygame.draw.rect(screen, GREY_LOADING, (progress_bar_x, progress_bar_y, progress_bar_width, progress_bar_height))
        pygame.draw.rect(screen, GREEN_LOADING, (progress_bar_x, progress_bar_y, current_progress_width, progress_bar_height))
        percent_text = info_font.render(f"{int(progress * 100)}%", True, WHITE_LOADING)
        percent_rect = percent_text.get_rect(center=(progress_bar_x + progress_bar_width / 2, progress_bar_y + progress_bar_height / 2))
        screen.blit(percent_text, percent_rect)
        pygame.display.flip()

        action = stage["action"]
        print(f"Loading stage [{i+1}/{num_stages}]: {stage['name']}")
        try:
            if action == "skyfield":
                ephemeris_path = resource_path(os.path.join('data', 'de421.bsp'))
                eph = load(ephemeris_path); ts = load.timescale()
                observer_topos = Topos(latitude_degrees=USER_LAT, longitude_degrees=USER_LON, elevation_m=USER_ALT)
            elif action == "airports":
                airports_data = load_airports(filename=AIRPORTS_CSV, types_to_show=SHOW_AIRPORT_TYPES)
            elif action == "runways":
                initial_airport_idents = {apt['ident'] for apt in airports_data}
                runways_data = load_runways(filename=RUNWAYS_CSV, airport_idents_to_load=initial_airport_idents)
            elif action == "navaids":
                navaids_data = load_navaids(filename=NAVAIDS_CSV, types_to_show=SHOW_NAVAID_TYPES)
            elif action == "vector_layer":
                load_specific_vector_layer_data(stage["layer_key"], stage["layer_config"], DEFAULT_SIMPLIFICATION_TOLERANCE_DEG)
        except Exception as e_load:
            print(f"Error during loading stage '{stage['name']}': {e_load}"); traceback.print_exc()
    print("All loading stages complete.")
    return True


def visualization_loop(screen, current_screen_width, current_screen_height):
    global running, current_display_range_km, HOST, PORT, DUMP1090_DEVICE_INDEX, DUMP1090_GAIN, USER_LAT, USER_LON, USER_ALT, USER_ALT_FT, AIRCRAFT_TIMEOUT, PREDICTION_INTERVAL, PREDICTION_HORIZON, PREDICTION_STEP, CONFLICT_ANGLE_DEG, EVENT_TIMEOUT, CONFLICT_RADIUS_KM, AIRCRAFT_HISTORY_MINUTES, SHOW_AIRPORT_TYPES, SHOW_NAVAID_TYPES, SHOW_AIRCRAFT_HISTORY, SHOW_EVENT_LOCATIONS, SHOW_GLIDESLOPE, SHOW_RANGE_RINGS, RANGE_RING_SPACING_NM_STR, RANGE_RING_SPACING_KM, MAX_RANGE_RINGS, observer_topos, eph, ts, config_file_full_path, aircraft_dict, event_dict, history_event_count, DUMP1090_CONNECTED, start_time, lock, dialog_result_storage, dialog_thread, airports_data, runways_data, navaids_data, data_loading_thread, data_load_result, active_glideslopes, dialog_runway_end_result_storage, dialog_runway_end_thread, selected_aircraft_for_transit_icao, SHOW_ALL_TRANSIT_STRIPS, VELOCITY_VECTOR_SECONDS, VELOCITY_VECTOR_MINUTES, SHOW_VELOCITY_VECTOR, VECTOR_LAYERS_VISIBILITY, map_features_geodata, last_clicked_transit_coord, last_clicked_transit_time

    # screen_width and screen_height will track the current dimensions of the 'screen' surface.
    # Initialize with the dimensions passed from __main__
    screen_width, screen_height = current_screen_width, current_screen_height
    
    # Pump events once at the start. This allows Pygame to finalize window setup
    # and report the true size if the OS made adjustments.
    pygame.event.pump()
    live_screen_dims = screen.get_size() # Get current size from the passed-in screen surface

    if (screen_width, screen_height) != live_screen_dims:
        print(f"visualization_loop: diffent screen size detacted: old: ({screen_width},{screen_height}) new: ({live_screen_dims[0]},{live_screen_dims[1]})")
        screen_width, screen_height = live_screen_dims
    
    # Calculate initial panel layout based on the (potentially updated) screen_width and screen_height
    left_rect, right_rect, current_panel_height = calculate_panel_layout(screen_width, screen_height)
    
    print(f"visualization_loop: window size set: ({screen_width}x{screen_height})")
    print(f"visualization_loop: calculated_panel_layout: L: {left_rect}, R: {right_rect}, H: {current_panel_height}")

    # Pygame is already initialized, and the display mode (screen) is set by __main__.
    # Re-affirm caption and icon on the existing screen's window.
    pygame.display.set_caption("ADS-B Transit Predictor")
    if ICON_PATH:
        try:
            icon_surface = pygame.image.load(ICON_PATH)
            pygame.display.set_icon(icon_surface)
        except Exception as e:
            print(f"Warning: Failed to load or set Pygame icon in visualization_loop: {e}")

    clock = pygame.time.Clock()

    AIRPORT_COLOR=(170,170,255);RUNWAY_COLOR=(150,150,150);NAVAID_COLOR=(255,165,255);LABEL_COLOR=(255,255,255);EVENT_ACAC_COLOR=(255,255,100);EVENT_SUN_COLOR=(255,180,100);EVENT_MOON_COLOR=(100,255,255);BLACK=(0,0,0);GREY=(100,100,100);DARK_GREY=(50,50,50);GREEN=(0,255,0);YELLOW=(255,255,0);RED=(255,0,0);WHITE=(255,255,255);BLUE=(100,100,255); DARK_BLUE = (15, 18, 26); RANGE_RING_COLOR = (0, 80, 0); GLIDESLOPE_COLOR = (180, 180, 255)
    TRANSIT_STRIP_SUN_COLOR_FILL = pygame.Color(255, 165, 0, 70)
    TRANSIT_STRIP_MOON_COLOR_FILL = pygame.Color(173, 216, 230, 70)
    TRANSIT_STRIP_SUN_COLOR_CENTER = pygame.Color(255, 100, 0, 180)
    TRANSIT_STRIP_MOON_COLOR_CENTER = pygame.Color(80, 130, 180, 180)
    CLICKED_COORD_COLOR = pygame.Color(255, 255, 150)
    POINT_FEATURE_RADIUS = 2

    def fade_color(color, alpha=HISTORY_ALPHA): r,g,b = pygame.colordict.THECOLORS.get(color,(255,255,255)) if isinstance(color, str) else color; factor=alpha/255.0; inv_factor=1.0-factor; grey_val=100; return (int(r*factor+grey_val*inv_factor), int(g*factor+grey_val*inv_factor), int(b*factor+grey_val*inv_factor))
    HISTORY_COLOR_GREEN=fade_color(GREEN);HISTORY_COLOR_YELLOW=fade_color(YELLOW);HISTORY_COLOR_RED=fade_color(RED)
    
    # Load fonts
    try: font=pygame.font.SysFont("Consolas",14);info_f=pygame.font.SysFont("Consolas",16);small_font=pygame.font.SysFont("Consolas",11)
    except: font=pygame.font.SysFont(None,18);info_f=pygame.font.SysFont(None,22);small_font=pygame.font.SysFont(None,14)
    font_h=font.get_height();info_f_h=info_f.get_height()
    
    current_display_range_km = INITIAL_MAP_RANGE_KM 
    config_button_width=80;config_button_height=30;config_button_margin=10
    # Ensure config_button_rect is relative to the current right_rect
    config_button_rect=pygame.Rect(right_rect.right - config_button_width - config_button_margin, right_rect.top + config_button_margin, config_button_width, config_button_height)
    
    running_inner = True; clicked_runway_cache = None; plane_size = 3
    prev_frame_transit_polys_info = []
    current_frame_transit_polys_info_temp = []
    map_background_surface = None
    redraw_map_background = True
    last_drawn_range_km = -1.0
    last_drawn_user_lat = -1.0
    last_drawn_user_lon = -1.0
    last_drawn_left_rect_size = (0,0)
    
    while running_inner:
        if not running: running_inner = False; continue
        current_frame_transit_polys_info_temp.clear()

        if current_display_range_km != last_drawn_range_km or \
           USER_LAT != last_drawn_user_lat or \
           USER_LON != last_drawn_user_lon or \
           (left_rect.width, left_rect.height) != last_drawn_left_rect_size: # left_rect size change triggers redraw
            redraw_map_background = True

        if data_loading_thread and not data_loading_thread.is_alive():
            new_data=data_load_result[0]
            if new_data and isinstance(new_data,dict) and "error" not in new_data: airports_data=new_data.get('airports',[]);runways_data=new_data.get('runways',collections.defaultdict(list));navaids_data=new_data.get('navaids',[])
            elif new_data and isinstance(new_data,dict) and "error" in new_data: print(f"Error during data loading: {new_data['error']}")
            data_load_result[:]=[None];data_loading_thread=None; redraw_map_background = True
        if dialog_thread and not dialog_thread.is_alive():
            result_data = dialog_result_storage[0]
            if result_data and isinstance(result_data,dict) and "error" not in result_data:
                new_config=result_data; requires_restart=new_config.get("_requires_restart",False)
                original_airport_filters=SHOW_AIRPORT_TYPES[:]; original_navaid_filters=SHOW_NAVAID_TYPES[:]
                original_vector_visibility = VECTOR_LAYERS_VISIBILITY.copy()
                HOST=new_config['host']; PORT=new_config['port']; DUMP1090_DEVICE_INDEX=new_config['device_index']; DUMP1090_GAIN=new_config['gain']
                USER_LAT=new_config['lat']; USER_LON=new_config['lon']; USER_ALT=new_config['alt_m']; USER_ALT_FT=USER_ALT*3.28084
                AIRCRAFT_TIMEOUT=new_config['aircraft_timeout']; PREDICTION_INTERVAL=new_config['pred_interval']; PREDICTION_HORIZON=new_config['pred_horizon']; PREDICTION_STEP=new_config['pred_step']; CONFLICT_ANGLE_DEG=new_config['conflict_angle']; EVENT_TIMEOUT=new_config['event_timeout']; CONFLICT_RADIUS_KM=new_config['conflict_radius_km']; AIRCRAFT_HISTORY_MINUTES=new_config['history_minutes']; SHOW_AIRPORT_TYPES=new_config['show_airport_types']; SHOW_NAVAID_TYPES=new_config['show_navaid_types']; SHOW_AIRCRAFT_HISTORY=new_config['show_history']; SHOW_EVENT_LOCATIONS=new_config['show_events']
                SHOW_GLIDESLOPE = new_config['show_glideslope']; SHOW_RANGE_RINGS = new_config['show_range_rings']; RANGE_RING_SPACING_NM_STR = new_config['range_ring_spacing_nm_str']; MAX_RANGE_RINGS = new_config['max_range_rings']
                SHOW_ALL_TRANSIT_STRIPS = new_config['show_all_transit_strips']
                VELOCITY_VECTOR_MINUTES = new_config['velocity_vector_minutes']; VELOCITY_VECTOR_SECONDS = VELOCITY_VECTOR_MINUTES * 60.0
                SHOW_VELOCITY_VECTOR = new_config['show_velocity_vector']
                VECTOR_LAYERS_VISIBILITY = new_config['vector_layers_visibility'].copy()
                if VECTOR_LAYERS_VISIBILITY != original_vector_visibility:
                    redraw_map_background = True
                try: RANGE_RING_SPACING_KM = float(RANGE_RING_SPACING_NM_STR) * NM_TO_KM
                except ValueError: RANGE_RING_SPACING_NM_STR = DEFAULT_RANGE_RING_SPACING_NM_STR; RANGE_RING_SPACING_KM = float(RANGE_RING_SPACING_NM_STR) * NM_TO_KM
                if save_config(config_file_full_path,new_config): print("Configuration saved.")
                if eph and ts:
                    try: observer_topos=Topos(latitude_degrees=USER_LAT,longitude_degrees=USER_LON,elevation_m=USER_ALT);print("Skyfield user observer updated.")
                    except Exception as e: print(f"Error updating Skyfield user observer: {e}");observer_topos=None
                filters_changed=(set(SHOW_AIRPORT_TYPES)!=set(original_airport_filters) or set(SHOW_NAVAID_TYPES)!=set(original_navaid_filters))
                if filters_changed:
                    if not (data_loading_thread and data_loading_thread.is_alive()): data_load_result[:]=[None];current_apt_filters=SHOW_AIRPORT_TYPES[:];current_nav_filters=SHOW_NAVAID_TYPES[:];data_loading_thread=threading.Thread(target=reload_geographic_data_threaded_target,args=(current_apt_filters,current_nav_filters,data_load_result),daemon=True);data_loading_thread.start()
                if requires_restart: print("\n"+"*"*10+" RESTART REQUIRED "+"*"*10+"\nChanges to 'Device Index' or 'Gain' require an application restart.\n"+"*"*38+"\n")
            elif result_data and isinstance(result_data,dict) and "error" in result_data: print(f"Error occurred in config dialog thread: {result_data['error']}")
            dialog_result_storage[:]=[None];dialog_thread=None
        if dialog_runway_end_thread and not dialog_runway_end_thread.is_alive():
            selected_end_states = dialog_runway_end_result_storage[0]
            if selected_end_states and isinstance(selected_end_states, dict) and clicked_runway_cache:
                runway_data_for_gs = clicked_runway_cache['runway_data']; airport_ident_for_gs = clicked_runway_cache['airport_ident']; airport_type_for_gs = clicked_runway_cache['airport_type']
                for end_ident, should_be_active in selected_end_states.items():
                    glideslope_key = (airport_ident_for_gs, end_ident)
                    with lock:
                        is_currently_active = glideslope_key in active_glideslopes
                        if should_be_active and not is_currently_active:
                            gs_calc_details = calculate_glideslope_details(runway_data_for_gs, end_ident, airport_type_for_gs)
                            if gs_calc_details: active_glideslopes[glideslope_key] = gs_calc_details; print(f"Activated glideslope for {airport_ident_for_gs} runway end {end_ident}")
                        elif not should_be_active and is_currently_active and glideslope_key in active_glideslopes:
                            del active_glideslopes[glideslope_key]; print(f"Deactivated glideslope for {airport_ident_for_gs} runway end {end_ident}")
                redraw_map_background = True
            elif selected_end_states and isinstance(selected_end_states, dict) and "error" in selected_end_states: print(f"Error in runway glideslope toggle dialog: {selected_end_states['error']}")
            dialog_runway_end_result_storage[:] = [None]; dialog_runway_end_thread = None; clicked_runway_cache = None

        mouse_pos=pygame.mouse.get_pos()
        for event in pygame.event.get():
            if event.type==pygame.QUIT: running_inner=False; running=False
            elif event.type==pygame.KEYDOWN:
                 if event.key==pygame.K_ESCAPE: running_inner=False; running=False
                 elif event.key in (pygame.K_EQUALS,pygame.K_KP_PLUS): current_display_range_km=max(MIN_MAP_RANGE_KM,current_display_range_km/ZOOM_FACTOR); redraw_map_background = True
                 elif event.key in (pygame.K_MINUS,pygame.K_KP_MINUS): current_display_range_km=min(MAX_MAP_RANGE_KM,current_display_range_km*ZOOM_FACTOR); redraw_map_background = True
            elif event.type==pygame.MOUSEBUTTONDOWN and event.button==1:
                mouse_event_handled = False
                if config_button_rect.collidepoint(event.pos):
                    if not (dialog_thread and dialog_thread.is_alive()):
                        current_runtime_config={'host':HOST,'port':PORT,'device_index':DUMP1090_DEVICE_INDEX,'gain':DUMP1090_GAIN,'lat':USER_LAT,'lon':USER_LON,'alt_m':USER_ALT,'aircraft_timeout':AIRCRAFT_TIMEOUT,'pred_interval':PREDICTION_INTERVAL,'pred_horizon':PREDICTION_HORIZON,'pred_step':PREDICTION_STEP,'conflict_angle':CONFLICT_ANGLE_DEG,'event_timeout':EVENT_TIMEOUT,'conflict_radius_km':CONFLICT_RADIUS_KM,'history_minutes':AIRCRAFT_HISTORY_MINUTES,'show_airport_types':SHOW_AIRPORT_TYPES[:],'show_navaid_types':SHOW_NAVAID_TYPES[:],'show_history':SHOW_AIRCRAFT_HISTORY,'show_events':SHOW_EVENT_LOCATIONS, 'show_glideslope': SHOW_GLIDESLOPE, 'show_range_rings': SHOW_RANGE_RINGS, 'range_ring_spacing_nm_str': RANGE_RING_SPACING_NM_STR, 'max_range_rings': MAX_RANGE_RINGS, 'show_all_transit_strips': SHOW_ALL_TRANSIT_STRIPS, 'velocity_vector_minutes': VELOCITY_VECTOR_MINUTES, 'show_velocity_vector': SHOW_VELOCITY_VECTOR, 'vector_layers_visibility': VECTOR_LAYERS_VISIBILITY.copy()}
                        open_config_dialog_threaded(current_runtime_config)
                    mouse_event_handled = True
                elif left_rect.collidepoint(event.pos):
                    scale_for_click = prev_frame_transit_polys_info[0][3] if prev_frame_transit_polys_info else (left_rect.width/2.0)/current_display_range_km if current_display_range_km >0 else 1
                    left_rect_for_click = prev_frame_transit_polys_info[0][4] if prev_frame_transit_polys_info else left_rect
                    _lcx_c = left_rect_for_click.left + left_rect_for_click.width//2; _lcy_c = left_rect_for_click.top + left_rect_for_click.height//2 # Use height for y center
                    _lr_c = EARTH_RADIUS_KM; _lf_c = max(0.01, cos(radians(USER_LAT)))
                    clicked_ac_icao_candidate = None; min_dist_sq_ac = float('inf')
                    for ac_clk in get_active_aircraft():
                        lat_c,lon_c = ac_clk.get('lat'),ac_clk.get('lon')
                        if lat_c is None or lon_c is None: continue
                        dx_c=(lon_c-USER_LON)*radians(1)*effective_radius_at_lat(USER_LAT, 0)*_lf_c; dy_c=(lat_c-USER_LAT)*radians(1)*effective_radius_at_lat(USER_LAT, 0)
                        sx_c=_lcx_c+int(dx_c*scale_for_click); sy_c=_lcy_c-int(dy_c*scale_for_click)
                        dist_sq_l=(event.pos[0]-sx_c)**2+(event.pos[1]-sy_c)**2; clk_r_sq_l=(plane_size*2.5)**2
                        if dist_sq_l < clk_r_sq_l and dist_sq_l < min_dist_sq_ac: min_dist_sq_ac=dist_sq_l; clicked_ac_icao_candidate=ac_clk['icao']
                    if clicked_ac_icao_candidate:
                        if selected_aircraft_for_transit_icao == clicked_ac_icao_candidate: selected_aircraft_for_transit_icao = None; print(f"Deselected AC {clicked_ac_icao_candidate}.")
                        else: selected_aircraft_for_transit_icao = clicked_ac_icao_candidate; print(f"Selected AC {selected_aircraft_for_transit_icao}.")
                        mouse_event_handled = True
                    if not mouse_event_handled:
                        for body_type, screen_poly_verts, _, scale_at_draw, rect_at_draw in prev_frame_transit_polys_info:
                            if is_point_in_polygon(event.pos[0], event.pos[1], screen_poly_verts):
                                clicked_lat, clicked_lon = screen_to_geo(event.pos[0], event.pos[1], rect_at_draw, scale_at_draw, USER_LAT, USER_LON)
                                if clicked_lat is not None: last_clicked_transit_coord = (clicked_lat, clicked_lon); last_clicked_transit_time = time.time(); print(f"Clicked {body_type} transit at: {clicked_lat:.4f}, {clicked_lon:.4f}")
                                mouse_event_handled = True; break
                    if not mouse_event_handled and SHOW_GLIDESLOPE and not (dialog_runway_end_thread and dialog_runway_end_thread.is_alive()):
                        found_rwy_l=None;min_dist_rwy_l=float('inf')
                        _lr_click_proj = effective_radius_at_lat(USER_LAT, 0); _lf_click_proj = max(0.01, cos(radians(USER_LAT)))
                        for apt_l in airports_data:
                            apt_id_l=apt_l.get('ident'); apt_ty_l=apt_l.get('type')
                            if apt_id_l in runways_data:
                                for rwy_l in runways_data[apt_id_l]:
                                    try:
                                        le_dx_w=(rwy_l['le_lon']-USER_LON)*radians(1)*_lr_click_proj*_lf_click_proj; le_dy_w=(rwy_l['le_lat']-USER_LAT)*radians(1)*_lr_click_proj
                                        le_sx_r,le_sy_r=_lcx_c+int(le_dx_w*scale_for_click),_lcy_c-int(le_dy_w*scale_for_click)
                                        he_dx_w=(rwy_l['he_lon']-USER_LON)*radians(1)*_lr_click_proj*_lf_click_proj; he_dy_w=(rwy_l['he_lat']-USER_LAT)*radians(1)*_lr_click_proj
                                        he_sx_r,he_sy_r=_lcx_c+int(he_dx_w*scale_for_click),_lcy_c-int(he_dy_w*scale_for_click)
                                        if not(min(le_sx_r,he_sx_r)>left_rect_for_click.right or max(le_sx_r,he_sx_r)<left_rect_for_click.left or min(le_sy_r,he_sy_r)>left_rect_for_click.bottom or max(le_sy_r,he_sy_r)<left_rect_for_click.top):
                                            dist_rwy=point_line_segment_distance(event.pos[0],event.pos[1],le_sx_r,le_sy_r,he_sx_r,he_sy_r)
                                            if dist_rwy<RUNWAY_CLICK_SENSITIVITY_PX and dist_rwy<min_dist_rwy_l:min_dist_rwy_l=dist_rwy;found_rwy_l={'runway_data':rwy_l.copy(),'airport_ident':apt_id_l,'airport_type':apt_ty_l}
                                    except: pass
                        if found_rwy_l: clicked_runway_cache=found_rwy_l; open_runway_glideslope_toggle_dialog_threaded(found_rwy_l,dialog_runway_end_result_storage); mouse_event_handled=True
                    if not mouse_event_handled and selected_aircraft_for_transit_icao is not None:
                        selected_aircraft_for_transit_icao=None; print("Deselected aircraft by map click.")
            elif event.type==pygame.VIDEORESIZE:
                print(f"VIDEORESIZE event: New dimensions {event.w}x{event.h}")
                screen_width, screen_height = event.w, event.h 

                # Recalculate panel layout with new dimensions
                left_rect, right_rect, current_panel_height = calculate_panel_layout(screen_width, screen_height)
                # Reposition config button based on new right_rect
                config_button_rect.topleft = (right_rect.right - config_button_width - config_button_margin, right_rect.top + config_button_margin)
                redraw_map_background = True # Map background needs to be redrawn for new size

        screen.fill(BLACK) # Fill entire screen, then draw panels
        
        # Map Panel Drawing (Left Panel)
        # map_panel_side = left_rect.width # Assuming square map panel
        map_panel_draw_width = left_rect.width
        map_panel_draw_height = left_rect.height # Use actual height of left_rect

        # Scale needs to consider the smaller dimension if map is not square, or be based on a consistent metric
        # For a square display area, this is fine. If left_rect can be non-square, adjust.
        # current_panel_height is the side of the square portion of the map.
        scale = (current_panel_height / 2.0) / current_display_range_km if current_display_range_km > 0 else 1
        
        # Center of the map drawing area (left_rect)
        left_center_x_on_screen = left_rect.left + map_panel_draw_width // 2
        left_center_y_on_screen = left_rect.top + map_panel_draw_height // 2
        
        map_proj_local_radius = effective_radius_at_lat(USER_LAT, 0)
        map_proj_lon_factor = max(0.01, cos(radians(USER_LAT)))
        lat_range_deg_view=degrees(current_display_range_km/map_proj_local_radius) if map_proj_local_radius>0 else 0
        lon_range_deg_view=degrees(current_display_range_km/(map_proj_local_radius*map_proj_lon_factor)) if map_proj_local_radius>0 and map_proj_lon_factor>0 else 0
        view_margin=1.1;min_lat_view=USER_LAT-lat_range_deg_view*view_margin;max_lat_view=USER_LAT+lat_range_deg_view*view_margin;min_lon_view=USER_LON-lon_range_deg_view*view_margin;max_lon_view=USER_LON+lon_range_deg_view*view_margin

        if redraw_map_background or map_background_surface is None or map_background_surface.get_size() != (map_panel_draw_width, map_panel_draw_height):
            print("Redrawing map background surface...")
            map_background_surface = pygame.Surface((map_panel_draw_width, map_panel_draw_height), pygame.SRCALPHA)
            map_background_surface.fill(DARK_BLUE) # Fill with base color
            
            # Center of the map_background_surface itself
            surface_center_x = map_panel_draw_width // 2
            surface_center_y = map_panel_draw_height // 2

            for layer_key, is_visible in VECTOR_LAYERS_VISIBILITY.items():
                if is_visible and layer_key in map_features_geodata and layer_key in VECTOR_LAYER_CONFIGS:
                    layer_data = map_features_geodata[layer_key]
                    config = VECTOR_LAYER_CONFIGS[layer_key]
                    color = config.get("color", GREY)
                    if config["type"] == "line":
                        for line_segment_geo in layer_data:
                            if not line_segment_geo or len(line_segment_geo) < 2: continue
                            min_lon_s = min(p[0] for p in line_segment_geo); max_lon_s = max(p[0] for p in line_segment_geo)
                            min_lat_s = min(p[1] for p in line_segment_geo); max_lat_s = max(p[1] for p in line_segment_geo)
                            if max_lon_s < min_lon_view or min_lon_s > max_lon_view or max_lat_s < min_lat_view or min_lat_s > max_lat_view: continue # Typo: min_s_lat
                            screen_points_on_surface = []
                            for lon_g, lat_g in line_segment_geo:
                                p_dx = (lon_g - USER_LON) * radians(1) * map_proj_local_radius * map_proj_lon_factor
                                p_dy = (lat_g - USER_LAT) * radians(1) * map_proj_local_radius
                                sx_surf = surface_center_x + int(p_dx * scale); sy_surf = surface_center_y - int(p_dy * scale)
                                screen_points_on_surface.append((sx_surf, sy_surf))
                            if len(screen_points_on_surface) >= 2:
                                try: pygame.draw.aalines(map_background_surface, color, False, screen_points_on_surface, 1)
                                except Exception: pass
                    elif config["type"] == "polygon":
                        for polygon_parts_geo in layer_data: # This is a list of lists of points (rings)
                            for part_geo in polygon_parts_geo: # Each part_geo is a ring (list of points)
                                if not part_geo or len(part_geo) < 3: continue
                                screen_points_on_surface = []
                                for lon_g, lat_g in part_geo:
                                    p_dx = (lon_g - USER_LON) * radians(1) * map_proj_local_radius * map_proj_lon_factor
                                    p_dy = (lat_g - USER_LAT) * radians(1) * map_proj_local_radius
                                    sx_surf = surface_center_x + int(p_dx * scale); sy_surf = surface_center_y - int(p_dy * scale)
                                    screen_points_on_surface.append((sx_surf, sy_surf))
                                if len(screen_points_on_surface) >= 3:
                                    # For filled polygons, draw on a temp surface if alpha < 255
                                    # For outlines (current code), aalines is fine.
                                    # If fill is desired: pygame.draw.polygon(map_background_surface, color, screen_points_on_surface)
                                    try: pygame.draw.aalines(map_background_surface, color, True, screen_points_on_surface, 1) # True for closed
                                    except Exception: pass
                    elif config["type"] == "point":
                        for lon_g, lat_g in layer_data: # Assuming layer_data is list of (lon, lat) tuples
                            p_dx = (lon_g - USER_LON) * radians(1) * map_proj_local_radius * map_proj_lon_factor
                            p_dy = (lat_g - USER_LAT) * radians(1) * map_proj_local_radius
                            sx_surf = surface_center_x + int(p_dx * scale); sy_surf = surface_center_y - int(p_dy * scale)
                            # Check if point is within surface bounds before drawing
                            if 0 <= sx_surf < map_background_surface.get_width() and \
                               0 <= sy_surf < map_background_surface.get_height():
                                try: pygame.draw.circle(map_background_surface, color, (sx_surf, sy_surf), POINT_FEATURE_RADIUS)
                                except Exception: pass
            
            if SHOW_RANGE_RINGS and RANGE_RING_SPACING_KM > 0:
                num_rings = min(int(ceil(current_display_range_km*1.05/RANGE_RING_SPACING_KM)), MAX_RANGE_RINGS)
                for i in range(1, num_rings + 1):
                    ring_r_px = int(i * RANGE_RING_SPACING_KM * scale)
                    if 2 < ring_r_px < (min(map_panel_draw_width, map_panel_draw_height)//2)*1.5 : # Check against surface dimensions
                        pygame.draw.circle(map_background_surface,RANGE_RING_COLOR,(surface_center_x,surface_center_y),ring_r_px,1)
            
            bg_r1_px=int(CONFLICT_RADIUS_KM*scale); bg_r2_px=int(CONFLICT_RADIUS_KM*2*scale)
            if bg_r1_px>3: pygame.draw.circle(map_background_surface,GREY,(surface_center_x,surface_center_y),bg_r1_px,1); map_background_surface.blit(font.render(f"{CONFLICT_RADIUS_KM}km",True,GREY),(surface_center_x+bg_r1_px+2,surface_center_y-font_h//2))
            if bg_r2_px>3 and abs(bg_r2_px-bg_r1_px)>5: pygame.draw.circle(map_background_surface,GREY,(surface_center_x,surface_center_y),bg_r2_px,1); map_background_surface.blit(font.render(f"{CONFLICT_RADIUS_KM*2}km",True,GREY),(surface_center_x+bg_r2_px+2,surface_center_y-font_h//2))
            cs_s=5; pygame.draw.line(map_background_surface,WHITE,(surface_center_x-cs_s,surface_center_y),(surface_center_x+cs_s,surface_center_y),1); pygame.draw.line(map_background_surface,WHITE,(surface_center_x,surface_center_y-cs_s),(surface_center_x,surface_center_y+cs_s),1)
            redraw_map_background = False; last_drawn_range_km = current_display_range_km; last_drawn_user_lat = USER_LAT; last_drawn_user_lon = USER_LON; last_drawn_left_rect_size = (map_panel_draw_width, map_panel_draw_height)

        if map_background_surface: screen.blit(map_background_surface, left_rect.topleft)
        
        # Clip drawing to the left panel (map area)
        screen.set_clip(left_rect)

        show_navaid_labels=current_display_range_km<NAVAID_LABEL_MIN_ZOOM_KM; nsym_sz=2
        for nvd in navaids_data:
             n_lat,n_lon=nvd['lat'],nvd['lon']
             if min_lat_view<=n_lat<=max_lat_view and min_lon_view<=n_lon<=max_lon_view:
                 n_dx=(n_lon-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor; n_dy=(n_lat-USER_LAT)*radians(1)*map_proj_local_radius
                 nsx=left_center_x_on_screen+int(n_dx*scale); nsy=left_center_y_on_screen-int(n_dy*scale)
                 if not left_rect.collidepoint(nsx,nsy): continue # Check against actual left_rect
                 if 'VOR' in nvd['type']: pygame.draw.polygon(screen,NAVAID_COLOR,[(nsx,nsy-nsym_sz-1),(nsx-nsym_sz,nsy+nsym_sz),(nsx+nsym_sz,nsy+nsym_sz)],1)
                 elif 'NDB' in nvd['type']: pygame.draw.circle(screen,NAVAID_COLOR,(nsx,nsy),nsym_sz+1,1)
                 else: pygame.draw.rect(screen,NAVAID_COLOR,pygame.Rect(nsx-nsym_sz,nsy-nsym_sz,nsym_sz*2,nsym_sz*2),1)
                 if show_navaid_labels:nl_s=small_font.render(nvd.get('ident','?'),True,LABEL_COLOR);screen.blit(nl_s,nl_s.get_rect(center=(nsx,nsy-nsym_sz-small_font.get_height()//2-2)))
        show_ap_lbls=current_display_range_km<AIRPORT_LABEL_MIN_ZOOM_KM;show_rwys=current_display_range_km<RUNWAY_MIN_ZOOM_KM;show_rwy_lbls=current_display_range_km<RUNWAY_LABEL_MIN_ZOOM_KM;ap_sym_sz=3
        for ap in airports_data:
            a_lat,a_lon=ap['lat'],ap['lon']
            if min_lat_view<=a_lat<=max_lat_view and min_lon_view<=a_lon<=max_lon_view:
                a_dx=(a_lon-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor;a_dy=(a_lat-USER_LAT)*radians(1)*map_proj_local_radius
                asx=left_center_x_on_screen+int(a_dx*scale);asy=left_center_y_on_screen-int(a_dy*scale)
                if not left_rect.collidepoint(asx,asy): continue
                pygame.draw.rect(screen,AIRPORT_COLOR,pygame.Rect(asx-ap_sym_sz,asy-ap_sym_sz,ap_sym_sz*2,ap_sym_sz*2))
                if show_ap_lbls:al_s=small_font.render(ap.get('ident','UNK'),True,LABEL_COLOR);screen.blit(al_s,al_s.get_rect(center=(asx,asy+ap_sym_sz+small_font.get_height()//2+2)))
                if show_rwys and ap.get('ident') in runways_data:
                    for rwy in runways_data[ap.get('ident')]:
                        try:
                            le_x,le_y=left_center_x_on_screen+int(((rwy['le_lon']-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor)*scale),left_center_y_on_screen-int(((rwy['le_lat']-USER_LAT)*radians(1)*map_proj_local_radius)*scale)
                            he_x,he_y=left_center_x_on_screen+int(((rwy['he_lon']-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor)*scale),left_center_y_on_screen-int(((rwy['he_lat']-USER_LAT)*radians(1)*map_proj_local_radius)*scale)
                            rwy_vx=he_x-le_x;rwy_vy=he_y-le_y;sl_sq=rwy_vx**2+rwy_vy**2
                            if sl_sq>0.5:
                                sl=sqrt(sl_sq);w_px=max(2.0,feet_to_km(rwy.get('width_ft',75))*scale)
                                if w_px>=2.0:pvx=-rwy_vy/sl;pvy=rwy_vx/sl;hwp=w_px/2.0;c1=(le_x+pvx*hwp,le_y+pvy*hwp);c2=(he_x+pvx*hwp,he_y+pvy*hwp);c3=(he_x-pvx*hwp,he_y-pvy*hwp);c4=(le_x-pvx*hwp,le_y-pvy*hwp);pygame.draw.polygon(screen,RUNWAY_COLOR,[c1,c2,c3,c4])
                                else: pygame.draw.aaline(screen,RUNWAY_COLOR,(le_x,le_y),(he_x,he_y))
                                if show_rwy_lbls and sl>20:
                                    uvx=rwy_vx/sl;uvy=rwy_vy/sl;
                                    if rwy.get('le_ident'):les=small_font.render(rwy.get('le_ident'),True,LABEL_COLOR);screen.blit(les,les.get_rect(center=(int(le_x-uvx*8),int(le_y-uvy*8))))
                                    if rwy.get('he_ident'):hes=small_font.render(rwy.get('he_ident'),True,LABEL_COLOR);screen.blit(hes,hes.get_rect(center=(int(he_x+uvx*8),int(he_y+uvy*8))))
                        except:pass
        if SHOW_GLIDESLOPE:
            with lock: gs_keys_draw = list(active_glideslopes.keys())
            for gs_key in gs_keys_draw:
                with lock: gs_data = active_glideslopes.get(gs_key)
                if not gs_data: continue
                try:
                    gs_ssx=left_center_x_on_screen+int(((gs_data['start_lon']-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor)*scale)
                    gs_ssy=left_center_y_on_screen-int(((gs_data['start_lat']-USER_LAT)*radians(1)*map_proj_local_radius)*scale)
                    ab_rad=radians(gs_data['bearing_deg']);gs_len_px=gs_data['length_km']*scale
                    gs_esx=gs_ssx+gs_len_px*sin(ab_rad);gs_esy=gs_ssy+gs_len_px*(-cos(ab_rad)) # Note: y-axis is inverted in Pygame
                    if not (min(gs_ssx,gs_esx)>left_rect.right or max(gs_ssx,gs_esx)<left_rect.left or min(gs_ssy,gs_esy)>left_rect.bottom or max(gs_ssy,gs_esy)<left_rect.top):
                        pygame.draw.aaline(screen,GLIDESLOPE_COLOR,(int(gs_ssx),int(gs_ssy)),(int(gs_esx),int(gs_esy)))
                        lvx_gs=gs_esx-gs_ssx;lvy_gs=gs_esy-gs_ssy;llp_gs=hypot(lvx_gs,lvy_gs)
                        if llp_gs>1:
                            gs_nvx=lvx_gs/llp_gs;gs_nvy=lvy_gs/llp_gs;pvx_gs,pvy_gs=-gs_nvy,gs_nvx # Perpendicular vector
                            num_ticks=int(gs_data['length_km']/GLIDESLOPE_TICK_INTERVAL_KM)
                            for i_tk in range(1,num_ticks+1):
                                dpt=i_tk*GLIDESLOPE_TICK_INTERVAL_KM*scale
                                if dpt>llp_gs+1:continue # Tick is beyond line end
                                tbx=gs_ssx+gs_nvx*dpt;tby=gs_ssy+gs_nvy*dpt
                                if not left_rect.collidepoint(int(tbx),int(tby)):continue
                                pygame.draw.aaline(screen,GLIDESLOPE_COLOR,(int(tbx+pvx_gs*GLIDESLOPE_TICK_HALF_LENGTH_PX),int(tby+pvy_gs*GLIDESLOPE_TICK_HALF_LENGTH_PX)),(int(tbx-pvx_gs*GLIDESLOPE_TICK_HALF_LENGTH_PX),int(tby-pvy_gs*GLIDESLOPE_TICK_HALF_LENGTH_PX)))
                except:pass

        active_acs_list = get_active_aircraft(); transit_rects_to_draw = []
        if eph:
            aircraft_to_calc_transit = [ac['icao'] for ac in active_acs_list] if SHOW_ALL_TRANSIT_STRIPS else ([selected_aircraft_for_transit_icao] if selected_aircraft_for_transit_icao and any(ac['icao'] == selected_aircraft_for_transit_icao for ac in active_acs_list) else [])
            if not aircraft_to_calc_transit and selected_aircraft_for_transit_icao and not SHOW_ALL_TRANSIT_STRIPS : selected_aircraft_for_transit_icao = None
            now_time = datetime.now(timezone.utc)
            for icao_code in aircraft_to_calc_transit:
                calculated_rect_data = calculate_transit_rectangle_for_aircraft(icao_code, now_time)
                if calculated_rect_data.get('sun'): transit_rects_to_draw.append((icao_code, 'sun', calculated_rect_data['sun']))
                if calculated_rect_data.get('moon'): transit_rects_to_draw.append((icao_code, 'moon', calculated_rect_data['moon']))
        for icao_code, body_type, rect_data in transit_rects_to_draw:
            L0_geo, R0_geo, R_end_geo, L_end_geo, C0_geo, C_end_geo = rect_data
            strip_fill_color = TRANSIT_STRIP_SUN_COLOR_FILL if body_type == 'sun' else TRANSIT_STRIP_MOON_COLOR_FILL
            centerline_color = TRANSIT_STRIP_SUN_COLOR_CENTER if body_type == 'sun' else TRANSIT_STRIP_MOON_COLOR_CENTER
            poly_geo_verts = [L0_geo, R0_geo, R_end_geo, L_end_geo]; screen_poly_verts = []; valid_poly = True
            for lat_g, lon_g in poly_geo_verts:
                if lat_g is None or lon_g is None: valid_poly = False; break
                p_dx = (lon_g - USER_LON) * radians(1) * map_proj_local_radius * map_proj_lon_factor; p_dy = (lat_g - USER_LAT) * radians(1) * map_proj_local_radius
                screen_poly_verts.append((left_center_x_on_screen + int(p_dx * scale), left_center_y_on_screen - int(p_dy * scale)))
            if valid_poly and len(screen_poly_verts) == 4:
                try:
                    min_x,max_x,min_y,max_y=min(p[0]for p in screen_poly_verts),max(p[0]for p in screen_poly_verts),min(p[1]for p in screen_poly_verts),max(p[1]for p in screen_poly_verts)
                    if max_x>left_rect.left and min_x<left_rect.right and max_y>left_rect.top and min_y<left_rect.bottom:
                        poly_surf_w,poly_surf_h=max_x-min_x,max_y-min_y
                        if poly_surf_w>0 and poly_surf_h>0:
                            temp_surf=pygame.Surface((poly_surf_w,poly_surf_h),pygame.SRCALPHA);local_pts=[(p[0]-min_x,p[1]-min_y)for p in screen_poly_verts]
                            pygame.draw.polygon(temp_surf,strip_fill_color,local_pts);screen.blit(temp_surf,(min_x,min_y))
                            current_frame_transit_polys_info_temp.append((body_type,screen_poly_verts,poly_geo_verts,scale,left_rect.copy()))
                except Exception: pass
            if C0_geo and C_end_geo:
                C0_dx,C0_dy=(C0_geo[1]-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor,(C0_geo[0]-USER_LAT)*radians(1)*map_proj_local_radius;C0_sx,C0_sy=left_center_x_on_screen+int(C0_dx*scale),left_center_y_on_screen-int(C0_dy*scale)
                C_end_dx,C_end_dy=(C_end_geo[1]-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor,(C_end_geo[0]-USER_LAT)*radians(1)*map_proj_local_radius;C_end_sx,C_end_sy=left_center_x_on_screen+int(C_end_dx*scale),left_center_y_on_screen-int(C_end_dy*scale)
                if not(min(C0_sx,C_end_sx)>left_rect.right or max(C0_sx,C_end_sx)<left_rect.left or min(C0_sy,C_end_sy)>left_rect.bottom or max(C0_sy,C_end_sy)<left_rect.top):
                   try:pygame.draw.aaline(screen,centerline_color,(C0_sx,C0_sy),(C_end_sx,C_end_sy),1)
                   except Exception:pass
        
        displayed_ac_count = 0; hist_cutoff = datetime.now(timezone.utc)-timedelta(minutes=AIRCRAFT_HISTORY_MINUTES)
        conflict_snap={}; involved_snap={}
        with lock:
             for icao,ac_d in aircraft_dict.items():conflict_snap[icao]=ac_d.get('conflict');involved_snap[icao]=bool(ac_d.get('event_ids'))
        for ac_s in active_acs_list:
            icao=ac_s['icao'];lat,lon=ac_s.get('lat'),ac_s.get('lon')
            if lat is None or lon is None: continue
            dx=(lon-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor;dy=(lat-USER_LAT)*radians(1)*map_proj_local_radius
            sx=left_center_x_on_screen+int(dx*scale);sy=left_center_y_on_screen-int(dy*scale)
            has_cfl=conflict_snap.get(icao)is not None;is_inv=involved_snap.get(icao,False);is_sel_ts=(selected_aircraft_for_transit_icao==icao)
            p_clr=RED if has_cfl else (YELLOW if is_inv else GREEN);
            if is_sel_ts: p_clr=BLUE
            if SHOW_AIRCRAFT_HISTORY:
                h_clr=HISTORY_COLOR_RED if has_cfl else(HISTORY_COLOR_YELLOW if is_inv else HISTORY_COLOR_GREEN)
                if is_sel_ts: h_clr=fade_color(BLUE,HISTORY_ALPHA)
                last_hx,last_hy=-1,-1;hist_pts_draw=[]
                with lock:
                    cadfd=aircraft_dict.get(icao)
                    if cadfd and 'history' in cadfd: hist_pts_draw=list(cadfd['history'])
                for ht,hlat,hlon,halt in hist_pts_draw:
                    if ht>=hist_cutoff:
                        hdx=(hlon-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor;hdy=(hlat-USER_LAT)*radians(1)*map_proj_local_radius
                        hx=left_center_x_on_screen+int(hdx*scale);hy=left_center_y_on_screen-int(hdy*scale)
                        if(hx,hy)!=(last_hx,last_hy)and left_rect.collidepoint(hx,hy):pygame.draw.rect(screen,h_clr,pygame.Rect(hx-1,hy-1,2,2));last_hx,last_hy=hx,hy
            if not left_rect.collidepoint(sx,sy): continue
            displayed_ac_count+=1
            if SHOW_VELOCITY_VECTOR:
                max_vector_time = min(VELOCITY_VECTOR_SECONDS, PREDICTION_HORIZON);traj_pts=[(sx,sy)];traj_step_s=5
                traj_clr=RED if has_cfl else(YELLOW if is_inv else BLUE) # Using BLUE for general, not green
                if is_sel_ts: traj_clr=BLUE # Override to BLUE if selected
                if max_vector_time > 0:
                    for dt_p in np.arange(traj_step_s, max_vector_time + traj_step_s, traj_step_s):
                        pred=predict_position(lat,lon,ac_s.get('altitude'),ac_s.get('speed'),ac_s.get('track'),dt_p,ac_s.get('vs'))
                        if pred[0]is None:break
                        pdx=(pred[1]-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor;pdy=(pred[0]-USER_LAT)*radians(1)*map_proj_local_radius
                        px=left_center_x_on_screen+int(pdx*scale);py=left_center_y_on_screen-int(pdy*scale)
                        if(px,py)!=traj_pts[-1]and left_rect.collidepoint(px,py):traj_pts.append((px,py))
                        elif not left_rect.collidepoint(px,py):break # Stop if path leaves map
                    if len(traj_pts)>1:pygame.draw.lines(screen,traj_clr,False,traj_pts,1)
            p_rect=pygame.Rect(sx-plane_size,sy-plane_size,plane_size*2,plane_size*2);pygame.draw.rect(screen,p_clr,p_rect)
            if is_sel_ts: pygame.draw.rect(screen,WHITE,p_rect,1) # Border for selected
            csign=ac_s.get('callsign')or icao;altf=ac_s.get('altitude');spdk=ac_s.get('speed');trkd=ac_s.get('track');sqwk=ac_s.get('squawk')
            it1=f"{csign[:7]}";fls=f"FL{altf/100:03.0f}"if altf is not None else"FL---";sps=f"{spdk:03.0f}KT"if spdk is not None else"---KT";trs=f"{trkd:03.0f}"if trkd is not None else"---";it2=f"{fls} {sps} {trs}";sqs=str(sqwk).zfill(4)if sqwk is not None else"----";it3=f"{sqs}"
            ts1=font.render(it1,True,p_clr);ts2=font.render(it2,True,p_clr);ts3=font.render(it3,True,p_clr)
            tth=font_h*3+2;sty=sy-tth//2+font_h;tx=sx+plane_size+5
            tr1=ts1.get_rect(topleft=(tx,sty));tr2=ts2.get_rect(topleft=(tx,tr1.bottom+1));tr3=ts3.get_rect(topleft=(tx,tr2.bottom+1))
            if max(tr1.right,tr2.right,tr3.right)>left_rect.right:tx=sx-plane_size-5;tr1=ts1.get_rect(topright=(tx,sty));tr2=ts2.get_rect(topright=(tx,tr1.bottom+1));tr3=ts3.get_rect(topright=(tx,tr2.bottom+1))
            screen.blit(ts1,tr1);screen.blit(ts2,tr2);screen.blit(ts3,tr3)
            cfl_txt=conflict_snap.get(icao)
            if cfl_txt:
                map_dt=cfl_txt[:27]+"..."if len(cfl_txt)>30 else cfl_txt
                try: cfl_s=font.render(map_dt,True,RED); cfl_p=(tr3.left,tr3.bottom+1)if tr3.x>sx else(tr3.right-cfl_s.get_width(),tr3.bottom+1);screen.blit(cfl_s,cfl_p)
                except:pass
        if SHOW_EVENT_LOCATIONS:
            ev_m_sz=4
            with lock:evs_draw=[ev for ev in list(event_dict.values())if'lat'in ev and'lon'in ev and ev['lat']is not None]
            for ev in evs_draw:
                ev_lat,ev_lon=ev['lat'],ev['lon']
                if min_lat_view<=ev_lat<=max_lat_view and min_lon_view<=ev_lon<=max_lon_view:
                    ev_dx=(ev_lon-USER_LON)*radians(1)*map_proj_local_radius*map_proj_lon_factor;ev_dy=(ev_lat-USER_LAT)*radians(1)*map_proj_local_radius
                    ev_x=left_center_x_on_screen+int(ev_dx*scale);ev_y=left_center_y_on_screen-int(ev_dy*scale)
                    if left_rect.collidepoint(ev_x,ev_y):
                        ev_c=EVENT_ACAC_COLOR if ev['type']=='AC-AC'else(EVENT_SUN_COLOR if ev['type']=='AC-Sun'else(EVENT_MOON_COLOR if ev['type']=='AC-Moon'else YELLOW))
                        pygame.draw.line(screen,ev_c,(ev_x-ev_m_sz,ev_y-ev_m_sz),(ev_x+ev_m_sz,ev_y+ev_m_sz),1);pygame.draw.line(screen,ev_c,(ev_x-ev_m_sz,ev_y+ev_m_sz),(ev_x+ev_m_sz,ev_y-ev_m_sz),1)
        
        # Right Panel Drawing
        screen.set_clip(right_rect); pygame.draw.rect(screen,BLACK,right_rect); pygame.draw.rect(screen,GREY,right_rect,1) # Border
        btn_c=GREY if config_button_rect.collidepoint(mouse_pos)else DARK_GREY; pygame.draw.rect(screen,btn_c,config_button_rect); pygame.draw.rect(screen,WHITE,config_button_rect,1)
        cfg_txt_s=info_f.render("Config",True,WHITE);screen.blit(cfg_txt_s,cfg_txt_s.get_rect(center=config_button_rect.center))
        y0=right_rect.top+config_button_rect.height+config_button_margin*2;x0=right_rect.left+10
        with lock:conn_s_txt="Connected"if DUMP1090_CONNECTED else"Disconnected";ac_cnt_dict=len(aircraft_dict);hist_c=history_event_count;ev_lst_cpy=sorted(list(event_dict.values()),key=lambda ev:ev.get('time',datetime.min.replace(tzinfo=timezone.utc)))
        el_s=(datetime.now(timezone.utc)-start_time).total_seconds();el_str=str(timedelta(seconds=int(el_s)))
        sts_lns=[f"Runtime: {el_str}",f"Dump1090: {conn_s_txt} ({HOST}:{PORT})",f"User Pos: {USER_LAT:.4f}, {USER_LON:.4f}, {USER_ALT_FT:.0f}ft",f"Tracked AC: {ac_cnt_dict} (Disp: {displayed_ac_count})",f"Map Range: {current_display_range_km:.1f} km (+/-)", f"Conflict Angle: {CONFLICT_ANGLE_DEG:.1f}°",f"History Events: {hist_c}"] # Updated Map Tol
        if SHOW_RANGE_RINGS:sts_lns.append(f"Range Rings: {RANGE_RING_SPACING_NM_STR}NM")
        if SHOW_VELOCITY_VECTOR: sts_lns.append(f"Velocity Vector: {VELOCITY_VECTOR_MINUTES} min")
        ac_disp_n = "All" if SHOW_ALL_TRANSIT_STRIPS else (selected_aircraft_for_transit_icao or "Selected")
        if SHOW_ALL_TRANSIT_STRIPS: sts_lns.append("Transit View: All")
        elif selected_aircraft_for_transit_icao:
            ac_disp_n=selected_aircraft_for_transit_icao;
            with lock: sel_ac_d=aircraft_dict.get(selected_aircraft_for_transit_icao)
            if sel_ac_d and sel_ac_d.get('callsign'): ac_disp_n=sel_ac_d['callsign']
            sts_lns.append(f"Transit View: {ac_disp_n}")
        clicked_coord_line=None; current_time_sec=time.time()
        if last_clicked_transit_coord and current_time_sec-last_clicked_transit_time<5.0: clicked_coord_line=f"Clicked Transit: {last_clicked_transit_coord[0]:.4f}, {last_clicked_transit_coord[1]:.4f}"
        elif last_clicked_transit_coord: last_clicked_transit_coord=None
        if clicked_coord_line:sts_lns.append(clicked_coord_line)
        for idx, line in enumerate(sts_lns):
            if y0 < right_rect.bottom - info_f_h: line_color = CLICKED_COORD_COLOR if clicked_coord_line and line == clicked_coord_line else WHITE; screen.blit(info_f.render(line,True,line_color),(x0,y0)); y0+=info_f_h+2
            else: break
        y0+=info_f_h
        if y0<right_rect.bottom-info_f_h:screen.blit(info_f.render("Predicted Events:",True,WHITE),(x0,y0));y0+=info_f_h+2
        else:ev_lst_cpy=[]
        if not ev_lst_cpy:
            if y0<right_rect.bottom-info_f_h:screen.blit(info_f.render(" (None)",True,GREY),(x0+10,y0))
        else:
            for ev in ev_lst_cpy:
                 if y0>right_rect.bottom-info_f_h:
                     if y0<right_rect.bottom:screen.blit(info_f.render("[... more ...]",True,GREY),(x0,y0))
                     break
                 try:
                     calls=' / '.join(ev.get('callsigns',['???']));ev_pred_t=ev.get('time',datetime.min.replace(tzinfo=timezone.utc));time_s=ev_pred_t.strftime('%H:%M:%S');ang_s=f"{ev.get('angle',0.0):.1f}°";ev_ty=ev.get('type','UNK');eta_s=(ev_pred_t-datetime.now(timezone.utc)).total_seconds();disp_eta_s=max(0,round(eta_s));eta_str=f"ETA: {disp_eta_s}s";txt=f"{time_s} {ev_ty}: {calls} ({ang_s}) {eta_str}"
                 except:txt="Error formatting event"
                 try:cw_aprx=info_f.size("X")[0]*0.7 if info_f.size("X")[0]>0 else 10;max_l=int((right_rect.width-30)//cw_aprx) if cw_aprx>0 else 30
                 except:max_l=30
                 if len(txt)>max_l:txt=txt[:max(0,max_l-3)]+"..."if max_l>3 else txt[:max(0,max_l)]
                 try:screen.blit(info_f.render(txt,True,YELLOW),(x0+10,y0));y0+=info_f_h+2
                 except:pass

        screen.set_clip(None); # Reset clip for next frame
        prev_frame_transit_polys_info = current_frame_transit_polys_info_temp.copy()
        pygame.display.flip();
        clock.tick(20)

    pygame.quit();print("Visualization loop ended.")


# --- Main Execution ---
if __name__ == "__main__":
    running = True
    pygame.init() 

    # --- load font ---
    try: loading_font_main = pygame.font.SysFont("Consolas", 28, bold=True)
    except: loading_font_main = pygame.font.SysFont(None, 38, bold=True)
    try: loading_info_font_main = pygame.font.SysFont("Consolas", 18)
    except: loading_info_font_main = pygame.font.SysFont(None, 24)

    # --- get desktop size ---
    display_info = pygame.display.Info()
    desktop_width = display_info.current_w
    desktop_height = display_info.current_h
    print(f"Desktop size: {desktop_width}x{desktop_height}")

    # --- load screen settings ---
    loading_screen_width, loading_screen_height = 800, 250
    try:
        win_x_loading = (desktop_width - loading_screen_width) // 2
        win_y_loading = (desktop_height - loading_screen_height) // 2
        os.environ['SDL_VIDEO_WINDOW_POS'] = f"{max(0,win_x_loading)},{max(0,win_y_loading)}"
    except Exception: pass # os.environ might fail in some restricted environments
    
    loading_screen_surface = pygame.display.set_mode((loading_screen_width, loading_screen_height))
    pygame.display.set_caption("ADS-B Transit Predictor - Loading...")
    if ICON_PATH:
        try: pygame.display.set_icon(pygame.image.load(ICON_PATH))
        except Exception as e: print(f"Warning: Failed when loading icon: {e}")

    # --- show loading process ---
    loading_successful = show_loading_screen_and_load_data(loading_screen_surface, loading_font_main, loading_info_font_main)

    # --- main interface settings ---
    main_screen_surface = None 
    actual_screen_width_main = 0
    actual_screen_height_main = 0

    if running and loading_successful:
        print("Loading app's interface...")

        pygame.quit() # Quit Pygame used for loading screen
        pygame.init() # Re-initialize Pygame for the main application window

        initial_window_width = 1700 
        initial_window_height = 1080
            
        try:
            win_x_main = (desktop_width - initial_window_width) // 2
            win_y_main = (desktop_height - initial_window_height) // 2
            os.environ['SDL_VIDEO_WINDOW_POS'] = f"{max(0, win_x_main)},{max(0, win_y_main)}"
        except Exception:
            os.environ['SDL_VIDEO_WINDOW_POS'] = "100,100" # Fallback position

        print(f"Creating main interface: {initial_window_width}x{initial_window_height} at ({os.environ.get('SDL_VIDEO_WINDOW_POS','N/A')})")

        try:
            main_screen_surface = pygame.display.set_mode(
                (initial_window_width, initial_window_height),
                pygame.RESIZABLE | pygame.DOUBLEBUF | pygame.HWSURFACE 
            )
        except pygame.error as e_main_window:
            print(f"Setting main interface ({initial_window_width}x{initial_window_height}) err: {e_main_window}。")
            print("Using 1200x700 instead。")
            initial_window_width_fallback = 1200
            initial_window_height_fallback = 700
            try:
                win_x_fallback = (desktop_width - initial_window_width_fallback) // 2
                win_y_fallback = (desktop_height - initial_window_height_fallback) // 2
                os.environ['SDL_VIDEO_WINDOW_POS'] = f"{max(0, win_x_fallback)},{max(0, win_y_fallback)}"
            except Exception: pass
            main_screen_surface = pygame.display.set_mode(
                (initial_window_width_fallback, initial_window_height_fallback),
                pygame.RESIZABLE | pygame.DOUBLEBUF | pygame.HWSURFACE
            )
        
        pygame.display.set_caption("ADS-B Transit Predictor")
        if ICON_PATH:
            try: pygame.display.set_icon(pygame.image.load(ICON_PATH))
            except Exception as e: print(f"warning: failed to load icon: {e}")

        actual_screen_width_main, actual_screen_height_main = main_screen_surface.get_size()
        print(f"Main interface created, size: ({main_screen_surface.get_width()}x{main_screen_surface.get_height()}), actual size for viz_loop: ({actual_screen_width_main}x{actual_screen_height_main})")
        
        # --- create threads ---
        print("Creating threads...")
        listener_thread = threading.Thread(target=start_listener, daemon=True, name="ListenerThread"); listener_thread.start()
        conflict_thread = threading.Thread(target=predict_conflicts, daemon=True, name="ConflictThread"); conflict_thread.start()
        if eph: celestial_thread = threading.Thread(target=predict_celestial_conflicts, daemon=True, name="CelestialConflictThread"); celestial_thread.start()
        event_cleaner_thread = threading.Thread(target=clean_expired_events, daemon=True, name="EventCleanerThread"); event_cleaner_thread.start()
        
        print("Initializing visual_loop...")
        try:
            visualization_loop(main_screen_surface, actual_screen_width_main, actual_screen_height_main)
        except KeyboardInterrupt: print("\nKeyboard interrupt, exiting visual_loop..."); running = False
        except Exception as main_loop_e: print(f"\nFatal error: {main_loop_e}"); traceback.print_exc(); running = False
    
    elif not running:
        print("Warning: User interrupt")
    else: # loading_successful is False
        print("Warning: Failed to load")
        running = False # Ensure running is false if loading failed

    # --- 清理 ---
    if dump1090_process and dump1090_process.poll() is None:
        print("Terminating dump1090..."); 
        try: dump1090_process.terminate(); dump1090_process.wait(timeout=3)
        except subprocess.TimeoutExpired: dump1090_process.kill(); dump1090_process.wait(timeout=2)
        except Exception as e_term: print(f"Failed to terminate dump1090: {e_term}")
    
    print("Wait for 0.5s...")
    running = False 
    time.sleep(0.5) 
    pygame.quit() 
    print("exiting...")
    sys.exit(0)
