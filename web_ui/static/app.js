const canvas = document.getElementById("mapCanvas");
const ctx = canvas.getContext("2d");
const MIN_3D_VIEW_ZOOM = 0.6;
const MAX_3D_VIEW_ZOOM = 6;
const MIN_3D_RANGE_KM = 2;
const MAX_3D_RANGE_KM = 500;
const MIN_3D_PITCH_DEG = 0;
const MAX_3D_PITCH_DEG = 82;
const FULL_3D_PITCH_DEG = 12;
function getClientId() {
  const key = "adsbTransitClientId";
  let id = "";
  try {
    id = localStorage.getItem(key) || "";
    if (!id) {
      id = (crypto.randomUUID ? crypto.randomUUID() : `${Date.now()}-${Math.random()}`).replace(/[^a-zA-Z0-9_-]/g, "");
      localStorage.setItem(key, id);
    }
  } catch {
    id = `${Date.now()}-${Math.random()}`.replace(/[^a-zA-Z0-9_-]/g, "");
  }
  return id.slice(0, 48) || "default";
}

function clamp3dPitch(value) {
  const pitch = Number(value);
  if (!Number.isFinite(pitch)) return 55;
  return Math.max(MIN_3D_PITCH_DEG, Math.min(MAX_3D_PITCH_DEG, pitch));
}

function pitch3dBlend(pitchDeg) {
  return Math.max(0, Math.min(1, clamp3dPitch(pitchDeg) / FULL_3D_PITCH_DEG));
}

function altitude3dBlend() {
  return pitch3dBlend(state.viewPitch ?? 55);
}

function effective3dViewZoom() {
  if (state.viewMode !== "3d") return 1;
  return clamp3dViewZoom(state.viewZoom || 1);
}

const state = {
  data: null,
  clientId: getClientId(),
  web: null,
  center: null,
  rangeKm: 60,
  selected: "",
  transits: "selected",
  pixelRatio: window.devicePixelRatio || 1,
  dragging: false,
  dragStart: null,
  touchStartDistance: 0,
  pinching: false,
  suppressClick: false,
  drawScheduled: false,
  drawingInteractive: false,
  lastInteractiveDraw: 0,
  interactiveDrawTimer: null,
  fetchInFlight: { light: false, full: false },
  pendingFetch: false,
  pendingFetchDetail: null,
  fetchTimer: null,
  fullFetchTimer: null,
  eventPauseTimer: null,
  eventPredictionPaused: false,
  lowDetailCache: null,
  lastGoodGeodata: null,
  lastGoodGeodataRangeClass: null,
  interactionGeodata: null,
  displayAircraftCache: null,
  aircraftSmoothing: new Map(),
  labelPlacements: new Map(),
  povPlacements: new Map(),
  glideslopeOverride: null,
  clockOffsetMs: null,
  lastStateServerMs: null,
  clockTimer: null,
  lastClockSecond: null,
  lastPovClockSecond: null,
  lastPanelRefreshMs: 0,
  viewMode: "2d",
  viewYaw: 35,
  viewPitch: 55,
  viewZoom: 1,
  viewAz: 0,
  viewEl: 8,
  viewFov: 55,
  viewDragging: false,
  viewDragStart: null,
};

function escapeHtml(value) {
  return String(value ?? "").replace(/[&<>"']/g, (char) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
    "'": "&#39;",
  }[char]));
}

const palettes = {
  current: {
    bgTop: "#0b1721", bgBottom: "#071018", grid: "rgba(116,145,165,0.16)",
    text: "#e8f0f7", dim: "rgba(232,240,247,0.42)", airport: "rgba(147,197,253,0.86)",
    runway: "rgba(180,190,200,0.42)", navaid: "rgba(244,114,182,0.72)",
    vector: "rgba(125,160,180,0.34)", land: "rgba(80,110,80,0.16)",
    aircraft: "#4ade80", selected: "#60a5fa", warning: "#facc15", alert: "#fb7185",
  },
  desktop: {
    bgTop: "#141414", bgBottom: "#080808", grid: "rgba(150,150,150,0.16)",
    text: "#eeeeee", dim: "rgba(210,210,210,0.42)", airport: "rgba(190,190,190,0.92)",
    runway: "rgba(165,165,165,0.76)", navaid: "rgba(210,210,210,0.68)",
    vector: "rgba(145,145,145,0.44)", land: "rgba(120,120,120,0.18)",
    aircraft: "#d8d8d8", selected: "#ffffff", warning: "#f0f0f0", alert: "#ff4040",
  },
  cwp_classic: {
    bgTop: "#020604", bgBottom: "#000201", grid: "rgba(78,146,96,0.10)",
    text: "#d6f5df", dim: "rgba(142,198,154,0.30)", airport: "rgba(126,210,150,0.44)",
    runway: "rgba(176,226,188,0.48)", navaid: "rgba(118,184,150,0.42)",
    vector: "rgba(118,160,128,0.24)", land: "rgba(34,58,40,0.13)",
    water: "rgba(42,104,128,0.30)", waterFill: "rgba(18,50,66,0.13)",
    boundary: "rgba(132,166,138,0.28)", urban: "rgba(132,152,136,0.08)",
    coast: "rgba(126,174,136,0.50)",
    aircraft: "#93f7a0", selected: "#ffffff", warning: "#f5df6a", alert: "#ff5a5a",
    sun: "#ffb25c", moon: "#d9e0e8", acac: "#f5df6a",
  },
  cwp_approach: {
    bgTop: "#020607", bgBottom: "#000203", grid: "rgba(92,164,164,0.10)",
    text: "#d9fbf6", dim: "rgba(148,214,206,0.30)", airport: "rgba(118,230,206,0.58)",
    runway: "rgba(225,246,232,0.70)", navaid: "rgba(108,194,224,0.46)",
    vector: "rgba(116,160,154,0.24)", land: "rgba(38,62,52,0.12)",
    water: "rgba(44,126,166,0.34)", waterFill: "rgba(18,62,88,0.13)",
    boundary: "rgba(136,166,158,0.28)", urban: "rgba(170,190,180,0.08)",
    coast: "rgba(132,198,182,0.50)",
    aircraft: "#5bf0d6", selected: "#ffffff", warning: "#f2d86b", alert: "#ff5555",
    sun: "#ffac55", moon: "#c8e1ff", acac: "#f2d86b",
  },
  cwp_enroute: {
    bgTop: "#03050b", bgBottom: "#010208", grid: "rgba(112,128,172,0.10)",
    text: "#dbe6ff", dim: "rgba(152,164,202,0.30)", airport: "rgba(132,158,214,0.34)",
    runway: "rgba(132,148,178,0.24)", navaid: "rgba(160,176,238,0.48)",
    vector: "rgba(118,136,188,0.28)", land: "rgba(48,56,76,0.12)",
    water: "rgba(60,104,174,0.30)", waterFill: "rgba(28,48,96,0.13)",
    boundary: "rgba(148,156,188,0.36)", urban: "rgba(140,150,170,0.08)",
    coast: "rgba(138,150,178,0.48)",
    aircraft: "#bfd8ff", selected: "#ffffff", warning: "#f0d57a", alert: "#ff6078",
    sun: "#ffb45f", moon: "#cbd8ff", acac: "#f0d57a",
  },
};

function setAppHeight() {
  const height = window.visualViewport?.height || window.innerHeight || document.documentElement.clientHeight;
  document.documentElement.style.setProperty("--app-height", `${Math.max(320, Math.round(height))}px`);
}

function openDialog(dialog) {
  if (typeof dialog.showModal === "function") {
    if (!dialog.open) dialog.showModal();
    return;
  }
  dialog.setAttribute("open", "");
  dialog.classList.add("modal-open");
  document.body.classList.add("modal-open");
}

function closeDialog(dialog) {
  if (typeof dialog.close === "function") {
    dialog.close();
    return;
  }
  dialog.removeAttribute("open");
  dialog.classList.remove("modal-open");
  document.body.classList.remove("modal-open");
}

function palette() {
  const style = state.data?.settings?.web?.visual_style || state.web?.visual_style || "cwp_classic";
  return palettes[style === "atc" ? "cwp_classic" : style] || palettes.cwp_classic;
}

const els = {
  scaleChip: document.getElementById("scaleChip"),
  connBadge: document.getElementById("connBadge"),
  clockLine: document.getElementById("clockLine"),
  activeCount: document.getElementById("activeCount"),
  displayedCount: document.getElementById("displayedCount"),
  eventCount: document.getElementById("eventCount"),
  statusList: document.getElementById("statusList"),
  selectedAircraft: document.getElementById("selectedAircraft"),
  eventsList: document.getElementById("eventsList"),
  trafficList: document.getElementById("trafficList"),
  centerUser: document.getElementById("centerUser"),
  toggleTransits: document.getElementById("toggleTransits"),
  viewModeButton: document.getElementById("viewModeButton"),
  viewOverlay: document.getElementById("viewOverlay"),
  viewTitle: document.getElementById("viewTitle"),
  viewHint: document.getElementById("viewHint"),
  closeViewOverlay: document.getElementById("closeViewOverlay"),
  viewCanvas: document.getElementById("viewCanvas"),
  settingsDialog: document.getElementById("settingsDialog"),
  openSettings: document.getElementById("openSettings"),
  closeSettings: document.getElementById("closeSettings"),
  settingsBody: document.getElementById("settingsBody"),
  settingsMessage: document.getElementById("settingsMessage"),
  saveSettings: document.getElementById("saveSettings"),
  gpsButton: document.getElementById("gpsButton"),
  windowsGpsButton: document.getElementById("windowsGpsButton"),
  hidePanel: document.getElementById("hidePanel"),
  showPanel: document.getElementById("showPanel"),
  mapAircraftInfo: document.getElementById("mapAircraftInfo"),
};

function fmtNum(value, digits = 0, suffix = "") {
  if (value === null || value === undefined || Number.isNaN(Number(value))) return "--";
  return `${Number(value).toFixed(digits)}${suffix}`;
}

function fmtEta(sec) {
  if (sec === null || sec === undefined) return "--";
  const rounded = Math.round(sec);
  if (rounded < 0) return `+${Math.abs(rounded)}s`;
  return `${rounded}s`;
}

function estimatedNowMs() {
  return state.clockOffsetMs === null ? Date.now() : performance.now() + state.clockOffsetMs;
}

function syncClockFromServer(serverTime) {
  const parsed = Date.parse(serverTime);
  if (!Number.isFinite(parsed)) return;
  state.lastStateServerMs = parsed;
  const offset = parsed - performance.now();
  state.clockOffsetMs = state.clockOffsetMs === null
    ? offset
    : state.clockOffsetMs * 0.9 + offset * 0.1;
}

function formatClockTime(date) {
  return date.toLocaleString(undefined, {
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
    hour: "2-digit",
    minute: "2-digit",
    second: "2-digit",
    hour12: false,
  });
}

function fmtEtaForTime(timeIso, fallbackSec) {
  const targetMs = Date.parse(timeIso);
  if (Number.isFinite(targetMs)) return fmtEta((targetMs - estimatedNowMs()) / 1000);
  return fmtEta(fallbackSec);
}

function updateLiveTimeLabels() {
  const nowMs = estimatedNowMs();
  const wholeSecond = Math.floor(nowMs / 1000);
  if (state.lastClockSecond !== wholeSecond) {
    state.lastClockSecond = wholeSecond;
    els.clockLine.textContent = formatClockTime(new Date(nowMs));
    document.querySelectorAll(".live-eta[data-event-time]").forEach((node) => {
      node.textContent = fmtEtaForTime(node.dataset.eventTime, Number(node.dataset.etaSec));
    });
  }
  if (state.data?.events?.length && state.lastPovClockSecond !== wholeSecond) {
    state.lastPovClockSecond = wholeSecond;
    requestDraw(false);
  }
  if (state.data?.aircraft?.length && !state.dragging && !state.touchStartDistance) {
    requestDraw(false);
  }
  drawActiveView();
}

function startClockLoop() {
  updateLiveTimeLabels();
  state.clockTimer = setTimeout(startClockLoop, 50);
}

function unitConfig() {
  const web = state.data?.settings?.web || state.web || {};
  return {
    distance: web.unit_distance || "km",
    speed: web.unit_speed || "kt",
    altitude: web.unit_altitude || "ft",
    labelFields: Array.isArray(web.aircraft_label_fields) ? web.aircraft_label_fields : ["callsign", "altitude", "speed", "vs"],
    labelLines: Array.isArray(web.aircraft_label_lines) ? web.aircraft_label_lines : [["callsign"], ["altitude", "speed", "vs"]],
    labelSize: web.aircraft_label_size || "medium",
  };
}

function aircraftLabelMetrics(size = unitConfig().labelSize) {
  const metrics = {
    small: { fontPx: 10, lineHeight: 10, boxPad: 5 },
    medium: { fontPx: 12, lineHeight: 12, boxPad: 6 },
    large: { fontPx: 14, lineHeight: 15, boxPad: 7 },
  }[size] || { fontPx: 12, lineHeight: 12, boxPad: 6 };
  return {
    ...metrics,
    font: `${metrics.fontPx}px ui-monospace, monospace`,
  };
}

function convertDistanceKm(valueKm) {
  const unit = unitConfig().distance;
  if (valueKm === null || valueKm === undefined) return [null, unit];
  if (unit === "nm") return [valueKm / 1.852, "nm"];
  if (unit === "mi") return [valueKm * 0.621371, "mi"];
  return [valueKm, "km"];
}

function convertSpeedKt(valueKt) {
  const unit = unitConfig().speed;
  if (valueKt === null || valueKt === undefined) return [null, unit];
  if (unit === "kmh") return [valueKt * 1.852, "km/h"];
  if (unit === "mph") return [valueKt * 1.15078, "mph"];
  return [valueKt, "kt"];
}

function convertAltitudeFt(valueFt) {
  const unit = unitConfig().altitude;
  if (valueFt === null || valueFt === undefined) return [null, unit];
  if (unit === "m") return [valueFt * 0.3048, "m"];
  return [valueFt, "ft"];
}

function destinationPoint(latDeg, lonDeg, bearingDeg, distanceKm) {
  if (![latDeg, lonDeg, bearingDeg, distanceKm].every((value) => Number.isFinite(Number(value)))) return null;
  if (Math.abs(distanceKm) < 1e-6) return { lat: Number(latDeg), lon: Number(lonDeg) };
  const earthRadiusKm = 6371.0088;
  const lat1 = (Number(latDeg) * Math.PI) / 180;
  const lon1 = (Number(lonDeg) * Math.PI) / 180;
  const brng = (Number(bearingDeg) * Math.PI) / 180;
  const angularDistance = Number(distanceKm) / earthRadiusKm;
  const sinLat1 = Math.sin(lat1);
  const cosLat1 = Math.cos(lat1);
  const sinAd = Math.sin(angularDistance);
  const cosAd = Math.cos(angularDistance);
  const lat2 = Math.asin(sinLat1 * cosAd + cosLat1 * sinAd * Math.cos(brng));
  const lon2 = lon1 + Math.atan2(
    Math.sin(brng) * sinAd * cosLat1,
    cosAd - sinLat1 * Math.sin(lat2),
  );
  return {
    lat: (lat2 * 180) / Math.PI,
    lon: ((((lon2 * 180) / Math.PI) + 540) % 360) - 180,
  };
}

function predictAircraftPosition(ac, dtSec) {
  if (!ac || ac.lat === null || ac.lon === null) return null;
  const speedKt = Number(ac.speed);
  const trackDeg = Number(ac.track);
  const altitudeFt = Number(ac.altitude);
  const vsFpm = Number(ac.vs);
  if (!Number.isFinite(speedKt) || !Number.isFinite(trackDeg)) return null;
  const distanceKm = Math.max(0, speedKt) * 1.852 * Math.max(0, dtSec) / 3600;
  const dest = destinationPoint(Number(ac.lat), Number(ac.lon), trackDeg, distanceKm);
  if (!dest) return null;
  const alt = Number.isFinite(altitudeFt)
    ? altitudeFt + (Number.isFinite(vsFpm) ? vsFpm * Math.max(0, dtSec) / 60 : 0)
    : ac.altitude;
  return { lat: dest.lat, lon: dest.lon, altitude: alt };
}

function haversineKm(lat1, lon1, lat2, lon2) {
  if (![lat1, lon1, lat2, lon2].every((value) => Number.isFinite(Number(value)))) return null;
  const earthRadiusKm = 6371.0088;
  const phi1 = (Number(lat1) * Math.PI) / 180;
  const phi2 = (Number(lat2) * Math.PI) / 180;
  const dPhi = ((Number(lat2) - Number(lat1)) * Math.PI) / 180;
  const dLambda = ((Number(lon2) - Number(lon1)) * Math.PI) / 180;
  const a = Math.sin(dPhi / 2) ** 2 + Math.cos(phi1) * Math.cos(phi2) * Math.sin(dLambda / 2) ** 2;
  return earthRadiusKm * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
}

function clientExtrapolationSec() {
  if (!state.lastStateServerMs) return 0;
  const dt = (estimatedNowMs() - state.lastStateServerMs) / 1000;
  if (!Number.isFinite(dt) || dt <= 0.05) return 0;
  return Math.min(8, dt);
}

function activeDisplayAircraft() {
  const aircraft = state.data?.aircraft || [];
  const dt = clientExtrapolationSec();
  const frameMs = performance.now();
  const user = state.data?.settings?.user;
  const center = state.center || state.data?.settings?.center || user;
  const cacheKey = [
    state.lastStateServerMs || 0,
    Math.floor(estimatedNowMs() / 50),
    state.viewMode,
    center?.lat?.toFixed?.(5) ?? "",
    center?.lon?.toFixed?.(5) ?? "",
  ].join(":");
  if (state.displayAircraftCache?.key === cacheKey) return state.displayAircraftCache.aircraft;
  const visibleIcaos = new Set();
  const displayAircraft = aircraft.map((ac) => {
    if (ac.icao) visibleIcaos.add(ac.icao);
    if ((!ac.visible && state.viewMode !== "3d") || ac.grounded) return ac;
    const predicted = predictAircraftPosition(ac, dt);
    if (!predicted) return ac;
    const prev = state.aircraftSmoothing.get(ac.icao);
    let lat = predicted.lat;
    let lon = predicted.lon;
    let altitude = predicted.altitude;
    if (prev && Number.isFinite(prev.lat) && Number.isFinite(prev.lon)) {
      const jumpKm = haversineKm(prev.lat, prev.lon, predicted.lat, predicted.lon);
      if (jumpKm !== null && jumpKm < 5) {
        const elapsed = Math.max(0, Math.min(250, frameMs - prev.frameMs));
        const alpha = 1 - Math.exp(-elapsed / 140);
        lat = prev.lat + (predicted.lat - prev.lat) * alpha;
        lon = prev.lon + (predicted.lon - prev.lon) * alpha;
        if (Number.isFinite(Number(prev.altitude)) && Number.isFinite(Number(predicted.altitude))) {
          altitude = prev.altitude + (predicted.altitude - prev.altitude) * alpha;
        }
      }
    }
    state.aircraftSmoothing.set(ac.icao, { lat, lon, altitude, frameMs });
    const next = { ...ac, lat, lon, altitude, client_extrapolated_sec: dt };
    if (user) next.distance_km = haversineKm(user.lat, user.lon, next.lat, next.lon);
    if (center) next.view_distance_km = haversineKm(center.lat, center.lon, next.lat, next.lon);
    return next;
  });
  for (const icao of state.aircraftSmoothing.keys()) {
    if (!visibleIcaos.has(icao)) state.aircraftSmoothing.delete(icao);
  }
  state.displayAircraftCache = { key: cacheKey, aircraft: displayAircraft };
  return displayAircraft;
}

function clamp3dViewZoom(value) {
  return Math.max(MIN_3D_VIEW_ZOOM, Math.min(MAX_3D_VIEW_ZOOM, Number(value) || 1));
}

function clamp3dRangeKm(value) {
  return Math.max(MIN_3D_RANGE_KM, Math.min(MAX_3D_RANGE_KM, Number(value) || 60));
}

function isMapInteracting() {
  return Boolean(state.dragging || state.viewDragging || state.touchStartDistance || state.pinching);
}

function geodataHasVectors(geo) {
  return Boolean(geo && Array.isArray(geo.vectors) && geo.vectors.length);
}

function geodataVisualQuality(geo) {
  if (!geodataHasVectors(geo)) return 0;
  return geo.vectors.reduce((score, feature) => {
    const layer = String(feature?.layer || "");
    if (feature?.type === "polygon" || layer.includes("land_fill") || layer.includes("coastline") || layer.startsWith("gshhs_")) {
      return score + 3;
    }
    if (layer.includes("lakes") || layer.includes("rivers")) return score + 2;
    return score + 1;
  }, 0);
}

function geodataRangeClass(rangeKm = state.rangeKm) {
  const range = Number(rangeKm || 0);
  if (range >= 700) return "overview";
  if (range >= 420) return "broad";
  if (range >= 260) return "wide";
  if (range >= 120) return "mid";
  return "near";
}

function activeGeodataForDrawing() {
  if (isMapInteracting() && state.interactionGeodata) return state.interactionGeodata;
  const geo = state.data?.geodata;
  if (state.lastGoodGeodataRangeClass !== geodataRangeClass()) return geodataHasVectors(geo) ? geo : state.lastGoodGeodata || geo;
  if (geodataVisualQuality(geo) >= Math.max(1, geodataVisualQuality(state.lastGoodGeodata) * 0.45)) return geo;
  return state.lastGoodGeodata || geo;
}

function lockInteractionGeodata() {
  state.interactionGeodata = activeGeodataForDrawing();
}

function releaseInteractionGeodata(delay = 260) {
  setTimeout(() => {
    if (!isMapInteracting()) state.interactionGeodata = null;
  }, delay);
}

function enforce3dViewBounds() {
  if (state.viewMode !== "3d") return;
  state.viewZoom = clamp3dViewZoom(state.viewZoom);
  state.rangeKm = clamp3dRangeKm(state.rangeKm);
}

function isAircraftDrawable(ac) {
  if (!ac || ac.lat === null || ac.lon === null) return false;
  return state.viewMode === "3d" || Boolean(ac.visible);
}

function isAircraftTrackDrawable(ac) {
  if (!isAircraftDrawable(ac)) return false;
  if (state.viewMode !== "3d") return true;
  const point = projectWithAltitude(ac.lat, ac.lon, aircraftAltM(ac));
  if (!point) return false;
  const rect = canvas.getBoundingClientRect();
  const margin = 90;
  return point.x >= -margin && point.x <= rect.width + margin && point.y >= -margin && point.y <= rect.height + margin;
}

function formatWithUnit(value, digits, unit) {
  if (value === null || value === undefined || Number.isNaN(Number(value))) return "--";
  return `${Number(value).toFixed(digits)}${unit}`;
}

function formatDistanceKm(valueKm, digits = 1) {
  const [value, unit] = convertDistanceKm(valueKm);
  return formatWithUnit(value, digits, unit);
}

function formatSpeedKt(valueKt, digits = 0) {
  const [value, unit] = convertSpeedKt(valueKt);
  return formatWithUnit(value, digits, unit);
}

function formatAltitudeFt(valueFt, digits = 0) {
  const [value, unit] = convertAltitudeFt(valueFt);
  return formatWithUnit(value, digits, unit);
}

function formatAltitudeM(valueM, digits = 0) {
  const units = unitConfig().altitude;
  if (valueM === null || valueM === undefined || Number.isNaN(Number(valueM))) return "--";
  if (units === "ft") return formatWithUnit(Number(valueM) * 3.28084, digits, "ft");
  return formatWithUnit(Number(valueM), digits, "m");
}

function formatVerticalSpeedFpm(valueFpm) {
  if (valueFpm === null || valueFpm === undefined || Number.isNaN(Number(valueFpm))) return "--";
  const value = Number(valueFpm);
  const sign = value > 0 ? "+" : value < 0 ? "-" : "";
  if (unitConfig().altitude === "m") {
    return `${sign}${Math.abs(value * 0.00508).toFixed(1)}m/s`;
  }
  return `${sign}${Math.abs(value).toFixed(0)}fpm`;
}

function verticalTrend(valueFpm) {
  if (valueFpm === null || valueFpm === undefined || Number.isNaN(Number(valueFpm))) return "";
  const value = Number(valueFpm);
  if (value > 64) return "↑";
  if (value < -64) return "↓";
  return "";
}

function formatTrackDeg(value) {
  if (value === null || value === undefined || Number.isNaN(Number(value))) return "--";
  return String(Math.round(Number(value)) % 360).padStart(3, "0");
}

const aircraftLabelNames = {
  callsign: "Callsign",
  icao: "ICAO",
  distance: "Distance",
  altitude: "Altitude",
  speed: "Speed",
  track: "Track",
  vs: "V/S",
  squawk: "Squawk",
};

const optionLabels = {
  "web.visual_style": {
    current: "Modern",
    desktop: "Classic",
    cwp_classic: "CWP Classic",
    cwp_approach: "CWP Approach",
    cwp_enroute: "CWP Enroute",
  },
  "web.ils_style": {
    atc: "ATC",
    desktop: "Classic",
    minimal: "Minimal",
  },
  "web.aircraft_label_color": {
    aircraft: "White",
    green: "Green",
  },
  "web.unit_distance": {
    km: "Kilometers",
    nm: "Nautical miles",
    mi: "Miles",
  },
  "web.unit_speed": {
    kt: "Knots",
    kmh: "km/h",
    mph: "mph",
  },
  "web.unit_altitude": {
    ft: "Feet",
    m: "Meters",
  },
  "web.aircraft_refresh_interval": {
    realtime: "Realtime",
    1: "1 s",
    2: "2 s",
    5: "5 s",
  },
  "web.trajectory_display_mode": {
    altitude: "Altitude gradient",
    points: "Points",
  },
};

function settingsHelpPanel() {
  return `<details class="settings-help">
    <summary>Settings help</summary>
    <div>
      <p><b>Receiver</b>: SBS Host and SBS Port are the BaseStation TCP source used by the listener. Changes are saved immediately, but the active socket may keep using the old connection until reconnect or restart. RTL Device Index and RTL Gain are dump1090 startup options; restart adsb-web/dump1090 to fully apply them. Use gain -10 for dump1090 auto gain.</p>
      <p><b>Observer</b>: Latitude, longitude, and altitude define the viewing point. They affect range rings, angular event geometry, celestial transit calculations, transit strip ground projection, and POV views. Use GPS or manual entry for observer altitude.</p>
      <p><b>Prediction</b>: Prediction Interval controls how often event prediction runs. Horizon is how far ahead to search. Step is the coarse aircraft-aircraft simulation step. Prediction Average smooths recent speed, track, and vertical speed. Min Event Elevation ignores very low-view-angle events near the horizon. Lower intervals and smaller steps increase CPU load.</p>
      <p><b>Display</b>: Aircraft refresh controls only live aircraft display updates. Track duration controls visible history trails. Speed vector length controls the forward projected blue vector, not the historical trail. Grounded aircraft controls whether landed targets remain visible after landing detection. Event aircraft links draw connectors from event markers to involved aircraft. Full active tracks shows all retained history for active aircraft.</p>
      <p><b>Airport and navaid data</b>: Airport Types and Navaid Types filter the OurAirports data loaded into the map. VORDME is the actual OurAirports type for VOR/DME navaids.</p>
      <p><b>Vector Layers</b>: These are local geographic map layers such as land, boundaries, coastlines, rivers, lakes, and urban areas. Changing them invalidates the map cache and reloads visible layers.</p>
    </div>
  </details>`;
}

function settingsAboutPanel(about = {}) {
  const dependencies = Array.isArray(about.dependencies) ? about.dependencies : [];
  const projectUrl = about.project_url || "https://github.com/RealSeaberry/ADS-B-Transit-Predictor";
  const version = about.version || "development";
  return `<details class="settings-about">
    <summary>About</summary>
    <div class="about-card">
      <img src="${escapeHtml(about.icon_url || "/assets/icon.png")}" alt="" loading="lazy">
      <div>
        <strong>${escapeHtml(about.name || "ADS-B Transit Predictor")}</strong>
        <span>Version ${escapeHtml(version)}</span>
        <a href="${escapeHtml(projectUrl)}" target="_blank" rel="noopener noreferrer">${escapeHtml(projectUrl)}</a>
      </div>
    </div>
    <div class="about-deps">
      <h3>External dependencies and data</h3>
      <ul>
        ${dependencies.map((item) => `<li>${escapeHtml(item)}</li>`).join("")}
      </ul>
    </div>
  </details>`;
}

function optionLabel(key, value) {
  return optionLabels[key]?.[String(value)] || String(value);
}

function aircraftLabelValue(ac, key) {
  const values = {
    callsign: ac.callsign || ac.icao,
    icao: ac.icao,
    distance: formatDistanceKm(ac.distance_km, 1),
    altitude: `${formatAltitudeFt(ac.altitude, 0)}${verticalTrend(ac.vs)}`,
    speed: formatSpeedKt(ac.speed, 0),
    track: formatTrackDeg(ac.track),
    vs: formatVerticalSpeedFpm(ac.vs),
    squawk: ac.squawk || "----",
  };
  return values[key] || "";
}

function isEmergencySquawk(ac) {
  const squawk = String(ac?.squawk || "").padStart(4, "0");
  return squawk === "7500" || squawk === "7600" || squawk === "7700";
}

function buildAircraftLabelLines(ac, fields, lineConfig) {
  const withApproachStatus = (lines) => {
    const status = ac?.approach_status;
    if (!status || !lines.length) return lines;
    const next = [...lines];
    if (!next[0].includes(status)) next[0] = `${next[0]} ${status}`;
    return next;
  };
  if (Array.isArray(lineConfig) && lineConfig.length) {
    const lines = lineConfig.slice(0, 4)
      .map((line) => Array.isArray(line) ? line : [])
      .flatMap((line) => {
        const values = line
          .map((key) => aircraftLabelValue(ac, key))
          .filter((value) => value && value !== "--");
        const rows = [];
        for (let i = 0; i < values.length; i += 2) rows.push(values.slice(i, i + 2).join(" "));
        return rows;
      })
      .filter(Boolean)
      .slice(0, 4);
    if (lines.length) return withApproachStatus(lines);
  }
  const selected = fields && fields.length ? fields : ["callsign"];
  const parts = selected
    .map((key) => aircraftLabelValue(ac, key))
    .filter((value) => value && value !== "--");
  if (!parts.length) return [ac.callsign || ac.icao];
  const lines = [];
  for (let i = 0; i < parts.length; i += 2) {
    lines.push(parts.slice(i, i + 2).join(" "));
  }
  return withApproachStatus(lines.slice(0, 4));
}

function resizeCanvas() {
  const rect = canvas.getBoundingClientRect();
  if (!rect.width || !rect.height) return;
  const ratio = window.devicePixelRatio || 1;
  const targetWidth = Math.max(1, Math.floor(rect.width * ratio));
  const targetHeight = Math.max(1, Math.floor(rect.height * ratio));
  state.pixelRatio = ratio;
  if (canvas.width !== targetWidth) canvas.width = targetWidth;
  if (canvas.height !== targetHeight) canvas.height = targetHeight;
  ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
  draw();
}

function canvasBackingStoreMismatch() {
  const rect = canvas.getBoundingClientRect();
  const ratio = window.devicePixelRatio || 1;
  const targetWidth = Math.max(1, Math.floor((rect.width || 1) * ratio));
  const targetHeight = Math.max(1, Math.floor((rect.height || 1) * ratio));
  return Math.abs(canvas.width - targetWidth) > 2 || Math.abs(canvas.height - targetHeight) > 2;
}

function scheduleResize() {
  requestAnimationFrame(() => {
    resizeCanvas();
    setTimeout(resizeCanvas, 120);
    setTimeout(resizeCanvas, 320);
  });
}

function requestDraw(interactive = false) {
  if (interactive) {
    const now = performance.now();
    const wait = 16 - (now - state.lastInteractiveDraw);
    if (wait > 0) {
      if (!state.interactiveDrawTimer) {
        state.interactiveDrawTimer = setTimeout(() => {
          state.interactiveDrawTimer = null;
          requestDraw(true);
        }, wait);
      }
      return;
    }
    state.lastInteractiveDraw = now;
  }
  if (state.drawScheduled) return;
  state.drawScheduled = true;
  requestAnimationFrame(() => {
    state.drawScheduled = false;
    draw({ interactive });
  });
}

function project(lat, lon) {
  const data = state.data;
  if (!data) return null;
  const rect = canvas.getBoundingClientRect();
  const center = state.center || data.settings.center || data.settings.user;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  const x = rect.width / 2 + (lon - center.lon) * kmPerDegLon * scale;
  const y = rect.height / 2 - (lat - center.lat) * kmPerDegLat * scale;
  const userAltM = userGroundAltitudeM(data);
  const groundAltM = userAltM;
  return transformViewPoint(x, y, (groundAltM - userAltM) / 1000, scale, rect);
}

function projectFlat(lat, lon) {
  const data = state.data;
  if (!data) return null;
  const rect = canvas.getBoundingClientRect();
  const center = state.center || data.settings.center || data.settings.user;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  return {
    x: rect.width / 2 + (lon - center.lon) * kmPerDegLon * scale,
    y: rect.height / 2 - (lat - center.lat) * kmPerDegLat * scale,
    scale,
  };
}

function transformViewPoint(x, y, altitudeKm = 0, scale = null, rect = null) {
  if (state.viewMode !== "3d") return { x, y, scale };
  const viewRect = rect || canvas.getBoundingClientRect();
  const pitchDeg = clamp3dPitch(state.viewPitch ?? 55);
  const effectiveZoom = effective3dViewZoom();
  const s = (scale || Math.min(viewRect.width, viewRect.height) / (state.rangeKm * 2)) * effectiveZoom;
  const cx = viewRect.width / 2;
  const cy = viewRect.height / 2;
  const dx = x - cx;
  const dy = y - cy;
  const yaw = ((state.viewYaw || 0) * Math.PI) / 180;
  const pitch = pitchDeg * Math.PI / 180;
  const rx = dx * Math.cos(yaw) - dy * Math.sin(yaw);
  const ry = dx * Math.sin(yaw) + dy * Math.cos(yaw);
  const altitudePxPerKm = Math.min(s * 1.55, Math.max(24, Math.min(55, viewRect.height / 16)));
  const altitudePitchScale = Math.sin(pitch);
  return {
    x: cx + rx * effectiveZoom,
    y: cy + ry * effectiveZoom * Math.cos(pitch) - altitudeKm * altitudePxPerKm * altitudePitchScale,
    scale: s,
  };
}

function projectWithAltitude(lat, lon, altitudeM = 0) {
  const data = state.data;
  if (!data) return null;
  const rect = canvas.getBoundingClientRect();
  const center = state.center || data.settings.center || data.settings.user;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  const x = rect.width / 2 + (lon - center.lon) * kmPerDegLon * scale;
  const y = rect.height / 2 - (lat - center.lat) * kmPerDegLat * scale;
  const userAltM = userGroundAltitudeM(data);
  return transformViewPoint(x, y, (Number(altitudeM || 0) - userAltM) / 1000, scale, rect);
}

function userGroundAltitudeM(data = state.data) {
  const value = Number(data?.settings?.user?.alt_m);
  return Number.isFinite(value) ? value : 0;
}

function pointAltitudeM(pt, fallbackAltitudeFt = null) {
  const altitudeFt = Number(pt?.altitude);
  if (Number.isFinite(altitudeFt)) return altitudeFt * 0.3048;
  const fallbackFt = Number(fallbackAltitudeFt);
  if (Number.isFinite(fallbackFt)) return fallbackFt * 0.3048;
  return 0;
}

function projectTrackPoint(pt, fallbackAltitudeFt = null) {
  if (state.viewMode === "3d") return projectWithAltitude(pt.lat, pt.lon, pointAltitudeM(pt, fallbackAltitudeFt));
  return project(pt.lat, pt.lon);
}

function projectEventPoint(ev, aircraftMap = null) {
  if (!ev || ev.lat === null || ev.lon === null) return null;
  if (state.viewMode !== "3d") return project(ev.lat, ev.lon);
  let altitudeFt = Number(ev.alt);
  if (!Number.isFinite(altitudeFt) && aircraftMap && Array.isArray(ev.icaos)) {
    for (const icao of ev.icaos) {
      const ac = aircraftMap.get(icao);
      altitudeFt = Number(ac?.altitude);
      if (Number.isFinite(altitudeFt)) break;
    }
  }
  return projectWithAltitude(ev.lat, ev.lon, Number.isFinite(altitudeFt) ? altitudeFt * 0.3048 : 0);
}

function unproject(x, y) {
  const data = state.data;
  if (!data) return null;
  const rect = canvas.getBoundingClientRect();
  const center = state.center || data.settings.center || data.settings.user;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  return {
    lat: center.lat - ((y - rect.height / 2) / scale) / kmPerDegLat,
    lon: center.lon + ((x - rect.width / 2) / scale) / kmPerDegLon,
  };
}

function drawReferenceGrid(w, h, p) {
  ctx.strokeStyle = p.grid;
  ctx.lineWidth = 1;
  const grid = 64;
  for (let x = (w / 2) % grid; x < w; x += grid) {
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, h);
    ctx.stroke();
  }
  for (let y = (h / 2) % grid; y < h; y += grid) {
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w, y);
    ctx.stroke();
  }
}

function niceGroundGridSpacingKm(rangeKm) {
  const range = Number(rangeKm || 60);
  const target = range <= 35 ? Math.max(2, range / 2.5) : Math.max(10, range / 2);
  const steps = [2, 2.5, 5, 7.5, 10, 15, 20, 30, 50, 75, 100, 150, 200, 300, 500, 1000];
  return steps.find((step) => step >= target) || 500;
}

function drawGroundGrid(p) {
  if (!state.data) return;
  const center = state.center || state.data.settings.center || state.data.settings.user;
  const user = state.data.settings.user;
  if (!center || !user) return;
  const rect = canvas.getBoundingClientRect();
  const viewZoom = effective3dViewZoom();
  const effectiveRangeKm = state.rangeKm / Math.max(0.2, viewZoom);
  const spacingKm = niceGroundGridSpacingKm(effectiveRangeKm);
  const pitch = clamp3dPitch(state.viewPitch ?? 55) * Math.PI / 180;
  const aspect = Math.max(1, Math.max(rect.width || 1, rect.height || 1) / Math.max(1, Math.min(rect.width || 1, rect.height || 1)));
  const pitchStretch = 1 / Math.max(0.18, Math.cos(pitch));
  const extentKm = Math.max(effectiveRangeKm * aspect * pitchStretch * 2.8, spacingKm * 12);
  const latRad = (Math.PI / 180) * user.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const centerNorthOffsetKm = (center.lat - user.lat) * kmPerDegLat;
  const centerEastOffsetKm = (center.lon - user.lon) * kmPerDegLon;
  const firstNorthOffsetKm = Math.floor((centerNorthOffsetKm - extentKm) / spacingKm) * spacingKm;
  const lastNorthOffsetKm = Math.ceil((centerNorthOffsetKm + extentKm) / spacingKm) * spacingKm;
  const firstEastOffsetKm = Math.floor((centerEastOffsetKm - extentKm) / spacingKm) * spacingKm;
  const lastEastOffsetKm = Math.ceil((centerEastOffsetKm + extentKm) / spacingKm) * spacingKm;
  ctx.save();
  ctx.strokeStyle = p.grid;
  ctx.lineWidth = 1;
  for (let northKm = firstNorthOffsetKm; northKm <= lastNorthOffsetKm; northKm += spacingKm) {
    const lat = user.lat + northKm / kmPerDegLat;
    const lonA = user.lon + (centerEastOffsetKm - extentKm) / kmPerDegLon;
    const lonB = user.lon + (centerEastOffsetKm + extentKm) / kmPerDegLon;
    strokeGroundLine(lat, lonA, lat, lonB);
  }
  for (let eastKm = firstEastOffsetKm; eastKm <= lastEastOffsetKm; eastKm += spacingKm) {
    const lon = user.lon + eastKm / kmPerDegLon;
    const latA = user.lat + (centerNorthOffsetKm - extentKm) / kmPerDegLat;
    const latB = user.lat + (centerNorthOffsetKm + extentKm) / kmPerDegLat;
    strokeGroundLine(latA, lon, latB, lon);
  }
  ctx.restore();
}

function drawGroundCircle(lat, lon, radiusKm, label = null, labelColor = null) {
  const steps = Math.max(144, Math.min(360, Math.round(radiusKm * 5)));
  ctx.beginPath();
  for (let i = 0; i <= steps; i += 1) {
    const point = destinationPoint(lat, lon, (i / steps) * 360, radiusKm);
    const screen = point ? project(point.lat, point.lon) : null;
    if (!screen) continue;
    if (i === 0) ctx.moveTo(screen.x, screen.y);
    else ctx.lineTo(screen.x, screen.y);
  }
  ctx.closePath();
  ctx.stroke();
  if (label) {
    const labelPoint = destinationPoint(lat, lon, 90, radiusKm);
    const screen = labelPoint ? project(labelPoint.lat, labelPoint.lon) : null;
    if (screen) {
      ctx.fillStyle = labelColor || ctx.strokeStyle;
      ctx.font = "12px ui-monospace, monospace";
      ctx.fillText(label, screen.x + 4, screen.y - 4);
    }
  }
}

function drawGroundDashedLine(aLat, aLon, bLat, bLon, dashPx = 10, gapPx = 6) {
  const totalKm = haversineKm(aLat, aLon, bLat, bLon);
  if (!Number.isFinite(totalKm) || totalKm <= 0) return;
  const bearing = calculateBearing(aLat, aLon, bLat, bLon);
  const dashKm = Math.max(0.05, groundKmForScreenPixels(dashPx));
  const gapKm = Math.max(0.03, groundKmForScreenPixels(gapPx));
  for (let distKm = 0; distKm < totalKm; distKm += dashKm + gapKm) {
    const endKm = Math.min(totalKm, distKm + dashKm);
    const start = destinationPoint(aLat, aLon, bearing, distKm);
    const end = destinationPoint(aLat, aLon, bearing, endKm);
    if (start && end) strokeGroundLine(start.lat, start.lon, end.lat, end.lon);
  }
}

function drawGroundDashedCircle(lat, lon, radiusKm, dashPx = 6, gapPx = 5) {
  const radius = Number(radiusKm);
  if (!Number.isFinite(radius) || radius <= 0) return;
  const circumferenceKm = 2 * Math.PI * radius;
  const dashKm = Math.max(0.05, groundKmForScreenPixels(dashPx));
  const gapKm = Math.max(0.03, groundKmForScreenPixels(gapPx));
  const cycleKm = dashKm + gapKm;
  for (let startKm = 0; startKm < circumferenceKm; startKm += cycleKm) {
    const endKm = Math.min(circumferenceKm, startKm + dashKm);
    const steps = Math.max(2, Math.ceil((endKm - startKm) / Math.max(0.08, radius * 0.04)));
    ctx.beginPath();
    for (let i = 0; i <= steps; i += 1) {
      const arcKm = startKm + ((endKm - startKm) * i) / steps;
      const bearing = (arcKm / circumferenceKm) * 360;
      const geo = destinationPoint(lat, lon, bearing, radius);
      const screen = geo ? project(geo.lat, geo.lon) : null;
      if (!screen) continue;
      if (i === 0) ctx.moveTo(screen.x, screen.y);
      else ctx.lineTo(screen.x, screen.y);
    }
    ctx.stroke();
  }
}

function feetToKm(feet) {
  const value = Number(feet);
  return Number.isFinite(value) ? value * 0.0003048 : 0;
}

function offsetLatLon(lat, lon, bearingDeg, distanceKm) {
  return destinationPoint(lat, lon, bearingDeg, distanceKm);
}

function interpolateLatLon(lat1, lon1, lat2, lon2, t) {
  return {
    lat: Number(lat1) + (Number(lat2) - Number(lat1)) * t,
    lon: Number(lon1) + (Number(lon2) - Number(lon1)) * t,
  };
}

function strokeGroundLine(aLat, aLon, bLat, bLon) {
  const a = project(aLat, aLon);
  const b = project(bLat, bLon);
  if (!a || !b) return null;
  ctx.beginPath();
  ctx.moveTo(a.x, a.y);
  ctx.lineTo(b.x, b.y);
  ctx.stroke();
  return { a, b };
}

function runwayScreenWidthPx(rwy) {
  const widthKm = feetToKm(rwy?.width_ft || 0);
  if (!widthKm) return 0;
  const mid = interpolateLatLon(rwy.le_lat, rwy.le_lon, rwy.he_lat, rwy.he_lon, 0.5);
  const bearing = calculateBearing(rwy.le_lat, rwy.le_lon, rwy.he_lat, rwy.he_lon);
  const left = offsetLatLon(mid.lat, mid.lon, bearing + 90, widthKm / 2);
  const right = offsetLatLon(mid.lat, mid.lon, bearing + 270, widthKm / 2);
  const a = left ? project(left.lat, left.lon) : null;
  const b = right ? project(right.lat, right.lon) : null;
  return a && b ? Math.hypot(a.x - b.x, a.y - b.y) : 0;
}

function runwayPolygonPoints(rwy) {
  const widthKm = feetToKm(rwy?.width_ft || 0);
  if (!widthKm) return null;
  const bearing = calculateBearing(rwy.le_lat, rwy.le_lon, rwy.he_lat, rwy.he_lon);
  const halfWidthKm = widthKm / 2;
  const points = [
    offsetLatLon(rwy.le_lat, rwy.le_lon, bearing + 90, halfWidthKm),
    offsetLatLon(rwy.he_lat, rwy.he_lon, bearing + 90, halfWidthKm),
    offsetLatLon(rwy.he_lat, rwy.he_lon, bearing + 270, halfWidthKm),
    offsetLatLon(rwy.le_lat, rwy.le_lon, bearing + 270, halfWidthKm),
  ];
  if (points.some((pt) => !pt)) return null;
  return points.map((pt) => project(pt.lat, pt.lon)).filter(Boolean);
}

function groundKmForScreenPixels(px) {
  const rect = canvas.getBoundingClientRect();
  const baseScale = Math.min(rect.width, rect.height) / Math.max(1, state.rangeKm * 2);
  const zoom = effective3dViewZoom();
  return Math.max(0.05, Math.min(2.0, Number(px || 1) / Math.max(0.001, baseScale * zoom)));
}

function drawBackground() {
  const rect = canvas.getBoundingClientRect();
  const w = rect.width;
  const h = rect.height;
  ctx.clearRect(0, 0, w, h);
  const p = palette();
  const mapBaseFill = p.waterFill || p.water || p.land;
  if (mapBaseFill) {
    ctx.fillStyle = mapBaseFill;
    ctx.fillRect(0, 0, w, h);
  }
  const gradient = ctx.createLinearGradient(0, 0, 0, h);
  gradient.addColorStop(0, mapBaseFill || p.bgTop);
  gradient.addColorStop(1, mapBaseFill || p.bgBottom);
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, w, h);
  if (state.data?.settings?.web?.show_background_grid !== false) {
    if (state.viewMode === "3d") drawGroundGrid(p);
    else drawReferenceGrid(w, h, p);
  }

  const userPoint = state.data
    ? project(state.data.settings.user.lat, state.data.settings.user.lon)
    : { x: w / 2, y: h / 2 };
  const radiusScale = Math.min(w, h) / (state.rangeKm * 2);
  if (state.data?.settings?.show_range_rings && userPoint) {
    ctx.strokeStyle = p.dim;
    const spacing = state.data.settings.range_ring_spacing_km || 18.52;
    const maxRings = Math.max(0, Number(state.data.settings.max_range_rings || 0));
    const ringCount = Math.min(Math.floor(state.rangeKm / spacing), maxRings);
    for (let i = 1; i <= ringCount; i += 1) {
      const km = i * spacing;
      if (state.viewMode === "3d") {
        drawGroundCircle(state.data.settings.user.lat, state.data.settings.user.lon, km, formatDistanceKm(km, km < 10 ? 1 : 0), p.dim);
      } else {
        ctx.beginPath();
        ctx.arc(userPoint.x, userPoint.y, km * radiusScale, 0, Math.PI * 2);
        ctx.stroke();
        ctx.fillStyle = p.dim;
        ctx.font = "12px ui-monospace, monospace";
        ctx.fillText(formatDistanceKm(km, km < 10 ? 1 : 0), userPoint.x + km * radiusScale + 4, userPoint.y - 4);
      }
    }
  }
  if (state.data?.settings?.web?.show_event_range_ring && userPoint) {
    ctx.strokeStyle = p.warning;
    if (state.viewMode === "3d") {
      ctx.setLineDash([]);
      drawGroundDashedCircle(state.data.settings.user.lat, state.data.settings.user.lon, state.data.settings.conflict_radius_km || 30, 6, 5);
    } else {
      ctx.setLineDash([6, 5]);
      ctx.beginPath();
      ctx.arc(userPoint.x, userPoint.y, (state.data.settings.conflict_radius_km || 30) * radiusScale, 0, Math.PI * 2);
      ctx.stroke();
    }
    ctx.setLineDash([]);
  }
  if (userPoint) {
    ctx.strokeStyle = p.text;
    ctx.beginPath();
    ctx.moveTo(userPoint.x - 6, userPoint.y);
    ctx.lineTo(userPoint.x + 6, userPoint.y);
    ctx.moveTo(userPoint.x, userPoint.y - 6);
    ctx.lineTo(userPoint.x, userPoint.y + 6);
    ctx.stroke();
  }
}

function drawPanFeedback() {
  if (!state.dragging || !state.dragStart || !state.center) return;
  const rect = canvas.getBoundingClientRect();
  const p = palette();
  const start = state.dragStart.center;
  const center = state.center;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos((Math.PI / 180) * start.lat));
  const eastKm = (center.lon - start.lon) * kmPerDegLon;
  const northKm = (center.lat - start.lat) * kmPerDegLat;
  const distanceKm = Math.hypot(eastKm, northKm);
  const ns = Math.abs(northKm) < 0.05 ? "" : northKm > 0 ? "N" : "S";
  const ew = Math.abs(eastKm) < 0.05 ? "" : eastKm > 0 ? "E" : "W";
  const label = `Pan ${formatDistanceKm(distanceKm, distanceKm < 10 ? 1 : 0)} ${ns}${ew}`.trim();
  ctx.save();
  ctx.font = "12px ui-monospace, monospace";
  const width = ctx.measureText(label).width + 18;
  const x = Math.max(12, (rect.width - width) / 2);
  const y = 16;
  ctx.fillStyle = "rgba(8, 11, 15, 0.82)";
  ctx.strokeStyle = "rgba(255, 255, 255, 0.24)";
  ctx.lineWidth = 1;
  ctx.fillRect(x, y, width, 28);
  ctx.strokeRect(x, y, width, 28);
  ctx.fillStyle = p.text;
  ctx.fillText(label, x + 9, y + 18);
  ctx.restore();
}

function geodataLayerStyle(feature, p, lowDetail = false) {
  const layer = feature.layer || "";
  const water = p.water || "rgba(96, 165, 250, 0.58)";
  const waterFill = p.waterFill || "rgba(37, 99, 235, 0.13)";
  const boundary = p.boundary || "rgba(226, 232, 240, 0.45)";
  const urban = p.urban || "rgba(248, 250, 252, 0.10)";
  const baseWidth = lowDetail ? 1.0 : 1.0;
  const coast = p.coast || "rgba(168, 168, 168, 0.74)";
  const isLandFill = feature.type === "polygon" && (
    layer.startsWith("gshhs_") ||
    layer === "ne_10m_land" ||
    layer.includes("ocean") ||
    layer.includes("geography_regions") ||
    layer.includes("minor_islands") ||
    layer.includes("countries")
  );
  if (isLandFill) return { stroke: null, fill: colorWithAlpha(p.land, 0.92), width: 0 };
  if (lowDetail && (layer.startsWith("gshhs_") || layer.includes("coastline"))) {
    return { stroke: coast, fill: null, width: 0.85 };
  }
  if (layer.startsWith("gshhs_")) return { stroke: coast, fill: null, width: baseWidth + 0.2 };
  if (layer.includes("coastline")) return { stroke: coast, fill: null, width: baseWidth + 0.2 };
  if (layer.includes("boundary")) return { stroke: boundary, fill: null, width: baseWidth + 0.3 };
  if (layer.includes("lakes") || layer.includes("rivers") || layer.includes("ocean")) {
    return { stroke: water, fill: feature.type === "polygon" ? waterFill : null, width: baseWidth };
  }
  if (lowDetail && layer.includes("urban")) return { stroke: null, fill: null, width: 0 };
  if (layer.includes("urban")) return { stroke: urban, fill: feature.type === "polygon" ? urban : null, width: baseWidth - 0.2 };
  if (layer.includes("land") || layer.includes("countries")) {
    return { stroke: p.vector, fill: feature.type === "polygon" ? p.land : null, width: baseWidth - 0.1 };
  }
  return { stroke: feature.type === "polygon" ? p.land : p.vector, fill: feature.type === "polygon" ? p.land : null, width: baseWidth };
}

function drawGeodata() {
  const geo = activeGeodataForDrawing();
  if (!geo) return;
  const p = palette();
  const labelRangeKm = state.viewMode === "3d"
    ? state.rangeKm / Math.max(0.25, effective3dViewZoom())
    : state.rangeKm;
  (geo.vectors || []).forEach((feature) => {
    const pts = (feature.points || []).map((pt) => project(pt[1], pt[0])).filter(Boolean);
    if (pts.length < 2) return;
    const style = geodataLayerStyle(feature, p);
    if (!style.fill && (!style.stroke || style.width <= 0)) return;
    if (style.stroke) ctx.strokeStyle = style.stroke;
    if (style.fill) ctx.fillStyle = style.fill;
    ctx.lineWidth = style.width;
    ctx.beginPath();
    ctx.moveTo(pts[0].x, pts[0].y);
    pts.slice(1).forEach((point) => ctx.lineTo(point.x, point.y));
    if (feature.type === "polygon") {
      ctx.closePath();
      if (style.fill) ctx.fill();
    }
    if (style.stroke && style.width > 0) ctx.stroke();
  });
  ctx.lineWidth = 1;
  ctx.strokeStyle = p.runway;
  (geo.runways || []).forEach((rwy, index) => {
    const a = project(rwy.le_lat, rwy.le_lon);
    const b = project(rwy.he_lat, rwy.he_lon);
    if (!a || !b) return;
    rwy.__screen = { a, b, index };
    const widthPx = runwayScreenWidthPx(rwy);
    const drawTrueWidth = state.rangeKm <= 30 || widthPx >= 2.2;
    let runwayDrawn = false;
    if (drawTrueWidth) {
      const poly = runwayPolygonPoints(rwy);
      if (poly?.length === 4) {
        ctx.save();
        ctx.fillStyle = colorWithAlpha(p.runway, state.viewMode === "3d" ? 0.34 : 0.42);
        ctx.strokeStyle = p.runway;
        ctx.lineWidth = Math.max(0.8, Math.min(1.4, widthPx * 0.25));
        ctx.beginPath();
        ctx.moveTo(poly[0].x, poly[0].y);
        poly.slice(1).forEach((pt) => ctx.lineTo(pt.x, pt.y));
        ctx.closePath();
        ctx.fill();
        if (widthPx >= 3.5) ctx.stroke();
        ctx.restore();
        runwayDrawn = true;
      }
    }
    if (!runwayDrawn) {
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.stroke();
    }
    if (labelRangeKm < 110) {
      drawRunwayEndLabels(rwy, a, b);
    }
  });
  drawGlideslopes();
  ctx.fillStyle = p.airport;
  (geo.airports || []).forEach((apt) => {
    const point = project(apt.lat, apt.lon);
    if (!point) return;
    ctx.fillRect(point.x - 2, point.y - 2, 4, 4);
    if (labelRangeKm < 180) {
      ctx.fillStyle = p.text;
      ctx.font = "11px ui-monospace, monospace";
      ctx.fillText(apt.ident, point.x + 5, point.y - 5);
      ctx.fillStyle = p.airport;
    }
  });
  ctx.strokeStyle = p.navaid;
  (geo.navaids || []).forEach((nav) => {
    const p = project(nav.lat, nav.lon);
    if (!p) return;
    ctx.beginPath();
    ctx.arc(p.x, p.y, 2.5, 0, Math.PI * 2);
    ctx.stroke();
    if (labelRangeKm < 220) {
      ctx.fillStyle = palette().text;
      ctx.font = "10px ui-monospace, monospace";
      ctx.fillText(nav.ident || nav.name || "", p.x + 5, p.y + 3);
      ctx.strokeStyle = palette().navaid;
    }
  });
}

function drawRunwayEndLabels(rwy, a, b) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const len = Math.hypot(dx, dy) || 1;
  const ux = dx / len;
  const uy = dy / len;
  const labels = [
    { text: rwy.le_ident, x: a.x - ux * 11, y: a.y - uy * 11 },
    { text: rwy.he_ident, x: b.x + ux * 11, y: b.y + uy * 11 },
  ];
  ctx.save();
  ctx.font = "9px ui-monospace, monospace";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  labels.forEach((label) => {
    if (!label.text) return;
    ctx.lineWidth = 3;
    ctx.strokeStyle = "rgba(0, 0, 0, 0.78)";
    ctx.strokeText(label.text, label.x, label.y);
    ctx.fillStyle = palette().text;
    ctx.fillText(label.text, label.x, label.y);
  });
  ctx.restore();
}

function draw3dNorthArrow() {
  if (state.viewMode !== "3d" || !state.data) return;
  const pitchDeg = clamp3dPitch(state.viewPitch ?? 55);
  const yaw = ((state.viewYaw || 0) * Math.PI) / 180;
  const pitch = pitchDeg * Math.PI / 180;
  const cosPitch = Math.cos(pitch);
  const eastBasis = { x: Math.cos(yaw), y: Math.sin(yaw) * cosPitch };
  const northBasis = { x: Math.sin(yaw), y: -Math.cos(yaw) * cosPitch };
  const fit = 20;
  const origin = { x: 56, y: 112 };
  const groundPoint = (eastScale, northScale) => ({
    x: origin.x + (eastBasis.x * eastScale + northBasis.x * northScale) * fit,
    y: origin.y + (eastBasis.y * eastScale + northBasis.y * northScale) * fit,
  });
  const tip = groundPoint(0, 1.82);
  const tail = groundPoint(0, -0.72);
  const leftHead = groundPoint(-0.34, 1.08);
  const spine = groundPoint(0, 1.30);
  const rightHead = groundPoint(0.34, 1.08);
  const pal = palette();
  ctx.save();
  ctx.strokeStyle = colorWithAlpha(pal.text, 0.86);
  ctx.fillStyle = pal.text;
  ctx.lineWidth = 1.25;
  ctx.setLineDash([]);
  ctx.beginPath();
  for (let i = 0; i <= 56; i += 1) {
    const a = (i / 56) * Math.PI * 2;
    const p = groundPoint(Math.cos(a), Math.sin(a));
    if (i === 0) ctx.moveTo(p.x, p.y);
    else ctx.lineTo(p.x, p.y);
  }
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(tail.x, tail.y);
  ctx.lineTo(tip.x, tip.y);
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(tip.x, tip.y);
  ctx.lineTo(leftHead.x, leftHead.y);
  ctx.lineTo(spine.x, spine.y);
  ctx.lineTo(rightHead.x, rightHead.y);
  ctx.closePath();
  ctx.fill();
  ctx.font = "11px ui-monospace, monospace";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  const label = groundPoint(0, 2.36);
  ctx.fillText("N", label.x, label.y);
  ctx.restore();
}

function lowDetailRangeClass() {
  if (state.rangeKm > 320) return "far";
  if (state.rangeKm > 120) return "mid";
  return "near";
}

function lowDetailLayerStyle(feature, p) {
  return geodataLayerStyle(feature, p, true);
}

function buildLowDetailCache(geo, p, paletteKey) {
  const rangeClass = lowDetailRangeClass();
  const limits = {
    far: { maxFeatures: 520, maxPts: 180, minStride: 2, maxRunways: 190, maxAirports: 220, maxNavaids: 240 },
    mid: { maxFeatures: 760, maxPts: 280, minStride: 1, maxRunways: 280, maxAirports: 310, maxNavaids: 340 },
    near: { maxFeatures: 1040, maxPts: 380, minStride: 1, maxRunways: 380, maxAirports: 410, maxNavaids: 440 },
  }[rangeClass];
  const vectors = [];
  for (const feature of geo.vectors || []) {
    if (vectors.length >= limits.maxFeatures) break;
    const source = feature.points || [];
    if (source.length < 2) continue;
    const layer = feature.layer || "";
    const isGshhg = layer.startsWith("gshhs_");
    const isCoastline = isGshhg || layer.includes("coastline");
    const isBoundary = layer.includes("boundary");
    const isLandArea = isGshhg || ["land", "ocean", "countries", "minor_islands", "geography_regions"].some((token) => layer.includes(token));
    const maxPts = isGshhg ? limits.maxPts * 8.0 : isCoastline ? limits.maxPts * 4.5 : isLandArea ? limits.maxPts * 3.6 : isBoundary ? limits.maxPts * 0.45 : limits.maxPts;
    const minStride = (isCoastline || isLandArea) ? Math.max(1, Math.floor(limits.minStride / 2)) : limits.minStride;
    const stride = Math.max(1, Math.ceil(source.length / maxPts), minStride);
    const points = [];
    for (let i = 0; i < source.length; i += stride) points.push(source[i]);
    const last = source[source.length - 1];
    if (points[points.length - 1] !== last) points.push(last);
    if (points.length >= 2) {
      vectors.push({
        type: feature.type,
        points,
        style: lowDetailLayerStyle(feature, p),
      });
    }
  }
  return {
    geo,
    paletteKey,
    rangeClass,
    vectors,
    runways: (geo.runways || []).slice(0, limits.maxRunways),
    airports: (geo.airports || []).slice(0, limits.maxAirports),
    navaids: (geo.navaids || []).slice(0, limits.maxNavaids),
  };
}

function getLowDetailCache(geo, p) {
  const paletteKey = state.data?.settings?.web?.visual_style || state.web?.visual_style || "cwp_classic";
  const rangeClass = lowDetailRangeClass();
  if (
    !state.lowDetailCache ||
    state.lowDetailCache.geo !== geo ||
    state.lowDetailCache.paletteKey !== paletteKey ||
    state.lowDetailCache.rangeClass !== rangeClass
  ) {
    state.lowDetailCache = buildLowDetailCache(geo, p, paletteKey);
  }
  return state.lowDetailCache;
}

function drawGeodataLowDetail() {
  const geo = activeGeodataForDrawing();
  if (!geo) return;
  const rect = canvas.getBoundingClientRect();
  const p = palette();
  const center = state.center || state.data.settings.center || state.data.settings.user;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  const projectFast = state.viewMode === "3d"
    ? (lat, lon) => project(lat, lon)
    : (lat, lon) => ({
      x: rect.width / 2 + (lon - center.lon) * kmPerDegLon * scale,
      y: rect.height / 2 - (lat - center.lat) * kmPerDegLat * scale,
    });
  const inView = (point, margin = 80) => (
    point &&
    point.x >= -margin &&
    point.x <= rect.width + margin &&
    point.y >= -margin &&
    point.y <= rect.height + margin
  );
  const cache = getLowDetailCache(geo, p);

  ctx.save();
  ctx.globalAlpha = 1;
  for (const feature of cache.vectors) {
    const points = feature.points;
    if (points.length < 2) continue;
    const style = feature.style;
    if (!style.fill && (!style.stroke || style.width <= 0)) continue;
    if (style.stroke) ctx.strokeStyle = style.stroke;
    if (style.fill) ctx.fillStyle = style.fill;
    ctx.lineWidth = style.width;
    ctx.beginPath();
    const first = projectFast(points[0][1], points[0][0]);
    let visible = inView(first);
    ctx.moveTo(first.x, first.y);
    for (let i = 1; i < points.length; i += 1) {
      const pt = projectFast(points[i][1], points[i][0]);
      if (!visible && inView(pt)) visible = true;
      ctx.lineTo(pt.x, pt.y);
    }
    if (!visible && feature.type !== "polygon") continue;
    if (feature.type === "polygon") {
      ctx.closePath();
      if (style.fill) ctx.fill();
    }
    if (style.stroke && style.width > 0) ctx.stroke();
  }

  if (state.rangeKm < 220) {
    ctx.strokeStyle = "rgba(229, 231, 235, 0.46)";
    ctx.lineWidth = 0.9;
    let runwayCount = 0;
    for (const rwy of cache.runways) {
      const a = projectFast(rwy.le_lat, rwy.le_lon);
      const b = projectFast(rwy.he_lat, rwy.he_lon);
      if (!inView(a) && !inView(b)) continue;
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.stroke();
      runwayCount += 1;
    }
  }

  ctx.fillStyle = p.airport;
  let airportCount = 0;
  for (const apt of cache.airports) {
    const point = projectFast(apt.lat, apt.lon);
    if (!inView(point, 20)) continue;
    ctx.fillRect(point.x - 1.5, point.y - 1.5, 3, 3);
    airportCount += 1;
  }

  ctx.strokeStyle = p.navaid;
  ctx.lineWidth = 1;
  let navaidCount = 0;
  for (const nav of cache.navaids) {
    const point = projectFast(nav.lat, nav.lon);
    if (!inView(point, 20)) continue;
    ctx.beginPath();
    ctx.moveTo(point.x - 2.5, point.y);
    ctx.lineTo(point.x + 2.5, point.y);
    ctx.moveTo(point.x, point.y - 2.5);
    ctx.lineTo(point.x, point.y + 2.5);
    ctx.stroke();
    navaidCount += 1;
  }
  ctx.restore();
}

function shouldDrawLowDetailGeodata(interactive = false) {
  if (state.viewMode === "ar") return false;
  if (interactive || isMapInteracting()) return false;
  return state.rangeKm > 700 && !geodataHasVectors(activeGeodataForDrawing());
}

function displayGlideslopes() {
  if (state.glideslopeOverride) return state.glideslopeOverride.glideslopes || [];
  const existing = state.data?.glideslopes || [];
  const active = state.data?.settings?.web?.active_glideslopes || state.web?.active_glideslopes || [];
  if (!active.length) return existing;
  const keyFor = (item) => `${item.airport}:${item.runway_index}:${item.end || item.runway_end_ident}`;
  const existingKeys = new Set(existing.map(keyFor));
  const runwayMap = new Map((state.data?.geodata?.runways || []).map((rwy) => [`${rwy.airport}:${rwy.runway_index}`, rwy]));
  const derived = [];
  active.forEach((item) => {
    const key = keyFor(item);
    if (existingKeys.has(key)) return;
    const runway = runwayMap.get(`${item.airport}:${item.runway_index}`);
    if (!runway) return;
    const gs = glideslopeFromRunway(runway, item.end || item.runway_end_ident, item);
    if (gs) derived.push(gs);
  });
  return existing.concat(derived);
}

function activeGlideslopeItems() {
  return state.glideslopeOverride?.activeItems
    || state.web?.active_glideslopes
    || state.data?.settings?.web?.active_glideslopes
    || [];
}

function copyGlideslopeItems(items) {
  return Array.isArray(items) ? items.map((item) => ({ ...item })) : [];
}

function glideslopeItemsKey(items) {
  return copyGlideslopeItems(items)
    .map((item) => `${item.airport}:${item.runway_index}:${item.end || item.runway_end_ident || ""}`)
    .sort()
    .join("|");
}

function drawGlideslopes() {
  if (!state.data?.settings?.show_glideslope) return;
  const p = palette();
  const style = state.data?.settings?.web?.ils_style || "atc";
  displayGlideslopes().forEach((gs) => {
    const a = project(gs.start_lat, gs.start_lon);
    const b = project(gs.end_lat, gs.end_lon);
    if (!a || !b) return;
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const len = Math.hypot(dx, dy) || 1;
    const ux = dx / len;
    const uy = dy / len;
    const nx = -uy;
    const ny = ux;
    const groundBearing = calculateBearing(gs.start_lat, gs.start_lon, gs.end_lat, gs.end_lon);
    const groundNormal = (groundBearing + 90) % 360;

    if (style === "desktop") {
      const halfWidth = 5;
      ctx.save();
      ctx.lineWidth = 1.2;
      ctx.strokeStyle = p.dim;
      ctx.setLineDash([]);
      if (state.viewMode === "3d") {
        const halfWidthKm = groundKmForScreenPixels(halfWidth);
        const leftStart = offsetLatLon(gs.start_lat, gs.start_lon, groundNormal, halfWidthKm);
        const leftEnd = offsetLatLon(gs.end_lat, gs.end_lon, groundNormal, halfWidthKm);
        const rightStart = offsetLatLon(gs.start_lat, gs.start_lon, groundNormal + 180, halfWidthKm);
        const rightEnd = offsetLatLon(gs.end_lat, gs.end_lon, groundNormal + 180, halfWidthKm);
        if (leftStart && leftEnd) strokeGroundLine(leftStart.lat, leftStart.lon, leftEnd.lat, leftEnd.lon);
        if (rightStart && rightEnd) strokeGroundLine(rightStart.lat, rightStart.lon, rightEnd.lat, rightEnd.lon);
      } else {
        ctx.beginPath();
        ctx.moveTo(a.x + nx * halfWidth, a.y + ny * halfWidth);
        ctx.lineTo(b.x + nx * halfWidth, b.y + ny * halfWidth);
        ctx.moveTo(a.x - nx * halfWidth, a.y - ny * halfWidth);
        ctx.lineTo(b.x - nx * halfWidth, b.y - ny * halfWidth);
        ctx.stroke();
      }
      ctx.strokeStyle = p.selected;
      ctx.lineWidth = 1.7;
      strokeGroundLine(gs.start_lat, gs.start_lon, gs.end_lat, gs.end_lon);
      ctx.fillStyle = "rgba(8, 11, 15, 0.72)";
      ctx.strokeStyle = "rgba(255,255,255,0.30)";
      const label = `${gs.airport} ${gs.runway_end_ident} ${Number(gs.length_km / 1.852).toFixed(0)}NM`;
      ctx.font = "11px ui-monospace, monospace";
      const labelW = ctx.measureText(label).width + 10;
      const labelX = b.x + 6;
      const labelY = b.y - 18;
      ctx.fillRect(labelX, labelY, labelW, 18);
      ctx.strokeRect(labelX, labelY, labelW, 18);
      ctx.fillStyle = p.text;
      ctx.fillText(label, labelX + 5, labelY + 13);
      ctx.restore();
      return;
    }

    if (style === "minimal") {
      ctx.save();
      ctx.strokeStyle = p.selected;
      ctx.fillStyle = ctx.strokeStyle;
      ctx.lineWidth = 1.4;
      ctx.setLineDash([]);
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.stroke();
      for (const point of [a, b]) {
        ctx.beginPath();
        ctx.arc(point.x, point.y, 3, 0, Math.PI * 2);
        ctx.fill();
      }
      ctx.strokeStyle = "rgba(255,255,255,0.48)";
      for (let i = 1; i <= 3; i += 1) {
        const t = i / 4;
        const x = a.x + dx * t;
        const y = a.y + dy * t;
        if (state.viewMode === "3d") {
          const center = interpolateLatLon(gs.start_lat, gs.start_lon, gs.end_lat, gs.end_lon, t);
          const tickHalfKm = groundKmForScreenPixels(3);
          const left = offsetLatLon(center.lat, center.lon, groundNormal, tickHalfKm);
          const right = offsetLatLon(center.lat, center.lon, groundNormal + 180, tickHalfKm);
          if (left && right) strokeGroundLine(left.lat, left.lon, right.lat, right.lon);
        } else {
          ctx.beginPath();
          ctx.moveTo(x - nx * 3, y - ny * 3);
          ctx.lineTo(x + nx * 3, y + ny * 3);
          ctx.stroke();
        }
      }
      ctx.restore();
      return;
    }

    ctx.strokeStyle = p.selected;
    ctx.lineWidth = 1.6;
    if (state.viewMode === "3d") {
      ctx.setLineDash([]);
      drawGroundDashedLine(gs.start_lat, gs.start_lon, gs.end_lat, gs.end_lon, 10, 6);
    } else {
      ctx.setLineDash([10, 6]);
      strokeGroundLine(gs.start_lat, gs.start_lon, gs.end_lat, gs.end_lon);
    }
    const ticks = 5;
    for (let i = 1; i <= ticks; i += 1) {
      const t = i / ticks;
      const x = a.x + dx * t;
      const y = a.y + dy * t;
      if (state.viewMode === "3d") {
        const center = interpolateLatLon(gs.start_lat, gs.start_lon, gs.end_lat, gs.end_lon, t);
        const tickHalfKm = groundKmForScreenPixels(5);
        const left = offsetLatLon(center.lat, center.lon, groundNormal, tickHalfKm);
        const right = offsetLatLon(center.lat, center.lon, groundNormal + 180, tickHalfKm);
        if (left && right) strokeGroundLine(left.lat, left.lon, right.lat, right.lon);
      } else {
        ctx.beginPath();
        ctx.moveTo(x - nx * 5, y - ny * 5);
        ctx.lineTo(x + nx * 5, y + ny * 5);
        ctx.stroke();
      }
    }
    ctx.setLineDash([]);
    ctx.fillStyle = p.selected;
    ctx.font = "11px ui-monospace, monospace";
    ctx.fillText(`${gs.airport} ${gs.runway_end_ident} ILS ${Number(gs.length_km / 1.852).toFixed(0)}NM`, b.x + 4, b.y - 4);
  });
  ctx.setLineDash([]);
}

function drawPolyline(points, color, width = 1, fallbackAltitudeFt = null) {
  const projected = points.map((pt) => projectTrackPoint(pt, fallbackAltitudeFt)).filter(Boolean);
  if (projected.length < 2) return;
  ctx.strokeStyle = color;
  ctx.lineWidth = width;
  ctx.beginPath();
  ctx.moveTo(projected[0].x, projected[0].y);
  projected.slice(1).forEach((p) => ctx.lineTo(p.x, p.y));
  ctx.stroke();
}

function drawGroundPolyline(points, color, width = 1) {
  const projected = points.map((pt) => project(pt.lat, pt.lon)).filter(Boolean);
  if (projected.length < 2) return;
  ctx.strokeStyle = color;
  ctx.lineWidth = width;
  ctx.beginPath();
  ctx.moveTo(projected[0].x, projected[0].y);
  projected.slice(1).forEach((p) => ctx.lineTo(p.x, p.y));
  ctx.stroke();
}

function altitudeColor(altitudeFt) {
  if (altitudeFt === null || altitudeFt === undefined) return "#9ca3af";
  if (altitudeFt < 3000) return "#00e5a8";
  if (altitudeFt < 10000) return "#00c8ff";
  if (altitudeFt < 20000) return "#f9f871";
  if (altitudeFt < 30000) return "#ff9f43";
  return "#ff4d6d";
}

function altitudeTrailColor(altitudeFt, minFt = null, maxFt = null) {
  if (altitudeFt === null || altitudeFt === undefined) return "#9ca3af";
  let altitude = Math.max(0, Number(altitudeFt));
  if (minFt !== null && maxFt !== null && maxFt > minFt) {
    const mid = (minFt + maxFt) / 2;
    const amplified = mid + (altitude - mid) * 2.2;
    const halfWindow = Math.max(1800, (maxFt - minFt) * 2.8);
    altitude = Math.max(mid - halfWindow, Math.min(mid + halfWindow, amplified));
  }
  const transitionFt = 3600 * 3.28084;
  const stops = [
    [0, [248, 250, 252]],
    [transitionFt, [250, 204, 21]],
    [32000, [34, 211, 238]],
    [41000, [255, 77, 109]],
  ];
  let left = stops[0];
  let right = stops[stops.length - 1];
  for (let i = 1; i < stops.length; i += 1) {
    if (altitude <= stops[i][0]) {
      left = stops[i - 1];
      right = stops[i];
      break;
    }
  }
  const range = Math.max(0.0001, right[0] - left[0]);
  const local = Math.max(0, Math.min(1, (altitude - left[0]) / range));
  const rgb = left[1].map((channel, idx) => Math.round(channel + (right[1][idx] - channel) * local));
  return `rgb(${rgb[0]}, ${rgb[1]}, ${rgb[2]})`;
}

function drawAltitudePath(points, fallbackColor) {
  const projected = points.map((pt) => ({ ...pt, screen: projectTrackPoint(pt) })).filter((pt) => pt.screen);
  if (projected.length < 2) return;
  const mode = state.data?.settings?.web?.trajectory_display_mode || "altitude";
  if (mode === "points") {
    ctx.fillStyle = "#4ade80";
    ctx.globalAlpha = 0.9;
    projected.forEach((pt) => {
      ctx.beginPath();
      ctx.arc(pt.screen.x, pt.screen.y, 0.45, 0, Math.PI * 2);
      ctx.fill();
    });
    ctx.globalAlpha = 1;
    return;
  }
  const altitudes = projected.map((pt) => pt.altitude).filter((alt) => alt !== null && alt !== undefined);
  const minAlt = altitudes.length ? Math.min(...altitudes) : null;
  const maxAlt = altitudes.length ? Math.max(...altitudes) : null;
  ctx.lineWidth = 1.1;
  ctx.globalAlpha = 0.98;
  for (let i = 1; i < projected.length; i += 1) {
    const a = projected[i - 1];
    const b = projected[i];
    const startColor = altitudeTrailColor(a.altitude ?? b.altitude, minAlt, maxAlt) || fallbackColor;
    const endColor = altitudeTrailColor(b.altitude ?? a.altitude, minAlt, maxAlt) || fallbackColor;
    const grad = ctx.createLinearGradient(a.screen.x, a.screen.y, b.screen.x, b.screen.y);
    grad.addColorStop(0, startColor);
    grad.addColorStop(1, endColor);
    ctx.strokeStyle = grad;
    ctx.beginPath();
    ctx.moveTo(a.screen.x, a.screen.y);
    ctx.lineTo(b.screen.x, b.screen.y);
    ctx.stroke();
  }
  ctx.globalAlpha = 1;
}

function pointSegmentDistance(px, py, ax, ay, bx, by) {
  const dx = bx - ax;
  const dy = by - ay;
  const lenSq = dx * dx + dy * dy;
  if (!lenSq) return Math.hypot(px - ax, py - ay);
  const t = Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / lenSq));
  return Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
}

function nearestRunwayAt(x, y) {
  let best = null;
  let bestDistance = 12;
  (state.data?.geodata?.runways || []).forEach((rwy) => {
    const a = project(rwy.le_lat, rwy.le_lon);
    const b = project(rwy.he_lat, rwy.he_lon);
    if (!a || !b) return;
    const distance = pointSegmentDistance(x, y, a.x, a.y, b.x, b.y);
    if (distance < bestDistance) {
      best = rwy;
      bestDistance = distance;
    }
  });
  return best;
}

function calculateBearing(lat1Deg, lon1Deg, lat2Deg, lon2Deg) {
  const lat1 = (Number(lat1Deg) * Math.PI) / 180;
  const lat2 = (Number(lat2Deg) * Math.PI) / 180;
  const dLon = ((Number(lon2Deg) - Number(lon1Deg)) * Math.PI) / 180;
  const y = Math.sin(dLon) * Math.cos(lat2);
  const x = Math.cos(lat1) * Math.sin(lat2) - Math.sin(lat1) * Math.cos(lat2) * Math.cos(dLon);
  return (((Math.atan2(y, x) * 180) / Math.PI) + 360) % 360;
}

function localEnuKm(lat, lon, altM = 0, origin = null) {
  const user = origin || state.data?.settings?.user;
  if (!user || lat === null || lon === null) return null;
  const meanLat = ((Number(lat) + Number(user.lat)) / 2) * Math.PI / 180;
  const east = (Number(lon) - Number(user.lon)) * 111.32 * Math.cos(meanLat);
  const north = (Number(lat) - Number(user.lat)) * 111.32;
  const up = (Number(altM || 0) - Number(user.alt_m || 0)) / 1000;
  return { east, north, up };
}

function aircraftAltM(ac) {
  const altFt = Number(ac?.altitude);
  return Number.isFinite(altFt) ? altFt * 0.3048 : 0;
}

function glideslopeFromRunway(runway, end, activeItem = null) {
  const lengthNm = Number(state.web?.ils_length_nm || state.data?.settings?.web?.ils_length_nm || 10);
  const lengthKm = (Number.isFinite(lengthNm) ? lengthNm : 10) * 1.852;
  let startLat = null;
  let startLon = null;
  let bearing = null;
  if (end === runway.le_ident && runway.le_ident) {
    startLat = runway.le_lat;
    startLon = runway.le_lon;
    bearing = calculateBearing(runway.he_lat, runway.he_lon, runway.le_lat, runway.le_lon);
  } else if (end === runway.he_ident && runway.he_ident) {
    startLat = runway.he_lat;
    startLon = runway.he_lon;
    bearing = calculateBearing(runway.le_lat, runway.le_lon, runway.he_lat, runway.he_lon);
  }
  if (startLat === null || startLon === null || bearing === null) return null;
  const endPoint = destinationPoint(startLat, startLon, bearing, lengthKm);
  if (!endPoint) return null;
  return {
    airport: runway.airport,
    runway_index: runway.runway_index,
    runway_end_ident: end,
    start_lat: startLat,
    start_lon: startLon,
    end_lat: endPoint.lat,
    end_lon: endPoint.lon,
    bearing_deg: bearing,
    length_km: lengthKm,
    ...(activeItem || {}),
  };
}

function applyOptimisticGlideslopes(activeItems, runway = null, end = null, adding = false) {
  state.web = { ...(state.web || {}), active_glideslopes: activeItems };
  if (state.data?.settings?.web) {
    state.data.settings.web = { ...state.data.settings.web, active_glideslopes: activeItems };
  }
  if (state.data?.settings) state.data.settings.show_glideslope = true;
  if (!state.data) return;
  const current = state.data.glideslopes || [];
  const keyFor = (item) => `${item.airport}:${item.runway_index}:${item.end || item.runway_end_ident}`;
  const activeKeys = new Set(activeItems.map(keyFor));
  let nextGlideslopes = current.filter((item) => activeKeys.has(keyFor(item)));
  if (adding && runway && end) {
    const optimistic = glideslopeFromRunway(runway, end, activeItems.find((item) => keyFor(item) === `${runway.airport}:${runway.runway_index}:${end}`));
    if (optimistic && !nextGlideslopes.some((item) => keyFor(item) === keyFor(optimistic))) {
      nextGlideslopes = [...nextGlideslopes, optimistic];
    }
  }
  state.data.glideslopes = nextGlideslopes;
  state.glideslopeOverride = { activeItems: copyGlideslopeItems(activeItems), glideslopes: [...nextGlideslopes] };
}

async function toggleGlideslope(runway, end) {
  const active = [...activeGlideslopeItems()];
  const key = `${runway.airport}:${runway.runway_index}:${end}`;
  const next = active.filter((item) => `${item.airport}:${item.runway_index}:${item.end}` !== key);
  const adding = next.length === active.length;
  if (next.length === active.length) {
    next.push({ airport: runway.airport, runway_index: runway.runway_index, end });
  }
  const previousWeb = state.web ? { ...state.web, active_glideslopes: active } : null;
  const previousGlideslopes = state.data?.glideslopes ? [...state.data.glideslopes] : [];
  const previousOverride = state.glideslopeOverride;
  applyOptimisticGlideslopes(next, runway, end, adding);
  draw();
  const res = await fetch("/api/config", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ show_glideslope: true, web: { active_glideslopes: next } }),
  });
  const payload = await res.json();
  if (!payload.ok) {
    if (previousWeb) state.web = previousWeb;
    if (state.data) state.data.glideslopes = previousGlideslopes;
    state.glideslopeOverride = previousOverride;
    draw();
    throw new Error(payload.error || "Could not update ILS");
  }
  state.web = payload.web;
  if (state.data?.settings?.web) state.data.settings.web = payload.web;
  applyOptimisticGlideslopes(next, runway, end, adding);
  draw();
  requestFullStateFetch(120);
}

function showRunwayOptions(runway) {
  const ends = [runway.le_ident, runway.he_ident].filter(Boolean);
  if (!ends.length) return false;
  const box = document.createElement("div");
  box.className = "runway-popover";
  box.innerHTML = `<strong>${runway.airport} ${runway.le_ident || ""}/${runway.he_ident || ""}</strong>`;
  ends.forEach((end) => {
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = `Toggle ${end} ILS`;
    button.addEventListener("click", () => {
      box.remove();
      toggleGlideslope(runway, end).catch(console.error);
    });
    box.appendChild(button);
  });
  const close = document.createElement("button");
  close.type = "button";
  close.textContent = "Close";
  close.addEventListener("click", () => box.remove());
  box.appendChild(close);
  document.body.appendChild(box);
  return true;
}

function drawTransits() {
  const pal = palette();
  (state.data?.transits || []).forEach((tr) => {
    const base = tr.body === "sun" ? (pal.sun || "#fb923c") : (pal.moon || "#93c5fd");
    const fill = colorWithAlpha(base, 0.20);
    const stroke = colorWithAlpha(base, 0.70);
    const slices = Array.isArray(tr.slices) ? tr.slices : [];
    if (slices.length > 1) {
      ctx.fillStyle = fill;
      ctx.strokeStyle = stroke;
      ctx.lineWidth = 1;
      for (let i = 1; i < slices.length; i += 1) {
        const prev = slices[i - 1];
        const curr = slices[i];
        const p1 = project(prev.left?.[0], prev.left?.[1]);
        const p2 = project(curr.left?.[0], curr.left?.[1]);
        const p3 = project(curr.right?.[0], curr.right?.[1]);
        const p4 = project(prev.right?.[0], prev.right?.[1]);
        if (![p1, p2, p3, p4].every(Boolean)) continue;
        ctx.beginPath();
        ctx.moveTo(p1.x, p1.y);
        ctx.lineTo(p2.x, p2.y);
        ctx.lineTo(p3.x, p3.y);
        ctx.lineTo(p4.x, p4.y);
        ctx.closePath();
        ctx.fill();
        ctx.stroke();
      }
    } else {
      const poly = (tr.polygon || []).map((pt) => project(pt[0], pt[1])).filter(Boolean);
      if (poly.length > 2) {
        ctx.fillStyle = fill;
        ctx.strokeStyle = stroke;
        ctx.beginPath();
        ctx.moveTo(poly[0].x, poly[0].y);
        poly.slice(1).forEach((p) => ctx.lineTo(p.x, p.y));
        ctx.closePath();
        ctx.fill();
        ctx.stroke();
      }
    }
    const color = colorWithAlpha(base, 0.95);
    drawGroundPolyline((tr.centerline || []).map((pt) => ({ lat: pt[0], lon: pt[1] })), color, 1.5);
  });
}

function colorWithAlpha(color, alpha) {
  if (String(color).startsWith("#") && color.length === 7) {
    const r = parseInt(color.slice(1, 3), 16);
    const g = parseInt(color.slice(3, 5), 16);
    const b = parseInt(color.slice(5, 7), 16);
    return `rgba(${r},${g},${b},${alpha})`;
  }
  return color;
}

function drawEvents() {
  const pal = palette();
  if (!state.data?.settings?.show_events) return;
  const acMap = state.viewMode === "3d" ? aircraftByIcao() : null;
  (state.data?.events || []).forEach((ev) => {
    if (ev.lat === null || ev.lon === null) return;
    const p = projectEventPoint(ev, acMap);
    if (!p) return;
    ctx.strokeStyle = eventColor(ev, pal);
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(p.x - 6, p.y - 6);
    ctx.lineTo(p.x + 6, p.y + 6);
    ctx.moveTo(p.x + 6, p.y - 6);
    ctx.lineTo(p.x - 6, p.y + 6);
    ctx.stroke();
  });
}

function aircraftByIcao() {
  const map = new Map();
  activeDisplayAircraft().forEach((ac) => {
    if (ac.icao) map.set(ac.icao, ac);
  });
  return map;
}

function eventColor(ev, pal = palette()) {
  return ev.type === "AC-Sun" ? (pal.sun || "#fb923c") : ev.type === "AC-Moon" ? (pal.moon || "#93c5fd") : (pal.acac || pal.warning || "#facc15");
}

function drawEventAircraftLinks() {
  if (!state.data?.settings?.show_events) return;
  const showLinks = Boolean(state.data?.settings?.web?.show_event_aircraft_links);
  const acMap = aircraftByIcao();
  ctx.save();
  ctx.lineWidth = 1.1;
  (state.data?.events || []).forEach((ev) => {
    if (ev.lat === null || ev.lon === null) return;
    const eventPoint = projectEventPoint(ev, acMap);
    if (!eventPoint) return;
    const targets = (ev.icaos || [])
      .map((icao) => acMap.get(icao))
      .filter((ac) => isAircraftDrawable(ac))
      .slice(0, ev.type === "AC-AC" ? 2 : 1);
    if (!targets.length) return;
    const color = eventColor(ev);
    ctx.strokeStyle = color;
    ctx.fillStyle = color;
    ctx.setLineDash([4, 5]);
    targets.forEach((ac) => {
      const acPoint = state.viewMode === "3d" ? projectWithAltitude(ac.lat, ac.lon, aircraftAltM(ac)) : project(ac.lat, ac.lon);
      if (!acPoint) return;
      if (showLinks) {
        ctx.globalAlpha = 0.72;
        ctx.beginPath();
        ctx.moveTo(eventPoint.x, eventPoint.y);
        ctx.lineTo(acPoint.x, acPoint.y);
        ctx.stroke();
      }
      ctx.setLineDash([]);
      ctx.globalAlpha = 0.95;
      ctx.beginPath();
      ctx.arc(acPoint.x, acPoint.y, ev.type === "AC-AC" ? 11 : 13, 0, Math.PI * 2);
      ctx.stroke();
      ctx.setLineDash([4, 5]);
    });
  });
  ctx.restore();
  ctx.setLineDash([]);
}

function wrapAzimuthDelta(az, centerAz) {
  let delta = az - centerAz;
  if (delta > 180) delta -= 360;
  if (delta < -180) delta += 360;
  return delta;
}

function circlePath(x, y, r) {
  ctx.beginPath();
  ctx.arc(x, y, r, 0, Math.PI * 2);
}

function drawMoonDisc(x, y, radius, phase) {
  const angle = Number(phase?.phase_angle_deg);
  if (!Number.isFinite(angle)) {
    ctx.fillStyle = "rgba(220, 226, 235, 0.9)";
    circlePath(x, y, radius);
    ctx.fill();
    return;
  }
  const phaseRad = ((angle % 360) * Math.PI) / 180;
  const sunX = Math.sin(phaseRad);
  const sunZ = -Math.cos(phaseRad);
  const step = Math.max(0.45, radius / 72);

  const litIntervals = (xn) => {
    const zMax = Math.sqrt(Math.max(0, 1 - xn * xn));
    if (zMax <= 0) return [];
    if (Math.abs(sunZ) < 1e-6) {
      return sunX * xn > 0 ? [[-zMax, zMax]] : [];
    }
    const threshold = -(sunX * xn) / sunZ;
    if (sunZ > 0) {
      if (threshold <= 0) return [[-zMax, zMax]];
      if (threshold >= zMax) return [];
      const yEdge = Math.sqrt(Math.max(0, zMax * zMax - threshold * threshold));
      return [[-yEdge, yEdge]];
    }
    if (threshold <= 0) return [];
    if (threshold >= zMax) return [[-zMax, zMax]];
    const yEdge = Math.sqrt(Math.max(0, zMax * zMax - threshold * threshold));
    return [[-zMax, -yEdge], [yEdge, zMax]];
  };

  ctx.save();
  circlePath(x, y, radius);
  ctx.clip();
  ctx.fillStyle = "rgba(35, 42, 54, 0.95)";
  ctx.fillRect(x - radius - 1, y - radius - 1, radius * 2 + 2, radius * 2 + 2);

  ctx.fillStyle = "rgba(225, 231, 238, 0.94)";
  for (let px = -radius; px <= radius; px += step) {
    const xn = Math.max(-1, Math.min(1, (px + step * 0.5) / radius));
    for (const [y1, y2] of litIntervals(xn)) {
      ctx.fillRect(x + px, y + y1 * radius, step + 0.35, Math.max(0.2, (y2 - y1) * radius));
    }
  }

  if (Math.abs(sunX) > 1e-5 && Math.abs(sunZ) > 0.025) {
    const termSign = -Math.sign(sunX * sunZ);
    const termWidth = Math.abs(sunZ);
    ctx.strokeStyle = "rgba(255,255,255,0.18)";
    ctx.lineWidth = 0.8;
    ctx.beginPath();
    for (let i = 0; i <= 48; i += 1) {
      const yn = -1 + (i / 48) * 2;
      const xn = termSign * termWidth * Math.sqrt(Math.max(0, 1 - yn * yn));
      const px = x + xn * radius;
      const py = y + yn * radius;
      if (i === 0) ctx.moveTo(px, py);
      else ctx.lineTo(px, py);
    }
    ctx.stroke();
  }
  ctx.restore();
  ctx.strokeStyle = "rgba(255,255,255,0.42)";
  ctx.lineWidth = 1;
  circlePath(x, y, radius);
  ctx.stroke();
}

function povBoxCandidates(anchor, size, index, rect) {
  const margin = 8;
  const step = 18 * (index % 3);
  return [
    { x: anchor.x + 54, y: anchor.y - size * 0.52 + step },
    { x: anchor.x - size - 24, y: anchor.y - size * 0.52 + step },
    { x: anchor.x + 28, y: anchor.y + 28 + step },
    { x: anchor.x - size - 20, y: anchor.y + 28 + step },
    { x: rect.width - size - margin, y: margin + index * 20 },
    { x: margin, y: margin + index * 20 },
    { x: rect.width - size - margin, y: rect.height - size - margin - index * 16 },
    { x: margin, y: rect.height - size - margin - index * 16 },
  ].map((box) => ({
    x: Math.max(margin, Math.min(rect.width - size - margin, box.x)),
    y: Math.max(margin, Math.min(rect.height - size - margin, box.y)),
    w: size,
    h: size,
  }));
}

function intersectsBox(box, other) {
  return box.x < other.x + other.w && box.x + box.w > other.x && box.y < other.y + other.h && box.y + box.h > other.y;
}

function pointInBox(point, box) {
  return point.x >= box.x && point.x <= box.x + box.w && point.y >= box.y && point.y <= box.y + box.h;
}

function ccw(a, b, c) {
  return (c.y - a.y) * (b.x - a.x) > (b.y - a.y) * (c.x - a.x);
}

function segmentsIntersect(a, b, c, d) {
  return ccw(a, c, d) !== ccw(b, c, d) && ccw(a, b, c) !== ccw(a, b, d);
}

function segmentIntersectsBox(a, b, box) {
  if (pointInBox(a, box) || pointInBox(b, box)) return true;
  const corners = [
    { x: box.x, y: box.y },
    { x: box.x + box.w, y: box.y },
    { x: box.x + box.w, y: box.y + box.h },
    { x: box.x, y: box.y + box.h },
  ];
  return corners.some((corner, idx) => segmentsIntersect(a, b, corner, corners[(idx + 1) % corners.length]));
}

function eventAircraftSegments(ev, anchor, acMap) {
  return (ev.icaos || [])
    .map((icao) => acMap.get(icao))
    .filter((ac) => isAircraftDrawable(ac))
    .slice(0, ev.type === "AC-AC" ? 2 : 1)
    .map((ac) => {
      const point = project(ac.lat, ac.lon);
      return point ? { a: anchor, b: point } : null;
    })
    .filter(Boolean);
}

function choosePovBox(ev, anchor, size, index, occupied, rect, avoidSegments = []) {
  const key = `${ev.type}:${(ev.icaos || []).join("-")}:${ev.time || index}`;
  const prior = state.povPlacements.get(key);
  const candidates = povBoxCandidates(anchor, size, index, rect);
  if (prior) candidates.unshift(prior);
  let best = candidates[0];
  let bestScore = Infinity;
  for (const candidate of candidates) {
    const overlaps = occupied.filter((box) => intersectsBox(candidate, box)).length;
    const lineHits = avoidSegments.filter((segment) => segmentIntersectsBox(segment.a, segment.b, candidate)).length;
    const centerX = candidate.x + candidate.w / 2;
    const centerY = candidate.y + candidate.h / 2;
    const linePenalty = Math.hypot(centerX - anchor.x, centerY - anchor.y) / 120;
    const score = overlaps * 1000 + lineHits * 180 + linePenalty;
    if (score < bestScore) {
      best = candidate;
      bestScore = score;
      if (overlaps === 0 && lineHits === 0) break;
    }
  }
  state.povPlacements.set(key, best);
  return best;
}

function drawPovBox(ev, anchor, index = 0, occupied = [], avoidSegments = []) {
  const pov = ev.pov || {};
  if (!pov.valid) return;
  const rect = canvas.getBoundingClientRect();
  const pal = palette();
  const size = Math.min(170, Math.max(128, Math.min(rect.width, rect.height) * 0.22));
  const half = size / 2;
  const box = choosePovBox(ev, anchor, size, index, occupied, rect, avoidSegments);
  const x = box.x;
  const y = box.y;
  occupied.push(box);

  let centerAz = 0;
  let centerEl = 0;
  let fovDeg = 2;
  if (ev.type === "AC-AC" && pov.ac1 && pov.ac2) {
    centerAz = (Number(pov.ac1.az) + Number(pov.ac2.az)) / 2;
    centerEl = (Number(pov.ac1.el) + Number(pov.ac2.el)) / 2;
    const azDiff = Math.abs(wrapAzimuthDelta(Number(pov.ac1.az), Number(pov.ac2.az))) * Math.cos((centerEl * Math.PI) / 180);
    const elDiff = Math.abs(Number(pov.ac1.el) - Number(pov.ac2.el));
    fovDeg = Math.max(2, Math.max(azDiff, elDiff) * 1.5);
  } else if (ev.type === "AC-Sun" || ev.type === "AC-Moon") {
    centerAz = Number(pov.body_az);
    centerEl = Number(pov.body_el);
    fovDeg = 1.5;
  } else {
    return;
  }

  const scale = size / Math.max(0.1, fovDeg);
  const projectPov = (az, el) => {
    const dx = wrapAzimuthDelta(Number(az), centerAz) * Math.cos((centerEl * Math.PI) / 180);
    const dy = Number(el) - centerEl;
    return { x: x + half + dx * scale, y: y + half - dy * scale };
  };
  const drawPovLabel = (text, lx, ly) => {
    if (!text) return;
    const margin = 5;
    ctx.save();
    ctx.font = "10px ui-monospace, monospace";
    const labelWidth = Math.min(size - margin * 2, ctx.measureText(text).width);
    const labelHeight = 12;
    const px = Math.max(x + margin, Math.min(x + size - margin - labelWidth, lx));
    const py = Math.max(y + margin, Math.min(y + size - margin - labelHeight, ly));
    ctx.fillStyle = pal.text;
    ctx.fillText(text, px, py + 10, labelWidth);
    ctx.restore();
  };

  ctx.save();
  ctx.fillStyle = "rgba(3, 7, 18, 0.86)";
  ctx.strokeStyle = ev.type === "AC-Sun" ? "#fb923c" : ev.type === "AC-Moon" ? "#d1d5db" : pal.warning;
  ctx.lineWidth = 1.2;
  ctx.fillRect(x, y, size, size);
  ctx.strokeRect(x, y, size, size);
  ctx.save();
  ctx.beginPath();
  ctx.rect(x + 1, y + 1, size - 2, size - 2);
  ctx.clip();
  ctx.strokeStyle = "rgba(255,255,255,0.28)";
  ctx.beginPath();
  ctx.moveTo(x + half - 8, y + half);
  ctx.lineTo(x + half + 8, y + half);
  ctx.moveTo(x + half, y + half - 8);
  ctx.lineTo(x + half, y + half + 8);
  ctx.stroke();

  if (ev.type === "AC-Sun" || ev.type === "AC-Moon") {
    const body = projectPov(pov.body_az, pov.body_el);
    const bodyRadiusDeg = Number(pov.body_angular_diameter_deg || (ev.type === "AC-Sun" ? 0.53 : 0.5)) / 2;
    const bodyRadiusPx = Math.max(5, bodyRadiusDeg * scale);
    if (ev.type === "AC-Moon") {
      drawMoonDisc(body.x, body.y, bodyRadiusPx, pov.moon_phase);
    } else {
      ctx.fillStyle = "rgba(255, 230, 90, 0.92)";
      circlePath(body.x, body.y, bodyRadiusPx);
      ctx.fill();
    }
    const ac = projectPov(pov.ac_az, pov.ac_el);
    const vec = projectPov(pov.ac_az_vec, pov.ac_el_vec);
    ctx.strokeStyle = "#2f80ff";
    ctx.beginPath();
    ctx.moveTo(ac.x, ac.y);
    ctx.lineTo(vec.x, vec.y);
    ctx.stroke();
    ctx.fillStyle = pal.aircraft;
    ctx.fillRect(ac.x - 3, ac.y - 3, 6, 6);
  } else {
    const ac1 = projectPov(pov.ac1.az, pov.ac1.el);
    const v1 = projectPov(pov.ac1.az_vec, pov.ac1.el_vec);
    const ac2 = projectPov(pov.ac2.az, pov.ac2.el);
    const v2 = projectPov(pov.ac2.az_vec, pov.ac2.el_vec);
    ctx.strokeStyle = "#22d3ee";
    ctx.beginPath();
    ctx.moveTo(ac1.x, ac1.y);
    ctx.lineTo(ac1.x + (v1.x - ac1.x) * 5, ac1.y + (v1.y - ac1.y) * 5);
    ctx.stroke();
    ctx.strokeStyle = "#ff4b4b";
    ctx.beginPath();
    ctx.moveTo(ac2.x, ac2.y);
    ctx.lineTo(ac2.x + (v2.x - ac2.x) * 5, ac2.y + (v2.y - ac2.y) * 5);
    ctx.stroke();
    ctx.strokeStyle = "rgba(255,255,255,0.36)";
    ctx.beginPath();
    ctx.moveTo(ac1.x, ac1.y);
    ctx.lineTo(ac2.x, ac2.y);
    ctx.stroke();
    ctx.fillStyle = "#22d3ee";
    ctx.beginPath();
    ctx.arc(ac1.x, ac1.y, 3, 0, Math.PI * 2);
    ctx.fill();
    ctx.fillStyle = "#ff4b4b";
    ctx.beginPath();
    ctx.arc(ac2.x, ac2.y, 3, 0, Math.PI * 2);
    ctx.fill();
    drawPovLabel(formatDistanceKm(ev.min_dist_km, 2), x + half + 10, y + half - 20);
  }
  ctx.restore();

  ctx.strokeStyle = ev.type === "AC-Sun" ? "#fb923c" : ev.type === "AC-Moon" ? "#d1d5db" : pal.warning;
  ctx.lineWidth = 1.2;
  ctx.strokeRect(x, y, size, size);
  ctx.fillStyle = pal.text;
  ctx.font = "11px ui-monospace, monospace";
  ctx.fillText(`POV ${fmtEtaForTime(ev.time, ev.eta_sec)}`, x + 6, y + 14);
  ctx.fillStyle = pal.dim;
  const nearestDistance = ev.type === "AC-AC"
    ? ev.min_dist_km
    : ev.event_slant_distance_km ?? ev.event_distance_km;
  ctx.fillText(`FOV ${fovDeg.toFixed(1)} deg`, x + 6, y + size - 22, size - 12);
  const distanceLabel = ev.type === "AC-AC" ? "Sep" : "AC";
  const bottomText = ev.type === "AC-AC"
    ? `Min ${fmtNum(ev.angle, 2, "deg")}`
    : `Min ${fmtNum(ev.angle, 2, "deg")} ${distanceLabel} ${formatDistanceKm(nearestDistance, 2)}`;
  ctx.fillText(bottomText, x + 6, y + size - 8, size - 12);
  ctx.restore();
}

function drawEventPovPreview() {
  const events = (state.data?.events || []).filter((ev) => ev.pov?.valid && ev.lat !== null && ev.lon !== null);
  if (!events.length) return;
  const occupied = [];
  const acMap = aircraftByIcao();
  const visibleKeys = new Set();
  const selectedEvents = [];
  const otherEvents = [];
  events.forEach((ev) => {
    if (state.selected && (ev.icaos || []).includes(state.selected)) selectedEvents.push(ev);
    else otherEvents.push(ev);
  });
  [...selectedEvents, ...otherEvents].slice(0, 8).forEach((ev, index) => {
    const anchor = project(ev.lat, ev.lon);
    if (anchor) {
      visibleKeys.add(`${ev.type}:${(ev.icaos || []).join("-")}:${ev.time || index}`);
      drawPovBox(ev, anchor, index, occupied, eventAircraftSegments(ev, anchor, acMap));
    }
  });
  for (const key of state.povPlacements.keys()) {
    if (!visibleKeys.has(key)) state.povPlacements.delete(key);
  }
}

function intersectsAnyLabel(box, boxes) {
  return boxes.some((other) => (
    box.x < other.x + other.w &&
    box.x + box.w > other.x &&
    box.y < other.y + other.h &&
    box.y + box.h > other.y
  ));
}

function labelOffset(candidate, width) {
  const offsets = {
    rightTop: { x: 10, y: -8 },
    rightBottom: { x: 10, y: 14 },
    leftTop: { x: -width - 10, y: -8 },
    leftBottom: { x: -width - 10, y: 14 },
    rightMiddle: { x: 14, y: -2 },
    leftMiddle: { x: -width - 14, y: -2 },
  };
  return offsets[candidate] || offsets.rightTop;
}

function labelBoxForCandidate(anchor, width, height, candidate, metrics = aircraftLabelMetrics()) {
  const offset = labelOffset(candidate, width);
  return {
    x: anchor.x + offset.x - 2,
    y: anchor.y + offset.y - metrics.lineHeight,
    w: width + metrics.boxPad,
    h: height + metrics.boxPad,
    textX: anchor.x + offset.x,
    textY: anchor.y + offset.y,
    candidate,
  };
}

function placeLabel(anchor, width, height, boxes, key, metrics = aircraftLabelMetrics()) {
  const candidates = ["rightTop", "rightBottom", "leftTop", "leftBottom", "rightMiddle", "leftMiddle"];
  const prior = key ? state.labelPlacements.get(key) : null;
  const ordered = prior ? [prior, ...candidates.filter((candidate) => candidate !== prior)] : candidates;
  for (const candidate of ordered) {
    const box = labelBoxForCandidate(anchor, width, height, candidate, metrics);
    if (!intersectsAnyLabel(box, boxes)) {
      if (key) state.labelPlacements.set(key, candidate);
      return box;
    }
  }
  const fallback = prior || candidates[0];
  if (key) state.labelPlacements.set(key, fallback);
  return labelBoxForCandidate(anchor, width, height, fallback, metrics);
}

function drawAircraft(options = {}) {
  const aircraft = activeDisplayAircraft();
  const units = unitConfig();
  const interactive = Boolean(options.interactive);
  const labelBoxes = [];
  const visibleLabelKeys = new Set();
  const orderedAircraft = [...aircraft].sort((a, b) => {
    const priority = (ac) => (state.selected === ac.icao ? 0 : ac.conflict ? 1 : ac.has_event ? 2 : 3);
    return priority(a) - priority(b);
  });
  if (!interactive && state.data.settings.show_history) {
    orderedAircraft.forEach((ac) => {
      if (!isAircraftTrackDrawable(ac)) return;
      const selected = state.selected === ac.icao;
      const pal = palette();
      const color = ac.conflict ? pal.alert : ac.has_event ? pal.warning : selected ? pal.selected : pal.aircraft;
      drawAltitudePath(ac.history || [], color);
    });
  }
  if (!interactive && state.data.settings.show_velocity_vector) {
    orderedAircraft.forEach((ac) => {
      if (!isAircraftTrackDrawable(ac)) return;
      const selected = state.selected === ac.icao;
      drawPolyline(ac.path || [], "#2f80ff", selected ? 1.4 : 1.0, ac.altitude);
    });
  }
  orderedAircraft.forEach((ac) => {
    if (!isAircraftDrawable(ac)) return;
    const groundPoint = project(ac.lat, ac.lon);
    const airPoint = state.viewMode === "3d" ? projectWithAltitude(ac.lat, ac.lon, aircraftAltM(ac)) : groundPoint;
    const p = airPoint;
    if (!p) return;
    const selected = state.selected === ac.icao;
    const pal = palette();
    const emergency = isEmergencySquawk(ac);
    const color = emergency || ac.conflict ? pal.alert : ac.has_event ? pal.warning : selected ? pal.selected : pal.aircraft;

    if (state.viewMode === "3d" && groundPoint) {
      ctx.strokeStyle = colorWithAlpha(color, 0.55);
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(groundPoint.x, groundPoint.y);
      ctx.lineTo(p.x, p.y);
      ctx.stroke();
      ctx.fillStyle = colorWithAlpha(color, 0.20);
      ctx.beginPath();
      ctx.arc(groundPoint.x, groundPoint.y, selected ? 4 : 3, 0, Math.PI * 2);
      ctx.fill();
    }

    ctx.fillStyle = color;
    ctx.fillRect(p.x - 4, p.y - 4, 8, 8);

    if (selected || ac.has_event || ac.conflict || emergency) {
      ctx.strokeStyle = emergency || ac.has_event || ac.conflict ? pal.alert : pal.text;
      ctx.lineWidth = emergency || ac.has_event || ac.conflict ? 2 : 1.5;
      ctx.beginPath();
      ctx.arc(p.x, p.y, 12, 0, Math.PI * 2);
      ctx.stroke();
    }

    const labelParts = buildAircraftLabelLines(ac, units.labelFields, units.labelLines);
    const labelColor = emergency ? pal.alert : state.data.settings.web?.aircraft_label_color === "green" ? "#4ade80" : pal.text;
    const labelMetrics = aircraftLabelMetrics(units.labelSize);
    ctx.font = labelMetrics.font;
    const labelWidth = Math.max(...labelParts.map((line) => ctx.measureText(line).width), 0);
    const labelKey = ac.icao || `${ac.lat},${ac.lon}`;
    visibleLabelKeys.add(labelKey);
    const labelBox = placeLabel(p, labelWidth, labelParts.length * labelMetrics.lineHeight, labelBoxes, labelKey, labelMetrics);
    labelBoxes.push(labelBox);
    ctx.fillStyle = labelColor;
    labelParts.forEach((line, index) => {
      ctx.fillText(line, labelBox.textX, labelBox.textY + index * labelMetrics.lineHeight);
    });
  });
  for (const key of state.labelPlacements.keys()) {
    if (!visibleLabelKeys.has(key)) state.labelPlacements.delete(key);
  }
}

function draw(options = {}) {
  if (canvasBackingStoreMismatch()) {
    resizeCanvas();
    return;
  }
  const interactive = Boolean(options.interactive);
  state.drawingInteractive = interactive;
  if (state.viewMode === "ar") state.viewMode = "2d";
  drawBackground();
  if (!state.data) {
    state.drawingInteractive = false;
    return;
  }
  if (interactive) {
    if (shouldDrawLowDetailGeodata(true)) drawGeodataLowDetail();
    else drawGeodata();
    drawTransits();
    drawEvents();
    drawEventAircraftLinks();
    drawAircraft();
    drawEventPovPreview();
    draw3dNorthArrow();
    drawPanFeedback();
    state.drawingInteractive = false;
    return;
  }
  if (shouldDrawLowDetailGeodata(false)) drawGeodataLowDetail();
  else drawGeodata();
  drawTransits();
  drawEvents();
  drawEventAircraftLinks();
  drawAircraft();
  drawEventPovPreview();
  draw3dNorthArrow();
  state.drawingInteractive = false;
}

function viewCtx() {
  return els.viewCanvas?.getContext("2d");
}

function resizeViewCanvas() {
  if (!els.viewCanvas || els.viewOverlay?.hidden) return;
  const rect = els.viewCanvas.getBoundingClientRect();
  const ratio = window.devicePixelRatio || 1;
  els.viewCanvas.width = Math.max(1, Math.floor(rect.width * ratio));
  els.viewCanvas.height = Math.max(1, Math.floor(rect.height * ratio));
  const vctx = viewCtx();
  if (vctx) vctx.setTransform(ratio, 0, 0, ratio, 0, 0);
  drawActiveView();
}

async function openView(mode) {
  if (!els.viewOverlay) return;
  state.viewMode = mode;
  els.viewOverlay.hidden = false;
  els.viewTitle.textContent = mode === "ar" ? "Observer Simulation" : "3D Traffic View";
  els.viewHint.textContent = mode === "ar" ? "Drag to pan, wheel to change FOV" : "Drag to rotate/tilt, wheel to zoom";
  resizeViewCanvas();
  drawActiveView();
}

function closeView() {
  state.viewMode = null;
  if (els.viewOverlay) els.viewOverlay.hidden = true;
}

function drawActiveView() {
  if (!state.viewMode || state.viewMode === "2d" || !els.viewCanvas || els.viewOverlay.hidden) return;
  if (state.viewMode === "ar") drawArView();
  else draw3dView();
}

function drawViewBackground(vctx, w, h) {
  const pal = palette();
  const grad = vctx.createLinearGradient(0, 0, 0, h);
  grad.addColorStop(0, pal.bgTop);
  grad.addColorStop(1, pal.bgBottom);
  vctx.fillStyle = grad;
  vctx.fillRect(0, 0, w, h);
  vctx.strokeStyle = pal.grid;
  vctx.lineWidth = 1;
  for (let x = 0; x <= w; x += 80) {
    vctx.beginPath();
    vctx.moveTo(x, 0);
    vctx.lineTo(x, h);
    vctx.stroke();
  }
  for (let y = 0; y <= h; y += 80) {
    vctx.beginPath();
    vctx.moveTo(0, y);
    vctx.lineTo(w, y);
    vctx.stroke();
  }
}

function draw3dView() {
  const vctx = viewCtx();
  if (!vctx || !state.data) return;
  const rect = els.viewCanvas.getBoundingClientRect();
  const w = rect.width;
  const h = rect.height;
  const pal = palette();
  drawViewBackground(vctx, w, h);
  const pitchDeg = clamp3dPitch(state.viewPitch ?? 55);
  const yaw = state.viewYaw * Math.PI / 180;
  const pitch = pitchDeg * Math.PI / 180;
  const effectiveZoom = clamp3dViewZoom(state.viewZoom || 1);
  const scale = Math.min(w, h) / Math.max(20, (state.rangeKm || 60) * 1.4) * effectiveZoom;
  const project3 = (east, north, up = 0) => {
    const x1 = east * Math.cos(yaw) - north * Math.sin(yaw);
    const y1 = east * Math.sin(yaw) + north * Math.cos(yaw);
    const y2 = y1 * Math.cos(pitch) - up * 8 * Math.sin(pitch);
    return { x: w / 2 + x1 * scale, y: h * 0.62 - y2 * scale };
  };
  vctx.strokeStyle = pal.dim;
  vctx.lineWidth = 1;
  for (let km = 10; km <= Math.min(120, state.rangeKm * 2); km += 10) {
    const a = project3(-km, 0, 0);
    const b = project3(km, 0, 0);
    const c = project3(0, -km, 0);
    const d = project3(0, km, 0);
    vctx.beginPath();
    vctx.moveTo(a.x, a.y);
    vctx.lineTo(b.x, b.y);
    vctx.moveTo(c.x, c.y);
    vctx.lineTo(d.x, d.y);
    vctx.stroke();
  }
  activeDisplayAircraft().forEach((ac) => {
    if (!isAircraftDrawable(ac)) return;
    const ground = localEnuKm(ac.lat, ac.lon, state.data.settings.user.alt_m);
    const air = localEnuKm(ac.lat, ac.lon, aircraftAltM(ac));
    if (!ground || !air) return;
    const pg = project3(ground.east, ground.north, 0);
    const pa = project3(air.east, air.north, air.up);
    const color = ac.conflict ? pal.alert : ac.has_event ? pal.warning : ac.icao === state.selected ? pal.selected : pal.aircraft;
    vctx.strokeStyle = colorWithAlpha(color, 0.50);
    vctx.lineWidth = 1;
    vctx.beginPath();
    vctx.moveTo(pg.x, pg.y);
    vctx.lineTo(pa.x, pa.y);
    vctx.stroke();
    vctx.fillStyle = colorWithAlpha(color, 0.20);
    vctx.beginPath();
    vctx.arc(pg.x, pg.y, 3, 0, Math.PI * 2);
    vctx.fill();
    vctx.fillStyle = color;
    vctx.beginPath();
    vctx.arc(pa.x, pa.y, ac.icao === state.selected ? 5 : 4, 0, Math.PI * 2);
    vctx.fill();
    vctx.font = "11px ui-monospace, monospace";
    vctx.fillText(`${ac.callsign || ac.icao} ${formatAltitudeFt(ac.altitude, 0)}`, pa.x + 6, pa.y - 5);
  });
  vctx.fillStyle = pal.text;
  vctx.font = "12px ui-monospace, monospace";
  vctx.fillText(`yaw ${Math.round(state.viewYaw)} pitch ${Math.round(state.viewPitch)} zoom ${state.viewZoom.toFixed(1)}`, 12, h - 14);
}

function drawArView() {
  const vctx = viewCtx();
  if (!vctx || !state.data) return;
  const rect = els.viewCanvas.getBoundingClientRect();
  const w = rect.width;
  const h = rect.height;
  const pal = palette();
  drawViewBackground(vctx, w, h);
  const fov = Math.max(8, Math.min(110, state.viewFov));
  const vFov = fov * h / Math.max(1, w);
  const projectSky = (az, el) => {
    const dx = wrapAzimuthDelta(Number(az), state.viewAz);
    const dy = Number(el) - state.viewEl;
    return { x: w / 2 + (dx / fov) * w, y: h / 2 - (dy / vFov) * h };
  };
  vctx.strokeStyle = pal.dim;
  vctx.lineWidth = 1;
  vctx.strokeRect(w * 0.1, h * 0.12, w * 0.8, h * 0.76);
  vctx.fillStyle = pal.dim;
  vctx.font = "11px ui-monospace, monospace";
  vctx.fillText(`FOV ${Math.round(fov)}deg  AZ ${Math.round(state.viewAz)}  EL ${Math.round(state.viewEl)}`, 12, 18);
  activeDisplayAircraft().forEach((ac) => {
    if (!isAircraftDrawable(ac)) return;
    const local = localEnuKm(ac.lat, ac.lon, aircraftAltM(ac));
    if (!local) return;
    const az = (Math.atan2(local.east, local.north) * 180 / Math.PI + 360) % 360;
    const dist = Math.max(0.01, Math.hypot(local.east, local.north));
    const el = Math.atan2(local.up, dist) * 180 / Math.PI;
    const p = projectSky(az, el);
    if (p.x < -30 || p.x > w + 30 || p.y < -30 || p.y > h + 30) return;
    const color = ac.conflict ? pal.alert : ac.has_event ? pal.warning : ac.icao === state.selected ? pal.selected : pal.aircraft;
    vctx.strokeStyle = color;
    vctx.lineWidth = 1.5;
    vctx.beginPath();
    vctx.arc(p.x, p.y, 5, 0, Math.PI * 2);
    vctx.stroke();
    vctx.fillStyle = color;
    vctx.font = "11px ui-monospace, monospace";
    vctx.fillText(`${ac.callsign || ac.icao} ${formatAltitudeFt(ac.altitude, 0)}`, p.x + 8, p.y - 5);
  });
}

function drawArMainView() {
  const rect = canvas.getBoundingClientRect();
  const w = rect.width;
  const h = rect.height;
  const pal = palette();
  drawViewBackground(ctx, w, h);
  if (!state.data) return;
  const fov = Math.max(8, Math.min(110, state.viewFov));
  const vFov = fov * h / Math.max(1, w);
  const projectSky = skyProjector(w, h, fov);

  ctx.save();
  ctx.strokeStyle = pal.dim;
  ctx.fillStyle = pal.dim;
  ctx.lineWidth = 1;
  const horizonPoint = projectSky(state.viewAz, 0);
  const horizon = visibleSkyPoint(horizonPoint, w, h, 240) ? horizonPoint.y : null;
  if (horizon !== null) {
    ctx.beginPath();
    ctx.moveTo(0, horizon);
    ctx.lineTo(w, horizon);
    ctx.stroke();
  }
  ctx.font = "11px ui-monospace, monospace";
  if (horizon !== null) ctx.fillText("HORIZON", 12, horizon - 5);
  ctx.strokeRect(w * 0.1, h * 0.12, w * 0.8, h * 0.76);
  ctx.fillText(`AR  FOV ${Math.round(fov)}deg  AZ ${Math.round(state.viewAz)}  EL ${Math.round(state.viewEl)}`, 12, 18);
  drawZenithGrid(ctx, projectSky, fov, vFov, pal);

  for (let azOffset = -Math.floor(fov / 2); azOffset <= Math.ceil(fov / 2); azOffset += 10) {
    const az = (state.viewAz + azOffset + 360) % 360;
    const top = projectSky(az, state.viewEl + vFov / 2);
    const bottom = projectSky(az, state.viewEl - vFov / 2);
    if (!visibleSkyPoint(top, w, h, 240) || !visibleSkyPoint(bottom, w, h, 240)) continue;
    ctx.strokeStyle = azOffset === 0 ? colorWithAlpha(pal.text, 0.36) : colorWithAlpha(pal.dim, 0.42);
    ctx.beginPath();
    ctx.moveTo(top.x, top.y);
    ctx.lineTo(bottom.x, bottom.y);
    ctx.stroke();
  }
  for (let el = Math.ceil((state.viewEl - vFov / 2) / 5) * 5; el <= state.viewEl + vFov / 2; el += 5) {
    const left = projectSky(state.viewAz - fov / 2, el);
    const right = projectSky(state.viewAz + fov / 2, el);
    if (!visibleSkyPoint(left, w, h, 240) || !visibleSkyPoint(right, w, h, 240)) continue;
    ctx.strokeStyle = el === 0 ? colorWithAlpha(pal.text, 0.38) : colorWithAlpha(pal.dim, 0.34);
    ctx.beginPath();
    ctx.moveTo(left.x, left.y);
    ctx.lineTo(right.x, right.y);
    ctx.stroke();
    ctx.fillText(`${el}deg`, 8, left.y - 2);
  }

  drawArCelestial(ctx, projectSky, pal);
  drawArAirports(ctx, projectSky, w, h, pal);
  drawArAircraft(ctx, projectSky, w, h, pal);
  ctx.restore();
}

function skyVectorFromAzEl(azDeg, elDeg) {
  const az = (Number(azDeg) * Math.PI) / 180;
  const el = (Number(elDeg) * Math.PI) / 180;
  return {
    x: Math.sin(az) * Math.cos(el),
    y: Math.cos(az) * Math.cos(el),
    z: Math.sin(el),
  };
}

function dot3(a, b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

function normalize3(v) {
  const mag = Math.hypot(v.x, v.y, v.z) || 1;
  return { x: v.x / mag, y: v.y / mag, z: v.z / mag };
}

function skyProjector(w, h, fovDeg) {
  const forward = normalize3(skyVectorFromAzEl(state.viewAz, state.viewEl));
  let right = normalize3({ x: forward.y, y: -forward.x, z: 0 });
  if (Math.hypot(right.x, right.y, right.z) < 0.001) right = { x: 1, y: 0, z: 0 };
  const up = normalize3({
    x: right.y * forward.z - right.z * forward.y,
    y: right.z * forward.x - right.x * forward.z,
    z: right.x * forward.y - right.y * forward.x,
  });
  const focal = (w / 2) / Math.tan((Math.max(8, Math.min(120, fovDeg)) * Math.PI / 180) / 2);
  return (az, el) => {
    const v = skyVectorFromAzEl(az, el);
    const z = dot3(v, forward);
    if (z <= 0.02) return { x: Number.NaN, y: Number.NaN, behind: true };
    return {
      x: w / 2 + (dot3(v, right) / z) * focal,
      y: h / 2 - (dot3(v, up) / z) * focal,
      behind: false,
    };
  };
}

function arPointForLatLonAlt(lat, lon, altM = 0) {
  const local = localEnuKm(lat, lon, altM);
  if (!local) return null;
  const az = (Math.atan2(local.east, local.north) * 180 / Math.PI + 360) % 360;
  const dist = Math.max(0.01, Math.hypot(local.east, local.north));
  const el = Math.atan2(local.up, dist) * 180 / Math.PI;
  return { az, el, dist };
}

function visibleSkyPoint(point, w = canvas.clientWidth, h = canvas.clientHeight, margin = 60) {
  return point && !point.behind
    && Number.isFinite(point.x) && Number.isFinite(point.y)
    && point.x >= -margin && point.x <= w + margin
    && point.y >= -margin && point.y <= h + margin;
}

function drawSkyPolyline(targetCtx, points, color, width = 1, fallbackAltitudeFt = null, projectSky = null) {
  const projector = projectSky || skyProjector(canvas.clientWidth, canvas.clientHeight, state.viewFov);
  const projected = points
    .map((pt) => {
      const sky = arPointForLatLonAlt(pt.lat, pt.lon, pointAltitudeM(pt, fallbackAltitudeFt));
      return sky ? projector(sky.az, sky.el) : null;
    })
    .filter((pt) => visibleSkyPoint(pt, canvas.clientWidth, canvas.clientHeight, 160));
  if (projected.length < 2) return;
  targetCtx.strokeStyle = color;
  targetCtx.lineWidth = width;
  targetCtx.beginPath();
  targetCtx.moveTo(projected[0].x, projected[0].y);
  projected.slice(1).forEach((pt) => targetCtx.lineTo(pt.x, pt.y));
  targetCtx.stroke();
}

function drawZenithGrid(targetCtx, projectSky, fov, vFov, pal) {
  targetCtx.save();
  targetCtx.setLineDash([3, 8]);
  targetCtx.strokeStyle = colorWithAlpha(pal.dim, 0.32);
  targetCtx.lineWidth = 1;
  for (let offset = -60; offset <= 60; offset += 20) {
    targetCtx.beginPath();
    let started = false;
    for (let el = Math.max(-10, state.viewEl - vFov / 2); el <= Math.min(90, state.viewEl + vFov / 2); el += 2) {
      const az = state.viewAz + offset * Math.cos((el * Math.PI) / 180);
      const p = projectSky(az, el);
      if (!visibleSkyPoint(p, canvas.clientWidth, canvas.clientHeight, 240)) {
        started = false;
        continue;
      }
      if (!started) {
        targetCtx.moveTo(p.x, p.y);
        started = true;
      } else {
        targetCtx.lineTo(p.x, p.y);
      }
    }
    targetCtx.stroke();
  }
  for (let el = 10; el <= 80; el += 10) {
    const left = projectSky(state.viewAz - fov / 2, el);
    const right = projectSky(state.viewAz + fov / 2, el);
    if (!visibleSkyPoint(left, canvas.clientWidth, canvas.clientHeight, 240)
      || !visibleSkyPoint(right, canvas.clientWidth, canvas.clientHeight, 240)) continue;
    targetCtx.beginPath();
    targetCtx.moveTo(left.x, left.y);
    targetCtx.lineTo(right.x, right.y);
    targetCtx.stroke();
  }
  targetCtx.setLineDash([]);
  const zenith = projectSky(state.viewAz, 90);
  if (visibleSkyPoint(zenith, canvas.clientWidth, canvas.clientHeight, 240)) {
    targetCtx.strokeStyle = colorWithAlpha(pal.text, 0.55);
    targetCtx.beginPath();
    targetCtx.moveTo(zenith.x - 5, zenith.y);
    targetCtx.lineTo(zenith.x + 5, zenith.y);
    targetCtx.moveTo(zenith.x, zenith.y - 5);
    targetCtx.lineTo(zenith.x, zenith.y + 5);
    targetCtx.stroke();
  }
  targetCtx.fillStyle = pal.dim;
  targetCtx.font = "10px ui-monospace, monospace";
  targetCtx.fillText("ZENITH RA/DEC GRID", 12, 34);
  targetCtx.restore();
}

function drawArCelestial(targetCtx, projectSky, pal) {
  const bodies = state.data?.celestial || {};
  [["sun", pal.sun || "#fb923c", 8], ["moon", pal.moon || "#d1d5db", 7]].forEach(([key, color, radius]) => {
    const body = bodies[key];
    if (!body || body.az === undefined || body.el === undefined) return;
    const p = projectSky(body.az, body.el);
    if (!visibleSkyPoint(p, canvas.clientWidth, canvas.clientHeight, 30)) return;
    targetCtx.strokeStyle = color;
    targetCtx.fillStyle = colorWithAlpha(color, 0.18);
    targetCtx.lineWidth = 1.5;
    targetCtx.beginPath();
    targetCtx.arc(p.x, p.y, radius, 0, Math.PI * 2);
    targetCtx.fill();
    targetCtx.stroke();
    targetCtx.fillStyle = color;
    targetCtx.fillText(key.toUpperCase(), p.x + radius + 4, p.y + 4);
  });
}

function drawArAirports(targetCtx, projectSky, w, h, pal) {
  const airports = state.data?.geodata?.airports || [];
  if (!airports.length) return;
  targetCtx.save();
  targetCtx.strokeStyle = pal.airport;
  targetCtx.fillStyle = pal.airport;
  targetCtx.font = "10px ui-monospace, monospace";
  airports.forEach((apt) => {
    const elevationM = Number.isFinite(Number(apt.elevation_m))
      ? Number(apt.elevation_m)
      : (Number.isFinite(Number(apt.elevation_ft)) ? Number(apt.elevation_ft) * 0.3048 : 0);
    const sky = arPointForLatLonAlt(apt.lat, apt.lon, elevationM);
    if (!sky || sky.dist > Math.max(8, state.rangeKm * 1.2)) return;
    const p = projectSky(sky.az, sky.el);
    if (!visibleSkyPoint(p, w, h, 50)) return;
    targetCtx.beginPath();
    targetCtx.moveTo(p.x - 4, p.y);
    targetCtx.lineTo(p.x + 4, p.y);
    targetCtx.moveTo(p.x, p.y - 4);
    targetCtx.lineTo(p.x, p.y + 4);
    targetCtx.stroke();
    if (sky.dist < 80) targetCtx.fillText(apt.ident || apt.name || "APT", p.x + 6, p.y - 5);
  });
  targetCtx.restore();
}

function drawArAircraft(targetCtx, projectSky, w, h, pal) {
  const aircraft = activeDisplayAircraft();
  const units = unitConfig();
  if (state.data?.settings?.show_history) {
    aircraft.forEach((ac) => {
      if (!isAircraftDrawable(ac)) return;
      const selected = ac.icao === state.selected;
      const color = isEmergencySquawk(ac) || ac.conflict ? pal.alert : ac.has_event ? pal.warning : selected ? pal.selected : pal.aircraft;
      drawSkyPolyline(targetCtx, ac.history || [], colorWithAlpha(color, 0.88), 1.1, ac.altitude, projectSky);
    });
  }
  if (state.data?.settings?.show_velocity_vector) {
    aircraft.forEach((ac) => {
      if (!isAircraftDrawable(ac)) return;
      drawSkyPolyline(targetCtx, ac.path || [], "#2f80ff", ac.icao === state.selected ? 1.5 : 1.0, ac.altitude, projectSky);
    });
  }
  activeDisplayAircraft().forEach((ac) => {
    if (!isAircraftDrawable(ac)) return;
    const sky = arPointForLatLonAlt(ac.lat, ac.lon, aircraftAltM(ac));
    if (!sky) return;
    const p = projectSky(sky.az, sky.el);
    if (!visibleSkyPoint(p, w, h, 50)) return;
    const selected = ac.icao === state.selected;
    const emergency = isEmergencySquawk(ac);
    const color = emergency || ac.conflict ? pal.alert : ac.has_event ? pal.warning : selected ? pal.selected : pal.aircraft;
    targetCtx.strokeStyle = color;
    targetCtx.fillStyle = color;
    targetCtx.lineWidth = selected ? 2 : 1.4;
    targetCtx.fillRect(p.x - 4, p.y - 4, 8, 8);
    if (selected || ac.has_event || ac.conflict || emergency) {
      targetCtx.beginPath();
      targetCtx.arc(p.x, p.y, 12, 0, Math.PI * 2);
      targetCtx.stroke();
    }
    const labelParts = buildAircraftLabelLines(ac, units.labelFields, units.labelLines);
    targetCtx.font = "11px ui-monospace, monospace";
    targetCtx.fillStyle = emergency ? pal.alert : color;
    labelParts.slice(0, 3).forEach((line, index) => {
      targetCtx.fillText(line, p.x + 9, p.y - 6 + index * 11);
    });
  });
}

function updateStatus() {
  const data = state.data;
  if (!data) return;
  const units = unitConfig();
  els.connBadge.textContent = data.settings.connected ? "Online" : "Offline";
  els.connBadge.classList.toggle("online", data.settings.connected);
  els.activeCount.textContent = data.counts.active_total;
  els.displayedCount.textContent = data.counts.displayed;
  els.eventCount.textContent = data.counts.events;
  els.scaleChip.textContent = `${formatDistanceKm(state.rangeKm, state.rangeKm < 10 ? 1 : 0)} range`;
  els.scaleChip.hidden = state.viewMode === "3d";

  const celestial = data.celestial;
  const rows = [
    ["Dump1090", `${data.settings.dump1090_host}:${data.settings.dump1090_port}`],
    ["Observer", `${fmtNum(data.settings.user.lat, 4)}, ${fmtNum(data.settings.user.lon, 4)}`],
    ["Altitude", formatAltitudeM(data.settings.user.alt_m, 0)],
    ["Conflict Angle", fmtNum(data.settings.conflict_angle_deg, 1, "deg")],
    ["Prediction", fmtNum(data.settings.prediction_horizon_sec, 0, "s")],
    ["Prediction Avg", fmtNum(data.settings.prediction_average_sec, 1, "s")],
  ];
  if (celestial) {
    rows.push(["Sun", `Az ${fmtNum(celestial.sun.az, 1)} El ${fmtNum(celestial.sun.el, 1)}`]);
    const moonPhase = celestial.moon?.phase;
    const moonText = moonPhase
      ? `Az ${fmtNum(celestial.moon.az, 1)} El ${fmtNum(celestial.moon.el, 1)} | ${moonPhase.name}, ${fmtNum(moonPhase.illumination_percent, 0)} lit`
      : `Az ${fmtNum(celestial.moon.az, 1)} El ${fmtNum(celestial.moon.el, 1)}`;
    rows.push(["Moon", moonText]);
  }
  els.statusList.innerHTML = rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("");
}

function updateSelected() {
  const ac = activeDisplayAircraft().find((item) => item.icao === state.selected);
  if (!ac) {
    els.selectedAircraft.className = "empty";
    els.selectedAircraft.textContent = "Click an aircraft on the map or table.";
    updateMapAircraftInfo(null);
    return;
  }
  const units = unitConfig();
  els.selectedAircraft.className = "selected-grid";
  const rows = [
    ["Callsign", ac.callsign || ac.icao],
    ["ICAO", ac.icao],
    ["Distance", formatDistanceKm(ac.distance_km, 1)],
    ["Altitude", `${formatAltitudeFt(ac.altitude, 0)}${verticalTrend(ac.vs)}`],
    ["Speed", formatSpeedKt(ac.speed, 0)],
    ["Track", formatTrackDeg(ac.track)],
    ["V/S", formatVerticalSpeedFpm(ac.vs)],
    ["Squawk", ac.squawk || "----"],
  ];
  els.selectedAircraft.innerHTML = rows.map(([k, v]) => `<div><span>${k}</span><strong>${v}</strong></div>`).join("");
  updateMapAircraftInfo(ac, rows);
}

function updateMapAircraftInfo(ac, rows = null) {
  if (!els.mapAircraftInfo) return;
  const hiddenPanel = document.body.classList.contains("panel-hidden");
  if (!hiddenPanel || !ac) {
    els.mapAircraftInfo.hidden = true;
    els.mapAircraftInfo.innerHTML = "";
    return;
  }
  const infoRows = rows || [
    ["Callsign", ac.callsign || ac.icao],
    ["ICAO", ac.icao],
    ["Distance", formatDistanceKm(ac.distance_km, 1)],
    ["Altitude", `${formatAltitudeFt(ac.altitude, 0)}${verticalTrend(ac.vs)}`],
    ["Speed", formatSpeedKt(ac.speed, 0)],
    ["Track", formatTrackDeg(ac.track)],
  ];
  els.mapAircraftInfo.hidden = false;
  els.mapAircraftInfo.innerHTML = `
    <strong>${ac.callsign || ac.icao}</strong>
    <dl>${infoRows.slice(1, 7).map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("")}</dl>
  `;
}

function updateEvents() {
  const events = state.data?.events || [];
  const eventDetail = (ev) => {
    const currentDistance = ev.current_dist_km ?? ev.ac_distance_km ?? ev.event_distance_km;
    const nearestDistance = ev.min_dist_km ?? ev.event_distance_km;
    return [
      `Dist ${formatDistanceKm(currentDistance, 1)}`,
      `Near ${formatDistanceKm(nearestDistance, 2)}`,
      `Now ${fmtNum(ev.current_angle, 2, "deg")}`,
      `Min ${fmtNum(ev.angle, 2, "deg")}`,
    ].join(" | ");
  };
  if (!events.length) {
    const historyEvents = state.data?.counts?.history_events || 0;
    els.eventsList.className = "list";
    els.eventsList.innerHTML = `<div class="event-row event-summary"><b>History</b><span>Completed events</span><span>${historyEvents}</span></div>`;
    return;
  }
  els.eventsList.className = "list";
  const historyEvents = state.data?.counts?.history_events || 0;
  els.eventsList.innerHTML = [
    `<div class="event-row event-summary"><b>History</b><span>Completed events</span><span>${historyEvents}</span></div>`,
    ...events.slice(0, 8).map((ev) => {
    const calls = (ev.callsigns || []).join(" / ") || "--";
    const pov = ev.pov?.valid ? " POV" : "";
    const etaAttrs = ev.time
      ? `class="live-eta" data-event-time="${ev.time}" data-eta-sec="${ev.eta_sec ?? ""}"`
      : "";
    return `<div class="event-row">
      <b>${ev.type}${pov}</b><span>${calls}</span><span ${etaAttrs}>${fmtEtaForTime(ev.time, ev.eta_sec)}</span>
      <small>${eventDetail(ev)}</small>
    </div>`;
  })].join("");
}

function updateTraffic() {
  const aircraft = activeDisplayAircraft();
  const units = unitConfig();
  els.trafficList.innerHTML = aircraft.slice(0, 80).map((ac) => {
    const dot = ac.conflict ? "alert" : ac.has_event ? "warn" : "";
    const active = ac.icao === state.selected ? " active" : "";
    return `<button class="traffic-row${active}" data-icao="${ac.icao}">
      <span class="dot ${dot}"></span>
      <span>${ac.callsign || ac.icao}<br><span class="muted">${ac.icao}</span></span>
      <span>${formatDistanceKm(ac.distance_km, 1)}</span>
      <span>${formatAltitudeFt(ac.altitude, 0)}</span>
      <span>${formatSpeedKt(ac.speed, 0)}</span>
    </button>`;
  }).join("");
}

function refreshUi(detail = "full") {
  document.body.dataset.style = state.data?.settings?.web?.visual_style || "cwp_classic";
  if (detail === "light") {
    const now = performance.now();
    if (now - state.lastPanelRefreshMs > 1000) {
      updateStatus();
      updateSelected();
      updateTraffic();
      state.lastPanelRefreshMs = now;
    }
    draw();
    return;
  }
  updateStatus();
  updateSelected();
  updateEvents();
  updateTraffic();
  state.lastPanelRefreshMs = performance.now();
  draw();
}

function field(key, label, value, type = "text", step = "any") {
  return `<div class="field"><label for="cfg_${key}">${label}</label><input id="cfg_${key}" data-key="${key}" type="${type}" step="${step}" value="${value ?? ""}"></div>`;
}

function selectField(key, label, value, options) {
  return `<div class="field"><label for="cfg_${key}">${label}</label><select id="cfg_${key}" data-key="${key}">
    ${options.map((opt) => `<option value="${opt}" ${String(value) === String(opt) ? "selected" : ""}>${optionLabel(key, opt)}</option>`).join("")}
  </select></div>`;
}

function checkbox(key, label, checked) {
  return `<label><input type="checkbox" data-key="${key}" ${checked ? "checked" : ""}>${label}</label>`;
}

function checkboxList(key, values, options, labels) {
  const selected = new Set(values || []);
  return `<div class="check-list" data-list="${key}">
    ${options.map((opt) => `<label><input type="checkbox" value="${opt}" ${selected.has(opt) ? "checked" : ""}>${labels?.[opt] || opt}</label>`).join("")}
  </div>`;
}

function orderedLabelList(values, lineValues, options) {
  const ordered = [...(values || []), ...options.filter((opt) => !(values || []).includes(opt))]
    .filter((value, index, arr) => options.includes(value) && arr.indexOf(value) === index);
  const fieldLines = {};
  (lineValues || []).forEach((line, lineIndex) => {
    if (!Array.isArray(line)) return;
    line.forEach((field) => {
      fieldLines[field] = String(lineIndex + 1);
    });
  });
  return `<div class="label-builder" data-list="web.aircraft_label_fields">
    <div class="label-builder-list">
      ${ordered.map((opt, index) => `<div class="label-builder-row" data-label-option="${opt}">
        <label><input type="checkbox" value="${opt}" ${values?.includes(opt) ? "checked" : ""}>${aircraftLabelNames[opt] || opt}</label>
        <div class="label-order-controls">
          <select data-label-line title="Label line">
            ${["1", "2", "3", "4"].map((line) => `<option value="${line}" ${String(fieldLines[opt] || (opt === "callsign" ? "1" : "2")) === line ? "selected" : ""}>L${line}</option>`).join("")}
          </select>
          <button type="button" data-label-move="up" title="Move up" ${index === 0 ? "disabled" : ""}>↑</button>
          <button type="button" data-label-move="down" title="Move down" ${index === ordered.length - 1 ? "disabled" : ""}>↓</button>
        </div>
      </div>`).join("")}
    </div>
    <div class="label-preview" id="labelPreview"></div>
  </div>`;
}

function updateLabelBuilderButtons(builder) {
  const rows = Array.from(builder.querySelectorAll(".label-builder-row"));
  rows.forEach((row, index) => {
    const up = row.querySelector('[data-label-move="up"]');
    const down = row.querySelector('[data-label-move="down"]');
    if (up) up.disabled = index === 0;
    if (down) down.disabled = index === rows.length - 1;
  });
}

function labelBuilderFields(builder) {
  return Array.from(builder.querySelectorAll(".label-builder-row"))
    .filter((row) => row.querySelector("input")?.checked)
    .map((row) => row.dataset.labelOption);
}

function labelBuilderLines(builder) {
  const lines = [[], [], [], []];
  Array.from(builder.querySelectorAll(".label-builder-row")).forEach((row) => {
    const input = row.querySelector("input");
    if (!input?.checked) return;
    const lineIndex = Math.max(0, Math.min(3, Number(row.querySelector("[data-label-line]")?.value || 1) - 1));
    lines[lineIndex].push(row.dataset.labelOption);
  });
  return lines.filter((line) => line.length);
}

function sampleAircraftForPreview() {
  const aircraft = activeDisplayAircraft();
  return aircraft.find((ac) => ac.callsign) || aircraft[0] || {
    icao: "ABC123",
    callsign: "SAMPLE",
    distance_km: 12.4,
    altitude: 18600,
    speed: 420,
    track: 273,
    vs: 832,
    squawk: "1200",
  };
}

function updateLabelPreview() {
  const builder = els.settingsBody.querySelector(".label-builder");
  const preview = document.getElementById("labelPreview");
  if (!builder || !preview) return;
  const lines = buildAircraftLabelLines(sampleAircraftForPreview(), labelBuilderFields(builder), labelBuilderLines(builder));
  const size = els.settingsBody.querySelector('[data-key="web.aircraft_label_size"]')?.value || "medium";
  const labelMetrics = aircraftLabelMetrics(size);
  preview.style.font = labelMetrics.font;
  preview.innerHTML = `<span></span><div>${lines.map((line) => `<strong>${line}</strong>`).join("")}</div>`;
}

function bindLabelBuilder() {
  const builder = els.settingsBody.querySelector(".label-builder");
  if (!builder) return;
  builder.addEventListener("click", (event) => {
    const button = event.target.closest("[data-label-move]");
    if (!button) return;
    const row = button.closest(".label-builder-row");
    if (!row) return;
    if (button.dataset.labelMove === "up" && row.previousElementSibling) {
      row.parentElement.insertBefore(row, row.previousElementSibling);
    }
    if (button.dataset.labelMove === "down" && row.nextElementSibling) {
      row.parentElement.insertBefore(row.nextElementSibling, row);
    }
    updateLabelBuilderButtons(builder);
    updateLabelPreview();
  });
  builder.addEventListener("change", updateLabelPreview);
  els.settingsBody.querySelector('[data-key="web.aircraft_label_size"]')?.addEventListener("change", updateLabelPreview);
  updateLabelBuilderButtons(builder);
  updateLabelPreview();
}

async function openSettings() {
  const res = await fetch("/api/config", { cache: "no-store" });
  const payload = await res.json();
  const cfg = payload.config;
  const web = payload.web;
  const opt = payload.options;
  const about = payload.about || {};
  els.settingsMessage.textContent = "";
  els.settingsBody.innerHTML = `
    ${settingsHelpPanel()}
    ${settingsAboutPanel(about)}
    <section class="settings-group">
      <h2>Map Display</h2>
      <div class="settings-grid">
        ${selectField("web.visual_style", "Theme", web.visual_style, opt.visual_styles)}
        ${selectField("web.aircraft_label_color", "Label color", web.aircraft_label_color, opt.aircraft_label_colors)}
        ${selectField("web.aircraft_label_size", "Label size", web.aircraft_label_size || "medium", opt.aircraft_label_sizes)}
        ${selectField("web.ils_style", "ILS appearance", web.ils_style, opt.ils_styles)}
        ${selectField("web.ils_length_nm", "ILS length", web.ils_length_nm, opt.ils_lengths_nm)}
      </div>
      <div class="check-list">
        ${checkbox("web.show_background_grid", "Background grid", web.show_background_grid !== false)}
        ${checkbox("web.show_geo_vectors", "Geographic vector layers", web.show_geo_vectors)}
        ${checkbox("web.show_event_range_ring", "Event range ring", web.show_event_range_ring)}
        ${checkbox("web.show_event_aircraft_links", "Event aircraft links", web.show_event_aircraft_links)}
      </div>
    </section>
    <section class="settings-group">
      <h2>Receiver</h2>
      <div class="settings-grid">
        ${field("host", "SBS Host", cfg.host)}
        ${field("port", "SBS Port", cfg.port, "number", "1")}
        ${field("device_index", "RTL Device Index", cfg.device_index, "number", "1")}
        ${field("gain", "RTL Gain (-10 auto)", cfg.gain)}
      </div>
    </section>
    <section class="settings-group">
      <h2>Observer</h2>
      <div class="settings-grid">
        ${field("lat", "Latitude", cfg.lat, "number", "0.000001")}
        ${field("lon", "Longitude", cfg.lon, "number", "0.000001")}
        ${field("alt_m", "Altitude m", cfg.alt_m, "number", "0.1")}
      </div>
    </section>
    <section class="settings-group">
      <h2>Prediction</h2>
      <div class="settings-grid">
        ${field("aircraft_timeout", "Aircraft Timeout s", cfg.aircraft_timeout, "number", "0.1")}
        ${field("pred_interval", "Prediction Interval s", cfg.pred_interval, "number", "0.1")}
        ${field("pred_horizon", "Prediction Horizon s", cfg.pred_horizon, "number", "0.1")}
        ${field("pred_step", "Prediction Step s", cfg.pred_step, "number", "0.1")}
        ${field("prediction_average_sec", "Prediction Average s", cfg.prediction_average_sec, "number", "0.5")}
        ${field("event_min_elevation_deg", "Min Event Elevation deg", cfg.event_min_elevation_deg ?? 2, "number", "0.1")}
        ${field("conflict_angle", "Conflict Angle deg", cfg.conflict_angle, "number", "0.1")}
        ${field("event_timeout", "Event Timeout s", cfg.event_timeout, "number", "0.1")}
        ${field("conflict_radius_km", "Conflict Radius km", cfg.conflict_radius_km, "number", "0.1")}
        ${field("history_minutes", "History Minutes", cfg.history_minutes, "number", "0.1")}
      </div>
    </section>
    <section class="settings-group">
      <h2>Display</h2>
      <div class="settings-grid">
        ${selectField("web.unit_distance", "Distance units", web.unit_distance, opt.unit_distances)}
        ${selectField("web.unit_speed", "Speed units", web.unit_speed, opt.unit_speeds)}
        ${selectField("web.unit_altitude", "Altitude units", web.unit_altitude, opt.unit_altitudes)}
        ${selectField("web.aircraft_refresh_interval", "Aircraft refresh", web.aircraft_refresh_interval || "realtime", opt.aircraft_refresh_intervals)}
        ${cfg.show_range_rings ? selectField("range_ring_spacing_nm_str", "Range ring spacing", cfg.range_ring_spacing_nm_str, opt.range_ring_spacing_nm) : ""}
        ${cfg.show_range_rings ? field("max_range_rings", "Max Range Rings", cfg.max_range_rings, "number", "1") : ""}
        ${selectField("web.trajectory_minutes", "Track duration", web.trajectory_minutes, opt.trajectory_minutes)}
        ${selectField("velocity_vector_minutes", "Speed vector length", cfg.velocity_vector_minutes, opt.velocity_vector_minutes)}
        ${selectField("web.trajectory_display_mode", "History style", web.trajectory_display_mode, opt.trajectory_display_modes)}
      </div>
      <div class="check-list">
        ${checkbox("show_history", "Aircraft history", cfg.show_history)}
        ${checkbox("web.show_active_full_history", "Full active tracks", web.show_active_full_history)}
        ${checkbox("web.show_grounded_aircraft", "Grounded aircraft", web.show_grounded_aircraft)}
        ${checkbox("show_events", "Event locations", cfg.show_events)}
        ${checkbox("show_glideslope", "Glideslope", cfg.show_glideslope)}
        ${checkbox("show_range_rings", "Range rings", cfg.show_range_rings)}
        ${checkbox("show_all_transit_strips", "All transit strips", cfg.show_all_transit_strips)}
        ${checkbox("show_velocity_vector", "Speed vector", cfg.show_velocity_vector)}
      </div>
    </section>
    <section class="settings-group full">
      <h2>Aircraft Labels</h2>
      ${orderedLabelList(web.aircraft_label_fields, web.aircraft_label_lines, opt.aircraft_label_fields)}
    </section>
    <section class="settings-group full">
      <h2>Airport Types</h2>
      ${checkboxList("show_airport_types", cfg.show_airport_types, opt.airport_types)}
    </section>
    <section class="settings-group full">
      <h2>Navaid Types</h2>
      ${checkboxList("show_navaid_types", cfg.show_navaid_types, opt.navaid_types)}
    </section>
    <section class="settings-group full">
      <h2>Vector Layers</h2>
      ${checkboxList("vector_layers_visibility", Object.entries(cfg.vector_layers_visibility || {}).filter(([, v]) => v).map(([k]) => k), Object.keys(opt.vector_layers), opt.vector_layers)}
    </section>
  `;
  openDialog(els.settingsDialog);
  bindLabelBuilder();
}

function readSettingsForm() {
  const payload = { web: {} };
  els.settingsBody.querySelectorAll("[data-key]").forEach((node) => {
    const key = node.dataset.key;
    const target = key.startsWith("web.") ? payload.web : payload;
    const cleanKey = key.startsWith("web.") ? key.slice(4) : key;
    if (node.type === "checkbox") target[cleanKey] = node.checked;
    else if (node.type === "number") target[cleanKey] = Number(node.value);
    else target[cleanKey] = node.value;
  });
  els.settingsBody.querySelectorAll("[data-list]").forEach((list) => {
    const key = list.dataset.list;
    const target = key.startsWith("web.") ? payload.web : payload;
    const cleanKey = key.startsWith("web.") ? key.slice(4) : key;
    if (cleanKey === "vector_layers_visibility") {
      target[cleanKey] = {};
      list.querySelectorAll("input").forEach((input) => {
        target[cleanKey][input.value] = input.checked;
      });
    } else {
      target[cleanKey] = Array.from(list.querySelectorAll("input:checked")).map((input) => input.value);
    }
  });
  const labelBuilder = els.settingsBody.querySelector(".label-builder");
  if (labelBuilder) {
    payload.web.aircraft_label_lines = labelBuilderLines(labelBuilder);
  }
  return payload;
}

async function saveSettings() {
  els.settingsMessage.textContent = "Saving...";
  const restartKeys = ["host", "port", "device_index", "gain"];
  const receiverRestartNeeded = restartKeys.some((key) => {
    const input = document.getElementById(`cfg_${key}`);
    return input && String(input.value) !== String(input.defaultValue);
  });
  const res = await fetch("/api/config", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(readSettingsForm()),
  });
  const payload = await res.json();
  if (!payload.ok) {
    els.settingsMessage.textContent = payload.error || "Save failed";
    return;
  }
  els.settingsMessage.textContent = receiverRestartNeeded
    ? "Saved. Receiver changes require restarting adsb-web/dump1090 to fully apply."
    : "Saved";
  state.web = payload.web || state.web;
  state.lowDetailCache = null;
  state.lastGoodGeodata = null;
  state.lastGoodGeodataRangeClass = null;
  state.interactionGeodata = null;
  if (state.data) {
    state.data.geodata = { airports: [], navaids: [], runways: [], vectors: [] };
    state.data.cache = { ...(state.data.cache || {}), map_pending: true };
  }
  await fetchState({ detail: "full", force: true });
  requestFullStateFetch(150);
}

function useGps() {
  if (!navigator.geolocation) {
    els.settingsMessage.textContent = "GPS is not available in this browser.";
    return;
  }
  els.settingsMessage.textContent = "Requesting GPS...";
  navigator.geolocation.getCurrentPosition(
    (position) => {
      const coords = position.coords;
      const lat = document.getElementById("cfg_lat");
      const lon = document.getElementById("cfg_lon");
      const alt = document.getElementById("cfg_alt_m");
      if (lat) lat.value = coords.latitude.toFixed(7);
      if (lon) lon.value = coords.longitude.toFixed(7);
      if (alt && coords.altitude !== null) alt.value = coords.altitude.toFixed(1);
      els.settingsMessage.textContent = coords.altitude === null ? "GPS filled lat/lon. Enter observer altitude manually." : "GPS filled.";
    },
    (error) => {
      els.settingsMessage.textContent = `${error.message || "GPS request failed."} Try Windows Location.`;
    },
    { enableHighAccuracy: true, timeout: 15000, maximumAge: 5000 },
  );
}

async function useWindowsLocation() {
  els.settingsMessage.textContent = "Requesting Windows Location...";
  const res = await fetch("/api/location/windows", { cache: "no-store" });
  const payload = await res.json();
  if (!payload.ok) {
    els.settingsMessage.textContent = payload.error || "Windows Location failed.";
    return;
  }
  const loc = payload.location;
  const lat = document.getElementById("cfg_lat");
  const lon = document.getElementById("cfg_lon");
  const alt = document.getElementById("cfg_alt_m");
  if (lat) lat.value = Number(loc.lat).toFixed(7);
  if (lon) lon.value = Number(loc.lon).toFixed(7);
  if (alt && loc.alt_m !== null && loc.alt_m !== undefined) alt.value = Number(loc.alt_m).toFixed(1);
  const acc = loc.horizontal_accuracy_m ? `, accuracy ${Number(loc.horizontal_accuracy_m).toFixed(0)}m` : "";
  els.settingsMessage.textContent = loc.alt_m === null || loc.alt_m === undefined
    ? `Windows Location filled lat/lon${acc}. Enter observer altitude manually.`
    : `Windows Location filled${acc}.`;
}

function formatBytes(bytes) {
  const value = Number(bytes || 0);
  if (!Number.isFinite(value) || value <= 0) return "0 KB";
  if (value >= 1024 * 1024) return `${(value / (1024 * 1024)).toFixed(1)} MB`;
  return `${Math.max(1, Math.round(value / 1024))} KB`;
}

function preserveFullStateFields(nextData, detail) {
  if (!state.data) return nextData;
  if (!Array.isArray(nextData.events)) nextData.events = state.data.events || [];
  if (!Array.isArray(nextData.transits)) nextData.transits = state.data.transits || [];
  const geo = nextData.geodata || {};
  const vectorCount = Array.isArray(geo.vectors) ? geo.vectors.length : 0;
  const previousVectorCount = Array.isArray(state.data.geodata?.vectors) ? state.data.geodata.vectors.length : 0;
  const incomingQuality = geodataVisualQuality(geo);
  const previousQuality = geodataVisualQuality(state.data.geodata);
  const sameRangeClass = geodataRangeClass(nextData.settings?.range_km) === geodataRangeClass(state.data.settings?.range_km);
  const hasGeodata = ["airports", "navaids", "runways", "vectors"].some((key) => Array.isArray(geo[key]) && geo[key].length);
  if (detail === "light" || (!hasGeodata && previousVectorCount > 0)) {
    nextData.geodata = state.data.geodata || nextData.geodata;
  } else if (
    nextData.cache?.map_pending
    && sameRangeClass
    && (
      !Array.isArray(geo.vectors)
      || !geo.vectors.length
      || (previousVectorCount > 0 && vectorCount < Math.max(3, previousVectorCount * 0.35))
      || (previousQuality > 0 && incomingQuality < previousQuality * 0.35)
    )
  ) {
    const previousGeo = state.data.geodata || {};
    nextData.geodata = {
      ...geo,
      vectors: Array.isArray(previousGeo.vectors) ? previousGeo.vectors : [],
    };
  }
  if (detail === "light") {
    nextData.glideslopes = state.data.glideslopes || [];
  } else if (!Array.isArray(nextData.glideslopes) || !nextData.glideslopes.length) {
    nextData.glideslopes = state.data.glideslopes || nextData.glideslopes;
  }
  if (state.glideslopeOverride) {
    nextData.glideslopes = state.glideslopeOverride.glideslopes || [];
    if (nextData.settings?.web) {
      nextData.settings.web = {
        ...nextData.settings.web,
        active_glideslopes: copyGlideslopeItems(state.glideslopeOverride.activeItems),
      };
    }
  }
  nextData.celestial = state.data.celestial || nextData.celestial;
  return nextData;
}

async function fetchState(options = {}) {
  const detail = options.detail === "light" ? "light" : "full";
  const rect = canvas.getBoundingClientRect();
  if (state.fetchTimer) {
    clearTimeout(state.fetchTimer);
    state.fetchTimer = null;
  }
  if (isMapInteracting()) {
    state.pendingFetch = true;
    state.pendingFetchDetail = state.pendingFetchDetail === "full" || detail === "full" ? "full" : "light";
    return;
  }
  if (state.fetchInFlight[detail] && !options.force) {
    state.pendingFetch = true;
    state.pendingFetchDetail = state.pendingFetchDetail === "full" || detail === "full" ? "full" : "light";
    return;
  }
  state.fetchInFlight[detail] = true;
  const viewportWidth = Math.max(1, Math.round(rect.width || 1));
  const viewportHeight = Math.max(1, Math.round(rect.height || 1));
  const effective3dRangeKm = state.rangeKm / Math.max(0.25, effective3dViewZoom());
  const requestRangeKm = state.viewMode === "3d"
    ? Math.max(state.rangeKm, Math.min(1000, effective3dRangeKm * 1.35), 8)
    : state.rangeKm;
  const mapViewportSize = state.viewMode === "3d"
    ? Math.round(Math.max(viewportWidth, viewportHeight) * 3)
    : null;
  const params = new URLSearchParams({
    range_km: requestRangeKm,
    selected: state.selected,
    transits: state.transits,
    center_lat: state.center?.lat ?? "",
    center_lon: state.center?.lon ?? "",
    viewport_width: mapViewportSize || viewportWidth,
    viewport_height: mapViewportSize || viewportHeight,
    detail,
    client: state.clientId,
  });
  try {
    const res = await fetch(`/api/state?${params.toString()}`, { cache: "no-store" });
    if (!res.ok) throw new Error(`state request failed: ${res.status}`);
    const payload = await res.json();
    const payloadServerMs = Date.parse(payload.server_time);
    if (Number.isFinite(payloadServerMs) && state.lastStateServerMs && payloadServerMs < state.lastStateServerMs - 50) {
      return;
    }
    if (
      detail === "full"
      && state.glideslopeOverride
      && glideslopeItemsKey(payload.settings?.web?.active_glideslopes || []) === glideslopeItemsKey(state.glideslopeOverride.activeItems)
    ) {
      state.glideslopeOverride = null;
    }
    if (isMapInteracting()) {
      state.pendingFetch = true;
      state.pendingFetchDetail = state.pendingFetchDetail === "full" || detail === "full" ? "full" : "light";
      return;
    }
    state.data = preserveFullStateFields(payload, detail);
    const dataRangeClass = geodataRangeClass(state.data.settings?.range_km);
    if (
      dataRangeClass !== state.lastGoodGeodataRangeClass
      || geodataVisualQuality(state.data.geodata) >= geodataVisualQuality(state.lastGoodGeodata)
    ) {
      state.lastGoodGeodata = state.data.geodata;
      state.lastGoodGeodataRangeClass = dataRangeClass;
    }
    syncClockFromServer(state.data.server_time);
    if (detail === "full" && !isMapInteracting()) state.lowDetailCache = null;
    state.web = state.data.settings.web;
    if (!state.center) state.center = state.data.settings.center || state.data.settings.user;
    if (!isMapInteracting()) refreshUi(detail);
    if (detail === "full" && state.data.cache?.map_pending) requestFullStateFetch(500);
  } finally {
    state.fetchInFlight[detail] = false;
    if (state.pendingFetch && !isMapInteracting()) {
      const nextDetail = state.pendingFetchDetail || "full";
      state.pendingFetch = false;
      state.pendingFetchDetail = null;
      fetchState({ detail: nextDetail }).catch(console.error);
    }
  }
}

function requestStateFetch(delay = 0, detail = "full") {
  if (state.fetchTimer) clearTimeout(state.fetchTimer);
  state.fetchTimer = setTimeout(() => {
    state.fetchTimer = null;
    fetchState({ detail }).catch(console.error);
  }, delay);
}

function requestFullStateFetch(delay = 0) {
  if (state.fullFetchTimer) clearTimeout(state.fullFetchTimer);
  state.fullFetchTimer = setTimeout(() => {
    state.fullFetchTimer = null;
    fetchState({ detail: "full" }).catch(console.error);
  }, delay);
}

function setEventPredictionPause(paused) {
  if (state.eventPauseTimer) {
    clearTimeout(state.eventPauseTimer);
    state.eventPauseTimer = null;
  }
  if (state.eventPredictionPaused === paused) return;
  state.eventPredictionPaused = paused;
  fetch("/api/interaction", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ pause_events: paused }),
    keepalive: true,
  }).catch(console.error);
}

function resumeEventPredictionSoon(delay = 300) {
  if (state.eventPauseTimer) clearTimeout(state.eventPauseTimer);
  state.eventPauseTimer = setTimeout(() => {
    state.eventPauseTimer = null;
    setEventPredictionPause(false);
  }, delay);
}

function fullRefreshIntervalMs() {
  const configuredSec = Number(state.data?.settings?.prediction_interval_sec || 2);
  return Math.max(500, Math.min(10000, configuredSec * 1000));
}

function aircraftRefreshIntervalMs() {
  const value = String(state.data?.settings?.web?.aircraft_refresh_interval || state.web?.aircraft_refresh_interval || "realtime");
  if (value === "realtime") return 250;
  const seconds = Number(value);
  return Number.isFinite(seconds) ? Math.max(250, Math.min(5000, seconds * 1000)) : 250;
}

function scheduleAircraftRefreshLoop() {
  setTimeout(() => {
    if (!isMapInteracting()) {
      fetchState({ detail: "light" }).catch(console.error);
    }
    scheduleAircraftRefreshLoop();
  }, aircraftRefreshIntervalMs());
}

function scheduleFullRefreshLoop() {
  setTimeout(() => {
    if (!isMapInteracting()) {
      fetchState({ detail: "full" }).catch(console.error);
    }
    scheduleFullRefreshLoop();
  }, fullRefreshIntervalMs());
}

function selectNearestAircraft(event) {
  if (state.viewMode === "ar") return;
  if (state.suppressClick) {
    state.suppressClick = false;
    return;
  }
  const data = state.data;
  if (!data) return;
  const rect = canvas.getBoundingClientRect();
  const click = { x: event.clientX - rect.left, y: event.clientY - rect.top };
  const runway = nearestRunwayAt(click.x, click.y);
  if (runway && showRunwayOptions(runway)) return;
  let best = null;
  let bestDist = 16;
  activeDisplayAircraft().forEach((ac) => {
    if (!isAircraftDrawable(ac)) return;
    const p = state.viewMode === "3d" ? projectWithAltitude(ac.lat, ac.lon, aircraftAltM(ac)) : project(ac.lat, ac.lon);
    if (!p) return;
    const d = Math.hypot(p.x - click.x, p.y - click.y);
    if (d < bestDist) {
      best = ac;
      bestDist = d;
    }
  });
  if (best) {
    state.selected = best.icao;
    if (state.data && state.transits === "selected") state.data.transits = [];
    refreshUi();
    fetchState({ detail: "full", force: true }).catch(console.error);
  } else if (state.selected) {
    state.selected = "";
    if (state.data && state.transits === "selected") state.data.transits = [];
    refreshUi();
    fetchState({ detail: "full", force: true }).catch(console.error);
  }
}

document.getElementById("zoomIn").addEventListener("click", () => {
  state.rangeKm = Math.max(1, state.rangeKm / 1.25);
  enforce3dViewBounds();
  fetchState().catch(console.error);
});

document.getElementById("zoomOut").addEventListener("click", () => {
  state.rangeKm = Math.min(1000, state.rangeKm * 1.25);
  enforce3dViewBounds();
  fetchState().catch(console.error);
});

els.centerUser.addEventListener("click", () => {
  if (!state.data) return;
  state.center = { ...state.data.settings.user };
  fetchState().catch(console.error);
});

els.toggleTransits.addEventListener("click", () => {
  state.transits = state.transits === "selected" ? "all" : state.transits === "all" ? "none" : "selected";
  els.toggleTransits.textContent = state.transits === "all" ? "All Transit" : state.transits === "none" ? "No Transit" : "Transit";
  if (state.data && (state.transits === "none" || (state.transits === "selected" && !state.selected))) {
    state.data.transits = [];
    draw();
  }
  fetchState({ detail: "full", force: true }).catch(console.error);
});

async function cycleViewMode() {
  const modes = ["2d", "3d"];
  const previous = state.viewMode;
  const next = modes[(modes.indexOf(state.viewMode) + 1) % modes.length] || "2d";
  state.viewMode = next;
  if (previous !== "3d" && next === "3d") {
    state.viewZoom = 1;
  }
  enforce3dViewBounds();
  if (els.viewModeButton) els.viewModeButton.textContent = next.toUpperCase();
  requestDraw(true);
  requestFullStateFetch(next === "3d" ? 60 : 180);
}

els.viewModeButton.addEventListener("click", () => cycleViewMode().catch(console.error));
els.closeViewOverlay?.addEventListener("click", closeView);

els.openSettings.addEventListener("click", () => openSettings().catch((err) => {
  els.settingsMessage.textContent = err.message;
}));
els.closeSettings.addEventListener("click", () => closeDialog(els.settingsDialog));
els.saveSettings.addEventListener("click", () => saveSettings().catch((err) => {
  els.settingsMessage.textContent = err.message;
}));
els.gpsButton.addEventListener("click", useGps);
els.windowsGpsButton.addEventListener("click", () => useWindowsLocation().catch((err) => {
  els.settingsMessage.textContent = err.message;
}));

els.trafficList.addEventListener("click", (event) => {
  const row = event.target.closest("[data-icao]");
  if (!row) return;
  state.selected = row.dataset.icao;
  fetchState().catch(console.error);
});

canvas.addEventListener("click", selectNearestAircraft);
canvas.addEventListener("wheel", (event) => {
  event.preventDefault();
  setEventPredictionPause(true);
  lockInteractionGeodata();
  if (state.viewMode === "3d") {
    state.viewZoom = clamp3dViewZoom(state.viewZoom * (event.deltaY < 0 ? 1.12 : 0.90));
    requestDraw(true);
    requestStateFetch(120, "light");
    requestFullStateFetch(180);
    releaseInteractionGeodata(360);
    resumeEventPredictionSoon(350);
    return;
  }
  const before = unproject(event.offsetX, event.offsetY);
  state.rangeKm = Math.max(1, Math.min(1000, state.rangeKm * (event.deltaY < 0 ? 0.85 : 1.18)));
  if (before) {
    const after = unproject(event.offsetX, event.offsetY);
    state.center = {
      lat: state.center.lat + (before.lat - after.lat),
      lon: state.center.lon + (before.lon - after.lon),
    };
  }
  requestDraw(true);
  requestStateFetch(120, "light");
  requestFullStateFetch(180);
  releaseInteractionGeodata(420);
  resumeEventPredictionSoon(450);
}, { passive: false });

canvas.addEventListener("contextmenu", (event) => {
  if (state.viewMode === "3d") event.preventDefault();
});

canvas.addEventListener("pointerdown", (event) => {
  if (state.pinching) return;
  setEventPredictionPause(true);
  lockInteractionGeodata();
  if (state.viewMode === "3d") {
    if (event.pointerType === "mouse" && event.button === 2) {
      state.dragging = true;
      state.dragStart = {
        x: event.clientX,
        y: event.clientY,
        center: { ...(state.center || state.data?.settings?.center || state.data?.settings?.user || {}) },
        is3dPan: true,
      };
      canvas.classList.add("dragging");
      canvas.setPointerCapture(event.pointerId);
      event.preventDefault();
      return;
    }
    if (event.pointerType === "mouse" && event.button !== 0) return;
    state.viewDragging = true;
    state.viewDragStart = {
      x: event.clientX,
      y: event.clientY,
      yaw: state.viewYaw,
      pitch: state.viewPitch,
      az: state.viewAz,
      el: state.viewEl,
    };
    canvas.classList.add("dragging");
    canvas.setPointerCapture(event.pointerId);
    return;
  }
  if (event.pointerType === "mouse" && event.button !== 0) return;
  state.dragging = true;
  state.dragStart = { x: event.clientX, y: event.clientY, center: { ...(state.center || state.data?.settings?.user) } };
  canvas.classList.add("dragging");
  canvas.setPointerCapture(event.pointerId);
});

canvas.addEventListener("pointermove", (event) => {
  if (state.pinching) return;
  if (state.viewDragging && state.viewDragStart && state.viewMode === "3d") {
    const dx = event.clientX - state.viewDragStart.x;
    const dy = event.clientY - state.viewDragStart.y;
    if (Math.hypot(dx, dy) > 4) state.suppressClick = true;
    state.viewYaw = (state.viewDragStart.yaw - dx * 0.35 + 360) % 360;
    state.viewPitch = clamp3dPitch(state.viewDragStart.pitch - dy * 0.25);
    requestDraw(true);
    return;
  }
  if (state.viewMode === "3d" && state.dragging && state.dragStart?.is3dPan && state.data) {
    const rect = canvas.getBoundingClientRect();
    const center = state.dragStart.center;
    const latRad = (Math.PI / 180) * center.lat;
    const kmPerDegLat = 111.32;
    const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
    const baseScale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
    const screenScale = Math.max(0.001, baseScale * effective3dViewZoom());
    const dx = event.clientX - state.dragStart.x;
    const dy = event.clientY - state.dragStart.y;
    if (Math.hypot(dx, dy) > 4) state.suppressClick = true;
    const yaw = ((state.viewYaw || 0) * Math.PI) / 180;
    const mapDx = dx * Math.cos(yaw) + dy * Math.sin(yaw);
    const mapDy = -dx * Math.sin(yaw) + dy * Math.cos(yaw);
    state.center = {
      lat: center.lat + (mapDy / screenScale) / kmPerDegLat,
      lon: center.lon - (mapDx / screenScale) / kmPerDegLon,
    };
    requestDraw(true);
    return;
  }
  if (state.pinching || !state.dragging || !state.dragStart || !state.data) return;
  const rect = canvas.getBoundingClientRect();
  const center = state.dragStart.center;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  const dx = event.clientX - state.dragStart.x;
  const dy = event.clientY - state.dragStart.y;
  if (Math.hypot(dx, dy) > 4) state.suppressClick = true;
  state.center = {
    lat: center.lat + (dy / scale) / kmPerDegLat,
    lon: center.lon - (dx / scale) / kmPerDegLon,
  };
  requestDraw(true);
});

canvas.addEventListener("pointerup", (event) => {
  if (state.pinching) return;
  if (state.viewDragging) {
    state.viewDragging = false;
    state.viewDragStart = null;
    canvas.classList.remove("dragging");
    try { canvas.releasePointerCapture(event.pointerId); } catch {}
    requestStateFetch(60, "light");
    requestFullStateFetch(220);
    releaseInteractionGeodata();
    resumeEventPredictionSoon(350);
    return;
  }
  if (!state.dragging) return;
  state.dragging = false;
  state.dragStart = null;
  if (state.interactiveDrawTimer) {
    clearTimeout(state.interactiveDrawTimer);
    state.interactiveDrawTimer = null;
  }
  canvas.classList.remove("dragging");
  try { canvas.releasePointerCapture(event.pointerId); } catch {}
  requestStateFetch(60, "light");
  requestFullStateFetch(220);
  releaseInteractionGeodata();
  resumeEventPredictionSoon(350);
});

canvas.addEventListener("pointercancel", () => {
  if (state.pinching) return;
  state.viewDragging = false;
  state.viewDragStart = null;
  state.dragging = false;
  state.dragStart = null;
  canvas.classList.remove("dragging");
  releaseInteractionGeodata(120);
  resumeEventPredictionSoon(100);
});

canvas.addEventListener("touchstart", (event) => {
  if (event.touches.length === 2) {
    setEventPredictionPause(true);
    lockInteractionGeodata();
    state.pinching = true;
    state.dragging = false;
    state.dragStart = null;
    state.viewDragging = false;
    state.viewDragStart = null;
    canvas.classList.remove("dragging");
    state.touchStartDistance = Math.hypot(
      event.touches[0].clientX - event.touches[1].clientX,
      event.touches[0].clientY - event.touches[1].clientY,
    );
    state.touchStartAngle = Math.atan2(
      event.touches[1].clientY - event.touches[0].clientY,
      event.touches[1].clientX - event.touches[0].clientX,
    );
    state.touchViewStart = {
      zoom: state.viewZoom,
      yaw: state.viewYaw,
      pitch: state.viewPitch,
      fov: state.viewFov,
      az: state.viewAz,
      center: { ...(state.center || state.data?.settings?.center || state.data?.settings?.user || {}) },
      midX: (event.touches[0].clientX + event.touches[1].clientX) / 2,
      midY: (event.touches[0].clientY + event.touches[1].clientY) / 2,
    };
  }
}, { passive: true });

canvas.addEventListener("touchmove", (event) => {
  if (event.touches.length !== 2 || !state.touchStartDistance) return;
  event.preventDefault();
  const rect = canvas.getBoundingClientRect();
  const midX = ((event.touches[0].clientX + event.touches[1].clientX) / 2) - rect.left;
  const midY = ((event.touches[0].clientY + event.touches[1].clientY) / 2) - rect.top;
  const before = unproject(midX, midY);
  const dist = Math.hypot(
    event.touches[0].clientX - event.touches[1].clientX,
    event.touches[0].clientY - event.touches[1].clientY,
  );
  const ratio = state.touchStartDistance / Math.max(1, dist);
  if (state.viewMode === "3d") {
    const start = state.touchViewStart || {};
    state.viewZoom = clamp3dViewZoom((start.zoom || 1) / ratio);
    const midClientX = (event.touches[0].clientX + event.touches[1].clientX) / 2;
    const midClientY = (event.touches[0].clientY + event.touches[1].clientY) / 2;
    const startCenter = start.center;
    if (startCenter?.lat !== undefined && startCenter?.lon !== undefined) {
      const latRad = (Math.PI / 180) * startCenter.lat;
      const kmPerDegLat = 111.32;
      const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
      const baseScale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
      const screenScale = Math.max(0.001, baseScale * state.viewZoom);
      const dx = midClientX - (start.midX || midClientX);
      const dy = midClientY - (start.midY || midClientY);
      const yaw = ((start.yaw || state.viewYaw || 0) * Math.PI) / 180;
      const mapDx = dx * Math.cos(yaw) + dy * Math.sin(yaw);
      const mapDy = -dx * Math.sin(yaw) + dy * Math.cos(yaw);
      state.center = {
        lat: startCenter.lat + (mapDy / screenScale) / kmPerDegLat,
        lon: startCenter.lon - (mapDx / screenScale) / kmPerDegLon,
      };
    }
    state.suppressClick = true;
    requestDraw(true);
    return;
  }
  state.rangeKm = Math.max(1, Math.min(1000, state.rangeKm * ratio));
  if (before) {
    const after = unproject(midX, midY);
    const center = state.center || state.data?.settings?.center || state.data?.settings?.user;
    state.center = {
      lat: center.lat + (before.lat - after.lat),
      lon: center.lon + (before.lon - after.lon),
    };
  }
  state.suppressClick = true;
  state.touchStartDistance = dist;
  requestDraw(true);
}, { passive: false });

canvas.addEventListener("touchend", () => {
  state.touchStartDistance = 0;
  state.touchStartAngle = 0;
  state.touchViewStart = null;
  state.pinching = false;
  if (state.interactiveDrawTimer) {
    clearTimeout(state.interactiveDrawTimer);
    state.interactiveDrawTimer = null;
  }
  requestStateFetch(60, "light");
  requestFullStateFetch(220);
  releaseInteractionGeodata();
  resumeEventPredictionSoon(350);
});

canvas.addEventListener("touchcancel", () => {
  state.touchStartDistance = 0;
  state.touchStartAngle = 0;
  state.touchViewStart = null;
  state.pinching = false;
  releaseInteractionGeodata(120);
  resumeEventPredictionSoon(100);
});

els.viewCanvas.addEventListener("pointerdown", (event) => {
  state.viewDragging = true;
  state.viewDragStart = {
    x: event.clientX,
    y: event.clientY,
    yaw: state.viewYaw,
    pitch: state.viewPitch,
    az: state.viewAz,
    el: state.viewEl,
  };
  els.viewCanvas.setPointerCapture(event.pointerId);
});

els.viewCanvas.addEventListener("pointermove", (event) => {
  if (!state.viewDragging || !state.viewDragStart) return;
  const dx = event.clientX - state.viewDragStart.x;
  const dy = event.clientY - state.viewDragStart.y;
  if (state.viewMode === "ar") {
    state.viewAz = (state.viewDragStart.az - dx * state.viewFov / Math.max(1, els.viewCanvas.clientWidth) + 360) % 360;
    state.viewEl = Math.max(-20, Math.min(80, state.viewDragStart.el + dy * state.viewFov / Math.max(1, els.viewCanvas.clientHeight)));
  } else {
    state.viewYaw = (state.viewDragStart.yaw - dx * 0.35 + 360) % 360;
    state.viewPitch = clamp3dPitch(state.viewDragStart.pitch - dy * 0.25);
  }
  drawActiveView();
});

els.viewCanvas.addEventListener("pointerup", (event) => {
  state.viewDragging = false;
  state.viewDragStart = null;
  try { els.viewCanvas.releasePointerCapture(event.pointerId); } catch {}
});

els.viewCanvas.addEventListener("wheel", (event) => {
  event.preventDefault();
  if (state.viewMode === "ar") {
    state.viewFov = Math.max(8, Math.min(110, state.viewFov * (event.deltaY < 0 ? 0.88 : 1.14)));
  } else {
    state.viewZoom = clamp3dViewZoom(state.viewZoom * (event.deltaY < 0 ? 1.12 : 0.90));
  }
  drawActiveView();
}, { passive: false });

els.hidePanel.addEventListener("click", () => {
  document.body.classList.add("panel-hidden");
  localStorage.setItem("adsb-panel-hidden", "1");
  updateSelected();
  scheduleResize();
});

els.showPanel.addEventListener("click", () => {
  document.body.classList.remove("panel-hidden");
  localStorage.setItem("adsb-panel-hidden", "0");
  updateMapAircraftInfo(null);
  scheduleResize();
});

els.settingsDialog.addEventListener("close", () => document.body.classList.remove("modal-open"));

if (localStorage.getItem("adsb-panel-hidden") === "1") {
  document.body.classList.add("panel-hidden");
}
setAppHeight();
window.addEventListener("resize", () => {
  setAppHeight();
  scheduleResize();
  resizeViewCanvas();
  requestFullStateFetch(180);
});
window.visualViewport?.addEventListener("resize", () => {
  setAppHeight();
  scheduleResize();
  resizeViewCanvas();
  requestFullStateFetch(180);
});
window.visualViewport?.addEventListener("scroll", () => {
  setAppHeight();
  scheduleResize();
});
resizeCanvas();
startClockLoop();
fetchState({ detail: "full" }).catch(console.error);
scheduleAircraftRefreshLoop();
scheduleFullRefreshLoop();
