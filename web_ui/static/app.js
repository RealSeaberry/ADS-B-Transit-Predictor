const canvas = document.getElementById("mapCanvas");
const ctx = canvas.getContext("2d");
const state = {
  data: null,
  web: null,
  center: null,
  rangeKm: 60,
  selected: "",
  transits: "selected",
  pixelRatio: window.devicePixelRatio || 1,
  dragging: false,
  dragStart: null,
  touchStartDistance: 0,
  suppressClick: false,
  drawScheduled: false,
  lastInteractiveDraw: 0,
  interactiveDrawTimer: null,
  fetchInFlight: false,
  pendingFetch: false,
  fetchTimer: null,
  lowDetailCache: null,
};

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
  atc: {
    bgTop: "#00150d", bgBottom: "#000805", grid: "rgba(0,255,128,0.12)",
    text: "#b8ffd9", dim: "rgba(120,255,180,0.46)", airport: "rgba(80,255,170,0.72)",
    runway: "rgba(120,255,180,0.36)", navaid: "rgba(0,220,255,0.64)",
    vector: "rgba(0,255,128,0.24)", land: "rgba(0,120,70,0.12)",
    aircraft: "#41ff78", selected: "#00e5ff", warning: "#ffee55", alert: "#ff4b4b",
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
  return palettes[state.data?.settings?.web?.visual_style || state.web?.visual_style || "current"] || palettes.current;
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
  const safe = Math.max(0, Math.round(sec));
  return `${safe}s`;
}

function unitConfig() {
  const web = state.data?.settings?.web || state.web || {};
  return {
    distance: web.unit_distance || "km",
    speed: web.unit_speed || "kt",
    altitude: web.unit_altitude || "ft",
    labelFields: Array.isArray(web.aircraft_label_fields) ? web.aircraft_label_fields : ["callsign", "altitude", "speed", "vs"],
    labelLines: Array.isArray(web.aircraft_label_lines) ? web.aircraft_label_lines : [["callsign"], ["altitude", "speed", "vs"]],
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
  if (unitConfig().altitude === "m") {
    return `${Math.abs(value * 0.00508).toFixed(1)}m/s`;
  }
  return `${Math.abs(value).toFixed(0)}fpm`;
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
    atc: "ATC",
  },
  "web.ils_style": {
    atc: "ATC",
    desktop: "Classic",
    minimal: "Minimal",
  },
  "web.aircraft_label_color": {
    aircraft: "By aircraft status",
    green: "Always green",
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
  "web.trajectory_display_mode": {
    altitude: "Altitude gradient",
    points: "Points",
  },
};

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

function buildAircraftLabelLines(ac, fields, lineConfig) {
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
    if (lines.length) return lines;
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
  return lines.slice(0, 4);
}

function resizeCanvas() {
  const rect = canvas.getBoundingClientRect();
  if (!rect.width || !rect.height) return;
  const ratio = window.devicePixelRatio || 1;
  state.pixelRatio = ratio;
  canvas.width = Math.max(1, Math.floor(rect.width * ratio));
  canvas.height = Math.max(1, Math.floor(rect.height * ratio));
  ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
  draw();
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
    const wait = 32 - (now - state.lastInteractiveDraw);
    if (wait > 0) {
      if (!state.interactiveDrawTimer) {
        state.interactiveDrawTimer = setTimeout(() => {
          state.interactiveDrawTimer = null;
          state.lastInteractiveDraw = performance.now();
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
  return { x, y, scale };
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

function drawBackground() {
  const rect = canvas.getBoundingClientRect();
  const w = rect.width;
  const h = rect.height;
  ctx.clearRect(0, 0, w, h);
  const p = palette();
  const gradient = ctx.createLinearGradient(0, 0, 0, h);
  gradient.addColorStop(0, p.bgTop);
  gradient.addColorStop(1, p.bgBottom);
  ctx.fillStyle = gradient;
  ctx.fillRect(0, 0, w, h);
  drawReferenceGrid(w, h, p);

  const userPoint = state.data ? project(state.data.settings.user.lat, state.data.settings.user.lon) : { x: w / 2, y: h / 2 };
  const radiusScale = Math.min(w, h) / (state.rangeKm * 2);
  if (state.data?.settings?.show_range_rings && userPoint) {
    ctx.strokeStyle = p.dim;
    const spacing = state.data.settings.range_ring_spacing_km || 18.52;
    const maxRings = Math.max(0, Number(state.data.settings.max_range_rings || 0));
    const ringCount = Math.min(Math.floor(state.rangeKm / spacing), maxRings);
    for (let i = 1; i <= ringCount; i += 1) {
      const km = i * spacing;
      ctx.beginPath();
      ctx.arc(userPoint.x, userPoint.y, km * radiusScale, 0, Math.PI * 2);
      ctx.stroke();
      ctx.fillStyle = p.dim;
      ctx.font = "12px ui-monospace, monospace";
      ctx.fillText(formatDistanceKm(km, km < 10 ? 1 : 0), userPoint.x + km * radiusScale + 4, userPoint.y - 4);
    }
  }
  if (state.data?.settings?.web?.show_event_range_ring && userPoint) {
    ctx.strokeStyle = p.warning;
    ctx.setLineDash([6, 5]);
    ctx.beginPath();
    ctx.arc(userPoint.x, userPoint.y, (state.data.settings.conflict_radius_km || 30) * radiusScale, 0, Math.PI * 2);
    ctx.stroke();
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

function drawGeodata() {
  const geo = state.data?.geodata;
  if (!geo) return;
  const p = palette();
  (geo.vectors || []).forEach((feature) => {
    const pts = (feature.points || []).map((pt) => project(pt[1], pt[0])).filter(Boolean);
    if (pts.length < 2) return;
    ctx.strokeStyle = feature.type === "polygon" ? p.land : p.vector;
    ctx.fillStyle = p.land;
    ctx.lineWidth = feature.layer?.includes("boundary") ? 1.4 : 1;
    ctx.beginPath();
    ctx.moveTo(pts[0].x, pts[0].y);
    pts.slice(1).forEach((point) => ctx.lineTo(point.x, point.y));
    if (feature.type === "polygon") {
      ctx.closePath();
      ctx.fill();
    }
    ctx.stroke();
  });
  ctx.lineWidth = 1;
  ctx.strokeStyle = p.runway;
  (geo.runways || []).forEach((rwy, index) => {
    const a = project(rwy.le_lat, rwy.le_lon);
    const b = project(rwy.he_lat, rwy.he_lon);
    if (!a || !b) return;
    rwy.__screen = { a, b, index };
    ctx.beginPath();
    ctx.moveTo(a.x, a.y);
    ctx.lineTo(b.x, b.y);
    ctx.stroke();
    if (state.rangeKm < 180) {
      drawRunwayEndLabels(rwy, a, b);
    }
  });
  drawGlideslopes();
  ctx.fillStyle = p.airport;
  (geo.airports || []).forEach((apt) => {
    const point = project(apt.lat, apt.lon);
    if (!point) return;
    ctx.fillRect(point.x - 2, point.y - 2, 4, 4);
    if (state.rangeKm < 180) {
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
    if (state.rangeKm < 220) {
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

function lowDetailRangeClass() {
  if (state.rangeKm > 320) return "far";
  if (state.rangeKm > 120) return "mid";
  return "near";
}

function lowDetailLayerStyle(feature, p) {
  const layer = feature.layer || "";
  if (layer.includes("coastline")) return { stroke: "rgba(56, 189, 248, 0.72)", fill: null, width: 1.1 };
  if (layer.includes("boundary")) return { stroke: "rgba(226, 232, 240, 0.45)", fill: null, width: 0.9 };
  if (layer.includes("lakes") || layer.includes("rivers")) return { stroke: "rgba(96, 165, 250, 0.58)", fill: "rgba(37, 99, 235, 0.13)", width: 0.9 };
  if (layer.includes("ocean")) return { stroke: "rgba(14, 165, 233, 0.32)", fill: "rgba(14, 116, 144, 0.10)", width: 0.8 };
  if (layer.includes("land") || layer.includes("countries")) return { stroke: "rgba(132, 204, 22, 0.30)", fill: "rgba(101, 163, 13, 0.08)", width: 0.8 };
  if (layer.includes("urban")) return { stroke: "rgba(248, 250, 252, 0.22)", fill: "rgba(248, 250, 252, 0.08)", width: 0.7 };
  return { stroke: feature.type === "polygon" ? p.land : p.vector, fill: feature.type === "polygon" ? "rgba(80, 110, 80, 0.07)" : null, width: 0.9 };
}

function buildLowDetailCache(geo, p, paletteKey) {
  const rangeClass = lowDetailRangeClass();
  const limits = {
    far: { maxFeatures: 120, maxPts: 24, minStride: 12, maxRunways: 80, maxAirports: 90, maxNavaids: 100 },
    mid: { maxFeatures: 160, maxPts: 32, minStride: 6, maxRunways: 110, maxAirports: 115, maxNavaids: 130 },
    near: { maxFeatures: 220, maxPts: 44, minStride: 4, maxRunways: 140, maxAirports: 150, maxNavaids: 170 },
  }[rangeClass];
  const vectors = [];
  for (const feature of geo.vectors || []) {
    if (vectors.length >= limits.maxFeatures) break;
    const source = feature.points || [];
    if (source.length < 2) continue;
    const stride = Math.max(2, Math.ceil(source.length / limits.maxPts), limits.minStride);
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
  const paletteKey = state.data?.settings?.web?.visual_style || state.web?.visual_style || "current";
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
  const geo = state.data?.geodata;
  if (!geo) return;
  const rect = canvas.getBoundingClientRect();
  const p = palette();
  const center = state.center || state.data.settings.center || state.data.settings.user;
  const latRad = (Math.PI / 180) * center.lat;
  const kmPerDegLat = 111.32;
  const kmPerDegLon = Math.max(8, 111.32 * Math.cos(latRad));
  const scale = Math.min(rect.width, rect.height) / (state.rangeKm * 2);
  const frameStart = performance.now();
  const frameBudgetMs = 5.0;
  const projectFast = (lat, lon) => ({
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
  ctx.globalAlpha = 0.74;
  for (const feature of cache.vectors) {
    if (performance.now() - frameStart > frameBudgetMs) break;
    const points = feature.points;
    if (points.length < 2) continue;
    const style = feature.style;
    ctx.strokeStyle = style.stroke;
    ctx.fillStyle = style.fill || style.stroke;
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
    if (!visible) continue;
    if (feature.type === "polygon") {
      ctx.closePath();
      if (style.fill) ctx.fill();
    }
    ctx.stroke();
  }

  if (state.rangeKm < 220) {
    ctx.strokeStyle = "rgba(229, 231, 235, 0.46)";
    ctx.lineWidth = 0.9;
    let runwayCount = 0;
    for (const rwy of cache.runways) {
      if (performance.now() - frameStart > frameBudgetMs + 1.5) break;
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
    if (performance.now() - frameStart > frameBudgetMs + 2.0) break;
    const point = projectFast(apt.lat, apt.lon);
    if (!inView(point, 20)) continue;
    ctx.fillRect(point.x - 1.5, point.y - 1.5, 3, 3);
    airportCount += 1;
  }

  ctx.strokeStyle = p.navaid;
  ctx.lineWidth = 1;
  let navaidCount = 0;
  for (const nav of cache.navaids) {
    if (performance.now() - frameStart > frameBudgetMs + 2.5) break;
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

function drawGlideslopes() {
  const p = palette();
  const style = state.data?.settings?.web?.ils_style || "atc";
  (state.data?.glideslopes || []).forEach((gs) => {
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

    if (style === "desktop") {
      const halfWidth = 5;
      ctx.save();
      ctx.lineWidth = 1.2;
      ctx.strokeStyle = p.dim;
      ctx.setLineDash([]);
      ctx.beginPath();
      ctx.moveTo(a.x + nx * halfWidth, a.y + ny * halfWidth);
      ctx.lineTo(b.x + nx * halfWidth, b.y + ny * halfWidth);
      ctx.moveTo(a.x - nx * halfWidth, a.y - ny * halfWidth);
      ctx.lineTo(b.x - nx * halfWidth, b.y - ny * halfWidth);
      ctx.stroke();
      ctx.strokeStyle = p.selected;
      ctx.lineWidth = 1.7;
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.stroke();
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
        ctx.beginPath();
        ctx.moveTo(x - nx * 3, y - ny * 3);
        ctx.lineTo(x + nx * 3, y + ny * 3);
        ctx.stroke();
      }
      ctx.restore();
      return;
    }

    ctx.strokeStyle = p.selected;
    ctx.lineWidth = 1.6;
    ctx.setLineDash([10, 6]);
    ctx.beginPath();
    ctx.moveTo(a.x, a.y);
    ctx.lineTo(b.x, b.y);
    ctx.stroke();
    const ticks = 5;
    for (let i = 1; i <= ticks; i += 1) {
      const t = i / ticks;
      const x = a.x + dx * t;
      const y = a.y + dy * t;
      ctx.beginPath();
      ctx.moveTo(x - nx * 5, y - ny * 5);
      ctx.lineTo(x + nx * 5, y + ny * 5);
      ctx.stroke();
    }
    ctx.setLineDash([]);
    ctx.fillStyle = p.selected;
    ctx.font = "11px ui-monospace, monospace";
    ctx.fillText(`${gs.airport} ${gs.runway_end_ident} ILS ${Number(gs.length_km / 1.852).toFixed(0)}NM`, b.x + 4, b.y - 4);
  });
  ctx.setLineDash([]);
}

function drawPolyline(points, color, width = 1) {
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
  const projected = points.map((pt) => ({ ...pt, screen: project(pt.lat, pt.lon) })).filter((pt) => pt.screen);
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

async function toggleGlideslope(runway, end) {
  const active = [...(state.web?.active_glideslopes || [])];
  const key = `${runway.airport}:${runway.runway_index}:${end}`;
  const next = active.filter((item) => `${item.airport}:${item.runway_index}:${item.end}` !== key);
  if (next.length === active.length) {
    next.push({ airport: runway.airport, runway_index: runway.runway_index, end });
  }
  const res = await fetch("/api/config", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ web: { active_glideslopes: next } }),
  });
  const payload = await res.json();
  if (!payload.ok) throw new Error(payload.error || "Could not update ILS");
  state.web = payload.web;
  await fetchState();
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
  (state.data?.transits || []).forEach((tr) => {
    const poly = (tr.polygon || []).map((pt) => project(pt[0], pt[1])).filter(Boolean);
    if (poly.length > 2) {
      ctx.fillStyle = tr.body === "sun" ? "rgba(251,146,60,0.22)" : "rgba(147,197,253,0.20)";
      ctx.strokeStyle = tr.body === "sun" ? "rgba(251,146,60,0.72)" : "rgba(147,197,253,0.70)";
      ctx.beginPath();
      ctx.moveTo(poly[0].x, poly[0].y);
      poly.slice(1).forEach((p) => ctx.lineTo(p.x, p.y));
      ctx.closePath();
      ctx.fill();
      ctx.stroke();
    }
    const color = tr.body === "sun" ? "rgba(251,146,60,0.95)" : "rgba(147,197,253,0.95)";
    drawPolyline((tr.centerline || []).map((pt) => ({ lat: pt[0], lon: pt[1] })), color, 1.5);
  });
}

function drawEvents() {
  if (!state.data?.settings?.show_events) return;
  (state.data?.events || []).forEach((ev) => {
    if (ev.lat === null || ev.lon === null) return;
    const p = project(ev.lat, ev.lon);
    if (!p) return;
    ctx.strokeStyle = ev.type === "AC-Sun" ? "#fb923c" : ev.type === "AC-Moon" ? "#93c5fd" : "#facc15";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(p.x - 6, p.y - 6);
    ctx.lineTo(p.x + 6, p.y + 6);
    ctx.moveTo(p.x + 6, p.y - 6);
    ctx.lineTo(p.x - 6, p.y + 6);
    ctx.stroke();
  });
}

function wrapAzimuthDelta(az, centerAz) {
  let delta = az - centerAz;
  if (delta > 180) delta -= 360;
  if (delta < -180) delta += 360;
  return delta;
}

function drawPovBox(ev, anchor) {
  const pov = ev.pov || {};
  if (!pov.valid) return;
  const rect = canvas.getBoundingClientRect();
  const pal = palette();
  const size = Math.min(170, Math.max(128, Math.min(rect.width, rect.height) * 0.22));
  const half = size / 2;
  let x = anchor.x + 56;
  let y = anchor.y - 72;
  if (x + size + 8 > rect.width) x = anchor.x - size - 18;
  if (y < 8) y = anchor.y + 18;
  if (y + size + 8 > rect.height) y = rect.height - size - 8;
  if (x < 8) x = 8;

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
    const bodyRadiusDeg = (ev.type === "AC-Sun" ? 0.53 : 0.5) / 2;
    ctx.fillStyle = ev.type === "AC-Sun" ? "rgba(255, 230, 90, 0.92)" : "rgba(220, 226, 235, 0.9)";
    ctx.beginPath();
    ctx.arc(body.x, body.y, Math.max(5, bodyRadiusDeg * scale), 0, Math.PI * 2);
    ctx.fill();
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
  }
  ctx.restore();

  ctx.strokeStyle = ev.type === "AC-Sun" ? "#fb923c" : ev.type === "AC-Moon" ? "#d1d5db" : pal.warning;
  ctx.lineWidth = 1.2;
  ctx.strokeRect(x, y, size, size);
  ctx.fillStyle = pal.text;
  ctx.font = "11px ui-monospace, monospace";
  ctx.fillText("POV", x + 6, y + 14);
  ctx.fillStyle = pal.dim;
  ctx.fillText(`FOV ${fovDeg.toFixed(1)} deg`, x + 6, y + size - 8);
  ctx.restore();
}

function drawEventPovPreview() {
  const events = (state.data?.events || []).filter((ev) => ev.pov?.valid && ev.lat !== null && ev.lon !== null);
  if (!events.length) return;
  const selectedEvent = events.find((ev) => state.selected && (ev.icaos || []).includes(state.selected)) || events[0];
  const anchor = project(selectedEvent.lat, selectedEvent.lon);
  if (anchor) drawPovBox(selectedEvent, anchor);
}

function intersectsAnyLabel(box, boxes) {
  return boxes.some((other) => (
    box.x < other.x + other.w &&
    box.x + box.w > other.x &&
    box.y < other.y + other.h &&
    box.y + box.h > other.y
  ));
}

function placeLabel(anchor, width, height, boxes) {
  const offsets = [
    { x: 10, y: -8 },
    { x: 10, y: 14 },
    { x: -width - 10, y: -8 },
    { x: -width - 10, y: 14 },
    { x: 14, y: -2 },
    { x: -width - 14, y: -2 },
  ];
  for (const offset of offsets) {
    const box = {
      x: anchor.x + offset.x - 2,
      y: anchor.y + offset.y - 12,
      w: width + 6,
      h: height + 6,
      textX: anchor.x + offset.x,
      textY: anchor.y + offset.y,
    };
    if (!intersectsAnyLabel(box, boxes)) return box;
  }
  return {
    x: anchor.x + 8,
    y: anchor.y - 20,
    w: width + 6,
    h: height + 6,
    textX: anchor.x + 10,
    textY: anchor.y - 8,
  };
}

function drawAircraft(options = {}) {
  const aircraft = state.data?.aircraft || [];
  const units = unitConfig();
  const interactive = Boolean(options.interactive);
  const labelBoxes = [];
  const orderedAircraft = [...aircraft].sort((a, b) => {
    const priority = (ac) => (state.selected === ac.icao ? 0 : ac.conflict ? 1 : ac.has_event ? 2 : 3);
    return priority(a) - priority(b);
  });
  orderedAircraft.forEach((ac) => {
    if (!ac.visible || ac.lat === null || ac.lon === null) return;
    const p = project(ac.lat, ac.lon);
    if (!p) return;
    const selected = state.selected === ac.icao;
    const pal = palette();
    const color = ac.conflict ? pal.alert : ac.has_event ? pal.warning : selected ? pal.selected : pal.aircraft;
    if (!interactive && state.data.settings.show_history) {
      drawAltitudePath(ac.history || [], color);
    }
    if (!interactive && state.data.settings.show_velocity_vector) {
      drawPolyline(ac.path || [], "#2f80ff", selected ? 1.4 : 1.0);
    }

    ctx.fillStyle = color;
    ctx.fillRect(p.x - 4, p.y - 4, 8, 8);

    if (selected || ac.has_event || ac.conflict) {
      ctx.strokeStyle = ac.has_event || ac.conflict ? pal.alert : pal.text;
      ctx.lineWidth = ac.has_event || ac.conflict ? 2 : 1.5;
      ctx.beginPath();
      ctx.arc(p.x, p.y, 12, 0, Math.PI * 2);
      ctx.stroke();
    }

    const labelParts = buildAircraftLabelLines(ac, units.labelFields, units.labelLines);
    const labelColor = state.data.settings.web?.aircraft_label_color === "green" ? "#4ade80" : color;
    ctx.font = "12px ui-monospace, monospace";
    const labelWidth = Math.max(...labelParts.map((line) => ctx.measureText(line).width), 0);
    const labelBox = placeLabel(p, labelWidth, labelParts.length * 12, labelBoxes);
    labelBoxes.push(labelBox);
    ctx.fillStyle = labelColor;
    labelParts.forEach((line, index) => {
      ctx.fillText(line, labelBox.textX, labelBox.textY + index * 12);
    });
  });
}

function draw(options = {}) {
  const interactive = Boolean(options.interactive);
  drawBackground();
  if (!state.data) return;
  if (interactive) {
    drawGeodataLowDetail();
    drawAircraft({ interactive: true });
    drawPanFeedback();
    return;
  }
  drawGeodata();
  drawTransits();
  drawEvents();
  drawAircraft();
  drawEventPovPreview();
}

function updateStatus() {
  const data = state.data;
  if (!data) return;
  const units = unitConfig();
  els.connBadge.textContent = data.settings.connected ? "Online" : "Offline";
  els.connBadge.classList.toggle("online", data.settings.connected);
  els.clockLine.textContent = new Date(data.server_time).toLocaleString();
  els.activeCount.textContent = data.counts.active_total;
  els.displayedCount.textContent = data.counts.displayed;
  els.eventCount.textContent = data.counts.events;
  els.scaleChip.textContent = `${formatDistanceKm(state.rangeKm, state.rangeKm < 10 ? 1 : 0)} range`;

  const celestial = data.celestial;
  const rows = [
    ["Dump1090", `${data.settings.dump1090_host}:${data.settings.dump1090_port}`],
    ["Observer", `${fmtNum(data.settings.user.lat, 4)}, ${fmtNum(data.settings.user.lon, 4)}`],
    ["Altitude", formatAltitudeM(data.settings.user.alt_m, 0)],
    ["Conflict Angle", fmtNum(data.settings.conflict_angle_deg, 1, "deg")],
    ["Prediction", fmtNum(data.settings.prediction_horizon_sec, 0, "s")],
  ];
  if (celestial) {
    rows.push(["Sun", `Az ${fmtNum(celestial.sun.az, 1)} El ${fmtNum(celestial.sun.el, 1)}`]);
    rows.push(["Moon", `Az ${fmtNum(celestial.moon.az, 1)} El ${fmtNum(celestial.moon.el, 1)}`]);
  }
  els.statusList.innerHTML = rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("");
}

function updateSelected() {
  const ac = (state.data?.aircraft || []).find((item) => item.icao === state.selected);
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
  if (!events.length) {
    els.eventsList.className = "list empty";
    els.eventsList.textContent = "None";
    return;
  }
  els.eventsList.className = "list";
  els.eventsList.innerHTML = events.slice(0, 8).map((ev) => {
    const calls = (ev.callsigns || []).join(" / ") || "--";
    const pov = ev.pov?.valid ? " POV" : "";
    return `<div class="event-row"><b>${ev.type}${pov}</b><span>${calls}</span><span>${fmtEta(ev.eta_sec)}</span></div>`;
  }).join("");
}

function updateTraffic() {
  const aircraft = state.data?.aircraft || [];
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

function refreshUi() {
  document.body.dataset.style = state.data?.settings?.web?.visual_style || "current";
  updateStatus();
  updateSelected();
  updateEvents();
  updateTraffic();
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
  return (state.data?.aircraft || []).find((ac) => ac.callsign) || (state.data?.aircraft || [])[0] || {
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
  updateLabelBuilderButtons(builder);
  updateLabelPreview();
}

async function openSettings() {
  const res = await fetch("/api/config", { cache: "no-store" });
  const payload = await res.json();
  const cfg = payload.config;
  const web = payload.web;
  const opt = payload.options;
  els.settingsMessage.textContent = "";
  els.settingsBody.innerHTML = `
    <section class="settings-group">
      <h2>Map Display</h2>
      <div class="settings-grid">
        ${selectField("web.visual_style", "Theme", web.visual_style, opt.visual_styles)}
        ${selectField("web.aircraft_label_color", "Label color", web.aircraft_label_color, opt.aircraft_label_colors)}
        ${selectField("web.ils_style", "ILS appearance", web.ils_style, opt.ils_styles)}
        ${selectField("web.ils_length_nm", "ILS length", web.ils_length_nm, opt.ils_lengths_nm)}
      </div>
      <div class="check-list">
        ${checkbox("web.show_geo_vectors", "Geographic vector layers", web.show_geo_vectors)}
        ${checkbox("web.show_event_range_ring", "Event range ring", web.show_event_range_ring)}
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
        ${selectField("range_ring_spacing_nm_str", "Range ring spacing", cfg.range_ring_spacing_nm_str, opt.range_ring_spacing_nm)}
        ${field("max_range_rings", "Max Range Rings", cfg.max_range_rings, "number", "1")}
        ${selectField("web.trajectory_minutes", "Track duration", web.trajectory_minutes, opt.trajectory_minutes)}
        ${selectField("velocity_vector_minutes", "Speed vector length", cfg.velocity_vector_minutes, opt.velocity_vector_minutes)}
        ${selectField("web.trajectory_display_mode", "History style", web.trajectory_display_mode, opt.trajectory_display_modes)}
      </div>
      <div class="check-list">
        ${checkbox("show_history", "Aircraft history", cfg.show_history)}
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
  els.settingsMessage.textContent = "Saved";
  state.rangeKm = Math.max(1, Number(payload.config.conflict_radius_km || state.rangeKm) * 2);
  state.web = payload.web || state.web;
  await fetchState();
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
      if (coords.altitude === null) {
        els.settingsMessage.textContent = "GPS filled lat/lon; altitude unavailable.";
      } else {
        els.settingsMessage.textContent = "GPS filled.";
      }
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
  if (loc.alt_m === null || loc.alt_m === undefined) {
    els.settingsMessage.textContent = `Windows Location filled lat/lon${acc}; altitude unavailable.`;
  } else {
    els.settingsMessage.textContent = `Windows Location filled${acc}.`;
  }
}

async function fetchState() {
  if (state.fetchTimer) {
    clearTimeout(state.fetchTimer);
    state.fetchTimer = null;
  }
  if (state.dragging || state.touchStartDistance) {
    state.pendingFetch = true;
    return;
  }
  if (state.fetchInFlight) {
    state.pendingFetch = true;
    return;
  }
  state.fetchInFlight = true;
  const params = new URLSearchParams({
    range_km: state.rangeKm,
    selected: state.selected,
    transits: state.transits,
    center_lat: state.center?.lat ?? "",
    center_lon: state.center?.lon ?? "",
  });
  try {
    const res = await fetch(`/api/state?${params.toString()}`, { cache: "no-store" });
    if (!res.ok) throw new Error(`state request failed: ${res.status}`);
    state.data = await res.json();
    state.lowDetailCache = null;
    state.web = state.data.settings.web;
    if (!state.center) state.center = state.data.settings.center || state.data.settings.user;
    if (!state.dragging) refreshUi();
  } finally {
    state.fetchInFlight = false;
    if (state.pendingFetch && !state.dragging) {
      state.pendingFetch = false;
      fetchState().catch(console.error);
    }
  }
}

function requestStateFetch(delay = 0) {
  if (state.fetchTimer) clearTimeout(state.fetchTimer);
  state.fetchTimer = setTimeout(() => {
    state.fetchTimer = null;
    fetchState().catch(console.error);
  }, delay);
}

function selectNearestAircraft(event) {
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
  (data.aircraft || []).forEach((ac) => {
    if (!ac.visible || ac.lat === null || ac.lon === null) return;
    const p = project(ac.lat, ac.lon);
    if (!p) return;
    const d = Math.hypot(p.x - click.x, p.y - click.y);
    if (d < bestDist) {
      best = ac;
      bestDist = d;
    }
  });
  if (best) {
    state.selected = best.icao;
    fetchState().catch(console.error);
  } else if (state.selected) {
    state.selected = "";
    fetchState().catch(console.error);
  }
}

document.getElementById("zoomIn").addEventListener("click", () => {
  state.rangeKm = Math.max(1, state.rangeKm / 1.25);
  fetchState().catch(console.error);
});

document.getElementById("zoomOut").addEventListener("click", () => {
  state.rangeKm = Math.min(1000, state.rangeKm * 1.25);
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
  fetchState().catch(console.error);
});

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
  requestStateFetch(140);
}, { passive: false });

canvas.addEventListener("pointerdown", (event) => {
  state.dragging = true;
  state.dragStart = { x: event.clientX, y: event.clientY, center: { ...(state.center || state.data?.settings?.user) } };
  canvas.classList.add("dragging");
  canvas.setPointerCapture(event.pointerId);
});

canvas.addEventListener("pointermove", (event) => {
  if (!state.dragging || !state.dragStart || !state.data) return;
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
  if (!state.dragging) return;
  state.dragging = false;
  state.dragStart = null;
  if (state.interactiveDrawTimer) {
    clearTimeout(state.interactiveDrawTimer);
    state.interactiveDrawTimer = null;
  }
  canvas.classList.remove("dragging");
  try { canvas.releasePointerCapture(event.pointerId); } catch {}
  fetchState().catch(console.error);
});

canvas.addEventListener("touchstart", (event) => {
  if (event.touches.length === 2) {
    state.touchStartDistance = Math.hypot(
      event.touches[0].clientX - event.touches[1].clientX,
      event.touches[0].clientY - event.touches[1].clientY,
    );
  }
}, { passive: true });

canvas.addEventListener("touchmove", (event) => {
  if (event.touches.length !== 2 || !state.touchStartDistance) return;
  event.preventDefault();
  const dist = Math.hypot(
    event.touches[0].clientX - event.touches[1].clientX,
    event.touches[0].clientY - event.touches[1].clientY,
  );
  const ratio = state.touchStartDistance / Math.max(1, dist);
  state.rangeKm = Math.max(1, Math.min(1000, state.rangeKm * ratio));
  state.suppressClick = true;
  state.touchStartDistance = dist;
  requestDraw(true);
}, { passive: false });

canvas.addEventListener("touchend", () => {
  state.touchStartDistance = 0;
  if (state.interactiveDrawTimer) {
    clearTimeout(state.interactiveDrawTimer);
    state.interactiveDrawTimer = null;
  }
  fetchState().catch(console.error);
});

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
});
window.visualViewport?.addEventListener("resize", () => {
  setAppHeight();
  scheduleResize();
});
window.visualViewport?.addEventListener("scroll", () => {
  setAppHeight();
  scheduleResize();
});
resizeCanvas();
fetchState().catch(console.error);
setInterval(() => fetchState().catch(console.error), 1000);
