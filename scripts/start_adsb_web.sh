#!/usr/bin/env bash
set -euo pipefail

SCRIPT_PATH="${BASH_SOURCE[0]}"
if command -v readlink >/dev/null 2>&1; then
  SCRIPT_PATH="$(readlink -f "${SCRIPT_PATH}")"
fi
ROOT_DIR="$(cd "$(dirname "${SCRIPT_PATH}")/.." && pwd)"
POWERSHELL="${POWERSHELL:-/mnt/c/Windows/System32/WindowsPowerShell/v1.0/powershell.exe}"
BUSID="${ADSB_USB_BUSID:-}"
WEB_HOST="${ADSB_WEB_HOST:-0.0.0.0}"
WEB_PORT="${ADSB_WEB_PORT:-8090}"
HTTPS="${ADSB_HTTPS:-1}"
SBS_PORT="${ADSB_SBS_PORT:-30003}"
GAIN="${ADSB_GAIN:--10}"
DEVICE_INDEX="${ADSB_DEVICE_INDEX:-0}"
DUMP1090_CMD="${DUMP1090_CMD:-}"
PYTHON_BIN="${ADSB_PYTHON:-python}"
DUMP1090_PID=""
WEB_PID=""

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
Usage: adsb-web

Starts the ADS-B receiver stack:
  1. Attach RTL-SDR from Windows to WSL with usbipd
  2. Start dump1090/dump1090-mutability with auto-gain
  3. Start ADS-B Transit Web UI

Environment overrides:
  ADSB_USB_BUSID=<busid>   USBIPD BUSID for RTL-SDR; required for automatic WSL attach
  ADSB_WEB_HOST=0.0.0.0    Web UI bind address
  ADSB_WEB_PORT=8090       Web UI port
  ADSB_HTTPS=1             Use HTTPS with a local self-signed certificate
  ADSB_SBS_PORT=30003      dump1090 SBS output port
  ADSB_GAIN=-10            dump1090 gain; -10 means auto-gain
  ADSB_DEVICE_INDEX=0      RTL-SDR device index
  ADSB_SKIP_USBIPD=1       Skip usbipd attach
  ADSB_NO_SUDO=1           Start dump1090 without sudo
  ADSB_RESTART=1           Stop existing listeners on Web/SBS ports before starting
EOF
  exit 0
fi

cleanup() {
  if [[ -n "${WEB_PID}" ]] && kill -0 "${WEB_PID}" 2>/dev/null; then
    echo "[adsb] Stopping Web UI (${WEB_PID})"
    kill "${WEB_PID}" 2>/dev/null || true
  fi
  if [[ -n "${DUMP1090_PID}" ]] && kill -0 "${DUMP1090_PID}" 2>/dev/null; then
    echo "[adsb] Stopping dump1090 (${DUMP1090_PID})"
    sudo -n kill "${DUMP1090_PID}" 2>/dev/null || kill "${DUMP1090_PID}" 2>/dev/null || true
  fi
}
trap cleanup EXIT INT TERM

port_pids() {
  local port="$1"
  ss -H -ltnp "( sport = :${port} )" 2>/dev/null \
    | sed -n 's/.*pid=\([0-9]\+\).*/\1/p' \
    | sort -u
}

stop_port_listeners() {
  local port="$1"
  local label="$2"
  local pids
  pids="$(port_pids "${port}")"
  if [[ -z "${pids}" ]]; then
    return 0
  fi
  if [[ "${ADSB_RESTART:-0}" != "1" ]]; then
    echo "[adsb] ${label} port ${port} is already in use by PID(s): ${pids//$'\n'/ }" >&2
    echo "[adsb] Stop the old process or run ADSB_RESTART=1 adsb-web" >&2
    exit 1
  fi
  echo "[adsb] Stopping existing ${label} listener(s) on port ${port}: ${pids//$'\n'/ }"
  while read -r pid; do
    [[ -n "${pid}" ]] && kill "${pid}" 2>/dev/null || true
  done <<<"${pids}"
  sleep 1
}

dump1090_pids() {
  ps -eo pid=,cmd= \
    | awk -v port="${SBS_PORT}" '/dump1090/ && $0 ~ "--net-sbs-port " port {print $1}' \
    | sort -u
}

stop_dump1090_for_restart() {
  local pids
  pids="$(dump1090_pids)"
  if [[ -z "${pids}" ]]; then
    return 0
  fi
  echo "[adsb] Stopping existing dump1090 process(es) on SBS port ${SBS_PORT}: ${pids//$'\n'/ }"
  while read -r pid; do
    [[ -n "${pid}" ]] && sudo -n kill "${pid}" 2>/dev/null || kill "${pid}" 2>/dev/null || true
  done <<<"${pids}"
  sleep 1
}

detect_rtlsdr_busid() {
  local output detected
  output="$("${POWERSHELL}" -NoProfile -Command "usbipd list" 2>/dev/null)" || return 0
  detected="$(
    awk '
      BEGIN { IGNORECASE = 1 }
      /^[[:space:]]*[0-9]+-[0-9]+[[:space:]]/ &&
      ($0 ~ /0bda:2838|0bda:2832|RTL2838|RTL-SDR|Bulk-In/) {
        print $1
        exit
      }
    ' <<<"${output}" | tr -d '\r'
  )"
  [[ -n "${detected}" ]] && echo "${detected}"
}

stop_port_listeners "${WEB_PORT}" "Web UI"

if [[ -x "${POWERSHELL}" && -z "${BUSID}" && "${ADSB_SKIP_USBIPD:-0}" != "1" ]]; then
  BUSID="$(detect_rtlsdr_busid)"
  if [[ -n "${BUSID}" ]]; then
    echo "[adsb] Auto-detected RTL-SDR USB BUSID ${BUSID}"
  fi
fi

if [[ -x "${POWERSHELL}" && -n "${BUSID}" && "${ADSB_SKIP_USBIPD:-0}" != "1" ]]; then
  echo "[adsb] Attaching USB BUSID ${BUSID} to WSL via usbipd"
  USBIPD_STATUS=0
  USBIPD_OUTPUT="$("${POWERSHELL}" -NoProfile -Command "usbipd attach --wsl --busid ${BUSID}" 2>&1)" || USBIPD_STATUS=$?
  if [[ "${USBIPD_STATUS}" != "0" ]]; then
    if grep -qi "already attached" <<<"${USBIPD_OUTPUT}"; then
      echo "[adsb] USB BUSID ${BUSID} is already attached to WSL"
    else
      echo "${USBIPD_OUTPUT}" >&2
    fi
  elif [[ -n "${USBIPD_OUTPUT}" ]]; then
    echo "${USBIPD_OUTPUT}"
  fi
elif [[ -x "${POWERSHELL}" && "${ADSB_SKIP_USBIPD:-0}" != "1" ]]; then
  echo "[adsb] ADSB_USB_BUSID is not set; skipping usbipd attach"
fi

if [[ -z "${DUMP1090_CMD}" ]]; then
  if command -v dump1090-mutability >/dev/null 2>&1; then
    DUMP1090_CMD="dump1090-mutability"
  elif command -v dump1090 >/dev/null 2>&1; then
    DUMP1090_CMD="dump1090"
  else
    echo "[adsb] dump1090-mutability or dump1090 was not found in PATH" >&2
    exit 1
  fi
fi

if [[ "${ADSB_RESTART:-0}" == "1" ]]; then
  stop_dump1090_for_restart
fi

if ss -ltn "( sport = :${SBS_PORT} )" | grep -q ":${SBS_PORT}"; then
  echo "[adsb] SBS port ${SBS_PORT} is already listening; leaving existing decoder running"
else
  echo "[adsb] Starting ${DUMP1090_CMD} with gain ${GAIN} (-10 means auto-gain)"
  if [[ "${ADSB_NO_SUDO:-0}" == "1" ]]; then
    DUMP1090_PREFIX=()
  else
    echo "[adsb] Requesting sudo for RTL-SDR access"
    if [[ -r /dev/tty ]]; then
      sudo -v </dev/tty
    else
      sudo -v
    fi
    DUMP1090_PREFIX=(sudo -n)
  fi
  "${DUMP1090_PREFIX[@]}" "${DUMP1090_CMD}" \
    --device-index "${DEVICE_INDEX}" \
    --gain "${GAIN}" \
    --net \
    --net-bind-address 127.0.0.1 \
    --net-sbs-port "${SBS_PORT}" \
    --quiet &
  DUMP1090_PID="$!"
  sleep 2
fi

echo "[adsb] Starting ADS-B Transit Web UI on ${WEB_HOST}:${WEB_PORT}"
cd "${ROOT_DIR}"
if [[ -x "${ROOT_DIR}/.venv/bin/python" && "${ADSB_PYTHON:-}" == "" ]]; then
  PYTHON_BIN="${ROOT_DIR}/.venv/bin/python"
fi
SERVER_ARGS=(web_ui/server.py --host "${WEB_HOST}" --port "${WEB_PORT}")
if [[ "${HTTPS}" == "1" ]]; then
  SERVER_ARGS+=(--https)
fi
"${PYTHON_BIN}" "${SERVER_ARGS[@]}" &
WEB_PID="$!"
wait "${WEB_PID}"
