#!/usr/bin/env bash
set -euo pipefail

SCRIPT_PATH="${BASH_SOURCE[0]}"
if command -v readlink >/dev/null 2>&1; then
  SCRIPT_PATH="$(readlink -f "${SCRIPT_PATH}")"
fi
ROOT_DIR="$(cd "$(dirname "${SCRIPT_PATH}")/.." && pwd)"
export PATH="${HOME}/.local/bin:${PATH}"
CONFIG_FILE="${ADSB_ENV_FILE:-${XDG_CONFIG_HOME:-${HOME}/.config}/adsb-transit/adsb-web.env}"
if [[ -f "${CONFIG_FILE}" ]]; then
  declare -A ADSB_ENV_OVERRIDES=()
  for name in \
    ADSB_USB_BUSID ADSB_WEB_HOST ADSB_WEB_PORT ADSB_HTTPS ADSB_SBS_PORT \
    ADSB_GAIN ADSB_DEVICE_INDEX DUMP1090_CMD ADSB_DECODER_MODE \
    ADSB_DECODER_CMD ADSB_DECODER_WATCHDOG_SEC ADSB_WSL_DISTRO \
    ADSB_USB_MATCH_REGEX ADSB_PYTHON ADSB_SKIP_USBIPD ADSB_NO_SUDO \
    ADSB_RESTART ADSB_DUMP1090_JSON_URL ADSB_DUMP1090_JSON_DIR \
    ADSB_DUMP1090_JSON_INTERVAL_SEC; do
    if [[ "${!name+x}" == "x" ]]; then
      ADSB_ENV_OVERRIDES["${name}"]="${!name}"
    fi
  done
  set -a
  # shellcheck disable=SC1090
  source "${CONFIG_FILE}"
  set +a
  for name in "${!ADSB_ENV_OVERRIDES[@]}"; do
    printf -v "${name}" "%s" "${ADSB_ENV_OVERRIDES[${name}]}"
    export "${name}"
  done
fi
POWERSHELL="${POWERSHELL:-/mnt/c/Windows/System32/WindowsPowerShell/v1.0/powershell.exe}"
IS_WSL=0
if [[ -r /proc/sys/kernel/osrelease ]] && grep -qiE 'microsoft|wsl' /proc/sys/kernel/osrelease; then
  IS_WSL=1
fi
BUSID="${ADSB_USB_BUSID:-}"
WEB_HOST="${ADSB_WEB_HOST:-127.0.0.1}"
WEB_PORT="${ADSB_WEB_PORT:-8090}"
HTTPS="${ADSB_HTTPS:-1}"
SBS_PORT="${ADSB_SBS_PORT:-30003}"
GAIN="${ADSB_GAIN:--10}"
DEVICE_INDEX="${ADSB_DEVICE_INDEX:-0}"
DUMP1090_CMD="${DUMP1090_CMD:-}"
if [[ -n "${DUMP1090_CMD}" && "${DUMP1090_CMD}" != */* ]] && command -v "${DUMP1090_CMD}" >/dev/null 2>&1; then
  DUMP1090_CMD="$(command -v "${DUMP1090_CMD}")"
fi
JSON_DIR="${ADSB_DUMP1090_JSON_DIR:-${XDG_RUNTIME_DIR:-/tmp}/adsb-transit-dump1090-json}"
DECODER_MODE="${ADSB_DECODER_MODE:-auto}"
DECODER_CMD="${ADSB_DECODER_CMD:-}"
DECODER_WATCHDOG_SEC="${ADSB_DECODER_WATCHDOG_SEC:-180}"
WSL_DISTRO="${ADSB_WSL_DISTRO:-}"
USB_MATCH_REGEX="${ADSB_USB_MATCH_REGEX:-0bda:2838|0bda:2832|RTL2838|RTL-SDR|Bulk-In|Airspy|SDRplay|RSP|HackRF|Mode-S Beast|FlightAware|Pro Stick}"
PYTHON_BIN="${ADSB_PYTHON:-python}"
DUMP1090_PID=""
WEB_PID=""
WATCHDOG_PID=""

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
Usage: adsb-web

Starts the ADS-B receiver stack:
  1. On WSL only, optionally attach an SDR from Windows with usbipd
  2. Use an existing SBS/BaseStation feed, or start a local ADS-B decoder
  3. Start ADS-B Transit Web UI

Environment overrides:
  ADSB_USB_BUSID=<busid>   WSL-only USBIPD BUSID for SDR; native Linux ignores this
  ADSB_USB_MATCH_REGEX=... WSL-only usbipd list regex used for SDR auto-detection
  ADSB_WEB_HOST=127.0.0.1
                            Web UI bind address
  ADSB_WEB_PORT=8090       Web UI port
  ADSB_HTTPS=1             Use HTTPS with a local self-signed certificate
  ADSB_SBS_PORT=30003      dump1090 SBS output port
  ADSB_GAIN=-10            dump1090 gain; -10 means auto-gain
  ADSB_DEVICE_INDEX=0      RTL-SDR device index
  ADSB_DECODER_MODE=auto   auto, managed, external, or none
  ADSB_DECODER_CMD='...'   Custom decoder command; must provide SBS on ADSB_SBS_PORT
  ADSB_DUMP1090_JSON_URL=  Optional dump1090-fa/readsb aircraft.json URL.
                            Used only when GPS altitude correction is enabled
                            in the Web UI developer settings.
                            Examples: http://127.0.0.1/dump1090-fa/data/aircraft.json
                                      http://127.0.0.1:8080/data/aircraft.json
                                      file:///tmp/adsb-transit-dump1090-json/aircraft.json
  ADSB_DUMP1090_JSON_DIR=/tmp/adsb-transit-dump1090-json
                            Local JSON directory used when managed dump1090-fa runs
  ADSB_DUMP1090_JSON_INTERVAL_SEC=1
                            Poll interval for the optional JSON feed
  ADSB_DECODER_WATCHDOG_SEC=180
                            Restart locally managed decoder after this many seconds
                            without SBS messages; set 0 to disable
  ADSB_WSL_DISTRO=Ubuntu    WSL distro name used by Windows controller to start
                            the local decoder as WSL root without a sudo prompt
  ADSB_ENV_FILE=...        Config file to load before reading these variables
  ADSB_SKIP_USBIPD=1       Skip usbipd attach
  ADSB_NO_SUDO=1           Start dump1090 without sudo
  ADSB_RESTART=1           Stop existing listeners on Web/SBS ports before starting

Examples:
  ADSB_DECODER_MODE=external adsb-web
  ADSB_DECODER_CMD='readsb --device-type airspy --net --net-sbs-port 30003' adsb-web
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
  if [[ -n "${WATCHDOG_PID}" ]] && kill -0 "${WATCHDOG_PID}" 2>/dev/null; then
    kill "${WATCHDOG_PID}" 2>/dev/null || true
  fi
}
trap cleanup EXIT INT TERM

port_pids() {
  local port="$1"
  {
    ss -H -ltnp "( sport = :${port} )" 2>/dev/null \
      | sed -n 's/.*pid=\([0-9]\+\).*/\1/p' || true
    if command -v fuser >/dev/null 2>&1; then
      fuser -n tcp "${port}" 2>/dev/null | tr ' ' '\n' || true
    fi
    if command -v lsof >/dev/null 2>&1; then
      lsof -tiTCP:"${port}" -sTCP:LISTEN 2>/dev/null || true
    fi
  } | sed '/^[[:space:]]*$/d' | sort -u
}

sbs_port_listening() {
  ss -ltn "( sport = :${SBS_PORT} )" 2>/dev/null | grep -q ":${SBS_PORT}"
}

kill_pid() {
  local pid="$1"
  local signal="${2:-TERM}"
  kill "-${signal}" "${pid}" 2>/dev/null || sudo -n kill "-${signal}" "${pid}" 2>/dev/null || true
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
    [[ -n "${pid}" ]] && kill_pid "${pid}" TERM
  done <<<"${pids}"
  sleep 1
  pids="$(port_pids "${port}")"
  if [[ -n "${pids}" ]]; then
    echo "[adsb] Force-stopping stubborn ${label} listener(s) on port ${port}: ${pids//$'\n'/ }"
    while read -r pid; do
      [[ -n "${pid}" ]] && kill_pid "${pid}" KILL
    done <<<"${pids}"
    sleep 0.5
  fi
  pids="$(port_pids "${port}")"
  if [[ -n "${pids}" ]]; then
    echo "[adsb] Could not free ${label} port ${port}; still held by PID(s): ${pids//$'\n'/ }" >&2
    exit 1
  fi
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

is_dump1090_fa_cmd() {
  [[ "$(basename "${DUMP1090_CMD}")" == "dump1090-fa" ]]
}

grant_wsl_usb_permissions() {
  if [[ -z "${WSL_DISTRO}" || ! -x "${POWERSHELL}" ]]; then
    return 1
  fi
  if [[ ! "${WSL_DISTRO}" =~ ^[A-Za-z0-9_.-]+$ ]]; then
    echo "[adsb] WSL distro name '${WSL_DISTRO}' contains unsupported characters; cannot adjust USB permissions as WSL root" >&2
    return 1
  fi
  echo "[adsb] Granting WSL USB device access via root in distro ${WSL_DISTRO}"
  local output status
  status=0
  output="$("${POWERSHELL}" -NoProfile -WindowStyle Hidden -Command "wsl.exe -d ${WSL_DISTRO} -u root -- bash -lc 'chmod -R a+rw /dev/bus/usb 2>/dev/null || true; test -r /dev/bus/usb'" 2>&1)" || status=$?
  if [[ "${status}" != "0" ]]; then
    echo "${output}" >&2
    return 1
  fi
  return 0
}

start_decoder_process() {
  if [[ "${DECODER_MODE}" == "none" || "${DECODER_MODE}" == "external" ]]; then
    return 0
  fi
  if sbs_port_listening; then
    echo "[adsb] SBS port ${SBS_PORT} is already listening; leaving existing decoder running"
    DUMP1090_PID=""
    return 0
  fi
  if [[ -n "${DECODER_CMD}" ]]; then
    echo "[adsb] Starting custom decoder command"
    bash -lc "${DECODER_CMD}" &
    DUMP1090_PID="$!"
  else
    echo "[adsb] Starting ${DUMP1090_CMD} with gain ${GAIN} (-10 means auto-gain)"
    local decoder_args=(
      --device-index "${DEVICE_INDEX}"
      --gain "${GAIN}"
      --net
      --net-bind-address 127.0.0.1
      --net-sbs-port "${SBS_PORT}"
      --quiet
    )
    if is_dump1090_fa_cmd; then
      mkdir -p "${JSON_DIR}"
      rm -f "${JSON_DIR}/aircraft.json" "${JSON_DIR}/receiver.json" "${JSON_DIR}/stats.json" 2>/dev/null || true
      decoder_args+=(--write-json "${JSON_DIR}" --write-json-every 1)
      if [[ -z "${ADSB_DUMP1090_JSON_URL:-}" ]]; then
        export ADSB_DUMP1090_JSON_URL="file://${JSON_DIR}/aircraft.json"
      fi
      echo "[adsb] dump1090-fa JSON feed: ${ADSB_DUMP1090_JSON_URL}"
    fi
    if [[ "${ADSB_NO_SUDO:-0}" == "1" ]]; then
      DUMP1090_PREFIX=()
    else
      if grant_wsl_usb_permissions; then
        DUMP1090_PREFIX=()
      else
        if [[ -n "${WSL_DISTRO}" ]]; then
          echo "[adsb] Could not grant WSL USB permissions; refusing to fall back to interactive sudo inside Windows Controller." >&2
          return 1
        fi
        echo "[adsb] Requesting sudo for RTL-SDR access"
        if [[ -r /dev/tty ]]; then
          sudo -v </dev/tty
        else
          echo "[adsb] Cannot prompt for sudo because this process has no interactive terminal." >&2
          echo "[adsb] Run from a WSL shell once, use an existing external decoder, or start via the Windows controller with ADSB_WSL_DISTRO set." >&2
          return 1
        fi
        DUMP1090_PREFIX=(sudo -n)
      fi
    fi
    "${DUMP1090_PREFIX[@]}" "${DUMP1090_CMD}" "${decoder_args[@]}" &
    DUMP1090_PID="$!"
  fi
  sleep 2
}

watch_decoder_messages() {
  if [[ "${DECODER_MODE}" == "none" || "${DECODER_MODE}" == "external" ]]; then
    return 0
  fi
  if [[ "${DECODER_WATCHDOG_SEC}" == "0" || -z "${DUMP1090_PID}" ]]; then
    return 0
  fi
  while true; do
    sleep "${DECODER_WATCHDOG_SEC}"
    if [[ -z "${DUMP1090_PID}" ]] || ! kill -0 "${DUMP1090_PID}" 2>/dev/null; then
      continue
    fi
    if timeout "${DECODER_WATCHDOG_SEC}" bash -c "exec 3<>/dev/tcp/127.0.0.1/${SBS_PORT}; IFS= read -r -t ${DECODER_WATCHDOG_SEC} _line <&3"; then
      continue
    fi
    echo "[adsb] No SBS messages for ${DECODER_WATCHDOG_SEC}s; restarting local decoder"
    sudo -n kill "${DUMP1090_PID}" 2>/dev/null || kill "${DUMP1090_PID}" 2>/dev/null || true
    wait "${DUMP1090_PID}" 2>/dev/null || true
    DUMP1090_PID=""
    start_decoder_process
  done
}

detect_sdr_busid() {
  local output detected
  output="$("${POWERSHELL}" -NoProfile -WindowStyle Hidden -Command "usbipd list" 2>/dev/null)" || return 0
  detected="$(
    awk -v pattern="${USB_MATCH_REGEX}" '
      BEGIN { IGNORECASE = 1 }
      /^[[:space:]]*[0-9]+-[0-9]+[[:space:]]/ &&
      ($0 ~ pattern) {
        print $1
        exit
      }
    ' <<<"${output}" | tr -d '\r'
  )"
  [[ -n "${detected}" ]] && echo "${detected}"
}

stop_port_listeners "${WEB_PORT}" "Web UI"

if [[ "${IS_WSL}" == "1" && -x "${POWERSHELL}" && -z "${BUSID}" && "${ADSB_SKIP_USBIPD:-0}" != "1" ]]; then
  BUSID="$(detect_sdr_busid)"
  if [[ -n "${BUSID}" ]]; then
    echo "[adsb] Auto-detected SDR USB BUSID ${BUSID}"
  fi
fi

if [[ "${IS_WSL}" == "1" && -x "${POWERSHELL}" && -n "${BUSID}" && "${ADSB_SKIP_USBIPD:-0}" != "1" ]]; then
  echo "[adsb] Attaching USB BUSID ${BUSID} to WSL via usbipd"
  USBIPD_STATUS=0
  USBIPD_OUTPUT="$("${POWERSHELL}" -NoProfile -WindowStyle Hidden -Command "usbipd attach --wsl --busid ${BUSID}" 2>&1)" || USBIPD_STATUS=$?
  if [[ "${USBIPD_STATUS}" != "0" ]]; then
    if grep -qi "already attached" <<<"${USBIPD_OUTPUT}"; then
      echo "[adsb] USB BUSID ${BUSID} is already attached to WSL"
    else
      echo "${USBIPD_OUTPUT}" >&2
    fi
  elif [[ -n "${USBIPD_OUTPUT}" ]]; then
    echo "${USBIPD_OUTPUT}"
  fi
elif [[ "${IS_WSL}" == "1" && -x "${POWERSHELL}" && "${ADSB_SKIP_USBIPD:-0}" != "1" ]]; then
  echo "[adsb] ADSB_USB_BUSID is not set; skipping usbipd attach"
fi

if [[ "${DECODER_MODE}" == "none" || "${DECODER_MODE}" == "external" ]]; then
  echo "[adsb] ADSB_DECODER_MODE=${DECODER_MODE}; not starting a local decoder"
elif [[ -z "${DECODER_CMD}" && -z "${DUMP1090_CMD}" ]]; then
  if sbs_port_listening; then
    echo "[adsb] Existing SBS feed detected on port ${SBS_PORT}; no local decoder command is required"
  elif command -v dump1090-mutability >/dev/null 2>&1; then
    DUMP1090_CMD="$(command -v dump1090-mutability)"
  elif command -v dump1090 >/dev/null 2>&1; then
    DUMP1090_CMD="$(command -v dump1090)"
  elif command -v dump1090-fa >/dev/null 2>&1; then
    DUMP1090_CMD="$(command -v dump1090-fa)"
  elif [[ -x "${HOME}/.local/bin/dump1090-fa" ]]; then
    DUMP1090_CMD="${HOME}/.local/bin/dump1090-fa"
  else
    echo "[adsb] dump1090-mutability or dump1090 was not found in PATH" >&2
    echo "[adsb] Use ADSB_DECODER_MODE=external for an existing SBS feed, or ADSB_DECODER_CMD='...' for another decoder." >&2
    exit 1
  fi
fi

if [[ "${ADSB_RESTART:-0}" == "1" ]]; then
  stop_dump1090_for_restart
fi

start_decoder_process
watch_decoder_messages &
WATCHDOG_PID="$!"

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
