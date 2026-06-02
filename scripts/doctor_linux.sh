#!/usr/bin/env bash
set -u

SCRIPT_PATH="${BASH_SOURCE[0]}"
if command -v readlink >/dev/null 2>&1; then
  SCRIPT_PATH="$(readlink -f "${SCRIPT_PATH}")"
fi
ROOT_DIR="$(cd "$(dirname "${SCRIPT_PATH}")/.." && pwd)"
CONFIG_FILE="${ADSB_ENV_FILE:-${XDG_CONFIG_HOME:-${HOME}/.config}/adsb-transit/adsb-web.env}"
SBS_PORT="${ADSB_SBS_PORT:-30003}"
WEB_PORT="${ADSB_WEB_PORT:-8090}"

if [[ -f "${CONFIG_FILE}" ]]; then
  set -a
  # shellcheck disable=SC1090
  source "${CONFIG_FILE}"
  set +a
  SBS_PORT="${ADSB_SBS_PORT:-${SBS_PORT}}"
  WEB_PORT="${ADSB_WEB_PORT:-${WEB_PORT}}"
fi

ok() { printf '[ OK ] %s\n' "$*"; }
warn() { printf '[WARN] %s\n' "$*"; }
fail() { printf '[FAIL] %s\n' "$*"; }
have_cmd() { command -v "$1" >/dev/null 2>&1; }

check_cmd() {
  if have_cmd "$1"; then ok "$1: $(command -v "$1")"; else warn "$1 not found"; fi
}

check_port() {
  local port="$1" label="$2"
  if have_cmd ss && ss -ltn "( sport = :${port} )" 2>/dev/null | grep -q ":${port}"; then
    ok "${label} port ${port} is listening"
  else
    warn "${label} port ${port} is not listening"
  fi
}

echo "ADS-B Transit Predictor Linux Doctor"
echo "Root: ${ROOT_DIR}"
echo "Config: ${CONFIG_FILE}"
echo

if [[ -f "${CONFIG_FILE}" ]]; then ok "runtime config exists"; else warn "runtime config missing; run ./scripts/install_linux.sh"; fi

if [[ -x "${ROOT_DIR}/.venv/bin/python" ]]; then
  ok "project venv python: ${ROOT_DIR}/.venv/bin/python"
  "${ROOT_DIR}/.venv/bin/python" - <<'PY' 2>/dev/null && ok "Python dependencies import" || fail "Python dependency import failed"
import numpy, shapefile, shapely, skyfield
PY
else
  warn "project venv missing; run ./scripts/install_linux.sh"
fi

check_cmd python3
check_cmd curl
check_cmd tar
check_cmd ss
check_cmd lsusb
check_cmd rtl_test
check_cmd dump1090-mutability
check_cmd dump1090
check_cmd readsb
if have_cmd dump1090-mutability || have_cmd dump1090 || have_cmd readsb || have_cmd dump1090-fa; then
  ok "ADS-B decoder available"
else
  warn "No local decoder found; use ADSB_DECODER_MODE=external or ADSB_DECODER_CMD for another receiver/decoder"
fi

echo
echo "Decoder mode: ${ADSB_DECODER_MODE:-auto}"
echo "SBS port: ${SBS_PORT}"
echo "Web port: ${WEB_PORT}"
check_port "${SBS_PORT}" "SBS/BaseStation"
check_port "${WEB_PORT}" "Web UI"

if [[ -d /mnt/c/Windows ]]; then
  ok "WSL detected"
  POWERSHELL="${POWERSHELL:-/mnt/c/Windows/System32/WindowsPowerShell/v1.0/powershell.exe}"
  if [[ -x "${POWERSHELL}" ]]; then
    ok "Windows PowerShell available for usbipd"
    "${POWERSHELL}" -NoProfile -Command "usbipd list" 2>/dev/null | sed 's/\r$//' | sed -n '1,12p'
  else
    warn "PowerShell not found at ${POWERSHELL}"
  fi
else
  ok "native Linux or non-WSL environment"
  if have_cmd lsusb; then lsusb | sed -n '1,12p'; fi
fi

echo
echo "Common next steps:"
echo "  RTL-SDR local decoder: adsb-web"
echo "  Existing decoder: ADSB_DECODER_MODE=external adsb-web"
echo "  Custom decoder: ADSB_DECODER_CMD='readsb --net --net-sbs-port 30003 ...' adsb-web"
