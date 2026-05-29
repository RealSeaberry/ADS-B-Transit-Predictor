#!/usr/bin/env bash
set -euo pipefail

SCRIPT_PATH="${BASH_SOURCE[0]}"
if command -v readlink >/dev/null 2>&1; then
  SCRIPT_PATH="$(readlink -f "${SCRIPT_PATH}")"
fi
ROOT_DIR="$(cd "$(dirname "${SCRIPT_PATH}")/.." && pwd)"
ALIAS_FILE="${ROOT_DIR}/scripts/adsb_alias.sh"
VENV_DIR="${ADSB_VENV_DIR:-${ROOT_DIR}/.venv}"
CONFIG_DIR="${ADSB_CONFIG_DIR:-${XDG_CONFIG_HOME:-${HOME}/.config}/adsb-transit}"
CONFIG_FILE="${ADSB_ENV_FILE:-${CONFIG_DIR}/adsb-web.env}"

SKIP_SYSTEM="${ADSB_SKIP_SYSTEM:-${ADSB_SKIP_APT:-0}}"
SKIP_PIP="${ADSB_SKIP_PIP:-0}"
INSTALL_DECODER="${ADSB_INSTALL_DECODER:-auto}"
INSTALL_RTL_UDEV="${ADSB_INSTALL_RTL_UDEV:-0}"
NONINTERACTIVE="${ADSB_NONINTERACTIVE:-0}"
INSTALL_PHASE="${ADSB_INSTALL_PHASE:-all}"

usage() {
  cat <<'EOF'
Usage: ./scripts/install_linux.sh

Installs the ADS-B Transit Predictor Linux Web UI dependencies and adsb-web launcher.

Environment overrides:
  ADSB_SKIP_SYSTEM=1       Skip system package installation
  ADSB_SKIP_PIP=1          Create venv but skip Python package installation
  ADSB_INSTALL_PHASE=all    all, system, or user
  ADSB_VENV_DIR=.venv      Python virtual environment path
  ADSB_ENV_FILE=...        Runtime config file written by the installer
  ADSB_SHELL_RC=~/.bashrc  Shell rc file where the adsb-web launcher is added
  ADSB_INSTALL_DECODER=auto  auto, dump1090, readsb, or none
  ADSB_INSTALL_RTL_UDEV=1  Install a basic RTL-SDR udev rule on native Linux

Examples:
  ./scripts/install_linux.sh
  ADSB_INSTALL_DECODER=readsb ./scripts/install_linux.sh
  ADSB_SKIP_SYSTEM=1 ./scripts/install_linux.sh
  ADSB_SKIP_PIP=1 ./scripts/install_linux.sh
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

detect_shell_rc() {
  if [[ -n "${ADSB_SHELL_RC:-}" ]]; then
    echo "${ADSB_SHELL_RC}"
    return
  fi
  case "${SHELL:-}" in
    */zsh) echo "${ZDOTDIR:-${HOME}}/.zshrc" ;;
    */bash) echo "${HOME}/.bashrc" ;;
    *) echo "${HOME}/.profile" ;;
  esac
}

have_cmd() {
  command -v "$1" >/dev/null 2>&1
}

run_sudo() {
  if [[ "$(id -u)" == "0" ]]; then
    "$@"
  elif [[ "${NONINTERACTIVE}" == "1" ]]; then
    sudo -n "$@" || {
      echo "[install] sudo requires a password, but this installer is running non-interactively." >&2
      echo "[install] Open the selected WSL distro once, run 'sudo -v', then run this installer again." >&2
      return 1
    }
  else
    sudo "$@"
  fi
}

package_manager() {
  if have_cmd apt-get; then echo apt; return; fi
  if have_cmd dnf; then echo dnf; return; fi
  if have_cmd yum; then echo yum; return; fi
  if have_cmd pacman; then echo pacman; return; fi
  if have_cmd zypper; then echo zypper; return; fi
  echo none
}

install_packages() {
  local pm="$1"
  shift
  local packages=("$@")
  case "${pm}" in
    apt)
      echo "[install] apt-get update"
      run_sudo env DEBIAN_FRONTEND=noninteractive apt-get -o=Dpkg::Use-Pty=0 -o=DPkg::Lock::Timeout=120 update
      echo "[install] apt-get install: ${packages[*]}"
      run_sudo env DEBIAN_FRONTEND=noninteractive apt-get -o=Dpkg::Use-Pty=0 -o=DPkg::Lock::Timeout=120 install -y --no-install-recommends "${packages[@]}"
      ;;
    dnf)
      run_sudo dnf install -y "${packages[@]}"
      ;;
    yum)
      run_sudo yum install -y "${packages[@]}"
      ;;
    pacman)
      run_sudo pacman -Sy --needed --noconfirm "${packages[@]}"
      ;;
    zypper)
      run_sudo zypper --non-interactive install "${packages[@]}"
      ;;
    *)
      return 1
      ;;
  esac
}

enable_ubuntu_universe() {
  if [[ ! -r /etc/os-release ]]; then
    return 1
  fi
  # shellcheck disable=SC1091
  source /etc/os-release
  if [[ "${ID:-}" != "ubuntu" ]]; then
    return 1
  fi
  if apt-cache show dump1090-mutability >/dev/null 2>&1; then
    return 0
  fi
  echo "[install] dump1090-mutability is not visible in apt; enabling Ubuntu universe repository"
  if ! have_cmd add-apt-repository; then
    echo "[install] apt-get install: software-properties-common"
    run_sudo env DEBIAN_FRONTEND=noninteractive apt-get -o=Dpkg::Use-Pty=0 -o=DPkg::Lock::Timeout=120 install -y --no-install-recommends software-properties-common || return 1
  fi
  run_sudo add-apt-repository -y universe || return 1
  echo "[install] apt-get update"
  run_sudo env DEBIAN_FRONTEND=noninteractive apt-get -o=Dpkg::Use-Pty=0 -o=DPkg::Lock::Timeout=120 update
}

install_system_dependencies() {
  if [[ "${SKIP_SYSTEM}" == "1" ]]; then
    echo "[install] Skipping system package installation"
    return
  fi

  local pm
  pm="$(package_manager)"
  if [[ "${pm}" == "none" ]]; then
    echo "[install] No supported package manager found; skipping system packages"
    return
  fi

  echo "[install] Installing base system packages with ${pm}"
  case "${pm}" in
    apt)
      install_packages "${pm}" python3 python3-venv python3-tk ca-certificates curl tar rtl-sdr usbutils iproute2
      ;;
    dnf|yum)
      install_packages "${pm}" python3 python3-tkinter ca-certificates curl tar rtl-sdr usbutils iproute
      ;;
    pacman)
      install_packages "${pm}" python python-pip ca-certificates curl tar rtl-sdr usbutils iproute2
      ;;
    zypper)
      install_packages "${pm}" python3 python3-venv python3-tk ca-certificates curl tar rtl-sdr usbutils iproute2
      ;;
  esac

  install_decoder_package "${pm}"
}

install_decoder_package() {
  local pm="$1"
  if [[ "${INSTALL_DECODER}" == "none" ]]; then
    echo "[install] Skipping ADS-B decoder package installation"
    return
  fi

  if have_cmd dump1090-mutability || have_cmd dump1090 || have_cmd readsb; then
    echo "[install] ADS-B decoder already available"
    return
  fi

  echo "[install] Trying to install ADS-B decoder package (${INSTALL_DECODER})"
  case "${pm}:${INSTALL_DECODER}" in
    apt:auto|apt:dump1090)
      install_packages apt dump1090-mutability \
        || (enable_ubuntu_universe && install_packages apt dump1090-mutability) \
        || {
          echo "[install] dump1090-mutability not available from current apt repositories"
          echo "[install] Use ADSB_DECODER_MODE=external for an existing decoder, or install readsb/dump1090 manually"
        }
      ;;
    apt:readsb)
      install_packages apt readsb || echo "[install] readsb not available in this apt repository"
      ;;
    dnf:auto|dnf:dump1090|yum:auto|yum:dump1090)
      install_packages "${pm}" dump1090 || echo "[install] dump1090 not available in this repository"
      ;;
    dnf:readsb|yum:readsb)
      install_packages "${pm}" readsb || echo "[install] readsb not available in this repository"
      ;;
    pacman:auto|pacman:dump1090)
      install_packages pacman dump1090 || echo "[install] dump1090 not available; check AUR/readsb options"
      ;;
    pacman:readsb)
      install_packages pacman readsb || echo "[install] readsb not available; check AUR options"
      ;;
    zypper:auto|zypper:dump1090|zypper:readsb)
      install_packages zypper readsb || install_packages zypper dump1090 || echo "[install] No decoder package found in this repository"
      ;;
    *)
      echo "[install] Unknown ADSB_INSTALL_DECODER=${INSTALL_DECODER}; skipping decoder package"
      ;;
  esac
}

install_rtl_udev_rule() {
  if [[ "${INSTALL_RTL_UDEV}" != "1" ]]; then
    return
  fi
  if [[ -d /mnt/c/Windows ]]; then
    echo "[install] WSL detected; skipping native Linux RTL-SDR udev rule"
    return
  fi
  local rule_file="/etc/udev/rules.d/20-rtlsdr.rules"
  echo "[install] Installing basic RTL-SDR udev rule to ${rule_file}"
  printf '%s\n' 'SUBSYSTEM=="usb", ATTRS{idVendor}=="0bda", ATTRS{idProduct}=="2838", MODE="0666", GROUP="plugdev", TAG+="uaccess"' \
    | run_sudo tee "${rule_file}" >/dev/null
  if have_cmd udevadm; then
    run_sudo udevadm control --reload-rules || true
    run_sudo udevadm trigger || true
  fi
}

install_python_dependencies() {
  local python_bin="python3"
  if ! have_cmd "${python_bin}"; then
    if have_cmd python; then python_bin="python"; else
      echo "[install] Python was not found" >&2
      exit 1
    fi
  fi

  echo "[install] Creating Python virtual environment at ${VENV_DIR}"
  "${python_bin}" -m venv "${VENV_DIR}"
  if [[ "${SKIP_PIP}" == "1" ]]; then
    echo "[install] Skipping Python dependency installation"
    return
  fi
  "${VENV_DIR}/bin/python" -m pip install --upgrade pip
  "${VENV_DIR}/bin/python" -m pip install -r "${ROOT_DIR}/requirements.txt"
}

install_shell_launcher() {
  local rc_file marker source_line
  rc_file="$(detect_shell_rc)"
  marker="# ADS-B Transit Predictor launcher"
  source_line="source \"${ALIAS_FILE}\""
  mkdir -p "$(dirname "${rc_file}")"
  touch "${rc_file}"
  if grep -Fq "${source_line}" "${rc_file}"; then
    echo "[install] adsb-web launcher already exists in ${rc_file}"
  else
    {
      echo ""
      echo "${marker}"
      echo "${source_line}"
    } >>"${rc_file}"
    echo "[install] Added adsb-web launcher to ${rc_file}"
  fi
}

install_runtime_config() {
  mkdir -p "${CONFIG_DIR}"
  if [[ -f "${CONFIG_FILE}" ]]; then
    echo "[install] Runtime config already exists: ${CONFIG_FILE}"
    return
  fi
  cat >"${CONFIG_FILE}" <<'EOF'
# ADS-B Transit Predictor runtime configuration.
# This file is loaded by adsb-web before reading environment variables.

# Web UI
ADSB_WEB_HOST=100.75.150.117
ADSB_WEB_PORT=8090
ADSB_HTTPS=1

# Decoder connection and startup.
# auto: start local dump1090 when no SBS listener is already running.
# external: do not start a decoder; use an existing local/remote SBS feed.
# none: do not start a decoder.
ADSB_DECODER_MODE=auto
ADSB_SBS_PORT=30003

# RTL-SDR/dump1090 defaults. ADSB_GAIN=-10 means auto-gain for dump1090.
ADSB_GAIN=-10
ADSB_DEVICE_INDEX=0

# WSL usbipd. Leave empty for auto-detection, or set a BUSID from "usbipd list".
ADSB_USB_BUSID=
ADSB_USB_MATCH_REGEX='0bda:2838|0bda:2832|RTL2838|RTL-SDR|Bulk-In|Airspy|SDRplay|RSP|HackRF|Mode-S Beast|FlightAware|Pro Stick'

# Custom decoder example:
# ADSB_DECODER_CMD='readsb --device-type airspy --net --net-sbs-port 30003'
EOF
  echo "[install] Created runtime config: ${CONFIG_FILE}"
}

print_next_steps() {
  echo ""
  echo "[install] Done."
  echo "[install] Open a new terminal, or run:"
  echo "          source \"${ALIAS_FILE}\""
  echo "[install] Then start with:"
  echo "          adsb-web"
  echo "          adsb-doctor"
  echo "[install] Runtime config:"
  echo "          ${CONFIG_FILE}"
  echo ""
  echo "[install] Compatibility notes:"
  echo "          RTL-SDR/RTL2832U: default dump1090 path should work."
  echo "          Existing or remote decoder: ADSB_DECODER_MODE=external adsb-web"
  echo "          Airspy/SDRplay/custom decoder: ADSB_DECODER_CMD='...' adsb-web"
  echo "          WSL USB attach: set ADSB_USB_BUSID=<busid> if auto-detect misses it."
}

main() {
  echo "[install] ADS-B Transit Predictor root: ${ROOT_DIR}"
  case "${INSTALL_PHASE}" in
    all)
      install_system_dependencies
      install_rtl_udev_rule
      install_python_dependencies
      chmod +x "${ROOT_DIR}/scripts/start_adsb_web.sh"
      chmod +x "${ROOT_DIR}/scripts/doctor_linux.sh" 2>/dev/null || true
      install_runtime_config
      install_shell_launcher
      print_next_steps
      ;;
    system)
      install_system_dependencies
      install_rtl_udev_rule
      echo "[install] System dependency phase complete."
      ;;
    user)
      SKIP_SYSTEM=1
      install_python_dependencies
      chmod +x "${ROOT_DIR}/scripts/start_adsb_web.sh"
      chmod +x "${ROOT_DIR}/scripts/doctor_linux.sh" 2>/dev/null || true
      install_runtime_config
      install_shell_launcher
      print_next_steps
      ;;
    *)
      echo "[install] Unknown ADSB_INSTALL_PHASE=${INSTALL_PHASE}; expected all, system, or user" >&2
      exit 1
      ;;
  esac
}

main "$@"
