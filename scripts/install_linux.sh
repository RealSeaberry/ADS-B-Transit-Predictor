#!/usr/bin/env bash
set -euo pipefail

SCRIPT_PATH="${BASH_SOURCE[0]}"
if command -v readlink >/dev/null 2>&1; then
  SCRIPT_PATH="$(readlink -f "${SCRIPT_PATH}")"
fi
ROOT_DIR="$(cd "$(dirname "${SCRIPT_PATH}")/.." && pwd)"
ALIAS_FILE="${ROOT_DIR}/scripts/adsb_alias.sh"
VENV_DIR="${ROOT_DIR}/.venv"

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

install_apt_dependencies() {
  if [[ "${ADSB_SKIP_APT:-0}" == "1" ]]; then
    echo "[install] Skipping apt dependency installation"
    return
  fi
  if ! command -v apt-get >/dev/null 2>&1; then
    echo "[install] apt-get not found; skipping system packages"
    return
  fi
  echo "[install] Installing system packages"
  sudo apt-get update
  sudo apt-get install -y python3 python3-venv python3-pip ca-certificates curl tar rtl-sdr
  if ! sudo apt-get install -y dump1090-mutability; then
    echo "[install] dump1090-mutability was not available from apt; install dump1090 manually if needed"
  fi
}

install_python_dependencies() {
  echo "[install] Creating Python virtual environment"
  python3 -m venv "${VENV_DIR}"
  if [[ "${ADSB_SKIP_PIP:-0}" == "1" ]]; then
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

main() {
  echo "[install] ADS-B Transit Predictor root: ${ROOT_DIR}"
  install_apt_dependencies
  install_python_dependencies
  chmod +x "${ROOT_DIR}/scripts/start_adsb_web.sh"
  install_shell_launcher
  echo ""
  echo "[install] Done."
  echo "[install] Open a new terminal, or run:"
  echo "          source \"${ALIAS_FILE}\""
  echo "[install] Then start with:"
  echo "          adsb-web"
  echo "[install] For offline packaging tests, use ADSB_SKIP_APT=1 ADSB_SKIP_PIP=1."
}

main "$@"
