# Source this file from bash/zsh to add the adsb-web launcher:
#   source "/path/to/ADS-B-Transit-Predictor/scripts/adsb_alias.sh"

_adsb_alias_script="${BASH_SOURCE[0]:-${(%):-%x}}"
if command -v readlink >/dev/null 2>&1; then
  _adsb_alias_script="$(readlink -f "${_adsb_alias_script}")"
fi
_adsb_alias_root="$(cd "$(dirname "${_adsb_alias_script}")/.." && pwd)"

alias adsb-web="cd \"${_adsb_alias_root}\" && ./scripts/start_adsb_web.sh"
