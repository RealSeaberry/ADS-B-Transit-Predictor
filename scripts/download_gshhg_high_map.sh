#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TARGET_DIR="$ROOT_DIR/data/map_vectors/gshhs_h_land"
ZIP_URL="https://www.soest.hawaii.edu/pwessel/gshhg/gshhg-shp-2.3.7.zip"

mkdir -p "$TARGET_DIR"

ZIP_PATH="$TARGET_DIR/gshhg-shp-2.3.7.zip"
PARTIAL_ZIP="$ZIP_PATH.part"

echo "[map] Downloading GSHHG 2.3.7 shapefile archive"
if command -v curl >/dev/null 2>&1; then
  curl -L --fail --retry 5 --retry-delay 3 --continue-at - -o "$PARTIAL_ZIP" "$ZIP_URL"
elif command -v wget >/dev/null 2>&1; then
  wget -c -O "$PARTIAL_ZIP" "$ZIP_URL"
else
  echo "[map] curl or wget is required" >&2
  exit 1
fi
mv "$PARTIAL_ZIP" "$ZIP_PATH"

unzip -j -o "$ZIP_PATH" "GSHHS_shp/h/GSHHS_h_L1.*" -d "$TARGET_DIR"
rm -f "$ZIP_PATH"

echo "[map] Installed GSHHG high-resolution coastline/land layer in $TARGET_DIR"
