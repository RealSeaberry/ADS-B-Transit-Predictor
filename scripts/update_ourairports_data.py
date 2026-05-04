#!/usr/bin/env python3
import argparse
import csv
import shutil
import sys
import tempfile
import urllib.request
from pathlib import Path


ROOT_DIR = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT_DIR / "data"
SOURCES = {
    "airports.csv": "https://davidmegginson.github.io/ourairports-data/airports.csv",
    "runways.csv": "https://davidmegginson.github.io/ourairports-data/runways.csv",
    "navaids.csv": "https://davidmegginson.github.io/ourairports-data/navaids.csv",
}
REQUIRED_COLUMNS = {
    "airports.csv": {"id", "ident", "type", "name", "latitude_deg", "longitude_deg"},
    "runways.csv": {"id", "airport_ident", "le_ident", "le_latitude_deg", "le_longitude_deg", "he_ident", "he_latitude_deg", "he_longitude_deg"},
    "navaids.csv": {"id", "ident", "name", "type", "latitude_deg", "longitude_deg"},
}
MIN_ROWS = {
    "airports.csv": 10000,
    "runways.csv": 10000,
    "navaids.csv": 1000,
}


def validate_csv(path, filename):
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        columns = set(reader.fieldnames or [])
        missing = REQUIRED_COLUMNS[filename] - columns
        if missing:
            raise RuntimeError(f"{filename}: missing required columns: {', '.join(sorted(missing))}")
        row_count = sum(1 for _ in reader)
    if row_count < MIN_ROWS[filename]:
        raise RuntimeError(f"{filename}: expected at least {MIN_ROWS[filename]} rows, got {row_count}")
    return row_count


def download_file(url, destination):
    request = urllib.request.Request(url, headers={"User-Agent": "ADS-B-Transit-Predictor/1.0"})
    with urllib.request.urlopen(request, timeout=60) as response:
        with destination.open("wb") as handle:
            shutil.copyfileobj(response, handle)


def update_one(filename, dry_run=False):
    url = SOURCES[filename]
    target = DATA_DIR / filename
    with tempfile.TemporaryDirectory(prefix="ourairports-", dir=DATA_DIR) as temp_dir:
        temp_path = Path(temp_dir) / filename
        download_file(url, temp_path)
        row_count = validate_csv(temp_path, filename)
        if not dry_run:
            temp_path.replace(target)
    action = "validated" if dry_run else "updated"
    print(f"{filename}: {action} {row_count} rows")


def main():
    parser = argparse.ArgumentParser(description="Update airport, runway, and navaid CSV files from OurAirports.")
    parser.add_argument("files", nargs="*", choices=sorted(SOURCES), help="Specific CSV files to update. Defaults to all.")
    parser.add_argument("--dry-run", action="store_true", help="Download and validate without replacing local data.")
    args = parser.parse_args()

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    selected = args.files or sorted(SOURCES)
    for filename in selected:
        update_one(filename, dry_run=args.dry_run)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"Update failed: {exc}", file=sys.stderr)
        sys.exit(1)
