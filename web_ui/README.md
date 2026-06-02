# ADS-B Transit Web UI

Browser-based Linux/WSL interface for ADS-B Transit Predictor. This is not the Windows `.exe` desktop build; it runs a Python web server and is intended for LAN/Tailscale access from browsers.

## Basic Start

Download a Linux/WSL release package and run the installer once:

```bash
mkdir -p ~/adsb-transit && cd ~/adsb-transit
wget -O ADS-B-Transit-Predictor-linux-web.tar.gz "https://github.com/RealSeaberry/ADS-B-Transit-Predictor/releases/latest/download/ADS-B-Transit-Predictor-linux-web.tar.gz"
tar -xzf ADS-B-Transit-Predictor-linux-web.tar.gz
cd ADS-B-Transit-Predictor-*/
./scripts/install_linux.sh
```

Open a new terminal, then start everything with:

```bash
adsb-web
```

The installer creates `.venv`, installs Python dependencies, installs common Linux receiver packages when `apt-get` is available, and adds the launcher to your shell startup file.

Manual start:

```bash
python web_ui/server.py --host 0.0.0.0 --port 8090 --https
```

Open `https://127.0.0.1:8090/` locally or `https://<server-ip>:8090/` from another device. The certificate is self-signed, so accept the browser warning on first use.

The server expects SBS/BaseStation ADS-B messages on the host and port configured in `config.json`, default `127.0.0.1:30003`.

## WSL Launcher

For Windows + WSL with RTL-SDR passed through by `usbipd`:

```bash
source scripts/adsb_alias.sh
adsb-web
```

Defaults:

1. Attach an RTL-SDR USB device to WSL when `ADSB_USB_BUSID` is set.
2. Start `dump1090-mutability` or `dump1090` with `--gain -10`.
3. Start HTTPS Web UI on `0.0.0.0:8090`.

Useful overrides:

```bash
ADSB_USB_BUSID=<busid> adsb-web
ADSB_WEB_PORT=8091 adsb-web
ADSB_GAIN=49.6 adsb-web
ADSB_SKIP_USBIPD=1 adsb-web
ADSB_RESTART=1 adsb-web
ADSB_HTTPS=0 adsb-web
```

## Configuration Flow

1. Start dump1090 or another SBS-compatible ADS-B decoder.
2. Start `web_ui/server.py`.
3. Open Settings in the browser.
4. Set receiver host/port.
5. Set observer latitude, longitude, and altitude in meters.
6. Tune prediction timing:
   - `Prediction Horizon`: how far ahead events are searched.
   - `Prediction Step`: coarse celestial/traffic scan step.
   - `Track duration`: historical trail length.
   - `Speed vector length`: forward velocity-vector length.
7. Save settings.

## GPS And Location

Browser GPS works on `localhost` or HTTPS. The default launcher uses HTTPS so GPS can work over Tailscale.

If browser/mobile altitude is missing, enter observer altitude manually in Settings.

## Map Data

The Web UI uses local vector map data and aviation overlays only. It does not require external map providers, elevation services, or map-service keys.

## Data Updates

Airport, runway, and navaid data comes from OurAirports. Refresh local CSV files with:

```bash
python scripts/update_ourairports_data.py --dry-run
python scripts/update_ourairports_data.py
```

Restart the web server after updating data.

## Endpoints

- `/` serves the Web UI.
- `/api/state` returns aircraft, events, geodata, ILS, celestial status, and transit strips.
- `/api/config` reads/writes runtime settings.
- `/api/health` returns a minimal health check.

Useful `/api/state` query parameters:

- `range_km=60`
- `selected=A1B2C3`
- `transits=selected`, `all`, or `none`
