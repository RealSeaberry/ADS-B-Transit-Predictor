# ADS-B Transit Predictor Linux Web Server

<p align="center"><img src="assets/icon.png" width="96" alt="ADS-B Transit Predictor icon"></p>

This package is the Linux/WSL web-server release of ADS-B Transit Predictor. It is not the older Windows desktop `.exe` release.

For release history, read [CHANGELOG.md](CHANGELOG.md).

## Project Motivation

As an aviation enthusiast and photographer, I was fascinated by two distinct and technically demanding photographic challenges: capturing the rare moment two aircraft appear to have a close encounter, and capturing the dramatic transit of a single aircraft across the sun or moon. Both types of events are incredibly fleeting, lasting only seconds, and their visibility is entirely dependent on the observer's precise location and timing. I realized that a purely observational approach was not just inefficient, but fundamentally limited by chance. This project was born out of a desire to create a scientific tool to solve this problem—to move from serendipity to predictable, planned photographic opportunities. The software achieves this by fusing real-time aeronautical data (ADS-B) with predictive geometry and celestial mechanics.

## Windows Desktop Demo

The older Windows desktop release remains available from previous GitHub Releases.

### Examples
![Example of a close encounter](assets/eg.jpg)
*<p align="center">A screenshot displaying a B747-8F and an IL-76 in close proximity.</p>*

## Screenshots

### S1: 3D Perspective View
![S1 3D View](assets/Screenshot_5.jpg)

### S2: 3D View — Low Pitch / Wide Area
![S2 3D Low Pitch](assets/Screenshot_6.jpg)

### S3: 3D View — Aircraft Transit
![S3 3D Transit](assets/Screenshot_7.jpg)

### S4: 3D View — Aircraft Close Encounter
![S4 3D Close](assets/Screenshot_8.jpg)

### Network Architecture
![Linux Web Architecture](assets/image-2-linux-web-architecture.svg)

## Download And Install

Supported baseline: Python 3.8 or newer. Ubuntu 20.04+ / Debian 11+ / current Fedora, Arch, or openSUSE are recommended. Ubuntu 18.04's default Python 3.6 is too old for this release.

```bash
mkdir -p ~/adsb-transit && cd ~/adsb-transit
wget -O ADS-B-Transit-Predictor-linux-web.tar.gz "https://github.com/RealSeaberry/ADS-B-Transit-Predictor/releases/latest/download/ADS-B-Transit-Predictor-linux-web.tar.gz"
tar -xzf ADS-B-Transit-Predictor-linux-web.tar.gz
cd ADS-B-Transit-Predictor-*/
./scripts/install_linux.sh
```

Open a new terminal, then start the receiver and Web UI:

```bash
adsb-doctor
adsb-web
```

Open:

* Local machine: `https://127.0.0.1:8090/`
* LAN/Tailscale device: `https://<server-ip>:8090/`

The HTTPS certificate is self-signed. Accept the browser warning on first visit.

## What The Installer Does

`scripts/install_linux.sh`:

* installs common Linux packages with `apt`, `dnf`, `yum`, `pacman`, or `zypper` when available
* creates `.venv`
* installs Python dependencies from `requirements.txt`
* creates `~/.config/adsb-transit/adsb-web.env`
* registers the `adsb-web` launcher in your shell startup file
* registers the `adsb-doctor` diagnostics command
* tries to install a packaged ADS-B decoder when one is available from your Linux distribution

Useful installer overrides:

```bash
ADSB_SKIP_SYSTEM=1 ./scripts/install_linux.sh
ADSB_SKIP_PIP=1 ./scripts/install_linux.sh
ADSB_SHELL_RC=~/.bashrc ./scripts/install_linux.sh
ADSB_INSTALL_DECODER=none ./scripts/install_linux.sh
ADSB_INSTALL_RTL_UDEV=1 ./scripts/install_linux.sh
```

Altitude correction defaults to METAR mode. On startup the server immediately tries to fetch the nearest valid METAR; if METAR is unavailable or expired, predictions continue with raw barometric altitude. EGM/geoid data is not installed by the v1.4.1 installer. The Web UI only shows EGM options when local geoid files are already present.

## Recommended First Run

After installation, run:

```bash
adsb-doctor
```

`adsb-doctor` checks the Python environment, decoder commands, SBS/Web ports, WSL detection, `usbipd list`, and attached USB devices. If you ask for help, include its output.

Then start:

```bash
adsb-web
```

Runtime defaults are stored in:

```text
~/.config/adsb-transit/adsb-web.env
```

Edit this file for persistent receiver settings instead of typing long environment variables every time.

## Before Asking For Help

Run:

```bash
adsb-doctor
```

Include the output when reporting install, SDR, decoder, WSL, or port issues. It avoids guesswork and helps identify whether the problem is Python dependencies, USB forwarding, decoder startup, or the SBS feed.

## Receiver Access: Native Linux vs WSL

Native Linux does not require `usbipd-win`. If `dump1090`, `dump1090-mutability`, `readsb`, or another SBS/BaseStation decoder is already listening on `127.0.0.1:30003`, `adsb-web` can use that local data stream directly:

```bash
adsb-web
# or explicitly:
ADSB_DECODER_MODE=external adsb-web
```

Use `usbipd-win` only when the SDR receiver is physically plugged into Windows and the server runs inside WSL.

## Configure usbipd For Windows + WSL

If the SDR receiver is plugged into Windows and the server runs in WSL, pass the USB device through with `usbipd`.

Install usbipd from Windows PowerShell if needed:

```powershell
winget install --interactive --exact dorssel.usbipd-win
```

List USB devices:

```powershell
usbipd list
```

Bind the SDR device once:

```powershell
usbipd bind --busid <busid>
```

Attach it to WSL:

```powershell
usbipd attach --wsl --busid <busid>
```

`adsb-web` can usually auto-detect and attach common RTL-SDR, Airspy, SDRplay, Mode-S Beast, or FlightAware receiver names shown by `usbipd list`. If more than one receiver is connected, specify the BUSID manually:

```bash
ADSB_USB_BUSID=<busid> adsb-web
```

Skip usbipd for an already attached WSL receiver. Native Linux skips usbipd automatically:

```bash
ADSB_SKIP_USBIPD=1 adsb-web
```

Confirm the receiver is visible inside Linux/WSL:

```bash
lsusb
rtl_test -t
```

`rtl_test` only applies to RTL2832U-compatible receivers. For Airspy, SDRplay, Beast, network receivers, or another decoder, verify the receiver with that decoder's own test command.

## SDR And Decoder Compatibility

The Web UI does not require a specific SDR. It reads SBS/BaseStation messages from `dump1090-fa`, `dump1090`, `readsb`, or any compatible decoder on the configured host and port.

Recommended receiver paths:

| Receiver setup | Recommended mode |
| --- | --- |
| Native Linux, existing local dump1090/readsb on SBS `127.0.0.1:30003` | default `adsb-web`, or `ADSB_DECODER_MODE=external adsb-web` |
| Native Linux, RTL-SDR / RTL2832U with no decoder running | default `adsb-web` with packaged `dump1090-mutability` / `dump1090` when available |
| WSL, receiver plugged into Windows | configure `usbipd`, then default `adsb-web` |
| Remote decoder on another computer | set SBS Host/Port in Settings, then `ADSB_DECODER_MODE=external adsb-web` |
| Airspy / SDRplay / Beast / custom decoder | set `ADSB_DECODER_CMD` in `~/.config/adsb-transit/adsb-web.env` |
| No receiver yet, demo UI only | `ADSB_DECODER_MODE=none adsb-web` |

Default mode first checks whether the SBS port is already listening. If so, it leaves the existing decoder alone and starts only the Web UI. If no SBS feed is listening, it tries to start a local decoder, preferring `dump1090-mutability`, then `dump1090`, then `dump1090-fa` if the user has installed it separately.

```bash
adsb-web
```

On Ubuntu, `dump1090-mutability` may be hidden if the `universe` repository is disabled. If installation fails with `E: Unable to locate package dump1090-mutability`, enable `universe` and retry:

```bash
sudo apt-get update
sudo apt-get install -y software-properties-common
sudo add-apt-repository -y universe
sudo apt-get update
sudo apt-get install -y dump1090-mutability rtl-sdr
```

The installer attempts this automatically. If your distribution still does not provide `dump1090-mutability`, use an existing decoder, install a decoder manually, or use custom decoder mode instead.

If you already run `dump1090-fa` or `readsb` with `aircraft.json` enabled, set the optional JSON URL manually:

```bash
ADSB_DUMP1090_JSON_URL='http://127.0.0.1/dump1090-fa/data/aircraft.json' adsb-web
# or, for decoders exposing JSON directly:
ADSB_DUMP1090_JSON_URL='http://127.0.0.1:8080/data/aircraft.json' adsb-web
```

When JSON `alt_geom` is unavailable, the per-aircraft correction factor stays at its last value, or `1.0` if that aircraft has never reported geometric altitude. The app still falls back to the METAR/manual altitude correction path.

Use an already running decoder, including a remote decoder, by setting the Web UI receiver host/port in Settings or `config.json`, then start only the Web UI stack:

```bash
ADSB_DECODER_MODE=external adsb-web
```

Use a custom local decoder command when the SDR needs another decoder or device driver. The command must provide SBS output on `ADSB_SBS_PORT`:

```bash
ADSB_DECODER_CMD='readsb --device-type airspy --net --net-sbs-port 30003' adsb-web
```

If WSL automatic USB detection misses your receiver, pass the BUSID manually or override the matching expression:

```bash
ADSB_USB_BUSID=<busid> adsb-web
ADSB_USB_MATCH_REGEX='Airspy|SDRplay|0bda:2838' adsb-web
```

## Configure Tailscale

Install and start Tailscale on the Linux/WSL server:

```bash
curl -fsSL https://tailscale.com/install.sh | sh
sudo tailscale up
```

Get the Tailnet address:

```bash
tailscale ip -4
```

Start ADS-B Transit Predictor:

```bash
adsb-web
```

Open from a phone, tablet, or laptop on the same Tailnet:

```text
https://<tailscale-ip>:8090/
```

## Why HTTPS Is Enabled By Default

Browser location access normally requires a secure context. `localhost` is secure, but a browser opening `http://<server-ip>:8090/` over LAN or Tailscale usually cannot use GPS.

`adsb-web` therefore starts the Web UI with HTTPS by default. The server creates a local self-signed certificate in `.web_certs/`; release packages do not include this certificate or private key.

Use HTTPS when you want the browser `Use GPS` button to fill observer latitude, longitude, and altitude where available:

```text
https://127.0.0.1:8090/
https://<tailscale-ip>:8090/
```

Disable HTTPS only for local testing or when browser GPS is not needed:

```bash
ADSB_HTTPS=0 adsb-web
```

## Runtime Overrides

```bash
ADSB_USB_BUSID=<busid> adsb-web
ADSB_WEB_PORT=8091 adsb-web
ADSB_GAIN=49.6 adsb-web
ADSB_SKIP_USBIPD=1 adsb-web
ADSB_RESTART=1 adsb-web
ADSB_HTTPS=0 adsb-web
ADSB_DECODER_MODE=external adsb-web
ADSB_DECODER_CMD='readsb --net --net-sbs-port 30003' adsb-web
```

## Basic Use

1. Connect the 1090 MHz antenna and RTL-SDR receiver.
2. Attach the receiver to WSL with `usbipd`, or run on native Linux.
3. Start the server with `adsb-web`.
4. Open `https://127.0.0.1:8090/`, `https://<lan-ip>:8090/`, or `https://<tailscale-ip>:8090/`.
5. Open Settings and set observer latitude, longitude, and altitude.
6. Set `SBS Host` / `SBS Port` if you use an existing decoder; defaults are `127.0.0.1:30003`.
7. Select an aircraft to view telemetry, history, speed vector, transit strips, and predicted events.

## Notes

The older Windows desktop `.exe` package remains available from older GitHub Releases. This Linux package is a separate release asset from the same project history.
