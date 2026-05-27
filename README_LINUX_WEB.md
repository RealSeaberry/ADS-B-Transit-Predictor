# ADS-B Transit Predictor Linux Web Server

This package is the Linux/WSL web-server release of ADS-B Transit Predictor. It is not the older Windows desktop `.exe` release.

## Project Motivation

As an aviation enthusiast and photographer, I was fascinated by two distinct and technically demanding photographic challenges: capturing the rare moment two aircraft appear to have a close encounter, and capturing the dramatic transit of a single aircraft across the sun or moon. Both types of events are incredibly fleeting, lasting only seconds, and their visibility is entirely dependent on the observer's precise location and timing. I realized that a purely observational approach was not just inefficient, but fundamentally limited by chance. This project was born out of a desire to create a scientific tool to solve this problem—to move from serendipity to predictable, planned photographic opportunities. The software achieves this by fusing real-time aeronautical data (ADS-B) with predictive geometry and celestial mechanics.

## Windows Desktop Demo

The older Windows desktop release remains available from previous GitHub Releases.

### Examples
![Example of a close encounter](assets/eg.jpg)
*<p align="center">A screenshot displaying a B747-8F and an IL-76 in close proximity.</p>*

## Screenshots

### S1: Mobile/Tailnet Web UI
![S1 Web UI](assets/Screenshot_5.jpg)

### S2: Settings And Receiver Configuration
![S2 Settings](assets/Screenshot_6.jpg)

### S3: Live Aviation Map
![S3 Live Map](assets/Screenshot_7.jpg)

### Network Architecture
![Linux Web Architecture](assets/image-2-linux-web-architecture.svg)

## Download And Install

```bash
mkdir -p ~/adsb-transit && cd ~/adsb-transit
wget -O ADS-B-Transit-Predictor-linux-web.tar.gz "https://github.com/RealSeaberry/ADS-B-Transit-Predictor/releases/latest/download/ADS-B-Transit-Predictor-linux-web-v1.3.0-20260504.tar.gz"
tar -xzf ADS-B-Transit-Predictor-linux-web.tar.gz
cd ADS-B-Transit-Predictor-linux-web-v1.3.0-20260504
./scripts/install_linux.sh
```

Open a new terminal, then start the receiver and Web UI:

```bash
adsb-web
```

Open:

* Local machine: `https://127.0.0.1:8090/`
* LAN/Tailscale device: `https://<server-ip>:8090/`

The HTTPS certificate is self-signed. Accept the browser warning on first visit.

## What The Installer Does

`scripts/install_linux.sh`:

* installs common Linux packages when `apt-get` is available
* creates `.venv`
* installs Python dependencies from `requirements.txt`
* registers the `adsb-web` launcher in your shell startup file

Useful installer overrides:

```bash
ADSB_SKIP_APT=1 ./scripts/install_linux.sh
ADSB_SKIP_PIP=1 ./scripts/install_linux.sh
ADSB_SHELL_RC=~/.bashrc ./scripts/install_linux.sh
```

## Configure usbipd For Windows + WSL

If the RTL-SDR receiver is plugged into Windows and the server runs in WSL, pass the USB device through with `usbipd`.

Install usbipd from Windows PowerShell if needed:

```powershell
winget install --interactive --exact dorssel.usbipd-win
```

List USB devices:

```powershell
usbipd list
```

Bind the RTL-SDR device once:

```powershell
usbipd bind --busid <busid>
```

Attach it to WSL:

```powershell
usbipd attach --wsl --busid <busid>
```

`adsb-web` can usually auto-detect and attach a common RTL-SDR receiver. If more than one receiver is connected, specify the BUSID manually:

```bash
ADSB_USB_BUSID=<busid> adsb-web
```

Skip usbipd for native Linux or an already attached receiver:

```bash
ADSB_SKIP_USBIPD=1 adsb-web
```

Confirm the receiver is visible inside Linux/WSL:

```bash
lsusb
rtl_test -t
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
