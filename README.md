# ADS-B Transit Predictor

A real-time visualization and prediction tool for aircraft transits across the Sun and Moon, plus aircraft-to-aircraft close visual encounters, using live ADS-B data.

## Motivation
As an aviation enthusiast and photographer, I was fascinated by two distinct and technically demanding photographic challenges: capturing the rare moment two aircraft appear to have a close encounter, and capturing the dramatic transit of a single aircraft across the sun or moon. Both types of events are incredibly fleeting, lasting only seconds, and their visibility is entirely dependent on the observer's precise location and timing. I realized that a purely observational approach was not just inefficient, but fundamentally limited by chance. This project was born out of a desire to create a scientific tool to solve this problem—to move from serendipity to predictable, planned photographic opportunities. The software achieves this by fusing real-time aeronautical data (ADS-B) with predictive geometry and celestial mechanics.

## Which Version Should I Download?

| Use case | Recommended package | Interface | Notes |
|---|---|---|---|
| Windows desktop app | Older Windows Desktop release | Pygame / Tk desktop UI | Use this if you want the previous `.exe` workflow. |
| Linux / WSL server | Latest Linux Web Server release | Browser Web UI | Use this for WSL, LAN/Tailscale access, mobile viewing, HTTPS GPS support, and `adsb-web`. |

Download packages from the [GitHub Releases page](https://github.com/RealSeaberry/ADS-B-Transit-Predictor/releases).

The latest Linux package is intended to be downloaded as:

```bash
mkdir -p ~/adsb-transit && cd ~/adsb-transit
wget -O ADS-B-Transit-Predictor-linux-web.tar.gz "https://github.com/RealSeaberry/ADS-B-Transit-Predictor/releases/latest/download/ADS-B-Transit-Predictor-linux-web.tar.gz"
tar -xzf ADS-B-Transit-Predictor-linux-web.tar.gz
cd ADS-B-Transit-Predictor-*
./scripts/install_linux.sh
```

For full Linux/WSL setup, including `usbipd`, Tailscale, HTTPS self-signed certificates, browser GPS, and `adsb-web`, read [README_LINUX_WEB.md](README_LINUX_WEB.md).

## Key Features

* **Real-time flight tracking:** Reads live SBS/BaseStation ADS-B messages from dump1090 or another compatible decoder.
* **Sun/Moon transit prediction:** Predicts whether an aircraft will cross the apparent disc of the Sun or Moon from the observer location.
* **Aircraft-to-aircraft close encounters:** Detects rare visual convergence opportunities between two aircraft.
* **High-precision geometry:** Uses Skyfield, WGS84 geodetic conversions, and refined closest-approach searches.
* **Geospatial context:** Uses Natural Earth vector data and OurAirports airport, runway, and navaid data.
* **Linux Web UI:** Provides a browser-based HTTPS interface for LAN, Tailscale, mobile, and tablet access.
* **Windows desktop release:** Older releases remain available for users who prefer the packaged desktop `.exe`.

## Linux Web Server Preview

### S1: Mobile/Tailnet Web UI
![S1 Web UI](assets/Screenshot_5.jpg)

### S2: Settings And Receiver Configuration
![S2 Settings](assets/Screenshot_6.jpg)

### S3: Live Aviation Map
![S3 Live Map](assets/Screenshot_7.jpg)

### Linux/WSL Network Architecture
![Linux Web Architecture](assets/image-2-linux-web-architecture.svg)

## Windows Desktop Preview

The earlier Windows release uses the original desktop interface. It remains available from older GitHub Releases.

### Windows Main Interface
![Windows Main Interface](assets/Screenshot_1.png)

### Windows Configuration
![Windows Configuration](assets/Screenshot_2.png)

### Windows Transit Map
![Windows Transit Map](assets/Screenshot_3.png)

### Windows POV Preview
![Windows POV Preview](assets/Screenshot_4.png)

## Windows Desktop Demo

### Examples
![Example of a close encounter](assets/eg.jpg)
*<p align="center">A screenshot displaying a B747-8F and an IL-76 in close proximity.</p>*

## Technical Stack

* **Core logic:** Python 3
* **Astronomy:** Skyfield with JPL DE421 ephemeris
* **Geodesy:** WGS84 Earth model
* **Map/vector processing:** NumPy, Shapely, PyShp, Natural Earth
* **Aviation data:** OurAirports airports, runways, and navaids
* **Windows desktop UI:** Pygame and Tkinter
* **Linux Web UI:** Python HTTP server, HTML Canvas, HTTPS, local vector map rendering
* **ADS-B decoder:** dump1090 / dump1090-mutability SBS output

## Release And Version Policy

This repository keeps one shared Git history for ADS-B Transit Predictor. Windows desktop and Linux web-server packages are release assets built from tagged states of that history; they are not separate repositories.

Older Windows releases remain preserved by their existing tags and GitHub Release pages. Publishing a new Linux web-server release does not delete or overwrite those assets. Users who need the Windows `.exe` should download the older Windows release asset from the Releases page.

Release packages may contain platform-specific README content:

* The repository README is a version-selection entry point.
* The Linux `.tar.gz` package uses a Linux-focused README with `usbipd`, Tailscale, HTTPS, GPS, and `adsb-web` setup.
* A future Windows package can include a Windows-focused README for the desktop `.exe` workflow.

Suggested release assets:

* `ADS-B-Transit-Predictor-linux-web.tar.gz`
* `ADS-B-Transit-Predictor-vX.Y.Z-linux-web.tar.gz`
* `ADS-B-Transit-Predictor-vX.Y.Z-windows.zip`

## Acknowledgements

* **Data sources:** Natural Earth and OurAirports.
* **Scientific models:** JPL DE421 ephemeris and WGS84.
* **ADS-B decoding:** dump1090, originally by Salvatore Sanfilippo, distributed under BSD 3-Clause license.

## License

This project is licensed under the [MIT License](LICENSE).
