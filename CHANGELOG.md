# Changelog

All notable user-facing changes are documented here.

## 2026-06-01 - v1.4.1 Linux/WSL Compatibility Update

### Added

* Added optional EGM96/EGM2008 geoid correction for dump1090-fa `alt_geom`.
  * Supports GeographicLib `.pgm` grids and the NGA EGM96 `WW15MGH.DAC` file.
  * Converts WGS84 ellipsoid height to approximate MSL before computing per-aircraft altitude correction factors.
  * The Settings UI shows EGM controls only when local geoid data files are present.
* Added a top-level Dev settings switch. GPS altitude correction and EGM controls are hidden unless Dev is enabled.

### Changed

* Fixed the main altitude stability path for prediction and display.
  * 2D/3D aircraft position and visible tracks use stable barometric altitude.
  * Corrected altitude is available as a label field, but GPS/JSON altitude correction is isolated behind Dev options.
  * METAR correction remains the normal fallback for event geometry without forcing unstable GPS altitude jumps into the map view.
* Improved Linux/WSL installation and runtime stability across clean systems.
* Improved compatibility with native Linux, WSL, and existing local ADS-B decoder setups.

## 2026-05-15 - Windows Controller Preview

### Added

* Added a Windows-side controller prototype for managing the WSL Linux Web Server version.
  * Installs or updates the WSL project files from a bundled `wsl_payload.tar.gz`.
  * Starts, stops, and restarts the existing WSL server scripts.
  * Opens the Web UI from Windows.
  * Runs the existing WSL doctor script.
  * Shows `usbipd` USB devices from Windows.
  * Adds local/LAN/Tailscale access mode controls, access URL display, Tailscale status, Tailscale URL copy, SDR USB auto-detection/attach, observer location writing, and Windows autostart shortcut controls.
* Added PyInstaller build files for creating a Windows controller executable.
* Added Windows installer and uninstaller PowerShell scripts.
* Added an all-in-one Windows bootstrap script for controller installation, WSL payload deployment, runtime config generation, and Linux dependency installation.
  * For safety, it now requires WSL and the selected distro to be installed first instead of enabling/installing WSL automatically.
  * Web UI binding defaults to `127.0.0.1`; LAN exposure requires an explicit `-AllowLanAccess` flag.
  * `usbipd-win` installation is optional and requires an explicit `-InstallUsbipd` flag.
* Added a deep Windows uninstaller that can optionally remove the WSL project, WSL runtime config, WSL distro, and usbipd-win.

### Notes

* The prediction server, Web UI, `adsb-web`, and `adsb-doctor` remain the existing Linux/WSL implementation.
* The Windows controller is a control surface, not a second prediction engine.
* The bundled WSL payload excludes local certificates, local Web UI preferences, virtual environments, caches, Git metadata, and private runtime files.

## 2026-05-12 - Prediction Stability And UI Responsiveness Update

### Added

* Added `event_min_elevation_deg`, default `2.0`, to suppress very low elevation transit/event predictions near the horizon.
* Added conservative likely-landed aircraft detection for low-speed, low-vertical-speed targets near airport pavement.
  * Likely-landed aircraft remain visible on the map.
  * They are excluded from event/transit prediction to reduce stale-position false positives.

### Changed

* Improved aircraft label placement stability so overlap avoidance keeps a stable side for each aircraft instead of flickering between positions.
* Decoupled aircraft view-state caching from synchronous `/api/state` responses so map/UI refresh is less affected by prediction workload.
* AC-AC, AC-Sun, AC-Moon, and transit-strip calculations now honor the minimum event elevation setting.

### Fixed

* Fixed label overlap avoidance oscillating when two valid label positions alternated between frames.
* Fixed low-elevation airport-area false event reports caused by aircraft near the horizon.
* Fixed stale airborne ADS-B positions from recently landed aircraft continuing to generate event predictions after ground speed dropped very low.

## 2026-05-08 - Linux Web Server Update

This update focuses on making the Linux/WSL Web UI release easier to install, easier to diagnose, and more reliable for live ADS-B transit prediction.

### Added

* Added a cross-distribution Linux installer: `scripts/install_linux.sh`.
  * Supports `apt`, `dnf`, `yum`, `pacman`, and `zypper` where available.
  * Creates a project `.venv` and installs Python dependencies.
  * Creates a persistent runtime configuration file at `~/.config/adsb-transit/adsb-web.env`.
  * Registers `adsb-web` and `adsb-doctor` launcher aliases.
* Added `scripts/doctor_linux.sh` / `adsb-doctor` for troubleshooting.
  * Checks Python dependencies, decoder commands, SBS/Web ports, WSL detection, `usbipd`, and attached USB devices.
* Added more flexible SDR and decoder startup modes.
  * Default RTL-SDR / RTL2832U path still uses `dump1090` or `dump1090-mutability`.
  * External decoder mode supports existing local or remote SBS/BaseStation feeds.
  * Custom decoder command mode supports Airspy, SDRplay, Beast, readsb, or other decoder setups that provide SBS output.
* Added persistent runtime settings via `ADSB_ENV_FILE`.
* Added high-resolution GSHHG coastline and land-fill map layers.
  * `GSHHG High Coastline` draws coastline strokes.
  * `GSHHG High Land Fill` draws land fill without duplicate coastline strokes.
* Added a higher precision viewport-aware map data request path for wide and tall screens.

### Changed

* Improved Web UI installation flow for first-time Linux/WSL users.
* Improved README guidance for release asset selection, Linux setup, WSL USB forwarding, Tailscale, HTTPS, and browser GPS.
* Improved map rendering performance during panning and zooming.
* Improved geographic map coverage so aircraft and high-resolution map data are not limited to a central square on wide or tall screens.
* Improved event prediction stability by using recent averaged aircraft motion for prediction inputs.
* Simplified and optimized transit/event calculation paths to reduce CPU load during live use.
* Separated speed vector length from aircraft history trail length.
* Improved trajectory rendering and active aircraft history handling.
* Updated vector layer naming and settings descriptions for clearer map controls.

### Fixed

* Fixed `ModuleNotFoundError: No module named 'numpy'` after launch by making the installer create and use the project virtual environment.
* Fixed velocity vector length being affected by trajectory length settings.
* Fixed short aircraft tracks when a longer track duration is configured.
* Fixed viewport mismatch where geographic maps and aircraft disappeared outside the center square on non-square screens.
* Fixed GSHHG land fill and coastline duplication by separating fill and stroke layers.
* Fixed map panning stutter by decoupling map refresh behavior from event prediction work.
* Fixed pinch-zoom instability on touch devices.
* Fixed several settings toggles and layer names that did not match current data.

### Notes

* The project source remains MIT licensed.
* Local runtime config, HTTPS certificates, private keys, and user-specific settings are not intended to be committed or included in release packages.
* OpenAIP airway support was evaluated but not added in this update.
* The older Windows desktop package remains available from older GitHub Releases.
