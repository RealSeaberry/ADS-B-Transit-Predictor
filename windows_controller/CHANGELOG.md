# Changelog

All notable user-facing changes for the Windows Controller package are documented here.

## 2026-06-01 - v1.4.1 Windows Controller Package

### Added

* Added a bundled Linux/WSL server payload based on ADS-B Transit Predictor v1.4.1.
* Added full Windows runtime files in `_internal/`, including packaged Python, Tk, Visual C++ runtime, and Universal CRT dependencies.
* Added clearer WSL distro selection display in the installer:
  * The installer now shows distro name, WSL version, running state, and whether it is the Windows default distro.
  * The install log now prints the exact selected target distro before running bootstrap.
  * Bootstrap output marks `selected` separately from `Windows default`.

### Changed

* Rebuilt the Windows controller, installer, and uninstaller with Windows Python 3.12.3 and PyInstaller 6.11.1.
* Changed the release ZIP layout to a flat user-facing package:
  * `ADSBTransitInstaller.exe`, `ADSBTransitController.exe`, and `ADSBTransitUninstaller.exe` are now at the top level after extraction.
  * Development-only source/spec/build files are no longer duplicated in the downloadable ZIP.
* Improved Windows controller installation robustness:
  * `install_windows_controller.ps1` now copies the complete `_internal` runtime folder with the controller executable.
  * Existing `_internal` runtime files are replaced during update to avoid mixed old/new DLLs.
  * Runtime validation warns if key DLLs are missing.
* Disabled UPX for future PyInstaller builds to reduce antivirus and runtime compatibility issues.
* Improved WSL/Linux dependency installation through the Windows bootstrap:
  * Linux system package installation runs as WSL root.
  * Python virtual environment and user launcher setup run as the default WSL user.
  * The Linux payload installer includes tkinter, Python headers, build tools, RTL-SDR utilities, `usbutils`, `iproute2`, and decoder package fallbacks where available.

### Fixed

* Fixed controller startup failures caused by installing only `ADSBTransitController.exe` without the adjacent `_internal` runtime directory.
* Fixed confusing installer logs where the WSL `*` default marker could be mistaken for the selected distro.
* Fixed nested release ZIP layout that placed the usable EXE files under an extra `ADSBTransitController-package/` folder.
* Fixed Windows bootstrap runtime config generation so it no longer depends on Python being installed inside WSL before dependency installation.

### Notes

* The Windows Controller remains a control surface for the Linux/WSL server; the prediction engine and Web UI still run in WSL.
* Users should run `ADSBTransitInstaller.exe` from the extracted package. Do not move `ADSBTransitController.exe` without `_internal/`.
