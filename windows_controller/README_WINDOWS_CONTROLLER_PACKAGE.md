# ADS-B Transit Windows Controller

Windows Controller is a small Windows app for managing the ADS-B Transit Predictor Linux/WSL Web Server. The receiver, prediction engine, and Web UI still run inside WSL; the Windows app only handles setup, configuration, USB forwarding, process control, and opening the browser.

## What It Includes

The release package contains:

- `ADSBTransitInstaller.exe` - guided installer for copying the controller and installing/updating the WSL server payload.
- `ADSBTransitController.exe` - Windows UI for starting, stopping, and configuring the WSL server.
- `ADSBTransitUninstaller.exe` - guided WSL-side cleanup tool.
- `_internal/wsl_payload.tar.gz` - sanitized Linux/WSL server files and bundled data.
- PowerShell scripts for manual install, update, and uninstall workflows.

## Requirements

Install and initialize WSL before running the installer. Ubuntu 22.04 or newer is recommended; Ubuntu 24.04 is supported. WSL2 is recommended for USB forwarding and networking.

For RTL-SDR receivers connected to Windows, install `usbipd-win` or let the installer install it when requested. Tailscale is optional and only needed if you want to access the Web UI from another device over a private tailnet.

## Install

1. Extract the release package.
2. Run `ADSBTransitInstaller.exe`.
3. Select the target WSL distro. If only one distro exists, it is selected automatically.
4. Keep the default WSL project directory unless you need a custom path.
5. Choose whether to allow LAN/Tailscale access and whether to install `usbipd-win`.
6. Click **Install** and wait for the log to finish.

The installer records the selected distro and install paths under:

```text
%APPDATA%\ADS-B Transit Predictor\installations.json
```

This lets future updates and the uninstaller reuse the same target without redesigning the package.

## Controller Use

Open **ADS-B Transit Controller** from the Start Menu or desktop shortcut.

Common flow:

1. Confirm the **WSL distro** and **WSL project dir**.
2. Set **Access mode**:
   - `local`: Windows browser on this PC, usually `https://127.0.0.1:8090/`.
   - `lan`: bind to all WSL interfaces for trusted LAN access.
   - `tailscale`: bind to all WSL interfaces and use the Tailscale IP shown by **Show URLs**.
3. Set receiver options on the **Receiver** tab.
4. Click **Start Server**.
5. The browser opens only after the Web UI has actually started listening.

The controller hides child terminals for `wsl.exe`, PowerShell, `usbipd`, and server startup so users should not see or accidentally close a black console window.

## Receiver Notes

Default `Decoder mode` is `auto`. For RTL-SDR / RTL2832U devices, the controller can auto-detect the USB BUSID, attach it through usbipd, grant WSL USB device access, then start `dump1090-mutability` inside WSL without an interactive sudo prompt.

Use `external` when another decoder already provides SBS/BaseStation data on the configured SBS port. Use `custom decoder cmd` for Airspy, SDRplay, Beast, readsb, or remote receiver setups.

## Access URLs

Use **Show URLs** to print local, LAN, and Tailscale URLs when available.

- On the Windows host, `127.0.0.1` normally reaches WSL2 services through localhost forwarding.
- On a phone/tablet, do not use `127.0.0.1`; use the Windows LAN IP or Tailscale IP.
- HTTPS is used because browser geolocation requires a secure context outside localhost. The certificate is self-signed, so the browser will show a first-use warning.

## Update

For a same-version test update, extract the newer package and run `ADSBTransitInstaller.exe` again against the same distro and WSL project directory. It will replace the WSL project files and controller executable while preserving runtime config where appropriate.

## Uninstall

Run `ADSBTransitUninstaller.exe`.

By default it removes only the WSL-side ADS-B installation:

- stops ADS-B Web UI and decoder processes
- removes the selected WSL project directory
- removes `~/.config/adsb-transit`
- removes generated HTTPS certs
- removes shell launcher lines from `.bashrc`, `.zshrc`, `.profile`, and `.bash_aliases`
- removes old `~/.local/bin/adsb-web` / `adsb-doctor` launchers if present

It reads `%APPDATA%\ADS-B Transit Predictor\installations.json` to target the distro and project directory used by the installer. It does not remove Windows files, Windows shortcuts, install records, `usbipd-win`, or the WSL distro itself. Delete the extracted Windows release folder manually when you no longer need it.

## Manual Scripts

Advanced users can run the PowerShell scripts directly:

```powershell
powershell -ExecutionPolicy Bypass -File .\bootstrap_all_windows.ps1 -Distro Ubuntu
powershell -ExecutionPolicy Bypass -File .\uninstall_all_windows.ps1
```

Use `-AllowLanAccess` only on trusted private networks, preferably with Tailscale.
