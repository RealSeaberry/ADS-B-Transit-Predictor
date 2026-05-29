param(
    [string]$Distro = "",
    [string]$WslProjectDir = "",
    [switch]$KeepWslProject,
    [switch]$KeepWslRuntime,
    [switch]$Force,
    [string]$InstallDir = "$env:LOCALAPPDATA\ADS-B Transit Predictor\Controller",
    [switch]$RemoveUserConfig,
    [switch]$RemoveWslProject,
    [switch]$RemoveWslRuntimeConfig,
    [switch]$UnregisterDistro,
    [switch]$UninstallUsbipd
)

$ErrorActionPreference = "Stop"

function Distro-Args {
    if ($Distro) { return @("-d", $Distro) }
    return @()
}

function Encode-Base64Utf8($Text) {
    return [Convert]::ToBase64String([Text.Encoding]::UTF8.GetBytes([string]$Text))
}

function Load-LastInstall {
    $Path = Join-Path $env:APPDATA "ADS-B Transit Predictor\installations.json"
    if (-not (Test-Path $Path)) {
        return $null
    }
    try {
        $Data = Get-Content $Path -Raw -Encoding UTF8 | ConvertFrom-Json
        return $Data.last
    } catch {
        Write-Warning "Could not read install record: $Path"
        return $null
    }
}

if ($RemoveUserConfig -or $UnregisterDistro -or $UninstallUsbipd) {
    Write-Warning "Windows files, install records, WSL distro unregister, and usbipd-win are not removed by this uninstaller."
    Write-Warning "Delete Windows package files manually if you no longer need them."
}

if ($RemoveWslProject) { $KeepWslProject = $false }
if ($RemoveWslRuntimeConfig) { $KeepWslRuntime = $false }

$LastInstall = Load-LastInstall
if ($LastInstall) {
    if (-not $Distro -and $LastInstall.distro) {
        $Distro = [string]$LastInstall.distro
        Write-Host "[uninstall] Loaded WSL distro from install record: $Distro"
    }
    if (-not $WslProjectDir -and $LastInstall.wsl_project_dir) {
        $WslProjectDir = [string]$LastInstall.wsl_project_dir
        Write-Host "[uninstall] Loaded WSL project dir from install record: $WslProjectDir"
    }
}
if (-not $WslProjectDir) {
    $WslProjectDir = "~/ADS-B-Transit-Predictor"
}

if (-not (Get-Command wsl.exe -ErrorAction SilentlyContinue)) {
    Write-Warning "wsl.exe was not found. Nothing to clean inside WSL."
    Write-Host "[uninstall] Windows files were left untouched."
    exit 0
}

$DistroArgs = Distro-Args
$ProjectB64 = Encode-Base64Utf8 $WslProjectDir
$RemoveProjectFlag = if ($KeepWslProject) { "0" } else { "1" }
$RemoveRuntimeFlag = if ($KeepWslRuntime) { "0" } else { "1" }

Write-Host "[uninstall] Target WSL distro: $(if ($Distro) { $Distro } else { '<default>' })"
Write-Host "[uninstall] WSL project dir: $WslProjectDir"
Write-Host "[uninstall] Windows controller files will not be removed."

$Script = @'
import base64
import os
import pathlib
import re
import shutil
import signal
import subprocess
import sys

project_raw = base64.b64decode(os.environ["ADSB_UNINSTALL_PROJECT_B64"]).decode("utf-8")
project_dir = pathlib.Path(os.path.expanduser(project_raw)).resolve()
remove_project = os.environ.get("ADSB_UNINSTALL_REMOVE_PROJECT") == "1"
remove_runtime = os.environ.get("ADSB_UNINSTALL_REMOVE_RUNTIME") == "1"
home = pathlib.Path.home()

def log(message):
    print(f"[uninstall] {message}", flush=True)

def process_table():
    current = os.getpid()
    for entry in pathlib.Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        if pid == current:
            continue
        try:
            raw = (entry / "cmdline").read_bytes()
        except OSError:
            continue
        if not raw:
            continue
        cmdline = raw.replace(b"\x00", b" ").decode("utf-8", errors="ignore").strip()
        if cmdline:
            yield pid, cmdline

def stop_adsb_processes():
    markers = (
        "web_ui/server.py",
        "/scripts/start_adsb_web.sh",
        " dump1090-mutability",
        " dump1090-fa",
        " dump1090 ",
        " readsb",
    )
    victims = []
    for pid, cmdline in process_table():
        padded = f" {cmdline} "
        if any(marker in padded for marker in markers):
            victims.append((pid, cmdline))
    for pid, cmdline in victims:
        try:
            os.kill(pid, signal.SIGTERM)
            log(f"Stopped process {pid}: {cmdline[:120]}")
        except ProcessLookupError:
            pass
        except PermissionError as exc:
            log(f"Could not stop process {pid}: {exc}")
    if victims:
        import time
        time.sleep(1.0)
    for pid, cmdline in victims:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            continue
        try:
            os.kill(pid, signal.SIGKILL)
            log(f"Force-stopped process {pid}: {cmdline[:120]}")
        except ProcessLookupError:
            pass
        except PermissionError as exc:
            log(f"Could not force-stop process {pid}: {exc}")

log("Stopping ADS-B Web UI and decoder processes")
stop_adsb_processes()

if remove_runtime:
    log("Removing WSL runtime config, generated certificates, and shell launchers")
    shutil.rmtree(home / ".config" / "adsb-transit", ignore_errors=True)
    shutil.rmtree(project_dir / ".web_certs", ignore_errors=True)
    local_bin = home / ".local" / "bin"
    for name in ("adsb-web", "adsb-doctor"):
        candidate = local_bin / name
        try:
            if candidate.exists() or candidate.is_symlink():
                text = ""
                try:
                    text = candidate.read_text(encoding="utf-8", errors="ignore")
                except Exception:
                    pass
                if "ADS-B" in text or "start_adsb_web" in text or "doctor_linux" in text:
                    candidate.unlink()
                    log(f"Removed {candidate}")
        except Exception as exc:
            log(f"Could not remove {candidate}: {exc}")

    marker_re = re.compile(r"^\s*# ADS-B Transit Predictor launcher\s*$")
    source_re = re.compile(r"^\s*source\s+['\"]?.*ADS-B-Transit-Predictor/scripts/adsb_alias\.sh['\"]?\s*$")
    for rc_name in (".bashrc", ".zshrc", ".profile", ".bash_aliases"):
        rc_path = home / rc_name
        if not rc_path.exists():
            continue
        lines = rc_path.read_text(encoding="utf-8", errors="ignore").splitlines()
        new_lines = []
        i = 0
        changed = False
        while i < len(lines):
            line = lines[i]
            next_line = lines[i + 1] if i + 1 < len(lines) else ""
            if marker_re.match(line):
                changed = True
                i += 1
                if i < len(lines) and source_re.match(lines[i]):
                    i += 1
                continue
            if source_re.match(line):
                changed = True
                i += 1
                continue
            new_lines.append(line)
            i += 1
        if changed:
            rc_path.write_text("\n".join(new_lines).rstrip() + "\n", encoding="utf-8")
            log(f"Removed launcher lines from {rc_path}")

if remove_project:
    if project_dir in (home, pathlib.Path("/")):
        raise SystemExit(f"Refusing to remove unsafe project directory: {project_dir}")
    log(f"Removing WSL project directory: {project_dir}")
    shutil.rmtree(project_dir, ignore_errors=True)

log("WSL cleanup complete")
'@

# Encode the cleanup script as base64 so it survives Windows command-line
# argument passing intact (newlines in -c arguments are not reliable on Windows).
$ScriptB64 = [Convert]::ToBase64String([Text.Encoding]::UTF8.GetBytes($Script))

& wsl.exe @DistroArgs env `
    "ADSB_UNINSTALL_PROJECT_B64=$ProjectB64" `
    "ADSB_UNINSTALL_REMOVE_PROJECT=$RemoveProjectFlag" `
    "ADSB_UNINSTALL_REMOVE_RUNTIME=$RemoveRuntimeFlag" `
    "ADSB_UNINSTALL_SCRIPT_B64=$ScriptB64" `
    python3 -c "import base64,os; exec(base64.b64decode(os.environ['ADSB_UNINSTALL_SCRIPT_B64']).decode('utf-8'))"
if ($LASTEXITCODE -ne 0) {
    throw "WSL cleanup failed with exit code $LASTEXITCODE"
}

Write-Host "[uninstall] Complete. Windows package/controller files were left untouched."
Write-Host "[uninstall] Delete the extracted Windows release folder manually when you are ready."
