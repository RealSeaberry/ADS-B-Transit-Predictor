param(
    [string]$InstallDir = "$env:LOCALAPPDATA\ADS-B Transit Predictor\Controller",
    [switch]$CreateDesktopShortcut = $true
)

$ErrorActionPreference = "Stop"
$SourceDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Exe = Join-Path $SourceDir "ADSBTransitController.exe"
$Py = Join-Path $SourceDir "adsb_windows_controller.py"

New-Item -ItemType Directory -Force -Path $InstallDir | Out-Null

if (Test-Path $Exe) {
    Copy-Item $Exe $InstallDir -Force
    if (Test-Path (Join-Path $SourceDir "wsl_payload.tar.gz")) {
        Copy-Item (Join-Path $SourceDir "wsl_payload.tar.gz") $InstallDir -Force
    }
    $Target = Join-Path $InstallDir "ADSBTransitController.exe"
} elseif (Test-Path $Py) {
    Copy-Item $Py $InstallDir -Force
    if (Test-Path (Join-Path $SourceDir "wsl_payload.tar.gz")) {
        Copy-Item (Join-Path $SourceDir "wsl_payload.tar.gz") $InstallDir -Force
    }
    $Target = "pythonw.exe"
    $Arguments = "`"$(Join-Path $InstallDir "adsb_windows_controller.py")`""
} else {
    throw "Controller executable or Python source was not found in $SourceDir"
}

if ($CreateDesktopShortcut) {
    $Desktop = [Environment]::GetFolderPath("Desktop")
    $ShortcutPath = Join-Path $Desktop "ADS-B Transit Controller.lnk"
    $Shell = New-Object -ComObject WScript.Shell
    $Shortcut = $Shell.CreateShortcut($ShortcutPath)
    $Shortcut.TargetPath = $Target
    if ($Arguments) { $Shortcut.Arguments = $Arguments }
    $Shortcut.WorkingDirectory = $InstallDir
    $Shortcut.Save()
}

$StartMenu = Join-Path $env:APPDATA "Microsoft\Windows\Start Menu\Programs\ADS-B Transit Predictor"
New-Item -ItemType Directory -Force -Path $StartMenu | Out-Null
$StartShortcut = Join-Path $StartMenu "ADS-B Transit Controller.lnk"
$Shell = New-Object -ComObject WScript.Shell
$Shortcut = $Shell.CreateShortcut($StartShortcut)
$Shortcut.TargetPath = $Target
if ($Arguments) { $Shortcut.Arguments = $Arguments }
$Shortcut.WorkingDirectory = $InstallDir
$Shortcut.Save()

Write-Host "Installed ADS-B Transit Controller to $InstallDir"
if (Get-Command wsl.exe -ErrorAction SilentlyContinue) {
    Write-Host ""
    Write-Host "Detected WSL distros:"
    $WslList = [string]::Join("`n", (& wsl.exe -l -v 2>$null))
    Write-Host $WslList.Replace([string][char]0, "")
    Write-Host ""
    Write-Host "Use bootstrap_all_windows.ps1 or the controller to install/update WSL project files and start adsb-web."
} else {
    Write-Warning "WSL was not found. Install and initialize WSL first, then run bootstrap_all_windows.ps1."
}
