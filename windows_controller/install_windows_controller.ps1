param(
    [string]$InstallDir = "$env:LOCALAPPDATA\ADS-B Transit Predictor\Controller",
    [switch]$CreateDesktopShortcut = $true
)

$ErrorActionPreference = "Stop"
$SourceDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Exe = Join-Path $SourceDir "ADSBTransitController.exe"
$Py = Join-Path $SourceDir "adsb_windows_controller.py"
$InternalDir = Join-Path $SourceDir "_internal"

function Copy-IfExists($Source, $Destination) {
    if (Test-Path $Source) {
        if ((Get-Item $Source).PSIsContainer -and (Test-Path $Destination)) {
            Remove-Item $Destination -Recurse -Force
        }
        Copy-Item $Source $Destination -Recurse -Force
    }
}

function Assert-Controller-Runtime($Dir) {
    $RuntimeDir = Join-Path $Dir "_internal"
    if (-not (Test-Path (Join-Path $Dir "ADSBTransitController.exe"))) {
        return
    }
    if (-not (Test-Path $RuntimeDir)) {
        Write-Warning "Controller runtime folder _internal was not found. The controller may not start on clean Windows systems."
        return
    }
    $Required = @("VCRUNTIME140.dll", "ucrtbase.dll", "_tkinter.pyd", "tcl86t.dll", "tk86t.dll")
    foreach ($Name in $Required) {
        if (-not (Test-Path (Join-Path $RuntimeDir $Name))) {
            Write-Warning "Controller runtime dependency is missing: _internal\$Name"
        }
    }
    if (-not (Get-ChildItem -Path $RuntimeDir -Filter "python*.dll" -File -ErrorAction SilentlyContinue)) {
        Write-Warning "Controller runtime dependency is missing: _internal\python*.dll"
    }
}

New-Item -ItemType Directory -Force -Path $InstallDir | Out-Null

if (Test-Path $Exe) {
    Copy-Item $Exe $InstallDir -Force
    Copy-IfExists $InternalDir (Join-Path $InstallDir "_internal")
    Copy-IfExists (Join-Path $SourceDir "wsl_payload.tar.gz") $InstallDir
    Copy-IfExists (Join-Path $SourceDir "icon.ico") $InstallDir
    $Target = Join-Path $InstallDir "ADSBTransitController.exe"
} elseif (Test-Path $Py) {
    Copy-Item $Py $InstallDir -Force
    Copy-IfExists (Join-Path $SourceDir "wsl_payload.tar.gz") $InstallDir
    Copy-IfExists (Join-Path $SourceDir "icon.ico") $InstallDir
    $Target = "pythonw.exe"
    $Arguments = "`"$(Join-Path $InstallDir "adsb_windows_controller.py")`""
} else {
    throw "Controller executable or Python source was not found in $SourceDir"
}

Assert-Controller-Runtime $InstallDir

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
