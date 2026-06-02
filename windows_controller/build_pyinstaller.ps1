$ErrorActionPreference = "Stop"
$Root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $Root

python -m PyInstaller --version | Out-Null

if (-not (Test-Path ".\wsl_payload.tar.gz")) {
    throw "Missing wsl_payload.tar.gz"
}

python -m PyInstaller .\adsb_windows_controller.spec --clean --noconfirm
python -m PyInstaller .\adsb_installer_launcher.py --onefile --windowed --name ADSBTransitInstaller --icon .\icon.ico --add-data "icon.ico;." --clean --noconfirm --noupx
python -m PyInstaller .\adsb_uninstaller_launcher.py --onefile --windowed --name ADSBTransitUninstaller --icon .\icon.ico --add-data "icon.ico;." --clean --noconfirm --noupx

$PackageDir = Join-Path $Root "ADSBTransitController-package"
Remove-Item $PackageDir -Recurse -Force -ErrorAction SilentlyContinue
New-Item -ItemType Directory -Force -Path $PackageDir | Out-Null
Copy-Item ".\dist\ADSBTransitController\*" $PackageDir -Recurse -Force
Copy-Item ".\dist\ADSBTransitInstaller.exe" $PackageDir -Force
Copy-Item ".\dist\ADSBTransitUninstaller.exe" $PackageDir -Force
Copy-Item ".\wsl_payload.tar.gz" $PackageDir -Force
Copy-Item ".\icon.ico" $PackageDir -Force
Copy-Item ".\adsb_windows_controller.py" $PackageDir -Force
Copy-Item ".\adsb_installer_launcher.py" $PackageDir -Force
Copy-Item ".\adsb_uninstaller_launcher.py" $PackageDir -Force
Copy-Item ".\install_windows_controller.ps1" $PackageDir -Force
Copy-Item ".\uninstall_windows_controller.ps1" $PackageDir -Force
Copy-Item ".\bootstrap_all_windows.ps1" $PackageDir -Force
Copy-Item ".\uninstall_all_windows.ps1" $PackageDir -Force
Copy-Item ".\README.md" $PackageDir -Force
Copy-Item ".\README_WINDOWS_CONTROLLER_PACKAGE.md" $PackageDir -Force

Write-Host "Built package: $PackageDir"
