param(
    [string]$InstallDir = "$env:LOCALAPPDATA\ADS-B Transit Predictor\Controller",
    [string]$Distro = "",
    [string]$WslProjectDir = "",
    [switch]$KeepWslProject,
    [switch]$KeepWslRuntime,
    [switch]$RemoveUserConfig,
    [switch]$RemoveWslProject
)

$ErrorActionPreference = "Stop"
$SourceDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$DeepUninstall = Join-Path $SourceDir "uninstall_all_windows.ps1"

if (-not (Test-Path $DeepUninstall)) {
    throw "Missing $DeepUninstall"
}

Write-Warning "This uninstaller no longer removes Windows controller files."
Write-Warning "It cleans only WSL-side ADS-B files and aliases. Delete Windows files manually when ready."

$UninstallArgs = @(
    "-ExecutionPolicy", "Bypass",
    "-File", $DeepUninstall
)
if ($Distro) { $UninstallArgs += @("-Distro", $Distro) }
if ($WslProjectDir) { $UninstallArgs += @("-WslProjectDir", $WslProjectDir) }
if ($KeepWslProject) { $UninstallArgs += "-KeepWslProject" }
if ($KeepWslRuntime) { $UninstallArgs += "-KeepWslRuntime" }

powershell.exe @UninstallArgs
