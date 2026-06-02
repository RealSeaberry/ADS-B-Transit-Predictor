param(
    [string]$InstallDir = "$env:LOCALAPPDATA\ADS-B Transit Predictor\Controller",
    [string]$Distro = "",
    [string]$WslProjectDir = "~/ADS-B-Transit-Predictor",
    [string]$WebHost = "127.0.0.1",
    [string]$WebPort = "8090",
    [string]$SbsPort = "30003",
    [string]$DecoderMode = "auto",
    [string]$Gain = "-10",
    [string]$DeviceIndex = "0",
    [string]$UsbBusId = "",
    [switch]$AllowLanAccess,
    [switch]$InstallUsbipd,
    [switch]$SkipLinuxDependencies,
    [switch]$NoDesktopShortcut
)

$ErrorActionPreference = "Stop"
$SourceDir = Split-Path -Parent $MyInvocation.MyCommand.Path

function Test-Admin {
    $Identity = [Security.Principal.WindowsIdentity]::GetCurrent()
    $Principal = New-Object Security.Principal.WindowsPrincipal($Identity)
    return $Principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

function Require-Admin {
    if (-not (Test-Admin)) {
        throw "Administrator PowerShell is required for this optional system change. Re-run PowerShell as Administrator or skip the option."
    }
}

function Restart-AsAdmin {
    if (Test-Admin) {
        return
    }
    $Args = @("-NoProfile", "-ExecutionPolicy", "Bypass", "-File", "`"$PSCommandPath`"")
    $Args += "-InstallDir"; $Args += "`"$InstallDir`""
    if ($Distro) { $Args += "-Distro"; $Args += "`"$Distro`"" }
    $Args += "-WslProjectDir"; $Args += "`"$WslProjectDir`""
    $Args += "-WebHost"; $Args += "`"$WebHost`""
    $Args += "-WebPort"; $Args += "`"$WebPort`""
    $Args += "-SbsPort"; $Args += "`"$SbsPort`""
    $Args += "-DecoderMode"; $Args += "`"$DecoderMode`""
    $Args += "-Gain"; $Args += "`"$Gain`""
    $Args += "-DeviceIndex"; $Args += "`"$DeviceIndex`""
    if ($UsbBusId) { $Args += "-UsbBusId"; $Args += "`"$UsbBusId`"" }
    if ($AllowLanAccess) { $Args += "-AllowLanAccess" }
    if ($InstallUsbipd) { $Args += "-InstallUsbipd" }
    if ($SkipLinuxDependencies) { $Args += "-SkipLinuxDependencies" }
    if ($NoDesktopShortcut) { $Args += "-NoDesktopShortcut" }
    Write-Host "[bootstrap] Administrator permission is needed for this optional system change."
    Write-Host "[bootstrap] Relaunching installer as Administrator..."
    Start-Process powershell.exe -Verb RunAs -ArgumentList $Args
    exit 0
}

function Have-Command($Name) {
    return [bool](Get-Command $Name -ErrorAction SilentlyContinue)
}

function Ensure-Winget {
    if (-not (Have-Command winget)) {
        throw "winget was not found. Install App Installer from Microsoft Store, then run this bootstrap again."
    }
}

function Ensure-Wsl {
    if (-not (Have-Command wsl.exe)) {
        throw @"
WSL is not installed.

For safety, this installer does not enable Windows optional features or install WSL automatically.
Please install WSL first, reboot if Windows asks, create your Linux user, then run this installer again.

Recommended command in Administrator PowerShell:
  wsl --install -d Ubuntu
"@
    }

    $RawWslList = Get-WslListRaw
    $Distros = Get-WslDistros $RawWslList
    Write-WslDistroList $Distros $RawWslList
    if ($Distros.Count -eq 0) {
        throw @"
No initialized WSL distro was found.

For safety, this installer does not create a distro automatically.
Please install and initialize Ubuntu 22.04 or newer first, then run this installer again:
  wsl --install -d Ubuntu-22.04
"@
    }

    if ($Distro) {
        $Match = @($Distros | Where-Object { $_.Name -eq $Distro })
        if ($Match.Count -gt 0) {
            $script:Distro = $Match[0].Name
            Write-Host "[bootstrap] WSL distro selected: $($Match[0].Name) (WSL$($Match[0].Version), $($Match[0].State))"
            Warn-WslVersion $Match[0]
            return
        }

        $Available = ($Distros | ForEach-Object { "  $($_.Name)  WSL$($_.Version)  $($_.State)" }) -join "`n"
        throw @"
WSL distro '$Distro' was not found.

Installed distros:
$Available
"@
    }

    $Selected = Select-WslDistroAuto $Distros
    $script:Distro = $Selected.Name
    Write-Host "[bootstrap] WSL distro selected: $($Selected.Name) (WSL$($Selected.Version), $($Selected.State))"
    Warn-WslVersion $Selected
}

function Get-WslListRaw {
    $Raw = [string]::Join("`n", (& wsl.exe -l -v 2>$null))
    return $Raw.Replace([string][char]0, "")
}

function Get-WslDistroNamesRaw {
    $Raw = [string]::Join("`n", (& wsl.exe -l -q 2>$null))
    return $Raw.Replace([string][char]0, "")
}

function Get-WslDistros($Raw) {
    $VerboseRows = @()
    foreach ($Line in ($Raw -split "`r?`n")) {
        $Clean = $Line.Trim()
        if (-not $Clean -or $Clean -match "^NAME\s+STATE\s+VERSION") {
            continue
        }
        $IsDefault = $Clean.StartsWith("*")
        $Clean = $Clean.TrimStart("*").Trim()
        if ($Clean -match "^(?<Name>.+?)\s{2,}(?<State>\S+)\s+(?<Version>\d+)$") {
            $VerboseRows += [pscustomobject]@{
                Name = $Matches.Name.Trim()
                State = $Matches.State
                Version = [int]$Matches.Version
                Default = $IsDefault
            }
        } elseif ($Clean -match "^(?<Name>\S+)\s+(?<State>\S+)\s+(?<Version>\d+)$") {
            $VerboseRows += [pscustomobject]@{
                Name = $Matches.Name.Trim()
                State = $Matches.State
                Version = [int]$Matches.Version
                Default = $IsDefault
            }
        }
    }

    $Rows = @()
    $NamesRaw = Get-WslDistroNamesRaw
    foreach ($Line in ($NamesRaw -split "`r?`n")) {
        $Name = $Line.Trim()
        if ($Name) {
            $Match = @($VerboseRows | Where-Object { $_.Name -eq $Name })
            if ($Match.Count -gt 0) {
                $Rows += $Match[0]
            } else {
                $Rows += [pscustomobject]@{
                    Name = $Name
                    State = "Unknown"
                    Version = 0
                    Default = ($Rows.Count -eq 0)
                }
            }
        }
    }
    if ($Rows.Count -eq 0) {
        $Rows = $VerboseRows
    }
    return @($Rows)
}

function Write-WslDistroList($Distros, $Raw) {
    Write-Host ""
    Write-Host "Installed WSL distros:"
    if ($Distros.Count -gt 0) {
        for ($Index = 0; $Index -lt $Distros.Count; $Index++) {
            $SelectedMark = if ($Distro -and ($Distros[$Index].Name -eq $Distro)) { " selected" } else { "" }
            $DefaultMark = if ($Distros[$Index].Default) { " Windows default" } else { "" }
            $VersionText = if ($Distros[$Index].Version -gt 0) { "WSL$($Distros[$Index].Version)" } else { "WSL?" }
            Write-Host ("  [{0}] {1}  {2}  {3}{4}{5}" -f ($Index + 1), $Distros[$Index].Name, $VersionText, $Distros[$Index].State, $SelectedMark, $DefaultMark)
        }
    } else {
        Write-Host "  Could not parse WSL distro rows. Raw output:"
        foreach ($Line in ($Raw -split "`r?`n")) {
            if ($Line.Trim()) {
                Write-Host "  $Line"
            }
        }
    }
    Write-Host ""
}

function Select-WslDistroAuto($Distros) {
    $Default = @($Distros | Where-Object { $_.Default })
    if ($Default.Count -gt 0) {
        Write-Host "[bootstrap] Auto-selecting default WSL distro. To choose another distro, rerun with -Distro <name>."
        return $Default[0]
    }
    Write-Host "[bootstrap] Auto-selecting first listed WSL distro. To choose another distro, rerun with -Distro <name>."
    return $Distros[0]
}

function Find-WslPayload {
    $Candidates = @(
        (Join-Path $SourceDir "wsl_payload.tar.gz"),
        (Join-Path $SourceDir "_internal\wsl_payload.tar.gz")
    )
    foreach ($Candidate in $Candidates) {
        if (Test-Path $Candidate) {
            return $Candidate
        }
    }
    throw "Missing WSL payload. Checked: $($Candidates -join ', ')"
}

function Convert-WindowsPathToWslPath($Path) {
    $FullPath = [IO.Path]::GetFullPath($Path)
    if ($FullPath -match '^([A-Za-z]):\\(.*)$') {
        $Drive = $Matches[1].ToLowerInvariant()
        $Rest = $Matches[2].Replace('\', '/')
        return "/mnt/$Drive/$Rest"
    }
    return ""
}

function Warn-WslVersion($SelectedDistro) {
    if ($SelectedDistro.Version -eq 0) {
        Write-Warning "Could not determine the selected distro's WSL version. WSL2 is recommended for SDR USB forwarding and stable networking."
        return
    }
    if ($SelectedDistro.Version -ne 2) {
        Write-Warning "Selected distro is WSL$($SelectedDistro.Version). WSL2 is recommended for SDR USB forwarding and stable networking."
        Write-Warning "To convert it later: wsl --set-version `"$($SelectedDistro.Name)`" 2"
    }
}

function Ensure-Usbipd {
    if (Have-Command usbipd) {
        Write-Host "[bootstrap] usbipd found"
        return
    }
    if (-not $InstallUsbipd) {
        Write-Host "[bootstrap] usbipd-win is not installed. Skipping USB forwarding setup."
        Write-Host "[bootstrap] Install it manually from https://github.com/dorssel/usbipd-win or rerun with -InstallUsbipd."
        return
    }
    Restart-AsAdmin
    Require-Admin
    Ensure-Winget
    Write-Host "[bootstrap] Installing usbipd-win with winget"
    winget install --id dorssel.usbipd-win -e --accept-package-agreements --accept-source-agreements
}

function Install-Controller {
    $InstallScript = Join-Path $SourceDir "install_windows_controller.ps1"
    if (-not (Test-Path $InstallScript)) {
        throw "Missing $InstallScript"
    }
    $DesktopArg = if ($NoDesktopShortcut) { @("-CreateDesktopShortcut:`$false") } else { @() }
    powershell.exe -ExecutionPolicy Bypass -File $InstallScript -InstallDir $InstallDir @DesktopArg
}

function Quote-ProcessArgument($Arg) {
    $Text = [string]$Arg
    if ($Text -notmatch '[\s"]') {
        return $Text
    }
    return '"' + ($Text.Replace('\', '\\').Replace('"', '\"')) + '"'
}

function Get-WslHome {
    $DistroArgs = @()
    if ($Distro) { $DistroArgs = @("-d", $Distro) }
    $Raw = [string]::Join("`n", (& wsl.exe @DistroArgs bash -lc 'printf %s "$HOME"'))
    if ($LASTEXITCODE -ne 0) {
        throw "Failed to resolve WSL home directory in $Distro"
    }
    $WslHomeDir = $Raw.Replace([string][char]0, "").Trim()
    if (-not $WslHomeDir) {
        throw "WSL returned an empty home directory in $Distro"
    }
    return $WslHomeDir
}

function Convert-WslProjectPath($Path) {
    $Text = [string]$Path
    if ($Text -eq "~") {
        return (Get-WslHome)
    }
    if ($Text.StartsWith("~/")) {
        return (Get-WslHome).TrimEnd("/") + "/" + $Text.Substring(2)
    }
    return $Text
}

function Quote-BashSingle($Text) {
    return "'" + ([string]$Text).Replace("'", "'\''") + "'"
}

function Copy-Payload-To-Wsl {
    $Payload = Find-WslPayload
    Write-Host "[bootstrap] Using WSL payload: $Payload"
    $DistroArgs = @()
    if ($Distro) { $DistroArgs = @("-d", $Distro) }
    $ProjectDir = Convert-WslProjectPath $WslProjectDir
    $ProjectDirQ = Quote-BashSingle $ProjectDir
    & wsl.exe @DistroArgs bash -lc "mkdir -p ${ProjectDirQ}"
    if ($LASTEXITCODE -ne 0) {
        throw "Failed to create WSL project directory in $Distro"
    }
    $Dest = "$ProjectDir/.windows-controller-payload.tar.gz"
    $DestQ = Quote-BashSingle $Dest
    $PayloadWslPath = Convert-WindowsPathToWslPath $Payload
    if ($PayloadWslPath) {
        $PayloadWslPathQ = Quote-BashSingle $PayloadWslPath
        & wsl.exe @DistroArgs bash -lc "cp ${PayloadWslPathQ} ${DestQ}"
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to copy WSL payload from $PayloadWslPath into $Distro"
        }
    } else {
        $Bytes = [IO.File]::ReadAllBytes($Payload)
        $Psi = New-Object System.Diagnostics.ProcessStartInfo
        $Psi.FileName = "wsl.exe"
        $AllArgs = @($DistroArgs + @("bash", "-lc", "cat > ${DestQ}"))
        $Psi.Arguments = ($AllArgs | ForEach-Object { Quote-ProcessArgument $_ }) -join " "
        $Psi.RedirectStandardInput = $true
        $Psi.UseShellExecute = $false
        $Process = [System.Diagnostics.Process]::Start($Psi)
        $Process.StandardInput.BaseStream.Write($Bytes, 0, $Bytes.Length)
        $Process.StandardInput.Close()
        $Process.WaitForExit()
        if ($Process.ExitCode -ne 0) {
            throw "Failed to copy WSL payload into $Distro"
        }
    }
    & wsl.exe @DistroArgs bash -lc "cd ${ProjectDirQ} && tar -xzf .windows-controller-payload.tar.gz --strip-components=1 && rm -f .windows-controller-payload.tar.gz && chmod +x scripts/*.sh"
    if ($LASTEXITCODE -ne 0) {
        throw "Failed to unpack WSL payload in $Distro at $ProjectDir"
    }
}

function Write-Wsl-Runtime-Config {
    $DistroArgs = @()
    if ($Distro) { $DistroArgs = @("-d", $Distro) }
    $BindHost = if ($AllowLanAccess) { "0.0.0.0" } else { $WebHost }
    if ($BindHost -eq "0.0.0.0") {
        Write-Warning "Web UI will listen on all WSL interfaces. Use only on trusted private networks, preferably through Tailscale."
    }
    $SkipUsb = if ((-not (Have-Command usbipd)) -and (-not $UsbBusId)) { "1" } else { "0" }
    $Https = "1"
    $Config = @"
# ADS-B Transit Predictor runtime configuration.
# Generated by Windows bootstrap.
ADSB_WEB_HOST=$BindHost
ADSB_WEB_PORT=$WebPort
ADSB_HTTPS=$Https
ADSB_DECODER_MODE=$DecoderMode
ADSB_SBS_PORT=$SbsPort
ADSB_GAIN=$Gain
ADSB_DEVICE_INDEX=$DeviceIndex
ADSB_USB_BUSID=$UsbBusId
ADSB_SKIP_USBIPD=$SkipUsb
ADSB_RESTART=1
"@
    $Encoded = [Convert]::ToBase64String([Text.Encoding]::UTF8.GetBytes($Config))
    & wsl.exe @DistroArgs bash -lc "mkdir -p ~/.config/adsb-transit && printf '%s' '$Encoded' | base64 -d > ~/.config/adsb-transit/adsb-web.env && printf '%s\n' ~/.config/adsb-transit/adsb-web.env"
    if ($LASTEXITCODE -ne 0) {
        throw "Failed to write WSL runtime config in $Distro"
    }
}

function Install-Linux-Dependencies {
    if ($SkipLinuxDependencies) {
        Write-Host "[bootstrap] Skipping Linux dependencies"
        return
    }
    $DistroArgs = @()
    if ($Distro) { $DistroArgs = @("-d", $Distro) }
    $ProjectDir = Convert-WslProjectPath $WslProjectDir
    $ProjectDirQ = Quote-BashSingle $ProjectDir
    Write-Host "[bootstrap] Installing Linux system packages as WSL root"
    & wsl.exe @DistroArgs -u root bash -lc "cd ${ProjectDirQ} && ADSB_NONINTERACTIVE=1 ADSB_INSTALL_PHASE=system ./scripts/install_linux.sh"
    if ($LASTEXITCODE -ne 0) {
        throw "Linux system dependency installer failed in $Distro at $ProjectDir"
    }
    Write-Host "[bootstrap] Installing Python venv and user launcher as default WSL user"
    & wsl.exe @DistroArgs bash -lc "cd ${ProjectDirQ} && ADSB_INSTALL_PHASE=user ./scripts/install_linux.sh"
    if ($LASTEXITCODE -ne 0) {
        throw "Linux user dependency installer failed in $Distro at $ProjectDir"
    }
}

function Write-Install-Record {
    $Dir = Join-Path $env:APPDATA "ADS-B Transit Predictor"
    $Path = Join-Path $Dir "installations.json"
    New-Item -ItemType Directory -Force -Path $Dir | Out-Null
    $Record = [pscustomobject]@{
        distro = $Distro
        wsl_project_dir = $WslProjectDir
        install_dir = $InstallDir
        web_host = $(if ($AllowLanAccess) { "0.0.0.0" } else { $WebHost })
        web_port = $WebPort
        installed_at = (Get-Date).ToString("o")
        package_source = $SourceDir
    }
    $Records = @()
    if (Test-Path $Path) {
        try {
            $Existing = Get-Content $Path -Raw | ConvertFrom-Json
            if ($Existing.installations) {
                $Records = @($Existing.installations)
            }
        } catch {
            $Records = @()
        }
    }
    $Records = @($Records | Where-Object { -not (($_.distro -eq $Distro) -and ($_.wsl_project_dir -eq $WslProjectDir)) })
    $Records += $Record
    [pscustomobject]@{
        schema_version = 1
        last = $Record
        installations = $Records
    } | ConvertTo-Json -Depth 6 | Set-Content -Path $Path -Encoding UTF8
    Write-Host "[bootstrap] Install record written: $Path"
}

Ensure-Wsl
Ensure-Usbipd
Install-Controller
Copy-Payload-To-Wsl
Write-Wsl-Runtime-Config
Install-Linux-Dependencies
Write-Install-Record

Write-Host ""
Write-Host "ADS-B Transit Predictor Windows/WSL bootstrap complete."
Write-Host "Open ADS-B Transit Controller from the Start Menu."
if (Test-Path (Join-Path $InstallDir "ADSBTransitController.exe")) {
    Write-Host "Controller executable:"
    Write-Host "  $InstallDir\ADSBTransitController.exe"
} else {
    Write-Host "Controller Python launcher installed. A packaged EXE can be built on Windows with:"
    Write-Host "  powershell -ExecutionPolicy Bypass -File .\build_pyinstaller.ps1"
}
