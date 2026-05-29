# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path

ROOT = Path.cwd()
PAYLOAD = ROOT / "wsl_payload.tar.gz"
ICON = ROOT / "icon.ico"
datas = []
if PAYLOAD.exists():
    datas.append((str(PAYLOAD), "."))
if ICON.exists():
    datas.append((str(ICON), "."))

a = Analysis(
    ["adsb_windows_controller.py"],
    pathex=[str(ROOT)],
    binaries=[],
    datas=datas,
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
)
pyz = PYZ(a.pure)
exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name="ADSBTransitController",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    icon=str(ICON) if ICON.exists() else None,
)
coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=True,
    upx_exclude=[],
    name="ADSBTransitController",
)
