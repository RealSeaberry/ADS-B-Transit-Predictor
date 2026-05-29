from __future__ import annotations

import os
import json
import queue
import subprocess
import sys
import threading
from pathlib import Path
from tkinter import END, BooleanVar, StringVar, Tk, Text, messagebox
from tkinter import ttk


APP_TITLE = "ADS-B Transit Installer"
INSTALL_RECORD = Path(os.environ.get("APPDATA", Path.home())) / "ADS-B Transit Predictor" / "installations.json"


def bundled_root() -> Path:
    return Path(sys.executable).resolve().parent if getattr(sys, "frozen", False) else Path(__file__).resolve().parent


def parse_wsl_distros(output: str) -> list[str]:
    distros: list[str] = []
    for line in output.replace("\x00", "").splitlines():
        name = line.strip().lstrip("*").strip()
        if name:
            distros.append(name)
    return distros


def list_wsl_distros() -> list[str]:
    result = subprocess.run(["wsl.exe", "-l", "-q"], text=True, capture_output=True, timeout=10)
    if result.returncode != 0:
        return []
    return parse_wsl_distros(result.stdout)


def load_last_install() -> dict[str, str]:
    try:
        data = json.loads(INSTALL_RECORD.read_text(encoding="utf-8-sig"))
        last = data.get("last") or {}
        return {
            "distro": str(last.get("distro") or ""),
            "wsl_project_dir": str(last.get("wsl_project_dir") or ""),
        }
    except Exception:
        return {}


class InstallerApp:
    def __init__(self, root: Tk) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("780x560")
        self.msgs: queue.Queue[str] = queue.Queue()
        self.proc: subprocess.Popen[str] | None = None
        self.distros = list_wsl_distros()
        last = load_last_install()
        initial_distro = last.get("distro") if last.get("distro") in self.distros else (self.distros[0] if self.distros else "")
        self.distro = StringVar(value=initial_distro)
        self.project_dir = StringVar(value=last.get("wsl_project_dir") or "~/ADS-B-Transit-Predictor")
        self.allow_lan = BooleanVar(value=False)
        self.install_usbipd = BooleanVar(value=False)
        self.skip_linux_deps = BooleanVar(value=False)
        self.no_desktop_shortcut = BooleanVar(value=False)
        self.build_ui()
        self.root.after(100, self.drain)

    def build_ui(self) -> None:
        frame = ttk.Frame(self.root, padding=14)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(1, weight=1)
        frame.rowconfigure(7, weight=1)

        ttk.Label(frame, text="ADS-B Transit Predictor Installer", font=("Segoe UI", 14, "bold")).grid(row=0, column=0, columnspan=3, sticky="w")

        ttk.Label(frame, text="WSL distro").grid(row=1, column=0, sticky="w", pady=(14, 4))
        state = "readonly" if len(self.distros) > 1 else "disabled"
        self.distro_combo = ttk.Combobox(frame, textvariable=self.distro, values=self.distros, state=state)
        self.distro_combo.grid(row=1, column=1, sticky="ew", pady=(14, 4))
        ttk.Button(frame, text="Refresh", command=self.refresh_distros).grid(row=1, column=2, padx=(8, 0), pady=(14, 4))

        if len(self.distros) == 1:
            hint = f"Only one distro found: {self.distros[0]}"
        elif self.distros:
            hint = "Choose the target distro for this release install."
        else:
            hint = "No WSL distro found. Install and initialize WSL first."
        self.hint = ttk.Label(frame, text=hint)
        self.hint.grid(row=2, column=1, sticky="w")

        ttk.Label(frame, text="WSL project dir").grid(row=3, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=self.project_dir).grid(row=3, column=1, sticky="ew", pady=4)

        ttk.Checkbutton(frame, text="Allow LAN/Tailscale access", variable=self.allow_lan).grid(row=4, column=1, sticky="w", pady=2)
        ttk.Checkbutton(frame, text="Install usbipd-win if missing", variable=self.install_usbipd).grid(row=5, column=1, sticky="w", pady=2)
        ttk.Checkbutton(frame, text="Skip Linux dependency install", variable=self.skip_linux_deps).grid(row=6, column=1, sticky="w", pady=2)
        ttk.Checkbutton(frame, text="Do not create Desktop shortcut", variable=self.no_desktop_shortcut).grid(row=7, column=1, sticky="nw", pady=2)

        log_frame = ttk.LabelFrame(frame, text="Progress", padding=8)
        log_frame.grid(row=8, column=0, columnspan=3, sticky="nsew", pady=(12, 0))
        frame.rowconfigure(8, weight=1)
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(0, weight=1)
        self.log = Text(log_frame, height=16, wrap="word")
        self.log.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(log_frame, orient="vertical", command=self.log.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.log.configure(yscrollcommand=scroll.set)

        buttons = ttk.Frame(frame)
        buttons.grid(row=9, column=0, columnspan=3, sticky="e", pady=(10, 0))
        self.start_btn = ttk.Button(buttons, text="Install", command=self.start_install)
        self.start_btn.pack(side="left", padx=(0, 8))
        ttk.Button(buttons, text="Close", command=self.root.destroy).pack(side="left")

    def refresh_distros(self) -> None:
        self.distros = list_wsl_distros()
        self.distro_combo.configure(values=self.distros, state=("readonly" if len(self.distros) > 1 else "disabled"))
        if self.distros:
            self.distro.set(self.distros[0])
            self.hint.configure(text=f"Detected: {', '.join(self.distros)}")
        else:
            self.distro.set("")
            self.hint.configure(text="No WSL distro found. Install and initialize WSL first.")

    def append(self, text: str) -> None:
        self.msgs.put(text)

    def drain(self) -> None:
        while True:
            try:
                msg = self.msgs.get_nowait()
            except queue.Empty:
                break
            self.log.insert(END, msg)
            self.log.see(END)
        self.root.after(100, self.drain)

    def start_install(self) -> None:
        script = bundled_root() / "bootstrap_all_windows.ps1"
        if not script.exists():
            messagebox.showerror(APP_TITLE, f"Missing installer script:\n{script}")
            return
        distro = self.distro.get().strip()
        if not distro:
            messagebox.showerror(APP_TITLE, "No WSL distro selected.")
            return
        self.start_btn.configure(state="disabled")
        cmd = [
            "powershell.exe",
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(script),
            "-Distro",
            distro,
            "-WslProjectDir",
            self.project_dir.get().strip() or "~/ADS-B-Transit-Predictor",
        ]
        if self.allow_lan.get():
            cmd.append("-AllowLanAccess")
        if self.install_usbipd.get():
            cmd.append("-InstallUsbipd")
        if self.skip_linux_deps.get():
            cmd.append("-SkipLinuxDependencies")
        if self.no_desktop_shortcut.get():
            cmd.append("-NoDesktopShortcut")

        self.append("$ " + " ".join(cmd) + os.linesep)
        threading.Thread(target=self.run_process, args=(cmd,), daemon=True).start()

    def run_process(self, cmd: list[str]) -> None:
        success = False
        try:
            creationflags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
            self.proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                creationflags=creationflags,
            )
            assert self.proc.stdout is not None
            for line in self.proc.stdout:
                self.append(line)
            code = self.proc.wait()
            success = code == 0
            self.append(os.linesep + (f"Installer finished successfully.{os.linesep}" if code == 0 else f"Installer exited with code {code}.{os.linesep}"))
            if code == 0:
                self.root.after(0, self.start_btn.pack_forget)
        except Exception as exc:
            self.append(f"Installer failed: {exc}{os.linesep}")
        finally:
            if not success:
                self.root.after(0, lambda: self.start_btn.configure(state="normal"))


def main() -> int:
    root = Tk()
    try:
        root.iconbitmap(str(bundled_root() / "icon.ico"))
    except Exception:
        pass
    InstallerApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
