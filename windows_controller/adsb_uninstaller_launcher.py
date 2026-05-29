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


APP_TITLE = "ADS-B Transit Uninstaller"
INSTALL_RECORD = Path(os.environ.get("APPDATA", Path.home())) / "ADS-B Transit Predictor" / "installations.json"


def bundled_root() -> Path:
    return Path(sys.executable).resolve().parent if getattr(sys, "frozen", False) else Path(__file__).resolve().parent


def parse_wsl_distros(output: str) -> list[str]:
    return [line.strip().lstrip("*").strip() for line in output.replace("\x00", "").splitlines() if line.strip()]


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


class UninstallerApp:
    def __init__(self, root: Tk) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("780x560")
        self.msgs: queue.Queue[str] = queue.Queue()
        self.distros = list_wsl_distros()
        last = load_last_install()
        initial_distro = last.get("distro") if last.get("distro") in self.distros else (self.distros[0] if self.distros else "")
        self.distro = StringVar(value=initial_distro)
        self.project_dir = StringVar(value=last.get("wsl_project_dir") or "~/ADS-B-Transit-Predictor")
        self.keep_wsl_project = BooleanVar(value=False)
        self.keep_wsl_runtime = BooleanVar(value=False)
        self.build_ui()
        self.root.after(100, self.drain)

    def build_ui(self) -> None:
        frame = ttk.Frame(self.root, padding=14)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(1, weight=1)
        frame.rowconfigure(6, weight=1)

        ttk.Label(frame, text="ADS-B Transit Predictor Uninstaller", font=("Segoe UI", 14, "bold")).grid(row=0, column=0, columnspan=3, sticky="w")

        ttk.Label(frame, text="WSL distro").grid(row=1, column=0, sticky="w", pady=(14, 4))
        state = "readonly" if len(self.distros) > 1 else "disabled"
        self.distro_combo = ttk.Combobox(frame, textvariable=self.distro, values=self.distros, state=state)
        self.distro_combo.grid(row=1, column=1, sticky="ew", pady=(14, 4))
        ttk.Button(frame, text="Refresh", command=self.refresh_distros).grid(row=1, column=2, padx=(8, 0), pady=(14, 4))

        hint = "Only one distro found." if len(self.distros) == 1 else "Choose the target distro for optional WSL cleanup."
        if not self.distros:
            hint = "No WSL distro found. Nothing can be cleaned inside WSL."
        elif load_last_install():
            hint = f"Loaded previous install record from {INSTALL_RECORD}"
        self.hint = ttk.Label(frame, text=hint)
        self.hint.grid(row=2, column=1, sticky="w")

        ttk.Label(frame, text="WSL project dir").grid(row=3, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=self.project_dir).grid(row=3, column=1, sticky="ew", pady=4)

        ttk.Label(
            frame,
            text="Default cleanup removes only WSL-side ADS-B files, runtime config, aliases, and generated certs. Windows files are left untouched.",
            wraplength=560,
        ).grid(row=4, column=1, sticky="w", pady=(8, 6))
        ttk.Checkbutton(frame, text="Keep WSL project directory", variable=self.keep_wsl_project).grid(row=5, column=1, sticky="w", pady=2)
        ttk.Checkbutton(frame, text="Keep WSL runtime config / aliases / certs", variable=self.keep_wsl_runtime).grid(row=6, column=1, sticky="w", pady=2)

        log_frame = ttk.LabelFrame(frame, text="Progress", padding=8)
        log_frame.grid(row=7, column=0, columnspan=3, sticky="nsew", pady=(12, 0))
        frame.rowconfigure(7, weight=1)
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(0, weight=1)
        self.log = Text(log_frame, height=14, wrap="word")
        self.log.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(log_frame, orient="vertical", command=self.log.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.log.configure(yscrollcommand=scroll.set)

        buttons = ttk.Frame(frame)
        buttons.grid(row=8, column=0, columnspan=3, sticky="e", pady=(10, 0))
        self.start_btn = ttk.Button(buttons, text="Uninstall", command=self.start_uninstall)
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
            self.hint.configure(text="No WSL distro found. Nothing can be cleaned inside WSL.")

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

    def start_uninstall(self) -> None:
        script = bundled_root() / "uninstall_all_windows.ps1"
        if not script.exists():
            messagebox.showerror(APP_TITLE, f"Missing uninstaller script:\n{script}")
            return
        distro = self.distro.get().strip()
        if not distro:
            messagebox.showerror(APP_TITLE, "No WSL distro selected.")
            return
        if not messagebox.askyesno(
            APP_TITLE,
            "This will stop ADS-B processes and remove the selected WSL-side ADS-B installation. Windows files will not be removed. Continue?",
        ):
            return
        self.start_btn.configure(state="disabled")
        cmd = [
            "powershell.exe",
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(script),
            "-WslProjectDir",
            self.project_dir.get().strip() or "~/ADS-B-Transit-Predictor",
        ]
        if distro:
            cmd.extend(["-Distro", distro])
        if self.keep_wsl_project.get():
            cmd.append("-KeepWslProject")
        if self.keep_wsl_runtime.get():
            cmd.append("-KeepWslRuntime")

        self.append("$ " + " ".join(cmd) + os.linesep)
        threading.Thread(target=self.run_process, args=(cmd,), daemon=True).start()

    def run_process(self, cmd: list[str]) -> None:
        try:
            creationflags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                creationflags=creationflags,
            )
            assert proc.stdout is not None
            for line in proc.stdout:
                self.append(line)
            code = proc.wait()
            self.append(os.linesep + (f"Uninstaller finished successfully.{os.linesep}" if code == 0 else f"Uninstaller exited with code {code}.{os.linesep}"))
        except Exception as exc:
            self.append(f"Uninstaller failed: {exc}{os.linesep}")
        finally:
            self.root.after(0, lambda: self.start_btn.configure(state="normal"))


def main() -> int:
    root = Tk()
    try:
        root.iconbitmap(str(bundled_root() / "icon.ico"))
    except Exception:
        pass
    UninstallerApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
