#!/usr/bin/env python3
"""
Windows controller for the ADS-B Transit Predictor WSL server.

The controller deliberately keeps the prediction server inside WSL.  Windows is
used only for configuration, process control, usbipd visibility, and opening the
browser.
"""

from __future__ import annotations

import json
import io
import os
import queue
import re
import socket
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import webbrowser
from dataclasses import asdict, dataclass
from pathlib import Path
from tkinter import BOTH, END, LEFT, W, Frame, StringVar, Tk, Text, filedialog, messagebox
from tkinter import ttk


APP_NAME = "ADS-B Transit Predictor"
CONFIG_DIR = Path(os.environ.get("APPDATA", Path.home())) / APP_NAME
CONFIG_PATH = CONFIG_DIR / "windows-controller.json"
DEFAULT_WSL_DIR = "~/ADS-B-Transit-Predictor"


def bundled_root() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def apply_windows_app_icon(root: Tk, app_id: str) -> None:
    if os.name == "nt":
        try:
            import ctypes

            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(app_id)
        except Exception:
            pass
    icon_path = bundled_root() / "icon.ico"
    if icon_path.exists():
        try:
            root.iconbitmap(default=str(icon_path))
        except Exception:
            pass


def parse_wsl_distros(output: str) -> list[str]:
    distros: list[str] = []
    for raw_line in output.replace("\x00", "").splitlines():
        line = raw_line.strip()
        if not line or re.match(r"^NAME\s+STATE\s+VERSION", line):
            continue
        line = line.lstrip("*").strip()
        match = re.match(r"^(?P<name>.+?)\s{2,}\S+\s+\d+$", line)
        if match:
            distros.append(match.group("name").strip())
            continue
        parts = line.split()
        if len(parts) >= 3 and parts[-1].isdigit():
            distros.append(" ".join(parts[:-2]))
    return distros


@dataclass
class ControllerConfig:
    distro: str = ""
    wsl_project_dir: str = DEFAULT_WSL_DIR
    access_mode: str = "local"
    web_host: str = "127.0.0.1"
    web_port: str = "8090"
    https: str = "1"
    open_after_start: str = "1"
    decoder_mode: str = "auto"
    sbs_port: str = "30003"
    gain: str = "-10"
    device_index: str = "0"
    usb_busid: str = ""
    skip_usbipd: str = "0"
    restart_existing: str = "1"
    custom_decoder_cmd: str = ""


class ControllerApp:
    def __init__(self, root: Tk) -> None:
        self.root = root
        self.root.title(APP_NAME + " - Windows Controller")
        self.config = self.load_config()
        self.proc: subprocess.Popen[str] | None = None
        self.log_queue: queue.Queue[str] = queue.Queue()
        self.vars: dict[str, StringVar] = {}
        self.distro_combo: ttk.Combobox | None = None
        self.build_ui()
        self.root.after(100, self.drain_log_queue)
        self.refresh_wsl_distros()

    def load_config(self) -> ControllerConfig:
        try:
            data = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
            return ControllerConfig(**{**asdict(ControllerConfig()), **data})
        except Exception:
            return ControllerConfig()

    def save_config(self) -> None:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        data = {key: var.get() for key, var in self.vars.items()}
        self.config = ControllerConfig(**{**asdict(self.config), **data})
        CONFIG_PATH.write_text(json.dumps(asdict(self.config), indent=2), encoding="utf-8")
        self.log(f"Saved controller config: {CONFIG_PATH}")

    def build_ui(self) -> None:
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Title.TLabel", font=("Segoe UI", 15, "bold"))
        style.configure("Hint.TLabel", foreground="#52616f")
        style.configure("Primary.TButton", padding=(12, 7))
        style.configure("Danger.TButton", padding=(12, 7))

        root_frame = ttk.Frame(self.root, padding=14)
        root_frame.pack(fill=BOTH, expand=True)
        root_frame.columnconfigure(0, weight=1)
        root_frame.rowconfigure(2, weight=1)

        header = ttk.Frame(root_frame)
        header.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        header.columnconfigure(0, weight=1)
        ttk.Label(header, text="ADS-B Transit Predictor", style="Title.TLabel").grid(row=0, column=0, sticky=W)
        ttk.Label(
            header,
            text="Windows controller for installing and running the Linux/WSL Web Server.",
            style="Hint.TLabel",
        ).grid(row=1, column=0, sticky=W, pady=(2, 0))

        notebook = ttk.Notebook(root_frame)
        notebook.grid(row=1, column=0, sticky="ew")

        server_tab = ttk.Frame(notebook, padding=12)
        receiver_tab = ttk.Frame(notebook, padding=12)
        actions_tab = ttk.Frame(notebook, padding=12)
        for tab in (server_tab, receiver_tab, actions_tab):
            tab.columnconfigure(1, weight=1)

        notebook.add(server_tab, text="Server")
        notebook.add(receiver_tab, text="Receiver")
        notebook.add(actions_tab, text="Actions")

        def add_field(parent: ttk.Frame, row: int, key: str, label: str, kind="entry", hint: str = "") -> None:
            ttk.Label(parent, text=label, width=20, anchor=W).grid(row=row, column=0, sticky=W, pady=4)
            var = StringVar(value=str(getattr(self.config, key)))
            self.vars[key] = var
            if isinstance(kind, list):
                ttk.OptionMenu(parent, var, var.get(), *kind).grid(row=row, column=1, sticky="ew", pady=4)
            elif kind == "combo":
                combo = ttk.Combobox(parent, textvariable=var, values=[], state="readonly")
                combo.grid(row=row, column=1, sticky="ew", pady=4)
                if key == "distro":
                    self.distro_combo = combo
            elif kind == "bool":
                ttk.Checkbutton(parent, variable=var, onvalue="1", offvalue="0", text="Yes").grid(row=row, column=1, sticky=W, pady=4)
            else:
                ttk.Entry(parent, textvariable=var).grid(row=row, column=1, sticky="ew", pady=4)
            if hint:
                ttk.Label(parent, text=hint, style="Hint.TLabel").grid(row=row, column=2, sticky=W, padx=(10, 0), pady=4)

        add_field(server_tab, 0, "distro", "WSL distro", "combo", "Select the target Linux distro")
        add_field(server_tab, 1, "wsl_project_dir", "WSL project dir", hint="Default is usually fine")
        add_field(server_tab, 2, "access_mode", "Access mode", ["local", "lan", "tailscale"])
        add_field(server_tab, 3, "web_host", "Web host", hint="Used for local mode")
        add_field(server_tab, 4, "web_port", "Web port")
        add_field(server_tab, 5, "https", "HTTPS", "bool", "Required for browser GPS outside localhost")
        add_field(server_tab, 6, "open_after_start", "Open after start", "bool")
        add_field(server_tab, 7, "restart_existing", "Restart existing", "bool", "Stops old Web/SBS listeners")

        add_field(receiver_tab, 0, "decoder_mode", "Decoder mode", ["auto", "managed", "external", "none"])
        add_field(receiver_tab, 1, "sbs_port", "SBS port")
        add_field(receiver_tab, 2, "gain", "RTL gain", hint="-10 means auto gain")
        add_field(receiver_tab, 3, "device_index", "RTL device index")
        add_field(receiver_tab, 4, "usb_busid", "USB BUSID", hint="Only needed for WSL USB forwarding")
        add_field(receiver_tab, 5, "skip_usbipd", "Skip usbipd", "bool")
        add_field(receiver_tab, 6, "custom_decoder_cmd", "Custom decoder cmd", hint="For Airspy, SDRplay, Beast, remote setups")

        action_groups = [
            ("Setup", [
                ("Save", self.save_config),
                ("Install / Update WSL Files", self.install_wsl_files),
                ("Install Linux Dependencies", self.install_linux_dependencies),
                ("Doctor", self.run_doctor),
            ]),
            ("Server Control", [
                ("Start Server", self.start_server),
                ("Stop Server", self.stop_server),
                ("Restart Server", self.restart_server),
                ("Open Web UI", self.open_web_ui),
                ("Show URLs", self.show_access_urls),
            ]),
            ("USB / Tailnet", [
                ("USB Devices", self.show_usb_devices),
                ("Auto USB BUSID", self.auto_detect_usb_busid),
                ("Attach USB", self.attach_usb_device),
                ("Tailscale Status", self.show_tailscale_status),
                ("Copy Tailscale URL", self.copy_tailscale_url),
            ]),
        ]
        for col, (title, actions) in enumerate(action_groups):
            group = ttk.LabelFrame(actions_tab, text=title, padding=10)
            group.grid(row=0, column=col, sticky="nsew", padx=(0 if col == 0 else 10, 0), pady=0)
            actions_tab.columnconfigure(col, weight=1)
            for row, (text, command) in enumerate(actions):
                ttk.Button(group, text=text, command=command, style="Primary.TButton").grid(row=row, column=0, sticky="ew", pady=3)
            group.columnconfigure(0, weight=1)

        log_frame = ttk.LabelFrame(root_frame, text="Activity Log", padding=10)
        log_frame.grid(row=2, column=0, sticky="nsew", pady=(12, 0))
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(0, weight=1)
        self.log_text = Text(log_frame, height=18, wrap="word", relief="flat")
        self.log_text.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(log_frame, orient="vertical", command=self.log_text.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.log_text.configure(yscrollcommand=scroll.set)

    def refresh_wsl_distros(self) -> None:
        try:
            result = run_hidden(["wsl.exe", "-l", "-v"], text=True, capture_output=True, timeout=8)
            distros = parse_wsl_distros(result.stdout)
            if self.distro_combo is not None:
                self.distro_combo.configure(values=distros)
            if distros:
                current = self.vars["distro"].get().strip()
                if current not in distros:
                    self.vars["distro"].set(distros[0])
                self.log("Detected WSL distros: " + ", ".join(distros))
        except Exception as exc:
            self.log(f"Could not list WSL distros: {exc}")

    def distro_args(self) -> list[str]:
        distro = self.vars["distro"].get().strip()
        return ["-d", distro] if distro else []

    def wsl(self, command: str, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
        args = ["wsl.exe", *self.distro_args(), "bash", "-lc", command]
        self.log("$ " + " ".join(args))
        return run_hidden(args, text=True, capture_output=True, timeout=timeout)

    def env_prefix(self) -> str:
        cfg = {key: var.get() for key, var in self.vars.items()}
        web_host = self.effective_web_host()
        env = {
            "ADSB_WEB_HOST": web_host,
            "ADSB_WEB_PORT": cfg["web_port"],
            "ADSB_HTTPS": cfg["https"],
            "ADSB_DECODER_MODE": cfg["decoder_mode"],
            "ADSB_DECODER_CMD": cfg["custom_decoder_cmd"],
            "ADSB_SBS_PORT": cfg["sbs_port"],
            "ADSB_GAIN": cfg["gain"],
            "ADSB_DEVICE_INDEX": cfg["device_index"],
            "ADSB_USB_BUSID": cfg["usb_busid"],
            "ADSB_SKIP_USBIPD": cfg["skip_usbipd"],
            "ADSB_RESTART": cfg["restart_existing"],
            "ADSB_WSL_DISTRO": cfg["distro"],
        }
        return " ".join(f"{key}={shell_quote(value)}" for key, value in env.items() if value != "")

    def effective_web_host(self) -> str:
        mode = self.vars["access_mode"].get()
        if mode in {"lan", "tailscale"}:
            return "0.0.0.0"
        return self.vars["web_host"].get().strip() or "127.0.0.1"

    def access_scheme(self) -> str:
        return "https" if self.vars["https"].get() == "1" else "http"

    def wsl_dir(self) -> str:
        return self.vars["wsl_project_dir"].get().strip() or DEFAULT_WSL_DIR

    def wsl_dir_expr(self) -> str:
        return bash_path_expr(self.wsl_dir())

    def log(self, text: str) -> None:
        stamp = time.strftime("%H:%M:%S")
        self.log_queue.put(f"[{stamp}] {text}\n")

    def drain_log_queue(self) -> None:
        while True:
            try:
                item = self.log_queue.get_nowait()
            except queue.Empty:
                break
            self.log_text.insert(END, item)
            self.log_text.see(END)
        self.root.after(100, self.drain_log_queue)

    def run_background(self, name: str, func) -> None:
        def target() -> None:
            try:
                func()
            except Exception as exc:
                self.log(f"{name} failed: {exc}")
        threading.Thread(target=target, daemon=True).start()

    def install_wsl_files(self) -> None:
        self.save_config()
        archive = bundled_root() / "wsl_payload.tar.gz"
        temp_archive: Path | None = None
        if not archive.exists():
            selected = filedialog.askdirectory(title="Select ADS-B Transit Predictor project folder")
            if not selected:
                return
            temp_archive = Path(tempfile.gettempdir()) / "adsb-transit-wsl-payload.tar.gz"
            create_payload_archive(Path(selected), temp_archive)
            archive = temp_archive

        def work() -> None:
            project_dir = self.wsl_dir_expr()
            result = self.wsl(f"mkdir -p {project_dir}", timeout=30)
            self.report_result(result)
            run_hidden(
                ["wsl.exe", *self.distro_args(), "bash", "-lc", f"cd {project_dir} && cat > .windows-controller-payload.tar.gz"],
                input=archive.read_bytes(),
                check=True,
            )
            result = self.wsl(f"cd {project_dir} && tar -xzf .windows-controller-payload.tar.gz --strip-components=1 && rm -f .windows-controller-payload.tar.gz", timeout=300)
            self.report_result(result)
            self.log("WSL project files installed/updated.")
            if temp_archive:
                temp_archive.unlink(missing_ok=True)

        self.run_background("Install WSL files", work)

    def install_linux_dependencies(self) -> None:
        self.save_config()

        def work() -> None:
            project_dir = self.wsl_dir_expr()
            cmd = f"cd {project_dir} && chmod +x scripts/*.sh && ADSB_NONINTERACTIVE=1 ADSB_INSTALL_PHASE=system ./scripts/install_linux.sh"
            args = ["wsl.exe", *self.distro_args(), "-u", "root", "bash", "-lc", cmd]
            self.log("$ " + " ".join(args))
            result = run_hidden(args, text=True, capture_output=True, timeout=None)
            self.report_result(result)
            if result.returncode != 0:
                return
            cmd = f"cd {project_dir} && ADSB_INSTALL_PHASE=user ./scripts/install_linux.sh"
            result = self.wsl(cmd, timeout=None)
            self.report_result(result)

        self.run_background("Linux dependency install", work)

    def start_server(self) -> None:
        self.save_config()
        if self.proc and self.proc.poll() is None:
            self.log("Server process is already running from this controller.")
            return
        cmd = f"cd {self.wsl_dir_expr()} && {self.env_prefix()} ./scripts/start_adsb_web.sh"
        args = ["wsl.exe", *self.distro_args(), "bash", "-lc", cmd]
        self.log("$ " + " ".join(args))
        self.opened_after_start = False
        self.proc = popen_hidden(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        threading.Thread(target=self.capture_server_output, daemon=True).start()

    def capture_server_output(self) -> None:
        if not self.proc or not self.proc.stdout:
            return
        for line in self.proc.stdout:
            self.log_queue.put(line)
            if (
                self.vars["open_after_start"].get() == "1"
                and not getattr(self, "opened_after_start", False)
                and "[web] ADS-B Transit Web UI:" in line
            ):
                self.opened_after_start = True
                self.root.after(250, self.open_web_ui)
        code = self.proc.wait()
        self.log(f"Server process exited with code {code}")

    def stop_server(self) -> None:
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            self.log("Terminated controller-owned WSL process.")
        cmd = "pkill -f 'web_ui/server.py' || true; pkill -f 'dump1090' || true"
        result = self.wsl(cmd, timeout=20)
        self.report_result(result)

    def restart_server(self) -> None:
        self.stop_server()
        self.root.after(1000, self.start_server)

    def open_web_ui(self) -> None:
        scheme = self.access_scheme()
        host = "127.0.0.1"
        port = self.vars["web_port"].get().strip() or "8090"
        webbrowser.open(f"{scheme}://{host}:{port}/")

    def local_lan_ip(self) -> str | None:
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
                sock.connect(("8.8.8.8", 80))
                return sock.getsockname()[0]
        except Exception:
            return None

    def tailscale_ip(self) -> str | None:
        for exe in ("tailscale.exe", "tailscale"):
            try:
                result = run_hidden([exe, "ip", "-4"], text=True, capture_output=True, timeout=8)
                if result.returncode == 0:
                    first = next((line.strip() for line in result.stdout.splitlines() if line.strip()), "")
                    if first:
                        return first
            except Exception:
                continue
        return None

    def access_urls(self) -> list[tuple[str, str]]:
        scheme = self.access_scheme()
        port = self.vars["web_port"].get().strip() or "8090"
        urls = [("Local", f"{scheme}://127.0.0.1:{port}/")]
        lan_ip = self.local_lan_ip()
        if lan_ip:
            urls.append(("LAN", f"{scheme}://{lan_ip}:{port}/"))
        ts_ip = self.tailscale_ip()
        if ts_ip:
            urls.append(("Tailscale", f"{scheme}://{ts_ip}:{port}/"))
        return urls

    def show_access_urls(self) -> None:
        mode = self.vars["access_mode"].get()
        self.log(f"Access mode: {mode}; bind host: {self.effective_web_host()}")
        for label, url in self.access_urls():
            self.log(f"{label}: {url}")
        if mode in {"lan", "tailscale"}:
            self.log("LAN/Tailscale access requires the server to bind 0.0.0.0 and should be used only on trusted private networks.")

    def show_tailscale_status(self) -> None:
        try:
            result = run_hidden(["tailscale.exe", "status"], text=True, capture_output=True, timeout=12)
            self.report_result(result)
        except FileNotFoundError:
            self.log("tailscale.exe was not found. Install Tailscale separately if you want Tailscale access.")
        except Exception as exc:
            self.log(f"Tailscale status failed: {exc}")

    def copy_tailscale_url(self) -> None:
        ts_ip = self.tailscale_ip()
        if not ts_ip:
            self.log("No Tailscale IPv4 address found.")
            return
        url = f"{self.access_scheme()}://{ts_ip}:{self.vars['web_port'].get().strip() or '8090'}/"
        self.root.clipboard_clear()
        self.root.clipboard_append(url)
        self.log(f"Copied Tailscale URL: {url}")

    def run_doctor(self) -> None:
        self.save_config()

        def work() -> None:
            result = self.wsl(f"cd {self.wsl_dir_expr()} && ./scripts/doctor_linux.sh", timeout=60)
            self.report_result(result)

        self.run_background("Doctor", work)

    def show_usb_devices(self) -> None:
        try:
            result = run_hidden(["powershell.exe", "-NoProfile", "-WindowStyle", "Hidden", "-Command", "usbipd list"], text=True, capture_output=True, timeout=20)
            self.report_result(result)
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"usbipd list failed: {exc}")

    def usbipd_list(self) -> str:
        result = run_hidden(["powershell.exe", "-NoProfile", "-WindowStyle", "Hidden", "-Command", "usbipd list"], text=True, capture_output=True, timeout=20)
        if result.returncode != 0:
            raise RuntimeError(result.stderr or result.stdout or "usbipd list failed")
        return result.stdout

    def auto_detect_usb_busid(self) -> None:
        try:
            output = self.usbipd_list()
            pattern = re.compile(r"^\s*(\d+-\d+)\s+.*(RTL|SDR|0bda:2838|0bda:2832|Airspy|SDRplay|HackRF|Beast|FlightAware|Pro Stick)", re.I)
            for line in output.splitlines():
                match = pattern.search(line)
                if match:
                    busid = match.group(1)
                    self.vars["usb_busid"].set(busid)
                    self.vars["skip_usbipd"].set("0")
                    self.log(f"Auto-detected USB BUSID: {busid}")
                    return
            self.log("No matching SDR USB device was found in usbipd list.")
        except Exception as exc:
            self.log(f"Auto USB detection failed: {exc}")

    def attach_usb_device(self) -> None:
        busid = self.vars["usb_busid"].get().strip()
        if not busid:
            self.log("USB BUSID is empty. Use USB Devices or Auto USB BUSID first.")
            return
        cmd = f"usbipd attach --wsl --busid {busid}"
        result = run_hidden(["powershell.exe", "-NoProfile", "-WindowStyle", "Hidden", "-Command", cmd], text=True, capture_output=True, timeout=40)
        self.report_result(result)

    def report_result(self, result: subprocess.CompletedProcess[str]) -> None:
        if result.stdout:
            self.log(result.stdout.rstrip())
        if result.stderr:
            self.log(result.stderr.rstrip())
        self.log(f"Exit code: {result.returncode}")


def shell_quote(value: str) -> str:
    return "'" + value.replace("'", "'\"'\"'") + "'"


def bash_path_expr(value: str) -> str:
    path = value.strip() or DEFAULT_WSL_DIR
    if path == "~":
        return '"$HOME"'
    if path.startswith("~/"):
        return '"$HOME"/' + shell_quote(path[2:])
    return shell_quote(path)


def powershell_quote(value: str) -> str:
    return "'" + value.replace("'", "''") + "'"


def hidden_subprocess_kwargs() -> dict:
    if os.name != "nt":
        return {}
    startupinfo = subprocess.STARTUPINFO()
    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    startupinfo.wShowWindow = 0
    return {
        "creationflags": subprocess.CREATE_NO_WINDOW,
        "startupinfo": startupinfo,
    }


def run_hidden(args, **kwargs):
    kwargs.update(hidden_subprocess_kwargs())
    return subprocess.run(args, **kwargs)


def popen_hidden(args, **kwargs):
    kwargs.update(hidden_subprocess_kwargs())
    return subprocess.Popen(args, **kwargs)


def create_payload_archive(source: Path, archive: Path) -> None:
    exclude_dirs = {".git", ".venv", ".web_certs", "__pycache__", "dist", "build"}
    exclude_names = {"web_ui_config.json"}
    with tarfile.open(archive, "w:gz") as tar:
        for item in source.rglob("*"):
            rel = item.relative_to(source)
            if any(part in exclude_dirs for part in rel.parts):
                continue
            if item.name in exclude_names or item.name.endswith(".pyc"):
                continue
            if rel.as_posix() == "config.json":
                data = json.loads(item.read_text(encoding="utf-8"))
                data.update({"lat": 51.471974, "lon": -0.453119, "alt_m": 28, "host": "127.0.0.1", "port": 30003})
                raw = (json.dumps(data, indent=4, sort_keys=True) + "\n").encode("utf-8")
                info = tarfile.TarInfo("ADS-B-Transit-Predictor/config.json")
                info.size = len(raw)
                tar.addfile(info, io.BytesIO(raw))
                continue
            tar.add(item, arcname=f"ADS-B-Transit-Predictor/{rel}")


def main() -> None:
    root = Tk()
    root.geometry("980x720")
    apply_windows_app_icon(root, "RealSeaberry.ADSBTransitPredictor.Controller")
    ControllerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
