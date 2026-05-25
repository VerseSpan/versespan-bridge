"""
ProPresenter Bridge — local agent with GUI window.

Runs on the ProPresenter machine. Connects outbound to the cloud backend via
WebSocket, relays ProPresenter events, and answers library/content queries.

First-run setup:
  The admin downloads this script pre-filled with a CONNECTION_CODE (base64 JSON
  containing backend_url + church_id + api_token). On first launch the user sees
  a setup screen to paste the code or fill in fields manually.

Window:
  Shows live status, now-playing, editable ProPresenter host/port with a Test
  button, network scan for auto-discovery, connection code entry, and a scrollable
  live log. Minimizes to tray if pystray is available.

Dependencies: requests websockets (pystray pillow zeroconf optional)
"""

from __future__ import annotations

import asyncio
import base64
import json
import logging
import queue
import socket
import sys
import threading
import time
import tkinter as tk
from pathlib import Path
from tkinter import messagebox, scrolledtext, ttk
from typing import Optional

import ssl

import certifi
import requests
import websockets
import websockets.exceptions

# SSL context using certifi's CA bundle — required for PyInstaller builds on
# macOS/Windows where the system certificate store isn't accessible
_SSL_CONTEXT = ssl.create_default_context(cafile=certifi.where())

# ── Optional: zeroconf for mDNS discovery ──────────────────────────────────
try:
    from zeroconf import ServiceBrowser, Zeroconf

    _HAS_ZEROCONF = True
except ImportError:
    _HAS_ZEROCONF = False

# ── Optional: pystray + Pillow for minimize-to-tray ────────────────────────
try:
    import pystray
    from PIL import Image, ImageDraw

    _HAS_TRAY = True
except ImportError:
    _HAS_TRAY = False

# ── Build metadata (replaced by CI at build time) ──────────────────────────
VERSION = "dev"
CONNECTION_CODE = ""

# ── Constants ───────────────────────────────────────────────────────────────
CONFIG_DIR = Path.home() / ".propresenter_bridge"
CONFIG_FILE = CONFIG_DIR / "config.json"
LOG_FILE = CONFIG_DIR / "bridge.log"
PP_DEFAULT_HOST = "localhost"
PP_DEFAULT_PORT = 50001
BACKEND_RECONNECT_SEC = 3
PP_POLL_INTERVAL_SEC = 1.0
PING_INTERVAL_SEC = 20
NETWORK_SCAN_TIMEOUT = 0.4  # seconds per host during scan
NETWORK_SCAN_WORKERS = 40  # parallel threads for subnet scan


# ══════════════════════════════════════════════════════════════════════════════
# Logging — writes to file + GUI queue
# ══════════════════════════════════════════════════════════════════════════════

CONFIG_DIR.mkdir(parents=True, exist_ok=True)

_log_queue: queue.Queue = queue.Queue()


class _QueueHandler(logging.Handler):
    def emit(self, record):
        _log_queue.put(self.format(record))


_file_handler = logging.FileHandler(LOG_FILE, encoding="utf-8")
_queue_handler = _QueueHandler()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[logging.StreamHandler(sys.stdout), _file_handler, _queue_handler],
)
logger = logging.getLogger(__name__)


# ══════════════════════════════════════════════════════════════════════════════
# Config helpers
# ══════════════════════════════════════════════════════════════════════════════


def _decode_connection_code(code: str) -> dict:
    """Accept base64-encoded JSON or raw JSON."""
    code = code.strip()
    # Try raw JSON first
    if code.startswith("{"):
        try:
            return json.loads(code)
        except Exception:
            pass
    # Add padding and decode base64
    padded = code + "=" * (-len(code) % 4)
    try:
        return json.loads(base64.b64decode(padded).decode())
    except Exception as e:
        raise ValueError(f"Could not parse connection code: {e}") from e


def load_config() -> Optional[dict]:
    if CONFIG_FILE.exists():
        try:
            return json.loads(CONFIG_FILE.read_text())
        except Exception:
            pass
    return None


def save_config(cfg: dict):
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    CONFIG_FILE.write_text(json.dumps(cfg, indent=2))
    logger.info(f"Config saved to {CONFIG_FILE}")


# ══════════════════════════════════════════════════════════════════════════════
# ProPresenter REST client
# ══════════════════════════════════════════════════════════════════════════════


class ProPresenterClient:
    """Thin wrapper around ProPresenter's local REST API (v1)."""

    def __init__(self, host: str, port: int):
        self.host = host
        self.port = port
        self.base = f"http://{host}:{port}/v1"
        self._session = requests.Session()
        self._session.timeout = 2
        self._session.verify = certifi.where()

    def _get(self, path: str) -> Optional[dict]:
        try:
            r = self._session.get(f"{self.base}{path}", timeout=2)
            r.raise_for_status()
            return r.json()
        except Exception as e:
            logger.warning(f"PP GET {path} → {type(e).__name__}: {e}")
            return None

    def is_alive(self) -> bool:
        """Check ProPresenter is reachable via TCP (avoids JSON parsing issues)."""
        return _check_port(self.host, self.port, timeout=1.0)

    def get_active_presentation(self) -> Optional[dict]:
        """
        Returns {uuid, name, slide_index, slides} for whatever is currently active.

        Uses /presentation/active as the source of truth for identity and slide texts.
        Also calls /presentation/slide_index (undocumented but working) for the current
        slide number — falls back to 0 for Bible verses where that endpoint returns null.
        """
        # Get current slide index if available (null for Bible/no-id presentations)
        slide_index = 0
        idx_data = self._get("/presentation/slide_index")
        if idx_data:
            info = idx_data.get("presentation_index") or {}
            slide_index = info.get("index", 0)

        # Full active presentation — works for both regular and Bible
        active_data = self._get("/presentation/active")
        if not active_data:
            return None

        pres = active_data.get("presentation") or {}
        groups = pres.get("groups", [])

        slides: list[str] = []
        slide_labels: list[str] = []
        for group in groups:
            for slide in group.get("slides", []):
                slides.append(slide.get("text", ""))
                slide_labels.append(slide.get("label", ""))

        if not slides:
            return None

        # Regular presentations have id.uuid; Bible verses have id=null → use groups[0].uuid
        pres_id = pres.get("id") or {}
        uuid = pres_id.get("uuid", "")
        name = pres_id.get("name", "")
        if not uuid and groups:
            uuid = groups[0].get("uuid", "")
            name = groups[0].get("name", "")  # e.g. "Genesis 2:1-25"

        if not uuid:
            return None

        # Find which group the current slide belongs to
        group_name = ""
        slide_count = 0
        for group in groups:
            group_slides = group.get("slides", [])
            if slide_count + len(group_slides) > slide_index:
                group_name = group.get("name", "")
                break
            slide_count += len(group_slides)

        slide_label = slide_labels[slide_index] if slide_index < len(slide_labels) else ""
        return {
            "uuid": uuid,
            "name": name,
            "slide_index": slide_index,
            "slides": slides,
            "slide_labels": slide_labels,
            "slide_label": slide_label,
            "group_name": group_name,
        }

    def get_libraries(self) -> list:
        # Response: [{"id": {"uuid": "...", "name": "...", "index": N}}]
        data = self._get("/libraries")
        if not data:
            return []
        items = data if isinstance(data, list) else data.get("libraries", [])
        return [
            {
                "id": item.get("id", {}).get("uuid", item.get("uuid", "")),
                "name": item.get("id", {}).get("name", item.get("name", "")),
            }
            for item in items
        ]

    def get_library(self, lib_id: str) -> list:
        # GET /v1/library/{id} → {updateType, items: [{uuid, name, index}]}
        data = self._get(f"/library/{lib_id}")
        if not data:
            return []
        items = data.get("items", data if isinstance(data, list) else [])
        return [{"name": p.get("name", ""), "uuid": p.get("uuid", "")} for p in items]

    def get_presentation(self, uuid: str) -> Optional[dict]:
        # ProPresenter only serves slide content for the currently active presentation.
        # Use /presentation/active — the user should navigate to the song in PP first.
        data = self._get("/presentation/active")
        if not data:
            return None
        pres = data.get("presentation", data) if isinstance(data, dict) else {}
        groups = pres.get("groups", [])
        texts = []
        for group in groups:
            for slide in group.get("slides", []):
                text = slide.get("text", "")
                if text:
                    texts.append(text)
        return {"slide_text": texts or None}

    def get_playlists(self) -> list:
        # Mirrors the libraries pattern: /v1/playlists returns list of playlists
        data = self._get("/playlists")
        if not data:
            return []
        items = data if isinstance(data, list) else data.get("playlists", [])
        return [
            {
                "id": item.get("id", {}).get("uuid", item.get("uuid", "")),
                "name": item.get("id", {}).get("name", item.get("name", "")),
            }
            for item in items
            if item.get("id", {}).get("uuid", item.get("uuid", ""))
        ]

    def get_playlist_items(self, playlist_id: str) -> list:
        # GET /v1/playlist/{id} → {id, items: [{id:{uuid,name,index}, type, presentation_info, ...}]}
        # item.id.uuid is the PLAYLIST ITEM uuid — NOT the presentation file uuid.
        # presentation_info.presentation_uuid is the actual presentation UUID for /v1/presentation/{uuid}.
        data = self._get(f"/playlist/{playlist_id}")
        if not data:
            return []
        items = data.get("items", data if isinstance(data, list) else [])
        presentations = []
        for item in items:
            if item.get("type") != "presentation":
                continue
            item_id = item.get("id", {})
            name = item_id.get("name", "") if isinstance(item_id, dict) else ""
            pres_info = item.get("presentation_info") or {}
            uuid = (
                pres_info.get("presentation_uuid")
                or item.get("target_uuid")
                or (item_id.get("uuid", "") if isinstance(item_id, dict) else "")
            )
            if uuid and name:
                presentations.append({"name": name, "uuid": uuid})
        return presentations


# ══════════════════════════════════════════════════════════════════════════════
# ProPresenter discovery
# ══════════════════════════════════════════════════════════════════════════════


def _check_port(host: str, port: int, timeout: float = NETWORK_SCAN_TIMEOUT) -> bool:
    """Quick TCP connect check — doesn't hit the HTTP API."""
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


def _get_local_subnet() -> Optional[str]:
    """Return local machine's /24 subnet, e.g. '192.168.1'."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        parts = ip.split(".")
        if len(parts) == 4:
            return ".".join(parts[:3])
    except Exception:
        pass
    return None


def scan_network_for_propresenter(
    port: int = PP_DEFAULT_PORT,
    on_progress: Optional[callable] = None,
) -> list[str]:
    """
    Parallel TCP scan of local /24 subnet for hosts with port open,
    then verify with ProPresenter API.
    Returns list of IPs that responded.
    """
    subnet = _get_local_subnet()
    if not subnet:
        logger.warning("Could not determine local subnet for network scan")
        return []

    candidates = [f"{subnet}.{i}" for i in range(1, 255)]
    results = []
    lock = threading.Lock()
    total = len(candidates)
    checked = [0]

    def check(host):
        if _check_port(host, port):
            client = ProPresenterClient(host, port)
            if client.is_alive():
                with lock:
                    results.append(host)
        with lock:
            checked[0] += 1
            if on_progress:
                on_progress(checked[0], total)

    threads = []
    for host in candidates:
        t = threading.Thread(target=check, args=(host,), daemon=True)
        threads.append(t)
        t.start()
        # Throttle thread creation
        if len(threads) >= NETWORK_SCAN_WORKERS:
            for t in threads:
                t.join()
            threads = []

    for t in threads:
        t.join()

    return results


def _discover_mdns(port: int = PP_DEFAULT_PORT, timeout: float = 3.0) -> Optional[tuple[str, int]]:
    if not _HAS_ZEROCONF:
        return None
    found = []

    class Listener:
        def add_service(self, zc, type_, name):
            info = zc.get_service_info(type_, name)
            if info and info.addresses:
                try:
                    addr = socket.inet_ntoa(info.addresses[0])
                    found.append((addr, info.port or port))
                except Exception:
                    pass

        def remove_service(self, *_):
            pass

        def update_service(self, *_):
            pass

    zc = Zeroconf()
    ServiceBrowser(zc, "_propresenter._tcp.local.", Listener())
    time.sleep(timeout)
    zc.close()
    return found[0] if found else None


def find_propresenter_quick(host: str, port: int) -> tuple[str, int, bool]:
    """
    Fast check: try configured host:port, then localhost:50001.
    Returns (host, port, found).
    """
    if ProPresenterClient(host, port).is_alive():
        return host, port, True
    if host != PP_DEFAULT_HOST or port != PP_DEFAULT_PORT:
        if ProPresenterClient(PP_DEFAULT_HOST, PP_DEFAULT_PORT).is_alive():
            return PP_DEFAULT_HOST, PP_DEFAULT_PORT, True
    return host, port, False


# ══════════════════════════════════════════════════════════════════════════════
# Bridge state
# ══════════════════════════════════════════════════════════════════════════════


class BridgeState:
    def __init__(self):
        self.backend_connected = False
        self.pp_connected = False
        self.now_playing: str = "—"
        self.backend_status: str = "Not connected"
        self.pp_status: str = "Not found"
        self.loop: Optional[asyncio.AbstractEventLoop] = None
        self.stop_event = threading.Event()
        self.cfg: dict = {}
        self.tray_icon = None
        # Callbacks set by GUI
        self.on_state_change: Optional[callable] = None

    def notify(self):
        if self.on_state_change:
            self.on_state_change()


state = BridgeState()


# ══════════════════════════════════════════════════════════════════════════════
# Bridge async core
# ══════════════════════════════════════════════════════════════════════════════


async def _run_bridge(cfg: dict):
    backend_url = cfg["backend_url"]
    church_id = cfg["church_id"]
    token = cfg.get("token", "")
    pp_host = cfg.get("pp_host", PP_DEFAULT_HOST)
    pp_port = int(cfg.get("pp_port", PP_DEFAULT_PORT))

    ws_url = (
        backend_url.replace("http://", "ws://").replace("https://", "wss://")
        + f"/api/propresenter/ws/propresenter/{church_id}?token={token}"
    )

    last_uuid: str = ""
    last_slide: int = -1

    while not state.stop_event.is_set():
        # Re-read pp_host/port from cfg in case user changed it via GUI
        pp_host = state.cfg.get("pp_host", PP_DEFAULT_HOST)
        pp_port = int(state.cfg.get("pp_port", PP_DEFAULT_PORT))

        pp_host, pp_port, pp_ok = find_propresenter_quick(pp_host, pp_port)
        state.pp_connected = pp_ok
        state.pp_status = f"{pp_host}:{pp_port} — connected" if pp_ok else f"{pp_host}:{pp_port} — not found"
        state.notify()
        pp_client = ProPresenterClient(pp_host, pp_port)

        if not pp_ok:
            logger.warning(f"ProPresenter not found at {pp_host}:{pp_port}")
            state.backend_status = "Waiting for ProPresenter…"
            state.notify()
            await asyncio.sleep(BACKEND_RECONNECT_SEC)
            continue

        logger.info(f"ProPresenter found at {pp_host}:{pp_port}")

        try:
            async with websockets.connect(ws_url, ssl=_SSL_CONTEXT, ping_interval=PING_INTERVAL_SEC) as ws:
                state.backend_connected = True
                host_display = backend_url.replace("https://", "").replace("http://", "")
                state.backend_status = f"{host_display} — connected"
                state.notify()
                logger.info(f"Connected to backend: {ws_url}")

                active = pp_client.get_active_presentation()
                if active:
                    last_uuid = active["uuid"]
                    last_slide = active["slide_index"]
                    slides = active["slides"]
                    slide_text = slides[last_slide] if last_slide < len(slides) else ""
                    state.now_playing = active["name"] or "Unknown"
                    state.notify()
                    await ws.send(json.dumps({
                        "type": "presentation_changed",
                        "name": active["name"],
                        "uuid": active["uuid"],
                        "slide_index": last_slide,
                        "slide_text": slide_text,
                        "slide_label": active.get("slide_label", ""),
                        "group_name": active.get("group_name", ""),
                    }))

                while not state.stop_event.is_set():
                    try:
                        raw = await asyncio.wait_for(ws.recv(), timeout=PP_POLL_INTERVAL_SEC)
                        msg = json.loads(raw)
                        await _handle_backend_message(ws, msg, pp_client)
                    except asyncio.TimeoutError:
                        pass
                    except websockets.exceptions.ConnectionClosed:
                        logger.warning("Backend WebSocket closed")
                        break

                    if not pp_client.is_alive():
                        logger.warning("ProPresenter stopped responding")
                        state.pp_connected = False
                        state.pp_status = f"{pp_host}:{pp_port} — lost connection"
                        state.notify()
                        break

                    state.pp_connected = True
                    active = pp_client.get_active_presentation()
                    if active:
                        slides = active["slides"]
                        slide_labels = active.get("slide_labels", [])
                        if active["uuid"] != last_uuid:
                            last_uuid = active["uuid"]
                            last_slide = active["slide_index"]
                            slide_text = slides[last_slide] if last_slide < len(slides) else ""
                            slide_label = slide_labels[last_slide] if last_slide < len(slide_labels) else ""
                            state.now_playing = active["name"] or "Unknown"
                            state.notify()
                            logger.info(f"Presentation: '{active['name']}' slide={last_slide} text={slide_text!r}")
                            await ws.send(json.dumps({
                                "type": "presentation_changed",
                                "name": active["name"],
                                "uuid": active["uuid"],
                                "slide_index": last_slide,
                                "slide_text": slide_text,
                                "slide_label": slide_label,
                                "group_name": active.get("group_name", ""),
                            }))
                        elif active["slide_index"] != last_slide:
                            last_slide = active["slide_index"]
                            slide_text = slides[last_slide] if last_slide < len(slides) else ""
                            slide_label = slide_labels[last_slide] if last_slide < len(slide_labels) else ""
                            logger.info(f"Slide changed: {last_slide} text={slide_text!r}")
                            await ws.send(json.dumps({
                                "type": "slide_changed",
                                "uuid": active["uuid"],
                                "index": last_slide,
                                "slide_text": slide_text,
                                "slide_label": slide_label,
                                "group_name": active.get("group_name", ""),
                            }))

        except (OSError, websockets.exceptions.WebSocketException) as e:
            logger.warning(f"Backend connection error: {e}")
            state.backend_status = "Connection error — retrying…"
        except Exception as e:
            logger.error(f"Bridge error: {e}", exc_info=True)
            state.backend_status = f"Error: {e}"
        finally:
            state.backend_connected = False
            state.notify()

        if not state.stop_event.is_set():
            logger.info(f"Reconnecting in {BACKEND_RECONNECT_SEC}s…")
            await asyncio.sleep(BACKEND_RECONNECT_SEC)


async def _handle_backend_message(ws, msg: dict, pp_client: ProPresenterClient):
    t = msg.get("type")
    if t == "ping":
        await ws.send(json.dumps({"type": "pong"}))
    elif t == "get_active":
        await ws.send(json.dumps({"type": "query_reply", "presentation": pp_client.get_active_presentation()}))
    elif t == "get_libraries":
        await ws.send(json.dumps({"type": "libraries_reply", "libraries": pp_client.get_libraries()}))
    elif t == "get_library":
        await ws.send(json.dumps({"type": "library_reply", "presentations": pp_client.get_library(msg.get("id", ""))}))
    elif t == "get_playlists":
        await ws.send(json.dumps({"type": "playlists_reply", "playlists": pp_client.get_playlists()}))
    elif t == "get_playlist":
        await ws.send(json.dumps({"type": "playlist_reply", "presentations": pp_client.get_playlist_items(msg.get("id", ""))}))
    elif t == "get_presentation":
        data = pp_client.get_presentation(msg.get("uuid", ""))
        await ws.send(
            json.dumps({"type": "presentation_reply", "slide_text": data.get("slide_text") if data else None})
        )
    elif t == "close":
        await ws.close()


def _run_asyncio_loop(cfg: dict):
    loop = asyncio.new_event_loop()
    state.loop = loop
    asyncio.set_event_loop(loop)
    try:
        loop.run_until_complete(_run_bridge(cfg))
    finally:
        loop.close()


# ══════════════════════════════════════════════════════════════════════════════
# Tray icon helpers (optional)
# ══════════════════════════════════════════════════════════════════════════════


def _make_tray_icon(color: str) -> "Image.Image":
    img = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    colors = {"green": (34, 197, 94), "yellow": (234, 179, 8), "red": (239, 68, 68)}
    draw.ellipse((8, 8, 56, 56), fill=colors.get(color, (128, 128, 128)))
    return img


# ══════════════════════════════════════════════════════════════════════════════
# Main GUI window
# ══════════════════════════════════════════════════════════════════════════════


class BridgeWindow:
    """Main tkinter window for the ProPresenter Bridge."""

    def __init__(self, root: tk.Tk, cfg: dict):
        self.root = root
        self.cfg = cfg
        self._scanning = False
        self._bridge_thread: Optional[threading.Thread] = None

        root.title(f"Versespan  {VERSION}")
        root.resizable(True, True)
        root.minsize(540, 560)
        root.protocol("WM_DELETE_WINDOW", self._on_close)

        self._build_ui()
        self._start_bridge()

        # Register state-change callback
        state.on_state_change = self._schedule_update

        # Poll log queue and state changes
        self._poll_ui()

    # ── UI construction ────────────────────────────────────────────────────

    def _build_ui(self):
        pad = {"padx": 10, "pady": 6}

        # ── Status bar at top ──────────────────────────────────────────────
        status_frame = ttk.LabelFrame(self.root, text="Status", padding=8)
        status_frame.pack(fill="x", **pad)
        status_frame.columnconfigure(1, weight=1)

        ttk.Label(status_frame, text="Backend:").grid(row=0, column=0, sticky="w")
        self._backend_dot = tk.Label(status_frame, text="●", fg="red", font=("", 14))
        self._backend_dot.grid(row=0, column=1, sticky="w")
        self._backend_label = ttk.Label(status_frame, text="Not connected")
        self._backend_label.grid(row=0, column=2, sticky="w", padx=(4, 0))

        ttk.Label(status_frame, text="ProPresenter:").grid(row=1, column=0, sticky="w")
        self._pp_dot = tk.Label(status_frame, text="●", fg="red", font=("", 14))
        self._pp_dot.grid(row=1, column=1, sticky="w")
        self._pp_label = ttk.Label(status_frame, text="Not found")
        self._pp_label.grid(row=1, column=2, sticky="w", padx=(4, 0))

        ttk.Label(status_frame, text="Now playing:").grid(row=2, column=0, sticky="w")
        self._now_playing_label = ttk.Label(status_frame, text="—", font=("", 10, "bold"))
        self._now_playing_label.grid(row=2, column=1, columnspan=2, sticky="w", padx=(4, 0))

        # ── ProPresenter connection ────────────────────────────────────────
        pp_frame = ttk.LabelFrame(self.root, text="ProPresenter Connection", padding=8)
        pp_frame.pack(fill="x", **pad)
        pp_frame.columnconfigure(1, weight=1)

        ttk.Label(pp_frame, text="Host:").grid(row=0, column=0, sticky="w")
        self._pp_host_var = tk.StringVar(value=self.cfg.get("pp_host", PP_DEFAULT_HOST))
        self._pp_host_entry = ttk.Entry(pp_frame, textvariable=self._pp_host_var, width=22)
        self._pp_host_entry.grid(row=0, column=1, sticky="ew", padx=4)

        ttk.Label(pp_frame, text="Port:").grid(row=0, column=2, sticky="w", padx=(8, 0))
        self._pp_port_var = tk.StringVar(value=str(self.cfg.get("pp_port", PP_DEFAULT_PORT)))
        self._pp_port_entry = ttk.Entry(pp_frame, textvariable=self._pp_port_var, width=7)
        self._pp_port_entry.grid(row=0, column=3, padx=4)

        btn_frame = ttk.Frame(pp_frame)
        btn_frame.grid(row=1, column=0, columnspan=4, sticky="w", pady=(6, 0))

        self._test_btn = ttk.Button(btn_frame, text="Test Connection", command=self._test_pp)
        self._test_btn.pack(side="left", padx=(0, 6))

        self._scan_btn = ttk.Button(btn_frame, text="Scan Network", command=self._scan_network)
        self._scan_btn.pack(side="left", padx=(0, 6))

        self._apply_pp_btn = ttk.Button(btn_frame, text="Apply & Reconnect", command=self._apply_pp_settings)
        self._apply_pp_btn.pack(side="left")

        self._pp_test_result = ttk.Label(pp_frame, text="")
        self._pp_test_result.grid(row=2, column=0, columnspan=4, sticky="w", pady=(4, 0))

        # Scan results dropdown (hidden until scan runs)
        self._scan_result_var = tk.StringVar()
        self._scan_combo = ttk.Combobox(pp_frame, textvariable=self._scan_result_var, state="readonly", width=30)
        self._scan_combo.grid(row=3, column=0, columnspan=3, sticky="ew", pady=(4, 0))
        self._scan_combo.grid_remove()
        self._use_scan_btn = ttk.Button(pp_frame, text="Use Selected", command=self._use_scan_result)
        self._use_scan_btn.grid(row=3, column=3, pady=(4, 0))
        self._use_scan_btn.grid_remove()

        # ── Connection code ───────────────────────────────────────────────
        code_frame = ttk.LabelFrame(self.root, text="Connection Code", padding=8)
        code_frame.pack(fill="x", **pad)
        code_frame.columnconfigure(0, weight=1)

        ttk.Label(code_frame, text="Paste your connection code from the admin Settings page:").grid(
            row=0, column=0, columnspan=2, sticky="w"
        )
        self._code_var = tk.StringVar()
        self._code_entry = ttk.Entry(code_frame, textvariable=self._code_var, show="*")
        self._code_entry.grid(row=1, column=0, sticky="ew", pady=(4, 0), padx=(0, 6))
        self._apply_code_btn = ttk.Button(code_frame, text="Apply Code", command=self._apply_code)
        self._apply_code_btn.grid(row=1, column=1, pady=(4, 0))
        self._code_result = ttk.Label(code_frame, text="")
        self._code_result.grid(row=2, column=0, columnspan=2, sticky="w", pady=(4, 0))

        # Current backend URL display
        self._backend_url_label = ttk.Label(
            code_frame,
            text=f"Backend: {self.cfg.get('backend_url', '—')}  |  Church ID: {self.cfg.get('church_id', '—')}",
            foreground="gray",
        )
        self._backend_url_label.grid(row=3, column=0, columnspan=2, sticky="w", pady=(4, 0))

        # ── Log ───────────────────────────────────────────────────────────
        log_frame = ttk.LabelFrame(self.root, text="Log", padding=4)
        log_frame.pack(fill="both", expand=True, **pad)

        self._log_text = scrolledtext.ScrolledText(
            log_frame,
            height=10,
            state="disabled",
            wrap="word",
            font=("Courier", 9),
            background="#1e1e1e",
            foreground="#d4d4d4",
        )
        self._log_text.pack(fill="both", expand=True)

        ttk.Button(log_frame, text="Clear Log", command=self._clear_log).pack(anchor="e", pady=(4, 0))

    # ── Bridge management ──────────────────────────────────────────────────

    def _start_bridge(self):
        state.stop_event.clear()
        self._bridge_thread = threading.Thread(target=_run_asyncio_loop, args=(self.cfg,), daemon=True)
        self._bridge_thread.start()

    def _restart_bridge(self):
        state.stop_event.set()
        if self._bridge_thread:
            self._bridge_thread.join(timeout=4)
        state.stop_event.clear()
        state.backend_connected = False
        state.pp_connected = False
        state.now_playing = "—"
        self._start_bridge()

    # ── UI callbacks ───────────────────────────────────────────────────────

    def _test_pp(self):
        host = self._pp_host_var.get().strip()
        try:
            port = int(self._pp_port_var.get().strip())
        except ValueError:
            self._pp_test_result.config(text="✗ Invalid port number", foreground="red")
            return
        self._pp_test_result.config(text="Testing…", foreground="gray")
        self._test_btn.config(state="disabled")

        def _do_test():
            client = ProPresenterClient(host, port)
            ok = client.is_alive()
            self.root.after(
                0,
                lambda: (
                    self._pp_test_result.config(
                        text=(
                            f"✓ ProPresenter responded at {host}:{port}"
                            if ok
                            else f"✗ No response from {host}:{port} — check host/port and that ProPresenter is running"
                        ),
                        foreground="green" if ok else "red",
                    ),
                    self._test_btn.config(state="normal"),
                ),
            )

        threading.Thread(target=_do_test, daemon=True).start()

    def _scan_network(self):
        if self._scanning:
            return
        self._scanning = True
        self._scan_btn.config(state="disabled", text="Scanning…")
        self._pp_test_result.config(text="Scanning local network for ProPresenter…", foreground="gray")
        self._scan_combo.grid_remove()
        self._use_scan_btn.grid_remove()

        def _do_scan():
            try:
                port = int(self._pp_port_var.get().strip())
            except ValueError:
                port = PP_DEFAULT_PORT

            def _progress(done, total):
                pct = int(done / total * 100)
                self.root.after(0, lambda: self._pp_test_result.config(text=f"Scanning… {pct}%", foreground="gray"))

            results = scan_network_for_propresenter(port=port, on_progress=_progress)

            def _done():
                self._scanning = False
                self._scan_btn.config(state="normal", text="Scan Network")
                if results:
                    self._pp_test_result.config(
                        text=f"Found {len(results)} host(s) running ProPresenter",
                        foreground="green",
                    )
                    self._scan_combo["values"] = results
                    self._scan_result_var.set(results[0])
                    self._scan_combo.grid()
                    self._use_scan_btn.grid()
                else:
                    # Try mDNS as fallback
                    mdns = _discover_mdns(port=port, timeout=2.0)
                    if mdns:
                        self._pp_test_result.config(
                            text=f"Found via mDNS: {mdns[0]}:{mdns[1]}",
                            foreground="green",
                        )
                        self._pp_host_var.set(mdns[0])
                        self._pp_port_var.set(str(mdns[1]))
                    else:
                        self._pp_test_result.config(
                            text="No ProPresenter found on network. Enter IP manually.",
                            foreground="orange",
                        )

            self.root.after(0, _done)

        threading.Thread(target=_do_scan, daemon=True).start()

    def _use_scan_result(self):
        selected = self._scan_result_var.get()
        if selected:
            self._pp_host_var.set(selected)
            self._scan_combo.grid_remove()
            self._use_scan_btn.grid_remove()

    def _apply_pp_settings(self):
        host = self._pp_host_var.get().strip()
        try:
            port = int(self._pp_port_var.get().strip())
        except ValueError:
            messagebox.showerror("Invalid Port", "Port must be a number.")
            return
        self.cfg["pp_host"] = host
        self.cfg["pp_port"] = port
        state.cfg["pp_host"] = host
        state.cfg["pp_port"] = port
        save_config(self.cfg)
        logger.info(f"ProPresenter host updated to {host}:{port} — reconnecting")
        self._restart_bridge()

    def _apply_code(self):
        code = self._code_var.get().strip()
        if not code:
            self._code_result.config(text="Please paste your connection code.", foreground="red")
            return
        try:
            data = _decode_connection_code(code)
            required = {"backend_url", "church_id"}
            if not required.issubset(data.keys()):
                raise ValueError("Missing backend_url or church_id")
            self.cfg.update(
                {
                    "backend_url": data["backend_url"].rstrip("/"),
                    "church_id": data["church_id"],
                    "token": data.get("token", self.cfg.get("token", "")),
                    "pp_host": data.get("pp_host", self.cfg.get("pp_host", PP_DEFAULT_HOST)),
                    "pp_port": data.get("pp_port", self.cfg.get("pp_port", PP_DEFAULT_PORT)),
                }
            )
            state.cfg.update(self.cfg)
            save_config(self.cfg)
            self._code_entry.delete(0, "end")
            self._code_result.config(text="✓ Connection code applied — reconnecting", foreground="green")
            self._backend_url_label.config(
                text=f"Backend: {self.cfg['backend_url']}  |  Church ID: {self.cfg['church_id']}"
            )
            self._pp_host_var.set(str(self.cfg.get("pp_host", PP_DEFAULT_HOST)))
            self._pp_port_var.set(str(self.cfg.get("pp_port", PP_DEFAULT_PORT)))
            logger.info(f"Connection code applied — backend={self.cfg['backend_url']}")
            self._restart_bridge()
        except Exception as e:
            self._code_result.config(text=f"✗ {e}", foreground="red")

    def _clear_log(self):
        self._log_text.config(state="normal")
        self._log_text.delete("1.0", "end")
        self._log_text.config(state="disabled")

    # ── State update (called from bridge thread via after()) ───────────────

    def _schedule_update(self):
        self.root.after(0, self._refresh_status)

    def _refresh_status(self):
        # Backend dot
        b_color = "green" if state.backend_connected else "red"
        self._backend_dot.config(fg=b_color)
        self._backend_label.config(text=state.backend_status)

        # PP dot
        if state.pp_connected:
            pp_color = "green" if state.backend_connected else "orange"
        else:
            pp_color = "red"
        self._pp_dot.config(fg=pp_color)
        self._pp_label.config(text=state.pp_status)

        self._now_playing_label.config(text=state.now_playing)

        # Update tray icon if available
        if _HAS_TRAY and state.tray_icon:
            color = (
                "green"
                if (state.backend_connected and state.pp_connected)
                else "yellow" if state.backend_connected else "red"
            )
            try:
                state.tray_icon.icon = _make_tray_icon(color)
                state.tray_icon.title = f"Versespan — {state.now_playing}"
            except Exception:
                pass

    # ── Log polling ────────────────────────────────────────────────────────

    def _poll_ui(self):
        try:
            while True:
                line = _log_queue.get_nowait()
                self._log_text.config(state="normal")
                self._log_text.insert("end", line + "\n")
                self._log_text.see("end")
                self._log_text.config(state="disabled")
        except queue.Empty:
            pass
        self.root.after(200, self._poll_ui)

    # ── Window close / minimize to tray ───────────────────────────────────

    def _on_close(self):
        if _HAS_TRAY:
            self._minimize_to_tray()
        else:
            if messagebox.askokcancel("Quit", "Stop the ProPresenter Bridge?"):
                self._quit()

    def _minimize_to_tray(self):
        self.root.withdraw()
        if state.tray_icon:
            return  # already in tray

        color = (
            "green"
            if (state.backend_connected and state.pp_connected)
            else "yellow" if state.backend_connected else "red"
        )
        icon_img = _make_tray_icon(color)

        def _show_window(icon, _item):
            icon.stop()
            state.tray_icon = None
            self.root.after(0, self.root.deiconify)

        def _quit_from_tray(icon, _item):
            icon.stop()
            state.tray_icon = None
            self.root.after(0, self._quit)

        menu = pystray.Menu(
            pystray.MenuItem("Open Window", _show_window, default=True),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem("Quit", _quit_from_tray),
        )
        tray = pystray.Icon("ProPresenter Bridge", icon_img, "ProPresenter Bridge", menu)
        state.tray_icon = tray
        threading.Thread(target=tray.run, daemon=True).start()

    def _quit(self):
        state.stop_event.set()
        self.root.destroy()


# ══════════════════════════════════════════════════════════════════════════════
# Setup flow for first run / missing config
# ══════════════════════════════════════════════════════════════════════════════


def _show_setup_dialog(pre_code: str = "") -> Optional[dict]:
    """
    Blocking setup dialog shown when no config exists.
    Returns cfg dict or None if user cancelled.
    """
    result = [None]

    dlg = tk.Tk()
    dlg.title("Versespan — First Run Setup")
    dlg.resizable(False, False)

    ttk.Label(dlg, text="Welcome to Versespan", font=("", 13, "bold")).pack(pady=(16, 4), padx=20)
    ttk.Label(
        dlg,
        text="Paste your connection code from the admin Settings page.\n"
        "It was provided when you downloaded this app.",
        justify="center",
    ).pack(pady=(0, 12), padx=20)

    frame = ttk.Frame(dlg, padding=12)
    frame.pack(fill="x")
    frame.columnconfigure(0, weight=1)

    ttk.Label(frame, text="Connection Code:").grid(row=0, column=0, sticky="w")
    code_var = tk.StringVar(value=pre_code)
    code_entry = ttk.Entry(frame, textvariable=code_var, width=48)
    code_entry.grid(row=1, column=0, sticky="ew", pady=(4, 0))

    err_label = ttk.Label(frame, text="", foreground="red")
    err_label.grid(row=2, column=0, sticky="w", pady=(4, 0))

    sep = ttk.Separator(frame, orient="horizontal")
    sep.grid(row=3, column=0, sticky="ew", pady=12)

    ttk.Label(frame, text="— OR fill in manually —", foreground="gray").grid(row=4, column=0)

    manual = ttk.Frame(frame)
    manual.grid(row=5, column=0, sticky="ew", pady=(8, 0))
    manual.columnconfigure(1, weight=1)

    ttk.Label(manual, text="Backend URL:").grid(row=0, column=0, sticky="w")
    url_var = tk.StringVar(value="https://versespan-api.fly.dev")
    ttk.Entry(manual, textvariable=url_var, width=38).grid(row=0, column=1, sticky="ew", padx=(6, 0))

    ttk.Label(manual, text="Church ID:").grid(row=1, column=0, sticky="w", pady=(6, 0))
    church_var = tk.StringVar()
    ttk.Entry(manual, textvariable=church_var, width=10).grid(row=1, column=1, sticky="w", padx=(6, 0), pady=(6, 0))

    ttk.Label(manual, text="API Token:").grid(row=2, column=0, sticky="w", pady=(6, 0))
    token_var = tk.StringVar()
    ttk.Entry(manual, textvariable=token_var, width=38, show="*").grid(
        row=2, column=1, sticky="ew", padx=(6, 0), pady=(6, 0)
    )

    btn_frame = ttk.Frame(dlg)
    btn_frame.pack(pady=12)

    def _submit():
        code = code_var.get().strip()
        cfg = None

        if code:
            try:
                data = _decode_connection_code(code)
                required = {"backend_url", "church_id"}
                if not required.issubset(data.keys()):
                    err_label.config(text="Code is missing backend_url or church_id.")
                    return
                cfg = {
                    "backend_url": data["backend_url"].rstrip("/"),
                    "church_id": data["church_id"],
                    "token": data.get("token", ""),
                    "pp_host": data.get("pp_host", PP_DEFAULT_HOST),
                    "pp_port": data.get("pp_port", PP_DEFAULT_PORT),
                }
            except ValueError as e:
                err_label.config(text=str(e))
                return
        else:
            url = url_var.get().strip()
            church = church_var.get().strip()
            if not url or not church:
                err_label.config(text="Enter a connection code OR fill in Backend URL and Church ID.")
                return
            cfg = {
                "backend_url": url.rstrip("/"),
                "church_id": church,
                "token": token_var.get().strip(),
                "pp_host": PP_DEFAULT_HOST,
                "pp_port": PP_DEFAULT_PORT,
            }

        result[0] = cfg
        dlg.destroy()

    def _cancel():
        dlg.destroy()

    ttk.Button(btn_frame, text="Connect", command=_submit).pack(side="left", padx=8)
    ttk.Button(btn_frame, text="Cancel", command=_cancel).pack(side="left")

    code_entry.focus()
    dlg.mainloop()
    return result[0]


# ══════════════════════════════════════════════════════════════════════════════
# Entry point
# ══════════════════════════════════════════════════════════════════════════════


def main():
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    cfg = None

    # 1. Try pre-injected connection code
    if CONNECTION_CODE:
        try:
            data = _decode_connection_code(CONNECTION_CODE)
            cfg = {
                "backend_url": data["backend_url"].rstrip("/"),
                "church_id": data["church_id"],
                "token": data.get("token", ""),
                "pp_host": data.get("pp_host", PP_DEFAULT_HOST),
                "pp_port": data.get("pp_port", PP_DEFAULT_PORT),
            }
            save_config(cfg)
            logger.info("Config loaded from embedded connection code")
        except Exception as e:
            logger.error(f"Failed to parse embedded connection code: {e}")

    # 2. Try saved config
    if cfg is None:
        cfg = load_config()
        if cfg:
            logger.info(f"Config loaded from {CONFIG_FILE}")

    # 3. First-run setup dialog
    if cfg is None:
        logger.info("No config found — showing setup dialog")
        pre_code = CONNECTION_CODE or ""
        cfg = _show_setup_dialog(pre_code)
        if cfg is None:
            logger.info("Setup cancelled — exiting")
            sys.exit(0)
        save_config(cfg)

    state.cfg = cfg

    # Launch main window
    root = tk.Tk()
    app = BridgeWindow(root, cfg)
    root.mainloop()

    # Cleanup
    state.stop_event.set()
    logger.info("Bridge stopped")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # noqa: BLE001
        import traceback

        msg = traceback.format_exc()
        try:
            import tkinter.messagebox as _mb

            _mb.showerror("Versespan — Fatal Error", msg)
        except Exception:
            print(msg)
        sys.exit(1)
