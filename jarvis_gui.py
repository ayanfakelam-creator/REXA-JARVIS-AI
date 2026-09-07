from email.mime import text
import pygetwindow as gw
import sys
import time
import math
import random
import shutil
import fnmatch
import asyncio
import threading
import subprocess
import tempfile
import datetime as dt
import urllib.parse
import webbrowser
import socket
import queue
import builtins
import json
import re
import base64
import io
import hashlib
import platform
import smtplib
import zipfile
import html
import urllib.error
import xml.etree.ElementTree as ET
from html.parser import HTMLParser
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.utils import formataddr
from pathlib import Path
import ast
import tkinter as tk
import os
from dotenv import load_dotenv

try:
    import requests
except ModuleNotFoundError as exc:
    if exc.name != "requests":
        raise
    requests = None

try:
    import chromadb
except ImportError:
    # Keep the JSON fallback available if ChromaDB is unavailable.
    chromadb = None

try:
    import wikipedia as wikipedia_api
except ImportError:
    wikipedia_api = None

try:
    import pytesseract
    tesseract_default_path = r"C:\Program Files\Tesseract-OCR\tesseract.exe"
    if os.path.exists(tesseract_default_path):
        pytesseract.pytesseract.tesseract_cmd = tesseract_default_path
except ImportError:
    pytesseract = None

try:
    import cv2
except ImportError:
    cv2 = None

try:
    from pynvml import (
        nvmlInit, nvmlDeviceGetCount, nvmlDeviceGetHandleByIndex,
        nvmlDeviceGetName, nvmlDeviceGetTemperature,
        NVML_TEMPERATURE_GPU, nvmlShutdown,
    )
except ImportError:
    nvmlInit = nvmlDeviceGetCount = nvmlDeviceGetHandleByIndex = None
    nvmlDeviceGetName = nvmlDeviceGetTemperature = nvmlShutdown = None

BASE_DIR = Path(__file__).resolve().parent
load_dotenv(BASE_DIR / ".env")
OPENROUTER_API_KEY = os.getenv("OPENROUTER_API_KEY")
OPENROUTER_BASE_URL = os.getenv(
    "OPENROUTER_BASE_URL",
    "https://openrouter.ai/api/v1",
)
OPENROUTER_MODEL = os.getenv(
    "OPENROUTER_MODEL",
    "openai/gpt-4o-mini",
).strip()
OPENROUTER_VISION_MODEL = os.getenv(
    "OPENROUTER_VISION_MODEL",
    "openai/gpt-4o-mini",
).strip()

try:
    from openai import OpenAI
except ImportError:
    OpenAI = None

# The optional SambaNova client is unavailable unless initialized elsewhere.
sambanova_client = None
if OpenAI is not None and OPENROUTER_API_KEY:
    try:
        openrouter_client = OpenAI(
            api_key=OPENROUTER_API_KEY,
            base_url=OPENROUTER_BASE_URL
        )
    except Exception:
        openrouter_client = None
else:
    openrouter_client = None
from tkinter import messagebox, simpledialog
try:
    import winreg
except ImportError:
    winreg = None
MEMORY_FILE = BASE_DIR / "memory.json"
VECTOR_MEMORY_FILE = BASE_DIR / "vector_memory.json"
WEB_CACHE_TTL_SECONDS = 15 * 60
web_cache = {}
_chroma_collection = None


def _get_chroma_collection():
    global _chroma_collection
    if chromadb is None:
        return None
    if _chroma_collection is None:
        client = chromadb.PersistentClient(path=str(BASE_DIR / ".rexa_chroma"))
        _chroma_collection = client.get_or_create_collection("rexa_memory")
    return _chroma_collection


def _vector_memory_items():
    items = memory.get("vector_memory", [])
    return items if isinstance(items, list) else []


def _remember_vector_text(text, kind="conversation"):
    """Persist redacted conversation facts for lightweight local retrieval."""
    cleaned = _redact_sensitive_text((text or "").strip())
    if len(cleaned) < 8:
        return
    items = _vector_memory_items()
    items.append({"text": cleaned[:1200], "kind": kind, "time": dt.datetime.now().isoformat()})
    memory["vector_memory"] = items[-500:]
    save_memory(memory)
    try:
        collection = _get_chroma_collection()
        if collection is not None:
            collection.upsert(
                ids=[hashlib.sha256(cleaned.encode("utf-8")).hexdigest()],
                documents=[cleaned[:1200]],
                metadatas=[{"kind": kind}],
            )
    except Exception as exc:
        log_message("REXA", f"[VECTOR-MEMORY] ChromaDB unavailable; using JSON fallback: {exc}")


def _retrieve_vector_memory(query, limit=3):
    """Retrieve relevant local memories without requiring a vector package."""
    try:
        collection = _get_chroma_collection()
        if collection is not None and query:
            result = collection.query(query_texts=[query], n_results=limit)
            documents = result.get("documents", [[]])
            return list(documents[0]) if documents else []
    except Exception as exc:
        log_message("REXA", f"[VECTOR-MEMORY] Retrieval fallback: {exc}")
    words = set(re.findall(r"[a-z0-9\u0980-\u09ff]{3,}", (query or "").casefold()))
    scored = []
    for item in _vector_memory_items():
        text = str(item.get("text", ""))
        overlap = len(words & set(re.findall(r"[a-z0-9\u0980-\u09ff]{3,}", text.casefold())))
        if overlap:
            scored.append((overlap, text))
    scored.sort(key=lambda pair: pair[0], reverse=True)
    return [text for _, text in scored[:limit]]


def load_memory():
    """Load local memory safely, including recovery from bad JSON."""
    try:
        if not MEMORY_FILE.exists():
            data = {
                "user_profile": {},
                "fact_graph": {"preferences": {}, "relationships": {}, "active_projects": {}},
                "protocol_states": {}, "facts": {}, "activity": [],
            }
            save_memory(data)
            return data

        data = json.loads(MEMORY_FILE.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("memory root must be an object")
        facts = data.get("facts", {})
        if not isinstance(facts, dict):
            data["facts"] = {}
        data.setdefault("user_profile", {})
        data.setdefault("fact_graph", {"preferences": {}, "relationships": {}, "active_projects": {}})
        data.setdefault("protocol_states", {})
        activities = data.get("activity", [])
        data["activity"] = activities[-500:] if isinstance(activities, list) else []
        return data
    except (OSError, json.JSONDecodeError, ValueError):
        return {
            "user_profile": {},
            "fact_graph": {"preferences": {}, "relationships": {}, "active_projects": {}},
            "protocol_states": {}, "facts": {}, "activity": [],
        }


def save_memory(data):
    try:
        activities = data.get("activity", [])
        if isinstance(activities, list):
            data["activity"] = activities[-500:]
        MEMORY_FILE.write_text(
            json.dumps(data, indent=2, ensure_ascii=True),
            encoding="utf-8"
        )
    except OSError:
        pass


memory = load_memory()

# ============================================================
# REXA AI - Gemini + bilingual voice + Windows Tools
# (Fixed + Upgraded version)
# ============================================================

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

# Optional packages
try:
    from dotenv import load_dotenv
except ImportError:
    load_dotenv = None
try:
    from google import genai
except ImportError:
    genai = None


try:
    import edge_tts
except ImportError:
    edge_tts = None

try:
    from pydub import AudioSegment  # pyright: ignore[reportMissingImports]
except ImportError:
    AudioSegment = None

try:
    import pygame
except ImportError:
    pygame = None

try:
    import psutil
except ImportError:
    psutil = None

try:
    import yt_dlp
except ImportError:
    yt_dlp = None

try:
    import pyautogui
except ImportError:
    pyautogui = None

try:
    import speech_recognition as sr
except ImportError:
    sr = None

try:
    import sounddevice as sd
except ImportError:
    sd = None

try:
    from faster_whisper import WhisperModel  # pyright: ignore[reportMissingImports]
except ImportError:
    WhisperModel = None

try:
    from silero_vad import (  # pyright: ignore[reportMissingImports]
        get_speech_timestamps,
        load_silero_vad,
    )
except ImportError:
    get_speech_timestamps = load_silero_vad = None

try:
    from PIL import ImageGrab
except ImportError:
    ImageGrab = None

try:
    from selenium import webdriver
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys
    from selenium.webdriver.chrome.service import Service as ChromeService
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC
    from webdriver_manager.chrome import ChromeDriverManager

    selenium_available = True

except ImportError:
    selenium_available = False
# ============================================================
# YOUTUBE SELENIUM STATE
# ============================================================

yt_driver = None          # Selenium WebDriver instance
yt_search_results = []    # List of {title, url} from last search
yt_context = {
    "mode": None,         # "search" | "playing" | "playlist"
    "query": None,
    "current_index": None,
    "current_url": None,
    "current_title": None,
}
youtube_scroll_mode_active = False

# Bangla digit + word → int
BANGLA_DIGIT_MAP = {
    "০": 0, "১": 1, "২": 2, "৩": 3, "৪": 4,
    "৫": 5, "৬": 6, "৭": 7, "৮": 8, "৯": 9,
}
BANGLA_WORD_MAP = {
    "এক": 1, "দুই": 2, "তিন": 3, "চার": 4, "পাঁচ": 5,
    "ছয়": 6, "সাত": 7, "আট": 8, "নয়": 9, "দশ": 10,
    "প্রথম": 1, "দ্বিতীয়": 2, "তৃতীয়": 3,
}
ENGLISH_ORDINAL_MAP = {
    "first": 1, "second": 2, "third": 3, "fourth": 4, "fifth": 5,
    "sixth": 6, "seventh": 7, "eighth": 8, "ninth": 9, "tenth": 10,
}


# ============================================================
# PATH / ENVIRONMENT
# ============================================================

GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "").strip()
GEMINI_MODEL = os.getenv(
    "GEMINI_MODEL",
    "gemini-3.5-flash"
).strip()

if genai is not None and GEMINI_API_KEY:
    try:
        gemini_client = genai.Client(api_key=GEMINI_API_KEY)
    except Exception:
        gemini_client = None
else:
    gemini_client = None
# ============================================================
# APP SETTINGS
# ============================================================

APP_NAME = "JARVIS AI"

BG = "#05090d"
PANEL = "#081116"
PANEL2 = "#0b151b"
CYAN = "#12b3e4"
CYAN2 = "#008fb3"
TEXT = "#d8faff"
MUTED = "#63858f"
GREEN = "#00ffb3"
RED = "#ff4d6d"
YELLOW = "#ffe66d"
GRID = "#10343c"
THREAT = "#ff5f7a"
AUX = "#7ef9ff"

# Distinct British butler-style voice profile. This is not an imitation or clone
# of any actor or copyrighted character performance.
VOICE_NAME = "en-GB-RyanNeural"
VOICE_FALLBACK_NAME = "en-GB-ThomasNeural"
VOICE_LANGUAGE = "en-GB"
VOICE_RATE = "+6%"
VOICE_PITCH = "-10Hz"
VOICE_VOLUME = "+20%"
CINEMATIC_AUDIO_FILTER = os.getenv(
    "REXA_CINEMATIC_AUDIO_FILTER", "false"
).strip().lower() in {"1", "true", "yes", "on"}
MIC_DEVICE_INDEX = None
TTS_CACHE_DIR = BASE_DIR / ".rexa_tts_cache"
WHISPER_MODEL_NAME = os.getenv("REXA_WHISPER_MODEL", "small").strip()
_local_whisper_model = None
_silero_vad_model = None

# Selenium otherwise starts Chrome with a temporary profile on every run.
# Keep one private profile for REXA so a social-media sign-in survives an app
# restart.  It is deliberately separate from the user's everyday Chrome
# profile, which avoids corrupting or locking their normal browser session.
REXA_BROWSER_PROFILE_DIR = Path(
    os.getenv("REXA_BROWSER_PROFILE_DIR", str(BASE_DIR / ".rexa_browser_profile"))
).resolve()
REXA_BROWSER_PROFILE_NAME = os.getenv("REXA_BROWSER_PROFILE_NAME", "Default").strip() or "Default"

state = {
    "mode": "SYSTEM READY",
    "voice": True,
    "speaking": False,
    "message_count": 0,
    "online": False,
    "last_command": None,
    "hud_phase": 0.0,
    "assistant_reply_count": 0,
    "conversation_mode": memory.get("conversation_mode", "normal"),
    "language_mode": memory.get("language_mode", "bengali"),
    "status_animation_token": 0,
    "awaiting_youtube_search": False,
    "awaiting_youtube_playlist": False,
    "wake_word_enabled": True,
    "boss_mode": False,
    "wake_word_listener_running": False,
    "last_active_app": "",
    "last_active_page": "",
    "active_social_inbox": "",
}

gemini_history = []
GEMINI_HISTORY_LIMIT = 12

DEFAULT_WAKE_WORDS = ("misa", "hey misa", "jarvis", "hey jarvis")


def confirm_destructive_action(action_name, description):
    """Central confirmation gate for potentially destructive commands."""
    try:
        if not messagebox.askyesno(action_name, f"{description}\n\nDo you want to continue?"):
            log_message("REXA", f"Cancelled: {description}")
            return False
        return True
    except Exception:
        log_message("REXA", f"Confirmation required before {action_name.lower()}.")
        return False


def get_active_window_context():
    """Return a compact description of the current active app/page.
    This is used for a JARVIS-style awareness layer without changing the original command system.
    """
    app_name = ""
    try:
        active = gw.getActiveWindow()
        if active is not None:
            app_name = (active.title or "").strip()
    except Exception:
        app_name = ""

    page_label = ""
    try:
        if yt_driver is not None:
            url = getattr(yt_driver, "current_url", "") or ""
            title = getattr(yt_driver, "title", "") or ""
            if url:
                page_label = f"{title} — {url}"
    except Exception:
        page_label = ""

    state["last_active_app"] = app_name
    state["last_active_page"] = page_label

    if page_label:
        return f"App: {app_name or 'Unknown'} | Page: {page_label}"
    if app_name:
        return f"App: {app_name}"
    return "App: unknown"


def safe_execute_command(command_text):
    """Wrap command execution in a crash-proof guard so failed commands never take down the UI."""
    text = (command_text or "").strip()
    if not text:
        return False

    try:
        if not handle_special_command(text):
            run_ai(text)
        return True
    except Exception as exc:
        log_message("REXA", f"Command failed safely: {exc}")
        try:
            set_mode("ERROR")
            speak("The command failed safely. Please try again.")
            root.after(1500, lambda: set_mode("SYSTEM READY"))
        except Exception:
            pass
        return False


def listen_for_wake_word_once(timeout=5):
    """Listen briefly for a wake word like 'MISA' or 'Hey MISA' and return the detected phrase if found."""
    if sr is None:
        return ""

    try:
        recognizer = sr.Recognizer()
        recognizer.dynamic_energy_threshold = False
        recognizer.energy_threshold = 350
        recognizer.pause_threshold = 0.8
        with sr.Microphone(device_index=MIC_DEVICE_INDEX) as source:
            recognizer.adjust_for_ambient_noise(source, duration=0.5)
            audio = recognizer.listen(source, timeout=timeout, phrase_time_limit=5)
        try:
            text = recognizer.recognize_google(audio, language="en-US")
        except Exception:
            return ""
        text = (text or "").strip().lower()
        if not text:
            return ""
        for wake in DEFAULT_WAKE_WORDS:
            if wake in text:
                return wake
        return ""
    except Exception:
        return ""


def start_wake_word_listener():
    """Background thread that waits for the wake word and then triggers a single command cycle."""
    if sr is None:
        log_message("REXA", "Wake word mode requires SpeechRecognition and PyAudio.")
        return

    if state.get("wake_word_listener_running"):
        return

    state["wake_word_listener_running"] = True
    log_message("REXA", "Wake-word mode active. Say 'Hey MISA' to begin.")

    def worker():
        try:
            while state.get("wake_word_listener_running"):
                wake = listen_for_wake_word_once(timeout=6)
                if not wake:
                    continue
                if not state.get("voice"):
                    continue
                set_mode("LISTENING")
                play_sfx("listen_on")
                log_message("REXA", "Wake word detected. Listening for your command.")
                speak("Listening.")
                command_text = recognize_voice_once()
                if command_text:
                    safe_execute_command(command_text)
                set_mode("SYSTEM READY")
        except Exception as exc:
            log_message("REXA", f"Wake-word listener stopped: {exc}")
        finally:
            state["wake_word_listener_running"] = False
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def stop_wake_word_listener():
    state["wake_word_listener_running"] = False
    log_message("REXA", "Wake-word listener stopped.")


def show_active_context():
    log_message("REXA", get_active_window_context())


def announce_active_context():
    """Give a short, direct description of the user's current activity."""
    try:
        get_active_window_context()
        app_name = state.get("last_active_app", "").strip()
        title = app_name.casefold()
        if "youtube" in title:
            activity = "You are currently watching YouTube in Google Chrome."
        elif "tiktok" in title:
            activity = "You are currently using TikTok in Google Chrome."
        elif "visual studio code" in title or "vs code" in title:
            activity = "You are currently working in Visual Studio Code."
        elif "chrome" in title:
            activity = "You are currently browsing in Google Chrome."
        elif app_name:
            activity = f"You are currently using {app_name}."
        else:
            activity = "I cannot identify the active window right now."

        if state.get("language_mode") == "bengali":
            translations = {
                "You are currently watching YouTube in Google Chrome.": "স্যার, আপনি এখন Google Chrome-এ YouTube দেখছেন।",
                "You are currently using TikTok in Google Chrome.": "স্যার, আপনি এখন Google Chrome-এ TikTok ব্যবহার করছেন।",
                "You are currently working in Visual Studio Code.": "স্যার, আপনি এখন Visual Studio Code-এ কাজ করছেন।",
                "You are currently browsing in Google Chrome.": "স্যার, আপনি এখন Google Chrome-এ ব্রাউজ করছেন।",
                "I cannot identify the active window right now.": "স্যার, বর্তমানে কোন active window ব্যবহার করছেন তা শনাক্ত করা যাচ্ছে না।",
            }
            message = translations.get(activity, f"স্যার, আপনি এখন {app_name} ব্যবহার করছেন।")
        else:
            message = activity

        log_message("REXA", message)
        speak(message)
    except Exception as exc:
        log_message("REXA", f"Active context announcement failed safely: {exc}")


# Safety hardening for command execution and destructive actions
# This keeps the original command parser intact while preventing crashes.

ui_queue = queue.Queue()
voice_lock = threading.Lock()

voice_recognition_running = False
voice_recognition_thread = None
voice_recognition_stop = threading.Event()
speech_interrupt = threading.Event()
barge_in_stop = threading.Event()
sentinel_stop = threading.Event()
sentinel_alerts = {}
observer_stop = threading.Event()
observer_alerts = {}
work_started_at = time.monotonic()
last_activity_at = time.monotonic()
reels_swipe_stop = threading.Event()
youtube_state = {
    "context": None,
    "last_search": "",
    "playlist_url": "",
    "current_video": None
}

# ============================================================
# TKINTER
# ============================================================
def minimize_window():
    try:
        root.iconify()
        return True
    except Exception as e:
        print("Minimize error:", e)
        return False


def minimize_chrome():
    """Minimize the visible Chrome window without minimizing MISA."""
    try:
        chrome_windows = [
            window for window in gw.getAllWindows()
            if "chrome" in (window.title or "").lower()
        ]
        if not chrome_windows:
            log_message("REXA", "I could not find an open Chrome window.")
            speak("I could not find an open Chrome window.")
            return False

        chrome_windows[0].minimize()
        log_message("REXA", "Chrome minimized.")
        speak("Chrome minimized.")
        return True
    except Exception as e:
        log_message("REXA", f"Chrome minimize error: {e}")
        return False


def minimize_vscode():
    """Minimize only the visible Visual Studio Code window."""
    try:
        vscode_windows = [
            window for window in gw.getAllWindows()
            if "visual studio code" in (window.title or "").lower()
            or (window.title or "").lower().endswith(" - code")
        ]
        if not vscode_windows:
            log_message("REXA", "I could not find an open Visual Studio Code window.")
            speak("I could not find an open Visual Studio Code window.")
            return False
        vscode_windows[0].minimize()
        log_message("REXA", "Visual Studio Code minimized.")
        speak("Visual Studio Code minimized.")
        return True
    except Exception as exc:
        log_message("REXA", f"VS Code minimize error: {exc}")
        return False


def maximize_active_window():
    """Maximize the currently focused application window without closing it."""
    try:
        window = gw.getActiveWindow()
        if window is None or not window.title:
            log_message("REXA", "I could not identify the active application window.")
            speak("I could not identify the active application window.")
            return False
        title = window.title
        window.maximize()
        log_message("REXA", f"Maximized: {title}")
        speak("The active window is now full screen.")
        return True
    except Exception as exc:
        log_message("REXA", f"Fullscreen error: {exc}")
        speak("I could not make the active window full screen.")
        return False


root = tk.Tk()
root.title(APP_NAME)
root.geometry("1450x950")
root.attributes("-fullscreen", True)
root.bind("<Escape>", lambda event: (root.attributes("-fullscreen", False), stop_speaking()))
root.configure(bg=BG)

root.grid_rowconfigure(2, weight=1)
root.grid_columnconfigure(0, weight=1)

mode_var = tk.StringVar(value="SYSTEM READY")
time_var = tk.StringVar()
date_var = tk.StringVar()
msg_var = tk.StringVar(value="MESSAGES 000")
cpu_var = tk.StringVar(value="CPU        --")
ram_var = tk.StringVar(value="RAM        --")
disk_var = tk.StringVar(value="DISK       --")
battery_var = tk.StringVar(value="BATTERY    --")
network_var = tk.StringVar(value="NETWORK    CHECKING")
voice_var = tk.StringVar(value="VOICE      ON")
status_var = tk.StringVar(value="SYSTEM READY")
status_indicator_var = tk.StringVar(value="● ONLINE")
input_var = tk.StringVar()

placeholder_active = True
PLACEHOLDER = "Type your command..."


# ============================================================
# UI HELPERS
# ============================================================

def ui_log(sender, text):
    ui_queue.put(("message", sender, str(text)))


def process_ui_queue():
    try:
        while True:
            item = ui_queue.get_nowait()

            if item[0] == "message":
                write_chat_message(item[1], item[2])

    except queue.Empty:
        pass

    try:
        root.after(50, process_ui_queue)
    except tk.TclError:
        pass


def now_text():
    return dt.datetime.now().strftime("%I:%M:%S %p")


def date_text():
    return dt.datetime.now().strftime("%d %b %Y")


def set_mode(text):
    text = str(text).upper()
    state["mode"] = text
    display_status = "ONLINE" if text == "SYSTEM READY" else text
    state["status_animation_token"] += 1
    token = state["status_animation_token"]

    try:
        root.after(
            0,
            lambda: (
                mode_var.set(text),
                status_var.set(text),
                status_indicator_var.set(
                    "● " + display_status
                )
            )
        )
        root.after(0, lambda: update_floating_status_pill(text))
        if display_status in {"THINKING", "LISTENING", "SPEAKING", "EXECUTING"}:
            _animate_status(display_status, token)
        animate_hud_glow()
    except Exception:
        pass


def create_floating_status_pill():
    """Create a compact status indicator without covering or stealing browser input."""
    global floating_pill, floating_pill_label
    try:
        floating_pill = tk.Toplevel(root)
        floating_pill.overrideredirect(True)
        # Do not keep this window above Chrome.  A topmost overlay can cover the
        # browser and make normal typing feel like it is being interrupted.
        floating_pill.attributes("-topmost", False)
        floating_pill.configure(bg="#11161c")
        floating_pill.attributes("-alpha", 0.94)
        width, height = 148, 38
        x = root.winfo_screenwidth() - width - 18
        y = (root.winfo_screenheight() - height) // 2
        floating_pill.geometry(f"{width}x{height}+{x}+{y}")
        floating_pill_label = tk.Label(
            floating_pill,
            text="●  REXA  •  READY",
            bg="#11161c",
            fg=GREEN,
            font=("Consolas", 9, "bold"),
            padx=10,
            pady=8,
        )
        floating_pill_label.pack(fill="both", expand=True)
        floating_pill.lift()

    except tk.TclError:
        floating_pill = None
        floating_pill_label = None


def update_floating_status_pill(text):
    try:
        if floating_pill_label.winfo_exists():
            mode = str(text).upper()
            colors = {
                "LISTENING": GREEN,
                "SPEAKING": AUX,
                "THINKING": "#64d9ff",
                "EXECUTING": THREAT,
                "ERROR": RED,
            }
            color = colors.get(mode, GREEN)
            floating_pill_label.configure(text=f"●  REXA  •  {mode}", fg=color)
    except (tk.TclError, AttributeError):
        pass


def animate_hud_glow():
    try:
        current_mode = str(state.get("mode", "SYSTEM READY")).upper()
        color_map = {
            "SYSTEM READY": CYAN,
            "LISTENING": GREEN,
            "SPEAKING": AUX,
            "THINKING": "#64d9ff",
            "EXECUTING": THREAT,
            "ERROR": RED,
        }
        accent = color_map.get(current_mode, CYAN)

        if "capsule" in globals():
            capsule.configure(highlightbackground=accent, highlightcolor=accent, highlightthickness=2)
            capsule.configure(bg=PANEL2)

        if "status_line" in globals() and status_line is not None:
            status_line.configure(bg=accent)

        if "input_border" in globals() and input_border is not None:
            input_border.configure(bg=accent)

        if "radar" in globals() and radar is not None:
            radar.configure(highlightbackground=accent, highlightthickness=1)

        if "root" in globals() and root is not None:
            try:
                root.configure(bg=BG)
            except Exception:
                pass
    except Exception:
        pass


def _animate_status(status, token, frame=0):
    if token != state.get("status_animation_token"):
        return

    dots = ("", ".", "..", "...")
    waves = ("▁▃▅▇", "▂▄▆█", "▃▅▇▅", "▄▆█▆")
    if status == "THINKING":
        indicator = "● THINKING" + dots[frame % len(dots)]
    elif status == "LISTENING":
        indicator = "● LISTENING " + waves[frame % len(waves)]
    elif status == "SPEAKING":
        indicator = "● SPEAKING " + waves[frame % len(waves)]
    else:
        indicator = "● EXECUTING" + dots[frame % len(dots)]

    try:
        status_indicator_var.set(indicator)
        root.after(180, lambda: _animate_status(status, token, frame + 1))
    except tk.TclError:
        pass


def write_chat_message(sender, text):
    state["message_count"] += 1

    try:
        chat_text.config(state="normal")

        tag = "rexa" if sender.upper() in {"REXA", "JARVIS"} else "you"
        label = "JARVIS" if sender.upper() in {"REXA", "JARVIS"} else "YOU"

        chat_text.insert("end", f"{label}  ", tag)
        chat_text.insert("end", str(text) + "\n\n", "body")

        chat_text.see("end")
        chat_text.config(state="disabled")

        msg_var.set(
            f"MESSAGES {state['message_count']:03d}"
        )

    except tk.TclError:
        pass


def log_message(sender, text):
    # Keep older command handlers compatible while presenting the new name.
    visible_sender = "REXA" if str(sender).upper() == "REXA" else sender
    visible_text = str(text)
    ui_log(visible_sender, visible_text)


def clear_chat():
    state["message_count"] = 0

    try:
        chat_text.config(state="normal")
        chat_text.delete("1.0", "end")
        chat_text.config(state="disabled")
        msg_var.set("MESSAGES 000")
    except tk.TclError:
        pass


# ============================================================
# BROWSER
# ============================================================

def safe_open(url):
    try:
        if not webbrowser.open(url, new=2):
            raise RuntimeError("Browser did not accept URL")

        record_web_activity(url, "", "opened")
        return True

    except Exception as e:
        log_message("REXA", f"Browser error: {e}")
        return False


# ============================================================
# HUD SOUND EFFECTS (synthesized — no external files, no copyright issue)
# ============================================================
try:
    import numpy as np
except ImportError:
    np = None

_sfx_cache = {}

def ensure_audio_mixer():
    if pygame is None:
        return False

    try:
        if not pygame.get_init():
            pygame.init()
        if not pygame.mixer.get_init():
            pygame.mixer.init(
                frequency=44100,
                size=-16,
                channels=2,
                buffer=512
            )
        return True
    except Exception as e:
        log_message("REXA", f"Audio device error: {e}")
        return False


def _load_sfx(name: str):
    if name in _sfx_cache:
        return _sfx_cache[name]
    path = BASE_DIR / "sounds" / f"{name}.mp3"
    if not path.exists():
        _sfx_cache[name] = None
        return None
    try:
        if not ensure_audio_mixer():
            _sfx_cache[name] = None
            return None
        sound = pygame.mixer.Sound(str(path))
        _sfx_cache[name] = sound
        return sound
    except Exception as e:
        print(f"[REXA Sound] Could not load '{name}.mp3': {e}")
        _sfx_cache[name] = None
        return None

def play_sfx(name: str):
    def worker():
        sound = _load_sfx(name)
        if sound is not None:
            try:
                sound.play()
            except Exception:
                pass
    threading.Thread(target=worker, daemon=True).start()
  
# ============================================================
# ENGLISH VOICE (TTS)
# ============================================================

def speak(text, voice_name=None):
    if not state["voice"] or not text:
        return

    if edge_tts is None or pygame is None:
        log_message(
            "REXA",
            "To use voice, install:\n"
            "pip install edge-tts pygame"
        )
        return

    def worker():
        with voice_lock:
            generated_path = None

            try:
                speech_interrupt.clear()
                state["speaking"] = True
                set_mode("SPEAKING")

                selected_voice = voice_name or (
                    "bn-BD-NabanitaNeural"
                    if state.get("language_mode") == "bengali"
                    else VOICE_NAME
                )
                cache_key = hashlib.sha256(
                    f"{selected_voice}|{VOICE_RATE}|{VOICE_PITCH}|{VOICE_VOLUME}|{text}".encode("utf-8")
                ).hexdigest()
                cached_path = TTS_CACHE_DIR / f"{cache_key}.mp3"
                audio_path = cached_path

                if not cached_path.exists():
                    TTS_CACHE_DIR.mkdir(parents=True, exist_ok=True)
                    fd, generated_path = tempfile.mkstemp(
                        prefix="rexa_voice_",
                        suffix=".mp3",
                        dir=str(TTS_CACHE_DIR)
                    )
                    os.close(fd)

                    async def make_audio():
                        voices = [selected_voice]
                        if selected_voice == VOICE_NAME:
                            voices.append(VOICE_FALLBACK_NAME)
                        last_error = None
                        for candidate in voices:
                            try:
                                communicate = edge_tts.Communicate(
                                    text,
                                    candidate,
                                    rate=VOICE_RATE,
                                    pitch=VOICE_PITCH,
                                    volume=VOICE_VOLUME
                                )
                                await communicate.save(generated_path)
                                return
                            except Exception as exc:
                                last_error = exc
                        raise RuntimeError(
                            f"Edge-TTS voice generation failed: {last_error}"
                        )

                    asyncio.run(make_audio())
                    os.replace(generated_path, cached_path)
                    generated_path = None

                if not ensure_audio_mixer():
                    return

                audio_path = _apply_cinematic_audio_filter(audio_path)
                pygame.mixer.music.stop()
                pygame.mixer.music.load(str(audio_path))
                pygame.mixer.music.set_volume(1.0)
                pygame.mixer.music.play()
                _start_barge_in_monitor()

                # Slightly more responsive for a faster, more energetic assistant feel.
                time.sleep(0.08)

                while pygame.mixer.music.get_busy() and not speech_interrupt.is_set():
                    time.sleep(0.05)

                pygame.mixer.music.stop()

            except Exception as e:
                log_message("REXA", f"Voice error: {e}")

            finally:
                barge_in_stop.set()
                state["speaking"] = False
                set_mode("SYSTEM READY")

                if generated_path:
                    for _ in range(30):
                        try:
                            if os.path.exists(generated_path):
                                os.remove(generated_path)
                            break
                        except PermissionError:
                            time.sleep(0.1)

    threading.Thread(target=worker, daemon=True).start()


def speak_streaming_sentences(text):
    """Queue short sentences so TTS starts before the whole reply is spoken."""
    sentences = [part.strip() for part in re.split(r"(?<=[.!?।])\s+", text or "") if part.strip()]
    if not sentences:
        return

    def worker():
        for sentence in sentences:
            if speech_interrupt.is_set():
                return
            speak(sentence)
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline and not state.get("speaking"):
                time.sleep(0.01)
            while state.get("speaking") and not speech_interrupt.is_set():
                time.sleep(0.03)

    threading.Thread(target=worker, name="REXA-Sentence-TTS", daemon=True).start()


def _start_barge_in_monitor():
    if sr is None or voice_recognition_running:
        return
    barge_in_stop.clear()

    def monitor():
        try:
            recognizer = sr.Recognizer()
            recognizer.dynamic_energy_threshold = False
            recognizer.energy_threshold = 450
            with sr.Microphone(device_index=MIC_DEVICE_INDEX) as source:
                while state.get("speaking") and not barge_in_stop.is_set():
                    try:
                        audio = recognizer.listen(source, timeout=0.35, phrase_time_limit=2)
                        if barge_in_stop.is_set():
                            return
                        heard = recognizer.recognize_google(audio, language="en-US").strip()
                        if heard:
                            stop_speaking()
                            log_message("YOU", f"Barge-in: {heard}")
                            execute_command(heard)
                            return
                    except sr.WaitTimeoutError:
                        continue
                    except (sr.UnknownValueError, sr.RequestError):
                        continue
        except Exception:
            return

    threading.Thread(target=monitor, name="JARVIS-BargeIn", daemon=True).start()


def stop_speaking():
    """Stop current TTS playback immediately and return the HUD to listening."""
    speech_interrupt.set()
    barge_in_stop.set()
    try:
        if pygame is not None and pygame.mixer.get_init():
            pygame.mixer.music.stop()
    except Exception:
        pass
    state["speaking"] = False
    set_mode("LISTENING")


def prepare_voice_listening(focus_ui=False):
    """Prepare voice capture without sending keys to the user's active app."""
    # Voice chat may be started while Chrome is active.  Sending Escape to the
    # global foreground window exits browser fullscreen and disrupts text input.
    if focus_ui and pyautogui is not None:
        previous_failsafe = pyautogui.FAILSAFE
        try:
            pyautogui.FAILSAFE = False
            for key in ("win", "ctrl", "alt", "shift"):
                pyautogui.keyUp(key)
            pyautogui.press("esc")
        except Exception as exc:
            log_message("REXA", f"[WARNING] Could not reset keyboard focus: {exc}")
        finally:
            pyautogui.FAILSAFE = previous_failsafe

    if focus_ui:
        try:
            root.after(0, root.lift)
            root.after(0, root.focus_force)
        except tk.TclError:
            pass


def _apply_cinematic_audio_filter(audio_path):
    """Optionally add a subtle presence band and 10 ms room reflection."""
    if not CINEMATIC_AUDIO_FILTER or AudioSegment is None:
        return audio_path
    try:
        source = Path(audio_path)
        filtered = source.with_name(source.stem + "_cinematic.mp3")
        if filtered.exists():
            return filtered
        audio = AudioSegment.from_file(str(source))
        presence = audio.high_pass_filter(2500).low_pass_filter(4000).apply_gain(1.5)
        enhanced = audio.overlay(presence)
        reflection = enhanced - 18
        enhanced = enhanced.overlay(reflection, position=10)
        enhanced.export(str(filtered), format="mp3", bitrate="192k")
        return filtered
    except Exception as exc:
        log_message("REXA", f"Optional cinematic audio filter disabled for this clip: {exc}")
        return audio_path


def _sentinel_alert(key, message):
    now = time.monotonic()
    if now - sentinel_alerts.get(key, 0) < 900:
        return
    sentinel_alerts[key] = now
    log_message("REXA", "[ALERT] " + message)
    speak(message)


def _observer_alert(key, message, cooldown=1800):
    """Announce observer events with a cooldown so window switching stays quiet."""
    try:
        now = time.monotonic()
        if now - observer_alerts.get(key, 0) < cooldown:
            return
        observer_alerts[key] = now
        log_message("REXA", "[SUGGESTION] " + message)
        speak(message)
    except Exception as exc:
        log_message("REXA", f"Observer alert failed safely: {exc}")


def _active_window_title():
    try:
        active = gw.getActiveWindow()
        return (getattr(active, "title", "") or "").strip()
    except Exception as exc:
        _monitor_notice(f"Active-window observer unavailable: {exc}")
        return ""


def _study_window_kind(title):
    """Classify only visible window titles; no keystrokes or screen contents are read."""
    low = title.casefold()
    categories = {
        "coding": (
            "visual studio code", "vs code", "pycharm", "idle", "notepad++",
            "sublime", "jupyter", "code -",
        ),
        "quiz": (
            "quiz", "kahoot", "quizizz", "leetcode", "hackerrank",
            "exam", "assessment",
        ),
        "study": (
            "coursera", "udemy", "edx", "classroom", "study", "lecture",
            "wikipedia", "tutorial", "documentation", "docs", "document",
            "microsoft word", "excel", "powerpoint", "acrobat", ".pdf",
        ),
    }
    for kind, markers in categories.items():
        if any(marker in low for marker in markers):
            return kind
    return ""


def background_observer_loop():
    """Watch active window titles and hardware metrics without blocking the Tk UI."""
    previous_title = ""
    while not observer_stop.wait(5):
        try:
            title = _active_window_title()
            if title and title != previous_title:
                previous_title = title
                kind = _study_window_kind(title)
                if kind:
                    _observer_alert(
                        f"window-{kind}",
                        "What are you doing, Sir? Can I help you, Sir? "
                        "Do you need some information about this?",
                    )
        except Exception as exc:
            log_message("REXA", f"Background observer failed safely: {exc}")


def start_background_observer():
    try:
        if any(thread.name == "JARVIS-Observer" and thread.is_alive()
               for thread in threading.enumerate()):
            return
        observer_stop.clear()
        threading.Thread(
            target=background_observer_loop,
            name="JARVIS-Observer",
            daemon=True,
        ).start()
    except Exception as exc:
        log_message("REXA", f"Could not start background observer safely: {exc}")


def verify_user_input(submitted, expected):
    """Compare an explicitly supplied answer/code with its expected value."""
    try:
        submitted = (submitted or "").strip()
        expected = (expected or "").strip()
        if not submitted or not expected:
            log_message("REXA", "Use: verify answer <submitted> | <right answer>")
            return
        if submitted.casefold() == expected.casefold():
            message = "Sir, you have done it easily!"
        else:
            message = f"Sir, you have submitted an incorrect answer. The right information is ({expected})"
        log_message("REXA", message)
        speak(message)
    except Exception as exc:
        log_message("REXA", f"Input verification failed safely: {exc}")


def _sentinel_metrics():
    metrics = {"battery": None, "cpu": None, "temperature": None}
    if psutil:
        try:
            metrics["cpu"] = psutil.cpu_percent(interval=0.2)
            battery = psutil.sensors_battery()
            metrics["battery"] = battery.percent if battery else None
        except Exception:
            pass
    if nvmlInit is not None:
        try:
            nvmlInit()
            temperatures = [
                nvmlDeviceGetTemperature(nvmlDeviceGetHandleByIndex(i), NVML_TEMPERATURE_GPU)
                for i in range(nvmlDeviceGetCount())
            ]
            metrics["temperature"] = max(temperatures) if temperatures else None
        except Exception:
            pass
        finally:
            try:
                nvmlShutdown()
            except Exception:
                pass
    return metrics


def _overdue_reminders():
    if not REMINDERS_FILE.exists():
        return 0
    try:
        now = dt.datetime.now()
        overdue = 0
        for line in REMINDERS_FILE.read_text(encoding="utf-8").splitlines():
            match = re.match(r"\[(\d{4}-\d{2}-\d{2} \d{2}:\d{2})\]", line)
            if match and dt.datetime.strptime(match.group(1), "%Y-%m-%d %H:%M") <= now:
                overdue += 1
        return overdue
    except Exception:
        return 0


def proactive_sentinel_loop():
    """Monitor safe read-only metrics and announce each alert at most once/15m."""
    while not sentinel_stop.wait(45):
        try:
            metrics = _sentinel_metrics()
            if metrics["battery"] is not None and metrics["battery"] < 20:
                _sentinel_alert("battery", "Sir, battery is low. Please plug in the charger.")
            if metrics["cpu"] is not None and metrics["cpu"] > 85:
                _sentinel_alert("cpu", "Sir, CPU load is running high. I am optimizing background processes.")
            if metrics["temperature"] is not None and metrics["temperature"] > 85:
                _sentinel_alert("temperature", f"GPU temperature is high at {metrics['temperature']} degrees Celsius.")
            if time.monotonic() - work_started_at >= 7200:
                _sentinel_alert("work_break", "Sir, you have been working continuously for two hours. Consider taking a short break.")
            if _overdue_reminders():
                _sentinel_alert("overdue", "You have overdue reminders. Say show my reminders to review them.")
        except Exception as exc:
            log_message("REXA", f"Sentinel check failed safely: {exc}")


def start_proactive_sentinel():
    if any(thread.name == "JARVIS-Sentinel" and thread.is_alive() for thread in threading.enumerate()):
        return
    sentinel_stop.clear()
    threading.Thread(target=proactive_sentinel_loop, name="JARVIS-Sentinel", daemon=True).start()


# ============================================================
# YOUTUBE  (expanded controls)
# ============================================================
# NOTE: These use YouTube's own keyboard shortcuts, so the
# YouTube tab/player must be the focused (active) window for
# them to work: k/space=play-pause, 0=restart, j/l=seek,
# shift+n/shift+p=next/prev (playlist), m=mute, f=fullscreen,
# up/down=volume, ctrl+w=close tab.

def _youtube_key_action(mode_label, key_fn, success_msg, error_prefix, delay=0.3):
    if pyautogui is None:
        log_message(
            "REXA",
            "For YouTube control, install:\n"
            "pip install pyautogui"
        )
        return

    def worker():
        try:
            set_mode(mode_label)
            browser_windows = [
                window for window in gw.getAllWindows()
                if any(name in (window.title or "").lower() for name in ("youtube", "chrome"))
            ]
            if browser_windows:
                browser_windows[0].restore()
                browser_windows[0].activate()
                time.sleep(0.2)
            time.sleep(delay)
            key_fn()
            log_message("REXA", success_msg)
        except Exception as e:
            log_message("REXA", f"{error_prefix}: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def _focus_chrome_for_youtube():
    """Bring a visible Chrome/YouTube window to the foreground.

    pygetwindow can report Windows error code 0 from ``activate`` even though
    the foreground request succeeded, so that specific condition is treated
    as success rather than as a failed navigation.
    """
    windows = [
        window for window in gw.getAllWindows()
        if any(
            marker in (window.title or "").casefold()
            for marker in ("youtube", "google chrome", "chrome")
        )
    ]
    if not windows:
        raise RuntimeError("No visible Google Chrome or YouTube window was found")

    window = windows[0]
    try:
        if getattr(window, "isMinimized", False):
            window.restore()
        window.activate()
    except Exception as exc:
        if "error code from windows: 0" not in str(exc).casefold():
            raise
    time.sleep(0.2)
    return window


def _send_media_next_track():
    """Best-effort Windows media-next signal; return False on an actual failure."""
    try:
        import ctypes

        user32 = ctypes.windll.user32
        user32.keybd_event(0xB0, 0, 0, 0)  # VK_MEDIA_NEXT_TRACK
        user32.keybd_event(0xB0, 0, 0x0002, 0)  # KEYEVENTF_KEYUP
        return True
    except Exception:
        return False


def youtube_open():
    if selenium_available:
        open_youtube()
        return

    if safe_open("https://www.youtube.com/"):
        log_message("REXA", "Opened YouTube. Selenium control is unavailable.")
        speak("Opening YouTube. Browser controls are unavailable.")



def youtube_close():
    _youtube_key_action(
        "CLOSE",
        lambda: pyautogui.hotkey("ctrl", "w"),
        "Closed the YouTube tab.",
        "YouTube close error"
    )


def youtube_replay():
    _youtube_key_action(
        "REPLAY",
        lambda: pyautogui.press("0"),
        "Restarted the YouTube video.",
        "YouTube replay error"
    )
    speak("Restarting the YouTube video.")


def youtube_pause_play():
    _youtube_key_action(
        "PLAY / PAUSE",
        lambda: pyautogui.press("k"),
        "Sent the play/pause command to YouTube.",
        "YouTube play/pause error",
        delay=0.25
    )


def youtube_next():
    if pyautogui is None:
        log_message(
            "REXA",
            "For YouTube control, install:\n"
            "pip install pyautogui"
        )
        return

    def worker():
        try:
            set_mode("NEXT")

            # YouTube's playlist shortcut is more deterministic than a global
            # media key, so focus Chrome before sending Shift+N.
            _focus_chrome_for_youtube()
            pyautogui.hotkey("shift", "n")
            log_message("REXA", "Played the next video.")
        except Exception as exc:
            # Keep a global media-key fallback for environments where
            # pyautogui cannot send the shortcut to the focused window.
            if _send_media_next_track():
                log_message("REXA", "Played the next video using the media-key fallback.")
            else:
                log_message("REXA", f"YouTube next error: {exc}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, name="JARVIS-YouTubeNext", daemon=True).start()


def youtube_previous():
    _youtube_key_action(
        "PREVIOUS",
        lambda: pyautogui.hotkey("shift", "p"),
        "Played the previous video.",
        "YouTube previous error"
    )


def youtube_forward():
    _youtube_key_action(
        "FORWARD",
        lambda: pyautogui.press("l"),
        "Skipped forward 10 seconds.",
        "YouTube forward error",
        delay=0.2
    )


def youtube_backward():
    _youtube_key_action(
        "BACKWARD",
        lambda: pyautogui.press("j"),
        "Skipped back 10 seconds.",
        "YouTube backward error",
        delay=0.2
    )


def youtube_mute_toggle():
    _youtube_key_action(
        "MUTE",
        lambda: pyautogui.press("m"),
        "Toggled mute/unmute.",
        "YouTube mute error",
        delay=0.2
    )


def youtube_fullscreen():
    visible_windows = [
        window for window in gw.getAllWindows()
        if "youtube" in (window.title or "").lower()
    ]
    if visible_windows and pyautogui is not None:
        def focus_video_and_fullscreen():
            try:
                youtube_window = visible_windows[0]
                youtube_window.activate()
                time.sleep(0.25)
                pyautogui.click(
                    youtube_window.left + int(youtube_window.width * 0.5),
                    youtube_window.top + int(youtube_window.height * 0.48)
                )
                pyautogui.press("f")
                log_message("REXA", "YouTube video fullscreen is on.")
                speak("YouTube video fullscreen is on.")
            except Exception as e:
                log_message("REXA", f"YouTube fullscreen error: {e}")

        threading.Thread(target=focus_video_and_fullscreen, daemon=True).start()
        return

    driver = yt_driver
    if driver is not None:
        def enter_fullscreen(active_driver):
            if "youtube.com" not in active_driver.current_url.lower():
                raise RuntimeError("the active page is not YouTube")
            video = active_driver.find_element(By.CSS_SELECTOR, "video")
            active_driver.execute_script(
                "arguments[0].requestFullscreen();", video
            )
            log_message("REXA", "YouTube is fullscreen, Boss.")
            speak("YouTube is fullscreen.")

        _browser_worker("FULLSCREEN", enter_fullscreen)
        return

    if pyautogui is not None:
        _youtube_key_action(
            "FULLSCREEN",
            lambda: pyautogui.press("f"),
            "Toggled fullscreen.",
            "YouTube fullscreen error",
            delay=0.2
        )
        return

    log_message("REXA", "YouTube isn't open. Should I open it?")


def youtube_volume_up():
    _youtube_key_action(
        "VOLUME UP",
        lambda: pyautogui.press("up"),
        "Turned the volume up.",
        "YouTube volume error",
        delay=0.15
    )


def youtube_volume_down():
    _youtube_key_action(
        "VOLUME DOWN",
        lambda: pyautogui.press("down"),
        "Turned the volume down.",
        "YouTube volume error",
        delay=0.15
    )


def youtube_skip_ad():
    # YouTube has no universal "skip ad" hotkey; best-effort is to
    # jump forward, which often lands past a skippable ad's timer.
    _youtube_key_action(
        "SKIP AD",
        lambda: pyautogui.press("l"),
        "Tried to skip the ad (not guaranteed — YouTube has no "
        "fixed 'skip ad' shortcut).",
        "YouTube skip ad error",
        delay=0.2
    )


def youtube_set_volume_percent(percent):
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        percent = max(0, min(100, int(percent)))
    except Exception:
        log_message("REXA", "Couldn't understand that volume percent.")
        return

    def worker():
        try:
            set_mode("YOUTUBE VOLUME")
            time.sleep(0.2)
            # Reset to 0 then step up in 10% presses (YouTube volume
            # steps ~5% per arrow press; this is an approximation).
            for _ in range(20):
                pyautogui.press("down")
            steps = round(percent / 5)
            for _ in range(steps):
                pyautogui.press("up")
            log_message("REXA", f"Set volume to about {percent}%.")
        except Exception as e:
            log_message("REXA", f"Volume set error: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def close_all_tabs():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("ctrl", "shift", "w")
        log_message(
            "REXA",
            "Sent the command to close the browser window/all tabs."
        )
    except Exception as e:
        log_message("REXA", f"Close tabs error: {e}")


def go_to_home_screen():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("win", "d")
        log_message("REXA", "Went to the desktop/home screen.")
    except Exception as e:
        log_message("REXA", f"Home screen error: {e}")


def open_wifi_settings():
    try:
        os.startfile("ms-settings:network-wifi")
        log_message(
            "REXA",
            "Opened Wi-Fi settings. Toggle it from here — for "
            "safety REXA can't turn Wi-Fi on/off by itself."
        )
    except Exception as e:
        log_message("REXA", f"Wi-Fi settings error: {e}")


def open_bluetooth_settings():
    try:
        os.startfile("ms-settings:bluetooth")
        log_message(
            "REXA",
            "Opened Bluetooth settings. Toggle it from here — for "
            "safety REXA can't turn Bluetooth on/off by itself."
        )
    except Exception as e:
        log_message("REXA", f"Bluetooth settings error: {e}")


def empty_recycle_bin():
    try:
        import ctypes
        # SHERB_NOCONFIRMATION | SHERB_NOPROGRESSUI | SHERB_NOSOUND
        ctypes.windll.shell32.SHEmptyRecycleBinW(None, None, 0x00000007)
        log_message("REXA", "Emptied the Recycle Bin. \U0001F5D1\uFE0F")
    except Exception as e:
        log_message(
            "REXA",
            f"Couldn't empty the Recycle Bin: {e}\n"
            "This only works on Windows."
        )


def open_alarm_clock():
    try:
        os.startfile("ms-clock:")
        log_message(
            "REXA",
            "Opened Windows Alarms & Clock. Set the alarm/timer time "
            "here — for accuracy REXA doesn't set the time itself."
        )
    except Exception as e:
        log_message("REXA", f"Alarm/Clock error: {e}")


def spotify_search(query):
    query = query.strip()
    if not query:
        return

    try:
        os.startfile(
            "spotify:search:" + urllib.parse.quote(query)
        )
        log_message("REXA", f"Searched Spotify for: {query}")
    except Exception:
        safe_open(
            "https://open.spotify.com/search/"
            + urllib.parse.quote(query)
        )
        log_message(
            "REXA",
            f"Searched Spotify Web for: {query}"
        )


def run_task_sequence(task_name, steps):
    """Run a bounded sequence of existing tools without blocking the UI."""
    if not steps:
        log_message("REXA", f"[ALERT] {task_name}: no steps were configured.")
        return

    def worker():
        set_mode("EXECUTING")
        total = len(steps)
        try:
            for index, (label, action) in enumerate(steps, start=1):
                log_message("REXA", f"[EXECUTING] {task_name} — [TASK {index}/{total}] {label}")
                action()
                log_message("REXA", f"[COMPLETED] {task_name} — {label}")
            speak(f"{task_name} completed, Sir.")
        except Exception as exc:
            log_message("REXA", f"[ALERT] {task_name} stopped: {exc}")
            speak(f"{task_name} could not be completed.")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(
        target=worker,
        name=f"REXA-{task_name.replace(' ', '-')}",
        daemon=True,
    ).start()


def set_volume_percent(percent):
    """Set Windows master volume using the existing keyboard media control."""
    if pyautogui is None:
        log_message("REXA", "Volume control needs: pip install pyautogui")
        return
    percent = max(0, min(100, int(percent)))
    try:
        pyautogui.press("volumemute")
        pyautogui.press("volumemute")
        pyautogui.press("volumedown", presses=50, interval=0.01)
        pyautogui.press("volumeup", presses=percent // 2, interval=0.01)
        log_message("REXA", f"Set volume to approximately {percent}%.")
    except Exception as exc:
        log_message("REXA", f"Volume error: {exc}")


def activate_workspace_preset(preset):
    """Activate a non-local-AI workspace preset using existing safe tools."""
    preset = preset.lower().strip()
    if preset == "coding":
        run_task_sequence("Coding mode", [
            ("Open VS Code workspace", open_vscode_workspace),
            ("Set volume to 40 percent", lambda: set_volume_percent(40)),
            ("Start focus music", lambda: spotify_search("focus music")),
            ("Start two-hour timer", lambda: start_countdown_timer(120)),
        ])
        return True

    if preset == "focus":
        run_task_sequence("Focus mode", [
            ("Enable Focus Assist", open_focus_assist),
            ("Set brightness to 60 percent", lambda: set_brightness(60)),
            ("Start Pomodoro timer", lambda: start_pomodoro(25)),
        ])
        return True

    if preset == "meeting":
        run_task_sequence("Meeting mode", [
            ("Open Google Calendar", open_google_calendar),
            ("Set volume to 70 percent", lambda: set_volume_percent(70)),
        ])
        return True

    if preset == "night":
        run_task_sequence("Night mode", [
            ("Open Night Light settings", open_night_light),
            ("Set brightness to 30 percent", lambda: set_brightness(30)),
            ("Set volume to 20 percent", lambda: set_volume_percent(20)),
        ])
        return True

    if preset == "gaming":
        run_task_sequence("Gaming mode", [
            ("Set volume to 80 percent", lambda: set_volume_percent(80)),
            ("Open Windows gaming settings", lambda: safe_open(
                "ms-settings:gaming-gamebar"
            )),
        ])
        return True

    return False


def run_ai(query):
    set_mode("THINKING")

    def worker():
        try:
            answer = ask_openrouter(query)
            if openrouter_client is None and gemini_client is not None:
                answer = ask_gemini(query)

            if answer.startswith(("OpenRouter error:", "Opps Boss", "Couldn't reach Gemini")):
                set_mode("ERROR")
                log_message("REXA", answer)
                speak("I couldn't complete that request. Please try again.")
                root.after(1500, lambda: set_mode("SYSTEM READY"))
                return

            _remember_vector_text(f"User: {query}\nREXA: {answer}")
            log_message("REXA", answer)
            play_sfx("done")
            speak_streaming_sentences(answer)
            if not state["voice"] or edge_tts is None or pygame is None:
                set_mode("SYSTEM READY")
        except Exception as e:
            set_mode("ERROR")
            log_message("REXA", f"I couldn't complete that request: {e}")
            speak("I couldn't complete that request. Please try again.")
            root.after(1500, lambda: set_mode("SYSTEM READY"))

    threading.Thread(target=worker, daemon=True).start()


def _redact_sensitive_text(value):
    """Prevent credentials and tokens from entering memory or repair prompts."""
    return re.sub(
        r"(?i)(api[_ -]?key|token|password|secret|private[_ -]?key)\s*[:=]\s*['\"]?[^'\"\s,;]+",
        r"\1=[REDACTED]",
        value or "",
    )


def _offer_missing_module_install(error_text):
    match = re.search(r"No module named ['\"]([^'\"]+)['\"]", error_text or "")
    if not match:
        return
    module_name = match.group(1).split(".", 1)[0]
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", module_name):
        return
    if not confirm_destructive_action(
        "Install Python Module",
        f"The sandbox needs '{module_name}'. Install it with pip?",
    ):
        return
    completed = subprocess.run(
        [sys.executable, "-m", "pip", "install", module_name],
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    if completed.returncode == 0:
        log_message("REXA", f"[COMPLETED] Installed Python module: {module_name}")
    else:
        log_message("REXA", f"[ALERT] Module install failed: {_redact_sensitive_text(completed.stderr)}")


def _validate_sandbox_code(code):
    """Reject common system, network, and file-destruction primitives before execution."""
    tree = ast.parse(code)
    blocked_modules = {
        "os", "subprocess", "socket", "ctypes", "winreg", "shutil",
        "pathlib", "requests", "urllib",
    }
    blocked_calls = {
        "eval", "exec", "compile", "__import__", "system", "popen",
        "remove", "unlink", "rmtree",
    }
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names = {alias.name.split(".", 1)[0] for alias in node.names}
            if names & blocked_modules:
                raise ValueError("Sandbox rejected a blocked module import.")
        elif isinstance(node, ast.ImportFrom):
            if (node.module or "").split(".", 1)[0] in blocked_modules:
                raise ValueError("Sandbox rejected a blocked module import.")
        elif isinstance(node, ast.Call):
            function_name = node.func.id if isinstance(node.func, ast.Name) else ""
            if function_name in blocked_calls:
                raise ValueError("Sandbox rejected a blocked system operation.")


def run_self_healing_sandbox(request):
    """Generate, execute, repair, and retry a Python script in an isolated folder."""
    request = _redact_sensitive_text(request.strip())

    def worker():
        sandbox_dir = BASE_DIR / ".rexa_sandbox"
        script_path = sandbox_dir / "generated_task.py"
        try:
            if openrouter_client is None and gemini_client is None:
                raise RuntimeError("An AI API client is required for sandbox generation.")
            sandbox_dir.mkdir(exist_ok=True)
            prompt = (
                "Generate only safe Python standard-library code for this request. "
                "Do not access credentials, delete files, change system settings, "
                "use network access, or execute shell commands. Return only code.\n"
                f"Request: {request}"
            )
            code = ask_openrouter(prompt)
            if openrouter_client is None and gemini_client is not None:
                code = ask_gemini(prompt)
            code = re.sub(r"^```(?:python)?\s*|\s*```$", "", code.strip(), flags=re.IGNORECASE)
            last_error = ""
            for attempt in range(1, 4):
                _validate_sandbox_code(code)
                script_path.write_text(code, encoding="utf-8")
                completed = subprocess.run(
                    [sys.executable, "-I", str(script_path)],
                    cwd=str(sandbox_dir),
                    capture_output=True,
                    text=True,
                    timeout=30,
                    check=False,
                )
                if completed.returncode == 0:
                    output = (completed.stdout or "").strip() or "No output."
                    log_message("REXA", f"[COMPLETED] Sandbox attempt {attempt}:\n{output[:4000]}")
                    speak("Sandbox task completed successfully.")
                    return
                last_error = _redact_sensitive_text(
                    (completed.stderr or completed.stdout or "Unknown execution error").strip()
                )
                _offer_missing_module_install(last_error)
                if attempt == 3:
                    break
                repair_prompt = (
                    "Repair this safe Python script. Return only the complete corrected code. "
                    "Keep it standard-library-only and do not add shell, network, credential, "
                    "file deletion, or system-setting operations.\n\n"
                    f"Error:\n{last_error}\n\nCode:\n{code}"
                )
                code = ask_openrouter(repair_prompt)
                if openrouter_client is None and gemini_client is not None:
                    code = ask_gemini(repair_prompt)
                code = re.sub(
                    r"^```(?:python)?\s*|\s*```$",
                    "",
                    code.strip(),
                    flags=re.IGNORECASE,
                )
            raise RuntimeError(f"Sandbox failed after 3 attempts: {last_error}")
        except subprocess.TimeoutExpired:
            log_message("REXA", "[ALERT] Sandbox stopped after the 30-second safety limit.")
        except Exception as exc:
            log_message("REXA", f"[ALERT] Sandbox error: {exc}")
        finally:
            try:
                if script_path.exists():
                    script_path.unlink()
            except OSError as exc:
                log_message("REXA", f"Sandbox cleanup warning: {exc}")
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, name="REXA-Self-Healing-Sandbox", daemon=True).start()


def generate_content_to_downloads(request, content_type):
    """Generate an application or note and save it under the user's Downloads."""
    def worker():
        try:
            set_mode("GENERATING APP" if content_type == "application" else "WRITING NOTE")
            if content_type == "application":
                prompt = (
                    "Create a complete, runnable Python application for this request:\n"
                    f"{request}\n\n"
                    "Return only the Python source code inside one ```python``` code block. "
                    "Do not include explanations, markdown outside the code block, or placeholders. "
                    "Use only the Python standard library unless a dependency is explicitly required."
                )
            else:
                prompt = (
                    "Write a useful, well-formatted note for this request:\n"
                    f"{request}\n\n"
                    "Return only the note text. Do not include commentary about writing the note."
                )
            answer = ask_openrouter(prompt)
            if openrouter_client is None and gemini_client is not None:
                answer = ask_gemini(prompt)

            if content_type == "application":
                match = re.search(
                    r"```(?:python|py)?\s*(.*?)```",
                    answer,
                    re.IGNORECASE | re.DOTALL,
                )
                if not match:
                    raise ValueError("AI did not return a Python code block")
                content = match.group(1).strip() + "\n"
                extension = "py"
                default_name = "generated_app"
            else:
                content = re.sub(r"```(?:text|markdown)?\s*|\s*```", "", answer).strip() + "\n"
                extension = "txt"
                default_name = "generated_note"

            requested_name = re.search(
                r"\b(?:called|named)\s+([A-Za-z0-9_-]+)",
                request,
                re.IGNORECASE,
            )
            file_name = requested_name.group(1) if requested_name else default_name
            file_name = re.sub(r"[^A-Za-z0-9_-]", "_", file_name).strip("_") or default_name

            output_dir = Path.home() / "Downloads" / "REXA_Generated"
            output_dir.mkdir(parents=True, exist_ok=True)
            target = output_dir / f"{file_name}.{extension}"
            target.write_text(content, encoding="utf-8")

            label = "Application" if content_type == "application" else "Note"
            log_message("REXA", f"[COMPLETED] {label} saved to:\n{target}")
            speak(f"{label} created and saved to your Downloads folder.")
            os.startfile(str(output_dir))
        except Exception as exc:
            log_message("REXA", f"[ALERT] Content generation failed: {exc}")
            speak("I could not create and save that content.")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, name="REXA-ContentGenerator", daemon=True).start()


def ask_weather():
    run_ai("What is the weather today?")


def find_youtube_url(query):
    if yt_dlp is None:
        return None

    options = {
        "quiet": True,
        "no_warnings": True,
        "skip_download": True,
        "extract_flat": True,
        "noplaylist": True,
    }

    try:
        with yt_dlp.YoutubeDL(options) as ydl:
            info = ydl.extract_info(
                f"ytsearch1:{query}",
                download=False
            )

        entries = info.get("entries") or []

        if not entries:
            return None

        item = entries[0]

        url = (
            item.get("webpage_url")
            or item.get("url")
        )

        if url and str(url).startswith("http"):
            return str(url)

        video_id = item.get("id")

        if video_id:
            return (
                "https://www.youtube.com/watch?v="
                + str(video_id)
            )

    except Exception as e:
        log_message(
            "REXA",
            f"YouTube search error: {e}"
        )

    return None


def play_youtube(query):
    query = query.strip()
    def worker():
        answer = ask_openrouter(query)
        if openrouter_client is None and gemini_client is not None:
            answer = ask_gemini(query)
        log_message("REXA", answer)
        speak(answer)

    threading.Thread(target=worker, daemon=True).start()
    # ============================================================
# YOUTUBE SELENIUM AUTOMATION
# ============================================================

def _get_yt_driver():
    """Get or create a Selenium Chrome driver. Returns driver or None."""
    global yt_driver

    if not selenium_available:
        log_message(
            "REXA",
            "Selenium is not installed.\n"
            "Run: pip install selenium webdriver-manager"
        )
        return None

    # Reuse existing driver if the window is still alive
    if yt_driver is not None:
        try:
            _ = yt_driver.window_handles  # throws if closed
            return yt_driver
        except Exception:
            try:
                yt_driver.quit()
            except Exception:
                pass
            yt_driver = None

    try:
        set_mode("STARTING BROWSER")
        log_message("REXA", "Starting browser...")

        options = webdriver.ChromeOptions()
        options.add_argument("--start-maximized")
        options.add_argument("--disable-notifications")
        options.add_argument("--disable-infobars")
        options.add_argument("--enable-gpu")
        options.add_argument("--enable-accelerated-video-decode")
        options.add_argument("--enable-features=VaapiVideoDecoder")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--disable-blink-features=AutomationControlled")
        options.add_argument(
            "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
        )
        options.add_argument("--autoplay-policy=no-user-gesture-required")
        # This makes TikTok/Facebook sign-ins persistent.  The first time a
        # social site is opened, the user signs in normally in this browser;
        # no password is read or stored by REXA itself.
        REXA_BROWSER_PROFILE_DIR.mkdir(parents=True, exist_ok=True)
        options.add_argument(f"--user-data-dir={REXA_BROWSER_PROFILE_DIR}")
        options.add_argument(f"--profile-directory={REXA_BROWSER_PROFILE_NAME}")
        # Suppress "Chrome is being controlled" banner
        options.add_experimental_option("excludeSwitches", ["enable-automation", "disable-popup-blocking"])
        options.add_experimental_option("useAutomationExtension", False)
        options.add_experimental_option("prefs", {
            "profile.default_content_setting_values.notifications": 2,
            "media_stream_mic": {"audio": 1},
        })

        # Selenium Manager matches the installed Chrome version more reliably.
        try:
            yt_driver = webdriver.Chrome(options=options)
        except Exception as manager_error:
            log_message("REXA", f"Selenium Manager failed, trying webdriver-manager: {manager_error}")
            try:
                service = ChromeService(ChromeDriverManager().install())
                yt_driver = webdriver.Chrome(service=service, options=options)
            except Exception as profile_error:
                # A previous Chrome/driver process may still hold the private
                # profile lock. Retry with an isolated profile rather than
                # leaving every YouTube command unavailable.
                log_message(
                    "REXA",
                    f"Saved Chrome profile unavailable, retrying isolated profile: {profile_error}",
                )
                isolated_profile = Path(
                    tempfile.mkdtemp(prefix="rexa-chrome-")
                ).resolve()
                options.arguments[:] = [
                    argument for argument in options.arguments
                    if not argument.startswith("--user-data-dir=")
                ]
                options.add_argument(f"--user-data-dir={isolated_profile}")
                yt_driver = webdriver.Chrome(options=options)
        set_mode("SYSTEM READY")
        return yt_driver

    except Exception as e:
        log_message("REXA", f"Could not start Chrome: {e}\nMake sure Google Chrome is installed.")
        set_mode("SYSTEM READY")
        return None


def _yt_wait(driver, by, selector, timeout=10):
    """Wait for an element and return it, or None on timeout."""
    try:
        return WebDriverWait(driver, timeout).until(
            EC.presence_of_element_located((by, selector))
        )
    except Exception:
        return None


def _yt_wait_clickable(driver, by, selector, timeout=10):
    """Wait for a clickable element and return it, or None on timeout."""
    try:
        return WebDriverWait(driver, timeout).until(
            EC.element_to_be_clickable((by, selector))
        )
    except Exception:
        return None


def parse_video_number(command_text):
    """
    Extract a 1-based video number from a command string.
    Supports: Arabic numerals (1,2,3), Bangla digits (১,২,৩),
    Bangla words (এক, দুই, তিন), English ordinals (first, second).
    Returns int or None.
    """
    low = command_text.lower()

    # English ordinals
    for word, num in ENGLISH_ORDINAL_MAP.items():
        if word in low:
            return num

    # Bangla words
    for word, num in BANGLA_WORD_MAP.items():
        if word in command_text:
            return num

    # Bangla digits — convert to ASCII then parse
    converted = command_text
    for b_digit, value in BANGLA_DIGIT_MAP.items():
        converted = converted.replace(b_digit, str(value))

    # Find standalone number in converted string
    import re
    match = re.search(r'\b(\d+)\b', converted)
    if match:
        return int(match.group(1))

    return None


def get_current_youtube_context():
    """Return a human-readable summary of the current YouTube session."""
    driver = yt_driver
    if driver is not None:
        try:
            video_state = driver.execute_script("""
                const video = document.querySelector('video');
                if (!video) return null;
                return {paused: video.paused, title: document.title,
                        url: window.location.href};
            """)
            if video_state:
                title = video_state.get("title", "").replace(" - YouTube", "").strip()
                if title:
                    yt_context["current_title"] = title
                yt_context["current_url"] = video_state.get("url") or yt_context.get("current_url")
                yt_context["mode"] = "paused" if video_state.get("paused") else "playing"
        except Exception as exc:
            log_message("REXA", f"YouTube status check failed safely: {exc}")

    if yt_context["mode"] is None:
        browser_titles = [
            window.title.strip() for window in gw.getAllWindows()
            if "youtube" in (window.title or "").lower()
            and window.title.strip()
        ]
        if browser_titles:
            title = browser_titles[0].replace(" - YouTube", "").strip()
            yt_context.update({"mode": "browser", "current_title": title})

    if yt_context["mode"] is None:
        return "No active YouTube session."

    parts = [f"Mode: {yt_context['mode']}"]
    if yt_context.get("query"):
        parts.append(f"Query: {yt_context['query']}")
    if yt_context.get("current_title"):
        parts.append(f"Playing: {yt_context['current_title']}")
    if yt_context.get("current_index") is not None:
        parts.append(f"Result #{yt_context['current_index']}")
    if yt_search_results:
        parts.append(f"Search results available: {len(yt_search_results)}")
    return " | ".join(parts)


def youtube_stop_video():
    """Pause the active YouTube video even when its browser window is minimized."""
    driver = yt_driver
    if driver is not None:
        try:
            video_state = driver.execute_script("""
                const video = document.querySelector('video');
                if (!video) return null;
                video.pause();
                return {title: document.title, url: window.location.href};
            """)
            if video_state:
                title = video_state.get("title", "").replace(" - YouTube", "").strip()
                yt_context["mode"] = "paused"
                yt_context["current_title"] = title or yt_context.get("current_title")
                yt_context["current_url"] = video_state.get("url") or yt_context.get("current_url")
                log_message("REXA", f"Paused video: {yt_context.get('current_title', 'current YouTube video')}")
                speak("The video is paused.")
                return
        except Exception as exc:
            log_message("REXA", f"Direct YouTube pause failed, trying window control: {exc}")

    if pyautogui is None:
        log_message("REXA", "YouTube control is unavailable because PyAutoGUI is not installed.")
        speak("I could not control the video.")
        return

    _youtube_key_action(
        "STOP VIDEO",
        lambda: pyautogui.press("k"),
        "Sent the pause command to YouTube.",
        "YouTube pause error",
    )


def open_youtube():
    """Open YouTube in Selenium browser and update context."""
    driver = _get_yt_driver()
    if driver is None:
        if safe_open("https://www.youtube.com/"):
            yt_context["mode"] = "browsing"
            log_message(
                "REXA",
                "Opened YouTube in the default browser. "
                "Selenium controls are unavailable.",
            )
            speak("YouTube is open, but browser controls are unavailable.")
        else:
            log_message(
                "REXA",
                "Could not open YouTube because the browser could not be started.",
            )
        return

    def worker():
        try:
            set_mode("OPENING YOUTUBE")
            driver.get("https://www.youtube.com/")
            _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
            yt_context["mode"] = "browsing"
            record_web_activity(driver.current_url, driver.title, "opened")
            log_message("REXA", "YouTube is open.")
            speak("YouTube is open.")
        except Exception as e:
            log_message("REXA", f"Could not open YouTube: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_search(query):
    """
    Search YouTube and list results with numbers.
    Stores results in yt_search_results for play-by-number commands.
    """
    query = query.strip()
    if not query:
        return

    driver = _get_yt_driver()
    if driver is None:
        return

    def worker():
        global yt_search_results
        try:
            set_mode("YOUTUBE SEARCH")
            log_message("REXA", f"Searching YouTube for: {query}")

            driver.get(
                "https://www.youtube.com/results?search_query="
                + urllib.parse.quote_plus(query)
            )

            # Wait for results to load
            _yt_wait(driver, By.CSS_SELECTOR, "ytd-video-renderer", timeout=15)
            time.sleep(1.5)  # let JS fully render

            # Scrape video titles and URLs
            results = driver.find_elements(
                By.CSS_SELECTOR,
                "ytd-video-renderer a#video-title"
            )

            yt_search_results = []
            seen_urls = set()

            for el in results:
                href = el.get_attribute("href") or ""
                title = (el.get_attribute("title") or el.text or "").strip()

                if not href or not title:
                    continue
                # Skip playlists/shorts for cleaner results
                if "list=" in href and "watch" not in href:
                    continue
                if href in seen_urls:
                    continue

                seen_urls.add(href)
                yt_search_results.append({
                    "title": title,
                    "url": href if href.startswith("http") else "https://www.youtube.com" + href,
                })

                if len(yt_search_results) >= 10:
                    break

            yt_context["mode"] = "search"
            yt_context["query"] = query
            record_web_activity(driver.current_url, driver.title, "searched", query)

            if not yt_search_results:
                log_message("REXA", "No results found. Try a different search term.")
                speak("No results found.")
                return

            # Build numbered list for chat display
            lines = [f"YouTube results for '{query}':\n"]
            for i, r in enumerate(yt_search_results, 1):
                lines.append(f"  {i}. {r['title']}")

            lines.append(
                '\nSay "play number 1" / "play first one" / "play last one" / '
                '"১ নম্বর চালাও" to play.'
            )
            log_message("REXA", "\n".join(lines))
            speak(
                f"Found {len(yt_search_results)} results for {query}. "
                "Say play number 1 to play the first result."
            )

        except Exception as e:
            log_message("REXA", f"YouTube search error: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_play_number(number):
    """
    Play the Nth result from the last youtube_search() call.
    number is 1-based.
    """
    if not yt_search_results:
        log_message(
            "REXA",
            "No search results available. "
            "Search first: 'search youtube for <query>'"
        )
        speak("Please search for something first.")
        return

    if number < 1 or number > len(yt_search_results):
        log_message(
            "REXA",
            f"I only have {len(yt_search_results)} results. "
            f"Choose a number between 1 and {len(yt_search_results)}."
        )
        speak(f"Please choose between 1 and {len(yt_search_results)}.")
        return

    driver = _get_yt_driver()
    if driver is None:
        return

    item = yt_search_results[number - 1]

    def worker():
        try:
            set_mode("YOUTUBE PLAYING")
            log_message("REXA", f"Playing #{number}: {item['title']}")
            speak(f"Playing {item['title']}")

            driver.get(item["url"])
            _yt_wait(driver, By.CSS_SELECTOR, "video", timeout=15)
            time.sleep(1.5)

            # Click play if video is paused (some pages autoplay, some don't)
            try:
                video = driver.find_element(By.CSS_SELECTOR, "video")
                paused = driver.execute_script(
                    "return arguments[0].paused;", video
                )
                if paused:
                    driver.find_element(
                        By.CSS_SELECTOR,
                        "button.ytp-play-button"
                    ).click()
            except Exception:
                pass

            yt_context["mode"] = "playing"
            yt_context["current_index"] = number
            yt_context["current_url"] = item["url"]
            yt_context["current_title"] = item["title"]

        except Exception as e:
            log_message("REXA", f"Playback error: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_play_search_range(start, end):
    """Play a bounded range of the latest YouTube search results in order."""
    if not yt_search_results:
        log_message("REXA", "Please search YouTube first.")
        speak("Please search YouTube first.")
        return

    start = max(1, start)
    end = min(end, len(yt_search_results))
    if start > end:
        log_message("REXA", "There are not enough YouTube search results for that range.")
        speak("There are not enough search results for that range.")
        return

    driver = _get_yt_driver()
    if driver is None:
        return

    items = yt_search_results[start - 1:end]

    def worker():
        try:
            set_mode("YOUTUBE QUEUE")
            for index, item in enumerate(items, start):
                log_message("REXA", f"Playing queued result #{index}: {item['title']}")
                driver.get(item["url"])
                _yt_wait(driver, By.CSS_SELECTOR, "video", timeout=15)

                try:
                    video = driver.find_element(By.CSS_SELECTOR, "video")
                    if driver.execute_script("return arguments[0].paused;", video):
                        driver.find_element(
                            By.CSS_SELECTOR, "button.ytp-play-button"
                        ).click()
                except Exception:
                    pass

                while True:
                    ended = driver.execute_script(
                        "return arguments[0].ended;", video
                    )
                    if ended:
                        break
                    time.sleep(1)

                yt_context["current_index"] = index
                yt_context["current_title"] = item["title"]
        except Exception as e:
            log_message("REXA", f"YouTube queue error: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_playlist_play_number(number):
    """
    Play the Nth video in a YouTube playlist page.
    Works when a playlist is already open in the Selenium browser.
    """
    driver = _get_yt_driver()
    if driver is None:
        return

    def worker():
        try:
            set_mode("YOUTUBE PLAYLIST")

            # YouTube renders playlist items lazily, so wait for the first
            # item instead of assuming the page is ready after navigation.
            items = []
            selectors = (
                "ytd-playlist-panel-video-renderer a#wc-endpoint, "
                "ytd-playlist-video-renderer a#video-title, "
                "ytd-playlist-video-renderer a[href*='/watch'], "
                "a[href*='/watch'][href*='list=']"
            )
            try:
                WebDriverWait(driver, 15).until(
                    lambda current_driver: current_driver.find_elements(
                        By.CSS_SELECTOR, selectors
                    )
                )
            except Exception:
                pass

            items = driver.find_elements(By.CSS_SELECTOR, selectors)

            if not items:
                log_message(
                    "REXA",
                    "No playlist found in the current page. "
                    "Open a YouTube playlist first."
                )
                return

            if number == -1:
                number = len(items)

            if number < 1 or number > len(items):
                log_message(
                    "REXA",
                    f"Playlist has {len(items)} items. "
                    f"Choose between 1 and {len(items)}."
                )
                return

            target = items[number - 1]
            title = target.get_attribute("title") or target.text or f"Video {number}"
            target_url = target.get_attribute("href") or ""

            # Navigating to the item's watch URL is more reliable than
            # clicking a lazy-rendered playlist card.
            if target_url:
                driver.get(target_url)
            else:
                driver.execute_script("arguments[0].click();", target)

            _yt_wait(driver, By.CSS_SELECTOR, "video", timeout=15)
            time.sleep(1)
            driver.execute_script("""
                const video = document.querySelector('video');
                if (video) {
                    video.play().catch(() => {});
                }
            """)

            yt_context["mode"] = "playlist"
            yt_context["current_index"] = number
            yt_context["current_title"] = title.strip()
            yt_context["current_url"] = driver.current_url

            log_message("REXA", f"Playing playlist item #{number}: {yt_context['current_title']}")
            speak(f"Playing playlist item {number}")

        except Exception as exc:
            log_message("REXA", f"Playlist error: {exc}")
            speak("I could not start that playlist video. Please make sure YouTube is signed in.")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_save_to_playlist():
    """Save the currently playing YouTube video to the first available playlist."""
    driver = yt_driver
    if driver is None:
        log_message("REXA", "YouTube is not open. Open and play a video first.")
        speak("Please open and play a YouTube video first.")
        return

    def worker():
        try:
            set_mode("SAVING PLAYLIST")
            if "youtube.com/watch" not in driver.current_url.lower():
                raise RuntimeError("no YouTube video is currently open")

            save_button = _yt_wait_clickable(
                driver,
                By.XPATH,
                "//button[contains(@aria-label, 'Save') or contains(@title, 'Save')]",
                timeout=8
            )
            if save_button is None:
                raise RuntimeError("the YouTube Save button was not found")
            save_button.click()

            playlist_option = _yt_wait_clickable(
                driver,
                By.CSS_SELECTOR,
                "ytd-playlist-add-to-option-renderer tp-yt-paper-checkbox, "
                "ytd-playlist-add-to-option-renderer #checkbox",
                timeout=8
            )
            if playlist_option is None:
                raise RuntimeError(
                    "no playlist was found; sign in to YouTube or create a playlist"
                )
            playlist_option.click()
            time.sleep(0.5)
            log_message("REXA", "Saved the current video to your first YouTube playlist.")
            speak("Saved this video to your playlist.")
        except Exception as e:
            log_message("REXA", f"Could not save the video to a playlist: {e}")
            speak("I could not save this video to your playlist.")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_next_selenium():
    """
    Navigate to the next recommended/autoplay video using Selenium.
    Falls back to existing pyautogui shortcut if driver not active.
    """
    global yt_search_results

    # If we're in search-result mode, play next result
    if (
        yt_context["mode"] in ("playing", "search")
        and yt_context.get("current_index") is not None
        and yt_search_results
    ):
        next_index = yt_context["current_index"] + 1
        if next_index <= len(yt_search_results):
            youtube_play_number(next_index)
            return

    driver = _get_yt_driver()
    if driver is None:
        youtube_next()   # fall back to existing pyautogui function
        return

    def worker():
        try:
            set_mode("YOUTUBE NEXT")

            # Try "Next" button in the player controls
            next_btn = _yt_wait_clickable(
                driver,
                By.CSS_SELECTOR,
                "a.ytp-next-button, button.ytp-next-button",
                timeout=5
            )
            if next_btn:
                next_btn.click()
                time.sleep(1.0)

                # Update title
                try:
                    yt_context["current_title"] = driver.title.replace(
                        " - YouTube", ""
                    ).strip()
                    yt_context["current_url"] = driver.current_url
                    if yt_context.get("current_index") is not None:
                        yt_context["current_index"] += 1
                except Exception:
                    pass

                log_message("REXA", f"Next video: {yt_context.get('current_title', '')}")
                speak("Next video.")
            else:
                # Fallback: keyboard shortcut
                youtube_next()

        except Exception as e:
            log_message("REXA", f"Next video error: {e}")
            youtube_next()
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_previous_selenium():
    """
    Navigate to the previous video using search results context,
    or fall back to pyautogui keyboard shortcut.
    """
    if (
        yt_context["mode"] in ("playing", "search")
        and yt_context.get("current_index") is not None
        and yt_search_results
    ):
        prev_index = yt_context["current_index"] - 1
        if prev_index >= 1:
            youtube_play_number(prev_index)
            return
        else:
            log_message("REXA", "Already at the first result.")
            speak("Already at the first result.")
            return

    # Fallback to existing keyboard shortcut
    youtube_previous()

def youtube_close_selenium():
    global yt_driver

    if yt_driver is None:
        youtube_close()
        return

    try:
        yt_driver.quit()
        log_message("REXA", "YouTube browser closed.")
        speak("YouTube closed")
    except Exception as e:
        log_message("REXA", f"Close error: {e}")
    finally:
        yt_driver = None
        yt_context["mode"] = None
        yt_context["current_title"] = None
        yt_context["current_index"] = None
        yt_search_results.clear()


def ask_youtube():
    """Ask the user what to search/play on YouTube."""
    query = simpledialog.askstring(
        "YouTube",
        "What do you want to search/play?"
    )

    if query:
        youtube_search(query)

# ============================================================
# TIKTOK
# ============================================================

def open_tiktok_search(query):
    query = query.strip()

    if query:
        safe_open(
            "https://www.tiktok.com/search?q="
            + urllib.parse.quote_plus(query)
        )

        log_message(
            "REXA",
            f"Opened TikTok search: {query}"
        )


def ask_tiktok():
    query = simpledialog.askstring(
        "TikTok",
        "What do you want to search for?"
    )

    if query:
        open_tiktok_search(query)


def tiktok_scroll_down():
    _youtube_key_action(
        "NEXT",
        lambda: pyautogui.scroll(-6),
        "Scrolled down on TikTok.",
        "TikTok scroll error"
    )


def tiktok_scroll_up():
    _youtube_key_action(
        "PREVIOUS",
        lambda: pyautogui.scroll(6),
        "Scrolled up on TikTok.",
        "TikTok scroll error"
    )


def switch_to_tiktok():
    open_tiktok()


def _social_login_required(driver, platform):
    """Best-effort detection for a social site that still needs sign-in."""
    try:
        url = (driver.current_url or "").lower()
        body = (driver.find_element(By.TAG_NAME, "body").text or "").lower()
        if "login" in url or "signin" in url:
            return True
        if platform == "tiktok":
            if driver.find_elements(By.CSS_SELECTOR, "[data-e2e='top-login-button']"):
                return True
            return "log in" in body and "sign up" in body
        return bool(driver.find_elements(By.CSS_SELECTOR, "input[name='email'], input[name='pass']"))
    except Exception:
        return False


def _open_social_page(platform, url):
    """Open a social page in REXA's persistent, non-temporary browser."""
    names = {"tiktok": "TikTok", "facebook": "Facebook Messenger"}
    driver = _get_yt_driver()
    if driver is None:
        # Still make the requested page available in the user's normal
        # browser if Selenium is not installed or Chrome cannot start.
        safe_open(url)
        log_message("REXA", f"Opened {names[platform]} in your default browser.")
        return None

    def worker():
        try:
            set_mode("OPENING " + names[platform].upper())
            driver.get(url)
            _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
            if _social_login_required(driver, platform):
                message = (
                    f"{names[platform]} is open. Please sign in to your own "
                    "account in this REXA browser once. Your login will be "
                    "kept for future inbox checks."
                )
            else:
                message = f"Opened your {names[platform]} account."
            log_message("REXA", message)
            speak(message)
        except Exception as exc:
            log_message("REXA", f"Could not open {names[platform]}: {exc}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()
    return driver


def open_tiktok():
    """Open TikTok in the user's normal browser profile."""
    state["active_social_inbox"] = "tiktok"
    # Google and TikTok can reject sign-in from a WebDriver-controlled
    # browser.  Use the user's normal, trusted Chrome profile instead.
    safe_open("https://www.tiktok.com/")
    log_message("REXA", "Opened TikTok in your normal browser.")


def login_tiktok():
    """Open TikTok's sign-in page in the user's normal browser."""
    state["active_social_inbox"] = "tiktok"
    safe_open("https://www.tiktok.com/login")
    log_message("REXA", "Opened TikTok sign-in in your normal browser.")


def _visible_social_threads(driver, platform):
    """Return visible conversation labels from a signed-in social web page."""
    selectors = {
        "tiktok": [
            "[data-e2e*='message']", "[data-e2e*='chat']",
            "a[href*='/messages/']",
        ],
        "facebook": [
            "a[href*='/t/']", "[role='main'] [role='row']",
            "[role='grid'] [role='row']",
        ],
    }[platform]
    script = """
        const selectors = arguments[0];
        const values = [];
        for (const selector of selectors) {
          for (const element of document.querySelectorAll(selector)) {
            const raw = element.getAttribute('aria-label') || element.innerText || '';
            // Conversation rows often contain sender, message preview, and
            // time on separate lines. Announce only the sender/row label.
            const label = (raw.split(/\\r?\\n/).find(Boolean) || raw)
              .replace(/\\s+/g, ' ').trim();
            if (label && label.length < 120) values.push(label);
          }
        }
        return [...new Set(values)].slice(0, 12);
    """
    values = driver.execute_script(script, selectors) or []
    ignored = {"messages", "messenger", "search", "new message", "inbox"}
    return [value for value in values if value.lower() not in ignored][:5]


def check_social_inbox(platform):
    """Open and summarize visible message threads without opening any message."""
    urls = {
        "tiktok": "https://www.tiktok.com/messages",
        "facebook": "https://www.messenger.com/",
    }
    names = {"tiktok": "TikTok", "facebook": "Facebook Messenger"}
    state["active_social_inbox"] = platform

    if platform == "tiktok":
        # Do not open a WebDriver browser for a private account.  Google
        # correctly treats that browser as automated and may reject OAuth
        # sign-in.  The default browser already has the user's normal,
        # trusted TikTok session.
        safe_open(urls[platform])
        threading.Thread(
            target=_open_first_tiktok_message_after_load,
            name="REXA-TikTok-Inbox",
            daemon=True,
        ).start()
        reply = (
            "Opened your TikTok messages in your normal browser. "
            "Sign in there if TikTok asks you to."
        )
        log_message("REXA", reply)
        speak(reply)
        return

    driver = _get_yt_driver()
    if driver is None:
        log_message("REXA", f"Could not start a browser to check {names[platform]}.")
        return

    def worker():
        try:
            set_mode("CHECKING INBOX")
            driver.get(urls[platform])
            _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
            # TikTok and Messenger render conversation rows after the shell
            # page is ready, so give the signed-in page a moment to populate.
            time.sleep(4)
            threads = _visible_social_threads(driver, platform)
            if _social_login_required(driver, platform):
                reply = (
                    f"Please sign in to your own {names[platform]} account "
                    "in the REXA browser, then say check my inbox again."
                )
            elif threads:
                reply = "Sir, you have visible message threads from " + ", ".join(threads) + "."
            else:
                reply = (
                    f"I opened your {names[platform]} inbox, but there are "
                    "no visible message threads to report."
                )
            log_message("REXA", reply)
            speak(reply)
        except Exception as exc:
            log_message("REXA", f"Could not check {names[platform]} inbox: {exc}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def open_instagram():
    safe_open("https://www.instagram.com/")
    log_message("REXA", "Opened Instagram.")


def open_instagram_notifications():
    safe_open("https://www.instagram.com/notifications/")
    log_message("REXA", "Opened Instagram notifications.")


def tiktok_message_person(person):
    open_tiktok_search(person)
    log_message(
        "REXA",
        f"Searched TikTok for '{person}' — REXA can't message them "
        "directly (needs login/private access), please open the "
        "profile and message them yourself."
    )


def whatsapp_reply_or_send(number_or_name, message):
    # Only truly automates opening a pre-filled draft; the user still
    # has to press Send. Cannot read/reply to an actual existing thread
    # or place a call, since that needs WhatsApp's private app access.
    whatsapp_message(number_or_name, message)


def cannot_do(feature):
    log_message(
        "REXA",
        f"Sorry, '{feature}' — REXA can't do this directly yet, "
        "because it needs that app's own account access/private API "
        "which this script doesn't have. I won't falsely claim I did it."
    )


def set_brightness(percent):
    try:
        import screen_brightness_control as sbc
        percent = max(0, min(100, int(percent)))
        sbc.set_brightness(percent)
        log_message("REXA", f"Set brightness to {percent}%. \u2600\uFE0F")
    except ImportError:
        log_message(
            "REXA",
            "For brightness control, install:\n"
            "pip install screen-brightness-control"
        )
    except Exception as e:
        log_message("REXA", f"Brightness error: {e}")


# ============================================================
# VOICE RECOGNITION
# ============================================================

def _record_with_sounddevice(seconds=8):
    """Capture a mono PCM recording when PyAudio is unavailable."""
    if sd is None or np is None or sr is None:
        return None

    # Ask PortAudio to validate the *current* Windows default input before
    # recording.  This produces a useful device error instead of passing an
    # empty recording to Google and reporting a misleading decode failure.
    device_info = sd.query_devices(kind="input")
    sample_rate = int(device_info.get("default_samplerate") or 16000)
    sample_rate = max(8000, sample_rate)
    sd.check_input_settings(
        device=device_info["name"], samplerate=sample_rate, channels=1,
        dtype="int16"
    )
    recording = sd.rec(
        int(seconds * sample_rate), samplerate=sample_rate, channels=1,
        dtype="int16",
    )
    sd.wait()
    if not recording.size or not np.any(recording):
        raise RuntimeError("The microphone recorded no audio")
    return sr.AudioData(recording.tobytes(), sample_rate, 2)


def _capture_voice_audio(recognizer, timeout, phrase_time_limit):
    """Capture from PyAudio, falling back to sounddevice on any backend error."""
    try:
        with sr.Microphone(device_index=MIC_DEVICE_INDEX) as source:
            recognizer.adjust_for_ambient_noise(source, duration=0.8)
            # Keep the calibrated value stable while the command is spoken.
            recognizer.dynamic_energy_threshold = False
            return recognizer.listen(
                source, timeout=timeout, phrase_time_limit=phrase_time_limit
            )
    except Exception as microphone_error:
        if sd is None:
            raise microphone_error
        log_message("REXA", "Using the compatible sounddevice microphone backend.")
        try:
            return _record_with_sounddevice(seconds=phrase_time_limit)
        except Exception as fallback_error:
            raise RuntimeError(
                f"Microphone capture failed ({microphone_error}); "
                f"sounddevice fallback failed ({fallback_error})"
            ) from fallback_error

def _mic_error_message(e):
    """Build a clear message for microphone failures on Windows."""
    err_text = str(e)

    if "No Default Input Device" in err_text or "Invalid input device" in err_text:
        return (
            "Couldn't open the microphone: no default input device is set "
            "in Windows.\n"
            "Fix: open 'open sound settings' -> Input, plug in/enable a "
            "microphone, and set it as the Default Device. Also check "
            "Settings > Privacy > Microphone to make sure app access is "
            "allowed, then try voice chat again."
        )

    return (
        f"Couldn't open the microphone: {err_text}\n"
        "Check Windows microphone permission and PyAudio."
    )


def _auto_switch_language_from_text(text):
    """Switch voice language silently when recognized input contains Bengali script."""
    if re.search(r"[\u0980-\u09FF]", text or ""):
        state["language_mode"] = "bengali"
        memory["language_mode"] = "bengali"
        save_memory(memory)
    elif re.search(r"[A-Za-z]", text or ""):
        state["language_mode"] = "english"
        memory["language_mode"] = "english"
        save_memory(memory)


def _recognize_with_local_whisper():
    """Use local Faster-Whisper when installed; return empty to use cloud fallback."""
    global _local_whisper_model, _silero_vad_model
    if WhisperModel is None or sd is None or np is None:
        return ""
    audio_data = _record_with_sounddevice(seconds=8)
    if audio_data is None:
        return ""
    samples = np.frombuffer(audio_data.get_raw_data(), dtype=np.int16).astype(np.float32) / 32768.0
    if not np.any(samples):
        return ""
    if _local_whisper_model is None:
        _local_whisper_model = WhisperModel(
            WHISPER_MODEL_NAME,
            device=os.getenv("REXA_WHISPER_DEVICE", "cpu"),
            compute_type=os.getenv("REXA_WHISPER_COMPUTE", "int8"),
        )
    if get_speech_timestamps is not None and load_silero_vad is not None:
        try:
            import torch  # pyright: ignore[reportMissingImports]
            if _silero_vad_model is None:
                _silero_vad_model = load_silero_vad()
            timestamps = get_speech_timestamps(
                torch.from_numpy(samples), _silero_vad_model, sampling_rate=audio_data.sample_rate
            )
            if timestamps:
                samples = np.concatenate(
                    [samples[item["start"]:item["end"]] for item in timestamps]
                )
        except (ImportError, RuntimeError, ValueError):
            pass
    language = "bn" if state.get("language_mode") == "bengali" else None
    segments, _ = _local_whisper_model.transcribe(
        samples,
        language=language,
        vad_filter=True,
        beam_size=1,
    )
    return " ".join(segment.text.strip() for segment in segments).strip()


def recognize_voice_once():
    if sr is None:
        log_message(
            "REXA",
            "For voice recognition, install:\n"
            "pip install SpeechRecognition PyAudio"
        )
        return ""

    try:
        if WhisperModel is not None and sd is not None and np is not None:
            set_mode("LISTENING...")
            local_text = _recognize_with_local_whisper()
            if local_text:
                _auto_switch_language_from_text(local_text)
                log_message("YOU", f"\U0001F3A4 {local_text}")
                return local_text
    except Exception as exc:
        log_message("REXA", f"Local speech recognition unavailable; using fallback: {exc}")

    try:
        recognizer = sr.Recognizer()
        # FIX: dynamic_energy_threshold constantly re-tunes the
        # cutoff mid-sentence, which can make it trigger "silence"
        # too early on a longer command. Turning it off and instead
        # doing one solid ambient-noise calibration below is more
        # reliable for full-sentence commands.
        recognizer.dynamic_energy_threshold = False
        recognizer.energy_threshold = 300
        # FIX: 0.8s was too short — any natural pause while speaking
        # (thinking, breathing) was read as "command finished" and
        # cut the rest of the sentence off. 1.3s gives more room.
        recognizer.pause_threshold = 1.3
        recognizer.non_speaking_duration = 0.5

        prepare_voice_listening(focus_ui=True)
        set_mode("LISTENING...")
        log_message("REXA", "\U0001F3A4 Listening... speak now.")

        audio = _capture_voice_audio(
            recognizer, timeout=6, phrase_time_limit=20
        )

        set_mode("VOICE PROCESSING")

        # FIX: the old code retried recognize_google() a second time
        # on the SAME audio after an UnknownValueError. Since the
        # audio doesn't change, the second call always fails with
        # the exact same error — it did nothing but waste an API
        # call. Removed; the outer except block already handles
        # UnknownValueError properly.
        recognition_language = "bn-BD" if state.get("language_mode") == "bengali" else "en-US"
        text = recognizer.recognize_google(audio, language=recognition_language)

        text = (text or "").strip()

        if text:
            _auto_switch_language_from_text(text)
            log_message(
                "YOU",
                f"\U0001F3A4 {text}"
            )

        return text

    except sr.WaitTimeoutError:
        log_message(
            "REXA",
            "I didn't hear anything. Try again."
        )

    except sr.UnknownValueError:
        log_message(
            "REXA",
            "I couldn't make out the recording. Speak after the listening "
            "prompt and check that Windows is using the right microphone."
        )

    except sr.RequestError as e:
        log_message(
            "REXA",
            f"Speech recognition service error: {e}"
        )

    except Exception as e:
        log_message(
            "REXA",
            _mic_error_message(e)
        )

    finally:
        set_mode("SYSTEM READY")

    return ""


def voice_command_once():
    text = recognize_voice_once()

    if text:
        execute_command(text)

def start_voice_chat():
    global voice_recognition_running
    global voice_recognition_thread

    play_sfx("listen_on")

    if sr is None:
        log_message(
            "REXA",
            "Install voice recognition:\n"
            "pip install SpeechRecognition PyAudio"
        )

        speak(
            "Voice recognition is not installed."
        )

        return

    if voice_recognition_running:
        log_message(
            "REXA",
            "Voice chat is already running."
        )
        return

    voice_recognition_running = True
    voice_recognition_stop.clear()

    log_message(
        "REXA",
        "\U0001F399\uFE0F Voice chat ON — REXA will listen to you."
    )

    speak(
        "Voice chat is on. "
        "You can talk to me now."
    )

    def worker():
        global voice_recognition_running

        recognizer = sr.Recognizer()

        # FIX: same reasoning as recognize_voice_once() — a fixed
        # threshold plus a longer pause_threshold stops REXA from
        # cutting a command off the moment you pause to think.
        recognizer.dynamic_energy_threshold = False
        recognizer.energy_threshold = 300
        recognizer.pause_threshold = 1.3
        recognizer.non_speaking_duration = 0.5

        try:
            try:
                source_context = sr.Microphone(device_index=MIC_DEVICE_INDEX)
                source = source_context.__enter__()
            except Exception:
                source_context = None
                source = None

            if source is None:
                log_message("REXA", "Using the compatible sounddevice microphone backend.")
            else:
                set_mode("CALIBRATING MIC")
                recognizer.adjust_for_ambient_noise(
                    source,
                    duration=1.0
                )
            log_message("REXA", "\U0001F3A4 Microphone ready. Speak.")

            while not voice_recognition_stop.is_set():

                    try:
                        # Do not let the recognizer transcribe REXA's own
                        # asynchronous TTS response as a user command.
                        while state["speaking"] and not voice_recognition_stop.is_set():
                            time.sleep(0.05)
                        if voice_recognition_stop.is_set():
                            break

                        prepare_voice_listening()
                        set_mode("LISTENING...")

                        # FIX: timeout=1 only controls how long REXA
                        # waits for you to START talking (fine, it
                        # just loops again if you're silent).
                        # phrase_time_limit=10 -> 20 so it doesn't cut
                        # off a longer sentence once you do start.
                        if source is None:
                            audio = _record_with_sounddevice()
                            if audio is None:
                                raise RuntimeError("Could not capture microphone audio")
                        else:
                            audio = recognizer.listen(
                                source, timeout=1, phrase_time_limit=20
                            )

                    except sr.WaitTimeoutError:
                        continue

                    if voice_recognition_stop.is_set():
                        break

                    try:
                        set_mode("VOICE PROCESSING")

                        # FIX: removed the pointless retry that called
                        # recognize_google() twice on the same audio
                        # after an UnknownValueError (it always fails
                        # the same way the second time too).
                        recognition_language = "bn-BD" if state.get("language_mode") == "bengali" else "en-US"
                        user_text = recognizer.recognize_google(audio, language=recognition_language)

                        user_text = (
                            user_text or ""
                        ).strip()

                        if user_text:
                            log_message(
                                "YOU",
                                f"\U0001F3A4 {user_text}"
                            )

                            execute_command(user_text)

                    except sr.UnknownValueError:
                        log_message(
                            "REXA",
                            "I couldn't make out the recording. Please try again."
                        )

                    except sr.RequestError as e:
                        log_message(
                            "REXA",
                            f"Speech service error: {e}"
                        )
                        time.sleep(1)

                    except Exception as e:
                        log_message(
                            "REXA",
                            f"Voice processing error: {e}"
                        )

            if source_context is not None:
                source_context.__exit__(None, None, None)

        except Exception as e:
            log_message(
                "REXA",
                _mic_error_message(e)
            )

        finally:
            voice_recognition_running = False
            set_mode("SYSTEM READY")

            log_message(
                "REXA",
                "\U0001F399\uFE0F Voice chat OFF."
            )

    voice_recognition_thread = threading.Thread(
        target=worker,
        daemon=True
    )

    voice_recognition_thread.start()


def stop_voice_chat():
    global voice_recognition_running

    if not voice_recognition_running:
        log_message(
            "REXA",
            "Voice chat is already OFF."
        )
        return

    voice_recognition_stop.set()
    voice_recognition_running = False

    set_mode("SYSTEM READY")

    log_message(
        "REXA",
        "\U0001F399\uFE0F Voice chat stopped."
    )


# ============================================================
# GEMINI AI
# ============================================================

GEMINI_SYSTEM = """
You are REXA / JARVIS — an omnipotent, ultra-responsive, proactive Windows AI
digital operator and personal technical aide running inside a Python Tkinter
desktop app powered by the OpenRouter API. Be sharp, respectful, calm,
technically correct, and honest about the capabilities and evidence available.

1. CORE PERSONA AND VOICE OPTIMIZATION
- Be calm, polite, extremely sharp, and precise, like a high-tech service AI.
- Keep everyday spoken responses to one to three crisp sentences for fast Edge-TTS playback.
- Start with the direct answer or action acknowledgment.
- Use respectful forms such as Sir or Boss when natural.
- Ask one short, relevant follow-up after every four to six responses, never every turn,
    and never after a direct technical query.
- Never claim an OS command, email, or script succeeded unless Python verified it.

2. AUTONOMOUS SYSTEM AND TOOL REASONING
- Decompose complex high-level intents into actionable Windows, browser, and scripting commands.
- Correlate available user context, including the active window, current screen, system metrics,
    and time of day, before answering. Do not imply context was inspected when it was not available.
- Ask for confirmation before destructive actions.
- Execute available safe actions directly instead of describing steps the user did not request.
- For explicit sandbox requests, generate only safe local Python, report stderr precisely, and
    never claim success without a verified exit code.

3. PROACTIVE MONITORING AND STATUS REPORTING
- Continuously inspect the conversation context and any provided code, logs, or command output.
- Detect syntax errors, bugs, performance bottlenecks, security risks, and build or test failures
    as soon as they appear; state the exact fix when one is clear.
- Track long-running commands and multi-step workflows, and report completion or failure promptly.
- Recommend the most relevant next step, edge-case test, or safe optimization when useful.
- Use concise status tags exactly as follows: [ALERT] for critical hardware or security issues,
    [EXECUTING] for active background work, [COMPLETED] only for verified success, and
    [SUGGESTION] for useful proactive recommendations.
- Do not claim monitoring, execution, or success without evidence from the available context or tools.

4. SCREEN VISION AND MULTIMODAL AWARENESS
- When the user references the screen, use the available screen inspection capability and analyze
    visible details precisely. If screen inspection is unavailable, say so instead of guessing.
- Read errors, explain charts, and summarize visible pages accurately and concisely.

5. EMAIL AND CALENDAR INTELLIGENCE
- Handle calendar queries, meeting scheduling, and email composition natively when the
    connected integration is available. Never pretend an email or event was sent or booked.

6. SEMANTIC MEMORY AND PRIVACY
- Correlate the user's profile, project notes, habits, and preferences by meaning.
- Never record or output passwords, API keys, private tokens, or financial credentials.

7. REAL-TIME PACING
- Use clean standard punctuation. Avoid complex symbols, heavy markdown, and long clauses
    that make text-to-speech difficult.

8. CODE AND CALCULATION
- Verify complex math, conversions, data transformations, regex, and logic before answering.

9. BILINGUAL ADAPTATION
- If the user writes in Bengali or Banglish, or Bengali mode is active, reply in polished,
    natural Bengali script. Do not answer in English unless the user asks for English.
- Keep technical terms, file paths, and app names in English where clearer.
- Otherwise reply in concise, professional English.

Keep all replies concise, direct, truthful, and suitable for both chat display and voice playback.
"""


def conversation_mode_prompt():
    if state.get("conversation_mode") == "story":
        return (
            "Conversation mode: STORY. Chat casually and naturally with the user. "
            "Keep replies short and warm, ask at most one relevant follow-up question, "
            "and avoid repeating questions already answered in the conversation. "
            "Do not turn casual conversation into a command list."
        )
    if state.get("conversation_mode") == "serious":
        return (
            "Conversation mode: SERIOUS. Answer questions directly and calmly. "
            "Use precise, thoughtful language, avoid jokes and playful wording, "
            "and clearly mention uncertainty when information is incomplete."
        )
    return (
        "Conversation mode: NORMAL. Be friendly, natural, concise, and helpful. "
        "Light warmth is okay, but do not overdo jokes or follow-up questions."
    )


def language_mode_prompt():
    if state.get("language_mode") == "bengali":
        return (
            "Language mode: BENGALI. Reply in clear, polished, natural Bengali script. "
            "If the user uses Banglish, understand it and still answer in Bengali script. "
            "Keep technical names and commands in English when that is clearer. "
            "Address the user respectfully as Sir or Boss. Keep spoken replies to "
            "one to three crisp, natural sentences."
        )
    return (
        "Language mode: ENGLISH. Reply in clear concise English unless the "
        "user explicitly requests another language. Address the user respectfully "
        "as Sir or Boss. Keep spoken replies to one to three crisp, natural sentences."
    )


def set_language_mode(language):
    language = "bengali" if language == "bengali" else "english"
    state["language_mode"] = language
    memory["language_mode"] = language
    save_memory(memory)
    label = "বাংলা মোড চালু হয়েছে।" if language == "bengali" else "English mode is on."
    log_message("REXA", label)
    speak(label)


def ask_gemini(user_text):
    if gemini_client is None:
        return (
            "Couldn't reach Gemini.\n\n"
            "Check these:\n"
            "1. pip install google-genai python-dotenv\n"
            "2. Is GEMINI_API_KEY set in your .env file?\n"
            "3. Is the API key correct?\n"
            "4. Is there an internet connection?"
        )

    try:
        gemini_history.append({
            "role": "user",
            "text": user_text
        })
        state["assistant_reply_count"] += 1
        ask_question = state["assistant_reply_count"] % 5 == 0

        recent = gemini_history[-GEMINI_HISTORY_LIMIT:]

        conversation = []
        for item in recent:
            role = "User" if item["role"] == "user" else "REXA"
            conversation.append(f"{role}: {item['text']}")

        profile_line = " ".join(
            part for part in [
                user_identity_summary_for_ai(),
                profile_summary_for_ai(),
                memory_summary_for_ai(),
                relevant_memory_summary_for_ai(user_text),
            ]
            if part
        )
        mood_line = mood_context(user_text)

        prompt = (
            GEMINI_SYSTEM
            + "\nKeep normal replies to one to three concise sentences so voice playback starts quickly."
            + f"\n\n{conversation_mode_prompt()}"
            + f"\n\n{language_mode_prompt()}"
            + (
                f"\n\nWhat you know about the user so far: {profile_line}"
                if profile_line else ""
            )
            + f"\n\n{mood_line}"
            + "\n\nConversation:\n"
            + "\n".join(conversation)
            + (
                "\n\nAsk one short, relevant question at the end of this reply."
                if ask_question else ""
            )
            + "\n\nREXA:"
        )

        response = gemini_client.models.generate_content(
            model=GEMINI_MODEL,
            contents=prompt
        )

        answer = ""
        if response is not None:
            answer = getattr(response, "text", "") or ""

        answer = answer.strip()

        if not answer:
            answer = "I didn't get a response. Please ask again."

        gemini_history.append({
            "role": "model",
            "text": answer
        })
        return answer

    except Exception:
        return "Opps Boss"

def ask_openrouter(user_text):
    if openrouter_client is None:
        return "OpenRouter API key not found. Add OPENROUTER_API_KEY to your .env file."

    try:
        gemini_history.append({"role": "user", "text": user_text})
        state["assistant_reply_count"] += 1
        ask_question = state["assistant_reply_count"] % 5 == 0
        recent = gemini_history[-GEMINI_HISTORY_LIMIT:]

        system_message = GEMINI_SYSTEM
        system_message += f"\n\n{conversation_mode_prompt()}"
        system_message += f"\n\n{language_mode_prompt()}"
        profile_line = " ".join(
            part for part in [
                user_identity_summary_for_ai(),
                profile_summary_for_ai(),
                memory_summary_for_ai(),
                relevant_memory_summary_for_ai(user_text),
            ]
            if part
        )
        mood_line = mood_context(user_text)
        system_message += "\nKeep normal replies to one to three concise sentences so voice playback starts quickly."
        if profile_line:
            system_message += f"\n\nWhat you know about the user so far: {profile_line}"
        system_message += f"\n\n{mood_line}"
        if ask_question:
            system_message += "\nAsk one short, relevant question at the end of this reply."
        messages = [{"role": "system", "content": system_message}]
        for item in recent:
            role = "user" if item["role"] == "user" else "assistant"
            messages.append({"role": role, "content": item["text"]})

        response = openrouter_client.chat.completions.create(
            model=OPENROUTER_MODEL,
            messages=messages,
            temperature=0.7,
            max_tokens=500
        )

        answer = response.choices[0].message.content.strip()
        gemini_history.append({"role": "model", "text": answer})
        return answer

    except Exception as e:
        return f"OpenRouter error: {e}"
# ============================================================
# WHATSAPP
# ============================================================

def whatsapp_message(number=None, message=None):
    if number is None:
        number = simpledialog.askstring(
            "WhatsApp",
            "Phone number with country code:"
        )

    if not number:
        return

    if message is None:
        message = simpledialog.askstring(
            "WhatsApp",
            "Message:"
        )

    if message is None:
        return

    clean_number = "".join(
        ch for ch in number
        if ch.isdigit()
    )

    if not clean_number:
        log_message(
            "REXA",
            "Couldn't find a valid phone number."
        )
        return

    url = (
        "https://wa.me/"
        + clean_number
        + "?text="
        + urllib.parse.quote(message)
    )

    if safe_open(url):
        log_message(
            "REXA",
            "WhatsApp message ready. "
            "You still need to press Send."
        )


def ask_whatsapp():
    whatsapp_message()


# ============================================================
# WINDOWS TOOLS
# ============================================================

def open_pc():
    try:
        os.startfile(str(Path.home()))
        log_message(
            "REXA",
            "Opened File Explorer."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"File Explorer error: {e}"
        )


def open_desktop():
    try:
        os.startfile(str(Path.home() / "Desktop"))
        log_message(
            "REXA",
            "Opened the Desktop folder."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Desktop error: {e}"
        )


def open_downloads():
    try:
        os.startfile(
            str(Path.home() / "Downloads")
        )

        log_message(
            "REXA",
            "Opened the Downloads folder."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Downloads error: {e}"
        )


def open_documents():
    try:
        os.startfile(
            str(Path.home() / "Documents")
        )

        log_message(
            "REXA",
            "Opened the Documents folder."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Documents error: {e}"
        )


def open_notepad():
    try:
        subprocess.Popen(["notepad.exe"])

        log_message(
            "REXA",
            "Opened Notepad."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Notepad error: {e}"
        )


def open_calculator():
    try:
        subprocess.Popen(["calc.exe"])

        log_message(
            "REXA",
            "Opened Calculator."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Calculator error: {e}"
        )


def open_paint():
    try:
        subprocess.Popen(["mspaint.exe"])
        log_message("REXA", "Opened Paint.")
    except Exception as e:
        log_message("REXA", f"Paint error: {e}")


def open_camera():
    try:
        os.startfile("microsoft.windows.camera:")
        log_message("REXA", "Opened Camera.")
    except Exception as e:
        log_message("REXA", f"Camera error: {e}")


def open_cmd():
    try:
        subprocess.Popen(["cmd.exe"])

        log_message(
            "REXA",
            "Opened Command Prompt."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"CMD error: {e}"
        )


def open_python():
    try:
        subprocess.Popen([sys.executable, "-m", "idlelib"])
        log_message("REXA", "Opened Python IDLE.")
        speak("Opening Python.")
    except Exception as e:
        log_message("REXA", f"Python open error: {e}")


def close_python():
    close_app("idle.exe", "Python IDLE")


def open_powershell():
    try:
        subprocess.Popen(["powershell.exe"])

        log_message(
            "REXA",
            "Opened PowerShell."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"PowerShell error: {e}"
        )


def open_settings():
    try:
        os.startfile("ms-settings:")

        log_message(
            "REXA",
            "Opened Windows Settings."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Settings error: {e}"
        )


def open_task_manager():
    try:
        subprocess.Popen(["taskmgr.exe"])

        log_message(
            "REXA",
            "Opened Task Manager."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Task Manager error: {e}"
        )


def open_google():
    query = simpledialog.askstring(
        "Google",
        "Google Search:"
    )

    if query:
        search_google_query(query)


def open_network_settings():
    try:
        os.startfile(
            "ms-settings:network"
        )

        log_message(
            "REXA",
            "Opened Network Settings."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Network settings error: {e}"
        )


def open_personalization():
    try:
        os.startfile(
            "ms-settings:personalization"
        )

        log_message(
            "REXA",
            "Opened Personalization."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Personalization error: {e}"
        )


def open_chrome():
    try:
        subprocess.Popen(["cmd", "/c", "start", "chrome"], shell=False)
        log_message("REXA", "Tried to open Chrome.")
    except Exception as e:
        log_message("REXA", f"Chrome error: {e}")


def open_edge():
    try:
        subprocess.Popen(["cmd", "/c", "start", "msedge"], shell=False)
        log_message("REXA", "Tried to open Edge.")
    except Exception as e:
        log_message("REXA", f"Edge error: {e}")


def open_spotify():
    try:
        os.startfile("spotify:")
        log_message("REXA", "Opened Spotify.")
    except Exception as e:
        log_message(
            "REXA",
            f"Couldn't find Spotify: {e}\n"
            "Check whether Spotify is installed."
        )


def close_active_window():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("alt", "f4")
        log_message("REXA", "Closed the active window.")
    except Exception as e:
        log_message("REXA", f"Close window error: {e}")


# ------------------------------------------------------------
# CLOSE SPECIFIC APPS BY NAME (NEW)
# ------------------------------------------------------------
# REXA could open a lot of apps but never close a *specific* one by
# name — only the currently focused window (close_active_window).
# This uses taskkill to close a named app wherever it's running.

def close_app(process_name, friendly_name=None):
    friendly_name = friendly_name or process_name

    try:
        result = subprocess.run(
            ["taskkill", "/f", "/im", process_name],
            capture_output=True,
            text=True
        )

        if result.returncode == 0:
            log_message("REXA", f"Closed {friendly_name}. \u2705")
        else:
            log_message(
                "REXA",
                f"I couldn't find {friendly_name} running right now."
            )
    except Exception as e:
        log_message("REXA", f"Close {friendly_name} error: {e}")


def close_notepad():
    close_app("notepad.exe", "Notepad")


def close_calculator():
    # Modern Windows Calculator runs as a UWP app under a different
    # process name than the old calc.exe, so try both.
    close_app("CalculatorApp.exe", "Calculator")
    close_app("calc.exe", "Calculator")


def close_paint():
    close_app("mspaint.exe", "Paint")


def close_cmd():
    close_app("cmd.exe", "Command Prompt")


def close_powershell():
    close_app("powershell.exe", "PowerShell")


def close_chrome():
    close_app("chrome.exe", "Chrome")


def close_chrome_safely():
    """Close Chrome and end the Selenium driver if it is still connected."""
    global yt_driver
    try:
        if yt_driver is not None:
            try:
                yt_driver.quit()
            except Exception:
                pass
            yt_driver = None
    finally:
        close_chrome()


def close_edge():
    close_app("msedge.exe", "Edge")


def close_spotify():
    close_app("Spotify.exe", "Spotify")


def close_task_manager():
    close_app("Taskmgr.exe", "Task Manager")


def close_settings_app():
    close_app("SystemSettings.exe", "Settings")


def close_file_explorer():
    close_app("explorer.exe", "File Explorer")


def close_camera_app():
    close_app("WindowsCamera.exe", "Camera")


def minimize_all_windows():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("win", "d")
        log_message("REXA", "Minimized all windows.")
    except Exception as e:
        log_message("REXA", f"Minimize error: {e}")


def switch_window():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("alt", "tab")
        log_message("REXA", "Switched windows.")
    except Exception as e:
        log_message("REXA", f"Switch window error: {e}")


def volume_up():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        for _ in range(3):
            pyautogui.press("volumeup")
        log_message("REXA", "Turned the volume up. \U0001F50A")
    except Exception as e:
        log_message("REXA", f"Volume error: {e}")


def volume_down():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        for _ in range(3):
            pyautogui.press("volumedown")
        log_message("REXA", "Turned the volume down. \U0001F509")
    except Exception as e:
        log_message("REXA", f"Volume error: {e}")


def volume_mute():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.press("volumemute")
        log_message("REXA", "Toggled mute/unmute. \U0001F507")
    except Exception as e:
        log_message("REXA", f"Mute error: {e}")


def lock_pc():
    try:
        subprocess.Popen([
            "rundll32.exe",
            "user32.dll,LockWorkStation"
        ])

        log_message(
            "REXA",
            "PC locked."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Lock error: {e}"
        )

def shutdown_pc(delay_seconds=10, delay_label=None):
    delay_label = delay_label or f"{delay_seconds} seconds"
    log_message("REXA", f"Shut down the PC in {delay_label}? Say yes or no.")
    speak("Are you sure you want to shut down the computer? Say yes or no.")

    def worker():
        answer = recognize_voice_once()   # মাইক থেকে শোনে
        low = answer.lower().strip()

        if "yes" in low or "হ্যাঁ" in answer:
            subprocess.Popen(["shutdown", "/s", "/t", str(delay_seconds)])
            if delay_seconds > 0:
                message = (
                    f"I got it, Sir. I have scheduled the system shutdown "
                    f"in {delay_label}."
                )
            else:
                message = "I got it, Sir. The system shutdown is scheduled now."
            log_message("REXA", message)
            speak(message)
        else:
            log_message("REXA", "Shutdown cancelled.")
            speak("Okay, cancelled.")

    threading.Thread(target=worker, daemon=True).start()


def parse_shutdown_delay(command):
    """Return (seconds, spoken label) using the first value in a time phrase."""
    match = re.search(
        r"\b(\d+)\s*(?:or|/)\s*(?:\d+\s*)?"
        r"(minutes?|mins?|hours?|hrs?)\b",
        command,
        flags=re.IGNORECASE,
    )
    if not match:
        match = re.search(
            r"\b(\d+)\s*(minutes?|mins?|hours?|hrs?)\b",
            command,
            flags=re.IGNORECASE,
        )
    if not match:
        return None

    value = int(match.group(1))
    unit = match.group(2).lower()
    multiplier = 3600 if unit.startswith(("hour", "hr")) else 60
    normalized_unit = "hour" if multiplier == 3600 else "minute"
    if value != 1:
        normalized_unit += "s"
    return value * multiplier, f"{value} {normalized_unit}"
    

def restart_pc():
    if messagebox.askyesno(
        "REXA",
        "Restart the PC?"
    ):
        subprocess.Popen([
            "shutdown",
            "/r",
            "/t",
            "10"
        ])

        log_message(
            "REXA",
            "The PC will restart in 10 seconds."
        )


def cancel_shutdown():
    try:
        subprocess.Popen([
            "shutdown",
            "/a"
        ])

        log_message(
            "REXA",
            "Cancelled the pending shutdown/restart."
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Cancel error: {e}"
        )


def take_screenshot():
    if ImageGrab is None:
        log_message(
            "REXA",
            "For screenshots, install:\n"
            "pip install pillow"
        )
        return

    try:
        folder = BASE_DIR / "screenshots"
        folder.mkdir(exist_ok=True)

        filename = folder / (
            "rexa_"
            + dt.datetime.now().strftime(
                "%Y%m%d_%H%M%S"
            )
            + ".png"
        )

        ImageGrab.grab().save(filename)

        log_message(
            "REXA",
            f"Screenshot saved:\n{filename}"
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Screenshot error: {e}"
        )


def _screen_image_data_url():
    """Capture and compress the desktop in memory; never writes a vision image to disk."""
    if ImageGrab is None:
        raise RuntimeError("Screen capture needs Pillow: pip install pillow")
    image = ImageGrab.grab(all_screens=True)
    image.thumbnail((1920, 1080))
    if image.mode not in {"RGB", "L"}:
        image = image.convert("RGB")
    buffer = io.BytesIO()
    image.save(buffer, format="JPEG", quality=72, optimize=True, progressive=True)
    encoded = base64.b64encode(buffer.getvalue()).decode("ascii")
    return "data:image/jpeg;base64," + encoded


def analyze_screen_with_vision(request):
    """Analyze the current screen without blocking Tkinter's event loop."""
    request = (request or "Describe the important visible content on my screen.").strip()

    def worker():
        try:
            set_mode("VISION ANALYSIS")
            if openrouter_client is None:
                raise RuntimeError(
                    "Vision analysis needs OPENROUTER_API_KEY and the OpenAI package."
                )
            image_url = _screen_image_data_url()
            response = openrouter_client.chat.completions.create(
                model=OPENROUTER_VISION_MODEL,
                messages=[{
                    "role": "user",
                    "content": [
                        {
                            "type": "text",
                            "text": (
                                "Analyze this Windows screenshot accurately. "
                                "Do not claim to click, type, or fix anything. "
                                "Answer in one to three concise sentences. "
                                "If Bengali mode is active, answer in natural Bengali. "
                                "Include a concrete code fix when an error is visible.\n\n"
                                f"User request: {request}"
                            ),
                        },
                        {"type": "image_url", "image_url": {"url": image_url}},
                    ],
                }],
                temperature=0.2,
                max_tokens=300,
                timeout=25,
            )
            answer = (response.choices[0].message.content or "").strip()
            if not answer:
                raise RuntimeError("The vision model returned an empty response.")
            log_message("REXA", "[SCREEN VISION] [COMPLETED] " + answer)
            speak(answer)
        except Exception as exc:
            log_message("REXA", f"[SCREEN VISION] [ALERT] Vision analysis failed: {exc}")
            speak(
                "আমি স্ক্রিন বিশ্লেষণ করতে পারিনি।"
                if state.get("language_mode") == "bengali"
                else "I could not analyze the screen."
            )
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, name="REXA-Screen-Vision", daemon=True).start()


def _computer_use_action(text):
    """Handle explicit coordinate click/type commands with a safety gate."""
    if pyautogui is None:
        log_message("REXA", "Computer control needs: pip install pyautogui")
        return True

    click_match = re.search(
        r"\b(?:click|press|tap)\s+(?:at\s+)?(\d{1,5})\s*[, ]\s*(\d{1,5})\b",
        text,
        flags=re.IGNORECASE,
    )
    type_match = re.match(r"^\s*(?:type|write)\s+(.+)$", text, flags=re.IGNORECASE | re.DOTALL)
    if not click_match and not type_match:
        return False

    action_text = text.strip()
    destructive_words = (
        "delete", "remove", "close", "submit", "send", "purchase",
        "buy", "pay", "shutdown", "restart", "format",
    )
    if any(word in action_text.lower() for word in destructive_words):
        if not confirm_destructive_action("Computer Use", action_text):
            return True

    def worker():
        try:
            set_mode("EXECUTING")
            if click_match:
                x, y = (int(click_match.group(1)), int(click_match.group(2)))
                pyautogui.click(x, y)
                log_message("REXA", f"[COMPLETED] Clicked at ({x}, {y}).")
            else:
                value = type_match.group(1)
                pyautogui.write(value, interval=0.01)
                log_message("REXA", "[COMPLETED] Typed the requested text.")
        except Exception as exc:
            log_message("REXA", f"[ALERT] Computer-use action failed: {exc}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, name="REXA-Computer-Use", daemon=True).start()
    return True


# ============================================================
# SYSTEM / NETWORK
# ============================================================

def check_network():
    try:
        socket.create_connection(
            ("8.8.8.8", 53),
            timeout=1
        )
        return True

    except Exception:
        return False


def system_info():
    if not psutil:
        log_message(
            "REXA",
            "psutil is not installed."
        )
        return

    try:
        cpu = psutil.cpu_percent(
            interval=0.2
        )

        ram = psutil.virtual_memory()

        disk = psutil.disk_usage(
            Path.home().anchor
        )

        text = (
            "SYSTEM INFORMATION\n\n"
            f"CPU: {cpu:.0f}%\n"
            f"RAM: {ram.percent:.0f}% "
            f"({ram.used / (1024**3):.1f} GB used)\n"
            f"DISK: {disk.percent:.0f}% "
            f"({disk.free / (1024**3):.1f} GB free)\n"
            f"OS: {sys.platform}\n"
            f"Python: {sys.version.split()[0]}"
        )

        try:
            battery = psutil.sensors_battery()

            if battery:
                text += (
                    f"\nBattery: "
                    f"{battery.percent:.0f}%"
                )
        except Exception:
            pass

        log_message(
            "REXA",
            text
        )

    except Exception as e:
        log_message(
            "REXA",
            f"System info error: {e}"
        )


def network_info():
    try:
        hostname = socket.gethostname()

        local_ip = socket.gethostbyname(
            hostname
        )

        log_message(
            "REXA",
            "NETWORK INFORMATION\n\n"
            f"Computer: {hostname}\n"
            f"Local IP: {local_ip}\n"
            f"Internet: "
            f"{'ONLINE' if check_network() else 'OFFLINE'}"
        )

    except Exception as e:
        log_message(
            "REXA",
            f"Network info error: {e}"
        )


def open_ip_search():
    safe_open(
        "https://www.google.com/search?q="
        "my+IP+address"
    )

    log_message(
        "REXA",
        "Opened an IP information search."
    )


# ============================================================
# GOOGLE SEARCH / WIKIPEDIA
# ============================================================

def search_google_query(query):
    if query:
        safe_open(
            "https://www.google.com/search?q="
            + urllib.parse.quote_plus(query)
        )

        log_message(
            "REXA",
            f"Opened Google search: {query}"
        )


def search_wikipedia_query(query):
    query = (query or "").strip()
    if not query:
        return

    def worker():
        if wikipedia_api is None:
            log_message("REXA", "Wikipedia voice search needs: pip install wikipedia")
            return
        try:
            wikipedia_api.set_lang("en")
            summary = wikipedia_api.summary(query, sentences=2, auto_suggest=True)
            log_message("REXA", f"Wikipedia: {query}\n\n{summary}")
            speak(summary)
        except Exception as exc:
            log_message("REXA", f"Wikipedia lookup failed: {exc}")

    threading.Thread(target=worker, name="JARVIS-Wikipedia", daemon=True).start()


# ============================================================
# ADVANCED BROWSER / MEDIA CONTROLS
# ============================================================

def youtube_speed_up():
    _youtube_key_action(
        "PLAY SPEED",
        lambda: pyautogui.hotkey("shift", "."),
        "Increased the playback speed by one step.",
        "Speed error", delay=0.2
    )


def youtube_speed_down():
    _youtube_key_action(
        "PLAY SPEED",
        lambda: pyautogui.hotkey("shift", ","),
        "Decreased the playback speed by one step.",
        "Speed error", delay=0.2
    )


def youtube_set_speed_1_5x():
    def worker():
        try:
            set_mode("PLAYBACK SPEED")
            time.sleep(0.2)
            # Reset toward 1x isn't reliable without reading state,
            # so we nudge up twice from a typical 1x default (1x -> 1.5x).
            pyautogui.hotkey("shift", ".")
            time.sleep(0.15)
            pyautogui.hotkey("shift", ".")
            log_message(
                "REXA",
                "Set the playback speed to about 1.5x (may not be "
                "exact if the video was already at a different speed)."
            )
        except Exception as e:
            log_message("REXA", f"Speed error: {e}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def youtube_toggle_subtitles():
    _youtube_key_action(
        "SUBTITLES",
        lambda: pyautogui.press("c"),
        "Toggled subtitles on/off.",
        "Subtitles error", delay=0.2
    )


def browser_close_tab():
    _youtube_key_action(
        "CLOSE TAB",
        lambda: pyautogui.hotkey("ctrl", "w"),
        "Closed the current tab.",
        "Close tab error", delay=0.2
    )


def browser_reopen_tab():
    _youtube_key_action(
        "REOPEN TAB",
        lambda: pyautogui.hotkey("ctrl", "shift", "t"),
        "Reopened the last closed tab.",
        "Reopen tab error", delay=0.2
    )


def browser_incognito():
    _youtube_key_action(
        "INCOGNITO",
        lambda: pyautogui.hotkey("ctrl", "shift", "n"),
        "Opened a new incognito window.",
        "Incognito error", delay=0.2
    )


def browser_bookmark_page():
    _youtube_key_action(
        "BOOKMARK",
        lambda: pyautogui.hotkey("ctrl", "d"),
        "Bookmarked the page.",
        "Bookmark error", delay=0.2
    )


def browser_scroll_half_page():
    _youtube_key_action(
        "SCROLL DOWN",
        lambda: pyautogui.press("space"),
        "Scrolled down half a page.",
        "Scroll error", delay=0.2
    )


def browser_refresh():
    _youtube_key_action(
        "REFRESH",
        lambda: pyautogui.press("f5"),
        "Refreshed the page.",
        "Refresh error", delay=0.2
    )


def browser_previous_tab():
    _youtube_key_action(
        "PREVIOUS TAB",
        lambda: pyautogui.hotkey("ctrl", "shift", "tab"),
        "Switched to the previous tab.",
        "Switch tab error", delay=0.2
    )


def open_youtube_and_play(query):
    youtube_open()

    def worker():
        time.sleep(1.2)
        play_youtube(query)

    threading.Thread(target=worker, daemon=True).start()


# ============================================================
# GENERIC WEB ASSISTANT
# ============================================================

web_assistant_mode = False


def _browser_driver():
    return _get_yt_driver()


def _browser_worker(mode_label, action):
    driver = _browser_driver()
    if driver is None:
        log_message(
            "REXA",
            "Browser automation is unavailable. "
            "Please install Chrome and the Selenium dependencies.",
        )
        return

    def worker():
        try:
            set_mode(mode_label)
            action(driver)
        except Exception as e:
            error_text = str(e).splitlines()[0].strip() or type(e).__name__
            log_message(
                "REXA",
                f"I can't interact with that webpage yet, Boss: {error_text}"
            )
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()


def browser_open_url(url):
    url = url.strip()
    if not url:
        return
    if not re.match(r"^https?://", url, flags=re.IGNORECASE):
        url = "https://" + url

    def action(driver):
        driver.get(url)
        _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
        record_web_activity(driver.current_url, driver.title, "opened")
        log_message("REXA", f"Opening {url}.")
        speak("The webpage is open.")

    _browser_worker("OPENING WEBPAGE", action)


def browser_read_page():
    def action(driver):
        body = driver.find_element(By.TAG_NAME, "body").text.strip()
        visible_text = body[:6000] if body else "No readable text is visible."
        log_message(
            "REXA",
            f"Page: {driver.title}\nURL: {driver.current_url}\n\n{visible_text}"
        )

    _browser_worker("READING WEBPAGE", action)


def browser_page_context():
    def action(driver):
        links = [
            (el.text or el.get_attribute("aria-label") or "").strip()
            for el in driver.find_elements(By.CSS_SELECTOR, "a,button")
        ]
        links = [item for item in links if item][:40]
        handles = driver.window_handles
        log_message(
            "REXA",
            f"Title: {driver.title}\nURL: {driver.current_url}\n"
            f"Open tabs: {len(handles)}\nVisible controls: "
            + (", ".join(links) if links else "none detected")
        )

    _browser_worker("INSPECTING WEBPAGE", action)


def browser_find_text(query):
    query = query.strip()
    if not query:
        return

    def action(driver):
        elements = driver.find_elements(
            By.XPATH,
            "//*[contains(translate(normalize-space(.), "
            "'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), "
            f"{json.dumps(query.lower())})]"
        )
        if not elements:
            log_message("REXA", f"I couldn't find '{query}' on this page.")
            return
        driver.execute_script(
            "arguments[0].scrollIntoView({block: 'center'});", elements[0]
        )
        log_message("REXA", f"Found '{query}' on the page and scrolled to it.")

    _browser_worker("FINDING WEBPAGE TEXT", action)


def browser_click_result(number):
    def action(driver):
        candidates = driver.find_elements(By.CSS_SELECTOR, "a,button")
        visible = [item for item in candidates if item.is_displayed() and item.text.strip()]
        if number < 1 or number > len(visible):
            raise ValueError(f"there are only {len(visible)} visible controls")
        element = visible[number - 1]
        driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", element)
        element.click()
        log_message("REXA", f"Opened visible result {number}.")

    _browser_worker("OPENING WEB RESULT", action)


def browser_click_text(label):
    label = label.strip()
    if not label:
        return

    def action(driver):
        element = WebDriverWait(driver, 10).until(
            EC.element_to_be_clickable((By.XPATH, f"//*[normalize-space()={json.dumps(label)}]"))
        )
        element.click()
        log_message("REXA", f"Clicked '{label}'.")

    _browser_worker("CLICKING WEBPAGE CONTROL", action)


def browser_fill_box(label, value):
    label = label.strip()
    value = value.strip()
    if not label or not value:
        return

    def action(driver):
        fields = driver.find_elements(By.CSS_SELECTOR, "input,textarea,[contenteditable='true']")
        field = next(
            (item for item in fields if item.is_displayed() and (
                label.lower() in (item.get_attribute("placeholder") or "").lower()
                or label.lower() in (item.get_attribute("aria-label") or "").lower()
                or label.lower() in (item.get_attribute("name") or "").lower()
            )),
            None
        )
        if field is None:
            raise ValueError(f"couldn't find a text box named '{label}'")
        field.clear()
        field.send_keys(value)
        log_message("REXA", f"Filled the '{label}' text box.")

    _browser_worker("FILLING WEBPAGE FORM", action)


def browser_submit_form():
    if not messagebox.askyesno("REXA", "Submit this webpage form?"):
        log_message("REXA", "Form submission cancelled.")
        return

    def action(driver):
        forms = [item for item in driver.find_elements(By.TAG_NAME, "form") if item.is_displayed()]
        if not forms:
            raise ValueError("no visible form was found")
        driver.execute_script("arguments[0].submit();", forms[0])
        log_message("REXA", "Submitted the visible webpage form.")

    _browser_worker("SUBMITTING WEB FORM", action)


def browser_new_tab():
    _browser_worker("OPENING NEW TAB", lambda driver: driver.switch_to.new_window("tab"))


def browser_switch_tab(number):
    def action(driver):
        handles = driver.window_handles
        if number < 1 or number > len(handles):
            raise ValueError(f"there are only {len(handles)} open tabs")
        driver.switch_to.window(handles[number - 1])
        log_message("REXA", f"Switched to tab {number}: {driver.title}")

    _browser_worker("SWITCHING BROWSER TAB", action)


def browser_scroll(direction="down"):
    amount = -650 if direction == "up" else 650
    _browser_worker(
        "SCROLLING WEBPAGE",
        lambda driver: driver.execute_script("window.scrollBy(0, arguments[0]);", amount)
    )


def youtube_exit_fullscreen():
    driver = yt_driver
    if driver is None:
        log_message("REXA", "YouTube isn't open. Should I open it?")
        return

    def action(active_driver):
        if "youtube.com" not in active_driver.current_url.lower():
            raise RuntimeError("the active page is not YouTube")
        active_driver.execute_script("document.exitFullscreen();")
        log_message("REXA", "YouTube exited fullscreen.")

    _browser_worker("EXITING FULLSCREEN", action)


def youtube_minimize_window():
    driver = yt_driver
    if driver is None:
        log_message("REXA", "YouTube isn't open. Should I open it?")
        return
    def action(active_driver):
        if "youtube.com" not in active_driver.current_url.lower():
            raise RuntimeError("the active page is not YouTube")
        active_driver.minimize_window()
        log_message("REXA", "YouTube browser window minimized.")

    _browser_worker("MINIMIZING YOUTUBE", action)


def youtube_scroll(amount="normal", direction="down"):
    distances = {"little": 300, "normal": 650, "lot": 1000}
    distance = distances.get(amount, distances["normal"])
    if direction == "up":
        distance *= -1

    def action(driver):
        if "youtube.com" not in driver.current_url.lower():
            raise RuntimeError("the active page is not YouTube")
        driver.execute_script(
            "window.scrollBy({top: arguments[0], left: 0, behavior: 'smooth'});",
            distance
        )
        log_message("REXA", "Scrolling YouTube " + direction + ".")

    if yt_driver is None:
        log_message("REXA", "YouTube isn't open. Should I open it?")
        return
    _browser_worker("YOUTUBE SCROLL", action)


def set_youtube_scroll_mode(active):
    """Enable or disable persistent YouTube scrolling for follow-up commands."""
    global youtube_scroll_mode_active
    youtube_scroll_mode_active = active

    if not active:
        log_message("REXA", "YouTube scroll mode is off.")
        speak("YouTube scroll mode is off.")
        return

    driver = _get_yt_driver()
    if driver is None:
        youtube_scroll_mode_active = False
        log_message("REXA", "I could not activate YouTube scroll mode because the browser is unavailable.")
        speak("I could not activate YouTube scroll mode.")
        return

    def action(active_driver):
        if "youtube.com" not in active_driver.current_url.lower():
            raise RuntimeError("the active browser page is not YouTube")
        active_driver.switch_to.window(active_driver.current_window_handle)
        yt_context["mode"] = yt_context.get("mode") or "browsing"
        log_message("REXA", "YouTube scroll mode is on. Say scroll up or scroll down.")
        speak("YouTube scroll mode is on.")

    _browser_worker("YOUTUBE SCROLL MODE", action)


def youtube_scroll_edge(edge):
    def action(driver):
        if "youtube.com" not in driver.current_url.lower():
            raise RuntimeError("the active page is not YouTube")
        position = "0" if edge == "top" else "document.body.scrollHeight"
        driver.execute_script(
            f"window.scrollTo({{top: {position}, behavior: 'smooth'}});"
        )
        log_message("REXA", f"YouTube scrolled to the {edge}.")

    if yt_driver is None:
        log_message("REXA", "YouTube isn't open. Should I open it?")
        return
    _browser_worker("YOUTUBE SCROLL", action)


def open_youtube_search_bar():
    visible_windows = [
        window for window in gw.getAllWindows()
        if "youtube" in (window.title or "").lower()
    ]
    if visible_windows and pyautogui is not None:
        def focus_active_youtube_search():
            try:
                set_mode("OPENING YOUTUBE SEARCH")
                youtube_window = visible_windows[0]
                youtube_window.activate()
                time.sleep(0.25)
                # YouTube's search field sits in the upper page toolbar.
                # Clicking it works for both the normal and signed-out home page.
                click_x = youtube_window.left + int(youtube_window.width * 0.48)
                click_y = youtube_window.top + int(youtube_window.height * 0.15)
                pyautogui.click(click_x, click_y)
                state["awaiting_youtube_search"] = True
                log_message("REXA", "What should I search for you, Boss?")
                speak("What should I search for you, Boss?")
            except Exception as e:
                log_message("REXA", f"I couldn't focus the YouTube search bar: {e}")
            finally:
                set_mode("SYSTEM READY")

        threading.Thread(target=focus_active_youtube_search, daemon=True).start()
        return

    if yt_driver is None:
        log_message("REXA", "YouTube isn't open. Say 'open YouTube' first.")
        return

    def action(driver):
        if "youtube.com" not in driver.current_url.lower():
            raise RuntimeError("the active page is not YouTube")
        search_box = WebDriverWait(driver, 10).until(
            EC.element_to_be_clickable(
                (By.CSS_SELECTOR, "input#search, ytd-searchbox input")
            )
        )
        search_box.click()
        state["awaiting_youtube_search"] = True
        log_message("REXA", "What should I search for you, Boss?")
        speak("What should I search for you, Boss?")

    _browser_worker("OPENING YOUTUBE SEARCH", action)
    
def open_chatgpt():
    if safe_open("https://chatgpt.com/"):
        log_message("REXA", "Opening ChatGPT.")
        speak("Opening ChatGPT.")


def chrome_fullscreen():
    if pyautogui is None:
        log_message("REXA", "I can't control Chrome fullscreen right now.")
        return

    browser_windows = [
        window for window in gw.getAllWindows()
        if any(name in (window.title or "").lower() for name in ("youtube", "chrome", "google"))
    ]
    if not browser_windows:
        log_message("REXA", "Chrome isn't open. Should I open it?")
        return

    def worker():
        try:
            browser_windows[0].activate()
            time.sleep(0.25)
            pyautogui.press("f11")
            log_message("REXA", "Chrome fullscreen toggled.")
        except Exception as e:
            log_message("REXA", f"Chrome fullscreen error: {e}")

    threading.Thread(target=worker, daemon=True).start()


def open_chatgpt_desktop():
    command = (
        "$app = Get-StartApps | Where-Object { $_.Name -match 'ChatGPT' } "
        "| Select-Object -First 1; "
        "if ($app) { Start-Process ('shell:AppsFolder\\' + $app.AppID) } "
        "else { exit 1 }"
    )
    try:
        result = subprocess.run(
            ["powershell.exe", "-NoProfile", "-Command", command],
            capture_output=True,
            text=True,
            timeout=10
        )
        if result.returncode == 0:
            log_message("REXA", "Opening the ChatGPT desktop app.")
            speak("Opening the ChatGPT desktop app.")
        else:
            log_message("REXA", "The ChatGPT desktop app is not installed.")
    except Exception as e:
        log_message("REXA", f"ChatGPT desktop app error: {e}")

def close_chatgpt():
    driver = yt_driver
    if driver is not None:
        try:
            if "chatgpt.com" in driver.current_url.lower() or "openai.com" in driver.current_url.lower():
                driver.close()
                log_message("REXA", "Closed ChatGPT.")
                return
        except Exception:
            pass

    if pyautogui is None:
        log_message("REXA", "I can't close ChatGPT because browser control is unavailable.")
        return
    _youtube_key_action(
        "CLOSE CHATGPT",
        lambda: pyautogui.hotkey("ctrl", "w"),
        "Closed the active ChatGPT tab.",
        "ChatGPT close error"
    )


# ============================================================
# MESSAGING / SOCIAL (only what's genuinely possible)
# ============================================================

def open_messenger():
    safe_open("https://www.messenger.com/")
    log_message(
        "REXA",
        "Opened Messenger Web — REXA can't send messages by itself, "
        "you'll need to type and press Send."
    )


def whatsapp_share_link(number_or_name, link):
    whatsapp_message(number_or_name, link)


def open_facebook_feed():
    state["active_social_inbox"] = "facebook"
    _open_social_page("facebook", "https://www.facebook.com/")


def open_notification_center():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return
    try:
        pyautogui.hotkey("win", "n")
        log_message(
            "REXA",
            "Opened the Windows Notification Center — REXA can't "
            "read/speak notification text by itself."
        )
    except Exception as e:
        log_message("REXA", f"Notification center error: {e}")


# ============================================================
# SYSTEM / POWER / VOLUME (advanced)
# ============================================================

REXA_TASK_PREFIX = "REXA_"


def _run_schtasks(task_name, schedule, action, start_time, start_date=None, days=None):
    """Create or replace a named, user-visible Task Scheduler task."""
    command = ["schtasks", "/create", "/tn", task_name, "/tr", action,
               "/sc", schedule, "/st", start_time, "/f"]
    if start_date:
        command.extend(["/sd", start_date])
    if days:
        command.extend(["/d", days])
    try:
        result = subprocess.run(command, capture_output=True, text=True)
        if result.returncode == 0:
            log_message("REXA", f"Scheduled task created: {task_name}.")
            return True
        log_message("REXA", f"Couldn't create {task_name}: {result.stderr.strip() or result.stdout.strip()}")
    except Exception as e:
        log_message("REXA", f"Task Scheduler error: {e}")
    return False


def _tomorrow_date():
    return (dt.date.today() + dt.timedelta(days=1)).strftime("%m/%d/%Y")


def set_system_volume(percent):
    """Set the master endpoint volume when pycaw is available."""
    try:
        from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
        from comtypes import CLSCTX_ALL
        device = AudioUtilities.GetSpeakers()
        interface = device.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
        volume = interface.QueryInterface(IAudioEndpointVolume)
        volume.SetMasterVolumeLevelScalar(max(0, min(100, percent)) / 100, None)
        log_message("REXA", f"Set system volume to {percent}%.")
    except ImportError:
        log_message("REXA", "System volume needs pycaw. Install it with: pip install pycaw comtypes")
    except Exception as e:
        log_message("REXA", f"System volume error: {e}")


def take_desktop_screenshot():
    if ImageGrab is None:
        log_message("REXA", "For screenshots, install: pip install pillow")
        return
    try:
        desktop = Path.home() / "Desktop"
        filename = desktop / f"rexa_{dt.datetime.now():%Y%m%d_%H%M%S}.png"
        ImageGrab.grab().save(filename)
        log_message("REXA", f"Screenshot saved to Desktop: {filename}")
    except Exception as e:
        log_message("REXA", f"Screenshot error: {e}")


def set_wifi(enabled):
    # Select the first active Wi-Fi adapter; Windows may require elevation.
    verb = "Enable" if enabled else "Disable"
    script = ("$a=Get-NetAdapter -Physical | Where-Object {$_.InterfaceDescription "
              "-match 'Wi-Fi|Wireless|802.11'} | Select-Object -First 1; "
              f"if($a){{{verb}-NetAdapter -Name $a.Name -Confirm:$false}}")
    try:
        result = subprocess.run(["powershell.exe", "-NoProfile", "-Command", script],
                                capture_output=True, text=True)
        if result.returncode == 0:
            log_message("REXA", f"Wi-Fi turned {'on' if enabled else 'off'}.")
        else:
            log_message("REXA", "Windows couldn't change Wi-Fi. Try running REXA as administrator.")
    except Exception as e:
        log_message("REXA", f"Wi-Fi error: {e}")


def schedule_pc_automation(kind):
    tomorrow = _tomorrow_date()
    documents = Path.home() / "Documents"
    if kind == "nightly_shutdown":
        _run_schtasks("REXA_NightlyShutdown", "DAILY", "shutdown.exe /s /f /t 0", "23:00")
    elif kind == "morning_email_calendar":
        _run_schtasks("REXA_MorningEmailCalendar", "ONCE",
                      "cmd.exe /c start https://mail.google.com & start https://calendar.google.com",
                      "08:00", tomorrow)
    elif kind == "weekday_task_reminder":
        _run_schtasks("REXA_WeekdayTaskReminder", "WEEKLY",
                      "powershell.exe -NoProfile -Command \"Add-Type -AssemblyName PresentationFramework;[System.Windows.MessageBox]::Show('Check your task list.','REXA Reminder')\"",
                      "09:00", days="MON,TUE,WED,THU,FRI")
    elif kind == "daily_backup":
        backup_dir = documents / "REXA_Backups"
        _run_schtasks("REXA_DailyDocumentsBackup", "DAILY",
                      f'cmd.exe /c if not exist "{backup_dir}" mkdir "{backup_dir}" & robocopy "{documents}" "{backup_dir}" /E /XD "{backup_dir}"',
                      "00:00")
    elif kind == "excel_project":
        _run_schtasks("REXA_MorningExcel", "ONCE", "excel.exe", "09:00", tomorrow)
        log_message("REXA", "Excel will open tomorrow at 9 AM. Add your project-file path to the task in Task Scheduler if needed.")
    elif kind == "python_cleanup":
        script = BASE_DIR / "cleanup.py"
        _run_schtasks("REXA_DailyPythonCleanup", "DAILY",
                      f'python.exe "{script}"', "06:00")
        if not script.exists():
            log_message("REXA", f"Note: create {script.name} before its first run.")
    elif kind == "weekly_report":
        script = BASE_DIR / "weekly_report.py"
        _run_schtasks("REXA_WeeklyReport", "WEEKLY", f'python.exe "{script}"', "10:00", days="MON")
        if not script.exists():
            log_message("REXA", f"Note: create {script.name} before Monday's run.")
    elif kind == "sunset_brightness":
        log_message("REXA", "Sunset-based brightness needs your location and a solar-time service, so I opened Display settings instead.")
        open_display_settings()
    elif kind == "wifi_nights":
        _run_schtasks("REXA_WifiOffMidnight", "DAILY", "powershell.exe -NoProfile -Command \"Disable-NetAdapter -Name 'Wi-Fi' -Confirm:$false\"", "00:00")
        _run_schtasks("REXA_WifiOnMorning", "DAILY", "powershell.exe -NoProfile -Command \"Enable-NetAdapter -Name 'Wi-Fi' -Confirm:$false\"", "07:00")


def cancel_rexa_task(task_name):
    try:
        result = subprocess.run(["schtasks", "/delete", "/tn", task_name, "/f"], capture_output=True, text=True)
        if result.returncode == 0:
            log_message("REXA", f"Cancelled scheduled task: {task_name}.")
        else:
            log_message("REXA", f"No scheduled REXA task named {task_name} was found.")
    except Exception as e:
        log_message("REXA", f"Task cancellation error: {e}")


def handle_pc_automation_command(text):
    """Exact PC-control and automation prompts supported by the command center."""
    low = text.lower().strip()
    if "shut down my pc in 10 minutes" in low:
        shutdown_pc(600); return True
    if "restart the computer now" in low:
        restart_pc(); return True
    if "put my pc to sleep" in low:
        sleep_pc(); return True
    if "lock my screen" in low:
        lock_pc(); return True
    volume = re.search(r"set (?:system )?volume to\s*(\d{1,3})%?", low)
    if volume:
        set_system_volume(min(100, int(volume.group(1)))); return True
    brightness = re.search(r"(?:increase )?screen brightness to\s*(\d{1,3})%?", low)
    if brightness:
        set_brightness(min(100, int(brightness.group(1)))); return True
    if "open chrome browser" in low:
        open_chrome(); return True
    if "close spotify" in low:
        close_spotify(); return True
    if "budget_2026.xlsx" in low:
        search_pc_for_file("budget_2026.xlsx"); return True
    if "take a screenshot" in low and "desktop" in low:
        take_desktop_screenshot(); return True
    if "turn off wi-fi" in low or "turn off wifi" in low:
        set_wifi(False); return True
    if "turn on bluetooth" in low:
        open_bluetooth_settings(); return True
    if "battery percentage" in low:
        check_battery_percent(); return True
    if "close all background apps" in low:
        open_task_manager(); log_message("REXA", "Task Manager is open so you can safely choose which apps to close."); return True
    if "clean up temporary files" in low:
        if messagebox.askyesno("REXA", "Clear temporary files? Files currently in use will be skipped."):
            clear_temp_files()
        return True
    if "print this document" in low:
        if pyautogui:
            pyautogui.hotkey("ctrl", "p"); log_message("REXA", "Opened the print dialog for the active document.")
        else:
            log_message("REXA", "Install pyautogui to open the print dialog.")
        return True
    if "start recording my screen" in low:
        if pyautogui:
            pyautogui.hotkey("win", "alt", "r"); log_message("REXA", "Sent the Xbox Game Bar screen-recording shortcut.")
        else:
            log_message("REXA", "Install pyautogui to start recording.")
        return True
    if "turn on night light mode" in low:
        open_night_light(); return True
    if "enable do not disturb mode" in low:
        open_focus_assist(); return True
    if "check for software updates" in low:
        open_windows_update(); return True

    scheduled = {
        "shut down my pc automatically at 11 pm every night": "nightly_shutdown",
        "tomorrow at 8 am, automatically open my email and calendar": "morning_email_calendar",
        "every weekday at 9 am, remind me to check my task list": "weekday_task_reminder",
        "automatically back up my documents folder every day at midnight": "daily_backup",
        "tomorrow at 9 am, automatically launch excel and my project file": "excel_project",
        "run my python cleanup script automatically every day at 6 am": "python_cleanup",
        "every monday at 10 am, automatically generate my weekly report": "weekly_report",
        "lower screen brightness automatically at sunset every day": "sunset_brightness",
        "turn off wi-fi automatically at midnight and turn it back on at 7 am": "wifi_nights",
    }
    for phrase, kind in scheduled.items():
        if phrase in low:
            if messagebox.askyesno("REXA", "Create this scheduled automation in Windows Task Scheduler?"):
                schedule_pc_automation(kind)
            return True
    if "cancel my scheduled 6 am auto-shutdown for tomorrow" in low:
        cancel_rexa_task("REXA_AutoShutdown_6AM"); return True
    return False

def sleep_pc():
    try:
        subprocess.Popen([
            "rundll32.exe", "powrprof.dll,SetSuspendState", "0,1,0"
        ])
        log_message("REXA", "PC is going to sleep mode. \U0001F4A4")
    except Exception as e:
        log_message("REXA", f"Sleep error: {e}")


def open_night_light():
    try:
        os.startfile("ms-settings:nightlight")
        log_message(
            "REXA",
            "Opened Night Light settings — toggle it on/off from here."
        )
    except Exception as e:
        log_message("REXA", f"Night light error: {e}")


def open_focus_assist():
    try:
        os.startfile("ms-settings:quickactions")
        log_message(
            "REXA",
            "Opened Focus/Do Not Disturb settings — turn it on from here."
        )
    except Exception as e:
        log_message("REXA", f"Focus assist error: {e}")


def check_battery_percent():
    if not psutil:
        log_message("REXA", "psutil is not installed.")
        return
    try:
        battery = psutil.sensors_battery()
        if battery:
            log_message(
                "REXA",
                f"Battery: {battery.percent:.0f}% "
                f"({'Charging' if battery.power_plugged else 'On battery'})"
            )
        else:
            log_message("REXA", "No battery sensor found on this device (might be a desktop PC).")
    except Exception as e:
        log_message("REXA", f"Battery check error: {e}")


def check_drive_space(drive="C:\\"):
    if not psutil:
        log_message("REXA", "psutil is not installed.")
        return
    try:
        usage = psutil.disk_usage(drive)
        log_message(
            "REXA",
            f"Drive {drive} — Free: {usage.free / (1024**3):.1f} GB / "
            f"Total: {usage.total / (1024**3):.1f} GB "
            f"({usage.percent:.0f}% used)"
        )
    except Exception as e:
        log_message("REXA", f"Drive space error: {e}")


def open_device_manager():
    try:
        os.startfile("devmgmt.msc")
        log_message("REXA", "Opened Device Manager.")
    except Exception as e:
        log_message("REXA", f"Device Manager error: {e}")


def set_dark_mode(dark=True):
    if winreg is None:
        log_message("REXA", "This only works on Windows.")
        return

    try:
        key_path = r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize"
        value = 0 if dark else 1

        key = winreg.OpenKey(
            winreg.HKEY_CURRENT_USER, key_path, 0, winreg.KEY_SET_VALUE
        )
        winreg.SetValueEx(key, "AppsUseLightTheme", 0, winreg.REG_DWORD, value)
        winreg.SetValueEx(key, "SystemUsesLightTheme", 0, winreg.REG_DWORD, value)
        winreg.CloseKey(key)

        log_message(
            "REXA",
            f"Turned on system {'Dark' if dark else 'Light'} mode. "
            "Some apps may need a restart to show the effect."
        )
    except Exception as e:
        log_message("REXA", f"Dark mode error: {e}")


def clear_temp_files():
    try:
        temp_dir = Path(tempfile.gettempdir())
        removed = 0

        for item in temp_dir.iterdir():
            try:
                if item.is_file():
                    item.unlink()
                    removed += 1
                elif item.is_dir():
                    shutil.rmtree(item, ignore_errors=True)
                    removed += 1
            except Exception:
                continue

        log_message(
            "REXA",
            f"Tried to clear {removed} item(s) from the temp folder "
            "(files in use were skipped)."
        )
    except Exception as e:
        log_message("REXA", f"Clear temp error: {e}")


# ============================================================
# NEW: 18 EXTRA WINDOWS / SYSTEM COMMANDS
# ============================================================

def open_control_panel():
    try:
        subprocess.Popen(["control.exe"])
        log_message("REXA", "Opened Control Panel.")
    except Exception as e:
        log_message("REXA", f"Control Panel error: {e}")


def open_sound_settings():
    try:
        os.startfile("ms-settings:sound")
        log_message("REXA", "Opened Sound settings.")
    except Exception as e:
        log_message("REXA", f"Sound settings error: {e}")


def open_display_settings():
    try:
        os.startfile("ms-settings:display")
        log_message("REXA", "Opened Display settings.")
    except Exception as e:
        log_message("REXA", f"Display settings error: {e}")


def open_windows_update():
    try:
        os.startfile("ms-settings:windowsupdate")
        log_message("REXA", "Opened Windows Update.")
    except Exception as e:
        log_message("REXA", f"Windows Update error: {e}")


def open_recycle_bin_folder():
    try:
        os.startfile("shell:RecycleBinFolder")
        log_message("REXA", "Opened Recycle Bin.")
    except Exception as e:
        log_message("REXA", f"Recycle Bin error: {e}")


def open_desktop_folder():
    try:
        os.startfile(str(Path.home() / "Desktop"))
        log_message("REXA", "Opened the Desktop folder.")
    except Exception as e:
        log_message("REXA", f"Desktop folder error: {e}")


def open_startup_folder():
    try:
        os.startfile("shell:startup")
        log_message("REXA", "Opened the Startup folder.")
    except Exception as e:
        log_message("REXA", f"Startup folder error: {e}")


def open_temp_folder():
    try:
        os.startfile(str(Path(tempfile.gettempdir())))
        log_message("REXA", "Opened the Temp folder.")
    except Exception as e:
        log_message("REXA", f"Temp folder error: {e}")


def restart_explorer():
    try:
        subprocess.Popen(["taskkill", "/f", "/im", "explorer.exe"])
        time.sleep(1.0)
        subprocess.Popen(["explorer.exe"])
        log_message("REXA", "Restarted Windows Explorer.")
    except Exception as e:
        log_message("REXA", f"Restart Explorer error: {e}")


def clear_clipboard():
    try:
        root.clipboard_clear()
        root.update()
        log_message("REXA", "Cleared the clipboard.")
    except Exception as e:
        log_message("REXA", f"Clear clipboard error: {e}")


def copy_time_to_clipboard():
    try:
        text = now_text()
        root.clipboard_clear()
        root.clipboard_append(text)
        root.update()
        log_message("REXA", f"Copied the time to clipboard: {text}")
    except Exception as e:
        log_message("REXA", f"Copy time error: {e}")


def copy_date_to_clipboard():
    try:
        text = date_text()
        root.clipboard_clear()
        root.clipboard_append(text)
        root.update()
        log_message("REXA", f"Copied the date to clipboard: {text}")
    except Exception as e:
        log_message("REXA", f"Copy date error: {e}")


def open_downloads_folder():
    open_downloads()


def open_documents_folder():
    open_documents()


def open_appdata_folder():
    try:
        os.startfile(str(Path.home() / "AppData"))
        log_message("REXA", "Opened the AppData folder.")
    except Exception as e:
        log_message("REXA", f"AppData folder error: {e}")


def open_windows_defender():
    try:
        os.startfile("windowsdefender:")
        log_message("REXA", "Opened Windows Security (Defender).")
    except Exception as e:
        log_message(
            "REXA",
            f"Couldn't open Windows Security directly: {e}\n"
            "Trying Windows Update settings instead, where Windows "
            "Security can also be reached."
        )
        open_windows_update()


# ============================================================
# FILE MANAGEMENT
# ============================================================

def create_desktop_folder(name):
    name = name.strip().strip("'\"") or "New Folder"
    try:
        target = Path.home() / "Desktop" / name
        target.mkdir(parents=True, exist_ok=True)
        log_message("REXA", f"Created the folder '{name}' on the Desktop.")
    except Exception as e:
        log_message("REXA", f"Folder create error: {e}")


def move_last_download_to_documents():
    try:
        downloads = Path.home() / "Downloads"
        documents = Path.home() / "Documents"

        files = [f for f in downloads.iterdir() if f.is_file()]
        if not files:
            log_message("REXA", "No files found in the Downloads folder.")
            return

        latest = max(files, key=lambda f: f.stat().st_mtime)
        shutil.move(str(latest), str(documents / latest.name))

        log_message(
            "REXA",
            f"Moved '{latest.name}' to Documents."
        )
    except Exception as e:
        log_message("REXA", f"Move file error: {e}")


def copy_file(source_path, dest_folder=None):
    source_path = source_path.strip().strip("'\"")
    if not source_path:
        return

    try:
        src = Path(source_path).expanduser()
        if not src.is_file():
            log_message("REXA", f"'{source_path}' is not a valid file.")
            return

        target_dir = Path(dest_folder).expanduser() if dest_folder else src.parent
        target_dir.mkdir(parents=True, exist_ok=True)

        stem, suffix = src.stem, src.suffix
        candidate = target_dir / f"{stem} - Copy{suffix}"
        counter = 2

        while candidate.exists():
            candidate = target_dir / f"{stem} - Copy ({counter}){suffix}"
            counter += 1

        shutil.copy2(str(src), str(candidate))

        log_message(
            "REXA",
            f"Copied '{src.name}' to '{candidate.name}'.\n"
            f"Location: {candidate.parent}"
        )
        speak("The file has been copied.")
    except Exception as e:
        log_message("REXA", f"Copy file error: {e}")


def ask_copy_file():
    from tkinter import filedialog

    source_path = filedialog.askopenfilename(
        title="Select file to copy"
    )

    if source_path:
        copy_file(source_path)


def open_screenshots_folder():
    try:
        folder = BASE_DIR / "screenshots"
        folder.mkdir(exist_ok=True)
        os.startfile(str(folder))
        log_message("REXA", "Opened the screenshots folder.")
    except Exception as e:
        log_message("REXA", f"Screenshot folder error: {e}")


def search_pc_for_file(filename):
    filename = filename.strip().strip("'\"")
    if not filename:
        return

    log_message("REXA", f"Searching for '{filename}', this may take a moment...")

    def worker():
        matches = []
        home = Path.home()

        try:
            for root_dir, dirs, files in os.walk(home):
                dirs[:] = [
                    d for d in dirs
                    if d.lower() not in {
                        "windows", "$recycle.bin", "node_modules",
                        "appdata"
                    }
                ]

                for f in files:
                    if fnmatch.fnmatch(f.lower(), f"*{filename.lower()}*"):
                        matches.append(str(Path(root_dir) / f))

                if len(matches) >= 20:
                    break

        except Exception as e:
            log_message("REXA", f"Search error: {e}")
            return

        if matches:
            log_message(
                "REXA",
                f"Found matches for '{filename}':\n" + "\n".join(matches[:20])
            )
        else:
            log_message("REXA", f"Couldn't find any file named '{filename}'.")

    threading.Thread(target=worker, daemon=True).start()


def compress_folder(folder_path):
    folder_path = folder_path.strip().strip("'\"")
    if not folder_path:
        return

    try:
        p = Path(folder_path).expanduser()
        if not p.is_dir():
            log_message("REXA", f"'{folder_path}' is not a valid folder.")
            return

        archive = shutil.make_archive(str(p), "zip", root_dir=str(p))
        log_message("REXA", f"Created the zip:\n{archive}")
    except Exception as e:
        log_message("REXA", f"Compress error: {e}")


def ask_compress_folder():
    folder_path = simpledialog.askstring(
        "Compress folder",
        "Which folder do you want to zip? (give the full path)"
    )
    if folder_path:
        compress_folder(folder_path)


def notepad_type_memo(text):
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    def worker():
        try:
            subprocess.Popen(["notepad.exe"])
            time.sleep(1.0)
            pyautogui.typewrite(text, interval=0.01)
            log_message("REXA", "Typed the memo in Notepad.")
        except Exception as e:
            log_message("REXA", f"Notepad memo error: {e}")

    threading.Thread(target=worker, daemon=True).start()


# ============================================================
# PRODUCTIVITY / TIMERS / TOOLS
# ============================================================

def start_pomodoro(minutes=25):
    log_message("REXA", f"Started a {minutes}-minute Pomodoro timer. \u23F1\uFE0F")
    speak(f"Started a {minutes} minute timer.")

    def worker():
        time.sleep(minutes * 60)
        log_message("REXA", f"\u23F0 Pomodoro done! {minutes} minutes are up — take a break.")
        speak("Your Pomodoro timer is done.")

    threading.Thread(target=worker, daemon=True).start()


def _safe_arithmetic_eval(node):
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.UnaryOp):
        value = _safe_arithmetic_eval(node.operand)
        if isinstance(node.op, ast.USub):
            return -value
        if isinstance(node.op, ast.UAdd):
            return value
    if isinstance(node, ast.BinOp):
        left = _safe_arithmetic_eval(node.left)
        right = _safe_arithmetic_eval(node.right)
        operations = {
            ast.Add: lambda: left + right,
            ast.Sub: lambda: left - right,
            ast.Mult: lambda: left * right,
            ast.Div: lambda: left / right,
            ast.FloorDiv: lambda: left // right,
            ast.Mod: lambda: left % right,
            ast.Pow: lambda: left ** right,
        }
        operation = next((fn for operator, fn in operations.items() if isinstance(node.op, operator)), None)
        if operation is not None:
            result = operation()
            if isinstance(result, (int, float)) and abs(result) <= 1e12:
                return result
    raise ValueError("unsupported arithmetic expression")


def calculator_compute(expression):
    # Only evaluate simple arithmetic safely — no arbitrary eval().
    import re
    cleaned = expression.lower().replace("times", "*").replace(
        "multiplied by", "*"
    ).replace("x", "*").replace("plus", "+").replace(
        "minus", "-"
    ).replace("divided by", "/")

    if not re.fullmatch(r"[0-9\.\+\-\*/\(\)\s]+", cleaned):
        log_message("REXA", "Couldn't understand that calculation, please use numbers.")
        return

    try:
        tree = ast.parse(cleaned, mode="eval")
        allowed = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant,
                   ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv,
                   ast.Mod, ast.Pow, ast.USub, ast.UAdd, ast.Load)
        if any(not isinstance(node, allowed) for node in ast.walk(tree)):
            raise ValueError("only basic arithmetic is allowed")
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and (
                    not isinstance(node.value, (int, float)) or abs(node.value) > 1e12):
                raise ValueError("numbers must be within the supported range")
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
                if not isinstance(node.right, ast.Constant) or not isinstance(node.right.value, (int, float)) or node.right.value > 100:
                    raise ValueError("exponents are limited to 100")
        result = _safe_arithmetic_eval(tree.body)
        log_message("REXA", f"{expression.strip()} = {result}")
        speak(f"The answer is {result}")
    except Exception:
        log_message("REXA", "Couldn't compute that.")


TASK_LIST_FILE = BASE_DIR / "rexa_tasks.txt"
NOTES_FILE = BASE_DIR / "rexa_notes.txt"
REMINDERS_FILE = BASE_DIR / "rexa_reminders.txt"
ROUTINE_FILE = BASE_DIR / "rexa_routine.json"
PROFILE_FILE = BASE_DIR / "rexa_profile.txt"
MISA_PROFILE_FILE = BASE_DIR / "misa_profile.txt"


SENSITIVE_MEMORY_TERMS = (
    "password", "passcode", "api key", "apikey", "token", "secret",
    "credit card", "bank account", "social security", "private key",
    "login", "signin", "sign-in", "checkout", "payment", "messages"
)


def _memory_facts():
    facts = memory.setdefault("facts", {})
    if not isinstance(facts, dict):
        memory["facts"] = {}
        facts = memory["facts"]
    return facts


def _is_sensitive_memory(text):
    lowered = text.lower()
    return any(term in lowered for term in SENSITIVE_MEMORY_TERMS)


def _memory_key(label):
    key = re.sub(r"[^a-z0-9]+", "_", label.lower()).strip("_")
    return key[:80]


def remember_memory_fact(label, value):
    label = label.strip(" .:?!\t\r\n")
    value = value.strip(" .\t\r\n")
    if not label or not value:
        return False
    if _is_sensitive_memory(f"{label} {value}"):
        log_message("REXA", "I won't save passwords, keys, or private financial information.")
        return False

    facts = _memory_facts()
    key = _memory_key(label)
    if key in {"likes", "dislikes"} and key in facts:
        previous = facts[key]
        values = previous if isinstance(previous, list) else [previous]
        if value not in values:
            values.append(value)
        facts[key] = values
    else:
        facts[key] = value
    graph = memory.setdefault("fact_graph", {
        "preferences": {}, "relationships": {}, "active_projects": {}
    })
    lowered = label.lower()
    if any(term in lowered for term in ("like", "dislike", "prefer", "favorite")):
        graph.setdefault("preferences", {})[key] = value
    elif any(term in lowered for term in ("father", "mother", "friend", "relationship")):
        graph.setdefault("relationships", {})[key] = value
    elif any(term in lowered for term in ("project", "study", "work")):
        graph.setdefault("active_projects", {})[key] = value
    save_memory(memory)
    return True


def _memory_text():
    facts = _memory_facts()
    profile = memory.get("user_profile", {})
    graph = memory.get("fact_graph", {})
    if not facts and not profile and not any(graph.values() if isinstance(graph, dict) else []):
        return ""

    lines = []
    for key, value in profile.items():
        lines.append(f"profile {key}: {value}")
    for key, value in facts.items():
        label = key.replace("_", " ")
        if isinstance(value, list):
            value = ", ".join(str(item) for item in value)
        lines.append(f"{label}: {value}")
    for category in ("preferences", "relationships", "active_projects"):
        values = graph.get(category, {}) if isinstance(graph, dict) else {}
        if isinstance(values, dict):
            for key, value in list(values.items())[:20]:
                lines.append(f"{category} {key}: {value}")
    return "\n".join(lines)[:6000]


def memory_summary_for_ai():
    text = _memory_text()
    return f"The user's saved memory:\n{text}" if text else ""


def relevant_memory_summary_for_ai(query):
    matches = _retrieve_vector_memory(query, limit=3)
    if not matches:
        return ""
    return "Relevant past conversation memory:\n" + "\n".join(
        f"- {item}" for item in matches
    )


def show_memory():
    text = _memory_text()
    if not text:
        log_message("REXA", "I don't have any saved memory about you yet.")
        return
    log_message("REXA", "YOUR MEMORY\n\n" + text)


def clear_memory():
    memory["facts"] = {}
    memory["activity"] = []
    save_memory(memory)
    if PROFILE_FILE.exists():
        forget_profile()
    else:
        log_message("REXA", "I've forgotten everything saved about you.")


def _activity_enabled():
    return memory.get("activity_enabled", True) is True


def _safe_activity_url(url):
    parsed = urllib.parse.urlparse(url or "")
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        return ""
    lowered = (parsed.netloc + parsed.path).lower()
    if any(term in lowered for term in SENSITIVE_MEMORY_TERMS):
        return ""
    return urllib.parse.urlunparse((parsed.scheme, parsed.netloc, parsed.path, "", "", ""))


def record_web_activity(url, title="", action="opened", query=""):
    if not _activity_enabled():
        return
    safe_url = _safe_activity_url(url)
    if not safe_url:
        return

    entry = {
        "date": dt.date.today().isoformat(),
        "url": safe_url,
        "site": urllib.parse.urlparse(safe_url).netloc,
        "title": (title or "")[:160],
        "action": action[:40],
    }
    if query and not _is_sensitive_memory(query):
        entry["query"] = query[:160]

    activities = memory.setdefault("activity", [])
    if not isinstance(activities, list):
        activities = []
        memory["activity"] = activities
    if activities and all(activities[-1].get(key) == entry.get(key) for key in ("url", "action", "query")):
        return
    activities.append(entry)
    memory["activity"] = activities[-500:]
    save_memory(memory)


def _yesterday_activity():
    yesterday = (dt.date.today() - dt.timedelta(days=1)).isoformat()
    return [item for item in memory.get("activity", []) if item.get("date") == yesterday]


def show_yesterday_activity():
    items = _yesterday_activity()
    if not items:
        log_message("REXA", "I have no saved activity from yesterday.")
        return
    lines = [f"{item.get('action', 'visited').title()} {item.get('site', 'a site')}" +
             (f" ({item['query']})" if item.get("query") else "") for item in items]
    log_message("REXA", "YESTERDAY'S ACTIVITY\n\n" + "\n".join(lines))


def forget_yesterday_activity():
    yesterday = (dt.date.today() - dt.timedelta(days=1)).isoformat()
    memory["activity"] = [
        item for item in memory.get("activity", []) if item.get("date") != yesterday
    ]
    save_memory(memory)
    log_message("REXA", "Yesterday's browsing activity has been forgotten.")


def set_activity_memory(enabled):
    memory["activity_enabled"] = enabled
    save_memory(memory)
    log_message(
        "REXA",
        "Browsing activity memory is " + ("on." if enabled else "off.")
    )


def proactive_web_check(driver):
    if not _activity_enabled():
        return
    try:
        url = _safe_activity_url(driver.current_url)
        if not url:
            return
        site = urllib.parse.urlparse(url).netloc.lower()
        key = f"{url}|{dt.date.today().isoformat()}"
        if memory.get("last_proactive_web_check") == key:
            return
        memory["last_proactive_web_check"] = key
        record_web_activity(url, driver.title, "visited")
        prior = [item for item in _yesterday_activity() if item.get("site") == site]
        if prior:
            detail = prior[-1].get("query") or prior[-1].get("title") or "this site"
            question = f"You visited {site} yesterday and were looking at {detail}. Are you continuing?"
        elif "youtube.com" in site:
            question = "You're on YouTube. Are you looking for something to watch?"
        elif any(word in site for word in ("amazon", "ebay", "walmart", "shop")):
            question = "Are you checking something to buy?"
        elif any(word in site for word in ("learn", "course", "edu", "docs")):
            question = "Are you studying something here?"
        else:
            return
        log_message("REXA", question)
        speak(question)
        save_memory(memory)
    except Exception:
        pass


def detect_mood(text):
    lowered = text.lower()
    moods = {
        "bored": ("bored", "nothing to do"),
        "frustrated": ("frustrated", "annoyed", "doesn't work", "not working"),
        "tired": ("tired", "exhausted", "sleepy"),
        "stressed": ("stressed", "overwhelmed", "too much"),
        "excited": ("excited", "amazing", "can't wait"),
        "happy": ("happy", "great news", "feeling good"),
        "confused": ("confused", "don't understand", "what does this mean"),
        "angry": ("angry", "furious", "hate this"),
        "calm": ("calm", "relaxed", "peaceful"),
    }
    for mood, phrases in moods.items():
        if any(phrase in lowered for phrase in phrases):
            return mood
    return "uncertain"


def mood_context(text):
    mood = detect_mood(text)
    if mood == "uncertain":
        return "The user's emotional tone is uncertain; do not assume how they feel."
    return f"The user's message may sound {mood}. Acknowledge this cautiously without claiming certainty."


def forget_memory_item(query):
    query = query.strip().strip("'\"")
    facts = _memory_facts()
    matches = [
        key for key, value in facts.items()
        if query.lower() in key.lower() or query.lower() in str(value).lower()
    ]
    for key in matches:
        del facts[key]
    save_memory(memory)
    log_message(
        "REXA",
        "I forgot that memory."
        if matches else "I couldn't find that memory."
    )


def learn_about_user(text):
    """Save only explicit preferences, habits, identity, or long-term facts."""
    cleaned = text.strip().strip(" .?!\t\r\n")
    patterns = [
        (r"my favorite ([\w ]+?) is (.+)", "favorite_{}"),
        (r"i usually (.+)", "habit"),
        (r"i prefer (.+)", "preference"),
        (r"i like (.+)", "likes"),
        (r"i don't like (.+)", "dislikes"),
        (r"i use (.+)", "uses"),
        (r"remember that (.+)", "note"),
        (r"remember (.+)", "note"),
    ]
    for pattern, label_template in patterns:
        match = re.fullmatch(pattern, cleaned, flags=re.IGNORECASE)
        if not match:
            continue
        if label_template == "favorite_{}":
            label = label_template.format(match.group(1))
            value = match.group(2)
        else:
            label = label_template
            value = match.group(1)
        if remember_memory_fact(label, value):
            log_message("REXA", f"Got it, Boss. I'll remember that {cleaned.lower()}.")
            speak("Got it, Boss. I'll remember that.")
        return True
    return False


def handle_memory_command(text):
    low = text.casefold().strip()
    normalized = re.sub(r"[?!.,]+$", "", low).strip()
    normalized = re.sub(r"^(?:hey\s+)?(?:jarvis|rexa)\s*[,:\-]?\s*", "", normalized)
    if normalized in {
        "can you see what i am doing now",
        "can you see what i'm doing now",
        "what am i doing now",
        "what am i doing",
        "আমি এখন কী করছি",
        "আমি কি করছি",
        "আমি কী করছি",
    }:
        announce_active_context()
        return True

    verification = extract_after(text, [
        "verify answer ", "check answer ", "যাচাই করো ",
    ])
    if verification and "|" in verification:
        submitted, expected = verification.split("|", 1)
        verify_user_input(submitted, expected)
        return True

    if matches_any(low, ["forget everything about me", "forget all my memory", "clear my memory"]):
        clear_memory()
        return True

    forgotten = extract_after(text, ["forget that ", "forget about "])
    if forgotten:
        forget_memory_item(forgotten)
        return True

    if matches_any(low, [
        "what do you know about me", "show my memory", "show my memories",
        "what do you remember about my projects",
        "আমার সম্পর্কে কী মনে রেখেছো", "আমার প্রজেক্ট সম্পর্কে কী মনে রেখেছো",
        "update my memory",
    ]):
        show_memory()
        return True

    favorite_question = re.search(r"(?:what is|what's) my favorite ([\w ]+?)[?!.]*$", low)
    if favorite_question:
        key = _memory_key(f"favorite_{favorite_question.group(1)}")
        value = _memory_facts().get(key)
        log_message("REXA", f"Your favorite {favorite_question.group(1)} is {value}, Boss." if value else "I don't know that yet.")
        return True

    remembered = extract_after(text, ["remember that "])
    if remembered:
        return learn_about_user("remember that " + remembered)
    return learn_about_user(text)


def _load_profile_lines(path):
    if not path or not path.exists():
        return {}
    profile = {}
    try:
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or ":" not in line:
                continue
            key, value = line.split(":", 1)
            key = key.strip().lower()
            value = value.strip()
            if key and value:
                profile[key] = value
    except Exception:
        return {}
    return profile


def _load_profile():
    """Read the user's profile from both the assistant profile and the legacy MISA profile file."""
    profile = {}

    if MISA_PROFILE_FILE.exists():
        profile.update(_load_profile_lines(MISA_PROFILE_FILE))

    if PROFILE_FILE.exists():
        profile.update(_load_profile_lines(PROFILE_FILE))

    if profile:
        _save_profile(profile)

    return profile


def _save_profile(profile):
    try:
        lines = [f"{k}: {v}" for k, v in profile.items() if v]
        PROFILE_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except Exception:
        pass


def set_profile_field(field, value):
    value = value.strip().strip("'\"")
    if not value:
        return

    profile = _load_profile()
    profile[field] = value
    memory.setdefault("user_profile", {})[field] = value
    _save_profile(profile)
    remember_memory_fact(field, value)


def add_profile_note(note_text):
    note_text = note_text.strip().strip("'\"")
    if not note_text:
        return

    profile = _load_profile()
    existing_notes = profile.get("notes", "")
    combined = (existing_notes + "; " + note_text) if existing_notes else note_text
    # Keep a large bounded history while preserving the plain-text profile format.
    parts = [p.strip() for p in combined.split(";") if p.strip()]
    profile["notes"] = "; ".join(parts[-1000:])
    _save_profile(profile)
    remember_memory_fact("notes", note_text)


def _normalize_profile_notes(notes):
    if not notes:
        return ""
    parts = []
    for chunk in str(notes).split(";"):
        clean = chunk.strip()
        clean = re.sub(r"^(?:my\s+)?(?:father|mother|best friend|your name)\b.*?is\s*", "", clean, flags=re.IGNORECASE)
        if clean and clean.lower() not in {"na", "n/a", "none", "a", ""}:
            parts.append(clean)
    cleaned = "; ".join(parts[-20:])
    return cleaned


def _clean_profile(profile):
    cleaned = {}
    for key, value in (profile or {}).items():
        if not isinstance(value, str):
            value = str(value)
        value = value.strip().strip("'\"")
        if not value or value.lower() in {"a", "na", "n/a", "none"}:
            continue
        cleaned[key] = value

    if cleaned.get("name", "").lower() in {"rexa", "assistant", "ai"}:
        cleaned.pop("name", None)

    name = cleaned.get("name")
    if name and re.search(r"\b(?:my name is|your name is)\b", name, flags=re.IGNORECASE):
        cleaned.pop("name", None)

    return cleaned


def user_identity_summary_for_ai():
    profile = _clean_profile(_load_profile())
    if not profile:
        return ""

    bits = []
    name = profile.get("name")
    if name:
        bits.append(f"The user's name is {name}. Call them {name} in replies.")

    father_name = profile.get("father") or profile.get("father_name")
    if father_name:
        bits.append(f"Their father is {father_name}.")

    mother_name = profile.get("mother") or profile.get("mother_name")
    if mother_name:
        bits.append(f"Their mother is {mother_name}.")

    friend_name = profile.get("best_friend") or profile.get("friend")
    if friend_name:
        bits.append(f"Their best friend is {friend_name}.")

    return " ".join(bits)


def profile_summary_for_ai():
    """Builds a short line for the Gemini prompt so REXA can remember
    who it's talking to. Returns '' if nothing is known yet."""
    profile = _clean_profile(_load_profile())

    if not profile:
        return ""

    bits = []
    if profile.get("name"):
        bits.append(f"The user's name is {profile['name']}.")
    if profile.get("study"):
        bits.append(f"They are studying/working on: {profile['study']}.")

    notes = _normalize_profile_notes(profile.get("notes"))
    if notes:
        bits.append(f"Things they've shared before: {notes}.")

    father_names = re.findall(r"father(?:'s)? name is ([a-zA-Z][a-zA-Z\s-]+)", notes, flags=re.IGNORECASE)
    mother_names = re.findall(r"mother(?:'s)? name is ([a-zA-Z][a-zA-Z\s-]+)", notes, flags=re.IGNORECASE)
    friend_names = re.findall(r"best friend is ([a-zA-Z][a-zA-Z\s-]+)", notes, flags=re.IGNORECASE)

    if father_names:
        father_name = father_names[-1].strip()
        bits.append(f"Their father is {father_name}.")
    if mother_names:
        mother_name = mother_names[-1].strip()
        bits.append(f"Their mother is {mother_name}.")
    if friend_names:
        friend_name = friend_names[-1].strip()
        bits.append(f"Their best friend is {friend_name}.")

    return " ".join(bits)


def show_profile():
    profile = _load_profile()

    if not profile:
        log_message(
            "REXA",
            "I don't know much about you yet! Tell me things like "
            "'call me <name>' or 'remember I'm studying <subject>' "
            "and I'll keep it in mind."
        )
        return

    lines = ["WHAT I KNOW ABOUT YOU\n"]
    if profile.get("name"):
        lines.append(f"Name: {profile['name']}")
    if profile.get("study"):
        lines.append(f"Studying: {profile['study']}")
    if profile.get("notes"):
        lines.append(f"Notes: {profile['notes']}")

    log_message("REXA", "\n".join(lines))


def forget_profile():
    try:
        if PROFILE_FILE.exists():
            PROFILE_FILE.unlink()
        log_message("REXA", "Okay, I've forgotten everything about you.")
    except Exception as e:
        log_message("REXA", f"Couldn't clear your profile: {e}")


def add_task(task_text):
    task_text = task_text.strip()
    if not task_text:
        return

    try:
        with open(TASK_LIST_FILE, "a", encoding="utf-8") as f:
            f.write(f"[ ] {task_text}\n")
        log_message("REXA", f"Added to your task list: {task_text}")
    except Exception as e:
        log_message("REXA", f"Task add error: {e}")


def show_tasks():
    try:
        if not TASK_LIST_FILE.exists():
            log_message("REXA", "Your task list is empty right now.")
            return

        content = TASK_LIST_FILE.read_text(encoding="utf-8").strip()
        log_message("REXA", "TASK LIST\n\n" + (content or "Empty."))
    except Exception as e:
        log_message("REXA", f"Task list error: {e}")


def open_google_calendar_new_event(title, when_text=""):
    try:
        url = (
            "https://calendar.google.com/calendar/render?action=TEMPLATE"
            "&text=" + urllib.parse.quote(title)
        )
        if when_text:
            url += "&details=" + urllib.parse.quote(when_text)

        safe_open(url)
        log_message(
            "REXA",
            f"Opened a new Google Calendar event draft: {title}\n"
            "Set the date/time yourself and click Save."
        )
    except Exception as e:
        log_message("REXA", f"Calendar error: {e}")


def open_google_calendar():
    safe_open("https://calendar.google.com/")
    log_message("REXA", "Opened Google Calendar — you can check today's schedule here.")


def dictate_type_text(text):
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.typewrite(text, interval=0.01)
        log_message("REXA", f"Typed: {text}")
    except Exception as e:
        log_message("REXA", f"Dictate error: {e}")


def read_clipboard_aloud():
    try:
        text = root.clipboard_get()
    except Exception:
        text = ""

    if not text.strip():
        log_message(
            "REXA",
            "I can't read text straight off the screen (that needs OCR), "
            "but if you copy the text (Ctrl+C) I can read it aloud."
        )
        return

    log_message("REXA", text)
    speak(text)


def convert_currency_query(text):
    run_ai(text)

# ============================================================
# SCREENSHOT / RECORDING / CAMERA / TRANSLATE
# ============================================================

def screenshot_active_window():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("alt", "printscreen")
        time.sleep(0.4)

        if ImageGrab is None:
            log_message(
                "REXA",
                "The active window was copied to the clipboard, but to "
                "save it install:\npip install pillow"
            )
            return

        img = ImageGrab.grabclipboard()

        if img is None:
            log_message("REXA", "Couldn't take a screenshot of the active window.")
            return

        folder = BASE_DIR / "screenshots"
        folder.mkdir(exist_ok=True)

        filename = folder / (
            "rexa_window_"
            + dt.datetime.now().strftime("%Y%m%d_%H%M%S")
            + ".png"
        )

        img.save(filename)
        log_message("REXA", f"Active window screenshot saved:\n{filename}")

    except Exception as e:
        log_message("REXA", f"Window screenshot error: {e}")


def toggle_screen_recording():
    if pyautogui is None:
        log_message("REXA", "For this, install: pip install pyautogui")
        return

    try:
        pyautogui.hotkey("win", "alt", "r")
        log_message(
            "REXA",
            "Toggled Xbox Game Bar screen recording (it will save to "
            "your Videos/Captures folder)."
        )
    except Exception as e:
        log_message("REXA", f"Screen recording error: {e}")


def snap_camera_photo():
    open_camera()

    if pyautogui is None:
        return

    def worker():
        time.sleep(2.5)
        try:
            pyautogui.press("space")
            log_message(
                "REXA",
                "Tried to take a photo in the Camera app (may not work "
                "if the app hasn't fully opened)."
            )
        except Exception as e:
            log_message("REXA", f"Camera snap error: {e}")

    threading.Thread(target=worker, daemon=True).start()


def translate_clipboard_to_bengali():
    try:
        text = root.clipboard_get()
    except Exception:
        text = ""

    if not text.strip():
        log_message(
            "REXA",
            "I couldn't find any selected/copied text — please copy the "
            "text with Ctrl+C first."
        )
        return

    run_ai(f"Translate this text into Bengali:\n{text}")


# ============================================================
# NEW: PERSONAL AI ASSISTANT COMMANDS (21 new features)
# ============================================================

def _parse_reminder_minutes(when_text):
    """Very small helper: pulls a number of minutes out of text like
    '10 minutes' / 'in 5 min' / '1 hour'. Defaults to 10 minutes."""
    low = when_text.lower()
    digits = "".join(ch for ch in low if ch.isdigit())
    minutes = int(digits) if digits else 10

    if "hour" in low:
        minutes = minutes * 60 if digits else 60

    return max(1, minutes)


def set_reminder(reminder_text, when_text="10 minutes"):
    reminder_text = reminder_text.strip()
    if not reminder_text:
        return

    minutes = _parse_reminder_minutes(when_text)
    fire_time = dt.datetime.now() + dt.timedelta(minutes=minutes)

    try:
        with open(REMINDERS_FILE, "a", encoding="utf-8") as f:
            f.write(
                f"[{fire_time.strftime('%Y-%m-%d %H:%M')}] {reminder_text}\n"
            )
    except Exception:
        pass

    log_message(
        "REXA",
        f"Reminder set: '{reminder_text}' in {minutes} minute(s) "
        f"(around {fire_time.strftime('%I:%M %p')})."
    )
    speak(f"Okay, I'll remind you about {reminder_text}.")

    def worker():
        time.sleep(minutes * 60)
        log_message("REXA", f"\u23F0 Reminder: {reminder_text}")
        speak(f"Reminder: {reminder_text}")

    threading.Thread(target=worker, daemon=True).start()


def _load_routine():
    if not ROUTINE_FILE.exists():
        return {}

    try:
        data = json.loads(ROUTINE_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _save_routine(routine):
    try:
        ROUTINE_FILE.write_text(
            json.dumps(routine, indent=2),
            encoding="utf-8"
        )
    except Exception as e:
        log_message("REXA", f"Routine save error: {e}")


def set_routine(routine_text, interval_text="7 minutes"):
    routine_text = routine_text.strip().strip("'\"")
    if not routine_text:
        log_message("REXA", "Tell me what routine you want me to check.")
        return

    minutes = _parse_reminder_minutes(interval_text)
    if minutes not in {7, 9}:
        log_message("REXA", "Routine check-ins can be every 7 or 9 minutes.")
        return

    routine = {
        "activity": routine_text,
        "interval_minutes": minutes,
        "next_check": (dt.datetime.now() + dt.timedelta(minutes=minutes)).timestamp(),
        "awaiting_answer": False,
    }
    _save_routine(routine)
    log_message(
        "REXA",
        f"Routine set: {routine_text}. I'll ask whether you've done it every "
        f"{minutes} minutes."
    )
    speak(f"Routine set. I'll check on {routine_text} every {minutes} minutes.")


def show_routine():
    routine = _load_routine()
    if not routine.get("activity"):
        log_message("REXA", "No routine is set.")
        return

    log_message(
        "REXA",
        f"ROUTINE\n\n{routine['activity']}\n"
        f"Check-in: every {routine.get('interval_minutes', 7)} minutes"
    )


def clear_routine():
    try:
        if ROUTINE_FILE.exists():
            ROUTINE_FILE.unlink()
        log_message("REXA", "Routine check-ins are off.")
    except Exception as e:
        log_message("REXA", f"Couldn't stop the routine: {e}")


def routine_check_loop():
    if yt_driver is not None:
        proactive_web_check(yt_driver)

    routine = _load_routine()
    activity = routine.get("activity")
    if activity:
        now = dt.datetime.now().timestamp()
        next_check = float(routine.get("next_check", now + 420))
        if now >= next_check:
            interval = int(routine.get("interval_minutes", 7))
            routine["next_check"] = (dt.datetime.now() + dt.timedelta(minutes=interval)).timestamp()
            routine["awaiting_answer"] = True
            _save_routine(routine)
            question = f"Have you done {activity}? What are you doing now?"
            log_message("REXA", question)
            speak(question)

    try:
        root.after(30000, routine_check_loop)
    except tk.TclError:
        pass


def show_reminders():
    try:
        if not REMINDERS_FILE.exists():
            log_message("REXA", "You don't have any reminders saved yet.")
            return

        content = REMINDERS_FILE.read_text(encoding="utf-8").strip()
        log_message("REXA", "REMINDERS\n\n" + (content or "Empty."))
    except Exception as e:
        log_message("REXA", f"Reminders error: {e}")


def add_note(note_text):
    note_text = note_text.strip()
    if not note_text:
        return

    try:
        with open(NOTES_FILE, "a", encoding="utf-8") as f:
            f.write(f"- {note_text}\n")
        log_message("REXA", f"Saved the note: {note_text}")
    except Exception as e:
        log_message("REXA", f"Note add error: {e}")


def show_notes():
    try:
        if not NOTES_FILE.exists():
            log_message("REXA", "You don't have any notes saved yet.")
            return

        content = NOTES_FILE.read_text(encoding="utf-8").strip()
        log_message("REXA", "NOTES\n\n" + (content or "Empty."))
    except Exception as e:
        log_message("REXA", f"Notes error: {e}")


def clear_notes():
    try:
        if NOTES_FILE.exists():
            NOTES_FILE.unlink()
        log_message("REXA", "Cleared all your notes.")
    except Exception as e:
        log_message("REXA", f"Clear notes error: {e}")


def roll_dice():
    result = random.randint(1, 6)
    log_message("REXA", f"\U0001F3B2 You rolled a {result}.")
    speak(f"You rolled a {result}.")


def flip_coin():
    result = random.choice(["Heads", "Tails"])
    log_message("REXA", f"\U0001FA99 {result}!")
    speak(result)


def tell_joke():
    run_ai("Tell me a short, clean, original joke.")


def define_word(word):
    word = word.strip()
    if not word:
        return
    safe_open(
        "https://www.google.com/search?q=define+"
        + urllib.parse.quote_plus(word)
    )
    log_message("REXA", f"Opened the definition for: {word}")


def convert_currency_dedicated(query):
    query = query.strip()
    if not query:
        safe_open("https://www.xe.com/currencyconverter/")
        log_message("REXA", "Opened the currency converter.")
        return

    safe_open(
        "https://www.google.com/search?q="
        + urllib.parse.quote_plus(query)
    )
    log_message("REXA", f"Looked up the currency conversion for: {query}")


def convert_units(query):
    run_ai(f"Convert this and show the result clearly: {query}")


def check_stock_price(symbol):
    symbol = symbol.strip()
    if not symbol:
        return
    safe_open(
        "https://www.google.com/search?q="
        + urllib.parse.quote_plus(symbol + " stock price")
    )
    log_message("REXA", f"Looked up the stock price for: {symbol}")


def check_crypto_price(coin):
    coin = coin.strip()
    if not coin:
        safe_open("https://coinmarketcap.com/")
        log_message("REXA", "Opened CoinMarketCap.")
        return

    safe_open(
        "https://www.google.com/search?q="
        + urllib.parse.quote_plus(coin + " price")
    )
    log_message("REXA", f"Looked up the price for: {coin}")


def open_maps():
    safe_open("https://www.google.com/maps")
    log_message("REXA", "Opened Google Maps.")


def _keyboard_action(action_name, action, response=None):
    """Run a pyautogui action without allowing an input command to crash the UI."""
    try:
        if pyautogui is None:
            log_message("REXA", "Keyboard control needs: pip install pyautogui.")
            return
        action()
        if response:
            log_message("REXA", response)
    except Exception as exc:
        log_message("REXA", f"{action_name} error: {exc}")


def type_active_text(value):
    """Type text into the currently focused application."""
    value = (value or "").strip()
    if not value:
        log_message("REXA", "Please say or type some text after 'type'.")
        return
    _keyboard_action("Typing", lambda: pyautogui.write(value, interval=0.01),
                     "Typed the requested text.")


def announce_current_time():
    try:
        answer = ("এখন সময় " if state.get("language_mode") == "bengali" else "The time is ") + now_text()
        log_message("REXA", answer)
        speak(answer)
    except Exception as exc:
        log_message("REXA", f"Time announcement error: {exc}")


def announce_current_date():
    try:
        answer = ("আজকের তারিখ " if state.get("language_mode") == "bengali" else "Today is ") + date_text()
        log_message("REXA", answer)
        speak(answer)
    except Exception as exc:
        log_message("REXA", f"Date announcement error: {exc}")


def open_gmail_web():
    try:
        safe_open("https://mail.google.com/")
        log_message("REXA", "Opened Gmail.")
    except Exception as exc:
        log_message("REXA", f"Gmail opening error: {exc}")


def open_chatgpt_web():
    try:
        safe_open("https://chatgpt.com/")
        log_message("REXA", "Opened ChatGPT.")
    except Exception as exc:
        log_message("REXA", f"ChatGPT opening error: {exc}")


def find_location_on_map(location):
    try:
        location = (location or "").strip()
        if not location:
            log_message("REXA", "Please provide a location after 'find on map'.")
            return
        safe_open(
            "https://www.google.com/maps/search/?api=1&query="
            + urllib.parse.quote_plus(location)
        )
        log_message("REXA", f"Searching Google Maps for: {location}")
    except Exception as exc:
        log_message("REXA", f"Map search error: {exc}")


def translate_text_to_bengali(value):
    try:
        value = (value or "").strip()
        if not value:
            log_message("REXA", "Please provide text after 'translate'.")
            return
        safe_open(
            "https://translate.google.com/?sl=auto&tl=bn&text="
            + urllib.parse.quote(value)
        )
        log_message("REXA", "Opened Google Translate for Bengali translation.")
    except Exception as exc:
        log_message("REXA", f"Translation opening error: {exc}")


def get_directions(destination):
    destination = destination.strip()
    if not destination:
        return
    safe_open(
        "https://www.google.com/maps/dir/?api=1&destination="
        + urllib.parse.quote_plus(destination)
    )
    log_message("REXA", f"Opened directions to: {destination}")


def quote_of_the_day():
    run_ai("Give me one short, original motivational quote for today.")


def search_amazon(query):
    query = query.strip()
    if not query:
        return
    safe_open(
        "https://www.amazon.com/s?k="
        + urllib.parse.quote_plus(query)
    )
    log_message("REXA", f"Searched Amazon for: {query}")


def open_github():
    safe_open("https://github.com/")
    log_message("REXA", "Opened GitHub.")


def open_slack():
    try:
        os.startfile("slack:")
        log_message("REXA", "Opened Slack.")
    except Exception:
        safe_open("https://slack.com/signin")
        log_message("REXA", "Opened Slack Web.")


def open_teams():
    try:
        os.startfile("msteams:")
        log_message("REXA", "Opened Microsoft Teams.")
    except Exception:
        safe_open("https://teams.microsoft.com/")
        log_message("REXA", "Opened Teams Web.")


def open_linkedin():
    safe_open("https://www.linkedin.com/")
    log_message("REXA", "Opened LinkedIn.")


def open_notion():
    safe_open("https://www.notion.so/")
    log_message("REXA", "Opened Notion.")


def open_canva():
    safe_open("https://www.canva.com/")
    log_message("REXA", "Opened Canva.")


def open_dropbox():
    safe_open("https://www.dropbox.com/")
    log_message("REXA", "Opened Dropbox.")


def open_outlook():
    safe_open("https://outlook.live.com/")
    log_message("REXA", "Opened Outlook.")


def web_search(query):
    query = query.strip()
    if not query:
        return
    safe_open("https://www.google.com/search?q=" + urllib.parse.quote_plus(query))
    log_message("REXA", f"Searched the web for: {query}")


class _VisibleTextParser(HTMLParser):
    """Extract readable page text without requiring BeautifulSoup."""

    def __init__(self):
        super().__init__()
        self.parts = []
        self._hidden = 0

    def handle_starttag(self, tag, attrs):
        if tag.lower() in {"script", "style", "noscript", "svg"}:
            self._hidden += 1

    def handle_endtag(self, tag):
        if tag.lower() in {"script", "style", "noscript", "svg"} and self._hidden:
            self._hidden -= 1

    def handle_data(self, data):
        if not self._hidden:
            value = re.sub(r"\s+", " ", data).strip()
            if value:
                self.parts.append(value)


def summarize_url(url):
    """Fetch and summarize a public URL asynchronously with a 15-minute cache."""
    url = (url or "").strip().strip("<>")
    if not urllib.parse.urlparse(url).scheme:
        url = "https://" + url
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        log_message("REXA", "[ALERT] Please provide a valid public URL.")
        return

    def worker():
        try:
            now = time.monotonic()
            cached = web_cache.get(url)
            if cached and now - cached["time"] < WEB_CACHE_TTL_SECONDS:
                text = cached["text"]
            else:
                if requests is None:
                    raise RuntimeError("URL summarization needs the requests package.")
                response = requests.get(
                    url,
                    headers={"User-Agent": "REXA-JARVIS/1.0"},
                    timeout=15,
                )
                response.raise_for_status()
                parser = _VisibleTextParser()
                parser.feed(response.text)
                text = " ".join(parser.parts)[:12000]
                web_cache[url] = {"time": now, "text": text}
            if not text:
                raise RuntimeError("The page did not contain readable text.")
            run_ai(
                "Summarize this webpage in one to three concise sentences. "
                f"URL: {url}\nPage text:\n{text}"
            )
        except Exception as exc:
            log_message("REXA", f"[ALERT] Web summary failed: {exc}")

    threading.Thread(target=worker, name="REXA-Web-Summary", daemon=True).start()


def weather_in_city(city):
    city = city.strip()
    if not city:
        return
    run_ai(f"What is the current weather in {city}?")


def world_clock(city):
    city = city.strip()
    if not city:
        return
    safe_open(
        "https://www.google.com/search?q=time+in+"
        + urllib.parse.quote_plus(city)
    )
    log_message("REXA", f"Looked up the current time in {city}.")


def calculate_age(birth_year_text):
    digits = "".join(ch for ch in birth_year_text if ch.isdigit())
    if not digits or len(digits) < 4:
        log_message("REXA", "Please give a 4-digit birth year, e.g. 'how old is someone born in 1998'.")
        return

    birth_year = int(digits[:4])
    current_year = dt.datetime.now().year
    age = current_year - birth_year

    if age < 0 or age > 130:
        log_message("REXA", f"'{birth_year}' doesn't look like a valid birth year.")
        return

    answer = f"Someone born in {birth_year} is about {age} years old this year."
    log_message("REXA", answer)
    speak(answer)


def generate_password(length_text=""):
    import string as _string

    digits = "".join(ch for ch in length_text if ch.isdigit())
    length = int(digits) if digits else 12
    length = max(6, min(64, length))

    alphabet = _string.ascii_letters + _string.digits + "!@#$%^&*"
    password = "".join(random.SystemRandom().choice(alphabet) for _ in range(length))

    log_message("REXA", f"Generated password ({length} characters):\n{password}")

    try:
        root.clipboard_clear()
        root.clipboard_append(password)
        root.update()
        log_message("REXA", "Copied it to your clipboard.")
    except Exception:
        pass


def water_reminder(interval_text="60 minutes"):
    minutes = _parse_reminder_minutes(interval_text)

    log_message(
        "REXA",
        f"Okay, I'll remind you to drink water every {minutes} minute(s) "
        "while REXA stays open."
    )
    speak("Water reminders are on.")

    def worker():
        while True:
            time.sleep(minutes * 60)
            log_message("REXA", "\U0001F4A7 Time to drink some water!")
            speak("Time to drink some water.")

    threading.Thread(target=worker, daemon=True).start()


def mark_task_done(task_text):
    task_text = task_text.strip()
    if not task_text or not TASK_LIST_FILE.exists():
        log_message("REXA", "I couldn't find that task in your list.")
        return

    try:
        lines = TASK_LIST_FILE.read_text(encoding="utf-8").splitlines()
        found = False
        new_lines = []

        for line in lines:
            if not found and task_text.lower() in line.lower() and line.strip().startswith("[ ]"):
                new_lines.append(line.replace("[ ]", "[x]", 1))
                found = True
            else:
                new_lines.append(line)

        TASK_LIST_FILE.write_text("\n".join(new_lines) + "\n", encoding="utf-8")

        if found:
            log_message("REXA", f"Marked '{task_text}' as done. \u2705")
        else:
            log_message("REXA", f"Couldn't find an open task matching '{task_text}'.")
    except Exception as e:
        log_message("REXA", f"Task update error: {e}")


def clear_tasks():
    try:
        if TASK_LIST_FILE.exists():
            TASK_LIST_FILE.unlink()
        log_message("REXA", "Cleared your whole task list.")
    except Exception as e:
        log_message("REXA", f"Clear tasks error: {e}")


def random_fact():
    run_ai("Tell me one short, interesting, true random fact.")


SOMOY_NEWS_RSS_URL = (
    "https://news.google.com/rss/search?q="
    + urllib.parse.quote_plus("site:somoynews.tv")
    + "&hl=bn&gl=BD&ceid=BD:bn"
)
SOMOY_LIVE_URL = "https://www.youtube.com/@SomoyTV/live"


def _clean_news_text(value):
    value = html.unescape(re.sub(r"<[^>]+>", " ", value or ""))
    return re.sub(r"\s+", " ", value).strip()


def _fetch_somoy_news():
    from urllib.request import Request, urlopen
    request = Request(SOMOY_NEWS_RSS_URL, headers={"User-Agent": "REXA/1.0"})
    with urlopen(request, timeout=8) as response:
        payload = response.read()

    root = ET.fromstring(payload)
    items = []
    for item in root.findall(".//item")[:5]:
        title = _clean_news_text(item.findtext("title", ""))
        if title:
            items.append(title)
    return items


def somoy_tv_news():
    """Fetch and announce the five latest Somoy TV headlines without blocking Tkinter."""
    log_message("REXA", "সময় টিভির সর্বশেষ খবর আনা হচ্ছে...")
    speak("সময় টিভির সর্বশেষ খবর আনা হচ্ছে।", voice_name="bn-BD-NabanitaNeural")

    def worker():
        try:
            items = _fetch_somoy_news()
            if not items:
                raise RuntimeError("RSS feed returned no headlines")

            headlines = "\n".join(
                f"{index}. {title}" for index, title in enumerate(items, 1)
            )
            log_message("REXA", "সময় টিভির সর্বশেষ ৫টি সংবাদ:\n" + headlines)
            speech = "। ".join(
                f"{index} নম্বর খবর: {title}" for index, title in enumerate(items, 1)
            )
            speak(speech, voice_name="bn-BD-NabanitaNeural")
        except (OSError, urllib.error.URLError, ET.ParseError, RuntimeError, ValueError) as exc:
            log_message("REXA", f"সময় টিভির খবর আনা যায়নি: {exc}")
            speak("সময় টিভির খবর এখন পাওয়া যাচ্ছে না।", voice_name="bn-BD-NabanitaNeural")

    threading.Thread(target=worker, daemon=True).start()


def news_headlines(topic=""):
    topic = topic.strip()
    if topic:
        safe_open(
            "https://news.google.com/search?q="
            + urllib.parse.quote_plus(topic)
        )
        log_message("REXA", f"Opened the latest news on: {topic}")
    else:
        safe_open("https://news.google.com/")
        log_message("REXA", "Opened today's top headlines.")


def search_recipe(dish):
    dish = dish.strip()
    if not dish:
        return
    safe_open(
        "https://www.google.com/search?q="
        + urllib.parse.quote_plus(dish + " recipe")
    )
    log_message("REXA", f"Looked up a recipe for: {dish}")


def affirmation_of_the_day():
    run_ai("Give me one short, original positive affirmation for today.")


def bmi_calculator(query_text):
    numbers = [
        float(chunk) for chunk in query_text.replace(",", " ").split()
        if chunk.replace(".", "", 1).isdigit()
    ]

    if len(numbers) < 2:
        log_message(
            "REXA",
            "Give me your weight in kg and height in cm, e.g. "
            "'calculate bmi 70 175'."
        )
        return

    weight_kg, height_cm = numbers[0], numbers[1]

    if height_cm <= 0 or weight_kg <= 0:
        log_message("REXA", "That weight/height doesn't look valid.")
        return

    height_m = height_cm / 100
    bmi = weight_kg / (height_m ** 2)

    if bmi < 18.5:
        category = "underweight"
    elif bmi < 25:
        category = "normal weight"
    elif bmi < 30:
        category = "overweight"
    else:
        category = "obese"

    answer = f"Your BMI is {bmi:.1f}, which falls in the '{category}' range."
    log_message("REXA", answer)
    speak(answer)


def start_countdown_timer(minutes=5):
    log_message("REXA", f"Started a {minutes}-minute countdown timer. \u23F2\uFE0F")
    speak(f"Countdown started for {minutes} minutes.")

    def worker():
        time.sleep(minutes * 60)
        log_message("REXA", f"\u23F0 Time's up! Your {minutes}-minute timer has ended.")
        speak("Time's up! Your timer has ended.")

    threading.Thread(target=worker, daemon=True).start()


# ============================================================

def extract_after(text, patterns):
    low = text.lower()

    for pattern in patterns:
        pos = low.find(pattern.lower())

        if pos >= 0:
            return text[
                pos + len(pattern):
            ].strip(" :,-")

    return ""


def matches_any(low, phrases):
    """
    Flexible matcher: returns True if the normalized text
    equals OR contains any of the given phrases. This lets
    REXA understand English commands even when the user adds
    extra words (e.g. "please open notepad for me").
    """
    for phrase in phrases:
        if phrase in low:
            return True
    return False


def show_help():
    log_message(
        "REXA",
        """REXA COMMANDS

KEYBOARD SHORTCUTS
- Enter: send the command from the command box
- Ctrl+Enter: send the command from anywhere in the app
- Ctrl+L: focus the command box
- F1: show this help
- F2: listen for one voice command
- F3: start voice chat
- F4: clear the chat
- Esc: stop speaking and exit fullscreen
Use YouTube's own shortcuts when the YouTube player is focused:
- Shift+N: next video
- Shift+P: previous video
- K or Space: play/pause
- J/L: seek backward/forward
- M: mute/unmute
- F: fullscreen

YOUTUBE
- open youtube / close youtube
- save it to my playlist / save this video to my playlist
- open youtube playlist / open playlist
- play playlist number 3 / play video 5 from playlist
- play youtube believer
- youtube play / pause / play again (replay)
- youtube next / previous
- youtube forward / backward (10s)
- youtube volume up / volume down / mute
- youtube fullscreen

INBOX / MESSAGES
- check my TikTok inbox / check TikTok messages
- check my Facebook inbox / check Messenger
- after opening TikTok or Facebook: check my inbox
- login to TikTok (first-time setup)

TIKTOK
- open tiktok / search tiktok football
- tiktok next / previous

VOICE
- voice command
- start voice chat / stop voice chat

CONVERSATION MODE
- serious mode / serious question mode
- normal mode / normal question mode
- story mode / let's talk
- what mode am I in

WEB & APPS
- google / search google python
- search wikipedia python
- login to gmail / sign in to gmail
- open gmail inbox / compose email
- open google calendar / open google drive
- open duckduckgo / open wikipedia
- search the web for <query>
- open linkedin / open notion / open canva
- open dropbox / open outlook
- open discord / open telegram / open reddit
- open twitter / open pinterest / open zoom
- open chatgpt (browser) / open chatgpt desktop
- open whatsapp / whatsapp message <number>|<text>
- open chrome / open edge / open spotify

WEB ASSISTANT
- web assistant mode / stop web assistant mode
- open website <url> / navigate to <url>
- read this page / what can I do here
- find the pricing section / click the search button
- fill <field> with <text> / submit this form
- scroll up/down / go back / go forward / refresh webpage
- create a new tab / switch to tab 2

ACTIVITY & PROACTIVE ASSISTANT
- show yesterday's activity / forget yesterday's activity
- stop remembering browsing activity
- remember my browsing activity
- MISA may ask a brief, non-assuming question about the active webpage

WINDOWS
- my pc / downloads / documents
- notepad / calculator / paint / camera
- cmd / powershell / open python
- close python (closes Python IDLE, not MISA)
- settings / network settings / personalization
- task manager / screenshot
- close window / minimize all / switch window
- volume up / volume down / mute

SYSTEM
- system info / network info / my ip
- time / date
- lock pc / restart pc / shutdown pc / cancel shutdown

MEDIA/APP CONTROL
- switch to tiktok / minimize this window / go to home screen
- open chrome and go to google / close all tabs
- skip the ad / fast-forward 30 seconds / rewind 10 seconds
- set volume to 50%

SEARCH & SHORTCUTS
- search youtube for <something> / find <name>'s profile on tiktok
- play <song/artist> on spotify
- create/generate/write an application and save it to Downloads
- write/generate a note and save it to Downloads
- set an alarm / set a timer  (opens Windows Clock, you set the time)
- what is the weather today

SYSTEM/HARDWARE
- turn on wifi / turn on bluetooth  (opens settings panel, toggle it yourself)
- increase screen brightness to maximum / to <N>%
  (needs: pip install screen-brightness-control)
- empty the recycle bin
- shut down the computer in 10 minutes

SOCIAL (limited — only what's genuinely possible)
- open instagram / open instagram and show my notifications
- open facebook and check my feed
- open messenger and text <name> <msg>  (opens draft, you press send)
REXA never makes false claims. It genuinely cannot do the
following (they need the app's private/login access):
  - making a real WhatsApp/Messenger call or talking on speakerphone
  - recording a voice message and sending it directly
  - reading, replying to, or deleting your actual SMS/call history
  - posting a story on Instagram
  - sending a direct message on TikTok/Messenger (can open the profile/chat)
  - deleting/renaming a 'selected' file in Explorer (can't know what's selected)
Can prepare a WhatsApp text draft (you press Send):
- send a whatsapp message to <number>|<message>
- send a whatsapp message to <number> saying '<message>'

ADVANCED BROWSER
- open youtube and play <something> / set playback speed to 1.5x
- youtube full screen / exit youtube full screen / minimize youtube
- open search bar, then speak or type your search
- turn on subtitles / close current tab / reopen last tab
- incognito window / bookmark this page / refresh page
- scroll down half a page / switch to previous tab

ADVANCED SYSTEM
- restart my computer right now / put the pc to sleep
- night light / do not disturb / check battery / drive c space
- turn on dark mode / open device manager / eject usb (gives a guide)
- close all background applications (opens Task Manager, End Task yourself)

WINDOWS SHORTCUTS (NEW)
- open control panel / open sound settings / open display settings
- open windows update / open recycle bin
- open desktop folder / open startup folder / open temp folder
- restart explorer
- clear clipboard / copy time to clipboard / copy date to clipboard
- open downloads folder / open documents folder / open appdata folder
- open bluetooth settings / open wifi settings
- open windows defender

FILE MANAGEMENT
- create a new folder on desktop named <name>
- move the last downloaded file to documents
- copy the selected file / duplicate this file (opens file picker, you choose)
- search my pc for <filename> / open my screenshot folder
- compress this folder into a zip / clear temporary system cache

PRODUCTIVITY
- start a 25-minute pomodoro / open calculator and compute 45 times 85
- add <task> to my task list / show my task list
- open google calendar and create an event for <something>
- dictate text: '<something>' / open my email inbox and compose

SCREEN & CAMERA
- high-resolution screenshot of the selected window
- start recording my screen / stop screen recording
- open camera app and snap a photo
- translate the selected sentence to bengali (Ctrl+C first)

PERSONAL ASSISTANT (NEW)
- set a reminder to <text> in <N> minutes / show my reminders
- add a note: <text> / show my notes / clear my notes
- roll a dice / flip a coin
- tell me a joke
- define <word>
- convert currency <query> / convert units <query>
- check stock price of <symbol> / check crypto price of <coin>
- open maps / get directions to <place>
- quote of the day
- search amazon for <item>
- open github / open slack / open teams
- start a countdown timer for <N> minutes

PERSONAL ASSISTANT (12 NEWEST ADDITIONS)
- weather in <city>
- what time is it in <city>
- how old is someone born in <year>
- generate a password / generate a 16 character password
- remind me to drink water every 60 minutes
- mark <task text> as done
- clear my task list
- random fact / fun fact
- show me the news / news about <topic>
- find a recipe for <dish>
- affirmation of the day
- calculate bmi 70 175  (weight in kg, height in cm)

MEMORY / GETTING TO KNOW YOU (NEW)
- call me <name>
- remember i'm studying <subject>
- remember <anything else you want REXA to know>
- my favorite color is blue / I like gaming
- I don't like <thing> / I prefer <thing>
- show my memory / update my memory
- what is my favorite color?
- forget that <thing> / forget everything about me
- what do you know about me / my profile
- forget about me   (clears everything REXA remembers about you)
REXA will bring this up naturally in chat and check in on you —
it's not just there to run commands.

ROUTINES
- set routine <activity> every 7 or 9 minutes
- show my routine / stop routine
- answer yes/done or not yet when REXA checks in

CLOSE APPS (NEW)
- close notepad / close calculator / close paint
- close cmd / close powershell
- close chrome / close edge / close spotify
- close task manager / close settings / close camera
- close file explorer

AI
- ask REXA (Gemini AI) anything else directly,
  in Bengali, Banglish, or English — REXA replies in English.
"""
    )

def open_gmail_compose():
    safe_open("https://mail.google.com/mail/u/0/#compose")
    log_message("REXA", "Opened a new Gmail compose window.")


def open_gmail_inbox():
    safe_open("https://mail.google.com/")
    log_message("REXA", "Opened your Gmail inbox.")


def check_gmail_inbox():
    open_gmail_inbox()
    log_message("REXA", "Checked Gmail inbox.")


def check_youtube_inbox():
    safe_open("https://www.youtube.com/inbox")
    log_message("REXA", "Opened YouTube inbox / notifications.")


def check_tiktok_inbox():
    check_social_inbox("tiktok")


def _open_first_tiktok_message_after_load():
    time.sleep(2.5)
    open_tiktok_message(1)


def open_tiktok_message(number=1):
    """Open a numbered TikTok inbox conversation in the normal Chrome window."""
    try:
        number = int(number)
    except (TypeError, ValueError):
        number = 1
    if number < 1:
        number = 1

    if pyautogui is None:
        log_message("REXA", "Opening a TikTok message requires PyAutoGUI.")
        speak("I cannot click the TikTok message because PyAutoGUI is not installed.")
        return

    browser_windows = [
        window for window in gw.getAllWindows()
        if "tiktok" in (window.title or "").lower()
        or "messages" in (window.title or "").lower()
    ]
    if not browser_windows:
        log_message("REXA", "TikTok messages is not open.")
        speak("TikTok messages is not open. Say check my TikTok inbox first.")
        return

    try:
        window = browser_windows[0]
        window.restore()
        window.activate()
        time.sleep(0.35)
        # TikTok's desktop message list is a vertical set of rows. Keep the
        # click inside the left conversation column and scale from the window.
        x = window.left + max(180, min(300, int(window.width * 0.22)))
        y = window.top + max(135, min(220, int(window.height * 0.23))) + (number - 1) * 72
        pyautogui.click(x, y)
        log_message("REXA", f"Opened TikTok message {number}.")
        speak(f"Opened TikTok message {number}.")
    except Exception as exc:
        log_message("REXA", f"Could not open TikTok message {number}: {exc}")
        speak("I could not open that TikTok message.")


def check_facebook_inbox():
    check_social_inbox("facebook")


def open_youtube_playlist(query=""):
    if query:
        safe_open(
            "https://www.youtube.com/results?search_query="
            + urllib.parse.quote_plus(f"{query} playlist")
        )
        log_message("REXA", f"Opened YouTube playlist search for: {query}")
        return

    safe_open("https://www.youtube.com/feed/playlists")
    log_message("REXA", "Opened your YouTube playlists.")

def open_youtube_playlist_by_name(query):
    """Find and open ONLY a playlist from the signed-in YouTube account."""

    driver = _get_yt_driver()
    if driver is None:
        return

    query = (query or "").strip()

    # Remove "playlist" from the end for matching
    if query.lower().endswith(" playlist"):
        query = query[:-9].strip()

    if not query:
        speak("Please tell me your playlist name.")
        return

    def normalize_title(text):
        text = (text or "").strip().lower()
        text = re.sub(r"[^\w\s]", " ", text, flags=re.UNICODE)
        text = re.sub(r"\s+", " ", text)

        if text.endswith(" playlist"):
            text = text[:-9].strip()

        return text

    requested = normalize_title(query)

    def get_playlist_id(href):
        if not href or "list=" not in href:
            return ""

        try:
            return urllib.parse.parse_qs(
                urllib.parse.urlparse(href).query
            ).get("list", [""])[0]
        except Exception:
            return ""

    def make_playlist_url(playlist_id):
        return f"https://www.youtube.com/playlist?list={playlist_id}"

    def worker():
        try:
            set_mode("FINDING YOUR PLAYLIST")

            # ==================================================
            # IMPORTANT:
            # ONLY search the user's signed-in playlist page.
            # NEVER use public YouTube search.
            # ==================================================
            driver.get("https://www.youtube.com/feed/playlists")

            _yt_wait(
                driver,
                By.TAG_NAME,
                "body",
                timeout=20
            )

            time.sleep(2)

            # Load lazy playlist cards
            for _ in range(5):
                driver.execute_script(
                    "window.scrollTo(0, document.body.scrollHeight);"
                )
                time.sleep(1)

            time.sleep(1)

            # ==================================================
            # Find playlist cards ONLY on /feed/playlists
            # ==================================================
            cards = driver.find_elements(
                By.CSS_SELECTOR,
                "ytd-grid-playlist-renderer, "
                "ytd-playlist-renderer, "
                "ytd-rich-item-renderer"
            )

            found_playlists = []

            for card in cards:
                try:
                    # Find playlist URLs inside this card. YouTube uses
                    # different card elements for private and public lists.
                    links = card.find_elements(
                        By.CSS_SELECTOR,
                        "a[href*='list=']"
                    )

                    playlist_id = ""
                    playlist_href = ""

                    for link in links:
                        href = link.get_attribute("href") or ""

                        if "list=" in href:
                            playlist_id = get_playlist_id(href)
                            playlist_href = href

                            if playlist_id:
                                break

                    if not playlist_id:
                        continue

                    # ------------------------------------------
                    # Get playlist title
                    # ------------------------------------------
                    title = ""

                    title_elements = card.find_elements(
                        By.CSS_SELECTOR,
                        "a#video-title, #video-title, h3, "
                        "a[href*='list=']"
                    )

                    for element in title_elements:
                        title = (
                            element.get_attribute("title")
                            or element.get_attribute("aria-label")
                            or element.text
                            or ""
                        ).strip()

                        if title and title.lower() not in {"view full playlist", "playlist"}:
                            break

                    # Fallback
                    if not title:
                        card_text = (card.text or "").strip()

                        if card_text:
                            lines = [
                                line.strip() for line in card_text.splitlines()
                                if line.strip()
                                and line.strip().lower() not in {
                                    "view full playlist", "private", "public",
                                    "playlist"
                                }
                            ]
                            title = lines[0] if lines else ""

                    if not title:
                        continue

                    found_playlists.append({
                        "id": playlist_id,
                        "title": title,
                        "normalized": normalize_title(title),
                        "url": make_playlist_url(playlist_id)
                    })

                except Exception as card_error:
                    log_message(
                        "REXA",
                        f"Playlist card error: {card_error}"
                    )

            # Some YouTube layouts do not expose playlist cards at all. Read
            # the rendered playlist links as a fallback, including private
            # playlists shown on the signed-in account page.
            page_links = driver.find_elements(By.CSS_SELECTOR, "a[href*='list=']")
            for link in page_links:
                try:
                    href = link.get_attribute("href") or ""
                    playlist_id = get_playlist_id(href)
                    if not playlist_id:
                        continue

                    title = (
                        link.get_attribute("title")
                        or link.get_attribute("aria-label")
                        or link.text
                        or ""
                    ).strip()
                    if not title or title.lower() in {"view full playlist", "playlist"}:
                        title = driver.execute_script(
                            """
                            const card = arguments[0].closest(
                                'ytd-grid-playlist-renderer,'
                                + 'ytd-playlist-renderer,'
                                + 'ytd-rich-item-renderer'
                            );
                            return card ? card.innerText : '';
                            """,
                            link,
                        ).strip().splitlines()[0] if link else ""
                    if title:
                        found_playlists.append({
                            "id": playlist_id,
                            "title": title,
                            "normalized": normalize_title(title),
                            "url": make_playlist_url(playlist_id),
                        })
                except Exception as link_error:
                    log_message("REXA", f"Playlist link error: {link_error}")

            # ==================================================
            # Remove duplicate playlist IDs
            # ==================================================
            unique = {}

            for playlist in found_playlists:
                unique[playlist["id"]] = playlist

            found_playlists = list(unique.values())

            log_message(
                "REXA",
                f"Found {len(found_playlists)} playlists in your account."
            )
            if found_playlists:
                log_message(
                    "REXA",
                    "Available playlists: " + ", ".join(
                        playlist["title"] for playlist in found_playlists[:20]
                    )
                )

            # ==================================================
            # EXACT MATCH
            # ==================================================
            exact = [
                p for p in found_playlists
                if p["normalized"] == requested
            ]

            if len(exact) == 1:

                selected = exact[0]

                # Save selected playlist
                state["selected_youtube_playlist_id"] = selected["id"]
                state["selected_youtube_playlist_title"] = selected["title"]
                state["selected_youtube_playlist_url"] = selected["url"]

                # Store complete context
                state["youtube_playlist_context"] = {
                    "id": selected["id"],
                    "title": selected["title"],
                    "url": selected["url"]
                }

                driver.get(selected["url"])

                time.sleep(2)

                log_message(
                    "REXA",
                    f"Selected YOUR playlist: {selected['title']}"
                )

                log_message(
                    "REXA",
                    f"Playlist ID: {selected['id']}"
                )

                speak(
                    f"Opening your playlist {selected['title']}."
                )

                return

            # ==================================================
            # MULTIPLE EXACT MATCHES
            # ==================================================
            if len(exact) > 1:

                names = ", ".join(
                    p["title"] for p in exact
                )

                log_message(
                    "REXA",
                    f"Multiple exact playlists found: {names}"
                )

                speak(
                    "I found multiple playlists with that name. "
                    "Please give me the exact name."
                )

                return

            # ==================================================
            # SAFE PARTIAL MATCH
            # ==================================================
            partial = [
                p for p in found_playlists
                if (
                    requested in p["normalized"]
                    or p["normalized"] in requested
                )
            ]

            # Only accept partial match if there is ONE.
            if len(partial) == 1:

                selected = partial[0]

                state["selected_youtube_playlist_id"] = selected["id"]
                state["selected_youtube_playlist_title"] = selected["title"]
                state["selected_youtube_playlist_url"] = selected["url"]

                state["youtube_playlist_context"] = {
                    "id": selected["id"],
                    "title": selected["title"],
                    "url": selected["url"]
                }

                driver.get(selected["url"])

                time.sleep(2)

                log_message(
                    "REXA",
                    f"Selected YOUR playlist: {selected['title']}"
                )

                log_message(
                    "REXA",
                    f"Playlist ID: {selected['id']}"
                )

                speak(
                    f"Opening your playlist {selected['title']}."
                )

                return

            # ==================================================
            # MULTIPLE PARTIAL MATCHES
            # ==================================================
            if len(partial) > 1:

                names = ", ".join(
                    p["title"] for p in partial[:5]
                )

                log_message(
                    "REXA",
                    f"Multiple similar playlists: {names}"
                )

                speak(
                    "I found several similar playlists. "
                    "Please give me the exact playlist name."
                )

                return

            # ==================================================
            # NOT FOUND
            #
            # NO PUBLIC SEARCH!
            # ==================================================
            log_message(
                "REXA",
                f"Your playlist was not found: {query}"
            )

            speak(
                f"I couldn't find your playlist {query} "
                "in your YouTube account."
            )

        except Exception as exc:
            error_text = str(exc).lower()
            if "invalid session" in error_text or "session deleted" in error_text:
                global yt_driver
                try:
                    yt_driver.quit()
                except Exception:
                    pass
                yt_driver = None
                log_message(
                    "REXA",
                    "The YouTube browser session was closed. Restarting it and retrying your playlist."
                )
                open_youtube_playlist_by_name(query)
                return

            log_message(
                "REXA",
                f"Playlist selection error: {exc}"
            )

            speak(
                "I couldn't open your playlist."
            )

        finally:
            set_mode("SYSTEM READY")

    threading.Thread(
        target=worker,
        daemon=True
    ).start()


def play_from_my_playlist():
    """Play the first item from the selected personal YouTube playlist."""
    playlist_url = state.get("selected_youtube_playlist_url", "")
    if not playlist_url:
        state["awaiting_youtube_playlist"] = True
        open_youtube_playlist()
        log_message("REXA", "Which of your YouTube playlists should I use?")
        speak("Which of your playlists should I use, Sir?")
        return

    driver = _get_yt_driver()
    if driver is None:
        return

    def worker():
        try:
            set_mode("YOUTUBE PLAYLIST")
            driver.get(playlist_url)
            _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
            time.sleep(1.2)
            youtube_playlist_play_number(1)
        except Exception as exc:
            log_message("REXA", f"Could not play from your playlist: {exc}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, daemon=True).start()

def open_gmail_login():
    if safe_open("https://mail.google.com/"):
        log_message(
            "REXA",
            "Gmail is open. If you are not signed in, please sign in manually; "
            "I never handle or store your password."
        )
        speak("Gmail is open. Please sign in manually if needed.")


def open_google_drive():
    safe_open("https://drive.google.com/")
    log_message("REXA", "Opened Google Drive.")


def open_duckduckgo():
    safe_open("https://duckduckgo.com/")
    log_message("REXA", "Opened DuckDuckGo.")


def open_wikipedia():
    safe_open("https://www.wikipedia.org/")
    log_message("REXA", "Opened Wikipedia.")


# ============================================================
# JARVIS AUTOMATION ENGINE
# ============================================================

JARVIS_PROTOCOLS = {
    "veronica": False, "clean_slate": False, "house_party": False,
    "sentry": False, "stealth": False,
}


def _jarvis_notice(message):
    log_message("REXA", message)


def _choose_path(title, directory=False):
    from tkinter import filedialog
    try:
        if directory:
            return filedialog.askdirectory(title=title)
        return filedialog.askopenfilename(title=title)
    except Exception as exc:
        _jarvis_notice(f"File picker error: {exc}")
        return ""


def open_youtube_reels():
    if selenium_available:
        driver = _get_yt_driver()
        if driver is None:
            return None

        def worker():
            try:
                set_mode("OPENING REELS")
                driver.get("https://www.youtube.com/shorts")
                _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
                _jarvis_notice("YouTube Shorts/Reels is open.")
            except Exception as exc:
                _jarvis_notice(f"Could not open YouTube Shorts/Reels: {exc}")
            finally:
                set_mode("SYSTEM READY")

        threading.Thread(target=worker, name="JARVIS-Reels-Open", daemon=True).start()
        return driver

    if safe_open("https://www.youtube.com/shorts"):
        _jarvis_notice("YouTube Shorts/Reels is open. Install Selenium for finish-aware auto-swipe.")
    return None


def open_youtube_reels_and_scroll_mode():
    """Open Shorts/Reels and enable persistent scrolling after navigation."""
    global youtube_scroll_mode_active

    if not selenium_available:
        if safe_open("https://www.youtube.com/shorts"):
            _jarvis_notice(
                "YouTube Shorts/Reels is open, but scroll mode needs Selenium."
            )
        return

    driver = _get_yt_driver()
    if driver is None:
        return

    def worker():
        global youtube_scroll_mode_active
        try:
            set_mode("OPENING REELS")
            driver.get("https://www.youtube.com/shorts")
            _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
            youtube_scroll_mode_active = True
            yt_context["mode"] = "browsing"
            _jarvis_notice(
                "YouTube Shorts/Reels is open. Scroll mode is on."
            )
            speak("YouTube Shorts scroll mode is on.")
        except Exception as exc:
            youtube_scroll_mode_active = False
            _jarvis_notice(
                f"Could not open YouTube Shorts/Reels with scroll mode: {exc}"
            )
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(
        target=worker,
        name="JARVIS-Reels-Scroll",
        daemon=True,
    ).start()


def start_auto_swipe_reels():
    if not selenium_available:
        _jarvis_notice("Finish-aware auto-swipe needs: pip install selenium webdriver-manager.")
        return
    reels_swipe_stop.clear()

    def worker():
        driver = _get_yt_driver()
        if driver is None:
            return
        try:
            set_mode("AUTO SWIPE REELS")
            driver.get("https://www.youtube.com/shorts")
            _yt_wait(driver, By.TAG_NAME, "body", timeout=15)
            _jarvis_notice("Finish-aware Reels auto-swipe started. The next Reel will open only after the current one finishes.")
            while not reels_swipe_stop.is_set():
                finished = False
                while not reels_swipe_stop.wait(0.5):
                    state_info = driver.execute_script("""
                        const video = document.querySelector('video');
                        if (!video) return null;
                        return {ended: video.ended, time: video.currentTime || 0,
                                duration: Number.isFinite(video.duration) ? video.duration : 0};
                    """)
                    if state_info and (state_info.get("ended") or (
                            state_info.get("duration", 0) > 0 and
                            state_info.get("time", 0) >= state_info.get("duration", 0) - 0.25)):
                        finished = True
                        break
                if not finished or reels_swipe_stop.is_set():
                    break
                driver.execute_script("window.scrollBy({top: window.innerHeight, left: 0, behavior: 'smooth'});")
                time.sleep(1.0)
        except Exception as exc:
            _jarvis_notice(f"Auto-swipe stopped safely: {exc}")
        finally:
            set_mode("SYSTEM READY")

    threading.Thread(target=worker, name="JARVIS-Reels", daemon=True).start()


def stop_auto_swipe_reels():
    reels_swipe_stop.set()
    _jarvis_notice("Automatic Shorts/Reels swipe stopped.")


def open_desktop_app(app_name):
    app_name = app_name.strip(" '\"")
    if not app_name:
        _jarvis_notice("Tell me the desktop app name to open.")
        return
    aliases = {
        "vs code": "Visual Studio Code",
        "v s code": "Visual Studio Code",
        "vscode code": "Visual Studio Code",
        "vscode": "Visual Studio Code",
        "visual studio code": "Visual Studio Code",
        "visual studio": "Visual Studio Code",
        "chat gpt": "ChatGPT",
        "chatgpt": "ChatGPT",
        "anti gravity": "Antigravity",
        "antigarveti": "Antigravity",
        "antigravity": "Antigravity",
    }
    app_name = aliases.get(app_name.lower(), app_name)
    escaped = app_name.replace("'", "''")
    command = (f"$a=Get-StartApps | Where-Object {{$_.Name -like '*{escaped}*'}} | "
               "Select-Object -First 1; if($a){Start-Process explorer.exe "
               "-ArgumentList ('shell:AppsFolder\\' + $a.AppID)} else{exit 1}")
    code, output = _run_process(["powershell.exe", "-NoProfile", "-Command", command], timeout=20)
    _jarvis_notice(f"Opened desktop app: {app_name}." if code == 0 else f"Could not open desktop app '{app_name}'. {output}")


def close_desktop_app(app_name):
    app_name = app_name.strip(" '\"")
    if not app_name:
        _jarvis_notice("Tell me the desktop app name to close.")
        return
    if not confirm_destructive_action("Close Desktop App", f"Close processes matching '{app_name}'?"):
        return
    escaped = app_name.replace("'", "''")
    command = (f"Get-Process | Where-Object {{$_.ProcessName -like '*{escaped}*' -or "
               f"$_.Description -like '*{escaped}*'}} | Stop-Process -Force")
    code, output = _run_process(["powershell.exe", "-NoProfile", "-Command", command], timeout=30)
    _jarvis_notice(f"Close request sent for desktop app: {app_name}." if code == 0 else f"Could not close '{app_name}': {output}")


def _run_process(command, cwd=None, timeout=60):
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True,
                                text=True, timeout=timeout, shell=False)
        output = (result.stdout or result.stderr).strip()
        return result.returncode, output[-3000:]
    except Exception as exc:
        return 1, str(exc)


def _protocol(name, enabled, description):
    JARVIS_PROTOCOLS[name] = enabled
    memory.setdefault("protocol_states", {})[name] = enabled
    save_memory(memory)
    _jarvis_notice(f"{description} {'enabled' if enabled else 'disabled'}.")


def _terminate_user_apps():
    """Close common user applications while preserving Windows and JARVIS."""
    protected = {"explorer", "python", "pythonw", "powershell", "cmd", "svchost",
                 "system", "services", "lsass", "winlogon", "dwm", "jarvis_gui"}
    targets = []
    try:
        for process in psutil.process_iter(["pid", "name"]):
            name = (process.info.get("name") or "").lower().removesuffix(".exe")
            if name and name not in protected and name not in targets:
                targets.append(name)
        closed = 0
        for name in targets:
            try:
                subprocess.run(["taskkill", "/f", "/im", name + ".exe"],
                               capture_output=True, text=True, timeout=3)
                closed += 1
            except Exception:
                continue
        _jarvis_notice(f"Clean Slate closed {closed} non-system user process group(s).")
    except Exception as exc:
        _jarvis_notice(f"Clean Slate app cleanup failed safely: {exc}")


def protocol_veronica():
    _protocol("veronica", True, "Protocol Veronica")
    open_vscode_workspace()
    open_powershell()
    auto_organize_downloads()


def protocol_clean_slate():
    if confirm_destructive_action("Clean Slate", "Remove temporary files and clear the assistant activity log?"):
        _protocol("clean_slate", True, "Clean Slate")
        _terminate_user_apps()
        clear_temp_files()
        memory["activity"] = []
        save_memory(memory)


def protocol_house_party():
    _protocol("house_party", True, "House Party")
    for command in (["start", "", "explorer.exe"], ["start", "", "ms-settings:display"]):
        try:
            subprocess.Popen(command, shell=False)
        except Exception:
            pass
    _jarvis_notice("House Party launched the configured desktop utilities.")


def protocol_sentry():
    _protocol("sentry", True, "Sentry Mode")
    system_info()
    network_info()
    startup_apps_audit()


def protocol_stealth():
    _protocol("stealth", True, "Stealth Mode")
    state["voice"] = False
    voice_var.set("VOICE      OFF")
    _jarvis_notice("Stealth Mode enabled. Voice output is muted.")


def threat_assessment():
    lines = [f"Protocol states: {JARVIS_PROTOCOLS}"]
    lines.append(f"Network: {'ONLINE' if check_network() else 'OFFLINE'}")
    lines.append(f"Platform: {platform.platform()}")
    if psutil:
        lines.append(f"CPU: {psutil.cpu_percent(interval=0.2):.0f}%")
        lines.append(f"RAM: {psutil.virtual_memory().percent:.0f}%")
    _jarvis_notice("THREAT ASSESSMENT\n\n" + "\n".join(lines))


def smart_home_webhook():
    """Trigger a configured Home Assistant/Tasmota/Tuya-compatible webhook."""
    if requests is None:
        _jarvis_notice("Smart Home webhooks need: pip install requests")
        return
    url = os.getenv("JARVIS_SMART_HOME_WEBHOOK", "").strip()
    if not url:
        url = simpledialog.askstring("Smart Home", "Webhook URL:") or ""
    if not url.lower().startswith(("http://", "https://")):
        _jarvis_notice("Smart Home cancelled: provide a valid HTTP(S) webhook URL.")
        return
    payload_text = simpledialog.askstring("Smart Home", "JSON payload (optional):") or "{}"
    try:
        payload = json.loads(payload_text)
        if not isinstance(payload, dict):
            raise ValueError("payload must be a JSON object")
        headers = {"Content-Type": "application/json"}
        token = os.getenv("JARVIS_SMART_HOME_TOKEN", "").strip()
        if token:
            headers["Authorization"] = f"Bearer {token}"
        response = requests.post(url, json=payload, headers=headers, timeout=15)
        response.raise_for_status()
        _jarvis_notice(f"Smart Home webhook completed with HTTP {response.status_code}.")
    except Exception as exc:
        _jarvis_notice(f"Smart Home webhook error: {exc}")


def smart_home_toggle(device, enabled):
    url = os.getenv(f"JARVIS_{device.upper()}_WEBHOOK", "").strip()
    if not url:
        _jarvis_notice(f"Configure JARVIS_{device.upper()}_WEBHOOK in .env first.")
        return
    if requests is None:
        _jarvis_notice("Smart Home controls need: pip install requests")
        return
    try:
        response = requests.post(url, json={"state": "ON" if enabled else "OFF"}, timeout=15)
        response.raise_for_status()
        _jarvis_notice(f"Smart Home {device} turned {'on' if enabled else 'off'}.")
    except Exception as exc:
        _jarvis_notice(f"Smart Home {device} error: {exc}")


def gpu_telemetry():
    if nvmlInit is None:
        _jarvis_notice("GPU telemetry needs: pip install nvidia-ml-py")
        return
    try:
        nvmlInit()
        rows = []
        for index in range(nvmlDeviceGetCount()):
            handle = nvmlDeviceGetHandleByIndex(index)
            name = nvmlDeviceGetName(handle)
            if isinstance(name, bytes):
                name = name.decode(errors="replace")
            temp = nvmlDeviceGetTemperature(handle, NVML_TEMPERATURE_GPU)
            rows.append(f"GPU {index}: {name}, {temp} C")
        _jarvis_notice("GPU TELEMETRY\n\n" + ("\n".join(rows) or "No NVIDIA GPU found."))
    except Exception as exc:
        _jarvis_notice(f"GPU telemetry error: {exc}")
    finally:
        try:
            nvmlShutdown()
        except Exception:
            pass


def battery_wear_report():
    if not psutil:
        _jarvis_notice("Battery report needs psutil.")
        return
    try:
        battery = psutil.sensors_battery()
        if not battery:
            _jarvis_notice("No battery was detected on this computer.")
            return
        report = Path.home() / "battery-report.html"
        code, output = _run_process(["powercfg", "/batteryreport", "/output", str(report)], timeout=30)
        if code == 0:
            _jarvis_notice(f"Battery report created at: {report}\nCurrent charge: {battery.percent:.0f}%")
        else:
            _jarvis_notice(f"Battery report failed: {output}")
    except Exception as exc:
        _jarvis_notice(f"Battery report error: {exc}")


def flush_dns():
    code, output = _run_process(["ipconfig", "/flushdns"], timeout=30)
    _jarvis_notice("DNS cache flushed." if code == 0 else f"DNS flush failed: {output}")


def kill_port_process(port_text):
    try:
        port = int(re.search(r"\d+", port_text).group())
        if not 1 <= port <= 65535:
            raise ValueError("port must be 1-65535")
        code, output = _run_process(["powershell.exe", "-NoProfile", "-Command",
            f"$c=Get-NetTCPConnection -LocalPort {port} -ErrorAction SilentlyContinue; "
            "if($c){$c | Select-Object -ExpandProperty OwningProcess -Unique | "
            "ForEach-Object {Stop-Process -Id $_ -Force}}"], timeout=30)
        _jarvis_notice(f"Port {port} process termination requested." if code == 0 else f"Port killer failed: {output}")
    except Exception as exc:
        _jarvis_notice(f"Port killer error: {exc}")


def send_secure_email():
    if not confirm_destructive_action("Send Email", "Send an email using the configured secure SMTP account?"):
        return
    recipient = simpledialog.askstring("Email", "Recipient email:")
    subject = simpledialog.askstring("Email", "Subject:")
    body = simpledialog.askstring("Email", "Message (HTML allowed):")
    attachment = _choose_path("Optional attachment")
    sender = os.getenv("SMTP_USERNAME", "").strip()
    password = os.getenv("SMTP_PASSWORD", "")
    host = os.getenv("SMTP_HOST", "smtp.gmail.com").strip()
    try:
        port = int(os.getenv("SMTP_PORT", "465"))
    except ValueError:
        _jarvis_notice("SMTP_PORT must be a number.")
        return
    if not all((recipient, subject, body, sender, password)):
        _jarvis_notice("Email cancelled: recipient, subject, body and SMTP credentials are required in .env.")
        return

    def send_worker():
        try:
            message = MIMEMultipart("mixed")
            message["From"] = formataddr((os.getenv("SMTP_FROM_NAME", "JARVIS"), sender))
            message["To"] = recipient
            message["Subject"] = subject
            alternative = MIMEMultipart("alternative")
            alternative.attach(MIMEText(re.sub(r"<[^>]+>", "", body), "plain", "utf-8"))
            styled_body = (
                '<div style="background:#05090d;color:#d8faff;padding:24px;'
                'font-family:Segoe UI,Arial,sans-serif;border:1px solid #12b3e4">'
                '<h2 style="color:#12b3e4;margin-top:0">JARVIS AI</h2>'
                f'<div style="white-space:pre-wrap">{body}</div></div>'
            )
            alternative.attach(MIMEText(styled_body, "html", "utf-8"))
            message.attach(alternative)
            if attachment:
                from email.mime.base import MIMEBase
                from email import encoders
                part = MIMEBase("application", "octet-stream")
                part.set_payload(Path(attachment).read_bytes())
                encoders.encode_base64(part)
                part.add_header("Content-Disposition", "attachment", filename=Path(attachment).name)
                message.attach(part)
            with smtplib.SMTP_SSL(host, port, timeout=30) as server:
                server.login(sender, password)
                server.send_message(message)
            _jarvis_notice(f"Email sent securely to {recipient}.")
        except Exception as exc:
            _jarvis_notice(f"Secure email error: {exc}")

    try:
        threading.Thread(target=send_worker, name="JARVIS-Email", daemon=True).start()
        _jarvis_notice("Email queued for secure background delivery.")
    except Exception as exc:
        _jarvis_notice(f"Could not start email worker: {exc}")


def git_action(action):
    folder = _choose_path("Choose Git repository", directory=True)
    if not folder:
        return
    if action == "push" and not confirm_destructive_action("Git Push", "Push local commits to the configured remote?"):
        return
    commands = {"status": ["git", "status", "--short"], "pull": ["git", "pull"],
                "push": ["git", "push"], "commit": ["git", "commit", "-am", "JARVIS update"]}
    code, output = _run_process(commands[action], cwd=folder, timeout=120)
    _jarvis_notice(f"Git {action}: {'OK' if code == 0 else 'FAILED'}\n{output or 'No output.'}")


def docker_action(action):
    command = ["docker", "compose", action] if action in {"up", "down"} else ["docker", action]
    code, output = _run_process(command, timeout=120)
    _jarvis_notice(f"Docker {action}: {'OK' if code == 0 else 'FAILED'}\n{output or 'No output.'}")


def open_vscode_workspace():
    folder = _choose_path("Choose VS Code workspace", directory=True)
    if folder:
        code, output = _run_process(["code", "--new-window", folder], timeout=20)
        _jarvis_notice("VS Code workspace opened." if code == 0 else f"VS Code error: {output}")


def run_project_tests():
    folder = _choose_path("Choose project to test", directory=True)
    if not folder:
        return
    command = ["pytest"] if (Path(folder) / "pytest.ini").exists() or list(Path(folder).glob("test*.py")) else ["python", "-m", "unittest", "discover"]
    code, output = _run_process(command, cwd=folder, timeout=300)
    _jarvis_notice(f"Tests {'passed' if code == 0 else 'failed'}.\n{output}")


def auto_organize_downloads():
    downloads = Path.home() / "Downloads"
    moved = 0
    categories = {"Images": {".png", ".jpg", ".jpeg", ".gif", ".webp"},
                  "Documents": {".pdf", ".doc", ".docx", ".txt", ".xlsx", ".csv"},
                  "Archives": {".zip", ".rar", ".7z", ".tar", ".gz"},
                  "Audio": {".mp3", ".wav", ".flac", ".aac"},
                  "Videos": {".mp4", ".mkv", ".mov", ".avi", ".webm"},
                  "Executables": {".exe", ".msi", ".bat", ".cmd"},
                  "Code": {".py", ".js", ".ts", ".html", ".css", ".json", ".java", ".cpp"}}
    try:
        for item in downloads.iterdir():
            if not item.is_file():
                continue
            category = next((name for name, suffixes in categories.items() if item.suffix.lower() in suffixes), "Other")
            target = downloads / category
            target.mkdir(exist_ok=True)
            shutil.move(str(item), str(target / item.name))
            moved += 1
        _jarvis_notice(f"Downloads organized. Moved {moved} file(s).")
    except Exception as exc:
        _jarvis_notice(f"Download organizer error: {exc}")


def find_duplicate_files():
    folder = _choose_path("Choose folder to scan for duplicates", directory=True)
    if not folder:
        return
    hashes = {}
    try:
        for item in Path(folder).rglob("*"):
            if item.is_file() and item.stat().st_size <= 500 * 1024 * 1024:
                digest = hashlib.md5(item.read_bytes()).hexdigest()
                hashes.setdefault(digest, []).append(str(item))
        duplicates = [paths for paths in hashes.values() if len(paths) > 1]
        text = "\n\n".join("\n".join(paths) for paths in duplicates) or "No duplicate files found."
        _jarvis_notice(f"DUPLICATE FILES\n\n{text[:6000]}")
    except Exception as exc:
        _jarvis_notice(f"Duplicate scan error: {exc}")


def secure_shred_file():
    path = _choose_path("Choose file to shred")
    if not path or not confirm_destructive_action("Secure Shredder", f"Permanently destroy {Path(path).name}?"):
        return
    try:
        target = Path(path)
        size = target.stat().st_size
        with target.open("r+b", buffering=0) as handle:
            for pattern in (b"\x00", b"\xff", None):
                handle.seek(0)
                remaining = size
                while remaining:
                    chunk = min(1024 * 1024, remaining)
                    handle.write(os.urandom(chunk) if pattern is None else pattern * chunk)
                    remaining -= chunk
            handle.flush()
        target.unlink()
        _jarvis_notice("File shredded and removed.")
    except Exception as exc:
        _jarvis_notice(f"Secure shredder error: {exc}")


def screen_ocr():
    if pytesseract is None or ImageGrab is None:
        _jarvis_notice("OCR needs: pip install pytesseract pillow, plus Tesseract OCR on Windows.")
        return
    try:
        text = pytesseract.image_to_string(ImageGrab.grab()).strip()
        _jarvis_notice(text or "No text was detected on the screen.")
    except Exception as exc:
        _jarvis_notice(f"OCR error: {exc}")


def decode_qr_from_screen():
    if cv2 is None or ImageGrab is None:
        _jarvis_notice("QR decoding needs: pip install opencv-python pillow.")
        return
    try:
        image = cv2.cvtColor(__import__("numpy").array(ImageGrab.grab()), cv2.COLOR_RGB2BGR)
        data, _, _ = cv2.QRCodeDetector().detectAndDecode(image)
        _jarvis_notice(f"QR code: {data}" if data else "No QR code was detected.")
    except Exception as exc:
        _jarvis_notice(f"QR decoder error: {exc}")


def cursor_color_picker():
    if pyautogui is None:
        _jarvis_notice("Cursor color picker needs: pip install pyautogui.")
        return
    try:
        x, y = pyautogui.position()
        color = pyautogui.pixel(x, y)
        value = "#%02x%02x%02x" % color
        _jarvis_notice(f"Cursor pixel at ({x}, {y}): RGB {color}, {value}")
        root.clipboard_clear()
        root.clipboard_append(value)
        root.update()
    except Exception as exc:
        _jarvis_notice(f"Color picker error: {exc}")


def search_arxiv():
    query = simpledialog.askstring("ArXiv", "Paper topic:")
    if not query:
        return
    url = "https://export.arxiv.org/api/query?search_query=all:" + urllib.parse.quote(query) + "&max_results=5"
    if requests is None:
        safe_open("https://arxiv.org/search/?query=" + urllib.parse.quote_plus(query) + "&searchtype=all")
        _jarvis_notice("Opened ArXiv search in the browser.")
        return
    try:
        response = requests.get(url, timeout=20)
        response.raise_for_status()
        titles = re.findall(r"<title>(.*?)</title>", response.text, flags=re.DOTALL)[1:6]
        titles = [re.sub(r"\s+", " ", title).strip() for title in titles]
        _jarvis_notice("ARXIV RESULTS\n\n" + ("\n".join(f"{i}. {title}" for i, title in enumerate(titles, 1)) or "No papers found."))
    except Exception as exc:
        _jarvis_notice(f"ArXiv search error: {exc}")


def extract_youtube_mp3():
    if yt_dlp is None:
        _jarvis_notice("MP3 extraction needs: pip install yt-dlp and an FFmpeg installation.")
        return
    url = simpledialog.askstring("YouTube MP3", "YouTube URL:")
    if not url or not url.lower().startswith(("https://", "http://")):
        _jarvis_notice("Please provide a valid YouTube URL.")
        return
    output_dir = BASE_DIR / "audio"
    output_dir.mkdir(exist_ok=True)
    try:
        options = {"format": "bestaudio/best", "outtmpl": str(output_dir / "%(title)s.%(ext)s"),
                   "noplaylist": True, "postprocessors": [{"key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192"}]}
        with yt_dlp.YoutubeDL(options) as downloader:
            info = downloader.extract_info(url, download=True)
        _jarvis_notice(f"MP3 extracted to {output_dir}: {info.get('title', 'audio')}")
    except Exception as exc:
        _jarvis_notice(f"YouTube MP3 error: {exc}. Ensure FFmpeg is installed and on PATH.")


def summarize_text_file():
    path = _choose_path("Choose text file to summarize")
    if not path:
        return
    try:
        content = Path(path).read_text(encoding="utf-8")
        run_ai("Summarize this document in concise bullet points:\n" + content[:20000])
    except Exception as exc:
        _jarvis_notice(f"Text summarizer error: {exc}")


def morning_briefing():
    system = "System data unavailable"
    if psutil:
        try:
            system = (f"CPU {psutil.cpu_percent(interval=0.2):.0f}%, "
                      f"RAM {psutil.virtual_memory().percent:.0f}%, "
                      f"Disk {psutil.disk_usage(Path.home().anchor).percent:.0f}%")
        except Exception:
            pass
    tasks = TASK_LIST_FILE.read_text(encoding="utf-8")[:3000] if TASK_LIST_FILE.exists() else "No tasks"
    reminders = REMINDERS_FILE.read_text(encoding="utf-8")[:3000] if REMINDERS_FILE.exists() else "No reminders"
    weather = "Weather unavailable"
    if requests:
        try:
            response = requests.get("https://wttr.in/?format=3", timeout=8)
            response.raise_for_status()
            weather = response.text.strip()
        except Exception:
            pass
    open_google_calendar()
    run_ai("Create a concise executive morning briefing from these current inputs. "
            f"Weather: {weather}\nHardware: {system}\nTasks:\n{tasks}\nReminders:\n{reminders}")


def expense_entry():
    amount = simpledialog.askstring("Expense", "Amount:")
    category = simpledialog.askstring("Expense", "Category:")
    if not amount or not category:
        return
    try:
        with (BASE_DIR / "expenses.csv").open("a", encoding="utf-8") as file:
            file.write(f"{dt.datetime.now().isoformat()},{category},{float(amount):.2f}\n")
        _jarvis_notice(f"Expense recorded: {category}, {float(amount):.2f}.")
    except Exception as exc:
        _jarvis_notice(f"Expense tracker error: {exc}")


def wake_on_lan():
    mac = simpledialog.askstring("Wake on LAN", "MAC address:")
    if not mac:
        return
    try:
        raw = bytes.fromhex(re.sub(r"[^0-9a-fA-F]", "", mac))
        if len(raw) != 6:
            raise ValueError("MAC address must contain 6 bytes")
        packet = b"\xff" * 6 + raw * 16
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            sock.sendto(packet, ("255.255.255.255", 9))
        _jarvis_notice("Wake-on-LAN magic packet sent.")
    except Exception as exc:
        _jarvis_notice(f"Wake-on-LAN error: {exc}")


def arp_scan():
    code, output = _run_process(["arp", "-a"], timeout=30)
    _jarvis_notice(output if code == 0 else f"ARP scan failed: {output}")


def port_scan():
    host = simpledialog.askstring("Port Scanner", "Host:") or "127.0.0.1"
    ports = [int(value) for value in (simpledialog.askstring("Port Scanner", "Ports (comma separated):") or "80,443,22").split(",") if value.strip().isdigit()]
    open_ports = []
    for port in ports[:100]:
        try:
            with socket.create_connection((host, port), timeout=0.3):
                open_ports.append(port)
        except OSError:
            pass
    _jarvis_notice(f"Open ports on {host}: {open_ports or 'none detected'}")


def startup_apps_audit():
    code, output = _run_process(["powershell.exe", "-NoProfile", "-Command",
        "Get-CimInstance Win32_StartupCommand | Select-Object Name,Command | Format-Table -AutoSize"], timeout=30)
    _jarvis_notice(output if code == 0 else f"Startup audit failed: {output}")


def network_panic_killswitch():
    if not confirm_destructive_action("Network Panic", "Disable all active network adapters now?"):
        return
    code, output = _run_process(["powershell.exe", "-NoProfile", "-Command",
        "Get-NetAdapter | Where-Object Status -eq 'Up' | Disable-NetAdapter -Confirm:$false"], timeout=60)
    _jarvis_notice("Active network adapters disabled." if code == 0 else f"Network panic failed: {output}")


def encrypt_file():
    path = _choose_path("Choose file to encrypt")
    if not path:
        return
    try:
        from cryptography.fernet import Fernet
        key_path = BASE_DIR / ".jarvis.key"
        key = key_path.read_bytes() if key_path.exists() else Fernet.generate_key()
        if not key_path.exists():
            key_path.write_bytes(key)
        target = Path(path)
        target.with_suffix(target.suffix + ".jarvis").write_bytes(Fernet(key).encrypt(target.read_bytes()))
        _jarvis_notice("Encrypted copy created. The original file was preserved.")
    except ImportError:
        _jarvis_notice("File encryption needs: pip install cryptography")
    except Exception as exc:
        _jarvis_notice(f"Encryption error: {exc}")


def handle_jarvis_automation(text):
    low = text.lower().strip()
    # Keep direct keyboard and daily-life commands ahead of broad legacy
    # substring matches such as "time", "gmail", and "translate".
    if low in {
        "open youtube reels and set it scroll mode",
        "open youtube reels and turn on scroll mode",
        "open youtube shorts and set it scroll mode",
        "open youtube shorts and turn on scroll mode",
        "ইউটিউব রিলস খোলো এবং স্ক্রল মোড চালু করো",
    }:
        open_youtube_reels_and_scroll_mode()
        return True

    keyboard_actions = {
        "press enter": ("Enter", lambda: pyautogui.press("enter")),
        "hit enter": ("Enter", lambda: pyautogui.press("enter")),
        "এন্টার চাপো": ("Enter", lambda: pyautogui.press("enter")),
        "এন্টার চাপ": ("Enter", lambda: pyautogui.press("enter")),
        "এন্টার চাপুন": ("Enter", lambda: pyautogui.press("enter")),
        "press space": ("Space", lambda: pyautogui.press("space")),
        "স্পেস চাপো": ("Space", lambda: pyautogui.press("space")),
        "স্পেস চাপুন": ("Space", lambda: pyautogui.press("space")),
        "press backspace": ("Backspace", lambda: pyautogui.press("backspace")),
        "ব্যাকস্পেস চাপো": ("Backspace", lambda: pyautogui.press("backspace")),
        "ব্যাকস্পেস চাপুন": ("Backspace", lambda: pyautogui.press("backspace")),
        "press tab": ("Tab", lambda: pyautogui.press("tab")),
        "ট্যাব চাপো": ("Tab", lambda: pyautogui.press("tab")),
        "ট্যাব চাপুন": ("Tab", lambda: pyautogui.press("tab")),
        "press escape": ("Escape", lambda: pyautogui.press("esc")),
        "press esc": ("Escape", lambda: pyautogui.press("esc")),
        "এস্কেপ চাপো": ("Escape", lambda: pyautogui.press("esc")),
        "copy this": ("Copy", lambda: pyautogui.hotkey("ctrl", "c")),
        "এটা কপি করো": ("Copy", lambda: pyautogui.hotkey("ctrl", "c")),
        "paste here": ("Paste", lambda: pyautogui.hotkey("ctrl", "v")),
        "এখানে পেস্ট করো": ("Paste", lambda: pyautogui.hotkey("ctrl", "v")),
        "select all": ("Select all", lambda: pyautogui.hotkey("ctrl", "a")),
        "সব সিলেক্ট করো": ("Select all", lambda: pyautogui.hotkey("ctrl", "a")),
        "save file": ("Save", lambda: pyautogui.hotkey("ctrl", "s")),
        "ফাইল সেভ করো": ("Save", lambda: pyautogui.hotkey("ctrl", "s")),
        "undo": ("Undo", lambda: pyautogui.hotkey("ctrl", "z")),
        "আনডু করো": ("Undo", lambda: pyautogui.hotkey("ctrl", "z")),
        "redo": ("Redo", lambda: pyautogui.hotkey("ctrl", "y")),
        "রিডু করো": ("Redo", lambda: pyautogui.hotkey("ctrl", "y")),
    }
    for phrase, (action_name, action) in keyboard_actions.items():
        if low == phrase or low.endswith(" " + phrase):
            _keyboard_action(action_name, action, f"{action_name} command sent.")
            return True

    typed_text = extract_after(text, ["type ", "টাইপ করো ", "লিখো "])
    if typed_text:
        type_active_text(typed_text)
        return True

    if low in {"open gmail", "জিমেইল খোলো", "জিমেইল খুলে দাও"}:
        open_gmail_web()
        return True
    if low in {"open chatgpt", "open chat gpt", "চ্যাটজিপিটি খোলো", "চ্যাট জিপিটি খোলো"}:
        open_chatgpt_web()
        return True

    location = extract_after(text, [
        "find on map ", "find in map ", "ম্যাপে খুঁজো ", "ম্যাপে খুঁজে দাও ",
    ])
    if location:
        find_location_on_map(location)
        return True

    translation = extract_after(text, [
        "translate ", "translate to bengali ", "বাংলায় অনুবাদ করো ",
        "বাংলায় অনুবাদ করো ",
    ])
    if translation and low not in {"translate selected", "translate the selected sentence to bengali"}:
        translate_text_to_bengali(translation)
        return True

    if low in {"what time is it", "what is the time", "এখন কয়টা বাজে", "এখন কয়টা বাজে"}:
        announce_current_time()
        return True
    if low in {"what is today's date", "what is todays date", "আজকের তারিখ কী", "আজকের তারিখ কি"}:
        announce_current_date()
        return True

    if matches_any(low, [
        "somoy tv live", "play somoy tv live",
        "সময় টিভি লাইভ", "সময় টিভি লাইভ",
    ]):
        safe_open(SOMOY_LIVE_URL)
        log_message("REXA", "সময় টিভির লাইভ সম্প্রচার চালু করছি।")
        speak("সময় টিভির লাইভ সম্প্রচার চালু করছি।", voice_name="bn-BD-NabanitaNeural")
        return True
    if matches_any(low, [
        "somoy tv news", "tell me somoy tv news", "somoy news",
        "সময় টিভির খবর", "সময় সংবাদ কি", "সময় টিভি",
        "সময় টিভির খবর", "সময় সংবাদ কি", "সময় টিভি",
    ]):
        somoy_tv_news()
        return True
    if low.startswith("wikipedia "):
        search_wikipedia_query(text[len("wikipedia "):])
        return True
    if low in {"bengali mode", "bangla mode", "বাংলা মোড", "বাংলা মোড চালু করো"}:
        set_language_mode("bengali")
        return True
    if low in {"english mode", "ইংরেজি মোড", "ইংরেজি মোড চালু করো"}:
        set_language_mode("english")
        return True
    if low in {
        "minimize", "minimise", "minimize all", "minimise all",
        "minimize all apps", "minimise all apps", "minimize everything",
        "minimise everything", "সব উইন্ডো ছোট করো", "সব অ্যাপ ছোট করো",
    }:
        minimize_all_windows()
        return True
    if low in {
        "make it full screen", "make it fullscreen", "make this full screen",
        "make this fullscreen", "maximize this window", "maximise this window",
        "maximize active window", "full screen this app",
    }:
        maximize_active_window()
        return True
    if matches_any(low, {
        "please make it full screen", "make the app full screen",
        "make the window full screen", "full screen this window",
        "maximize the app", "maximise the app",
    }):
        maximize_active_window()
        return True
    if matches_any(low, {
        "see me all minimize apps", "see me all minimise apps",
        "make all apps minimize", "make all apps minimise",
        "minimize all open apps", "minimise all open apps",
        "please minimize all apps", "please minimise all apps",
    }):
        minimize_all_windows()
        return True
    exact = {
        "protocol veronica": protocol_veronica, "activate protocol veronica": protocol_veronica,
        "clean slate": protocol_clean_slate, "protocol clean slate": protocol_clean_slate,
        "house party": protocol_house_party, "protocol house party": protocol_house_party,
        "sentry mode": protocol_sentry, "stealth mode": protocol_stealth,
        "threat assessment": threat_assessment, "gpu telemetry": gpu_telemetry,
        "gpu temperature": gpu_telemetry, "battery wear report": battery_wear_report,
        "flush dns": flush_dns, "send email": send_secure_email,
        "git status": lambda: git_action("status"), "git commit": lambda: git_action("commit"),
        "git push": lambda: git_action("push"), "git pull": lambda: git_action("pull"),
        "docker up": lambda: docker_action("up"), "docker down": lambda: docker_action("down"),
        "open vscode workspace": open_vscode_workspace, "run project tests": run_project_tests,
        "organize downloads": auto_organize_downloads, "find duplicate files": find_duplicate_files,
        "secure shred file": secure_shred_file, "ocr screen": screen_ocr,
        "read screen text": screen_ocr, "decode qr code": decode_qr_from_screen,
        "cursor color picker": cursor_color_picker, "pick cursor color": cursor_color_picker,
        "search arxiv": search_arxiv, "arxiv paper search": search_arxiv,
        "extract youtube mp3": extract_youtube_mp3, "youtube to mp3": extract_youtube_mp3,
        "summarize text file": summarize_text_file, "summarize document": summarize_text_file,
        "morning briefing": morning_briefing, "record expense": expense_entry,
        "wake on lan": wake_on_lan, "arp scan": arp_scan, "port scan": port_scan,
        "startup apps audit": startup_apps_audit, "network panic": network_panic_killswitch,
        "encrypt file": encrypt_file,
        "smart home webhook": smart_home_webhook,
        "turn on smart lights": lambda: smart_home_toggle("lights", True),
        "turn off smart lights": lambda: smart_home_toggle("lights", False),
        "turn on smart plug": lambda: smart_home_toggle("plug", True),
        "turn off smart plug": lambda: smart_home_toggle("plug", False),
        "open youtube reels": open_youtube_reels, "youtube reels open": open_youtube_reels,
        "open youtube reel": open_youtube_reels, "open youtube shorts": open_youtube_reels,
        "start auto swipe reels": start_auto_swipe_reels,
        "active auto swipe reels": start_auto_swipe_reels,
        "active auto syap reels": start_auto_swipe_reels,
        "auto teels": start_auto_swipe_reels,
        "start auto teels": start_auto_swipe_reels,
        "start automatic reels": start_auto_swipe_reels,
        "stop auto swipe reels": stop_auto_swipe_reels,
        "stop automatic reels": stop_auto_swipe_reels,
        "stop auto teels": stop_auto_swipe_reels,
    }
    if low in exact:
        exact[low](); return True
    normalized = re.sub(r"\s+", " ", low)
    if "reel" in normalized or "short" in normalized:
        if any(term in normalized for term in ("stop", "disable", "cancel")):
            stop_auto_swipe_reels()
        elif any(term in normalized for term in ("swipe", "scroll", "start", "active", "automatic", "auto")):
            start_auto_swipe_reels()
        else:
            open_youtube_reels()
        return True
    catalog = globals().get("JARVIS_COMMAND_CATALOG", {})
    if low in catalog:
        catalog[low](); return True
    if low.startswith("kill process on port "):
        kill_port_process(low); return True
    if low.startswith("open desktop app "):
        open_desktop_app(text[len("open desktop app "):]); return True
    if matches_any(low, [
        "open vs code", "open v s code", "open vscode", "launch vs code",
        "launch v s code", "launch vscode", "open visual studio code",
        "open visual studio"
    ]):
        open_desktop_app("Visual Studio Code"); return True
    if matches_any(low, [
        "minimize vs code", "minimize v s code", "minimize vscode",
        "minimize visual studio code", "minimise vs code", "hide vs code"
    ]):
        minimize_vscode(); return True
    if matches_any(low, [
        "open antigravity", "open anti gravity", "launch antigravity",
        "open antigarveti", "launch antigarveti"
    ]):
        open_desktop_app("Antigravity"); return True
    if low.startswith("close desktop app "):
        close_desktop_app(text[len("close desktop app "):]); return True
    if low.startswith("scan ports"):
        port_scan(); return True
    if low.startswith("start a pomodoro") or low.startswith("start pomodoro"):
        start_pomodoro(_parse_reminder_minutes(low)); return True
    return False


# Explicit registry for the production command surface.  Keeping aliases in
# one place makes the supported automation count auditable and discoverable.
JARVIS_COMMAND_CATALOG = {
    **{f"protocol {name}": action for name, action in {
        "veronica": protocol_veronica, "clean slate": protocol_clean_slate,
        "house party": protocol_house_party, "sentry mode": protocol_sentry,
        "stealth mode": protocol_stealth, "threat assessment": threat_assessment,
    }.items()},
    "gpu telemetry": gpu_telemetry, "gpu temperature": gpu_telemetry,
    "battery wear report": battery_wear_report, "flush dns": flush_dns,
    "send secure email": send_secure_email, "send email": send_secure_email,
    "git status": lambda: git_action("status"), "git commit": lambda: git_action("commit"),
    "git push": lambda: git_action("push"), "git pull": lambda: git_action("pull"),
    "docker up": lambda: docker_action("up"), "docker down": lambda: docker_action("down"),
    "open vscode workspace": open_vscode_workspace, "run project tests": run_project_tests,
    "organize downloads": auto_organize_downloads, "find duplicate files": find_duplicate_files,
    "secure shred file": secure_shred_file, "ocr screen": screen_ocr,
    "read screen text": screen_ocr, "decode qr code": decode_qr_from_screen,
    "morning briefing": morning_briefing, "record expense": expense_entry,
    "wake on lan": wake_on_lan, "arp scan": arp_scan, "port scan": port_scan,
    "startup apps audit": startup_apps_audit, "network panic": network_panic_killswitch,
    "encrypt file": encrypt_file,
}

# Additional concrete aliases expose the existing Windows and browser tools
# through the same JARVIS registry, bringing the complete command surface well
# above one hundred real actions without duplicating their implementations.
JARVIS_COMMAND_CATALOG.update({
    "open file explorer": open_pc, "open desktop": open_desktop,
    "open downloads": open_downloads, "open documents": open_documents,
    "open notepad": open_notepad, "open calculator": open_calculator,
    "open paint": open_paint, "open camera": open_camera, "open command prompt": open_cmd,
    "open powershell": open_powershell, "open settings": open_settings,
    "minimize vs code": minimize_vscode, "minimize vscode": minimize_vscode,
    "minimize visual studio code": minimize_vscode,
    "open task manager": open_task_manager, "open chrome": open_chrome,
    "open edge": open_edge, "open spotify": open_spotify, "open wifi settings": open_wifi_settings,
    "open bluetooth settings": open_bluetooth_settings, "open sound settings": open_sound_settings,
    "open display settings": open_display_settings, "open windows update": open_windows_update,
    "open recycle bin": open_recycle_bin_folder, "open startup folder": open_startup_folder,
    "open temp folder": open_temp_folder, "open control panel": open_control_panel,
    "open device manager": open_device_manager, "restart explorer": restart_explorer,
    "clear clipboard": clear_clipboard, "copy time to clipboard": copy_time_to_clipboard,
    "copy date to clipboard": copy_date_to_clipboard, "take screenshot": take_screenshot,
    "screenshot active window": screenshot_active_window, "start screen recording": toggle_screen_recording,
    "stop screen recording": toggle_screen_recording, "volume up": volume_up,
    "volume down": volume_down, "mute volume": volume_mute, "lock pc": lock_pc,
    "restart pc": restart_pc, "cancel shutdown": cancel_shutdown, "sleep pc": sleep_pc,
    "show system info": system_info, "show network info": network_info,
    "show battery": check_battery_percent, "check drive space": check_drive_space,
    "open google": lambda: safe_open("https://www.google.com/"),
    "open wikipedia": open_wikipedia, "open github": open_github,
    "open slack": open_slack, "open teams": open_teams, "open linkedin": open_linkedin,
    "open notion": open_notion, "open canva": open_canva, "open dropbox": open_dropbox,
    "open outlook": open_outlook, "open maps": open_maps, "open gmail": open_gmail_inbox,
    "open calendar": open_google_calendar, "open drive": open_google_drive,
    "open youtube": youtube_open, "close youtube": youtube_close_selenium,
    "youtube play pause": youtube_pause_play, "youtube replay": youtube_replay,
    "youtube next": youtube_next, "youtube previous": youtube_previous,
    "youtube forward": youtube_forward, "youtube backward": youtube_backward,
    "youtube mute": youtube_mute_toggle, "youtube fullscreen": youtube_fullscreen,
    "youtube volume up": youtube_volume_up, "youtube volume down": youtube_volume_down,
    "youtube subtitles": youtube_toggle_subtitles, "youtube refresh": browser_refresh,
    "browser back": lambda: _browser_worker("GOING BACK", lambda driver: driver.back()),
    "browser forward": lambda: _browser_worker("GOING FORWARD", lambda driver: driver.forward()),
    "new browser tab": browser_new_tab, "close browser tab": browser_close_tab,
    "reopen browser tab": browser_reopen_tab, "incognito browser": browser_incognito,
    "bookmark page": browser_bookmark_page, "scroll page down": lambda: browser_scroll("down"),
    "scroll page up": lambda: browser_scroll("up"), "open tiktok": open_tiktok,
    "open instagram": open_instagram, "open messenger": open_messenger,
    "open whatsapp": lambda: safe_open("https://web.whatsapp.com/"),
    "set reminder": lambda: set_reminder(simpledialog.askstring("Reminder", "Reminder:" ) or ""),
    "show reminders": show_reminders, "add note": lambda: add_note(simpledialog.askstring("Note", "Note:") or ""),
    "show notes": show_notes, "clear notes": clear_notes, "roll dice": roll_dice,
    "flip coin": flip_coin, "tell joke": tell_joke, "quote of the day": quote_of_the_day,
    "random fact": random_fact, "affirmation of the day": affirmation_of_the_day,
    "show tasks": show_tasks, "clear tasks": clear_tasks, "show routine": show_routine,
    "stop routine": clear_routine, "generate password": generate_password,
    "currency converter": lambda: convert_currency_dedicated(""), "news headlines": news_headlines,
    "open amazon": lambda: safe_open("https://www.amazon.com/"), "open chatgpt": open_chatgpt,
})


# ============================================================
# SPECIAL COMMANDS
# ============================================================
def handle_special_command(text):
    global web_assistant_mode
    low = text.lower().strip()

    if matches_any(low, [
        "what's on my screen", "whats on my screen", "what is on my screen",
        "look at my screen", "analyze my screen", "analyze the screen",
        "explain this chart", "explain the chart", "explain this diagram",
        "explain the diagram", "read what's written on my screen",
        "read whats written on my screen", "read my screen",
        "fix this code error", "look at my screen and fix this code error",
        "আমার স্ক্রিনে কী আছে দেখো", "আমার স্ক্রিনে কি আছে দেখো",
        "স্ক্রিনের এরর দেখে সমাধান বলো", "স্ক্রিনের ছবিটা বুঝিয়ে দাও",
        "স্ক্রিনের ছবিটা বুঝিয়ে দাও", "স্ক্রিনের লেখাগুলো পড়ো",
        "স্ক্রিনের লেখাগুলো পড়ো", "স্ক্রিন দেখো", "স্ক্রিন বিশ্লেষণ করো",
    ]):
        analyze_screen_with_vision(text)
        return True

    workspace_presets = {
        "coding": [
            "activate coding mode", "coding mode", "কোডিং মোড চালু করো",
        ],
        "focus": [
            "activate focus mode", "focus mode", "ফোকাস মোড চালু করো",
        ],
        "meeting": [
            "activate meeting mode", "meeting mode", "মিটিং মোড চালু করো",
        ],
        "night": [
            "activate night mode", "night mode", "নাইট মোড চালু করো",
        ],
        "gaming": [
            "activate gaming mode", "gaming mode", "গেমিং মোড চালু করো",
        ],
    }
    for preset, triggers in workspace_presets.items():
        if matches_any(low, triggers):
            activate_workspace_preset(preset)
            return True

    if _computer_use_action(text):
        return True

    if low.startswith(("run in sandbox", "run this safely", "execute safely",
                        "run a safe python script", "sandbox script")):
        run_self_healing_sandbox(text)
        return True

    wants_generation = any(word in low for word in ("create", "generate", "write", "make"))
    save_target = any(word in low for word in ("download", "downloads", "folder", "save"))
    if wants_generation and save_target and any(
        word in low for word in ("application", "app", "program")
    ):
        generate_content_to_downloads(text, "application")
        return True

    if wants_generation and save_target and any(
        word in low for word in ("note", "notes", "memo", "document")
    ):
        generate_content_to_downloads(text, "note")
        return True

    if handle_jarvis_automation(text):
        return True

    # Keep the supported PC-control prompts together, before broad legacy
    # phrase matching can route them to a less specific action.
    if handle_pc_automation_command(text):
        return True

    if matches_any(low, [
        "fullscreen chrome", "full screen chrome", "make chrome fullscreen",
        "make chrome full screen", "chrome browser fullscreen"
    ]):
        chrome_fullscreen()
        return True

    if matches_any(low, [
        "minimize chrome", "minimise chrome", "minimize google chrome",
        "hide chrome"
    ]):
        minimize_chrome()
        return True

    if matches_any(low, [
        "close chrome", "chrome close", "close google chrome",
        "exit chrome", "quit chrome"
    ]):
        close_chrome_safely()
        return True

    if state.get("awaiting_youtube_playlist"):
        if low in {"cancel", "never mind", "stop"}:
            state["awaiting_youtube_playlist"] = False
            log_message("REXA", "YouTube playlist selection cancelled.")
            speak("Playlist selection cancelled.")
            return True
        state["awaiting_youtube_playlist"] = False
        open_youtube_playlist_by_name(text)
        return True

    if state.get("awaiting_youtube_search"):
        if low in {"cancel", "never mind", "stop"}:
            state["awaiting_youtube_search"] = False
            log_message("REXA", "YouTube search cancelled.")
            return True
        state["awaiting_youtube_search"] = False
        youtube_search(text)
        return True

    if matches_any(low, [
        "serious mode", "serious question mode", "answer seriously",
        "be serious"
    ]):
        state["conversation_mode"] = "serious"
        memory["conversation_mode"] = "serious"
        save_memory(memory)
        log_message("REXA", "Serious mode is on. I will answer questions directly and carefully.")
        speak("Serious mode is on.")
        return True

    if matches_any(low, [
        "story mode", "start conversation mode", "let's talk", "lets talk",
        "talk with me", "গল্প করো"
    ]):
        state["conversation_mode"] = "story"
        memory["conversation_mode"] = "story"
        save_memory(memory)
        log_message("REXA", "Story mode is on. We can talk naturally.")
        speak("Story mode is on. Let's talk.")
        return True

    if matches_any(low, [
        "normal mode", "normal question mode", "regular mode",
        "be normal", "exit story mode"
    ]):
        state["conversation_mode"] = "normal"
        memory["conversation_mode"] = "normal"
        save_memory(memory)
        log_message("REXA", "Normal mode is on. I will answer naturally and helpfully.")
        speak("Normal mode is on.")
        return True

    if matches_any(low, ["what mode am i in", "current conversation mode", "conversation mode"]):
        mode = state.get("conversation_mode", "normal").upper()
        log_message("REXA", f"Conversation mode: {mode}")
        return True

    if handle_memory_command(text):
        return True

    if matches_any(low, ["open python", "launch python", "open python idle", "open idle"]):
        open_python()
        return True

    if matches_any(low, ["close python", "close python idle", "close idle"]):
        close_python()
        return True

    if matches_any(low, [
        "open youtube search bar", "open search bar", "open screah bar",
        "open serach bar", "click search bar", "click youtube search",
        "click the youtube search bar"
    ]):
        open_youtube_search_bar()
        return True

    if matches_any(low, [
        "login to gmail", "log in to gmail", "sign in to gmail",
        "open gmail login"
    ]):
        open_gmail_login()
        return True

    if matches_any(low, [
        "open gmail inbox", "gmail inbox", "open my gmail",
        "open gmail", "check my gmail",
        "check my email inbox", "inbox checker"
    ]):
        check_gmail_inbox()
        return True

    if matches_any(low, ["check inbox", "check my inbox", "check messages"]):
        active_inbox = state.get("active_social_inbox", "")
        if active_inbox in {"tiktok", "facebook"}:
            check_social_inbox(active_inbox)
        else:
            log_message(
                "REXA",
                "Say 'check my TikTok inbox', 'check my Facebook inbox', "
                "or 'check my Gmail inbox'."
            )
        return True

    if matches_any(low, [
        "compose gmail", "write email", "open gmail compose",
        "new gmail", "compose an email"
    ]):
        open_gmail_compose()
        return True

    if matches_any(low, [
        "check youtube inbox", "youtube inbox", "open youtube inbox",
        "check my youtube inbox", "check notifications"
    ]):
        check_youtube_inbox()
        return True

    if matches_any(low, [
        "check tiktok inbox", "tiktok inbox", "open tiktok inbox",
        "check my tiktok inbox", "open my messages on tiktok",
        "check tiktok messages"
    ]):
        check_tiktok_inbox()
        return True

    if (
        ("tiktok" in low or state.get("active_social_inbox") == "tiktok")
        and ("message" in low or "conversation" in low or "chat" in low)
        and any(term in low for term in ("open", "show", "select", "number", "first", "second", "third"))
    ):
        message_number = parse_video_number(text) or 1
        open_tiktok_message(message_number)
        return True

    if matches_any(low, [
        "check facebook inbox", "check my facebook inbox",
        "open facebook inbox", "check messenger", "check my messenger",
        "check facebook messages"
    ]):
        check_facebook_inbox()
        return True

    if matches_any(low, [
        "open google calendar", "open my calendar", "calendar",
        "show my calendar"
    ]):
        open_google_calendar()
        return True

    if matches_any(low, [
        "open google drive", "go to google drive", "launch google drive",
        "show my drive"
    ]):
        open_google_drive()
        return True

    playlist_query = extract_after(text, ["open youtube playlist ", "open my playlist ", "open playlist ", "youtube playlist "])
    if playlist_query:
        open_youtube_playlist_by_name(playlist_query)
        return True

    if matches_any(low, [
        "open youtube playlist", "open my playlist", "open playlist",
        "show my playlists", "youtube playlist"
    ]):
        state["awaiting_youtube_playlist"] = True
        open_youtube_playlist()
        log_message("REXA", "Which YouTube playlist should I open?")
        speak("Which YouTube playlist should I open, sir?")
        return True

    if matches_any(low, [
        "open duckduckgo", "go to duckduckgo", "search with duckduckgo",
        "launch duckduckgo"
    ]):
        open_duckduckgo()
        return True

    if matches_any(low, [
        "open wikipedia", "go to wikipedia", "search wikipedia",
        "launch wikipedia"
    ]):
        open_wikipedia()
        return True

    if matches_any(low, [
        "open chatgpt desktop", "open chatgpt app", "launch chatgpt app",
        "open desktop chatgpt", "open chatgpt"
    ]):
        open_chatgpt_desktop()
        return True

    if matches_any(low, [
        "open chat gpt", "launch chatgpt", "launch chat gpt",
        "go to chatgpt", "go to chat gpt", "open chatgpt website"
    ]):
        open_chatgpt()
        return True

    if matches_any(low, [
        "close chatgpt", "close chat gpt", "exit chatgpt",
        "exit chat gpt", "quit chatgpt", "quit chat gpt"
    ]):
        close_chatgpt()
        return True

    if matches_any(low, ["show yesterday's activity", "show yesterday activity", "yesterday activity"]):
        show_yesterday_activity()
        return True

    if matches_any(low, ["forget yesterday's activity", "forget yesterday activity"]):
        forget_yesterday_activity()
        return True

    if matches_any(low, ["stop remembering browsing activity", "stop browsing memory", "disable browsing memory"]):
        set_activity_memory(False)
        return True

    if matches_any(low, ["remember my browsing activity", "enable browsing memory", "start browsing memory"]):
        set_activity_memory(True)
        return True

    if matches_any(low, [
        "exit fullscreen", "exit full screen", "leave fullscreen",
        "leave full screen", "exit youtube fullscreen",
        "exit youtube full screen"
    ]):
        youtube_exit_fullscreen()
        return True

    if matches_any(low, ["minimize youtube", "make youtube smaller"]):
        youtube_minimize_window()
        return True

    if matches_any(low, [
        "fullscreen youtube", "youtube fullscreen", "full screen youtube",
        "youtube full screen", "make youtube fullscreen",
        "make youtube full screen", "enter fullscreen", "enter full screen",
        "go fullscreen", "go full screen", "fullscreen the video",
        "full screen the video"
    ]):
        youtube_fullscreen()
        return True

    if matches_any(low, [
        "activate youtube scroll mode", "enable youtube scroll mode",
        "start youtube scroll mode", "youtube scroll mode on",
        "turn on youtube scroll mode", "youtube scroll mode active",
        "youtube scroll active", "yt scroll mode active",
        "activate yt scroll mode", "ইউটিউব স্ক্রল মোড চালু করো",
    ]):
        set_youtube_scroll_mode(True)
        return True

    if matches_any(low, [
        "deactivate youtube scroll mode", "disable youtube scroll mode",
        "stop youtube scroll mode", "youtube scroll mode off",
        "turn off youtube scroll mode", "ইউটিউব স্ক্রল মোড বন্ধ করো",
    ]):
        set_youtube_scroll_mode(False)
        return True

    if matches_any(low, ["scroll to the top", "go to the top", "scroll youtube to the top"]):
        youtube_scroll_edge("top")
        return True

    if matches_any(low, ["scroll to the bottom", "go to the bottom", "scroll youtube to the bottom"]):
        youtube_scroll_edge("bottom")
        return True

    if "scroll" in low and (
        "youtube" in low
        or youtube_scroll_mode_active
        or yt_context.get("mode") in {"browsing", "search", "playing"}
    ):
        direction = "up" if "up" in low or "back up" in low else "down"
        amount = "little" if any(word in low for word in ["little", "a bit", "slightly"]) else "lot" if any(word in low for word in ["lot", "a lot", "far"]) else "normal"
        youtube_scroll(amount, direction)
        return True

    if matches_any(low, ["web assistant mode", "enable web assistant", "browser assistant mode"]):
        web_assistant_mode = True
        log_message("REXA", "Web Assistant Mode is on. I will focus on the current webpage.")
        speak("Web Assistant Mode is on.")
        return True

    if matches_any(low, ["stop web assistant mode", "disable web assistant", "exit web assistant mode"]):
        web_assistant_mode = False
        log_message("REXA", "Web Assistant Mode is off.")
        speak("Web Assistant Mode is off.")
        return True

    url = extract_after(text, ["open website ", "go to website ", "go to url ", "navigate to ", "take me to "])
    if url:
        browser_open_url(url)
        return True

    if matches_any(low, ["read this page", "read webpage", "read the page"]):
        browser_read_page()
        return True

    if matches_any(low, ["what can i do here", "inspect this webpage", "show page controls"]):
        browser_page_context()
        return True

    find_text = extract_after(text, ["find text ", "find on this page ", "find the "])
    if find_text:
        browser_find_text(find_text)
        return True

    result_match = re.search(r"(?:click|open) (?:the )?(?:result|link|item) (\d+|first|second|third)", low)
    if result_match:
        positions = {"first": 1, "second": 2, "third": 3}
        number = positions.get(result_match.group(1), int(result_match.group(1)) if result_match.group(1).isdigit() else 1)
        browser_click_result(number)
        return True

    click_text = extract_after(text, ["click the ", "click "])
    if click_text and not any(word in click_text.lower() for word in ["result", "link"]):
        browser_click_text(click_text)
        return True

    fill_match = re.match(r"(?:fill|type in) (.+?) (?:with|as) (.+)$", text, flags=re.IGNORECASE)
    if fill_match:
        browser_fill_box(fill_match.group(1), fill_match.group(2))
        return True

    if matches_any(low, ["submit this form", "submit the form", "send this form"]):
        browser_submit_form()
        return True

    if matches_any(low, ["scroll up", "go up on the page"]):
        browser_scroll("up")
        return True

    if matches_any(low, ["scroll down", "go down on the page"]):
        browser_scroll("down")
        return True

    if matches_any(low, ["go back in browser", "browser back", "go back"]):
        _browser_worker("GOING BACK", lambda driver: driver.back())
        return True

    if matches_any(low, ["go forward in browser", "browser forward", "go forward"]):
        _browser_worker("GOING FORWARD", lambda driver: driver.forward())
        return True

    if matches_any(low, ["refresh webpage", "refresh this page", "reload webpage"]):
        _browser_worker("REFRESHING WEBPAGE", lambda driver: driver.refresh())
        return True

    if matches_any(low, ["open a new browser tab", "new browser tab", "create a new tab"]):
        browser_new_tab()
        return True

    tab_match = re.search(r"(?:switch to|go to) (?:browser )?tab (\d+)", low)
    if tab_match:
        browser_switch_tab(int(tab_match.group(1)))
        return True

    if matches_any(low, [
        "minimize",
        "minimize window",
        "minimize rexa",
        "rexa minimize",
        "minimize the window",
        "window minimize",
        "minimise",
        "minimise window",

        "উইন্ডো মিনিমাইজ করো",
        "মিনিমাইজ করো",
        "মিসা মিনিমাইজ করো",
        "উইন্ডো ছোট করো",
    ]):
        minimize_window()
        return True

    # ---------- YOUTUBE ----------

    if matches_any(low, [
        "save it to my playlist",
        "save it my playlist",
        "save this to my playlist",
        "save this video to my playlist",
        "add it to my playlist",
        "add this video to my playlist",
        "save video to playlist",
        "প্লেলিস্টে সেভ করো",
        "আমার প্লেলিস্টে সেভ করো",
    ]) or (
        ("save" in low or "add" in low)
        and ("playlist" in low or "play list" in low)
    ):
        youtube_save_to_playlist()
        return True

    if matches_any(low, [
        "close youtube", "youtube close", "exit youtube","close the youtube", "youtube exit", "youtube quit","close",
    ]):
        youtube_close_selenium()
        return True
        # ---------- YOUTUBE SELENIUM (new) ----------

    # Context query
    if matches_any(low, [
        "youtube context", "what is playing", "which video is playing",
        "what video is playing", "what video playing", "who is video playing",
        "who is video is playing", "which video playing", "current youtube", "youtube status",
        "এখন কি চলছে", "কোন ভিডিও চলছে", "Akon ki cholche", "Akon ki chol se",
    ]):
        context = get_current_youtube_context()
        log_message("REXA", context)
        playing = next(
            (part for part in context.split(" | ") if part.startswith("Playing: ")),
            context,
        )
        speak(playing)
        return True

    if matches_any(low, [
        "stop video", "stop the video", "pause video", "pause the video",
        "stop youtube video", "pause youtube video", "ভিডিও বন্ধ করো",
        "ভিডিও থামাও", "ইউটিউব ভিডিও থামাও",
    ]):
        youtube_stop_video()
        return True

    # Open YouTube in Selenium browser
    if matches_any(low, [
        "open youtube browser", "launch youtube", "go to youtube",
        "start youtube", "youtube browser",
        "selenium youtube", "ইউটিউব খোলো", "ইউটিউব চালু করো",
    ]):
        open_youtube()
        return True

    # YouTube search via Selenium
    combined_search_match = re.search(
        r"\b(?:open|launch|go to)\s+youtube\s+and\s+search(?:\s+for)?\s+(.+)$",
        text,
        re.IGNORECASE,
    )
    if combined_search_match:
        youtube_search(combined_search_match.group(1).strip())
        return True

    yt_search_triggers = [
        "search youtube for ", "youtube search ", "ইউটিউবে খোঁজো ",
        "ইউটিউবে সার্চ করো ", "youtube te search koro ",
        "find ", "look up ", "ইউটিউবে ", "youtube e khojo ",
    ]
    sq_new = extract_after(text, yt_search_triggers)
    if sq_new:
        youtube_search(sq_new)
        return True

    # Play by number from search results
    # Matches: "play number 2", "play 3rd", "২ নম্বর চালাও",
    # "play the first one", "১ নম্বরটা চালাও", "second video chalaو"
    play_number_triggers = [
        "play number ", "play result ", "result number ",
        "play the ", "নম্বর চালাও", "নম্বরটা চালাও",
        "number er video", "চালাও নম্বর ", "play #",
        "video number ", "play no ",
    ]

    if any(p in low for p in [
        "play first 3", "play first three", "play the first 3",
        "play the first three"
    ]):
        youtube_play_search_range(1, 3)
        return True

    if any(p in low for p in [
        "play last 3", "play last three", "play the last 3",
        "play the last three"
    ]):
        youtube_play_search_range(max(1, len(yt_search_results) - 2), len(yt_search_results))
        return True

    first_one_patterns = [
        "play first one", "play the first one", "play first",
        "first one", "first video", "play first result"
    ]
    if any(p in low for p in first_one_patterns) and "last" not in low:
        if yt_search_results:
            youtube_play_number(1)
            return True

    last_one_patterns = [
        "play last one", "play the last one", "play last",
        "last one", "last video", "play last result"
    ]
    if any(p in low for p in last_one_patterns) or "শেষ" in text:
        if yt_search_results:
            youtube_play_number(len(yt_search_results))
            return True

    found_play_number = False
    for trigger in play_number_triggers:
        if trigger in low or trigger in text:
            num = parse_video_number(text)
            if num is not None:
                youtube_play_number(num)
                found_play_number = True
                break

    # Also catch bare patterns like "3 nmbr chalao" or "৩ চালাও"
    if not found_play_number:
        if (
            ("চালাও" in text or "chalao" in low or "play" in low)
            and any(str(d) in text for d in range(1, 11))
            or any(b in text for b in BANGLA_DIGIT_MAP)
            or any(w in text for w in BANGLA_WORD_MAP)
            or any(w in low for w in ENGLISH_ORDINAL_MAP)
        ):
            num = parse_video_number(text)
            if num is not None and yt_search_results:
                youtube_play_number(num)
                found_play_number = True

    if found_play_number:
        return True

    if matches_any(low, [
        "play a video from my playlist",
        "play a video from playlist",
        "play from my playlist",
        "play something from my playlist",
        "play my playlist",
        "play any one from my playlist",
        "play anyone from my playlist",
        "play any video from my playlist",
        "play a playlist video",
    ]):
        play_from_my_playlist()
        return True

    # Playlist play by number
    if any(p in low for p in [
        "open first playlist item", "play first playlist item",
        "first playlist item", "open first item in playlist"
    ]):
        youtube_playlist_play_number(1)
        return True

    if any(p in low for p in [
        "open last playlist item", "play last playlist item",
        "last playlist item", "open last item in playlist"
    ]):
        youtube_playlist_play_number(-1)
        return True

    playlist_triggers = [
        "playlist number ", "playlist video ", "play playlist ",
        "playlist e ", "প্লেলিস্ট নম্বর ", "video from playlist",
        "from playlist", "play video ", "play the ", "play number "
    ]
    for trigger in playlist_triggers:
        if trigger in low:
            if "playlist" in low or "from playlist" in low:
                num = parse_video_number(text)
                if num is not None:
                    youtube_playlist_play_number(num)
                    return True

    if "playlist" in low and any(str(d) in text for d in range(1, 11)):
        num = parse_video_number(text)
        if num is not None:
            youtube_playlist_play_number(num)
            return True

    # Next / Previous using Selenium context awareness
    if matches_any(low, [
        "youtube next",
        "next video",
        "next playlist video",
        "play next playlist video",
        "skip video",
        "play next",
        "পরের ভিডিও",
        "next ta chala",
        "পরেরটা চালাও",
    ]):
        youtube_next()
        return True

    if matches_any(low, [
        "play another",
        "play another video",
        "next one",
        "play the next one",
    ]) and (
        yt_context.get("mode") in {"playlist", "playing", "search"}
        or state.get("selected_youtube_playlist_url")
    ):
        youtube_next()
        return True
    # Help
    if matches_any(low, [
        "help", "commands", "what can you do"
    ]):
        show_help()
        return True

    # Greeting
    if matches_any(low, [
        "hi rexa", "hello rexa", "hey rexa",
        "wake up", "rexa wake up",
    ]) or low in {"hi", "hello", "hey"}:
        profile = _load_profile()
        name = profile.get("name", "")
        study = profile.get("study", "")

        greeting_text = f"Hey {name}!" if name else "Hey there!"

        followup = (
            f"How's {study} going? Anything I can help with today?"
            if study else
            "How are you doing today?"
        )

        answer = f"{greeting_text} \U0001F44B\nI'm here with you.\n{followup}"

        log_message("REXA", answer)
        speak(f"{greeting_text} {followup}")

        return True

    # Time
    if matches_any(low, ["what time", " time"]) or low == "time":
        answer = (
            "The time is "
            + now_text()
        )

        log_message("REXA", answer)
        speak(answer)

        return True

    # Date
    if matches_any(low, ["what date", "today's date", "date"]):
        answer = (
            "Today is "
            + date_text()
        )

        log_message("REXA", answer)
        speak(answer)

        return True

    # ---------- PERSONAL MEMORY (NEW) ----------
    # REXA can now actually remember things about you between
    # messages: your name, what you're studying, and anything else
    # you ask it to remember.

    nameq = extract_after(text, ["call me ", "my name is "])
    if nameq:
        set_profile_field("name", nameq)
        answer = f"Got it — I'll call you {nameq.strip()} from now on! \U0001F44B"
        log_message("REXA", answer)
        speak(answer)
        return True

    studyq = extract_after(text, [
        "remember i'm studying ", "remember i am studying ",
        "remember im studying ", "i'm studying ", "i am studying "
    ])
    if studyq:
        set_profile_field("study", studyq)
        answer = (
            f"Noted — you're studying {studyq.strip()}. I'll keep that "
            "in mind and check in on how it's going."
        )
        log_message("REXA", answer)
        speak(answer)
        return True

    if matches_any(low, [
        "what do you know about me", "show my profile", "my profile"
    ]):
        show_profile()
        return True

    if matches_any(low, [
        "forget about me", "forget my profile", "delete my profile"
    ]):
        forget_profile()
        return True

    rememberq = extract_after(text, ["remember that ", "remember "])
    if rememberq and not low.startswith("remind"):
        add_profile_note(rememberq)
        answer = "Got it, I'll remember that about you."
        log_message("REXA", answer)
        speak(answer)
        return True

    # ---------- PERSONAL ASSISTANT (NEW COMMANDS) ----------

    routineq = extract_after(text, ["set routine ", "create routine "])
    if routineq:
        routine_text = routineq
        interval_text = "7 minutes"
        if " every " in routineq.lower():
            split_at = routineq.lower().rfind(" every ")
            routine_text = routineq[:split_at]
            interval_text = routineq[split_at + len(" every "):]
        set_routine(routine_text, interval_text)
        return True

    if matches_any(low, ["show my routine", "routine status", "what is my routine"]):
        show_routine()
        return True

    if matches_any(low, ["stop routine", "clear routine", "disable routine"]):
        clear_routine()
        return True

    routine = _load_routine()
    if routine.get("awaiting_answer") and matches_any(low, [
        "yes", "yes i did", "done", "i did it", "finished", "completed"
    ]):
        routine["awaiting_answer"] = False
        _save_routine(routine)
        log_message("REXA", f"Good. I marked '{routine['activity']}' as done.")
        speak("Good. I marked it as done.")
        return True

    if routine.get("awaiting_answer") and matches_any(low, [
        "no", "not yet", "not done", "i haven't", "still working"
    ]):
        routine["awaiting_answer"] = False
        _save_routine(routine)
        log_message("REXA", f"Okay. Keep going with {routine['activity']}.")
        speak(f"Okay. Keep going with {routine['activity']}.")
        return True

    rq = extract_after(text, ["set a reminder to ", "remind me to "])
    if rq:
        when_text = "10 minutes"
        reminder_text = rq
        if " in " in rq:
            reminder_text, when_text = rq.rsplit(" in ", 1)
        set_reminder(reminder_text.strip(), when_text.strip())
        return True

    if matches_any(low, ["show my reminders", "my reminders"]):
        show_reminders()
        return True

    nq = extract_after(text, ["add a note: ", "add a note ", "note: "])
    if nq:
        add_note(nq)
        return True

    if matches_any(low, ["show my notes", "my notes"]):
        show_notes()
        return True

    if matches_any(low, ["clear my notes", "delete my notes"]):
        clear_notes()
        return True

    if matches_any(low, ["roll a dice", "roll dice", "roll the dice"]):
        roll_dice()
        return True

    if matches_any(low, ["flip a coin", "flip coin", "toss a coin"]):
        flip_coin()
        return True

    if matches_any(low, ["tell me a joke", "tell a joke", "joke"]):
        tell_joke()
        return True

    dq = extract_after(text, ["define "])
    if dq:
        define_word(dq)
        return True

    cq = extract_after(text, ["convert currency ", "currency convert "])
    if cq:
        convert_currency_dedicated(cq)
        return True

    if matches_any(low, ["convert currency"]):
        convert_currency_dedicated("")
        return True

    uq = extract_after(text, ["convert units ", "convert "])
    if uq:
        convert_units(uq)
        return True

    sq2 = extract_after(text, ["check stock price of ", "stock price of ", "stock price "])
    if sq2:
        check_stock_price(sq2)
        return True

    ccq = extract_after(text, ["check crypto price of ", "crypto price of ", "crypto price "])
    if ccq:
        check_crypto_price(ccq)
        return True

    if matches_any(low, ["open maps", "open google maps"]):
        open_maps()
        return True

    dirq = extract_after(text, ["get directions to ", "directions to "])
    if dirq:
        get_directions(dirq)
        return True

    if matches_any(low, ["quote of the day", "give me a quote"]):
        quote_of_the_day()
        return True

    amq = extract_after(text, ["search amazon for ", "amazon search "])
    if amq:
        search_amazon(amq)
        return True

    if matches_any(low, ["open github"]):
        open_github()
        return True

    if matches_any(low, ["open slack"]):
        open_slack()
        return True

    if matches_any(low, ["open teams", "open microsoft teams"]):
        open_teams()
        return True

    if matches_any(low, ["open linkedin", "go to linkedin", "launch linkedin"]):
        open_linkedin()
        return True

    if matches_any(low, ["open notion", "go to notion", "launch notion"]):
        open_notion()
        return True

    if matches_any(low, ["open canva", "go to canva", "launch canva"]):
        open_canva()
        return True

    if matches_any(low, ["open dropbox", "go to dropbox", "launch dropbox"]):
        open_dropbox()
        return True

    if matches_any(low, ["open outlook", "go to outlook", "launch outlook"]):
        open_outlook()
        return True

    new_open_sites = {
        "discord": "https://discord.com/app",
        "telegram": "https://web.telegram.org/",
        "reddit": "https://www.reddit.com/",
        "twitter": "https://x.com/",
        "x": "https://x.com/",
        "pinterest": "https://www.pinterest.com/",
        "zoom": "https://zoom.us/join",
    }
    for site_name, site_url in new_open_sites.items():
        if matches_any(low, [
            f"open {site_name}", f"go to {site_name}",
            f"launch {site_name}"
        ]):
            safe_open(site_url)
            log_message("REXA", f"Opened {site_name.title()}.")
            return True

    url_query = extract_after(text, [
        "summarize this url:", "summarize this url ",
        "এই পেজের সারমর্ম বলো ", "এই পেজের সারমর্ম বলো:",
    ])
    if url_query and re.match(r"https?://", url_query.strip(), re.IGNORECASE):
        summarize_url(url_query)
        return True

    if matches_any(low, [
        "what is the latest news today", "latest news today",
        "আজকের তাজা খবর কী", "আজকের খবর কী",
    ]):
        news_headlines()
        return True

    web_query = extract_after(text, ["search the web for ", "search for ", "look up ", "find "])
    if web_query and not any(word in low for word in ["youtube", "google maps", "amazon", "github", "calendar", "gmail"]):
        web_search(web_query)
        return True

    ctq = extract_after(text, [
        "start a countdown timer for ", "countdown timer for ",
        "countdown timer ", "set a timer for ", "set timer for "
    ])
    if ctq:
        digits = "".join(ch for ch in ctq if ch.isdigit())
        start_countdown_timer(int(digits) if digits else 5)
        return True

    # ---------- 12 NEW PERSONAL ASSISTANT COMMANDS ----------

    wq = extract_after(text, ["weather in ", "weather for "])
    if wq:
        weather_in_city(wq)
        return True

    tcq = extract_after(text, ["what time is it in ", "time in ", "world clock "])
    if tcq:
        world_clock(tcq)
        return True

    ageq = extract_after(text, ["how old is someone born in ", "calculate age ", "age of someone born in "])
    if ageq:
        calculate_age(ageq)
        return True

    if matches_any(low, ["generate a password", "generate password", "create a password"]):
        pwq = extract_after(text, ["generate a ", "generate "])
        generate_password(pwq)
        return True

    wrq = extract_after(text, ["remind me to drink water every ", "water reminder every "])
    if wrq:
        water_reminder(wrq)
        return True

    if matches_any(low, ["remind me to drink water", "water reminder"]):
        water_reminder("60 minutes")
        return True

    mtq = extract_after(text, ["mark ", ])
    if mtq and ("as done" in low or " done" in low) and "task" not in mtq.lower()[:6]:
        clean = mtq.replace("as done", "").replace("done", "").strip(" '\"")
        mark_task_done(clean)
        return True

    if matches_any(low, ["clear my task list", "clear all tasks", "delete my task list"]):
        clear_tasks()
        return True

    if matches_any(low, ["random fact", "tell me a fact", "fun fact"]):
        random_fact()
        return True

    nwq = extract_after(text, ["news about ", "headlines about ", "news on "])
    if nwq:
        news_headlines(nwq)
        return True

    if matches_any(low, ["show me the news", "today's headlines", "top headlines", "open the news"]):
        news_headlines()
        return True

    rcq = extract_after(text, ["find a recipe for ", "recipe for ", "search recipe for "])
    if rcq:
        search_recipe(rcq)
        return True

    if matches_any(low, ["affirmation of the day", "give me an affirmation", "today's affirmation"]):
        affirmation_of_the_day()
        return True

    if matches_any(low, ["calculate bmi", "calculate my bmi", "what is my bmi"]):
        bmiq = extract_after(text, ["calculate bmi ", "calculate my bmi ", "bmi "])
        bmi_calculator(bmiq)
        return True

    # ---------- YOUTUBE ----------

    if matches_any(low, [
        "close youtube", "youtube close", "exit youtube"
    ]):
        youtube_close()
        return True

    if matches_any(low, [
        "skip the ad", "skip ad"
    ]):
        youtube_skip_ad()
        return True

    if matches_any(low, [
        "fast-forward 30", "fast forward 30", "forward 30 seconds"
    ]):
        _youtube_key_action(
            "YOUTUBE FORWARD 30",
            lambda: [pyautogui.press("l") for _ in range(3)],
            "Skipped forward 30 seconds.",
            "YouTube forward error",
            delay=0.2
        )
        return True

    if matches_any(low, [
        "rewind 10", "rewind 10 seconds"
    ]):
        youtube_backward()
        return True

    q = extract_after(text, ["set volume to "])
    if q:
        digits = "".join(ch for ch in q if ch.isdigit())
        if digits:
            youtube_set_volume_percent(digits)
            return True

    if matches_any(low, [
        "youtube play again", "replay youtube", "youtube replay",
        "play youtube again", "restart youtube video",
    ]):
        youtube_replay()
        return True

    if matches_any(low, [
        "youtube next", "next video", "skip video", "play next",
    ]):
        youtube_next()
        return True

    if matches_any(low, [
        "youtube previous", "previous video", "play previous",
    ]):
        youtube_previous()
        return True

    if matches_any(low, [
        "youtube forward", "forward video", "skip forward",
    ]):
        youtube_forward()
        return True

    if matches_any(low, [
        "youtube backward", "rewind video", "skip backward",
    ]):
        youtube_backward()
        return True

    if matches_any(low, [
        "youtube mute", "mute youtube", "unmute youtube",
    ]):
        youtube_mute_toggle()
        return True

    if matches_any(low, [
        "youtube fullscreen", "fullscreen youtube",
    ]):
        youtube_fullscreen()
        return True

    if matches_any(low, [
        "youtube volume up", "volume up youtube",
    ]):
        youtube_volume_up()
        return True

    if matches_any(low, [
        "youtube volume down", "volume down youtube",
    ]):
        youtube_volume_down()
        return True

    if matches_any(low, ["switch to tiktok"]):
        switch_to_tiktok()
        return True

    # ---------- CLOSE SPECIFIC APPS (NEW) ----------
    # Checked early so "close notepad" doesn't fall through to the
    # generic "notepad" match later (which would re-open it instead).

    close_commands = [
        (["close notepad"], close_notepad),
        (["close calculator"], close_calculator),
        (["close paint"], close_paint),
        (["close cmd", "close command prompt"], close_cmd),
        (["close powershell"], close_powershell),
        (["close chrome"], close_chrome),
        (["close edge"], close_edge),
        (["close spotify"], close_spotify),
        (["close task manager", "close taskmanager"], close_task_manager),
        (["close settings"], close_settings_app),
        (["close camera"], close_camera_app),
        (["close file explorer", "close my pc"], close_file_explorer),
    ]
    

    for phrases, action in close_commands:
        if matches_any(low, phrases):
            action()
            return True

    if matches_any(low, [
        "minimize this window", "minimize window"
    ]):
        minimize_all_windows()
        return True

    if matches_any(low, [
        "go to the home screen", "home screen"
    ]):
        go_to_home_screen()
        return True

    if matches_any(low, ["close all open tabs", "close all tabs"]):
        close_all_tabs()
        return True

    if matches_any(low, [
        "open chrome and go to google", "open chrome go to google"
    ]):
        open_chrome()

        def _later():
            time.sleep(2.0)
            safe_open("https://www.google.com/")

        threading.Thread(target=_later, daemon=True).start()
        return True

    if matches_any(low, [
        "youtube pause", "pause youtube", "youtube play",
        "play youtube", "resume youtube",
    ]):
        youtube_pause_play()
        return True

    if matches_any(low, [
        "tiktok next", "next tiktok", "scroll tiktok",
        "scroll down tiktok", "tiktok scroll",
    ]):
        tiktok_scroll_down()
        return True

    if matches_any(low, [
        "tiktok previous", "previous tiktok", "scroll up tiktok",
        "tiktok scroll up",
    ]):
        tiktok_scroll_up()
        return True

    # Voice once
    if matches_any(low, [
        "voice command", "voice recognize", "recognize voice",
        "listen to me",
    ]):
        threading.Thread(
            target=voice_command_once,
            daemon=True
        ).start()

        return True

    # Voice quiet / mute command: silence the assistant immediately.
    if matches_any(low, [
        "shut up", "be quiet", "quiet", "stop speaking", "mute voice",
        "mute assistant", "silence", "keep quiet", "be silent",
    ]):
        mute_assistant_voice()
        return True

    # Voice chat OFF (checked first so "stop voice chat" doesn't
    # accidentally match the bare "voice chat" start-trigger below)
    if matches_any(low, [
        "stop voice chat", "voice chat off", "stop listening",
    ]):
        stop_voice_chat()
        return True

    # Voice chat ON
    if matches_any(low, [
        "start voice chat", "voice chat on", "talk with me",
        "talk to me", "voice chat",
    ]):
        start_voice_chat()
        return True

    # Wikipedia search
    q = extract_after(
        text,
        [
            "search wikipedia ", "wikipedia search ",
        ]
    )

    if q:
        search_wikipedia_query(q)
        return True

    # Google search
    q = extract_after(
        text,
        [
            "search google ",
            "google search "
        ]
    )

    if q:
        search_google_query(q)
        return True

    # YouTube
    q = extract_after(
        text,
        [
            "search youtube for ",
            "play youtube ",
            "play on youtube ",
            "youtube play ",
            "youtube ",
        ]
    )

    if not q and yt_context.get("mode") in {"browsing", "search", "playing"}:
        q = extract_after(text, ["search for ", "find ", "look up "])

    if q:
        play_youtube(q)
        return True

    if matches_any(low, [
        "open youtube", "launch youtube", "go to youtube", "start youtube",
        "youtube"
    ]):
        youtube_open()
        return True

    # TikTok search
    q = extract_after(
        text,
        [
            "search tiktok ",
            "tiktok search "
        ]
    )

    if q:
        open_tiktok_search(q)
        return True

    if matches_any(low, [
        "login to tiktok", "log in to tiktok", "sign in to tiktok",
        "open tiktok login"
    ]):
        login_tiktok()
        return True

    if matches_any(low, [
        "open tiktok", "tiktok"
    ]):
        open_tiktok()
        return True

    # WhatsApp
    if matches_any(low, [
        "open whatsapp", "whatsapp"
    ]):
        safe_open(
            "https://web.whatsapp.com/"
        )

        log_message(
            "REXA",
            "Opened WhatsApp Web."
        )

        return True

    wa = extract_after(
        text,
        [
            "whatsapp message ",
            "send a whatsapp message to ",
            "reply to ",
        ]
    )

    if wa:
        if "|" in wa:
            number, message = wa.split(
                "|",
                1
            )

            whatsapp_reply_or_send(
                number.strip(),
                message.strip()
            )

        elif " saying " in wa:
            number, message = wa.split(" saying ", 1)
            whatsapp_reply_or_send(
                number.strip(" '\""),
                message.strip(" '\"")
            )

        elif ":" in wa:
            number, message = wa.split(":", 1)
            whatsapp_reply_or_send(
                number.strip(" '\""),
                message.strip(" '\"")
            )

        else:
            log_message(
                "REXA",
                "Format:\n"
                "whatsapp message "
                "8801XXXXXXXXX | your message"
            )

        return True

    # Messaging/calling things REXA genuinely cannot do
    if matches_any(low, [
        "call ", "on speakerphone", "speakerphone"
    ]) and "whatsapp" in low or "speakerphone" in low:
        cannot_do("making a WhatsApp/phone call")
        return True

    if matches_any(low, [
        "read my last text", "read my text message", "last text message"
    ]):
        cannot_do("reading SMS messages")
        return True

    tk_msg = extract_after(text, [
        "open tiktok and message ", "message on tiktok ",
    ])
    if tk_msg:
        tiktok_message_person(tk_msg)
        return True

    ig_find = extract_after(text, ["find ", ])
    if "profile on tiktok" in low and ig_find:
        person = ig_find.replace("'s profile on tiktok", "").replace(
            "profile on tiktok", ""
        ).strip()
        open_tiktok_search(person)
        return True

    if matches_any(low, ["open instagram and show my notifications"]):
        open_instagram_notifications()
        return True

    if matches_any(low, ["post a story on instagram"]):
        cannot_do("posting an Instagram story")
        return True

    if matches_any(low, ["open instagram"]):
        open_instagram()
        return True

    # System & hardware
    if matches_any(low, [
        "turn on wifi", "turn on wi-fi"
    ]):
        open_wifi_settings()
        return True

    if matches_any(low, [
        "turn off bluetooth", "turn on bluetooth", "bluetooth"
    ]):
        open_bluetooth_settings()
        return True

    if matches_any(low, [
        "empty the recycle bin", "empty recycle bin"
    ]):
        empty_recycle_bin()
        return True

    # ---------- NEW: 18 EXTRA WINDOWS / SYSTEM COMMANDS ----------

    if matches_any(low, ["open control panel"]):
        open_control_panel()
        return True

    if matches_any(low, ["open sound settings"]):
        open_sound_settings()
        return True

    if matches_any(low, ["open display settings"]):
        open_display_settings()
        return True

    if matches_any(low, ["open windows update"]):
        open_windows_update()
        return True

    if matches_any(low, ["open recycle bin"]):
        open_recycle_bin_folder()
        return True

    if matches_any(low, ["open desktop folder"]):
        open_desktop_folder()
        return True

    if matches_any(low, ["open startup folder"]):
        open_startup_folder()
        return True

    if matches_any(low, ["open temp folder"]):
        open_temp_folder()
        return True

    if matches_any(low, ["restart explorer"]):
        restart_explorer()
        return True

    if matches_any(low, ["clear clipboard"]):
        clear_clipboard()
        return True

    if matches_any(low, ["copy time to clipboard"]):
        copy_time_to_clipboard()
        return True

    if matches_any(low, ["copy date to clipboard"]):
        copy_date_to_clipboard()
        return True

    if matches_any(low, ["open downloads folder"]):
        open_downloads_folder()
        return True

    if matches_any(low, ["open documents folder"]):
        open_documents_folder()
        return True

    if matches_any(low, ["open appdata folder"]):
        open_appdata_folder()
        return True

    if matches_any(low, ["open bluetooth settings"]):
        open_bluetooth_settings()
        return True

    if matches_any(low, ["open wifi settings", "open wi-fi settings"]):
        open_wifi_settings()
        return True

    if matches_any(low, ["open windows defender", "open windows security"]):
        open_windows_defender()
        return True

    b = extract_after(text, ["increase screen brightness to ", "brightness "])
    if b or "maximum" in low and "brightness" in low:
        if "maximum" in low:
            set_brightness(100)
        else:
            digits = "".join(ch for ch in b if ch.isdigit())
            if digits:
                set_brightness(digits)
        return True

    if matches_any(low, ["set an alarm", "set a timer"]):
        open_alarm_clock()
        return True

    if matches_any(low, ["what is the weather", "weather today"]):
        ask_weather()
        return True

    sp = extract_after(text, ["play ", ])
    if "on spotify" in low and sp:
        spotify_search(sp.replace("on spotify", "").strip())
        return True

    # Simple commands (substring-based, so extra words are fine)
    simple_commands = [
        (["notepad"], open_notepad),
        (["calculator"], open_calculator),
        (["open paint", "paint"], open_paint),
        (["open camera", "camera"], open_camera),
        (["open cmd", "command prompt"], open_cmd),
        (["cmd"], open_cmd),
        (["powershell"], open_powershell),
        (["settings"], open_settings),
        (["task manager", "taskmanager"], open_task_manager),
        (["downloads"], open_downloads),
        (["documents"], open_documents),
        (["my pc", "file explorer"], open_pc),
        (["open google search", "open google"], lambda: safe_open("https://www.google.com/")),
        (["network settings"], open_network_settings),
        (["personalization"], open_personalization),
        (["screenshot", "take a screenshot"], take_screenshot),
        (["open chrome"], open_chrome),
        (["open edge"], open_edge),
        (["open spotify"], open_spotify),
        (["close window", "close this window"], close_active_window),
        (["minimize all", "show desktop"], minimize_all_windows),
        (["switch window", "alt tab"], switch_window),
        (["volume up", "increase volume"], volume_up),
        (["volume down", "decrease volume"], volume_down),
        (["mute volume", "mute sound"], volume_mute),
        (["notepad", "নোটপ্যড", "নোটপ্যড খোলো"], open_notepad),
        (["calculator", "ক্যালকুলেটর", "ক্যালকুলেটর খোলো"], open_calculator),
        (["volume up", "ভলিউম বাড়াও", "সাউন্ড বাড়াও"], volume_up),
                # ---------- MORE SIMPLE COMMANDS ----------
        (["open spotify"], open_spotify),
        (["open chrome"], open_chrome),
        (["open edge"], open_edge),

        (["open downloads"], open_downloads),
        (["open documents"], open_documents),
    
        (["open desktop"], open_desktop),

        (["screenshot", "take screenshot"], take_screenshot),

        (["minimize all", "show desktop"], minimize_all_windows),
        (["close window", "close this window"], close_active_window),

        (["switch window", "alt tab"], switch_window),

        (["volume up", "increase volume", "volume max"], volume_up),
        (["volume down", "decrease volume", "volume কমাও"], volume_down),
        (["mute volume", "mute sound"], volume_mute),

        (["lock pc", "lock computer"], lock_pc),

        (["open task manager", "task manager"], open_task_manager),
        (["open settings", "windows settings"], open_settings),

        (["open command prompt", "open cmd"], open_cmd),
        (["open powershell", "powershell"], open_powershell),

        (["open calculator", "calculator"], open_calculator),
        (["open notepad", "notepad"], open_notepad),

        (["open google", "google"], lambda: safe_open("https://www.google.com/")),
        (["open youtube", "youtube"], lambda: safe_open("https://www.youtube.com/")),

        (["open gmail", "gmail"], lambda: safe_open("https://mail.google.com/")),
        (["open chatgpt", "chatgpt"], lambda: safe_open("https://chatgpt.com/")),

        (["open facebook", "facebook"], lambda: safe_open("https://www.facebook.com/")),
        (["open instagram", "instagram"], lambda: safe_open("https://www.instagram.com/")),

        (["refresh page", "refresh"], lambda: pyautogui.press("f5")),

        (["next tab"], lambda: pyautogui.hotkey("ctrl", "tab")),
        (["previous tab"], lambda: pyautogui.hotkey("ctrl", "shift", "tab")),
        (["new tab"], lambda: pyautogui.hotkey("ctrl", "t")),
        (["close tab"], lambda: pyautogui.hotkey("ctrl", "w")),

        (["copy"], lambda: pyautogui.hotkey("ctrl", "c")),
        (["paste"], lambda: pyautogui.hotkey("ctrl", "v")),
        (["select all"], lambda: pyautogui.hotkey("ctrl", "a")),

        (["play pause", "pause play"], lambda: pyautogui.press("space")),
        (["next video", "next"], lambda: pyautogui.press("n")),
        (["previous video", "previous"], lambda: pyautogui.hotkey("shift", "p")),
    ]

    for phrases, action in simple_commands:
        if matches_any(low, phrases):
            action()
            return True

    if low == "google":
        safe_open("https://www.google.com/")
        return True

    # System info
    if matches_any(low, [
        "system info", "system information", "system status",
        "check system status"
    ]):
        system_info()
        return True

    # Network info
    if matches_any(low, [
        "network info", "network information"
    ]):
        network_info()
        return True

    # IP
    if matches_any(low, [
        "my ip", "ip address"
    ]):
        open_ip_search()
        return True

    # Lock
    if matches_any(low, [
        "lock pc", "lock computer"
    ]):
        lock_pc()
        return True

    # Restart
    if matches_any(low, [
        "restart pc", "restart computer"
    ]):
        restart_pc()
        return True

    # Shutdown with a delay, e.g. "shut down in 50 or 60 minutes".
    if (
        ("shut down" in low or "shutdown" in low or "turn off" in low)
        and re.search(r"\b(?:minutes?|mins?|hours?|hrs?)\b", low)
    ):
        delay = parse_shutdown_delay(low)
        if delay is None:
            log_message("REXA", "Please specify the shutdown delay in minutes or hours.")
            return True
        delay_seconds, delay_label = delay
        shutdown_pc(delay_seconds=delay_seconds, delay_label=delay_label)
        return True

    # Shutdown
    if matches_any(low, [
        "shutdown pc", "shutdown computer", "shut down the computer","shut down pc"
    ]):
        shutdown_pc()
        return True
    # Simple shutdown command
    if matches_any(low, [
        "shut down",
        "shutdown",
        "turn off pc",
        "turn off computer"
    ]):
        shutdown_pc()
        return True
    # Cancel shutdown
    if matches_any(low, [
        "cancel shutdown", "abort shutdown"
    ]):
        cancel_shutdown()
        return True
      
    # ---------- Advanced browser / media ----------

    yq = extract_after(text, ["open youtube and play "])
    if yq:
        open_youtube_and_play(yq)
        return True

    if matches_any(low, [
        "lo-fi study beats", "lofi study beats", "play some lofi",
        "play lofi", "lofi music"
    ]):
        open_youtube_and_play("lofi study beats")
        return True

    if matches_any(low, ["set playback speed to 1.5x", "playback speed 1.5"]):
        youtube_set_speed_1_5x()
        return True

    if matches_any(low, ["increase playback speed", "speed up video"]):
        youtube_speed_up()
        return True

    if matches_any(low, ["decrease playback speed", "slow down video"]):
        youtube_speed_down()
        return True

    if matches_any(low, [
        "turn on subtitles", "turn off subtitles", "subtitles"
    ]):
        youtube_toggle_subtitles()
        return True

    if matches_any(low, ["close the current browser tab", "close current tab"]):
        browser_close_tab()
        return True

    if matches_any(low, ["reopen the last closed tab", "reopen last tab"]):
        browser_reopen_tab()
        return True

    if matches_any(low, ["open a new incognito window", "incognito"]):
        browser_incognito()
        return True

    if matches_any(low, ["bookmark this page", "bookmark page"]):
        browser_bookmark_page()
        return True

    if matches_any(low, ["scroll down half a page", "scroll half page"]):
        browser_scroll_half_page()
        return True

    if matches_any(low, ["refresh the web page", "refresh page", "reload page"]):
        browser_refresh()
        return True

    if matches_any(low, ["switch to the previous tab", "previous tab"]):
        browser_previous_tab()
        return True

    # ---------- Messaging / calls / socials (honest scope) ----------

    msg = extract_after(text, ["open messenger and text "])
    if msg:
        open_messenger()
        cannot_do("sending a text directly to someone on Messenger")
        return True

    if matches_any(low, [
        "voice call", "record a", "voice message", "decline the incoming call",
        "clear my recent call history", "disconnect my bluetooth headset"
    ]):
        if "whatsapp" in low or "voice call" in low:
            cannot_do("making a WhatsApp voice call")
        elif "voice message" in low or "record a" in low:
            cannot_do("recording and sending a voice message")
        elif "decline" in low:
            cannot_do("declining an incoming call")
        elif "call history" in low:
            cannot_do("viewing/clearing call history (that's phone data, not accessible from a PC)")
        elif "bluetooth headset" in low:
            open_bluetooth_settings()
        return True

    if matches_any(low, ["read out my unread notifications", "unread notifications"]):
        open_notification_center()
        return True

    tg = extract_after(text, ["open tiktok and search for "])
    if tg:
        open_tiktok_search(tg)
        return True

    share = extract_after(text, ["share this video link with "])
    if share and " on whatsapp" in low:
        name = share.split(" on whatsapp")[0].strip()
        log_message(
            "REXA",
            f"Want me to open a WhatsApp draft to share the video link with "
            f"'{name}'? Type 'whatsapp message <number>|<link>'."
        )
        return True

    if matches_any(low, ["block notifications from social media for 1 hour", "do not disturb"]):
        open_focus_assist()
        return True

    if matches_any(low, ["open facebook and check my feed", "open facebook"]):
        state["active_social_inbox"] = "facebook"
        open_facebook_feed()
        return True

    # ---------- System / volume / power (advanced) ----------

    if matches_any(low, ["restart my computer right now", "restart now"]):
        subprocess.Popen(["shutdown", "/r", "/t", "0"])
        log_message("REXA", "The PC is restarting now.")
        return True

    if matches_any(low, ["put the pc to sleep", "sleep mode"]):
        sleep_pc()
        return True

    if matches_any(low, ["night light"]):
        open_night_light()
        return True

    if matches_any(low, ["mute all app audio except calls"]):
        log_message(
            "REXA",
            "Muting individual apps needs the Windows Volume Mixer "
            "(Settings > System > Sound > Volume mixer) — REXA can't do "
            "that reliably by itself."
        )
        return True

    if matches_any(low, ["turn off wifi and switch to ethernet", "switch to ethernet"]):
        open_network_settings()
        return True

    if matches_any(low, ["enable do not disturb"]):
        open_focus_assist()
        return True

    if matches_any(low, ["check system battery", "battery percentage"]):
        check_battery_percent()
        return True

    if matches_any(low, ["close all background applications", "close background apps"]):
        log_message(
            "REXA",
            "Closing all background apps by itself is risky (it could "
            "close important system processes) — so I'm opening Task "
            "Manager, choose and End Task yourself from there."
        )
        open_task_manager()
        return True

    if matches_any(low, ["eject the external usb", "eject usb", "safely remove"]):
        try:
            os.startfile("::{20D04FE0-3AEA-1069-A2D8-08002B30309D}")
        except Exception:
            pass
        log_message(
            "REXA",
            "Opened This PC — Windows doesn't let a specific drive be "
            "safely ejected without a file/PID reference, so right-click "
            "the drive and choose 'Eject'."
        )
        return True

    # ---------- File management ----------

    fq = extract_after(text, ["create a new folder on desktop named "])
    if fq:
        create_desktop_folder(fq)
        return True

    if matches_any(low, ["move the last downloaded file to documents"]):
        move_last_download_to_documents()
        return True

    if matches_any(low, [
        "copy the selected file", "copy selected file", "copy this file",
        "make a copy of this file", "make copy file", "duplicate this file",
        "duplicate the selected file"
    ]):
        ask_copy_file()
        return True

    if matches_any(low, ["delete selected file permanently", "delete selected file"]):
        cannot_do(
            "deleting a specific file safely, since REXA can't know which "
            "file is 'selected' in Explorer"
        )
        return True

    sq = extract_after(text, ["search my pc for "])
    if sq:
        search_pc_for_file(sq)
        return True

    if matches_any(low, ["open my screenshot folder", "screenshot folder"]):
        open_screenshots_folder()
        return True

    if matches_any(low, ["rename the selected file", "rename selected file"]):
        cannot_do("renaming a file, since REXA can't know which file is 'selected'")
        return True

    if matches_any(low, ["compress this folder into a zip"]):
        ask_compress_folder()
        return True

    memo = extract_after(text, ["open notepad and type "])
    if memo:
        notepad_type_memo(memo)
        return True

    if matches_any(low, ["clear temporary system cache", "clear temp files"]):
        clear_temp_files()
        return True

    # ---------- Productivity / timers / tools ----------

    if matches_any(low, ["start a 25-minute pomodoro", "pomodoro"]):
        start_pomodoro(25)
        return True

    calc = extract_after(text, ["open calculator and compute "])
    if calc:
        open_calculator()
        calculator_compute(calc)
        return True

    task = extract_after(text, ["add "])
    if task and "to my task list" in low:
        task_clean = task.split("to my task list")[0].strip(" '\"")
        add_task(task_clean)
        return True

    if matches_any(low, ["show my task list", "my tasks"]):
        show_tasks()
        return True

    cal = extract_after(text, ["open google calendar and create an event for "])
    if cal:
        open_google_calendar_new_event("New Event", cal)
        return True

    if matches_any(low, ["show my daily schedule", "daily schedule", "today's schedule"]):
        open_google_calendar()
        return True

    dic = extract_after(text, ["dictate text: ", "dictate text "])
    if dic:
        dictate_type_text(dic.strip(" '\""))
        return True

    if matches_any(low, ["read the text on my screen out loud", "read screen"]):
        read_clipboard_aloud()
        return True

    if matches_any(low, ["convert ", "us dollars to"]) and "convert" in low:
        convert_currency_query(text)
        return True

    if matches_any(low, ["open my email inbox and compose", "compose a new message"]):
        open_gmail_compose()
        return True

    if matches_any(low, ["open my email inbox", "email inbox"]):
        open_gmail_inbox()
        return True

    # ---------- Quick info / smart actions ----------

    if matches_any(low, ["high-resolution screenshot of the selected window", "screenshot of the selected window"]):
        screenshot_active_window()
        return True

    if matches_any(low, ["start recording my screen", "start screen recording"]):
        toggle_screen_recording()
        return True

    if matches_any(low, ["stop screen recording", "stop recording"]):
        toggle_screen_recording()
        return True

    if matches_any(low, ["open camera app and snap a photo", "snap a photo"]):
        snap_camera_photo()
        return True

    if matches_any(low, ["translate the selected sentence to bengali", "translate selected"]):
        translate_clipboard_to_bengali()
        return True

    if matches_any(low, ["turn on dark mode for all system apps", "dark mode"]):
        set_dark_mode(dark=True)
        return True

    if matches_any(low, ["check remaining storage space on drive c", "storage on drive c", "drive c space"]):
        check_drive_space("C:\\")
        return True

    if matches_any(low, ["open device manager"]):
        open_device_manager()
        return True

    return False


def execute_command(text):
    global last_activity_at
    text = text.strip()

    if not text:
        return

    log_message("YOU", text)

    state["last_command"] = text
    last_activity_at = time.monotonic()

    try:
        handled = handle_special_command(text)
        if not handled:
            run_ai(text)
        else:
            play_sfx("done")
    except Exception as exc:
        log_message("REXA", f"Command execution error: {exc}")
        try:
            set_mode("ERROR")
            speak("I hit an error while processing that command. Please try again.")
            root.after(1500, lambda: set_mode("SYSTEM READY"))
        except Exception:
            pass

# ============================================================
# INPUT BOX
# ============================================================

def remove_placeholder(event=None):
    global placeholder_active

    if placeholder_active:
        input_var.set("")
        entry.config(fg=TEXT)
        placeholder_active = False


def add_placeholder(event=None):
    global placeholder_active

    if not entry.get():
        input_var.set(PLACEHOLDER)
        entry.config(fg=MUTED)
        placeholder_active = True


def send_from_box(event=None):
    global placeholder_active

    text = entry.get().strip()

    if not text or placeholder_active:
        return "break"

    input_var.set("")
    placeholder_active = False
    entry.config(fg=TEXT)

    execute_command(text)

    return "break"


def focus_command_box(event=None):
    entry.focus_set()
    entry.icursor("end")
    return "break"


def clear_chat_shortcut(event=None):
    clear_chat()
    return "break"


def bind_keyboard_shortcuts():
    """Register keyboard controls for the main JARVIS window."""
    root.bind("<Control-Return>", send_from_box)
    root.bind("<Control-l>", focus_command_box)
    root.bind("<F1>", lambda event: (show_help(), "break")[1])
    root.bind("<F2>", lambda event: (voice_command_once(), "break")[1])
    root.bind("<F3>", lambda event: (start_voice_chat(), "break")[1])
    root.bind("<F4>", clear_chat_shortcut)


def mute_assistant_voice():
    """Silence future voice output immediately while keeping the system listening."""
    state["voice"] = False
    voice_var.set("VOICE      OFF")
    stop_speaking()
    log_message(
        "REXA",
        "[WARNING] Voice muted. I will stay quiet until you say 'voice on' or 'start voice chat'."
    )


def toggle_voice():
    state["voice"] = not state["voice"]

    if state["voice"]:
        voice_var.set("VOICE      ON")
        log_message(
            "REXA",
            "Voice turned ON. \U0001F50A"
        )
        speak("Voice on.")

    else:
        voice_var.set("VOICE      OFF")
        log_message(
            "REXA",
            "Voice turned OFF."
        )


# ============================================================
# UI BUILDERS
# ============================================================

def create_panel(parent):
    outer = tk.Frame(
        parent,
        bg=CYAN
    )

    inner = tk.Frame(
        outer,
        bg=PANEL
    )

    inner.pack(
        fill="both",
        expand=True,
        padx=1,
        pady=1
    )

    return outer, inner


def make_button(parent, text, command):
    def clicked():
        play_sfx("click")
        command()

    button = tk.Button(
        parent,
        text=text,
        command=clicked,
        bg=PANEL,
        fg=TEXT,
        activebackground=CYAN2,
        activeforeground="white",
        relief="flat",
        bd=0,
        highlightthickness=1,
        highlightbackground="#102f38",
        font=("Consolas", 8, "bold"),
        cursor="hand2",
        padx=14,
        pady=8
    )
    button.bind("<Enter>", lambda event: (button.configure(fg=CYAN), button.configure(highlightbackground=CYAN), button.configure(highlightthickness=2)))
    button.bind("<Leave>", lambda event: (button.configure(fg=TEXT), button.configure(highlightbackground="#102f38"), button.configure(highlightthickness=1)))
    return button


# ============================================================
# HEADER
# ============================================================

header = tk.Frame(
    root,
    bg=BG
)

header.grid(
    row=0,
    column=0,
    sticky="ew",
    padx=32,
    pady=(14, 0)
)

header.grid_columnconfigure(
    1,
    weight=1
)

logo_area = tk.Frame(
    header,
    bg=BG
)

logo_area.grid(
    row=0,
    column=0,
    sticky="w"
)

tk.Label(
    logo_area,
    text="JARVIS AI",
    fg=CYAN,
    bg=BG,
    font=("Consolas", 24, "bold")
).pack(anchor="w")

tk.Label(
    logo_area,
    text="// COMMAND CENTER  \u2022  GEMINI AI",
    fg=MUTED,
    bg=BG,
    font=("Consolas", 8, "bold")
).pack(anchor="w")


capsule = tk.Frame(
    header,
    bg=PANEL2,
    highlightbackground=CYAN2,
    highlightthickness=1,
    width=170,
    height=42
)

capsule.grid(
    row=0,
    column=1
)

capsule.grid_propagate(False)

tk.Label(
    capsule,
    textvariable=status_indicator_var,
    fg=CYAN,
    bg=PANEL2,
    font=("Consolas", 8, "bold"),
    anchor="center"
).pack(expand=True)


clock_area = tk.Frame(
    header,
    bg=BG
)

clock_area.grid(
    row=0,
    column=2,
    sticky="e"
)

tk.Label(
    clock_area,
    textvariable=time_var,
    fg=CYAN,
    bg=BG,
    font=("Consolas", 22, "bold")
).pack(anchor="e")

tk.Label(
    clock_area,
    textvariable=date_var,
    fg=MUTED,
    bg=BG,
    font=("Consolas", 9)
).pack(anchor="e")


status_line = tk.Frame(
    root,
    bg=CYAN,
    height=3
)
status_line.grid(
    row=0,
    column=0,
    sticky="sew",
    padx=32,
    pady=(108, 0)
)


# ============================================================
# NAVIGATION
# ============================================================

nav = tk.Frame(
    root,
    bg=BG
)

nav.grid(
    row=1,
    column=0,
    sticky="ew",
    padx=32,
    pady=(12, 8)
)

nav_buttons = [
    ("MY PC", open_pc),
    (
        "WEB",
        lambda: safe_open(
            "https://www.google.com/"
        )
    ),
    ("TOOLS", open_notepad),
    ("TASK MANAGER", open_task_manager),
    ("CONTROL", open_settings),
    ("NETWORK", open_network_settings),
    ("SCREENSHOT", take_screenshot),
]

for i, (label, command) in enumerate(
    nav_buttons
):
    nav.columnconfigure(
        i,
        weight=1
    )

    make_button(
        nav,
        label,
        command
    ).grid(
        row=0,
        column=i,
        sticky="ew",
        padx=3
    )


# ============================================================
# MAIN
# ============================================================

main = tk.Frame(
    root,
    bg=BG
)

main.grid(
    row=2,
    column=0,
    sticky="nsew",
    padx=32,
    pady=4
)

main.grid_columnconfigure(
    0,
    minsize=285,
    weight=0
)

main.grid_columnconfigure(
    1,
    weight=1
)

main.grid_columnconfigure(
    2,
    minsize=280,
    weight=0
)

main.grid_rowconfigure(
    0,
    weight=1
)


# ============================================================
# LEFT TOOL PANEL
# ============================================================

left_outer = tk.Frame(
    main,
    bg=BG
)

left_outer.grid(
    row=0,
    column=0,
    sticky="nsw",
    padx=(0, 16)
)

tk.Label(
    left_outer,
    text="SYSTEM TOOLS",
    fg=CYAN,
    bg=BG,
    font=("Consolas", 9, "bold")
).pack(
    anchor="w",
    pady=(0, 8)
)

tool_filter_var = tk.StringVar()

tool_search_frame = tk.Frame(
    left_outer,
    bg=PANEL,
    highlightthickness=1,
    highlightbackground=GRID,
    highlightcolor=CYAN
)

tool_search_frame.pack(
    fill="x",
    pady=(0, 8)
)

tool_search_entry = tk.Entry(
    tool_search_frame,
    textvariable=tool_filter_var,
    bg=PANEL,
    fg=TEXT,
    insertbackground=CYAN,
    relief="flat",
    bd=0,
    font=("Consolas", 9)
)

tool_search_entry.insert(0, "\U0001F50E Filter tools...")
tool_search_entry.config(fg=MUTED)

tool_search_placeholder_active = True


def _tool_search_focus_in(event=None):
    global tool_search_placeholder_active
    if tool_search_placeholder_active:
        tool_search_entry.delete(0, "end")
        tool_search_entry.config(fg=TEXT)
        tool_search_placeholder_active = False


def _tool_search_focus_out(event=None):
    global tool_search_placeholder_active
    if not tool_filter_var.get().strip():
        tool_search_placeholder_active = True
        tool_search_entry.delete(0, "end")
        tool_search_entry.insert(0, "\U0001F50E Filter tools...")
        tool_search_entry.config(fg=MUTED)


tool_search_entry.bind("<FocusIn>", _tool_search_focus_in)
tool_search_entry.bind("<FocusOut>", _tool_search_focus_out)

tool_search_entry.pack(
    fill="x",
    padx=8,
    pady=6
)

tool_button_registry = []


def filter_tool_buttons(*_args):
    if tool_search_placeholder_active:
        query = ""
    else:
        query = tool_filter_var.get().strip().lower()

    for frame, label in tool_button_registry:
        frame.pack_forget()

    for frame, label in tool_button_registry:
        if query in label:
            frame.pack(fill="x", pady=3)

    try:
        left_canvas.configure(scrollregion=left_canvas.bbox("all"))
    except tk.TclError:
        pass


tool_filter_var.trace_add("write", filter_tool_buttons)

left_canvas = tk.Canvas(
    left_outer,
    bg=BG,
    highlightthickness=0,
    width=270
)

left_scroll = tk.Scrollbar(
    left_outer,
    orient="vertical",
    command=left_canvas.yview
)

left = tk.Frame(left_canvas, bg=BG)

left.bind(
    "<Configure>",
    lambda e: left_canvas.configure(
        scrollregion=left_canvas.bbox("all")
    )
)

left_canvas.create_window((0, 0), window=left, anchor="nw", width=270)
left_canvas.configure(yscrollcommand=left_scroll.set)

left_canvas.pack(side="left", fill="both", expand=True)
left_scroll.pack(side="right", fill="y")


def tool_button(text, command):
    def clicked():
        play_sfx("click")
        command()

    frame = tk.Frame(
        left,
        bg=CYAN,
        height=40
    )

    frame.pack(
        fill="x",
        pady=3
    )

    frame.pack_propagate(False)

    tk.Button(
        frame,
        text=text,
        command=clicked,
        bg=PANEL,
        fg=TEXT,
        activebackground=PANEL2,
        activeforeground=CYAN,
        relief="flat",
        bd=0,
        anchor="w",
        font=("Consolas", 8, "bold"),
        padx=16,
        cursor="hand2"
    ).pack(
        fill="both",
        expand=True,
        padx=1,
        pady=1
    )

    tool_button_registry.append((frame, text.lower()))


for label, command in [
    ("\u25A3   MY PC", open_pc),
    ("\u25B6   YOUTUBE OPEN", youtube_open),
    ("\u2715   YOUTUBE CLOSE", youtube_close),
    ("\u23EF   YOUTUBE PLAY/PAUSE", youtube_pause_play),
    ("\u21BB   YT REPLAY", youtube_replay),
    ("\u23ED   YT NEXT", youtube_next),
    ("\u23EE   YT PREVIOUS", youtube_previous),
    ("\U0001F50D  SEARCH & PLAY YOUTUBE", ask_youtube),
    ("\U0001F3A4   VOICE", voice_command_once),
    ("\u25C9   VOICE CHAT", start_voice_chat),
    ("\u25A0   STOP VOICE", stop_voice_chat),
    ("\u266A   TIKTOK", ask_tiktok),
    ("\u2193   TIKTOK NEXT", tiktok_scroll_down),
    ("\u2191   TIKTOK PREV", tiktok_scroll_up),
    ("\u25CF   WHATSAPP", ask_whatsapp),
    ("\u25CE   GOOGLE", open_google),
    ("\U0001F310  CHROME", open_chrome),
    ("\U0001F310  EDGE", open_edge),
    ("\U0001F3B5  SPOTIFY", open_spotify),
    ("\U0001F3A7  LOFI STUDY BEATS", lambda: open_youtube_and_play("lofi study beats")),
    ("\u2193   DOWNLOADS", open_downloads),
    ("\u25A4   DOCUMENTS", open_documents),
    ("\u29C9   COPY FILE", ask_copy_file),
    ("\u25A4   NOTEPAD", open_notepad),
    ("\u25A0   CALCULATOR", open_calculator),
    ("\U0001F3A8  PAINT", open_paint),
    ("\U0001F4F7  CAMERA", open_camera),
    ("\u2699   SETTINGS", open_settings),
    (">_  CMD", open_cmd),
    ("PS  POWERSHELL", open_powershell),
    ("\u25A3   TASK MANAGER", open_task_manager),
    ("\u25A3   SCREENSHOT", take_screenshot),
    ("\U0001F50A  VOLUME UP", volume_up),
    ("\U0001F509  VOLUME DOWN", volume_down),
    ("\U0001F507  MUTE", volume_mute),
    ("\u25C9   NETWORK INFO", network_info),
    ("\u23F0  SET REMINDER", lambda: (lambda t: set_reminder(t) if t else None)(simpledialog.askstring("Reminder", "Remind me to:"))),
    ("\U0001F4CB  SHOW REMINDERS", show_reminders),
    ("\U0001F4DD  ADD NOTE", lambda: (lambda t: add_note(t) if t else None)(simpledialog.askstring("Note", "Note text:"))),
    ("\U0001F4D2  SHOW NOTES", show_notes),
    ("\U0001F3B2  ROLL DICE", roll_dice),
    ("\U0001FA99  FLIP COIN", flip_coin),
    ("\U0001F602  TELL A JOKE", tell_joke),
    ("\U0001F4D6  DEFINE WORD", lambda: (lambda t: define_word(t) if t else None)(simpledialog.askstring("Define", "Word to define:"))),
    ("\U0001F4B1  CURRENCY CONVERT", lambda: (lambda t: convert_currency_dedicated(t or ""))(simpledialog.askstring("Currency", "Convert what?"))),
    ("\U0001F4C8  STOCK PRICE", lambda: (lambda t: check_stock_price(t) if t else None)(simpledialog.askstring("Stock", "Symbol:"))),
    ("\u20BF   CRYPTO PRICE", lambda: (lambda t: check_crypto_price(t) if t else None)(simpledialog.askstring("Crypto", "Coin:"))),
    ("\U0001F5FA  MAPS", open_maps),
    ("\U0001F9ED  DIRECTIONS", lambda: (lambda t: get_directions(t) if t else None)(simpledialog.askstring("Directions", "Destination:"))),
    ("\u2728  QUOTE OF THE DAY", quote_of_the_day),
    ("\U0001F6D2  AMAZON SEARCH", lambda: (lambda t: search_amazon(t) if t else None)(simpledialog.askstring("Amazon", "Search for:"))),
    ("\U0001F419  GITHUB", open_github),
    ("#\uFE0F\u20E3  SLACK", open_slack),
    ("\U0001F465  TEAMS", open_teams),
    ("\u23F2   COUNTDOWN TIMER", lambda: start_countdown_timer(5)),
]:
    tool_button(
        label,
        command
    )


# ============================================================
# CENTER CHAT
# ============================================================

center = tk.Frame(
    main,
    bg=BG
)

center.grid(
    row=0,
    column=1,
    sticky="nsew"
)

center.grid_rowconfigure(
    2,
    weight=1
)

center.grid_columnconfigure(
    0,
    weight=1
)

tk.Label(
    center,
    textvariable=mode_var,
    fg=MUTED,
    bg=BG,
    font=("Consolas", 8, "bold")
).grid(
    row=0,
    column=0,
    sticky="ew",
    pady=(0, 5)
)


# Radar
radar_outer, radar_panel = create_panel(center)

radar_outer.grid(
    row=1,
    column=0,
    sticky="ew"
)

radar = tk.Canvas(
    radar_panel,
    bg=PANEL,
    highlightthickness=0,
    height=430,
    bd=0
)

radar.pack(
    fill="both",
    expand=True,
    padx=2,
    pady=2
)

try:
    radar.bind("<Configure>", lambda event: draw_radar())
except Exception:
    pass


# Chat
chat_outer, chat_panel = create_panel(center)

chat_outer.grid(
    row=2,
    column=0,
    sticky="nsew",
    pady=(8, 0)
)

chat_panel.grid_columnconfigure(
    0,
    weight=1
)

chat_panel.grid_rowconfigure(
    0,
    weight=1
)

chat_text = tk.Text(
    chat_panel,
    bg=PANEL,
    fg=TEXT,
    insertbackground=CYAN,
    selectbackground=CYAN2,
    selectforeground="white",
    relief="flat",
    bd=0,
    wrap="word",
    undo=False,
    font=("Consolas", 10),
    padx=14,
    pady=12,
    spacing1=2,
    spacing3=5
)

chat_text.grid(
    row=0,
    column=0,
    sticky="nsew"
)

scroll = tk.Scrollbar(
    chat_panel,
    command=chat_text.yview,
    bg=PANEL2,
    troughcolor=PANEL,
    activebackground=CYAN2
)

scroll.grid(
    row=0,
    column=1,
    sticky="ns"
)

chat_text.configure(
    yscrollcommand=scroll.set,
    state="disabled"
)

chat_text.tag_configure(
    "rexa",
    foreground=CYAN,
    font=("Consolas", 10, "bold")
)

chat_text.tag_configure(
    "you",
    foreground=GREEN,
    font=("Consolas", 10, "bold")
)

chat_text.tag_configure(
    "body",
    foreground=TEXT,
    background=PANEL2,
    font=("Consolas", 10),
    lmargin1=10,
    lmargin2=10,
    rmargin=10,
    spacing1=3,
    spacing3=8
)


# ============================================================
# RIGHT INFO PANEL
# ============================================================

right = tk.Frame(
    main,
    bg=BG
)

right.grid(
    row=0,
    column=2,
    sticky="nse",
    padx=(16, 0)
)


def info_panel(title):
    outer = tk.Frame(
        right,
        bg=CYAN
    )

    outer.pack(
        fill="x",
        pady=(0, 12)
    )

    inner = tk.Frame(
        outer,
        bg=PANEL
    )

    inner.pack(
        fill="both",
        expand=True,
        padx=1,
        pady=1
    )

    tk.Label(
        inner,
        text=title,
        fg=CYAN,
        bg=PANEL,
        font=("Consolas", 9, "bold")
    ).pack(
        anchor="w",
        padx=12,
        pady=9
    )

    return inner


monitor = info_panel(
    "SYSTEM MONITOR"
)

for var in (
    cpu_var,
    ram_var,
    disk_var,
    battery_var,
    network_var,
    voice_var,
    status_var,
    msg_var
):
    tk.Label(
        monitor,
        textvariable=var,
        fg=TEXT,
        bg=PANEL,
        anchor="w",
        font=("Consolas", 8)
    ).pack(
        fill="x",
        padx=14,
        pady=4
    )


quick = info_panel(
    "REXA QUICK INFO"
)

for item in [
    "\u2022 Gemini AI brain",
    "\u2022 Replies in English",
    "\u2022 Deep English male voice",
    "\u2022 YouTube open/close/play/pause",
    "\u2022 YouTube replay/next/prev/seek",
    "\u2022 TikTok search + scroll",
    "\u2022 Voice recognition + voice chat",
    "\u2022 WhatsApp preparation",
    "\u2022 Google + Wikipedia search",
    "\u2022 Chrome / Edge / Spotify",
    "\u2022 Screenshot",
    "\u2022 System information",
    "\u2022 Network information",
    "\u2022 Calculator / Notepad / Paint",
    "\u2022 PowerShell / CMD",
    "\u2022 Volume up/down/mute",
    "\u2022 Windows controls",
    "\u2022 Live system monitor",
    "\u2022 Reminders & notes",
    "\u2022 Dice, coin, jokes, quotes",
    "\u2022 Stocks, crypto, currency",
    "\u2022 Maps, directions, timers",
]:
    tk.Label(
        quick,
        text=item,
        fg=TEXT,
        bg=PANEL,
        anchor="w",
        font=("Consolas", 8)
    ).pack(
        fill="x",
        padx=14,
        pady=2
    )
# ============================================================
# BOTTOM BAR
# ============================================================

command_area = tk.Frame(
    root,
    bg=BG,
    height=58
)

command_area.grid(
    row=4,
    column=0,
    sticky="ew",
    padx=32,
    pady=(8, 4)
)

command_area.grid_propagate(False)
command_area.grid_columnconfigure(0, weight=1)

input_border = tk.Frame(
    command_area,
    bg=CYAN
)

input_border.grid(
    row=0,
    column=0,
    sticky="nsew",
    padx=(0, 8)
)

input_inner = tk.Frame(
    input_border,
    bg=PANEL
)

input_inner.pack(
    fill="both",
    expand=True,
    padx=1,
    pady=1
)

entry = tk.Entry(
    input_inner,
    textvariable=input_var,
    bg=PANEL,
    fg=TEXT,
    insertbackground=CYAN,
    relief="flat",
    bd=0,
    font=("Consolas", 10)
)

entry.pack(
    fill="both",
    expand=True,
    padx=15
)

entry.bind("<FocusIn>", remove_placeholder)
entry.bind("<FocusOut>", add_placeholder)
entry.bind("<Return>", send_from_box)
bind_keyboard_shortcuts()


def command_button(text, command, column):
    tk.Button(
        command_area,
        text=text,
        command=command,
        bg=PANEL,
        fg=TEXT,
        activebackground=CYAN2,
        activeforeground="white",
        relief="flat",
        bd=0,
        highlightthickness=1,
        highlightbackground="#1B95B3",
        font=("Consolas", 8, "bold"),
        width=8,
        height=2,
        cursor="hand2"
    ).grid(row=0, column=column, padx=3)


command_button("SEND", send_from_box, 1)
command_button("VOICE", voice_command_once, 2)
command_button("CHAT", start_voice_chat, 3)
command_button("CLEAR", clear_chat, 4)
command_button("HELP", show_help, 5)
command_button("বাংলা", lambda: set_language_mode("bengali"), 6)

input_var.set(PLACEHOLDER)
entry.config(fg=MUTED)
bottom = tk.Frame(
    root,
    bg=BG
)

bottom.grid(
    row=5,
    column=0,
    sticky="ew",
    padx=32,
    pady=(2, 10)
)

tk.Label(
    bottom,
    text=(
        "JARVIS AI  \u2022  GEMINI AI  \u2022  SYSTEM ONLINE  "
        "\u2022  READY FOR COMMAND"
    ),
    fg=MUTED,
    bg=BG,
    font=("Consolas", 7, "bold")
).pack(side="left")


def bottom_button(text, command):
    tk.Button(
        bottom,
        text=text,
        command=command,
        bg=PANEL,
        fg=TEXT,
        activebackground=CYAN2,
        activeforeground="white",
        relief="flat",
        bd=0,
        font=("Consolas", 8, "bold"),
        padx=14,
        pady=5,
        cursor="hand2"
    ).pack(
        side="right",
        padx=3
    )


def toggle_boss_mode():
    state["boss_mode"] = not state.get("boss_mode", False)

    if state["boss_mode"]:
        globals()["CYAN"] = "#7ef9ff"
        globals()["CYAN2"] = "#4cc9f0"
        globals()["GREEN"] = "#7cffb2"
        globals()["RED"] = "#ff5f7a"
        globals()["YELLOW"] = "#ffe66d"
        globals()["GRID"] = "#123e4f"
        globals()["BG"] = "#030811"
        globals()["PANEL"] = "#091722"
        globals()["PANEL2"] = "#0f1f2b"
        log_message("REXA", "Boss Mode enabled. Threat matrix online.")
        speak("Boss mode engaged. Command center fully active and fully operational.")
    else:
        globals()["CYAN"] = "#12b3e4"
        globals()["CYAN2"] = "#008fb3"
        globals()["GREEN"] = "#00ffb3"
        globals()["RED"] = "#ff4d6d"
        globals()["YELLOW"] = "#ffe66d"
        globals()["GRID"] = "#10343c"
        globals()["BG"] = "#05090d"
        globals()["PANEL"] = "#081116"
        globals()["PANEL2"] = "#0b151b"
        log_message("REXA", "Normal mode restored.")
        speak("Normal operations restored. All systems stable.")

    try:
        if "root" in globals() and root is not None:
            root.configure(bg=BG)
        if "status_line" in globals() and status_line is not None:
            status_line.configure(bg=CYAN)
        if "capsule" in globals() and capsule is not None:
            capsule.configure(bg=PANEL2, highlightbackground=CYAN, highlightcolor=CYAN)
    except Exception:
        pass

    animate_hud_glow()
    set_mode("SYSTEM READY")


bottom_button(
    "BOSS MODE",
    toggle_boss_mode
)

bottom_button(
    "SHUTDOWN",
    shutdown_pc
)

bottom_button(
    "RESTART",
    restart_pc
)

bottom_button(
    "CANCEL",
    cancel_shutdown
)

bottom_button(
    "LOCK",
    lock_pc
)


# ============================================================
# RADAR ANIMATION
# ============================================================

def draw_radar():
    try:
        radar.delete("all")

        w = max(radar.winfo_width(), 500)
        h = max(radar.winfo_height(), 285)
        cx = w // 2
        cy = h // 2
        phase = time.time()
        mode = str(state.get("mode", "SYSTEM READY")).upper()
        active = mode in {"LISTENING", "SPEAKING", "THINKING", "EXECUTING"}
        accent = GREEN if mode == "SPEAKING" else CYAN

        # Background grid / tactical HUD border
        radar.create_rectangle(8, 8, w - 8, h - 8, outline="#12343c", width=1)
        radar.create_line(0, cy, w, cy, fill=GRID, width=1)
        radar.create_line(cx, 0, cx, h, fill=GRID, width=1)

        # Corner brackets for more cinematic JARVIS HUD feel
        bracket_len = 26
        for bx, by, dx, dy in [
            (12, 12, 1, 1),
            (w - 12, 12, -1, 1),
            (12, h - 12, 1, -1),
            (w - 12, h - 12, -1, -1),
        ]:
            radar.create_line(bx, by, bx + bracket_len * dx, by, fill=CYAN, width=2)
            radar.create_line(bx, by, bx, by + bracket_len * dy, fill=CYAN, width=2)

        max_radius = min(w, h) * 0.43

        # Outer ring / scan rings
        for i, ring_scale in enumerate((0.22, 0.38, 0.55, 0.73, 0.9)):
            r = max_radius * ring_scale
            radar.create_oval(
                cx - r, cy - r, cx + r, cy + r,
                outline=accent if i == 0 else "#0d2933",
                width=2 if i == 0 else 1,
            )

        # Animated arc sweep
        sweep_angle = phase * 1.9
        sweep_radius = max_radius
        sx = cx + sweep_radius * math.cos(sweep_angle)
        sy = cy + sweep_radius * math.sin(sweep_angle)
        radar.create_line(cx, cy, sx, sy, fill=GREEN, width=2)

        for ring_index, ring_scale in enumerate((0.92, 0.68, 0.48)):
            ring_radius = max_radius * ring_scale
            radar.create_arc(
                cx - ring_radius, cy - ring_radius, cx + ring_radius, cy + ring_radius,
                start=-(phase * (16 + ring_index * 8)) % 360,
                extent=72 if ring_index != 1 else -105,
                style="arc",
                outline=accent,
                width=2,
            )

        # Status scan line
        scan_y = (cy - max_radius) + (math.sin(phase * 0.7) * 0.5 + 0.5) * (max_radius * 2)
        radar.create_line(cx - max_radius, scan_y, cx + max_radius, scan_y, fill=accent, width=1, dash=(5, 4))

        # Animated orbital points
        for i in range(24):
            angle = phase * 0.35 + i * math.pi / 11
            radius = max_radius * (0.28 + 0.52 * (0.5 + 0.5 * math.sin(phase * 0.8 + i)))
            x = cx + radius * math.cos(angle)
            y = cy + radius * math.sin(angle)
            radar.create_oval(x - 2, y - 2, x + 2, y + 2, fill=accent, outline="")

        # Waveform bars respond to mode activity
        bars = 34
        waveform_width = max_radius * 1.5
        bar_gap = waveform_width / bars
        for bar in range(bars):
            wave = abs(math.sin(phase * (5.2 if active else 2.4) + bar * 0.7))
            height = 4 + wave * (30 if active else 12)
            x = cx - waveform_width / 2 + bar * bar_gap
            radar.create_line(x, cy + max_radius * 0.75 - height, x, cy + max_radius * 0.75 + height, fill=accent, width=2)

        # Stronger central pulse ring
        pulse_phase = phase * (8 if active else 2.2)
        pulse = 38 + (math.sin(pulse_phase) + 1) * (18 if active else 6)
        reactor_energy = 1.0 if active else 0.55
        reactor_pulse = 42 + (math.sin(phase * (10 if active else 3)) + 1) * (18 * reactor_energy)
        reactor_color = GREEN if mode == "SPEAKING" else CYAN
        radar.create_oval(
            cx - reactor_pulse * 1.8, cy - reactor_pulse * 1.8,
            cx + reactor_pulse * 1.8, cy + reactor_pulse * 1.8,
            outline="#075164", width=1
        )
        radar.create_oval(
            cx - reactor_pulse * 1.35, cy - reactor_pulse * 1.35,
            cx + reactor_pulse * 1.35, cy + reactor_pulse * 1.35,
            outline=reactor_color, width=2
        )
        radar.create_oval(
            cx - reactor_pulse, cy - reactor_pulse,
            cx + reactor_pulse, cy + reactor_pulse,
            outline="#9ef7ff" if active else reactor_color, width=3
        )
        for spoke in range(8):
            angle = phase * 0.8 + spoke * math.pi / 4
            inner = reactor_pulse * 1.08
            outer = reactor_pulse * (1.25 if active else 1.16)
            radar.create_line(
                cx + math.cos(angle) * inner, cy + math.sin(angle) * inner,
                cx + math.cos(angle) * outer, cy + math.sin(angle) * outer,
                fill=reactor_color, width=2
            )
        radar.create_oval(cx - pulse * 1.35, cy - pulse * 1.35, cx + pulse * 1.35, cy + pulse * 1.35, outline="#0b4d5d", width=1)
        radar.create_oval(cx - pulse, cy - pulse, cx + pulse, cy + pulse, outline=accent, width=2)
        radar.create_oval(cx - 34, cy - 34, cx + 34, cy + 34, outline=accent, width=2)
        radar.create_oval(cx - 10, cy - 10, cx + 10, cy + 10, fill=GREEN if mode == "SPEAKING" else accent, outline="")

        # HUD labels
        flicker_texts = ["SCANNING...", "SYSTEM ACTIVE", "JARVIS ONLINE", "STANDBY"]
        idx = int(phase * 0.85) % len(flicker_texts)
        radar.create_text(30, 14, text=flicker_texts[idx], fill=accent, anchor="w", font=("Consolas", 7, "bold"))
        radar.create_text(30, h - 22, text=f"MSG {state['message_count']:03d}", fill=MUTED, anchor="w", font=("Consolas", 7))
        radar.create_text(w - 30, 14, text="SECURE", fill=GREEN, anchor="e", font=("Consolas", 7, "bold"))

        radar.create_text(cx, cy - 8, text="JARVIS", fill=TEXT, font=("Consolas", 16, "bold"))
        radar.create_text(cx, cy + 18, text=mode, fill=accent, font=("Consolas", 8, "bold"))

        # Rebuilding the radar canvas too frequently blocks Tk's event loop and
        # can cause dropped keystrokes while another application is active.
        root.after(80, draw_radar)

    except tk.TclError:
        pass


# ============================================================
# LIVE MONITOR
# ============================================================

def update_monitor():
    if psutil is None:
        cpu_var.set("CPU        N/A")
        ram_var.set("RAM        N/A")
        disk_var.set("DISK       N/A")
        battery_var.set("BATTERY    N/A")
    else:
        try:
            cpu_var.set(f"CPU        {psutil.cpu_percent(interval=None):>3.0f}%")
        except Exception as exc:
            cpu_var.set("CPU        ERROR")
            _monitor_notice(f"CPU monitor unavailable: {exc}")

        try:
            ram_var.set(f"RAM        {psutil.virtual_memory().percent:>3.0f}%")
        except Exception as exc:
            ram_var.set("RAM        ERROR")
            _monitor_notice(f"RAM monitor unavailable: {exc}")

        try:
            drive = os.environ.get("SystemDrive", "C:") + "\\"
            disk_var.set(f"DISK       {psutil.disk_usage(drive).percent:>3.0f}%")
        except Exception as exc:
            disk_var.set("DISK       ERROR")
            _monitor_notice(f"Disk monitor unavailable: {exc}")

        try:
            battery = psutil.sensors_battery()
            battery_var.set(f"BATTERY    {battery.percent:>3.0f}%" if battery else "BATTERY    AC POWER")
        except Exception as exc:
            battery_var.set("BATTERY    ERROR")
            _monitor_notice(f"Battery monitor unavailable: {exc}")

    state["online"] = check_network()

    network_var.set(
        "NETWORK    ONLINE"
        if state["online"]
        else
        "NETWORK    OFFLINE"
    )

    try:
        root.after(
            3000,
            update_monitor
        )
    except tk.TclError:
        pass


def _monitor_notice(message):
    """Report a monitor fault at most once per five minutes."""
    now = time.monotonic()
    previous = state.get("monitor_notice_at", 0)
    if now - previous >= 300:
        state["monitor_notice_at"] = now
        log_message("REXA", "[WARNING] " + message)


# ============================================================
# CLOCK
# ============================================================

def clock_loop():
    time_var.set(now_text())
    date_var.set(date_text())

    try:
        root.after(
            500,
            clock_loop
        )
    except tk.TclError:
        pass
# ============================================================
# STARTUP
# ============================================================
def show_boot_animation():
    import math, random

    sw = root.winfo_screenwidth()
    sh = root.winfo_screenheight()

    boot_win = tk.Toplevel(root)
    boot_win.title("")
    boot_win.geometry(f"{sw}x{sh}+0+0")
    boot_win.configure(bg="#05090d")
    boot_win.overrideredirect(True)
    boot_win.lift()
    boot_win.attributes("-topmost", True)
    boot_win.focus_force()

    cv = tk.Canvas(boot_win, width=sw, height=sh,
                   bg="#05090d", highlightthickness=0)
    cv.pack(fill="both", expand=True)

    CX, CY = sw // 2, sh // 2
    R = min(sw, sh) // 3

    # ── static grid ──────────────────────────────────────
    for x in range(0, sw, 55):
        cv.create_line(x, 0, x, sh, fill="#080f14", width=1)
    for y in range(0, sh, 55):
        cv.create_line(0, y, sw, y, fill="#080f14", width=1)

    # ── corner brackets ───────────────────────────────────
    L = 50
    for bx, by, dx, dy in [(22,22,1,1),(sw-22,22,-1,1),
                             (22,sh-22,1,-1),(sw-22,sh-22,-1,-1)]:
        cv.create_line(bx,by,bx+L*dx,by, fill="#00eaff",width=2)
        cv.create_line(bx,by,bx,by+L*dy, fill="#00eaff",width=2)

    # ── HUD labels static ─────────────────────────────────
    cv.create_text(35, 18, anchor="w",
        text="REXA AI  //  COMMAND CENTER  //  v2.6.1",
        fill="#0d3d4d", font=("Consolas", 9))
    cv.create_text(sw-35, 18, anchor="e",
        text="GEMINI AI  //  EDGE-TTS  //  PYGAME 2.6.1",
        fill="#0d3d4d", font=("Consolas", 9))
    cv.create_text(35, sh-18, anchor="w",
        text="SYSTEM BOOT SEQUENCE",
        fill="#0d3d4d", font=("Consolas", 9))
    cv.create_text(sw-35, sh-18, anchor="e",
        text="SECURE // ENCRYPTED",
        fill="#0d3d4d", font=("Consolas", 9))

    # ── clock ─────────────────────────────────────────────
    clock_id = cv.create_text(CX, 18, anchor="center",
        text="", fill="#00eaff", font=("Consolas", 10, "bold"))

    # ── radar static rings ────────────────────────────────
    ring_colors = ["#00eaff","#0e3545","#0a2535","#071a28"]
    ring_widths  = [1.5, 1, 0.8, 0.6]
    for i, r in enumerate([R, int(R*.72), int(R*.47), int(R*.24)]):
        cv.create_oval(CX-r,CY-r,CX+r,CY+r,
                       outline=ring_colors[i], width=ring_widths[i])

    # ── cross hair ────────────────────────────────────────
    cv.create_line(CX-R-8,CY,CX+R+8,CY, fill="#0d2d3a",width=1)
    cv.create_line(CX,CY-R-8,CX,CY+R+8, fill="#0d2d3a",width=1)
    for ang in [45,135,225,315]:
        a = math.radians(ang)
        cv.create_line(CX,CY,CX+math.cos(a)*R,CY+math.sin(a)*R,
                       fill="#091f2a",width=1)

    # ── center rings ──────────────────────────────────────
    eye_outer = cv.create_oval(CX-42,CY-42,CX+42,CY+42,
                               outline="#00eaff",width=1.5)
    eye_mid = cv.create_oval(CX-28,CY-28,CX+28,CY+28,
                             outline="#00eaff",width=1.5)
    eye_core = cv.create_oval(CX-7,CY-7,CX+7,CY+7,
                              fill="#00eaff",outline="")
    eye_glow = cv.create_oval(CX-72,CY-72,CX+72,CY+72,
                              outline="#00eaff",width=1, state="hidden")
    eye_pulse = cv.create_oval(CX-104,CY-104,CX+104,CY+104,
                               outline="#00ffb3",width=1, state="hidden")
    cv.create_text(CX, CY-10, text="REXA",
        fill="#d8faff", font=("Consolas",18,"bold"))
    cv.create_text(CX, CY+10, text="ONLINE",
        fill="#00ffb3", font=("Consolas",8,"bold"))

    # ── LOGO & subtitle ───────────────────────────────────
    logo_y = CY + R + 60
    cv.create_text(CX, logo_y, text="JARVIS  AI",
        fill="#00eaff", font=("Consolas", 54, "bold"))
    cv.create_text(CX, logo_y+52,
        text="◆  COMMAND CENTER  //  INITIALIZING  ◆",
        fill="#1a5565", font=("Consolas", 11))

    # ── progress bar ──────────────────────────────────────
    pb_y  = logo_y + 98
    pbx1, pbx2 = CX-300, CX+300
    cv.create_rectangle(pbx1, pb_y, pbx2, pb_y+4,
                        fill="#071820", outline="#0e3545")
    prog_rect = cv.create_rectangle(pbx1, pb_y, pbx1, pb_y+4,
                                    fill="#00eaff", outline="")
    # glow effect on progress
    prog_glow = cv.create_rectangle(pbx1, pb_y-1, pbx1, pb_y+5,
                                    fill="#00eaff", outline="",
                                    stipple="gray50")
    status_id = cv.create_text(CX, pb_y+20,
        text="INITIALIZING...", fill="#00eaff",
        font=("Consolas", 9))
    pct_id = cv.create_text(CX, pb_y+36,
        text="0 %", fill="#2a7080",
        font=("Consolas", 8))
    # Bengali companion text makes the boot status understandable at a glance.
    bengali_status_id = cv.create_text(CX, pb_y+53,
        text="লোড হচ্ছে...", fill="#1a5565",
        font=("Segoe UI", 9, "bold"))

    # Segmented loader: this stays in motion even while a boot step is waiting.
    loader_y = pb_y - 22
    loader_segments = []
    segment_w, segment_gap, segment_count = 16, 7, 16
    loader_start = CX - ((segment_w + segment_gap) * segment_count - segment_gap) / 2
    for i in range(segment_count):
        x1 = loader_start + i * (segment_w + segment_gap)
        loader_segments.append(cv.create_rectangle(
            x1, loader_y, x1 + segment_w, loader_y + 3,
            fill="#0b2a33", outline=""
        ))

    # A narrow highlight travels across the filled part of the progress bar.
    progress_shine = cv.create_rectangle(
        pbx1, pb_y - 2, pbx1, pb_y + 6,
        fill="#b8fbff", outline="", state="hidden"
    )

    # ── boot log area ─────────────────────────────────────
    log_y0 = pb_y + 58
    log_lines = []

    # ── animated elements (dynamic) ───────────────────────
    # sweep trail — pre-create lines for smooth redraw
    TRAIL = 18
    trail_ids = []
    for _ in range(TRAIL):
        tid = cv.create_line(CX,CY,CX+R,CY,
                             fill="#05090d", width=2)
        trail_ids.append(tid)
    sweep_id = cv.create_line(CX,CY,CX+R,CY,
                              fill="#00ffb3", width=2)

    # scan line
    scan_id = cv.create_line(CX-R, CY, CX+R, CY,
                             fill="#00eaff", width=1,
                             dash=(8,5))

    # radar dots — pre-create, toggle visibility
    NDOTS = 24
    dot_data = []
    for _ in range(NDOTS):
        ang = random.uniform(0, 2*math.pi)
        rad = random.uniform(R*0.18, R*0.90)
        dx  = CX + math.cos(ang)*rad
        dy2 = CY + math.sin(ang)*rad
        did = cv.create_oval(dx-4,dy2-4,dx+4,dy2+4,
                             fill="#00eaff", outline="",
                             state="hidden")
        gid = cv.create_oval(dx-9,dy2-9,dx+9,dy2+9,
                             fill="#001a22", outline="",
                             state="hidden")
        dot_data.append({"ang": ang, "rad": rad,
                          "did": did, "gid": gid})

    # ── animation state ───────────────────────────────────
    st = {
        "sweep"   : 0.0,
        "scan_y"  : float(CY - R),
        "scan_dir": 1,
        "prog"    : 0.0,
        "prog_tgt": 0.0,
        "running" : True,
        "frame"   : 0,
        "blink"   : True,
        "bengali_status": "লোড হচ্ছে...",
    }

    # ── clock updater ─────────────────────────────────────
    def tick_clock():
        import datetime as _dt
        if not st["running"]: return
        cv.itemconfig(clock_id,
            text=_dt.datetime.now().strftime("%H : %M : %S"))
        boot_win.after(500, tick_clock)
    tick_clock()

    # ── MAIN ANIMATION LOOP (16ms ≈ 60 fps) ──────────────
    def animate():
        if not st["running"]:
            return

        f = st["frame"]

        # 1. sweep line — smooth continuous rotation
        st["sweep"] += 0.025          # speed
        sw_ang = st["sweep"]
        ex = CX + math.cos(sw_ang) * R
        ey = CY + math.sin(sw_ang) * R
        cv.coords(sweep_id, CX, CY, ex, ey)

        # 2. trail lines — smooth fade
        for i, tid in enumerate(trail_ids):
            t_ang = sw_ang - (i+1) * 0.055
            tx = CX + math.cos(t_ang) * R
            ty = CY + math.sin(t_ang) * R
            # fade: brightest near sweep, dark at tail
            fade = (TRAIL - i) / TRAIL
            g = int(fade * 80)
            b = int(fade * 130)
            col = f"#00{g:02x}{b:02x}"
            cv.coords(tid, CX, CY, tx, ty)
            cv.itemconfig(tid, fill=col,
                          width=max(1, int(fade*2.5)))

        # 3. scan line — smooth bounce
        st["scan_y"] += st["scan_dir"] * 2.5
        if st["scan_y"] >= CY + R:
            st["scan_dir"] = -1
        elif st["scan_y"] <= CY - R:
            st["scan_dir"] = 1
        sy = st["scan_y"]
        # clip to circle boundary
        half_w = math.sqrt(max(0, R**2-(sy-CY)**2))
        cv.coords(scan_id, CX-half_w, sy, CX+half_w, sy)

        # 4. dots — appear/fade based on sweep angle
        sw_deg = math.degrees(sw_ang) % 360
        for d in dot_data:
            dot_deg = math.degrees(d["ang"]) % 360
            diff = (sw_deg - dot_deg) % 360
            if diff < 40:
                fade2 = (40 - diff) / 40
                g2 = int(fade2 * 234)
                b2 = int(fade2 * 255)
                col2 = f"#00{g2:02x}{b2:02x}"
                cv.itemconfig(d["gid"], state="normal",
                    fill=f"#00{int(fade2*30):02x}{int(fade2*50):02x}")
                cv.itemconfig(d["did"], state="normal",
                    fill=col2)
            else:
                cv.itemconfig(d["did"], state="hidden")
                cv.itemconfig(d["gid"], state="hidden")

        # 5. central AI eye pulse — more dramatic JARVIS-style boot glow
        eye_scale = 70 + (math.sin(sw_ang * 2.2) + 1) * 20
        cv.coords(eye_glow, CX - eye_scale, CY - eye_scale, CX + eye_scale, CY + eye_scale)
        cv.coords(eye_pulse, CX - (eye_scale + 34), CY - (eye_scale + 34), CX + (eye_scale + 34), CY + (eye_scale + 34))
        cv.itemconfig(eye_glow, state="normal", outline="#00eaff")
        cv.itemconfig(eye_pulse, state="normal", outline="#00ffb3")
        cv.itemconfig(eye_core, fill="#9ef7ff" if st["blink"] else "#00eaff")

        # 6. progress bar — smooth easing toward target
        if st["prog"] < st["prog_tgt"]:
            st["prog"] += (st["prog_tgt"] - st["prog"]) * 0.06
        p = st["prog"]
        fill_x = pbx1 + (pbx2 - pbx1) * p / 100
        cv.coords(prog_rect, pbx1, pb_y, fill_x, pb_y+4)
        cv.coords(prog_glow,  pbx1, pb_y-1, fill_x+3, pb_y+5)

        # 7. continuous loading effect: chase the active segment and sweep light
        # across the already loaded portion of the bar.
        active_segment = (f // 4) % segment_count
        for i, segment in enumerate(loader_segments):
            distance = (active_segment - i) % segment_count
            if distance == 0:
                color = "#d8faff"
            elif distance in (1, 2):
                color = "#00eaff"
            elif distance in (3, 4):
                color = "#126072"
            else:
                color = "#0b2a33"
            cv.itemconfig(segment, fill=color)

        if p > 1:
            shine_x = pbx1 + ((f * 4) % max(1, int(fill_x - pbx1)))
            cv.coords(progress_shine, shine_x - 12, pb_y - 2, shine_x + 12, pb_y + 6)
            cv.itemconfig(progress_shine, state="normal")
        else:
            cv.itemconfig(progress_shine, state="hidden")
        cv.itemconfig(bengali_status_id, text=st["bengali_status"])

        # 8. blink clock label
        if f % 30 == 0:
            st["blink"] = not st["blink"]
            cv.itemconfig(clock_id,
                fill="#00eaff" if st["blink"] else "#005566")

        st["frame"] += 1
        boot_win.after(16, animate)   # 60 fps

    animate()

    # ── boot sequence messages ────────────────────────────
    steps = [
        (800,  12, "LOADING AUDIO ENGINE...", "অডিও ইঞ্জিন লোড হচ্ছে...",
                   "[ OK ]  pygame 2.6.1 — mixer ready",          "beep"),
        (1800, 25, "CONNECTING VOICE ENGINE...", "ভয়েস ইঞ্জিন সংযুক্ত হচ্ছে...",
                   "[ OK ]  edge-tts — Guy Neural online",         "scan"),
        (2800, 40, "AUTHENTICATING GEMINI AI...", "জেমিনি এআই যাচাই করা হচ্ছে...",
                   "[ OK ]  gemini AI client — authenticated",     "beep"),
        (3800, 55, "LOADING HUD SOUND SYSTEM...", "হাড সাউন্ড সিস্টেম লোড হচ্ছে...",
                   "[ OK ]  14 HUD clips loaded (MP3)",            "notify"),
        (4800, 67, "STARTING SPEECH MODULE...", "স্পিচ মডিউল চালু হচ্ছে...",
                   "[ OK ]  speech recognition — active",          "beep"),
        (5800, 78, "PREPARING SELENIUM DRIVER...", "সেলেনিয়াম ড্রাইভার প্রস্তুত হচ্ছে...",
                   "[WAIT]  selenium — standby mode",              "alert"),
        (6800, 88, "STARTING SYSTEM MONITOR...", "সিস্টেম মনিটর চালু হচ্ছে...",
                   "[ OK ]  CPU / RAM / DISK monitor live",        "beep"),
        (7800, 96, "RUNNING FINAL CHECK...", "চূড়ান্ত পরীক্ষা চলছে...",
                   "[ OK ]  all modules verified",                  "success"),
    ]

    def add_log(msg):
        y = log_y0 + len(log_lines) * 19
        if y > sh - 30:
            return
        color = "#2a7080" if "OK" in msg else "#8a7020"
        lid = cv.create_text(CX-290, y, anchor="w",
            text=msg, fill=color,
            font=("Consolas", 8))
        log_lines.append(lid)

    for delay, pct, stat_msg, bengali_msg, log_msg, sfx_name in steps:
        def do_step(p=pct, sm=stat_msg, bm=bengali_msg, lm=log_msg, sn=sfx_name):
            st["prog_tgt"] = p
            st["bengali_status"] = bm
            cv.itemconfig(status_id, text=sm)
            cv.itemconfig(pct_id, text=f"{p} %")
            add_log(lm)
            play_sfx(sn)
        boot_win.after(delay, do_step)


    # ── READY + close ─────────────────────────────────────
    def show_ready():
        st["prog_tgt"] = 100
        st["bengali_status"] = "সব সিস্টেম প্রস্তুত"
        cv.itemconfig(status_id, text="ALL SYSTEMS ONLINE")
        cv.itemconfig(pct_id, text="100 %")
        # big READY text
        cv.create_text(CX, log_y0 + len(log_lines)*19 + 30,
            text="▪  SYSTEM READY  ▪",
            fill="#00ffb3", font=("Consolas", 14, "bold"))
        play_sfx("done")
        boot_win.after(2000, close_boot)

    def close_boot():
        st["running"] = False
        boot_win.destroy()

    boot_win.after(8800, show_ready)
    # ── keep boot window on top ────────────────────────────
    boot_win.grab_set()
def toggle_boss_mode():
    state["boss_mode"] = not state.get("boss_mode", False)

    if state["boss_mode"]:
        globals()["CYAN"] = "#7ef9ff"
        globals()["CYAN2"] = "#4cc9f0"
        globals()["GREEN"] = "#7cffb2"
        globals()["RED"] = "#ff5f7a"
        globals()["YELLOW"] = "#ffe66d"
        globals()["GRID"] = "#123e4f"
        globals()["BG"] = "#030811"
        globals()["PANEL"] = "#091722"
        globals()["PANEL2"] = "#0f1f2b"
        log_message("REXA", "Boss Mode enabled. Threat matrix online.")
        speak("Boss mode engaged. Command center fully active and fully operational.")
    else:
        globals()["CYAN"] = "#12b3e4"
        globals()["CYAN2"] = "#008fb3"
        globals()["GREEN"] = "#00ffb3"
        globals()["RED"] = "#ff4d6d"
        globals()["YELLOW"] = "#ffe66d"
        globals()["GRID"] = "#10343c"
        globals()["BG"] = "#05090d"
        globals()["PANEL"] = "#081116"
        globals()["PANEL2"] = "#0b151b"
        log_message("REXA", "Normal mode restored.")
        speak("Normal operations restored. All systems stable.")

    try:
        if "root" in globals() and root is not None:
            root.configure(bg=BG)
        if "status_line" in globals() and status_line is not None:
            status_line.configure(bg=CYAN)
        if "capsule" in globals() and capsule is not None:
            capsule.configure(bg=PANEL2, highlightbackground=CYAN, highlightcolor=CYAN)
    except Exception:
        pass

    animate_hud_glow()
    set_mode("SYSTEM READY")


def wish_me():
    """Announce a short, time-aware startup greeting and readiness state."""
    hour = dt.datetime.now().hour
    if 5 <= hour < 12:
        greeting = "Good morning, Sir"
    elif 12 <= hour < 17:
        greeting = "Good afternoon, Sir"
    elif 17 <= hour < 21:
        greeting = "Good evening, Sir"
    else:
        greeting = "Good night, Sir"
    readiness = "JARVIS AI is online and all available systems are ready."
    message = f"{greeting}. {readiness}"
    log_message("REXA", message)
    play_sfx("startup")
    speak(message)


def startup():
    start_proactive_sentinel()
    start_background_observer()
    show_boot_animation()
    create_floating_status_pill()
    ensure_audio_mixer()

    message = (
        "শুভ সন্ধ্যা, Boss। \U0001F44B\n"
        "JARVIS অনলাইনে আছে এবং আপনার কমান্ডের জন্য প্রস্তুত।\n"
        "আপনি বাংলা, Banglish বা English-এ প্রশ্ন করতে পারেন — "
        "REXA বাংলায় উত্তর দেবে।\n"
        "সব কমান্ড দেখতে HELP লিখুন।\n"
        "REXA-এর সঙ্গে কথা বলতে Voice Chat চালু করুন।"
    )

    log_message("REXA", message)

    if gemini_client is None:
        log_message(
            "REXA",
            "\u26A0\uFE0F Gemini isn't connected yet. "
            "Put GEMINI_API_KEY in your .env file."
        )

    wish_me()


# ============================================================
# START APP
# ============================================================

process_ui_queue()
clock_loop()
routine_check_loop()
update_monitor()
draw_radar()

root.after(
    300,
    entry.focus_set
)

root.after(
    700,
    startup
)

root.mainloop()
