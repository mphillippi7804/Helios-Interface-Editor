import bisect
import glob
import itertools
import threading
import time
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import tkinter.font as tkfont
import json
import math
import copy
import os
import re
import shutil
import sys
import tempfile
import textwrap
import zipfile
import ctypes
from datetime import datetime
from typing import NamedTuple, Optional
from Text_Editor_Prototype import FILE_TYPES as TEXT_EDITOR_FILE_TYPES, TextEditorPrototype

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
except ImportError:
    DND_FILES = None
    TkinterDnD = None

# Name of the window/taskbar icon inside the app assets folder.
APP_ICON_FILE = os.path.join("assets", "Helios Interface Editor.ico")


# ── Default folders of the file dialogs ───────────────────────────────────────
# Everything is kept under the user's Documents\Helios folder: interfaces in Interfaces\
# HeliosInterfaces, and this editor's own files in Interface Editor (reference tables in
# Reference Tables, Monitor Removal results and packages in Profile Exports).  Generate
# starts in the DCS install's aircraft folder.
INTERFACE_FOLDER_UNDER_DOCUMENTS = ("Helios", "Interfaces", "HeliosInterfaces")
REFERENCE_TABLE_FOLDER_UNDER_DOCUMENTS = ("Helios", "Interface Editor", "Reference Tables")
# Monitor Removal reads a Helios profile from Documents\Helios\Profiles and writes the result,
# under the same file name, to Documents\Helios\Interface Editor\Profile Exports.
PROFILE_FOLDER_UNDER_DOCUMENTS = ("Helios", "Profiles")
# Package picks the profile images from Documents\Helios\Images.
IMAGE_FOLDER_UNDER_DOCUMENTS = ("Helios", "Images")
EXPORT_FOLDER_UNDER_DOCUMENTS = ("Helios", "Interface Editor", "Profile Exports")
# The DCS install: <Program Files>\Eagle Dynamics\<DCS folder>\Mods\aircraft.  The DCS folder
# is usually "DCS World" but may be named differently (e.g. "DCS World OpenBeta").
DCS_PUBLISHER_FOLDER = r"C:\Program Files\Eagle Dynamics"
DCS_PREFERRED_INSTALL_NAME = "DCS World"
DCS_AIRCRAFT_UNDER_INSTALL = ("Mods", "aircraft")


def documents_folder():
    """The user's Documents folder - where Windows really keeps it (it may be moved, e.g.
    into OneDrive), asked from Windows itself (Known Folder 'Documents'); elsewhere, or when
    that fails, ~/OneDrive/Documents when it exists, else ~/Documents."""
    if sys.platform.startswith("win"):
        try:
            import ctypes.wintypes
            class KnownFolderId(ctypes.Structure):
                _fields_ = [("Data1", ctypes.c_uint32), ("Data2", ctypes.c_uint16),
                            ("Data3", ctypes.c_uint16), ("Data4", ctypes.c_ubyte * 8)]
            documents_id = KnownFolderId(0xFDD39AD0, 0x238F, 0x46AF,
                                         (ctypes.c_ubyte * 8)(0xAD, 0xB4, 0x6C, 0x85, 0x48, 0x03, 0x69, 0xC7))
            path_pointer = ctypes.c_wchar_p()
            if ctypes.windll.shell32.SHGetKnownFolderPath(ctypes.byref(documents_id), 0, None,
                                                          ctypes.byref(path_pointer)) == 0:
                folder_path = path_pointer.value
                ctypes.windll.ole32.CoTaskMemFree(path_pointer)
                if folder_path:
                    return folder_path
        except Exception:
            pass
    home_folder = os.path.expanduser("~")
    onedrive_documents = os.path.join(home_folder, "OneDrive", "Documents")
    return onedrive_documents if os.path.isdir(onedrive_documents) else os.path.join(home_folder, "Documents")


def ensure_folder(folder_path):
    """Create folder_path (and its parents) when it does not exist.  Returns the path, or
    None when it cannot be created (e.g. no permission)."""
    try:
        os.makedirs(folder_path, exist_ok=True)
        return folder_path
    except OSError:
        return None


def default_interface_folder():
    r"""Where Save / Save As of an interface (profile) starts: Documents\Helios\Interfaces\
    HeliosInterfaces, created when missing (None if even that fails)."""
    return ensure_folder(os.path.join(documents_folder(), *INTERFACE_FOLDER_UNDER_DOCUMENTS))


def default_reference_table_folder():
    r"""Where saving and loading reference tables (Reference and Old References) start:
    Documents\Helios\Interface Editor\Reference Tables, created when missing (None when it
    cannot be created)."""
    return ensure_folder(os.path.join(documents_folder(), *REFERENCE_TABLE_FOLDER_UNDER_DOCUMENTS))


def default_profile_folder():
    r"""Where Monitor Removal's file picker starts: Documents\Helios\Profiles when it exists,
    otherwise the Documents folder (the folder is not created: nothing is saved there)."""
    profile_folder = os.path.join(documents_folder(), *PROFILE_FOLDER_UNDER_DOCUMENTS)
    return profile_folder if os.path.isdir(profile_folder) else documents_folder()


def default_image_folder():
    r"""Where Package's image folder picker starts: Documents\Helios\Images when it exists,
    otherwise the Documents folder (the folder is not created: nothing is saved there)."""
    image_folder = os.path.join(documents_folder(), *IMAGE_FOLDER_UNDER_DOCUMENTS)
    return image_folder if os.path.isdir(image_folder) else documents_folder()


def default_export_folder():
    r"""Where Monitor Removal and Package save their results: Documents\Helios\Interface Editor\
    Profile Exports, created when missing (None when it cannot be created)."""
    return ensure_folder(os.path.join(documents_folder(), *EXPORT_FOLDER_UNDER_DOCUMENTS))


def default_aircraft_folder():
    r"""Where Generate's folder picker starts: <DCS_PUBLISHER_FOLDER>\<DCS folder>\Mods\aircraft.
    The DCS folder named DCS_PREFERRED_INSTALL_NAME is used when present, otherwise any folder
    of DCS_PUBLISHER_FOLDER that has Mods\aircraft (alphabetically).  None when DCS is not
    found - the install folder is never created.  One listing of the publisher folder."""
    preferred = os.path.join(DCS_PUBLISHER_FOLDER, DCS_PREFERRED_INSTALL_NAME, *DCS_AIRCRAFT_UNDER_INSTALL)
    if os.path.isdir(preferred):
        return preferred
    try:
        install_names = sorted(os.listdir(DCS_PUBLISHER_FOLDER), key=str.lower)
    except OSError:
        return None
    for install_name in install_names:
        aircraft_folder = os.path.join(DCS_PUBLISHER_FOLDER, install_name, *DCS_AIRCRAFT_UNDER_INSTALL)
        if os.path.isdir(aircraft_folder):
            return aircraft_folder
    return None


def dialog_start_folder(current_file_path, default_folder_function):
    """The folder a file dialog opens in: the current file's folder when there is one,
    otherwise the default folder (default_folder_function)."""
    if current_file_path and os.path.isdir(os.path.dirname(current_file_path)):
        return os.path.dirname(current_file_path)
    return default_folder_function()


LIVE_SYNC_DELAY_MS = 600       # how long after the last change the other editor is brought up to date


def is_logger_hook_line(line):
    """True for a line of Export.lua that is an Argument Logger hook, whatever folder or file path
    it names: it sets HELIOS_ARGUMENT_LOGGER_DIR or runs ArgumentLogger_For_PythonGUI.lua."""
    return "HELIOS_ARGUMENT_LOGGER_DIR" in line or "ArgumentLogger_For_PythonGUI.lua" in line


def icon_search_base_folders():
    """Folders the window icon is looked for in, best first: the PyInstaller bundle folder, the
    folder of the .exe and the folder the script was started from (each with its _internal
    folder), then the folder of this file and the working folder."""
    base_folders = []
    for base_folder in (getattr(sys, "_MEIPASS", None),
                        os.path.dirname(os.path.abspath(sys.executable)) if getattr(sys, "frozen", False) else None,
                        os.path.dirname(os.path.abspath(sys.argv[0])) if sys.argv and sys.argv[0] else None):
        if base_folder:
            base_folders += [base_folder, os.path.join(base_folder, "_internal")]
    try:
        base_folders.append(os.path.dirname(os.path.abspath(__file__)))
    except NameError:
        pass
    base_folders.append(os.getcwd())
    return base_folders


def find_app_icon():
    """The window icon file, or "" when it cannot be found.  Looked for where a PyInstaller build
    puts it (the bundle folder sys._MEIPASS, its _internal folder, the folder of the .exe) and
    where the script runs from, both in an "assets" folder and loose beside the program, so the
    icon shows whether the build is one-file or one-folder and whether the icon was added with
    --add-data (assets) or just copied next to the .exe."""
    icon_name = os.path.basename(APP_ICON_FILE)
    icon_folder = os.path.dirname(APP_ICON_FILE)
    for base_folder in icon_search_base_folders():
        for candidate_path in (os.path.join(base_folder, icon_folder, icon_name), os.path.join(base_folder, icon_name)):
            if os.path.isfile(candidate_path):
                return candidate_path
    return ""


def resource_path(filename):
    """Absolute path to a bundled resource. Works for a normal run (file next to
    the script) and for a PyInstaller one-file build (sys._MEIPASS)."""
    base = getattr(sys, "_MEIPASS", None)
    if base is None:
        try:
            base = os.path.dirname(os.path.abspath(__file__))
        except NameError:
            base = os.getcwd()
    return os.path.join(base, filename)


def strip_private_fields(value):
    """Return a copy of a profile value (dict / list / scalar) without the editor's private
    bookkeeping keys - every key that starts with an underscore - at any depth."""
    if isinstance(value, dict):
        return {
            key: strip_private_fields(item)
            for key, item in value.items()
            if not key.startswith("_")
        }
    if isinstance(value, list):
        return [strip_private_fields(item) for item in value]
    return value


def scaled_value_uses_base_scale(entry):
    """True when a ScaledNetworkValue keeps the legacy baseValue/scale form
    instead of calibration points."""
    if not isinstance(entry, dict):
        return False
    if "baseValue" in entry or "scale" in entry:
        return True
    calibration = entry.get("calibration")
    if isinstance(calibration, dict):
        points = calibration.get("points")
        if isinstance(points, list) and points:
            return False
    return False


SCALED_BASE_SCALE_UNUSED_KEYS = ("calibration", "points", "precision", "minValue", "maxValue",
                                 "minMappedValue", "maxMappedValue")


def rebuilt_scaled_calibration(calibration, existing_points, existing_precision):
    """The {"points", "precision"} calibration of a ScaledNetworkValue, taken from its calibration
    block, else from loose points / precision fields (default precision 5)."""
    precision = existing_precision if existing_precision not in (None, "") else 5
    points = None
    if isinstance(calibration, dict):
        if isinstance(calibration.get("points"), list):
            points = copy.deepcopy(calibration["points"])
        calibration_precision = calibration.get("precision", precision)
        if calibration_precision not in (None, ""):
            precision = calibration_precision
    if points is None and isinstance(existing_points, list):
        points = copy.deepcopy(existing_points)
    return {"points": points if isinstance(points, list) else [], "precision": precision}


def normalize_scaled_for_export(function):
    """Write ScaledNetworkValue in the schema it already uses.

    Standard entries store calibration.points + calibration.precision. Some
    HIF entries instead use baseValue + scale without any calibration.
    Preserve whichever shape is already present; never rewrite one into the
    other on save.
    """
    if function.get("heliosType") != DCS_LEADER + "ScaledNetworkValue":
        return
    if scaled_value_uses_base_scale(function):
        for unused_key in SCALED_BASE_SCALE_UNUSED_KEYS:
            function.pop(unused_key, None)
        return
    calibration = function.get("calibration")
    existing_points = function.pop("points", None)
    existing_precision = function.pop("precision", None)
    function["calibration"] = rebuilt_scaled_calibration(calibration, existing_points, existing_precision)

# The device/name "prettifier" lives in the Lua compiler module. Import it once
# (lazily-safe) so the editor still runs even when that file isn't present.
try:
    from parser_engine import _prettify_device as _core_prettify_device
except Exception:
    _core_prettify_device = None


def prettify_label(text):
    """Clean up a raw device/name string for display while preserving the
    user's original capitalization: take the trailing dotted leaf, turn
    underscores into spaces, and leave letter case untouched (e.g.
    'MAIN.gear_handle' -> 'gear handle', 'MY_DEVICE' -> 'MY DEVICE')."""
    raw_text = str(text or "").strip()
    if not raw_text:
        return ""
    leaf = raw_text.split(".")[-1]
    return leaf.replace("_", " ")


def device_names_as_shown(raw_names):
    """Device names the way JSON Controls shows them (prettify_label), alphabetical, without
    repeats - for the drop-downs of the dialogs that add or change devices."""
    shown = {prettify_label(name) for name in raw_names if str(name or "").strip()}
    shown.discard("")
    return sorted(shown, key=lambda name: (name.lower(), name))


def device_name_lookup(raw_names):
    """{lower-case name: stored name} so that a device name picked or typed as JSON Controls
    shows it ("ADI ARU 11 A") finds the stored name ("ADI_ARU_11_A").  A stored name always
    finds itself."""
    lookup = {}
    for raw_name in raw_names:
        raw_name = str(raw_name or "").strip()
        if raw_name:
            lookup.setdefault(prettify_label(raw_name).lower(), raw_name)
    for raw_name in raw_names:
        raw_name = str(raw_name or "").strip()
        if raw_name:
            lookup[raw_name.lower()] = raw_name
    return lookup


def get_monitor_workarea(window):
    """Return monitor work-area bounds (left, top, right, bottom) for window.

    On Windows this uses the monitor nearest to the supplied HWND so dialogs
    stay on the same display as their parent window.
    """
    try:
        if sys.platform.startswith("win"):
            user32 = ctypes.windll.user32

            class RECT(ctypes.Structure):
                _fields_ = [
                    ("left", ctypes.c_long),
                    ("top", ctypes.c_long),
                    ("right", ctypes.c_long),
                    ("bottom", ctypes.c_long),
                ]

            class MONITORINFO(ctypes.Structure):
                _fields_ = [
                    ("cbSize", ctypes.c_ulong),
                    ("rcMonitor", RECT),
                    ("rcWork", RECT),
                    ("dwFlags", ctypes.c_ulong),
                ]

            window.update_idletasks()
            monitor = user32.MonitorFromWindow(window.winfo_id(), 2)  # nearest monitor
            if monitor:
                info = MONITORINFO()
                info.cbSize = ctypes.sizeof(MONITORINFO)
                if user32.GetMonitorInfoW(monitor, ctypes.byref(info)):
                    work = info.rcWork
                    return work.left, work.top, work.right, work.bottom
    except Exception:
        pass

    # Fallback: Tk virtual-root geometry.
    try:
        window.update_idletasks()
        left = int(window.winfo_vrootx())
        top = int(window.winfo_vrooty())
        width = int(window.winfo_vrootwidth())
        height = int(window.winfo_vrootheight())
        if width > 0 and height > 0:
            return left, top, left + width, top + height
    except Exception:
        pass

    screen_width = int(window.winfo_screenwidth())
    screen_height = int(window.winfo_screenheight())
    return 0, 0, screen_width, screen_height


def clamp_rect_to_monitor(parent, position_x, position_y, width, height):
    """Clamp a child-window rectangle into the parent's monitor work area.
    Returns the (x, y) of the top-left corner after clamping."""
    left, top, right, bottom = get_monitor_workarea(parent)
    max_x = max(left, right - width)
    max_y = max(top, bottom - height)
    return max(left, min(position_x, max_x)), max(top, min(position_y, max_y))


def centered_position_on_parent(parent, width, height):
    """Center a child window over parent, then clamp to parent's monitor."""
    try:
        parent.update_idletasks()
        parent_width = parent.winfo_width()
        parent_height = parent.winfo_height()
        parent_x = parent.winfo_rootx()
        parent_y = parent.winfo_rooty()
    except Exception:
        parent_width = parent_height = 0
        parent_x = parent_y = 0

    if parent_width > 1 and parent_height > 1:
        position_x = parent_x + (parent_width - width) // 2
        position_y = parent_y + (parent_height - height) // 2
    else:
        left, top, right, bottom = get_monitor_workarea(parent)
        position_x = left + ((right - left - width) // 2)
        position_y = top + ((bottom - top - height) // 2)
    return clamp_rect_to_monitor(parent, position_x, position_y, width, height)


# ── Constants ──────────────────────────────────────────────────────────────────
DCS_LEADER = "DCS.Common."
BALL_ROTATION_TYPE = DCS_LEADER + "DCSBallRotation"

HELIOS_TYPES = [
    DCS_LEADER + "PushButton",
    DCS_LEADER + "Switch",
    DCS_LEADER + "Axis",
    DCS_LEADER + "RotaryEncoder",
    DCS_LEADER + "NetworkValue",
    DCS_LEADER + "ScaledNetworkValue",
    DCS_LEADER + "FlagValue",
    DCS_LEADER + "Text",
    DCS_LEADER + "DrawingValue",
    BALL_ROTATION_TYPE,
]

# Generates the tab labels in order
TAB_LABELS = {helios_type: re.sub(r"(\w)([A-Z])", r"\1 \2", helios_type.split(".")[-1])
              for helios_type in HELIOS_TYPES}
TAB_LABELS[BALL_ROTATION_TYPE] = "3D Ball"

BALL_AXIS_DEFAULTS = {
    "calibration x": {
        "points": [
            {"value": -1.0, "mappedValue": 180.0},
            {"value": 1.0, "mappedValue": -180.0},
        ],
        "precision": 1,
    },
    "calibration y": {
        "points": [
            {"value": 0.0, "mappedValue": 0.0},
            {"value": 1.0, "mappedValue": 1.0},
        ],
        "precision": 1,
    },
    "calibration z": {
        "points": [
            {"value": -1.0, "mappedValue": -180.0},
            {"value": 1.0, "mappedValue": 180.0},
        ],
        "precision": 1,
    },
}

# Default export "format" strings for each helios type. These are the values
# the Add/Edit dialog pre-fills for a NEW entry (and the user can change).
DEFAULT_PUSHBUTTON_FORMAT = "%1d"
DEFAULT_FLAG_FORMAT = "%0.1f"
DEFAULT_SWITCH_FORMAT = "%0.1f"
DEFAULT_AXIS_FORMAT = "%0.3f"
DEFAULT_ROTARY_FORMAT = "%0.3f"
DEFAULT_NETWORK_FORMAT = "%0.3f"
DEFAULT_SCALED_FORMAT = "%0.4f"
DEFAULT_DRAWING_FORMAT = "%.2f"

UNIT_GROUPS = [
    ("Generic Units", ["NoValue", "Numeric", "Text", "Boolean"]),
    ("Angle Units", ["Radians", "Degrees"]),
    ("Temperature Units", ["Celsius"]),
    ("Distance Units", ["Meters", "Kilometers", "Feet", "Miles", "NauticalMiles"]),
    ("Revolution Units", ["RPMPercent"]),
    ("Time Units", ["Seconds", "Minutes", "Hours"]),
    ("Mass Units", ["Pounds", "Kilograms"]),
    ("Area Units", ["SquareInch", "SquareFoot", "SquareCentimeter"]),
    ("Speed Units", ["MetersPerSecond", "FeetPerSecond", "FeetPerMinute", "MilesPerHour", "Knots", "KilometersPerHour"]),
    ("Mass Flow Units", ["PoundsPerHour"]),
    ("Pressure Units", ["PoundsPerSquareInch", "PoundsPerSquareFoot", "InchesOfMercury", "MilimetersOfMercury", "Millibar", "Bar", "KilgramsForcePerSquareCentimeter"]),
    ("Volume Units", ["Liters"]),
    ("Electrical Units", ["Volts"]),
]

# Standard description text applied per helios type by the "Set Descriptions"
# button. ScaledNetworkValue maps to None, meaning "leave the description
# exactly as it is" (it is intentionally left blank).
DESCRIPTION_BY_TYPE = {
    DCS_LEADER + "PushButton":         "Current State of This Button",
    DCS_LEADER + "Switch":             "Current Position of This Switch",
    DCS_LEADER + "FlagValue":          "Current State of This Indicator",
    DCS_LEADER + "Axis":               "Current Value of This Potentiometer",
    DCS_LEADER + "RotaryEncoder":      "Current Position of This Rotary Encoder",
    DCS_LEADER + "NetworkValue":       "Numeric Value Between 0 and 1",
    DCS_LEADER + "ScaledNetworkValue": "Mapped Output from lua min/max to desired range",   # leave blank, as it is now
    BALL_ROTATION_TYPE:                 "Single value containing X, Y & Z movement of the ADI Ball.",
    DCS_LEADER + "Text":               "Text Value",
    DCS_LEADER + "DrawingValue":       "0.0 to 1.0",
}

# Columns that hold DCS IDs. They are validated as positive integers and sorted
# numerically (not as strings) when the user clicks a column header.
ID_COLUMNS = {
    "id",
    "btn_deviceId", "pushId", "releaseId",
    "set_deviceId", "set_actionId",
    "inc_deviceId", "inc_actionId", "dec_deviceId", "dec_actionId",
    "deviceId", "actionId",
}

# Grid columns whose cell values are centred within their column. Covers every
# ID-type column plus the axis bounds, switch positions and calibration-point
# counts. Text columns (device, name, description) stay left-aligned.
CENTERED_COLUMNS = set(ID_COLUMNS) | {"argumentMin", "argumentMax", "positions", "points"}

# Optional (key, label) id fields validated per helios type by the entry dialog,
# in addition to the always-required Export ID(Arg).
_OPTIONAL_ID_CHECKS_BY_TYPE = {
    DCS_LEADER + "PushButton": [
        ("btn_deviceId", "Device ID"), ("pushId", "Push ID"), ("releaseId", "Release ID")],
    DCS_LEADER + "Axis": [
        ("set_deviceId", "Set Device ID"), ("set_actionId", "Set Action ID")],
    DCS_LEADER + "RotaryEncoder": [
        ("inc_deviceId", "Increment Device ID"), ("inc_actionId", "Increment Action ID"),
        ("dec_deviceId", "Decrement Device ID"), ("dec_actionId", "Decrement Action ID")],
    DCS_LEADER + "Switch": [
        ("deviceId", "Device ID"), ("switch_actionId", "Action ID (default)")],
}

# Entry-save dispatch. The methods stay separate for clarity, but the lookup
# table is shared instead of being rebuilt every time a row is saved.
ENTRY_FIELD_SAVER_NAMES = {
    DCS_LEADER + "PushButton": "_save_pushbutton",
    DCS_LEADER + "Axis": "_save_axis",
    DCS_LEADER + "NetworkValue": "_save_network",
    DCS_LEADER + "ScaledNetworkValue": "_save_scaled",
    BALL_ROTATION_TYPE: "_save_ball",
    DCS_LEADER + "RotaryEncoder": "_save_rotary",
    DCS_LEADER + "Switch": "_save_switch",
    DCS_LEADER + "DrawingValue": "_save_drawing",
}

# ── Theming ─────────────────────────────────────────────────────────────────────
# Three full colour palettes, chosen in Options > Color Scheme. apply_theme() copies a
# palette into the module-level colour names below; every widget reads those names at
# build time, so switching themes is a matter of re-applying a palette and rebuilding
# the UI.  The Default Palette is the Argument Logger's original look (the standard
# Windows colours) and is used when the editor starts.
DEFAULT_THEME = {
    "bg": "#f0f0f0", "mid": "#ffffff", "panel": "#f0f0f0",
    "row_odd": "#ffffff", "row_even": "#ffffff", "row_sel": "#0078d7", "row_sel_text": "#ffffff",
    "accent": "#0078d7", "accent2": "#c2560c",
    "text_pri": "#000000", "text_sec": "#555555", "text_head": "#000000",
    "border": "#adadad", "success": "#0b5e20", "warn": "#9a6700",
    "error": "#c42b1c", "danger_bg": "#fde7e9", "danger_fg": "#c42b1c",
}

DARK_THEME = {
    "bg": "#1a1f2e", "mid": "#252b3b", "panel": "#1e2436",
    "row_odd": "#252b3b", "row_even": "#2c3348", "row_sel": "#3a5a8c",
    "accent": "#4a9eff", "accent2": "#ff7c4a",
    "text_pri": "#e8eaf0", "text_sec": "#8b92a8", "text_head": "#b8c0d4",
    "border": "#363d52", "success": "#4aff8c", "warn": "#ffd24a",
    "error": "#ff4a6a", "danger_bg": "#4a1a2a", "danger_fg": "#ff4a6a",
}

GRAYSCALE_THEME = {
    "bg": "#202020", "mid": "#2b2b2b", "panel": "#242424",
    "row_odd": "#2b2b2b", "row_even": "#333333", "row_sel": "#505050",
    "accent": "#c4c4c4", "accent2": "#ff7c4a",
    "text_pri": "#e8e8e8", "text_sec": "#a0a0a0", "text_head": "#c8c8c8",
    "border": "#454545", "success": "#4aff8c", "warn": "#ffd24a",
    "error": "#ff4a6a", "danger_bg": "#4a1a2a", "danger_fg": "#ff4a6a",
}

# Theme name -> palette, and the names shown in Options > Color Scheme (in menu order).
THEMES = {"default": DEFAULT_THEME, "dark": DARK_THEME, "grayscale": GRAYSCALE_THEME}
THEME_MENU_LABELS = (("default", "Default Palette"), ("dark", "Dark Mode - Default"),
                     ("grayscale", "Dark Mode - Grayscale"))

# Colour names used throughout the UI (populated by apply_theme below).
DARK_BG = MID_BG = PANEL_BG = ROW_ODD = ROW_EVEN = ROW_SELECTED = ROW_SELECTED_TEXT = ""
ACCENT = ACCENT2 = TEXT_PRI = TEXT_SEC = TEXT_HEAD = BORDER = ""
SUCCESS = WARN = ERROR = DANGER_BG = DANGER_FG = ""


def apply_theme(palette):
    """Copy `palette` into the module-level colour names so the whole UI can
    read them. Call this before (re)building the window."""
    global DARK_BG, MID_BG, PANEL_BG, ROW_ODD, ROW_EVEN, ROW_SELECTED, ROW_SELECTED_TEXT
    global ACCENT, ACCENT2, TEXT_PRI, TEXT_SEC, TEXT_HEAD, BORDER
    global SUCCESS, WARN, ERROR, DANGER_BG, DANGER_FG
    DARK_BG   = palette["bg"]
    MID_BG    = palette["mid"]
    PANEL_BG  = palette["panel"]
    ROW_ODD   = palette["row_odd"]
    ROW_EVEN  = palette["row_even"]
    ROW_SELECTED   = palette["row_sel"]
    ROW_SELECTED_TEXT = palette.get("row_sel_text", palette["text_pri"])
    ACCENT    = palette["accent"]
    ACCENT2   = palette["accent2"]
    TEXT_PRI  = palette["text_pri"]
    TEXT_SEC  = palette["text_sec"]
    TEXT_HEAD = palette["text_head"]
    BORDER    = palette["border"]
    SUCCESS   = palette["success"]
    WARN      = palette["warn"]
    ERROR     = palette["error"]
    DANGER_BG = palette["danger_bg"]
    DANGER_FG = palette["danger_fg"]


apply_theme(DEFAULT_THEME)  # start with the Default Palette (the saved scheme is applied by HeliosEditor)


# ── Settings kept between runs ─────────────────────────────────────────────────
# The colour scheme and the Argument Logger's scan interval, in
# Documents\Helios\Interface Editor\Interface Editor Settings.json.
EDITOR_SETTINGS_FILE_NAME = "Interface Editor Settings.json"


def editor_settings_path():
    """Full path of the editor's settings file (in the Documents/Helios/Interface Editor folder)."""
    return os.path.join(documents_folder(), "Helios", "Interface Editor", EDITOR_SETTINGS_FILE_NAME)


def load_editor_settings():
    """The saved settings ({} when there are none or the file cannot be read)."""
    try:
        with open(editor_settings_path(), "r", encoding="utf-8") as settings_file:
            settings = json.load(settings_file)
    except (OSError, ValueError):
        return {}
    return settings if isinstance(settings, dict) else {}

FONT_MONO = ("Consolas", 9)
FONT_UI   = ("Segoe UI", 9)
FONT_HEAD = ("Segoe UI", 9, "bold")
FONT_TITLE= ("Segoe UI", 11, "bold")


def blank_flag_value_fields():
    """Default fields of a new Flag Value."""
    return {"exports": [{"format": DEFAULT_FLAG_FORMAT, "id": ""}]}


def blank_text_fields():
    """Default fields of a new Text value."""
    return {"exports": [{"isExportedEveryFrame": True, "id": ""}]}


def blank_push_button_fields():
    """Default fields of a new Push Button (export and one button)."""
    return {"exports": [{"format": DEFAULT_PUSHBUTTON_FORMAT, "isExportedEveryFrame": False, "id": ""}],
            "buttons": [{"deviceId": "", "pushId": "", "pushValue": 1.0, "releaseId": "", "releaseValue": 0.0}]}


def blank_axis_fields():
    """Default fields of a new Axis (export, argument range and the Set action)."""
    return {"exports": [{"format": DEFAULT_AXIS_FORMAT, "isExportedEveryFrame": False, "id": ""}],
            "loop": False,
            "argumentValue": "0.025",
            "argumentMin": "0.0",
            "argumentMax": "1.0",
            "actions": {"set": {"deviceId": "", "actionId": ""}}}


def blank_network_value_fields():
    """Default fields of a new Network Value."""
    return {"exports": [{"format": DEFAULT_NETWORK_FORMAT, "id": ""}], "unit": "Numeric"}


def blank_scaled_network_value_fields():
    """Default fields of a new Scaled Network Value (with a two-point calibration)."""
    return {"exports": [{"format": DEFAULT_SCALED_FORMAT, "id": ""}],
            "unit": "Numeric",
            "valueDescription": "",
            "exposeunscaledvalue": True,
            "calibration": {
                "minValue": "0.0",
                "maxValue": "1.0",
                "minMappedValue": "0.0",
                "maxMappedValue": "1.0",
                "points": [{"value": "0.0", "mappedValue": "0.0"}, {"value": "1.0", "mappedValue": "1.0"}],
                "precision": 5
            }}


def blank_drawing_value_fields():
    """Default fields of a new Drawing Value."""
    return {"exports": [{"format": DEFAULT_DRAWING_FORMAT, "id": ""}],
            "unit": "Numeric",
            "valueDescription": "Number with 0 being closed",
            "aircraftDrawArgument": ""}


def blank_ball_rotation_fields():
    """Default fields of a new Ball Rotation (one block of defaults per axis)."""
    fields = {"exports": [{"id": ""}]}
    for axis_key, axis_defaults in BALL_AXIS_DEFAULTS.items():
        fields[axis_key] = copy.deepcopy(axis_defaults)
    return fields


def blank_rotary_encoder_fields():
    """Default fields of a new Rotary Encoder (increment and decrement actions)."""
    return {"exports": [{"format": DEFAULT_ROTARY_FORMAT, "isExportedEveryFrame": False, "id": ""}],
            "unit": "Numeric",
            "argumentValue": 0.025,
            "actions": {
                "increment": {"deviceId": "", "actionId": ""},
                "decrement": {"deviceId": "", "actionId": ""}
            }}


def blank_switch_fields():
    """Default fields of a new Switch (two positions with descending argument values)."""
    return {"exports": [{"format": DEFAULT_SWITCH_FORMAT, "isExportedEveryFrame": False, "id": ""}],
            "deviceId": "",
            "positions": [
                {"argumentValue": "1.0", "name": "", "actionId": ""},   # descending until
                {"argumentValue": "0.0", "name": "", "actionId": ""}    # Swap Argument Values is used
            ]}


def blank_field_builders():
    """{Helios type: function giving the fields that type needs beyond the common ones}."""
    return {
        DCS_LEADER + "FlagValue": blank_flag_value_fields,
        DCS_LEADER + "Text": blank_text_fields,
        DCS_LEADER + "PushButton": blank_push_button_fields,
        DCS_LEADER + "Axis": blank_axis_fields,
        DCS_LEADER + "NetworkValue": blank_network_value_fields,
        DCS_LEADER + "ScaledNetworkValue": blank_scaled_network_value_fields,
        DCS_LEADER + "DrawingValue": blank_drawing_value_fields,
        BALL_ROTATION_TYPE: blank_ball_rotation_fields,
        DCS_LEADER + "RotaryEncoder": blank_rotary_encoder_fields,
        DCS_LEADER + "Switch": blank_switch_fields,
    }


def make_blank_entry(helios_type):
    """Create a new, empty Helios function of the given type with every field that type needs
    (device, name, description, exports, buttons / positions / actions, calibration ...)
    filled with its defaults."""
    blank_entry = {
        "heliosType": helios_type,
        "device": "",
        "name": "",
        "description": DESCRIPTION_BY_TYPE.get(helios_type) or "",
    }
    field_builder = blank_field_builders().get(helios_type)
    if field_builder is not None:
        blank_entry.update(field_builder())
    return blank_entry


def _fill_missing_from_default(entry, default):
    """Recursively add any key present in `default` but absent from `entry`,
    without ever touching a key the entry already has (even if blank)."""
    for key, default_value in default.items():
        if key not in entry:
            entry[key] = copy.deepcopy(default_value)
            continue
        current_value = entry[key]
        if isinstance(default_value, dict) and isinstance(current_value, dict):
            _fill_missing_from_default(current_value, default_value)
        elif isinstance(default_value, list) and isinstance(current_value, list) and current_value:
            _fill_list_items_from_default(current_value, default_value)


def _fill_list_items_from_default(items, default_items):
    """Fill each dict in a list from the default list's item at the same position (the first
    default item for positions beyond the default list)."""
    template = default_items[0] if default_items else None
    for index, item in enumerate(items):
        item_default = default_items[index] if index < len(default_items) else template
        if isinstance(item, dict) and isinstance(item_default, dict):
            _fill_missing_from_default(item, item_default)


def ensure_default_fields(function):
    """Backfill any field this editor knows about for the entry's helios type
    but that is missing from the loaded JSON (e.g. a hand-edited or
    externally-authored file), so a re-saved file is always fully populated.
    Existing values — including blanks the user cleared on purpose — are never
    overwritten."""
    helios_type = function.get("heliosType", "")
    if helios_type not in HELIOS_TYPES:
        return
    _fill_missing_from_default(function, make_blank_entry(helios_type))


# ── Utility ────────────────────────────────────────────────────────────────────
def first_export(entry):
    """Return the entry's first export dict, or {} when it has none.

    Real Helios profiles sometimes carry an empty ``exports`` list (some
    RotaryEncoders in some stock profiles do), so callers must never assume
    ``exports[0]`` exists."""
    exports = entry.get("exports")
    if isinstance(exports, list) and exports:
        first = exports[0]
        return first if isinstance(first, dict) else {}
    return {}


def get_all_ids(functions):
    """Every Export ID(Arg) used in the given functions, as a set of integers (blank or non-
    numeric ids are skipped)."""
    ids = set()
    for function in functions:
        for export in function.get("exports", []):
            export_id = str(export.get("id", "")).strip()
            if export_id:
                try:
                    ids.add(int(export_id))
                except ValueError:
                    pass
    return ids


def max_id(functions):
    """The highest Export ID(Arg) used in the given functions, or 0 when there is none."""
    ids = get_all_ids(functions)
    return max(ids) if ids else 0


def to_int(value):
    """Coerce id-like fields to int for JSON output.
    - Whole numbers ("3001", "3001.0", 3001) -> int 3001
    - Blank/None -> "" (preserves the original blank-field behavior)
    - Non-numeric text -> returned unchanged so nothing is lost
    """
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    text = str(value).strip()
    if text == "":
        return ""
    try:
        if text.lstrip("+-").isdigit():
            return int(text)
        as_float = float(text)
        if as_float.is_integer():
            return int(as_float)
    except (ValueError, TypeError):
        pass
    return value


def positive_int_or_none(value):
    """Interpret an ID-field value.
    Returns:
      None        -> the field was blank
      int (> 0)   -> a valid positive integer ID
      False       -> the field held something that is not a positive integer
    """
    text = str(value).strip()
    if text == "":
        return None
    try:
        if text.lstrip("+").isdigit():
            number = int(text)
            return number if number > 0 else False
        as_float = float(text)
        if as_float.is_integer() and as_float > 0:
            return int(as_float)
    except (ValueError, TypeError):
        pass
    return False


def int_sort_value(value, missing=float("inf")):
    """Return an integer suitable for numeric sorting, or `missing` when the
    value isn't a (signed) integer so blanks/non-numerics sort consistently."""
    text = str(value).strip()
    if text.lstrip("+-").isdigit():
        return int(text)
    return missing


# ── Helios type conversion ──────────────────────────────────────────────────────
# Several helios types store a "primary" DCS device id, but in different places.
# When the user changes a function's type we keep that device id (along with the
# common device/name/description/export-id fields) and reset everything else to
# the new type's defaults, since the type-specific wiring doesn't map cleanly.
def _push_device_id(entry):
    """Device ID of a Push Button: the deviceId of its first button."""
    return entry.get("buttons", [{}])[0].get("deviceId", "")


def _switch_device_id(entry):
    """Device ID of a Switch: its top-level deviceId (Switch functions keep one device for all
    positions). Used by get_primary_device_id."""
    return entry.get("deviceId", "")


def _axis_device_id(entry):
    """Device ID of an Axis: the deviceId of its 'set' action (an Axis has one action). Used by
    get_primary_device_id."""
    return entry.get("actions", {}).get("set", {}).get("deviceId", "")


def _rotary_device_id(entry):
    """Device ID of a Rotary Encoder: the deviceId of its increment action, else of its
    decrement action."""
    actions = entry.get("actions", {})
    return (actions.get("increment", {}).get("deviceId", "")
            or actions.get("decrement", {}).get("deviceId", ""))


_DEVICE_ID_GETTERS = {
    DCS_LEADER + "PushButton":    _push_device_id,
    DCS_LEADER + "Switch":        _switch_device_id,
    DCS_LEADER + "Axis":          _axis_device_id,
    DCS_LEADER + "RotaryEncoder": _rotary_device_id,
}


def get_primary_device_id(entry):
    """Best-effort: pull the main DCS device id out of a function entry,
    wherever the entry's helios type happens to keep it. Returns "" if none."""
    getter = _DEVICE_ID_GETTERS.get(entry.get("heliosType", ""))
    return getter(entry) if getter else ""


def _push_action_id(entry):
    """Action ID of a Push Button: the pushId of its first button, else its releaseId."""
    button = entry.get("buttons", [{}])[0]
    return button.get("pushId", "") or button.get("releaseId", "")


def _switch_default_action_id(entry):
    """The switch's display/derived default action id: the persisted default
    Action ID when one is stored. Otherwise derive it from the positions,
    preferring Position 2 (index 1) — in Helios/DCS the second position is the
    one that stays on the shared default, while Position 1 is the most likely
    to carry an override — and falling back to Position 1 for single-position
    switches."""
    default = entry.get("_switchDefaultActionId")
    if default not in (None, ""):
        return str(default)
    positions = entry.get("positions", [])
    for index in ((1, 0) if len(positions) > 1 else (0,)):
        action_id = str(positions[index].get("actionId", "")).strip()
        if action_id:
            return action_id
    return ""


def _axis_action_id(entry):
    """Action ID of an Axis: the actionId of its 'set' action. Used by get_primary_action_id."""
    return entry.get("actions", {}).get("set", {}).get("actionId", "")


def _rotary_action_id(entry):
    """Action ID of a Rotary Encoder: the actionId of its increment action, else of its
    decrement action."""
    actions = entry.get("actions", {})
    return (actions.get("increment", {}).get("actionId", "")
            or actions.get("decrement", {}).get("actionId", ""))


_ACTION_ID_GETTERS = {
    DCS_LEADER + "PushButton":    _push_action_id,
    DCS_LEADER + "Switch":        _switch_default_action_id,
    DCS_LEADER + "Axis":          _axis_action_id,
    DCS_LEADER + "RotaryEncoder": _rotary_action_id,
}


def get_primary_action_id(entry):
    """Best-effort: pull the main DCS action id out of a function entry.
    Returns "" when the type has no single action id (network/text values)."""
    getter = _ACTION_ID_GETTERS.get(entry.get("heliosType", ""))
    return getter(entry) if getter else ""


def _as_id_str(value):
    """An id as clean text for comparisons and display: None and "" become "", anything else its
    text form."""
    return str(value) if value not in (None, "") else ""


def _scan_actions_for_ids(entry):
    """Return (device_id, action_id) gleaned from any of the entry's `actions`
    sub-objects (set / increment / decrement / ...)."""
    device_id = ""
    action_id = ""
    actions = entry.get("actions", {})
    if isinstance(actions, dict):
        for sub in actions.values():
            if isinstance(sub, dict):
                device_id = device_id or _as_id_str(sub.get("deviceId"))
                action_id = action_id or _as_id_str(sub.get("actionId"))
    return device_id, action_id


def _first_button_device_id(entry):
    """Device id of the entry's first button, or "" when there is none."""
    buttons = entry.get("buttons", [])
    if isinstance(buttons, list) and buttons and isinstance(buttons[0], dict):
        return _as_id_str(buttons[0].get("deviceId"))
    return ""


def best_effort_ids(entry):
    """Return (device_id, action_id) as strings for *any* function, including
    types this editor doesn't model (AbsoluteEncoder, the VHF encoders, etc.).
    Tries the type-aware getters first, then falls back to scanning the entry's
    `actions` sub-objects, a top-level deviceId, or the first button."""
    device_id = _as_id_str(get_primary_device_id(entry))
    action_id = _as_id_str(get_primary_action_id(entry))
    scanned_device, scanned_action = _scan_actions_for_ids(entry)
    device_id = device_id or scanned_device or _as_id_str(entry.get("deviceId"))
    action_id = action_id or scanned_action
    if not device_id:
        device_id = _first_button_device_id(entry)
    return device_id, action_id


def set_primary_device_id(entry, device_id):
    """Write a device id into the place the entry's helios type expects it.
    No-op for types that have no single primary device id (network/text values)."""
    if device_id in ("", None):
        return
    helios_type = entry.get("heliosType", "")
    if helios_type == DCS_LEADER + "PushButton":
        entry["buttons"][0]["deviceId"] = to_int(device_id)
    elif helios_type == DCS_LEADER + "Switch":
        entry["deviceId"] = to_int(device_id)
    elif helios_type == DCS_LEADER + "Axis":
        entry["actions"]["set"]["deviceId"] = to_int(device_id)
    elif helios_type == DCS_LEADER + "RotaryEncoder":
        entry["actions"]["increment"]["deviceId"] = to_int(device_id)
        entry["actions"]["decrement"]["deviceId"] = to_int(device_id)


def set_primary_action_id(entry, action_id):
    """Write an action id into the place the entry's helios type expects it.
    For a PushButton the action id maps to *both* pushId and releaseId; for a
    Switch it is written to every position. No-op for types that have no single
    primary action id (network/text values)."""
    if action_id in ("", None):
        return
    value = to_int(action_id)
    helios_type = entry.get("heliosType", "")
    if helios_type == DCS_LEADER + "PushButton":
        entry["buttons"][0]["pushId"] = value
        entry["buttons"][0]["releaseId"] = value
    elif helios_type == DCS_LEADER + "Switch":
        for position in entry.get("positions", []):
            position["actionId"] = value
    elif helios_type == DCS_LEADER + "Axis":
        entry["actions"]["set"]["actionId"] = value
    elif helios_type == DCS_LEADER + "RotaryEncoder":
        entry["actions"]["increment"]["actionId"] = value
        entry["actions"]["decrement"]["actionId"] = value


def convert_entry_type(entry, new_type):
    """Build a fresh entry of `new_type` that preserves the common fields and the
    export id from `entry`, carrying the primary device id where it maps cleanly.
    All other type-specific fields are reset to the new type's defaults."""
    new_entry = make_blank_entry(new_type)
    new_entry["device"]      = entry.get("device", "")
    new_entry["name"]        = entry.get("name", "")
    # Always re-stamp the description with the destination type's default.
    new_entry["description"] = DESCRIPTION_BY_TYPE.get(new_type) or entry.get("description", "")
    # Preserve the export id (first export) so existing wiring/links stay intact.
    old_exports = entry.get("exports", [{}])
    old_id = old_exports[0].get("id", "") if old_exports else ""
    if new_entry.get("exports"):
        new_entry["exports"][0]["id"] = to_int(old_id)
    # Best-effort device-id and action-id carryover between the two types.
    set_primary_device_id(new_entry, get_primary_device_id(entry))
    set_primary_action_id(new_entry, get_primary_action_id(entry))
    return new_entry


def device_action_sort_key(entry):
    """Sort key used for saving, the Full View, and the in-memory order after
    every add / load / import.

    Entries that have *neither* a device id nor an action id — the display
    values such as NetworkValue / FlagValue / ScaledNetworkValue / Text — are
    ordered first, alphabetically by device name and then by name.

    Entries that have a device id and/or action id are ordered after those
    display-only entries, by primary device id and then by primary action id
    (ids compare as integers; a missing id sorts last within its group via
    int_sort_value's +inf)."""
    device_value = int_sort_value(get_primary_device_id(entry))
    action_value = int_sort_value(get_primary_action_id(entry))
    if device_value == float("inf") and action_value == float("inf"):
        return (0,
                str(entry.get("device", "")).lower(),
                str(entry.get("name", "")).lower(),
                0.0, 0.0)
    return (1, device_value, action_value, "", "")


def device_name_sort_key(entry):
    """Sort key: alphabetical by device name, then by name (both
    case-insensitive). Used as the alternative save / Full View ordering."""
    return (str(entry.get("device", "")).lower(), str(entry.get("name", "")).lower())


# The two save / Full View ordering options the user can pick between.
# key -> (menu label, sort-key function)
SORT_METHODS = {
    "deviceaction": ("Device ID, then Action ID", device_action_sort_key),
    "devicename":   ("Device Name, then Name (alphabetical)", device_name_sort_key),
}


def find_last_added_function(editor, helios_type):
    """The function of this type that was created most recently in this session (highest
    _created_session_index), falling back to the editor's remembered last-added function.
    Used to pre-fill Duplicate Last."""
    best = None
    best_index = -1
    for function in editor._data.get("functions", []):
        if function.get("heliosType") != helios_type:
            continue
        created_index = function.get("_created_session_index", -1)
        if created_index > best_index:
            best = function
            best_index = created_index

    if best is not None:
        return best

    last_added = getattr(editor, "_last_added_function", None)
    if last_added is not None and last_added.get("heliosType") == helios_type:
        return last_added
    return None


SESSION_MARKER_KEYS = ("_saved_session_index", "_created_session_index")


def function_signature(function):
    """What identifies a function independently of its Python object: type, device, name and
    Export IDs.  Used to find the starred function again when the profile's functions were
    rebuilt (live sync with the Text Editor, undo / document switches)."""
    return (function.get("heliosType"), str(function.get("device", "")), str(function.get("name", "")),
            tuple(str(export_entry.get("id", "")) for export_entry in function.get("exports", [])
                  if isinstance(export_entry, dict)))


def matching_function(functions, remembered):
    """The function in `functions` with the same signature as `remembered` (or None)."""
    if remembered is None:
        return None
    wanted = function_signature(remembered)
    for function in functions:
        if function_signature(function) == wanted:
            return function
    return None


def carry_session_markers(old_functions, new_functions):
    """Copy the session markers (which function was saved / created last, the star) from the
    functions of the old profile onto the equal functions (same signature) of a rebuilt one,
    so the star stays where it was.  Functions that changed keep no marker."""
    old_by_signature = {}
    for function in old_functions:
        old_by_signature.setdefault(function_signature(function), function)
    for function in new_functions:
        old = old_by_signature.get(function_signature(function))
        if old is None:
            continue
        for key in SESSION_MARKER_KEYS:
            if key in old and key not in function:
                function[key] = old[key]


def find_last_saved_function(editor, helios_type):
    """The function of this type that was saved most recently in this session (highest
    _saved_session_index), falling back to the editor's remembered last-saved function. That
    row is shown with a star."""
    best = None
    best_index = -1
    for function in editor._data.get("functions", []):
        if function.get("heliosType") != helios_type:
            continue
        saved_index = function.get("_saved_session_index", -1)
        if saved_index > best_index:
            best = function
            best_index = saved_index

    if best is not None:
        return best

    last_saved = getattr(editor, "_last_saved_function", None)
    if last_saved is not None and last_saved.get("heliosType") == helios_type:
        return matching_function(editor._data.get("functions", []), last_saved) or last_saved
    return None


def duplicate_last(editor, helios_type):
    """Duplicate the most recently saved device of `helios_type` within
    the given `editor` instance. Clears export ids and refreshes the UI.
    """
    last_saved = find_last_saved_function(editor, helios_type)
    if last_saved is None:
        messagebox.showinfo("No Entry", "No previous saved entry to duplicate for this tab.", parent=editor)
        return

    entry = copy.deepcopy(last_saved)
    for export_entry in entry.get("exports", []):
        export_entry["id"] = ""
    entry["name"] = (entry.get("name", "") or "") + " (copy)"
    entry[ADDED_FLAG] = True
    editor._push_undo_state()
    editor._data["functions"].append(entry)
    editor._last_added_device = entry.get("device", "")
    editor._last_added_device_id = get_primary_device_id(entry)
    editor._last_added_function = entry
    editor._mark_saved(entry)                    # the copy now carries the star of its category
    editor._sort_functions()
    editor._refresh_all()
    editor._update_max_id()

    # Select the duplicated entry and immediately open it for editing.
    for index, function in enumerate(editor._data["functions"]):
        if function is entry:
            editor._select_tab(helios_type)
            editor._select_function(helios_type, index)
            editor._edit_entry(helios_type)
            break

def duplicate_selected(editor, helios_type):
    """Duplicate the currently selected row in the given `editor` tab.
    Clears export ids and opens the duplicate for editing."""
    tree = editor._trees.get(helios_type)
    if tree is None:
        return
    selection = tree.selection()
    if not selection:
        messagebox.showinfo("No Selection", "Select a row to duplicate.", parent=editor)
        return
    if len(selection) > 1:
        messagebox.showinfo("Select One",
                            "Duplicate Selected works on a single row — select just one.",
                            parent=editor)
        return
    item_id = selection[0]
    tags = tree.item(item_id, "tags")
    function_index = int(tags[0]) if tags else -1
    if function_index < 0:
        return

    original = editor._data["functions"][function_index]
    entry = copy.deepcopy(original)
    entry["_created_session_index"] = editor._next_created_session_index
    editor._next_created_session_index += 1
    for export_entry in entry.get("exports", []):
        export_entry["id"] = ""
    entry["name"] = (entry.get("name", "") or "") + " (copy)"
    entry[ADDED_FLAG] = True
    editor._push_undo_state()
    editor._data["functions"].append(entry)
    editor._last_added_device = entry.get("device", "")
    editor._last_added_device_id = get_primary_device_id(entry)
    editor._last_added_function = entry
    editor._mark_saved(entry)                    # the copy now carries the star of its category
    editor._sort_functions()
    editor._refresh_all()
    editor._update_max_id()

    for index, function in enumerate(editor._data["functions"]):
        if function is entry:
            editor._select_tab(helios_type)
            editor._select_function(helios_type, index)
            editor._edit_entry(helios_type)
            break


# The canonical "axis" values that must keep a one-decimal form when saved or
# shown. Every other float is rounded to at most three decimal places.
SPECIAL_FLOAT_STRINGS = {
    -1.0: "-1.0",
    -0.5: "-0.5",
    0.0:  "0.0",
    0.5:  "0.5",
    1.0:  "1.0",
}


def format_float(value):
    """Format a float for saving / display.

    The canonical values -1.0, -0.5, 0.0, 0.5 and 1.0 are written exactly in
    that one-decimal form. Every other value is rounded to at most three
    decimal places, with any trailing zeros trimmed (e.g. 0.025 -> "0.025",
    0.100 -> "0.1", 3.14159 -> "3.142")."""
    try:
        number = float(value)
    except (TypeError, ValueError):
        return str(value)
    # Round first so values that drift onto a canonical value (e.g. 0.49996 or
    # a tiny 0.0001) still take the canonical one-decimal form. Adding 0.0
    # normalises a possible -0.0 before the lookup.
    rounded = round(number, 3) + 0.0
    if rounded in SPECIAL_FLOAT_STRINGS:
        return SPECIAL_FLOAT_STRINGS[rounded]
    text = f"{rounded:.3f}".rstrip("0").rstrip(".")
    if text in ("", "-", "-0"):
        return "0.0"
    return text


def _coerce_to_float(value):
    """Turn an int or numeric string into a float; leave bools, blanks and
    non-numeric text untouched. Used to funnel a value into format_float so the
    canonical SPECIAL_FLOAT_STRINGS form is applied even when the source stored
    it as a bare integer (e.g. a switch position of "1" or a pushValue of 0)."""
    if isinstance(value, bool):
        return value
    if isinstance(value, float):
        return value
    if isinstance(value, int):
        return float(value)
    if isinstance(value, str):
        text = value.strip()
        if text == "":
            return value
        try:
            return float(text)
        except (ValueError, TypeError):
            return value
    return value


def _coerce_keys(mapping, keys):
    """Coerce the given keys of a dict in place to floats, when the dict has
    them. A no-op for non-dicts."""
    if not isinstance(mapping, dict):
        return
    for key in keys:
        if key in mapping:
            mapping[key] = _coerce_to_float(mapping[key])


def _coerce_keys_in_list(items, keys):
    """Coerce the given keys to floats in every dict found in `items`."""
    for item in items or []:
        _coerce_keys(item, keys)


def normalize_special_floats(entry):
    """Coerce the specific value fields that should use the canonical
    SPECIAL_FLOAT_STRINGS formatting to floats, so they are written and shown in
    that form even when stored as bare integers. Scoped to exactly:

    * ScaledNetworkValue : calibration.points[].value, .mappedValue
    * DCSBallRotation    : calibration x/y/z.points[].value, .mappedValue
      * PushButton         : buttons[].pushValue, .releaseValue
      * Switch             : positions[].argumentValue
      * Axis               : argumentMin, argumentMax

    ID fields and everything else are left untouched. Mutates and returns
    `entry`."""
    _coerce_keys(entry, ("argumentMin", "argumentMax"))
    _coerce_keys_in_list(entry.get("buttons"), ("pushValue", "releaseValue"))
    _coerce_keys_in_list(entry.get("positions"), ("argumentValue",))
    calibration = entry.get("calibration")
    if isinstance(calibration, dict):
        _coerce_keys_in_list(calibration.get("points"), ("value", "mappedValue"))
    for axis_key in BALL_AXIS_DEFAULTS:
        axis_calibration = entry.get(axis_key)
        if isinstance(axis_calibration, dict):
            _coerce_keys_in_list(axis_calibration.get("points"), ("value", "mappedValue"))
    return entry


def _equal_values(first, second):
    """Compare two raw field values for equality: numerically when both are
    numeric (so 1 and "1.0" count as equal), otherwise by trimmed string."""
    coerced_first = _coerce_to_float(first)
    coerced_second = _coerce_to_float(second)
    if isinstance(coerced_first, float) and isinstance(coerced_second, float):
        return abs(coerced_first - coerced_second) < 1e-9
    return str(first).strip() == str(second).strip()


def arg_min_max_match(entry):
    """True when an entry defines both argumentMin and argumentMax and the two
    hold the same value — meaning no range of travel. Checked for every function
    regardless of helios type (Axis, AbsoluteEncoder, the VHF encoders, ...),
    since argumentMin/argumentMax are the schema's universal range bounds."""
    if "argumentMin" not in entry or "argumentMax" not in entry:
        return False
    return _equal_values(entry.get("argumentMin"), entry.get("argumentMax"))


def _duplicate_position_value(entry):
    """Return the argumentValue shared by two or more of a switch's positions, or
    None if every position value is distinct."""
    seen = []
    for position in entry.get("positions", []) or []:
        if not isinstance(position, dict) or "argumentValue" not in position:
            continue
        value = position.get("argumentValue")
        if any(_equal_values(value, prior) for prior in seen):
            return value
        seen.append(value)
    return None


def _points_conflict(point_a, point_b):
    """True when two calibration points share a `value` but map it to different
    `mappedValue`s."""
    if "value" not in point_a or "value" not in point_b:
        return False
    return (_equal_values(point_a.get("value"), point_b.get("value"))
            and not _equal_values(point_a.get("mappedValue"), point_b.get("mappedValue")))


def _calibration_conflict(entry):
    """Return (value, mappedA, mappedB) for the first pair of ScaledNetworkValue
    calibration points that share a `value` but map to different `mappedValue`s,
    or None if there is no such conflict."""
    calibration = entry.get("calibration", {})
    points = calibration.get("points", []) if isinstance(calibration, dict) else []
    cleaned = [point for point in points if isinstance(point, dict)]
    for point_a_position, point_a in enumerate(cleaned):
        for point_b in cleaned[point_a_position + 1:]:
            if _points_conflict(point_a, point_b):
                return (point_a.get("value"), point_a.get("mappedValue"),
                        point_b.get("mappedValue"))
    return None


def _ball_axis_conflict(entry, axis_key):
    """For one 3D Ball calibration axis (e.g. 'calibration x'): the first pair of points that
    share a value but map to different results, as (value, mapped A, mapped B), or None."""
    axis_calibration = entry.get(axis_key)
    if not isinstance(axis_calibration, dict):
        return None
    points = axis_calibration.get("points", [])
    cleaned = [point for point in points if isinstance(point, dict)]
    for point_a_position, point_a in enumerate(cleaned):
        for point_b in cleaned[point_a_position + 1:]:
            if _points_conflict(point_a, point_b):
                return (point_a.get("value"), point_a.get("mappedValue"),
                        point_b.get("mappedValue"))
    return None


def _arg_min_max_issue(entry):
    """Problem text when a function's Argument Min equals its Argument Max (a range of zero),
    else None."""
    if "argumentMin" in entry and "argumentMax" in entry \
            and _equal_values(entry.get("argumentMin"), entry.get("argumentMax")):
        return f"Argument Min equals Argument Max ({format_float(entry.get('argumentMin', ''))})"
    return None


def _switch_issue(entry):
    """Problem text when two positions of a Switch share the same argument value, else None."""
    duplicate = _duplicate_position_value(entry)
    if duplicate is not None:
        return f"Two or more positions share argumentValue {format_float(duplicate)}"
    return None


def _scaled_issue(entry):
    """Problem text when a Scaled Network Value's calibration maps one value to two different
    results, else None."""
    conflict = _calibration_conflict(entry)
    if conflict is None:
        return None
    value, mapped_a, mapped_b = conflict
    return (f"Calibration value {format_float(value)} maps to both "
            f"{format_float(mapped_a)} and {format_float(mapped_b)}")


def _ball_issue(entry):
    """Problem text for the first 3D Ball axis whose calibration maps one value to two
    different results, else None."""
    for axis_key, axis_label in (("calibration x", "X"), ("calibration y", "Y"), ("calibration z", "Z")):
        conflict = _ball_axis_conflict(entry, axis_key)
        if conflict is None:
            continue
        value, mapped_a, mapped_b = conflict
        return (f"Calibration {axis_label} value {format_float(value)} maps to both "
                f"{format_float(mapped_a)} and {format_float(mapped_b)}")
    return None


def _button_value_clash(button):
    """True when a Push Button's push value equals its release value (pressing it would change
    nothing)."""
    return (isinstance(button, dict) and "pushValue" in button and "releaseValue" in button
            and _equal_values(button.get("pushValue"), button.get("releaseValue")))


def _pushbutton_issue(entry):
    """Problem text for the first button of a Push Button whose push and release values are
    equal, else None."""
    for button in entry.get("buttons", []) or []:
        if _button_value_clash(button):
            return f"Push value equals Release value ({format_float(button.get('pushValue', ''))})"
    return None


# Per-type validation rules, dispatched by helios type in validation_issue.
_TYPE_VALIDATORS = {
    DCS_LEADER + "Switch": _switch_issue,
    DCS_LEADER + "ScaledNetworkValue": _scaled_issue,
    BALL_ROTATION_TYPE: _ball_issue,
    DCS_LEADER + "PushButton": _pushbutton_issue,
}


def validation_issue(entry):
    """Return a short description of a validation problem with this function, or
    None when it passes. Rules:

      * Any type        : argumentMin equals argumentMax (no range of travel).
      * Switch          : two or more positions share an argumentValue
                          (this also covers "min equals max", since a set whose
                          min equals its max is all-equal).
      * ScaledNetworkValue : two calibration points share a `value` but map to
                          different `mappedValue`s.
      * PushButton      : a button's pushValue equals its releaseValue.

    The generic min/max rule wins first; otherwise the type-specific rule runs."""
    generic = _arg_min_max_issue(entry)
    if generic is not None:
        return generic
    validator = _TYPE_VALIDATORS.get(entry.get("heliosType", ""))
    return validator(entry) if validator else None


def cast_numbers_to_strings(value):
    """Recursively convert every numeric value (int/float) to its string form,
    walking dicts and lists. Booleans and None are left untouched so flags such
    as isExportedEveryFrame keep their type. Used on save so the written file
    stores all numbers as strings. Floats are formatted by format_float so the
    canonical axis values keep their one-decimal form and all other floats are
    limited to three decimal places."""
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        return format_float(value)
    if isinstance(value, dict):
        return {key: cast_numbers_to_strings(item) for key, item in value.items()}
    if isinstance(value, list):
        return [cast_numbers_to_strings(item) for item in value]
    return value


def _string_to_number(text):
    """Turn a numeric-looking string into an int or float; leave anything else
    (e.g. '%.3f', 'Initial', '') unchanged."""
    stripped = text.strip()
    if stripped == "":
        return text
    if re.fullmatch(r"[+-]?\d+", stripped):
        try:
            return int(stripped)
        except ValueError:
            return text
    if stripped.lower().lstrip("+-") in ("inf", "infinity", "nan"):
        return text  # don't let float() turn these into inf/nan
    try:
        return float(stripped)
    except (ValueError, TypeError):
        return text


TEXT_KEYS_KEPT_AS_TEXT = {"name", "description", "valueDescription"}


def cast_dict_values_to_numbers(value):
    """A copy of a dict with its numeric-looking strings cast, except under the text-only keys."""
    return {key: (item if key in TEXT_KEYS_KEPT_AS_TEXT else cast_strings_to_numbers(item))
            for key, item in value.items()}


def cast_strings_to_numbers(value):
    """Recursively convert every numeric-looking string into an int or float,
    walking dicts and lists. Non-numeric strings and all other types are left
    untouched. Used on open so numbers come back in as numbers."""
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return _string_to_number(value)
    if isinstance(value, dict):
        return cast_dict_values_to_numbers(value)
    if isinstance(value, list):
        return [cast_strings_to_numbers(item) for item in value]
    return value


# Some hand-edited/exported profiles (e.g. a .hif.json file) spell this
# key "actionID" instead of the "actionId" this editor reads everywhere, so
# Switch positions silently look empty on load. Normalize it on open.
def normalized_action_key(key):
    """"actionId" for any casing of actionid (a string key); every other key unchanged."""
    return "actionId" if isinstance(key, str) and key.lower() == "actionid" else key


def normalize_action_id_keys(value):
    """Recursively rename any dict key that case-insensitively matches
    "actionid" to "actionId", so mixed-casing in a profile's JSON (e.g.
    "actionID") doesn't hide values from the rest of the editor."""
    if isinstance(value, dict):
        return {normalized_action_key(key): normalize_action_id_keys(item) for key, item in value.items()}
    if isinstance(value, list):
        return [normalize_action_id_keys(item) for item in value]
    return value


# ── Dialog base ────────────────────────────────────────────────────────────────
class EntryDialog(tk.Toplevel):
    """Modal dialog for adding or editing one Helios function of any type."""
    def __init__(self, parent, title, helios_type, existing=None, functions=None, edit_index=None):
        """Build the modal Add / Edit dialog for one Helios function of helios_type. existing
        pre-fills the fields (an entry being edited, or a seed for a new one); functions is
        the whole profile, used for the duplicate-id checks; edit_index is the edited
        function's position (None when adding). result is the finished entry, or None when
        cancelled."""
        super().__init__(parent)
        self.withdraw()
        self._parent = parent
        self.transient(parent)
        self.title(title)
        self.helios_type = helios_type
        self.functions = functions or []
        self.edit_index = edit_index
        self.result = None
        if helios_type == DCS_LEADER + "ScaledNetworkValue":
            self._prepare_scaled_format(existing)

        self.configure(bg=DARK_BG)
        self.resizable(True, True)
        self.grab_set()

        self._vars = {}
        self._position_vars = []
        # Last shared switch Action ID actually set by the user via the shared
        # field, used by the propagation trace to tell "still following the
        # default" from a manually typed value. Starts unset (None) so the
        # first real edit propagates to every position field.
        self._switch_action_prev = None
        self._position_count_var = tk.IntVar(value=2)
        self._min_var = tk.DoubleVar(value=0.0)
        self._max_var = tk.DoubleVar(value=1.0)
        # When True the auto-generated switch position values are assigned in
        # reverse (decreasing) order (toggled by the "Swap Position Values"
        # button); names stay anchored to their rows. Defaults to True so new
        # switches, and newly added positions on them, list argument values in
        # decreasing order by default.
        self._positions_reversed = True
        # Per-position Action ID sub-rows are hidden by default; the Positions
        # header button toggles them on.
        self._show_position_actions = False
        self._position_action_button = None
        # ScaledNetworkValue calibration points (dynamic, like switch positions)
        self._calibration_point_vars = []
        self._calibration_point_count_var = tk.IntVar(value=2)
        self._ball_axis_enabled_vars = {}
        self._ball_axis_point_counts = {}
        # Debounce timers: rebuild the position / point rows only once the user
        # has paused typing, so a multi-digit count (e.g. "12") doesn't rebuild
        # at "1" first and throw away rows in between.
        self._position_rebuild_after = None
        self._calibration_rebuild_after = None

        self._build_ui(existing)
        self._auto_fit_dialog_to_content(center_on_parent=True, force_recenter=True)
        self.deiconify()

    # ── helpers ──────────────────────────────────────────────────────────────
    def _frame(self, parent, **kwargs):
        """A plain dialog-coloured frame (extra keyword arguments go to tk.Frame)."""
        return tk.Frame(parent, bg=DARK_BG, **kwargs)

    def _label(self, parent, text, sub=False):
        """A dialog label; sub=True uses the secondary (dimmer) text colour."""
        colour = TEXT_SEC if sub else TEXT_HEAD
        return tk.Label(parent, text=text, bg=DARK_BG, fg=colour, font=FONT_UI)

    def _entry(self, parent, width=28):
        """A text box in the dialog's style (flat, monospace, accent outline when focused)."""
        return tk.Entry(parent, width=width, bg=MID_BG, fg=TEXT_PRI, insertbackground=TEXT_PRI,
                        relief="flat", font=FONT_MONO,
                        highlightthickness=1, highlightcolor=ACCENT, highlightbackground=BORDER)

    def _row(self, parent, label, key, default="", sub=False, row=None):
        """Add a 'label + text box' row for field key with a default value, remember its
        StringVar in self._vars, and return the next free grid row."""
        row_index = row if row is not None else len(self._vars)
        self._label(parent, label, sub).grid(row=row_index, column=0, sticky="w", padx=(8, 4), pady=3)
        var = tk.StringVar(value=str(default))
        entry_widget = self._entry(parent)
        entry_widget.configure(textvariable=var)
        entry_widget.grid(row=row_index, column=1, sticky="ew", padx=(0, 8), pady=3)
        self._vars[key] = var
        return row_index + 1

    def _bool_dropdown_row(self, parent, label, key, default=False, row=None):
        """A label + readonly True/False dropdown, stored in self._vars like
        a normal text row ("True"/"False" strings)."""
        row_index = row if row is not None else len(self._vars)
        self._label(parent, label).grid(row=row_index, column=0, sticky="w", padx=(8, 4), pady=3)
        var = tk.StringVar(value="True" if self._coerce_bool_value(default) else "False")
        combo = ttk.Combobox(parent, textvariable=var, values=["False", "True"],
                             state="readonly", width=6, font=FONT_MONO, style="Dark.TCombobox")
        combo.grid(row=row_index, column=1, sticky="w", padx=(0, 8), pady=3)
        self._vars[key] = var
        return row_index + 1

    def _prepare_scaled_format(self, existing):
        """Remember both ways a Scaled Network Value can be written (base value + scale, or
        calibration points) so switching between them in the dialog loses nothing, and which one
        the entry uses now."""
        blank_scaled = make_blank_entry(self.helios_type)
        existing_calibration = copy.deepcopy((existing or {}).get("calibration"))
        self._scaled_format_cache = copy.deepcopy((existing or {}).get("_scaledFormatCache"))
        if not isinstance(self._scaled_format_cache, dict):
            self._scaled_format_cache = {
                "base": {
                    "baseValue": str((existing or {}).get("baseValue", "0.0")),
                    "scale": str((existing or {}).get("scale", "1.0")),
                },
                "calibration": existing_calibration or copy.deepcopy(blank_scaled["calibration"]),
            }
        self._scaled_format = (existing or {}).get("_scaledFormatActive")
        if self._scaled_format not in {"base", "calibration"}:
            self._scaled_format = "base" if scaled_value_uses_base_scale(existing or {}) else "calibration"
        self._scaled_entry_seed = copy.deepcopy(existing or blank_scaled)

    def _auto_fit_dialog_to_content(self, center_on_parent=False, force_recenter=False):
        """Resize the dialog to fit content (grow or shrink) as dynamic rows
        are added or removed."""
        self.update_idletasks()
        monitor_left, monitor_top, monitor_right, monitor_bottom = get_monitor_workarea(self._parent)
        monitor_width = max(300, monitor_right - monitor_left)
        monitor_height = max(300, monitor_bottom - monitor_top)
        new_width, new_height = self._fitting_size(monitor_width, monitor_height)
        current_width = self.winfo_width()
        current_height = self.winfo_height()
        if (new_width == current_width and new_height == current_height) and not force_recenter:
            return

        if center_on_parent or not self.winfo_ismapped():
            try:
                position_x, position_y = centered_position_on_parent(self._parent, new_width, new_height)
            except Exception:  # noqa
                position_x, position_y = monitor_left, monitor_top
        else:
            position_x = self.winfo_x() - (new_width - current_width) // 2
            position_y = self.winfo_y() - (new_height - current_height) // 2
            position_x, position_y = clamp_rect_to_monitor(self._parent, position_x, position_y, new_width, new_height)
        self.geometry(f"{new_width}x{new_height}+{position_x}+{position_y}")

    def _fitting_size(self, monitor_width, monitor_height):
        """(width, height) that shows all the content, including the Save / Cancel row, and
        still fits the monitor."""
        requested_width = self._dialog_inner.winfo_reqwidth()
        requested_height = self._dialog_inner.winfo_reqheight()
        # Include non-scroll content (notably the bottom action button row) in
        # the fit budget so short dialogs still show Save/Cancel at high DPI.
        full_requested_width = self.winfo_reqwidth()
        full_requested_height = self.winfo_reqheight()
        needed_width_visual = requested_width + 80
        # Two-column form budget: left label + gap + right entry + paddings.
        needed_width_text = self._widest_label_pixels() + self._widest_value_pixels() + 240
        needed_width = min(max(needed_width_visual, needed_width_text, full_requested_width + 16),
                           max(320, monitor_width - 40))
        needed_height = min(max(requested_height + 80, full_requested_height + 16), max(240, monitor_height - 40))

        # Keep short value dialogs comfortably tall enough that their action
        # buttons remain visible on aggressive Windows DPI scaling.
        min_height_by_type = {
            DCS_LEADER + "NetworkValue": 360,
            DCS_LEADER + "FlagValue": 360,
        }
        target_min_height = min_height_by_type.get(self.helios_type)
        if target_min_height is not None:
            needed_height = max(needed_height, min(target_min_height, max(240, monitor_height - 40)))
        return needed_width, needed_height

    def _widest_label_pixels(self):
        """The widest label text anywhere in the dialog (used to size the label column)."""
        label_font = tkfont.Font(font=FONT_UI)
        widest = 0
        pending_widgets = [self._dialog_inner]
        while pending_widgets:
            widget = pending_widgets.pop()
            if isinstance(widget, tk.Label) and widget.cget("text"):
                widest = max(widest, label_font.measure(str(widget.cget("text"))))
            pending_widgets.extend(widget.winfo_children())
        return widest

    def _widest_value_pixels(self):
        """The widest value text among the dialog's entry fields."""
        value_font = tkfont.Font(font=FONT_MONO)
        value_vars = list(self._vars.values())
        value_vars += [var for position_vars in self._position_vars for var in position_vars]
        value_vars += [value_var for value_var, _mapped_var in self._calibration_point_vars]
        value_vars += [mapped_var for _value_var, mapped_var in self._calibration_point_vars]
        widest = 0
        for var in value_vars:
            try:
                text = str(var.get())
            except Exception:  # noqa
                text = ""
            if text:
                widest = max(widest, value_font.measure(text))
        return widest

    # ── build ─────────────────────────────────────────────────────────────────
    def _section(self, parent, text, row):
        """Render a section header + divider; returns the next free grid row."""
        tk.Label(parent, text=text, bg=DARK_BG, fg=ACCENT, font=FONT_HEAD
                 ).grid(row=row, column=0, columnspan=2, sticky="w", padx=8, pady=(10, 2))
        tk.Frame(parent, bg=BORDER, height=1).grid(
            row=row + 1, column=0, columnspan=2, sticky="ew", padx=8)
        return row + 2

    def _build_pushbutton_fields(self, inner, entry, export, existing, row):
        """Push Button fields: export format, exported-every-frame, and the button mapping
        (device id, push / release ids and values). Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        row = self._row(inner, "Format", "format",
                        export.get("format") or DEFAULT_PUSHBUTTON_FORMAT, row=row)
        row = self._bool_dropdown_row(inner, "Exported Every Frame", "isExportedEveryFrame",
                                      export.get("isExportedEveryFrame", False), row=row)
        row = self._section(inner, "Button Mapping", row)
        button = entry.get("buttons", [{}])[0]
        row = self._row(inner, "Device ID", "btn_deviceId", button.get("deviceId", ""), row=row)
        row = self._row(inner, "Push ID", "pushId", button.get("pushId", ""), row=row)
        row = self._row(inner, "Push Value", "pushValue", button.get("pushValue", 1.0), row=row)
        row = self._row(inner, "Release ID", "releaseId", button.get("releaseId", ""), row=row)
        row = self._row(inner, "Release Value", "releaseValue", button.get("releaseValue", 0.0), row=row)
        return row

    def _build_axis_fields(self, inner, entry, export, existing, row):
        """Axis fields: export format, exported-every-frame, loop, argument min / max and the
        'set' action's device / action ids. Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        row = self._row(inner, "Format", "format",
                        export.get("format") or DEFAULT_AXIS_FORMAT, row=row)
        row = self._bool_dropdown_row(inner, "Exported Every Frame", "isExportedEveryFrame",
                                      export.get("isExportedEveryFrame", False), row=row)
        row = self._section(inner, "Axis Config", row)
        row = self._bool_dropdown_row(inner, "Loop", "loop", entry.get("loop", False), row=row)
        row = self._row(inner, "Argument Min",   "argumentMin",   entry.get("argumentMin", "0.0"), row=row)
        row = self._row(inner, "Argument Max",   "argumentMax",   entry.get("argumentMax", "1.0"), row=row)
        row = self._section(inner, "Set Action", row)
        set_action = entry.get("actions", {}).get("set", {})
        row = self._row(inner, "Device ID",  "set_deviceId",  set_action.get("deviceId", ""), row=row)
        row = self._row(inner, "Action ID",  "set_actionId",  set_action.get("actionId", ""), row=row)
        return row

    def _build_network_fields(self, inner, entry, export, existing, row):
        """Network Value fields: just the export format. Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        return self._row(inner, "Format", "format",
                         export.get("format") or DEFAULT_NETWORK_FORMAT, row=row)

    def _build_flag_fields(self, inner, entry, export, existing, row):
        """Flag Value fields: just the export format. Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        return self._row(inner, "Format", "format",
                         export.get("format") or DEFAULT_FLAG_FORMAT, row=row)

    def _build_drawing_fields(self, inner, entry, export, existing, row):
        """Drawing Value fields: export format, unit (same dropdown as Scaled Network Value),
        value description, and the aircraft draw argument. aircraftDrawArgument is its own
        editable field (defaulting to the Export ID(Arg) for a new entry, same as before, but
        changeable independently of it from then on). Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        row = self._row(inner, "Format", "format",
                        export.get("format") or DEFAULT_DRAWING_FORMAT, row=row)
        self._add_drawing_unit_dropdown(inner, row, existing)
        row += 1
        row = self._row(inner, "Value Description", "valueDescription",
                        (existing or {}).get("valueDescription") or "Number with 0 being closed", row=row)
        default_draw_arg = (existing or {}).get("aircraftDrawArgument")
        if default_draw_arg in (None, ""):
            default_draw_arg = export.get("id", "")
        return self._row(inner, "Aircraft Draw Argument", "aircraftDrawArgument", default_draw_arg, row=row)

    def _add_drawing_unit_dropdown(self, inner, row, existing):
        """The Unit label and its drop-down button (a menu of the units, grouped) in a grid row;
        the chosen unit is kept in self._unit_var."""
        self._label(inner, "Unit").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        initial_unit = (existing or {}).get("unit") or "Numeric"
        if initial_unit not in {unit for _, units in UNIT_GROUPS for unit in units}:
            initial_unit = "Numeric"
        self._unit_var = tk.StringVar(value=initial_unit)
        unit_button = tk.Frame(inner, bg=MID_BG, bd=0, highlightthickness=1,
                               highlightcolor=ACCENT, highlightbackground=BORDER)
        unit_button.grid(row=row, column=1, sticky="ew", padx=(0, 8), pady=3)
        unit_button.columnconfigure(0, weight=1)
        unit_text = tk.Label(unit_button, text=initial_unit, bg=MID_BG, fg=TEXT_PRI,
                             font=FONT_MONO, anchor="w")
        unit_text.grid(row=0, column=0, sticky="ew", padx=(4, 0), pady=2)
        unit_arrow = tk.Label(unit_button, text="▼", bg=MID_BG, fg=TEXT_HEAD,
                              font=FONT_UI, anchor="e")
        unit_arrow.grid(row=0, column=1, sticky="e", padx=(0, 4), pady=2)
        unit_menu = tk.Menu(unit_button, tearoff=False, bg=MID_BG, fg=TEXT_PRI)

        def open_unit_menu(event=None):
            """Unit button clicked: drop the list of units down just below the button."""
            unit_menu.tk_popup(unit_button.winfo_rootx(), unit_button.winfo_rooty() + unit_button.winfo_height())

        def set_unit(value):
            """Unit picked from the list: store it and show it on the button."""
            self._unit_var.set(value)
            unit_text.configure(text=value)

        for widget in (unit_button, unit_text, unit_arrow):
            widget.configure(cursor="hand2")
            widget.bind("<Button-1>", open_unit_menu)
        for group_name, units in UNIT_GROUPS:
            unit_menu.add_separator()
            unit_menu.add_command(
                label=group_name,
                command=lambda: None,
                font=(FONT_UI[0], FONT_UI[1] + 1, "bold"),
                foreground=TEXT_SEC,
                background=MID_BG,
                activebackground=MID_BG,
                activeforeground=TEXT_SEC,
            )
            for unit_name in units:
                unit_menu.add_command(label=unit_name, command=lambda value=unit_name: set_unit(value))

    def _debounce_calibration_points(self):
        """Rebuild the calibration point rows 0.5 s after the user stops typing a point count,
        instead of on every keystroke."""
        if self._calibration_rebuild_after is not None:
            try:
                self.after_cancel(self._calibration_rebuild_after)
            except Exception:  # noqa
                pass
        self._calibration_rebuild_after = self.after(500, lambda: self._build_calibration_points(None))

    @staticmethod
    def _coerce_bool_value(value, default=False):
        """Read a true / false setting that may be stored as a bool or as text ('1', 'true',
        'yes', 'on' ...); anything unrecognised gives default."""
        if isinstance(value, bool):
            return value
        if isinstance(value, str):
            text = value.strip().lower()
            if text in {"1", "true", "yes", "on"}:
                return True
            if text in {"0", "false", "no", "off", ""}:
                return False
        if value in (None, ""):
            return default
        return bool(value)

    def _build_scaled_fields(self, inner, entry, export, existing, row):
        """Scaled Network Value fields: export format, unit, value description, expose-
        unscaled, and either base value / scale or a table of calibration points (switchable
        with the format toggle button). Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        row = self._row(inner, "Format", "format",
                        export.get("format") or DEFAULT_SCALED_FORMAT, row=row)
        row = self._add_scaled_format_toggle(inner, row)
        row = self._add_unit_dropdown(inner, existing, row)
        row = self._row(inner, "Value Description", "valueDescription",
                        (existing or {}).get("valueDescription", ""), row=row)

        self._expose_unscaled_var = tk.BooleanVar(
            value=self._coerce_bool_value((existing or {}).get("exposeunscaledvalue", True), True)
        )
        expose_text_var = tk.StringVar(value="true" if self._expose_unscaled_var.get() else "false")
        self._expose_unscaled_var.trace_add(
            "write",
            lambda *_: expose_text_var.set("true" if self._expose_unscaled_var.get() else "false")
        )

        if self._scaled_format == "base":
            row = self._row(inner, "Base Value", "baseValue",
                            (existing or {}).get("baseValue", "0.0"), row=row)
            row = self._row(inner, "Scale", "scale",
                            (existing or {}).get("scale", "1.0"), row=row)
            return row
        return self._build_calibration_fields(inner, existing, row, expose_text_var)

    def _add_scaled_format_toggle(self, inner, row):
        """The button that switches between base value / scale and calibration points."""
        toggle_text = ("Use Calibration Points" if self._scaled_format == "base"
                       else "Use Base Value / Scale")
        tk.Button(
            inner,
            text=f"⇄  {toggle_text}",
            bg=ACCENT2,
            fg=DARK_BG,
            font=FONT_UI,
            relief="flat",
            padx=10,
            pady=3,
            cursor="hand2",
            command=self._toggle_scaled_format,
        ).grid(row=row, column=1, sticky="w", padx=(0, 8), pady=(2, 6))
        return row + 1

    def _add_unit_dropdown(self, inner, existing, row):
        """The Unit row: a button that drops down the list of units, grouped. Returns the next row."""
        self._label(inner, "Unit").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        initial_unit = (existing or {}).get("unit") or "Numeric"
        if initial_unit not in {unit for _, units in UNIT_GROUPS for unit in units}:
            initial_unit = "Numeric"
        self._unit_var = tk.StringVar(value=initial_unit)
        unit_button = tk.Frame(inner, bg=MID_BG, bd=0, highlightthickness=1,
                               highlightcolor=ACCENT, highlightbackground=BORDER)
        unit_button.grid(row=row, column=1, sticky="ew", padx=(0, 8), pady=3)
        unit_button.columnconfigure(0, weight=1)

        unit_text = tk.Label(unit_button, text=initial_unit, bg=MID_BG, fg=TEXT_PRI,
                             font=FONT_MONO, anchor="w")
        unit_text.grid(row=0, column=0, sticky="ew", padx=(4, 0), pady=2)
        unit_arrow = tk.Label(unit_button, text="▼", bg=MID_BG, fg=TEXT_HEAD,
                              font=FONT_UI, anchor="e")
        unit_arrow.grid(row=0, column=1, sticky="e", padx=(0, 4), pady=2)

        unit_menu = tk.Menu(unit_button, tearoff=False, bg=MID_BG, fg=TEXT_PRI)
        for widget in (unit_button, unit_text, unit_arrow):
            widget.configure(cursor="hand2")
            widget.bind("<Button-1>", lambda _event: self._open_unit_menu(unit_button, unit_menu))
        self._fill_unit_menu(unit_menu, unit_text)
        return row + 1

    @staticmethod
    def _open_unit_menu(unit_button, unit_menu):
        """Unit button clicked in the Scaled Network Value fields: drop the list of units down
        just below the button so one can be picked."""
        unit_menu.tk_popup(unit_button.winfo_rootx(), unit_button.winfo_rooty() + unit_button.winfo_height())

    def _fill_unit_menu(self, unit_menu, unit_text):
        """Add each group heading and its units to the unit list."""
        for group_name, units in UNIT_GROUPS:
            unit_menu.add_separator()
            unit_menu.add_command(
                label=group_name,
                command=lambda: None,
                font=(FONT_UI[0], FONT_UI[1] + 1, "bold"),
                foreground=TEXT_SEC,
                background=MID_BG,
                activebackground=MID_BG,
                activeforeground=TEXT_SEC,
            )
            for unit_name in units:
                unit_menu.add_command(
                    label=unit_name,
                    command=lambda value=unit_name: self._set_unit(value, unit_text),
                )

    def _set_unit(self, value, unit_text):
        """Unit picked from the list: store it and show it on the button."""
        self._unit_var.set(value)
        unit_text.configure(text=value)

    def _build_calibration_fields(self, inner, existing, row, expose_text_var):
        """Calibration-point mode: the Expose Unscaled check box, Precision, the Min / Max range,
        the point count with its arrange / swap buttons, and the point table. Returns the next row."""
        self._label(inner, "Expose Unscaled Value").grid(
            row=row, column=0, sticky="w", padx=(8, 4), pady=3
        )
        tk.Checkbutton(
            inner,
            variable=self._expose_unscaled_var,
            textvariable=expose_text_var,
            bg=DARK_BG,
            fg=TEXT_PRI,
            selectcolor=MID_BG,
            activebackground=DARK_BG,
            activeforeground=TEXT_PRI,
            highlightthickness=0,
            relief="flat",
        ).grid(row=row, column=1, sticky="w", padx=(0, 8), pady=3)
        row += 1

        calibration = (existing or {}).get("calibration", {})
        precision_default = calibration.get("precision", (existing or {}).get("precision", 5))
        row = self._row(inner, "Precision", "cal_precision", precision_default, row=row)

        row = self._section(inner, "Calibration Points", row)
        self._add_calibration_range_fields(inner, existing, row)
        row += 1

        row = self._section(inner, "Calibration Points", row)
        self._label(inner, "Point Count (≥2)").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        point_count_entry = self._entry(inner, width=8)
        point_count_entry.configure(textvariable=self._calibration_point_count_var)
        point_count_entry.grid(row=row, column=1, sticky="w", padx=(0, 8), pady=3)
        row += 1

        # Load existing point count if editing.
        if existing:
            existing_points = existing.get("calibration", {}).get("points", [])
            if not existing_points:
                existing_points = existing.get("points", [])
            if existing_points:
                self._calibration_point_count_var.set(len(existing_points))

        self._add_calibration_buttons(inner, row)
        row += 1

        self._calibration_point_frame = tk.Frame(inner, bg=DARK_BG)
        self._calibration_point_frame.grid(row=row, column=0, columnspan=2, sticky="ew", padx=8)
        row += 1
        self._calibration_point_frame.columnconfigure(1, weight=1)
        self._calibration_point_frame.columnconfigure(2, weight=1)
        self._build_calibration_points(existing)
        for key in ("cal_minValue", "cal_maxValue", "cal_minMappedValue", "cal_maxMappedValue"):
            self._vars[key].trace_add("write", lambda *_: self._debounce_calibration_points())
        self._calibration_point_count_var.trace_add("write", lambda *_: self._debounce_calibration_points())
        return row

    def _add_calibration_range_fields(self, inner, existing, row):
        """The Min / Max Value and Min / Max Mapped Value entry fields in a two-by-two grid."""
        range_frame = tk.Frame(inner, bg=DARK_BG)
        range_frame.grid(row=row, column=0, columnspan=2, sticky="ew", padx=8)
        range_frame.columnconfigure(1, weight=1)
        range_frame.columnconfigure(3, weight=1)
        # (grid row, label column, label, variable key, entry padx, saved key, point key, default, from last point)
        range_fields = (
            (0, 0, "Min Value", "cal_minValue", (0, 8), "minValue", "value", "0.0", False),
            (0, 2, "Min Mapped Value", "cal_minMappedValue", (0, 0), "minMappedValue", "mappedValue", "0.0", False),
            (1, 0, "Max Value", "cal_maxValue", (0, 8), "maxValue", "value", "1.0", True),
            (1, 2, "Max Mapped Value", "cal_maxMappedValue", (0, 0), "maxMappedValue", "mappedValue", "1.0", True),
        )
        for grid_row, label_column, label_text, variable_key, entry_padx, saved_key, point_key, default, from_last \
                in range_fields:
            self._label(range_frame, label_text).grid(row=grid_row, column=label_column, sticky="w",
                                                      padx=(0, 4), pady=3)
            field_var = tk.StringVar(value=self._calibration_field_default(
                existing, saved_key, point_key, default, from_last=from_last))
            field_entry = self._entry(range_frame, width=10)
            field_entry.configure(textvariable=field_var)
            field_entry.grid(row=grid_row, column=label_column + 1, sticky="ew", padx=entry_padx, pady=3)
            self._vars[variable_key] = field_var

    def _add_calibration_buttons(self, inner, row):
        """The Arrange Values / Swap Values / Swap Mapped Values buttons."""
        button_row = tk.Frame(inner, bg=DARK_BG)
        button_row.grid(row=row, column=0, columnspan=2, sticky="ew", padx=8, pady=(2, 4))
        button_row.columnconfigure(0, weight=1)
        button_row.columnconfigure(4, weight=1)
        buttons = (
            ("↺  Arrange Values", ACCENT, self._arrange_calibration_points),
            ("⇅  Swap Values", ACCENT2, self._swap_calibration_points),
            ("⇅  Swap Mapped Values", ACCENT2, self._swap_calibration_mapped_points),
        )
        for column, (button_text, button_color, button_command) in enumerate(buttons, start=1):
            tk.Button(
                button_row,
                text=button_text,
                bg=button_color,
                fg=DARK_BG,
                font=FONT_UI,
                relief="flat",
                padx=10,
                pady=3,
                cursor="hand2",
                command=button_command,
            ).grid(row=0, column=column, padx=(0, 6))

    def _capture_scaled_format(self):
        """Keep the currently edited scaled-value representation in memory."""
        if self._scaled_format == "base":
            self._scaled_format_cache["base"] = {
                "baseValue": self._vars.get("baseValue", tk.StringVar(value="0.0")).get(),
                "scale": self._vars.get("scale", tk.StringVar(value="1.0")).get(),
            }
            return

        calibration = {
            "minValue": self._vars.get("cal_minValue", tk.StringVar(value="0.0")).get(),
            "maxValue": self._vars.get("cal_maxValue", tk.StringVar(value="1.0")).get(),
            "minMappedValue": self._vars.get("cal_minMappedValue", tk.StringVar(value="0.0")).get(),
            "maxMappedValue": self._vars.get("cal_maxMappedValue", tk.StringVar(value="1.0")).get(),
            "precision": self._vars.get("cal_precision", tk.StringVar(value="5")).get(),
            "points": [
                {"value": value_var.get(), "mappedValue": mapped_var.get()}
                for value_var, mapped_var in self._calibration_point_vars
            ],
        }
        self._scaled_format_cache["calibration"] = calibration

    def _scaled_entry_for_format(self):
        """Build the dialog seed used when switching the visible format."""
        entry = copy.deepcopy(self._scaled_entry_seed)
        for key in ("id", "device", "name", "description"):
            if key in self._vars:
                value = self._vars[key].get().strip()
                if key == "id":
                    entry["exports"][0]["id"] = value
                else:
                    entry[key] = value
        if "format" in self._vars:
            entry["exports"][0]["format"] = self._vars["format"].get().strip()
        entry["unit"] = self._unit_var.get()
        entry["valueDescription"] = self._vars.get(
            "valueDescription", tk.StringVar(value="")
        ).get()
        entry["exposeunscaledvalue"] = bool(self._expose_unscaled_var.get())

        if self._scaled_format == "base":
            entry.pop("calibration", None)
            entry.update(copy.deepcopy(self._scaled_format_cache["base"]))
        else:
            entry.pop("baseValue", None)
            entry.pop("scale", None)
            entry["calibration"] = copy.deepcopy(self._scaled_format_cache["calibration"])
        return entry

    def _toggle_scaled_format(self):
        """Switch a Scaled Network Value between 'base value / scale' and 'calibration points',
        keeping what was typed, and rebuild the dialog body in the other format."""
        self._capture_scaled_format()
        self._scaled_format = "calibration" if self._scaled_format == "base" else "base"
        entry = self._scaled_entry_for_format()

        self._dialog_outer.destroy()
        self._dialog_buttons.destroy()
        self._vars = {}
        self._calibration_point_vars = []
        self._calibration_rebuild_after = None
        self._build_ui(entry)
        self._auto_fit_dialog_to_content(center_on_parent=False, force_recenter=False)

    @staticmethod
    def _ball_axis_points(existing, axis_key):
        """Calibration points of one 3D Ball axis from the existing entry, or that axis's
        default points."""
        axis_calibration = (existing or {}).get(axis_key)
        if isinstance(axis_calibration, dict):
            points = axis_calibration.get("points", [])
            if isinstance(points, list) and points:
                return points
        return copy.deepcopy(BALL_AXIS_DEFAULTS[axis_key]["points"])

    @staticmethod
    def _ball_axis_precision(existing, axis_key):
        """Precision of one 3D Ball axis from the existing entry, or that axis's default
        precision."""
        axis_calibration = (existing or {}).get(axis_key)
        if isinstance(axis_calibration, dict):
            return axis_calibration.get("precision", BALL_AXIS_DEFAULTS[axis_key]["precision"])
        return BALL_AXIS_DEFAULTS[axis_key]["precision"]

    def _build_ball_axis_fields(self, inner, existing, axis_key, axis_label, row):
        """Fields for one 3D Ball axis: an enabled switch, precision, point count and the
        calibration points. Returns the next free grid row."""
        row = self._section(inner, f"{axis_label} Calibration", row)
        axis_calibration = (existing or {}).get(axis_key) if existing else None
        enabled_default = True if not existing else axis_calibration is not None
        enabled_var = tk.BooleanVar(value=enabled_default)
        self._ball_axis_enabled_vars[axis_key] = enabled_var
        enabled_text_var = tk.StringVar(value="true" if enabled_var.get() else "false")
        enabled_var.trace_add(
            "write",
            lambda *_: enabled_text_var.set("true" if enabled_var.get() else "false")
        )
        self._label(inner, "Enabled").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        tk.Checkbutton(
            inner,
            variable=enabled_var,
            textvariable=enabled_text_var,
            bg=DARK_BG,
            fg=TEXT_PRI,
            selectcolor=MID_BG,
            activebackground=DARK_BG,
            activeforeground=TEXT_PRI,
            highlightthickness=0,
            relief="flat",
        ).grid(row=row, column=1, sticky="w", padx=(0, 8), pady=3)
        row += 1

        points = self._ball_axis_points(existing, axis_key)
        self._ball_axis_point_counts[axis_key] = len(points)
        for index, point in enumerate(points):
            point_label = "Min" if index == 0 else "Max" if index == 1 else f"Point {index + 1}"
            row = self._row(inner, f"{point_label} Value", f"{axis_key}_value_{index}",
                            point.get("value", ""), row=row)
            row = self._row(inner, f"{point_label} Mapped Value", f"{axis_key}_mapped_{index}",
                            point.get("mappedValue", ""), row=row)
        row = self._row(inner, "Precision", f"{axis_key}_precision",
                        self._ball_axis_precision(existing, axis_key), row=row)
        return row

    def _build_ball_fields(self, inner, entry, export, existing, row):
        """3D Ball fields: the X, Y and Z axis sections. Returns the next free grid row."""
        for axis_key, axis_label in (("calibration x", "X"), ("calibration y", "Y"), ("calibration z", "Z")):
            row = self._build_ball_axis_fields(inner, existing, axis_key, axis_label, row)
        return row

    def _build_rotary_fields(self, inner, entry, export, existing, row):
        """Rotary Encoder fields: export format, exported-every-frame, step (argument value)
        and the increment / decrement device and action ids. Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        row = self._row(inner, "Format", "format",
                        export.get("format") or DEFAULT_ROTARY_FORMAT, row=row)
        row = self._bool_dropdown_row(inner, "Exported Every Frame", "isExportedEveryFrame",
                                      export.get("isExportedEveryFrame", False), row=row)
        row = self._section(inner, "Rotary Config", row)
        row = self._row(inner, "Argument Value", "argumentValue",
                        entry.get("argumentValue", 0.025), row=row)
        row = self._section(inner, "Actions", row)
        increment = entry.get("actions", {}).get("increment", {})
        decrement = entry.get("actions", {}).get("decrement", {})
        row = self._row(inner, "Increment Device ID", "inc_deviceId", increment.get("deviceId", ""), row=row)
        row = self._row(inner, "Increment Action ID", "inc_actionId", increment.get("actionId", ""), row=row)
        row = self._row(inner, "Decrement Device ID", "dec_deviceId", decrement.get("deviceId", ""), row=row)
        row = self._row(inner, "Decrement Action ID", "dec_actionId", decrement.get("actionId", ""), row=row)
        return row

    def _build_switch_config(self, inner, entry, existing, row):
        """Switch settings: device id, the default action id shared by the positions, position
        count, argument range and whether each position gets its own action id. Returns the
        next free grid row."""
        row = self._section(inner, "Switch Config", row)
        self._label(inner, "Device ID *").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        device_id_var = tk.StringVar(value=entry.get("deviceId", ""))
        device_id_entry = self._entry(inner)
        device_id_entry.configure(textvariable=device_id_var)
        device_id_entry.grid(row=row, column=1, sticky="ew", padx=(0, 8), pady=3)
        self._vars["deviceId"] = device_id_var
        row += 1

        # Shared Action ID: assigned to every position by default. Each
        # position can override it with its own Action ID in the Positions
        # table below.
        self._label(inner, "Action ID (default)").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        action_id_var = tk.StringVar(value="")
        action_id_entry = self._entry(inner)
        action_id_entry.configure(textvariable=action_id_var)
        action_id_entry.grid(row=row, column=1, sticky="ew", padx=(0, 8), pady=3)
        self._vars["switch_actionId"] = action_id_var
        action_id_var.trace_add("write", lambda *_: self._propagate_switch_action_id())
        row += 1

        # The default Action ID is independent of any single position. Restore
        # it from the editor-only `_switchDefaultActionId` persisted on the
        # entry; when that's absent (a legacy / externally-saved file), derive
        # it from the positions (Position 2 preferred) so the field matches
        # what the main grid shows. Setting it applies to every position;
        # editing a position never writes back. The trace seeds
        # `_switch_action_prev` (init as None) so a restored value becomes the
        # propagation baseline.
        if existing:
            stored_default = existing.get("_switchDefaultActionId", "")
            if stored_default in (None, ""):
                stored_default = _switch_default_action_id(existing)
            if stored_default not in (None, ""):
                action_id_var.set(str(stored_default))

        self._label(inner, "Min Value").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        min_entry = self._entry(inner, width=14)
        min_entry.configure(textvariable=self._min_var)
        min_entry.grid(row=row, column=1, sticky="w", padx=(0, 8), pady=3)
        row += 1

        self._label(inner, "Max Value").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        max_entry = self._entry(inner, width=14)
        max_entry.configure(textvariable=self._max_var)
        max_entry.grid(row=row, column=1, sticky="w", padx=(0, 8), pady=3)
        row += 1

        self._label(inner, "Position Count (≥2)").grid(row=row, column=0, sticky="w", padx=(8, 4), pady=3)
        count_entry = self._entry(inner, width=8)
        count_entry.configure(textvariable=self._position_count_var)
        count_entry.grid(row=row, column=1, sticky="w", padx=(0, 8), pady=3)
        row += 1
        return row

    def _load_switch_bounds(self, existing):
        """Seed Min/Max/Count and the reversed flag from an existing switch's
        stored position values."""
        position_list = existing.get("positions", [])
        if not position_list:
            return
        try:
            first_value = float(position_list[0].get("argumentValue", 0.0))
            last_value = float(position_list[-1].get("argumentValue", 1.0))
        except (ValueError, TypeError):
            first_value, last_value = 0.0, 1.0
        # Keep the Min/Max bounds ascending and record whether the stored values
        # run high→low (a previously swapped switch).
        self._positions_reversed = first_value > last_value
        self._min_var.set(min(first_value, last_value))
        self._max_var.set(max(first_value, last_value))
        self._position_count_var.set(len(position_list))

    def _propagate_switch_action_id(self):
        """Apply the default Action ID to every position field. This is the
        one-way "set all" action: populating/changing the default overwrites
        all per-position values, while editing a position never writes back to
        the default field. No-op unless the default value actually changed, so
        rebuilds/swaps that re-fire the trace don't clobber anything."""
        shared_var = self._vars.get("switch_actionId")
        if shared_var is None:
            return
        new_value = shared_var.get().strip()
        if new_value == getattr(self, "_switch_action_prev", None):
            return
        self._switch_action_prev = new_value
        for _value_var, _name_var, action_var in self._position_vars:
            action_var.set(new_value)

    def _toggle_position_actions(self):
        """Show/hide the per-position Action ID sub-rows and rebuild the table
        so rows re-pack (typed values are preserved across the rebuild)."""
        self._show_position_actions = not self._show_position_actions
        if self._position_action_button is not None:
            self._position_action_button.config(
                text="⚯  Hide Action IDs" if self._show_position_actions else "⚯  Show Action IDs")
        self._build_positions(None)

    def _debounce_positions(self):
        """Rebuild the switch position rows 0.5 s after the user stops typing (count / range
        changes), instead of on every keystroke."""
        if self._position_rebuild_after is not None:
            try:
                self.after_cancel(self._position_rebuild_after)
            except Exception:  # noqa
                pass
        self._position_rebuild_after = self.after(500, lambda: self._build_positions(None))

    def _build_switch_positions(self, inner, existing, row):
        """The switch Positions section: arrange / reverse buttons and the frame that holds one
        row per position. Returns the next free grid row."""
        row = self._section(inner, "Positions", row)
        button_row = tk.Frame(inner, bg=DARK_BG)
        button_row.grid(row=row, column=0, columnspan=2, sticky="ew", padx=8, pady=(2, 4))
        button_row.columnconfigure(0, weight=1)
        button_row.columnconfigure(4, weight=1)
        tk.Button(
            button_row,
            text="↺  Arrange Argument Values",
            bg=ACCENT,
            fg=DARK_BG,
            font=FONT_UI,
            relief="flat",
            padx=10,
            pady=3,
            cursor="hand2",
            command=self._auto_arrange_positions,
        ).grid(row=0, column=1, padx=(0, 6))
        tk.Button(
            button_row,
            text="⇅  Swap Argument Values",
            bg=ACCENT2,
            fg=DARK_BG,
            font=FONT_UI,
            relief="flat",
            padx=10,
            pady=3,
            cursor="hand2",
            command=self._swap_positions,
        ).grid(row=0, column=2, padx=(0, 6))
        tk.Button(
            button_row,
            text="⇅  Swap Position Names",
            bg=ACCENT2,
            fg=DARK_BG,
            font=FONT_UI,
            relief="flat",
            padx=10,
            pady=3,
            cursor="hand2",
            command=self._swap_position_names,
        ).grid(row=0, column=3, padx=(0, 6))
        self._position_action_button = tk.Button(
            button_row,
            text="⚯  Show Action IDs",
            bg=MID_BG,
            fg=TEXT_SEC,
            font=FONT_UI,
            relief="flat",
            padx=10,
            pady=3,
            cursor="hand2",
            command=self._toggle_position_actions,
        )
        self._position_action_button.grid(row=0, column=4, padx=(0, 6))
        row += 1
        self._position_frame = tk.Frame(inner, bg=DARK_BG)
        self._position_frame.grid(row=row, column=0, columnspan=2, sticky="ew", padx=8)
        row += 1
        self._position_frame.columnconfigure(1, weight=1)
        self._build_positions(existing)
        for var in (self._min_var, self._max_var, self._position_count_var):
            var.trace_add("write", lambda *_: self._debounce_positions())
        return row

    def _build_switch_fields(self, inner, entry, export, existing, row):
        """Switch fields: export format, exported-every-frame, switch settings and positions.
        Returns the next free grid row."""
        row = self._section(inner, "Export Format", row)
        row = self._row(inner, "Format", "format",
                        export.get("format") or DEFAULT_SWITCH_FORMAT, row=row)
        row = self._bool_dropdown_row(inner, "Exported Every Frame", "isExportedEveryFrame",
                                      export.get("isExportedEveryFrame", False), row=row)
        row = self._build_switch_config(inner, entry, existing, row)
        if existing:
            self._load_switch_bounds(existing)
        return self._build_switch_positions(inner, existing, row)

    def _build_dialog_buttons(self):
        """The Save Entry and Cancel buttons at the bottom of the dialog."""
        button_row = tk.Frame(self, bg=DARK_BG)
        button_row.pack(fill="x", padx=12, pady=(0, 12))
        self._dialog_buttons = button_row
        tk.Button(button_row, text="✓  Save Entry", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=16, pady=6, cursor="hand2",
                  command=self._save).pack(side="right", padx=(4, 0))
        tk.Button(button_row, text="✕  Cancel", bg=MID_BG, fg=TEXT_SEC, font=FONT_UI,
                  relief="flat", padx=16, pady=6, cursor="hand2",
                  command=self.destroy).pack(side="right")

    def _build_ui(self, existing):
        """Build the scrollable dialog body: the common fields (export id, device, name,
        description) followed by the fields of this function's type."""
        outer = tk.Frame(self, bg=DARK_BG)
        outer.pack(fill="both", expand=True, padx=12, pady=12)
        self._dialog_outer = outer

        canvas = tk.Canvas(outer, bg=DARK_BG, highlightthickness=0)
        scrollbar = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        inner = tk.Frame(canvas, bg=DARK_BG)
        self._dialog_inner = inner
        window_id = canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda event: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda event: canvas.itemconfig(window_id, width=event.width))
        canvas.bind_all("<MouseWheel>",
                        lambda event: canvas.yview_scroll(int(-1 * (event.delta / 120)), "units"))
        inner.columnconfigure(1, weight=1)

        entry = existing or {}
        export = first_export(entry)

        row = self._section(inner, "Core", 0)
        row = self._row(inner, "Export ID(Arg) *", "id", export.get("id", ""), row=row)
        row = self._row(inner, "Device *",    "device", entry.get("device", ""), row=row)
        row = self._row(inner, "Name *",      "name",   entry.get("name", ""), row=row)
        # Default the description to the per-type text when none is set yet.
        default_description = entry.get("description") or DESCRIPTION_BY_TYPE.get(self.helios_type) or ""
        row = self._row(inner, "Description", "description", default_description, row=row)

        # Per-type fields, dispatched by helios type.
        builders = {
            DCS_LEADER + "PushButton":         self._build_pushbutton_fields,
            DCS_LEADER + "Axis":               self._build_axis_fields,
            DCS_LEADER + "NetworkValue":       self._build_network_fields,
            DCS_LEADER + "ScaledNetworkValue": self._build_scaled_fields,
            DCS_LEADER + "FlagValue":          self._build_flag_fields,
            DCS_LEADER + "DrawingValue":       self._build_drawing_fields,
            BALL_ROTATION_TYPE:                self._build_ball_fields,
            DCS_LEADER + "RotaryEncoder":      self._build_rotary_fields,
            DCS_LEADER + "Switch":             self._build_switch_fields,
        }
        builder = builders.get(self.helios_type)
        if builder:
            builder(inner, entry, export, existing, row)

        self._build_dialog_buttons()

    def _read_position_params(self):
        """Parse (count, minimum, maximum) from the position controls, clamping
        the count to at least 2. Returns None if any field doesn't parse."""
        try:
            count = int(self._position_count_var.get())
            minimum = float(self._min_var.get())
            maximum = float(self._max_var.get())
        except (ValueError, tk.TclError):
            return None
        return max(2, count), minimum, maximum

    @staticmethod
    def _position_values(count, minimum, maximum, reverse):
        """Ascending argument values spanning minimum..maximum (the last pinned
        exactly to maximum so float drift can't push it off the bound), reversed
        when the switch has been swapped."""
        delta = ((maximum - minimum) / (count - 1)) if count > 1 else 0
        values = [round(maximum if position == count - 1 else minimum + position * delta, 3)
                  for position in range(count)]
        return values[::-1] if reverse else values

    @staticmethod
    def _position_names(existing, prior_names):
        """Names come from the existing entry on first build, otherwise from
        whatever the user has already typed (captured before the rebuild)."""
        if existing:
            return [position.get("name", "") for position in existing.get("positions", [])]
        return prior_names

    @staticmethod
    def _position_action_ids(existing, prior_actions):
        """Per-position Action IDs, mirroring _position_names: from the
        existing entry on first build, otherwise whatever the user has already
        typed (captured before the rebuild)."""
        if existing:
            return [_as_id_str(position.get("actionId"))
                    for position in existing.get("positions", [])]
        return prior_actions

    def _render_position_row(self, index, arg_value, name0, action0):
        # Each position uses one grid row, or two when its Action ID sub-row
        # is shown (the sub-row sits beneath, offset under the Argument Value).
        """Draw one switch position row (argument value, position name and, when enabled, its
        own action id) and remember its variables."""
        show_action = getattr(self, "_show_position_actions", False)
        row_base = index * 2 + 1 if show_action else index + 1
        value_var = tk.StringVar(value=format_float(arg_value))
        value_entry = self._entry(self._position_frame, width=16)
        value_entry.configure(textvariable=value_var)
        value_entry.grid(row=row_base, column=1, padx=4, pady=2, sticky="ew")

        name_var = tk.StringVar(value=name0)
        name_entry = self._entry(self._position_frame, width=20)
        name_entry.configure(textvariable=name_var)
        name_entry.grid(row=row_base, column=2, padx=4, pady=2, sticky="ew")

        index_label = tk.Label(self._position_frame, text=str(index + 1), bg=DARK_BG, fg=TEXT_SEC,
                               font=FONT_UI)
        index_label.grid(row=row_base, column=0, padx=4, pady=2)

        action_var = tk.StringVar(value=action0)
        if show_action:
            # Action ID sits beneath the position's Argument Value, indented a
            # touch so it reads as belonging to that row.
            action_label = self._label(self._position_frame, "↳ Action ID", sub=True)
            action_label.grid(row=row_base + 1, column=0, padx=(14, 4), pady=(0, 2), sticky="e")
            action_entry = self._entry(self._position_frame, width=12)
            action_entry.configure(textvariable=action_var)
            action_entry.grid(row=row_base + 1, column=1, padx=4, pady=(0, 2), sticky="w")

        self._position_vars.append((value_var, name_var, action_var))

    def _render_position_rows(self, count, values, names, actions, default_action=""):
        """Draw the position table: a header row, then one row per position, pre-filled from
        the given values, names and action ids."""
        headers = ["Pos", "Argument Value", "Position Name"]
        for column_index, header in enumerate(headers):
            tk.Label(self._position_frame, text=header, bg=DARK_BG, fg=ACCENT, font=FONT_HEAD,
                     ).grid(row=0, column=column_index, sticky="w", padx=4, pady=(0, 4))
        for index in range(count):
            name0 = names[index] if index < len(names) else ""
            # Rows without a stored/typed Action ID default to the shared one.
            action0 = actions[index] if index < len(actions) else default_action
            self._render_position_row(index, values[index], name0, action0)

    def _arrange_position_values(self):
        """Arrange button: spread the position values evenly between the argument min and max
        (reversed when the switch is reversed)."""
        params = self._read_position_params()
        if params is None:
            return
        count, minimum, maximum = params
        values = self._position_values(count, minimum, maximum, self._positions_reversed)
        for index, (value_var, _name_var, _action_var) in enumerate(self._position_vars):
            if index < len(values):
                value_var.set(format_float(values[index]))

    def _swap_position_names(self):
        """Reverse the switch's position names while keeping the values in place."""
        reversed_names = [name_var.get() for (_value_var, name_var, _action_var) in self._position_vars][::-1]
        for (_value_var, name_var, _action_var), new_name in zip(self._position_vars, reversed_names):
            name_var.set(new_name)

    def _build_positions(self, existing=None):
        """(Re)build the switch position rows from the current count and range, keeping any
        names and action ids already typed."""
        self._position_rebuild_after = None
        # A debounced rebuild can fire after the dialog has closed; bail out if
        # the frame is gone.
        if not self._position_frame.winfo_exists():
            return
        # Preserve names already typed so a rebuild (count/min/max change, or a
        # value swap) keeps each name anchored to its row; same for Action IDs.
        prior_names = [name_var.get() for (_value_var, name_var, _action_var) in self._position_vars]
        prior_actions = [action_var.get() for (_value_var, _name_var, action_var) in self._position_vars]
        for child in self._position_frame.winfo_children():
            child.destroy()
        self._position_vars = []

        position_params = self._read_position_params()
        if position_params is None:
            return
        count, minimum, maximum = position_params
        values = self._initial_position_values(existing, count, minimum, maximum)
        names = self._position_names(existing, prior_names)
        # Per-position Action IDs come only from the existing entry (first
        # build) or what the user typed (rebuilds). They never fall back to the
        # default field here, so reopening a saved switch shows each position's
        # own stored value without the default overwriting them.
        actions = self._position_action_ids(existing, prior_actions)
        self._render_position_rows(count, values, names, actions)
        self._auto_fit_dialog_to_content()

    def _initial_position_values(self, existing, count, minimum, maximum):
        """The argument value of each position: the saved ones of an entry being edited (the rest
        generated), else all generated - in reverse order when the switch has been swapped."""
        generated_values = self._position_values(count, minimum, maximum, self._positions_reversed)
        if not existing:
            return generated_values
        saved_values = [format_float(position.get("argumentValue", ""))
                        for position in existing.get("positions", [])[:count]]
        return saved_values + generated_values[len(saved_values):]

    def _swap_positions(self):
        """Reverse the switch's positions in place: each argument value carries
        its name and Action ID with it. The reversal is sticky, so it survives
        later count or min/max edits until swapped back."""
        self._positions_reversed = not self._positions_reversed
        rows = [(value_var.get(), name_var.get(), action_var.get())
                for (value_var, name_var, action_var) in self._position_vars][::-1]
        for (value_var, name_var, action_var), (value, name, action) in zip(self._position_vars, rows):
            value_var.set(value)
            name_var.set(name)
            action_var.set(action)

    def _auto_arrange_positions(self):
        """Evenly space the current position values without changing names."""
        self._arrange_position_values()

    @staticmethod
    def _parse_float_or_none(value):
        """A number from text, or None when the text is blank or not a number."""
        try:
            text = str(value).strip()
            if text == "":
                return None
            return float(text)
        except (TypeError, ValueError):
            return None

    @staticmethod
    def _calibration_values(count, minimum, maximum):
        """count evenly spaced calibration values from minimum to maximum (the last one is
        exactly maximum)."""
        delta = ((maximum - minimum) / (count - 1)) if count > 1 else 0
        values = [round(maximum if position == count - 1 else minimum + position * delta, 3)
                  for position in range(count)]
        return values

    @staticmethod
    def _calibration_field_default(existing, key, point_key, default, from_last=False):
        """Default for a calibration setting: the stored setting when present, otherwise taken
        from the first (or last) calibration point."""
        calibration = (existing or {}).get("calibration", {})
        if key in calibration:
            return calibration.get(key, default)
        points = calibration.get("points", [])
        if not points:
            points = (existing or {}).get("points", [])
        if points:
            point = points[-1] if from_last else points[0]
            value = point.get(point_key, default)
            if value not in (None, ""):
                return value
        return default

    def _calibration_range_values(self):
        """The calibration range currently typed in the dialog, with defaults for anything
        blank or invalid."""
        def read(key, default):
            """A calibration range field as a number, or default when blank / invalid."""
            var = self._vars.get(key)
            value = self._parse_float_or_none(var.get()) if var is not None else None
            return value if value is not None else default

        return (
            read("cal_minValue", 0.0),
            read("cal_maxValue", 1.0),
            read("cal_minMappedValue", 0.0),
            read("cal_maxMappedValue", 1.0),
        )

    def _arrange_calibration_points(self):
        """Evenly space both calibration columns using the range fields."""
        count = max(2, len(self._calibration_point_vars))
        minimum, maximum, mapped_minimum, mapped_maximum = self._calibration_range_values()
        values = self._calibration_values(count, minimum, maximum)
        mapped_values = self._calibration_values(count, mapped_minimum, mapped_maximum)
        for index, (value_var, _mapped_var) in enumerate(self._calibration_point_vars):
            if index < len(values):
                value_var.set(format_float(values[index]))
        for index, (_value_var, mapped_var) in enumerate(self._calibration_point_vars):
            if index < len(mapped_values):
                mapped_var.set(format_float(mapped_values[index]))

    def _swap_calibration_points(self):
        """Reverse the Value column while leaving the Mapped Value column in place."""
        reversed_values = [value_var.get() for (value_var, _mapped_var) in self._calibration_point_vars][::-1]
        for (value_var, _mapped_var), new_value in zip(self._calibration_point_vars, reversed_values):
            value_var.set(new_value)

    def _swap_calibration_mapped_points(self):
        """Reverse the Mapped Value column while leaving the Value column in place."""
        reversed_values = [mapped_var.get() for (_value_var, mapped_var) in self._calibration_point_vars][::-1]
        for (_value_var, mapped_var), new_value in zip(self._calibration_point_vars, reversed_values):
            mapped_var.set(new_value)

    def _build_calibration_points(self, existing=None):
        """Build N calibration-point rows (Value / Mapped Value), mirroring the
        dynamic switch positions table. Typed values survive a count change."""
        self._calibration_rebuild_after = None
        # A debounced rebuild can fire after the dialog has closed; bail out if
        # the frame is gone.
        if not self._calibration_point_frame.winfo_exists():
            return
        try:
            count = int(self._calibration_point_count_var.get())
        except (ValueError, tk.TclError):
            return
        count = max(2, count)

        # Capture currently-typed values so they aren't lost when the count changes
        current = [(value_var.get(), mapped_var.get()) for (value_var, mapped_var) in self._calibration_point_vars]

        for child in self._calibration_point_frame.winfo_children():
            child.destroy()
        self._calibration_point_vars = []

        headers = ["Pt", "Value", "Mapped Value"]
        for column_index, header in enumerate(headers):
            tk.Label(self._calibration_point_frame, text=header, bg=DARK_BG, fg=ACCENT, font=FONT_HEAD,
                     ).grid(row=0, column=column_index, sticky="w", padx=4, pady=(0, 4))

        for index, (value_text, mapped_text) in enumerate(self._calibration_point_start_values(existing, count, current)):
            self._add_calibration_point_row(index, value_text, mapped_text)

        self._auto_fit_dialog_to_content()

    def _calibration_point_start_values(self, existing, count, current):
        """[(value, mapped value)] for each of the count rows: the saved points of the entry being
        edited, then what is typed now; for a new entry an even spread over the range fields."""
        if not existing:
            minimum, maximum, mapped_minimum, mapped_maximum = self._calibration_range_values()
            values = self._calibration_values(count, minimum, maximum)
            mapped_values = self._calibration_values(count, mapped_minimum, mapped_maximum)
            return [(format_float(values[index]), format_float(mapped_values[index])) for index in range(count)]
        points = existing.get("calibration", {}).get("points", [])
        if not points:
            points = existing.get("points", [])
        start_values = []
        for index in range(count):
            if index < len(points):
                start_values.append((points[index].get("value", ""), points[index].get("mappedValue", "")))
            elif index < len(current):
                start_values.append(current[index])
            else:
                start_values.append(("", ""))
        return start_values

    def _add_calibration_point_row(self, index, value_text, mapped_text):
        """One row of the calibration table: its number and its two entry fields."""
        frame = self._calibration_point_frame
        index_label = tk.Label(frame, text=str(index + 1), bg=DARK_BG, fg=TEXT_SEC, font=FONT_UI)
        index_label.grid(row=index + 1, column=0, padx=4)

        value_var = tk.StringVar(value=value_text)
        value_entry = self._entry(frame, width=20)
        value_entry.configure(textvariable=value_var)
        value_entry.grid(row=index + 1, column=1, padx=4, pady=2, sticky="ew")

        mapped_var = tk.StringVar(value=mapped_text)
        mapped_entry = self._entry(frame, width=20)
        mapped_entry.configure(textvariable=mapped_var)
        mapped_entry.grid(row=index + 1, column=2, padx=4, pady=2, sticky="ew")

        self._calibration_point_vars.append((value_var, mapped_var))

    @staticmethod
    def _check_id_value(value, label, required):
        """Return an error string for one id field, or None when it's valid.
        Blank is allowed unless the field is required; a non-blank value must be
        a positive integer."""
        parsed = positive_int_or_none(value)
        if parsed is None:
            return f"{label} is required and must be a positive integer." if required else None
        if parsed is False:
            return f"{label} must be a positive integer."
        return None

    def _validate_id_fields(self, values):
        """Ensure every ID field is a positive integer. The Export ID(Arg) is
        required; the rest are optional but must be positive integers when
        filled in. Returns an error string, or None when everything is valid."""
        checks = [("id", "Export ID(Arg)", True)]
        checks += [(key, label, False)
                   for key, label in _OPTIONAL_ID_CHECKS_BY_TYPE.get(self.helios_type, [])]
        for key, label, required in checks:
            error = self._check_id_value(values.get(key, ""), label, required)
            if error:
                return error
        return None

    def _validate_required(self, values):
        """Return an error message for the first missing required text field, or
        None when Export ID(Arg), Device and Name are all present."""
        for key, label in (("id", "Export ID(Arg)"), ("device", "Device"), ("name", "Name")):
            if not values.get(key, ""):
                return f"{label} is required."
        return None

    def _validate_type_specific_fields(self, values):
        """Check the fields only some types have before saving: Push Button push / release values
        must be numbers; every Switch position's action id must be a positive whole number when
        given; a Scaled Network Value needs numeric base value and scale (or valid calibration
        points). Returns the first problem as a message for the user, or None when everything is
        valid."""
        if self.helios_type == DCS_LEADER + "PushButton":
            return self._first_non_number_message(values, (("pushValue", "Push Value"), ("releaseValue", "Release Value")))
        if self.helios_type == DCS_LEADER + "Switch":
            return self._check_switch_action_ids()
        if self.helios_type == DCS_LEADER + "ScaledNetworkValue":
            return self._check_scaled_network_value(values)
        if self.helios_type == BALL_ROTATION_TYPE:
            return self._check_ball_rotation_precisions(values)
        return None

    @staticmethod
    def _first_non_number_message(values, key_and_label_pairs):
        """The message for the first field that is empty or not a number, or None."""
        for key, label in key_and_label_pairs:
            text = values.get(key, "").strip()
            if not text:
                return f"{label} is required and must be a number."
            try:
                float(text)
            except ValueError:
                return f"{label} must be a number."
        return None

    def _check_switch_action_ids(self):
        """Per-position Action IDs are optional but must be positive ints."""
        for index, (_value_var, _name_var, action_var) in enumerate(self._position_vars):
            error = self._check_id_value(action_var.get(), f"Position {index + 1} Action ID", False)
            if error:
                return error
        return None

    def _check_scaled_network_value(self, values):
        """Base Value and Scale must be numbers; with calibration points instead, Precision
        must be a positive whole number."""
        if "baseValue" in self._vars or "scale" in self._vars:
            return self._first_non_number_message(values, (("baseValue", "Base Value"), ("scale", "Scale")))
        text = values.get("cal_precision", "").strip()
        if not text:
            return "Precision is required and must be a positive integer."
        if not text.lstrip("+").isdigit() or int(text) <= 0:
            return "Precision must be a positive integer."
        return None

    def _check_ball_rotation_precisions(self, values):
        """Each enabled axis needs a positive whole-number Precision."""
        for axis_key, axis_label in (("calibration x", "X"), ("calibration y", "Y"), ("calibration z", "Z")):
            enabled_var = self._ball_axis_enabled_vars.get(axis_key)
            if enabled_var is not None and not enabled_var.get():
                continue
            text = values.get(f"{axis_key}_precision", "").strip()
            if not text:
                return f"{axis_label} Precision is required and must be a positive integer."
            if not text.lstrip("+").isdigit() or int(text) <= 0:
                return f"{axis_label} Precision must be a positive integer."
        return None

    def _is_edit_index(self, index):
        """True when `index` is the function currently being edited (so it is
        skipped by the duplicate scans)."""
        return self.edit_index is not None and index == self.edit_index

    @staticmethod
    def _function_uses_id(function, export_id):
        """True when a function has export_id among its Export IDs(Arg)."""
        for export in function.get("exports", []):
            if str(export.get("id", "")).strip() == export_id:
                return True
        return False

    def _find_entry_collisions(self, entry):
        """Every existing function the entry-to-be-saved would collide with, and
        why — matching the Collisions tab rules: a shared Export ID(Arg), a shared
        Device ID + Action ID, or a shared Device + Name (both must match).
        Returns a list of (other_function, [reason, ...])."""
        new_ids = (str(first_export(entry).get("id", "")).strip(),
                   str(get_primary_device_id(entry)).strip(),
                   str(get_primary_action_id(entry)).strip(),
                   str(entry.get("device", "")).strip(),
                   str(entry.get("name", "")).strip())
        collisions = []
        for index, other in enumerate(self.functions):
            if self._is_edit_index(index):
                continue
            reasons = self._collision_reasons(other, *new_ids)
            if reasons:
                collisions.append((other, reasons))
        return collisions

    def _collision_reasons(self, other, new_export, new_device_id, new_action_id, new_device, new_name):
        """Why another function collides with the entry: shared Export ID(Arg), shared
        Device ID + Action ID, or shared Device + Name."""
        reasons = []
        if new_export and self._function_uses_id(other, new_export):
            reasons.append(f"Export ID(Arg) {new_export}")
        if new_device_id and new_action_id \
                and str(get_primary_device_id(other)).strip() == new_device_id \
                and str(get_primary_action_id(other)).strip() == new_action_id:
            reasons.append(
                f"Device ID {new_device_id} + Action ID {new_action_id}")
        if new_name \
                and str(other.get("device", "")).strip() == new_device \
                and str(other.get("name", "")).strip() == new_name:
            reasons.append(f"Device + Name '{new_device} · {new_name}'")
        return reasons

    def _confirm_collisions(self, collisions):
        """Tell the user exactly what this entry collides with (and why) before it
        lands on the Collisions tab; return True to add it anyway."""
        lines = ["Heads up — this entry will be listed on the Collisions tab.",
                 "", "It collides with:"]
        for other, reasons in collisions[:12]:
            other_type = TAB_LABELS.get(other.get("heliosType", ""),
                                        other.get("heliosType", "").split(".")[-1])
            label = " · ".join(part for part in
                               (str(other.get("device", "")).strip(),
                                str(other.get("name", "")).strip()) if part) or "(unnamed)"
            lines.append(f"  • {label} ({other_type}) — shares {'; '.join(reasons)}")
        if len(collisions) > 12:
            lines.append(f"  …and {len(collisions) - 12} more.")
        lines += ["", "Collisions are allowed but flagged for review.",
                  "", "Add this entry anyway?"]
        return messagebox.askyesno("Collision Detected", "\n".join(lines), parent=self)

    def _save_pushbutton(self, entry, values):
        """Copy the Push Button fields from the dialog into the entry (ids as numbers, values
        as formatted floats)."""
        entry["buttons"][0]["deviceId"]     = to_int(values.get("btn_deviceId", ""))
        entry["buttons"][0]["pushId"]       = to_int(values.get("pushId", ""))
        entry["buttons"][0]["releaseId"]    = to_int(values.get("releaseId", ""))
        entry["buttons"][0]["pushValue"]    = format_float(values.get("pushValue", "1.0"))
        entry["buttons"][0]["releaseValue"] = format_float(values.get("releaseValue", "0.0"))

    def _save_axis(self, entry, values):
        """Copy the Axis fields from the dialog into the entry (loop, argument range, set
        action ids)."""
        entry["loop"] = values.get("loop") == "True"
        entry["argumentMin"] = values.get("argumentMin", "")
        entry["argumentMax"] = values.get("argumentMax", "")
        entry["actions"]["set"]["deviceId"] = to_int(values.get("set_deviceId", ""))
        entry["actions"]["set"]["actionId"] = to_int(values.get("set_actionId", ""))

    def _save_network(self, entry, values):
        """Copy the export format from the dialog into the entry (left unchanged when blank)."""
        export_format = values.get("format", "").strip()
        if export_format:
            entry["exports"][0]["format"] = export_format

    def _save_scaled(self, entry, values):
        """Copy the Scaled Network Value fields into the entry, in whichever format (base value
        / scale or calibration points) is active."""
        self._save_network(entry, values)  # identical export-format handling
        self._capture_scaled_format()
        entry["unit"] = self._unit_var.get().strip() or "Numeric"
        entry["valueDescription"] = values.get("valueDescription", "")
        entry["exposeunscaledvalue"] = bool(self._expose_unscaled_var.get())

        if "baseValue" in self._vars or "scale" in self._vars:
            entry["baseValue"] = format_float(values.get("baseValue", "0.0"))
            entry["scale"] = format_float(values.get("scale", "1.0"))
            entry.pop("calibration", None)
            entry.pop("points", None)
            entry.pop("precision", None)
            entry.pop("minValue", None)
            entry.pop("maxValue", None)
            entry.pop("minMappedValue", None)
            entry.pop("maxMappedValue", None)
            entry["_scaledFormatCache"] = copy.deepcopy(self._scaled_format_cache)
            entry["_scaledFormatActive"] = self._scaled_format
            return

        entry["calibration"]["minValue"] = format_float(values.get("cal_minValue", "0.0"))
        entry["calibration"]["maxValue"] = format_float(values.get("cal_maxValue", "1.0"))
        entry["calibration"]["minMappedValue"] = format_float(values.get("cal_minMappedValue", "0.0"))
        entry["calibration"]["maxMappedValue"] = format_float(values.get("cal_maxMappedValue", "1.0"))
        entry["calibration"]["precision"] = int(values.get("cal_precision", "5").strip().lstrip("+"))
        entry["calibration"]["points"] = [
            {"value": value_var.get().strip(), "mappedValue": mapped_var.get().strip()}
            for (value_var, mapped_var) in self._calibration_point_vars
        ]
        entry["_scaledFormatCache"] = copy.deepcopy(self._scaled_format_cache)
        entry["_scaledFormatActive"] = self._scaled_format

    def _save_drawing(self, entry, values):
        """Copy the Drawing Value fields into the entry. aircraftDrawArgument is its own
        editable field (defaulted to the Export ID(Arg) when the dialog opened, but the
        user may have changed it since), so it's saved as entered rather than re-derived."""
        self._save_network(entry, values)  # identical export-format handling
        entry["unit"] = self._unit_var.get().strip() or "Numeric"
        entry["valueDescription"] = values.get("valueDescription", "").strip() or "Number with 0 being closed"
        entry["aircraftDrawArgument"] = to_int(values.get("aircraftDrawArgument", ""))

    def _save_ball(self, entry, values):
        """Copy each enabled 3D Ball axis's precision and calibration points into the entry;
        disabled axes are stored as None."""
        for axis_key, axis_defaults in BALL_AXIS_DEFAULTS.items():
            enabled_var = self._ball_axis_enabled_vars.get(axis_key)
            if enabled_var is not None and not enabled_var.get():
                entry[axis_key] = None
                continue
            point_count = self._ball_axis_point_counts.get(axis_key, len(axis_defaults["points"]))
            entry[axis_key] = {
                "points": [
                    {
                        "value": values.get(f"{axis_key}_value_{index}", ""),
                        "mappedValue": values.get(f"{axis_key}_mapped_{index}", ""),
                    }
                    for index in range(point_count)
                ],
                "precision": int(values.get(f"{axis_key}_precision", str(axis_defaults["precision"])).strip().lstrip("+")),
            }

    def _save_rotary(self, entry, values):
        """Copy the Rotary Encoder fields from the dialog into the entry (step, increment /
        decrement ids)."""
        entry["argumentValue"] = format_float(values.get("argumentValue", "0.025"))
        entry["actions"]["increment"]["deviceId"] = to_int(values.get("inc_deviceId", ""))
        entry["actions"]["increment"]["actionId"] = to_int(values.get("inc_actionId", ""))
        entry["actions"]["decrement"]["deviceId"] = to_int(values.get("dec_deviceId", ""))
        entry["actions"]["decrement"]["actionId"] = to_int(values.get("dec_actionId", ""))

    def _save_switch(self, entry, values):
        """Copy the Switch fields into the entry: device id, the shared default action id, and
        each position's value, name and action id (a blank one inherits the default)."""
        entry["deviceId"] = to_int(values.get("deviceId", ""))
        shared_action = to_int(values.get("switch_actionId", ""))
        # Persist the default in an editor-only field so it survives a
        # save/reopen. Leading-underscore keys are stripped from the saved file.
        entry["_switchDefaultActionId"] = shared_action
        # Each position keeps its own Action ID; a blank one inherits the
        # shared Action ID from the Switch Config section.
        positions = []
        for value_var, name_var, action_var in self._position_vars:
            action_text = action_var.get().strip()
            positions.append({
                "argumentValue": format_float(value_var.get().strip()),
                "name": name_var.get().strip(),
                "actionId": to_int(action_text) if action_text else shared_action,
            })
        entry["positions"] = positions

    def _populate_entry_fields(self, helios_type, entry, values):
        """Fill the type-specific fields of a freshly built entry from the form
        values, dispatched by helios type."""
        saver_name = ENTRY_FIELD_SAVER_NAMES.get(helios_type)
        if saver_name:
            getattr(self, saver_name)(entry, values)
        # Every type with an editable "Format" field shares this same
        # export[0].format save path (NetworkValue/ScaledNetworkValue already
        # set it via their own savers above; this covers the rest).
        export_format = values.get("format", "").strip()
        if export_format:
            entry["exports"][0]["format"] = export_format
        # Shared save path for the Axis/RotaryEncoder/PushButton/Switch
        # "Exported Every Frame" dropdown.
        if "isExportedEveryFrame" in values:
            entry["exports"][0]["isExportedEveryFrame"] = values.get("isExportedEveryFrame") == "True"

    def _save(self):
        """Save Entry button: check required fields and ids (asking about duplicates), build
        the finished entry from the dialog, store it in result and close."""
        values = {key: var.get().strip() for key, var in self._vars.items()}

        # Validate required text fields, then that every ID field is a positive int.
        error = self._validate_required(values)
        if error:
            messagebox.showerror("Missing Field", error, parent=self)
            return
        id_error = self._validate_id_fields(values)
        if id_error:
            messagebox.showerror("Invalid ID", id_error, parent=self)
            return
        type_error = self._validate_type_specific_fields(values)
        if type_error:
            messagebox.showerror("Invalid Value", type_error, parent=self)
            return

        export_id = values.get("id", "")
        device = values.get("device", "")
        name = values.get("name", "")

        helios_type = self.helios_type
        entry = make_blank_entry(helios_type)
        entry["device"] = device
        entry["name"] = name
        entry["description"] = values.get("description", "")
        entry["exports"][0]["id"] = to_int(export_id)
        self._populate_entry_fields(helios_type, entry, values)

        # Alert on anything that would put this entry on the Collisions tab —
        # a shared Export ID(Arg), Device ID + Action ID, or Name — naming each
        # colliding function and the cause. Collisions are allowed, so the user
        # can proceed or cancel.
        collisions = self._find_entry_collisions(entry)
        if collisions and not self._confirm_collisions(collisions):
            return

        self.result = entry
        self.destroy()


# ── Change-type dialog ──────────────────────────────────────────────────────────
class ChangeTypeDialog(tk.Toplevel):
    """Small dialog to pick a new helios type for an existing function.
    Sets self.result to the chosen full helios type string (e.g.
    'DCS.Common.Switch'), or leaves it None on cancel / no change."""
    # Map friendly tab labels back to their full helios type strings.
    LABEL_TO_TYPE = {label: helios_type for helios_type, label in TAB_LABELS.items()}

    def __init__(self, parent, entry, count=1):
        """Build the modal Change Type dialog: shows the selected function(s) and a list of the
        other Helios types to convert to. result stays None unless a new type is confirmed."""
        super().__init__(parent)
        self.transient(parent)
        self.title("Change Helios Type")
        self.configure(bg=DARK_BG)
        self.resizable(False, False)
        self.grab_set()
        self.result = None
        self._entry = entry
        self._count = count

        current_type = entry.get("heliosType", "")
        self._label_var = tk.StringVar(value=TAB_LABELS.get(current_type, current_type))

        outer = tk.Frame(self, bg=DARK_BG)
        outer.pack(fill="both", expand=True, padx=18, pady=16)
        outer.columnconfigure(1, weight=1)

        tk.Label(outer, text="Change Helios Type", bg=DARK_BG, fg=ACCENT,
                 font=FONT_TITLE).grid(row=0, column=0, columnspan=2,
                                       sticky="w", pady=(0, 12))

        name = entry.get("name", "") or "(unnamed)"
        device = entry.get("device", "") or "(no device)"
        export_id = first_export(entry).get("id", "")
        if self._count > 1:
            function_text = f"Functions:  {self._count} selected (showing '{name}')"
        else:
            function_text = f"Function:   {name}"
        tk.Label(outer, text=function_text, bg=DARK_BG, fg=TEXT_PRI,
                 font=FONT_UI).grid(row=1, column=0, columnspan=2, sticky="w")
        tk.Label(outer, text=f"Device:     {device}", bg=DARK_BG, fg=TEXT_SEC,
                 font=FONT_UI).grid(row=2, column=0, columnspan=2, sticky="w")
        tk.Label(outer, text=f"Export ID(Arg):  {export_id}", bg=DARK_BG, fg=TEXT_SEC,
                 font=FONT_UI).grid(row=3, column=0, columnspan=2, sticky="w",
                                    pady=(0, 12))

        tk.Label(outer, text="Current type", bg=DARK_BG, fg=TEXT_SEC,
                 font=FONT_UI).grid(row=4, column=0, sticky="w", pady=3)
        tk.Label(outer, text=TAB_LABELS.get(current_type, current_type), bg=DARK_BG, fg=WARN,
                 font=FONT_MONO).grid(row=4, column=1, sticky="w", padx=(8, 0), pady=3)

        tk.Label(outer, text="New type", bg=DARK_BG, fg=TEXT_SEC,
                 font=FONT_UI).grid(row=5, column=0, sticky="w", pady=3)
        combo = ttk.Combobox(outer, textvariable=self._label_var,
                             values=[TAB_LABELS[helios_type] for helios_type in HELIOS_TYPES],
                             state="readonly", width=26, font=FONT_UI)
        combo.grid(row=5, column=1, sticky="ew", padx=(8, 0), pady=3)

        note = ("Keeps device, name and Export ID(Arg) (plus the device "
                "ID where it maps).\nDescription is reset to the new type's "
                "default. All other type-specific fields reset to the "
                "new type's defaults — open\nthe entry with Edit afterwards to "
                "fill them in.")
        tk.Label(outer, text=note, bg=DARK_BG, fg=TEXT_SEC, font=FONT_UI,
                 justify="left").grid(row=6, column=0, columnspan=2,
                                      sticky="w", pady=(12, 0))

        button_row = tk.Frame(self, bg=DARK_BG)
        button_row.pack(fill="x", padx=18, pady=(0, 14))
        tk.Button(button_row, text="✓  Change Type", bg=ACCENT, fg=DARK_BG,
                  font=FONT_HEAD, relief="flat", padx=16, pady=6, cursor="hand2",
                  command=self._confirm).pack(side="right", padx=(4, 0))
        tk.Button(button_row, text="✕  Cancel", bg=MID_BG, fg=TEXT_SEC, font=FONT_UI,
                  relief="flat", padx=16, pady=6, cursor="hand2",
                  command=self.destroy).pack(side="right")

        self.update_idletasks()
        window_width, window_height = self.winfo_reqwidth(), self.winfo_reqheight()
        position_x, position_y = centered_position_on_parent(parent, window_width, window_height)
        self.geometry(f"{window_width}x{window_height}+{position_x}+{position_y}")

    def _confirm(self):
        """OK button: store the chosen type in result and close; tells the user when the chosen
        type is the one the function already has."""
        new_type = self.LABEL_TO_TYPE.get(self._label_var.get())
        if not new_type:
            self.destroy()
            return
        if new_type == self._entry.get("heliosType", ""):
            messagebox.showinfo("No Change",
                                "That's already this function's type.",
                                parent=self)
            return
        self.result = new_type
        self.destroy()


# ── Column definitions per type ────────────────────────────────────────────────
def get_columns(helios_type):
    """The grid columns shown for a Helios type, as (field id, heading, width): the common
    Export ID / Device / Name / Description columns plus the fields that only that type has."""
    base = [("id", "Export ID(Arg)", 60), ("device", "Device", 100),
            ("name", "Name", 120), ("description", "Description", 180)]
    if helios_type == DCS_LEADER + "PushButton":
        return base + [("btn_deviceId", "Btn DeviceID", 90), ("pushId", "Push ID", 80),
                       ("releaseId", "Release ID", 80)]
    if helios_type == DCS_LEADER + "Axis":
        return base + [("argumentMin", "Arg Min", 70), ("argumentMax", "Arg Max", 70),
                       ("set_deviceId", "Set DevID", 80), ("set_actionId", "Set ActID", 80)]
    if helios_type == DCS_LEADER + "ScaledNetworkValue":
        return base + [("points", "Calibration Points", 130)]
    if helios_type == DCS_LEADER + "DrawingValue":
        return base + [("unit", "Unit", 90), ("valueDescription", "Value Description", 220)]
    if helios_type == BALL_ROTATION_TYPE:
        return base + [("x_points", "X Points", 80), ("y_points", "Y Points", 80),
                       ("z_points", "Z Points", 80)]
    if helios_type == DCS_LEADER + "RotaryEncoder":
        return base + [("inc_deviceId", "Inc DevID", 80), ("inc_actionId", "Inc ActID", 80),
                       ("dec_deviceId", "Dec DevID", 80), ("dec_actionId", "Dec ActID", 80)]
    if helios_type == DCS_LEADER + "Switch":
        return base + [("deviceId", "DeviceID", 80), ("actionId", "Action ID", 80),
                       ("positions", "Positions", 120)]
    return base


def flatten_push_button(entry, flat):
    """Add the Push Button columns (device, push and release ids) to the flat grid row."""
    button = entry.get("buttons", [{}])[0]
    flat["btn_deviceId"] = str(button.get("deviceId", ""))
    flat["pushId"] = str(button.get("pushId", ""))
    flat["releaseId"] = str(button.get("releaseId", ""))


def flatten_axis(entry, flat):
    # Profiles written by Helios or by hand use the "argumentMin" / "argumentMax" keys.
    """Add the Axis columns (argument range, Set device and action) to the flat grid row."""
    flat["argumentMin"] = format_float(entry.get("argumentMin", ""))
    flat["argumentMax"] = format_float(entry.get("argumentMax", ""))
    set_action = entry.get("actions", {}).get("set", {})
    flat["set_deviceId"] = str(set_action.get("deviceId", ""))
    flat["set_actionId"] = str(set_action.get("actionId", ""))


def flatten_scaled_network_value(entry, flat):
    """Add the Scaled Network Value column (calibration point count) to the flat grid row."""
    points = entry.get("calibration", {}).get("points", [])
    flat["points"] = f"{len(points)} points"


def flatten_drawing_value(entry, flat):
    """Add the Drawing Value columns (unit and value description) to the flat grid row."""
    flat["unit"] = entry.get("unit", "")
    flat["valueDescription"] = entry.get("valueDescription", "")


def flatten_ball_rotation(entry, flat):
    """Add the Ball Rotation columns (point count per axis, or Off) to the flat grid row."""
    for axis_key, flat_key in (("calibration x", "x_points"), ("calibration y", "y_points"), ("calibration z", "z_points")):
        axis_calibration = entry.get(axis_key)
        if isinstance(axis_calibration, dict):
            point_count = len(axis_calibration.get("points", []) or [])
            flat[flat_key] = f"{point_count} points"
        else:
            flat[flat_key] = "Off"


def flatten_rotary_encoder(entry, flat):
    """Add the Rotary Encoder columns (increment and decrement device and action) to the flat grid row."""
    increment = entry.get("actions", {}).get("increment", {})
    decrement = entry.get("actions", {}).get("decrement", {})
    flat["inc_deviceId"] = str(increment.get("deviceId", ""))
    flat["inc_actionId"] = str(increment.get("actionId", ""))
    flat["dec_deviceId"] = str(decrement.get("deviceId", ""))
    flat["dec_actionId"] = str(decrement.get("actionId", ""))


def flatten_switch(entry, flat):
    """Add the Switch columns (device, position count and default action id) to the flat grid row."""
    flat["deviceId"] = str(entry.get("deviceId", ""))
    positions = entry.get("positions", [])
    flat["positions"] = f"{len(positions)} positions"
    # The grid shows the switch's default Action ID (falling back to
    # Position 2, then Position 1, only when no default is stored).
    flat["actionId"] = _switch_default_action_id(entry)


def flatten_entry(entry):
    """Turn one profile function into a flat {column: text} dict for its device tab: the common
    columns (Export ID, device, name, description) plus the fields of its type - button ids for
    a Push Button, argument range and set action for an Axis, calibration points for a Scaled
    Network Value, positions for a Switch, and so on. Reads both spellings of the argument keys
    so imported and hand-written profiles display alike. One pass over the function's own data."""
    export = first_export(entry)
    flat = {
        "id":          str(export.get("id", "")),
        "device":      entry.get("device", ""),
        "name":        entry.get("name", ""),
        "description": entry.get("description", ""),
    }
    type_fields = {
        DCS_LEADER + "PushButton": flatten_push_button,
        DCS_LEADER + "Axis": flatten_axis,
        DCS_LEADER + "ScaledNetworkValue": flatten_scaled_network_value,
        DCS_LEADER + "DrawingValue": flatten_drawing_value,
        BALL_ROTATION_TYPE: flatten_ball_rotation,
        DCS_LEADER + "RotaryEncoder": flatten_rotary_encoder,
        DCS_LEADER + "Switch": flatten_switch,
    }
    add_type_fields = type_fields.get(entry.get("heliosType", ""))
    if add_type_fields is not None:
        add_type_fields(entry, flat)
    return flat


# ── Main App ───────────────────────────────────────────────────────────────────
# ════════════════════════════════════════════════════════════════════════════════
# COMMAND TABLE ENGINE  (the DCS Cockpit Command Table Editor, embedded)
# =====================================================================
#
# A Tkinter program that shows and edits a table with the columns
#
#     Type | Arg # | Arg Name | Note | Device | Device # | Command | Command #
#
# and can GENERATE that table from the Lua files of a DCS World aircraft
# (for example  C:\\Program Files\\Eagle Dynamics\\DCS World\\Mods\\aircraft\\<aircraft>).
#
# Where it appears in this program
# --------------------------------
#   The "Table" tab (the last tab) shows the table; the "Table" menu holds
#   Generate... (Ctrl+G), Load..., Save and Save As....  In the tab: double-click a cell
#   to edit, Insert / Delete keys add / remove rows, right-click for Insert / Delete /
#   Function Mapping..., click a column header to sort (sorting by Device # also sorts
#   each device's rows by Command #).
#
# How Generate works (the pipeline, in the order it runs)
# -------------------------------------------------------
#   1. find_aircraft_files()          walk the chosen folder once: every .lua file, every
#                                     clickabledata.lua, every file under an "Input" folder.
#   2. LuaExecutionContext.run_lua_file(clickabledata.lua)
#                                     tokenize + parse each file ONCE into a syntax tree, then
#                                     run it.  dofile() pulls in devices.lua, command_defs.lua,
#                                     draw_args.lua ... exactly like DCS does.  Running the Lua
#                                     (instead of pattern matching) is what gives the numbers:
#                                     counters, reset_counter(), local helper functions,
#                                     loops, metatables, string building, etc.
#   3. TableRowBuilder.build_element_rows()      one or more rows per elements[...] entry
#   4. TableRowBuilder.build_input_binding_rows() rows for key bindings in the Input folder
#                                     (keyboard folder first, then the other Input folders)
#   5. TableRowBuilder.build_definition_file_rows() every arg # / command # defined in an
#                                     arg file (draw_args.lua) or command file (command_defs.lua)
#      TableRowBuilder.build_arg_mention_rows()   args given to variables in the aircraft's
#                                     other .lua files (NAME = f{arg = 404}, NAME.arg = 404 ...)
#   6. fill_devices_of_command_only_rows()  a row with just a command gets the device that
#                                     uses that command, when exactly one device does;
#                                     commands with no device found are still shown
#      remove_duplicate_device_commands()   one row per (Device #, Command #)
#   7. apply_row_corrections()        optional hand corrections from a table_corrections.json
#                                     placed in the aircraft folder (see TABLE_CORRECTIONS_FILE_NAME)
#   8. order_generated_rows()         rows with an Arg # (by Arg #), then the rest by
#                                     Device # / Command #
#   9. find_viewport_calls()          every try_find_assigned_viewport("...") call in the
#                                     folder's .lua files, for the Viewport tab
#      find_flyable_vehicle_names()   the first parameter of every make_flyable(...) call in
#                                     entry.lua, for the Vehicles field of the interface header
#  10. build_source_rows()            where each row's arg, device and command were found,
#                                     for the Source tab (same order as the Reference table)
#      (also: every device name discovered, kept alphabetically for Build Device's Device box)
#
# ======================================================================================
# WHERE TO EDIT TO TEACH THE PROGRAM NEW WAYS OF FINDING THE COMMAND # VALUE
# ======================================================================================
# The Command # of a row is simply the VALUE the Lua code gives the command expression
# (e.g. device_commands.Button_1) after the aircraft's files have been run.  So almost
# everything comes down to "can the interpreter run this Lua?".  In order of how often
# you will need them:
#
#   A. A command file uses a Lua library function the interpreter does not know yet
#      (for example string.gsub, bit.band, math.pow ...)
#        -> add it to LUA_STANDARD_LIBRARY (section "Lua standard library").  Each entry is
#           a small Python function  f(context, argument_values) -> result  .  Return
#           UNKNOWN when it cannot be worked out.  Nothing else has to change.
#
#   B. Commands are grouped in a new way (per device, per panel, nested tables ...)
#        -> TableRowBuilder.device_for_definition_path()  decides which device a command
#           defined at a variable path such as  per_device_commands.RADIO.X  belongs to.
#
#   C. An aircraft stores its command tables under unusual names, so command_defs.lua is
#      not recognised as a command file
#        -> COMMAND_FILE_NAME_WORDS / ARG_FILE_NAME_WORDS (file names that always count), or
#           TableRowBuilder.find_definition_files() (files whose variables the elements use).
#
#   D. The element functions (default_button, multiposition_switch ...) are defined in a
#      file that is not in the chosen folder, so their parameters are guessed
#        -> TableRowBuilder.guess_parameter_roles()  (order: hint, device, command(s), arg(s)).
#           ELEMENT_FIELD_ROLES lists which table fields mean hint/device/command/arg when
#           the function definition IS available (analyze_parameter_roles()).
#
#   E. Key bindings in the Input folder use other field names for commands
#        -> INPUT_BINDING_COMMAND_FIELDS.
#
#   F. A value in the finished table deliberately differs from what the Lua gives
#      (renamed device text, re-numbered command, rows removed / added by hand)
#        -> put the edits in a table_corrections.json in that aircraft's folder (format
#           next to TABLE_CORRECTIONS_FILE_NAME).  Nothing aircraft-specific is written
#           into the program itself.
#
#   G. Very large command files hit a safety limit
#        -> MAX_LOOP_ITERATIONS, MAX_CALL_DEPTH, MAX_EXECUTED_STATEMENTS.
#
# Computational cost (n = number of Lua tokens, r = rows)
# -------------------------------------------------------
#   * every file is tokenized, block-matched and parsed exactly once:   O(n)
#   * running the Lua costs what the Lua itself costs (loops really loop)
#   * repeated metatable __index lookups (some aircraft look every command up this way) are
#     cached until a table or variable changes
#   * elements[...] scan, Input scan: one pass over the tokens:          O(n)
#   * finding arg / command definition files: prefix index               O(definitions)
#   * duplicates: hash set O(r);  overrides: hash lookups O(r);  ordering O(r log r)
# ════════════════════════════════════════════════════════════════════════════════

# ======================================================================================
# Table layout and general settings
# ======================================================================================
TABLE_COLUMNS = ["Type", "Arg #", "Arg Name", "Note", "Device", "Device #", "Command", "Command #"]
TREEVIEW_COLUMN_IDS = [f"column_{position}" for position in range(len(TABLE_COLUMNS))]
TREEVIEW_COLUMN_WIDTHS = [170, 60, 220, 180, 140, 70, 230, 85]
JSON_FILE_TYPES = [("JSON files", "*.json"), ("All files", "*.*")]
# Interface files: a new interface is saved as "DCS.<module>.hif.json" by default.
INTERFACE_FILE_EXTENSION = ".hif.json"
ADDED_FLAG = "_added_since_save"   # private: device added since the last save (stripped on save)
INTERFACE_FILE_PREFIX = "DCS."
HELIOS_FILE_PREFIX = "Helios."
INTERFACE_FILE_PREFIXES = (INTERFACE_FILE_PREFIX, HELIOS_FILE_PREFIX)
INTERFACE_FILE_TYPES = [("Helios interface files", "*.hif *.hif.json *.json"), ("All files", "*.*")]   # Open
INTERFACE_SAVE_FILE_TYPES = [("Helios interface files", "*.hif.json"), ("JSON files", "*.json"), ("All files", "*.*")]                             # Save
# Helios profiles (Monitor Removal).
PROFILE_FILE_TYPES = [("Helios profiles", "*.hpf *.hif"), ("All files", "*.*")]

# Which table column each generated value is written to.  Change the right-hand side to
# rearrange the table (the left-hand side names are used throughout the generator).
GENERATED_VALUE_COLUMN = {
    "element_name": "Note",            # text between elements[ ]
    "arg_name": "Arg Name",            # arg variable name (cockpit_args.RADIO_Power_Switch -> RADIO_Power_Switch)
    "arg_number": "Arg #",             # arg evaluated to a number
    "element_type": "Type",            # function called (default_button) or class value
    "device_name": "Device",           # device name exactly as in the Lua (underscores kept)
    "device_number": "Device #",       # device id from devices.lua
    "command_name": "Command",         # command variable name (device_commands.X -> X)
    "command_number": "Command #",     # command evaluated to a number
}

# True: rows with an Arg # first (sorted by Arg #), then the rest by Device # / Command #.
# False: rows stay in the order they were found in the Lua files.
SORT_GENERATED_ROWS = True

# Clicking this column header also sorts ties by the second column.
SECONDARY_SORT_COLUMN = {"Device #": "Command #"}

# Internal marker on every generated row: the files its arg, device and command were found
# in, as (arg file, device file, command file) - None where it has none.  It becomes the
# row's Source tab entry and is removed before the rows are shown.
SOURCE_FILES_MARKER = "\0source_files"
# The Source tab (Tables ▸ Source): one row per Reference row, in the same order.
SOURCE_COLUMNS = ["Folder Path", "File Name", "Arg #", "Arg Name", "Device", "Command", "Command #"]
SOURCE_LIST_SEPARATOR = "; "          # between files / folders when a row came from several
SOURCE_FILE_PATHS_KEY = "\0file_paths"  # internal: a Source row's full file paths (not shown)
# The Source tab's file view (one file chosen in its drop-down).
SOURCE_FILE_COLUMNS = ["Folder Path", "Variable Name", "Variable Value"]
SOURCE_ALL_FILES_OPTION = "(All files - current table)"

# Internal marker put on rows that come from Input key bindings (removed before display).
INPUT_ROW_MARKER = "\0input_binding"

# Table fields that reveal what a function parameter is, when the function that builds a
# clickable element is available, e.g.  return { hint = hint_, action = {command_}, arg = {arg_} }
ELEMENT_FIELD_ROLES = {"hint": "hint", "device": "device", "action": "command",
                       "stop_action": "command", "arg": "arg"}

# Fields of an Input key binding that hold a command:
#   { down = device_commands.X, up = ..., cockpit_device_id = devices.Y, name = _('...') }
INPUT_BINDING_COMMAND_FIELDS = ("down", "pressed", "up", "action")

# Functions that only translate text, e.g. _("Master Arm") -> "Master Arm".
TRANSLATION_FUNCTION_NAMES = {"_", "gettext", "translate", "tr", "localize", "LOCALIZE"}

# File names that always count as arg files / command files (in addition to files whose
# variables are used by the elements).
ARG_FILE_NAME_WORDS = ("arg",)
# "Arg mentions" (TableRowBuilder.build_arg_mention_rows): every other .lua file of the
# aircraft that mentions one of these words is examined for args given to a variable:
#     NAME = make_lamp{ arg = 404, external_arg = 1404 }   (the 'arg' field, never 'external_arg')
#     NAME = make_lamp(404, 1404)                          (when make_lamp's parameter is named 'arg')
#     NAME = { arg = 404 }        NAME.arg = 404        NAME.arg_number = 404
# Each gives a row: Arg # = the arg value, Arg Name = NAME.
ARG_MENTION_PATTERN = re.compile(r"\b(?:external_)?arg(?:_number)?\b")
ARG_VALUE_FIELD_NAMES = ("arg", "arg_number")       # fields / parameters whose value is an Arg #
COMMAND_FILE_NAME_WORDS = ("command", "cmd")

# Safety limits for running Lua.
MAX_LOOP_ITERATIONS = 10000        # per loop
MAX_CALL_DEPTH = 120               # nested Lua function calls
MAX_EXECUTED_STATEMENTS = 2_000_000  # per clickabledata.lua and everything it includes


# ======================================================================================
# Optional table corrections file  (no aircraft values are built into the program)
# ======================================================================================
# Everything in a generated table comes from the aircraft's own Lua files.  When a
# finished table deliberately differs from what the Lua gives (renamed device text,
# re-numbered commands, rows removed or added by hand), those edits can be kept in a
# JSON file named TABLE_CORRECTIONS_FILE_NAME next to the aircraft, e.g.
#     ...\Mods\aircraft\<aircraft>\table_corrections.json
# Generate finds it during its single folder walk and applies it to that aircraft only.
# A corrections file applies to an aircraft when it sits in the aircraft folder (the
# folder that contains "Cockpit" / "Input"), anywhere inside it, or in a folder above
# it; when several apply, the most specific (deepest) one wins.  File format:
#
#   {
#     "add_rows":    [ {all 8 columns}, ... ],            added next to the Input key
#                                                           bindings unless an identical
#                                                           row was generated already
#     "remove_rows": [ {column: value, ...}, ... ],       every row whose listed columns
#                                                           ALL match is removed
#     "change_rows": [ {"where": {column: value, ...},    every row matching "where"
#                       "set":   {column: value, ...}} ]    gets the "set" values
#   }
#
# Matching uses exact text.  Corrections run after duplicate removal and before sorting,
# so a changed Command # also moves the row to its sorted position.
TABLE_CORRECTIONS_FILE_NAME = "table_corrections.json"
TABLE_CORRECTION_SECTIONS = ("add_rows", "remove_rows", "change_rows")


# ======================================================================================
# Small text / number helpers
# ======================================================================================
def format_number_text(number_value):
    """Text for a number in the table: 3.0 -> "3", 0.5 -> "0.5", None -> ""."""
    if number_value is None:
        return ""
    if isinstance(number_value, float) and number_value.is_integer() and abs(number_value) < 1e15:
        return str(int(number_value))
    return str(number_value)


def parse_number_or_none(text_value):
    """"3016" -> 3016.0 ; "" or "abc" -> None.  Used for ordering rows."""
    try:
        return float(text_value)
    except (TypeError, ValueError):
        return None


# ======================================================================================
# Lua tokenizer
# ======================================================================================
# The source text is split into tokens ONCE per file.  Everything later (parsing, the
# elements[...] scan, the Input scan, parameter-role analysis) works on this list.
class LuaParseError(Exception):
    """Raised when some Lua cannot be parsed; the parser skips a token and carries on."""


class LuaToken:
    """One token.  kind is "name", "number", "string", "operator" or "end_of_file"."""
    __slots__ = ("kind", "value", "start_offset", "end_offset")

    def __init__(self, kind, value, start_offset, end_offset):
        """Store one token: its kind (name / number / string / operator / end_of_file), its
        value and where it starts and ends in the source text."""
        self.kind = kind
        self.value = value
        self.start_offset = start_offset
        self.end_offset = end_offset


LUA_KEYWORDS = {
    "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "goto", "if",
    "in", "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
}
NAME_PATTERN = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
NUMBER_PATTERN = re.compile(
    r"0[xX][0-9a-fA-F]*(?:\.[0-9a-fA-F]*)?(?:[pP][+-]?\d+)?|(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?")
LONG_BRACKET_OPEN_PATTERN = re.compile(r"\[(=*)\[")
MULTI_CHARACTER_OPERATORS = ("...", "..", "==", "~=", "<=", ">=", "//", "::", "<<", ">>")
STRING_ESCAPES = {"n": "\n", "t": "\t", "r": "\r", "a": "\a", "b": "\b", "f": "\f", "v": "\v",
                  "\\": "\\", '"': '"', "'": "'", "\n": "\n", "\r": "\n"}


def convert_lua_number_text(number_text):
    """Lua number literal -> Python int / float ("0x10" -> 16, "1e3" -> 1000.0)."""
    lowered_text = number_text.lower()
    try:
        if lowered_text.startswith("0x"):
            if "." in lowered_text or "p" in lowered_text:
                return float.fromhex(lowered_text)
            return int(lowered_text, 16)
        if "." in lowered_text or "e" in lowered_text:
            return float(lowered_text)
        return int(lowered_text)
    except ValueError:
        return 0


def skip_white_space(source_text, position):
    """The offset of the first character at or after position that is not white space."""
    while position < len(source_text) and source_text[position].isspace():
        position += 1
    return position


def read_hex_escape(source_text, position):
    """\\xNN: (character, offset after it); a bad escape gives the letter x."""
    try:
        return chr(int(source_text[position + 2:position + 4], 16)), position + 4
    except ValueError:
        return "x", position + 2


def read_decimal_escape(source_text, position):
    """\\ddd (up to three digits): (character, offset after it)."""
    digits = re.match(r"[0-9]{1,3}", source_text[position + 1:position + 4]).group()
    return chr(int(digits) % 256), position + 1 + len(digits)


def read_unicode_escape(source_text, position):
    """\\u{XXXX}: (character, offset after it); a bad escape gives the letter u."""
    closing_brace = source_text.find("}", position + 3)
    try:
        return chr(int(source_text[position + 3:closing_brace], 16)), closing_brace + 1
    except (ValueError, OverflowError):
        return "u", position + 2


def read_string_escape(source_text, position):
    """The escape sequence whose backslash is at position: (text it stands for, offset after it)."""
    escape_letter = source_text[position + 1]
    if escape_letter in STRING_ESCAPES:
        return STRING_ESCAPES[escape_letter], position + 2
    if escape_letter == "z":                       # \z skips following white space
        return "", skip_white_space(source_text, position + 2)
    if escape_letter == "x":
        return read_hex_escape(source_text, position)
    if "0" <= escape_letter <= "9":
        return read_decimal_escape(source_text, position)
    if escape_letter == "u" and source_text.startswith("{", position + 2):
        return read_unicode_escape(source_text, position)
    return escape_letter, position + 2


def read_short_string(source_text, opening_offset):
    """Read a '...' or "..." string starting at opening_offset.
    Returns (string value, offset just after the closing quote)."""
    quote_character = source_text[opening_offset]
    source_length = len(source_text)
    position = opening_offset + 1
    collected_characters = []
    while position < source_length:
        character = source_text[position]
        if character == quote_character:
            return "".join(collected_characters), position + 1
        if character == "\n":                      # unterminated: stop at the line end
            break
        if character == "\\" and position + 1 < source_length:
            escaped_text, position = read_string_escape(source_text, position)
            collected_characters.append(escaped_text)
            continue
        collected_characters.append(character)
        position += 1
    return "".join(collected_characters), position


def read_comment(source_text, position, tokens):
    """A -- comment (line or long): the offset after it, or None when none starts here."""
    if not source_text.startswith("--", position):
        return None
    long_bracket = LONG_BRACKET_OPEN_PATTERN.match(source_text, position + 2)
    if long_bracket:
        closing_text = "]" + long_bracket.group(1) + "]"
        closing_offset = source_text.find(closing_text, long_bracket.end())
        return len(source_text) if closing_offset < 0 else closing_offset + len(closing_text)
    line_end = source_text.find("\n", position)
    return len(source_text) if line_end < 0 else line_end + 1


def read_name_token(source_text, position, tokens):
    """A name or keyword: adds its token and returns the offset after it, or None."""
    name_match = NAME_PATTERN.match(source_text, position)
    if not name_match:
        return None
    tokens.append(LuaToken("name", name_match.group(), position, name_match.end()))
    return name_match.end()


def read_number_token(source_text, position, tokens):
    """A number: adds its token and returns the offset after it, or None."""
    character = source_text[position]
    starts_number = "0" <= character <= "9" or (
        character == "." and position + 1 < len(source_text) and "0" <= source_text[position + 1] <= "9")
    if not starts_number:
        return None
    number_match = NUMBER_PATTERN.match(source_text, position)
    tokens.append(LuaToken("number", convert_lua_number_text(number_match.group()), position, number_match.end()))
    return number_match.end()


def read_quoted_string_token(source_text, position, tokens):
    """A '...' or "..." string: adds its token and returns the offset after it, or None."""
    if source_text[position] not in "\"'":
        return None
    string_value, end_position = read_short_string(source_text, position)
    tokens.append(LuaToken("string", string_value, position, end_position))
    return end_position


def read_long_string_token(source_text, position, tokens):
    """A [[long string]]: adds its token and returns the offset after it, or None."""
    if source_text[position] != "[":
        return None
    long_bracket = LONG_BRACKET_OPEN_PATTERN.match(source_text, position)
    if not long_bracket:
        return None
    source_length = len(source_text)
    closing_text = "]" + long_bracket.group(1) + "]"
    closing_offset = source_text.find(closing_text, long_bracket.end())
    end_position = source_length if closing_offset < 0 else closing_offset + len(closing_text)
    string_body = source_text[long_bracket.end():(source_length if closing_offset < 0 else closing_offset)]
    if string_body.startswith("\r\n"):
        string_body = string_body[2:]
    elif string_body.startswith("\n"):
        string_body = string_body[1:]
    tokens.append(LuaToken("string", string_body, position, end_position))
    return end_position


def read_operator_token(source_text, position, tokens):
    """An operator or punctuation mark (the longest match): adds its token and returns the
    offset after it."""
    for operator_text in MULTI_CHARACTER_OPERATORS:
        if source_text.startswith(operator_text, position):
            tokens.append(LuaToken("operator", operator_text, position, position + len(operator_text)))
            return position + len(operator_text)
    tokens.append(LuaToken("operator", source_text[position], position, position + 1))
    return position + 1


TOKEN_READERS = (read_comment, read_name_token, read_number_token, read_quoted_string_token,
                 read_long_string_token, read_operator_token)


def tokenize_lua_source(source_text):
    """Lua source text -> list of LuaToken (comments and white space removed).  O(n)."""
    tokens = []
    position = 0
    source_length = len(source_text)
    while position < source_length:
        if source_text[position].isspace():
            position += 1
            continue
        for token_reader in TOKEN_READERS:           # the first reader that recognises the text wins
            next_position = token_reader(source_text, position, tokens)
            if next_position is not None:
                position = next_position
                break
    tokens.append(LuaToken("end_of_file", None, source_length, source_length))
    return tokens


def name_words_with_index(tokens):
    """[(token index, word)] of every name token (keywords included)."""
    return [(token_index, token.value) for token_index, token in enumerate(tokens) if token.kind == "name"]


def match_lua_blocks(tokens):
    """One pass with a stack over the tokens.  Returns
         block_end_index[opener index]     -> index of its 'end' (or 'until' for repeat)
         if_branch_indices[if index]       -> indices of that if's own 'elseif' / 'else'
    Openers are function / if / do / repeat ('while' and 'for' open with their 'do').
    Knowing every block's end up front makes parsing robust: one bad statement can never
    make the parser lose track of where a function or loop ends.  O(n)."""
    block_end_index = {}
    if_branch_indices = {}
    open_block_stack = []
    for token_index, word in name_words_with_index(tokens):
        if word in ("function", "if", "do", "repeat"):
            open_block_stack.append(token_index)
            if word == "if":
                if_branch_indices[token_index] = []
        elif word in ("elseif", "else"):
            note_if_branch(tokens, token_index, open_block_stack, if_branch_indices)
        elif word in ("end", "until") and open_block_stack:
            block_end_index[open_block_stack.pop()] = token_index
    return block_end_index, if_branch_indices


def note_if_branch(tokens, token_index, open_block_stack, if_branch_indices):
    """An 'elseif' / 'else' belongs to the innermost open block when that is an 'if'."""
    if open_block_stack and tokens[open_block_stack[-1]].value == "if":
        if_branch_indices[open_block_stack[-1]].append(token_index)


# ======================================================================================
# Lua parser: tokens -> syntax tree (built once per file, executed as often as needed)
# ======================================================================================
class SyntaxNode:
    """An expression in the syntax tree.  kind is one of
        number, string, constant, vararg, name, index, call, table, function, unary,
        binary, parenthesized
    Only the attributes that belong to the kind are set, e.g. a "binary" node has
    operator / left / right, an "index" node has table_expression / key_expression."""

    def __init__(self, kind, source_text, start_offset, end_offset,
                 first_token_index, after_last_token_index, **node_fields):
        """Store one expression node: its kind, where it is in the source (characters and
        tokens) and the fields of that kind."""
        self.kind = kind
        self.source_text = source_text
        self.start_offset = start_offset
        self.end_offset = end_offset
        self.first_token_index = first_token_index
        self.after_last_token_index = after_last_token_index
        self.__dict__.update(node_fields)

    @property
    def raw_text(self):
        """The expression as written in the file, white space collapsed."""
        return " ".join(self.source_text[self.start_offset:self.end_offset].split())


class LuaStatement:
    """A statement in the syntax tree.  kind is one of
        local, assign, call, local_function, function, if, while, numeric_for,
        generic_for, repeat, do, return, break"""

    def __init__(self, kind, **statement_fields):
        """Store one statement node: its kind and the fields of that kind."""
        self.kind = kind
        self.__dict__.update(statement_fields)


class FunctionDefinition:
    """A function as written in the source (parsed once).  Running code creates
    LuaFunction closures that point at a FunctionDefinition."""

    def __init__(self, name, parameter_names, body_statements, body_first_token_index,
                 body_end_token_index, tokens, source_text, source_path):
        """Store a parsed function: name, parameters, body, token range and source; also finds
        whether it is a counter() helper. Roles are worked out later, on demand."""
        self.name = name                                  # e.g. "default_button" (None if anonymous)
        self.parameter_names = parameter_names            # e.g. ["hint_", "device_", "command_", "arg_"]
        self.body_statements = body_statements
        self.body_first_token_index = body_first_token_index
        self.body_end_token_index = body_end_token_index  # index of the closing 'end'
        self.tokens = tokens
        self.source_text = source_text
        self.source_path = source_path
        self.parameter_roles = None                       # cache for analyze_parameter_roles()
        self.roles_being_analyzed = False
        self.counter_variable_name = find_counter_variable(self)  # "count" for counter()-style functions
        self.first_closure_scope = None                   # where it was first defined at run time
        self.return_classes = None                        # cache for analyze_return_classes()
        self.return_classes_being_analyzed = False


def is_counter_increment(five_tokens):
    """True for the token pattern   v = v + 1   (or -)."""
    target, equals, source, operator, amount = five_tokens
    return (target.kind == "name" and equals.kind == "operator" and equals.value == "="
            and source.kind == "name" and source.value == target.value
            and operator.kind == "operator" and operator.value in ("+", "-") and amount.kind == "number")


def returns_variable_after(body_tokens, first_position, variable_name):
    """True when   return <variable_name>   appears in body_tokens from first_position on."""
    return any(body_tokens[position].kind == "name" and body_tokens[position].value == "return"
               and body_tokens[position + 1].kind == "name" and body_tokens[position + 1].value == variable_name
               for position in range(first_position, len(body_tokens) - 1))


def find_counter_variable(function_definition):
    """If a function has no parameters and looks like   v = v + 1 ... return v
    (the usual DCS counter()), return v.  Such variables are helper counters, never
    commands or args, so they are left out of the table."""
    if function_definition.parameter_names:
        return None
    body_tokens = function_definition.tokens[function_definition.body_first_token_index:
                                             function_definition.body_end_token_index]
    for position in range(len(body_tokens) - 4):
        if not is_counter_increment(body_tokens[position:position + 5]):
            continue
        counter_name = body_tokens[position].value
        if returns_variable_after(body_tokens, position + 5, counter_name):
            return counter_name
    return None


# Binary operator priorities (left, right) exactly as in the Lua reference parser.
BINARY_OPERATOR_PRIORITY = {
    "or": (1, 1), "and": (2, 2),
    "<": (3, 3), ">": (3, 3), "<=": (3, 3), ">=": (3, 3), "~=": (3, 3), "==": (3, 3),
    "|": (4, 4), "~": (5, 5), "&": (6, 6), "<<": (7, 7), ">>": (7, 7),
    "..": (9, 8), "+": (10, 10), "-": (10, 10),
    "*": (11, 11), "/": (11, 11), "//": (11, 11), "%": (11, 11), "^": (14, 13),
}
UNARY_OPERATOR_PRIORITY = 12
BLOCK_CLOSING_WORDS = ("end", "else", "elseif", "until")


class LuaSyntaxParser:
    """Recursive-descent parser for one file.  parse_chunk() returns the file's statements;
    parse_expression_at(token_index) is used by the scanners to read one expression."""

    def __init__(self, tokens, source_text, source_path, block_end_index, if_branch_indices,
                 function_registry):
        """Prepare to parse one file's tokens; block_end_index / if_branch_indices come from
        match_lua_blocks, and every function parsed is added to function_registry."""
        self.tokens = tokens
        self.source_text = source_text
        self.source_path = source_path
        self.block_end_index = block_end_index
        self.if_branch_indices = if_branch_indices
        self.function_registry = function_registry   # every FunctionDefinition parsed is added here
        self.position = 0
        self.last_token_index = len(tokens) - 1

    # ---------------------------------------------------------------- token helpers
    def current_token(self):
        """The token at the read position (the end-of-file token once past the end)."""
        return self.tokens[min(self.position, self.last_token_index)]

    def token_at_offset(self, offset=0):
        """The token offset places after the read position (clamped to end of file)."""
        return self.tokens[min(self.position + offset, self.last_token_index)]

    def token_is(self, expected_value, offset=0):
        """True when the token at offset is the name or operator expected_value."""
        token = self.token_at_offset(offset)
        return token.kind in ("name", "operator") and token.value == expected_value

    def expect(self, expected_value):
        """Step over expected_value, or raise LuaParseError when something else is there."""
        if not self.token_is(expected_value):
            raise LuaParseError(f"expected '{expected_value}'")
        self.position += 1

    def read_name(self):
        """Read a variable / field name (not a keyword) and step past it."""
        token = self.current_token()
        if token.kind != "name" or token.value in LUA_KEYWORDS:
            raise LuaParseError("expected a name")
        self.position += 1
        return token.value

    def make_node(self, kind, first_token_index, **node_fields):
        """Create an expression node that starts at first_token_index and ends just before the
        read position."""
        last_token = self.tokens[self.position - 1] if self.position > first_token_index else self.tokens[first_token_index]
        return SyntaxNode(kind, self.source_text, self.tokens[first_token_index].start_offset,
                          last_token.end_offset, first_token_index, self.position, **node_fields)

    # ---------------------------------------------------------------- statements
    def parse_chunk(self):
        """Parse a whole file: statement after statement until the end of the tokens. Returns the
        file's top-level statements (the syntax tree run by execute_block)."""
        return self.parse_block(self.last_token_index)

    def parse_block(self, stop_token_index):
        """Statements up to (not including) stop_token_index.  A statement that cannot be
        parsed is skipped one token at a time, like the original DCS-tolerant behaviour."""
        statements = []
        while self.position < stop_token_index and self.current_token().kind != "end_of_file":
            statement_start = self.position
            try:
                statement = self.parse_statement(stop_token_index)
                if statement is not None:
                    statements.append(statement)
            except (LuaParseError, RecursionError):
                self.position = statement_start + 1
            if self.position <= statement_start:
                self.position = statement_start + 1
        return statements

    def block_end_for(self, opener_index):
        """Index of the 'end' / 'until' that closes the block opened at opener_index (from the
        block map)."""
        end_index = self.block_end_index.get(opener_index)
        if end_index is None:
            raise LuaParseError("block without 'end'")
        return end_index

    def parse_statement(self, stop_token_index):
        """Parse one statement at the read position: local / function / if / while / do / for /
        repeat / return / break / goto, an assignment or a call. Returns None for things
        that do nothing (';', labels)."""
        token = self.current_token()
        if self.token_is(";"):
            self.position += 1
            return None
        if self.token_is("::"):                                    # label: ignored
            self.position += 1
            self.read_name()
            self.expect("::")
            return None
        if token.kind == "name" and token.value in self.KEYWORD_STATEMENT_PARSERS:
            keyword_parser = getattr(self, self.KEYWORD_STATEMENT_PARSERS[token.value])
            return keyword_parser(self.position, stop_token_index)
        return self.parse_assignment_or_call()

    KEYWORD_STATEMENT_PARSERS = {
        "local": "parse_local_statement", "function": "parse_function_statement",
        "if": "parse_if_keyword_statement", "while": "parse_while_statement",
        "do": "parse_do_statement", "for": "parse_for_keyword_statement",
        "repeat": "parse_repeat_statement", "return": "parse_return_statement",
        "break": "parse_break_statement", "goto": "parse_goto_statement",
    }

    def parse_local_statement(self, statement_index, stop_token_index):
        """local function name ... end   or   local a, b = values."""
        self.position += 1
        if self.token_is("function"):
            function_keyword_index = self.position
            self.position += 1
            function_name = self.read_name()
            definition = self.parse_function_body(function_name, False, function_keyword_index)
            return LuaStatement("local_function", name=function_name, definition=definition)
        target_nodes = [self.parse_local_name()]
        while self.token_is(","):
            self.position += 1
            target_nodes.append(self.parse_local_name())
        value_nodes = []
        if self.token_is("="):
            self.position += 1
            value_nodes = self.parse_expression_list()
        return LuaStatement("local", targets=target_nodes, values=value_nodes)

    def parse_function_statement(self, statement_index, stop_token_index):
        """function a.b.c(...) ... end   or   function a.b:method(...) ... end."""
        self.position += 1
        name_parts, is_method = [self.read_name()], False
        while self.token_is("."):
            self.position += 1
            name_parts.append(self.read_name())
        if self.token_is(":"):
            self.position += 1
            name_parts.append(self.read_name())
            is_method = True
        definition = self.parse_function_body(".".join(name_parts), is_method, statement_index)
        return LuaStatement("function", name_parts=name_parts, definition=definition)

    def parse_if_keyword_statement(self, statement_index, stop_token_index):
        """Parse an if statement (entry of the keyword dispatch table)."""
        return self.parse_if_statement(statement_index)

    def parse_while_statement(self, statement_index, stop_token_index):
        """while condition do ... end."""
        self.position += 1
        condition = self.parse_expression()
        do_index = self.position
        self.expect("do")
        end_index = self.block_end_for(do_index)
        body = self.parse_block(end_index)
        self.position = end_index + 1
        return LuaStatement("while", condition=condition, body=body)

    def parse_do_statement(self, statement_index, stop_token_index):
        """do ... end."""
        end_index = self.block_end_for(statement_index)
        self.position += 1
        body = self.parse_block(end_index)
        self.position = end_index + 1
        return LuaStatement("do", body=body)

    def parse_for_keyword_statement(self, statement_index, stop_token_index):
        """Parse a for statement (entry of the keyword dispatch table)."""
        return self.parse_for_statement()

    def parse_repeat_statement(self, statement_index, stop_token_index):
        """repeat ... until condition."""
        until_index = self.block_end_for(statement_index)
        self.position += 1
        body = self.parse_block(until_index)
        self.position = until_index + 1
        condition = self.parse_expression()
        return LuaStatement("repeat", body=body, condition=condition)

    def parse_return_statement(self, statement_index, stop_token_index):
        """return [values]."""
        self.position += 1
        value_nodes = []
        next_token = self.current_token()
        if not (next_token.kind == "end_of_file" or self.position >= stop_token_index or self.token_is(";")
                or (next_token.kind == "name" and next_token.value in BLOCK_CLOSING_WORDS)):
            value_nodes = self.parse_expression_list()
        return LuaStatement("return", values=value_nodes)

    def parse_break_statement(self, statement_index, stop_token_index):
        """Parse a break statement (entry of the keyword dispatch table)."""
        self.position += 1
        return LuaStatement("break")

    def parse_goto_statement(self, statement_index, stop_token_index):
        """goto label: ignored."""
        self.position += 1
        self.read_name()
        return None

    def parse_assignment_or_call(self):
        """a, b = values   or a call used as a statement."""
        first_expression = self.parse_suffixed_expression()
        if self.token_is("=") or self.token_is(","):
            target_nodes = [first_expression]
            while self.token_is(","):
                self.position += 1
                target_nodes.append(self.parse_suffixed_expression())
            self.expect("=")
            return LuaStatement("assign", targets=target_nodes, values=self.parse_expression_list())
        if first_expression.kind == "call":
            return LuaStatement("call", expression=first_expression)
        raise LuaParseError("unexpected expression")

    def parse_local_name(self):
        """One name of a local declaration (a Lua 5.4 <const> / <close> attribute is skipped)."""
        name_token_index = self.position
        variable_name = self.read_name()
        name_node = self.make_node("name", name_token_index, name=variable_name)
        if self.token_is("<"):                        # Lua 5.4:  local x <const> = ...
            self.position += 1
            self.read_name()
            self.expect(">")
        return name_node

    def parse_if_statement(self, if_index):
        """Parse if / elseif / else: each branch's condition (None for else) and its
        statements, using the block map for where each branch ends."""
        end_index = self.block_end_for(if_index)
        branch_boundaries = self.if_branch_indices.get(if_index, []) + [end_index]
        branches = []                                   # [(condition or None for else, statements)]
        self.position = if_index + 1
        condition = self.parse_expression()
        self.expect("then")
        for boundary_index in branch_boundaries:
            branches.append((condition, self.parse_block(boundary_index)))
            self.position = boundary_index
            boundary_word = self.tokens[boundary_index].value
            if boundary_word == "elseif":
                self.position += 1
                condition = self.parse_expression()
                self.expect("then")
            elif boundary_word == "else":
                self.position += 1
                condition = None
        self.position = end_index + 1
        return LuaStatement("if", branches=branches)

    def parse_for_statement(self):
        """Parse a numeric for (for i = a, b, step) or a generic for (for k, v in pairs(t))."""
        self.position += 1
        variable_names = [self.read_name()]
        if self.token_is("="):                           # for i = start, stop [, step] do
            self.position += 1
            bound_nodes = self.parse_expression_list()
            do_index = self.position
            self.expect("do")
            end_index = self.block_end_for(do_index)
            body = self.parse_block(end_index)
            self.position = end_index + 1
            return LuaStatement("numeric_for", variable_name=variable_names[0],
                                start_expression=bound_nodes[0],
                                stop_expression=bound_nodes[1] if len(bound_nodes) > 1 else None,
                                step_expression=bound_nodes[2] if len(bound_nodes) > 2 else None,
                                body=body)
        while self.token_is(","):                        # for k, v in pairs(t) do
            self.position += 1
            variable_names.append(self.read_name())
        self.expect("in")
        iterator_nodes = self.parse_expression_list()
        do_index = self.position
        self.expect("do")
        end_index = self.block_end_for(do_index)
        body = self.parse_block(end_index)
        self.position = end_index + 1
        return LuaStatement("generic_for", variable_names=variable_names, iterator_expressions=iterator_nodes,
                            body=body)

    def parse_function_body(self, function_name, is_method, function_keyword_index):
        """Parses '(parameters) body end'.  The end is taken from the block map."""
        end_index = self.block_end_for(function_keyword_index)
        self.expect("(")
        parameter_names = ["self"] if is_method else []
        while not self.token_is(")"):
            if self.token_is("..."):
                self.position += 1
                parameter_names.append("...")
            else:
                parameter_names.append(self.read_name())
            if self.token_is(","):
                self.position += 1
            elif not self.token_is(")"):
                raise LuaParseError("bad parameter list")
        self.position += 1
        body_first_token_index = self.position
        body_statements = self.parse_block(end_index)
        self.position = end_index + 1
        definition = FunctionDefinition(function_name, parameter_names, body_statements,
                                        body_first_token_index, end_index, self.tokens,
                                        self.source_text, self.source_path)
        self.function_registry.append(definition)
        return definition

    # ---------------------------------------------------------------- expressions
    def parse_expression_at(self, token_index):
        """Read one expression starting at token_index (used by the table scanners)."""
        self.position = token_index
        return self.parse_expression()

    def parse_expression(self, priority_limit=0):
        """Parse an expression with operator priorities (precedence climbing): unary operators,
        operands, then binary operators stronger than priority_limit."""
        first_token_index = self.position
        if self.token_is("not") or self.token_is("-") or self.token_is("#") or self.token_is("~"):
            operator = self.current_token().value
            self.position += 1
            operand = self.parse_expression(UNARY_OPERATOR_PRIORITY)
            left_node = self.make_node("unary", first_token_index, operator=operator, operand=operand)
        else:
            left_node = self.parse_simple_expression()
        while True:
            token = self.current_token()
            if (token.kind in ("name", "operator") and token.value in BINARY_OPERATOR_PRIORITY
                    and BINARY_OPERATOR_PRIORITY[token.value][0] > priority_limit):
                self.position += 1
                right_node = self.parse_expression(BINARY_OPERATOR_PRIORITY[token.value][1])
                left_node = self.make_node("binary", first_token_index, operator=token.value,
                                           left=left_node, right=right_node)
            else:
                return left_node

    def parse_expression_list(self):
        """Parse expressions separated by commas (the right-hand side of an assignment, return
        values, call arguments) and return them in order."""
        expressions = [self.parse_expression()]
        while self.token_is(","):
            self.position += 1
            expressions.append(self.parse_expression())
        return expressions

    def parse_simple_expression(self):
        """Parse an operand: number, string, nil / true / false, '...', a table constructor, a
        function expression or a name / call / index chain."""
        token, first_token_index = self.current_token(), self.position
        if token.kind == "number":
            self.position += 1
            return self.make_node("number", first_token_index, value=token.value)
        if token.kind == "string":
            self.position += 1
            return self.make_node("string", first_token_index, value=token.value)
        if token.kind == "name" and token.value in ("nil", "true", "false"):
            self.position += 1
            return self.make_node("constant", first_token_index,
                                  value={"nil": None, "true": True, "false": False}[token.value])
        if self.token_is("..."):
            self.position += 1
            return self.make_node("vararg", first_token_index)
        if self.token_is("{"):
            return self.parse_table_constructor()
        if self.token_is("function"):
            self.position += 1
            definition = self.parse_function_body(None, False, first_token_index)
            return self.make_node("function", first_token_index, definition=definition)
        return self.parse_suffixed_expression()

    def parse_primary_expression(self):
        """The start of a name / call / index chain: a variable name, or an expression in
        parentheses. parse_simple_expression then adds any .field, [key], :method() and (...)
        suffixes."""
        token, first_token_index = self.current_token(), self.position
        if token.kind == "name" and token.value not in LUA_KEYWORDS:
            self.position += 1
            return self.make_node("name", first_token_index, name=token.value)
        if self.token_is("("):
            self.position += 1
            inner_expression = self.parse_expression()
            self.expect(")")
            return self.make_node("parenthesized", first_token_index, inner=inner_expression)
        raise LuaParseError("unexpected symbol")

    def parse_suffixed_expression(self):
        """name / (expr) followed by any number of  .key  [key]  :method(args)  (args)"""
        first_token_index = self.position
        expression = self.parse_primary_expression()
        while True:
            if self.token_is("."):
                self.position += 1
                key_token_index = self.position
                key_name = self.read_name()
                key_token = self.tokens[key_token_index]
                key_node = SyntaxNode("string", self.source_text, key_token.start_offset, key_token.end_offset,
                                      key_token_index, key_token_index + 1, value=key_name)
                expression = self.make_node("index", first_token_index, table_expression=expression,
                                            key_expression=key_node, key_written_as_name=True)
            elif self.token_is("["):
                self.position += 1
                key_node = self.parse_expression()
                self.expect("]")
                expression = self.make_node("index", first_token_index, table_expression=expression,
                                            key_expression=key_node, key_written_as_name=False)
            elif self.token_is(":"):
                self.position += 1
                method_name = self.read_name()
                expression = self.make_node("call", first_token_index, function_expression=expression,
                                            method_name=method_name, arguments=self.parse_call_arguments())
            elif self.token_is("(") or self.token_is("{") or self.current_token().kind == "string":
                expression = self.make_node("call", first_token_index, function_expression=expression,
                                            method_name=None, arguments=self.parse_call_arguments())
            else:
                return expression

    def parse_call_arguments(self):
        """Call arguments: (a, b, ...), a single table constructor, or a single string."""
        if self.token_is("("):
            self.position += 1
            argument_nodes = [] if self.token_is(")") else self.parse_expression_list()
            self.expect(")")
            return argument_nodes
        if self.token_is("{"):
            return [self.parse_table_constructor()]
        if self.current_token().kind == "string":
            string_token_index = self.position
            self.position += 1
            return [self.make_node("string", string_token_index, value=self.tokens[string_token_index].value)]
        raise LuaParseError("expected call arguments")

    def parse_table_constructor(self):
        """{ value, name = value, [key] = value, ... }  ->  node.fields = [(key node or None, value node)]
        node.name_keyed_fields holds the keys written as  name = value  (used for roles)."""
        first_token_index = self.position
        self.expect("{")
        fields = []
        name_keyed_field_positions = []
        while not self.token_is("}"):
            if self.token_is("["):
                self.position += 1
                key_node = self.parse_expression()
                self.expect("]")
                self.expect("=")
                fields.append((key_node, self.parse_expression()))
            elif (self.current_token().kind == "name" and self.current_token().value not in LUA_KEYWORDS
                  and self.token_is("=", 1)):
                key_token_index = self.position
                key_token = self.tokens[key_token_index]
                self.position += 2
                key_node = SyntaxNode("string", self.source_text, key_token.start_offset, key_token.end_offset,
                                      key_token_index, key_token_index + 1, value=key_token.value)
                name_keyed_field_positions.append(len(fields))
                fields.append((key_node, self.parse_expression()))
            else:
                fields.append((None, self.parse_expression()))
            if self.token_is(",") or self.token_is(";"):
                self.position += 1
            elif not self.token_is("}"):
                raise LuaParseError("expected '}'")
        self.position += 1
        return self.make_node("table", first_token_index, fields=fields,
                              name_keyed_field_positions=name_keyed_field_positions)


# ======================================================================================
# Lua values while running
# ======================================================================================
#   Lua nil      -> Python None          Lua boolean -> bool       Lua number -> int / float
#   Lua string   -> str                  Lua table   -> LuaTable   Lua function -> LuaFunction
#   library function -> BuiltinFunction
#   UNKNOWN      -> a value the program cannot know (DCS engine functions, missing files ...)
class UnknownValue:
    """Type of UNKNOWN, the marker for a value the interpreter cannot work out."""
    def __repr__(self):
        """How UNKNOWN prints in messages and while debugging: <unknown>. UNKNOWN is the
        interpreter's marker for a value it cannot work out (DCS engine functions, missing
        files)."""
        return "<unknown>"


UNKNOWN = UnknownValue()


class LuaTable(dict):
    """A Lua table: a dict plus an optional metatable.
    shadowed_entries keeps values that a repeated key overwrote inside one table
    constructor ({ A = 1, A = 2 }): Lua keeps the last, but both numbers were handed out,
    and the finished tables list both."""
    __slots__ = ("metatable", "shadowed_entries", "key_order_cache")

    def __init__(self, *dict_arguments, **dict_keywords):
        """An empty table (dict arguments are accepted) without a metatable."""
        super().__init__(*dict_arguments, **dict_keywords)
        self.metatable = None
        self.shadowed_entries = None
        self.key_order_cache = None          # (keys in order, key -> position) for next(); see key_after

    def key_after(self, previous_key):
        """The key that follows previous_key in this table's order (the first key for nil),
        None at the end or for an unknown key - what Lua's next() walks.  The key order and
        each key's position are kept and rebuilt only when the table's size changed or an
        unknown key is asked for, so walking a whole table costs O(n), not O(n^2)."""
        cache = self.key_order_cache
        if cache is None or len(cache[0]) != len(self) or (previous_key is not None and previous_key not in cache[1]):
            ordered_keys = list(self.keys())
            cache = (ordered_keys, {key: position for position, key in enumerate(ordered_keys)})
            self.key_order_cache = cache
        ordered_keys, position_of_key = cache
        if previous_key is None:
            return ordered_keys[0] if ordered_keys else None
        key_position = position_of_key.get(previous_key)
        if key_position is None or key_position + 1 >= len(ordered_keys):
            return None
        return ordered_keys[key_position + 1]

    __hash__ = object.__hash__          # tables are compared and hashed by identity, like Lua
    __eq__ = object.__eq__


class BuiltinFunction:
    """A Lua library function implemented in Python:  python_function(context, argument_values)."""
    __slots__ = ("name", "python_function")

    def __init__(self, name, python_function):
        """Wrap a Python function as a Lua library function called name."""
        self.name = name
        self.python_function = python_function

    def __repr__(self):
        """How a library function prints in messages and while debugging: <builtin name>."""
        return f"<builtin {self.name}>"


class LuaFunction:
    """A closure: the parsed definition plus the scope it was created in."""
    __slots__ = ("definition", "captured_scope")

    def __init__(self, definition, captured_scope):
        """A closure: the function's definition plus the scope it was created in."""
        self.definition = definition
        self.captured_scope = captured_scope


class VariableScope:
    """One level of local variables: a file, a function call, a block or one loop pass."""
    __slots__ = ("variables", "parent_scope", "variable_arguments", "is_function_scope")

    def __init__(self, parent_scope=None, variable_arguments=None, is_function_scope=False):
        """An empty scope inside parent_scope; variable_arguments holds '...' for a function
        called with extra values."""
        self.variables = {}
        self.parent_scope = parent_scope
        self.variable_arguments = variable_arguments   # tuple for a function called with '...'
        self.is_function_scope = is_function_scope


class PairsIteration:
    """What pairs() / ipairs() return; a generic for loop walks through its items."""
    __slots__ = ("items",)

    def __init__(self, items):
        """The (key, value) pairs a generic for loop will walk through."""
        self.items = items


class ReturnSignal(Exception):
    """Raised by 'return' to leave a function (or a file run by dofile)."""

    def __init__(self, returned_values):
        """Carry the values of a 'return' up to the function (or file) being left."""
        super().__init__()
        self.returned_values = returned_values


class BreakSignal(Exception):
    """Raised by 'break' to leave the innermost loop."""


def is_lua_number(value):
    """True for a Lua number: a Python int or float, but not a bool (Python treats True as 1, Lua
    does not)."""
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def is_lua_truthy(value):
    """Lua truth: everything except nil (None) and false counts as true."""
    return value is not None and value is not False


def normalise_table_key(key):
    """Make a key usable as a dict key the way Lua uses it: Lua treats 3.0 and 3 as the same table
    key, so whole-number floats become ints. Other keys are returned unchanged."""
    if isinstance(key, float) and key.is_integer():
        return int(key)
    return key


def lua_value_to_text(value):
    """tostring() for strings and numbers (Lua 5.1 prints 3.0 as "3")."""
    if isinstance(value, str):
        return value
    if isinstance(value, float):
        return str(int(value)) if value.is_integer() else "%.14g" % value
    return str(value)


def lua_table_length(table_value):
    """Lua's # operator on a table: the count of consecutive integer keys 1, 2, 3 ... (the array
    part). Stops at the first missing key, as a Lua border does."""
    length = 0
    while (length + 1) in table_value:
        length += 1
    return length


def lua_type_name(value):
    """Lua's type() of a value: nil, boolean, number, string, table or function (UNKNOWN for
    values the interpreter cannot know)."""
    if value is None:
        return "nil"
    if isinstance(value, bool):
        return "boolean"
    if is_lua_number(value):
        return "number"
    if isinstance(value, str):
        return "string"
    if isinstance(value, dict):
        return "table"
    if isinstance(value, (LuaFunction, BuiltinFunction)):
        return "function"
    return UNKNOWN


# ======================================================================================
# Lua standard library   (EXTENSION POINT A: add missing library functions here)
# ======================================================================================
# Every entry:   "name" or "library.name"  ->  python_function(context, argument_values)
# Return UNKNOWN whenever the result cannot be worked out.  Functions that change a
# table must call context.note_state_change() (it keeps the lookup cache correct).
def library_tostring(context, argument_values):
    """Lua tostring(): text of a string or number (Lua 5.1 style, 3.0 -> '3'); 'nil' for nil."""
    if not argument_values:
        return UNKNOWN
    value = argument_values[0]
    if isinstance(value, str) or is_lua_number(value):
        return lua_value_to_text(value)
    return "nil" if value is None else UNKNOWN


def text_to_number(stripped_text, argument_values):
    """The number a Lua string stands for (honouring tonumber's optional base); ValueError
    when the text is not a number."""
    if len(argument_values) > 1 and is_lua_number(argument_values[1]):
        return int(stripped_text, int(argument_values[1]))
    if stripped_text.lower().startswith("0x"):
        return int(stripped_text, 16)
    return float(stripped_text) if re.search(r"[.eE]", stripped_text) else int(stripped_text)


def library_tonumber(context, argument_values):
    """Lua tonumber(): a number from a number or numeric text, with an optional base; nil when
    the text is not a number."""
    if not argument_values:
        return UNKNOWN
    value = argument_values[0]
    if is_lua_number(value):
        return value
    if not isinstance(value, str):
        return UNKNOWN
    try:
        return text_to_number(value.strip(), argument_values)
    except ValueError:
        return None


def library_pairs(context, argument_values):
    """Lua pairs(t): every key / value of a table (nil values skipped), for a generic for loop."""
    if argument_values and isinstance(argument_values[0], dict):
        return PairsIteration([(key, value) for key, value in list(argument_values[0].items())
                               if value is not None])
    return UNKNOWN


def library_ipairs(context, argument_values):
    """Lua ipairs(t): the values at keys 1, 2, 3 ... up to the first gap, for a generic for
    loop."""
    if argument_values and isinstance(argument_values[0], dict):
        table_value = argument_values[0]
        return PairsIteration([(position, table_value[position])
                               for position in range(1, lua_table_length(table_value) + 1)])
    return UNKNOWN


def key_after_in_plain_dict(table_value, previous_key):
    """The key after previous_key in a plain dict (the first key for None), by linear search."""
    all_keys = list(table_value.keys())
    if previous_key is None:
        return all_keys[0] if all_keys else None
    try:
        key_position = all_keys.index(previous_key)
    except ValueError:
        return None
    return all_keys[key_position + 1] if key_position + 1 < len(all_keys) else None


def library_next(context, argument_values):
    """Lua next(t, key) -> the key that follows key in t (the first key for nil); only the
    key is returned (multiple results are not modelled).  O(1) per call for Lua tables
    (LuaTable.key_after keeps the key order); plain dicts fall back to a linear search."""
    if not argument_values or not isinstance(argument_values[0], dict):
        return UNKNOWN
    previous_key = argument_values[1] if len(argument_values) > 1 else None
    if isinstance(argument_values[0], LuaTable):
        return argument_values[0].key_after(previous_key)
    return key_after_in_plain_dict(argument_values[0], previous_key)


def library_select(context, argument_values):
    """Lua select('#', ...) -> number of extra arguments; select(n, ...) -> the n-th of them."""
    if not argument_values:
        return UNKNOWN
    selector = argument_values[0]
    if selector == "#":
        return len(argument_values) - 1
    if is_lua_number(selector):
        return argument_values[int(selector)] if int(selector) < len(argument_values) else None
    return UNKNOWN


def library_setmetatable(context, argument_values):
    """Lua setmetatable(t, mt): attach a metatable (its __index can supply missing keys) and
    return t."""
    if not argument_values:
        return UNKNOWN
    table_value = argument_values[0]
    metatable = argument_values[1] if len(argument_values) > 1 else None
    if isinstance(table_value, LuaTable):
        table_value.metatable = metatable if isinstance(metatable, dict) else None
        context.note_state_change()
    return table_value


def library_getmetatable(context, argument_values):
    """Lua getmetatable(t): the metatable set on table t (by setmetatable), or nil when it has none
    or t is not a table."""
    if not argument_values:
        return UNKNOWN
    return argument_values[0].metatable if isinstance(argument_values[0], LuaTable) else None


def library_rawget(context, argument_values):
    """Lua rawget(t, k): the value stored at t[k] without consulting the metatable's __index (nil
    when the key is missing)."""
    if len(argument_values) > 1 and isinstance(argument_values[0], dict):
        return argument_values[0].get(normalise_table_key(argument_values[1]))
    return UNKNOWN


def library_rawset(context, argument_values):
    """Lua rawset(t, k, v): store without consulting the metatable; returns t."""
    if len(argument_values) > 2 and isinstance(argument_values[0], dict):
        argument_values[0][normalise_table_key(argument_values[1])] = argument_values[2]
        context.note_state_change()
        return argument_values[0]
    return UNKNOWN


def library_unpack(context, argument_values):
    """unpack(t) -> first element only (multiple results are not modelled)."""
    if argument_values and isinstance(argument_values[0], dict):
        return argument_values[0].get(1)
    return UNKNOWN


def library_table_insert(context, argument_values):
    """Lua table.insert(t, v) appends v; table.insert(t, pos, v) inserts v at pos and moves
    later entries up."""
    if len(argument_values) == 2 and isinstance(argument_values[0], dict):
        table_value = argument_values[0]
        table_value[lua_table_length(table_value) + 1] = argument_values[1]
        context.note_state_change()
    elif len(argument_values) >= 3 and isinstance(argument_values[0], dict) and is_lua_number(argument_values[1]):
        table_value, insert_position, inserted_value = argument_values[0], int(argument_values[1]), argument_values[2]
        for moved_position in range(lua_table_length(table_value), insert_position - 1, -1):
            table_value[moved_position + 1] = table_value[moved_position]
        table_value[insert_position] = inserted_value
        context.note_state_change()
    return None


def library_table_concat(context, argument_values):
    """Lua table.concat(t [, separator]): the array part of t joined into one text (UNKNOWN if
    an entry is not text or a number)."""
    if not argument_values or not isinstance(argument_values[0], dict):
        return UNKNOWN
    table_value = argument_values[0]
    separator = argument_values[1] if len(argument_values) > 1 and isinstance(argument_values[1], str) else ""
    pieces = [table_value[position] for position in range(1, lua_table_length(table_value) + 1)]
    if not all(isinstance(piece, str) or is_lua_number(piece) for piece in pieces):
        return UNKNOWN
    return separator.join(lua_value_to_text(piece) for piece in pieces)


def format_one_lua_value(flags, conversion, value):
    """One string.format conversion of value; UNKNOWN when value cannot be converted."""
    if conversion in "diouxXc":
        if not is_lua_number(value):
            return UNKNOWN
        return ("%" + flags + ("d" if conversion in "iu" else conversion)) % int(value)
    if conversion in "eEfgG":
        if not is_lua_number(value):
            return UNKNOWN
        return ("%" + flags + conversion) % value
    if not (isinstance(value, (str, bool)) or is_lua_number(value) or value is None):
        return UNKNOWN
    text = lua_scalar_text(value)
    return ("%" + flags + "s") % text if conversion == "s" else '"' + text + '"'


def lua_scalar_text(value):
    """A string, number, boolean or nil as Lua prints it."""
    if value is None:
        return "nil"
    if isinstance(value, bool):
        return "true" if value else "false"
    return lua_value_to_text(value)


def library_string_format(context, argument_values):
    """Lua string.format: fills %d %i %u %o %x %X %c %e %f %g %s %q and %% in the format text with
    the arguments, converting each the way Lua does; UNKNOWN when the format or an argument
    cannot be known."""
    if not argument_values or not isinstance(argument_values[0], str):
        return UNKNOWN
    format_text, format_arguments = argument_values[0], argument_values[1:]
    output_pieces, argument_position, text_position = [], 0, 0
    for specifier in re.finditer(r"%([-+ #0]*\d*(?:\.\d+)?)([diouxXeEfgGcsq%])", format_text):
        output_pieces.append(format_text[text_position:specifier.start()])
        text_position = specifier.end()
        flags, conversion = specifier.group(1), specifier.group(2)
        if conversion == "%":
            output_pieces.append("%")
            continue
        if argument_position >= len(format_arguments) or format_arguments[argument_position] is UNKNOWN:
            return UNKNOWN
        value = format_arguments[argument_position]
        argument_position += 1
        converted_text = format_one_lua_value(flags, conversion, value)
        if converted_text is UNKNOWN:
            return UNKNOWN
        output_pieces.append(converted_text)
    output_pieces.append(format_text[text_position:])
    return "".join(output_pieces)


def library_string_sub(context, argument_values):
    """Lua string.sub(s, i [, j]): the part of s from position i to j (1-based, negative counts
    from the end)."""
    if not argument_values or not isinstance(argument_values[0], str):
        return UNKNOWN
    text = argument_values[0]
    first = argument_values[1] if len(argument_values) > 1 else 1
    last = argument_values[2] if len(argument_values) > 2 else -1
    if not (is_lua_number(first) and is_lua_number(last)):
        return UNKNOWN
    text_length, first, last = len(text), int(first), int(last)
    first = text_length + first + 1 if first < 0 else max(first, 1)
    last = text_length + last + 1 if last < 0 else min(last, text_length)
    return text[first - 1:last] if first <= last else ""


def make_number_function(python_function):
    """Wrap a Python math function as a Lua library function that only runs when every argument is
    a number (math.floor, math.max ...); any other argument gives UNKNOWN instead of an error."""
    def library_number_function(context, argument_values):
        """Run the wrapped math function when every argument is a number, else UNKNOWN."""
        if argument_values and all(is_lua_number(value) for value in argument_values):
            return python_function(*argument_values)
        return UNKNOWN
    return library_number_function


def make_string_function(python_function):
    """Wrap a Python string function so it only runs on a string first argument."""
    def library_string_function(context, argument_values):
        """Run the wrapped string function when the first argument is text, else UNKNOWN."""
        if argument_values and isinstance(argument_values[0], str) and UNKNOWN not in argument_values:
            return python_function(*argument_values)
        return UNKNOWN
    return library_string_function


LUA_STANDARD_LIBRARY = {
    "tostring": library_tostring,
    "tonumber": library_tonumber,
    "type": lambda context, argument_values: lua_type_name(argument_values[0]) if argument_values else UNKNOWN,
    "pairs": library_pairs,
    "ipairs": library_ipairs,
    "next": library_next,
    "select": library_select,
    "unpack": library_unpack,
    "setmetatable": library_setmetatable,
    "getmetatable": library_getmetatable,
    "rawget": library_rawget,
    "rawset": library_rawset,
    "assert": lambda context, argument_values: argument_values[0] if argument_values else UNKNOWN,
    "print": lambda context, argument_values: None,
    "error": lambda context, argument_values: None,        # keep going (e.g. >1000 commands)
    "table.insert": library_table_insert,
    "table.concat": library_table_concat,
    "table.unpack": library_unpack,
    "table.getn": lambda context, argument_values: lua_table_length(argument_values[0])
    if argument_values and isinstance(argument_values[0], dict) else UNKNOWN,
    "math.floor": make_number_function(math.floor),
    "math.ceil": make_number_function(math.ceil),
    "math.abs": make_number_function(abs),
    "math.max": make_number_function(max),
    "math.min": make_number_function(min),
    "math.fmod": make_number_function(math.fmod),
    "string.format": library_string_format,
    "string.sub": library_string_sub,
    "string.upper": make_string_function(lambda text, *unused: text.upper()),
    "string.lower": make_string_function(lambda text, *unused: text.lower()),
    "string.len": make_string_function(lambda text, *unused: len(text)),
    "string.rep": make_string_function(
        lambda text, count=1, *unused: text * int(count) if is_lua_number(count) else UNKNOWN),
}


def call_builtin_function(context, builtin_function, argument_values):
    """Run a library function; any Python error while doing so gives UNKNOWN instead of
    stopping the generation."""
    try:
        return builtin_function.python_function(context, argument_values)
    except (TypeError, ValueError, KeyError, IndexError, OverflowError, AttributeError):
        return UNKNOWN


# ======================================================================================
# Finding and reading Lua files
# ======================================================================================
def read_lua_file_text(file_path):
    """Read a Lua file as text: UTF-8 (with or without a byte-order mark), falling back to
    Latin-1 for older files."""
    with open(file_path, "rb") as lua_file:
        raw_bytes = lua_file.read()
    try:
        return raw_bytes.decode("utf-8-sig")
    except UnicodeDecodeError:
        return raw_bytes.decode("latin-1")


class LuaFileLocator:
    """Every .lua file under the chosen folder, for resolving dofile() paths such as
    LockOn_Options.script_path .. "devices.lua"   or   folder .. "../../../Cockpit/devices.lua"."""

    def __init__(self, lua_file_paths):
        """Index every .lua file three ways - absolute path, lower-case path with forward
        slashes, and by file name - so dofile() paths can be found with dictionary lookups."""
        self.absolute_paths = [os.path.abspath(path) for path in lua_file_paths]
        self.lowercase_slash_paths = [(path.replace("\\", "/").lower(), path) for path in self.absolute_paths]
        self.paths_by_file_name = {}
        for path in self.absolute_paths:
            self.paths_by_file_name.setdefault(os.path.basename(path).lower(), []).append(path)

    @staticmethod
    def shared_folder_length(first_path, second_path):
        """Length of the folder path two files have in common (0 when they are on different
        drives); larger means closer together."""
        try:
            return len(os.path.commonpath([first_path, second_path]))
        except ValueError:
            return 0

    def find_file(self, relative_path_text, including_file_path):
        """Tries, in order: next to the including file (with and without the given folders),
        any file whose path ends with the given path, any file with the same file name.
        When several match, the one closest to the including file wins."""
        path_parts = [part for part in relative_path_text.replace("\\", "/").split("/") if part not in ("", ".")]
        if not path_parts:
            return None
        including_folder = os.path.dirname(including_file_path)
        for candidate_path in (os.path.join(including_folder, *path_parts),
                               os.path.join(including_folder, path_parts[-1])):
            if os.path.isfile(candidate_path):
                return os.path.abspath(candidate_path)
        wanted_ending = "/" + "/".join(path_parts).lower()
        matching_paths = [path for lowered, path in self.lowercase_slash_paths if lowered.endswith(wanted_ending)]
        if not matching_paths:
            matching_paths = self.paths_by_file_name.get(path_parts[-1].lower(), [])
        if not matching_paths:
            return None
        return max(matching_paths, key=lambda path: self.shared_folder_length(path, including_file_path))


class ParsedLuaFile:
    """A file after tokenizing, block matching and parsing (done once per file)."""

    def __init__(self, file_path, source_text, tokens, statements, function_definitions):
        """Keep everything known about one parsed file: path, source text, tokens, top-level
        statements and the functions defined in it."""
        self.file_path = file_path
        self.source_text = source_text
        self.tokens = tokens
        self.statements = statements
        self.function_definitions = function_definitions


# ======================================================================================
# Syntax-tree helpers
# ======================================================================================
def dotted_name(node):
    """devices.RADIO -> "devices.RADIO";  anything that is not a plain name chain -> None."""
    if node.kind == "name":
        return node.name
    if node.kind == "index" and node.key_expression.kind == "string":
        base_name = dotted_name(node.table_expression)
        return f"{base_name}.{node.key_expression.value}" if base_name else None
    return None


def root_variable_name(node):
    """The first name of a variable path (cockpit_args.RADIO_Power_Switch -> "cockpit_args"), used
    to tell which table a reference belongs to; None for anything that is not a plain name
    chain."""
    while node.kind == "index":
        node = node.table_expression
    return node.name if node.kind == "name" else None


def expand_table_argument(node):
    """An argument written as {a, b} counts as the separate values a and b."""
    if node.kind == "table":
        return [value_node for key_node, value_node in node.fields if key_node is None]
    return [node]


SIMPLE_CHILD_ATTRIBUTES = {          # expression kind -> attributes holding its sub-expressions, in order
    "index": ("table_expression", "key_expression"),
    "binary": ("left", "right"),
    "unary": ("operand",),
    "parenthesized": ("inner",),
}


def table_field_nodes(table_node, with_keys):
    """The key (when with_keys) and value expressions of a table constructor's fields."""
    field_nodes = []
    for key_node, value_node in table_node.fields:
        if with_keys and key_node is not None:
            field_nodes.append(key_node)
        field_nodes.append(value_node)
    return field_nodes


def expression_children(node, with_function=True, with_keys=True):
    """The sub-expressions of an expression node, in source order.  with_function: include the
    called function's own expression; with_keys: include the keys of table constructor fields."""
    kind = node.kind
    if kind in SIMPLE_CHILD_ATTRIBUTES:
        return [getattr(node, attribute_name) for attribute_name in SIMPLE_CHILD_ATTRIBUTES[kind]]
    if kind == "call":
        return ([node.function_expression] if with_function else []) + list(node.arguments)
    if kind == "table":
        return table_field_nodes(node, with_keys)
    return []


def names_in_expression(node, collected_names=None):
    """Every variable name used in an expression, in source order and each once - used to find
    which parameters an element function passes on and which tables it reads."""
    if collected_names is None:
        collected_names = []
    if node.kind == "name":
        collected_names.append(node.name)
    for child_node in expression_children(node):
        names_in_expression(child_node, collected_names)
    return collected_names


def split_variable_path(variable_path):
    """'per_device_commands.GEAR["A B"][3].X' -> ['per_device_commands', 'GEAR', 'A B', 3, 'X']"""
    path_segments = []
    for segment_match in re.finditer(r"([A-Za-z_]\w*)|\[([^\]]*)\]", variable_path):
        if segment_match.group(1):
            path_segments.append(segment_match.group(1))
            continue
        bracket_text = segment_match.group(2)
        if re.fullmatch(r"-?\d+", bracket_text):
            path_segments.append(int(bracket_text))
        elif len(bracket_text) >= 2 and bracket_text[0] == bracket_text[-1] and bracket_text[0] in "'\"":
            path_segments.append(bracket_text[1:-1])
        else:
            path_segments.append(bracket_text)
    return path_segments


def parameter_role_from_name(parameter_name):
    """Last resort when a function body does not show what a parameter is:
    hint_ -> hint, device_ -> device, command1_ -> command, arg_ -> arg (arg_val / arg_lim are not)."""
    lowered_name = parameter_name.lower().strip("_")
    if "hint" in lowered_name:
        return "hint"
    if lowered_name.startswith("dev"):
        return "device"
    if "command" in lowered_name or "cmd" in lowered_name or lowered_name.startswith("action"):
        return "command"
    if re.fullmatch(r"arg(ument)?_?\d*", lowered_name):
        return "arg"
    return None


NOT_GIVEN = object()   # marker for "no scope given" in lookup_variable()
NOT_RECORDED = object()  # marker for "no remembered value" in TableRowBuilder.evaluated_value()
LITERAL_NODE_KINDS = frozenset(("number", "string", "constant"))   # values that never change


class ParameterRoleFinder:
    """Walks the body of one Lua element function and records which of its parameters play which
    role (hint / device / command / arg / name), as described in
    LuaExecutionContext.analyze_parameter_roles.  The first role found for a parameter wins."""

    def __init__(self, execution_context, definition, lookup_scope):
        self.execution_context = execution_context
        self.definition = definition
        self.lookup_scope = lookup_scope
        self.parameter_positions = {name: position for position, name in enumerate(definition.parameter_names)
                                    if name != "..."}
        self.found_roles = {}                    # parameter position -> role

    def run(self):
        """Walk the whole function body; returns {parameter position: role}."""
        try:
            self.visit_statements(self.definition.body_statements)
        except RecursionError:
            pass
        return self.found_roles

    def claim_parameters(self, expression_node, role):
        """Give every parameter used in the expression the role (the first role found wins)."""
        for used_name in names_in_expression(expression_node):
            if used_name in self.parameter_positions:
                self.found_roles.setdefault(self.parameter_positions[used_name], role)

    # ── expressions ───────────────────────────────────────────────────────────────
    def visit_expression(self, node):
        """Look through an expression for role-revealing table fields and for calls that pass
        parameters on to other element functions."""
        handler = self.EXPRESSION_HANDLERS.get(node.kind)
        if handler is not None:
            handler(self, node)

    def visit_table(self, node):
        """Look at the fields of a table constructor; fields named like element fields claim parameter roles."""
        name_keyed_positions = set(node.name_keyed_field_positions)
        for field_position, (key_node, value_node) in enumerate(node.fields):
            if field_position in name_keyed_positions and key_node.value in ELEMENT_FIELD_ROLES:
                self.claim_parameters(value_node, ELEMENT_FIELD_ROLES[key_node.value])
            if key_node is not None:
                self.visit_expression(key_node)
            self.visit_expression(value_node)

    def visit_call(self, node):
        """Look at a call: roles the callee gives its parameters, then the callee and its arguments."""
        if node.function_expression.kind == "name" and node.method_name is None:
            self.take_roles_from_callee(node)
        self.visit_expression(node.function_expression)
        for argument_node in node.arguments:
            self.visit_expression(argument_node)

    def take_roles_from_callee(self, call_node):
        """A parameter passed straight on to another element function takes the role that
        function gives that argument position."""
        callee_value = self.execution_context.lookup_variable(call_node.function_expression.name, self.lookup_scope)
        if not isinstance(callee_value, LuaFunction) or callee_value.definition is self.definition:
            return
        callee_roles = self.execution_context.analyze_parameter_roles(callee_value.definition)
        for argument_position, argument_node in enumerate(call_node.arguments):
            passes_parameter_on = (argument_position in callee_roles and argument_node.kind == "name"
                                   and argument_node.name in self.parameter_positions)
            if passes_parameter_on:
                self.found_roles.setdefault(self.parameter_positions[argument_node.name],
                                            callee_roles[argument_position])

    def visit_index(self, node):
        """Look at the table and the key of an index expression."""
        self.visit_expression(node.table_expression)
        self.visit_expression(node.key_expression)

    def visit_binary(self, node):
        """Look at both operands of a binary expression."""
        self.visit_expression(node.left)
        self.visit_expression(node.right)

    def visit_unary(self, node):
        """Look at the operand of a unary expression."""
        self.visit_expression(node.operand)

    def visit_parenthesized(self, node):
        """Look at the expression inside parentheses."""
        self.visit_expression(node.inner)

    def visit_function_expression(self, node):
        """Look at the body of an anonymous function."""
        self.visit_statements(node.definition.body_statements)

    EXPRESSION_HANDLERS = {
        "table": visit_table, "call": visit_call, "index": visit_index, "binary": visit_binary,
        "unary": visit_unary, "parenthesized": visit_parenthesized, "function": visit_function_expression,
    }

    # ── statements ────────────────────────────────────────────────────────────────
    def visit_statements(self, statements):
        """Look through statements (and nested blocks / functions) in source order."""
        for statement in statements:
            handler = self.STATEMENT_HANDLERS.get(statement.kind)
            if handler is not None:
                handler(self, statement)

    def visit_assignment(self, statement):
        """Look at an assignment: roles read from assigned fields, then every assigned value."""
        for target_position, target_node in enumerate(statement.targets):
            value_node = statement.values[target_position] if target_position < len(statement.values) else None
            if target_node.kind == "index":
                self.read_roles_from_assigned_field(target_node, value_node)
                self.visit_expression(target_node)
        for value_node in statement.values:
            self.visit_expression(value_node)

    def read_roles_from_assigned_field(self, target_node, value_node):
        """`something.hint = x` gives x's parameters that role; `elements[x] = ...` names x."""
        key_node = target_node.key_expression
        if (target_node.key_written_as_name and key_node.value in ELEMENT_FIELD_ROLES
                and value_node is not None):
            self.claim_parameters(value_node, ELEMENT_FIELD_ROLES[key_node.value])
        is_elements_table = (target_node.table_expression.kind == "name"
                             and target_node.table_expression.name == "elements")
        if is_elements_table and key_node.kind == "name" and key_node.name in self.parameter_positions:
            self.found_roles.setdefault(self.parameter_positions[key_node.name], "name")

    def visit_call_statement(self, statement):
        """Look at the call of a call statement."""
        self.visit_expression(statement.expression)

    def visit_function_statement(self, statement):
        """Look at the body of a function statement."""
        self.visit_statements(statement.definition.body_statements)

    def visit_if(self, statement):
        """Look at the conditions and branches of an if statement."""
        for condition, branch_statements in statement.branches:
            if condition is not None:
                self.visit_expression(condition)
            self.visit_statements(branch_statements)

    def visit_condition_loop(self, statement):
        """Look at the condition and body of a while or repeat loop."""
        self.visit_expression(statement.condition)
        self.visit_statements(statement.body)

    def visit_numeric_for(self, statement):
        """Look at the bounds and body of a numeric for loop."""
        for bound_node in (statement.start_expression, statement.stop_expression, statement.step_expression):
            if bound_node is not None:
                self.visit_expression(bound_node)
        self.visit_statements(statement.body)

    def visit_generic_for(self, statement):
        """Look at the iterator expressions and body of a generic for loop."""
        for iterator_node in statement.iterator_expressions:
            self.visit_expression(iterator_node)
        self.visit_statements(statement.body)

    def visit_block(self, statement):
        """Look at the statements of a do block."""
        self.visit_statements(statement.body)

    def visit_return(self, statement):
        """Look at the returned values of a return statement."""
        for value_node in statement.values:
            self.visit_expression(value_node)

    STATEMENT_HANDLERS = {
        "local": visit_assignment, "assign": visit_assignment, "call": visit_call_statement,
        "local_function": visit_function_statement, "function": visit_function_statement,
        "if": visit_if, "while": visit_condition_loop, "repeat": visit_condition_loop,
        "numeric_for": visit_numeric_for, "generic_for": visit_generic_for, "do": visit_block,
        "return": visit_return,
    }


class ReturnClassFinder:
    """Walks the body of one Lua element function (nested function bodies skipped) and works out
    the class(es) of the element it returns, as described in LuaExecutionContext.analyze_return_classes."""

    BLOCK_STATEMENT_KINDS = ("while", "repeat", "numeric_for", "generic_for", "do")

    def __init__(self, execution_context, definition, lookup_scope):
        self.execution_context = execution_context
        self.definition = definition
        self.lookup_scope = lookup_scope
        self.tables_by_variable = {}             # local name -> table constructor it was given
        self.classes_by_variable = {}            # local name -> class entries set through  name.class = {...}
        self.calls_by_variable = {}              # local name -> call it was given
        self.returned_nodes = []                 # first value of every return statement, in order

    def run(self):
        """The classes of the first return statement that shows any; [] when nothing shows them."""
        try:
            self.collect(self.definition.body_statements)
            return self.first_returned_classes()
        except RecursionError:
            return []

    @staticmethod
    def class_texts(table_node):
        """The entries of a table constructor's  class  field, as written (None without that field)."""
        for key_node, value_node in table_node.fields:
            if key_node is not None and key_node.kind == "string" and key_node.value == "class":
                return [entry_node.raw_text for entry_node in expand_table_argument(value_node)]
        return None

    def collect(self, statements):
        """Collect returned values and what local variables were given, in source order."""
        for statement in statements:
            kind = statement.kind
            if kind in ("local", "assign"):
                self.collect_assignment(statement)
            elif kind == "return":
                self.returned_nodes.extend(statement.values[:1])
            elif kind == "if":
                for _condition, branch_statements in statement.branches:
                    self.collect(branch_statements)
            elif kind in self.BLOCK_STATEMENT_KINDS:
                self.collect(statement.body)

    def collect_assignment(self, statement):
        """Remember the value assigned to each target of an assignment."""
        for target_position, target_node in enumerate(statement.targets):
            value_node = statement.values[target_position] if target_position < len(statement.values) else None
            if value_node is not None:
                self.remember_assignment(target_node, value_node)

    def remember_assignment(self, target_node, value_node):
        """Remember a variable assigned a table or a call, or a class field assigned to a variable, for later class lookups."""
        if target_node.kind == "name" and value_node.kind == "table":
            self.tables_by_variable[target_node.name] = value_node
        elif target_node.kind == "name" and value_node.kind == "call":
            self.calls_by_variable[target_node.name] = value_node
        elif self.is_class_field_target(target_node):
            self.classes_by_variable[target_node.table_expression.name] = \
                [entry_node.raw_text for entry_node in expand_table_argument(value_node)]

    @staticmethod
    def is_class_field_target(target_node):
        """True for the target  name.class  /  name["class"]."""
        return (target_node.kind == "index" and target_node.table_expression.kind == "name"
                and target_node.key_expression.kind == "string"
                and target_node.key_expression.value == "class")

    def first_returned_classes(self):
        """The class texts of the first returned value that has any."""
        found_classes = []
        for returned_node in self.returned_nodes:
            found_classes = self.classes_of_returned(returned_node)
            if found_classes:
                break
        return found_classes

    def classes_of_returned(self, returned_node):
        """The class texts a returned expression stands for (a table, a variable or a call)."""
        if returned_node.kind == "table":
            return self.class_texts(returned_node) or []
        if returned_node.kind == "name":
            return self.classes_of_returned_variable(returned_node.name)
        if returned_node.kind == "call":
            return self.classes_of_call(returned_node)
        return []

    def classes_of_returned_variable(self, variable_name):
        """The classes a returned local variable has: set directly, from its table, or from its call."""
        if self.classes_by_variable.get(variable_name):
            return self.classes_by_variable[variable_name]
        if variable_name in self.tables_by_variable:
            table_classes = self.class_texts(self.tables_by_variable[variable_name])
            if table_classes:
                return table_classes
        if variable_name in self.calls_by_variable:
            return self.classes_of_call(self.calls_by_variable[variable_name]) or []
        return []

    def classes_of_call(self, call_node):
        """The return classes of another element function this one calls by name (e.g. return
        default_button(...)), found by analyzing that function in turn."""
        if call_node.function_expression.kind != "name":
            return []
        callee_value = self.execution_context.lookup_variable(call_node.function_expression.name, self.lookup_scope)
        if isinstance(callee_value, LuaFunction) and callee_value.definition is not self.definition:
            return self.execution_context.analyze_return_classes(callee_value.definition)
        return []


# ======================================================================================
# The Lua interpreter
# ======================================================================================
class LuaExecutionContext:
    """Runs one clickabledata.lua and everything it (and the Input files) pull in.

    Unknown things are never fatal: an unknown value is UNKNOWN, a branch whose condition
    is UNKNOWN is still walked ("uncertain", its 'return' is ignored), a loop whose bounds
    are UNKNOWN runs once.  That way the parts that CAN be known are always found."""

    def __init__(self, search_root_folder, file_locator):
        """Start an empty Lua world for one aircraft: globals with the standard library,
        scopes, caches, the record of numbers defined, and the dispatch tables for
        statements and expressions."""
        self.search_root_folder = search_root_folder
        self.file_locator = file_locator
        self.global_variables = {}
        self.current_scope = None                   # innermost VariableScope (None = only globals)
        self.file_scopes = {}                       # file key -> that file's top-level locals
        self.uncertainty_depth = 0                  # > 0 while running an uncertain branch
        self.call_depth = 0
        self.executed_statement_count = 0
        # The FIRST number each variable was given (as listed where it is defined, e.g. in the
        # cockpit_args table), kept even when a later script or a repeated key changes it.
        self.first_numeric_definitions = {}        # variable path -> (file path, number)
        # Values the Lua ACTUALLY produced for the expressions in a file's top-level code,
        # keyed by (file key, first token, token after the last).  The row builders read
        # these instead of evaluating the expressions again: evaluating a call such as
        # command_counter() a second time would increment the counter again and give the
        # wrong number (and shift every later one).  Only expressions evaluated outside
        # function calls are kept (call_depth 0); literals are not kept (they never change).
        self.top_level_values = {}
        self.recording_file_key = None             # the file whose top-level code is running
        self.state_version = 0                      # changes whenever a table / outer variable changes
        self.index_lookup_cache = {}                # (table id, key) -> (state_version, value)
        self.visited_file_keys = set()
        self.file_stack = []                        # files currently running (dofile nesting)
        self.parsed_files = {}                      # file key -> ParsedLuaFile
        self.function_definitions = []              # every function in every parsed file
        self.processed_file_paths = []
        self.numeric_definitions = {}               # variable path -> (file path, number)
        self.shadowed_numeric_definitions = []      # [(path, file path, number)] overwritten duplicates
        self.element_arg_references = set()         # variable paths used as element args
        self.element_command_references = set()     # variable paths used as element commands
        self.input_file_keys = set()
        self.partial_path_endings = {}              # variable -> known end of a dofile path
        self.unmapped_function_names = set()
        self.warnings = []
        self.step_limit_reported = False
        self.install_standard_library()
        self.statement_executors = {
            "local": self.execute_local, "assign": self.execute_assign, "call": self.execute_call,
            "local_function": self.execute_local_function, "function": self.execute_function,
            "if": self.execute_if, "while": self.execute_while, "numeric_for": self.execute_numeric_for,
            "generic_for": self.execute_generic_for, "repeat": self.execute_repeat, "do": self.execute_do,
            "return": self.execute_return, "break": self.execute_break,
        }
        self.expression_evaluators = {
            "number": self.evaluate_literal, "string": self.evaluate_literal, "constant": self.evaluate_literal,
            "name": self.evaluate_name, "parenthesized": self.evaluate_parenthesized,
            "index": self.evaluate_index, "call": self.evaluate_call, "table": self.evaluate_table,
            "function": self.evaluate_function, "vararg": self.evaluate_vararg,
            "unary": self.evaluate_unary, "binary": self.evaluate_binary,
        }

    # ------------------------------------------------------------------ general helpers
    def relative_path(self, file_path):
        """A file's path relative to the chosen folder (e.g. Cockpit/Scripts/devices.lua), so
        messages and the Source tab stay short; the full path when it is on another drive."""
        try:
            return os.path.relpath(file_path, self.search_root_folder)
        except ValueError:
            return file_path

    @staticmethod
    def file_key(file_path):
        """Key identifying a file regardless of how its path is written (absolute, case-
        normalised on Windows)."""
        return os.path.normcase(os.path.abspath(file_path))

    def install_standard_library(self):
        """Put _VERSION and every LUA_STANDARD_LIBRARY function into the globals (dotted names
        go into library tables such as string / table / math)."""
        self.global_variables["_VERSION"] = "Lua 5.1"          # DCS runs Lua 5.1
        for library_name, python_function in LUA_STANDARD_LIBRARY.items():
            name_parts = library_name.split(".")
            builtin_function = BuiltinFunction(library_name, python_function)
            if len(name_parts) == 1:
                self.global_variables[library_name] = builtin_function
            else:
                library_table = self.global_variables.setdefault(name_parts[0], LuaTable())
                library_table[name_parts[1]] = builtin_function

    def note_state_change(self):
        """Called whenever a table or an outer variable changes: increases state_version, which
        makes every cached metatable __index result stale, so lookups after a change are worked
        out again."""
        self.state_version += 1

    # ------------------------------------------------------------------ variables
    def lookup_variable(self, variable_name, starting_scope=NOT_GIVEN):
        """Value of a variable: the nearest local with that name (starting at starting_scope),
        else the global, else UNKNOWN."""
        scope = self.current_scope if starting_scope is NOT_GIVEN else starting_scope
        while scope is not None:
            if variable_name in scope.variables:
                return scope.variables[variable_name]
            scope = scope.parent_scope
        return self.global_variables.get(variable_name, UNKNOWN)

    def assign_variable(self, variable_name, value):
        """Assign to the nearest local with that name, else to the global."""
        scope = self.current_scope
        inside_current_call = True
        while scope is not None:
            if variable_name in scope.variables:
                scope.variables[variable_name] = value
                if self.call_depth == 0 or not inside_current_call:
                    self.note_state_change()
                return
            if scope.is_function_scope:
                inside_current_call = False
            scope = scope.parent_scope
        self.global_variables[variable_name] = value
        self.note_state_change()

    def declare_local(self, variable_name, value):
        """Create a local variable in the current scope (a global when there is no scope)."""
        if self.current_scope is None:
            self.global_variables[variable_name] = value
            self.note_state_change()
        else:
            self.current_scope.variables[variable_name] = value
            if self.call_depth == 0:
                self.note_state_change()

    def current_variable_arguments(self):
        """The '...' values of the innermost function call, or None outside such a call."""
        scope = self.current_scope
        while scope is not None:
            if scope.variable_arguments is not None:
                return scope.variable_arguments
            scope = scope.parent_scope
        return None

    def is_function_local(self, variable_name):
        """True when the variable belongs to a function call (a temporary)."""
        scope = self.current_scope
        while scope is not None:
            if variable_name in scope.variables:
                while scope is not None:
                    if scope.is_function_scope:
                        return True
                    scope = scope.parent_scope
                return False
            scope = scope.parent_scope
        return False

    def set_variable_path(self, name_parts, value):
        """Store a value at a dotted path (function a.b.c() ... end stores the function at a.b.c):
        walks the existing tables a, a.b and sets the last field; nothing is stored when a table
        on the way does not exist."""
        if len(name_parts) == 1:
            self.assign_variable(name_parts[0], value)
            return
        container = self.lookup_variable(name_parts[0])
        for name_part in name_parts[1:-1]:
            container = container.get(name_part) if isinstance(container, dict) else None
        if isinstance(container, dict):
            container[name_parts[-1]] = value
            self.note_state_change()

    # ------------------------------------------------------------------ files
    def get_parsed_file(self, file_path):
        """Tokenize, block-match and parse a file once; later calls return the cached result."""
        key = self.file_key(file_path)
        parsed_file = self.parsed_files.get(key)
        if parsed_file is None:
            source_text = read_lua_file_text(file_path)
            tokens = tokenize_lua_source(source_text)
            block_end_index, if_branch_indices = match_lua_blocks(tokens)
            file_function_definitions = []
            parser = LuaSyntaxParser(tokens, source_text, file_path, block_end_index, if_branch_indices,
                                     file_function_definitions)
            statements = parser.parse_chunk()
            parsed_file = ParsedLuaFile(file_path, source_text, tokens, statements, file_function_definitions)
            parsed_file.block_end_index = block_end_index
            parsed_file.if_branch_indices = if_branch_indices
            self.parsed_files[key] = parsed_file
            self.function_definitions.extend(file_function_definitions)
        return parsed_file

    def run_lua_file(self, file_path):
        """Run a file once, like dofile: parse it (cached in parsed_files), run its statements in a
        fresh file scope with recording of top-level values switched on, and return what the
        file returns. A file already run is not run again, so dofile chains and repeated
        includes cost one run each."""
        file_path = os.path.abspath(file_path)
        key = self.file_key(file_path)
        if key in self.visited_file_keys or len(self.file_stack) > 40:
            return None
        self.visited_file_keys.add(key)
        try:
            parsed_file = self.get_parsed_file(file_path)
        except OSError as read_error:
            self.warnings.append(f"Could not read {self.relative_path(file_path)}: {read_error}")
            return None
        self.processed_file_paths.append(file_path)
        self.file_stack.append(file_path)
        saved_scope, saved_uncertainty, saved_call_depth = self.current_scope, self.uncertainty_depth, self.call_depth
        saved_recording_file_key = self.recording_file_key
        self.recording_file_key = key                  # remember this file's top-level values
        self.current_scope = VariableScope(None)
        self.file_scopes[key] = self.current_scope
        self.uncertainty_depth = 0
        returned_value = None
        try:
            self.execute_block(parsed_file.statements)
        except ReturnSignal as return_signal:
            returned_value = return_signal.returned_values[0] if return_signal.returned_values else None
        except BreakSignal:
            pass
        except RecursionError:
            self.warnings.append(f"{self.relative_path(file_path)} is nested too deeply to process completely.")
        finally:
            self.current_scope, self.uncertainty_depth, self.call_depth = saved_scope, saved_uncertainty, saved_call_depth
            self.recording_file_key = saved_recording_file_key
            self.file_stack.pop()
        return returned_value

    def include_file(self, path_argument_node):
        """dofile(...): work out the file from the literal part of the path and run it."""
        relative_path_text = self.literal_path_ending(path_argument_node)
        including_file = self.file_stack[-1] if self.file_stack else self.search_root_folder
        if not relative_path_text:
            self.warnings.append(f"Could not work out the dofile() path '{path_argument_node.raw_text}' "
                                 f"in {self.relative_path(including_file)}")
            return UNKNOWN
        target_path = self.file_locator.find_file(relative_path_text, including_file)
        if target_path:
            return self.run_lua_file(target_path)
        self.warnings.append(f"Included file '{relative_path_text}' not found "
                             f"(from {self.relative_path(including_file)})")
        return UNKNOWN

    def literal_path_ending(self, node):
        """The known part of a dofile path:
             LockOn_Options.script_path .. "devices.lua"          -> "devices.lua"
             cockpit .. "devices.lua" (cockpit = folder .. "../../../Cockpit/")
                                                                  -> "../../../Cockpit/devices.lua" """
        value = self.evaluate(node)
        if isinstance(value, str):
            return value
        if node.kind == "string":
            return node.value
        if node.kind == "binary" and node.operator == "..":
            return self.concatenated_path_ending(node)
        if node.kind == "parenthesized":
            return self.literal_path_ending(node.inner)
        if node.kind == "name":
            return self.partial_path_endings.get(node.name)
        return None

    def concatenated_path_ending(self, node):
        """The known end of  left .. right  (None when the right part is not known)."""
        right_ending = self.literal_path_ending(node.right)
        if right_ending is None:
            return None
        left_value = self.evaluate(node.left)
        if isinstance(left_value, str):
            return left_value + right_ending
        left_ending = self.literal_path_ending(node.left)
        return (left_ending + right_ending) if left_ending else right_ending

    # ------------------------------------------------------------------ statements
    def execute_block(self, statements):
        """Run statements one by one through the statement dispatch table."""
        statement_executors = self.statement_executors
        for statement in statements:
            self.executed_statement_count += 1
            statement_executors[statement.kind](statement)

    def execute_in_new_scope(self, statements, scope=None):
        """Run statements inside a fresh block scope (or the given one), restoring the previous
        scope afterwards."""
        saved_scope = self.current_scope
        self.current_scope = scope if scope is not None else VariableScope(saved_scope)
        try:
            self.execute_block(statements)
        finally:
            self.current_scope = saved_scope

    def execute_uncertain(self, statements, scope=None):
        """Run code whose condition is unknown: everything it defines is still recorded,
        but a 'return' inside it does not end the function."""
        self.uncertainty_depth += 1
        try:
            self.execute_in_new_scope(statements, scope)
        finally:
            self.uncertainty_depth -= 1

    def execute_local(self, statement):
        """local a, b = ...: evaluates the right-hand side first, then declares each name as a
        local of the current scope (assign_targets), so later code in the block sees the new
        values."""
        self.assign_targets(statement.targets, statement.values, is_local=True)

    def execute_assign(self, statement):
        """a, b.c, d[e] = ...: evaluates the right-hand side first (as Lua does), then stores into
        each target - a variable, or a table field / index - through assign_targets."""
        self.assign_targets(statement.targets, statement.values)

    def execute_call(self, statement):
        """A call used as a statement, e.g. dofile(...) or table.insert(...)."""
        self.evaluate(statement.expression)

    def create_closure(self, definition):
        """Make a LuaFunction for a definition, capturing the current scope (the first scope is
        also remembered for role analysis)."""
        if definition.first_closure_scope is None:
            definition.first_closure_scope = self.current_scope if self.current_scope is not None else NOT_GIVEN
        return LuaFunction(definition, self.current_scope)

    def execute_local_function(self, statement):
        """local function name(...) - declared first so the function can call itself."""
        self.declare_local(statement.name, None)                   # visible inside itself (recursion)
        self.declare_local(statement.name, self.create_closure(statement.definition))

    def execute_function(self, statement):
        """function a.b.c(...) ... end: makes a closure of the definition (create_closure) and
        stores it at that path with set_variable_path, creating nothing that does not already
        exist."""
        self.set_variable_path(statement.name_parts, self.create_closure(statement.definition))

    def execute_if(self, statement):
        """Run the first branch whose condition is true; a branch whose condition is UNKNOWN is
        run as uncertain, and so are later branches."""
        earlier_condition_unknown = False
        for condition, branch_statements in statement.branches:
            if condition is None:                                  # else
                self.run_branch(branch_statements, earlier_condition_unknown)
                return
            condition_value = self.evaluate(condition)
            if condition_value is UNKNOWN:
                earlier_condition_unknown = True
                self.execute_uncertain(branch_statements)
            elif is_lua_truthy(condition_value):
                self.run_branch(branch_statements, earlier_condition_unknown)
                return

    def run_branch(self, branch_statements, uncertain):
        """Run a branch that is taken; uncertain when an earlier condition was UNKNOWN."""
        if uncertain:
            self.execute_uncertain(branch_statements)
        else:
            self.execute_in_new_scope(branch_statements)

    def execute_while(self, statement):
        """Loop while the condition is true (at most MAX_LOOP_ITERATIONS); an UNKNOWN condition
        runs the body once as uncertain."""
        for iteration_number in range(MAX_LOOP_ITERATIONS):
            condition_value = self.evaluate(statement.condition)
            if condition_value is UNKNOWN:
                if iteration_number == 0:
                    self.execute_uncertain_once(statement.body)
                return
            if not is_lua_truthy(condition_value):
                return
            try:
                self.execute_in_new_scope(statement.body)
            except BreakSignal:
                return

    def execute_uncertain_once(self, body_statements, loop_scope=None):
        """Run a loop body once as uncertain; a 'break' just ends it."""
        try:
            self.execute_uncertain(body_statements, loop_scope)
        except BreakSignal:
            pass

    def execute_numeric_for(self, statement):
        """for i = start, stop, step: runs for real when the bounds are numbers (up to
        MAX_LOOP_ITERATIONS), otherwise once as uncertain with i UNKNOWN."""
        start_value = self.evaluate(statement.start_expression)
        stop_value = self.evaluate(statement.stop_expression) if statement.stop_expression else UNKNOWN
        step_value = self.evaluate(statement.step_expression) if statement.step_expression else 1
        iteration_count = self.numeric_for_iteration_count(start_value, stop_value, step_value)
        if iteration_count is None:                                # unknown bounds: walk the body once
            loop_scope = VariableScope(self.current_scope)
            loop_scope.variables[statement.variable_name] = UNKNOWN
            self.execute_uncertain_once(statement.body, loop_scope)
            return
        for iteration_number in range(iteration_count):
            loop_scope = VariableScope(self.current_scope)
            loop_scope.variables[statement.variable_name] = start_value + iteration_number * step_value
            try:
                self.execute_in_new_scope(statement.body, loop_scope)
            except BreakSignal:
                return

    @staticmethod
    def numeric_for_iteration_count(start_value, stop_value, step_value):
        """How many times a numeric for runs, or None when a bound is unknown or the count
        exceeds MAX_LOOP_ITERATIONS."""
        if not (is_lua_number(start_value) and is_lua_number(stop_value) and is_lua_number(step_value)
                and step_value != 0):
            return None
        iteration_count = max(0, math.floor((stop_value - start_value) / step_value) + 1)
        return None if iteration_count > MAX_LOOP_ITERATIONS else iteration_count

    def execute_generic_for(self, statement):
        """for k, v in pairs(t) / ipairs(t): one pass per item; an unknown iterator runs the
        body once as uncertain."""
        iterator_value = self.evaluate(statement.iterator_expressions[0]) if statement.iterator_expressions else UNKNOWN
        if isinstance(iterator_value, PairsIteration):
            self.run_pairs_iteration(statement, iterator_value)
            return
        loop_scope = VariableScope(self.current_scope)
        for variable_name in statement.variable_names:
            loop_scope.variables[variable_name] = UNKNOWN
        self.execute_uncertain_once(statement.body, loop_scope)

    def run_pairs_iteration(self, statement, pairs_iteration):
        """Run the loop body once per item (at most MAX_LOOP_ITERATIONS); 'break' stops it."""
        for item in pairs_iteration.items[:MAX_LOOP_ITERATIONS]:
            loop_scope = VariableScope(self.current_scope)
            for position, variable_name in enumerate(statement.variable_names):
                loop_scope.variables[variable_name] = item[position] if position < len(item) else None
            try:
                self.execute_in_new_scope(statement.body, loop_scope)
            except BreakSignal:
                return

    def execute_repeat(self, statement):
        """repeat ... until condition (the condition can see the body's locals)."""
        for iteration_number in range(MAX_LOOP_ITERATIONS):
            saved_scope = self.current_scope
            self.current_scope = VariableScope(saved_scope)          # 'until' sees the body's locals
            try:
                try:
                    self.execute_block(statement.body)
                except BreakSignal:
                    return
                condition_value = self.evaluate(statement.condition)
            finally:
                self.current_scope = saved_scope
            if condition_value is UNKNOWN or is_lua_truthy(condition_value):
                return

    def execute_do(self, statement):
        """do ... end: runs the statements in a new block scope (execute_in_new_scope), so locals
        declared inside are gone afterwards, as in Lua."""
        self.execute_in_new_scope(statement.body)

    def execute_return(self, statement):
        """return values - ends the function, unless we are inside uncertain code."""
        returned_values = [self.evaluate(value_node) for value_node in statement.values]
        if self.uncertainty_depth == 0:
            raise ReturnSignal(returned_values)

    def execute_break(self, statement):
        """break: leaves the innermost loop by raising BreakSignal, which the loop executors catch."""
        raise BreakSignal()

    # ------------------------------------------------------------------ assignment
    def assign_targets(self, target_nodes, value_nodes, is_local=False):
        """Evaluate the right-hand side first (like Lua), then store into each target; also
        remembers the literal end of partial dofile paths."""
        values = [self.evaluate(value_node) for value_node in value_nodes]   # right side first, like Lua
        for position, target_node in enumerate(target_nodes):
            value_node = value_nodes[position] if position < len(value_nodes) else None
            value = values[position] if position < len(values) else None
            self.store_value(target_node, value, is_local)
            if target_node.kind == "name":
                self.remember_partial_path(target_node.name, value, value_node)

    def remember_partial_path(self, variable_name, value, value_node):
        """Remember the literal end of a partial dofile path ("dir" .. unknown) assigned to a variable."""
        path_ending = None
        if value is UNKNOWN and value_node is not None and value_node.kind == "binary" \
                and value_node.operator == "..":
            path_ending = self.literal_path_ending(value_node)
        if path_ending:
            self.partial_path_endings[variable_name] = path_ending
        else:
            self.partial_path_endings.pop(variable_name, None)

    def store_value(self, target_node, value, is_local=False):
        """Store one value into a variable or table field, and record the numbers it defines
        (for arg / command rows) unless the variable belongs to a function call."""
        if isinstance(value, LuaFunction) and value.definition.name is None:
            value.definition.name = dotted_name(target_node) or target_node.raw_text
        if target_node.kind == "name":
            if is_local:
                self.declare_local(target_node.name, value)
            else:
                self.assign_variable(target_node.name, value)
        elif target_node.kind == "index":
            self.store_table_field(target_node, value)
        self.record_defined_number(target_node, value)

    def store_table_field(self, target_node, value):
        """table[key] = value (nil removes the key); nothing happens for an unknown table or key."""
        table_value = self.evaluate(target_node.table_expression)
        if not isinstance(table_value, dict):
            return
        key = normalise_table_key(self.evaluate(target_node.key_expression))
        if key is None or key is UNKNOWN:
            return
        if value is None:
            table_value.pop(key, None)                 # assigning nil removes the key
        else:
            table_value[key] = value
        self.note_state_change()

    def record_defined_number(self, target_node, value):
        """Remember numbers written to variables that outlive the code writing them (globals
        and file-level locals such as a local table of per-device commands).  Variables of a
        function call are temporary and left out.  These become arg / command rows."""
        root_name = target_node.name if target_node.kind == "name" else root_variable_name(target_node)
        if self.file_stack and root_name is not None and not self.is_function_local(root_name):
            variable_path = self.target_variable_path(target_node)
            if variable_path:
                self.record_numeric_definitions(variable_path, value, self.file_stack[-1])

    def target_variable_path(self, target_node):
        """devices.RADIO / ARG["X"] / ARG[3]  ->  "devices.RADIO" / "ARG.X" / "ARG[3]" """
        if target_node.kind == "name":
            return target_node.name
        if target_node.kind != "index":
            return None
        base_path = self.target_variable_path(target_node.table_expression)
        if base_path is None:
            return None
        key = normalise_table_key(self.evaluate(target_node.key_expression))
        if isinstance(key, str) and re.fullmatch(r"[A-Za-z_]\w*", key):
            return f"{base_path}.{key}"
        if isinstance(key, str):
            return f"{base_path}[{key!r}]"
        if isinstance(key, int) and not isinstance(key, bool):
            return f"{base_path}[{key}]"
        return None

    def record_numeric_definitions(self, variable_path, value, file_path, nesting_depth=0):
        """Record every number reachable from variable_path (nested tables included, up to 6
        levels), with the file that defined it; duplicate keys overwritten in a constructor
        are recorded too."""
        if is_lua_number(value):
            self.numeric_definitions.pop(variable_path, None)      # a re-assignment moves it to the end
            self.numeric_definitions[variable_path] = (file_path, value)
            self.first_numeric_definitions.setdefault(variable_path, (file_path, value))
        elif isinstance(value, dict) and nesting_depth < 6:
            self.record_shadowed_definitions(variable_path, value, file_path)
            for key, nested_value in value.items():
                nested_path = self.nested_variable_path(variable_path, key)
                if nested_path is not None:
                    self.record_numeric_definitions(nested_path, nested_value, file_path, nesting_depth + 1)

    @staticmethod
    def nested_variable_path(variable_path, key):
        """variable_path.key (or variable_path[number]) for a table key, None for other kinds of key."""
        if isinstance(key, str) and re.fullmatch(r"[A-Za-z_]\w*", key):
            return f"{variable_path}.{key}"
        if is_lua_number(key):
            return f"{variable_path}[{format_number_text(key)}]"
        return None

    def record_shadowed_definitions(self, variable_path, table_value, file_path):
        """Numbers a table constructor wrote twice under the same key (the earlier ones)."""
        for shadowed_key, shadowed_value in (getattr(table_value, "shadowed_entries", None) or []):
            if is_lua_number(shadowed_value):
                shadowed_path = (f"{variable_path}.{shadowed_key}" if isinstance(shadowed_key, str)
                                 else f"{variable_path}[{format_number_text(shadowed_key)}]")
                self.shadowed_numeric_definitions.append((shadowed_path, file_path, shadowed_value))
                # a repeated key: the first one written is the one listed first
                self.first_numeric_definitions.setdefault(shadowed_path, (file_path, shadowed_value))

    # ------------------------------------------------------------------ expressions
    def evaluate(self, node):
        """Value of an expression, through the expression dispatch table.  While a file's
        top-level code runs, the value is also remembered in top_level_values."""
        value = self.expression_evaluators[node.kind](node)
        if self.call_depth == 0 and self.recording_file_key is not None and node.kind not in LITERAL_NODE_KINDS:
            self.top_level_values[(self.recording_file_key, node.first_token_index, node.after_last_token_index)] = value
        return value

    def evaluate_literal(self, node):
        """A literal in the code - a number, string, nil, true or false - is its own value;
        returned as written."""
        return node.value

    def evaluate_name(self, node):
        """A plain variable used in an expression: its value, found by lookup_variable (innermost
        local first, then globals), or UNKNOWN when it is defined nowhere."""
        return self.lookup_variable(node.name)

    def evaluate_parenthesized(self, node):
        """(expression): the value of the expression inside the parentheses. Used by the expression
        dispatch table; parentheses only group, so the inner value is returned unchanged."""
        return self.evaluate(node.inner)

    def evaluate_index(self, node):
        """table.key / table[key], metatables included (see index_value)."""
        return self.index_value(self.evaluate(node.table_expression),
                                normalise_table_key(self.evaluate(node.key_expression)))

    def evaluate_function(self, node):
        """function(...) ... end used as a value: makes a new closure (create_closure) that
        remembers the scope it was made in, as Lua does."""
        return self.create_closure(node.definition)

    def evaluate_vararg(self, node):
        """'...' used as a single value: the first of the extra arguments the current function was
        called with (nil when there are none, UNKNOWN outside a function)."""
        variable_arguments = self.current_variable_arguments()
        if variable_arguments is None:
            return UNKNOWN
        return variable_arguments[0] if variable_arguments else None

    def index_value(self, table_value, key, chain_depth=0):
        """table[key] with Lua rules: a missing key is nil unless the metatable's __index
        (a table or a function) supplies it.  __index FUNCTION results are cached until
        some table or outer variable changes (state_version), which makes a metatable-based
        per-device command lookup cheap after the first time."""
        if not isinstance(table_value, dict) or key is UNKNOWN:
            return UNKNOWN
        if key in table_value:
            return table_value[key]
        metatable = table_value.metatable if isinstance(table_value, LuaTable) else None
        if metatable is None or chain_depth >= 20:
            return None
        index_handler = metatable.get("__index")
        if isinstance(index_handler, dict):
            return self.index_value(index_handler, key, chain_depth + 1)
        if isinstance(index_handler, LuaFunction):
            return self.cached_index_function_result(index_handler, table_value, key)
        if isinstance(index_handler, BuiltinFunction):
            return call_builtin_function(self, index_handler, [table_value, key])
        return None

    def cached_index_function_result(self, index_function, table_value, key):
        """The value an __index function gives for key; remembered until the state changes."""
        cache_key = (id(table_value), key)
        cached_entry = self.index_lookup_cache.get(cache_key)
        if cached_entry is not None and cached_entry[0] == self.state_version:
            return cached_entry[1]
        version_before_call = self.state_version
        looked_up_value = self.invoke_lua_function(index_function, [table_value, key])
        if self.state_version == version_before_call:          # only cache side-effect-free lookups
            self.index_lookup_cache[cache_key] = (version_before_call, looked_up_value)
        return looked_up_value

    def evaluate_table(self, node):
        """{ ... }: builds a LuaTable; a final '...' adds every extra argument; a key given
        twice keeps the last value but remembers the first."""
        new_table, next_array_position = LuaTable(), 1
        last_field_position = len(node.fields) - 1
        for field_position, (key_node, value_node) in enumerate(node.fields):
            if key_node is not None:
                self.add_keyed_field(new_table, key_node, self.evaluate(value_node))
                continue
            for array_value in self.array_field_values(value_node, field_position == last_field_position):
                new_table[next_array_position] = array_value
                next_array_position += 1
        return new_table

    def array_field_values(self, value_node, is_last_field):
        """The values an unkeyed table field adds: every extra argument for a final '...', else one."""
        if value_node.kind == "vararg" and is_last_field:
            return list(self.current_variable_arguments() or ())
        return [self.evaluate(value_node)]

    def add_keyed_field(self, new_table, key_node, field_value):
        """[key] = value / name = value inside a table constructor (an unusable key is skipped)."""
        key = normalise_table_key(self.evaluate(key_node))
        if key is None or key is UNKNOWN:
            return
        if key in new_table:            # same key twice: Lua keeps the last, both were defined
            new_table.shadowed_entries = (new_table.shadowed_entries or []) + [(key, new_table[key])]
        new_table[key] = field_value

    def evaluate_unary(self, node):
        """The unary operators: -x (negation, numbers only), #x (length of a string, or the 1..n
        array part of a table via lua_table_length) and not x (Lua truth). Anything the
        interpreter cannot know gives UNKNOWN."""
        operand_value = self.evaluate(node.operand)
        operator = node.operator
        if operator == "-" and is_lua_number(operand_value):
            return -operand_value
        if operator == "#":
            if isinstance(operand_value, str):
                return len(operand_value)
            if isinstance(operand_value, dict):
                return lua_table_length(operand_value)
        if operator == "not" and operand_value is not UNKNOWN:
            return not is_lua_truthy(operand_value)
        return UNKNOWN

    COMPARISON_OPERATORS = {"<": lambda a, b: a < b, "<=": lambda a, b: a <= b,
                            ">": lambda a, b: a > b, ">=": lambda a, b: a >= b}
    ARITHMETIC_OPERATORS = {"+": lambda a, b: a + b, "-": lambda a, b: a - b, "*": lambda a, b: a * b,
                            "/": lambda a, b: a / b, "//": lambda a, b: a // b, "%": lambda a, b: a % b,
                            "^": lambda a, b: float(a) ** b}

    def evaluate_binary(self, node):
        """and / or (with 'x or default' using the default when x is unknown), .., comparisons
        and arithmetic; anything involving UNKNOWN is UNKNOWN."""
        operator = node.operator
        if operator in ("and", "or"):
            return self.evaluate_logical(node)
        left_value, right_value = self.evaluate(node.left), self.evaluate(node.right)
        if left_value is UNKNOWN or right_value is UNKNOWN:
            return UNKNOWN
        if operator == "..":
            return self.concatenate_values(left_value, right_value)
        if operator in ("==", "~="):
            values_equal = self.lua_values_equal(left_value, right_value)
            return values_equal if operator == "==" else not values_equal
        if operator in self.COMPARISON_OPERATORS:
            return self.compare_values(operator, left_value, right_value)
        return self.calculate(operator, left_value, right_value)

    def evaluate_logical(self, node):
        """'and' / 'or' of two expressions."""
        operator = node.operator
        left_value = self.evaluate(node.left)
        if left_value is UNKNOWN:
            # "x = x or {}" when x is unknown: use the known default
            return self.evaluate(node.right) if operator == "or" else UNKNOWN
        if operator == "or":
            return left_value if is_lua_truthy(left_value) else self.evaluate(node.right)
        return self.evaluate(node.right) if is_lua_truthy(left_value) else left_value

    @staticmethod
    def concatenate_values(left_value, right_value):
        """left .. right for strings and numbers; anything else is UNKNOWN."""
        def is_text_or_number(value):
            """True for a value that Lua can join with '..'."""
            return isinstance(value, str) or is_lua_number(value)
        if is_text_or_number(left_value) and is_text_or_number(right_value):
            return lua_value_to_text(left_value) + lua_value_to_text(right_value)
        return UNKNOWN

    @staticmethod
    def lua_values_equal(left_value, right_value):
        """Lua == : tables and functions by identity, otherwise by value and type (numbers
        of either kind compare by value)."""
        if isinstance(left_value, (dict, LuaFunction, BuiltinFunction)):
            return left_value is right_value
        return (left_value == right_value and type(left_value) is type(right_value)) or (
            is_lua_number(left_value) and is_lua_number(right_value) and left_value == right_value)

    def compare_values(self, operator, left_value, right_value):
        """< <= > >= of two numbers or two strings; anything else is UNKNOWN."""
        both_numbers = is_lua_number(left_value) and is_lua_number(right_value)
        both_strings = isinstance(left_value, str) and isinstance(right_value, str)
        if both_numbers or both_strings:
            return self.COMPARISON_OPERATORS[operator](left_value, right_value)
        return UNKNOWN

    def calculate(self, operator, left_value, right_value):
        """Arithmetic of two numbers; UNKNOWN otherwise or when it cannot be computed."""
        if not (is_lua_number(left_value) and is_lua_number(right_value)):
            return UNKNOWN
        calculation = self.ARITHMETIC_OPERATORS.get(operator)
        if calculation is None:
            return UNKNOWN
        try:
            return calculation(left_value, right_value)
        except (ZeroDivisionError, OverflowError):
            return UNKNOWN

    def evaluate_arguments(self, argument_nodes):
        """Evaluate call arguments; a trailing '...' passes every extra value along."""
        if not argument_nodes:
            return []
        argument_values = [self.evaluate(argument_node) for argument_node in argument_nodes[:-1]]
        last_argument_node = argument_nodes[-1]
        variable_arguments = self.current_variable_arguments() if last_argument_node.kind == "vararg" else None
        if variable_arguments is not None:
            argument_values.extend(variable_arguments)
        else:
            argument_values.append(self.evaluate(last_argument_node))
        return argument_values

    def evaluate_call(self, node):
        """Calls: object:method(...), dofile(...), Lua functions, library functions, and
        _("text") translations of unknown functions."""
        if node.method_name is not None:                                    # object:method(...)
            return self.evaluate_method_call(node)
        function_name = dotted_name(node.function_expression)
        if function_name == "dofile":
            return self.include_file(node.arguments[0]) if node.arguments else UNKNOWN
        function_value = self.evaluate(node.function_expression)
        # Like Lua, the arguments are always evaluated, in order, before the call - also when
        # the function itself is unknown (e.g. defined in a file outside the chosen folder).
        # That keeps every value as it was at this point of the run (an element's
        # cockpit_args.X is read now, not after a later file changed it) and runs any counter
        # passed as an argument (default_button(..., next_arg())) exactly once, here.
        argument_values = self.evaluate_arguments(node.arguments)
        if isinstance(function_value, (LuaFunction, BuiltinFunction)):
            return self.call_function_value(function_value, argument_values)
        if function_value is UNKNOWN and function_name and argument_values \
                and function_name.split(".")[-1] in TRANSLATION_FUNCTION_NAMES:
            translated_text = argument_values[0]                     # _("text") -> "text"
            return translated_text if isinstance(translated_text, str) else UNKNOWN
        return UNKNOWN

    def evaluate_method_call(self, node):
        """object:method(...) for a table or a string."""
        object_value = self.evaluate(node.function_expression)
        argument_values = self.evaluate_arguments(node.arguments)
        if isinstance(object_value, dict):
            method_value = self.index_value(object_value, node.method_name)
            return self.call_function_value(method_value, [object_value] + argument_values)
        if isinstance(object_value, str):                               # ("x"):upper()
            string_function = LUA_STANDARD_LIBRARY.get("string." + node.method_name)
            if string_function:
                return call_builtin_function(self, BuiltinFunction(node.method_name, string_function),
                                             [object_value] + argument_values)
        return UNKNOWN

    def call_function_value(self, function_value, argument_values):
        """Call a Lua or library function value with already evaluated arguments (anything else
        gives UNKNOWN)."""
        if isinstance(function_value, LuaFunction):
            return self.invoke_lua_function(function_value, argument_values)
        if isinstance(function_value, BuiltinFunction):
            return call_builtin_function(self, function_value, argument_values)
        return UNKNOWN

    def invoke_lua_function(self, lua_function, argument_values):
        """Run a Lua function for real: a new scope inside the function's captured scope,
        parameters bound to the argument values ('...' keeps the extras), the body executed, and
        the first returned value given back (nil when it returns nothing). Guards the call depth
        (MAX_CALL_DEPTH) so runaway recursion gives UNKNOWN instead of a crash."""
        if self.call_depth >= MAX_CALL_DEPTH:
            return UNKNOWN
        if self.executed_statement_count > MAX_EXECUTED_STATEMENTS:
            if not self.step_limit_reported:
                self.warnings.append("Lua statement limit reached; some values may be missing.")
                self.step_limit_reported = True
            return UNKNOWN
        definition = lua_function.definition
        call_scope = VariableScope(lua_function.captured_scope, is_function_scope=True)
        self.bind_parameters(call_scope, definition.parameter_names, argument_values)
        saved_scope, saved_uncertainty = self.current_scope, self.uncertainty_depth
        self.current_scope, self.uncertainty_depth = call_scope, 0
        self.call_depth += 1
        try:
            self.execute_block(definition.body_statements)
            return None
        except ReturnSignal as return_signal:
            return return_signal.returned_values[0] if return_signal.returned_values else None
        except BreakSignal:
            return None
        except RecursionError:
            return UNKNOWN
        finally:
            self.current_scope, self.uncertainty_depth = saved_scope, saved_uncertainty
            self.call_depth -= 1

    @staticmethod
    def bind_parameters(call_scope, parameter_names, argument_values):
        """Give each parameter its argument (nil when missing); '...' keeps the extra arguments."""
        for position, parameter_name in enumerate(parameter_names):
            if parameter_name == "...":
                call_scope.variable_arguments = tuple(argument_values[position:])
                break
            call_scope.variables[parameter_name] = argument_values[position] if position < len(argument_values) else None

    # ------------------------------------------------------------------ function return types
    def analyze_return_classes(self, definition):
        """The class(es) a function's returned element has, as written, e.g.
              return { class = {class_type.TUMB, class_type.TUMB}, ... }   -> ["class_type.TUMB", "class_type.TUMB"]
        Found through:  a returned table constructor's 'class' field;  a returned local
        variable that was given such a table, or the result of another element function
        (local element = tumbler(...) ... return element), or whose .class was set;  a
        returned call to another element function (its return classes).  [] when nothing
        shows it.
        Cached per definition: one walk over the body (nested function bodies skipped)."""
        if definition.return_classes is not None:
            return definition.return_classes
        if definition.return_classes_being_analyzed:
            return []
        definition.return_classes_being_analyzed = True
        lookup_scope = definition.first_closure_scope
        if lookup_scope is NOT_GIVEN:
            lookup_scope = None
        found_classes = ReturnClassFinder(self, definition, lookup_scope).run()
        definition.return_classes = found_classes
        definition.return_classes_being_analyzed = False
        return found_classes

    # ------------------------------------------------------------------ function parameter roles
    def analyze_parameter_roles(self, definition):
        """Which parameter of an element function is the hint / device / command / arg /
        element name, e.g.  default_button(hint_, device_, command_, arg_, ...)
            -> {0: "hint", 1: "device", 2: "command", 3: "arg"}
        Found (in source order, first finding wins) from:
          * table fields written  hint = x / device = x / action = {x} / arg = {x}   (ELEMENT_FIELD_ROLES)
            or  something.arg = x
          * elements[x] = ...                                     -> x is the element name
          * passing a parameter on to another element function     -> it takes that role
        and finally from parameter names (parameter_role_from_name).  Cached per definition."""
        if definition.parameter_roles is not None:
            return definition.parameter_roles
        if definition.roles_being_analyzed:
            return {}
        definition.roles_being_analyzed = True
        lookup_scope = definition.first_closure_scope
        if lookup_scope is NOT_GIVEN:
            lookup_scope = None
        found_roles = ParameterRoleFinder(self, definition, lookup_scope).run()
        self.add_roles_from_parameter_names(definition, found_roles)
        definition.parameter_roles = found_roles
        definition.roles_being_analyzed = False
        return found_roles

    @staticmethod
    def add_roles_from_parameter_names(definition, found_roles):
        """Parameters the body did not reveal get a role from their name, unless that role is
        already taken by another parameter."""
        roles_found_in_body = set(found_roles.values())
        for position, parameter_name in enumerate(definition.parameter_names):
            if position in found_roles or parameter_name == "...":
                continue
            role_from_name = parameter_role_from_name(parameter_name)
            if role_from_name and role_from_name not in roles_found_in_body:
                found_roles[position] = role_from_name


# ======================================================================================
# Turning the executed Lua into table rows
# ======================================================================================
def make_table_row(values_by_meaning):
    """{"command_name": "Button_1", ...} -> a full row dict using GENERATED_VALUE_COLUMN."""
    table_row = dict.fromkeys(TABLE_COLUMNS, "")
    for meaning, cell_text in values_by_meaning.items():
        column_name = GENERATED_VALUE_COLUMN.get(meaning)
        if column_name in table_row:
            table_row[column_name] = cell_text
    return table_row


def match_square_brackets(tokens):
    """One pass: index of every '[' operator -> index of its matching ']'.  O(n)."""
    matching_bracket_index = {}
    open_bracket_stack = []
    for token_index, token in enumerate(tokens):
        if token.kind != "operator":
            continue
        if token.value == "[":
            open_bracket_stack.append(token_index)
        elif token.value == "]" and open_bracket_stack:
            matching_bracket_index[open_bracket_stack.pop()] = token_index
    return matching_bracket_index


SEARCH_CHILD_ATTRIBUTES = {          # kind -> (attribute, may itself be collected) pairs, in source order
    "index": (("table_expression", False), ("key_expression", False)),
    "binary": (("left", True), ("right", True)),
    "unary": (("operand", True),),
    "parenthesized": (("inner", True),),
}


def table_search_children(node):
    """[(sub-expression, may itself be collected)] of an expression, in source order.  Only values,
    arguments and operands can be collected as tables; keys and called functions are only searched."""
    kind = node.kind
    if kind in SEARCH_CHILD_ATTRIBUTES:
        return [(getattr(node, attribute_name), is_collectable)
                for attribute_name, is_collectable in SEARCH_CHILD_ATTRIBUTES[kind]]
    if kind == "table":
        children = []
        for key_node, value_node in node.fields:
            if key_node is not None:
                children.append((key_node, False))
            children.append((value_node, True))
        return children
    if kind == "call":
        return [(node.function_expression, False)] + [(argument_node, True) for argument_node in node.arguments]
    return []


def nested_table_nodes(node, collected_tables):
    """Every table constructor inside an expression (any depth), for the Input scan."""
    for child_node, may_be_collected in table_search_children(node):
        if may_be_collected and child_node.kind == "table":
            collected_tables.append(child_node)
        nested_table_nodes(child_node, collected_tables)
    return collected_tables


class TableRowBuilder:
    """Reads the results of a LuaExecutionContext and produces table rows."""

    def __init__(self, execution_context):
        """Start a row builder for one aircraft's execution context; the prefix index and
        device lookup are built later, on first use."""
        self.context = execution_context
        self.definition_files_by_path_prefix = None     # built on first use (prefix index)
        self.scanned_file_key = None                    # file whose expressions are being turned into rows
        self.command_device_lookup = None               # (command name, number) -> its device, built once
        self.scanned_file_path = None                   # path of the file being scanned (for Source)
        self.device_number_index, self.device_number_index_key = {}, None   # see device_names_by_number
        self.definition_file_lookup = None              # (name, number) -> defining file, built once
        self.function_return_types = {}                 # function name -> its return classes
        self.element_details = {}                       # element name -> {"position_count", "position_step"}
        self.device_lookup_tables = None                # (devices by name, device names by number), built once

    # ------------------------------------------------------------------ source files (Source tab)
    def definition_file_index(self):
        """(variable's own name, number text) -> the file that defined it, for values reached
        indirectly (a metatable lookup, a local alias).  First definition wins.  Built once:
        O(numbers defined)."""
        if self.definition_file_lookup is None:
            definition_lookup = {}
            for variable_path, file_path, number in self.all_numeric_definitions():
                path_segments = split_variable_path(variable_path)
                if path_segments and isinstance(path_segments[-1], str):
                    definition_lookup.setdefault((path_segments[-1], format_number_text(number)), file_path)
            self.definition_file_lookup = definition_lookup
        return self.definition_file_lookup

    def source_file_for(self, node):
        """The file where the value of an expression was found:
             a variable / table field  -> the file that defines it (devices.RADIO ->
                                          devices.lua; device_commands.X -> the command file,
                                          even through a metatable lookup)
             anything else (a literal) -> the file being scanned, where it is written.
        None when there is no expression.  Dictionary lookups only."""
        if node is None:
            return None
        variable_path = dotted_name(node)
        if variable_path:
            definition = self.context.numeric_definitions.get(variable_path)
            if definition is not None:
                return definition[0]
            value = self.evaluated_value(node)
            if is_lua_number(value):
                defining_file = self.definition_file_index().get(
                    (variable_path.split(".")[-1], format_number_text(value)))
                if defining_file is not None:
                    return defining_file
        return self.scanned_file_path

    def device_source_file(self, device_name):
        """The file that gives a device its number (e.g. devices["RADAR"] = 52 in devices.lua)."""
        definition = self.context.numeric_definitions.get(f"devices.{device_name}") if device_name else None
        return definition[0] if definition is not None else None

    # ------------------------------------------------------------------ cell text
    def evaluated_value(self, node):
        """The value this expression had when the Lua ran (see
        LuaExecutionContext.top_level_values); evaluated now only when it was not
        remembered (e.g. code that never ran).  Never runs a counter a second time for code
        that did run.  One dictionary lookup."""
        remembered_value = self.context.top_level_values.get(
            (self.scanned_file_key, node.first_token_index, node.after_last_token_index), NOT_RECORDED)
        if remembered_value is not NOT_RECORDED:
            return remembered_value
        return self.context.evaluate(node)

    def variable_name_text(self, node):
        """Name shown for a device / command / arg:
             device_commands.Button_16 -> "Button_16", devices["RADIO"] -> "RADIO",
             anything else -> the text as written (e.g. a literal 604)."""
        if node is None:
            return ""
        if node.kind == "index":
            key_value = self.evaluated_value(node.key_expression)
            if isinstance(key_value, str):
                return key_value
        return node.raw_text

    def device_name_text(self, node):
        """Device name for the table: the device's variable name exactly as written in the
        Lua, underscores kept (devices.RADIO_PANEL -> RADIO_PANEL).  When the device is
        given another way - a plain number (device = 20) or a calculation (devices.RADIO + 1) -
        and its value belongs to exactly one entry of the devices table, that entry's name is
        used (20 -> RADIO); otherwise the text as written."""
        written_name = self.variable_name_text(node)
        if node is None or node.kind in ("name", "index", "string"):
            return written_name
        device_number = self.evaluated_value(node)
        if not is_lua_number(device_number):
            return written_name
        matching_names = self.device_names_by_number().get(device_number, ())
        return matching_names[0] if len(matching_names) == 1 else written_name

    def device_names_by_number(self):
        """device number -> [device names with that number] for the devices table, built once
        and rebuilt only when the table's size changes, so naming a device given by number is
        one dictionary lookup (not a scan of every device per element)."""
        devices_table = self.context.global_variables.get("devices")
        if not isinstance(devices_table, dict):
            return {}
        cache_key = (id(devices_table), len(devices_table))
        if self.device_number_index_key != cache_key:
            names_by_number = {}
            for device_name, number in devices_table.items():
                if isinstance(device_name, str) and is_lua_number(number):
                    names_by_number.setdefault(number, []).append(device_name)
            self.device_number_index, self.device_number_index_key = names_by_number, cache_key
        return self.device_number_index

    def number_text(self, node):
        """The value of an expression as table text ("3016"), or "" when it is not a number."""
        if node is None:
            return ""
        value = self.evaluated_value(node)
        return format_number_text(value) if is_lua_number(value) else ""

    def plain_text(self, node):
        """_("Radio Transmit") -> "Radio Transmit";  a string -> itself;  anything else -> as written."""
        value = self.evaluated_value(node)
        if isinstance(value, str):
            return value
        if node.kind == "call" and node.arguments and node.arguments[0].kind == "string":
            return node.arguments[0].value
        return node.raw_text

    @staticmethod
    def note_variable_references(node, reference_set):
        """Remember which variables an element's arg / command uses (to find arg / command files)."""
        if node is None:
            return
        if node.kind in ("name", "index"):
            full_name = dotted_name(node)
            if full_name:
                reference_set.add(full_name)
        for child_node in expression_children(node, with_function=False, with_keys=False):
            TableRowBuilder.note_variable_references(child_node, reference_set)

    def with_file_scope(self, file_path, work_function):
        """Run work_function() with the file's top-level locals visible (e.g. a local
        GEAR = device_commands.RADIO used in clickabledata.lua)."""
        saved_scope = self.context.current_scope
        self.context.current_scope = self.context.file_scopes.get(LuaExecutionContext.file_key(file_path))
        try:
            return work_function()
        finally:
            self.context.current_scope = saved_scope

    # ------------------------------------------------------------------ elements[...]
    def build_element_rows(self, clickabledata_path):
        """One pass over clickabledata.lua's tokens.  Every  elements[ ... ]  outside a
        function definition makes rows, except when a '.' follows the ']'
        (elements["X"].side = ...).  Returns (rows, number of elements[...] used)."""
        parsed_file = self.context.parsed_files.get(LuaExecutionContext.file_key(clickabledata_path))
        if parsed_file is None:
            return [], 0
        return self.with_file_scope(clickabledata_path, lambda: self.scan_element_assignments(parsed_file))

    def scan_element_assignments(self, parsed_file):
        """(see build_element_rows)  Values are read back with evaluated_value, keyed to this file."""
        self.scanned_file_key = LuaExecutionContext.file_key(parsed_file.file_path)
        self.scanned_file_path = parsed_file.file_path
        return self.scan_element_assignment_tokens(parsed_file)

    def scan_element_assignment_tokens(self, parsed_file):
        """One pass over clickabledata.lua's tokens: function bodies are skipped in one jump,
        every elements[...] (not followed by '.') is turned into rows by rows_for_element.
        Returns (rows, number of elements[...] used)."""
        tokens = parsed_file.tokens
        function_body_end_by_start = {definition.body_first_token_index: definition.body_end_token_index
                                      for definition in parsed_file.function_definitions}
        matching_bracket_index = match_square_brackets(tokens)
        expression_parser = LuaSyntaxParser(tokens, parsed_file.source_text, parsed_file.file_path,
                                            parsed_file.block_end_index, parsed_file.if_branch_indices, [])
        element_rows, element_count = [], 0
        token_index, token_count = 0, len(tokens)
        while token_index < token_count - 1:
            if token_index in function_body_end_by_start:           # skip function definitions
                token_index = function_body_end_by_start[token_index]
                continue
            if not self.starts_element_reference(tokens, token_index):
                token_index += 1
                continue
            opening_bracket_index = token_index + 1
            closing_bracket_index = matching_bracket_index.get(opening_bracket_index)
            if closing_bracket_index is None:
                break
            token_index = closing_bracket_index + 1                 # continue after the ']'
            rows_of_reference = self.rows_for_element_reference(parsed_file, expression_parser,
                                                                opening_bracket_index, closing_bracket_index)
            if rows_of_reference is not None:
                element_rows += rows_of_reference
                element_count += 1
        return element_rows, element_count

    def rows_for_element_reference(self, parsed_file, expression_parser, opening_bracket_index,
                                   closing_bracket_index):
        """The rows of one elements[...] reference (with its assigned value, when it is followed
        by '='); None for elements["X"].side = ..., which gives no row."""
        tokens = parsed_file.tokens
        following_token = tokens[min(closing_bracket_index + 1, len(tokens) - 1)]
        if following_token.kind == "operator" and following_token.value == ".":
            return None
        element_name = self.element_name_between_brackets(parsed_file, opening_bracket_index,
                                                          closing_bracket_index)
        assigned_node = None
        if following_token.kind == "operator" and following_token.value == "=":
            assigned_node = self.parse_assigned_expression(expression_parser, closing_bracket_index + 2)
        return self.rows_for_element(element_name, assigned_node)

    @staticmethod
    def starts_element_reference(tokens, token_index):
        """True when the tokens at token_index read  elements [ ."""
        token, next_token = tokens[token_index], tokens[token_index + 1]
        return (token.kind == "name" and token.value == "elements"
                and next_token.kind == "operator" and next_token.value == "[")

    @staticmethod
    def element_name_between_brackets(parsed_file, opening_bracket_index, closing_bracket_index):
        """The element's name: elements["PNT_10"] -> PNT_10; elements["A"..i] -> as written."""
        tokens = parsed_file.tokens
        inner_tokens = tokens[opening_bracket_index + 1:closing_bracket_index]
        if len(inner_tokens) == 1 and inner_tokens[0].kind == "string":
            return inner_tokens[0].value
        return " ".join(parsed_file.source_text[tokens[opening_bracket_index].end_offset:
                                                tokens[closing_bracket_index].start_offset].split())

    @staticmethod
    def parse_assigned_expression(expression_parser, token_index):
        """The expression starting at token_index, or None when it cannot be parsed."""
        try:
            return expression_parser.parse_expression_at(token_index)
        except (LuaParseError, RecursionError):
            return None

    def rows_for_element(self, element_name, assigned_node):
        """Rows for  elements[name] = <assigned_node>.
          * function call  -> Type = function name; device / commands / args from the
                              function's parameter roles (analyzed, or guessed when the
                              function's definition is not available)
          * table { ... }  -> Type = its class value(s); device / action / arg fields
          * anything else  -> Type = the expression as written
        Identical repeated commands (or args) count once; different ones get a row each,
        paired by position (2nd command with 2nd arg, or with the only arg)."""
        context = self.context
        if assigned_node is None:
            type_text, device_node, command_nodes, arg_nodes, class_nodes = "", None, [], [], []
        elif assigned_node.kind == "call" and assigned_node.method_name is None:
            type_text, device_node, command_nodes, arg_nodes = self.parts_of_function_call(element_name, assigned_node)
            class_nodes = []
        elif assigned_node.kind == "table":
            device_node, command_nodes, arg_nodes, class_nodes = self.parts_of_table(element_name, assigned_node)
            type_text = ""
        else:
            type_text, device_node, command_nodes, arg_nodes, class_nodes = assigned_node.raw_text, None, [], [], []

        for arg_node in arg_nodes:
            self.note_variable_references(arg_node, context.element_arg_references)
        for command_node in command_nodes:
            self.note_variable_references(command_node, context.element_command_references)
        command_nodes = self.single_if_all_identical(command_nodes)
        arg_nodes = self.single_if_all_identical(arg_nodes)
        return [self.element_row_at(row_position, element_name, type_text, device_node,
                                    command_nodes, arg_nodes, class_nodes)
                for row_position in range(max(len(command_nodes), len(arg_nodes), 1))]

    @staticmethod
    def single_if_all_identical(nodes):
        """Only the first node when every node has the same text (they count once)."""
        if len({node.raw_text for node in nodes}) <= 1:
            return nodes[:1]
        return nodes

    def parts_of_function_call(self, element_name, call_node):
        """(type text, device node, command nodes, arg nodes) of  elements[name] = function(...)."""
        type_text = dotted_name(call_node.function_expression) or call_node.function_expression.raw_text
        parameter_roles, parameter_names = self.roles_of_called_function(element_name, type_text, call_node)
        self.record_element_parameters(element_name, [
            (self.parameter_label(parameter_names, parameter_roles, position), argument_node)
            for position, argument_node in enumerate(call_node.arguments)])
        device_node, command_nodes, arg_nodes = self.argument_nodes_by_role(call_node.arguments, parameter_roles)
        return type_text, device_node, command_nodes, arg_nodes

    def roles_of_called_function(self, element_name, type_text, call_node):
        """({argument position: role}, parameter names) of the function an element calls: from
        its definition when known, else guessed from the arguments."""
        function_value = self.evaluated_value(call_node.function_expression)
        if isinstance(function_value, LuaFunction):
            self.record_function_details(type_text, function_value.definition, element_name, call_node)
            return (self.context.analyze_parameter_roles(function_value.definition),
                    function_value.definition.parameter_names)
        self.context.unmapped_function_names.add(type_text)
        return self.guess_parameter_roles(call_node.arguments), []   # unknown definition: no parameter names

    @staticmethod
    def argument_nodes_by_role(argument_nodes, parameter_roles):
        """(first device node, command nodes, arg nodes) among the arguments, by their roles."""
        device_node, command_nodes, arg_nodes = None, [], []
        for parameter_position in sorted(parameter_roles):
            if parameter_position >= len(argument_nodes):
                continue
            argument_node, role = argument_nodes[parameter_position], parameter_roles[parameter_position]
            if role == "device" and device_node is None:
                device_node = argument_node
            elif role == "command":
                command_nodes += expand_table_argument(argument_node)
            elif role == "arg":
                arg_nodes += expand_table_argument(argument_node)
        return device_node, command_nodes, arg_nodes

    @staticmethod
    def parameter_label(parameter_names, parameter_roles, position):
        """The name of a call's parameter: its declared name, else its role, else 'argument N'."""
        if position < len(parameter_names) and parameter_names[position] != "...":
            return parameter_names[position]
        return parameter_roles.get(position, f"argument {position + 1}")

    def parts_of_table(self, element_name, table_node):
        """(device node, command nodes, arg nodes, class nodes) of  elements[name] = { ... }."""
        named_fields = {key_node.value: value_node for key_node, value_node in table_node.fields
                        if key_node is not None and key_node.kind == "string"}
        self.record_element_parameters(element_name, list(named_fields.items()))
        class_nodes = expand_table_argument(named_fields["class"]) if "class" in named_fields else []
        command_nodes, arg_nodes = [], []
        for command_field in ("action", "stop_action"):
            if command_field in named_fields:
                command_nodes = expand_table_argument(named_fields[command_field])
                break
        if "arg" in named_fields:
            arg_nodes = expand_table_argument(named_fields["arg"])
        return named_fields.get("device"), command_nodes, arg_nodes, class_nodes

    def element_row_at(self, row_position, element_name, type_text, device_node, command_nodes, arg_nodes, class_nodes):
        """The row at row_position: the command / arg / class paired by position (or the only one)."""
        command_node = command_nodes[min(row_position, len(command_nodes) - 1)] if command_nodes else None
        arg_node = arg_nodes[min(row_position, len(arg_nodes) - 1)] if arg_nodes else None
        element_type = class_nodes[min(row_position, len(class_nodes) - 1)].raw_text if class_nodes else type_text
        element_row = make_table_row({
            "element_name": element_name,
            "element_type": element_type,
            "arg_name": self.variable_name_text(arg_node),
            "arg_number": self.arg_number_text(arg_node),
            "device_name": self.device_name_text(device_node),
            "device_number": self.number_text(device_node),
            "command_name": self.variable_name_text(command_node),
            "command_number": self.number_text(command_node),
        })
        element_row[SOURCE_FILES_MARKER] = (self.source_file_for(arg_node), self.source_file_for(device_node),
                                            self.source_file_for(command_node))
        return element_row

    def parameter_value_text(self, value_node):
        """A parameter's value as table text: translated text without _( ), numbers and words as
        their value, anything else (tables, expressions) as written."""
        if self.looks_like_text(value_node):
            return self.plain_text(value_node)
        value = self.evaluated_value(value_node)
        if isinstance(value, bool):
            return "true" if value else "false"
        if is_lua_number(value):
            return format_number_text(value)
        if isinstance(value, str):
            return value
        return value_node.raw_text

    def record_element_parameters(self, element_name, named_value_nodes):
        """Keep every parameter name and value an element was created with (a function call's
        parameters, or a table element's fields), e.g. {"hint_": "Landing Gear",
        "arg_lim_": "{0, 1}", ...}, under element_details[element_name]["parameters"]."""
        if not element_name:
            return
        parameters = {str(parameter_name): self.parameter_value_text(value_node)
                      for parameter_name, value_node in named_value_nodes}
        if parameters:
            self.element_details.setdefault(element_name, {})["parameters"] = parameters

    def record_function_details(self, function_name, definition, element_name, call_node):
        """Remember, for Build Device, what an element's function returns (its class, e.g.
        class_type.TUMB -> a Switch) and, from the call's arguments:
          * count_ (and delta_)            -> the number of positions (and the step between them)
          * value1_, value2_ and value3_   -> a 3-position switch's values (value1 = minimum,
                                              value3 = maximum); only when all three are numbers."""
        return_classes = self.context.analyze_return_classes(definition)
        if return_classes:
            self.function_return_types.setdefault(function_name, return_classes)
        element_detail, position_values = self.numeric_argument_details(definition, call_node)
        if len(position_values) == len(POSITION_VALUE_PARAMETER_NAMES):       # value1_, value2_, value3_
            element_detail["position_values"] = [position_values[name] for name in POSITION_VALUE_PARAMETER_NAMES]
        if "position_count" in element_detail or "position_values" in element_detail:
            self.element_details.setdefault(element_name, {}).update(element_detail)

    def numeric_argument_details(self, definition, call_node):
        """(details, position values) found in the numeric arguments of a call, by parameter name."""
        element_detail, position_values = {}, {}
        for parameter_name, argument_node in zip(definition.parameter_names, call_node.arguments):
            argument_value = self.evaluated_value(argument_node)
            if is_lua_number(argument_value):
                self.note_position_parameter(parameter_name.lower().strip("_"), argument_value,
                                             element_detail, position_values)
        return element_detail, position_values

    @staticmethod
    def note_position_parameter(plain_parameter_name, argument_value, element_detail, position_values):
        """Keep the value of a count_ / delta_ / valueN_ parameter."""
        if plain_parameter_name in POSITION_COUNT_PARAMETER_NAMES and argument_value >= 1:
            element_detail["position_count"] = int(argument_value)
        elif plain_parameter_name in POSITION_STEP_PARAMETER_NAMES and argument_value > 0:
            element_detail["position_step"] = argument_value
        elif plain_parameter_name in POSITION_VALUE_PARAMETER_NAMES:
            position_values[plain_parameter_name] = argument_value

    def arg_number_text(self, arg_node):
        """An element's Arg #.  For a reference into an arg table (e.g. cockpit_args.RADIO_Volume)
        the value generated for that variable is used whenever the element's own value differs
        from it: the first number the variable was given, as listed where it is defined
        (first_numeric_definitions).  Anything else: the value the Lua produced at the element."""
        generated_text = self.number_text(arg_node)
        if arg_node is None or not self.is_arg_table_reference(arg_node):
            return generated_text
        variable_definition = self.context.first_numeric_definitions.get(dotted_name(arg_node) or "")
        if variable_definition is None:
            return generated_text
        defined_text = format_number_text(variable_definition[1])
        return defined_text if defined_text != generated_text else generated_text

    def is_arg_table_reference(self, node):
        """Is this a reference into an arg table (e.g. cockpit_args.RADIO_Power_Switch)?  True when the
        table name contains 'arg', or it was defined in a file whose name contains 'arg'."""
        if node.kind != "index":
            return False
        if "arg" in (root_variable_name(node) or "").lower():
            return True
        full_name = dotted_name(node)
        if full_name and full_name in self.context.numeric_definitions:
            defining_file = self.context.numeric_definitions[full_name][0]
            return "arg" in os.path.basename(defining_file).lower()
        return False

    def guess_parameter_roles(self, argument_nodes):
        """EXTENSION POINT D.  For element functions whose definition is not available
        (e.g. a helper file outside the chosen folder).  Expected call shape:
            hint, device, command(s), arg(s), options...
        Table references are told apart by the table they come from: devices.* is the
        device, an arg table (is_arg_table_reference) is an arg, any other table reference
        after the device is a command.  When the call uses no arg table at all, the arg is
        the first plain number after the device / command, or the first calculated value
        after the command (a call such as next_arg() or an expression such as base + 7) that
        gave a number when the Lua ran - read back with evaluated_value, so a counter is not
        run a second time."""
        guessed_roles = {}
        call_uses_arg_table = any(self.is_arg_table_reference(node) for node in argument_nodes)
        for argument_position, argument_node in enumerate(argument_nodes):
            role = self.guess_argument_role(argument_node, set(guessed_roles.values()), call_uses_arg_table)
            if role is not None:
                guessed_roles[argument_position] = role
        return guessed_roles

    def guess_argument_role(self, argument_node, roles_so_far, call_uses_arg_table):
        """The role ("hint", "device", "command" or "arg") of one argument given the roles
        already guessed for the earlier ones, or None."""
        if not roles_so_far and self.looks_like_text(argument_node):
            return "hint"
        if "device" not in roles_so_far and root_variable_name(argument_node) == "devices":
            return "device"
        if "device" in roles_so_far:
            role_after_device = self.role_after_device(argument_node, roles_so_far)
            if role_after_device:
                return role_after_device
        if call_uses_arg_table or "arg" in roles_so_far:
            return None
        return self.plain_number_role(argument_node, roles_so_far)

    def role_after_device(self, argument_node, roles_so_far):
        """"arg" for a reference to the argument table, "command" for the first other indexed
        value after the device; otherwise None."""
        if self.is_arg_table_reference(argument_node):
            return "arg"
        is_other_index = argument_node.kind == "index" and root_variable_name(argument_node) != "devices"
        if "arg" not in roles_so_far and is_other_index:
            return "command"
        return None

    def plain_number_role(self, argument_node, roles_so_far):
        """"arg" for a number (or a computed number) that follows a device or command."""
        has_command = "command" in roles_so_far
        if argument_node.kind == "number" and (has_command or "device" in roles_so_far):
            return "arg"
        computed_kinds = ("call", "binary", "unary", "parenthesized")
        if (has_command and argument_node.kind in computed_kinds and not self.looks_like_text(argument_node)
                and is_lua_number(self.evaluated_value(argument_node))):
            return "arg"
        return None

    # ------------------------------------------------------------------ Input key bindings
    def build_input_binding_rows(self, input_file_paths):
        """Rows for the commands bound in the Input folder files, read two ways:
          * binding tables, e.g.
              { down = device_commands.CANOPY_Toggle, cockpit_device_id = devices.CANOPY,
                name = _('Toggle Canopy') }
            (a name, cockpit_device_id and at least one INPUT_BINDING_COMMAND_FIELDS field);
          * helper calls, e.g.
              push_button('Radio Power', device_commands.RADIO_Power, ...)
              switch_2('Radio Mode', {...}, device_commands.A, device_commands.B, ...)
            every command passed to the call becomes a row (see rows_for_input_call).
        Each row: Arg Name = the binding's name, Device / Device #, Command / Command #.
        Identical rows (keyboard and joystick profiles repeat bindings) are added once."""
        binding_rows, seen_row_texts = [], set()
        for input_file_path in input_file_paths:
            input_file_key = LuaExecutionContext.file_key(input_file_path)
            self.context.input_file_keys.add(input_file_key)
            self.context.run_lua_file(input_file_path)       # runs its dofile's (devices / commands)
            parsed_file = self.context.parsed_files.get(input_file_key)
            if parsed_file is not None:
                self.with_file_scope(input_file_path,
                                     lambda: self.scan_input_file(parsed_file, binding_rows, seen_row_texts))
        return binding_rows

    def scan_input_file(self, parsed_file, binding_rows, seen_row_texts):
        """Both Input passes over one file: binding tables, then helper calls."""
        self.scan_input_tables(parsed_file, binding_rows, seen_row_texts)
        self.scan_input_calls(parsed_file, binding_rows, seen_row_texts)

    @staticmethod
    def looks_like_text(node):
        """True for a string, a text concatenation or a translated string _("...")."""
        return node.kind == "string" or (node.kind == "binary" and node.operator == "..") or (
            node.kind == "call" and bool(node.arguments) and node.arguments[0].kind == "string"
            and (dotted_name(node.function_expression) or "").split(".")[-1] in TRANSLATION_FUNCTION_NAMES)

    def command_device_index(self):
        """(command name, Command # text) -> (device name, device number) for every command the
        aircraft defines, from where it is stored (device_for_definition_path): e.g.
        per_device_commands.RADIO.RADIO_Power = 3001
            -> ("RADIO_Power", "3001"): ("RADIO", 20).
        Device tables and arg tables are not commands.  Built once: O(numbers defined)."""
        if self.command_device_lookup is None:
            command_lookup = {}
            for variable_path, file_path, number in self.all_numeric_definitions():
                path_segments = split_variable_path(variable_path)
                if not self.is_command_path(path_segments):
                    continue
                lookup_key = (path_segments[-1], format_number_text(number))
                if lookup_key not in command_lookup:
                    command_lookup[lookup_key] = self.device_for_definition_path(variable_path)
            self.command_device_lookup = command_lookup
        return self.command_device_lookup

    @staticmethod
    def is_command_path(path_segments):
        """True for a path such as table.NAME that is not stored under devices or an arg table."""
        if len(path_segments) < 2 or not isinstance(path_segments[-1], str):
            return False
        root_name = str(path_segments[0]).lower()
        return root_name != "devices" and "arg" not in root_name

    def scan_input_calls(self, parsed_file, binding_rows, seen_row_texts):
        """Every call in the file's code - at statement level, inside table constructors
        (e.g. local binds = { push_button(...), switch_2(...), ... }) and passed as arguments,
        in nested blocks too (function bodies are skipped: they only define helpers) - and
        their commands become rows.  One walk over the syntax tree: O(nodes)."""
        found_calls = []
        self.collect_calls_in_statements(parsed_file.statements, found_calls)
        for call_node in found_calls:
            for binding_row in self.rows_for_input_call(call_node):
                row_text = tuple(binding_row[column] for column in TABLE_COLUMNS)
                if row_text not in seen_row_texts:
                    seen_row_texts.add(row_text)
                    binding_rows.append(binding_row)

    @staticmethod
    def collect_calls_in_expression(expression_node, found_calls):
        """Remember every call in an expression, at any depth (not inside function bodies)."""
        kind = expression_node.kind
        if kind == "call":
            found_calls.append(expression_node)
            for argument_node in expression_node.arguments:
                TableRowBuilder.collect_calls_in_expression(argument_node, found_calls)
        elif kind == "table":
            for _key_node, value_node in expression_node.fields:
                TableRowBuilder.collect_calls_in_expression(value_node, found_calls)
        elif kind == "binary":
            TableRowBuilder.collect_calls_in_expression(expression_node.left, found_calls)
            TableRowBuilder.collect_calls_in_expression(expression_node.right, found_calls)
        elif kind in ("unary", "parenthesized"):
            inner_node = expression_node.operand if kind == "unary" else expression_node.inner
            TableRowBuilder.collect_calls_in_expression(inner_node, found_calls)

    @staticmethod
    def nested_statement_lists(statement):
        """The statement lists directly inside a statement (if branches, loop bodies, do blocks)."""
        if statement.kind == "if":
            return [branch_statements for _condition, branch_statements in statement.branches]
        if statement.kind in ("while", "repeat", "numeric_for", "generic_for", "do"):
            return [statement.body]
        return []

    @staticmethod
    def collect_calls_in_statements(statements, found_calls):
        """Collect the calls of statements and nested blocks (not function bodies)."""
        for statement in statements:
            if statement.kind == "call":
                TableRowBuilder.collect_calls_in_expression(statement.expression, found_calls)
            elif statement.kind in ("local", "assign", "return"):
                for value_node in statement.values:
                    TableRowBuilder.collect_calls_in_expression(value_node, found_calls)
            for nested_statements in TableRowBuilder.nested_statement_lists(statement):
                TableRowBuilder.collect_calls_in_statements(nested_statements, found_calls)

    def rows_for_input_call(self, call_node):
        """Rows for one helper call such as push_button('Name', device_commands.X, ...):
          * name    - its first text argument, else the 'name' field of a table argument
          * commands - arguments (and fields of table arguments) whose value is a number the
                       aircraft defines as a command (command_device_index); one row each
          * device  - the cockpit_device_id of a table argument when given, else the device the
                       command is stored under (device_for_definition_path)."""
        name_node, device_node, candidate_nodes = self.parts_of_input_call(call_node)
        command_lookup = self.command_device_index()
        call_rows, seen_command_texts = [], set()
        binding_name = self.plain_text(name_node) if name_node is not None else ""
        for candidate_node in candidate_nodes:
            if candidate_node.raw_text in seen_command_texts:
                continue
            command_value = self.evaluated_value(candidate_node)
            if not is_lua_number(command_value):
                continue
            command_name = self.variable_name_text(candidate_node)
            command_number_text = format_number_text(command_value)
            lookup_key = (command_name, command_number_text)
            if lookup_key not in command_lookup:
                continue                                    # a number, but not a command
            seen_command_texts.add(candidate_node.raw_text)
            call_rows.append(self.input_command_row(binding_name, device_node, candidate_node, command_name,
                                                    command_number_text, command_lookup[lookup_key]))
        return call_rows

    def parts_of_input_call(self, call_node):
        """(name node, device node, nodes that may be commands) of a helper call's arguments."""
        name_node, device_node, candidate_nodes = None, None, []
        for argument_node in call_node.arguments:
            if name_node is None and self.looks_like_text(argument_node):
                name_node = argument_node
            if argument_node.kind == "index":
                candidate_nodes.append(argument_node)
            elif argument_node.kind == "table":
                table_name, table_device, table_candidates = self.table_argument_parts(argument_node)
                name_node = name_node or table_name
                device_node = device_node or table_device
                candidate_nodes += table_candidates
        return name_node, device_node, candidate_nodes

    def table_argument_parts(self, table_node):
        """(name node, device node, nodes that may be commands) of one table argument."""
        name_node = self.name_node_of_table_argument(table_node)
        device_node = self.field_value_node(table_node, ("cockpit_device_id",))
        candidate_nodes = [value_node for _key_node, value_node in table_node.fields if value_node.kind == "index"]
        return name_node, device_node, candidate_nodes

    def name_node_of_table_argument(self, table_node):
        """The 'name' field of a table argument when it is text, else None."""
        table_name_node = self.field_value_node(table_node, ("name",))
        if table_name_node is not None and self.looks_like_text(table_name_node):
            return table_name_node
        return None

    def input_command_row(self, binding_name, device_node, command_node, command_name, command_number_text,
                          command_device):
        """The row for one command of a helper call; command_device is the (device name, device
        number) the command is stored under."""
        command_source = self.source_file_for(command_node)
        if device_node is not None:
            device_text, device_number_text = self.device_name_text(device_node), self.number_text(device_node)
            device_source = self.source_file_for(device_node)
        else:
            device_name, device_number = command_device
            device_text = device_name or ""
            device_number_text = format_number_text(device_number) if device_number is not None else ""
            # a device that is only a command group (no devices entry) is found in the command file
            device_source = self.device_source_file(device_name) or (command_source if device_name else None)
        binding_row = make_table_row({
            "arg_name": binding_name,
            "device_name": device_text,
            "device_number": device_number_text,
            "command_name": command_name,
            "command_number": command_number_text,
        })
        binding_row[INPUT_ROW_MARKER] = True
        binding_row[SOURCE_FILES_MARKER] = (self.scanned_file_path if binding_name else None,
                                            device_source, command_source)
        return binding_row


    def scan_input_tables(self, parsed_file, binding_rows, seen_row_texts):
        """(see build_input_binding_rows)  Values are read back with evaluated_value."""
        self.scanned_file_key = LuaExecutionContext.file_key(parsed_file.file_path)
        self.scanned_file_path = parsed_file.file_path
        return self.scan_input_table_tokens(parsed_file, binding_rows, seen_row_texts)

    def scan_input_table_tokens(self, parsed_file, binding_rows, seen_row_texts):
        """One pass: each outermost table constructor is parsed once; the tables nested in
        it are taken from its syntax tree instead of being parsed again.  O(n)."""
        tokens = parsed_file.tokens
        table_parser = LuaSyntaxParser(tokens, parsed_file.source_text, parsed_file.file_path,
                                       parsed_file.block_end_index, parsed_file.if_branch_indices, [])
        token_index, token_count = 0, len(tokens)
        while token_index < token_count:
            token = tokens[token_index]
            if not (token.kind == "operator" and token.value == "{"):
                token_index += 1
                continue
            table_parser.position = token_index
            try:
                outer_table_node = table_parser.parse_table_constructor()
            except (LuaParseError, RecursionError):
                token_index += 1
                continue
            table_nodes = [outer_table_node] + sorted(nested_table_nodes(outer_table_node, []),
                                                      key=lambda table_node: table_node.first_token_index)
            for table_node in table_nodes:
                self.add_new_binding_rows(self.rows_for_input_binding(table_node), binding_rows, seen_row_texts)
            token_index = outer_table_node.after_last_token_index

    @staticmethod
    def add_new_binding_rows(candidate_rows, binding_rows, seen_row_texts):
        """Append the rows whose text has not been seen yet."""
        for binding_row in candidate_rows:
            row_text = tuple(binding_row[column] for column in TABLE_COLUMNS)
            if row_text not in seen_row_texts:
                seen_row_texts.add(row_text)
                binding_rows.append(binding_row)

    def rows_for_input_binding(self, table_node):
        """Rows for one Input binding table: needs name, cockpit_device_id and at least one
        command field; one row per different command (Arg Name = the binding's name)."""
        named_fields = {key_node.value: value_node for key_node, value_node in table_node.fields
                        if key_node is not None and key_node.kind == "string"}
        if "name" not in named_fields or "cockpit_device_id" not in named_fields:
            return []
        command_nodes, seen_command_texts = [], set()
        for command_field_name in INPUT_BINDING_COMMAND_FIELDS:
            command_node = named_fields.get(command_field_name)
            if command_node is not None and command_node.raw_text not in seen_command_texts:
                seen_command_texts.add(command_node.raw_text)       # identical down / up -> one row
                command_nodes.append(command_node)
        binding_name = self.plain_text(named_fields["name"])
        device_node = named_fields["cockpit_device_id"]
        binding_rows = []
        for command_node in command_nodes:
            binding_row = make_table_row({
                "arg_name": binding_name,
                "device_name": self.device_name_text(device_node),
                "device_number": self.number_text(device_node),
                "command_name": self.variable_name_text(command_node),
                "command_number": self.number_text(command_node),
            })
            binding_row[INPUT_ROW_MARKER] = True
            # the binding's name is written in the Input file itself
            binding_row[SOURCE_FILES_MARKER] = (self.scanned_file_path, self.source_file_for(device_node),
                                                self.source_file_for(command_node))
            binding_rows.append(binding_row)
        return binding_rows

    # ------------------------------------------------------------------ args mentioned in other files
    @staticmethod
    def field_value_node(table_node, field_names):
        """The value of the first field of a table constructor whose key is one of field_names
        (written  name = ...  or  ["name"] = ...), or None."""
        for key_node, value_node in table_node.fields:
            if key_node is not None and key_node.kind == "string" and key_node.value in field_names:
                return value_node
        return None

    def arg_value_node(self, value_node):
        """Where the arg is in an assigned value, or None:
             { arg = 404, ... }                  the 'arg' / 'arg_number' field
             make_lamp{ arg = 404, external_arg = 1404 } / make_lamp({ ... })   that field of a table argument
             make_lamp(404, 1404)                the argument at the position of make_lamp's parameter
                                                 named 'arg' (external_arg is never used)"""
        if value_node.kind == "table":
            return self.field_value_node(value_node, ARG_VALUE_FIELD_NAMES)
        if value_node.kind != "call":
            return None
        for argument_node in value_node.arguments:
            if argument_node.kind == "table":
                arg_node = self.field_value_node(argument_node, ARG_VALUE_FIELD_NAMES)
                if arg_node is not None:
                    return arg_node
        return self.argument_at_arg_parameter(value_node)

    def argument_at_arg_parameter(self, call_node):
        """The call's argument at the position of the called function's parameter named 'arg', or None."""
        if call_node.method_name is not None:
            return None
        function_value = self.evaluated_value(call_node.function_expression)
        if not isinstance(function_value, LuaFunction):
            return None
        for parameter_position, parameter_name in enumerate(function_value.definition.parameter_names):
            if parameter_name.lower().strip("_") in ARG_VALUE_FIELD_NAMES \
                    and parameter_position < len(call_node.arguments):
                return call_node.arguments[parameter_position]
        return None

    def arg_number_of(self, arg_node):
        """The Arg # an arg expression gives: a number, or the first number of a table such
        as {404}; None when it is not a number."""
        arg_value = self.evaluated_value(arg_node)
        if isinstance(arg_value, dict):
            arg_value = arg_value.get(1)
        return arg_value if is_lua_number(arg_value) else None

    def collect_arg_mentions(self, parsed_file):
        """Every (variable name, Arg #) found in one file's statements, nested blocks and
        function bodies included.  Values come from evaluated_value (what the Lua produced).
        One walk over the syntax tree: O(statements)."""
        self.scanned_file_key = LuaExecutionContext.file_key(parsed_file.file_path)
        self.scanned_file_path = parsed_file.file_path
        found_mentions = []
        self.visit_statements_for_arg_mentions(parsed_file.statements, found_mentions)
        return found_mentions

    def remember_arg_mention(self, found_mentions, variable_name, arg_node):
        """Keep (variable name, Arg #) when the arg expression gives a number."""
        arg_number = self.arg_number_of(arg_node)
        if variable_name and arg_number is not None:
            found_mentions.append((variable_name, arg_number))

    def visit_statements_for_arg_mentions(self, statements, found_mentions):
        """Look for args given to variables in statements, nested blocks and function bodies."""
        for statement in statements:
            kind = statement.kind
            if kind in ("local", "assign"):
                self.collect_assignment_arg_mentions(statement, found_mentions)
            elif kind in ("local_function", "function"):
                self.visit_statements_for_arg_mentions(statement.definition.body_statements, found_mentions)
            elif kind == "if":
                for _condition, branch_statements in statement.branches:
                    self.visit_statements_for_arg_mentions(branch_statements, found_mentions)
            elif kind in ("while", "repeat", "numeric_for", "generic_for", "do"):
                self.visit_statements_for_arg_mentions(statement.body, found_mentions)

    def collect_assignment_arg_mentions(self, statement, found_mentions):
        """Args given by one local / assignment statement: NAME.arg = 404, NAME = f{arg = 404},
        NAME = { arg = 404 } or NAME = f(404, ...)."""
        for target_position, target_node in enumerate(statement.targets):
            if target_position >= len(statement.values):
                continue
            value_node = statement.values[target_position]
            if target_node.kind == "index":           # NAME.arg = 404 / NAME.arg_number = 404
                key_value = self.evaluated_value(target_node.key_expression)
                if key_value in ARG_VALUE_FIELD_NAMES:
                    self.remember_arg_mention(found_mentions, self.variable_name_text(target_node.table_expression),
                                              value_node)
                    continue
            arg_node = self.arg_value_node(value_node)
            if arg_node is not None:
                self.remember_arg_mention(found_mentions, self.variable_name_text(target_node), arg_node)

    def build_arg_mention_rows(self, candidate_file_paths, existing_rows):
        """Rows for args mentioned in the aircraft's other .lua files (see ARG_MENTION_PATTERN):
        each found arg becomes a row with Arg # = its value and Arg Name = the variable's
        name (underscores kept).  A file is only parsed and run when a quick text search
        finds one of the arg words in it, so most files cost one read.  An Arg # or name
        already in the table is not added again.  Returns (rows, files that gave rows)."""
        context = self.context
        arg_number_column = GENERATED_VALUE_COLUMN.get("arg_number")
        arg_name_column = GENERATED_VALUE_COLUMN.get("arg_name")
        numbers_in_table = {row.get(arg_number_column, "") for row in existing_rows} - {""}
        names_in_table = {row.get(arg_name_column, "") for row in existing_rows} - {""}
        mention_rows, files_used = [], []
        for candidate_path in candidate_file_paths:
            parsed_file = self.parsed_file_with_arg_words(candidate_path)
            if parsed_file is None:
                continue
            file_rows = self.arg_mention_rows_of_file(candidate_path, parsed_file, numbers_in_table, names_in_table)
            mention_rows += file_rows
            if file_rows:
                files_used.append(context.relative_path(candidate_path))
        return mention_rows, files_used

    def parsed_file_with_arg_words(self, candidate_path):
        """The parsed file (run when it was not yet) if a quick text search finds an arg word
        in it, else None."""
        context = self.context
        parsed_file = context.parsed_files.get(LuaExecutionContext.file_key(candidate_path))
        try:
            source_text = parsed_file.source_text if parsed_file else read_lua_file_text(candidate_path)
        except OSError:
            return None
        if not ARG_MENTION_PATTERN.search(source_text):
            return None                                    # no arg word: never parsed or run
        context.run_lua_file(candidate_path)               # skipped when it already ran
        return context.parsed_files.get(LuaExecutionContext.file_key(candidate_path))

    def arg_mention_rows_of_file(self, candidate_path, parsed_file, numbers_in_table, names_in_table):
        """New rows for the args one file mentions; the two sets are updated with what was added."""
        file_rows = []
        for variable_name, arg_number in self.with_file_scope(
                candidate_path, lambda: self.collect_arg_mentions(parsed_file)):
            number_text = format_number_text(arg_number)
            if number_text in numbers_in_table or variable_name in names_in_table:
                continue
            numbers_in_table.add(number_text)
            names_in_table.add(variable_name)
            mention_row = make_table_row({"arg_number": number_text, "arg_name": variable_name})
            mention_row[SOURCE_FILES_MARKER] = (candidate_path, None, None)
            file_rows.append(mention_row)
        return file_rows

    # ------------------------------------------------------------------ arg / command files
    def all_numeric_definitions(self):
        """[(variable path, defining file, number)] including overwritten duplicate keys."""
        definitions = [(variable_path, file_path, number)
                       for variable_path, (file_path, number) in self.context.numeric_definitions.items()]
        return definitions + list(self.context.shadowed_numeric_definitions)

    def build_prefix_index(self):
        """variable path prefix -> files that define something under it.  With it, finding the
        file that defines e.g. device_commands.X is one dictionary lookup instead of a
        comparison with every definition.  O(total path length)."""
        prefix_index = {}
        for variable_path, file_path, number in self.all_numeric_definitions():
            file_key = os.path.normcase(file_path)
            prefix_index.setdefault(variable_path, set()).add(file_key)
            for character_position, character in enumerate(variable_path):
                if character in ".[" and character_position > 0:
                    prefix_index.setdefault(variable_path[:character_position], set()).add(file_key)
        return prefix_index

    def find_definition_files(self, clickabledata_path, element_references, file_name_words):
        """EXTENSION POINT C.  Files that count as arg / command files:
          * files that define a variable the elements use (e.g. device_commands.X), or
          * files whose name contains one of file_name_words ("arg", "command", "cmd").
        clickabledata.lua itself and Input files never count."""
        if self.definition_files_by_path_prefix is None:
            self.definition_files_by_path_prefix = self.build_prefix_index()
        definition_file_keys = set()
        for reference_path in element_references:
            definition_file_keys |= self.definition_files_by_path_prefix.get(reference_path, set())
        for processed_path in self.context.processed_file_paths:
            if any(word in os.path.basename(processed_path).lower() for word in file_name_words):
                definition_file_keys.add(os.path.normcase(processed_path))
        definition_file_keys.discard(LuaExecutionContext.file_key(clickabledata_path))
        definition_file_keys -= self.context.input_file_keys
        return definition_file_keys

    def device_for_definition_path(self, variable_path):
        """EXTENSION POINT B.  Device a command belongs to, from where it is stored:
             per_device_commands.RADIO.X -> ("RADIO", 20)   (id looked up in devices)
             device_commands[20].X            -> ("RADIO", 20)   (name looked up in devices)
             per_device_commands.UNASSIGNED.X  -> ("UNASSIGNED", 0)     (not a device -> id 0)
             device_commands.Button_1         -> (None, None)          (not grouped by device)"""
        path_segments = split_variable_path(variable_path)
        if len(path_segments) < 3:
            return None, None
        devices_table, device_name_by_number = self.device_tables()
        for path_segment in reversed(path_segments[1:-1]):
            if isinstance(path_segment, str) and is_lua_number(devices_table.get(path_segment)):
                return path_segment, devices_table[path_segment]
            if is_lua_number(path_segment) and path_segment in device_name_by_number:
                return device_name_by_number[path_segment], path_segment
        group_name = path_segments[-2]
        return (group_name if isinstance(group_name, str) else format_number_text(group_name)), 0

    def device_tables(self):
        """(devices table, {device number: device name}) - built once per aircraft, not once per command."""
        if self.device_lookup_tables is None:
            devices_table = self.context.global_variables.get("devices")
            devices_table = devices_table if isinstance(devices_table, dict) else {}
            self.device_lookup_tables = (devices_table, {
                device_number: device_name for device_name, device_number in devices_table.items()
                if is_lua_number(device_number) and isinstance(device_name, str)})
        return self.device_lookup_tables

    def build_definition_file_rows(self, clickabledata_path, existing_rows, definition_kind):
        """Rows for every number defined in the arg files (definition_kind "arg":
        Arg # + Arg Name) or command files ("command": Command # + Command, plus the
        device from device_for_definition_path).  Anything already in the table is skipped:
        commands per (Device #, Command #) when grouped by device, otherwise by name - a name
        counts as present only when its row has a number.  Several names may share a number
        (e.g. arg 999 for six lights; command 3001 in two counters): each name gets its row.
        An arg written more than once (the same key twice) uses its FIRST listed value.
        Returns (rows, files used)."""
        context = self.context
        is_command_kind = definition_kind == "command"
        element_references = context.element_command_references if is_command_kind else context.element_arg_references
        file_name_words = COMMAND_FILE_NAME_WORDS if is_command_kind else ARG_FILE_NAME_WORDS
        definition_file_keys = self.find_definition_files(clickabledata_path, element_references, file_name_words)
        if not definition_file_keys:
            return [], []
        new_rows = self.rows_from_definition_files(definition_file_keys, existing_rows, is_command_kind)
        files_used = sorted(context.relative_path(path) for path in context.processed_file_paths
                            if os.path.normcase(path) in definition_file_keys)
        return new_rows, files_used

    def rows_from_definition_files(self, definition_file_keys, existing_rows, is_command_kind):
        """The new table rows for the numbers defined in the given definition files."""
        meanings = ("command_number", "command_name") if is_command_kind else ("arg_number", "arg_name")
        names_in_table, device_command_pairs_in_table = self.numbers_already_in_table(existing_rows, meanings)
        # Args of the table the elements use get their short name (cockpit_args.RADIO_Power_Switch ->
        # RADIO_Power_Switch); args of other tables keep the prefix (external_args.CANOPY_Open).
        element_arg_tables = {split_variable_path(reference)[0]
                              for reference in self.context.element_arg_references if split_variable_path(reference)}
        new_rows = []
        for variable_path, file_path, listed_number in self.definition_candidates(definition_file_keys, is_command_kind):
            number = listed_number if is_command_kind else self.first_listed_number(variable_path, listed_number)
            definition_row = self.definition_row(variable_path, file_path, number, meanings, element_arg_tables,
                                                 names_in_table, device_command_pairs_in_table)
            if definition_row is not None:
                new_rows.append(definition_row)
        return new_rows

    @staticmethod
    def numbers_already_in_table(existing_rows, meanings):
        """(names of rows that have a number, {(Device #, number)}) of the rows already in the table."""
        number_column = GENERATED_VALUE_COLUMN.get(meanings[0])
        name_column = GENERATED_VALUE_COLUMN.get(meanings[1])
        device_number_column = GENERATED_VALUE_COLUMN.get("device_number")
        names_in_table = {existing_row.get(name_column, "") for existing_row in existing_rows
                          if existing_row.get(number_column, "").strip()} - {""}
        device_command_pairs = {(existing_row.get(device_number_column, ""), existing_row.get(number_column, ""))
                                for existing_row in existing_rows}
        return names_in_table, device_command_pairs

    def definition_candidates(self, definition_file_keys, is_command_kind):
        """(variable path, file path, number) of the defined numbers that may become rows: those
        of the definition files that are not counter variables (and, for commands, are stored in
        tables, e.g. device_commands.X or Keys.X, not plain variables)."""
        counter_variable_names = {definition.counter_variable_name for definition in self.context.function_definitions
                                  if definition.counter_variable_name}
        for variable_path, file_path, number in self.all_numeric_definitions():
            if os.path.normcase(file_path) not in definition_file_keys or variable_path in counter_variable_names:
                continue
            if is_command_kind and not re.search(r"[.\[]", variable_path):
                continue
            yield variable_path, file_path, number

    def first_listed_number(self, variable_path, number):
        """The value listed first for this arg (number itself when there is no earlier one)."""
        first_definition = self.context.first_numeric_definitions.get(variable_path)
        return number if first_definition is None else first_definition[1]

    def definition_row(self, variable_path, file_path, number, meanings, element_arg_tables,
                       names_in_table, device_command_pairs_in_table):
        """The table row for one defined number, or None when the table already has it.
        meanings = (number meaning, name meaning); the two sets are updated for a new row."""
        number_meaning, name_meaning = meanings
        is_command_kind = number_meaning == "command_number"
        number_text = format_number_text(number)
        path_segments = split_variable_path(variable_path)
        use_short_name = bool(path_segments) and (is_command_kind or path_segments[0] in element_arg_tables)
        shown_name = path_segments[-1] if use_short_name else variable_path
        shown_name = shown_name if isinstance(shown_name, str) else format_number_text(shown_name)
        values_by_meaning = {number_meaning: number_text, name_meaning: shown_name}
        device_name, device_number = self.device_for_definition_path(variable_path) if is_command_kind else (None, None)
        if device_name is not None:
            device_number_text = format_number_text(device_number)
            if (device_number_text, number_text) in device_command_pairs_in_table:
                return None
            device_command_pairs_in_table.add((device_number_text, number_text))
            values_by_meaning["device_name"] = device_name              # underscores kept
            values_by_meaning["device_number"] = device_number_text
        elif shown_name in names_in_table:
            return None
        names_in_table.add(shown_name)
        definition_row = make_table_row(values_by_meaning)
        definition_row[SOURCE_FILES_MARKER] = self.definition_source_files(is_command_kind, device_name, file_path)
        return definition_row

    def definition_source_files(self, is_command_kind, device_name, file_path):
        """(arg file, device file, command file) the row came from."""
        if not is_command_kind:
            return (file_path, None, None)
        device_source = (self.device_source_file(device_name) or file_path) if device_name is not None else None
        return (None, device_source, file_path)


# ======================================================================================
# Duplicates, per-aircraft corrections, ordering
# ======================================================================================
def source_paths_of_row(source_files):
    """([each file once, in order], [the folder of each, once]) for a row's (arg, device, command) files."""
    file_paths, folder_paths = [], []
    for source_file in source_files:                 # arg, device, command
        if source_file and source_file not in file_paths:
            file_paths.append(source_file)
            folder_path = os.path.dirname(source_file)
            if folder_path not in folder_paths:
                folder_paths.append(folder_path)
    return file_paths, folder_paths


def build_source_rows(table_rows):
    """The Source tab rows, one per table row in the same order, and removes each row's
    SOURCE_FILES_MARKER.  File Name lists the files the row's arg, device and command were
    found in, in that order, each once; Folder Path lists their folders the same way.  O(rows)."""
    source_rows = []
    for table_row in table_rows:
        file_paths, folder_paths = source_paths_of_row(table_row.pop(SOURCE_FILES_MARKER, None) or ())
        source_rows.append({
            SOURCE_FILE_PATHS_KEY: list(file_paths),        # the full paths, for the file drop-down
            "Folder Path": SOURCE_LIST_SEPARATOR.join(folder_paths),
            "File Name": SOURCE_LIST_SEPARATOR.join(os.path.basename(file_path) for file_path in file_paths),
            "Arg #": table_row.get("Arg #", ""), "Arg Name": table_row.get("Arg Name", ""),
            "Device": table_row.get("Device", ""), "Command": table_row.get("Command", ""),
            "Command #": table_row.get("Command #", ""),
        })
    return source_rows


def command_key_of_row(table_row):
    """(Command, Command #) of a row, or None when it has no Command #."""
    command_number = normalize_id_text(table_row.get(GENERATED_VALUE_COLUMN.get("command_number"), ""))
    command_name = table_row.get(GENERATED_VALUE_COLUMN.get("command_name"), "").strip()
    return (command_name, command_number) if command_number else None


def devices_by_command_key(table_rows):
    """{command key: {(device, device #): device source file}} - the devices each command is used with."""
    device_name_column = GENERATED_VALUE_COLUMN.get("device_name")
    device_number_column = GENERATED_VALUE_COLUMN.get("device_number")
    devices_by_command = {}
    for table_row in table_rows:
        key = command_key_of_row(table_row)
        device_name = table_row.get(device_name_column, "").strip()
        device_number = normalize_id_text(table_row.get(device_number_column, ""))
        if key is not None and (device_name or device_number):
            source_files = table_row.get(SOURCE_FILES_MARKER) or (None, None, None)
            devices_by_command.setdefault(key, {}).setdefault((device_name, device_number), source_files[1])
    return devices_by_command


def is_command_only_row(table_row):
    """True for a row with a Command # but no device, arg, type or note."""
    if command_key_of_row(table_row) is None:
        return False
    checked_columns = (GENERATED_VALUE_COLUMN.get("device_name"), GENERATED_VALUE_COLUMN.get("device_number"),
                       GENERATED_VALUE_COLUMN.get("arg_number"), GENERATED_VALUE_COLUMN.get("element_type"),
                       GENERATED_VALUE_COLUMN.get("element_name"))
    return not any(table_row.get(column, "").strip() for column in checked_columns)


def fill_devices_of_command_only_rows(table_rows):
    """Rows with just a command - not a cockpit element (no Type, no Note) and a Command /
    Command # but no Device, Device # or Arg # (a key binding's name may be there) - get the
    device that the other rows use with the same Command and Command #.  Element rows are
    never changed: their device is chosen inside their own function, so another row's
    device could be the wrong one.
      * exactly one device uses it   -> its Device and Device # are filled in (and, for the
                                        Source tab, the file that device was found in);
      * several different devices    -> the device is left blank (it cannot be told which).
    Two passes over the rows with one dictionary: O(rows).  Returns how many were filled."""
    device_name_column = GENERATED_VALUE_COLUMN.get("device_name")
    device_number_column = GENERATED_VALUE_COLUMN.get("device_number")
    devices_by_command = devices_by_command_key(table_rows)
    filled_count = 0
    for table_row in table_rows:
        if not is_command_only_row(table_row):
            continue
        matching_devices = devices_by_command.get(command_key_of_row(table_row), {})
        if len(matching_devices) != 1:
            continue                               # no device, or several: leave it blank
        (device_name, device_number), device_source = next(iter(matching_devices.items()))
        table_row[device_name_column] = device_name
        table_row[device_number_column] = device_number
        arg_source, _old_device_source, command_source = table_row.get(SOURCE_FILES_MARKER) or (None, None, None)
        table_row[SOURCE_FILES_MARKER] = (arg_source, device_source, command_source)
        filled_count += 1
    return filled_count


REFERENCE_TABLE_FILE_SUFFIX = " Reference Table.json"


def chosen_folder_name(chosen_folder):
    """The last folder name of a chosen folder path (either path separator), with the
    characters Windows does not allow in file names replaced by "_"; "" for a drive root."""
    folder_path = (chosen_folder or "").replace("\\", "/").rstrip("/")     # either separator
    folder_name = folder_path.rsplit("/", 1)[-1].strip()
    if folder_name.endswith(":"):
        folder_name = ""                                  # a drive root such as C:/
    return re.sub(r'[<>:"/\\|?*]', "_", folder_name)


def reference_table_file_name(chosen_folder):
    """The name Generate gives the table: the chosen folder's name + " Reference Table.json"
    (…/Aircraft Files/MyJet -> "MyJet Reference Table.json"); a drive root gives
    "Reference Table.json".  See chosen_folder_name."""
    folder_name = chosen_folder_name(chosen_folder)
    return f"{folder_name}{REFERENCE_TABLE_FILE_SUFFIX}" if folder_name else REFERENCE_TABLE_FILE_SUFFIX.strip()


def interface_file_name(module_name, prefix=None):
    """The default file name of a new interface: "DCS.<module>.hif.json" (module MyJet ->
    "DCS.MyJet.hif.json"), with the characters Windows does not allow in file names replaced
    by "_"; "" when the module is blank.  `prefix` ("DCS." or "Helios.") replaces the default
    first part of the name."""
    module_name = re.sub(r'[<>:"/\\|?*]', "_", (module_name or "").strip())
    prefix = prefix or INTERFACE_FILE_PREFIX
    return f"{prefix}{module_name}{INTERFACE_FILE_EXTENSION}" if module_name else ""


def with_interface_extension(path):
    """End an interface file path with ".hif.json": "DCS.P-51D" / "DCS.P-51D.json" /
    "DCS.P-51D.hif" -> "DCS.P-51D.hif.json"; a path already ending ".hif.json" is unchanged."""
    lower = path.lower()
    if lower.endswith(".hif.json"):
        return path
    if lower.endswith(".json"):
        path = path[:-len(".json")]
    elif lower.endswith(".hif"):
        path = path[:-len(".hif")]
    return path + INTERFACE_FILE_EXTENSION


def swap_interface_prefix(file_name, prefix):
    """Change the first part of an interface file name to `prefix` ("DCS." or "Helios."):
    "DCS.MyJet.hif.json" -> "Helios.MyJet.hif.json" and back.  A name that starts with neither
    gets the prefix put in front.  "" stays ""."""
    if not file_name:
        return ""
    for known_prefix in INTERFACE_FILE_PREFIXES:
        if file_name.lower().startswith(known_prefix.lower()):
            file_name = file_name[len(known_prefix):]
            break
    return prefix + file_name


class DeviceCommandDeduper:
    """Decides which rows repeat a (Device #, Command #) pair an earlier row already has."""

    def __init__(self):
        self.pairs_from_other_rows = set()
        self.pairs_from_bindings = set()
        self.named_bindings_seen = set()

    def is_duplicate(self, device_command_pair, binding_name, is_input_binding):
        """True when the row repeats an earlier one; otherwise the row is remembered.  Input key
        bindings are separate actions: two bindings with different names on the same device +
        command are both kept."""
        if is_input_binding:
            named_binding = (device_command_pair, binding_name)
            if device_command_pair in self.pairs_from_other_rows or named_binding in self.named_bindings_seen:
                return True
            self.named_bindings_seen.add(named_binding)
            self.pairs_from_bindings.add(device_command_pair)
            return False
        if device_command_pair in self.pairs_from_other_rows or device_command_pair in self.pairs_from_bindings:
            return True
        self.pairs_from_other_rows.add(device_command_pair)
        return False


def remove_duplicate_device_commands(table_rows):
    """Keep only the first row for each (Device #, Command #).  Rows without both numbers
    are always kept.  Input key bindings are separate actions: two bindings with different
    names on the same device + command are both kept (e.g. 'Radio On' / 'Radio Off').
    Also removes the internal Input marker.  O(r).  Returns (kept rows, number removed)."""
    device_number_column = GENERATED_VALUE_COLUMN.get("device_number")
    command_number_column = GENERATED_VALUE_COLUMN.get("command_number")
    binding_name_column = GENERATED_VALUE_COLUMN.get("arg_name")
    deduper = DeviceCommandDeduper()
    kept_rows = []
    for table_row in table_rows:
        is_input_binding = table_row.pop(INPUT_ROW_MARKER, False)
        device_command_pair = (table_row.get(device_number_column, ""), table_row.get(command_number_column, ""))
        has_both_numbers = bool(device_command_pair[0] and device_command_pair[1])
        if has_both_numbers and deduper.is_duplicate(device_command_pair, table_row.get(binding_name_column, ""),
                                                     is_input_binding):
            continue
        kept_rows.append(table_row)
    return kept_rows, len(table_rows) - len(kept_rows)


def find_aircraft_folder(file_path):
    """The aircraft folder of a file: the folder that contains 'Cockpit' (or 'Input'),
    e.g. ...\\Mods\\aircraft\\<aircraft>\\Cockpit\\Scripts\\clickabledata.lua -> ...\\<aircraft>.
    Falls back to the file's own folder when neither marker folder is in the path."""
    absolute_path = os.path.abspath(file_path)
    path_parts = absolute_path.replace("\\", "/").split("/")
    lowered_parts = [part.lower() for part in path_parts]
    for marker_folder in ("cockpit", "input"):
        if marker_folder in lowered_parts:
            marker_position = len(lowered_parts) - 1 - lowered_parts[::-1].index(marker_folder)
            if marker_position > 0:
                return os.path.normpath(absolute_path[:len("/".join(path_parts[:marker_position]))] or os.sep)
    return os.path.dirname(absolute_path)


def folder_contains(outer_folder, inner_path):
    """True when inner_path is outer_folder itself or somewhere inside it."""
    try:
        return os.path.commonpath([os.path.normcase(outer_folder), os.path.normcase(inner_path)]) == \
            os.path.normcase(outer_folder)
    except ValueError:                                   # different drives on Windows
        return False


def choose_corrections_file(corrections_paths, aircraft_file_path):
    """The TABLE_CORRECTIONS_FILE_NAME that applies to the aircraft of aircraft_file_path:
    one in the aircraft folder, inside it, or in a folder above it; the deepest wins.
    None when there is none.  O(number of corrections files)."""
    aircraft_folder = find_aircraft_folder(aircraft_file_path)
    applicable_paths = [corrections_path for corrections_path in corrections_paths
                        if folder_contains(aircraft_folder, corrections_path)
                        or folder_contains(os.path.dirname(corrections_path), aircraft_folder)]
    if not applicable_paths:
        return None
    return max(applicable_paths, key=lambda corrections_path: len(os.path.dirname(corrections_path)))


def valid_correction_entries(loaded_corrections, section_name, warnings):
    """The usable entries of one corrections section (a warning is added for a malformed one)."""
    section_entries = loaded_corrections.get(section_name, [])
    if not isinstance(section_entries, list) or not all(isinstance(entry, dict) for entry in section_entries):
        warnings.append(f"{TABLE_CORRECTIONS_FILE_NAME}: '{section_name}' must be a list of objects - ignored")
        return []
    if section_name == "change_rows":
        return [entry for entry in section_entries
                if isinstance(entry.get("where"), dict) and isinstance(entry.get("set"), dict)]
    return section_entries


def load_table_corrections(corrections_path, warnings):
    """Read a corrections file.  Returns its sections as a dict, or None (with a warning)
    when the file cannot be read or does not have the expected shape."""
    try:
        with open(corrections_path, "r", encoding="utf-8") as corrections_file:
            loaded_corrections = json.load(corrections_file)
    except (OSError, ValueError) as read_error:
        warnings.append(f"{TABLE_CORRECTIONS_FILE_NAME} ignored ({corrections_path}): {read_error}")
        return None
    if not isinstance(loaded_corrections, dict):
        warnings.append(f"{TABLE_CORRECTIONS_FILE_NAME} ignored ({corrections_path}): expected a JSON object")
        return None
    return {section_name: valid_correction_entries(loaded_corrections, section_name, warnings)
            for section_name in TABLE_CORRECTION_SECTIONS}


def row_cell_tuple(row):
    """The cell texts of a row, in column order (to tell whether two rows are the same)."""
    return tuple(row.get(column, "") for column in TABLE_COLUMNS)


def override_rows_to_add(table_corrections, existing_rows, corrections_path=None):
    """The corrections file's "add_rows" that were not generated already (marked as Input
    rows so duplicate removal treats them like key bindings).  O(rows + added rows)."""
    if not table_corrections:
        return []
    existing_row_texts = {row_cell_tuple(existing_row) for existing_row in existing_rows}
    added_rows = []
    for configured_row in table_corrections.get("add_rows", []):
        new_row = {column: str(configured_row.get(column, "")) for column in TABLE_COLUMNS}
        row_text = row_cell_tuple(new_row)
        if row_text not in existing_row_texts:
            existing_row_texts.add(row_text)
            new_row[INPUT_ROW_MARKER] = True
            new_row[SOURCE_FILES_MARKER] = (corrections_path, None, None)   # written in the corrections file
            added_rows.append(new_row)
    return added_rows


def group_correction_rules(table_corrections):
    """{(columns...): {(values...): [("remove", None) | ("set", {column: value})]}} - the rules
    grouped by the columns they test."""
    rules_by_column_group = {}
    for removal_pattern in table_corrections.get("remove_rows", []):
        column_group = tuple(sorted(removal_pattern))
        match_values = tuple(str(removal_pattern[column]) for column in column_group)
        rules_by_column_group.setdefault(column_group, {}).setdefault(match_values, []).append(("remove", None))
    for change_rule in table_corrections.get("change_rows", []):
        column_group = tuple(sorted(change_rule["where"]))
        match_values = tuple(str(change_rule["where"][column]) for column in column_group)
        rules_by_column_group.setdefault(column_group, {}).setdefault(match_values, []).append(
            ("set", change_rule["set"]))
    return rules_by_column_group


def rules_matching_row(table_row, column_group, rules_by_values):
    """The (kind, new values) rules whose column values equal this row's."""
    return rules_by_values.get(tuple(table_row.get(column, "") for column in column_group)) or []


def change_row_values(table_row, new_values):
    """Set the values a change rule gives (as text) in a row."""
    table_row.update({column: str(value) for column, value in new_values.items()})


def apply_rules_to_row(table_row, rules_by_column_group):
    """Apply every matching rule to one row: its values are changed in place.
    Returns (True when a rule removes the row, number of change rules applied)."""
    remove_this_row, changed_count = False, 0
    for column_group, rules_by_values in rules_by_column_group.items():
        for rule_kind, new_values in rules_matching_row(table_row, column_group, rules_by_values):
            if rule_kind == "remove":
                remove_this_row = True
            else:
                change_row_values(table_row, new_values)
                changed_count += 1
    return remove_this_row, changed_count


def apply_row_corrections(table_rows, table_corrections):
    """Apply "remove_rows" and "change_rows".  Rules are grouped by the columns they test, so
    every row needs one dictionary lookup per group:  O(r x number of column groups).
    Returns (rows, removed count, changed count)."""
    if not table_corrections:
        return table_rows, 0, 0
    rules_by_column_group = group_correction_rules(table_corrections)
    corrected_rows, removed_count, changed_count = [], 0, 0
    for table_row in table_rows:
        remove_this_row, row_changes = apply_rules_to_row(table_row, rules_by_column_group)
        changed_count += row_changes
        if remove_this_row:
            removed_count += 1
        else:
            corrected_rows.append(table_row)
    return corrected_rows, removed_count, changed_count


def order_generated_rows(table_rows):
    """Rows with an Arg # first, sorted by Arg #; then every other row sorted by Device #
    and Command # (blank numbers last).  Ties keep their generated order.  O(r log r)."""
    arg_number_column = GENERATED_VALUE_COLUMN.get("arg_number")
    device_number_column = GENERATED_VALUE_COLUMN.get("device_number")
    command_number_column = GENERATED_VALUE_COLUMN.get("command_number")
    infinity = float("inf")

    def number_or_last(text_value):
        """Sort key for one cell of order_generated_rows: its number, or infinity for blanks / text
        so those rows go after every numbered row."""
        number = parse_number_or_none(text_value)
        return infinity if number is None else number

    rows_with_arg = [table_row for table_row in table_rows
                     if parse_number_or_none(table_row.get(arg_number_column)) is not None]
    rows_without_arg = [table_row for table_row in table_rows
                        if parse_number_or_none(table_row.get(arg_number_column)) is None]
    rows_with_arg.sort(key=lambda table_row: parse_number_or_none(table_row.get(arg_number_column)))
    rows_without_arg.sort(key=lambda table_row: (number_or_last(table_row.get(device_number_column)),
                                                 number_or_last(table_row.get(command_number_column))))
    return rows_with_arg + rows_without_arg


# ======================================================================================
# Generate: the whole pipeline
# ======================================================================================
class GenerationResult:
    """Everything one Generate run produces (rows, mapping, warnings, counts, files, viewports)."""
    def __init__(self):
        """Everything Generate produces: the rows, the function mapping, warnings, counts per
        stage (elements, bindings, arg / command rows, duplicates, corrections), the files
        used and the viewport calls."""
        self.clickabledata_paths = []
        self.table_rows = []
        self.function_mapping = []
        self.warnings = []
        self.unmapped_function_names = set()
        self.element_count = 0
        self.files_processed = 0
        self.input_file_paths = []
        self.input_row_count = 0
        self.arg_file_paths = []
        self.arg_row_count = 0
        self.command_file_paths = []
        self.command_row_count = 0
        self.duplicate_row_count = 0
        self.corrections_file_paths = []     # table_corrections.json files that were applied
        self.arg_mention_file_paths = []     # other .lua files whose arg mentions became rows
        self.arg_mention_row_count = 0
        self.viewport_calls = []            # (text passed, file path) per try_find_assigned_viewport() call
        self.source_rows = []               # Source tab: one row per table row, same order
        self.command_only_devices_filled = 0  # command-only rows given the one device using their command
        self.file_variables = {}            # file path -> [(variable name, value text)] (Source tab)
        self.function_return_types = {}     # function name -> return classes (Build Device type)
        self.element_details = {}           # element name -> position count / step (Build Device)
        self.discovered_devices = {}        # device name -> device # text ("" when unknown), all aircraft
        self.vehicle_names = []             # first parameter of every make_flyable() call in entry.lua
        self.correction_rows_added = 0
        self.correction_rows_removed = 0
        self.correction_rows_changed = 0


# The Input folder is searched starting with its keyboard folder: those files are processed
# first, so when the keyboard and joystick profiles bind the same command, the keyboard
# binding is the one kept (and the one the Source tab names).
FIRST_INPUT_FOLDER_NAME = "keyboard"


def input_file_order(input_file_path):
    """Sort key for Input files: files inside a folder named FIRST_INPUT_FOLDER_NAME
    ('keyboard') first, then every other Input file; alphabetical within each group."""
    folder_names = [part.lower() for part in os.path.dirname(os.path.abspath(input_file_path)).replace("\\", "/").split("/")]
    return (0 if FIRST_INPUT_FOLDER_NAME in folder_names else 1, input_file_path.lower())


def categories_of_lua_search_file(lowered_file_name, is_input_folder):
    """Which lists a file found by find_aircraft_files belongs to."""
    if lowered_file_name == TABLE_CORRECTIONS_FILE_NAME.lower():
        return ["corrections"]
    if not lowered_file_name.endswith(".lua"):
        return []
    categories = ["lua"]
    if lowered_file_name == "clickabledata.lua":
        categories.append("clickabledata")
    if is_input_folder:
        categories.append("input")
    return categories


def find_aircraft_files(search_root_folder):
    """Walk the folder ONCE and sort what is found into:
         lua_file_paths        every .lua file (for resolving dofile paths)
         clickabledata_paths   every clickabledata.lua (one aircraft each)
         input_file_paths      every .lua file inside a folder named 'Input'
         corrections_paths     every TABLE_CORRECTIONS_FILE_NAME (optional hand corrections)
    The .lua list is also what the viewport search looks through."""
    paths_by_category = {"lua": [], "clickabledata": [], "input": [], "corrections": []}
    root_folder_name = os.path.basename(search_root_folder).lower()
    for folder_path, _sub_folders, file_names in os.walk(search_root_folder):
        folder_parts = [root_folder_name] + os.path.relpath(folder_path, search_root_folder).lower().replace(
            "\\", "/").split("/")
        is_input_folder = "input" in folder_parts
        for file_name in file_names:
            for category in categories_of_lua_search_file(file_name.lower(), is_input_folder):
                paths_by_category[category].append(os.path.join(folder_path, file_name))
    return (paths_by_category["lua"], sorted(paths_by_category["clickabledata"]),
            sorted(paths_by_category["input"], key=input_file_order), sorted(paths_by_category["corrections"]))


# ======================================================================================
# Viewport search:  try_find_assigned_viewport("...")
# ======================================================================================
# DCS cockpit scripts call  try_find_assigned_viewport("F4E_LEFT_MFCD")  (sometimes with a
# second, fallback name) to hook an indicator to a monitor viewport.  Generate lists the
# text passed in every such call in the folder's .lua files, for the Viewport tab.
#
# Cost: only .lua files are searched (the list comes from the single folder walk in
# find_aircraft_files), and each is opened once.  A .lua file that is really compiled Lua
# bytecode (some modules ship those) is recognised from its first few KB and skipped; a
# text file is only tokenized when a plain substring test shows it mentions the function
# at all, so the expensive work is limited to the few files that matter.
# Overall O(total size of the .lua files).
VIEWPORT_FUNCTION_NAME = "try_find_assigned_viewport"
BINARY_PROBE_SIZE = 4096                     # bytes read to decide text vs. binary


def read_text_if_it_mentions(file_path, searched_bytes):
    """Return the decoded text of a TEXT file that contains searched_bytes, else None.
    A NUL byte in the first BINARY_PROBE_SIZE bytes marks the file as binary."""
    try:
        with open(file_path, "rb") as opened_file:
            first_block = opened_file.read(BINARY_PROBE_SIZE)
            if b"\0" in first_block:
                return None                  # binary: stop reading here
            file_bytes = first_block + opened_file.read()
    except OSError:
        return None
    if searched_bytes not in file_bytes:     # fast C-level substring test
        return None
    try:
        return file_bytes.decode("utf-8-sig")
    except UnicodeDecodeError:
        return file_bytes.decode("latin-1")


def bracket_depth_change(token):
    """+1 for an opening bracket token, -1 for a closing one, 0 for any other token."""
    if token.kind != "operator":
        return 0
    if token.value in "([{":
        return 1
    return -1 if token.value in ")]}" else 0


def split_call_arguments(tokens, name_token_index):
    """The token lists of the arguments of the call that starts after tokens[name_token_index]
    (which is followed by '('); None when the call is not closed before the end of the file."""
    argument_token_lists, argument_tokens, nesting_depth = [], [], 0
    for token in tokens[name_token_index + 2:]:
        if token.kind == "end_of_file":
            return None
        depth_change = bracket_depth_change(token)
        if depth_change < 0 and nesting_depth == 0:             # the call's closing ')'
            break
        nesting_depth += depth_change
        if nesting_depth == 0 and token.kind == "operator" and token.value == ",":
            argument_token_lists.append(argument_tokens)
            argument_tokens = []
            continue
        argument_tokens.append(token)
    argument_token_lists.append(argument_tokens)
    return argument_token_lists


def argument_text(argument_tokens, source_text):
    """One call argument as text: a lone string gives its value (no quotes), anything else the
    expression as written (white space collapsed)."""
    if len(argument_tokens) == 1 and argument_tokens[0].kind == "string":
        return argument_tokens[0].value
    return " ".join(source_text[argument_tokens[0].start_offset:argument_tokens[-1].end_offset].split())


def call_argument_texts(tokens, source_text, name_token_index):
    """The arguments of one call starting at tokens[name_token_index], as a list of texts.
    A string argument gives its value (without quotes); any other argument gives the
    expression as written.  Returns None when the name is not followed by a call (e.g. a
    definition).  One pass over the call's tokens."""
    following_token = tokens[name_token_index + 1]
    if following_token.kind == "string":                       # f"NAME" call syntax
        return [following_token.value]
    if not (following_token.kind == "operator" and following_token.value == "("):
        return None
    argument_token_lists = split_call_arguments(tokens, name_token_index)
    if argument_token_lists is None:
        return None
    return [argument_text(argument_tokens, source_text) for argument_tokens in argument_token_lists
            if argument_tokens]


def follows_function_keyword(tokens, token_index):
    """True when the token after the word 'function' is at token_index (a definition, not a call)."""
    if token_index == 0:
        return False
    previous_token = tokens[token_index - 1]
    return previous_token.kind == "name" and previous_token.value == "function"


def calls_in_tokens(tokens, source_text, function_name, full_file_path):
    """[(argument texts, file path)] for every call of function_name in one file's tokens."""
    function_calls = []
    for token_index in range(len(tokens) - 1):
        token = tokens[token_index]
        if token.kind != "name" or token.value != function_name or follows_function_keyword(tokens, token_index):
            continue
        argument_texts = call_argument_texts(tokens, source_text, token_index)
        if argument_texts is not None:
            function_calls.append((argument_texts, full_file_path))
    return function_calls


def find_function_calls(file_paths, function_name):
    """Every call of function_name in the given files, in file order then source order, as
    (list of argument texts, full path of the file holding the call).  Comments are ignored
    (the Lua tokenizer drops them) and the function's own definition ('function NAME(...)')
    is not a call.  Each file is read once and only tokenized when it mentions the name."""
    searched_bytes = function_name.encode("ascii")
    function_calls = []
    for file_path in file_paths:
        source_text = read_text_if_it_mentions(file_path, searched_bytes)
        if source_text is None:
            continue
        full_file_path = os.path.abspath(file_path)              # shown in the File column
        function_calls += calls_in_tokens(tokenize_lua_source(source_text), source_text, function_name,
                                          full_file_path)
    return function_calls


def find_viewport_calls(file_paths):
    """Every call of VIEWPORT_FUNCTION_NAME in the given files, as (text passed to it - several
    arguments joined with ", " -, full path of the file holding the call), for the Viewport
    tab.  See find_function_calls."""
    return [(", ".join(argument_texts), file_path)
            for argument_texts, file_path in find_function_calls(file_paths, VIEWPORT_FUNCTION_NAME)]


def merge_viewport_calls(listed_viewport_calls, additional_viewport_calls):
    """Table > Load additional viewports: the listed calls followed by every additional call
    whose viewport text is not listed yet (a viewport is never repeated, whichever file it
    comes from).  Returns (merged calls, number added).  O(listed + additional), one set."""
    listed_viewport_texts = {viewport_text for viewport_text, _file_path in listed_viewport_calls}
    merged_calls = list(listed_viewport_calls)
    for viewport_text, file_path in additional_viewport_calls:
        if viewport_text not in listed_viewport_texts:
            listed_viewport_texts.add(viewport_text)
            merged_calls.append((viewport_text, file_path))
    return merged_calls, len(merged_calls) - len(listed_viewport_calls)


# ======================================================================================
# Vehicle search:  make_flyable('NAME', ...)  in entry.lua
# ======================================================================================
# A module's entry.lua calls make_flyable once per vehicle the module lets the player fly;
# the first parameter is the vehicle's name.  Generate lists those names (each once, in
# file then source order) for the Vehicles field of the interface header.
VEHICLE_ENTRY_FILE_NAME = "entry.lua"
VEHICLE_FUNCTION_NAME = "make_flyable"


def find_flyable_vehicle_names(lua_file_paths):
    """The first parameter of every VEHICLE_FUNCTION_NAME call in the files named
    VEHICLE_ENTRY_FILE_NAME, each name once, in file then source order.  Only those files are
    opened; O(their size)."""
    entry_file_paths = sorted(file_path for file_path in lua_file_paths
                              if os.path.basename(file_path).lower() == VEHICLE_ENTRY_FILE_NAME)
    vehicle_names = {}                                           # a dict keeps first-seen order
    for argument_texts, _file_path in find_function_calls(entry_file_paths, VEHICLE_FUNCTION_NAME):
        if argument_texts and argument_texts[0].strip():
            vehicle_names.setdefault(argument_texts[0].strip(), None)
    return list(vehicle_names)


# ======================================================================================
# Package:  gather a profile's files into one folder, ready to hand out
# ======================================================================================
# Profile > Package builds a folder named after the aircraft, zips it and saves the archive in
# Documents\Helios\Interface Editor\Profile Exports as <aircraft>.helios16 (a zip file under that extension; the
# folder itself is built in a temporary place and not kept).  The folder / archive holds
#     Helios\Images\<the chosen image folder, as it sits under Documents\Helios\Images>
#     Helios\Profiles\<every chosen profile, with its unused monitors removed>
#     Helios\Interfaces\<...>\<the chosen interface JSON and the .lua of the same name>   (optional)
#     Profile16.json           the manifest: aircraft, version, authors, the Helios version
#                              needed and one option (description) per profile
# A chosen folder / file keeps the part of its path below the matching Documents\Helios folder;
# one chosen elsewhere goes directly below the package folder of its kind.
PACKAGE_ROOT_FOLDER_NAME = "Helios"
PACKAGE_IMAGE_FOLDER_NAME = "Images"
PACKAGE_PROFILE_FOLDER_NAME = "Profiles"
PACKAGE_INTERFACE_FOLDER_NAMES = ("Interfaces", "HeliosInterfaces")
PACKAGE_MANIFEST_FILE_NAME = "Profile16.json"
PACKAGE_MANIFEST_PRODUCT = "Helios"
PACKAGE_INTERFACE_SCRIPT_EXTENSION = ".lua"
PACKAGE_ARCHIVE_EXTENSION = ".helios16"


def path_below_folder(chosen_path, base_folder):
    """The folder names from base_folder down to chosen_path, as a tuple; () when they are the
    same folder; None when chosen_path is not inside base_folder."""
    chosen_path, base_folder = os.path.abspath(chosen_path), os.path.abspath(base_folder)
    try:
        relative_path = os.path.relpath(chosen_path, base_folder)
    except ValueError:                                   # e.g. another drive
        return None
    if relative_path == os.curdir:
        return ()
    folder_names = tuple(relative_path.replace("\\", "/").split("/"))
    return None if folder_names[0] == os.pardir else folder_names


def package_image_folder_names(image_folder):
    r"""Where the chosen image folder goes in a package: Helios\Images followed by its path below
    Documents\Helios\Images (the folder's own name when it was chosen elsewhere)."""
    below_images = path_below_folder(image_folder, os.path.join(documents_folder(), *IMAGE_FOLDER_UNDER_DOCUMENTS))
    if below_images is None:
        below_images = (os.path.basename(os.path.abspath(image_folder)),)
    return (PACKAGE_ROOT_FOLDER_NAME, PACKAGE_IMAGE_FOLDER_NAME) + tuple(name for name in below_images if name)


def package_interface_folder_names(interface_path):
    r"""Where the chosen interface file goes in a package: Helios\Interfaces followed by its
    folder's path below Documents\Helios\Interfaces (Helios\Interfaces\HeliosInterfaces when
    it was chosen elsewhere or directly in the Interfaces folder)."""
    interfaces_folder = os.path.join(documents_folder(), PACKAGE_ROOT_FOLDER_NAME, PACKAGE_INTERFACE_FOLDER_NAMES[0])
    below_interfaces = path_below_folder(os.path.dirname(os.path.abspath(interface_path)), interfaces_folder)
    if not below_interfaces:
        below_interfaces = PACKAGE_INTERFACE_FOLDER_NAMES[1:]
    return (PACKAGE_ROOT_FOLDER_NAME, PACKAGE_INTERFACE_FOLDER_NAMES[0]) + tuple(below_interfaces)


def package_extra_file_folder_names(file_path):
    r"""Where an additional file goes in a package: Helios followed by the folders of its path
    below Documents\Helios (Documents\Helios\Scripts\x.lua -> Helios\Scripts); a file chosen
    from outside Documents\Helios goes directly in the package's Helios folder."""
    helios_folder = os.path.join(documents_folder(), PACKAGE_ROOT_FOLDER_NAME)
    below_helios = path_below_folder(os.path.dirname(os.path.abspath(file_path)), helios_folder)
    return (PACKAGE_ROOT_FOLDER_NAME,) + tuple(name for name in (below_helios or ()) if name)


# The script created beside every new interface (DCS.Aircraft.hif.lua with "Aircraft" replaced
# by the module): the same name as the interface file, ending ".lua" instead of ".json".
INTERFACE_SCRIPT_TEMPLATE = (
    "\r\nfunction driver.processHighImportance(mainPanelDevice)\r\n\t\r\nend\r\n\r\n\r\n\r\n"
    "function driver.processLowImportance(mainPanelDevice) --luacheck: no unused args\r\n    \r\nend")


def interface_script_path(interface_path):
    """The script that goes with an interface file: DCS.<module>.hif.json -> DCS.<module>.hif.lua."""
    return os.path.splitext(interface_path)[0] + PACKAGE_INTERFACE_SCRIPT_EXTENSION


def create_interface_script(interface_path):
    """Write the interface's script (INTERFACE_SCRIPT_TEMPLATE) beside the interface file unless
    one is already there.  Returns the script's path when it was created, else None."""
    script_path = interface_script_path(interface_path)
    if os.path.exists(script_path):
        return None
    with open(script_path, "w", encoding="utf-8", newline="") as handle:
        handle.write(INTERFACE_SCRIPT_TEMPLATE)
    return script_path


def interface_files_to_package(interface_path):
    """The chosen interface JSON file and, when it exists beside it, the script of the same
    name with PACKAGE_INTERFACE_SCRIPT_EXTENSION (MyInterface.json -> MyInterface.lua)."""
    script_path = interface_script_path(interface_path)
    return [interface_path] + ([script_path] if os.path.isfile(script_path) else [])


def package_folder_name(aircraft):
    """The package's name (the archive is <name>.helios16): the Aircraft entered, with the
    characters Windows does not allow in names replaced by "_" and trailing dots and spaces
    dropped ("" when blank)."""
    return re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", aircraft).strip(" .")


# The installer message of the manifest (Profile16.json).  {Authors}, {Aircraft}, {Version} and
# {Minimum} are replaced by what was entered in the Package dialog and {Release Date} by the
# day of packaging, written as an international (ISO 8601, year-month-day) date.
PACKAGE_MESSAGE_TEMPLATE = (
    "\tAircraft:\t\t{Authors} {Aircraft} Version {Version}\n"
    "\tRequirements:\tHelios {Minimum} or above\n"
    "\tAspect Ratio:\t16:9\n"
    "\tDefault Size:\t1920x1080\n"
    "\tRelease Date:\t{Release Date}")


def package_release_date():
    """Today's date in the international format, year-month-day (2026-11-04)."""
    return datetime.now().strftime("%Y-%m-%d")


def package_message(aircraft, version, authors, minimum_version, release_date):
    """PACKAGE_MESSAGE_TEMPLATE with its {placeholders} filled in."""
    values = {"Authors": ", ".join(authors), "Aircraft": aircraft, "Version": version,
              "Minimum": minimum_version, "Release Date": release_date}
    message = PACKAGE_MESSAGE_TEMPLATE
    for placeholder, value in values.items():
        message = message.replace("{" + placeholder + "}", value)
    return message


PACKAGE_DESCRIPTION_WIDTH = 80          # a description line is cut at the first space after this many characters


def wrap_description(description, width=PACKAGE_DESCRIPTION_WIDTH):
    """The description with a line break at the first white space found after `width`
    characters of a line (the line may therefore run a little past `width`, but a word is never
    split).  A line of `width` characters or fewer is left alone, and line breaks already in
    the text are kept."""
    wrapped_lines = []
    for line in description.split("\n"):
        while len(line) > width:
            break_at = next((position for position in range(width, len(line)) if line[position].isspace()), None)
            if break_at is None:
                break
            wrapped_lines.append(line[:break_at].rstrip())
            line = line[break_at:].lstrip()
        wrapped_lines.append(line)
    return "\n".join(wrapped_lines)


def build_package_manifest(aircraft, version, authors_text, minimum_version, profile_paths, descriptions,
                           release_date=None):
    """The contents of PACKAGE_MANIFEST_FILE_NAME: aircraft, version, the authors (the text
    split on commas), the Helios version needed and one choice - its message built from
    PACKAGE_MESSAGE_TEMPLATE with today's date (or release_date) - with an option per profile:
    its description (the version number when none was typed), and in "Excludes" the package
    paths of the other profiles (the ones not installed when that option is picked; empty when
    there is only one profile)."""
    authors = [author.strip() for author in authors_text.split(",") if author.strip()]
    package_profile_paths = ["/".join((PACKAGE_ROOT_FOLDER_NAME, PACKAGE_PROFILE_FOLDER_NAME, os.path.basename(path)))
                             for path in profile_paths]
    return {
        "Aircraft": aircraft.strip(),
        "Version": version.strip(),
        "Authors": authors,
        "License": None,
        "VersionsRequired": [{"Product": PACKAGE_MANIFEST_PRODUCT, "Minimum": minimum_version.strip()}],
        "Choices": [{
            "Message": package_message(aircraft.strip(), version.strip(), authors, minimum_version.strip(),
                                       release_date or package_release_date()),
            "Options": [{"Description": wrap_description(description.strip() or version.strip()),
                         "Excludes": [other_path for other_position, other_path in enumerate(package_profile_paths)
                                      if other_position != position]}
                        for position, description in enumerate(descriptions)],
        }],
    }


def manifest_entries(container, key):
    """container[key] as a list of its dict entries ([] when missing or of another kind)."""
    entries = container.get(key)
    return [entry for entry in entries if isinstance(entry, dict)] if isinstance(entries, list) else []


def manifest_authors_text(authors):
    """The manifest's "Authors" value as comma separated text, or None when it has none."""
    if isinstance(authors, list):
        return ", ".join(str(author) for author in authors)
    return None if authors is None else str(authors)


def manifest_basic_fields(manifest):
    """{"aircraft": ..., "version": ...} text of the fields a manifest holds."""
    return {field_key: str(manifest[manifest_key])
            for field_key, manifest_key in (("aircraft", "Aircraft"), ("version", "Version"))
            if manifest.get(manifest_key) is not None}


def read_package_manifest(manifest_path):
    """Read a manifest file (the PACKAGE_MANIFEST_FILE_NAME layout, see build_package_manifest)
    back into the Package dialog's inputs.  Returns ({"aircraft", "version", "authors" (comma
    separated), "minimum_version"} - only the ones the file holds -, [the options'
    descriptions, in order]).  The minimum version is the PACKAGE_MANIFEST_PRODUCT entry of
    "VersionsRequired" (else its first entry); the descriptions come from the first choice
    (the message is not read: it is rebuilt from the template at every packaging).  Raises OSError / ValueError when the file cannot be read or is not such a file."""
    with open(manifest_path, "r", encoding="utf-8-sig") as manifest_file:
        manifest = json.load(manifest_file)                      # JSONDecodeError is a ValueError
    if not isinstance(manifest, dict):
        raise ValueError("the file does not hold package data")
    field_texts = manifest_basic_fields(manifest)
    authors_text = manifest_authors_text(manifest.get("Authors"))
    if authors_text is not None:
        field_texts["authors"] = authors_text
    minimum_version = manifest_minimum_version(manifest)
    if minimum_version is not None:
        field_texts["minimum_version"] = minimum_version
    descriptions = []
    for choice in manifest_entries(manifest, "Choices")[:1]:
        descriptions = [str(option.get("Description") or "") for option in manifest_entries(choice, "Options")]
    return field_texts, descriptions


def manifest_minimum_version(manifest):
    """The Minimum of the PACKAGE_MANIFEST_PRODUCT entry of "VersionsRequired" (else of its
    first entry) as text, or None."""
    required_versions = manifest_entries(manifest, "VersionsRequired")
    helios_versions = [entry for entry in required_versions if entry.get("Product") == PACKAGE_MANIFEST_PRODUCT]
    for version_entry in (helios_versions or required_versions)[:1]:
        if version_entry.get("Minimum") is not None:
            return str(version_entry["Minimum"])
    return None


# ── Package: only the images the profile refers to ──────────────────────────────────
# While packaging, each chosen profile (the Helios profile file itself) is searched for every
# entry that ends in ".png".  A .png in the chosen image folder that no profile entry refers to
# is left out of the package, and so is a folder that would be left empty.  An entry whose
# image is not in the chosen image folder pauses the packaging (see MissingImagesDialog), which
# shows the Name of its control.  Files that are not .png are always packaged.
IMAGE_REFERENCE_PATTERN = re.compile(r"[^<>\"'|*?\r\n=]+?\.png", re.IGNORECASE)


def read_profile_text(profile_path):
    """The text of a profile file (UTF-8 with or without a byte order mark, UTF-16, else Windows-1252)."""
    with open(profile_path, "rb") as profile_file:
        data = profile_file.read()
    for encoding in ("utf-8-sig", "utf-16", "cp1252"):
        try:
            text = data.decode(encoding)
        except UnicodeError:
            continue
        if "\x00" not in text:
            return text
    return data.decode("latin-1")


class ImageReferenceCollector:
    """Collects (control name, image path) pairs without repeats, in the order found."""

    def __init__(self):
        self.references = []
        self.seen_keys = set()

    def add(self, control_name, image_path):
        """Record one image path used by a control, once; Helios' own {Helios} images are skipped."""
        image_path = image_path.strip()
        if image_path.lower().startswith("{helios}"):
            return                         # Helios' own images are not packaged or checked
        key = (control_name, image_path.lower())
        if image_path and key not in self.seen_keys:
            self.seen_keys.add(key)
            self.references.append((control_name, image_path))

    def read_xml_element(self, element, control_name):
        """Collect the .png values of an element and (recursively) its children."""
        control_name = self.control_name_of(element, control_name)
        for value in list(element.attrib.values()) + [element.text or ""]:
            if value.strip().lower().endswith(".png"):
                self.add(control_name, value)
        for child in element:
            self.read_xml_element(child, control_name)

    @staticmethod
    def control_name_of(element, enclosing_control_name):
        """The Name of a Control element (when it has a non-empty one), else the enclosing name."""
        if element.tag.rsplit("}", 1)[-1] != "Control":
            return enclosing_control_name
        own_name = next((value for key, value in element.attrib.items()
                         if key.rsplit("}", 1)[-1] == "Name" and value.strip()), None)
        return enclosing_control_name if own_name is None else own_name.strip()

    def scan_text(self, profile_text):
        """Not well-formed XML: walk the text, keeping the open <Control ... Name="..."> tags."""
        token_pattern = re.compile(r"<Control\b[^>]*>|</Control\s*>|" + IMAGE_REFERENCE_PATTERN.pattern, re.IGNORECASE)
        open_controls = []                       # names of the controls the scan is inside
        for token in token_pattern.finditer(profile_text):
            self.scan_token(token.group(0), open_controls)

    def scan_token(self, token_text, open_controls):
        """Handle one match: a Control tag opens or closes a control, anything else is an image reference."""
        lowered_text = token_text.lower()
        if lowered_text.startswith("</control"):
            if open_controls:
                open_controls.pop()
        elif lowered_text.startswith("<control"):
            self.open_control_tag(token_text, open_controls)
        else:
            self.add(open_controls[-1] if open_controls else "", token_text)

    @staticmethod
    def open_control_tag(tag_text, open_controls):
        """A <Control ...> tag: note its Name (the enclosing control's name when it has none);
        a self-closing tag opens nothing."""
        name_pattern = re.compile(r"\bName\s*=\s*(?:\"([^\"]*)\"|'([^']*)')")
        name_match = name_pattern.search(tag_text)
        name = ((name_match.group(1) or name_match.group(2) or "").strip() if name_match else "")
        if not tag_text.rstrip().endswith("/>"):
            open_controls.append(name or (open_controls[-1] if open_controls else ""))


def image_references_in_profile(profile_text):
    """[(control name, image path)] for every entry of a profile that ends in ".png", in file
    order and without repeats.  The control name is the Name value of the <Control TypeIdentifier=""
    Name="..."> the entry sits in (the nearest one when controls are nested; "" when there is none).
    Read as XML when possible, else by scanning the text."""
    collector = ImageReferenceCollector()
    try:
        import xml.etree.ElementTree as element_tree
        root = element_tree.fromstring(profile_text.lstrip("﻿").encode("utf-8"))
    except Exception:
        root = None
    if root is not None:
        collector.read_xml_element(root, "")
    else:
        collector.scan_text(profile_text)
    return collector.references


def image_path_segments(path_text):
    """A path as lower-case folder / file names (either slash), without empty or '.' parts."""
    return [part for part in path_text.replace("\\", "/").lower().split("/") if part not in ("", ".")]


def image_folder_segments(current_folder, image_folder):
    """(lower-case key segments, segments to show) of a folder below the image folder."""
    if os.path.abspath(current_folder) == os.path.abspath(image_folder):
        return [], []
    relative_folder = os.path.relpath(current_folder, image_folder)
    key_segments = image_path_segments(relative_folder)
    if not key_segments:
        return key_segments, []
    shown_segments = [part for part in relative_folder.replace("/", "\\").split("\\") if part not in ("", ".")]
    return key_segments, shown_segments


def index_package_images(image_folder, image_prefix):
    """Every .png below image_folder as ({"a/b/c.png": file path}, {file path: pathway to show}).
    The key starts with image_prefix (the folder's own place below Helios\\Images)."""
    files_by_key = {}
    shown_paths = {}
    for current_folder, _sub_folders, file_names in os.walk(image_folder):
        below_folder, shown_below = image_folder_segments(current_folder, image_folder)
        for file_name in (name for name in file_names if name.lower().endswith(".png")):
            key = "/".join([part.lower() for part in image_prefix] + below_folder + [file_name.lower()])
            full_path = os.path.normcase(os.path.abspath(os.path.join(current_folder, file_name)))
            files_by_key[key] = full_path
            shown_paths[full_path] = "\\".join(list(image_prefix) + shown_below + [file_name])
    return files_by_key, shown_paths


def match_image_references(references, files_by_key):
    """(files the references point to, [(control name, image path)] with no file).  A reference
    may start above Helios\\Images, so every tail of its path is tried."""
    allowed, missing, missing_seen = set(), [], set()
    for control_name, image_path in references:
        segments = image_path_segments(image_path)
        found = None
        for start in range(len(segments)):
            found = files_by_key.get("/".join(segments[start:]))
            if found:
                break
        if found:
            allowed.add(found)
        elif (control_name, image_path.lower()) not in missing_seen:
            missing_seen.add((control_name, image_path.lower()))
            missing.append((control_name, image_path))
    return allowed, missing


def analyze_package_images(image_folder, profile_paths):
    r"""Compare the images to be packaged with the images the chosen profiles refer to.
    Returns a dict:
      "allowed"    set of normalised paths of the .png files to package, or None when every
                   file is packaged (a profile could not be read, or the profiles refer to no .png);
      "missing"    [(control name, image path)] a profile refers to that is not in the chosen
                   image folder;
      "unreadable" the profiles that could not be read;
      "left_out"   how many .png files are left out;
      "left_out_paths" their pathways (below Helios\\Images), sorted.
    A reference matches a file when the file's path below Helios\Images (the image folder's
    own place below it plus the file's place in the folder) is the end of the reference."""
    image_prefix = list(package_image_folder_names(image_folder)[2:])      # below Helios\Images
    files_by_key, shown_paths = index_package_images(image_folder, image_prefix)
    result = {"allowed": None, "missing": [], "unreadable": [], "left_out": 0, "left_out_paths": []}
    references = []
    for profile_path in profile_paths:
        try:
            references += image_references_in_profile(read_profile_text(profile_path))
        except OSError:
            result["unreadable"].append(profile_path)
    if result["unreadable"] or not references:
        return result                                 # nothing to compare with: package every image
    allowed, result["missing"] = match_image_references(references, files_by_key)
    result["allowed"] = allowed
    result["left_out"] = len(files_by_key) - len(allowed)
    result["left_out_paths"] = sorted(shown_paths[path] for path in set(files_by_key.values()) - allowed)
    return result


class LeftOutImagesDialog(tk.Toplevel):
    """Lists the image pathways that were left out of a finished package."""

    def __init__(self, parent, paths):
        super().__init__(parent)
        self.title("Images Left Out")
        self.transient(parent)
        ttk.Label(self, text=f"{len(paths)} image(s) were not referenced by the profile and were left out:"
                  ).pack(anchor="w", padx=10, pady=(10, 4))
        body = ttk.Frame(self)
        body.pack(fill="both", expand=True, padx=10)
        listing = tk.Listbox(body, width=80, height=min(max(len(paths), 4), 20), activestyle="none")
        scroll_y = ttk.Scrollbar(body, orient="vertical", command=listing.yview)
        scroll_x = ttk.Scrollbar(body, orient="horizontal", command=listing.xview)
        listing.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
        listing.grid(row=0, column=0, sticky="nsew")
        scroll_y.grid(row=0, column=1, sticky="ns")
        scroll_x.grid(row=1, column=0, sticky="ew")
        body.columnconfigure(0, weight=1)
        body.rowconfigure(0, weight=1)
        for path in paths:
            listing.insert("end", path)
        ttk.Button(self, text="OK", command=self.destroy).pack(pady=10)
        self.bind("<Escape>", lambda _event: self.destroy())
        center_over(parent.master if parent.master is not None else parent, self)   # middle of the main window
        self.grab_set()
        self.wait_window(self)


def copy_image_folder(image_folder, image_target, allowed_png_files=None):
    """Copy the image folder into the package.  With allowed_png_files (from
    analyze_package_images) a .png that is not in the set is left out, and so is every folder
    that would be left without a file; other files are always copied."""
    if allowed_png_files is None:
        shutil.copytree(image_folder, image_target, dirs_exist_ok=True)
        return
    for current_folder, _sub_folders, file_names in os.walk(image_folder):
        relative_folder = os.path.relpath(current_folder, image_folder)
        target_folder = image_target if relative_folder == "." else os.path.join(image_target, relative_folder)
        for file_name in file_names:
            source_path = os.path.join(current_folder, file_name)
            if file_name.lower().endswith(".png") and \
                    os.path.normcase(os.path.abspath(source_path)) not in allowed_png_files:
                continue
            os.makedirs(target_folder, exist_ok=True)         # only a folder that gets a file
            shutil.copy2(source_path, os.path.join(target_folder, file_name))


class MissingImagesDialog(tk.Toplevel):
    """Packaging pauses here: images the profile refers to that are not in the
    chosen image folder, each with the name of its control.  Continue packages without them;
    Cancel stops.  result is True to continue."""

    def __init__(self, parent, missing):
        super().__init__(parent)
        self.result = False
        self.title("Missing Images")
        self.configure(bg=PANEL_BG)
        self.transient(parent)
        content = tk.Frame(self, bg=PANEL_BG, padx=14, pady=12)
        content.pack(fill="both", expand=True)
        tk.Label(content, text=f"{len(missing)} image{'s' if len(missing) != 1 else ''} in the profile "
                               "cannot be found in the selected image folder:", bg=PANEL_BG, fg=TEXT_PRI,
                 font=FONT_HEAD, anchor="w").pack(fill="x", pady=(0, 8))
        table_frame = tk.Frame(content, bg=PANEL_BG)
        table_frame.pack(fill="both", expand=True)
        view = ttk.Treeview(table_frame, columns=("name", "path"), show="headings", height=12)
        view.heading("name", text="Name", anchor=tk.W)
        view.heading("path", text="Image Pathway", anchor=tk.W)
        view.column("name", width=220, anchor=tk.W)
        view.column("path", width=520, anchor=tk.W)
        scroll = ttk.Scrollbar(table_frame, orient="vertical", command=view.yview)
        view.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        view.pack(side="left", fill="both", expand=True)
        for control_name, image_path in missing:
            view.insert("", tk.END, values=(control_name, image_path))
        buttons = tk.Frame(content, bg=PANEL_BG)
        buttons.pack(fill="x", pady=(10, 0))
        tk.Button(buttons, text="Continue Packaging", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat",
                  padx=14, pady=5, cursor="hand2", command=lambda: self.finish(True)).pack(side="left")
        tk.Button(buttons, text="Cancel", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat",
                  padx=14, pady=5, cursor="hand2", command=lambda: self.finish(False)).pack(side="left", padx=(8, 0))
        self.protocol("WM_DELETE_WINDOW", lambda: self.finish(False))
        self.bind("<Escape>", lambda _event: self.finish(False))
        center_over(parent.master if parent.master is not None else parent, self)   # middle of the main window
        self.grab_set()

    def finish(self, answer):
        """Store the chosen answer and close the dialog."""
        self.result = answer
        self.destroy()


def write_package(package_folder, image_folder, profile_paths, interface_path, manifest, extra_file_paths=(),
                  allowed_png_files=None):
    """Build the package in package_folder (created when missing; files already there with the
    same names are replaced): the image folder with everything in it, the profiles - each put
    through Monitor Removal (remove_unused_monitors_from_file) on its way in, the chosen
    files themselves are not changed -, the optional interface file with its script, and the
    manifest in the package's root.  extra_file_paths are optional additional files, each
    copied under its own path below Documents\\Helios (package_extra_file_folder_names).
    Returns the number of files written.  Raises OSError on a file problem."""
    image_target = os.path.join(package_folder, *package_image_folder_names(image_folder))
    copy_image_folder(image_folder, image_target, allowed_png_files)
    file_count = sum(len(file_names) for _folder, _sub_folders, file_names in os.walk(image_target))
    profile_target = os.path.join(package_folder, PACKAGE_ROOT_FOLDER_NAME, PACKAGE_PROFILE_FOLDER_NAME)
    os.makedirs(profile_target, exist_ok=True)
    for profile_path in profile_paths:                           # silently: no message per profile
        remove_unused_monitors_from_file(profile_path, os.path.join(profile_target, os.path.basename(profile_path)))
    file_count += len(profile_paths)
    if interface_path:
        interface_target = os.path.join(package_folder, *package_interface_folder_names(interface_path))
        os.makedirs(interface_target, exist_ok=True)
        for file_path in interface_files_to_package(interface_path):
            shutil.copy2(file_path, os.path.join(interface_target, os.path.basename(file_path)))
            file_count += 1
    for file_path in extra_file_paths:
        extra_target = os.path.join(package_folder, *package_extra_file_folder_names(file_path))
        os.makedirs(extra_target, exist_ok=True)
        shutil.copy2(file_path, os.path.join(extra_target, os.path.basename(file_path)))
        file_count += 1
    with open(os.path.join(package_folder, PACKAGE_MANIFEST_FILE_NAME), "w", encoding="utf-8") as manifest_file:
        json.dump(manifest, manifest_file, indent=4, ensure_ascii=False)
    return file_count + 1


def zip_folder(folder_path, archive_path, report_progress=None):
    """Zip everything inside folder_path into archive_path (compressed; the paths in the
    archive are relative to folder_path, with "/" between folder names, so the folder's own
    contents sit in the archive's root).  One walk of the folder lists the files; after each
    file is added report_progress(files zipped, files in all) is called, when given (it is
    also called once with 0 before the first file).  Raises OSError."""
    file_paths = [os.path.join(current_folder, file_name)
                  for current_folder, _sub_folders, file_names in os.walk(folder_path) for file_name in file_names]
    if report_progress is not None:
        report_progress(0, len(file_paths))
    with zipfile.ZipFile(archive_path, "w", zipfile.ZIP_DEFLATED) as archive:
        for zipped_count, file_path in enumerate(file_paths, start=1):
            archive.write(file_path, os.path.relpath(file_path, folder_path).replace("\\", "/"))
            if report_progress is not None:
                report_progress(zipped_count, len(file_paths))


def write_package_archive(archive_path, image_folder, profile_paths, interface_path, manifest, report_progress=None,
                          extra_file_paths=(), allowed_png_files=None):
    """Build the package folder (write_package) in a temporary folder, zip it and save the zip
    as archive_path (replacing a file of that name); the temporary folder is removed.
    report_progress, when given, follows the zipping (see zip_folder).
    Returns the number of files packaged.  Raises OSError on a file problem."""
    with tempfile.TemporaryDirectory() as temporary_folder:
        package_folder = os.path.join(temporary_folder, "package")
        file_count = write_package(package_folder, image_folder, profile_paths, interface_path, manifest,
                                   extra_file_paths, allowed_png_files)
        temporary_archive = os.path.join(temporary_folder, "package.zip")
        zip_folder(package_folder, temporary_archive, report_progress)
        shutil.move(temporary_archive, archive_path)             # only a finished archive is saved
    return file_count


# ======================================================================================
# Monitor Removal:  drop the unused monitors of a Helios profile
# ======================================================================================
# A Helios profile lists every monitor of the PC it was made on inside <Monitors>.  A
# monitor whose <Children> holds no control is unused.  Monitor Removal
#   1. removes every unused <Monitor>,
#   2. moves every monitor that is kept to Location 0,0,
#   3. renumbers the "Visual;Monitor N" references (bindings) to the kept monitors' new
#      numbers (a reference to a removed monitor becomes Monitor 1).
# The profile is edited as text, so everything else in the file (layout, line ends,
# declaration) stays byte for byte as it was.  One pass over the <Monitors> section's
# Monitor tags plus one pass over the references: O(file size).
MONITOR_TAG_PATTERN = re.compile(r"<(/?)Monitor(?:\s[^>]*?)?(/?)>")
MONITOR_LIST_START_PATTERN = re.compile(r"<Monitors(?:\s[^>]*)?>")
MONITOR_LIST_END_TAG = "</Monitors>"
MONITOR_CHILDREN_PATTERN = re.compile(r"<Children(?:\s[^>]*?)?(?:/>|>(\s*)(</Children>)?)")
MONITOR_LOCATION_PATTERN = re.compile(r"(<Location>)[^<]*(</Location>)")
MONITOR_REFERENCE_PATTERN = re.compile(r"(Visual;Monitor )(\d+)")
MONITOR_KEPT_LOCATION = "0,0"


class MonitorBlockScanner:
    """Follows the <Monitor> tags inside <Monitors> and records the outermost blocks."""

    def __init__(self):
        self.monitor_blocks = []
        self.nesting_depth = 0
        self.block_start = 0

    def feed(self, tag_match):
        """Take the next opening, closing or self-closing Monitor tag."""
        is_closing_tag, is_self_closing = bool(tag_match.group(1)), bool(tag_match.group(2))
        if is_closing_tag:
            self.nesting_depth = max(0, self.nesting_depth - 1)
            if self.nesting_depth == 0:
                self.monitor_blocks.append((self.block_start, tag_match.end()))
        elif self.nesting_depth == 0:
            self.block_start = tag_match.start()
            if is_self_closing:
                self.monitor_blocks.append((self.block_start, tag_match.end()))
            else:
                self.nesting_depth = 1
        elif not is_self_closing:
            self.nesting_depth += 1


def find_monitor_blocks(profile_text):
    """The (start, end) text offsets of every <Monitor>…</Monitor> directly inside the
    profile's <Monitors> list, in order.  Monitor tags nested deeper are part of their
    outer block.  Empty list when the profile has no <Monitors>.  One pass over the tags."""
    list_start = MONITOR_LIST_START_PATTERN.search(profile_text)
    if list_start is None:
        return []
    list_end = profile_text.find(MONITOR_LIST_END_TAG, list_start.end())
    if list_end < 0:
        list_end = len(profile_text)
    scanner = MonitorBlockScanner()
    for tag_match in MONITOR_TAG_PATTERN.finditer(profile_text, list_start.end(), list_end):
        scanner.feed(tag_match)
    return scanner.monitor_blocks


def monitor_children_match(profile_text, block_start, block_end):
    """The match of a monitor block's own <Children> tag (its first one), or None; group 2 or
    a self-closing tag means the monitor holds no control."""
    return MONITOR_CHILDREN_PATTERN.search(profile_text, block_start, block_end)


def monitor_is_unused(children_match):
    """True when a monitor has no control: it has no <Children>, or that element is empty
    (<Children /> or <Children></Children>)."""
    return (children_match is None or children_match.group(0).endswith("/>")
            or children_match.group(2) is not None)


def whole_line_span(profile_text, block_start, block_end):
    """(start, end) of a monitor block widened to the whole lines it fills (the indent before it
    and the line end after it), unless other text shares those lines."""
    line_start = profile_text.rfind("\n", 0, block_start) + 1
    if profile_text[line_start:block_start].strip():
        line_start = block_start
    line_end = profile_text.find("\n", block_end)
    line_end = block_end if line_end < 0 or profile_text[block_end:line_end].strip() else line_end + 1
    return line_start, line_end


def remove_unused_monitors(profile_text):
    """Monitor Removal on the text of a Helios profile (see the notes above).  Returns
    (new text, number of monitors removed, number kept).  The text is returned unchanged
    apart from the removed monitors (whole lines), the kept monitors' Location and the
    renumbered "Visual;Monitor N" references."""
    text_pieces, copied_up_to = [], 0
    new_number_by_old_number, kept_count = {}, 0
    monitor_blocks = find_monitor_blocks(profile_text)
    for old_number, (block_start, block_end) in enumerate(monitor_blocks, start=1):
        children_match = monitor_children_match(profile_text, block_start, block_end)
        if monitor_is_unused(children_match):
            line_start, line_end = whole_line_span(profile_text, block_start, block_end)
            text_pieces.append(profile_text[copied_up_to:line_start])
            copied_up_to = line_end
            continue
        kept_count += 1
        new_number_by_old_number[old_number] = kept_count
        location_match = MONITOR_LOCATION_PATTERN.search(profile_text, block_start, children_match.start())
        if location_match is not None:
            text_pieces.append(profile_text[copied_up_to:location_match.end(1)])
            text_pieces.append(MONITOR_KEPT_LOCATION)
            copied_up_to = location_match.start(2)
    text_pieces.append(profile_text[copied_up_to:])
    removed_count = len(monitor_blocks) - kept_count

    def renumbered_reference(reference_match):
        """One "Visual;Monitor N" with N replaced by that monitor's new number (1 when the
        monitor was removed)."""
        return reference_match.group(1) + str(new_number_by_old_number.get(int(reference_match.group(2)), 1))

    new_text = "".join(text_pieces)
    if kept_count:                                   # nothing to point at when no monitor is left
        new_text = MONITOR_REFERENCE_PATTERN.sub(renumbered_reference, new_text)
    return new_text, removed_count, kept_count


def remove_unused_monitors_from_file(profile_path, export_path):
    """Read the Helios profile at profile_path, remove its unused monitors
    (remove_unused_monitors) and write the result to export_path with the same encoding and
    line ends.  Returns (number removed, number kept).  Raises OSError on a file problem."""
    with open(profile_path, "rb") as profile_file:
        profile_bytes = profile_file.read()
    try:
        text_encoding, profile_text = "utf-8", profile_bytes.decode("utf-8")
    except UnicodeDecodeError:
        text_encoding, profile_text = "latin-1", profile_bytes.decode("latin-1")
    new_text, removed_count, kept_count = remove_unused_monitors(profile_text)
    with open(export_path, "wb") as export_file:
        export_file.write(new_text.encode(text_encoding))
    return removed_count, kept_count


# ======================================================================================
# Check Bindings:  list the devices of a Helios profile that nothing is bound to
# ======================================================================================
# Every control inside <Monitors> (an element with a TypeIdentifier and a Name) is a device.  A
# device counts as bound when its own <Bindings> holds a <Binding>, or when a binding anywhere in
# the profile names it as a Source (trigger, its output) or Target (action, the data it receives): its
# path "Visual;Monitor N.parent.child;Type;name" (or, when no path matches, its name when that name is unique in the profile).
# Monitors, viewports, panels, labels (text), images and input bindings never need a binding and are skipped,
# although a panel still appears in the pathway of the devices inside it.
BINDING_EXEMPT_TYPE_WORDS = ("monitor", "viewport", "panel", "label", "image", "textdecoration", "input")
BINDING_REFERENCE_ATTRIBUTES = ("Source", "Target")


def xml_local_name(tag):
    """An element tag without its XML namespace."""
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def binding_exempt_type(type_identifier):
    """True for the device types that need no binding (BINDING_EXEMPT_TYPE_WORDS)."""
    lowered = type_identifier.lower()
    if lowered.endswith(".text"):
        return True
    return any(word in lowered for word in BINDING_EXEMPT_TYPE_WORDS)


def parse_profile_xml(profile_text):
    """The root element of a Helios profile's XML.  Raises ValueError when it is not readable."""
    import xml.etree.ElementTree as element_tree
    try:
        return element_tree.fromstring(profile_text.lstrip("﻿").encode("utf-8"))
    except (element_tree.ParseError, ValueError) as parse_error:
        try:
            return element_tree.fromstring(re.sub(r"^<\?xml[^>]*\?>", "", profile_text.lstrip("﻿")))
        except element_tree.ParseError:
            raise ValueError(f"the profile could not be read as XML ({parse_error})") from None


def collect_binding_references(root):
    """Every Trigger Source / Action Target reference of the profile, lower case."""
    references = set()
    for element in root.iter():
        for attribute in BINDING_REFERENCE_ATTRIBUTES:
            value = element.get(attribute)
            if value:
                references.add(value.strip().lower())
    return references


def collect_profile_devices(element, chain, devices):
    """Add (name, type, parent chain, element) for every named, typed control below element."""
    for child in element:
        child_name = child.get("Name")
        if child.get("TypeIdentifier") is not None and child_name is not None:
            devices.append((child_name, child.get("TypeIdentifier"), chain, child))
            collect_profile_devices(child, chain + [child_name], devices)
        else:
            collect_profile_devices(child, chain, devices)


def list_profile_devices(root):
    """[(name, type, parent chain, element)] for every named, typed control of every monitor,
    in file order.  The chain starts with "Monitor N"."""
    devices = []
    for monitors_list in (element for element in root.iter() if xml_local_name(element.tag) == "Monitors"):
        monitors = [monitor for monitor in monitors_list if xml_local_name(monitor.tag) == "Monitor"]
        for monitor_number, monitor in enumerate(monitors, start=1):
            collect_profile_devices(monitor, [f"Monitor {monitor_number}"], devices)
    return devices


def has_own_binding(device_element):
    """True when the device holds a Bindings list with at least one Binding."""
    return any(xml_local_name(child.tag) == "Binding"
               for container in device_element if xml_local_name(container.tag) == "Bindings"
               for child in container)


def dotted_visual_references(references):
    """The dotted device pathways of the "visual;Monitor 3.Main Panel.Mechanics.Off flag;..." references."""
    dotted_references = set()
    for reference in references:
        reference_parts = reference.split(";")
        if len(reference_parts) >= 2 and reference_parts[0] == "visual":
            dotted_references.add(reference_parts[1])
    return dotted_references


def count_device_names(devices):
    """{lower-case device name: how many devices have it}."""
    name_counts = {}
    for name, _type, _chain, _element in devices:
        name_counts[name.lower()] = name_counts.get(name.lower(), 0) + 1
    return name_counts


def find_unbound_devices(profile_text):
    """[(device name, type, pathway)] for every device of the profile that has no binding, in
    file order.  The pathway runs parent to child ("Monitor 1 > Panel > Knob").  Raises
    ValueError when the profile is not readable XML."""
    root = parse_profile_xml(profile_text)
    references = collect_binding_references(root)
    reference_last_parts = {reference.rsplit(";", 1)[-1] for reference in references}
    # A real profile writes a device as  Visual;Monitor 3.Main Panel.Mechanics.Off flag;<Type>;<Name>
    # (dots between the parents), as the Source of a Trigger (its output) or the Target of an
    # Action (its input): either one means the device has a binding.
    dotted_references = dotted_visual_references(references)
    devices = list_profile_devices(root)
    name_counts = count_device_names(devices)
    unbound = []
    for name, type_identifier, chain, element in devices:
        if binding_exempt_type(type_identifier):
            continue
        full_path = ";".join(["Visual"] + chain + [name]).lower()
        dotted_path = ".".join(chain + [name]).lower()
        is_bound = (has_own_binding(element) or full_path in references or dotted_path in dotted_references
                    or (name_counts[name.lower()] == 1 and name.lower() in reference_last_parts))
        if not is_bound:
            unbound.append((name, type_identifier, " > ".join(chain + [name])))
    return unbound


class UnboundDevicesDialog(tk.Toplevel):
    """Profile > Check Bindings result: the devices with no binding, each with its pathway.
    With confirm=True (while packaging) the buttons are Accept and Cancel and `accepted`
    tells which was used; Cancel (or Escape / closing the window) means "leave this profile out"."""

    def __init__(self, parent, profile_path, unbound, confirm=False):
        super().__init__(parent)
        self.accepted = not confirm
        self.title("Check Bindings")
        self.configure(bg=PANEL_BG)
        self.transient(parent)
        content = tk.Frame(self, bg=PANEL_BG, padx=14, pady=12)
        content.pack(fill="both", expand=True)
        count = len(unbound)
        heading = (f"{count} device{'' if count == 1 else 's'} without a binding in "
                   f"{os.path.basename(profile_path)}" if count else
                   f"Every device in {os.path.basename(profile_path)} has a binding.")
        tk.Label(content, text=heading, bg=PANEL_BG, fg=TEXT_PRI, font=FONT_HEAD, anchor="w").pack(fill="x", pady=(0, 8))
        table_frame = tk.Frame(content, bg=PANEL_BG)
        table_frame.pack(fill="both", expand=True)
        view = ttk.Treeview(table_frame, columns=("device", "type", "path"), show="headings", height=16)
        for column, text, width in (("device", "Device", 200), ("type", "Type", 200), ("path", "Pathway", 520)):
            view.heading(column, text=text, anchor=tk.W)
            view.column(column, width=width, anchor=tk.W, stretch=False)    # fixed widths: the table scrolls sideways
        scroll = ttk.Scrollbar(table_frame, orient="vertical", command=view.yview)
        scroll_x = ttk.Scrollbar(table_frame, orient="horizontal", command=view.xview)
        view.configure(yscrollcommand=scroll.set, xscrollcommand=scroll_x.set)
        scroll.pack(side="right", fill="y")
        scroll_x.pack(side="bottom", fill="x")
        view.pack(side="left", fill="both", expand=True)
        # a pathway longer than its column is still reachable: size the column to the longest one
        longest = max((len(row[2]) for row in unbound), default=0)
        view.column("path", width=max(520, longest * 8))
        for row in unbound:
            view.insert("", tk.END, values=row)
        button_row = tk.Frame(content, bg=PANEL_BG)
        button_row.pack(anchor="w", pady=(10, 0))
        if confirm:
            tk.Button(button_row, text="Accept", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat", padx=14,
                      pady=5, cursor="hand2", command=self.accept).pack(side="left")
            tk.Button(button_row, text="Cancel", bg=MID_BG, fg=TEXT_PRI, font=FONT_HEAD, relief="flat", padx=14,
                      pady=5, cursor="hand2", command=self.destroy).pack(side="left", padx=(8, 0))
        else:
            tk.Button(button_row, text="Close", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat", padx=14,
                      pady=5, cursor="hand2", command=self.destroy).pack(side="left")
        self.bind("<Escape>", lambda _event: self.destroy())
        center_over(parent.master if parent.master is not None else parent, self)   # middle of the main window

    def accept(self):
        """Accept button (packaging): keep the profile in the package and close."""
        self.accepted = True
        self.destroy()


FUNCTION_MAPPING_ROLES = ("hint", "device", "command", "arg")


def function_mapping_entry(execution_context, definition, parameter_roles):
    """The View > Function Mapping entry of one function."""
    parameters_by_role = {role: [definition.parameter_names[position] for position in sorted(parameter_roles)
                                 if parameter_roles[position] == role]
                          for role in FUNCTION_MAPPING_ROLES}
    return {
        "function": definition.name,
        "parameters": definition.parameter_names,
        "hint": parameters_by_role["hint"],
        "device": parameters_by_role["device"],
        "commands": parameters_by_role["command"],
        "args": parameters_by_role["arg"],
        "file": execution_context.relative_path(definition.source_path),
    }


def build_function_mapping(execution_context, already_listed):
    """For View > Function Mapping: every named function with a hint/device/command/arg parameter."""
    mapping_entries = []
    for definition in execution_context.function_definitions:
        if not definition.name:
            continue
        parameter_roles = execution_context.analyze_parameter_roles(definition)
        if not set(parameter_roles.values()) & set(FUNCTION_MAPPING_ROLES):
            continue
        listing_key = (definition.name, os.path.normcase(definition.source_path))
        if listing_key in already_listed:
            continue
        already_listed.add(listing_key)
        mapping_entries.append(function_mapping_entry(execution_context, definition, parameter_roles))
    return mapping_entries


class TableGenerator:
    """Builds the whole reference table for every aircraft under one folder (see
    generate_table_from_folder).  One aircraft job = one clickabledata.lua plus the Input files and
    other .lua files that belong to it; its rows and statistics are added to self.result."""

    def __init__(self, search_root_folder):
        self.search_root_folder = os.path.abspath(search_root_folder)
        (self.lua_file_paths, self.clickabledata_paths,
         self.input_file_paths, self.corrections_paths) = find_aircraft_files(self.search_root_folder)
        self.file_locator = LuaFileLocator(self.lua_file_paths)
        self.result = GenerationResult()
        self.result.clickabledata_paths = self.clickabledata_paths
        self.functions_listed = set()
        self.input_files_by_clickabledata = {path: [] for path in self.clickabledata_paths}
        self.other_files_by_clickabledata = {path: [] for path in self.clickabledata_paths}

    def closest_clickabledata(self, file_path):
        """The clickabledata.lua sharing the most folders with file_path."""
        return max(self.clickabledata_paths, key=lambda clickabledata_path: LuaFileLocator.shared_folder_length(
            os.path.dirname(clickabledata_path), file_path))

    def assign_files_to_aircraft(self):
        """Every Input file and every other .lua file belongs to the clickabledata.lua it shares
        the most folders with."""
        if not self.clickabledata_paths:
            return
        for input_file_path in self.input_file_paths:
            self.input_files_by_clickabledata[self.closest_clickabledata(input_file_path)].append(input_file_path)
        input_or_clickable_keys = {LuaExecutionContext.file_key(path)
                                   for path in self.input_file_paths + self.clickabledata_paths}
        for other_file_path in sorted(self.lua_file_paths):
            if LuaExecutionContext.file_key(other_file_path) not in input_or_clickable_keys:
                self.other_files_by_clickabledata[self.closest_clickabledata(other_file_path)].append(other_file_path)

    def aircraft_jobs(self):
        """[(clickabledata.lua or None, its Input files)] - an Input folder on its own still works."""
        if self.input_file_paths and not self.clickabledata_paths:
            return [(None, self.input_file_paths)]
        return [(path, self.input_files_by_clickabledata[path]) for path in self.clickabledata_paths]

    def run(self):
        """Process every aircraft found in the folder, then look up the viewports and flyable vehicles."""
        self.assign_files_to_aircraft()
        for clickabledata_path, aircraft_input_files in self.aircraft_jobs():
            self.process_aircraft(clickabledata_path, aircraft_input_files)
        result = self.result
        result.viewport_calls = find_viewport_calls(sorted(self.lua_file_paths))             # step 9 (.lua only)
        result.vehicle_names = find_flyable_vehicle_names(self.lua_file_paths)               # step 9: Vehicles
        if SORT_GENERATED_ROWS:                                                              # step 8
            result.table_rows = order_generated_rows(result.table_rows)
        result.source_rows = build_source_rows(result.table_rows)                            # step 10
        result.function_mapping.sort(key=lambda mapping_entry: mapping_entry["function"].lower())
        return result

    def relative_path(self, file_path):
        """A file path relative to the folder that was searched."""
        return os.path.relpath(file_path, self.search_root_folder)

    def process_aircraft(self, clickabledata_path, aircraft_input_files):
        """Steps 2-7 for one aircraft: element, Input, command, arg and arg-mention rows, then
        duplicate removal and the aircraft's corrections file."""
        result = self.result
        execution_context = LuaExecutionContext(self.search_root_folder, self.file_locator)
        row_builder = TableRowBuilder(execution_context)
        aircraft_rows = []
        if clickabledata_path:
            execution_context.run_lua_file(clickabledata_path)                          # step 2
            element_rows, element_count = row_builder.build_element_rows(clickabledata_path)   # step 3
            aircraft_rows += element_rows
            result.element_count += element_count
        binding_rows = row_builder.build_input_binding_rows(aircraft_input_files)       # step 4
        corrections_path = choose_corrections_file(self.corrections_paths,
                                                   clickabledata_path or aircraft_input_files[0])
        table_corrections = (load_table_corrections(corrections_path, execution_context.warnings)
                             if corrections_path else None)
        added_rows = override_rows_to_add(table_corrections, aircraft_rows + binding_rows, corrections_path)
        aircraft_rows += binding_rows + added_rows
        result.input_row_count += len(binding_rows)
        result.correction_rows_added += len(added_rows)
        result.input_file_paths += [self.relative_path(path) for path in aircraft_input_files]
        if clickabledata_path:
            self.add_command_rows(execution_context, row_builder, clickabledata_path, aircraft_rows)
        result.command_only_devices_filled += fill_devices_of_command_only_rows(aircraft_rows)  # step 6
        aircraft_rows, duplicate_count = remove_duplicate_device_commands(aircraft_rows)       # step 6
        result.duplicate_row_count += duplicate_count
        if clickabledata_path:
            self.add_arg_rows(row_builder, clickabledata_path, aircraft_rows)
        aircraft_rows, removed_count, changed_count = apply_row_corrections(aircraft_rows, table_corrections)  # step 7
        if table_corrections:
            result.corrections_file_paths.append(self.relative_path(corrections_path))
            result.correction_rows_removed += removed_count
            result.correction_rows_changed += changed_count
        self.record_aircraft_totals(execution_context, row_builder, aircraft_rows)
        warning_prefix = f"{self.relative_path(clickabledata_path)}: " if clickabledata_path else ""
        result.warnings += [warning_prefix + warning for warning in execution_context.warnings]

    def add_command_rows(self, execution_context, row_builder, clickabledata_path, aircraft_rows):
        """Step 5: rows from the command definition files."""
        result = self.result
        command_rows, files_used = row_builder.build_definition_file_rows(clickabledata_path, aircraft_rows, "command")
        aircraft_rows += command_rows
        result.command_row_count += len(command_rows)
        result.command_file_paths += [path for path in files_used if path not in result.command_file_paths]
        result.function_mapping += build_function_mapping(execution_context, self.functions_listed)

    def add_arg_rows(self, row_builder, clickabledata_path, aircraft_rows):
        """Step 5 (after duplicate removal): an arg whose only element row was removed as a
        duplicate (e.g. a variant branch with the same device / command) still gets its row."""
        result = self.result
        arg_rows, files_used = row_builder.build_definition_file_rows(clickabledata_path, aircraft_rows, "arg")
        aircraft_rows += arg_rows
        result.arg_row_count += len(arg_rows)
        result.arg_file_paths += [path for path in files_used if path not in result.arg_file_paths]
        mention_rows, mention_files = row_builder.build_arg_mention_rows(
            self.other_files_by_clickabledata[clickabledata_path], aircraft_rows)
        aircraft_rows += mention_rows
        result.arg_mention_row_count += len(mention_rows)
        result.arg_mention_file_paths += [path for path in mention_files
                                          if path not in result.arg_mention_file_paths]

    def record_aircraft_totals(self, execution_context, row_builder, aircraft_rows):
        """Add one aircraft's rows, file counts, function types, variables and devices to the result."""
        result = self.result
        result.table_rows += aircraft_rows
        result.files_processed += len(execution_context.processed_file_paths)
        result.unmapped_function_names |= execution_context.unmapped_function_names
        for function_name, return_classes in row_builder.function_return_types.items():
            result.function_return_types.setdefault(function_name, return_classes)
        self.record_file_variables(execution_context)
        self.record_discovered_devices(execution_context, aircraft_rows)
        result.element_details.update(row_builder.element_details)

    def record_file_variables(self, execution_context):
        """Every variable each file defined (name and value), for the Source tab's file view."""
        file_variables = self.result.file_variables
        for variable_path, (file_path, number) in execution_context.numeric_definitions.items():
            file_variables.setdefault(file_path, []).append((variable_path, format_number_text(number)))
        for variable_path, file_path, number in execution_context.shadowed_numeric_definitions:
            file_variables.setdefault(file_path, []).append((variable_path, format_number_text(number)))

    def record_discovered_devices(self, execution_context, aircraft_rows):
        """Every device name discovered: the aircraft's devices table, then the rows' Device column
        (which also holds command groups that are not in the devices table, e.g. UNASSIGNED)."""
        discovered_devices = self.result.discovered_devices
        devices_table = execution_context.global_variables.get("devices")
        for device_name, device_number in (devices_table.items() if isinstance(devices_table, dict) else ()):
            if isinstance(device_name, str) and device_name.strip():
                discovered_devices.setdefault(device_name.strip(), self.device_number_text(device_number))
        for table_row in aircraft_rows:
            device_name = table_row.get("Device", "").strip()
            if device_name and not discovered_devices.get(device_name):
                discovered_devices[device_name] = normalize_id_text(table_row.get("Device #", ""))

    @staticmethod
    def device_number_text(device_number):
        """A device number as text, '' when it is not a number."""
        return format_number_text(device_number) if is_lua_number(device_number) else ""


def generate_table_from_folder(search_root_folder):
    """Table > Generate: build the whole table for every aircraft under the chosen folder.
    Walks the folder once, then for each clickabledata.lua runs its Lua, builds element /
    Input / arg / command rows, removes duplicates and applies that aircraft's optional
    corrections file; finally lists viewport calls and sorts the rows. Returns a
    GenerationResult."""
    return TableGenerator(search_root_folder).run()


# ════════════════════════════════════════════════════════════════════════════════
# COMMAND TABLE TAB
# ════════════════════════════════════════════════════════════════════════════════
# The "Table" tab: an editable table of DCS clickable elements, arguments, devices and
# commands.  Its file actions live in the "Table" menu of the main window:
#   Table ▸ Generate…   build the table from an aircraft folder (see the engine above)
#   Table ▸ Load…       open a table saved earlier (JSON list of row objects)
#   Table ▸ Save / Save As…   write the table as JSON (every value is a string)
# Inside the tab: double-click a cell to edit (Enter keeps, Esc cancels, Tab moves on),
# double-click the empty area to add a row, Insert / Delete keys add / remove rows,
# right-click for Insert / Delete / Function Mapping, click a header to sort
# (again to reverse; sorting by Device # also sorts each device's rows by Command #).
# Main tabs, and the sub tabs they hold:
#   Devices           Push Button ... 3D Ball, Collisions
#   Tables            Current Data, Old References, Mismatched, Viewport, Source
#   Argument Logger   the argument logger (the Change Tracker's sub tabs)
#   Text Editor       standalone text editor tools embedded in the interface
DEVICES_TAB_LABEL = "JSON Controls"
TABLES_TAB_LABEL = "Reference Data"
ARGUMENT_LOGGING_TAB_LABEL = "Aircraft Data"
TEXT_EDITOR_TAB_LABEL = "Text Editor"
FULL_VIEW_TAB_LABEL = "Full View"
COLLISIONS_TAB_LABEL = "Collisions"
COMMAND_TABLE_TAB_LABEL = "Current Data"           # the current reference table (generated / loaded)
OLD_REFERENCE_TAB_LABEL = "Old References"      # an earlier reference table, to compare against
MISMATCHED_TAB_LABEL = "Mismatched"             # rows whose numbers changed between the two

# A CommandTablePanel works in one of two roles:
#   CURRENT_REFERENCE_ROLE  the Reference tab: Generate, Build Device, Auto-fill, viewports
#   OLD_REFERENCE_ROLE      the Old References tab: same table, no buttons; its Load reads
#                           only the table part of a file and its Save replaces only that part
CURRENT_REFERENCE_ROLE = "current"
OLD_REFERENCE_ROLE = "old"

# Blue marks a row that differs between Reference and Old References (it wins over green).
MISMATCHED_ROW_BACKGROUND = {"dark": "#1f4f99", "grayscale": "#2f5c99", "default": "#b8d4ff"}

# The Mismatched tab: old values from Old References, new values from Reference.
MISMATCHED_COLUMNS = ["Old Arg #", "New Arg #", "Arg Name", "Old Device", "New Device",
                      "Old Device #", "New Device #", "Old Command #", "New Command #"]
MISMATCHED_COLUMN_IDS = [f"mismatched_column_{position}" for position in range(len(MISMATCHED_COLUMNS))]
MISMATCHED_COLUMN_WIDTHS = [80, 80, 240, 170, 170, 95, 95, 110, 110]
# Clicking one of these headers also sorts each group's rows by the second column.
MISMATCHED_SECONDARY_SORT = {"Old Device": "Old Command #", "Old Device #": "Old Command #",
                             "New Device": "New Command #", "New Device #": "New Command #"}

# The Reference / Old References tables show the 8 TABLE_COLUMNS.  A row whose Arg # /
# Device # / Command # already exist in a device of the Helios profile is shown green.
# ADDED_COLUMN is only the key older table files used for that mark; loading ignores it.
ADDED_COLUMN = "Added"
TABLE_TAB_COLUMNS = list(TABLE_COLUMNS)
TABLE_TAB_COLUMN_IDS = [f"table_tab_column_{position}" for position in range(len(TABLE_TAB_COLUMNS))]
TABLE_TAB_COLUMN_WIDTHS = list(TREEVIEW_COLUMN_WIDTHS)
ADDED_ROW_BACKGROUND = {"dark": "#1f4a2e", "grayscale": "#1f4a2e",
                        "default": "#cdeed6"}   # green, per theme

# Build Device: the default device type for the class an element returns.
CLASS_TYPE_TO_HELIOS_TYPE = {
    "class_type.BTN": DCS_LEADER + "PushButton",
    "class_type.TUMB": DCS_LEADER + "Switch",
    "class_type.LEV": DCS_LEADER + "Axis",
}
# Element-function parameters that give a switch's number of positions and the step
# between position values (e.g. multiposition_switch(hint_, device_, command_, arg_, count_, delta_)).
POSITION_COUNT_PARAMETER_NAMES = ("count",)        # compared without underscores / case
POSITION_STEP_PARAMETER_NAMES = ("delta",)
# Element-function parameters that give a 3-position switch's values: value1_ (the
# minimum), value2_ (the middle position) and value3_ (the maximum).  When all three are
# given and the element is built as a Switch, it gets exactly these 3 positions.
POSITION_VALUE_PARAMETER_NAMES = ("value1", "value2", "value3")

# Table files are saved as  {"table": [row, ...], "viewports": [{"Viewport": ..., "File": ...}]}.
# Older files that are just a list of rows still load (table only).
TABLE_FILE_TABLE_KEY = "table"
TABLE_FILE_VIEWPORTS_KEY = "viewports"
# A Reference table file also keeps what Generate learned about the element functions:
#   "function_return_types": {function name: ["class_type.TUMB", ...]}
#   "element_details":       {element name: {"position_count": 5, "position_step": 0.1,
#                                            "position_values": [-1, 0, 1]}}
TABLE_FILE_RETURN_TYPES_KEY = "function_return_types"
TABLE_FILE_ELEMENT_DETAILS_KEY = "element_details"
#   "device_names": [{"Device": "ADI_ARU_11_A", "Device #": "44"}, ...]   every device name
#   Generate discovered, alphabetically (for Build Device's Device drop-down)
TABLE_FILE_DEVICE_NAMES_KEY = "device_names"


def sorted_device_names(device_numbers):
    """Device names in alphabetical order (upper / lower case ignored, then exact text)."""
    return sorted(device_numbers, key=lambda device_name: (device_name.lower(), device_name))
VIEWPORT_FILE_FIELDS = ("Viewport", "File")

# Every combination of the three numbers a table row can have, as (arg, device, command).
ID_MATCH_PATTERNS = [(True, True, True), (True, True, False), (True, False, True), (False, True, True),
                     (True, False, False), (False, True, False), (False, False, True)]


def normalize_id_text(value):
    """'3001', 3001, 3001.0 and ' 3001 ' all become '3001'; blanks become ''."""
    text_value = "" if value is None else str(value).strip()
    if not text_value:
        return ""
    try:
        number = float(text_value)
    except ValueError:
        return text_value
    return str(int(number)) if number.is_integer() else str(number)


class FunctionIdCollector:
    """Sorts every id found in a Helios function's data into arg, device and action id sets."""

    ACTION_ID_KEYS = ("actionId", "pushId", "releaseId", "_switchDefaultActionId")

    def __init__(self):
        self.arg_ids = set()
        self.device_ids = set()
        self.action_ids = set()

    def walk(self, node, inside_exports):
        """Walk a function's data recursively, sorting every id found into the arg / device / action sets."""
        if isinstance(node, list):
            for item in node:
                self.walk(item, inside_exports)
        elif isinstance(node, dict):
            for key, value in node.items():
                if key == "exports":
                    self.walk(value, True)
                elif not self.collect_id(key, value, inside_exports):
                    self.walk(value, inside_exports)

    def collect_id(self, key, value, inside_exports):
        """Store value when key names an id; False when it does not."""
        if key == "deviceId":
            self.device_ids.add(normalize_id_text(value))
        elif key in self.ACTION_ID_KEYS:
            self.action_ids.add(normalize_id_text(value))
        elif key == "id" and inside_exports:
            self.arg_ids.add(normalize_id_text(value))
        else:
            return False
        return True


def collect_function_ids(function):
    """All ids a Helios function holds, wherever its type keeps them:
         arg ids     every exports[*].id
         device ids  every deviceId (buttons, actions, top level)
         action ids  every actionId / pushId / releaseId (positions, buttons, actions)
    One walk over the function's data.  Returns three sets of normalized texts."""
    collector = FunctionIdCollector()
    collector.walk(function, False)
    for id_set in (collector.arg_ids, collector.device_ids, collector.action_ids):
        id_set.discard("")
    return collector.arg_ids, collector.device_ids, collector.action_ids


def function_match_keys(function):
    """Every match key of one device: one for each combination of its ids that
    ID_MATCH_PATTERNS allows (a pattern that needs an id kind the device lacks is skipped)."""
    id_lists = collect_function_ids(function)
    for pattern in ID_MATCH_PATTERNS:
        if not all(ids or not is_used for is_used, ids in zip(pattern, id_lists)):
            continue
        id_choices = [ids if is_used else ("",) for is_used, ids in zip(pattern, id_lists)]
        for id_combination in itertools.product(*id_choices):
            yield (*pattern, *id_combination)


def build_added_match_keys(functions):
    """A set of keys, one for every combination of ids that some device holds, so that a
    table row can be checked with a single set lookup.  Cost: O(functions x the few id
    combinations each function has)."""
    return {key for function in functions for key in function_match_keys(function)}


def table_row_match_key(arg_text, device_number_text, command_number_text):
    """The key of one table row: whichever of Arg # / Device # / Command # it has must all
    match the SAME device.  A row with only an Arg # (and Arg Name) matches on the Arg #.
    A row with none of the three numbers never matches (returns None)."""
    arg_id = normalize_id_text(arg_text)
    device_id = normalize_id_text(device_number_text)
    action_id = normalize_id_text(command_number_text)
    if not (arg_id or device_id or action_id):
        return None
    return (bool(arg_id), bool(device_id), bool(action_id), arg_id, device_id, action_id)


# ── Reference / Old References comparison ─────────────────────────────────────────
# How two rows are paired, and when a pair counts as MISMATCHED:
#   * a row with an Arg Name is paired with the old row of the same Arg Name; the pair is
#     mismatched when the Arg #, Device # or Command # differ.  (A row that only has an
#     arg and Arg # has blank Device # / Command #, so for it only the Arg # can differ.)
#   * a row without an Arg Name is paired with the old row that has the same Device,
#     Device #, Command and Command #; the pair is mismatched when the Arg # differs.
# Rows found in only one table are not mismatches.  When several rows share a key (an arg
# with two commands, for example), identical pairs are matched first so they are not
# reported, and the rest are paired in table order.  Cost: O(rows of both tables).
def reference_pairing_key(table_row):
    """What a row is paired on (see above), or None for a row with nothing to pair on."""
    arg_name = table_row.get("Arg Name", "").strip()
    if arg_name:
        return ("arg_name", arg_name)
    # Device names are compared with "_" and spaces treated alike, so a table saved when
    # names were shown with spaces still pairs with one that keeps the underscores.
    device_text = " ".join(table_row.get("Device", "").replace("_", " ").split())
    command_text = table_row.get("Command", "").strip()
    device_number = normalize_id_text(table_row.get("Device #", ""))
    command_number = normalize_id_text(table_row.get("Command #", ""))
    if not (device_text or command_text or device_number or command_number):
        return None
    return ("device_command", device_text, device_number, command_text, command_number)


def reference_compared_values(table_row, pairing_key):
    """The numbers that must be equal for a pair to match: Arg #, Device # and Command #
    for rows paired by Arg Name; only Arg # for rows paired by device / command."""
    if pairing_key[0] == "arg_name":
        return (normalize_id_text(table_row.get("Arg #", "")), normalize_id_text(table_row.get("Device #", "")),
                normalize_id_text(table_row.get("Command #", "")))
    return (normalize_id_text(table_row.get("Arg #", "")),)


def row_has_only_an_arg(table_row):
    """True when a row has no device and no command, i.e. only an arg (Arg Name / Arg #)."""
    return not any(table_row.get(column, "").strip() for column in ("Device", "Device #", "Command", "Command #"))


def reference_pairing_groups(rows_with_ids, only_keys=None):
    """{pairing key: [(row id, row)]} for the rows that have a pairing key (only those in
    only_keys, when given), in table order."""
    rows_by_key = {}
    for row_id, row in rows_with_ids:
        pairing_key = reference_pairing_key(row)
        if pairing_key is not None and (only_keys is None or pairing_key in only_keys):
            rows_by_key.setdefault(pairing_key, []).append((row_id, row))
    return rows_by_key


def unpaired_rows_after_identical_pairs(new_group, old_group, pairing_key):
    """Pair each new row with an identical old row first (such pairs are never reported).
    Returns (new rows left over, old rows left over), both in table order."""
    unused_old_by_values = {}                 # compared values -> old positions, LAST first
    for old_position in range(len(old_group) - 1, -1, -1):
        old_row = old_group[old_position][1]
        unused_old_by_values.setdefault(reference_compared_values(old_row, pairing_key), []).append(old_position)
    used_old_positions, unpaired_new = set(), []
    for new_row_id, new_row in new_group:
        same_value_positions = unused_old_by_values.get(reference_compared_values(new_row, pairing_key))
        if same_value_positions:
            used_old_positions.add(same_value_positions.pop())     # the earliest unused one, O(1)
        else:
            unpaired_new.append((new_row_id, new_row))
    remaining_old = [old_group[position] for position in range(len(old_group)) if position not in used_old_positions]
    return unpaired_new, remaining_old


def mismatch_record(new_row_id, new_row, old_row_id, old_row):
    """The record describing how a new row differs from the old row it was paired with."""
    return {
        "Old Arg #": old_row.get("Arg #", ""), "New Arg #": new_row.get("Arg #", ""),
        "Arg Name": new_row.get("Arg Name", ""),
        "Old Device": old_row.get("Device", ""), "New Device": new_row.get("Device", ""),
        "Old Device #": old_row.get("Device #", ""), "New Device #": new_row.get("Device #", ""),
        "Old Command #": old_row.get("Command #", ""), "New Command #": new_row.get("Command #", ""),
        "new_row_id": new_row_id, "old_row_id": old_row_id,
        "only_arg": row_has_only_an_arg(new_row) and row_has_only_an_arg(old_row),
    }


def compare_reference_tables(new_rows_with_ids, old_rows_with_ids):
    """Compare the Reference rows (new) with the Old References rows (old).
    Both arguments are [(row id, {column: text})] in table order.  Returns
    (mismatch records, ids of mismatched new rows, ids of mismatched old rows); each record
    holds the MISMATCHED_COLUMNS values plus new_row_id, old_row_id and only_arg."""
    old_rows_by_key = reference_pairing_groups(old_rows_with_ids)
    new_rows_by_key = reference_pairing_groups(new_rows_with_ids, only_keys=old_rows_by_key)
    mismatch_records, mismatched_new_ids, mismatched_old_ids = [], set(), set()
    for pairing_key, new_group in new_rows_by_key.items():
        unpaired_new, remaining_old = unpaired_rows_after_identical_pairs(
            new_group, old_rows_by_key[pairing_key], pairing_key)
        # the rest are paired in table order: these pairs are the mismatches
        for (new_row_id, new_row), (old_row_id, old_row) in zip(unpaired_new, remaining_old):
            mismatch_records.append(mismatch_record(new_row_id, new_row, old_row_id, old_row))
            mismatched_new_ids.add(new_row_id)
            mismatched_old_ids.add(old_row_id)
    return mismatch_records, mismatched_new_ids, mismatched_old_ids


def build_functions_by_match_key(functions):
    """match key -> [functions holding that id combination] (same keys as
    build_added_match_keys), so the devices behind an old row are found in one lookup."""
    functions_by_key = {}
    for function in functions:
        for key in function_match_keys(function):
            holders = functions_by_key.setdefault(key, [])
            if not holders or holders[-1] is not function:
                holders.append(function)
    return functions_by_key


class FunctionIdReplacer:
    """Walks one Helios function and replaces the ids listed in the three change maps."""

    ACTION_ID_KEYS = ("actionId", "pushId", "releaseId", "_switchDefaultActionId")

    def __init__(self, export_id_changes, device_id_changes, action_id_changes):
        self.export_id_changes = export_id_changes
        self.device_id_changes = device_id_changes
        self.action_id_changes = action_id_changes
        self.changed = False

    @staticmethod
    def new_id_for(old_value, id_changes):
        """The new id for old_value from id_changes, or None when it does not change."""
        normalized_old = normalize_id_text(old_value)
        if normalized_old and normalized_old in id_changes:
            return to_int(id_changes[normalized_old])
        return None

    def replacement_for(self, key, value, inside_exports):
        """(True, new id or None) when key holds an id that may be replaced; (False, None) otherwise."""
        if key == "id" and inside_exports:
            return True, self.new_id_for(value, self.export_id_changes)
        if key == "deviceId":
            return True, self.new_id_for(value, self.device_id_changes)
        if key in self.ACTION_ID_KEYS:
            return True, self.new_id_for(value, self.action_id_changes)
        return False, None

    def walk(self, node, inside_exports):
        """Visit every dict / list of the function, replacing ids by their key."""
        if isinstance(node, list):
            for item in node:
                self.walk(item, inside_exports)
        elif isinstance(node, dict):
            self.walk_dict(node, inside_exports)

    def walk_dict(self, node, inside_exports):
        """Visit the fields of one dict; everything under "exports" counts as inside exports."""
        for key, value in list(node.items()):
            if key == "exports":
                self.walk(value, True)
            else:
                self.visit_field(node, key, value, inside_exports)

    def visit_field(self, node, key, value, inside_exports):
        """Replace one id field by its key, or look further down into any other field."""
        is_id_field, replacement = self.replacement_for(key, value, inside_exports)
        if not is_id_field:
            self.walk(value, inside_exports)
        elif replacement is not None and normalize_id_text(replacement) != normalize_id_text(value):
            node[key] = replacement
            self.changed = True


def replace_function_ids(function, export_id_changes, device_id_changes, action_id_changes):
    """Replace ids inside one Helios function, everywhere its type stores them:
         exports[*].id                               via export_id_changes
         every deviceId                              via device_id_changes
         every actionId / pushId / releaseId (and the switch default action id) via action_id_changes
    Each *_changes maps an old id text to its new id text.  All replacements are made from
    the ORIGINAL values in one walk, so swapped numbers (A->B, B->A) cannot chain.
    Returns True when something changed."""
    replacer = FunctionIdReplacer(export_id_changes, device_id_changes, action_id_changes)
    replacer.walk(function, False)
    return replacer.changed


TYPE_WORD_RULES = (              # (words in the Type text, Helios type) - first rule that matches wins
    (("axis", "lev"), "Axis"),
    (("roller", "encoder"), "RotaryEncoder"),
    (("tumb", "switch", "lever", "cover", "breaker", "flipcover"), "Switch"),
    (("button", "btn"), "PushButton"),
)


def guess_helios_type_for_row(table_row, function_return_types=None):
    """Default device type for Build Device (the user can change it in the dialog):
      1. an Arg # but no Command #                     -> Network Value
      2. the class the element returns (the class written in a table element's Type, or the
         return type Generate recorded for its function), first one that maps:
            class_type.BTN -> Push Button,  class_type.TUMB -> Switch,  class_type.LEV -> Axis
      3. otherwise a guess from the Type text (axis / roller / switch / button words)."""
    has_arg = bool(table_row.get("Arg #", "").strip())
    has_command = bool(table_row.get("Command #", "").strip())
    if has_arg and not has_command:
        return DCS_LEADER + "NetworkValue"
    type_text = table_row.get("Type", "").strip()
    class_candidates = list((function_return_types or {}).get(type_text, [])) + [type_text]
    for class_text in class_candidates:
        helios_type = CLASS_TYPE_TO_HELIOS_TYPE.get(" ".join(class_text.split()))
        if helios_type:
            return helios_type
    lowered_type = type_text.lower()
    for type_words, type_name in TYPE_WORD_RULES:
        if any(word in lowered_type for word in type_words):
            return DCS_LEADER + type_name
    return DCS_LEADER + ("PushButton" if has_command else "NetworkValue")   # an arg with no command: an indicator


def element_parameter(element_detail, *parameter_names):
    """The value Generate kept for the first of parameter_names an element was created with
    (names compared without surrounding underscores, upper / lower case ignored), or ""."""
    parameters = (element_detail or {}).get("parameters") or {}
    plain_parameters = {str(name).lower().strip("_"): value for name, value in parameters.items()}
    for parameter_name in parameter_names:
        if parameter_name in plain_parameters:
            return plain_parameters[parameter_name]
    return ""


def element_help_text(element_detail):
    """The help text of an element made by a function call: its 'help' parameter, else its
    'hint' parameter (DCS's help text).  "" for table elements or when there is none."""
    parameters = (element_detail or {}).get("parameters") or {}
    if not parameters or "class" in parameters:      # a table element, not a function call
        return ""
    return element_parameter(element_detail, "help", "hint").strip()


def apply_combined_entry(new_function, helios_type, first_row, second_row):
    """Combine: the second entry becomes the second option of the device (the first entry
    already gave the Export ID(Arg), Device ID and its own command):
         Push Button / Axis  -> its action id is the second entry's Command #
                                (deviceA arg 1, device 2, command 3 + deviceB command 6 ->
                                 id 1, deviceId 2, actionId 6)
         Switch              -> position 1 gets the first Command #, position 2 the second
         Rotary Encoder      -> increment gets the first Command #, decrement the second"""
    first_command = first_row.get("Command #", "").strip()
    second_command = second_row.get("Command #", "").strip()
    if not second_command:
        return
    if helios_type in (DCS_LEADER + "PushButton", DCS_LEADER + "Axis"):
        set_primary_action_id(new_function, second_command)
    elif helios_type == DCS_LEADER + "Switch":
        combine_into_switch(new_function, first_command, second_command)
    elif helios_type == DCS_LEADER + "RotaryEncoder":
        combine_into_rotary_encoder(new_function, first_command, second_command)


def combine_into_switch(new_function, first_command, second_command):
    """Position 1 gets the first Command #, position 2 the second."""
    positions = new_function.get("positions") or []
    if len(positions) < 2:
        positions = switch_positions(2)
        new_function["positions"] = positions
    if first_command:
        positions[0]["actionId"] = to_int(first_command)
    positions[1]["actionId"] = to_int(second_command)


def combine_into_rotary_encoder(new_function, first_command, second_command):
    """Increment gets the first Command #, decrement the second."""
    actions = new_function.get("actions") or {}
    if first_command and isinstance(actions.get("increment"), dict):
        actions["increment"]["actionId"] = to_int(first_command)
    if isinstance(actions.get("decrement"), dict):
        actions["decrement"]["actionId"] = to_int(second_command)


def switch_positions(position_count, position_step=None):
    """position_count switch positions for a new Switch: values 0, step, 2*step ... when a
    step is known, else spread evenly from 0 to 1."""
    if position_count <= 1:
        values = [0.0]
    elif position_step:
        values = [round(position * position_step, 6) for position in range(position_count)]
    else:
        values = [round(position / (position_count - 1), 6) for position in range(position_count)]
    return [{"argumentValue": str(float(value)), "name": "", "actionId": ""} for value in values]


def build_default_device(table_row, helios_type, device_name, element_detail=None):
    """A new Helios function of helios_type filled from a table row:
         Export ID(Arg) <- Arg #      Device    <- Device      Device ID <- Device #
         Action ID      <- Command #  Description <- Note (type default when Note is blank)
         Name           <- the name chosen in the Build Device dialog
         Positions      <- for a Switch: value1_, value2_, value3_ when the element has them
                           (3 positions, value1 the minimum, value3 the maximum), else
                           element_detail's position_count (and position_step)"""
    new_function = make_blank_entry(helios_type)
    element_detail = element_detail or {}
    position_values = element_detail.get("position_values")
    position_count = element_detail.get("position_count")
    if position_values and "positions" in new_function:      # a switch with value1_, value2_, value3_
        new_function["positions"] = [{"argumentValue": str(float(value)), "name": "", "actionId": ""}
                                     for value in position_values]
    elif position_count and "positions" in new_function:     # a switch with count_ positions
        new_function["positions"] = switch_positions(position_count, element_detail.get("position_step"))
    new_function["name"] = device_name
    new_function["device"] = table_row.get("Device", "").strip()
    note_text = table_row.get("Note", "").strip()
    if note_text:
        new_function["description"] = note_text
    arg_text = table_row.get("Arg #", "").strip()
    if arg_text and first_export(new_function):
        first_export(new_function)["id"] = to_int(arg_text)
    set_primary_device_id(new_function, table_row.get("Device #", "").strip())
    set_primary_action_id(new_function, table_row.get("Command #", "").strip())
    return new_function


class CommandTablePanel(tk.Frame):
    """The table editor, living inside a notebook tab of the Helios editor.  Used twice:
    as the Reference tab (panel_role CURRENT_REFERENCE_ROLE: Generate, Build Device,
    Auto-fill, viewports) and as the Old References tab (OLD_REFERENCE_ROLE: the same table
    without buttons, compared against Reference).  `saved_state` (from export_state)
    restores the rows after the tabs are rebuilt, e.g. when switching light / dark mode."""

    def __init__(self, parent_frame, host_window, saved_state=None, panel_role=CURRENT_REFERENCE_ROLE):
        """Build the tab (toolbar and table) and, when the tabs are being rebuilt, restore the
        rows it had before."""
        super().__init__(parent_frame, bg=PANEL_BG)
        self.host_window = host_window                # the HeliosEditor (dialog parent)
        self.panel_role = panel_role
        self.is_current_reference = panel_role == CURRENT_REFERENCE_ROLE
        self.tab_label = COMMAND_TABLE_TAB_LABEL if self.is_current_reference else OLD_REFERENCE_TAB_LABEL
        self.added_row_ids = set()                    # rows already a device in the profile (green)
        self.highest_arg_number = 0                   # highest Arg # in the table (for "Max id used")
        self.mismatched_row_ids = set()               # rows differing from the other table (blue)
        self.logger_row_ids = set()                   # rows the logger saw that are not in the interface (orange)
        self.loaded_file_contents = None              # Old References: the loaded file, kept for Save
        self.current_file_path = None
        self.suggested_file_name = ""                 # set by Generate: "<folder> Reference Table.json"
        self.has_unsaved_changes = False
        self.active_cell_editor = None                # (entry widget, row id, column position)
        self.function_mapping = []
        self.sorted_column_id = None
        self.sort_descending = False
        self.build_toolbar()
        self.build_table_view()
        if saved_state:
            self.restore_state(saved_state)
        self.refresh_status()

    # ------------------------------------------------------------------ layout
    def build_toolbar(self):
        """Toolbar: (Reference only) Build Device and Auto-fill Id's buttons; the colour legend
        and the status text (rows, added rows, mismatched rows, file name)."""
        toolbar = tk.Frame(self, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)
        if not self.is_current_reference:              # Old References: no buttons
            tk.Label(toolbar, text="Old reference table   (Table ▸ Old Reference ▸ Load…)   ·   "
                                   "green: already a device   ·   blue: differs from Reference",
                     bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left")
            self.status_label = tk.Label(toolbar, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
            self.status_label.pack(side="right", padx=(8, 8))
            return
        # Build Device: a new Helios device from the selected row (see BuildDeviceDialog).
        tk.Button(toolbar, text="🛠  Build Device", bg=ACCENT2, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=14, pady=3, cursor="hand2",
                  command=self.build_device_from_selected_row).pack(side="left")
        # Auto-fill Id's: gives every Reference row without an Arg # the next free Arg #
        # (see auto_fill_arg_numbers).  The profile's devices are not changed.
        tk.Button(toolbar, text="🔢  Auto-fill Id's", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=14, pady=3, cursor="hand2",
                  command=self.auto_fill_arg_numbers).pack(side="left", padx=(10, 0))
        tk.Label(toolbar, text="green: already a device   ·   blue: differs from Old References",
                 bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left", padx=(16, 0))
        self.status_label = tk.Label(toolbar, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
        self.status_label.pack(side="right", padx=(8, 8))

    def build_table_view(self):
        """The table itself: columns (Added first), row colours, scroll bars, editing / sorting
        bindings and the right-click menu."""
        table_container = tk.Frame(self, bg=PANEL_BG)
        table_container.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        vertical_scrollbar = ttk.Scrollbar(table_container, orient="vertical")
        horizontal_scrollbar = ttk.Scrollbar(table_container, orient="horizontal")
        self.table_view = ttk.Treeview(table_container, columns=TABLE_TAB_COLUMN_IDS, show="headings",
                                       selectmode="extended", yscrollcommand=vertical_scrollbar.set,
                                       xscrollcommand=horizontal_scrollbar.set)
        vertical_scrollbar.configure(command=self.table_view.yview)
        horizontal_scrollbar.configure(command=self.table_view.xview)
        for column_id, column_name, column_width in zip(TABLE_TAB_COLUMN_IDS, TABLE_TAB_COLUMNS, TABLE_TAB_COLUMN_WIDTHS):
            self.table_view.heading(column_id, text=column_name, anchor=tk.W,
                                    command=lambda clicked_column=column_id: self.sort_by_column(clicked_column))
            self.table_view.column(column_id, width=column_width, minwidth=40, anchor=tk.W, stretch=True)
        self.table_view.tag_configure("even_row", background=ROW_EVEN)
        self.table_view.tag_configure("odd_row", background=ROW_ODD)
        theme_name = getattr(self.host_window, "_theme_name", "dark")
        self.table_view.tag_configure("added_row", background=ADDED_ROW_BACKGROUND.get(theme_name, "#1f4a2e"))
        self.table_view.tag_configure("mismatched_row", background=MISMATCHED_ROW_BACKGROUND.get(theme_name, "#1f4f99"))
        self.table_view.tag_configure("logger_row", background=LOGGER_ORANGE, foreground="#000000")
        vertical_scrollbar.pack(side="right", fill="y")
        horizontal_scrollbar.pack(side="bottom", fill="x")
        self.table_view.pack(side="left", fill="both", expand=True)

        self.table_view.bind("<Double-1>", self.on_double_click)
        self.table_view.bind("<Return>", self.edit_selected_row)
        self.table_view.bind("<F2>", self.edit_selected_row)
        self.table_view.bind("<Delete>", lambda event: self.delete_selected_rows())
        self.table_view.bind("<Insert>", lambda event: self.add_row())
        for widget in (self.table_view, vertical_scrollbar, horizontal_scrollbar):
            widget.bind("<Button-1>", lambda event: self.finish_cell_edit(True), add="+")
        for event_name in ("<MouseWheel>", "<Button-4>", "<Button-5>", "<Configure>"):
            self.table_view.bind(event_name, lambda event: self.finish_cell_edit(True), add="+")

        self.row_context_menu = tk.Menu(self, tearoff=False, bg=MID_BG, fg=TEXT_PRI,
                                        activebackground=ACCENT, activeforeground=DARK_BG)
        self.row_context_menu.add_command(label="Insert blank row", command=self.add_row)
        self.row_context_menu.add_command(label="Delete selected row(s)", command=self.delete_selected_rows)
        if self.is_current_reference:                  # the mapping comes from Generate
            self.row_context_menu.add_separator()
            self.row_context_menu.add_command(label="Function Mapping…", command=self.show_function_mapping)
        self.table_view.bind("<Button-2>" if sys.platform == "darwin" else "<Button-3>", self.show_row_context_menu)

    def refresh_status(self):
        """After any change: find the rows that are already a device in the Helios profile
        (one pass, one set lookup per row: a row whose Arg # / Device # / Command # match a
        device), recolour the rows, update the status text, and ask the main window to
        compare Reference with Old References again (coalesced: once when the window is idle)."""
        match_keys = self.interface_match_keys()
        id_column_ids = [TABLE_TAB_COLUMN_IDS[TABLE_TAB_COLUMNS.index(name)]
                         for name in ("Arg #", "Device #", "Command #")]
        self.added_row_ids = set()
        highest_arg_number = 0
        for row_id in self.table_view.get_children():
            arg_text, device_text, command_text = (str(self.table_view.set(row_id, column_id))
                                                   for column_id in id_column_ids)
            row_key = table_row_match_key(arg_text, device_text, command_text)
            if row_key is not None and row_key in match_keys:
                self.added_row_ids.add(row_id)
            arg_number = parse_number_or_none(arg_text)    # same pass: the highest Arg #
            if arg_number is not None and arg_number > highest_arg_number:
                highest_arg_number = int(arg_number)
        self.highest_arg_number = highest_arg_number
        self.compute_logger_rows(match_keys)
        self.apply_row_colors()
        self.notify_host_of_table_change()

    def notify_host_of_table_change(self):
        """Tell the main window to update "Max id used" (current Reference table only) and to
        compare Reference with Old References again."""
        if self.is_current_reference:                      # "Max id used" counts the Reference Arg #
            update_max_id = getattr(self.host_window, "_update_max_id", None)
            if update_max_id is not None:
                update_max_id()
        schedule_comparison = getattr(self.host_window, "schedule_reference_comparison", None)
        if schedule_comparison is not None:
            schedule_comparison()

    def compute_logger_rows(self, match_keys=None):
        """The rows whose Arg # / Device # / Command # the Argument Logger has seen but that no
        device of the interface holds: shown in bright orange (current Reference table only)."""
        self.logger_row_ids = set()
        seen_function = getattr(self.host_window, "logger_seen_ids", None)
        if not self.is_current_reference or seen_function is None:
            return
        seen_args, seen_commands = seen_function()
        if not seen_args and not seen_commands:
            return
        if match_keys is None:
            match_keys = self.interface_match_keys()
        for row_id in self.table_view.get_children():
            arg_id, device_id, command_id = self.row_id_texts(row_id)
            row_key = table_row_match_key(arg_id, device_id, command_id)
            is_unheld = row_key is not None and row_key not in match_keys
            if is_unheld and self.logger_has_seen_ids(arg_id, device_id, command_id, seen_args, seen_commands):
                self.logger_row_ids.add(row_id)

    def interface_match_keys(self):
        """Match keys of the devices the editor holds (empty when the editor cannot say)."""
        match_keys_function = getattr(self.host_window, "table_added_match_keys", None)
        return match_keys_function() if match_keys_function else set()

    def row_id_texts(self, row_id):
        """(Arg #, Device #, Command #) of a table row, normalised."""
        column_ids = [TABLE_TAB_COLUMN_IDS[TABLE_TAB_COLUMNS.index(name)] for name in ("Arg #", "Device #", "Command #")]
        arg_id, device_id, command_id = (normalize_id_text(str(self.table_view.set(row_id, column_id)))
                                         for column_id in column_ids)
        return arg_id, device_id, command_id

    @staticmethod
    def logger_has_seen_ids(arg_id, device_id, command_id, seen_args, seen_commands):
        """True when the logger has seen this row's arg, or its command (with its device or without)."""
        if arg_id and arg_id in seen_args:
            return True
        return bool(command_id) and ((device_id, command_id) in seen_commands or ("", command_id) in seen_commands)

    def update_logger_highlight(self):
        """The logger saw new values: recolour the rows."""
        self.compute_logger_rows()
        self.apply_row_colors()

    def apply_row_colors(self):
        """Colour every row: blue when it differs from the other reference table, else green
        when it is already a device, else the normal alternating shade; then update the
        status text.  O(rows)."""
        for row_position, row_id in enumerate(self.table_view.get_children()):
            if row_id in getattr(self, "logger_row_ids", ()):
                row_tags = ("logger_row",)
            elif row_id in self.mismatched_row_ids:
                row_tags = ("mismatched_row",)
            elif row_id in self.added_row_ids:
                row_tags = ("added_row",)
            else:
                row_tags = ("odd_row" if row_position % 2 else "even_row",)
            self.table_view.item(row_id, tags=row_tags)
        self.update_status_text()

    def update_status_text(self):
        """Row count, added count, mismatched count and file name (* = unsaved changes)."""
        row_count = len(self.table_view.get_children())
        if self.current_file_path:
            file_name = os.path.basename(self.current_file_path)
        elif self.suggested_file_name:
            file_name = f"{self.suggested_file_name} (not saved yet)"
        else:
            file_name = "not saved yet"
        mismatched_text = f"   |   {len(self.mismatched_row_ids)} mismatched" if self.mismatched_row_ids else ""
        self.status_label.configure(
            text=f"{'* ' if self.has_unsaved_changes else ''}{row_count} row{'' if row_count == 1 else 's'}"
                 f"   |   {len(self.added_row_ids)} added{mismatched_text}   |   {file_name}")

    def rows_with_ids(self):
        """[(row id, {column: text})] for every row, in table order (for the comparison)."""
        return [(row_id, {column: str(self.table_view.set(row_id, column_id))
                          for column, column_id in zip(TABLE_TAB_COLUMNS, TABLE_TAB_COLUMN_IDS)})
                for row_id in self.table_view.get_children()]

    def set_cell_text(self, row_id, column, new_text):
        """Change one cell (used by Update).  Returns True when the text changed."""
        column_id = TABLE_TAB_COLUMN_IDS[TABLE_TAB_COLUMNS.index(column)]
        if not self.table_view.exists(row_id) or str(self.table_view.set(row_id, column_id)) == new_text:
            return False
        self.table_view.set(row_id, column_id, new_text)
        return True

    def mark_unsaved(self):
        """Note that the table has changes that are not saved yet, and update the status text."""
        self.has_unsaved_changes = True
        self.refresh_status()

    @staticmethod
    def row_to_cell_texts(table_row):
        """A row dict -> the list of cell texts in column order (missing values become '')."""
        return ["" if table_row.get(column) is None else str(table_row.get(column)) for column in TABLE_TAB_COLUMNS]

    def replace_all_rows(self, rows_of_cell_texts):
        """Replace every row of the table (used by Generate and Load) and clear the sort arrow."""
        self.clear_sort_indicator()
        self.table_view.delete(*self.table_view.get_children())
        for cell_texts in rows_of_cell_texts:
            self.table_view.insert("", tk.END, values=cell_texts)

    def close_table(self):
        """Close the table: no rows, no file, nothing unsaved.  For the Reference tab the lists
        that came with the table (viewports, sources, Build Device details, device names) are
        emptied too.  The caller saves first when the table has to be kept."""
        self.finish_cell_edit(True)
        self.replace_all_rows(())
        self.function_mapping = []
        if self.is_current_reference:
            for update_name in ("update_viewport_list", "update_source_list"):
                update_list = getattr(self.host_window, update_name, None)
                if update_list is not None:
                    update_list([])
            self.host_window._function_return_types = {}
            self.host_window._element_details = {}
            self.host_window._discovered_devices = {}
        self.current_file_path = None
        self.suggested_file_name = ""
        self.has_unsaved_changes = False
        self.table_aircraft = None
        self.refresh_status()

    # ------------------------------------------------------------------ keeping the rows across tab rebuilds
    def export_state(self):
        """Everything needed to rebuild this tab (used when Helios rebuilds its tabs)."""
        self.finish_cell_edit(True)
        return {
            "rows": [[str(self.table_view.set(row_id, column_id)) for column_id in TABLE_TAB_COLUMN_IDS]
                     for row_id in self.table_view.get_children()],
            "current_file_path": self.current_file_path,
            "suggested_file_name": self.suggested_file_name,
            "has_unsaved_changes": self.has_unsaved_changes,
            "function_mapping": self.function_mapping,
            "loaded_file_contents": self.loaded_file_contents,
            "table_aircraft": getattr(self, "table_aircraft", None),
        }

    def restore_state(self, saved_state):
        """Put back the rows, file path, unsaved flag and function mapping saved by
        export_state."""
        self.replace_all_rows(saved_state.get("rows", []))
        self.current_file_path = saved_state.get("current_file_path")
        self.suggested_file_name = saved_state.get("suggested_file_name", "")
        self.has_unsaved_changes = saved_state.get("has_unsaved_changes", False)
        self.function_mapping = saved_state.get("function_mapping", [])
        self.loaded_file_contents = saved_state.get("loaded_file_contents")
        self.table_aircraft = saved_state.get("table_aircraft")

    # ------------------------------------------------------------------ sorting
    @staticmethod
    def natural_sort_key(cell_text):
        """Numbers sort by value, text sorts naturally (Button_2 before Button_10)."""
        stripped_text = cell_text.strip()
        try:
            return (0, float(stripped_text), "")
        except ValueError:
            text_pieces = re.split(r"(\d+)", stripped_text.lower())
            return (1, 0.0, tuple((0, int(piece), "") if piece.isdigit() else (1, 0, piece) for piece in text_pieces))

    def rows_sorted_by(self, row_ids, column_id, descending):
        """Row ids ordered by one column; blank cells stay at the bottom either way."""
        filled_row_ids = [row_id for row_id in row_ids if str(self.table_view.set(row_id, column_id)).strip()]
        blank_row_ids = [row_id for row_id in row_ids if not str(self.table_view.set(row_id, column_id)).strip()]
        filled_row_ids.sort(key=lambda row_id: self.natural_sort_key(str(self.table_view.set(row_id, column_id))),
                            reverse=descending)
        return filled_row_ids + blank_row_ids

    def sort_by_column(self, column_id):
        """Header clicked: sort by that column (again to reverse); Device # also orders each
        device's rows by Command #. Blank cells stay at the bottom."""
        self.finish_cell_edit(True)
        if self.sorted_column_id == column_id:
            self.sort_descending = not self.sort_descending
        else:
            self.sorted_column_id, self.sort_descending = column_id, False
        original_order = list(self.table_view.get_children())
        new_order = original_order
        # sort by the tie-breaker first; Python's sort is stable so it survives the main sort
        secondary_column = SECONDARY_SORT_COLUMN.get(TABLE_TAB_COLUMNS[TABLE_TAB_COLUMN_IDS.index(column_id)])
        if secondary_column in TABLE_TAB_COLUMNS:
            new_order = self.rows_sorted_by(new_order, TABLE_TAB_COLUMN_IDS[TABLE_TAB_COLUMNS.index(secondary_column)],
                                            self.sort_descending)
        new_order = self.rows_sorted_by(new_order, column_id, self.sort_descending)
        for new_position, row_id in enumerate(new_order):
            self.table_view.move(row_id, "", new_position)
        self.update_sort_indicator()
        if new_order != original_order:
            self.mark_unsaved()                 # the saved file follows the table order
        else:
            self.refresh_status()

    def update_sort_indicator(self):
        """Show an up / down arrow on the header of the column the table is sorted by (and none on
        the others), so the current sort order is visible."""
        for column_id, column_name in zip(TABLE_TAB_COLUMN_IDS, TABLE_TAB_COLUMNS):
            arrow_text = ""
            if column_id == self.sorted_column_id:
                arrow_text = "  \u25bc" if self.sort_descending else "  \u25b2"
            self.table_view.heading(column_id, text=column_name + arrow_text)

    def clear_sort_indicator(self):
        """Forget which column the table was sorted by and remove the arrow from its header (used
        after Generate / Load replace the rows)."""
        self.sorted_column_id, self.sort_descending = None, False
        self.update_sort_indicator()

    # ------------------------------------------------------------------ cell editing
    def on_double_click(self, event):
        """Double-click: edit the clicked cell (the Added column is skipped), or add a row when
        the empty area is clicked."""
        clicked_region = self.table_view.identify_region(event.x, event.y)
        if clicked_region == "nothing":
            self.add_row()
            return
        if clicked_region != "cell":
            return
        row_id = self.table_view.identify_row(event.y)
        column_reference = self.table_view.identify_column(event.x)       # "#3"
        if row_id and column_reference:
            self.start_cell_edit(row_id, int(column_reference[1:]) - 1)

    def edit_selected_row(self, event=None):
        """Enter / F2: start editing the selected row's first editable cell."""
        selected_row_ids = self.table_view.selection()
        if selected_row_ids:
            self.start_cell_edit(selected_row_ids[0], 0)
        return "break"

    def start_cell_edit(self, row_id, column_position):
        """Place a text box over one cell and bind its keys: Enter keeps, Esc cancels, Tab /
        Shift+Tab move to the next / previous cell."""
        self.finish_cell_edit(True)
        self.table_view.see(row_id)
        self.table_view.update_idletasks()
        cell_box = self.table_view.bbox(row_id, TABLE_TAB_COLUMN_IDS[column_position])
        if not cell_box:
            return
        box_x, box_y, box_width, box_height = cell_box
        cell_entry = tk.Entry(self.table_view, bg=MID_BG, fg=TEXT_PRI, insertbackground=TEXT_PRI,
                              relief="flat", font=FONT_MONO, highlightthickness=1,
                              highlightcolor=ACCENT, highlightbackground=BORDER)
        cell_entry.insert(0, self.table_view.set(row_id, TABLE_TAB_COLUMN_IDS[column_position]))
        cell_entry.select_range(0, tk.END)
        cell_entry.place(x=box_x, y=box_y, width=box_width, height=box_height)
        cell_entry.focus_set()
        self.active_cell_editor = (cell_entry, row_id, column_position)
        cell_entry.bind("<Return>", lambda event: self.finish_edit_and_refocus())
        cell_entry.bind("<KP_Enter>", lambda event: self.finish_edit_and_refocus())
        cell_entry.bind("<Escape>", lambda event: self.finish_edit_and_refocus(keep_change=False))
        cell_entry.bind("<Tab>", lambda event: self.move_cell_edit(1))
        cell_entry.bind("<Shift-Tab>", lambda event: self.move_cell_edit(-1))
        cell_entry.bind("<ISO_Left_Tab>", lambda event: self.move_cell_edit(-1))
        cell_entry.bind("<FocusOut>", lambda event: self.finish_cell_edit(True))
        self.table_view.selection_set(row_id)

    def finish_edit_and_refocus(self, keep_change=True):
        """Finish the cell edit (keeping or dropping the change) and give focus back to the
        table."""
        self.finish_cell_edit(keep_change)
        self.table_view.focus_set()
        return "break"

    def finish_cell_edit(self, keep_change=True):
        """Close the cell text box and store its text in the cell when keep_change is True and
        the text changed."""
        if not self.active_cell_editor:
            return
        cell_entry, row_id, column_position = self.active_cell_editor
        self.active_cell_editor = None          # cleared first so FocusOut from destroy() does nothing
        new_text = cell_entry.get()
        cell_entry.destroy()
        if not keep_change or not self.table_view.exists(row_id):
            return
        if new_text != self.table_view.set(row_id, TABLE_TAB_COLUMN_IDS[column_position]):
            self.table_view.set(row_id, TABLE_TAB_COLUMN_IDS[column_position], new_text)
            self.mark_unsaved()

    def move_cell_edit(self, step):
        """Tab / Shift+Tab: finish this cell and edit the next / previous one, wrapping to the
        next / previous row and skipping Added."""
        if not self.active_cell_editor:
            return "break"
        _unused_entry, row_id, column_position = self.active_cell_editor
        all_row_ids = list(self.table_view.get_children())
        self.finish_cell_edit(True)
        column_position += step
        row_position = all_row_ids.index(row_id) if row_id in all_row_ids else 0
        if column_position >= len(TABLE_TAB_COLUMNS):
            column_position, row_position = 0, row_position + 1
        elif column_position < 0:
            column_position, row_position = len(TABLE_TAB_COLUMNS) - 1, row_position - 1
        if 0 <= row_position < len(all_row_ids):
            self.start_cell_edit(all_row_ids[row_position], column_position)
        return "break"

    # ------------------------------------------------------------------ rows
    def add_row(self):
        """Insert a blank row after the selection (or at the end) and start editing it."""
        self.finish_cell_edit(True)
        selected_row_ids = self.table_view.selection()
        insert_position = self.table_view.index(selected_row_ids[-1]) + 1 if selected_row_ids else tk.END
        new_row_id = self.table_view.insert("", insert_position, values=[""] * len(TABLE_TAB_COLUMNS))
        self.mark_unsaved()
        self.start_cell_edit(new_row_id, 0)

    def delete_selected_rows(self):
        """Delete key / right-click Delete: remove the selected rows from the table, mark the table
        unsaved and refresh the colours, counts and comparison (refresh_status)."""
        self.finish_cell_edit(False)
        selected_row_ids = self.table_view.selection()
        if selected_row_ids:
            self.table_view.delete(*selected_row_ids)
            self.mark_unsaved()

    def show_row_context_menu(self, event):
        """Right-click: select the clicked row and show Insert / Delete / Function Mapping."""
        row_id = self.table_view.identify_row(event.y)
        if row_id and row_id not in self.table_view.selection():
            self.table_view.selection_set(row_id)
        self.row_context_menu.tk_popup(event.x_root, event.y_root)

    # ------------------------------------------------------------------ Table ▸ Generate…
    def ask_generation_folder(self):
        """Ask for the aircraft folder Generate searches (the picker starts in the DCS install's
        Mods\\aircraft folder, default_aircraft_folder).  Returns the folder, or "" when cancelled."""
        return filedialog.askdirectory(title="Select the aircraft folder to search for clickabledata.lua",
                                       mustexist=True, parent=self.host_window,
                                       initialdir=default_aircraft_folder())

    def generate_table(self):
        """Table > Generate: ask for a folder, save and close the table that is open
        (save_and_close_table; Generate stops when that save is cancelled) and generate the
        new table from the folder (generate_table_from_chosen_folder).  Returns True when a
        table was made."""
        chosen_folder = self.ask_generation_folder()
        if not chosen_folder or not self.save_and_close_table():
            return False
        return self.generate_table_from_chosen_folder(chosen_folder)

    def save_and_close_table(self):
        """Save the table when it has unsaved changes (to its file; Save As when it has none),
        then close it (close_table).  Returns False - closing nothing - when the save was
        cancelled or failed, so no work is lost; True otherwise (also when no table was open)."""
        self.finish_cell_edit(True)
        if not self.confirm_discard_changes():          # asks: save first? (Yes / No / Cancel)
            return False
        self.close_table()
        return True

    def generate_table_from_chosen_folder(self, chosen_folder):
        """Run generate_table_from_folder on chosen_folder, show the rows, the viewport list
        and the Source tab, put the vehicles found in the interface header, give every row
        without an Arg # one (Auto-fill Id's) and say "Reference Generation Complete".
        Returns True when a table was made."""
        self.host_window.config(cursor="watch")
        self.status_label.configure(text=f"Searching {chosen_folder} …")
        self.host_window.update_idletasks()
        try:
            result = generate_table_from_folder(chosen_folder)
        except Exception as unexpected_error:      # keep the window alive on unexpected input
            messagebox.showerror("Generate failed", f"Something went wrong while processing:\n{unexpected_error}",
                                 parent=self.host_window)
            return False
        finally:
            self.host_window.config(cursor="")
            self.refresh_status()
        if not result.clickabledata_paths and not result.input_file_paths:
            messagebox.showinfo("Generate", f"No clickabledata.lua or Input folder was found in:\n{chosen_folder}",
                                parent=self.host_window)
            return False
        self.show_generated_result(result)
        self.current_file_path = None
        self.suggested_file_name = reference_table_file_name(chosen_folder)   # e.g. "MyJet Reference Table.json"
        self.table_aircraft = chosen_folder_name(chosen_folder) or None
        self.has_unsaved_changes = True
        self.auto_fill_arg_numbers(show_message=False)  # every generated row gets an Arg #
        self.refresh_status()
        table_loaded = getattr(self.host_window, "reference_table_loaded", None)
        if self.is_current_reference and table_loaded is not None:
            table_loaded(self)
        messagebox.showinfo("Generate", "Reference Generation Complete", parent=self.host_window)
        return True

    def show_generated_result(self, result):
        """Put a generation result where it is shown: the rows, the Viewport and Source tabs, the
        recorded function / element / device details and the header's Vehicles field."""
        self.replace_all_rows(self.row_to_cell_texts(table_row) for table_row in result.table_rows)
        self.function_mapping = result.function_mapping
        show_viewports = getattr(self.host_window, "update_viewport_list", None)
        if show_viewports is not None:                  # fill the Viewport tab
            show_viewports(result.viewport_calls)
        show_sources = getattr(self.host_window, "update_source_list", None)
        if show_sources is not None:                    # fill the Source tab
            show_sources(result.source_rows, result.file_variables)
        self.host_window._function_return_types = dict(result.function_return_types)
        self.host_window._element_details = dict(result.element_details)
        self.host_window._discovered_devices = dict(result.discovered_devices)
        show_vehicles = getattr(self.host_window, "apply_generated_vehicles", None)
        if show_vehicles is not None:                   # fill the header's Vehicles field
            show_vehicles(result.vehicle_names)

    def show_function_mapping(self):
        """Window listing each element function's hint / device / command / arg parameters,
        with an Export button."""
        if not self.function_mapping:
            messagebox.showinfo("Function Mapping", "Run Table ▸ Generate… first to build the function mapping.",
                                parent=self.host_window)
            return
        mapping_window = tk.Toplevel(self.host_window)
        mapping_window.title("Function Mapping")
        mapping_window.configure(bg=PANEL_BG)
        mapping_window.geometry("1100x450")
        mapping_columns = ("Function", "Hint", "Device", "Command(s)", "Arg(s)", "All Parameters", "Defined In")
        mapping_widths = (190, 90, 90, 160, 110, 260, 200)
        mapping_frame = tk.Frame(mapping_window, bg=PANEL_BG)
        mapping_frame.pack(fill="both", expand=True, padx=6, pady=6)
        mapping_view = ttk.Treeview(mapping_frame, columns=mapping_columns, show="headings")
        for column_name, column_width in zip(mapping_columns, mapping_widths):
            mapping_view.heading(column_name, text=column_name, anchor=tk.W)
            mapping_view.column(column_name, width=column_width, anchor=tk.W)
        for mapping_entry in self.function_mapping:
            mapping_view.insert("", tk.END, values=(
                mapping_entry["function"], ", ".join(mapping_entry["hint"]), ", ".join(mapping_entry["device"]),
                ", ".join(mapping_entry["commands"]), ", ".join(mapping_entry["args"]),
                ", ".join(mapping_entry["parameters"]), mapping_entry["file"]))
        mapping_scrollbar = ttk.Scrollbar(mapping_frame, orient="vertical", command=mapping_view.yview)
        mapping_view.configure(yscrollcommand=mapping_scrollbar.set)
        mapping_scrollbar.pack(side="right", fill="y")
        mapping_view.pack(side="left", fill="both", expand=True)

        def export_function_mapping():
            """Export button of the Function Mapping window: ask for a file name and save the
            mapping (each element function with its hint / device / command / arg parameters) as
            JSON."""
            export_path = filedialog.asksaveasfilename(parent=mapping_window, title="Export function mapping",
                                                       defaultextension=".json", filetypes=JSON_FILE_TYPES,
                                                       initialfile="function_mapping.json")
            if export_path:
                try:
                    with open(export_path, "w", encoding="utf-8") as export_file:
                        json.dump(self.function_mapping, export_file, indent=4, ensure_ascii=False)
                except OSError as write_error:
                    messagebox.showerror("Export failed", str(write_error), parent=mapping_window)

        tk.Button(mapping_window, text="Export Mapping as JSON…", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=14, pady=3, cursor="hand2",
                  command=export_function_mapping).pack(side="right", padx=6, pady=(0, 6))

    # ------------------------------------------------------------------ Table ▸ Load / Save / Save As
    def collect_table_rows(self):
        """Every row as {column: text} (the green marks are worked out fresh first)."""
        self.refresh_status()
        table_rows = [{column: str(self.table_view.set(row_id, column_id))
                       for column, column_id in zip(TABLE_TAB_COLUMNS, TABLE_TAB_COLUMN_IDS)}
                      for row_id in self.table_view.get_children()]
        return table_rows or [dict.fromkeys(TABLE_TAB_COLUMNS, "")]     # empty table -> one blank entry

    def build_table_file_contents(self, file_path=None):
        """What Save writes to file_path.
        Reference: the table rows and the Viewport tab's list
            {"table": [{"Type": ..., "Arg #": ..., ...}, ...],
             "viewports": [{"Viewport": "F4E_LEFT_MFCD", "File": "C:/.../mfcd_init.lua"}, ...]}
        Old References: only the table part changes.  The rest (viewports ...) is taken from
        the file being written when it exists, else from the file that was loaded, so viewport
        data is never altered.  A file in the older list-of-rows format stays a list."""
        if not self.is_current_reference:
            return self.build_old_reference_file_contents(file_path)
        viewport_calls = getattr(self.host_window, "_viewport_calls", []) or []
        return {
            TABLE_FILE_TABLE_KEY: self.collect_table_rows(),
            TABLE_FILE_VIEWPORTS_KEY: [dict(zip(VIEWPORT_FILE_FIELDS, (viewport_text, file_path)))
                                       for viewport_text, file_path in viewport_calls],
            TABLE_FILE_RETURN_TYPES_KEY: dict(getattr(self.host_window, "_function_return_types", {}) or {}),
            TABLE_FILE_ELEMENT_DETAILS_KEY: dict(getattr(self.host_window, "_element_details", {}) or {}),
            TABLE_FILE_DEVICE_NAMES_KEY: [
                {"Device": device_name, "Device #": discovered_devices[device_name]}
                for discovered_devices in [getattr(self.host_window, "_discovered_devices", {}) or {}]
                for device_name in sorted_device_names(discovered_devices)],
        }

    @staticmethod
    def split_table_file_contents(loaded_data):
        """Accepts the current format ({"table": [...], "viewports": [...]}) and the older
        list-of-rows format.  Returns (table rows data, viewport list data or None)."""
        if isinstance(loaded_data, dict) and (TABLE_FILE_TABLE_KEY in loaded_data
                                              or TABLE_FILE_VIEWPORTS_KEY in loaded_data):
            return loaded_data.get(TABLE_FILE_TABLE_KEY, []), loaded_data.get(TABLE_FILE_VIEWPORTS_KEY)
        return loaded_data, None

    @staticmethod
    def validate_loaded_viewports(viewport_data):
        """[{"Viewport": ..., "File": ...}, ...] -> [(viewport text, file path)], or an error."""
        if not isinstance(viewport_data, list):
            return None, "The file's viewports must be a list."
        viewport_calls = []
        for entry_number, entry in enumerate(viewport_data, start=1):
            if isinstance(entry, dict):
                viewport_calls.append((str(entry.get("Viewport", "")), str(entry.get("File", ""))))
            elif isinstance(entry, str):
                viewport_calls.append((entry, ""))
            else:
                return None, f"Viewport entry {entry_number} is not an object."
        return viewport_calls, None

    @staticmethod
    def validate_loaded_json(loaded_data):
        """Check the rows read from a table file before they replace the table: it must be a list
        of objects (or one object), each with exactly the TABLE_COLUMNS keys (an older 'Added'
        key is dropped). Returns (rows of cell texts in column order, None), or (None, a message
        saying which entry is wrong)."""
        if isinstance(loaded_data, dict):
            loaded_data = [loaded_data]
        if not isinstance(loaded_data, list):
            return None, "The JSON file must contain a list of objects."
        rows_of_cell_texts = []
        for entry_number, entry in enumerate(loaded_data, start=1):
            cell_texts, error_message = CommandTablePanel.cell_texts_of_entry(entry_number, entry)
            if error_message:
                return None, error_message
            rows_of_cell_texts.append(cell_texts)
        return rows_of_cell_texts, None

    @staticmethod
    def entry_key_problems(entry_number, entry_keys):
        """Message when an entry's keys differ from the table columns, else None."""
        expected_keys = set(TABLE_TAB_COLUMNS)
        if entry_keys == expected_keys:
            return None
        problems = []
        if expected_keys - entry_keys:
            problems.append("missing: " + ", ".join(sorted(expected_keys - entry_keys)))
        if entry_keys - expected_keys:
            problems.append("unexpected: " + ", ".join(sorted(entry_keys - expected_keys)))
        return f"Entry {entry_number} does not match the table format ({'; '.join(problems)})."

    @staticmethod
    def cell_texts_of_entry(entry_number, entry):
        """(cell texts in column order, None) for one entry of a table file, or (None, message)."""
        if not isinstance(entry, dict):
            return None, f"Entry {entry_number} is not an object."
        if ADDED_COLUMN in entry:                       # files saved while the Added column existed
            entry = {key: value for key, value in entry.items() if key != ADDED_COLUMN}
        key_problem = CommandTablePanel.entry_key_problems(entry_number, set(entry))
        if key_problem:
            return None, key_problem
        cell_texts = []
        for column in TABLE_TAB_COLUMNS:
            cell_value = entry[column]
            if isinstance(cell_value, (dict, list)):
                return None, f"Entry {entry_number}, '{column}' must be a simple value, not a {type(cell_value).__name__}."
            cell_texts.append(CommandTablePanel.cell_value_text(cell_value))
        return cell_texts, None

    @staticmethod
    def cell_value_text(cell_value):
        """A simple JSON value as the text shown in a table cell."""
        if cell_value is None:
            return ""
        if isinstance(cell_value, bool):
            return "true" if cell_value else "false"
        if isinstance(cell_value, (int, float)):
            return format_number_text(cell_value)   # older files with numbers load as text
        return str(cell_value)

    def build_old_reference_file_contents(self, file_path):
        """Old References ▸ Save: the target file (or the loaded file) with its table replaced."""
        table_rows = self.collect_table_rows()
        base_contents = None
        if file_path and os.path.exists(file_path):
            try:
                with open(file_path, "r", encoding="utf-8") as existing_file:
                    base_contents = json.load(existing_file)
            except (OSError, ValueError):
                base_contents = None                   # unreadable: write a fresh file
        if base_contents is None:
            base_contents = self.loaded_file_contents
        if isinstance(base_contents, list):            # older list-of-rows format stays a list
            return table_rows
        if isinstance(base_contents, dict):
            file_contents = dict(base_contents)        # every other key kept as it was
            file_contents[TABLE_FILE_TABLE_KEY] = table_rows
            return file_contents
        return {TABLE_FILE_TABLE_KEY: table_rows, TABLE_FILE_VIEWPORTS_KEY: []}

    def load_table(self):
        """Table > Load: read a table file (current or older format), put its rows in the Table
        tab and its viewports in the Viewport tab.  The dialog opens in the reference-table
        folder (default_reference_table_folder, created when missing)."""
        self.finish_cell_edit(True)
        if not self.confirm_discard_changes():
            return
        load_title = "Load table" if self.is_current_reference else "Load old reference table"
        chosen_path = filedialog.askopenfilename(title=load_title, filetypes=JSON_FILE_TYPES, parent=self.host_window,
                                                 initialdir=default_reference_table_folder())
        loaded_data = self.read_table_file(chosen_path) if chosen_path else None
        checked_file = self.check_table_file(loaded_data) if loaded_data is not None else None
        if checked_file is None:
            return
        rows_of_cell_texts, viewport_calls = checked_file
        table_aircraft = reference_table_aircraft(loaded_data, chosen_path)
        if self.is_current_reference and not self._current_table_load_allowed(table_aircraft):
            return                                     # refused: the current table is kept
        self.replace_all_rows(rows_of_cell_texts)
        self.show_loaded_table_extras(loaded_data, viewport_calls)
        self.current_file_path = chosen_path
        self.suggested_file_name = ""                  # a loaded table is named by its own file
        self.has_unsaved_changes = False
        self.table_aircraft = table_aircraft
        self.refresh_status()
        table_loaded = getattr(self.host_window, "reference_table_loaded", None)
        if self.is_current_reference and table_loaded is not None:
            table_loaded(self)

    def show_loaded_table_extras(self, loaded_data, viewport_calls):
        """Hand a loaded file's Build Device details and viewports on to where they belong."""
        if self.is_current_reference and isinstance(loaded_data, dict):   # Build Device details, when saved
            self.store_build_device_details(loaded_data)
        show_viewports = getattr(self.host_window, "update_viewport_list", None)
        if viewport_calls is not None and show_viewports is not None:   # the file's viewports go to the Viewport tab
            show_viewports(viewport_calls)

    def check_table_file(self, loaded_data):
        """(rows of cell texts, viewport calls or None) from a table file's JSON, or None after
        telling the person what is wrong with it."""
        table_data, viewport_data = self.split_table_file_contents(loaded_data)
        rows_of_cell_texts, error_message = self.validate_loaded_json(table_data)
        if error_message:
            messagebox.showerror("Load failed", f"{error_message}\n\nEach entry must have exactly these keys:\n"
                                 + ", ".join(TABLE_TAB_COLUMNS), parent=self.host_window)
            return None
        viewport_calls = None
        if not self.is_current_reference:
            viewport_data = None                       # Old References reads only the table part
            self.loaded_file_contents = loaded_data    # kept so Save leaves the rest unaltered
        if viewport_data is not None:
            viewport_calls, error_message = self.validate_loaded_viewports(viewport_data)
            if error_message:
                messagebox.showerror("Load failed", error_message, parent=self.host_window)
                return None
        return rows_of_cell_texts, viewport_calls

    def _current_table_load_allowed(self, table_aircraft) -> bool:
        """The main window may refuse a table of another aircraft; True when loading may go on."""
        load_allowed = getattr(self.host_window, "reference_load_allowed", None)
        return load_allowed is None or bool(load_allowed(table_aircraft))

    def read_table_file(self, file_path):
        """The JSON in a table file, or None (after telling the person) when it cannot be read."""
        try:
            with open(file_path, "r", encoding="utf-8") as json_file:
                return json.load(json_file)
        except json.JSONDecodeError as json_error:
            messagebox.showerror("Load failed", f"Not a valid JSON file:\n{json_error}", parent=self.host_window)
        except OSError as read_error:
            messagebox.showerror("Load failed", f"Could not open file:\n{read_error}", parent=self.host_window)
        return None

    def store_build_device_details(self, loaded_data):
        """Keep the function return types, element details and device names a table file holds
        for Build Device."""
        return_types = loaded_data.get(TABLE_FILE_RETURN_TYPES_KEY)
        element_details = loaded_data.get(TABLE_FILE_ELEMENT_DETAILS_KEY)
        self.host_window._function_return_types = return_types if isinstance(return_types, dict) else {}
        self.host_window._element_details = element_details if isinstance(element_details, dict) else {}
        device_entries = loaded_data.get(TABLE_FILE_DEVICE_NAMES_KEY)
        self.host_window._discovered_devices = {
            str(entry.get("Device", "")).strip(): str(entry.get("Device #", "") or "")
            for entry in (device_entries if isinstance(device_entries, list) else [])
            if isinstance(entry, dict) and str(entry.get("Device", "")).strip()}

    def table_unchanged_since_save(self):
        """True when the table has a file and what Save would write is exactly what that file
        already holds (no difference since the last save), so it need not be written again."""
        self.finish_cell_edit(True)
        if not self.current_file_path or not os.path.isfile(self.current_file_path):
            return False
        try:
            with open(self.current_file_path, "r", encoding="utf-8") as json_file:
                saved_contents = json.load(json_file)
            current_contents = json.loads(json.dumps(self.build_table_file_contents(self.current_file_path),
                                                     ensure_ascii=False))
        except (OSError, ValueError, TypeError):
            return False
        if current_contents != saved_contents:
            return False
        self.has_unsaved_changes = False                 # edited back to what is saved
        self.update_status_text()
        return True

    def save_table(self):
        """Table > Save: write to the current table file (Save As when there is none)."""
        self.finish_cell_edit(True)
        if not self.current_file_path:
            return self.save_table_as()
        return self.write_table_file(self.current_file_path)

    def save_table_as(self):
        """Table > Save As: choose a file name and write the table file.  The dialog opens in the
        table's own folder, else the reference-table folder (default_reference_table_folder,
        created when missing), and suggests the current file name, else the name Generate gave
        the table ("<folder> Reference Table.json"), else a default."""
        self.finish_cell_edit(True)
        chosen_path = filedialog.asksaveasfilename(
            title="Save table as" if self.is_current_reference else "Save old reference table as",
            defaultextension=".json", filetypes=JSON_FILE_TYPES, parent=self.host_window,
            initialdir=dialog_start_folder(self.current_file_path, default_reference_table_folder),
            initialfile=(os.path.basename(self.current_file_path) if self.current_file_path
                         else self.suggested_file_name
                         or ("table.json" if self.is_current_reference else "old_reference.json")))
        if not chosen_path:
            return False
        return self.write_table_file(chosen_path)

    def write_table_file(self, file_path):
        """Write the table and the viewport list to file_path as JSON and mark the table saved."""
        file_contents = self.build_table_file_contents(file_path)     # read the target before overwriting it
        try:
            with open(file_path, "w", encoding="utf-8") as json_file:
                json.dump(file_contents, json_file, indent=4, ensure_ascii=False)
        except OSError as write_error:
            messagebox.showerror("Save failed", f"Could not write file:\n{write_error}", parent=self.host_window)
            return False
        self.current_file_path = file_path
        self.has_unsaved_changes = False
        self.refresh_status()
        return True

    def auto_fill_arg_numbers(self, show_message=True):
        """Auto-fill Id's: every row whose Arg # is blank gets the next free Arg #, counting up
        from the highest Arg # already in this table, in table order (top to bottom).
        Rows that already have an Arg # are never changed.  Two passes over the rows: O(rows).
        Generate runs it with show_message False (no message box).  Returns the rows filled."""
        self.finish_cell_edit(True)
        arg_column_id = TABLE_TAB_COLUMN_IDS[TABLE_TAB_COLUMNS.index("Arg #")]
        row_ids = self.table_view.get_children()
        highest_arg_number = 0
        for row_id in row_ids:
            arg_number = parse_number_or_none(self.table_view.set(row_id, arg_column_id))
            if arg_number is not None:
                highest_arg_number = max(highest_arg_number, int(arg_number))
        next_arg_number, filled_count = highest_arg_number + 1, 0
        for row_id in row_ids:
            if not str(self.table_view.set(row_id, arg_column_id)).strip():
                self.table_view.set(row_id, arg_column_id, str(next_arg_number))
                next_arg_number += 1
                filled_count += 1
        if filled_count:
            self.mark_unsaved()
            message = (f"Gave {filled_count} row{'' if filled_count == 1 else 's'} an Arg #, "
                       f"{highest_arg_number + 1} to {next_arg_number - 1}.")
        else:
            message = "Every row already has an Arg #."
        if show_message:
            messagebox.showinfo("Auto-fill Id's", message, parent=self.host_window)
        return filled_count

    # ------------------------------------------------------------------ Build Device
    def build_device_from_selected_row(self):
        """Build Device button.  One selected row: Device Information for it.  Several rows:
        a Selection window lists them (to the right) and Device Information goes through them
        in order; each can be added (Create / Review), skipped, combined with a second entry
        picked in the Selection window, or removed from the list; the previous device's name
        is the Device default for the next row that has no device of its own.  A Details
        window (below) shows Hint / arg_lim / arg_val for rows with Arg #, Device # and
        Command #.  Cancel stops."""
        self.finish_cell_edit(True)
        entries = self.selected_entries_to_build()
        if entries is None:
            return
        selection_window = SelectionWindow(self.host_window, entries) if len(entries) > 1 else None
        try:
            added_count = self.build_entries_in_turn(entries, selection_window)
        finally:
            if selection_window is not None and selection_window.winfo_exists():
                selection_window.destroy()
        if added_count and self.winfo_exists():
            self.status_label.configure(text=f"Added {added_count} device{'' if added_count == 1 else 's'}")
            self.after(2500, lambda: self.winfo_exists() and self.refresh_status())

    def build_entries_in_turn(self, entries, selection_window):
        """Device Information for each remaining entry in turn (just the one without a Selection
        window).  Returns how many devices were added."""
        previous_device_name, added_count = "", 0
        while True:
            remaining = selection_window.remaining_entries() if selection_window else entries
            if not remaining:
                break
            entry_key, table_row = remaining[0]
            stop, added_device_name = self.build_one_entry(selection_window, entry_key, table_row,
                                                           previous_device_name)
            if added_device_name is not None:
                added_count += 1
                previous_device_name = added_device_name
            if stop or not selection_window:
                break
        return added_count

    def selected_entries_to_build(self):
        """[(row id, row as {column: text})] for the selected rows, or None when nothing is
        selected or the person declines to build a device that is already in the profile."""
        selected_row_ids = [row_id for row_id in self.table_view.get_children() if row_id in self.table_view.selection()]
        if not selected_row_ids:
            messagebox.showinfo("Build Device", "Select one or more rows in the table first.", parent=self.host_window)
            return None
        entries = [(row_id, {column: str(self.table_view.set(row_id, column_id))
                             for column, column_id in zip(TABLE_TAB_COLUMNS, TABLE_TAB_COLUMN_IDS)})
                   for row_id in selected_row_ids]
        if len(entries) == 1 and entries[0][0] in self.added_row_ids and not messagebox.askyesno(
                "Build Device", "A device with these ids is already in the profile.\n\nBuild another one?",
                parent=self.host_window):
            return None
        return entries

    def ask_device_information(self, selection_window, entry_key, table_row, previous_device_name, element_detail):
        """Show Device Information (and the Details window below it when the row has Arg #,
        Device # and Command #) and wait; returns the dialog's result (None = cancelled)."""
        dialog = BuildDeviceDialog(self.host_window, table_row,
                                   getattr(self.host_window, "_function_return_types", {}), element_detail,
                                   getattr(self.host_window, "_discovered_devices", {}) or {},
                                   previous_device_name, selection_window, entry_key)
        if selection_window:
            place_beside(dialog, selection_window, "right")
        details_window = None
        if all(table_row.get(column, "").strip() for column in ("Arg #", "Device #", "Command #")):
            details_window = DeviceDetailsWindow(self.host_window, element_detail)
            place_beside(dialog, details_window, "below")
        self.host_window.wait_window(dialog)
        if details_window is not None and details_window.winfo_exists():
            details_window.destroy()             # Details closes with Device Information
        return dialog.result

    def build_one_entry(self, selection_window, entry_key, table_row, previous_device_name):
        """Device Information for one row.  Returns (stop, name of the device that was added or
        None): stop is True when the person cancelled."""
        if selection_window:
            selection_window.mark_current(entry_key)
        element_details = getattr(self.host_window, "_element_details", {}) or {}
        element_detail = element_details.get(table_row.get("Note", "").strip())
        choice = self.ask_device_information(selection_window, entry_key, table_row, previous_device_name,
                                             element_detail)
        if choice is None:                       # Cancel / window closed
            return True, None
        if choice["action"] == "skip":
            if selection_window:
                selection_window.remove_entry(entry_key)
            return False, None
        built_row = dict(table_row, **{"Device": choice["device_name"], "Device #": choice["device_number"]})
        new_function = build_default_device(built_row, choice["helios_type"], choice["name"], element_detail)
        if choice["combined_row"] is not None:
            apply_combined_entry(new_function, choice["helios_type"], built_row, choice["combined_row"])
        add_device = getattr(self.host_window, "add_built_device", None)
        if add_device is None or not add_device(new_function, choice["action"] == "review"):
            return False, None
        if selection_window:
            selection_window.remove_entry(entry_key)
            selection_window.remove_entry(choice["combined_key"])
        return False, choice["device_name"]

    def confirm_discard_changes(self, title="Unsaved Table Changes"):
        """Ask to save unsaved table changes.  Returns True to continue, False to cancel."""
        self.finish_cell_edit(True)
        if not self.has_unsaved_changes:
            return True
        answer = messagebox.askyesnocancel(title, f"The {self.tab_label} tab has unsaved changes.\n\nSave them first?",
                                           parent=self.host_window)
        if answer is None:
            return False
        return bool(self.save_table()) if answer else True


class MismatchedPanel(tk.Frame):
    """The Mismatched tab: one row per Reference / Old References pair whose numbers differ
    (see compare_reference_tables).  Old values come from Old References, new values from
    Reference.  Sortable by every header (Old / New Device and Device # also sort by the
    matching Command #); rows can be multi-selected; Update copies the new values into
    Old References and into the profile's devices - all rows, or only the selected ones."""

    def __init__(self, parent_frame, host_window):
        """Build the toolbar (Update button, explanation, count) and the table."""
        super().__init__(parent_frame, bg=PANEL_BG)
        self.host_window = host_window
        self.records_by_row_id = {}                   # table row id -> mismatch record
        self.sorted_column_id = None
        self.sort_descending = False

        toolbar = tk.Frame(self, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)
        tk.Button(toolbar, text="⇄  Update", bg=ACCENT2, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=14, pady=3, cursor="hand2",
                  command=self.update_old_values).pack(side="left")
        tk.Label(toolbar, text="Copies the new values into Old References and the matching devices "
                               "(all rows, or only the selected ones)",
                 bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left", padx=(16, 0))
        self.count_label = tk.Label(toolbar, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
        self.count_label.pack(side="right", padx=(8, 8))

        table_container = tk.Frame(self, bg=PANEL_BG)
        table_container.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        vertical_scrollbar = ttk.Scrollbar(table_container, orient="vertical")
        horizontal_scrollbar = ttk.Scrollbar(table_container, orient="horizontal")
        self.mismatched_view = ttk.Treeview(table_container, columns=MISMATCHED_COLUMN_IDS, show="headings",
                                            selectmode="extended", yscrollcommand=vertical_scrollbar.set,
                                            xscrollcommand=horizontal_scrollbar.set)
        vertical_scrollbar.configure(command=self.mismatched_view.yview)
        horizontal_scrollbar.configure(command=self.mismatched_view.xview)
        for column_id, column_name, column_width in zip(MISMATCHED_COLUMN_IDS, MISMATCHED_COLUMNS,
                                                        MISMATCHED_COLUMN_WIDTHS):
            self.mismatched_view.heading(column_id, text=column_name, anchor=tk.W,
                                         command=lambda clicked_column=column_id: self.sort_by_column(clicked_column))
            self.mismatched_view.column(column_id, width=column_width, minwidth=50, anchor=tk.W, stretch=True)
        self.mismatched_view.tag_configure("even_row", background=ROW_EVEN)
        self.mismatched_view.tag_configure("odd_row", background=ROW_ODD)
        vertical_scrollbar.pack(side="right", fill="y")
        horizontal_scrollbar.pack(side="bottom", fill="x")
        self.mismatched_view.pack(side="left", fill="both", expand=True)
        self.show_mismatches([])

    def show_mismatches(self, mismatch_records):
        """Replace the rows with the latest comparison and keep the current sort order.
        O(rows) (plus O(rows log rows) when sorted)."""
        self.mismatched_view.delete(*self.mismatched_view.get_children())
        self.records_by_row_id = {}
        for mismatch_record in mismatch_records:
            row_id = self.mismatched_view.insert("", tk.END, values=[mismatch_record[column] for column in MISMATCHED_COLUMNS])
            self.records_by_row_id[row_id] = mismatch_record
        if self.sorted_column_id is not None:
            self.apply_sort()
        else:
            self.shade_rows()
        record_count = len(mismatch_records)
        self.count_label.configure(text=f"{record_count} mismatched row{'' if record_count == 1 else 's'}")

    def shade_rows(self):
        """Give the Mismatched rows alternating shades in their current order (after filling or
        sorting), so long lists are easier to read."""
        for row_position, row_id in enumerate(self.mismatched_view.get_children()):
            self.mismatched_view.item(row_id, tags=("odd_row" if row_position % 2 else "even_row",))

    def sort_by_column(self, column_id):
        """A Mismatched header was clicked: sort by that column, or reverse the order when it is
        already the sort column (apply_sort also orders each device's rows by its command #)."""
        if self.sorted_column_id == column_id:
            self.sort_descending = not self.sort_descending
        else:
            self.sorted_column_id, self.sort_descending = column_id, False
        self.apply_sort()

    def rows_sorted_by(self, row_ids, column_id, descending):
        """Row ids ordered by one column (numbers by value, text naturally); blanks last."""
        filled = [row_id for row_id in row_ids if str(self.mismatched_view.set(row_id, column_id)).strip()]
        blank = [row_id for row_id in row_ids if not str(self.mismatched_view.set(row_id, column_id)).strip()]
        filled.sort(key=lambda row_id: CommandTablePanel.natural_sort_key(str(self.mismatched_view.set(row_id, column_id))),
                    reverse=descending)
        return filled + blank

    def apply_sort(self):
        """Sort by the chosen column; for Old / New Device (#) each group is also ordered by
        the matching Old / New Command # (sorted first - Python's sort is stable)."""
        row_ids = list(self.mismatched_view.get_children())
        column_name = MISMATCHED_COLUMNS[MISMATCHED_COLUMN_IDS.index(self.sorted_column_id)]
        secondary_column = MISMATCHED_SECONDARY_SORT.get(column_name)
        if secondary_column:
            row_ids = self.rows_sorted_by(row_ids, MISMATCHED_COLUMN_IDS[MISMATCHED_COLUMNS.index(secondary_column)],
                                          self.sort_descending)
        row_ids = self.rows_sorted_by(row_ids, self.sorted_column_id, self.sort_descending)
        for new_position, row_id in enumerate(row_ids):
            self.mismatched_view.move(row_id, "", new_position)
        for column_id, column_label in zip(MISMATCHED_COLUMN_IDS, MISMATCHED_COLUMNS):
            arrow = ("  \u25bc" if self.sort_descending else "  \u25b2") if column_id == self.sorted_column_id else ""
            self.mismatched_view.heading(column_id, text=column_label + arrow)
        self.shade_rows()

    def update_old_values(self):
        """Update button: the selected rows, or every row when nothing is selected, are
        handed to HeliosEditor.update_old_reference_values."""
        selected_row_ids = self.mismatched_view.selection()
        chosen_row_ids = selected_row_ids if selected_row_ids else self.mismatched_view.get_children()
        chosen_records = [self.records_by_row_id[row_id] for row_id in chosen_row_ids if row_id in self.records_by_row_id]
        if not chosen_records:
            messagebox.showinfo("Update", "There are no mismatched rows.", parent=self.host_window)
            return
        self.host_window.update_old_reference_values(chosen_records)


# ════════════════════════════════════════════════════════════════════════════════
# SOURCE TAB
# ════════════════════════════════════════════════════════════════════════════════
SOURCE_TAB_LABEL = "Source"
SOURCE_COLUMN_WIDTHS = (420, 260, 70, 220, 170, 240, 85)


class SourcePanel(tk.Frame):
    """Tables ▸ Source.  A drop-down picks what is shown:
      * SOURCE_ALL_FILES_OPTION (the default) - the current table: for every Reference row of
        the last Generate, the folder(s) and file(s) its arg, device and command were found in
        (in that order), with its Arg #, Arg Name, Device, Command and Command #;
      * one source file (alphabetically by file name) - its folder, and every variable it
        defined with its value.
    Read-only; filled by Generate.  The data is kept by the main window
    (HeliosEditor._source_rows / _source_file_variables) so a theme switch keeps it."""

    def __init__(self, parent_frame, source_rows, file_variables=None):
        """Build the toolbar (title, file drop-down, count) and the two tables (all files /
        one file; only one is shown at a time), then show the data."""
        super().__init__(parent_frame, bg=PANEL_BG)
        self.source_rows = []
        self.file_variables = {}
        self.file_paths_by_option = {}             # drop-down text -> full file path
        toolbar = tk.Frame(self, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)
        tk.Label(toolbar, text="Source file", bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left")
        self.file_choice = tk.StringVar(value=SOURCE_ALL_FILES_OPTION)
        self.file_chooser = ttk.Combobox(toolbar, textvariable=self.file_choice, state="readonly", width=60)
        self.file_chooser.pack(side="left", padx=(8, 0))
        self.file_chooser.bind("<<ComboboxSelected>>", lambda event: self.show_chosen_view())
        self.count_label = tk.Label(toolbar, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
        self.count_label.pack(side="right", padx=(8, 8))
        self.all_files_view = self.build_table(SOURCE_COLUMNS, SOURCE_COLUMN_WIDTHS)
        self.file_view = self.build_table(SOURCE_FILE_COLUMNS, (520, 520, 160))
        self.show_source_data(source_rows, file_variables or {})

    def build_table(self, column_names, column_widths):
        """One scrollable read-only table (kept in its own frame so it can be shown / hidden)."""
        container = tk.Frame(self, bg=PANEL_BG)
        vertical_scrollbar = ttk.Scrollbar(container, orient="vertical")
        horizontal_scrollbar = ttk.Scrollbar(container, orient="horizontal")
        column_ids = [f"column_{position}" for position in range(len(column_names))]
        table_view = ttk.Treeview(container, columns=column_ids, show="headings", selectmode="extended",
                                  yscrollcommand=vertical_scrollbar.set, xscrollcommand=horizontal_scrollbar.set)
        vertical_scrollbar.configure(command=table_view.yview)
        horizontal_scrollbar.configure(command=table_view.xview)
        for column_id, column_name, column_width in zip(column_ids, column_names, column_widths):
            table_view.heading(column_id, text=column_name, anchor=tk.W)
            table_view.column(column_id, width=column_width, minwidth=60, anchor=tk.W, stretch=True)
        table_view.tag_configure("even_row", background=ROW_EVEN)
        table_view.tag_configure("odd_row", background=ROW_ODD)
        vertical_scrollbar.pack(side="right", fill="y")
        horizontal_scrollbar.pack(side="bottom", fill="x")
        table_view.pack(side="left", fill="both", expand=True)
        table_view.container = container
        return table_view

    @staticmethod
    def fill_table(table_view, rows_of_cells):
        """Replace every row of one of the Source tab's tables with rows_of_cells (each a list of
        cell texts), alternating the row shading. O(rows)."""
        table_view.delete(*table_view.get_children())
        for row_position, cell_texts in enumerate(rows_of_cells):
            table_view.insert("", tk.END, values=cell_texts, tags=("odd_row" if row_position % 2 else "even_row",))

    def show_source_data(self, source_rows, file_variables):
        """New data from Generate: rebuild the drop-down (every file named by the rows or that
        defined variables, alphabetically by file name; files sharing a name also show their
        folder) and show the current choice when it still exists, else the current table."""
        self.source_rows = list(source_rows)
        self.file_variables = dict(file_variables)
        file_paths = set(self.file_variables)
        for source_row in self.source_rows:
            file_paths.update(source_row.get(SOURCE_FILE_PATHS_KEY, []))
        name_counts = {}
        for file_path in file_paths:
            name_counts[os.path.basename(file_path)] = name_counts.get(os.path.basename(file_path), 0) + 1
        self.file_paths_by_option = {}
        for file_path in sorted(file_paths, key=lambda path: (os.path.basename(path).lower(), path.lower())):
            file_name = os.path.basename(file_path)
            option_text = file_name if name_counts[file_name] == 1 else f"{file_name}   ({os.path.dirname(file_path)})"
            self.file_paths_by_option[option_text] = file_path
        self.file_chooser.configure(values=[SOURCE_ALL_FILES_OPTION] + list(self.file_paths_by_option))
        if self.file_choice.get() not in self.file_paths_by_option:
            self.file_choice.set(SOURCE_ALL_FILES_OPTION)
        self.fill_table(self.all_files_view, [[source_row.get(column, "") for column in SOURCE_COLUMNS]
                                              for source_row in self.source_rows])
        self.show_chosen_view()

    def rows_of_file(self, file_path):
        """(folder, variable name, value) for every variable the file defined, in file order."""
        return [(os.path.dirname(file_path), variable_name, value_text)
                for variable_name, value_text in self.file_variables.get(file_path, [])]

    def show_chosen_view(self):
        """Show the table for the drop-down's choice: the current table, or one file's variables."""
        chosen_option = self.file_choice.get()
        if chosen_option in self.file_paths_by_option:
            file_rows = self.rows_of_file(self.file_paths_by_option[chosen_option])
            self.fill_table(self.file_view, file_rows)
            self.all_files_view.container.pack_forget()
            self.file_view.container.pack(fill="both", expand=True, padx=8, pady=(0, 8))
            row_count, row_word = len(file_rows), "variable"
        else:
            self.file_view.container.pack_forget()
            self.all_files_view.container.pack(fill="both", expand=True, padx=8, pady=(0, 8))
            row_count, row_word = len(self.source_rows), "row"
        self.count_label.configure(text=f"{row_count} {row_word}{'' if row_count == 1 else 's'}")

    def show_view_and_select(self, option_text, row_position):
        """For Find: show a view (SOURCE_ALL_FILES_OPTION or a file option) and select the
        row at row_position in it."""
        self.file_choice.set(option_text if option_text in self.file_paths_by_option else SOURCE_ALL_FILES_OPTION)
        self.show_chosen_view()
        table_view = self.file_view if option_text in self.file_paths_by_option else self.all_files_view
        row_ids = table_view.get_children()
        if 0 <= row_position < len(row_ids):
            table_view.selection_set(row_ids[row_position])
            table_view.see(row_ids[row_position])


# ════════════════════════════════════════════════════════════════════════════════
# FILE ▸ VIEW DEVICES
# ════════════════════════════════════════════════════════════════════════════════
DEVICE_VIEWER_COLUMNS = ("Arg", "Name", "Device Type", "Device ID", "Action ID")
DEVICE_VIEWER_COLUMN_WIDTHS = (70, 260, 170, 90, 90)


class PackageDialog(tk.Toplevel):
    """Profile > Package: pick the image folder (required), the profile(s) (required) and an
    interface file (optional), fill in the manifest fields - with one Description per profile;
    the Installer Template row loads them from an existing manifest file -
    and save the package as <Aircraft>.helios16 in Documents\\Helios\\Interface Editor\\Profile Exports (see
    write_package_archive)."""

    MANIFEST_FIELDS = (("aircraft", "Aircraft"), ("version", "Version"), ("authors", "Authors (comma-sep)"),
                       ("minimum_version", "Minimum Version"))

    def __init__(self, parent, default_aircraft=""):
        """Build the dialog: the file rows (Images, Profile(s), Interface, Installer Template), the manifest
        fields, the Description rows (rebuilt whenever the profiles change) and the Package /
        Cancel buttons; the dialog opens in the middle of the parent window.  default_aircraft pre-fills the Aircraft field."""
        super().__init__(parent)
        self.withdraw()                          # shown once it is built and placed (no jump)
        self.transient(parent)
        self.title("Package")
        self.configure(bg=DARK_BG)
        self.resizable(True, False)
        self.image_folder = ""
        self.profile_paths = []
        self.interface_path = ""
        self.extra_file_paths = []               # optional additional files (Additional File(s) row)
        self.description_variables = []          # one per profile, same order as profile_paths
        self.loaded_descriptions = []            # from a loaded manifest: defaults for the Description rows

        outer = tk.Frame(self, bg=DARK_BG)
        outer.pack(fill="both", expand=True, padx=18, pady=16)
        outer.columnconfigure(1, weight=1)
        tk.Label(outer, text="Package", bg=DARK_BG, fg=ACCENT, font=FONT_TITLE).grid(
            row=0, column=0, columnspan=3, sticky="w", pady=(0, 12))

        self.chosen_text_variables = {}
        file_rows = (("images", "Images:", "required", self.choose_image_folder),
                     ("profiles", "Profile(s):", "required", self.choose_profiles),
                     ("interface", "Interface:", "optional", self.choose_interface),
                     ("extra_files", "Additional File(s):", "optional", self.choose_extra_files),
                     ("manifest", "Installer Template:", "optional - loads the fields below", self.choose_manifest))
        for row_number, (row_key, row_label, row_note, choose_command) in enumerate(file_rows, start=1):
            tk.Label(outer, text=row_label, bg=DARK_BG, fg=TEXT_PRI, font=FONT_UI).grid(
                row=row_number, column=0, sticky="nw", pady=3)
            chosen_text = tk.StringVar(value=f"({row_note})")
            self.chosen_text_variables[row_key] = chosen_text
            tk.Label(outer, textvariable=chosen_text, bg=DARK_BG, fg=TEXT_SEC, font=FONT_UI, justify="left",
                     anchor="w", wraplength=520).grid(row=row_number, column=1, sticky="ew", padx=8, pady=3)
            button_cell = tk.Frame(outer, bg=DARK_BG)
            button_cell.grid(row=row_number, column=2, sticky="ne", pady=3)
            tk.Button(button_cell, text="Select…", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat", padx=10,
                      cursor="hand2", command=choose_command).pack(side="left")
            if row_key == "extra_files":
                tk.Button(button_cell, text="Clear", bg=MID_BG, fg=TEXT_SEC, font=FONT_UI, relief="flat", padx=8,
                          cursor="hand2", command=self.clear_extra_files).pack(side="left", padx=(4, 0))

        self.field_variables = {}
        first_field_row = len(file_rows) + 1
        for row_number, (field_key, field_label) in enumerate(self.MANIFEST_FIELDS, start=first_field_row):
            self.field_variables[field_key] = tk.StringVar(value=default_aircraft if field_key == "aircraft" else "")
            self.add_entry_row(outer, row_number, field_label, self.field_variables[field_key])
        self.description_frame = tk.Frame(outer, bg=DARK_BG)
        self.description_frame.grid(row=first_field_row + len(self.MANIFEST_FIELDS), column=0, columnspan=3, sticky="ew")
        self.description_frame.columnconfigure(1, weight=1)
        self.rebuild_description_rows()

        button_row = tk.Frame(self, bg=DARK_BG)
        button_row.pack(fill="x", padx=18, pady=(0, 14))
        self.package_button = tk.Button(button_row, text="📦  Package", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                                        relief="flat", padx=16, pady=6, cursor="hand2", command=self.build_package)
        self.package_button.pack(side="left")
        tk.Button(button_row, text="Cancel", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat", padx=16, pady=6,
                  cursor="hand2", command=self.destroy).pack(side="left", padx=(8, 0))
        # progress of the zipping: shown (below the buttons) only while a package is being built
        self.progress_row = tk.Frame(self, bg=DARK_BG)
        self.progress_text = tk.StringVar(value="")
        tk.Label(self.progress_row, textvariable=self.progress_text, bg=DARK_BG, fg=TEXT_SEC, font=FONT_UI,
                 anchor="w").pack(fill="x")
        self.progress_bar = ttk.Progressbar(self.progress_row, orient="horizontal", mode="determinate")
        self.progress_bar.pack(fill="x", pady=(4, 0))
        self.bind("<Escape>", lambda event: self.destroy())
        center_over(parent, self)                # opens in the middle of the editor window
        self.show_in_front()

    def show_progress(self, zipped_count, file_count):
        """Progress of the zipping (called by zip_folder after every file): set the bar and its
        "Zipping n of m files" text and redraw them."""
        self.progress_bar.configure(maximum=max(file_count, 1), value=zipped_count)
        self.progress_text.set(f"Zipping {zipped_count} of {file_count} files…")
        self.update_idletasks()

    def set_packaging(self, is_packaging):
        """Start / end of a build: show the progress row (reset, "Gathering the files") and
        disable the Package button while packaging; hide the row and enable the button after."""
        if is_packaging:
            self.progress_bar.configure(maximum=1, value=0)
            self.progress_text.set("Gathering the files…")
            self.progress_row.pack(fill="x", padx=18, pady=(0, 14))
        else:
            self.progress_row.pack_forget()
        self.package_button.configure(state="disabled" if is_packaging else "normal")
        self.config(cursor="watch" if is_packaging else "")
        self.update_idletasks()

    def show_in_front(self):
        """Bring the dialog to the front and give it the keyboard.  It is made modal only once it
        is on screen, and stays usable (not modal) when the window system refuses that - so
        the dialog always appears, whatever the main window has or has not loaded."""
        self.deiconify()
        self.lift()
        try:
            self.wait_visibility()
            self.grab_set()
        except tk.TclError:
            pass
        self.focus_set()

    @staticmethod
    def add_entry_row(parent_frame, row_number, label_text, text_variable):
        """One labelled entry field on row_number of parent_frame's grid."""
        tk.Label(parent_frame, text=label_text, bg=DARK_BG, fg=TEXT_PRI, font=FONT_UI, justify="left").grid(
            row=row_number, column=0, sticky="w", pady=3)
        tk.Entry(parent_frame, textvariable=text_variable, bg=MID_BG, fg=TEXT_PRI, insertbackground=TEXT_PRI,
                 relief="flat", font=FONT_UI, width=60).grid(row=row_number, column=1, columnspan=2, sticky="ew",
                                                             padx=(8, 0), pady=3)

    def rebuild_description_rows(self):
        """Show one Description field per chosen profile (a single one before any profile is
        chosen), keeping the text already in each field; a field that is new or empty gets the
        description a loaded manifest has for that position."""
        typed_texts = [variable.get() for variable in self.description_variables]
        typed_texts += [""] * (len(self.loaded_descriptions) - len(typed_texts))
        typed_texts = [typed_text or loaded_text for typed_text, loaded_text in
                       zip(typed_texts, self.loaded_descriptions + [""] * len(typed_texts))]
        for row_widget in self.description_frame.winfo_children():
            row_widget.destroy()
        self.description_variables = []
        for position, profile_path in enumerate(self.profile_paths or [""]):
            description = tk.StringVar(value=typed_texts[position] if position < len(typed_texts) else "")
            self.description_variables.append(description)
            label_text = "Description" + (f"\n{os.path.basename(profile_path)}" if len(self.profile_paths) > 1 else "")
            self.add_entry_row(self.description_frame, position, label_text, description)

    def choose_image_folder(self):
        r"""Images row: pick the folder of the profile images (the picker starts in
        Documents\Helios\Images) and show where it goes in the package."""
        chosen_folder = filedialog.askdirectory(title="Select the folder of the profile images", mustexist=True,
                                                parent=self, initialdir=default_image_folder())
        if chosen_folder:
            self.image_folder = os.path.normpath(chosen_folder)
            self.chosen_text_variables["images"].set(
                f"{self.image_folder}\n→ {os.path.join(*package_image_folder_names(self.image_folder))}")

    def choose_profiles(self):
        r"""Profile(s) row: pick one or more profiles (the picker starts in
        Documents\Helios\Profiles) and give each its own Description field."""
        chosen_paths = filedialog.askopenfilenames(title="Select the profile(s)", filetypes=PROFILE_FILE_TYPES,
                                                   parent=self, initialdir=default_profile_folder())
        if chosen_paths:
            self.profile_paths = [os.path.normpath(chosen_path) for chosen_path in chosen_paths]
            self.chosen_text_variables["profiles"].set("\n".join(self.profile_paths))
            self.rebuild_description_rows()
            self.check_profile_bindings()

    def check_profile_bindings(self):
        """Check Bindings (find_unbound_devices) runs automatically for every profile just chosen;
        a profile with devices that have no binding gets its list shown with Accept (keep the
        profile) and Cancel (leave it out of the package)."""
        kept_paths = []
        for profile_path in self.profile_paths:
            try:
                unbound = find_unbound_devices(read_profile_text(profile_path))
            except (OSError, ValueError) as file_error:
                messagebox.showwarning("Check Bindings",
                                       f"Could not check {os.path.basename(profile_path)}:\n{file_error}", parent=self)
                kept_paths.append(profile_path)
                continue
            if unbound:
                dialog = UnboundDevicesDialog(self, profile_path, unbound, confirm=True)
                self.wait_window(dialog)
                if not dialog.accepted:
                    continue
            kept_paths.append(profile_path)
        if kept_paths != self.profile_paths:
            self.profile_paths = kept_paths
            self.chosen_text_variables["profiles"].set("\n".join(kept_paths) if kept_paths else "(required)")
            self.rebuild_description_rows()

    def choose_interface(self):
        r"""Interface row: pick the interface JSON file (the picker starts in
        Documents\Helios\Interfaces\HeliosInterfaces); the .lua of the same name beside it is
        taken along.  Shows the files and where they go in the package."""
        chosen_path = filedialog.askopenfilename(title="Select the interface file", filetypes=JSON_FILE_TYPES,
                                                 parent=self, initialdir=default_interface_folder())
        if chosen_path:
            self.interface_path = os.path.normpath(chosen_path)
            self.chosen_text_variables["interface"].set(
                "\n".join(interface_files_to_package(self.interface_path))
                + f"\n→ {os.path.join(*package_interface_folder_names(self.interface_path))}")

    def choose_extra_files(self):
        r"""Additional File(s) row (optional): navigate to and pick one or more files (the picker
        starts in Documents\Helios); each is added to the package under its own path below
        Documents\Helios.  Pick again to add more files, Clear to start over."""
        chosen_paths = filedialog.askopenfilenames(title="Select the additional file(s)", parent=self,
                                                   initialdir=os.path.join(documents_folder(), PACKAGE_ROOT_FOLDER_NAME)
                                                   if os.path.isdir(os.path.join(documents_folder(), PACKAGE_ROOT_FOLDER_NAME))
                                                   else documents_folder())
        for chosen_path in chosen_paths:
            chosen_path = os.path.normpath(chosen_path)
            if chosen_path not in self.extra_file_paths:
                self.extra_file_paths.append(chosen_path)
        self.show_extra_files()

    def clear_extra_files(self):
        """Clear button of the Additional File(s) row: forget the chosen files."""
        self.extra_file_paths = []
        self.show_extra_files()

    def show_extra_files(self):
        """Show each additional file with the package folder it goes to."""
        if not self.extra_file_paths:
            self.chosen_text_variables["extra_files"].set("(optional)")
            return
        self.chosen_text_variables["extra_files"].set("\n".join(
            f"{file_path}\n→ {os.path.join(*package_extra_file_folder_names(file_path))}"
            for file_path in self.extra_file_paths))

    def choose_manifest(self):
        r"""Installer Template row: pick a manifest JSON file (the picker starts in Documents\Helios\Interface Editor\Profile Exports)
        and fill the inputs below from it: Aircraft, Version, Authors, Minimum Version
        and the Descriptions (first description to the first profile, and so on; descriptions
        beyond the profiles chosen so far are kept for profiles chosen later)."""
        chosen_path = filedialog.askopenfilename(title="Select the installer template (Profile16) file",
                                                 filetypes=JSON_FILE_TYPES, parent=self,
                                                 initialdir=default_export_folder() or documents_folder())
        if not chosen_path:
            return
        try:
            field_texts, descriptions = read_package_manifest(chosen_path)
        except (OSError, ValueError) as read_error:
            messagebox.showerror("Package", f"Could not load the file:\n{read_error}", parent=self)
            return
        self.chosen_text_variables["manifest"].set(os.path.normpath(chosen_path))
        for field_key, field_text in field_texts.items():
            self.field_variables[field_key].set(field_text)
        self.loaded_descriptions = descriptions
        for variable in self.description_variables:              # the loaded descriptions replace typed ones
            variable.set("")
        self.rebuild_description_rows()

    def build_package(self):
        r"""Package button: check what is required (Images, Profile(s) and the Aircraft, which
        names the package), then build the package, zip it and save it as <Aircraft>.helios16 in
        Documents\Helios\Interface Editor\Profile Exports, and say where it is.  The profiles go through Monitor Removal
        without a message of their own; a progress bar follows the zipping."""
        fields = {field_key: variable.get() for field_key, variable in self.field_variables.items()}
        folder_name = package_folder_name(fields["aircraft"])
        if not self._required_package_fields_given(folder_name):
            return
        export_folder = default_export_folder()
        if export_folder is None:
            messagebox.showerror("Package", "The Helios Profile Exports folder could not be created.", parent=self)
            return
        descriptions = [variable.get() for variable in self.description_variables]
        archive_path = os.path.join(export_folder, folder_name + PACKAGE_ARCHIVE_EXTENSION)
        if os.path.exists(archive_path) and not messagebox.askyesno(
                "Package", f"This package already exists:\n{archive_path}\n\nReplace it?", parent=self):
            return
        manifest = build_package_manifest(fields["aircraft"], fields["version"], fields["authors"],
                                          fields["minimum_version"], self.profile_paths, descriptions)
        image_plan = self._plan_images_to_package()
        if image_plan is None:
            return
        self.set_packaging(True)
        try:
            file_count = write_package_archive(archive_path, self.image_folder, self.profile_paths,
                                               self.interface_path, manifest, self.show_progress,
                                               extra_file_paths=self.extra_file_paths,
                                               allowed_png_files=image_plan["allowed"])
        except (OSError, shutil.Error) as file_error:
            self.set_packaging(False)
            messagebox.showerror("Package", f"Could not build the package:\n{file_error}", parent=self)
            return
        messagebox.showinfo("Package", f"Packaged {file_count} files.{self._package_notes(image_plan)}"
                                       f"\n\nSaved:\n{archive_path}", parent=self)
        if image_plan["allowed"] is not None and image_plan["left_out_paths"]:
            LeftOutImagesDialog(self, image_plan["left_out_paths"])
        self.destroy()

    def _required_package_fields_given(self, folder_name) -> bool:
        """Tell the person which required inputs (Images, Profile(s), Aircraft) are missing."""
        missing_rows = [row_label for row_label, is_given in (("Images", self.image_folder),
                                                              ("Profile(s)", self.profile_paths),
                                                              ("Aircraft (it names the package)", folder_name))
                        if not is_given]
        if missing_rows:
            messagebox.showerror("Package", "Fill these in first:\n\n" + "\n".join(missing_rows), parent=self)
        return not missing_rows

    def _plan_images_to_package(self):
        """Only the images the profiles refer to are packaged; an image a profile names that is
        not in the image folder pauses the packaging.  Returns the analyze_package_images result,
        or None when the person stopped the packaging (or the images could not be read)."""
        self.config(cursor="watch")
        self.update_idletasks()
        try:
            image_plan = analyze_package_images(self.image_folder, self.profile_paths)
        except OSError as file_error:
            self.config(cursor="")
            messagebox.showerror("Package", f"Could not read the images:\n{file_error}", parent=self)
            return None
        self.config(cursor="")
        if image_plan["missing"]:
            missing_dialog = MissingImagesDialog(self, image_plan["missing"])
            self.wait_window(missing_dialog)
            if not missing_dialog.result:
                return None
        return image_plan

    @staticmethod
    def _package_notes(image_plan) -> str:
        """The lines added to the 'Packaged N files' message about images left out or unreadable profiles."""
        notes = ""
        if image_plan["allowed"] is not None:
            notes += f"\n\n{image_plan['left_out']} .png image(s) not used by the profile were left out."
        if image_plan["unreadable"]:
            notes += ("\n\nCould not read: "
                      + ", ".join(os.path.basename(path) for path in image_plan["unreadable"])
                      + "\nAll images were packaged.")
        return notes


class DeviceViewerWindow(tk.Toplevel):
    """JSON ▸ View Devices: pick (or type) a device name and see every function of that
    device: Arg, Name, Device Type, Device ID and Action ID.  Rows start sorted by
    Device ID, then Action ID, then Arg (blank numbers last); any header re-sorts by its
    column (again to reverse).  Double-click a row to show that function in its tab.
    The list always reflects the active document at the moment it is shown."""

    def __init__(self, host_window):
        """Build the window: the device name box (a drop-down you can also type in), a
        count, and the table; then fill the drop-down from the active profile."""
        super().__init__(host_window)
        self.host_window = host_window
        self.title("View Devices")
        self.configure(bg=PANEL_BG)
        window_width, window_height = 760, 460
        position_x, position_y = centered_position_on_parent(host_window, window_width, window_height)
        self.geometry(f"{window_width}x{window_height}+{position_x}+{position_y}")
        self.all_device_names = []
        self.shown_function_indices = []
        self.sorted_column = None                      # None = the default Device ID / Action ID / Arg order
        self.sort_descending = False

        chooser_row = tk.Frame(self, bg=PANEL_BG, pady=8)
        chooser_row.pack(fill="x", padx=10)
        tk.Label(chooser_row, text="Device", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI).pack(side="left")
        self.device_name_variable = tk.StringVar()
        self.device_chooser = ttk.Combobox(chooser_row, textvariable=self.device_name_variable, width=40)
        self.device_chooser.pack(side="left", padx=(8, 0))
        self.device_chooser.bind("<<ComboboxSelected>>", lambda event: self.show_device_functions())
        self.device_chooser.bind("<KeyRelease>", self.on_device_text_typed)
        self.device_chooser.bind("<Return>", lambda event: self.show_device_functions())
        self.count_label = tk.Label(chooser_row, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
        self.count_label.pack(side="right")

        table_container = tk.Frame(self, bg=PANEL_BG)
        table_container.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        vertical_scrollbar = ttk.Scrollbar(table_container, orient="vertical")
        self.functions_view = ttk.Treeview(table_container, columns=DEVICE_VIEWER_COLUMNS, show="headings",
                                           selectmode="browse", yscrollcommand=vertical_scrollbar.set)
        vertical_scrollbar.configure(command=self.functions_view.yview)
        for column_name, column_width in zip(DEVICE_VIEWER_COLUMNS, DEVICE_VIEWER_COLUMN_WIDTHS):
            centered = column_name in ("Arg", "Device ID", "Action ID")
            self.functions_view.heading(column_name, text=column_name, anchor="center" if centered else "w",
                                        command=lambda clicked_column=column_name: self.sort_by_column(clicked_column))
            self.functions_view.column(column_name, width=column_width, minwidth=50, stretch=True,
                                       anchor="center" if centered else "w")
        self.functions_view.tag_configure("even_row", background=ROW_EVEN)
        self.functions_view.tag_configure("odd_row", background=ROW_ODD)
        vertical_scrollbar.pack(side="right", fill="y")
        self.functions_view.pack(side="left", fill="both", expand=True)
        self.functions_view.bind("<Double-1>", self.jump_to_selected_function)
        self.functions_view.bind("<Return>", self.jump_to_selected_function)
        tk.Label(self, text="Double-click a row to show it in its tab", bg=PANEL_BG, fg=TEXT_SEC,
                 font=FONT_UI).pack(side="left", padx=10, pady=(0, 8))
        self.reload_device_names()
        self.device_chooser.focus_set()

    def reload_device_names(self):
        """Fill the drop-down with every device name of the active profile (sorted, each once).
        O(functions)."""
        self.host_window._sync_header_to_data()
        device_names = {str(function.get("device", "")).strip() for function in self.host_window._data.get("functions", [])}
        device_names.discard("")
        self.all_device_names = sorted(device_names, key=str.lower)
        self.device_chooser.configure(values=self.all_device_names)
        self.show_device_functions()

    def on_device_text_typed(self, event):
        """While typing: narrow the drop-down list to the names containing the text, and show
        the matching functions."""
        if event.keysym in ("Up", "Down", "Return", "Escape", "Tab"):
            return
        typed_text = self.device_name_variable.get().strip().lower()
        matching_names = [name for name in self.all_device_names if typed_text in name.lower()] if typed_text \
            else self.all_device_names
        self.device_chooser.configure(values=matching_names)
        self.show_device_functions()

    def chosen_device_names(self):
        """The device(s) to show: the name typed / picked (ignoring upper / lower case); when no
        name matches exactly, every name containing the text.  Empty text -> none."""
        typed_text = self.device_name_variable.get().strip().lower()
        if not typed_text:
            return set()
        exact_names = {name for name in self.all_device_names if name.lower() == typed_text}
        return exact_names or {name for name in self.all_device_names if typed_text in name.lower()}

    @staticmethod
    def number_or_last(cell_text):
        """A cell as a number for sorting; blanks and non-numbers sort after every number."""
        number = parse_number_or_none(cell_text)
        return (0, number) if number is not None else (1, 0.0)

    def default_sort_key(self, row_values):
        """Default order: Device ID, then Action ID, then Arg (blank numbers last), then Name."""
        arg_text, name_text, _type_text, device_id_text, action_id_text = row_values
        return (self.number_or_last(device_id_text), self.number_or_last(action_id_text),
                self.number_or_last(arg_text), name_text.lower())

    def show_device_functions(self):
        """(Re)fill the table with the chosen device's functions from the active profile, in
        the current sort order.  O(functions + shown rows x log shown rows)."""
        chosen_names = self.chosen_device_names()
        rows = self.sorted_function_rows(self.function_rows_of_devices(chosen_names))
        self.functions_view.delete(*self.functions_view.get_children())
        for row_number, (function_index, row_values) in enumerate(rows):
            self.functions_view.insert("", tk.END, iid=str(function_index), values=row_values,
                                       tags=("odd_row" if row_number % 2 else "even_row",))
        device_count = len(chosen_names)
        self.count_label.configure(
            text=(f"{len(rows)} function{'' if len(rows) == 1 else 's'}"
                  + (f" in {device_count} devices" if device_count > 1 else "")) if chosen_names else "")
        for column_name in DEVICE_VIEWER_COLUMNS:
            arrow = ("  ▼" if self.sort_descending else "  ▲") if column_name == self.sorted_column else ""
            self.functions_view.heading(column_name, text=column_name + arrow)

    def function_rows_of_devices(self, chosen_names):
        """[(function index, (Arg, Name, Device Type, Device ID, Action ID))] of the functions of the chosen devices."""
        rows = []
        for function_index, function in enumerate(self.host_window._data.get("functions", [])):
            if str(function.get("device", "")).strip() not in chosen_names:
                continue
            helios_type = function.get("heliosType", "")
            device_id, action_id = best_effort_ids(function)
            rows.append((function_index, (str(first_export(function).get("id", "")), str(function.get("name", "")),
                                          TAB_LABELS.get(helios_type, helios_type.split(".")[-1]),
                                          device_id, action_id)))
        return rows

    def sorted_function_rows(self, rows):
        """The rows in the current sort order (the default order until a header is clicked);
        rows with a blank value in the sorted column come last."""
        if self.sorted_column is None:
            return sorted(rows, key=lambda row: self.default_sort_key(row[1]))
        column_position = DEVICE_VIEWER_COLUMNS.index(self.sorted_column)
        filled = [row for row in rows if row[1][column_position].strip()]
        blank = [row for row in rows if not row[1][column_position].strip()]
        filled.sort(key=lambda row: CommandTablePanel.natural_sort_key(row[1][column_position]),
                    reverse=self.sort_descending)
        return filled + blank

    def sort_by_column(self, column_name):
        """Header clicked: sort by that column (again to reverse); blanks stay last."""
        if self.sorted_column == column_name:
            self.sort_descending = not self.sort_descending
        else:
            self.sorted_column, self.sort_descending = column_name, False
        self.show_device_functions()

    def jump_to_selected_function(self, _event=None):
        """Show the selected function in its tab (Devices ▸ its type) and select it."""
        selected_ids = self.functions_view.selection()
        if not selected_ids:
            return
        function_index = int(selected_ids[0])
        functions = self.host_window._data.get("functions", [])
        if function_index >= len(functions):
            return                                      # the profile changed since it was shown
        helios_type = functions[function_index].get("heliosType", "")
        if helios_type in TAB_LABELS:
            self.host_window._select_tab(helios_type)
            self.host_window._select_function(helios_type, function_index)


class DeviceDetailsWindow(tk.Toplevel):
    """Details: shown below Device Information for a row with an Arg #, Device # and
    Command #.  Lists, stacked, the element's Hint, arg_lim and arg_val as Generate kept them
    (function parameters hint_ / arg_lim_ / arg_val_, or table fields hint / arg_lim /
    arg_value).  Closed together with Device Information."""

    def __init__(self, parent_window, element_detail):
        """Build the Details window: a heading and the element's Hint, arg_lim and arg_val stacked
        one per line, each read from the parameters Generate kept (element_parameter), blank
        when the element had none."""
        super().__init__(parent_window)
        self.title("Details")
        self.configure(bg=PANEL_BG)
        self.transient(parent_window)
        self.resizable(False, False)
        content = tk.Frame(self, bg=PANEL_BG, padx=16, pady=10)
        content.pack(fill="both", expand=True)
        tk.Label(content, text="Details", bg=PANEL_BG, fg=ACCENT, font=FONT_TITLE).pack(anchor="w", pady=(0, 6))
        for label_text, parameter_names in (("Hint", ("hint", "help")), ("arg_lim", ("arg_lim",)),
                                            ("arg_val", ("arg_val", "arg_value"))):
            tk.Label(content, text=f"{label_text} = {element_parameter(element_detail, *parameter_names)}",
                     bg=PANEL_BG, fg=TEXT_PRI, font=FONT_MONO, anchor="w", justify="left",
                     wraplength=520).pack(anchor="w", pady=1)


SELECTION_COLUMNS = ("Arg#", "Arg Name", "Device", "Device ID", "Command", "Command#")
SELECTION_COLUMN_WIDTHS = (60, 170, 130, 80, 170, 100)


class SelectionWindow(tk.Toplevel):
    """Selection: the reference rows chosen for Build Device, to the right of Device
    Information.  Entries leave the list when they are added, skipped, combined or removed
    (Remove button).  Combine uses the entry selected here as the second option."""

    def __init__(self, parent_window, entries, columns=None, widths=None):
        """entries: [(row key, row dict)] in table order.  Builds the list and the Remove button.
        columns / widths replace the default Build Device columns (Change Device ID uses its own
        headings); a row dict is read by column name ("Device ID" also reads a table row's
        "Device #")."""
        super().__init__(parent_window)
        columns = columns or SELECTION_COLUMNS
        widths = widths or (SELECTION_COLUMN_WIDTHS if columns is SELECTION_COLUMNS else (110,) * len(columns))
        self.title("Selection")
        self.configure(bg=PANEL_BG)
        self.transient(parent_window)
        self.rows_by_key = {}
        content = tk.Frame(self, bg=PANEL_BG, padx=10, pady=10)
        content.pack(fill="both", expand=True)
        column_ids = [f"c{position}" for position in range(len(columns))]
        self.selection_view = ttk.Treeview(content, columns=column_ids, show="headings",
                                           selectmode="extended", height=12)
        for column_id, column_name, column_width in zip(column_ids, columns, widths):
            self.selection_view.heading(column_id, text=column_name, anchor=tk.W)
            self.selection_view.column(column_id, width=column_width, minwidth=50, anchor=tk.W)
        self.selection_view.tag_configure("current_entry", background=ACCENT, foreground=DARK_BG)
        self.selection_view.pack(fill="both", expand=True)
        for row_key, table_row in entries:
            self.rows_by_key[row_key] = table_row
            self.selection_view.insert("", tk.END, iid=row_key, values=tuple(
                self.cell_text(table_row, column_name) for column_name in columns))
        tk.Button(content, text="Remove", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat", padx=12, pady=3,
                  cursor="hand2", command=self.remove_selected).pack(anchor="e", pady=(8, 0))

    @staticmethod
    def cell_text(table_row, column_name):
        """The text a row dict gives for one Selection column: the table's own names (Arg #,
        Command #, Device #) are read for the matching short headings."""
        aliases = {"Arg#": "Arg #", "Command#": "Command #", "Device ID": "Device #"}
        if column_name in table_row:
            text = table_row[column_name]
        else:
            text = table_row.get(aliases.get(column_name, column_name), "")
        return prettify_label(text) if column_name == "Device" else text      # as JSON Controls shows it

    def remaining_entries(self):
        """The Selection list's entries that are still waiting, as [(row key, row dict)] in list
        order; the Build Device loop takes the first one each time."""
        return [(row_key, self.rows_by_key[row_key]) for row_key in self.selection_view.get_children()]

    def remove_entry(self, row_key):
        """Take one entry out of the list (no-op when it is already gone)."""
        if row_key is not None and self.selection_view.exists(row_key):
            self.selection_view.delete(row_key)

    def remove_selected(self):
        """Remove button: take the entries selected in the Selection list out of it, so the Build
        Device loop skips them."""
        for row_key in self.selection_view.selection():
            self.remove_entry(row_key)

    def selected_entry(self):
        """(row key, row dict) of the entry selected in the list, or None."""
        selected_keys = self.selection_view.selection()
        if not selected_keys:
            return None
        return selected_keys[0], self.rows_by_key[selected_keys[0]]

    def mark_current(self, row_key):
        """Highlight the entry that Device Information is building, so it is clear which row of the
        Selection list is being worked on; every other entry is shown normally."""
        for listed_key in self.selection_view.get_children():
            self.selection_view.item(listed_key, tags=("current_entry",) if listed_key == row_key else ())


def center_over(anchor_window, placed_window):
    """Move placed_window so its middle is over the middle of anchor_window (where that window
    is now), kept fully on the screen when it fits.  The size of placed_window is not changed."""
    placed_window.update_idletasks()                     # so the requested size is known
    anchor_window.update_idletasks()
    placed_width, placed_height = placed_window.winfo_reqwidth(), placed_window.winfo_reqheight()
    left = anchor_window.winfo_rootx() + (anchor_window.winfo_width() - placed_width) // 2
    top = anchor_window.winfo_rooty() + (anchor_window.winfo_height() - placed_height) // 2
    left = max(0, min(left, placed_window.winfo_screenwidth() - placed_width))
    top = max(0, min(top, placed_window.winfo_screenheight() - placed_height))
    placed_window.geometry(f"+{left}+{top}")


def place_beside(anchor_window, placed_window, side):
    """Put placed_window to the right of anchor_window (side "right") or below it ("below"),
    moved back inside the screen when it would not fit."""
    anchor_window.update_idletasks()
    placed_window.update_idletasks()
    if side == "right":
        position_x = anchor_window.winfo_x() + anchor_window.winfo_width() + 12
        position_y = anchor_window.winfo_y()
    else:
        position_x = anchor_window.winfo_x()
        position_y = anchor_window.winfo_y() + anchor_window.winfo_height() + 34
    placed_width = max(placed_window.winfo_width(), placed_window.winfo_reqwidth())
    placed_height = max(placed_window.winfo_height(), placed_window.winfo_reqheight())
    position_x = min(position_x, placed_window.winfo_screenwidth() - placed_width - 4)
    position_y = min(position_y, placed_window.winfo_screenheight() - placed_height - 40)
    placed_window.geometry(f"+{max(0, position_x)}+{max(0, position_y)}")


def keep_inside_main_window(window):
    """Move a sub window (once) so it lies inside the main window's area.  The size is not
    changed; a window larger than the main window lines up with its top-left corner.  Pop-up
    lists (override-redirect windows) and the main window itself are left alone."""
    try:
        main_window = window.nametowidget(".")
        if window is main_window or window.overrideredirect() or not window.winfo_exists():
            return
        if main_window.state() in ("iconic", "withdrawn") or window.state() == "withdrawn":
            return
        window.update_idletasks()
        width = max(window.winfo_width(), 1)
        height = max(window.winfo_height(), 1)
        if width <= 1 or height <= 1:
            width, height = window.winfo_reqwidth(), window.winfo_reqheight()
        main_left, main_top = main_window.winfo_rootx(), main_window.winfo_rooty()
        main_right = main_left + main_window.winfo_width()
        main_bottom = main_top + main_window.winfo_height()
        left, top = window.winfo_x(), window.winfo_y()
        new_left = max(main_left, min(left, main_right - width))
        new_top = max(main_top, min(top, main_bottom - height))
        if (new_left, new_top) != (left, top):
            window.geometry(f"+{new_left}+{new_top}")
    except tk.TclError:
        pass


_original_toplevel_init = tk.Toplevel.__init__


def _toplevel_init_inside_main(self, *args, **kwargs):
    """Every Toplevel of the editor opens inside the main window: once it has been built and
    placed, keep_inside_main_window pulls it in (again when it is first shown)."""
    _original_toplevel_init(self, *args, **kwargs)
    state = {"done": False}

    def place_once(_event=None):
        """Move a new window inside the main window, once, when it first appears."""
        if _event is not None and _event.widget is not self:
            return
        if _event is not None:
            state["done"] = True
        keep_inside_main_window(self)

    self.after_idle(place_once)
    self.bind("<Map>", lambda event: None if state["done"] else place_once(event), add="+")


tk.Toplevel.__init__ = _toplevel_init_inside_main


CHANGE_DEVICE_COLUMNS = ("Arg#", "Name", "Device", "Device ID", "Type", "Action ID")
CHANGE_DEVICE_COLUMN_WIDTHS = (60, 170, 130, 80, 110, 80)


class ChangeDeviceIdDialog(tk.Toplevel):
    """Change Device ID: shows the Current Device / Current Device ID of the entry picked in the
    Selection window, and takes a New Device Name (a drop-down you can type in, listing the
    profile's devices) and a New Device ID (starts as the Current Device ID).  Apply to Selection
    changes the entries selected in the Selection window; Apply to All changes every entry in
    it.  Changed entries leave the Selection window; the dialog closes with it."""

    def __init__(self, editor, selection_window, device_names):
        """editor: the main window (it does the changing); selection_window: a SelectionWindow
        whose entries are (key, row dict with "Device" and "Device ID"); device_names: the
        profile's device names for the drop-down."""
        super().__init__(editor)
        self.editor = editor
        self.selection_window = selection_window
        self.title("Change Device ID")
        self.configure(bg=DARK_BG)
        self.transient(editor)
        self.resizable(False, False)
        self.current_device = tk.StringVar()
        self.current_device_id = tk.StringVar()
        self.new_device_name = tk.StringVar()
        self.new_device_id = tk.StringVar()

        outer = tk.Frame(self, bg=DARK_BG)
        outer.pack(fill="both", expand=True, padx=18, pady=16)
        outer.columnconfigure(1, weight=1)
        for row_number, (label_text, text_variable) in enumerate((
                ("Current Device", self.current_device), ("Current Device ID", self.current_device_id))):
            tk.Label(outer, text=label_text, bg=DARK_BG, fg=TEXT_PRI, font=FONT_UI).grid(
                row=row_number, column=0, sticky="w", pady=3)
            tk.Label(outer, textvariable=text_variable, bg=MID_BG, fg=ACCENT2, font=FONT_MONO, anchor="w",
                     width=34, padx=4).grid(row=row_number, column=1, sticky="ew", padx=(10, 0), pady=3)
        tk.Label(outer, text="New Device Name", bg=DARK_BG, fg=TEXT_PRI, font=FONT_UI).grid(
            row=2, column=0, sticky="w", pady=3)
        self.name_box = ttk.Combobox(outer, textvariable=self.new_device_name, values=device_names_as_shown(device_names), width=36)
        self.name_box.grid(row=2, column=1, sticky="ew", padx=(10, 0), pady=3)
        tk.Label(outer, text="New Device ID", bg=DARK_BG, fg=TEXT_PRI, font=FONT_UI).grid(
            row=3, column=0, sticky="w", pady=3)
        tk.Entry(outer, textvariable=self.new_device_id, bg=MID_BG, fg=TEXT_PRI, insertbackground=TEXT_PRI,
                 relief="flat", font=FONT_MONO, width=36).grid(row=3, column=1, sticky="ew", padx=(10, 0), pady=3)

        buttons = tk.Frame(self, bg=DARK_BG)
        buttons.pack(fill="x", padx=18, pady=(0, 14))
        tk.Button(buttons, text="Apply to Selection", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat",
                  padx=14, pady=5, cursor="hand2", command=lambda: self.apply(False)).pack(side="left")
        tk.Button(buttons, text="Apply to All", bg=ACCENT2, fg=DARK_BG, font=FONT_HEAD, relief="flat",
                  padx=14, pady=5, cursor="hand2", command=lambda: self.apply(True)).pack(side="left", padx=(8, 0))
        tk.Button(buttons, text="Close", bg=MID_BG, fg=TEXT_SEC, font=FONT_UI, relief="flat",
                  padx=14, pady=5, cursor="hand2", command=self.close).pack(side="right")

        view = selection_window.selection_view
        view.bind("<<TreeviewSelect>>", lambda event: self.show_current(), add="+")
        selection_window.bind("<Destroy>", self.on_selection_window_destroyed, add="+")
        self.protocol("WM_DELETE_WINDOW", self.close)
        first_keys = view.get_children()
        if first_keys:
            view.selection_set(first_keys[0])
        self.show_current()

    def show_current(self):
        """Fill Current Device / Current Device ID (and the New Device fields) from the first entry
        selected in the Selection window; the New Device ID starts as the Current Device ID."""
        selected = self.selection_window.selection_view.selection()
        if not selected:
            return
        row = self.selection_window.rows_by_key[selected[0]]
        self.current_device.set(prettify_label(row.get("Device", "")))
        self.current_device_id.set(str(row.get("Device ID", "")))
        self.new_device_name.set(prettify_label(row.get("Device", "")))
        self.new_device_id.set(str(row.get("Device ID", "")))

    def apply(self, to_all):
        """Apply to All / Apply to Selection: give those Selection entries the New Device Name and
        New Device ID, then take them out of the Selection window."""
        view = self.selection_window.selection_view
        keys = list(view.get_children()) if to_all else list(view.selection())
        if not keys:
            messagebox.showinfo("Change Device ID", "Select one or more entries in the Selection window first.",
                                parent=self)
            return
        new_name, new_id = self.new_device_name.get().strip(), self.new_device_id.get().strip()
        if not new_name:
            messagebox.showerror("Change Device ID", "Enter or choose a New Device Name.", parent=self)
            return
        if new_id and not (new_id.isdigit() and int(new_id) > 0):
            messagebox.showerror("Change Device ID", "The New Device ID must be a positive whole number.",
                                 parent=self)
            return
        new_name = device_name_lookup(self.editor.profile_device_names()).get(new_name.lower(), new_name)
        changed = self.editor.apply_device_change(
            [self.selection_window.rows_by_key[key]["_function"] for key in keys], new_name, new_id)
        for key in keys:
            self.selection_window.remove_entry(key)
        self.name_box.configure(values=device_names_as_shown(self.editor.profile_device_names()))
        if not view.get_children():
            self.close()
            return
        view.selection_set(view.get_children()[0])
        self.show_current()

    def on_selection_window_destroyed(self, event):
        """The Selection window was closed: close this dialog with it."""
        if event.widget is self.selection_window and self.winfo_exists():
            self.destroy()

    def close(self):
        """Close button: close this dialog and the Selection window."""
        if self.selection_window.winfo_exists():
            self.selection_window.destroy()
        if self.winfo_exists():
            self.destroy()


class BuildDeviceDialog(tk.Toplevel):
    """Device Information (Build Device): shows what the new device gets from a table row
    (Export ID(Arg) = Arg #, Device = Device, Device ID = Device #, Action ID = Command #,
    Description = Note), and lets the user pick the device type and the name: the element's
    Help text (default for rows made by function calls), the row's Arg Name, its Command, or
    a name typed in.  With several rows selected it also offers Skip and Combine (the second
    entry is picked in the Selection window).  Not modal, so the Selection window can be used.
    result = {"action": "create" | "review" | "skip", "helios_type", "name", "device_name",
              "device_number", "combined_key", "combined_row"} or None when cancelled."""

    def __init__(self, parent_window, table_row, function_return_types=None, element_detail=None,
                 discovered_devices=None, default_device_name="", selection_window=None, entry_key=None):
        """Build the Build Device dialog for one table row: what the row fills in, a device type
        list (defaulted by guess_helios_type_for_row from the row and the function return
        types), the name choice (Arg Name / Command / typed) and the create / review / cancel
        buttons.  When the element has a position count (its function's count_), the dialog
        defaults to "Review in Add dialog" (Enter) and the Add dialog opens with that count.
        The Device line is a drop-down you can type in: every device name Generate discovered,
        alphabetically, narrowed while typing.  When the row has no Device #, a chosen device
        whose number is known fills the Device ID.  default_device_name (the previous device of
        a multi-row build) fills the Device box when the row has no device of its own."""
        super().__init__(parent_window)
        self.selection_window = selection_window      # None when one row is being built
        self.entry_key = entry_key
        self.combined_key, self.combined_row = None, None
        self.help_text = element_help_text(element_detail)
        self.position_count = (element_detail or {}).get("position_count")
        self.position_values = (element_detail or {}).get("position_values")
        self.title("Device Information")
        self.configure(bg=PANEL_BG)
        self.transient(parent_window)
        self.resizable(False, False)
        self.result = None
        self.table_row = table_row
        self._remember_device_names(table_row, discovered_devices, default_device_name)

        content = tk.Frame(self, bg=PANEL_BG, padx=16, pady=12)
        content.pack(fill="both", expand=True)
        tk.Label(content, text="Device Information", bg=PANEL_BG, fg=ACCENT,
                 font=FONT_TITLE).grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 10))
        next_row = self._add_filled_fields(content, table_row, default_device_name)
        self.update_device_id_label()
        next_row = self._add_device_type_section(content, next_row, function_return_types)
        next_row = self._add_name_choices(content, next_row)
        self._add_buttons(content, next_row)

        self.update_idletasks()
        dialog_width, dialog_height = self.winfo_reqwidth(), self.winfo_reqheight()
        position_x, position_y = centered_position_on_parent(parent_window, dialog_width, dialog_height)
        self.geometry(f"+{position_x}+{position_y}")
        self.default_button.focus_set()          # not modal: the Selection window stays usable

    def _remember_device_names(self, table_row, discovered_devices, default_device_name):
        """The device names the Device drop-down offers, and how typed names map to them."""
        self.discovered_devices = dict(discovered_devices or {})
        self.all_device_names = device_names_as_shown(self.discovered_devices)    # as JSON Controls shows them
        self.device_names_by_lowercase = device_name_lookup(sorted_device_names(self.discovered_devices))
        for own_name in (table_row.get("Device", ""), default_device_name):     # names not discovered
            own_name = str(own_name or "").strip()
            if own_name:
                self.device_names_by_lowercase.setdefault(prettify_label(own_name).lower(), own_name)

    def _add_filled_fields(self, content, table_row, default_device_name):
        """What the row fills in; the Device line is a typable drop-down of the discovered names.
        Returns the next free grid row."""
        filled_fields = (("Export ID(Arg)", table_row.get("Arg #", "")), ("Device", None),
                         ("Device ID", table_row.get("Device #", "")), ("Action ID", table_row.get("Command #", "")),
                         ("Description", table_row.get("Note", "") or "(type default)"))
        for row_number, (field_label, field_value) in enumerate(filled_fields, start=1):
            tk.Label(content, text=field_label, bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI).grid(
                row=row_number, column=0, sticky="w", padx=(0, 12), pady=1)
            if field_label == "Device":
                self._add_device_chooser(content, row_number, table_row, default_device_name)
                continue
            value_label = tk.Label(content, text=field_value or "—", bg=PANEL_BG, fg=TEXT_PRI, font=FONT_MONO)
            value_label.grid(row=row_number, column=1, columnspan=2, sticky="w", pady=1)
            if field_label == "Device ID":
                self.device_id_label = value_label
            elif field_label == "Action ID":
                self.action_id_label = value_label
        return len(filled_fields) + 1

    def _add_device_chooser(self, content, row_number, table_row, default_device_name):
        """The Device drop-down (typable, narrowed while typing)."""
        self.device_variable = tk.StringVar(
            value=prettify_label(table_row.get("Device", "").strip() or default_device_name))
        self.device_chooser = ttk.Combobox(content, textvariable=self.device_variable,
                                           values=self.all_device_names, width=34)
        self.device_chooser.grid(row=row_number, column=1, columnspan=2, sticky="w", pady=1)
        self.device_chooser.bind("<KeyRelease>", self.on_device_text_typed)
        self.device_chooser.bind("<<ComboboxSelected>>", lambda event: self.update_device_id_label())

    def _add_device_type_section(self, content, next_row, function_return_types):
        """The device type list, the note about stored ids, and the position hint. Returns the next row."""
        tk.Label(content, text="Device type", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI).grid(
            row=next_row, column=0, sticky="w", padx=(0, 12), pady=(10, 2))
        self.type_labels = [TAB_LABELS[helios_type] for helios_type in HELIOS_TYPES]
        self.type_variable = tk.StringVar(value=TAB_LABELS[guess_helios_type_for_row(self.table_row, function_return_types)])
        ttk.Combobox(content, textvariable=self.type_variable, values=self.type_labels, state="readonly",
                     width=24).grid(row=next_row, column=1, columnspan=2, sticky="w", pady=(10, 2))
        next_row += 1
        tk.Label(content, text="Device ID / Action ID are stored by Push Button, Switch, Axis and "
                               "Rotary Encoder devices.", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI,
                 wraplength=420, justify="left").grid(row=next_row, column=0, columnspan=3, sticky="w")
        next_row += 1
        position_hint = self._position_hint_text()
        if position_hint:
            tk.Label(content, text=position_hint,
                     bg=PANEL_BG, fg=ACCENT2, font=FONT_UI, wraplength=420, justify="left").grid(
                row=next_row, column=0, columnspan=3, sticky="w", pady=(4, 0))
            next_row += 1
        self.combined_label = tk.Label(content, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_UI,
                                       wraplength=420, justify="left")
        self.combined_label.grid(row=next_row, column=0, columnspan=3, sticky="w")
        return next_row + 1

    def _position_hint_text(self):
        """The note about the positions the element's function gave (3 values, or a count), or ''."""
        if self.position_values:
            value_texts = ", ".join(format_number_text(value) for value in self.position_values)
            return (f"As a Switch it gets 3 positions ({value_texts}): minimum "
                    f"{format_number_text(self.position_values[0])}, maximum "
                    f"{format_number_text(self.position_values[-1])}.")
        if self.position_count:
            return (f"This element has {self.position_count} positions: it opens in the Add dialog "
                    f"with a position count of {self.position_count}.")
        return ""

    def _add_name_choices(self, content, next_row):
        """The Name choice: help text, Arg Name, Command or a typed name. Returns the next row."""
        tk.Label(content, text="Name", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI).grid(
            row=next_row, column=0, sticky="nw", padx=(0, 12), pady=(10, 2))
        arg_name = self.table_row.get("Arg Name", "").strip()
        command_name = self.table_row.get("Command", "").strip()
        default_choice = "help" if self.help_text else ("arg_name" if arg_name else ("command" if command_name else "manual"))
        self.name_choice = tk.StringVar(value=default_choice)
        self.manual_name = tk.StringVar(value=self.help_text or arg_name or command_name)
        radio_options = dict(bg=PANEL_BG, fg=TEXT_PRI, selectcolor=MID_BG, activebackground=PANEL_BG,
                             activeforeground=TEXT_PRI, font=FONT_UI, anchor="w", highlightthickness=0)
        if self.help_text:                                  # the element function's help text
            tk.Radiobutton(content, text=f"Help:  {self.help_text}", variable=self.name_choice, value="help",
                           **radio_options).grid(row=next_row, column=1, columnspan=2, sticky="w", pady=(10, 0))
            next_row += 1
        tk.Radiobutton(content, text=f"Arg Name:  {arg_name or '(blank)'}", variable=self.name_choice,
                       value="arg_name", state="normal" if arg_name else "disabled", **radio_options).grid(
            row=next_row, column=1, columnspan=2, sticky="w", pady=(10, 0))
        tk.Radiobutton(content, text=f"Command:  {command_name or '(blank)'}", variable=self.name_choice,
                       value="command", state="normal" if command_name else "disabled", **radio_options).grid(
            row=next_row + 1, column=1, columnspan=2, sticky="w")
        tk.Radiobutton(content, text="Type a name:", variable=self.name_choice, value="manual",
                       **radio_options).grid(row=next_row + 2, column=1, sticky="w")
        self.manual_entry = tk.Entry(content, textvariable=self.manual_name, width=28, bg=MID_BG, fg=TEXT_PRI,
                                     insertbackground=TEXT_PRI, relief="flat", font=FONT_MONO,
                                     highlightthickness=1, highlightcolor=ACCENT, highlightbackground=BORDER)
        self.manual_entry.grid(row=next_row + 2, column=2, sticky="w", padx=(4, 0))
        self.manual_entry.bind("<FocusIn>", lambda event: self.name_choice.set("manual"))
        return next_row + 3

    def _add_buttons(self, content, next_row):
        """Cancel, Skip / Combine (several rows), Review and Create buttons; Enter runs the blue one."""
        button_row = tk.Frame(content, bg=PANEL_BG)
        button_row.grid(row=next_row, column=0, columnspan=3, sticky="e", pady=(14, 0))
        tk.Button(button_row, text="Cancel", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat",
                  padx=12, pady=3, cursor="hand2", command=self.destroy).pack(side="right", padx=(8, 0))
        if self.selection_window is not None:              # several rows: skip / combine entries
            tk.Button(button_row, text="Skip", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat",
                      padx=12, pady=3, cursor="hand2", command=self.skip_entry).pack(side="right", padx=(8, 0))
            tk.Button(button_row, text="Combine", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI, relief="flat",
                      padx=12, pady=3, cursor="hand2", command=self.combine_with_selected).pack(side="right", padx=(8, 0))
        review_is_default = bool(self.position_count)        # a count: review (and set positions) first
        review_button = tk.Button(button_row, text="Review in Add dialog…", bg=ACCENT if review_is_default else ACCENT2,
                                  fg=DARK_BG, font=FONT_HEAD, relief="flat", padx=12, pady=3, cursor="hand2",
                                  highlightthickness=0, command=lambda: self.confirm(True))
        review_button.pack(side="right", padx=(8, 0))
        create_button = tk.Button(button_row, text="Create device", bg=ACCENT2 if review_is_default else ACCENT,
                                  fg=DARK_BG, font=FONT_HEAD, relief="flat", padx=12, pady=3, cursor="hand2",
                                  highlightthickness=0, command=lambda: self.confirm(False))
        create_button.pack(side="right")
        self.default_review_first = review_is_default
        self.default_button = review_button if review_is_default else create_button   # blue, Enter, focus
        self.bind("<Return>", lambda event: None if event.widget is self.device_chooser
                  else self.confirm(self.default_review_first))
        self.bind("<Escape>", lambda event: self.destroy())

    def chosen_device(self):
        """(device name, device # text) for the new device: the name in the Device box (a typed
        name matching a discovered device, upper / lower case ignored, becomes that device's
        exact name), and the row's Device # - or, when the row has none, the chosen device's
        discovered number."""
        device_name = self.device_variable.get().strip()
        if device_name and device_name not in self.discovered_devices:
            device_name = self.device_names_by_lowercase.get(device_name.lower(), device_name)   # stored name
        row_device_number = self.table_row.get("Device #", "").strip()
        if row_device_number:
            return device_name, row_device_number
        return device_name, self.discovered_devices.get(device_name, "")

    def update_device_id_label(self):
        """Show the Device ID the new device will get (see chosen_device)."""
        _device_name, device_number = self.chosen_device()
        self.device_id_label.configure(text=device_number or "—")

    def on_device_text_typed(self, event):
        """While typing a device name: narrow the drop-down to the names containing the text
        (upper / lower case ignored) and update the Device ID shown."""
        if event.keysym in ("Up", "Down", "Return", "Escape", "Tab"):
            return
        typed_text = self.device_variable.get().strip().lower()
        self.device_chooser.configure(values=[device_name for device_name in self.all_device_names
                                              if typed_text in device_name.lower()] if typed_text
                                      else self.all_device_names)
        self.update_device_id_label()

    def skip_entry(self):
        """Skip: this entry is not added (it leaves the Selection list)."""
        self.result = {"action": "skip"}
        self.destroy()

    def combine_with_selected(self):
        """Combine: the entry selected in the Selection window becomes this device's second
        option (see apply_combined_entry).  Only two entries combine: choosing again replaces
        the second one."""
        selected_entry = self.selection_window.selected_entry() if self.selection_window else None
        if selected_entry is None or selected_entry[0] == self.entry_key:
            messagebox.showinfo("Combine", "Select the second entry in the Selection window, then press Combine.",
                                parent=self)
            return
        self.combined_key, self.combined_row = selected_entry
        self.combined_label.configure(
            text=f"Combined with: Arg # {self.combined_row.get('Arg #', '') or '—'}, "
                 f"{self.combined_row.get('Arg Name', '') or self.combined_row.get('Command', '')}, "
                 f"Command # {self.combined_row.get('Command #', '') or '—'} (the device's second option)")
        if self.combined_row.get("Command #", "").strip():
            self.action_id_label.configure(
                text=f"{self.table_row.get('Command #', '') or '—'} + {self.combined_row.get('Command #', '')}")

    def chosen_name(self):
        """The name picked in the dialog: the Help text, the row's Arg Name, its Command, or the
        typed name."""
        choice = self.name_choice.get()
        if choice == "help":
            return self.help_text
        if choice == "arg_name":
            return self.table_row.get("Arg Name", "").strip()
        if choice == "command":
            return self.table_row.get("Command", "").strip()
        return self.manual_name.get().strip()

    def confirm(self, review_first):
        """Create or Review button: check a name was chosen, store the choices in result (see
        the class notes) and close."""
        device_name = self.chosen_name()
        if not device_name:
            messagebox.showinfo("Build Device", "Choose or type a name for the device.", parent=self)
            return
        helios_type = HELIOS_TYPES[self.type_labels.index(self.type_variable.get())]
        chosen_device, chosen_device_number = self.chosen_device()
        self.result = {"action": "review" if review_first else "create", "helios_type": helios_type,
                       "name": device_name, "device_name": chosen_device, "device_number": chosen_device_number,
                       "combined_key": self.combined_key, "combined_row": self.combined_row}
        self.destroy()


# ════════════════════════════════════════════════════════════════════════════════
# VIEWPORT TAB
# ════════════════════════════════════════════════════════════════════════════════
# Lists the text passed to every try_find_assigned_viewport("...") call found by
# Table ▸ Generate… (see find_viewport_calls).  Every call is listed, so a name used by
# several indicators appears several times.  Read-only.
VIEWPORT_TAB_LABEL = "Viewport"


class ViewportPanel(tk.Frame):
    """Read-only list of viewport calls: the viewport text and the file it is in.
    The calls themselves are kept by the main window (HeliosEditor._viewport_calls) so
    they survive the tab rebuild of a theme switch; this panel only displays them."""

    VIEWPORT_COLUMNS = (("viewport", "Viewport", 260), ("file", "File", 760))

    def __init__(self, parent_frame, viewport_calls):
        """Build the Viewport tab: a count and a two-column list (viewport text, file) filled
        with viewport_calls."""
        super().__init__(parent_frame, bg=PANEL_BG)
        toolbar = tk.Frame(self, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)
        tk.Label(toolbar, text="try_find_assigned_viewport() calls   (filled by Table ▸ Generate…)",
                 bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left")
        self.count_label = tk.Label(toolbar, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
        self.count_label.pack(side="right", padx=(8, 8))

        list_container = tk.Frame(self, bg=PANEL_BG)
        list_container.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        vertical_scrollbar = ttk.Scrollbar(list_container, orient="vertical")
        horizontal_scrollbar = ttk.Scrollbar(list_container, orient="horizontal")   # long paths
        column_ids = [column_id for column_id, _label, _width in self.VIEWPORT_COLUMNS]
        self.viewport_view = ttk.Treeview(list_container, columns=column_ids, show="headings",
                                          selectmode="extended", yscrollcommand=vertical_scrollbar.set,
                                          xscrollcommand=horizontal_scrollbar.set)
        vertical_scrollbar.configure(command=self.viewport_view.yview)
        horizontal_scrollbar.configure(command=self.viewport_view.xview)
        for column_id, column_label, column_width in self.VIEWPORT_COLUMNS:
            self.viewport_view.heading(column_id, text=column_label, anchor=tk.W)
            self.viewport_view.column(column_id, width=column_width, minwidth=80, anchor=tk.W, stretch=True)
        self.viewport_view.tag_configure("even_row", background=ROW_EVEN)
        self.viewport_view.tag_configure("odd_row", background=ROW_ODD)
        vertical_scrollbar.pack(side="right", fill="y")
        horizontal_scrollbar.pack(side="bottom", fill="x")
        self.viewport_view.pack(side="left", fill="both", expand=True)
        self.show_viewport_calls(viewport_calls)

    def show_viewport_calls(self, viewport_calls):
        """Replace the list: one row per call, (viewport text, file path).  O(number of calls)."""
        self.viewport_view.delete(*self.viewport_view.get_children())
        for row_position, (viewport_text, file_path) in enumerate(viewport_calls):
            self.viewport_view.insert("", tk.END, values=(viewport_text, file_path),
                                      tags=("odd_row" if row_position % 2 else "even_row",))
        call_count = len(viewport_calls)
        self.count_label.configure(text=f"{call_count} call{'' if call_count == 1 else 's'}")


# ══════════════════════════════════════════════════════════════════════════════
# Argument Logger
# ══════════════════════════════════════════════════════════════════════════════
# The Argument Logger tab and its Logger menu: follows the log written by the DCS
# exporter ArgumentLogger_For_PythonGUI.lua (kept next to this editor; its control file
# and Logs folder are in Documents/Helios/Interface Editor) and shows every value DCS passes, with grouping.

# Capture categories written to the control file and read by the Lua exporter.
# (key, label, enabled by default).  The labels are also the names of the
# sub tabs of the Aircraft Data tab.
CAPTURE_OPTIONS = [
    ("ARGS", "Cockpit Arguments", True),
    ("INDICATIONS", "Indications", True),
    ("FLIGHT", "Flight Data", True),
    ("SYSTEMS", "Engine / Systems", True),
    ("SENSORS", "Sensors", True),
    ("DEVICES", "Radio / Device State", True),
    ("COMMANDS", "Commands Received", True),
    ("DRAWARGS", "Draw Arguments", True),
    ("PROBE", "Deep Device Probe", True),
]

# The log line type each capture option produces.
CAPTURE_LINE_TYPES = {
    "ARGS": "argument",
    "INDICATIONS": "indication",
    "FLIGHT": "flight",
    "SYSTEMS": "systems",
    "SENSORS": "sensors",
    "DEVICES": "device",
    "COMMANDS": "command",
    "DRAWARGS": "draw",
    "PROBE": "probe",
}

DATA_TYPES = [(CAPTURE_LINE_TYPES[key], label) for key, label, _default in CAPTURE_OPTIONS]

# The name of each type in the Type columns, e.g. "Cockpit Argument".
TYPE_NAMES = {
    "argument": "Cockpit Argument",
    "indication": "Indication",
    "flight": "Flight Data",
    "systems": "Engine / Systems",
    "sensors": "Sensor",
    "device": "Radio / Device State",
    "command": "Command Received",
    "draw": "Draw Argument",
    "probe": "Deep Device Probe",
}
# Sub tabs: (key, label).  "all" shows every type together.
LIVE_SUBTABS = [("all", "All")] + DATA_TYPES + [("gui", "GUI Markers")]
TRACKER_SUBTABS = [("all", "All")] + DATA_TYPES

INTERVAL_CHOICES = ("0.2", "0.5", "1", "2", "5", "10")
# Fill of the check / radio boxes in the Capture dialog, so the boxes stand out on the dark schemes.
CAPTURE_BOX_COLORS = {"dark": "#04060a", "grayscale": "#0a0a0a"}

# Device getters the exporter reads without the deep probe; any other
# getter in the log came from the deep probe.
SAFE_DEVICE_GETTERS = ("get_frequency", "is_on")

LINE_PREFIXES = [
    ("ARG CHANGE:", "argument"),
    ("ARG Marker", "argument"),
    ("DRAW CHANGE:", "draw"),
    ("DATA CHANGE: [FLIGHT]", "flight"),
    ("DATA REMOVED: [FLIGHT]", "flight"),
    ("DATA CHANGE: [SYSTEMS]", "systems"),
    ("DATA REMOVED: [SYSTEMS]", "systems"),
    ("DATA CHANGE: [SENSORS]", "sensors"),
    ("DATA REMOVED: [SENSORS]", "sensors"),
    ("DEV ", "device"),
    ("CMD IN:", "command"),
    ("[GUI]", "gui"),
]

MAX_MARKER_ROWS = 5000       # GUI Markers rows kept
MAX_ACTIVITY_PER_PARAMETER = 50
NO_PREVIOUS = "—"   # shown when the value was not known before the change
REMOVED = "(removed)"

# Line types whose numbers are formatted by the exporter.
NUMERIC_LINE_TYPES = ("argument", "draw", "flight", "systems", "sensors", "device", "probe", "command")
_NEGATIVE_ZERO = re.compile(r"(?<![\w.])-(0(?:\.0+)?)(?![\d.])")
_DEVICE_LINE = re.compile(r"^DEV (?:CHANGE|REMOVED): Dev \S+ (\S+)")
_CALL = re.compile(r"^(.*?)\(([^,()]*)(?:,\s*(.*))?\)$")

# Table layouts.  (column id, heading, width, stretch)
ARGUMENT_COLUMNS = (
    ("arg", "Arg #", 70, False),
    ("name", "Arg Name", 320, True),
    ("device", "Device", 200, True),
    ("command", "Command", 240, True),
    ("value", "Current Value", 110, False),
    ("difference", "Value Difference", 120, False),
)
INDICATOR_COLUMNS = (
    ("indicator", "Indicator #", 90, False),
    ("name", "Call Name", 320, True),
    ("last", "Last", 200, True),
    ("previous1", "Previous 1", 200, True),
    ("previous2", "Previous 2", 200, True),
)
CHANGE_COLUMNS = (
    ("type", "Type", 150, False),
    ("parameter", "Parameter", 320, True),
    ("previous", "Previous", 190, True),
    ("current", "Current", 190, True),
    ("change", "Change", 90, False),
)
MARKER_COLUMNS = (("message", "Message", 900, True),)
ACTIVITY_COLUMNS = (
    ("type", "Type", 150, False),
    ("parameter", "Parameter", 240, True),
    ("name", "Name", 220, True),
    ("current", "Current Value", 120, False),
    ("previous", "Previous Value", 120, False),
    ("difference", "Value Difference", 120, False),
)
GROUPED_COLUMNS = (
    ("type", "Type", 150, False),
    ("parameter", "Parameter", 200, True),
    ("name", "Name", 280, True),
    ("device", "Device", 180, True),
    ("command", "Command", 220, True),
)
# Cockpit and draw arguments share the Devices-tab layout and the reference table.
ARGUMENT_TYPES = ("argument", "draw")

# The column each table is sorted by until a heading is clicked: the
# parameter DCS passes.
DEFAULT_SORT = {"argument": "arg", "draw": "arg", "indication": "name", "gui": None}


def device_line_type(getter: str) -> str:
    """'device' for a getter known to be safe to read, else 'probe'."""
    return "device" if getter in SAFE_DEVICE_GETTERS else "probe"


def line_type_by_prefix(line: str):
    """The line type a log line's start gives it ("other" when no known prefix matches)."""
    for prefix, line_type in LINE_PREFIXES:
        if not line.startswith(prefix):
            continue
        device_match = _DEVICE_LINE.match(line) if line_type == "device" else None
        return device_line_type(device_match.group(1)) if device_match else line_type
    return "other"


def classify_line(line: str, in_indication_block: bool):
    """Return (line_type, in_indication_block) for one log line."""
    if line.startswith("indications Dump "):
        return "indication", True
    if in_indication_block:
        return "indication", line.strip() != ""
    if line.startswith("indications Removed "):
        return "indication", False
    return line_type_by_prefix(line), False


def build_control_text(enabled: bool, interval: float, options: dict) -> str:
    """Control file contents: ON/OFF on the first line, then KEY=VALUE options."""
    lines = ["ON" if enabled else "OFF", f"INTERVAL={interval:g}"]
    for key, _label, _default in CAPTURE_OPTIONS:
        lines.append(f"{key}={1 if options.get(key) else 0}")
    return "\n".join(lines) + "\n"


def strip_negative_zero(text: str) -> str:
    """Turn -0, -0.000 and similar into 0, 0.000."""
    return _NEGATIVE_ZERO.sub(r"\1", text)


def parse_number(text) -> Optional[float]:
    """The text as a finite float, or None when it is not a number."""
    try:
        number = float(text)
    except (TypeError, ValueError):
        return None
    return number if math.isfinite(number) else None


def parse_min_change(text: str) -> Optional[float]:
    """A threshold field's value: the absolute value of the number typed."""
    number = parse_number(text.strip().replace(",", "."))
    if number is None or number == 0:
        return None
    return abs(number)


def text_matches(filter_text: str, text: str) -> bool:
    """The Display Value filter: a case-insensitive match anywhere in the text."""
    return not filter_text or filter_text.lower() in text.lower()


def natural_key(value) -> tuple:
    """Sort numbers by value, then text alphabetically, then blanks."""
    text = str(value).strip()
    if text == "" or text == NO_PREVIOUS:
        return (2, "")
    number = parse_number(text)
    if number is not None:
        return (0, number)
    return (1, text.lower())


def aircraft_from_log(log_path: Optional[str]) -> str:
    """"A-10C_Argument_Log_2.log" -> "A-10C"."""
    if not log_path:
        return "Unknown Aircraft"
    name = os.path.basename(log_path)
    match = re.match(r"^(.+?)_Argument_Log(?:_\d+)?\.log$", name, re.IGNORECASE)
    return match.group(1) if match else os.path.splitext(name)[0]


class LoggerChange(NamedTuple):
    """One logged value that changed: scan, type, item, previous and current text, and the numeric change."""
    scan: str
    line_type: str
    item: str
    previous: str
    current: str
    delta: Optional[float] = None   # current - previous when both are numbers
    numeric: bool = False           # current is a number (previous may be unknown)
    extra: tuple = ()               # indications: (indicator #, call name, last, prev 1, prev 2)

    @property
    def delta_text(self) -> str:
        """The numeric change with its sign (empty when either value was not a number)."""
        return "" if self.delta is None else strip_negative_zero(f"{self.delta:+.3f}")

    @property
    def parameter(self) -> str:
        """The variable DCS passes: an argument number, a call name, a getter..."""
        if self.line_type == "indication" and self.extra:
            return self.extra[1]
        return self.item

    @property
    def key(self) -> tuple:
        """(type, parameter): what grouping works with."""
        return (self.line_type, self.parameter)

    @property
    def row_key(self) -> tuple:
        """Identifies the table row this value belongs to."""
        if self.line_type == "indication" and self.extra:
            return ("indication", self.extra[0], self.extra[1])
        return (self.line_type, self.item)


def change_passes_min(change: Optional[LoggerChange], min_change: Optional[float]) -> bool:
    """Rows are only hidden by a difference they have; rows without one stay."""
    if min_change is None or change is None or change.delta is None:
        return True
    return round(abs(change.delta), 9) >= min_change


class LoggerChangeTracker:
    """Turns log lines into Change records.

    feed() returns the changes: values that differ from the last value seen.
    The full listing DCS writes on the first scan after logging starts is
    remembered but not returned, because nothing changed yet.  Every value
    logged, changed or not, is also collected as a live record (see
    take_live_records).
    """

    _BASE = re.compile(r"^(ARG|DRAW) BASE: (?:Arg\s+(\d+)\s*=\s*(.*))?")
    _ARG = re.compile(r"^(ARG CHANGE|ARG Marker|DRAW CHANGE)\s*:\s*Arg\s+(\d+)\s*=\s*(.*)$")
    _DATA = re.compile(r"^DATA (CHANGE|REMOVED): \[(\w+)\] (.*)$")
    _DEV = re.compile(r"^DEV (CHANGE|REMOVED): (Dev \S+ (\S+))(?: = (.*))?$")
    _CMD = re.compile(r"^CMD IN: t=\S+ (.*)$")
    _IND_ROW = re.compile(r"^\s*\[(.*)\] = string: \"(.*)\"$")

    def __init__(self) -> None:
        self.reset()

    def reset(self) -> None:
        """Forget every value seen and start over without a baseline."""
        self.values = {}
        self.indications = {}
        self.scan = ""
        self.baseline = False
        self.indication_id = None
        self.indication_rows = {}
        # Set once the exporter has listed the non-zero starting values of
        # cockpit ("argument") or draw ("draw") arguments: from then on an
        # argument never seen before is known to have been 0.
        self.start_at_zero = set()
        self._base_pending = set()
        # (indicator number, call name) -> up to three values, newest first.
        # Neighbouring values always differ, so [1] is the last value that
        # was different from [0], and [2] the last that differed from [1].
        self.indicator_history = {}
        self.indicator_updates = set()   # keys changed since the view last looked
        self.live_records = []

    def take_live_records(self) -> list:
        """Hand over the changes recorded since the last call, and empty the list."""
        records, self.live_records = self.live_records, []
        return records

    def _record_indicator(self, indication_id: str, name: str, value: str) -> tuple:
        """Keep the last three values of one indicator, newest first; mark it updated when the value changes."""
        key = (indication_id, name)
        history = self.indicator_history.setdefault(key, [])
        if not history or history[0] != value:
            history.insert(0, value)
            del history[3:]
            self.indicator_updates.add(key)
        padded = list(history) + [""] * (3 - len(history))
        return (indication_id, name, padded[0], padded[1], padded[2])

    def indicator_row(self, key) -> tuple:
        """The table row of one indicator: id, name and its last three values."""
        history = self.indicator_history[key]
        padded = list(history) + [""] * (3 - len(history))
        return (key[0], key[1], padded[0], padded[1], padded[2])

    def feed(self, line: str) -> list:
        """Handle one log line; returns the changes it caused (see the class description)."""
        text = line.rstrip("\r\n")
        if self.indication_id is not None:
            return self._feed_indication_row(text)
        for line_handler in (self._feed_scan_line, self._feed_base_line, self._feed_indication_start_line,
                             self._feed_arg_line, self._feed_data_line, self._feed_device_line,
                             self._feed_command_line):
            changes = line_handler(text)
            if changes is not None:                   # None = this handler does not know the line
                return changes
        return []

    def _feed_indication_row(self, text):
        """A line inside an indications listing: a blank line ends it, a row is remembered."""
        if text.strip() == "":
            return self._finish_indication()
        match = self._IND_ROW.match(text)
        if match:
            self.indication_rows[match.group(1)] = match.group(2)
        return []

    def _feed_scan_line(self, text):
        """The '=== Scan ===' header and the 'Suppressing Initial Values' marker."""
        if text.startswith("=== Scan ==="):
            self.scan = text[len("=== Scan ==="):].strip()
            self.baseline = False
            return []
        if text.startswith("=   Suppressing Initial Values"):
            self.baseline = True
            self._base_pending = {"argument", "draw"}
            return []
        return None

    def _feed_base_line(self, text):
        """'ARG BASE:' / 'DRAW BASE:' - a starting value of the first scan."""
        match = self._BASE.match(text)
        if not match:
            return None
        line_type = "argument" if match.group(1) == "ARG" else "draw"
        if line_type in self._base_pending:
            # A fresh starting list replaces whatever was remembered.
            self._base_pending.discard(line_type)
            self.values = {key: value for key, value in self.values.items() if key[0] != line_type}
        self.start_at_zero.add(line_type)
        if match.group(2):
            key = (line_type, str(int(match.group(2))))
            self.values[key] = strip_negative_zero(match.group(3).strip())
            # The starting value is kept as a live record (the latest value of the parameter).
            self.live_records.append(self._make_change(line_type, key[1], None, self.values[key]))
        return []

    def _feed_indication_start_line(self, text):
        """'indications Dump <id>' starts a listing; 'indications Removed <id>' ends one at once."""
        if text.startswith("indications Dump "):
            self.indication_id = text[len("indications Dump "):].strip()
            self.indication_rows = {}
            return []
        if text.startswith("indications Removed "):
            self.indication_id = text[len("indications Removed "):].strip()
            self.indication_rows = {}
            return self._finish_indication()
        return None

    def _feed_arg_line(self, text):
        """'ARG CHANGE' / 'ARG Marker' / 'DRAW CHANGE'; "ARG Marker" is the only line the
        exporter writes when argument 1352 changes."""
        match = self._ARG.match(text)
        if not match:
            return None
        # The parameter is just the argument number.
        line_type = "draw" if match.group(1) == "DRAW CHANGE" else "argument"
        return self._changed(line_type, str(int(match.group(2))), match.group(3))

    def _feed_data_line(self, text):
        """'DATA CHANGE: [type] item = value' and 'DATA REMOVED: [type] item'."""
        match = self._DATA.match(text)
        if not match:
            return None
        line_type = match.group(2).lower()
        if match.group(1) == "REMOVED":
            return self._removed(line_type, match.group(3))
        item, separator, value = match.group(3).partition(" = ")
        return self._changed(line_type, item, value) if separator else []

    def _feed_device_line(self, text):
        """'DEV CHANGE' / 'DEV REMOVED' lines."""
        match = self._DEV.match(text)
        if not match:
            return None
        line_type = device_line_type(match.group(3))
        if match.group(1) == "REMOVED":
            return self._removed(line_type, match.group(2))
        return self._changed(line_type, match.group(2), match.group(4) or "")

    def _feed_command_line(self, text):
        """'CMD IN:' - a command received.  "Dev 023 performClickableAction(3001, 1)": the
        parameter is "Dev 023 performClickableAction(3001)" and the value is 1."""
        match = self._CMD.match(text)
        if not match:
            return None
        call = strip_negative_zero(match.group(1).strip())
        call_match = _CALL.match(call)
        if call_match:
            parameter = f"{call_match.group(1)}({call_match.group(2).strip()})"
            value = (call_match.group(3) or "").strip()
        else:
            parameter, value = call, ""
        return self._event("command", parameter, value)

    def _make_change(self, line_type, item, previous, value, extra=()) -> LoggerChange:
        """Build a LoggerChange, working out the numeric change when both values are numbers."""
        number = parse_number(value)
        delta = None
        if previous is not None and number is not None:
            previous_number = parse_number(previous)
            if previous_number is not None:
                delta = number - previous_number
        return LoggerChange(
            self.scan,
            line_type,
            item,
            NO_PREVIOUS if previous is None else previous,
            value,
            delta,
            number is not None,
            extra,
        )

    def _event(self, line_type: str, item: str, value: str) -> list:
        """Commands: every one is reported, even during the first scan."""
        key = (line_type, item)
        previous = self.values.get(key)
        self.values[key] = value
        change = self._make_change(line_type, item, previous, value)
        self.live_records.append(change)
        return [change]

    def _changed(self, line_type: str, item: str, value: str) -> list:
        """Store the new value of an item and give the change when it differs from the previous one."""
        value = strip_negative_zero(value.strip())
        key = (line_type, item)
        previous = self.values.get(key)
        if previous is None and line_type in self.start_at_zero:
            previous = "0.000"
        self.values[key] = value
        change = self._make_change(line_type, item, previous, value)
        self.live_records.append(change)
        if self.baseline or previous == value:
            return []
        return [change]

    def _removed(self, line_type: str, item: str) -> list:
        """Forget an item that DCS stopped sending and give the removal as a change."""
        previous = self.values.pop((line_type, item), None)
        change = LoggerChange(self.scan, line_type, item, NO_PREVIOUS if previous is None else previous, REMOVED)
        self.live_records.append(change)
        return [] if self.baseline else [change]

    def _finish_indication(self) -> list:
        """Close the indication being read and compare its rows with the previous dump of it."""
        indication_id, rows = self.indication_id, self.indication_rows
        self.indication_id, self.indication_rows = None, {}
        previous_values = self.indications.get(indication_id) or {}
        self.indications[indication_id] = rows

        changes = []
        names = sorted(set(rows) | set(previous_values))
        for name in names:
            current = rows.get(name, REMOVED)
            record = self._record_indicator(indication_id, name, current)
            change = LoggerChange(
                self.scan,
                "indication",
                f"Indication {indication_id}: {name}",
                previous_values.get(name, NO_PREVIOUS),
                current,
                extra=record,
            )
            if name in rows or name in previous_values:
                self.live_records.append(change)
            if not self.baseline and previous_values.get(name) != current:
                changes.append(change)
        return changes


def _normalise_arg(value) -> str:
    """Argument numbers as plain text without padding: "007" and 7 -> "7"."""
    text = str(value).strip()
    try:
        return str(int(text))
    except ValueError:
        return text


def _name_with_number(name: str, number: str) -> str:
    """"UFC" + "25" -> "UFC (25)"; a single value when only one is known."""
    if name and number and name != number:
        return f"{name} ({number})"
    return name or number


def reference_from_rows(table_rows) -> dict:
    """{arg number: [(arg name, device, command), ...]} from reference table rows
    ([{"Arg #": ..., "Arg Name": ..., "Device": ..., ...}], as in Tables > Reference).  An
    argument can have more than one row, for example a rocker switch whose two directions
    send different commands."""
    def field(row, name):
        """A row's value as stripped text (empty when missing)."""
        value = row.get(name)
        return "" if value is None else str(value).strip()

    reference = {}
    for row in table_rows:
        arg = field(row, "Arg #")
        if arg == "":
            continue
        entry = (
            field(row, "Arg Name"),
            _name_with_number(field(row, "Device"), field(row, "Device #")),
            _name_with_number(field(row, "Command"), field(row, "Command #")),
        )
        matches = reference.setdefault(_normalise_arg(arg), [])
        if entry not in matches:
            matches.append(entry)
    return reference




# ── Table addendum: names for the arguments a reference table leaves unnamed ──────
# When a reference table is loaded into the Argument Logger, every Arg # in its Cockpit
# Arguments and Draw Arguments sub tabs without an Arg Name is looked up in the aircraft's
# Lua files with the table generator's own parsing (clickable elements, arg definition
# files and arg mentions).  What is found is written, in the reference table format, to
# "Documents\Helios\Interface Editor\Table Updates\<aircraft> Table Addendum.json".
TABLE_UPDATES_FOLDER_NAME = "Table Updates"
# The logger's own folder (Logs, the control file, Table Updates) under Documents.
LOGGER_FOLDER_UNDER_DOCUMENTS = ("Helios", "Interface Editor")
TABLE_ADDENDUM_FILE_SUFFIX = " Table Addendum.json"
STEAM_DCS_AIRCRAFT_FOLDER = os.path.join(r"C:\Program Files (x86)\Steam\steamapps\common\DCSWorld",
                                         *DCS_AIRCRAFT_UNDER_INSTALL)


def comparable_vehicle_name(name):
    """A vehicle name as the exporter writes it in log file names ('F-14B Tomcat' and
    "'F-14B_Tomcat'" -> "f-14b_tomcat"), for comparing names from both places."""
    name = str(name).strip().strip("'\"")
    return re.sub(r"_+", "_", re.sub(r"[^\w\-]", "_", name)).strip("_").lower()


def dcs_aircraft_roots(saved_games_folder=None):
    """Every Mods\\aircraft folder an aircraft can be installed in: each DCS install under
    DCS_PUBLISHER_FOLDER, the Steam install, and the DCS Saved Games folder (mods)."""
    roots = []
    try:
        install_names = sorted(os.listdir(DCS_PUBLISHER_FOLDER), key=str.lower)
    except OSError:
        install_names = []
    install_names.sort(key=lambda name: name != DCS_PREFERRED_INSTALL_NAME)   # preferred first
    for install_name in install_names:
        roots.append(os.path.join(DCS_PUBLISHER_FOLDER, install_name, *DCS_AIRCRAFT_UNDER_INSTALL))
    roots.append(STEAM_DCS_AIRCRAFT_FOLDER)
    if saved_games_folder:
        roots.append(os.path.join(saved_games_folder, "Mods", "aircraft"))
    return [root for root in roots if os.path.isdir(root)]


def aircraft_folders_with_entry_file(aircraft_root):
    """[(folder name, path of its entry.lua)] for the folders of aircraft_root that have one."""
    try:
        folder_names = sorted(os.listdir(aircraft_root), key=str.lower)
    except OSError:
        return []
    entries = [(name, os.path.join(aircraft_root, name, VEHICLE_ENTRY_FILE_NAME)) for name in folder_names]
    return [(name, entry_path) for name, entry_path in entries if os.path.isfile(entry_path)]


def entry_file_makes_flyable(entry_path, wanted_name):
    """True when the entry.lua makes a vehicle flyable whose comparable name is wanted_name
    (an unreadable entry.lua counts as no)."""
    try:
        vehicle_names = find_flyable_vehicle_names([entry_path])
    except Exception:
        return False
    return wanted_name in {comparable_vehicle_name(name) for name in vehicle_names}


def find_aircraft_module_folder(vehicle_name, aircraft_roots):
    """The aircraft folder whose entry.lua makes `vehicle_name` flyable
    (make_flyable('FA-18C_hornet', ...) -> ...\\Mods\\aircraft\\FA-18C), or None."""
    wanted_name = comparable_vehicle_name(vehicle_name)
    for aircraft_root in aircraft_roots:
        for folder_name, entry_path in aircraft_folders_with_entry_file(aircraft_root):
            if entry_file_makes_flyable(entry_path, wanted_name):
                return os.path.join(aircraft_root, folder_name)
    return None


def same_aircraft(table_aircraft, aircraft_label, vehicle_name=""):
    """True when a reference table's aircraft ('FA-18C', from its folder or file name) is the
    aircraft being flown (its folder name 'FA-18C', or its vehicle name 'FA-18C_hornet')."""
    table_name = comparable_vehicle_name(table_aircraft)
    if not table_name:
        return True
    names = {comparable_vehicle_name(aircraft_label), comparable_vehicle_name(vehicle_name)} - {""}
    return any(table_name == name or name.startswith(table_name + "_") or table_name.startswith(name + "_")
               for name in names)


AIRCRAFT_FOLDER_IN_PATH = re.compile(r"[\\/]Mods[\\/]aircraft[\\/]([^\\/]+)", re.IGNORECASE)


def aircraft_of_viewport_files(loaded_data):
    """The aircraft folder name found in the first viewport file path that has one, or None."""
    if not isinstance(loaded_data, dict):
        return None
    for viewport in loaded_data.get(TABLE_FILE_VIEWPORTS_KEY) or []:
        if isinstance(viewport, dict):
            match = AIRCRAFT_FOLDER_IN_PATH.search(str(viewport.get("File", "")))
            if match:
                return match.group(1)
    return None


def reference_table_aircraft(loaded_data, file_path=""):
    """The aircraft a reference table file is for: the aircraft folder its viewport files
    are in (...\\Mods\\aircraft\\FA-18C\\...), else the name Generate gives the file
    ('FA-18C Reference Table.json'); None when it cannot be told."""
    aircraft = aircraft_of_viewport_files(loaded_data)
    if aircraft:
        return aircraft
    file_name = os.path.basename(file_path or "")
    if file_name.lower().endswith(REFERENCE_TABLE_FILE_SUFFIX.lower()):
        return file_name[: -len(REFERENCE_TABLE_FILE_SUFFIX)].strip() or None
    return None


def table_addendum_file_name(aircraft_label):
    """'FA-18C' -> 'FA-18C Table Addendum.json' (characters Windows forbids become '_')."""
    safe_label = re.sub(r'[<>:"/\\|?*]', "_", aircraft_label).strip() or "Aircraft"
    return safe_label + TABLE_ADDENDUM_FILE_SUFFIX


class ArgNameSearch:
    """Looks for the names of wanted Arg #s in one aircraft folder (see generate_arg_addendum)."""

    def __init__(self, aircraft_folder, wanted_args):
        self.aircraft_folder = os.path.abspath(aircraft_folder)
        self.wanted_args = wanted_args
        (self.lua_file_paths, self.clickabledata_paths,
         input_file_paths, _corrections) = find_aircraft_files(self.aircraft_folder)
        self.file_locator = LuaFileLocator(self.lua_file_paths)
        self.input_file_keys = {LuaExecutionContext.file_key(path) for path in input_file_paths}
        self.names_found = {}          # arg text -> (name, file path)
        self.element_rows_by_arg = {}  # arg text -> first element row (Type, Device, Command ...)
        self.warnings = []

    def run(self):
        """Search every clickabledata.lua (or the loose files when there is none); returns the rows."""
        for clickabledata_path in self.clickabledata_paths or [None]:
            self.search_one_aircraft(clickabledata_path)
        return self.build_rows()

    def relative_path(self, file_path):
        """A file path relative to the aircraft folder."""
        return os.path.relpath(file_path, self.aircraft_folder)

    def consider(self, number, name, file_path):
        """Remember a name for an arg that is wanted, has no name yet and gets a real name here."""
        arg_text = format_number_text(number) if is_lua_number(number) else str(number).strip()
        name_text = name if isinstance(name, str) else format_number_text(name)
        name_text = (name_text or "").strip()
        for field_name in ARG_VALUE_FIELD_NAMES:          # nav_light.arg = 3 -> nav_light
            if name_text.endswith("." + field_name):
                name_text = name_text[: -len(field_name) - 1]
        is_new_name = (arg_text in self.wanted_args and arg_text not in self.names_found
                       and name_text and name_text != arg_text)
        if is_new_name:
            self.names_found[arg_text] = (name_text, file_path)

    def search_one_aircraft(self, clickabledata_path):
        """Read one aircraft's clickabledata and arg definition files and collect the arg names."""
        context = LuaExecutionContext(self.aircraft_folder, self.file_locator)
        row_builder = TableRowBuilder(context)
        if clickabledata_path:
            self.read_clickabledata(context, row_builder, clickabledata_path)
            self.run_arg_files_nothing_includes(context)
            self.read_arg_definition_files(row_builder, clickabledata_path)
        self.read_other_files_with_arg_words(context, row_builder)
        self.use_hint_texts(row_builder, clickabledata_path)    # last resort
        self.warnings += context.warnings

    def read_clickabledata(self, context, row_builder, clickabledata_path):
        """Step 1: the elements of clickabledata.lua give Device / Command (and Type) and arg names."""
        try:
            context.run_lua_file(clickabledata_path)
            element_rows, _element_count = row_builder.build_element_rows(clickabledata_path)
        except Exception as error:                     # keep going with the other searches
            self.warnings.append(f"{self.relative_path(clickabledata_path)}: {error}")
            element_rows = []
        for element_row in element_rows:
            arg_text = element_row.get("Arg #", "").strip()
            if arg_text in self.wanted_args:
                self.element_rows_by_arg.setdefault(arg_text, element_row)
                self.consider(arg_text, element_row.get("Arg Name", ""), clickabledata_path)

    def run_arg_files_nothing_includes(self, context):
        """Step 2: every file whose name has an arg word is run, even when nothing includes it."""
        for lua_file_path in sorted(self.lua_file_paths):
            has_arg_word = any(word in os.path.basename(lua_file_path).lower() for word in ARG_FILE_NAME_WORDS)
            if LuaExecutionContext.file_key(lua_file_path) in self.input_file_keys or not has_arg_word:
                continue
            try:
                context.run_lua_file(lua_file_path)
            except Exception as error:
                self.warnings.append(f"{self.relative_path(lua_file_path)}: {error}")

    def read_arg_definition_files(self, row_builder, clickabledata_path):
        """Collect arg names from the arg definition files (a failure becomes a warning)."""
        try:
            definition_rows, _files = row_builder.build_definition_file_rows(clickabledata_path, [], "arg")
        except Exception as error:
            self.warnings.append(f"arg definition files: {error}")
            return
        for definition_row in definition_rows:
            source_file = (definition_row.get(SOURCE_FILES_MARKER) or (None,))[0]
            self.consider(definition_row.get("Arg #", ""), definition_row.get("Arg Name", ""), source_file)

    def read_other_files_with_arg_words(self, context, row_builder):
        """Step 3: every other .lua file that mentions an arg word is run and searched for args
        given to a variable (NAME.arg_number = 404, NAME = make_lamp{ arg = 404 })."""
        for lua_file_path in sorted(self.lua_file_paths):
            if LuaExecutionContext.file_key(lua_file_path) in self.input_file_keys:
                continue
            mentions = self.arg_mentions_in_file(context, row_builder, lua_file_path)
            for variable_name, arg_number in mentions:
                self.consider(arg_number, variable_name, lua_file_path)

    def arg_mentions_in_file(self, context, row_builder, lua_file_path):
        """[(variable name, arg number)] a file gives; [] for a file without an arg word or a bad file."""
        try:
            file_key = LuaExecutionContext.file_key(lua_file_path)
            parsed_file = context.parsed_files.get(file_key)
            source_text = parsed_file.source_text if parsed_file else read_lua_file_text(lua_file_path)
            if not ARG_MENTION_PATTERN.search(source_text):
                return []                              # no arg word: never parsed or run
            context.run_lua_file(lua_file_path)        # skipped when it already ran
            parsed_file = context.parsed_files.get(file_key)
            if parsed_file is None:
                return []
            return row_builder.with_file_scope(lua_file_path, lambda: row_builder.collect_arg_mentions(parsed_file))
        except Exception as error:                     # one bad file never stops the search
            self.warnings.append(f"{self.relative_path(lua_file_path)}: {error}")
            return []

    def use_hint_texts(self, row_builder, clickabledata_path):
        """Step 4: an arg still without a name takes its element's hint text (the control's tooltip)."""
        for arg_text, element_row in self.element_rows_by_arg.items():
            detail = row_builder.element_details.get(element_row.get("Note", ""), {})
            hint_text = str(detail.get("parameters", {}).get("hint_", "") or "").strip()
            if hint_text:
                self.consider(arg_text, hint_text, clickabledata_path)

    def build_rows(self):
        """One reference-table row for every arg a name was found for, in Arg # order."""
        kind_notes = {"cockpit": "Cockpit argument", "draw": "Draw argument", "both": "Cockpit and draw argument"}
        rows = []
        for arg_text in sorted(self.names_found, key=lambda text: (parse_number_or_none(text) is None,
                                                                    parse_number_or_none(text) or 0, text)):
            name, file_path = self.names_found[arg_text]
            element_row = self.element_rows_by_arg.get(arg_text, {})
            found_in = self.relative_path(file_path) if file_path else ""
            note = kind_notes.get(self.wanted_args[arg_text], "")
            rows.append({
                "Type": element_row.get("Type", ""),
                "Arg #": arg_text,
                "Arg Name": name,
                "Note": f"{note}; found in {found_in}" if found_in else note,
                "Device": element_row.get("Device", ""),
                "Device #": element_row.get("Device #", ""),
                "Command": element_row.get("Command", ""),
                "Command #": element_row.get("Command #", ""),
            })
        return rows


def generate_arg_addendum(aircraft_folder, wanted_args):
    """Look for names of the Arg #s in wanted_args ({arg text: "cockpit" / "draw" / "both"})
    with the table generator's parsing:
      1. each clickabledata.lua is run and its elements give Device / Command (and Type);
      2. the arg definition files give names (cockpit_args.RADIO_Power = 404); every file
         whose name has an arg word is run for this, even when nothing includes it;
      3. every other .lua file that mentions an arg word is run and searched for args given
         to a variable (NAME.arg_number = 404, NAME = make_lamp{ arg = 404 });
      4. an arg still without a name takes its clickable element's hint (tooltip) text.
    Unlike Generate, an Arg # already known is not skipped: these are the ones without a name.
    Returns (rows in the reference table format, warnings); only args a name was found for
    get a row."""
    search = ArgNameSearch(aircraft_folder, wanted_args)
    rows = search.run()
    return rows, search.warnings


class LoggerRow(NamedTuple):
    """One row of a logger table: its cell values, grouping meta, update key and Treeview tags."""
    values: tuple
    meta: Optional[tuple] = None   # (line type, parameter) for grouping
    key: Optional[tuple] = None    # identifies a row that is updated in place
    tags: tuple = ()               # Treeview tags (e.g. a row colour)


class LoggerTable:
    """A Treeview with scroll bars that sorts by any column.

    Click a heading to sort by it; click again to reverse.  New rows are put
    straight into their sorted place and the view never scrolls by itself.
    Rows with a key are updated in place by upsert() and never move when
    their values change; clicking a heading sorts them again.
    """

    def __init__(self, parent, columns, sortable: bool = True, default_sort: Optional[str] = None) -> None:
        self.columns = columns
        self.column_ids = [column[0] for column in columns]
        self.sortable = sortable
        self.sort_column = default_sort if sortable and default_sort in self.column_ids else None
        self.sort_descending = False
        self._seq = 0
        self._keys = []      # sort keys, ascending
        self._iids = []      # row ids in the same order as _keys
        self._info = {}      # row id -> [values, meta, key, sort key]
        self._by_key = {}    # row key -> row id

        frame = ttk.Frame(parent)
        frame.pack(fill=tk.BOTH, expand=True)
        self.tree = ttk.Treeview(frame, columns=self.column_ids, show="headings", selectmode="extended")
        for name, heading, width, stretch in columns:
            if sortable:
                self.tree.heading(name, text=heading, anchor=tk.W, command=lambda c=name: self.sort_by(c))
            else:
                self.tree.heading(name, text=heading, anchor=tk.W)
            self.tree.column(name, width=width, anchor=tk.W, stretch=stretch)
        scroll_y = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.tree.yview)
        scroll_x = ttk.Scrollbar(frame, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
        scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        scroll_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.tree.tag_configure("orange_row", background=LOGGER_ORANGE, foreground="#000000")
        self._update_headings()

    # -- reading ---------------------------------------------------------
    @property
    def headings(self) -> list:
        """The heading text of every column."""
        return [column[1] for column in self.columns]

    def rows(self) -> list:
        """Row values in the order shown."""
        return [tuple(self._info[row_id][0]) for row_id in self.tree.get_children() if row_id in self._info]

    def keys(self) -> list:
        """The update keys of the rows that have one."""
        return list(self._by_key)

    def selected_keys(self) -> list:
        """The keys of the selected rows, in the order shown."""
        return [self._info[row_id][2] for row_id in self.tree.get_children()
                if row_id in self.tree.selection() and row_id in self._info
                and self._info[row_id][2] is not None]

    def selected_metas(self) -> list:
        """The distinct meta values of the selected rows."""
        metas = []
        for row_id in self.tree.selection():
            info = self._info.get(row_id)
            if info is not None and info[1] is not None and info[1] not in metas:
                metas.append(info[1])
        return metas

    # -- sorting ---------------------------------------------------------
    def _sort_key(self, values, seq) -> tuple:
        """Sort key of a row: its natural-sorted value in the sort column, then its arrival order."""
        if self.sort_column is None:
            return (seq,)
        return (natural_key(values[self.column_ids.index(self.sort_column)]), seq)

    def _update_headings(self) -> None:
        """Show the sort arrow on the heading of the sorted column."""
        for name, heading, _width, _stretch in self.columns:
            if name == self.sort_column:
                heading += " ▼" if self.sort_descending else " ▲"
            self.tree.heading(name, text=heading)

    def sort_by(self, column: str) -> None:
        """Sort by a column; choosing the same column again reverses the order."""
        if column == self.sort_column:
            self.sort_descending = not self.sort_descending
        else:
            self.sort_column = column
            self.sort_descending = False
        self._update_headings()
        # Re-insert in the original arrival order so equal values keep it.
        ordered = sorted(self._info.values(), key=lambda info: info[3][-1])
        self.set_rows([LoggerRow(info[0], info[1], info[2], info[4]) for info in ordered])

    # -- writing ---------------------------------------------------------
    def _insert(self, row: LoggerRow) -> str:
        """Insert one row at its sorted position."""
        self._seq += 1
        sort_key = self._sort_key(row.values, self._seq)
        position = bisect.bisect_right(self._keys, sort_key)
        index = len(self._keys) - position if self.sort_descending else position
        row_id = self.tree.insert("", index, values=row.values, tags=tuple(row.tags))
        self._keys.insert(position, sort_key)
        self._iids.insert(position, row_id)
        self._info[row_id] = [tuple(row.values), row.meta, row.key, sort_key, tuple(row.tags)]
        if row.key is not None:
            self._by_key[row.key] = row_id
        return row_id

    def _remove(self, row_id) -> None:
        """Remove one row and its bookkeeping."""
        _values, _meta, key, sort_key, _tags = self._info.pop(row_id)
        position = bisect.bisect_left(self._keys, sort_key)
        del self._keys[position]
        del self._iids[position]
        if key is not None:
            self._by_key.pop(key, None)
        self.tree.delete(row_id)

    def append(self, rows) -> None:
        """Insert several rows at their sorted positions."""
        for row in rows:
            self._insert(row)

    def upsert(self, row: LoggerRow) -> None:
        """Add a keyed row, or update it where it is (it never moves)."""
        row_id = self._by_key.get(row.key)
        if row_id is None:
            self._insert(row)
            return
        info = self._info[row_id]
        values = tuple(row.values)
        if info[0] != values:
            self.tree.item(row_id, values=values)
            info[0] = values
        if info[4] != tuple(row.tags):
            self.tree.item(row_id, tags=tuple(row.tags))
            info[4] = tuple(row.tags)
        info[1] = row.meta

    def remove_key(self, key) -> None:
        """Remove the row with this update key, if there is one."""
        row_id = self._by_key.get(key)
        if row_id is not None:
            self._remove(row_id)

    def clear(self) -> None:
        """Remove every row."""
        self.tree.delete(*self.tree.get_children())
        self._keys, self._iids, self._info, self._by_key = [], [], {}, {}

    def set_rows(self, rows) -> None:
        """Replace every row, keeping the scroll position and keyed selections."""
        scroll_position = self.tree.yview()
        selected_keys = [self._info[row_id][2] for row_id in self.tree.selection()
                         if row_id in self._info and self._info[row_id][2] is not None]
        self.clear()
        sorted_entries = self._sorted_entries(rows)
        for sort_key, row in (reversed(sorted_entries) if self.sort_descending else sorted_entries):
            row_id = self.tree.insert("", tk.END, values=row.values, tags=tuple(row.tags))
            self._info[row_id] = [tuple(row.values), row.meta, row.key, sort_key, tuple(row.tags)]
            if row.key is not None:
                self._by_key[row.key] = row_id
        # _keys and _iids are kept in ascending order.
        self._keys = [sort_key for sort_key, _row in sorted_entries]
        ascending_row_ids = list(self.tree.get_children())
        if self.sort_descending:
            ascending_row_ids.reverse()
        self._iids = ascending_row_ids
        self._reselect_keys(selected_keys)
        if scroll_position:
            self.tree.yview_moveto(scroll_position[0])

    def _sorted_entries(self, rows) -> list:
        """[(sort key, row)] of the rows in ascending sort order (equal keys keep their order)."""
        entries = []
        for row in rows:
            self._seq += 1
            entries.append((self._sort_key(row.values, self._seq), row))
        entries.sort(key=lambda entry: entry[0])
        return entries

    def _reselect_keys(self, selected_keys) -> None:
        """Select again the rows that have these keys (those still present)."""
        for key in selected_keys:
            row_id = self._by_key.get(key)
            if row_id is not None:
                self.tree.selection_add(row_id)


ALL_FILES_OPTION = "All"       # File Filter choice that shows every value
LOGGER_ORANGE = "#ff9a00"      # bright orange: in the logger and the Reference table, not in the interface


class FileFilterBox(ttk.Frame):
    """A fillable "File Filter:" box.  Typing lists the file names that contain the typed
    text; Up / Down choose one, Tab (or Enter) completes it.  Only file names are shown,
    never paths.  The text lives in `variable` (shared by every box showing it) and
    `on_change` is called once a name is chosen, or the box is emptied."""

    MAX_LISTED = 10

    def __init__(self, parent, variable, get_names, on_change, width=28) -> None:
        super().__init__(parent)
        self.variable = variable
        self.get_names = get_names
        self.on_change = on_change
        self.popup = None
        self.listbox = None
        self.matches = []
        self.entry = ttk.Entry(self, textvariable=variable, width=width)
        self.entry.pack(side=tk.LEFT)
        self.button = ttk.Button(self, text="\u25bc", width=2, command=self.show_all)
        self.button.pack(side=tk.LEFT, padx=(2, 0))
        self.entry.bind("<KeyRelease>", self._key_release)
        self.entry.bind("<Down>", lambda _e: self._move(1))
        self.entry.bind("<Up>", lambda _e: self._move(-1))
        self.entry.bind("<Tab>", self._tab)
        self.entry.bind("<Return>", self._return)
        self.entry.bind("<Escape>", lambda _e: self.close_popup())
        self.entry.bind("<FocusOut>", lambda _e: self.after(150, self._focus_lost))
        self.bind("<Destroy>", lambda _e: self.close_popup(), add="+")

    # -- list ------------------------------------------------------------
    def _matching(self, text: str) -> list:
        """The file names to offer for the typed text: names starting with it first, then names containing it."""
        text = text.strip().lower()
        names = [ALL_FILES_OPTION] + list(self.get_names())
        if not text:
            return names
        starts = [name for name in names if name.lower().startswith(text)]
        contains = [name for name in names if text in name.lower() and name not in starts]
        return starts + contains

    def show_all(self) -> None:
        """Drop down the list of every file name."""
        self._open_popup(self._matching(""))
        self.entry.focus_set()

    def _open_popup(self, matches) -> None:
        """Show (or refresh) the drop-down list of matches under the entry."""
        self.matches = matches[:200]
        if not self.matches:
            self.close_popup()
            return
        if self.popup is None:
            self.popup = tk.Toplevel(self)
            self.popup.withdraw()
            self.popup.overrideredirect(True)
            self.listbox = tk.Listbox(self.popup, bg=MID_BG, fg=TEXT_PRI, selectbackground=ACCENT,
                                      selectforeground=DARK_BG, font=FONT_UI, activestyle="none",
                                      exportselection=False, relief=tk.SOLID, bd=1)
            self.listbox.pack(fill=tk.BOTH, expand=True)
            self.listbox.bind("<Button-1>", self._click)
            self.listbox.bind("<Double-Button-1>", self._click)
        self.listbox.delete(0, tk.END)
        for name in self.matches:
            self.listbox.insert(tk.END, name)
        self.listbox.configure(height=min(self.MAX_LISTED, len(self.matches)))
        self.update_idletasks()
        x = self.entry.winfo_rootx()
        y = self.entry.winfo_rooty() + self.entry.winfo_height()
        self.popup.geometry(f"{max(self.entry.winfo_width(), 220)}x{self.listbox.winfo_reqheight()}+{x}+{y}")
        self.popup.deiconify()
        self.popup.lift()

    def close_popup(self) -> None:
        """Close the drop-down list."""
        if self.popup is not None:
            try:
                self.popup.destroy()
            except tk.TclError:
                pass
        self.popup = None
        self.listbox = None
        self.matches = []

    def _pointer_in_popup(self) -> bool:
        """True when the mouse pointer is over the drop-down list."""
        if self.popup is None:
            return False
        try:
            x, y = self.popup.winfo_pointerxy()
            return (self.popup.winfo_rootx() <= x < self.popup.winfo_rootx() + self.popup.winfo_width()
                    and self.popup.winfo_rooty() <= y < self.popup.winfo_rooty() + self.popup.winfo_height())
        except tk.TclError:
            return False

    def _focus_lost(self) -> None:
        """Close the drop-down list when focus leaves the entry (unless the list itself is being clicked)."""
        if self._pointer_in_popup():
            return                             # a click on the list is on its way
        try:
            if self.focus_get() is not self.entry:
                self.close_popup()
        except (tk.TclError, KeyError):
            self.close_popup()

    # -- keys ------------------------------------------------------------
    def _key_release(self, event) -> None:
        """After a key press: refresh the list of matching file names (navigation keys are ignored)."""
        if event.keysym in ("Up", "Down", "Tab", "Return", "Escape", "Shift_L", "Shift_R", "Control_L",
                            "Control_R", "ISO_Left_Tab"):
            return
        text = self.variable.get().strip()
        if not text:
            self.close_popup()
            self.on_change()
            return
        self._open_popup(self._matching(text))
        exact = [name for name in [ALL_FILES_OPTION] + list(self.get_names()) if name.lower() == text.lower()]
        if exact:
            self.on_change()

    def _selected_index(self):
        """Position of the highlighted entry in the list, or None."""
        if self.listbox is None:
            return None
        selection = self.listbox.curselection()
        return selection[0] if selection else None

    def _move(self, step: int):
        """Move the highlight up or down the list (opening it first when closed)."""
        if self.popup is None:
            self._open_popup(self._matching(self.variable.get()))
        if self.listbox is None or not self.matches:
            return "break"
        current = self._selected_index()
        if current is None:
            new_index = 0 if step > 0 else len(self.matches) - 1
        else:
            new_index = max(0, min(len(self.matches) - 1, current + step))
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(new_index)
        self.listbox.see(new_index)
        return "break"

    def _choose(self, name: str) -> None:
        """Take the chosen file name, close the list and apply the filter."""
        self.variable.set(name)
        self.entry.icursor(tk.END)
        self.close_popup()
        self.on_change()

    def _tab(self, _event):
        """Tab picks the highlighted (or first) match when the list is open."""
        if self.popup is None or not self.matches:
            return None                       # no list: Tab moves on as usual
        index = self._selected_index()
        self._choose(self.matches[0 if index is None else index])
        return "break"

    def _return(self, _event):
        """Return picks the highlighted match, or just applies the typed text."""
        if self.popup is not None and self.matches:
            index = self._selected_index()
            if index is not None:
                self._choose(self.matches[index])
                return "break"
        self.close_popup()
        self.on_change()
        return "break"

    def _click(self, event):
        """A click on a name chooses it at once (the pointer may leave the box before the
        button is released, so this does not wait for the release)."""
        if self.listbox is None:
            return "break"
        index = self.listbox.nearest(event.y)
        if 0 <= index < len(self.matches):
            self._choose(self.matches[index])
        return "break"


class ArgumentLoggerPanel:
    """The Argument Logger tab: follows the log the DCS exporter
    (ArgumentLogger_For_PythonGUI.lua) writes and shows it in the Change Tracker and Live
    Viewer sub tabs, with grouping.

    The logger's data lives in this object for the whole session.  build_menu() adds the
    Logger menu to the editor's menu bar and build_ui() draws the tab; the editor calls both
    again whenever it rebuilds its window (a colour scheme change), and the tab is redrawn
    from the data kept here.  The exporter is kept next to the editor; its control file, the
    Logs folder and Table Updates are in Documents\\Helios\\Interface Editor.  The Arg Names, Devices
    and Commands come from the table in Tables > Reference (see use_reference_rows)."""

    def __init__(self, host) -> None:
        self.host = host

        app_path = sys.executable if getattr(sys, "frozen", False) else __file__
        self.app_dir = os.path.dirname(os.path.abspath(app_path))
        # Without a DCS Saved Games folder the logger still shows logs, but cannot set the
        # Export.lua hook; the reason is shown when the tab is first opened.
        self.saved_games_error = None
        try:
            self.saved_games_dir = self._detect_saved_games_dir()
        except RuntimeError as error:
            self.saved_games_dir = None
            self.saved_games_error = str(error)
        self.scripts_dir = os.path.join(self.saved_games_dir, "Scripts") if self.saved_games_dir else None
        self.export_lua_path = os.path.join(self.scripts_dir, "Export.lua") if self.scripts_dir else None
        # The Lua exporter stays next to the editor; the logs and the control file DCS reads
        # live in Documents\\Helios\\Interface Editor (the folder is passed to the exporter by
        # the Export.lua hook line).
        self.logger_dir = os.path.join(documents_folder(), *LOGGER_FOLDER_UNDER_DOCUMENTS)
        self.lua_export_path = os.path.join(self.app_dir, "ArgumentLogger_For_PythonGUI.lua")
        self.log_dir = os.path.join(self.logger_dir, "Logs")
        self.log_path = None
        self.control_path = os.path.join(self.logger_dir, "ArgumentLogger_For_PythonGUI.control")
        try:
            os.makedirs(self.log_dir, exist_ok=True)
        except OSError:
            pass

        self.tail_fp = None
        self.tail_offset = 0
        self.follow_log = True
        self.pending_fragment = ""   # incomplete last line of the log
        self.in_indication_block = False
        self.logging_enabled = False
        self.tracker = LoggerChangeTracker()
        # One table row per parameter, updated in place.  Keyed by row key.
        self.live_state = {}         # latest value logged for each parameter (LoggerChange)
        self.tracker_state = {}      # latest change of each parameter that changed (LoggerChange)
        self.markers = []            # GUI markers (scan start / stop notes): list of LoggerRow
        self.reference = {}          # arg number -> [(arg name, device, command)]
        self.reference_path = None   # the Reference tab's file, when it has one
        self._reference_signature = None   # the Reference tab's rows last taken over
        # Grouping windows.
        self.activity_window = None
        self.activity_view = None
        self.activity_threshold_var = None
        self.activity_changes = {}   # (line type, parameter) -> recent changes
        self.grouped_window = None
        self.grouped_view = None
        self.grouped_keys = []       # (line type, parameter) in the order added
        self.grouped_removed = set() # Grouped Commands rows taken out with Remove
        self._filter_job = None
        self._last_poll_status = None
        self.hook_checked = False    # the Export.lua hook is checked when the tab is first opened
        # Table addendum (see generate_arg_addendum): searched on a worker thread.
        self._addendum_pending = False
        self._addendum_thread = None
        self._addendum_result = None
        self._aircraft_folders = {}  # vehicle name (from the log) -> aircraft folder
        self._addendum_table_aircraft = None   # the aircraft of the table the search waits for
        # The aircraft being flown (see _check_running_aircraft).
        self._session_start = time.time()      # logs written before this are from an earlier session
        self._detected_vehicle = None
        self._aircraft_check_busy = False
        self._locked_aircraft = None           # (folder name, vehicle) the logger generated the table for

        # Widgets: made by build_ui() (and made again when the editor rebuilds its tabs).
        self.views_built = False
        self.panel_frame = None
        self.notebook = None
        self.tracker_notebook = None
        self.live_notebook = None
        self.tracker_subtab_keys = [key for key, _label in TRACKER_SUBTABS]
        self.live_subtab_keys = [key for key, _label in LIVE_SUBTABS]
        self.tracker_views = {}
        self.live_views = {}
        self.logger_menu = None

        # Settings and readouts that outlive a rebuild of the tab.
        self.capture_vars = {
            key: tk.BooleanVar(master=host, value=default) for key, _label, default in CAPTURE_OPTIONS
        }
        saved_interval = str(getattr(host, "editor_settings", {}).get("scan_interval", "1"))
        self.interval_var = tk.StringVar(master=host, value=saved_interval if saved_interval in INTERVAL_CHOICES else "1")
        self.display_value_var = tk.StringVar(master=host)
        self.min_change_var = tk.StringVar(master=host)
        self.file_filter_var = tk.StringVar(master=host, value=ALL_FILES_OPTION)
        self.not_in_interface_var = tk.BooleanVar(master=host, value=False)
        self.file_hint_var = tk.StringVar(master=host, value="")
        self.file_names = []               # the source file names, as shown (no paths)
        self.file_ref_ids = {}             # lower-case file name -> {id(reference row)}
        self.reference_entry_rows = {}     # (arg, (name, device, command)) -> [reference rows]
        self.reference_rows_by_arg = {}
        self.reference_rows_by_command = {}
        self._seen_job = None
        self._reported_keys = set()
        self.status_var = tk.StringVar(master=host, value="Status: Waiting for log file")
        self.scan_var = tk.StringVar(master=host, value="Scan: —")
        self.tracker_count_var = tk.StringVar(master=host, value="No changes yet")
        self.logging_button_var = tk.StringVar(master=host, value="Start Logging")
        self.log_path_var = tk.StringVar(master=host, value="Log: waiting for session")
        self.control_path_var = tk.StringVar(master=host, value=f"Control: {self.control_path}")
        self.export_path_var = tk.StringVar(
            master=host,
            value=(f"Export.lua: {self.export_lua_path}" if self.export_lua_path
                   else "Export.lua: DCS Saved Games folder not found"),
        )
        self.reference_var = tk.StringVar(
            master=host, value="Reference: Tables > Reference is empty"
        )

        try:
            self._ensure_control_file("OFF")
        except OSError as error:
            self._set_status(f"Could not write the control file: {error}")
        self.host.after(300, self._poll_log)

    # ------------------------------------------------------------------
    # Menu and layout
    # ------------------------------------------------------------------
    def build_menu(self, menu_bar, menu_options) -> None:
        """Add the Logger menu to the editor's menu bar."""
        logger_menu = tk.Menu(menu_bar, **menu_options)
        self.logger_menu = logger_menu
        menu_bar.add_cascade(label="Logger", menu=logger_menu)

        # Capture opens a pop-up window with the capture options and an Apply button.
        self.capture_panel = None
        self.capture_click_binding = None
        self.capture_dirty = False
        self.capture_dialog = None
        logger_menu.add_command(label="Capture", command=self.open_capture_dialog)
        logger_menu.add_separator()

        logger_menu.add_command(label="Open Log Folder", command=self.open_log_folder)
        logger_menu.add_command(label="Set Export Hook", command=self.install_export_hook)

    def build_ui(self, parent) -> None:
        """Draw the tab inside `parent` (the Argument Logger tab's frame) and fill it from
        the data kept in this object."""
        self.views_built = False
        self.panel_frame = parent

        top = ttk.Frame(parent, padding=10)
        top.pack(fill=tk.X)

        ttk.Label(
            top,
            text=(
                "Start DCS and enter the cockpit, then click Start Logging. "
                "Logger > Capture chooses what DCS writes to the log. Click a column heading to sort."
            ),
        ).pack(anchor=tk.W, pady=(0, 8))

        buttons = ttk.Frame(top)
        buttons.pack(fill=tk.X)
        # One button starts and stops logging; its label says what a click will do.
        ttk.Button(buttons, textvariable=self.logging_button_var, command=self.toggle_logging,
                   width=14).pack(side=tk.LEFT)
        ttk.Button(buttons, text="Start Grouping", command=self.start_grouping).pack(side=tk.LEFT, padx=(8, 0))
        ttk.Button(buttons, text="Generate Change Log", command=self.generate_change_log).pack(
            side=tk.LEFT, padx=(8, 0))
        ttk.Button(buttons, text="Clear View", command=self.clear_view).pack(side=tk.LEFT, padx=(8, 0))
        # The scan the latest values came from.
        ttk.Label(buttons, textvariable=self.scan_var, font=FONT_HEAD).pack(side=tk.LEFT, padx=(16, 0))
        ttk.Label(buttons, textvariable=self.tracker_count_var).pack(side=tk.LEFT, padx=(16, 0))

        # One filter for every table.
        filter_frame = ttk.LabelFrame(top, text="Entry Filter", padding=(10, 6))
        filter_frame.pack(fill=tk.X, pady=(8, 0))
        first_row = ttk.Frame(filter_frame)
        first_row.pack(fill=tk.X)
        ttk.Label(first_row, text="Display Value:").pack(side=tk.LEFT)
        display_entry = ttk.Entry(first_row, textvariable=self.display_value_var, width=32)
        display_entry.pack(side=tk.LEFT, padx=(6, 16))
        display_entry.bind("<KeyRelease>", self._schedule_filter)
        ttk.Label(first_row, text="Min Change (≥):").pack(side=tk.LEFT)
        min_change_entry = ttk.Entry(first_row, textvariable=self.min_change_var, width=10)
        min_change_entry.pack(side=tk.LEFT, padx=(6, 12))
        min_change_entry.bind("<KeyRelease>", self._schedule_filter)
        ttk.Label(first_row, text="Min Change applies to the Change Tracker.",
                  foreground=TEXT_SEC).pack(side=tk.LEFT)
        second_row = ttk.Frame(filter_frame)
        second_row.pack(fill=tk.X, pady=(6, 0))
        ttk.Label(second_row, text="File Filter:").pack(side=tk.LEFT)
        self.file_filter_box = FileFilterBox(second_row, self.file_filter_var, lambda: self.file_names,
                                             self._on_file_filter_changed)
        self.file_filter_box.pack(side=tk.LEFT, padx=(6, 16))
        ttk.Checkbutton(second_row, text="Only values not in the interface",
                        variable=self.not_in_interface_var,
                        command=self._on_file_filter_changed).pack(side=tk.LEFT)
        tk.Label(second_row, text=" orange ", bg=LOGGER_ORANGE, fg="#000000", font=FONT_UI).pack(
            side=tk.LEFT, padx=(12, 4))
        ttk.Label(second_row, text="= in the Reference table and the logger, not in the interface",
                  foreground=TEXT_SEC).pack(side=tk.LEFT)
        ttk.Label(second_row, textvariable=self.file_hint_var, foreground=TEXT_SEC).pack(
            side=tk.LEFT, padx=(12, 0))


        path_frame = ttk.Frame(parent, padding=(10, 8, 10, 8))
        path_frame.pack(fill=tk.X)
        for variable in (self.log_path_var, self.control_path_var, self.export_path_var, self.reference_var):
            ttk.Label(path_frame, textvariable=variable).pack(anchor=tk.W)

        self.notebook = ttk.Notebook(parent)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        # ---- The tracker's sub tabs sit directly in the Aircraft Data tab.
        self.tracker_notebook = self.notebook
        self.tracker_views = {}
        self.live_views = {}
        for key, label in TRACKER_SUBTABS:
            frame = ttk.Frame(self.tracker_notebook, padding=4)
            self.tracker_notebook.add(frame, text=label)
            self.tracker_views[key] = LoggerTable(
                frame, self._subtab_columns(key), default_sort=DEFAULT_SORT.get(key, "parameter"))

        self.views_built = True
        self._render_all_views()

    @staticmethod
    def _subtab_columns(key: str):
        # Cockpit / Draw Arguments use the argument layout (with the reference table) and
        # Indications the indicator layout.
        """The columns of a logger sub tab: argument layout for Cockpit / Draw Arguments, indicator layout for Indications."""
        if key in ARGUMENT_TYPES:
            return ARGUMENT_COLUMNS
        if key == "indication":
            return INDICATOR_COLUMNS
        if key == "gui":
            return MARKER_COLUMNS
        return CHANGE_COLUMNS

    def on_shown(self) -> None:
        """The tab was brought to the front: the first time, check the Export.lua hook."""
        if self.hook_checked:
            return
        self.hook_checked = True
        if self.saved_games_error:
            self._set_status("DCS Saved Games folder not found: the Export.lua hook cannot be set")
            messagebox.showwarning("Argument Logger", self.saved_games_error, parent=self.host)
            return
        self._check_export_hook_on_startup()

    def open_capture_dialog(self) -> None:
        """Logger > Capture: a pop-up with every capture option (the categories and the scan
        interval).  Ticking changes nothing yet; Apply puts the choices into effect (the control
        file is updated) and closes the pop-up; closing it any other way drops the choices."""
        existing = self.capture_dialog
        if existing is not None and existing.winfo_exists():
            existing.lift()
            existing.focus_force()
            return
        host = self.host.winfo_toplevel()
        dialog = tk.Toplevel(host)
        self.capture_dialog = dialog
        dialog.title("Capture")
        dialog.configure(bg=PANEL_BG)
        dialog.transient(host)
        dialog.resizable(False, False)
        box_color = self._check_box_color()            # contrasting boxes on the dark schemes
        staged = {key: tk.BooleanVar(master=dialog, value=self.capture_vars[key].get())
                  for key, _label, _default in CAPTURE_OPTIONS}
        staged_interval = tk.StringVar(master=dialog, value=self.interval_var.get())

        content = tk.Frame(dialog, bg=PANEL_BG, padx=16, pady=12)
        content.pack(fill="both", expand=True)

        def style(widget):
            """Apply the dialog's colours and layout to one widget."""
            widget.configure(bg=PANEL_BG, fg=TEXT_PRI, activebackground=PANEL_BG, activeforeground=TEXT_PRI,
                             selectcolor=box_color, font=FONT_UI, anchor="w", highlightthickness=0, bd=0)
            widget.pack(fill="x", pady=1)

        tk.Label(content, text="Capture", bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD, anchor="w").pack(fill="x", pady=(0, 4))
        for key, label, _default in CAPTURE_OPTIONS:
            style(tk.Checkbutton(content, text=label + " (slower)" if key == "PROBE" else label,
                                 variable=staged[key]))
        tk.Frame(content, bg=BORDER, height=1).pack(fill="x", pady=8)
        tk.Label(content, text="Scan Interval", bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD, anchor="w").pack(fill="x", pady=(0, 4))
        for value in INTERVAL_CHOICES:
            style(tk.Radiobutton(content, text=f"{value} s", value=value, variable=staged_interval))

        def apply_and_close():
            """Apply the staged capture choices and scan interval, then close the dialog."""
            for key, variable in staged.items():
                self.capture_vars[key].set(variable.get())
            self.interval_var.set(staged_interval.get())
            self._on_capture_changed()
            self.close_capture_dialog()

        tk.Button(content, text="Apply", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat", padx=18, pady=5,
                  cursor="hand2", command=apply_and_close).pack(anchor="e", pady=(12, 0))
        dialog.protocol("WM_DELETE_WINDOW", self.close_capture_dialog)
        dialog.bind("<Escape>", lambda _event: self.close_capture_dialog())
        center_over(host, dialog)
        dialog.focus_force()

    def close_capture_dialog(self) -> None:
        """Close the Capture dialog if it is open."""
        dialog, self.capture_dialog = self.capture_dialog, None
        if dialog is not None:
            try:
                dialog.destroy()
            except tk.TclError:
                pass

    def _check_box_color(self) -> str:
        """The fill of the check / radio boxes in the Capture dialog: a box that contrasts with the
        dialog on the two dark colour schemes, the panel colour on the light one."""
        theme_name = getattr(self.host, "_theme_name", "default")
        return CAPTURE_BOX_COLORS.get(theme_name, MID_BG)

    def _mark_capture_changed(self) -> None:
        """An option was ticked in the Capture window: it takes effect when the window closes."""
        self.capture_dirty = True

    def close_capture_panel(self) -> None:
        """Close the Capture window; the choices made in it take effect now."""
        panel, self.capture_panel = self.capture_panel, None
        if self.capture_dirty:                        # the panel closed: all the picks take effect now
            self.capture_dirty = False
            self._on_capture_changed()
        binding, self.capture_click_binding = self.capture_click_binding, None
        if binding is not None:
            try:
                self.host.winfo_toplevel().unbind("<ButtonPress>", binding)
            except tk.TclError:
                pass
        if panel is not None:
            try:
                panel.destroy()
            except tk.TclError:
                pass

    def toggle_logging(self) -> None:
        """The Start Logging / Stop Logging button."""
        if self.logging_enabled:
            self.stop_logging()
        else:
            self.start_logging()
        self.logging_button_var.set("Stop Logging" if self.logging_enabled else "Start Logging")

    def close(self) -> None:
        """Stop following the log (the editor is closing)."""
        self.close_capture_panel()
        self.follow_log = False
        if self.tail_fp is not None:
            try:
                self.tail_fp.close()
            except OSError:
                pass

    def _grouping_anchor(self):
        """The grouping windows are centred on the Argument Logger tab."""
        if self.panel_frame is not None and self.panel_frame.winfo_exists():
            return self.panel_frame
        return self.host

    def _is_valid_dcs_saved_games_dir(self, folder: str) -> bool:
        """True when the folder looks like a DCS Saved Games folder (Scripts, Mods, Config and a Mission Editor folder)."""
        if not folder:
            return False
        required_dirs = ("Scripts", "Mods", "Config")
        if not all(os.path.isdir(os.path.join(folder, name)) for name in required_dirs):
            return False
        mission_editor_dirs = ("Mission Editor", "MissionEditor")
        return any(os.path.isdir(os.path.join(folder, name)) for name in mission_editor_dirs)

    def _detect_saved_games_dir(self) -> str:
        """The DCS Saved Games folder: DCS_SAVED_GAMES_DIR, else the profile this copy of the app
        sits in, else the one DCS-prefixed folder under Saved Games.  Raises RuntimeError when
        there is none or more than one."""
        # 1) Allow explicit override for advanced users.
        env_override = os.environ.get("DCS_SAVED_GAMES_DIR", "").strip()
        if self._is_valid_dcs_saved_games_dir(env_override):
            return os.path.abspath(env_override)
        # 2) Prefer a DCS profile above this copy if it is inside Scripts.
        profile_above_app = self._saved_games_dir_above_app()
        if profile_above_app:
            return profile_above_app
        # 3) Search DCS-prefixed Saved Games folders if the logger was launched elsewhere.
        candidates = self._saved_games_candidates()
        if len(candidates) == 1:
            return candidates[0]
        if candidates:
            folders = "\n".join(candidates)
            raise RuntimeError(
                "More than one DCS Saved Games folder contains the expected profile folders "
                "(Scripts, Mods, Config, and MissionEditor/Mission Editor):\n"
                f"{folders}\n\n"
                "This app can run from any folder. Set DCS_SAVED_GAMES_DIR "
                "to the intended Saved Games folder."
            )
        raise RuntimeError(
            "Could not find a DCS Saved Games folder containing Scripts, Mods, Config, "
            "and MissionEditor (or Mission Editor). "
            "Set DCS_SAVED_GAMES_DIR to the intended Saved Games folder. "
            "This app can run from any folder."
        )

    def _saved_games_dir_above_app(self) -> str:
        """The valid DCS profile folder that has this app inside its Scripts folder, or ''."""
        app_path = sys.executable if getattr(sys, "frozen", False) else __file__
        current_dir = os.path.dirname(os.path.abspath(app_path))
        while True:
            if os.path.basename(current_dir).casefold() == "scripts":
                candidate = os.path.dirname(current_dir)
                if self._is_valid_dcs_saved_games_dir(candidate):
                    return candidate
            parent_dir = os.path.dirname(current_dir)
            if parent_dir == current_dir:
                return ""
            current_dir = parent_dir

    def _saved_games_candidates(self) -> list:
        """Every valid DCS-prefixed folder under the user's Saved Games folder."""
        userprofile = os.environ.get("USERPROFILE") or os.path.expanduser("~")
        saved_games_root = os.path.join(userprofile, "Saved Games")
        if not os.path.isdir(saved_games_root):
            return []
        candidates = []
        for name in os.listdir(saved_games_root):
            folder = os.path.join(saved_games_root, name)
            if name.casefold().startswith("dcs") and self._is_valid_dcs_saved_games_dir(folder):
                candidates.append(os.path.abspath(folder))
        return candidates

    # ------------------------------------------------------------------
    # Control file and Export.lua hook
    # ------------------------------------------------------------------
    def _scan_interval(self) -> float:
        """The scan interval in seconds, kept between 0.2 and 60 (1 when the field is not a number)."""
        try:
            interval = float(self.interval_var.get())
        except (ValueError, tk.TclError):
            interval = 1.0
        return min(max(interval, 0.2), 60.0)

    def _ensure_control_file(self, state: str) -> None:
        """Write the control file that tells the DCS side whether logging is ON or OFF, with the capture options and interval."""
        enabled = state.strip().upper() == "ON"
        options = {key: var.get() for key, var in self.capture_vars.items()}
        text = build_control_text(enabled, self._scan_interval(), options)
        os.makedirs(os.path.dirname(self.control_path), exist_ok=True)
        # Write to a temporary file and swap it in so DCS never reads a
        # half-written control file.
        temp_path = self.control_path + ".tmp"
        with open(temp_path, "w", encoding="utf-8") as opened_file:
            opened_file.write(text)
        try:
            os.replace(temp_path, self.control_path)
        except OSError:
            # DCS may have the file open for reading; fall back to rewriting it.
            with open(self.control_path, "w", encoding="utf-8") as opened_file:
                opened_file.write(text)
            try:
                os.remove(temp_path)
            except OSError:
                pass
        self.logging_enabled = enabled

    def _on_capture_changed(self, _event=None) -> None:
        """Save the scan interval and rewrite the control file after a capture option changed."""
        save_setting = getattr(self.host, "save_editor_setting", None)
        if save_setting is not None:
            save_setting("scan_interval", self.interval_var.get())   # remembered between runs
        try:
            self._ensure_control_file("ON" if self.logging_enabled else "OFF")
        except OSError as error:
            self._set_status(f"Could not update control file: {error}")

    @staticmethod
    def _lua_string(value: str) -> str:
        """The text as a quoted Lua string literal."""
        escaped = (
            value.replace("\\", "\\\\")
            .replace('"', '\\"')
            .replace("\r", "\\r")
            .replace("\n", "\\n")
        )
        return f'"{escaped}"'

    def _export_hook_line(self) -> str:
        """The one pcall line for Export.lua that points DCS at this app's logger script."""
        logger_dir = self._lua_string(os.path.abspath(self.logger_dir))
        lua_path = self._lua_string(os.path.abspath(self.lua_export_path))
        return (
            "pcall(function() "
            f"HELIOS_ARGUMENT_LOGGER_DIR = {logger_dir}; "
            f"dofile({lua_path}); "
            "end,nil)"
        )

    def _read_export_lua_for_check(self):
        """(text of Export.lua or None when the file does not exist yet, True); (None, False)
        after telling the person that the file could not be read."""
        try:
            with open(self.export_lua_path, "r", encoding="utf-8", errors="replace") as export_file:
                return export_file.read(), True
        except FileNotFoundError:
            return None, True
        except OSError as read_error:
            self._set_status("Could not check Export.lua hook")
            messagebox.showerror(
                "Check Export Hook",
                f"Could not read the DCS Export.lua file:\n{self.export_lua_path}\n\n{read_error}",
            )
            return None, False

    def _export_hook_problem(self, export_text) -> str:
        """What is wrong with the logger hook in Export.lua (None text: the file does not exist)."""
        if export_text is None:
            return "The DCS Export.lua file does not exist yet."
        if self._export_hook_line() in export_text:
            return "The Helios Argument Logger hook is not the only one, or is not the last line of Export.lua."
        if any(is_logger_hook_line(line) for line in export_text.splitlines()):
            return "The existing Helios Argument Logger hook does not point to this app folder."
        return "The Helios Argument Logger hook is missing."

    def _check_export_hook_on_startup(self) -> None:
        """At start-up: offer to install or repair the Export.lua hook when it is not in place."""
        if self.export_lua_path is None:
            return
        export_text, could_read = self._read_export_lua_for_check()
        if not could_read:
            return
        if export_text is not None and self.export_hook_in_place(export_text):
            self._set_status("Export hook is installed")
            return
        should_install = messagebox.askyesno(
            "Helios Argument Logger Export Hook",
            f"{self._export_hook_problem(export_text)}\n\n"
            f"Install or repair the hook in:\n{self.export_lua_path}\n\n"
            "This updates only the logger hook and preserves other Export.lua lines. "
            "Install/Repair now?",
        )
        if should_install:
            self.install_export_hook(confirm_replacement=False)
        else:
            self._set_status("Export hook needs installation or repair (Logger > Set Export Hook)")

    @staticmethod
    def export_with_single_hook(content: str, hook_line: str) -> str:
        """Export.lua text with every Argument Logger hook line removed and the one hook_line as
        the last line (other lines, their order and the file's line ends are kept; blank lines
        left at the end are dropped)."""
        newline = "\r\n" if "\r\n" in content else "\n"
        kept = [line for line in content.splitlines() if not is_logger_hook_line(line)]
        while kept and not kept[-1].strip():
            kept.pop()
        return newline.join(kept + [hook_line]) + newline

    def export_hook_in_place(self, content: str) -> bool:
        """True when Export.lua already has exactly one logger hook, this one, as its last line."""
        return self.export_with_single_hook(content, self._export_hook_line()).strip() == content.strip() \
            and content.rstrip().splitlines()[-1:] == [self._export_hook_line()]

    def install_export_hook(self, confirm_replacement: bool = True) -> None:
        """Make the logger hook the only one, and the last line, of the DCS Export.lua file."""
        if self.export_lua_path is None:
            messagebox.showerror("Set Export Hook", self.saved_games_error or "DCS Saved Games folder not found.")
            return
        hook_line = self._export_hook_line()
        if not os.path.isfile(self.lua_export_path):
            messagebox.showerror(
                "Set Export Hook",
                f"Logger Lua exporter was not found:\n{self.lua_export_path}",
            )
            self._set_status("Logger Lua exporter missing")
            return

        try:
            os.makedirs(self.scripts_dir, exist_ok=True)

            if os.path.exists(self.export_lua_path):
                with open(self.export_lua_path, "r", encoding="utf-8", errors="replace") as opened_file:
                    content = opened_file.read()

                if self.export_hook_in_place(content):
                    self._set_status("Export hook already present")
                    self._append_raw_data("[GUI] Export hook already installed\n")
                    return

                # Exactly one hook line, and it is the last line of the file.
                content = self.export_with_single_hook(content, hook_line)
                self._set_status("Updated Export.lua hook")

                with open(self.export_lua_path, "w", encoding="utf-8") as opened_file:
                    opened_file.write(content)
            else:
                with open(self.export_lua_path, "w", encoding="utf-8") as opened_file:
                    opened_file.write(hook_line + "\n")

            self._set_status("Installed Export.lua hook")
            self._append_raw_data("[GUI] Installed Export.lua hook for ArgumentLogger_For_PythonGUI.lua\n")
            messagebox.showinfo("Set Export Hook", "Export.lua hook installed successfully.")
        except OSError as error:
            messagebox.showerror("Set Export Hook", f"Failed to update Export.lua:\n{error}")

    # ------------------------------------------------------------------
    # Filtering and row building
    # ------------------------------------------------------------------
    def _display_filter(self) -> str:
        """The text typed in the display-value filter."""
        return self.display_value_var.get().strip()

    def _min_change(self) -> Optional[float]:
        """The smallest numeric change to show, or None for no limit."""
        return parse_min_change(self.min_change_var.get())

    def _schedule_filter(self, _event=None) -> None:
        # Wait for a pause in typing before redrawing every table.
        """Redraw the tables once typing in a filter has paused for a moment."""
        if self._filter_job is not None:
            self.host.after_cancel(self._filter_job)
        self._filter_job = self.host.after(250, self._apply_filters)

    def _apply_filters(self) -> None:
        """Redraw every table with the current filters."""
        self._filter_job = None
        self._render_all_views()

    def _references(self, line_type: str, parameter: str) -> list:
        """The (name, device, command) references of a parameter; one blank reference when it has none."""
        if line_type in ARGUMENT_TYPES:
            return self.reference.get(parameter) or [("", "", "")]
        return [("", "", "")]

    @staticmethod
    def _meta(key) -> tuple:
        """(type, parameter) for a row key."""
        if key[0] == "indication":
            return ("indication", key[2])
        return key

    def _all_views(self):
        """(mode, sub tab key, view) for every data table."""
        for key, view in self.tracker_views.items():
            yield "tracker", key, view

    def _view_keys(self, view_key: str) -> list:
        """The parameters a sub tab lists: every one seen, plus, for Cockpit
        Arguments, every argument in the reference table, so rows without
        data are still shown."""
        keys = [key for key in self.live_state if view_key == "all" or key[0] == view_key]
        if view_key == "argument":
            seen = set(keys)
            keys.extend(("argument", arg) for arg in self.reference if ("argument", arg) not in seen)
        return keys

    def _rows_for_key(self, key, view_key: str, mode: str) -> list:
        """All rows one parameter has in one sub tab, visible or not."""
        change = (self.tracker_state if mode == "tracker" else self.live_state).get(key)
        line_type = key[0]
        meta = self._meta(key)
        if view_key in ARGUMENT_TYPES:
            return self._argument_rows_for_key(key, change, meta)
        if view_key == "indication":
            values = tuple(change.extra) if change else (key[1], key[2], "", "", "")
            return [LoggerRow(values, meta, (key, 0))]
        if change is not None:
            values = (
                TYPE_NAMES.get(line_type, line_type),
                change.item,
                change.previous,
                change.current,
                change.delta_text,
            )
        else:
            item = f"Indication {key[1]}: {key[2]}" if line_type == "indication" else key[1]
            values = (TYPE_NAMES.get(line_type, line_type), item, "", "", "")
        orange = line_type != "indication" and self._status_visible(line_type, key[1])[1]
        return [LoggerRow(values, meta, (key, 0), ("orange_row",) if orange else ())]

    def _argument_rows_for_key(self, key, change, meta) -> list:
        """One row per Reference entry of an argument (name, device, command)."""
        line_type = key[0]
        current = change.current if change else ""
        difference = change.delta_text if change else ""
        rows = []
        for index, (name, device, command) in enumerate(self._references(line_type, key[1])):
            _shown, orange = self._status_visible(line_type, key[1], (name, device, command))
            rows.append(LoggerRow((key[1], name, device, command, current, difference), meta, (key, index),
                                  ("orange_row",) if orange else ()))
        return rows

    def _row_visible(self, row: LoggerRow, change: Optional[LoggerChange], mode: str) -> bool:
        """True when the row passes the minimum change, the file filter, 'not in the interface'
        and the text filter."""
        if mode == "tracker" and not change_passes_min(change, self._min_change()):
            return False
        if (self._file_filter() or self.not_in_interface_var.get()) and row.meta is not None:
            if not self._row_passes_status_filters(row):
                return False
        return text_matches(self._display_filter(), " ".join(str(value) for value in row.values))

    def _row_passes_status_filters(self, row: LoggerRow) -> bool:
        """The file filter and 'not in the interface' test for a row that has a parameter."""
        line_type, parameter = row.meta
        entry = None
        if line_type in ARGUMENT_TYPES and isinstance(row.key, tuple) and len(row.key) == 2 \
                and isinstance(row.key[1], int) and row.key[0][0] == line_type:
            entries = self._references(line_type, parameter)
            entry = entries[row.key[1]] if row.key[1] < len(entries) else None
        if line_type == "indication":
            return not self._file_filter()
        return bool(self._status_visible(line_type, parameter, entry)[0])

    def _render_view(self, mode: str, view_key: str, view: LoggerTable) -> None:
        """Refill one table with the rows of its keys that pass the filters."""
        state = self.tracker_state if mode == "tracker" else self.live_state
        rows = []
        for key in self._view_keys(view_key):
            change = state.get(key)
            rows.extend(row for row in self._rows_for_key(key, view_key, mode) if self._row_visible(row, change, mode))
        view.set_rows(rows)

    def _render_all_views(self) -> None:
        """Refill every table."""
        if not self.views_built:
            return
        for mode, view_key, view in self._all_views():
            self._render_view(mode, view_key, view)
        self._update_tracker_count()
        self._schedule_seen_notify()

    def _refresh_keys(self, keys) -> None:
        """Update the rows of these parameters where they are."""
        if not keys or not self.views_built:
            return
        self._report_new_keys(keys)
        for mode, view_key, view in self._all_views():
            state = self.tracker_state if mode == "tracker" else self.live_state
            for key in self._keys_shown_in_view(keys, view_key):
                self._refresh_key_in_view(key, mode, view_key, view, state.get(key))
        self._update_tracker_count()

    def _report_new_keys(self, keys) -> None:
        """Tell the editor about parameters seen for the first time."""
        new_keys = [key for key in keys if key not in self._reported_keys]
        if new_keys:
            self._reported_keys.update(new_keys)
            self._schedule_seen_notify()

    @staticmethod
    def _keys_shown_in_view(keys, view_key) -> list:
        """The keys a view shows: all of them in the "all" view, else those of its line type."""
        return [key for key in keys if view_key == "all" or key[0] == view_key]

    def _refresh_key_in_view(self, key, mode, view_key, view, change) -> None:
        """Show, update or remove the rows of one parameter in one view."""
        for row in self._rows_for_key(key, view_key, mode):
            if self._row_visible(row, change, mode):
                view.upsert(row)
            else:
                view.remove_key(row.key)

    def _visible_rows(self, rows) -> list:
        """The rows whose text matches the display-value filter."""
        filter_text = self._display_filter()
        return [row for row in rows if text_matches(filter_text, " ".join(str(cell_value) for cell_value in row.values))]

    def _update_tracker_count(self) -> None:
        """Show how many parameters have changed."""
        total = len(self.tracker_state)
        self.tracker_count_var.set("No changes yet" if total == 0 else f"{total} parameters changed")

    @staticmethod
    def _selected_subtab(notebook, keys) -> str:
        """The key of the sub tab selected in a notebook."""
        try:
            return keys[notebook.index(notebook.select())]
        except (tk.TclError, TypeError, IndexError):
            return keys[0]

    def _active_view(self) -> Optional[LoggerTable]:
        """The table on screen: the selected sub tab of the Aircraft Data tab."""
        if not self.views_built:
            return None
        return self.tracker_views[self._selected_subtab(self.tracker_notebook, self.tracker_subtab_keys)]

    # ------------------------------------------------------------------
    # Incoming log data
    # ------------------------------------------------------------------
    def _append_raw_data(self, text: str) -> None:
        """Take in newly logged text: feed it to the change tracker, then show what changed."""
        if not text:
            return
        new_changes, new_markers = self._feed_log_lines(text)
        records = self.tracker.take_live_records()
        if self.tracker.scan:
            self.scan_var.set(f"Scan: {self.tracker.scan}")

        affected = set()
        for record in records:
            self.live_state[record.row_key] = record
            affected.add(record.row_key)
        active_changes = []
        for change in new_changes:
            self.tracker_state[change.row_key] = change
            affected.add(change.row_key)
            active_changes.append(change)

        self._refresh_keys(affected)
        self._add_markers(new_markers)
        self._add_activity(active_changes)

    def _feed_log_lines(self, text: str):
        """Feed each line of logged text to the tracker.  Returns (changes found, marker rows
        for GUI and other messages)."""
        new_changes = []
        new_markers = []
        for line in text.splitlines(keepends=True):
            if line.startswith(("ARG BASE: ", "DRAW BASE: ")):
                self.tracker.feed(line)   # starting values
                continue
            line_type, self.in_indication_block = classify_line(line, self.in_indication_block)
            if line_type in NUMERIC_LINE_TYPES:
                line = strip_negative_zero(line)
            message = line.strip()
            if line_type == "gui":
                new_markers.append(LoggerRow((message[len("[GUI]"):].strip(),)))
                continue
            if line_type == "other" and message and not message.startswith(("=== Scan ===", "=   ")):
                new_markers.append(LoggerRow((message,)))
            new_changes.extend(self.tracker.feed(line))
        return new_changes, new_markers

    def _add_markers(self, markers) -> None:
        """Keep scan markers (limited to MAX_MARKER_ROWS, oldest dropped first)."""
        if not markers:
            return
        self.markers.extend(markers)             # kept (capped) for the change log
        if len(self.markers) > MAX_MARKER_ROWS:
            del self.markers[: len(self.markers) - MAX_MARKER_ROWS // 2]

    def _set_status(self, text: str) -> None:
        """Show a status message."""
        self.status_var.set(f"Status: {text}")

    def _set_poll_status(self, text: str) -> None:
        # The log is polled twice a second; only a change of state is shown,
        # so messages from buttons and menus stay visible.
        """Show a status message from the log poll, only when it differs from the last one."""
        if text != self._last_poll_status:
            self._last_poll_status = text
            self._set_status(text)

    def start_logging(self) -> None:
        """Tell the DCS side to start logging."""
        try:
            self._ensure_control_file("ON")
            self._set_status("Logging enabled (control=ON)")
            self._append_raw_data("\n[GUI] Logging enabled\n")
        except OSError as error:
            messagebox.showerror("Start Logging", f"Failed to write control file:\n{error}")

    def stop_logging(self) -> None:
        """Tell the DCS side to pause logging."""
        try:
            self._ensure_control_file("OFF")
            self._set_status("Logging paused (control=OFF)")
            self._append_raw_data("\n[GUI] Logging paused\n")
        except OSError as error:
            messagebox.showerror("Stop Logging", f"Failed to write control file:\n{error}")

    def reset_all(self) -> None:
        """Profile > Reset: forget everything this tab holds - the followed log, every value
        and row, the Reference rows it was given, the grouping windows
        and the file filter.  Logs written before now are not picked up again."""
        try:
            self._ensure_control_file("OFF")
        except OSError:
            pass
        self._forget_followed_log()
        self._forget_logged_values()
        self.file_filter_var.set(ALL_FILES_OPTION)
        self.not_in_interface_var.set(False)
        self.display_value_var.set("")
        self.min_change_var.set("")
        self._reported_keys = set()
        self._reference_signature = None
        self.use_reference_rows([], None, [])
        self.log_path_var.set("Log: waiting for session")
        self.scan_var.set("Scan: —")
        self.logging_button_var.set("Start Logging")
        self._render_all_views()
        self._set_status("Reset: waiting for log file")

    def _forget_followed_log(self) -> None:
        """Close the followed log file and start waiting for a new session."""
        if self.tail_fp is not None:
            try:
                self.tail_fp.close()
            except OSError:
                pass
        self.tail_fp = None
        self.tail_offset = 0
        self.pending_fragment = ""
        self.in_indication_block = False
        self.log_path = None
        self._reset_time = time.time()
        self._detected_vehicle = None
        self._locked_aircraft = None
        self._addendum_pending = False
        self._addendum_result = None

    def _forget_logged_values(self) -> None:
        """Empty every value, row and grouping this tab holds."""
        self.tracker.reset()
        self.live_state, self.tracker_state, self.markers = {}, {}, []
        self.activity_changes = {}
        self.grouped_keys, self.grouped_removed = [], set()
        self._close_activity_window()
        self._close_grouped_window()

    def clear_view(self) -> None:
        # Clears the recorded changes and markers.  Every parameter keeps its
        # row and latest value: values that do not change are only logged
        # once, so they could not be shown again.
        """Forget the recorded changes and markers; every parameter keeps its row and latest value."""
        self.tracker_state = {}
        self.markers = []
        self._render_all_views()

    def _reset_session_views(self) -> None:
        """A new log is a new session, possibly a new aircraft."""
        self.live_state = {}
        self.tracker_state = {}
        self._render_all_views()

    # ------------------------------------------------------------------
    # Grouping
    # ------------------------------------------------------------------
    def start_grouping(self) -> None:
        """Open the Activity and Grouped Commands windows and place them."""
        if self.activity_window is None:
            self._open_activity_window()
        if self.grouped_window is None:
            self._open_grouped_window()
        self._place_grouping_windows()

    def _place_grouping_windows(self) -> None:
        """Stack Activity above Grouped Commands, centred on the panel they were opened from."""
        width, top_height, bottom_height = 900, 420, 320
        title_bar_gap = 40   # room for the lower window's title bar
        anchor = self._grouping_anchor()
        try:
            self.host.update_idletasks()
            centre_x = anchor.winfo_rootx() + anchor.winfo_width() // 2
            centre_y = anchor.winfo_rooty() + anchor.winfo_height() // 2
            screen_width = self.host.winfo_screenwidth()
            screen_height = self.host.winfo_screenheight()
        except (tk.TclError, TypeError):
            return
        total_height = top_height + title_bar_gap + bottom_height
        x = max(0, min(centre_x - width // 2, screen_width - width))
        y = max(0, min(centre_y - total_height // 2, screen_height - total_height))
        placements = (
            (self.activity_window, f"{width}x{top_height}+{x}+{y}"),
            (self.grouped_window, f"{width}x{bottom_height}+{x}+{y + top_height + title_bar_gap}"),
        )
        for window, geometry in placements:
            # Hidden while it is moved: some window managers ignore a new
            # position given to a window that is already showing.
            window.withdraw()
            window.geometry(geometry)
            window.deiconify()
            window.lift()

    def _open_activity_window(self) -> None:
        """Build the Activity window (changes per parameter, with a threshold)."""
        window = tk.Toplevel(self.host)
        window.configure(bg=PANEL_BG)
        window.title("Activity")
        header = ttk.Frame(window, padding=8)
        header.pack(side=tk.TOP, fill=tk.X)
        ttk.Label(header, text="Threshold:").pack(side=tk.LEFT)
        self.activity_threshold_var = tk.StringVar()
        threshold_entry = ttk.Entry(header, textvariable=self.activity_threshold_var, width=10)
        threshold_entry.pack(side=tk.LEFT, padx=(6, 0))
        threshold_entry.bind("<KeyRelease>", lambda _event: self._render_activity())
        ttk.Label(header, text="File Filter:").pack(side=tk.LEFT, padx=(16, 0))
        FileFilterBox(header, self.file_filter_var, lambda: self.file_names,
                      self._on_file_filter_changed, width=24).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Checkbutton(header, text="Only values not in the interface", variable=self.not_in_interface_var,
                        command=self._on_file_filter_changed).pack(side=tk.LEFT, padx=(12, 0))
        footer = ttk.Frame(window, padding=8)
        footer.pack(side=tk.BOTTOM, fill=tk.X)
        ttk.Button(footer, text="Add to Group", command=self.add_to_group).pack(side=tk.LEFT)
        body = ttk.Frame(window, padding=(8, 0, 8, 0))
        body.pack(fill=tk.BOTH, expand=True)
        self.activity_view = LoggerTable(body, ACTIVITY_COLUMNS, default_sort="parameter")
        self.activity_changes = {}   # activity is collected from now on
        self.activity_window = window
        window.protocol("WM_DELETE_WINDOW", self._close_activity_window)

    def _close_activity_window(self) -> None:
        """Close the Activity window and forget its changes."""
        if self.activity_window is not None:
            self.activity_window.destroy()
        self.activity_window = None
        self.activity_view = None
        self.activity_changes = {}

    def _activity_row(self, key) -> Optional[LoggerRow]:
        """The latest change of this parameter that meets the threshold."""
        threshold = parse_min_change(self.activity_threshold_var.get())
        shown, orange = self._status_visible(key[0], key[1])
        if not shown:
            return None
        for change in reversed(self.activity_changes.get(key, [])):
            # A change without a numeric difference is never hidden by the threshold.
            if threshold is None or change.delta is None or round(abs(change.delta), 9) >= threshold:
                values = (
                    TYPE_NAMES.get(change.line_type, change.line_type),
                    change.parameter,
                    self._parameter_name(change.line_type, change.parameter),
                    change.current,
                    change.previous,
                    change.delta_text,
                )
                return LoggerRow(values, key, key, ("orange_row",) if orange else ())
        return None

    def _render_activity(self) -> None:
        """Refill the Activity window."""
        if self.activity_view is None:
            return
        rows = [self._activity_row(key) for key in self.activity_changes]
        self.activity_view.set_rows([row for row in rows if row is not None])

    def _add_activity(self, changes) -> None:
        """Add new changes to the Activity window's history of each parameter."""
        if self.activity_view is None or not changes:
            return
        touched = []
        for change in changes:
            history = self.activity_changes.setdefault(change.key, [])
            history.append(change)
            del history[:-MAX_ACTIVITY_PER_PARAMETER]
            if change.key not in touched:
                touched.append(change.key)
        for key in touched:
            row = self._activity_row(key)
            if row is None:
                self.activity_view.remove_key(key)
            else:
                self.activity_view.upsert(row)

    def add_to_group(self) -> None:
        """Add the parameters of the selected Activity rows to the Grouped Commands list."""
        metas = self.activity_view.selected_metas() if self.activity_view is not None else []
        if not metas:
            self._set_status("Select one or more rows in Activity, then click Add to Group")
            return
        added = 0
        for meta in metas:
            if meta not in self.grouped_keys:
                self.grouped_keys.append(meta)
                added += 1
            # Adding a parameter again brings back rows of it that were removed.
            self.grouped_removed = {key for key in self.grouped_removed if key[:2] != meta}
        if self.grouped_window is None:
            self._open_grouped_window()
        self._render_grouped()
        self._set_status(f"Added {added} to Grouped Commands")

    def _open_grouped_window(self) -> None:
        """Build the Grouped Commands window."""
        window = tk.Toplevel(self.host)
        window.configure(bg=PANEL_BG)
        window.title("Grouped Commands")
        footer = ttk.Frame(window, padding=8)
        footer.pack(side=tk.BOTTOM, fill=tk.X)
        if hasattr(self, "add_devices_from_group"):
            ttk.Button(footer, text="Add Device(s)", command=self.add_devices_from_group).pack(side=tk.LEFT)
        ttk.Button(footer, text="Remove", command=self.remove_grouped_selection).pack(
            side=tk.LEFT, padx=(8, 0) if hasattr(self, "add_devices_from_group") else 0)
        body = ttk.Frame(window, padding=(8, 8, 8, 0))
        body.pack(fill=tk.BOTH, expand=True)
        # Rows stay in the order they were added; this table is not sorted.
        self.grouped_view = LoggerTable(body, GROUPED_COLUMNS, sortable=False)
        self._configure_grouped_tags()
        self.grouped_window = window
        window.protocol("WM_DELETE_WINDOW", self._close_grouped_window)
        self._render_grouped()

    def _close_grouped_window(self) -> None:
        """Close the Grouped Commands window."""
        if self.grouped_window is not None:
            self.grouped_window.destroy()
        self.grouped_window = None
        self.grouped_view = None

    def _render_grouped(self) -> None:
        """Refill the Grouped Commands window."""
        if self.grouped_view is None:
            return
        self.grouped_view.set_rows(self._grouped_rows())

    def remove_grouped_selection(self) -> None:
        """Remove button: take the selected rows out of Grouped Commands.  A parameter
        whose rows are all removed leaves the group."""
        keys = self.grouped_view.selected_keys() if self.grouped_view is not None else []
        if not keys:
            self._set_status("Select one or more rows in Grouped Commands, then click Remove")
            return
        self.grouped_removed.update(keys)
        remaining = {row.meta for row in self._grouped_rows()}
        self.grouped_keys = [meta for meta in self.grouped_keys if meta in remaining]
        self.grouped_removed = {key for key in self.grouped_removed if key[:2] in self.grouped_keys}
        self._render_grouped()
        self._set_status(f"Removed {len(keys)} from Grouped Commands")

    # ------------------------------------------------------------------
    # Change log export
    # ------------------------------------------------------------------
    def _filter_summary(self, view_key: str) -> str:
        """Text describing the filters in force, for the change log header."""
        parts = [f"sub tab {dict(TRACKER_SUBTABS)[view_key]}"]
        text = self._display_filter()
        if text:
            parts.append(f'display value "{text}"')
        min_change = self._min_change()
        if min_change is not None:
            parts.append(f"min change >= {min_change:g}")
        return "; ".join(parts)

    def generate_change_log(self) -> None:
        """Write the rows shown in the selected Change Tracker sub tab, in the order shown."""
        view_key = self._selected_subtab(self.tracker_notebook, self.tracker_subtab_keys)
        view = self.tracker_views[view_key]
        rows = view.rows()
        if not rows:
            messagebox.showinfo(
                "Generate Change Log",
                "There are no changes to export with the current filters.",
            )
            return

        # Kept in a subfolder so the viewer does not mistake it for a DCS log.
        change_log_dir = os.path.join(self.log_dir, "ChangeLogs")
        source_name = os.path.basename(self.log_path) if self.log_path else "Session.log"
        base_name = os.path.splitext(source_name)[0]
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        path = os.path.join(change_log_dir, f"{base_name}_Changes_{stamp}.log")

        headings = view.headings
        table = [headings] + [[str(value) for value in row] for row in rows]
        widths = [min(max(len(row[i]) for row in table), 60) for i in range(len(headings))]

        def format_row(values) -> str:
            """One row of the change log with its columns padded to their widths."""
            return "  ".join(value.ljust(width) for value, width in zip(values, widths)).rstrip()

        lines = [
            f"=== Change Log generated {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} ===",
            f"=== Source: {source_name} ===",
            f"=== Filters: {self._filter_summary(view_key)} ===",
            f"=== {len(rows)} rows ===",
            format_row(headings),
        ]
        lines.extend(format_row(row) for row in table[1:])

        try:
            os.makedirs(change_log_dir, exist_ok=True)
            with open(path, "w", encoding="utf-8") as opened_file:
                opened_file.write("\n".join(lines) + "\n")
        except OSError as error:
            messagebox.showerror("Generate Change Log", f"Failed to write the change log:\n{error}")
            return

        self.last_change_log_path = path
        self._set_status(f"Change log saved: {path}")
        messagebox.showinfo(
            "Generate Change Log",
            f"Saved {len(rows)} rows to:\n{path}",
        )

    # ------------------------------------------------------------------
    # Log file tailing
    # ------------------------------------------------------------------
    def open_log_folder(self) -> None:
        """Open the logger's log folder in the file explorer."""
        os.makedirs(self.log_dir, exist_ok=True)
        if hasattr(os, "startfile"):
            os.startfile(self.log_dir)

    def _open_tail_file(self) -> None:
        """Follow the newest log file: switch to a new log when one appears, and open it for
        reading (starting near its end when it is already large)."""
        log_files = glob.glob(os.path.join(self.log_dir, "*.log"))
        reset_time = getattr(self, "_reset_time", None)
        if reset_time is not None:          # Reset: only a log written since then
            log_files = [path for path in log_files if os.path.getmtime(path) >= reset_time]
        latest_log_path = max(log_files, key=os.path.getmtime) if log_files else None
        if latest_log_path != self.log_path:
            self._switch_to_log(latest_log_path)
        if not self.log_path:
            return
        current_size = os.path.getsize(self.log_path)
        if self.tail_fp is None:
            self.tail_fp = open(self.log_path, "r", encoding="utf-8", errors="replace")
            self.tail_offset = max(current_size - 60000, 0)
            self.tail_fp.seek(self.tail_offset)
            if self.tail_offset > 0:
                self.tail_fp.readline()  # skip the partial first line
                self._append_raw_data("[GUI] Showing last part of existing log...\n")

    def _switch_to_log(self, latest_log_path) -> None:
        """Start following a different log: a new log is a new session (possibly a new aircraft)."""
        if self.tail_fp is not None:
            self.tail_fp.close()
            self.tail_fp = None
        self.log_path = latest_log_path
        self.tail_offset = 0
        self.one_shot_scan_pending = ""
        self.pending_fragment = ""
        self.tracker.reset()
        self._reset_session_views()
        if self.log_path:
            self.log_path_var.set(f"Log: {self.log_path}")
            self._append_raw_data(f"\n[GUI] Following log: {os.path.basename(self.log_path)}\n")
        else:
            self.log_path_var.set("Log: waiting for session")

    def _poll_log(self) -> None:
        """Read new lines from the followed log and update the tables (runs twice a second)."""
        if not self.follow_log:
            return

        try:
            self._open_tail_file()
            if self.tail_fp is not None:
                data = self.pending_fragment + self.tail_fp.read()
                last_newline = data.rfind("\n")
                self.pending_fragment = data[last_newline + 1:]
                data = data[: last_newline + 1]
                if data:
                    self._append_raw_data(data)
                    self._set_poll_status("Reading log output")
                elif self.log_path and os.path.exists(self.log_path):
                    self._set_poll_status("Waiting for new log lines")
                else:
                    self._set_poll_status("Waiting for log file")
            else:
                self._set_poll_status("Waiting for log file")
        except OSError as error:
            self._set_poll_status(f"Log read error: {error}")

        self._check_table_addendum()      # a finished search is saved and shown
        self._check_running_aircraft()    # a new aircraft: check the reference table against it
        self.host.after(500, self._poll_log)

    # ------------------------------------------------------------------
    # Table addendum
    # ------------------------------------------------------------------
    @staticmethod
    def _has_arg_name(arg: str, references) -> bool:
        """True when a reference gives the Arg # a name other than the number itself."""
        return any(name.strip() and name.strip() != arg for name, _device, _command in references)

    @staticmethod
    def _arg_origin(arg, cockpit_args, draw_args) -> str:
        """"both", "cockpit" or "draw": which kinds of logged argument carry this Arg #."""
        if arg in cockpit_args and arg in draw_args:
            return "both"
        return "cockpit" if arg in cockpit_args else "draw"

    def _unnamed_args(self) -> dict:
        """Arg #s DCS is passing (logged as cockpit or draw arguments) whose number has no Arg
        Name in the reference table: {arg text: "cockpit" / "draw" / "both"}.  Arguments that
        are only in the table, with nothing received for them, are not searched for."""
        cockpit_args = {key[1] for key in self.live_state if key[0] == "argument"}
        draw_args = {key[1] for key in self.live_state if key[0] == "draw"}
        return {arg: self._arg_origin(arg, cockpit_args, draw_args) for arg in cockpit_args | draw_args
                if not self._has_arg_name(arg, self.reference.get(arg, []))}

    def on_reference_loaded(self, table_aircraft=None) -> None:
        """Tables > Reference was loaded or generated by the user: the parser looks once for
        the names of the arguments DCS is passing that the table leaves unnamed (as soon as
        the aircraft being flown is known)."""
        self._addendum_pending = True
        self._addendum_table_aircraft = table_aircraft
        self._start_table_addendum()

    def _start_table_addendum(self) -> None:
        """Start looking up the names of unnamed arguments in the flown aircraft's files, in a background thread."""
        if not self._addendum_pending or not self.log_path or self._addendum_thread is not None:
            return
        vehicle_name = aircraft_from_log(self.log_path)
        if (self._addendum_table_aircraft
                and not same_aircraft(self._addendum_table_aircraft, self._aircraft_label(vehicle_name), vehicle_name)):
            return       # the table is for another aircraft: it waits until that aircraft is flown
        self._addendum_pending = False
        unnamed = self._unnamed_args()
        if not unnamed:
            return
        aircraft_folder = self._aircraft_folders.get(vehicle_name)
        if aircraft_folder is None:
            aircraft_folder = find_aircraft_module_folder(vehicle_name, dcs_aircraft_roots(self.saved_games_dir))
        if aircraft_folder is None:           # never asked for: the current reference data is used as it is
            self._set_status(f"Table addendum skipped: the {vehicle_name} aircraft folder was not found")
            return
        self._aircraft_folders[vehicle_name] = aircraft_folder
        self._set_status(f"Searching {chosen_folder_name(aircraft_folder) or vehicle_name} for "
                         f"{len(unnamed)} unnamed arguments...")
        # The Lua is parsed on a worker thread so the window stays responsive; the result is
        # picked up by the log poll (Tk is only ever used from the main thread).
        self._addendum_result = None

        def work():
            """Background thread: look up the unnamed arguments and store the outcome for the main thread."""
            try:
                rows, warnings = generate_arg_addendum(aircraft_folder, unnamed)
                self._addendum_result = ("done", aircraft_folder, unnamed, rows, warnings)
            except Exception as error:                  # reported in the main thread
                self._addendum_result = ("error", aircraft_folder, unnamed, error, [])

        self._addendum_thread = threading.Thread(target=work, name="table-addendum", daemon=True)
        self._addendum_thread.start()

    def _check_table_addendum(self) -> None:
        """Called by the log poll: finish a search that has completed."""
        result = self._addendum_result
        if result is None:
            return
        self._addendum_result = None
        self._addendum_thread = None
        outcome, aircraft_folder, unnamed, payload, warnings = result
        if outcome == "error":
            self._set_status("Table addendum failed")
            messagebox.showerror("Table Addendum", f"Could not search {aircraft_folder}:\n\n{payload}",
                                 parent=self.host)
        else:
            self._save_table_addendum(aircraft_folder, unnamed, payload, warnings)
        self._start_table_addendum()                    # a table loaded meanwhile is searched next

    def _save_table_addendum(self, aircraft_folder, unnamed, rows, warnings) -> None:
        """A search finished: the names found go into Tables > Reference (by Arg #), and the
        Table Addendum file records only the arguments no name was found for."""
        vehicle_name = aircraft_from_log(self.log_path)
        found_args = {row["Arg #"] for row in rows}
        apply_names = getattr(self.host, "apply_found_arg_names", None)
        updated, added = apply_names(rows, unnamed) if apply_names is not None and rows else (0, 0)

        # The addendum: every argument searched for this aircraft that is still unnamed.  Each
        # search only covers the arguments DCS had passed by then, so the list builds up.
        searched = set(unnamed)
        kind_notes = {"cockpit": "Cockpit argument", "draw": "Draw argument", "both": "Cockpit and draw argument"}
        kinds = dict(unnamed)
        not_found_rows = []
        for arg in sorted(searched - found_args, key=natural_key):
            name, device, command = (self.reference.get(arg) or [("", "", "")])[0]
            not_found_rows.append({
                "Type": "", "Arg #": arg, "Arg Name": "",
                "Note": f"{kind_notes.get(kinds.get(arg), 'Argument')}; no name found",
                "Device": device, "Device #": "", "Command": command, "Command #": "",
            })
        label = chosen_folder_name(aircraft_folder) or vehicle_name
        folder = os.path.join(self.logger_dir, TABLE_UPDATES_FOLDER_NAME)
        path = os.path.join(folder, table_addendum_file_name(label))
        contents = {
            "aircraft": label,
            "aircraft_folder": aircraft_folder,
            "reference_table": self.reference_path or "",
            "generated": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "table": not_found_rows,
        }
        try:
            os.makedirs(folder, exist_ok=True)
            with open(path, "w", encoding="utf-8") as json_file:
                json.dump(contents, json_file, indent=4, ensure_ascii=False)
        except OSError as error:
            messagebox.showerror("Table Addendum", f"Could not save:\n{path}\n\n{error}", parent=self.host)
            return
        message = (f"Names found for {len(rows)} of {len(unnamed)} unnamed arguments: Reference table "
                   f"updated ({updated} rows named, {added} rows added); "
                   f"{len(not_found_rows)} still unnamed in {os.path.basename(path)}")
        self._set_status(message)
        self._add_markers([LoggerRow((f"{message}: {path}",))])
        if warnings:
            self._add_markers([LoggerRow((f"Table addendum: {len(warnings)} Lua warnings while searching",))])

    def use_reference_rows(self, table_rows, source_path=None, source_rows=None) -> None:
        """Take over the rows of Tables > Reference ([{column: text}]); the editor calls this
        whenever that table changes (Generate, Load, an edit, Close).  Nothing is redrawn when
        the rows are the same as last time."""
        signature = (tuple(tuple(row.get(column, "") for column in TABLE_COLUMNS) for row in table_rows),
                     tuple(str(row.get("File Name", "")) for row in (source_rows or ())))
        if signature == self._reference_signature:
            return
        self._reference_signature = signature
        self.reference = reference_from_rows(table_rows)
        self.reference_path = source_path
        self._index_reference_rows(table_rows)
        self._index_source_files(table_rows, source_rows or ())
        self.reference_var.set(self._reference_summary_text(source_path))
        self._render_all_views()
        self._render_grouped()
        self._render_activity()

    def _reference_summary_text(self, source_path) -> str:
        """The "Reference: ..." line telling where the reference rows come from and how many."""
        if not self.reference:
            return "Reference: Tables > Reference is empty"
        entry_count = sum(len(matches) for matches in self.reference.values())
        source_prefix = f"{os.path.basename(source_path)}, " if source_path else ""
        return (f"Reference: Tables > Reference ({source_prefix}{entry_count} entries, "
                f"{len(self.reference)} arguments)")

    @staticmethod
    def _source_key(row) -> tuple:
        """The (Arg Name, Device, Command, Command #) texts that tie a Source tab row to a Reference row."""
        return tuple(str(row.get(column) or "").strip() for column in ("Arg Name", "Device", "Command", "Command #"))

    def _index_source_files(self, table_rows, source_rows) -> None:
        """Which source files each Reference row came from: the Source tab of the last Generate
        (matched on Arg Name, Device, Command and Command #) and the "found in" file of a row
        the table addendum added.  File names only; paths are never kept here."""
        shown_names = {}                             # lower-case -> shown name
        row_ids_by_file = {}
        rows_by_key = {}
        for row in table_rows:
            rows_by_key.setdefault(self._source_key(row), []).append(row)
        for source_row in source_rows:
            source_paths = self._source_row_paths(source_row)
            for row in self._table_rows_of_source_row(rows_by_key, source_row):
                for path in source_paths:
                    self._remember_source_file(shown_names, row_ids_by_file, path, row)
        self._index_found_in_notes(table_rows, shown_names, row_ids_by_file)
        self.file_names = sorted(shown_names.values(), key=str.lower)
        self.file_ref_ids = row_ids_by_file
        self._reset_unknown_file_filter()
        self.file_hint_var.set("" if self.file_names else
                               "(no source files known: Generate the Reference table to list them)")

    def _index_found_in_notes(self, table_rows, shown_names, row_ids_by_file) -> None:
        """Rows the table addendum added say in their Note which file they were "found in"."""
        for row in table_rows:
            found_in = re.search(r"found in (.+)$", str(row.get("Note") or ""))
            if found_in:
                self._remember_source_file(shown_names, row_ids_by_file, found_in.group(1).strip(), row)

    def _reset_unknown_file_filter(self) -> None:
        """Back to "all files" when the chosen file filter names a file no row came from."""
        chosen_file = self.file_filter_var.get().strip().lower()
        if chosen_file and chosen_file not in self.file_ref_ids:
            self.file_filter_var.set(ALL_FILES_OPTION)

    @staticmethod
    def _remember_source_file(names, ids, path_text, row) -> None:
        """Note that row came from the file at path_text (only its name is kept)."""
        base = os.path.basename(str(path_text).replace("\\", "/").rstrip("/"))
        if base:
            names.setdefault(base.lower(), base)
            ids.setdefault(base.lower(), set()).add(id(row))

    @staticmethod
    def _source_row_paths(source_row) -> list:
        """The source file paths (or names) a Source tab row lists."""
        paths = list(source_row.get(SOURCE_FILE_PATHS_KEY) or [])
        if not paths:
            paths = [name for name in str(source_row.get("File Name", "")).split(SOURCE_LIST_SEPARATOR) if name]
        return paths

    def _table_rows_of_source_row(self, rows_by_key, source_row) -> list:
        """The Reference rows a Source tab row belongs to (same key and, when it has one, Arg #)."""
        candidates = rows_by_key.get(self._source_key(source_row), [])
        source_arg = normalize_id_text(source_row.get("Arg #"))
        if source_arg:
            candidates = [row for row in candidates if normalize_id_text(row.get("Arg #")) == source_arg]
        return candidates

    # ------------------------------------------------------------------
    # File filter, "not in the interface" and the orange rows
    # ------------------------------------------------------------------
    def _file_filter(self) -> str:
        """The lower-case file name chosen in File Filter, or "" (partial text filters nothing)."""
        text = self.file_filter_var.get().strip().lower()
        return text if text in self.file_ref_ids else ""

    def _on_file_filter_changed(self) -> None:
        """Redraw the tables after the file filter changed."""
        self._render_all_views()
        self._render_activity()

    def _row_status(self, line_type, parameter, entry=None):
        """(Reference rows, held by the interface, orange) for one logged value.  The Reference
        rows are those of the argument / command (just the row of `entry` when it is given);
        the value is "held" when a device of the interface holds the ids of one of them (or,
        without Reference rows, its own Arg # / Device # / Command #); it is orange when it has
        Reference rows with ids and none is held."""
        rows = []
        if entry is not None and line_type in ARGUMENT_TYPES:
            rows = list(self.reference_entry_rows.get((_normalise_arg(parameter), tuple(entry)), []))
        if not rows:
            rows = self._reference_rows_for(line_type, parameter)
        match_keys = self._interface_match_keys()
        row_keys = self._match_keys_of_rows(rows)
        if row_keys:
            is_held = any(row_key in match_keys for row_key in row_keys)
            return rows, is_held, not is_held
        own_ids = None if rows else self._own_ids_of_parameter(line_type, parameter)
        if own_ids is None:
            return rows, False, False
        own_key = table_row_match_key(*own_ids)
        return rows, own_key is not None and own_key in match_keys, False

    @staticmethod
    def _match_keys_of_rows(rows) -> list:
        """The match keys of the Reference rows that have ids (rows without any are left out)."""
        row_keys = (table_row_match_key(row.get("Arg #"), row.get("Device #"), row.get("Command #"))
                    for row in rows)
        return [row_key for row_key in row_keys if row_key is not None]

    def _own_ids_of_parameter(self, line_type, parameter):
        """(Arg #, Device #, Command #) a logged value stands for on its own, or None."""
        if line_type in ARGUMENT_TYPES:
            return (parameter, "", "")
        if line_type == "command" and self._command_ids(parameter):
            return ("",) + self._command_ids(parameter)
        return None

    def _status_visible(self, line_type, parameter, entry=None):
        """(shown, orange) after File Filter and "Only values not in the interface"."""
        rows, held, orange = self._row_status(line_type, parameter, entry)
        file_name = self._file_filter()
        if file_name:
            wanted = self.file_ref_ids.get(file_name, ())
            if not any(id(row) in wanted for row in rows):
                return False, orange
        if self.not_in_interface_var.get() and held:
            return False, orange
        return True, orange

    def seen_ids(self):
        """(Arg #s, (Device #, Command #) pairs) of every value the logger has seen, for the
        orange rows of the Reference table."""
        args, commands = set(), set()
        for state in (self.live_state, self.tracker_state):
            for key in state:
                line_type, parameter = key[0], key[1]
                if line_type in ARGUMENT_TYPES:
                    args.add(normalize_id_text(parameter))
                elif line_type == "command" and self._command_ids(parameter):
                    commands.add(self._command_ids(parameter))
        args.discard("")
        return args, commands

    def refresh_interface_state(self) -> None:
        """The interface changed: redraw the logger's rows (their orange colour)."""
        if self.views_built:
            self._render_all_views()
        self._render_activity()

    def _schedule_seen_notify(self) -> None:
        """Tell the editor shortly (once) that the set of seen parameters changed."""
        if self._seen_job is None:
            try:
                self._seen_job = self.host.after(1500, self._notify_seen)
            except tk.TclError:
                self._seen_job = None

    def _notify_seen(self) -> None:
        """Ask the editor to refresh the Reference table highlights."""
        self._seen_job = None
        callback = getattr(self.host, "refresh_reference_highlight", None)
        if callback is not None:
            callback()

    # ------------------------------------------------------------------
    # The aircraft being flown
    # ------------------------------------------------------------------
    def _aircraft_folder_for(self, vehicle_name):
        """The aircraft folder of a vehicle (remembered, else found from entry.lua); None
        when it is not found."""
        folder = self._aircraft_folders.get(vehicle_name)
        if folder is None:
            folder = find_aircraft_module_folder(vehicle_name, dcs_aircraft_roots(self.saved_games_dir))
            if folder is not None:
                self._aircraft_folders[vehicle_name] = folder
        return folder

    def _aircraft_label(self, vehicle_name):
        """'FA-18C_hornet' -> 'FA-18C' (its aircraft folder's name), else the vehicle name."""
        folder = self._aircraft_folder_for(vehicle_name)
        return chosen_folder_name(folder) if folder else vehicle_name

    def _check_running_aircraft(self) -> None:
        """Called by the log poll once log lines arrive.  When DCS is writing a log for an
        aircraft the logger has not seen yet in this session, the reference table is checked
        against it (see _on_aircraft_detected).  A log left from an earlier session does not
        count until DCS writes to it again."""
        if not self.log_path or self._aircraft_check_busy:
            return
        try:
            if os.path.getmtime(self.log_path) < self._session_start:
                return
        except OSError:
            return
        vehicle_name = aircraft_from_log(self.log_path)
        if vehicle_name == self._detected_vehicle:
            return
        self._detected_vehicle = vehicle_name
        self._aircraft_check_busy = True
        try:
            self._on_aircraft_detected(vehicle_name)
        finally:
            self._aircraft_check_busy = False

    def _on_aircraft_detected(self, vehicle_name) -> None:
        """A new aircraft is being flown.  The logger never asks for an aircraft file or folder:
        it works with the reference data that is loaded (Reference Data > Current Data).  When a
        table is loaded and still waiting, the names of the arguments it leaves unnamed are looked
        for (on_reference_loaded), when the aircraft's folder is found by itself."""
        info = getattr(self.host, "current_reference_info", None)
        has_table = info()[0] if info is not None else bool(self.reference)
        if has_table:
            self._start_table_addendum()      # the reference data already loaded is used as it is

    def _generate_reference(self, aircraft_folder, vehicle_name) -> None:
        """Generate Tables > Reference from the aircraft folder (as Table > Generate does)."""
        generate = getattr(self.host, "generate_reference_for_logger", None)
        if generate is None:
            return
        self._aircraft_folders[vehicle_name] = aircraft_folder
        if generate(aircraft_folder):
            # The generated table covers the whole aircraft: no name search is needed, and a
            # table of another aircraft can no longer be loaded while this one is flown.
            self._addendum_pending = False
            self._locked_aircraft = (chosen_folder_name(aircraft_folder), vehicle_name)

    def reference_load_allowed(self, table_aircraft) -> bool:
        """Asked before a table is loaded into Tables > Reference: once the logger generated the
        table for the aircraft being flown, a table of another aircraft is refused (and the
        current table kept).  A table whose aircraft cannot be told is allowed."""
        if not self._locked_aircraft or not table_aircraft:
            return True
        locked_label, vehicle_name = self._locked_aircraft
        if same_aircraft(table_aircraft, locked_label, vehicle_name):
            return True
        messagebox.showerror(
            "Load Reference Table",
            f"This reference table is for {table_aircraft}, but {locked_label} is being flown.\n\n"
            "The table was not loaded; the current table is kept.", parent=self.host)
        return False

    def refresh_colors(self) -> None:
        """The editor changed its colour scheme: recolour the logger's open windows (the tab
        itself is redrawn by build_ui)."""
        for window in (self.activity_window, self.grouped_window):
            if window is not None:
                try:
                    window.configure(bg=PANEL_BG)
                except tk.TclError:
                    pass

    # ------------------------------------------------------------------
    # Grouped Commands and the interface (Add Device(s), green rows)
    # ------------------------------------------------------------------
    _COMMAND_PARAMETER = re.compile(r"^(?:Dev\s+(\d+)\s+)?[A-Za-z_]\w*\(\s*([-+]?\d+(?:\.\d+)?)\s*\)$")

    def _index_reference_rows(self, table_rows) -> None:
        """Keep the Reference rows by Arg # and by (Device #, Command #), so a grouped
        parameter can be matched to its rows and to the devices of the interface."""
        self.reference_rows_by_arg = {}
        self.reference_rows_by_command = {}
        self.reference_entry_rows = {}
        for row in table_rows:
            raw_arg = str(row.get("Arg #") or "").strip()
            if raw_arg:
                entry = (str(row.get("Arg Name") or "").strip(),
                         _name_with_number(str(row.get("Device") or "").strip(), str(row.get("Device #") or "").strip()),
                         _name_with_number(str(row.get("Command") or "").strip(), str(row.get("Command #") or "").strip()))
                self.reference_entry_rows.setdefault((_normalise_arg(raw_arg), entry), []).append(row)
            arg = normalize_id_text(row.get("Arg #"))
            device = normalize_id_text(row.get("Device #"))
            command = normalize_id_text(row.get("Command #"))
            if arg:
                self.reference_rows_by_arg.setdefault(arg, []).append(row)
            if command:
                self.reference_rows_by_command.setdefault((device, command), []).append(row)
                self.reference_rows_by_command.setdefault(("", command), []).append(row)

    def _command_ids(self, parameter):
        """'Dev 023 performClickableAction(3001)' -> ('23', '3001'); 'LoSetCommand(71)' ->
        ('', '71'); None for anything else."""
        match = self._COMMAND_PARAMETER.match(str(parameter).strip())
        if not match:
            return None
        return normalize_id_text(match.group(1) or ""), normalize_id_text(match.group(2))

    def _reference_rows_for(self, line_type, parameter) -> list:
        """The Reference rows of a parameter: by Arg # for cockpit / draw arguments, by
        Device # and Command # for a command received."""
        if line_type in ARGUMENT_TYPES:
            return list(getattr(self, "reference_rows_by_arg", {}).get(normalize_id_text(parameter), []))
        if line_type == "command":
            ids = self._command_ids(parameter)
            if ids:
                return list(getattr(self, "reference_rows_by_command", {}).get(ids, []))
        return []

    def _parameter_name(self, line_type: str, parameter: str) -> str:
        """The Arg Name the reference table gives this parameter ("" when it has none)."""
        names = []
        for row in self._reference_rows_for(line_type, parameter):
            name = str(row.get("Arg Name") or "").strip()
            if name and name not in names:
                names.append(name)
        return " / ".join(names)

    def _interface_match_keys(self):
        """Every id combination held by a device of the interface (from the editor)."""
        match_keys = getattr(self.host, "table_added_match_keys", None)
        try:
            return match_keys() if match_keys else set()
        except Exception:
            return set()

    def _configure_grouped_tags(self) -> None:
        """Colour the rows already held by an interface device, using the theme's added-row colour."""
        theme_name = getattr(self.host, "_theme_name", "default")
        colour = ADDED_ROW_BACKGROUND.get(theme_name, ADDED_ROW_BACKGROUND.get("dark", "#1f4a2e"))
        self.grouped_view.tree.tag_configure("in_interface", background=colour)

    def _grouped_rows(self) -> list:
        """One row per Reference row of every grouped parameter (one plain row when it has
        none).  A row is green when its Arg # / Device # / Command # (whichever it has) are
        already held by a device in the interface."""
        match_keys = self._interface_match_keys()
        self.grouped_row_ids = {}       # row key -> (Arg #, Device #, Command #)
        rows = []
        for line_type, parameter in self.grouped_keys:
            for name, device, command, ids in self._grouped_entries(line_type, parameter):
                key = (line_type, parameter, name, device, command)
                if key in self.grouped_removed:
                    continue
                self.grouped_row_ids[key] = ids
                rows.append(self._grouped_row(key, ids, match_keys))
        return rows

    @staticmethod
    def _grouped_row(key, ids, match_keys) -> "LoggerRow":
        """The table row of one grouped entry; tagged "in_interface" when a device holds its ids."""
        line_type, parameter, name, device, command = key
        row_match_key = table_row_match_key(*ids) if any(ids) else None
        is_in_interface = row_match_key is not None and row_match_key in match_keys
        values = (TYPE_NAMES.get(line_type, line_type), parameter, name, device, command)
        return LoggerRow(values, (line_type, parameter), key, ("in_interface",) if is_in_interface else ())

    def _grouped_entries(self, line_type, parameter) -> list:
        """[(name, device, command, (Arg #, Device #, Command #))] for one grouped parameter: one
        per Reference row, or a single plain entry when it has none."""
        entries = []
        for row in self._reference_rows_for(line_type, parameter):
            ids = (normalize_id_text(row.get("Arg #")), normalize_id_text(row.get("Device #")),
                   normalize_id_text(row.get("Command #")))
            entries.append((
                str(row.get("Arg Name") or "").strip(),
                _name_with_number(str(row.get("Device") or "").strip(), ids[1]),
                _name_with_number(str(row.get("Command") or "").strip(), ids[2]),
                ids))
        if not entries:
            ids = self._ids_of_unlisted_parameter(line_type, parameter)
            entries.append(("", ids[1], ids[2], ids))
        return entries

    def _ids_of_unlisted_parameter(self, line_type, parameter) -> tuple:
        """(Arg #, Device #, Command #) of a parameter that has no Reference row."""
        if line_type in ARGUMENT_TYPES:
            return (normalize_id_text(parameter), "", "")
        if line_type == "command" and self._command_ids(parameter):
            return ("",) + self._command_ids(parameter)
        return ("", "", "")

    def add_devices_from_group(self) -> None:
        """Add Device(s): select the Reference rows of the chosen Grouped Commands rows (all
        rows when none is selected) in Tables > Reference and start Build Device on them."""
        if self.grouped_view is None:
            return
        keys = self.grouped_view.selected_keys() or self.grouped_view.keys()
        ids = [self.grouped_row_ids.get(key) for key in keys]
        ids = [row_ids for row_ids in ids if row_ids and any(row_ids)]
        if not ids:
            messagebox.showinfo("Add Device(s)", "There are no Grouped Commands rows with an Arg #, "
                                "Device # or Command # to build a device from.", parent=self.grouped_window)
            return
        build = getattr(self.host, "build_devices_for_logger", None)
        if build is None:
            return
        found = build(ids)
        if not found:
            messagebox.showinfo("Add Device(s)", "None of these rows are in the table in Tables > Reference, "
                                "so no device can be built from them.", parent=self.grouped_window)
            return
        self._render_grouped()


class HeliosEditor(TkinterDnD.Tk if TkinterDnD else tk.Tk):
    """Main window of the Helios Interface Editor: profile documents, tables, logger and text editor."""
    def __init__(self):
        """Build the main window: session state (open documents, undo history, clipboard, Table
        / Viewport tab state), theme and styles, menus, the document tab bar, header and
        tabs, then start with one empty profile."""
        super().__init__()
        self._last_saved_star_image = tk.PhotoImage(master=self, width=13, height=13)
        star_pixels = (
            "......#......",
            "......#......",
            ".....###.....",
            ".....###.....",
            "#############",
            ".###########.",
            "..#########..",
            "...#######...",
            "....#####....",
            "...##...##...",
            "..##.....##..",
            ".##.......##.",
            ".............",
        )
        for y, row in enumerate(star_pixels):
            for x, pixel in enumerate(row):
                if pixel == "#":
                    self._last_saved_star_image.put("#ffd24a", (x, y))
        # The colour scheme saved last time (Options > Color Scheme), applied before anything is built.
        self.editor_settings = load_editor_settings()
        saved_theme = self.editor_settings.get("color_scheme")
        self._saved_theme_name = saved_theme if saved_theme in THEMES else "default"
        apply_theme(THEMES[self._saved_theme_name])
        self.title("Helios Interface Editor")
        self._set_window_icon()
        self.configure(bg=DARK_BG)

        screen_width = self.winfo_screenwidth()
        screen_height = self.winfo_screenheight()
        startup_scale = 0.8  # Open 20% smaller than the previous default size.
        base_width = max(900, (screen_width * 33) // 80)
        base_height = max(700, (screen_height * 3) // 4)
        window_width = int(base_width * startup_scale)
        window_height = int(base_height * startup_scale)
        position_x = max(0, (screen_width - window_width) // 2)
        position_y = max(0, (screen_height - window_height) // 2)
        self.geometry(f"{window_width}x{window_height}+{position_x}+{position_y}")
        self.state("normal")

        self._data = {
            "source": "User", "version": "Initial", "commit": "", "type": "DCS",
            "name": "", "module": "", "vehicles": [], "functions": []
        }
        self._documents = []
        self._document_tab_bars = []
        self._active_document_index = 0
        self._clipboard_functions = []
        self._clipboard_type = None
        self._last_focused_tree_type = None
        self._undo_stack = []
        self._redo_stack = []
        self._current_file = None
        # Active save / Full View ordering: "deviceaction" or "devicename".
        self._sort_method = "devicename"
        # Remember the device of the most recently added entry so the next Add
        # dialog can pre-fill the same device name + id.
        self._last_added_device = ""
        self._last_added_device_id = ""
        self._last_added_function = None
        self._last_saved_function = None
        self._next_saved_session_index = 1
        self._next_created_session_index = 1
        self._trees = {}        # heliosType -> Treeview
        self._tab_count_labels = {}   # heliosType -> per-tab count Label
        self._sort_column_by_type = {}     # heliosType -> (col, reverse)
        self._theme_name = self._saved_theme_name
        # Options > Color Scheme's choice: one variable for the whole session (the menu is rebuilt
        # on every switch, the variable is not).
        self._theme_choice = tk.StringVar(master=self, value=self._theme_name)
        self._header_frame = None
        self._text_editor = None
        self._text_editor_frame = None
        self._text_editor_state = None
        self._pending_saved_editor_syncs = {}
        self._last_main_tab_label = None
        self._text_editor_menu_options = None
        # Baseline used to detect unsaved changes (set after the UI is built).
        self._clean_signature = None


        # Table tab: the panel, and its rows while the tabs are being rebuilt
        # (switching light / dark mode destroys and recreates every tab).
        self._command_table_panel = None
        self._command_table_state = None
        # Old References / Mismatched tabs (the old table's rows survive rebuilds the same way).
        self._old_reference_panel = None
        self._old_reference_state = None
        self._mismatched_panel = None
        self._reference_comparison_pending = False  # a comparison is queued for when the window is idle
        # Viewport tab: the calls found by Table ▸ Generate… (kept here so a tab
        # rebuild does not lose them).
        self._viewport_panel = None
        self._viewport_calls = []           # [(viewport text, file path)]
        self._source_panel = None
        self._source_rows = []              # Source tab rows of the last Generate
        self._source_file_variables = {}    # file path -> [(variable name, value text)] (Source tab)
        self._function_return_types = {}    # element function -> return classes (Build Device type)
        self._element_details = {}          # element name -> position count / step (Build Device)
        self._discovered_devices = {}       # device name -> device # text, from Generate (Build Device box)
        # Find results window (one at a time; replaced on every Find).
        self._find_all_window = None
        # Table tab "Added" check: keys of every id combination in the profile, built on
        # demand and thrown away whenever the profile changes (see _refresh_all).
        self._added_match_keys = None

        self._setup_styles()
        # The Argument Logger keeps its data for the whole session; its tab and Logger menu
        # are drawn by _build_tabs / _build_menu.
        self._logger_generating_reference = False   # set while the logger generates the table
        self._argument_logger = ArgumentLoggerPanel(self)
        self._build_menu()
        self._build_header()
        self._build_tabs()
        self._refresh_all()

        if DND_FILES is not None:
            self.drop_target_register(DND_FILES)
            self.dnd_bind("<<Drop>>", self._on_file_drop)

        # Closing the window (the X button) goes through the same unsaved-change
        # prompt as the application's close handler.
        self.protocol("WM_DELETE_WINDOW", self._on_exit)
        # The freshly-opened, empty profile is the initial clean baseline.
        self._mark_clean()
        self._documents.append(self._make_document_record(replace_on_open=True))
        self._render_document_tabs()

    def _build_document_tabs(self, parent):
        """Add a profile-tab strip below the toolbar in a JSON subtab."""
        tab_bar = tk.Frame(parent, bg=PANEL_BG, height=34)
        tab_bar.pack(fill="x", padx=8, pady=(0, 4))
        tab_bar.pack_propagate(False)
        self._document_tab_bars.append(tab_bar)

    def _make_document_record(self, data=None, current_file=None, clean_signature=None,
                              replace_on_open=False):
        """Snapshot of one document for the document tabs: its profile data, file path, saved-
        state signature, sort method, last added / saved functions, session counters and
        undo history. `replace_on_open` marks the clean automatic Untitled placeholder; explicit
        New documents are not marked for replacement."""
        return {
            "data": copy.deepcopy(self._data if data is None else data),
            "current_file": current_file,
            "clean_signature": (self._clean_signature if clean_signature is None
                                 else clean_signature),
            "sort_method": self._sort_method,
            "last_added_device": self._last_added_device,
            "last_added_device_id": self._last_added_device_id,
            "last_added_function": copy.deepcopy(self._last_added_function),
            "last_saved_function": copy.deepcopy(self._last_saved_function),
            "next_saved_session_index": self._next_saved_session_index,
            "next_created_session_index": self._next_created_session_index,
            "undo_stack": copy.deepcopy(self._undo_stack),
            "redo_stack": copy.deepcopy(self._redo_stack),
            "replace_on_open": replace_on_open,
        }

    def _capture_active_document(self):
        """Store the active document's current state into its record (called before switching,
        opening, creating or closing a document)."""
        if not self._documents:
            return
        self._sync_header_to_data()
        current_document = self._documents[self._active_document_index]
        self._documents[self._active_document_index] = self._make_document_record(
            current_file=self._current_file,
            replace_on_open=current_document.get("replace_on_open", False))

    def _is_replaceable_auto_untitled(self):
        """Whether the sole document is an untouched automatic Untitled placeholder."""
        if len(self._documents) != 1 or self._active_document_index != 0:
            return False
        document = self._documents[0]
        return (document.get("replace_on_open", False)
                and document.get("current_file") is None
                and not self._document_is_dirty(0))

    def _restore_document(self, index):
        """Make document `index` the active one: load its stored state into the editor and
        refresh every view."""
        document = self._documents[index]
        self._active_document_index = index
        self._data = copy.deepcopy(document["data"])
        self._current_file = document["current_file"]
        self._clean_signature = document["clean_signature"]
        self._sort_method = document["sort_method"]
        sort_var = getattr(self, "_sort_method_var", None)
        if sort_var is not None:
            sort_var.set(self._sort_method)
        self._last_added_device = document["last_added_device"]
        self._last_added_device_id = document["last_added_device_id"]
        self._last_added_function = copy.deepcopy(document["last_added_function"])
        self._last_saved_function = copy.deepcopy(document["last_saved_function"])
        self._next_saved_session_index = document["next_saved_session_index"]
        self._next_created_session_index = document["next_created_session_index"]
        self._undo_stack = copy.deepcopy(document.get("undo_stack", []))
        self._redo_stack = copy.deepcopy(document.get("redo_stack", []))
        self._sync_data_to_header()
        self._refresh_all()
        self._update_window_title()
        self._render_document_tabs()
        self._select_text_document_of_active_json()

    def _select_text_document_of_active_json(self):
        """The JSON Controls document now showing is also the one selected in the Text Editor: the
        Text Editor document with the same full path (so two files of the same name in different
        folders are told apart).  Nothing happens when that file is not open in the Text Editor."""
        text_editor = getattr(self, "_text_editor", None)
        if text_editor is None or getattr(self, "_syncing_selection", False) or not self._current_file:
            return
        path_key = self._sync_path_key(self._current_file)
        target = next((document for document in text_editor.documents
                       if self._sync_path_key(document.get("path")) == path_key), None)
        if target is None:
            return
        self._syncing_selection = True
        try:
            if text_editor.notebook.select() != str(target["frame"]):
                text_editor.notebook.select(target["frame"])
        except tk.TclError:
            pass
        finally:
            self._syncing_selection = False

    def _on_text_document_selected(self, _event=None):
        """A Text Editor document was selected: when the same file (full path) is open in JSON
        Controls, make that JSON document the active one."""
        text_editor = getattr(self, "_text_editor", None)
        if text_editor is None or getattr(self, "_syncing_selection", False) or not self._documents:
            return
        try:
            text_document = text_editor._current_document()
        except tk.TclError:
            return
        if text_document is None or not text_document.get("path"):
            return
        path_key = self._sync_path_key(text_document["path"])
        index = next((position for position, document in enumerate(self._documents)
                      if document.get("current_file")
                      and self._sync_path_key(document["current_file"]) == path_key), None)
        if index is None or index == self._active_document_index:
            return
        self._syncing_selection = True
        try:
            self._capture_active_document()
            self._restore_document(index)
        finally:
            self._syncing_selection = False

    def _update_active_file_path(self):
        """Show the active JSON file's full path (drive letter to file name) in the Active File
        Path bar; empty for a document that has no file yet."""
        path_variable = getattr(self, "_active_file_path_var", None)
        if path_variable is not None:
            path_variable.set(os.path.abspath(self._current_file) if getattr(self, "_current_file", None) else "")

    def _update_window_title(self):
        """Show the active document's file name (or 'Untitled') in the window title."""
        self._update_active_file_path()
        if self._current_file:
            self.title(f"Helios Interface Editor — {os.path.basename(self._current_file)}")
        else:
            self.title("Helios Interface Editor — Untitled")

    def _stored_document_signature(self, document):
        """Signature of a stored (inactive) document's data.  Stored data never changes -
        a document record is replaced as a whole when it is captured - so the JSON
        signature is worked out once and kept in the record ("data_signature").
        Before, every redraw of the document tab bar re-serialised every document."""
        data_signature = document.get("data_signature")
        if data_signature is None:
            data_signature = self._document_signature(document["data"])
            document["data_signature"] = data_signature
        return data_signature

    def _document_label(self, document, index):
        """Text for a document tab: the file name (or "Untitled n"), plus " *" when it has
        unsaved changes.  The active document is checked against the live profile."""
        if document["current_file"]:
            label = os.path.basename(document["current_file"])
        else:
            untitled_number = sum(
                1 for open_document in self._documents[:index + 1]
                if not open_document["current_file"])
            label = "Untitled" if untitled_number == 1 else f"Untitled {untitled_number}"
        if self._document_is_dirty(index):
            label += " *"
        return label

    @staticmethod
    def _document_signature(data):
        """Text fingerprint of a profile (JSON with private fields removed) used to tell
        whether it differs from its saved state."""
        try:
            return json.dumps(strip_private_fields(data), sort_keys=True)
        except Exception:
            return repr(data)

    def _render_document_tabs(self):
        """Redraw the shared document list in every JSON subtab's tab strip."""
        for tab_bar in getattr(self, "_document_tab_bars", ()):
            if not tab_bar.winfo_exists():
                continue
            for child in tab_bar.winfo_children():
                child.destroy()
            for index, document in enumerate(self._documents):
                active = index == self._active_document_index
                tab_frame = tk.Frame(tab_bar,
                               bg=PANEL_BG if active else MID_BG,
                               highlightthickness=1,
                               highlightbackground=ACCENT if active else BORDER)
                tab_frame.pack(side="left", padx=(6 if index == 0 else 2, 0), pady=4)
                label = tk.Button(tab_frame, text=self._document_label(document, index),
                                  bg=PANEL_BG if active else MID_BG,
                                  fg=ACCENT if active else TEXT_PRI,
                                  activebackground=PANEL_BG, activeforeground=ACCENT,
                                  relief="flat", bd=0, padx=10, pady=2,
                                  font=FONT_UI,
                                  command=lambda item=document: self._select_document(item))
                label.pack(side="left")
                close = tk.Button(tab_frame, text="x", bg=tab_frame.cget("bg"), fg=TEXT_SEC,
                                  activebackground=tab_frame.cget("bg"), activeforeground=ERROR,
                                  relief="flat", bd=0, padx=5, pady=2, font=FONT_UI,
                                  command=lambda item=document: self._close_document(item))
                close.pack(side="left")
                close.bind(
                    "<ButtonRelease-1>",
                    lambda event, item=document: self._close_document_from_tab(event, item),
                )
                for widget in (tab_frame, label):
                    widget.bind(
                        "<ButtonPress-1>",
                        lambda event, tab_index=index: self._start_document_drag(tab_index),
                    )
                    widget.bind("<B1-Motion>", self._drag_document)
                    widget.bind(
                        "<ButtonRelease-1>",
                        lambda event, source_bar=tab_bar: self._finish_document_drag(
                            event, source_bar),
                    )

    def _close_document_from_tab(self, event, document):
        """Close from the tab's x button without routing its click through drag handling."""
        widget = event.widget
        if 0 <= event.x < widget.winfo_width() and 0 <= event.y < widget.winfo_height():
            self._close_document(document)
        return "break"

    def _document_index(self, document):
        """Position of a document record in the open-document list, or None."""
        for index, item in enumerate(self._documents):
            if item is document:
                return index
        return None

    def _select_document(self, document):
        """Document tab clicked: store the current document and switch to the clicked one."""
        index = self._document_index(document)
        if index is None:
            return
        if index == self._active_document_index:
            return
        self._capture_active_document()
        self._restore_document(index)

    def _start_document_drag(self, index):
        """Mouse pressed on a document tab: remember which tab may be dragged."""
        self._dragged_document_index = index
        self._document_drag_moved = False

    def _drag_document(self, _event):
        """Mouse moved with the button down: note that this is a drag, not a click."""
        self._document_drag_moved = True

    def _move_document(self, index, target):
        """Move a document from position index to position target, keeping the active document
        active, and redraw the tab bar."""
        if index == target:
            return
        document = self._documents.pop(index)
        self._documents.insert(target, document)
        if self._active_document_index == index:
            self._active_document_index = target
        elif index < self._active_document_index <= target:
            self._active_document_index -= 1
        elif target <= self._active_document_index < index:
            self._active_document_index += 1
        self._render_document_tabs()

    def _finish_document_drag(self, _event, tab_bar):
        """Mouse released: when the tab was dragged, drop it at the position under the pointer."""
        index = getattr(self, "_dragged_document_index", None)
        if index is None or index >= len(self._documents):
            return
        if not getattr(self, "_document_drag_moved", False):
            self._dragged_document_index = None
            return
        pointer_x = tab_bar.winfo_pointerx()
        target = index
        for candidate, tab in enumerate(tab_bar.winfo_children()):
            midpoint = tab.winfo_rootx() + tab.winfo_width() / 2
            if pointer_x < midpoint:
                target = candidate
                break
            target = candidate
        self._dragged_document_index = target
        self._move_document(index, target)
        self._dragged_document_index = None

    def _document_is_dirty(self, index):
        """True when document `index` has unsaved changes (the active one is compared
        live; stored ones use their cached signature)."""
        if index == self._active_document_index:
            return self._has_unsaved_changes()
        document = self._documents[index]
        return document["clean_signature"] != self._stored_document_signature(document)

    def _close_document(self, document):
        """Close a document (asking first when it has unsaved changes); closing the last one
        leaves a new empty document."""
        index = self._document_index(document)
        if index is None:
            return
        if self._document_is_dirty(index):
            if not messagebox.askyesno(
                    "Close File", "This file has unsaved changes.\n\nClose it anyway?",
                    parent=self):
                return
        self._capture_active_document()
        self._documents.pop(index)
        if not self._documents:
            self._reset_to_new_profile()
            self._mark_clean()
            self._documents.append(self._make_document_record(replace_on_open=True))
            self._active_document_index = 0
            self._restore_document(0)
        else:
            if index < self._active_document_index:
                self._active_document_index -= 1
            elif index == self._active_document_index:
                self._active_document_index = min(index, len(self._documents) - 1)
            self._restore_document(self._active_document_index)
        self._render_document_tabs()

    # ── window icon ──────────────────────────────────────────────────────────────
    def _set_window_icon(self):
        """Use Helios.ico for the title bar / taskbar instead of the default Tk
        feather. `default=` applies it to this window and every dialog opened
        afterwards. Silently keeps the default icon if the file isn't found
        (e.g. Helios.ico wasn't kept next to the script)."""
        if sys.platform == "win32":                 # lets the taskbar show this program's own icon
            try:
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("HeliosInterfaceEditor")
            except Exception:
                pass
        icon_path = find_app_icon()
        if not icon_path:
            return
        try:
            self.iconbitmap(default=icon_path)
        except Exception:
            try:
                self.iconbitmap(icon_path)
            except Exception:
                pass

    # ── styles ─────────────────────────────────────────────────────────────────
    def _setup_styles(self):
        """Configure the ttk styles (notebook tabs, tables, scrollbars, combo boxes) for the
        current colour theme."""
        style = ttk.Style(self)
        style.theme_use("clam")
        style.configure("TNotebook",        background=DARK_BG, borderwidth=0)
        style.configure("TNotebook.Tab",    background=MID_BG,  foreground=TEXT_SEC,
                        font=FONT_UI, padding=[10, 6], borderwidth=1)   # 10: all 15 tabs fit ~1400 px
        style.map("TNotebook.Tab",
                  background=[("selected", ROW_SELECTED), ("active", ROW_EVEN)],
                  foreground=[("selected", ROW_SELECTED_TEXT)],
                  font=[("selected", FONT_HEAD)],
                  borderwidth=[("selected", 2)])
        style.configure("Treeview",         background=ROW_ODD, fieldbackground=ROW_ODD,
                        foreground=TEXT_PRI, font=FONT_MONO, rowheight=24, borderwidth=0)
        style.configure("Treeview.Heading", background=PANEL_BG, foreground=TEXT_HEAD,
                        font=FONT_HEAD, relief="flat")
        style.map("Treeview",
                  background=[("selected", ROW_SELECTED)],
                  foreground=[("selected", ROW_SELECTED_TEXT)])
        style.configure("Vertical.TScrollbar", background=MID_BG, troughcolor=DARK_BG,
                        arrowcolor=TEXT_SEC, borderwidth=0)
        style.configure("Dark.TCombobox", fieldbackground=MID_BG, background=MID_BG,
                        foreground=TEXT_PRI, arrowcolor=TEXT_PRI, bordercolor=BORDER,
                        lightcolor=MID_BG, darkcolor=MID_BG, selectbackground=MID_BG,
                        selectforeground=TEXT_PRI)
        style.map("Dark.TCombobox",
                  fieldbackground=[("readonly", MID_BG)],
                  background=[("readonly", MID_BG)],
                  foreground=[("readonly", TEXT_PRI)])
        self.option_add("*TCombobox*Listbox.background", MID_BG)
        self.option_add("*TCombobox*Listbox.foreground", TEXT_PRI)
        self.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
        self.option_add("*TCombobox*Listbox.selectForeground", "white")
        # ttk widgets used by the Argument Logger tab and its windows.
        style.configure("TFrame", background=PANEL_BG)
        style.configure("TLabel", background=PANEL_BG, foreground=TEXT_PRI, font=FONT_UI)
        style.configure("TLabelframe", background=PANEL_BG, bordercolor=BORDER,
                        lightcolor=PANEL_BG, darkcolor=PANEL_BG)
        style.configure("TLabelframe.Label", background=PANEL_BG, foreground=TEXT_HEAD, font=FONT_UI)
        style.configure("TButton", background=MID_BG, foreground=TEXT_PRI, bordercolor=BORDER,
                        lightcolor=MID_BG, darkcolor=MID_BG, font=FONT_UI, padding=[8, 3])
        style.map("TButton", background=[("active", ROW_EVEN), ("pressed", ROW_SELECTED)],
                  foreground=[("pressed", ROW_SELECTED_TEXT)])
        style.configure("TEntry", fieldbackground=MID_BG, foreground=TEXT_PRI, bordercolor=BORDER,
                        lightcolor=MID_BG, darkcolor=MID_BG, insertcolor=TEXT_PRI)
        # Table, tab and scroll bar borders in the scheme's colours too.
        style.configure("Treeview", bordercolor=BORDER, lightcolor=ROW_ODD, darkcolor=ROW_ODD)
        style.configure("TNotebook", bordercolor=BORDER, lightcolor=PANEL_BG, darkcolor=PANEL_BG)
        style.configure("TNotebook.Tab", bordercolor=BORDER, lightcolor=ROW_EVEN, darkcolor=ROW_EVEN)
        style.configure("Main.TNotebook", background=DARK_BG, borderwidth=0)
        style.configure("Main.TNotebook.Tab", background=MID_BG, foreground=TEXT_PRI,
                        font=FONT_HEAD, padding=[14, 8], borderwidth=1,
                        bordercolor=ACCENT2, lightcolor=ACCENT2, darkcolor=ACCENT2)
        style.map("Main.TNotebook.Tab",
                  background=[("selected", ROW_SELECTED), ("active", ROW_EVEN)],
                  foreground=[("selected", ROW_SELECTED_TEXT)])
        # Scroll bars in the scheme's colours (both directions, every part of them).
        for scrollbar_style in ("Vertical.TScrollbar", "Horizontal.TScrollbar"):
            style.configure(scrollbar_style, background=MID_BG, troughcolor=DARK_BG,
                            bordercolor=BORDER, lightcolor=MID_BG, darkcolor=MID_BG,
                            arrowcolor=TEXT_SEC, gripcount=0, borderwidth=0)
            style.map(scrollbar_style, background=[("active", ROW_EVEN), ("pressed", ROW_SELECTED)],
                      arrowcolor=[("active", TEXT_PRI)])

    # ── menu ───────────────────────────────────────────────────────────────────
    def _build_menu(self):
        """Build the menu bar: Profile (new, edit, save, package, monitor removal - interface
        and reference table together), JSON (new, open, save, save as), Options
        (colour scheme), Table (generate, load, load additional viewports, save, save as) and
        Logger (the Argument Logger tab). The Text Editor menu is attached when its tab is built."""
        menu_bar = tk.Menu(self, bg=MID_BG, fg=TEXT_PRI, activebackground=ACCENT,
                           activeforeground=DARK_BG, relief="flat", font=FONT_UI)
        self.configure(menu=menu_bar)
        previous_menu_bar = getattr(self, "_menu_bar", None)
        self._menu_bar = menu_bar
        if previous_menu_bar is not None:
            previous_menu_bar.destroy()
        # Profile menu (left-most): the interface and its reference table handled together.
        profile_menu = tk.Menu(menu_bar, tearoff=0, bg=MID_BG, fg=TEXT_PRI,
                               activebackground=ACCENT, activeforeground=DARK_BG, font=FONT_UI)
        menu_bar.add_cascade(label="Profile", menu=profile_menu)
        profile_menu.add_command(label="New",  command=self._profile_new,  accelerator="Ctrl+N")
        profile_menu.add_command(label="Edit", command=self._profile_edit, accelerator="Ctrl+E")
        profile_menu.add_command(label="Save", command=self._profile_save, accelerator="Ctrl+S")
        profile_menu.add_command(label="Package", command=self._profile_package, accelerator="Ctrl+P")
        profile_menu.add_command(label="Monitor Removal", command=self._profile_monitor_removal,
                                 accelerator="Ctrl+M")
        profile_menu.add_command(label="Check Bindings", command=self._profile_check_bindings,
                                 accelerator="Ctrl+B")
        profile_menu.add_command(label="Reset", command=self._profile_reset, accelerator="Ctrl+R")

        file_menu = tk.Menu(menu_bar, tearoff=0, bg=MID_BG, fg=TEXT_PRI,
                            activebackground=ACCENT, activeforeground=DARK_BG, font=FONT_UI)
        menu_bar.add_cascade(label="JSON", menu=file_menu)
        file_menu.add_command(label="New",        command=self._new)
        file_menu.add_command(label="Open…",      command=self._open,   accelerator="Ctrl+O")
        file_menu.add_command(label="Save",       command=self._save)
        file_menu.add_command(label="Save As…",   command=self._save_as)
        file_menu.add_command(label="Save As Helios Type…", command=self._save_as_helios_type)
        file_menu.add_command(label="Save As DCS Type…",    command=self._save_as_dcs_type)
        file_menu.add_separator()
        file_menu.add_command(label="View Devices…", command=self._show_device_viewer)
        # file_menu.add_separator()
        # # Import moved into the File menu and renamed; it now searches the chosen
        # # cockpit folder and all of its subfolders for the clickabledata file.
        # file_menu.add_command(label="Import DCS Cockpit folder…",
        #                       command=self._import_dcs_folder,
        #                       accelerator="Ctrl+I")
        options_menu = tk.Menu(menu_bar, tearoff=0, bg=MID_BG, fg=TEXT_PRI,
                             activebackground=ACCENT, activeforeground=DARK_BG, font=FONT_UI)
        self._options_menu = options_menu
        theme_menu = tk.Menu(options_menu, tearoff=0, bg=MID_BG, fg=TEXT_PRI,
                             activebackground=ACCENT, activeforeground=DARK_BG, font=FONT_UI)
        self._theme_choice.set(self._theme_name)
        for theme_name, theme_label in THEME_MENU_LABELS:
            # The switch rebuilds the menu bar, so it runs once this menu has closed: rebuilding
            # a menu from inside its own click can crash Tk on Windows.
            theme_menu.add_radiobutton(label=theme_label, value=theme_name, variable=self._theme_choice,
                                       selectcolor=TEXT_PRI,
                                       command=lambda chosen=theme_name: self.after(50, self._set_theme, chosen))
        options_menu.add_cascade(label="Color Scheme", menu=theme_menu)

        # Table menu: two drop-downs.
        #   Current Reference ▸ Generate / Load / Save / Save As   -> the Reference tab
        #   Old Reference     ▸ Load / Save / Save As              -> the Old References tab
        menu_options = dict(tearoff=0, bg=MID_BG, fg=TEXT_PRI, activebackground=ACCENT,
                            activeforeground=DARK_BG, font=FONT_UI)
        self._text_editor_menu_options = menu_options
        table_menu = tk.Menu(menu_bar, **menu_options)
        menu_bar.add_cascade(label="Reference Data", menu=table_menu)
        current_reference_menu = tk.Menu(table_menu, **menu_options)
        table_menu.add_cascade(label="Current Reference", menu=current_reference_menu)
        current_reference_menu.add_command(label="Generate…", accelerator="Ctrl+G",
                                           command=lambda: self._run_table_action("generate_table"))
        current_reference_menu.add_command(label="Load…", command=lambda: self._run_table_action("load_table"))
        current_reference_menu.add_command(label="Load additional viewports…", command=self.load_additional_viewports)
        current_reference_menu.add_command(label="Save", command=lambda: self._run_table_action("save_table"))
        current_reference_menu.add_command(label="Save As…", command=lambda: self._run_table_action("save_table_as"))
        old_reference_menu = tk.Menu(table_menu, **menu_options)
        table_menu.add_cascade(label="Old Reference", menu=old_reference_menu)
        old_reference_menu.add_command(label="Load…",
                                       command=lambda: self._run_table_action("load_table", OLD_REFERENCE_ROLE))
        old_reference_menu.add_command(label="Save",
                                       command=lambda: self._run_table_action("save_table", OLD_REFERENCE_ROLE))
        old_reference_menu.add_command(label="Save As…",
                                       command=lambda: self._run_table_action("save_table_as", OLD_REFERENCE_ROLE))

        # Logger menu: the Argument Logger tab's commands.
        self._argument_logger.build_menu(menu_bar, menu_options)

        self.bind_all("<Control-n>", lambda event: self._route_text_editor_shortcut(
            event, "new_document", fallback=self._profile_new))
        self.bind_all("<Control-e>", lambda event: self._profile_edit())
        self.bind_all("<Control-s>", lambda event: self._route_text_editor_shortcut(
            event, "save_current", fallback=self._profile_save))
        self.bind_all("<Control-p>", lambda event: self._profile_package())
        self.bind_all("<Control-m>", lambda event: self._profile_monitor_removal())
        self.bind_all("<Control-b>", lambda event: self._profile_check_bindings())
        self.bind_all("<Control-r>", lambda event: self._profile_reset())
        self.bind_all("<Control-o>", lambda event: self._route_text_editor_shortcut(
            event, "open_files", fallback=self._open))
        self.bind_all("<Control-z>", lambda event: self._route_text_editor_shortcut(
            event, "_undo_current", fallback=self._undo))
        self.bind_all("<Control-x>", lambda event: self._route_text_editor_shortcut(
            event, "_cut", fallback=self._cut_selected_functions))
        self.bind_all("<Control-g>", lambda event: self._run_table_action("generate_table"))
        self.bind_all("<Control-c>", lambda event: self._route_text_editor_shortcut(
            event, "_text_event", "<<Copy>>", fallback=self._copy_selected_functions))
        self.bind_all("<Control-v>", lambda event: self._route_text_editor_shortcut(
            event, "_text_event", "<<Paste>>", fallback=self._paste_functions))
        self.bind_all("<Control-y>", lambda event: self._route_text_editor_shortcut(
            event, "_redo_current", fallback=self._redo))
        self.bind_all("<Control-Shift-s>", lambda event: self._route_text_editor_shortcut(
            event, "save_current_as"))
        self.bind_all("<Control-w>", lambda event: self._route_text_editor_shortcut(
            event, "close_current"))
        self.bind_all("<Control-a>", lambda event: self._route_text_editor_shortcut(
            event, "_select_all"))
        self.bind_all("<Control-f>", lambda event: self._route_text_editor_shortcut(
            event, "show_find"))
        self.bind_all("<F3>", lambda event: self._route_text_editor_shortcut(
            event, "_find_next"))
        self.bind_all("<Control-Tab>", lambda event: self._route_text_editor_shortcut(
            event, "_next_tab"))
        self.bind_all("<Control-Shift-Tab>", lambda event: self._route_text_editor_shortcut(
            event, "_previous_tab"))
        # self.bind_all("<Control-i>", lambda event: self._import_dcs_folder())

    def _text_editor_is_selected(self):
        """True when the Text Editor tab is the selected main tab."""
        if getattr(self, "_main_notebook", None) is None:
            return False
        try:
            return (
                self._main_notebook.tab(self._main_notebook.select(), "text")
                == TEXT_EDITOR_TAB_LABEL
            )
        except tk.TclError:
            return False

    def _route_text_editor_shortcut(self, _event, method, *args, fallback=None):
        """Run a keyboard shortcut on the Text Editor when its tab is selected, else run the fallback."""
        if not self._text_editor_is_selected():
            return fallback() if fallback is not None else None
        if self._text_editor is not None:
            if method == "open_files":
                self._open_text_editor_files()
            else:
                getattr(self._text_editor, method)(*args)
        return "break"

    def _run_text_editor_action(self, method, *args):
        """Select the Text Editor tab and run one of its actions."""
        if self._text_editor is None:
            return
        if self._text_editor_frame is not None:
            self._main_notebook.select(self._text_editor_frame)
        if method == "open_files":
            return self._open_text_editor_files()
        result = getattr(self._text_editor, method)(*args)
        if method in ("save_current", "save_current_as") and result:
            self._record_text_editor_save()
        return result

    def _record_text_editor_save(self):
        """Note that the Text Editor saved a file so the matching JSON document can take the saved content."""
        document = self._text_editor._current_document()
        if document is not None and document.get("path"):
            path_key = self._sync_path_key(document["path"])
            self._pending_saved_editor_syncs[path_key] = {
                "source": "text",
                "path": document["path"],
                "content": document["saved_content"],
            }
            self._sync_saved_editor_changes()

    @staticmethod
    def _sync_path_key(path):
        """A path in a form that compares equal for the same file (None for no path)."""
        return os.path.normcase(os.path.realpath(os.path.abspath(path))) if path else None

    @staticmethod
    def _sync_json_signature(data):
        """A text fingerprint of JSON data that ignores key order."""
        return json.dumps(data, sort_keys=True, ensure_ascii=False)

    @staticmethod
    def _sync_text_content(text_document):
        """The text shown in a Text Editor document."""
        return text_document["editor"].text.get("1.0", "end-1c")

    @staticmethod
    def _normalise_saved_profile(content):
        """Parse profile text and bring it to the editor's form: numbers cast, actionId keys spelled alike, vehicles present."""
        profile = json.loads(content)
        if not isinstance(profile, dict):
            raise ValueError("The saved JSON must contain an object at the top level.")
        profile = cast_strings_to_numbers(profile)
        profile = normalize_action_id_keys(profile)
        profile.setdefault("vehicles", [])
        profile.setdefault("functions", [])
        if not isinstance(profile["vehicles"], list) or not isinstance(profile["functions"], list):
            raise ValueError("The saved JSON must contain lists for 'vehicles' and 'functions'.")
        if any(not isinstance(function, dict) for function in profile["functions"]):
            raise ValueError("Every item in the saved JSON 'functions' list must be an object.")
        return profile

    def _replace_text_document_with_saved_profile(self, document, content):
        """Show saved profile text in a Text Editor document and mark it unmodified."""
        normalized_content = content.replace("\r\n", "\n").replace("\r", "\n")
        editor = document["editor"]
        text_widget = editor.text
        text_widget.delete("1.0", "end")
        text_widget.insert("1.0", normalized_content)
        text_widget.edit_reset()
        text_widget.edit_modified(False)
        for mark in tuple(editor.bookmark_marks):
            text_widget.mark_unset(mark)
        editor.bookmark_marks.clear()
        document["encoding"] = "utf-8"
        document["newline"] = os.linesep
        document["saved_content"] = normalized_content
        document["dirty"] = False
        document["replace_on_open"] = False
        editor._schedule_redraw()
        self._text_editor._refresh_tab_labels()
        self._text_editor._update_title()

    def _replace_json_document_with_saved_profile(self, index, profile):
        """Make a JSON document hold a saved profile, sorted and marked clean."""
        document = self._documents[index]
        replacement = copy.deepcopy(profile)
        replacement["functions"].sort(key=device_action_sort_key)
        document.update({
            "data": replacement,
            "clean_signature": self._document_signature(replacement),
            "last_added_device": "",
            "last_added_device_id": "",
            "last_added_function": None,
            "last_saved_function": None,
            "next_saved_session_index": 1,
            "next_created_session_index": 1,
            "undo_stack": [],
            "redo_stack": [],
        })
        document.pop("data_signature", None)
        if index == self._active_document_index:
            self._restore_document(index)
            self._mark_clean()
        else:
            self._render_document_tabs()

    def _sync_saved_editor_changes(self):
        """A file was saved in one editor: the other editor's copies of that same file (matched by
        full path) take over what was saved, without asking - the Text Editor documents get the
        saved text and become clean; the JSON Controls documents get the saved profile and become
        clean."""
        if not self._pending_saved_editor_syncs or self._text_editor is None:
            return
        self._live_sync_busy = True
        try:
            for path_key, pending in tuple(self._pending_saved_editor_syncs.items()):
                self._pending_saved_editor_syncs.pop(path_key, None)
                if pending["source"] == "json":
                    self._sync_saved_json_to_text_documents(path_key, pending["content"])
                elif pending["source"] == "text":
                    self._sync_saved_text_to_json_documents(path_key, pending["content"])
        finally:
            self._live_sync_busy = False

    def _sync_saved_json_to_text_documents(self, path_key, saved_content):
        """The Text Editor documents of the saved file take over the saved text."""
        for document in [document for document in self._text_editor.documents
                         if self._sync_path_key(document.get("path")) == path_key]:
            self._replace_text_document_with_saved_profile(document, saved_content)

    def _sync_saved_text_to_json_documents(self, path_key, saved_text):
        """The JSON Controls documents of the saved file take over the saved profile."""
        self._capture_active_document()
        try:
            saved_profile = self._normalise_saved_profile(saved_text)
        except (json.JSONDecodeError, TypeError, ValueError):
            return                                # a saved file that is not a profile: leave the JSON tab alone
        saved_signature = self._document_signature(saved_profile)
        for index, document in enumerate(self._documents):
            if self._sync_path_key(document.get("current_file")) != path_key:
                continue
            if self._document_signature(document["data"]) != saved_signature:
                self._replace_json_document_with_saved_profile(index, saved_profile)
                continue
            document["clean_signature"] = saved_signature     # same data: only the saved baseline moves
            if index == self._active_document_index:
                self._clean_signature = saved_signature
            self._render_document_tabs()

    # ── live two-way sync between a Text Editor document and its JSON Controls document ──────
    # Both ways the other side follows a moment after a change (LIVE_SYNC_DELAY_MS), matched by the
    # file's full path.  Text that is not (yet) a valid Helios profile while it is being typed
    # changes nothing; whichever side already holds the same data is left alone, so the two
    # directions never echo.
    def _install_live_sync(self):
        """Hook the Text Editor's change notification (called whenever the text editor is built)."""
        text_editor = self._text_editor
        original = text_editor._document_changed

        def document_changed(document):
            """A Text Editor document changed: run the original handler, then schedule the JSON update."""
            original(document)
            self._schedule_text_to_json(document)

        text_editor._document_changed = document_changed

    def _schedule_text_to_json(self, document):
        """Update the JSON document from the Text Editor once typing has paused."""
        if getattr(self, "_live_sync_busy", False) or not document.get("path"):
            return
        pending_job = getattr(self, "_text_to_json_job", None)
        if pending_job is not None:
            self.after_cancel(pending_job)
        self._text_to_json_job = self.after(LIVE_SYNC_DELAY_MS, lambda: self._apply_text_to_json(document))

    def _schedule_json_to_text(self):
        """Update the Text Editor from the JSON document once changes have paused."""
        if getattr(self, "_live_sync_busy", False) or getattr(self, "_text_editor", None) is None:
            return
        pending_job = getattr(self, "_json_to_text_job", None)
        if pending_job is not None:
            self.after_cancel(pending_job)
        self._json_to_text_job = self.after(LIVE_SYNC_DELAY_MS, self._apply_json_to_text)

    def _apply_text_to_json(self, document):
        """The text of a Text Editor document changed: when it is a valid profile, the JSON Controls
        documents of the same file take its data."""
        self._text_to_json_job = None
        text_editor = self._text_editor
        if (getattr(self, "_live_sync_busy", False) or text_editor is None
                or document not in text_editor.documents or not document.get("path")):
            return
        path_key = self._sync_path_key(document["path"])
        if not any(self._sync_path_key(item.get("current_file")) == path_key for item in self._documents):
            return
        try:
            profile = self._normalise_saved_profile(self._sync_text_content(document))
        except (json.JSONDecodeError, TypeError, ValueError, AttributeError):
            return                                    # still being typed: nothing to apply yet
        profile["functions"].sort(key=device_action_sort_key)
        signature = self._document_signature(profile)
        self._capture_active_document()
        self._live_sync_busy = True
        try:
            for index, item in enumerate(self._documents):
                if (self._sync_path_key(item.get("current_file")) != path_key
                        or self._document_signature(item["data"]) == signature):
                    continue
                carry_session_markers(item["data"].get("functions", []), profile["functions"])
                item["data"] = copy.deepcopy(profile)
                item.pop("data_signature", None)
                if index == self._active_document_index:
                    self._data = copy.deepcopy(profile)
                    self._sync_data_to_header()
                    self._refresh_all()
            self._render_document_tabs()
        finally:
            self._live_sync_busy = False

    def _apply_json_to_text(self):
        """The active JSON Controls document changed: the Text Editor documents of the same file
        show it (the text is only replaced when its data differs, so typing there is not disturbed)."""
        self._json_to_text_job = None
        text_editor = self._text_editor
        if (getattr(self, "_live_sync_busy", False) or text_editor is None
                or not self._current_file or not self._documents):
            return
        path_key = self._sync_path_key(self._current_file)
        targets = [document for document in text_editor.documents
                   if self._sync_path_key(document.get("path")) == path_key]
        if not targets:
            return
        try:
            content = json.dumps(self._build_save_payload(), indent=2)
            wanted = self._document_signature(self._normalise_saved_profile(content))
        except Exception:
            return
        self._live_sync_busy = True
        try:
            for document in targets:
                if self._shown_signature(document) != wanted:
                    self._replace_document_text(document, content)
        finally:
            self._live_sync_busy = False

    def _shown_signature(self, document):
        """Signature of the JSON a Text Editor document shows now (None when it is not valid JSON)."""
        try:
            return self._document_signature(self._normalise_saved_profile(self._sync_text_content(document)))
        except (json.JSONDecodeError, TypeError, ValueError):
            return None

    def _replace_document_text(self, document, content):
        """Put new text in a Text Editor document, keeping the cursor and scroll position."""
        text_widget = document["editor"].text
        cursor_index, view_top = text_widget.index("insert"), text_widget.yview()[0]
        text_widget.delete("1.0", "end")
        text_widget.insert("1.0", content)
        try:
            text_widget.mark_set("insert", cursor_index)
        except tk.TclError:
            pass
        text_widget.yview_moveto(view_top)
        document["editor"]._schedule_redraw()
        self._refresh_text_document_state(document)

    def _refresh_text_document_state(self, document):
        """Recompute a Text Editor document's unsaved mark and tab label after its text was replaced."""
        text_editor = self._text_editor
        document["dirty"] = self._sync_text_content(document) != document["saved_content"]
        text_editor._refresh_tab_labels()
        text_editor._update_title()

    @staticmethod
    def _text_editor_theme():
        """The colours the Text Editor uses, taken from the current theme."""
        return {
            "window": DARK_BG,
            "panel": PANEL_BG,
            "tab": MID_BG,
            "text_bg": MID_BG,
            "text_fg": TEXT_PRI,
            "gutter_bg": PANEL_BG,
            "gutter_fg": TEXT_SEC,
            "selection": ROW_SELECTED,
            "bookmark": ACCENT,
            "find": WARN,
            "added": SUCCESS,
            "removed": DANGER_BG,
            "changed": WARN,
            "border": BORDER,
            "accent": ACCENT,
        }

    # ── theme switching ─────────────────────────────────────────────────────────
    def _toggle_theme(self):
        """Switch between the Default Palette and Dark Mode through _set_theme, which rebuilds
        the window and keeps every document, table and list.  (Options > Color Scheme picks
        either scheme.)"""
        self._set_theme("default" if self._theme_name == "dark" else "dark")

    def _set_theme(self, name):
        """Switch the colour scheme and rebuild the chrome so every widget picks
        up the new palette. Field values and the active tab are preserved."""
        if name == self._theme_name:
            return
        self._sync_header_to_data()
        visible_main_tab_label = self._main_notebook.tab(self._main_notebook.select(), "text")
        visible_tab_label = self._visible_tab_label()   # reselected after the rebuild
        if self._text_editor is not None:
            self._text_editor_state = self._text_editor.export_state()

        self._theme_name = name
        apply_theme(THEMES.get(name, DEFAULT_THEME))
        self.save_editor_setting("color_scheme", name)        # remembered between runs

        self.configure(bg=DARK_BG)
        self._setup_styles()
        self._build_menu()

        # Rebuild header + tabs against the new palette.
        if self._header_frame is not None:
            self._header_frame.destroy()
        if self._command_table_panel is not None:
            self._command_table_state = self._command_table_panel.export_state()
        if self._old_reference_panel is not None:
            self._old_reference_state = self._old_reference_panel.export_state()
        self._main_notebook.destroy()
        self._text_editor = None
        self._text_editor_frame = None
        self._build_header()
        self._build_tabs()
        self._sync_data_to_header()
        self._refresh_all()
        self._argument_logger.refresh_colors()
        if visible_tab_label:
            self._last_main_tab_label = visible_main_tab_label
            self._select_tab_by_label(visible_tab_label, visible_main_tab_label)

    # ── header ─────────────────────────────────────────────────────────────────
    def _build_header(self):
        """Build the header: profile fields (source, version, commit, type, module, vehicles),
        the generated name, max id and device counters, and the search strip (Find, Find
        All, Set Descriptions)."""
        header = tk.Frame(self, bg=PANEL_BG, pady=10)
        header.pack(fill="x", padx=0, pady=0)
        self._header_frame = header

        tk.Label(header, text="HELIOS INTERFACE EDITOR", bg=PANEL_BG, fg=ACCENT,
                 font=("Segoe UI", 13, "bold")).grid(row=0, column=0, columnspan=3,
                                                     sticky="w", padx=16, pady=(0, 8))

        self._header_vars = {}

        fields = [
            ("Source",  "source",  12),
            ("Version", "version", 10),
            ("Commit",  "commit",  12),
            ("Type",    "type",    12),
            ("Module",  "module",  14),
            ("Vehicles (comma-sep)", "vehicles_str", 20),
        ]
        grid_column = 0
        for label, key, width in fields:
            tk.Label(header, text=label, bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI
                     ).grid(row=1, column=grid_column, sticky="w", padx=(12, 2))
            var = tk.StringVar()
            entry = tk.Entry(header, textvariable=var, width=width, bg=MID_BG, fg=TEXT_PRI,
                             insertbackground=TEXT_PRI, relief="flat", font=FONT_MONO,
                             highlightthickness=1, highlightcolor=ACCENT, highlightbackground=BORDER)
            entry.grid(row=2, column=grid_column, sticky="ew", padx=(12, 2), pady=2)
            self._header_vars[key] = var
            grid_column += 1

        # Name (read-only derived)
        tk.Label(header, text="Name (auto)", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI
                 ).grid(row=1, column=grid_column, sticky="w", padx=(12, 2))
        self._name_label = tk.Label(header, text="", bg=MID_BG, fg=WARN, font=FONT_MONO,
                                  width=22, anchor="w", relief="flat", padx=4)
        self._name_label.grid(row=2, column=grid_column, sticky="ew", padx=(12, 2), pady=2)
        grid_column += 1

        # Max ID
        tk.Label(header, text="Max id used", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI
                 ).grid(row=1, column=grid_column, sticky="w", padx=(16, 2))
        self._max_id_label = tk.Label(header, text="0", bg=MID_BG, fg=SUCCESS, font=("Consolas", 13, "bold"),
                                    width=8, anchor="center", relief="flat", padx=4)
        self._max_id_label.grid(row=2, column=grid_column, padx=(16, 12), pady=2)
        grid_column += 1

        # Total devices (all types combined)
        tk.Label(header, text="Total devices", bg=PANEL_BG, fg=TEXT_SEC, font=FONT_UI
                 ).grid(row=1, column=grid_column, sticky="w", padx=(16, 2))
        self._total_count_label = tk.Label(header, text="0", bg=MID_BG, fg=ACCENT,
                                         font=("Consolas", 13, "bold"),
                                         width=8, anchor="center", relief="flat", padx=4)
        self._total_count_label.grid(row=2, column=grid_column, padx=(16, 12), pady=2)

        # Active File Path: where the active JSON file was loaded from / saved to, above Type.
        if getattr(self, "_active_file_path_var", None) is None:
            self._active_file_path_var = tk.StringVar(master=self)
        path_frame = tk.Frame(header, bg=PANEL_BG)
        path_frame.grid(row=0, column=3, columnspan=11, sticky="w", padx=(12, 2), pady=(0, 8))
        tk.Label(path_frame, text="Active File Path:", bg=PANEL_BG, fg=TEXT_SEC,
                 font=FONT_UI).pack(side="left", padx=(0, 4))
        tk.Label(path_frame, textvariable=self._active_file_path_var, bg=PANEL_BG, fg=TEXT_PRI,
                 font=FONT_MONO, anchor="w").pack(side="left")
        self._update_active_file_path()

        # Traces
        for key in ("type", "module"):
            self._header_vars[key].trace_add("write", self._update_name)

        # Search strip — find a function by name/device/id and jump to its tab.
        search_frame = tk.Frame(header, bg=PANEL_BG)
        search_frame.grid(row=3, column=0, columnspan=15, sticky="w", padx=12, pady=(8, 0))

        tk.Label(search_frame, text="🔍  Search", bg=PANEL_BG, fg=TEXT_SEC,
                 font=FONT_UI).pack(side="left", padx=(0, 6))

        self._search_var = tk.StringVar()
        search_entry = tk.Entry(search_frame, textvariable=self._search_var, width=36,
                                bg=MID_BG, fg=TEXT_PRI, insertbackground=TEXT_PRI,
                                relief="flat", font=FONT_MONO, highlightthickness=1,
                                highlightcolor=ACCENT, highlightbackground=BORDER)
        search_entry.pack(side="left")
        search_entry.bind("<Return>", lambda event: self._find_all())

        # Find (Enter too): every function and table row matching the search box, listed in
        # one results window (see _find_all).
        tk.Button(search_frame, text="Find", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=14, pady=3, cursor="hand2",
                  command=self._find_all).pack(side="left", padx=(6, 0))

        self._search_status = tk.Label(search_frame, text="", bg=PANEL_BG, fg=TEXT_SEC,
                                       font=FONT_UI)
        self._search_status.pack(side="left", padx=(10, 0))

        # Global action: stamp a standard description onto every function based
        # on its helios type (ScaledNetworkValue is intentionally left blank).
        tk.Button(search_frame, text="🏷  Set Descriptions", bg=ACCENT2, fg=DARK_BG,
                  font=FONT_HEAD, relief="flat", padx=14, pady=3, cursor="hand2",
                  command=self._apply_descriptions).pack(side="left", padx=(24, 0))

        # (Auto-fill Id's now lives in the Table tab's toolbar.)

        # Populate
        self._header_vars["source"].set(self._data.get("source", "User"))

    # ── search ─────────────────────────────────────────────────────────────────
    def _function_matches_query(self, function, query):
        """True when `query` (already lowercased) appears in any searchable
        field of `function`: name, device, description, export id, the
        prettified name/device, or the primary device/action ids."""
        haystack = [
            str(function.get("name", "")),
            str(function.get("device", "")),
            str(function.get("description", "")),
            prettify_label(function.get("name", "")),
            prettify_label(function.get("device", "")),
            str(get_primary_device_id(function)),
            str(get_primary_action_id(function)),
        ]
        for export in function.get("exports", []):
            haystack.append(str(export.get("id", "")))
            ### Edit here 
        return any(query in field.lower() for field in haystack)

    # ── Find ───────────────────────────────────────────────────────────────
    FIND_ALL_COLUMNS = (("deviceType", "Device Type", 150), ("arg", "Arg", 80), ("name", "Name", 240),
                        ("deviceId", "Device ID", 90), ("actionId", "Action ID", 90))

    def _find_all(self):
        """Find button (and Enter in the search box): every function (of every device type) that matches the
        search box - the same fields Find looks at (_function_matches_query) - and every
        row of the Reference, Old References, Mismatched, Viewport and Source tables (the
        Source tab's current table and each file's variables) containing the text, listed in
        a results window.  One pass over the functions and one over each
        table: O(functions + table rows)."""
        query = self._search_var.get().strip().lower()
        if not query:
            self._search_status.configure(text="Type something to find", fg=ERROR)
            return
        matching_functions = [(function_index, function)
                              for function_index, function in enumerate(self._data["functions"])
                              if self._function_matches_query(function, query)]
        matching_table_rows = self._find_in_tables(query)
        match_count = len(matching_functions) + len(matching_table_rows)
        self._search_status.configure(text=f"{match_count} match{'' if match_count == 1 else 'es'}",
                                      fg=SUCCESS if match_count else ERROR)
        self._show_find_all_results(query, matching_functions, matching_table_rows)

    def _find_in_tables(self, query):
        """Rows of the Tables tabs whose text contains query (ignoring upper / lower case), as
        (tab label, table view, row id, the five Find cells).  Cells: where it was found,
        Arg #, a name (Arg Name, else Command, else Note), Device #, Command #."""
        found_rows = []
        found_rows += self._find_in_command_and_old_tables(query)
        found_rows += self._find_in_mismatched_table(query)
        found_rows += self._find_in_source_table(query)
        found_rows += self._find_in_viewport_table(query)
        return found_rows

    def _find_in_command_and_old_tables(self, query):
        """Matches in the Command Table and Old Reference tabs."""
        matches = []
        for tab_label, panel in ((COMMAND_TABLE_TAB_LABEL, self._command_table_panel),
                                 (OLD_REFERENCE_TAB_LABEL, self._old_reference_panel)):
            if panel is not None and panel.winfo_exists():
                matches += self._find_in_table_panel(tab_label, panel, query)
        return matches

    @staticmethod
    def _find_in_table_panel(tab_label, panel, query):
        """Matches in the rows of one table panel."""
        matches = []
        for row_id, table_row in panel.rows_with_ids():
            if any(query in cell_text.lower() for cell_text in table_row.values()):
                shown_name = table_row["Arg Name"] or table_row["Command"] or table_row["Note"]
                matches.append((tab_label, panel.table_view, row_id,
                                (f"{tab_label} table", table_row["Arg #"], shown_name,
                                 table_row["Device #"], table_row["Command #"])))
        return matches

    def _find_in_mismatched_table(self, query):
        """Matches in the Mismatched tab."""
        mismatched_panel = self._mismatched_panel
        if mismatched_panel is None or not mismatched_panel.winfo_exists():
            return []
        return [(MISMATCHED_TAB_LABEL, mismatched_panel.mismatched_view, row_id,
                 (f"{MISMATCHED_TAB_LABEL} table", record["New Arg #"], record["Arg Name"],
                  record["New Device #"], record["New Command #"]))
                for row_id, record in mismatched_panel.records_by_row_id.items()
                if any(query in str(record[column]).lower() for column in MISMATCHED_COLUMNS)]

    def _find_in_source_table(self, query):
        """Matches in the Source tab: the current table, then each file's variables."""
        source_panel = self._source_panel
        if source_panel is None or not source_panel.winfo_exists():
            return []
        return self._find_in_source_rows(source_panel, query) + self._find_in_source_files(source_panel, query)

    @staticmethod
    def _find_in_source_rows(source_panel, query):
        """Matches in the Source tab's copy of the current table."""
        matches = []
        for row_position, source_row in enumerate(source_panel.source_rows):
            if any(query in str(source_row.get(column, "")).lower() for column in SOURCE_COLUMNS):
                matches.append((SOURCE_TAB_LABEL, source_panel, (SOURCE_ALL_FILES_OPTION, row_position),
                                (f"{SOURCE_TAB_LABEL} table", source_row.get("Arg #", ""),
                                 source_row.get("Arg Name", "") or source_row.get("Command", ""), "",
                                 source_row.get("Command #", ""))))
        return matches

    @staticmethod
    def _find_in_source_files(source_panel, query):
        """Matches in the variables each source file defines."""
        matches = []
        for option_text, file_path in source_panel.file_paths_by_option.items():
            for row_position, (folder_path, variable_name, value_text) in enumerate(source_panel.rows_of_file(file_path)):
                if query in variable_name.lower() or query in value_text.lower() or query in folder_path.lower():
                    matches.append((SOURCE_TAB_LABEL, source_panel, (option_text, row_position),
                                    (f"{SOURCE_TAB_LABEL}: {os.path.basename(file_path)}", value_text,
                                     variable_name, "", "")))
        return matches

    def _find_in_viewport_table(self, query):
        """Matches in the Viewports tab."""
        viewport_panel = self._viewport_panel
        if viewport_panel is None or not viewport_panel.winfo_exists():
            return []
        matches = []
        viewport_view = viewport_panel.viewport_view
        for row_id in viewport_view.get_children():
            viewport_text, file_path = (str(value) for value in viewport_view.item(row_id, "values"))
            if query in viewport_text.lower() or query in file_path.lower():
                matches.append((VIEWPORT_TAB_LABEL, viewport_view, row_id,
                                (f"{VIEWPORT_TAB_LABEL} table", "", viewport_text, "", "")))
        return matches

    @staticmethod
    def _find_all_row(function):
        """The five cells shown for one function: device type, arg, name, device id, action id."""
        helios_type = function.get("heliosType", "")
        device_id, action_id = best_effort_ids(function)
        return (TAB_LABELS.get(helios_type, helios_type.split(".")[-1]),
                str(first_export(function).get("id", "")),
                str(function.get("name", "")),
                device_id,
                action_id)

    def _show_find_all_results(self, query, matching_functions, matching_table_rows=()):
        """Open (or replace) the Find window: matching functions first, then matching
        table rows.  Double-click a row to jump to it (the function in its tab, or the row in
        its table)."""
        if self._find_all_window is not None and self._find_all_window.winfo_exists():
            self._find_all_window.destroy()      # recreated so it uses the current theme
        results_window = tk.Toplevel(self)
        self._find_all_window = results_window
        results_window.title(f"Find - '{query}'  ({len(matching_functions) + len(matching_table_rows)} found)")
        results_window.configure(bg=PANEL_BG)
        window_width, window_height = 760, 420
        position_x, position_y = centered_position_on_parent(self, window_width, window_height)
        results_window.geometry(f"{window_width}x{window_height}+{position_x}+{position_y}")
        results_view = self._build_find_results_view(results_window)
        for row_number, (function_index, function) in enumerate(matching_functions):
            results_view.insert("", "end", iid=str(function_index), values=self._find_all_row(function),
                                tags=("even" if row_number % 2 == 0 else "odd",))
        table_row_targets = {}                          # result row id -> (tab label, table view, row id)
        for row_number, (tab_label, table_view, table_row_id, cells) in enumerate(
                matching_table_rows, start=len(matching_functions)):
            result_row_id = results_view.insert("", "end", values=cells,
                                                tags=("even" if row_number % 2 == 0 else "odd",))
            table_row_targets[result_row_id] = (tab_label, table_view, table_row_id)

        def jump_to_selected_result(_event=None):
            """Double-click / Enter on a Find result."""
            self._jump_to_find_result(results_view, table_row_targets)

        results_view.bind("<Double-1>", jump_to_selected_result)
        results_view.bind("<Return>", jump_to_selected_result)
        tk.Label(results_window, text="Double-click a row to jump to it", bg=PANEL_BG, fg=TEXT_SEC,
                 font=FONT_UI).pack(side="left", padx=10, pady=(0, 8))

    def _build_find_results_view(self, results_window):
        """The empty results table (with its scroll bar) inside the Find window."""
        results_container = tk.Frame(results_window, bg=PANEL_BG)
        results_container.pack(fill="both", expand=True, padx=8, pady=8)
        vertical_scrollbar = ttk.Scrollbar(results_container, orient="vertical")
        column_ids = [column_id for column_id, _label, _width in self.FIND_ALL_COLUMNS]
        results_view = ttk.Treeview(results_container, columns=column_ids, show="headings",
                                    selectmode="browse", yscrollcommand=vertical_scrollbar.set)
        vertical_scrollbar.configure(command=results_view.yview)
        for column_id, column_label, column_width in self.FIND_ALL_COLUMNS:
            centered = column_id in ("arg", "deviceId", "actionId")
            results_view.heading(column_id, text=column_label, anchor="center" if centered else "w")
            results_view.column(column_id, width=column_width, minwidth=50, stretch=True,
                                anchor="center" if centered else "w")
        results_view.tag_configure("even", background=ROW_EVEN)
        results_view.tag_configure("odd", background=ROW_ODD)
        vertical_scrollbar.pack(side="right", fill="y")
        results_view.pack(side="left", fill="both", expand=True)
        return results_view

    def _jump_to_find_result(self, results_view, table_row_targets):
        """Show the selected Find result: that function in its tab, or that table row in its table."""
        selected_ids = results_view.selection()
        if not selected_ids:
            return
        if selected_ids[0] in table_row_targets:
            self._jump_to_table_row(*table_row_targets[selected_ids[0]])
            return
        function_index = int(selected_ids[0])
        if function_index >= len(self._data["functions"]):
            return                              # the profile changed since Find
        helios_type = self._data["functions"][function_index].get("heliosType", "")
        if helios_type not in TAB_LABELS:
            return                              # a type without its own tab
        self._select_tab(helios_type)
        self._select_function(helios_type, function_index)

    def _jump_to_table_row(self, tab_label, table_view, table_row_id):
        """Select a found row in its Tables tab (in the Source tab: a view option and row position)."""
        if isinstance(table_view, SourcePanel):
            if table_view.winfo_exists():
                self._select_tab_by_label(tab_label)
                table_view.show_view_and_select(*table_row_id)
            return
        if table_view.winfo_exists() and table_view.exists(table_row_id):
            self._select_tab_by_label(tab_label)
            table_view.selection_set(table_row_id)
            table_view.see(table_row_id)

    def _update_name(self, *_):
        """Show the profile name.  A name the file already has is never changed (opening and
        saving leave the "name" field as it was).  Only a profile with no name yet (a new one)
        gets '<type> <module>', which follows the type and module while it is being typed."""
        stored_name = self._data.get("name", "")
        if not stored_name or stored_name == getattr(self, "_last_auto_name", None):
            profile_type = self._header_vars["type"].get().strip()
            module = self._header_vars["module"].get().strip()
            stored_name = f"{profile_type} {module}".strip()
            self._data["name"] = stored_name
            self._last_auto_name = stored_name
        self._name_label.configure(text=stored_name)

    def _sync_header_to_data(self):
        """Copy the header fields into the profile data (vehicles split on commas)."""
        for key in ("source", "version", "commit", "type", "module"):
            self._data[key] = self._header_vars[key].get().strip()
        vehicles_str = self._header_vars["vehicles_str"].get().strip()
        self._data["vehicles"] = [vehicle.strip() for vehicle in vehicles_str.split(",") if vehicle.strip()]
        self._update_name(None)
        self._update_max_id()

    def _sync_data_to_header(self):
        """Show the active profile's header values (source, version, commit, type, module,
        vehicles) in the header fields, e.g. after opening a file or switching documents."""
        self._last_auto_name = None      # a name this profile already has is kept as it is
        for key in ("source", "version", "commit", "type", "module"):
            self._header_vars[key].set(self._data.get(key, ""))
        self._header_vars["vehicles_str"].set(", ".join(self._data.get("vehicles", [])))
        self._update_name()
        self._update_max_id()

    def _update_max_id(self):
        """Show "Max id used": the highest of the devices' Export IDs(Arg) and the Reference
        table's Arg # (the table works out its highest Arg # while it refreshes, so this
        costs one pass over the devices only)."""
        highest = max_id(self._data.get("functions", []))
        reference_panel = getattr(self, "_command_table_panel", None)
        if reference_panel is not None:
            highest = max(highest, reference_panel.highest_arg_number)
        max_id_label = getattr(self, "_max_id_label", None)
        if max_id_label is not None and max_id_label.winfo_exists():
            max_id_label.configure(text=str(highest))

    # ── tabs ───────────────────────────────────────────────────────────────────
    def _build_tabs(self):
        """Build the main tabs and their sub tabs:
             Devices           one sub tab per Helios type, then Collisions and Full View
             Tables            Current Data, Old References, Mismatched, Viewport, Source
             Argument Logger   the Change Tracker's sub tabs (see ArgumentLoggerPanel)
             Text Editor       embedded multi-document text editor
        The Reference / Old References tables and the viewport list keep their contents
        when the tabs are rebuilt (theme switch)."""
        self._document_tab_bars = []
        self._main_notebook = ttk.Notebook(self, style="Main.TNotebook")
        self._main_notebook.pack(fill="both", expand=True, padx=0, pady=0)
        self._trees = {}
        self._tab_count_labels = {}
        self._full_view_texts = []
        self._sort_method_var = tk.StringVar(master=self, value=self._sort_method)

        # ---- Devices: one sub tab per Helios type, then Collisions
        devices_frame = tk.Frame(self._main_notebook, bg=PANEL_BG)
        self._main_notebook.add(devices_frame, text=DEVICES_TAB_LABEL)
        self._devices_notebook = ttk.Notebook(devices_frame)
        self._devices_notebook.pack(fill="both", expand=True, padx=0, pady=(4, 0))
        for helios_type in HELIOS_TYPES:
            frame = tk.Frame(self._devices_notebook, bg=PANEL_BG)
            self._devices_notebook.add(frame, text=TAB_LABELS[helios_type])
            self._build_tab(frame, helios_type)
        # Collisions flags functions sharing an Export ID(Arg), or a Device ID + Action ID,
        # and highlights the shared value.
        collisions_frame = tk.Frame(self._devices_notebook, bg=PANEL_BG)
        self._devices_notebook.add(collisions_frame, text=COLLISIONS_TAB_LABEL)
        self._build_collisions_tab(collisions_frame)
        devices_full_view_frame = tk.Frame(self._devices_notebook, bg=PANEL_BG)
        self._devices_notebook.add(devices_full_view_frame, text=FULL_VIEW_TAB_LABEL)
        self._build_full_view_tab(devices_full_view_frame, document_tabs=True)

        # ---- Tables: Current Data, Old References, Mismatched, Viewport
        tables_frame = tk.Frame(self._main_notebook, bg=PANEL_BG)
        self._main_notebook.add(tables_frame, text=TABLES_TAB_LABEL)
        self._tables_notebook = ttk.Notebook(tables_frame)
        self._tables_notebook.pack(fill="both", expand=True, padx=0, pady=(4, 0))
        # The Reference table.  Its rows survive tab rebuilds through self._command_table_state.
        table_frame = tk.Frame(self._tables_notebook, bg=PANEL_BG)
        self._tables_notebook.add(table_frame, text=COMMAND_TABLE_TAB_LABEL)
        self._command_table_panel = CommandTablePanel(table_frame, self, self._command_table_state)
        self._command_table_panel.pack(fill="both", expand=True)
        self._command_table_state = None
        # Old References: the same table in the old role (no buttons), then the Mismatched list.
        old_reference_frame = tk.Frame(self._tables_notebook, bg=PANEL_BG)
        self._tables_notebook.add(old_reference_frame, text=OLD_REFERENCE_TAB_LABEL)
        self._old_reference_panel = CommandTablePanel(old_reference_frame, self, self._old_reference_state,
                                                      panel_role=OLD_REFERENCE_ROLE)
        self._old_reference_panel.pack(fill="both", expand=True)
        self._old_reference_state = None
        mismatched_frame = tk.Frame(self._tables_notebook, bg=PANEL_BG)
        self._tables_notebook.add(mismatched_frame, text=MISMATCHED_TAB_LABEL)
        self._mismatched_panel = MismatchedPanel(mismatched_frame, self)
        self._mismatched_panel.pack(fill="both", expand=True)
        self.schedule_reference_comparison()         # fill Mismatched / blue rows after a rebuild
        viewport_frame = tk.Frame(self._tables_notebook, bg=PANEL_BG)
        self._tables_notebook.add(viewport_frame, text=VIEWPORT_TAB_LABEL)
        self._viewport_panel = ViewportPanel(viewport_frame, self._viewport_calls)
        self._viewport_panel.pack(fill="both", expand=True)
        # Source: where each Reference row was found (after Viewport).
        source_frame = tk.Frame(self._tables_notebook, bg=PANEL_BG)
        self._tables_notebook.add(source_frame, text=SOURCE_TAB_LABEL)
        self._source_panel = SourcePanel(source_frame, self._source_rows, self._source_file_variables)
        self._source_panel.pack(fill="both", expand=True)

        # ---- Argument Logger: drawn by the logger, which keeps its data across rebuilds.
        argument_logger_frame = tk.Frame(self._main_notebook, bg=PANEL_BG)
        self._main_notebook.add(argument_logger_frame, text=ARGUMENT_LOGGING_TAB_LABEL)
        self._argument_logger.build_ui(argument_logger_frame)

        # ---- Text Editor: embedded editor with its own document tabs and scoped menu.
        self._text_editor_frame = tk.Frame(self._main_notebook, bg=PANEL_BG)
        self._main_notebook.add(self._text_editor_frame, text=TEXT_EDITOR_TAB_LABEL)
        self._text_editor = TextEditorPrototype(
            self,
            parent=self._text_editor_frame,
            embedded=True,
            theme=self._text_editor_theme(),
            create_initial_document=False,
        )
        if self._text_editor_state is None:
            self._text_editor.new_document(replace_on_open=True)
        else:
            self._text_editor.restore_state(self._text_editor_state)
            self._text_editor_state = None
        self._text_editor.notebook.bind("<<NotebookTabChanged>>", self._on_text_document_selected, add="+")
        self._install_live_sync()
        self._text_editor._build_menu(
            self._menu_bar,
            self._text_editor_menu_options,
            self._run_text_editor_action,
        )
        self._menu_bar.add_cascade(label="Options", menu=self._options_menu)

        # Auto-refresh Collisions / Full View whenever they become the visible tab
        # (a change of main tab can reveal them too, so all three notebooks report changes).
        for notebook in (self._main_notebook, self._devices_notebook, self._tables_notebook):
            notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)
        self._render_document_tabs()
        try:
            self._last_main_tab_label = self._main_notebook.tab(
                self._main_notebook.select(), "text")
        except tk.TclError:
            self._last_main_tab_label = ""

    def _sub_notebooks(self):
        """(main tab label, its sub notebook) for the main tabs that hold sub tabs."""
        return ((DEVICES_TAB_LABEL, getattr(self, "_devices_notebook", None)),
                (TABLES_TAB_LABEL, getattr(self, "_tables_notebook", None)))

    def _select_tab_by_label(self, tab_label, main_tab_label=None):
        """Bring the tab called tab_label to the front: a main tab, or a sub tab (its main
        tab is selected as well).  Returns True when the tab was found."""
        for main_label, sub_notebook in self._sub_notebooks():
            if main_tab_label is not None and main_label != main_tab_label:
                continue
            sub_index = self._tab_index_by_label(sub_notebook, tab_label)
            if sub_index is not None:
                self._select_tab_by_label(main_label)
                sub_notebook.select(sub_index)
                return True
        main_index = self._tab_index_by_label(self._main_notebook, tab_label)
        if main_index is not None:
            self._main_notebook.select(main_index)
            return True
        return False

    @staticmethod
    def _tab_index_by_label(notebook, tab_label):
        """The index of the tab with this text in a notebook (None when there is none, or no notebook)."""
        if notebook is None:
            return None
        for tab_index in range(notebook.index("end")):
            if notebook.tab(tab_index, "text") == tab_label:
                return tab_index
        return None

    def _build_collisions_tab(self, frame):
        """Build the Collisions tab: a description, a count and a scrollable area listing
        groups of functions that share ids or names."""
        toolbar = tk.Frame(frame, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)
        tk.Label(toolbar,
                 text="Functions sharing an Export ID(Arg), a Device ID + Action ID, or a Device + Name"
                      "   (double-click a row to go to it)",
                 bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left")
        tk.Button(toolbar, text="⟳  Refresh", bg=ACCENT, fg=DARK_BG, font=FONT_UI,
                  relief="flat", padx=12, pady=4, cursor="hand2",
                  command=self._refresh_collisions).pack(side="left", padx=(12, 0))
        self._collision_count_label = tk.Label(toolbar, text="", bg=PANEL_BG,
                                              fg=TEXT_SEC, font=FONT_UI)
        self._collision_count_label.pack(side="right")

        self._build_document_tabs(frame)
        container = tk.Frame(frame, bg=PANEL_BG)
        container.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        canvas = tk.Canvas(container, bg=PANEL_BG, highlightthickness=0)
        vertical_sb = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vertical_sb.set)
        vertical_sb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        inner = tk.Frame(canvas, bg=PANEL_BG)
        window_id = canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda event: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda event: canvas.itemconfig(window_id, width=event.width))
        self._collision_inner = inner
        self._refresh_collisions()

    @staticmethod
    def _collision_cells(entry):
        """The collision columns: ID, Name, Device Type, DeviceID, ActionID, plus
        a trailing Function label so each colliding row is identifiable."""
        export_id = first_export(entry).get("id", "")
        name = str(entry.get("name", "")).strip()
        device_type = TAB_LABELS.get(entry.get("heliosType", ""),
                                     entry.get("heliosType", "").split(".")[-1])
        device_id = get_primary_device_id(entry)
        action_id = get_primary_action_id(entry)
        function = " · ".join(part for part in (str(entry.get("device", "")).strip(),
                                                str(entry.get("name", "")).strip()) if part)
        return [str(export_id), name, str(device_type), str(device_id),
                str(action_id), function]

    @staticmethod
    def _group_by(functions, key_func):
        """Bucket functions by key_func(function), skipping falsy keys."""
        buckets = {}
        for function in functions:
            key = key_func(function)
            if key:
                buckets.setdefault(key, []).append(function)
        return buckets

    @staticmethod
    def _export_key(function):
        """Collision key for 'shared Export ID(Arg)': the function's first export id as text (''
        when it has none, which never collides)."""
        return str(first_export(function).get("id", "")).strip()

    @staticmethod
    def _device_action_key(function):
        """Collision key: a function's (Device ID, Action ID), or None when either is blank."""
        device_id = str(get_primary_device_id(function)).strip()
        action_id = str(get_primary_action_id(function)).strip()
        return (device_id, action_id) if device_id and action_id else None

    @staticmethod
    def _name_key(function):
        """The (Device, Name) pair. Two functions are treated as a duplicate-name
        collision only when BOTH their device and their name match."""
        device = str(function.get("device", "")).strip()
        name = str(function.get("name", "")).strip()
        return (device, name) if name else None

    @staticmethod
    def _find_collisions(functions):
        """Return collision groups. A group is 2+ functions that share either the
        same Export ID(Arg), the same (Device ID, Action ID) pair, or the same
        Device + Name (both must match). Each group names which column indices are
        shared so they can be highlighted."""
        def shared_device_name(device_and_name):
            """The device and name joined for display (empty parts left out)."""
            return " · ".join(part for part in device_and_name if part)

        collision_kinds = (                # (key function, label text of a key, highlighted columns)
            (HeliosEditor._export_key, lambda export_id: f"Shared Export ID(Arg): {export_id}", {0}),
            (HeliosEditor._device_action_key,
             lambda key: f"Shared Device ID + Action ID: {key[0]} / {key[1]}", {3, 4}),
            (HeliosEditor._name_key, lambda key: f"Shared Device + Name: {shared_device_name(key)}", {1}),
        )
        groups = []
        for key_function, label_of_key, highlighted_columns in collision_kinds:
            for shared_key, members in HeliosEditor._group_by(functions, key_function).items():
                if len(members) > 1:
                    groups.append({
                        "label": f"⚠  {label_of_key(shared_key)}   ({len(members)} functions)",
                        "entries": members,
                        "highlight": highlighted_columns,
                    })
        return groups

    @staticmethod
    def _collision_cell_style(shared):
        """(bg, fg, font) for a collision cell, emphasised when it's a shared
        (colliding) column."""
        if shared:
            return WARN, DARK_BG, FONT_HEAD
        return DARK_BG, TEXT_PRI, FONT_MONO

    def _render_collision_headers(self, inner, headers):
        """Draw the Collisions list's column headings (ID, Name, Device Type, DeviceID, ActionID,
        Function) in its first grid row."""
        for column, header in enumerate(headers):
            tk.Label(inner, text=header, bg=PANEL_BG, fg=ACCENT, font=FONT_HEAD,
                     anchor="w", padx=8, pady=4).grid(row=0, column=column, sticky="ew")
        inner.columnconfigure(len(headers) - 1, weight=1)

    def _render_collision_entry(self, inner, grid_row, entry, highlight, function_index=None):
        """Draw one function of a collision group; the shared columns are highlighted.
        Double-clicking any cell of the row goes to that function (see _go_to_function)."""
        for column, value in enumerate(self._collision_cells(entry)):
            cell_background, cell_foreground, cell_font = self._collision_cell_style(column in highlight)
            cell_label = tk.Label(inner, text=value, bg=cell_background, fg=cell_foreground, font=cell_font,
                                  anchor="w", padx=8, pady=2, cursor="hand2" if function_index is not None else "")
            cell_label.grid(row=grid_row, column=column, sticky="ew")
            if function_index is not None:
                cell_label.bind("<Double-1>", lambda event, index=function_index: self._go_to_function(index))

    def _go_to_function(self, function_index):
        """Show a function in its tab (Devices ▸ its type) and select it - used by the
        Collisions rows."""
        functions = self._data.get("functions", [])
        if not 0 <= function_index < len(functions):
            return                                     # the profile changed since the list was drawn
        helios_type = functions[function_index].get("heliosType", "")
        if helios_type in TAB_LABELS:
            self._select_tab(helios_type)
            self._select_function(helios_type, function_index)

    def _render_collision_group(self, inner, grid_row, group, header_count, index_by_function=None):
        """Draw a collision group's heading and its functions; returns the next free grid row.
        index_by_function (id(function) -> its position in the profile) lets each row jump."""
        tk.Label(inner, text=group["label"], bg=MID_BG, fg=WARN, font=FONT_HEAD,
                 anchor="w", padx=8, pady=3).grid(
                     row=grid_row, column=0, columnspan=header_count, sticky="ew", pady=(8, 0))
        grid_row += 1
        for entry in group["entries"]:
            self._render_collision_entry(inner, grid_row, entry, group["highlight"],
                                         (index_by_function or {}).get(id(entry)))
            grid_row += 1
        return grid_row

    def _show_no_collisions(self, inner, header_count):
        """Collisions tab with nothing to report: a single 'No collisions found' line across all
        columns and a zero count in the toolbar."""
        tk.Label(inner, text="✓  No collisions found.", bg=PANEL_BG, fg=SUCCESS,
                 font=FONT_UI, anchor="w", padx=8, pady=8).grid(
                     row=1, column=0, columnspan=header_count, sticky="w")
        self._collision_count_label.configure(text="0 collisions")

    def _refresh_collisions(self):
        """Rebuild the Collisions list from the current profile (only called while that tab is
        visible or being opened)."""
        inner = getattr(self, "_collision_inner", None)
        if inner is None:
            return
        for child in inner.winfo_children():
            child.destroy()

        headers = ["ID", "Name", "Device Type", "DeviceID", "ActionID", "Function"]
        self._render_collision_headers(inner, headers)

        groups = self._find_collisions(self._data["functions"])
        if not groups:
            self._show_no_collisions(inner, len(headers))
            return

        # each function's position in the profile (one pass), so a double-click can go to it
        index_by_function = {id(function): function_index
                             for function_index, function in enumerate(self._data["functions"])}
        grid_row = 1
        for group in groups:
            grid_row = self._render_collision_group(inner, grid_row, group, len(headers), index_by_function)

        plural = "s" if len(groups) != 1 else ""
        self._collision_count_label.configure(text=f"{len(groups)} collision group{plural}")

    def _build_full_view_tab(self, frame, document_tabs=False):
        """Build the Full View tab: a read-only text box showing the profile exactly as it
        would be saved, with a refresh button and, in JSON Controls, the profile tabs."""
        toolbar = tk.Frame(frame, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)
        tk.Label(toolbar, text="All devices in save-file format (read-only)",
                 bg=PANEL_BG, fg=TEXT_HEAD, font=FONT_HEAD).pack(side="left")
        tk.Button(toolbar, text="⟳  Refresh", bg=ACCENT, fg=DARK_BG, font=FONT_UI,
                  relief="flat", padx=12, pady=4, cursor="hand2",
                  command=self._refresh_full_view).pack(side="left", padx=(12, 0))

        # Sort-method toggle (also drives the order used when saving).
        tk.Label(toolbar, text="Sort:", bg=PANEL_BG, fg=TEXT_SEC,
                 font=FONT_UI).pack(side="left", padx=(18, 4))
        def on_toggle():
            """A sort-order option was picked in the Save dialog: remember it as the profile's sort
            method for this save."""
            self._set_sort_method(self._sort_method_var.get())

        short_labels = {"deviceaction": "Device ID + Action ID",
                        "devicename": "Device Name + Name (A→Z)"}
        for key in SORT_METHODS:
            tk.Radiobutton(toolbar, text=short_labels.get(key, key),
                           variable=self._sort_method_var, value=key, command=on_toggle,
                           bg=PANEL_BG, fg=TEXT_PRI, selectcolor=MID_BG,
                           activebackground=PANEL_BG, activeforeground=ACCENT,
                           font=FONT_UI).pack(side="left", padx=(0, 4))

        if document_tabs:
            self._build_document_tabs(frame)
        container = tk.Frame(frame, bg=PANEL_BG)
        container.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        vertical_sb = ttk.Scrollbar(container, orient="vertical")
        horizontal_sb = ttk.Scrollbar(container, orient="horizontal")
        text = tk.Text(container, wrap="none", bg=MID_BG, fg=TEXT_PRI,
                       insertbackground=TEXT_PRI, relief="flat", font=FONT_MONO,
                       yscrollcommand=vertical_sb.set, xscrollcommand=horizontal_sb.set,
                       highlightthickness=0, borderwidth=0)
        vertical_sb.configure(command=text.yview)
        horizontal_sb.configure(command=text.xview)
        vertical_sb.pack(side="right", fill="y")
        horizontal_sb.pack(side="bottom", fill="x")
        text.pack(side="left", fill="both", expand=True)

        self._full_view_texts.append(text)
        self._refresh_full_view()

    def _refresh_full_view(self):
        """Render the current profile in save-file JSON format into the Full
        View tabs' read-only text boxes."""
        texts = getattr(self, "_full_view_texts", ())
        if not texts:
            return
        try:
            content = json.dumps(self._build_save_payload(), indent=2)
        except Exception as error:                       # never let the view crash
            content = f"// Unable to render save view: {error}"
        for text in texts:
            if not text.winfo_exists():
                continue
            text.configure(state="normal")
            text.delete("1.0", "end")
            text.insert("1.0", content)
            text.configure(state="disabled")

    def _build_tab(self, frame, helios_type):
        """Build one Helios type's tab: its toolbar (add, edit, duplicate, delete, change
        type), shared profile tabs below the toolbar, a device count and a sortable table with
        double-click editing and a right-click menu."""
        toolbar = tk.Frame(frame, bg=PANEL_BG, pady=6)
        toolbar.pack(fill="x", padx=8)

        tk.Button(toolbar, text="＋  Add Entry", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=12, pady=4, cursor="hand2",
                  command=lambda chosen_type=helios_type: self._add_entry(chosen_type)).pack(side="left", padx=(0, 6))
        tk.Button(toolbar, text="✎  Edit", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI,
              relief="flat", padx=12, pady=4, cursor="hand2",
              command=lambda chosen_type=helios_type: self._edit_entry(chosen_type)).pack(side="left", padx=(0, 6))
        tk.Button(toolbar, text="#  Change Device ID", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI,
              relief="flat", padx=12, pady=4, cursor="hand2",
              command=lambda chosen_type=helios_type: self._change_device_id(chosen_type)).pack(side="left", padx=(0, 6))
        tk.Button(toolbar, text="⎘  Duplicate Last", image=self._last_saved_star_image, compound="right",
              bg=MID_BG, fg=TEXT_PRI, font=FONT_UI,
              relief="flat", padx=12, pady=4, cursor="hand2",
              activeforeground=TEXT_PRI, command=lambda chosen_type=helios_type: duplicate_last(self, chosen_type)).pack(side="left", padx=(0, 6))
        tk.Button(toolbar, text="⎘  Duplicate Selected", bg=MID_BG, fg=TEXT_PRI, font=FONT_UI,
              relief="flat", padx=12, pady=4, cursor="hand2",
              command=lambda chosen_type=helios_type: duplicate_selected(self, chosen_type)).pack(side="left", padx=(0, 6))
        tk.Button(toolbar, text="✕  Delete", bg=DANGER_BG, fg=DANGER_FG, font=FONT_UI,
                  relief="flat", padx=12, pady=4, cursor="hand2",
                  command=lambda chosen_type=helios_type: self._delete_entry(chosen_type)).pack(side="left", padx=(0, 6))
        tk.Button(toolbar, text="⇄  Change Type", bg=MID_BG, fg=ACCENT2, font=FONT_UI,
                  relief="flat", padx=12, pady=4, cursor="hand2",
                  command=lambda chosen_type=helios_type: self._change_type(chosen_type)).pack(side="left", padx=(0, 6))

        tk.Label(toolbar, text="Click a column header to sort by value", bg=PANEL_BG, fg=TEXT_SEC,
                 font=FONT_UI).pack(side="left", padx=(16, 4))


        # Count of how many functions of this type (updated on every refresh).
        count_label = tk.Label(toolbar, text="", bg=PANEL_BG, fg=ACCENT2, font=FONT_HEAD)
        count_label.pack(side="right", padx=(8, 8))
        self._tab_count_labels[helios_type] = count_label

        self._build_document_tabs(frame)
        # Treeview
        columns = get_columns(helios_type)
        column_ids = [column[0] for column in columns]
        display_column_ids = ["device"] + [column_id for column_id in column_ids if column_id != "device"]

        container = tk.Frame(frame, bg=PANEL_BG)
        container.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        vertical_sb = ttk.Scrollbar(container, orient="vertical")
        horizontal_sb = ttk.Scrollbar(container, orient="horizontal")

        tree = ttk.Treeview(container, columns=column_ids, displaycolumns=display_column_ids,
                            show="tree headings",
                            yscrollcommand=vertical_sb.set, xscrollcommand=horizontal_sb.set,
                            selectmode="extended")
        tree.heading("#0", text="")
        tree.column("#0", width=24, minwidth=24, stretch=False, anchor="center")
        vertical_sb.configure(command=tree.yview)
        horizontal_sb.configure(command=tree.xview)

        for column_id, column_label, column_width in columns:
            centered = column_id in CENTERED_COLUMNS
            heading_kwargs = {
                "text": column_label,
                "command": lambda sort_column=column_id, chosen_type=helios_type: self._sort_by_column(chosen_type, sort_column),
            }
            column_kwargs = {"width": column_width, "minwidth": 50, "stretch": True}
            if centered:
                heading_kwargs["anchor"] = "center"
                column_kwargs["anchor"] = "center"
            tree.heading(column_id, **heading_kwargs)
            tree.column(column_id, **column_kwargs)

        tree.tag_configure("even", background=ROW_EVEN)
        tree.tag_configure("odd",  background=ROW_ODD)

        tree.bind("<Double-1>", lambda event, chosen_type=helios_type: self._edit_entry(chosen_type))
        tree.bind("<FocusIn>", lambda event, chosen_type=helios_type: self._remember_tree_focus(chosen_type))
        tree.bind("<Button-3>",
              lambda event, chosen_type=helios_type, chosen_tree=tree: self._show_tree_context_menu(event, chosen_type, chosen_tree))

        vertical_sb.pack(side="right",  fill="y")
        horizontal_sb.pack(side="bottom", fill="x")
        tree.pack(side="left",  fill="both", expand=True)

        self._trees[helios_type] = tree

    def _remember_tree_focus(self, helios_type):
        """Remember which type's table was used last (for copy / paste)."""
        self._last_focused_tree_type = helios_type

    def _tree_for_focus(self):
        """Which device table the keyboard focus (or the last click) is in, as (type, table), for
        Copy / Paste; (None, None) when it is not in a device table."""
        focused = self.focus_get()
        for helios_type, tree in self._trees.items():
            if focused is tree:
                return helios_type, tree
        return None, None

    def _copy_selected_functions(self, _event=None, helios_type=None, tree=None):
        """Copy the selected functions of a table to the editor's clipboard."""
        if tree is None:
            helios_type, tree = self._tree_for_focus()
        if tree is None:
            return
        indices = self._selected_indices(tree)
        if not indices:
            return
        self._clipboard_functions = [
            copy.deepcopy(self._data["functions"][index]) for index in indices
        ]
        self._clipboard_type = helios_type

    def _cut_selected_functions(self, _event=None, helios_type=None, tree=None):
        """Copy the selected functions, then remove them with one undoable change."""
        if tree is None:
            helios_type, tree = self._tree_for_focus()
        if tree is None:
            return
        indices = self._selected_indices(tree)
        if not indices:
            return "break"
        self._clipboard_functions = [
            copy.deepcopy(self._data["functions"][index]) for index in indices
        ]
        self._clipboard_type = helios_type
        self._push_undo_state()
        for index in sorted(indices, reverse=True):
            self._data["functions"].pop(index)
        self._refresh_all()
        return "break"

    def _paste_functions(self, _event=None, target_type=None):
        """Paste the copied functions (as new functions, with an undo step); ignored while
        typing in a text box."""
        focused = self.focus_get()
        if target_type is None and isinstance(focused, (tk.Entry, tk.Text, ttk.Entry, ttk.Combobox)):
            return
        if not self._clipboard_functions:
            return
        helios_type = self._clipboard_type
        if helios_type not in self._trees:
            return
        pasted = self._renamed_copies_of_clipboard()
        for function in pasted:
            function[ADDED_FLAG] = True
        self._push_undo_state()
        self._data["functions"].extend(pasted)
        self._sort_functions()
        self._refresh_all()
        self._select_tab(helios_type)
        pasted_indices = [
            index for index, function in enumerate(self._data["functions"])
            if any(function is pasted_function for pasted_function in pasted)
        ]
        self._select_functions(helios_type, pasted_indices)

    def _renamed_copies_of_clipboard(self):
        """Copies of the clipboard functions; a name already used by the same device gets ': copy N'."""
        pasted = copy.deepcopy(self._clipboard_functions)
        existing_names = {
            (str(function.get("device", "")), str(function.get("name", "")))
            for function in self._data["functions"]
        }
        for function in pasted:
            base_name = str(function.get("name", ""))
            device = str(function.get("device", ""))
            candidate = base_name
            copy_number = 1
            while (device, candidate) in existing_names and base_name:
                candidate = f"{base_name}: copy {copy_number}"
                copy_number += 1
            if base_name:
                function["name"] = candidate
            existing_names.add((device, candidate))
        return pasted

    def _make_undo_snapshot(self):
        """A copy of everything an undo step must restore."""
        self._sync_header_to_data()
        return {
            "data": copy.deepcopy(self._data),
            "last_added_device": self._last_added_device,
            "last_added_device_id": self._last_added_device_id,
            "last_added_function": copy.deepcopy(self._last_added_function),
            "last_saved_function": copy.deepcopy(self._last_saved_function),
            "next_saved_session_index": self._next_saved_session_index,
            "next_created_session_index": self._next_created_session_index,
            "sort_method": self._sort_method,
        }

    def _push_undo_state(self):
        """Record the current profile and session state before a new change."""
        self._undo_stack.append(self._make_undo_snapshot())
        self._redo_stack.clear()

    def _restore_undo_snapshot(self, snapshot):
        """Put back the state saved by _make_undo_snapshot."""
        self._data = copy.deepcopy(snapshot["data"])
        self._last_added_device = snapshot["last_added_device"]
        self._last_added_device_id = snapshot["last_added_device_id"]
        self._last_added_function = copy.deepcopy(snapshot["last_added_function"])
        self._last_saved_function = copy.deepcopy(snapshot["last_saved_function"])
        self._next_saved_session_index = snapshot["next_saved_session_index"]
        self._next_created_session_index = snapshot["next_created_session_index"]
        self._sort_method = snapshot["sort_method"]
        sort_method_var = getattr(self, "_sort_method_var", None)
        if sort_method_var is not None and sort_method_var.get() != self._sort_method:
            sort_method_var.set(self._sort_method)
        self._sync_data_to_header()
        self._refresh_all()
        self._capture_active_document()
        self._render_document_tabs()

    def _undo(self, _event=None):
        """Undo the last profile change; ignored while typing in a text box."""
        focused = self.focus_get()
        if isinstance(focused, (tk.Entry, tk.Text, ttk.Entry, ttk.Combobox)):
            return
        if not self._undo_stack:
            return
        self._redo_stack.append(self._make_undo_snapshot())
        self._restore_undo_snapshot(self._undo_stack.pop())

    def _redo(self, _event=None):
        """Redo the most recently undone profile change; ignored while typing in a text box."""
        focused = self.focus_get()
        if isinstance(focused, (tk.Entry, tk.Text, ttk.Entry, ttk.Combobox)):
            return
        if not self._redo_stack:
            return
        self._undo_stack.append(self._make_undo_snapshot())
        self._restore_undo_snapshot(self._redo_stack.pop())

    def _show_tree_context_menu(self, event, helios_type, tree):
        """Show the device actions in a menu styled like the Text Editor context menu."""
        item_id = tree.identify_row(event.y)
        if item_id and item_id not in tree.selection():
            tree.selection_set(item_id)
        tree.focus_set()
        has_selection = bool(tree.selection())
        text_widget = self._text_editor._active_text()
        if text_widget is None:
            return "break"
        text_context_menu = text_widget.master.context_menu
        menu_style = {
            option: text_context_menu.cget(option)
            for option in (
                "bg",
                "fg",
                "activebackground",
                "activeforeground",
                "disabledforeground",
                "font",
                "relief",
                "borderwidth",
                "activeborderwidth",
            )
        }
        menu = tk.Menu(text_widget, tearoff=False, **menu_style)
        menu.add_command(
            label="Cut",
            accelerator="Ctrl+X",
            state="normal" if has_selection else "disabled",
            command=lambda: self._cut_selected_functions(
                helios_type=helios_type, tree=tree))
        menu.add_command(
            label="Copy",
            accelerator="Ctrl+C",
            state="normal" if has_selection else "disabled",
            command=lambda: self._copy_selected_functions(
                helios_type=helios_type, tree=tree))
        menu.add_command(
            label="Paste",
            accelerator="Ctrl+V",
            state="normal" if self._clipboard_functions else "disabled",
            command=lambda: self._paste_functions(target_type=helios_type))
        menu.add_separator()
        menu.add_command(
            label="Undo",
            accelerator="Ctrl+Z",
            state="normal" if self._undo_stack else "disabled",
            command=self._undo)
        menu.add_command(
            label="Redo",
            accelerator="Ctrl+Y",
            state="normal" if self._redo_stack else "disabled",
            command=self._redo)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()
        return "break"

    # ── data ops ───────────────────────────────────────────────────────────────
    def _entries_for(self, helios_type):
        """(index, function) for every function of one type, in profile order."""
        return [(index, function) for index, function in enumerate(self._data["functions"])
                if function.get("heliosType") == helios_type]

    def _sort_functions(self):
        """Sort the in-memory functions by device id then action id (the same
        order used when saving), so the grids stay ordered as soon as anything
        is added. Re-sorting renumbers every function's index, so callers must
        rebuild all tabs (not just one) afterward."""
        self._data["functions"].sort(key=device_action_sort_key)

    def _ask_description_scope(self):
        """Set Descriptions: ask whether to set the open device sub tab only or the full profile.
        Returns "device", "full" or None (cancelled)."""
        dialog = tk.Toplevel(self)
        dialog.transient(self)
        dialog.title("Set Descriptions")
        dialog.configure(bg=DARK_BG)
        dialog.resizable(False, False)
        dialog.grab_set()
        tk.Label(dialog, text="Set the descriptions for:", bg=DARK_BG, fg=TEXT_HEAD,
                 font=FONT_HEAD).pack(anchor="w", padx=18, pady=(16, 10))
        result = {"scope": None}

        def choose(scope):
            """A scope button was clicked: remember it and close."""
            result["scope"] = scope
            dialog.destroy()

        buttons = tk.Frame(dialog, bg=DARK_BG)
        buttons.pack(fill="x", padx=18, pady=(0, 16))
        tk.Button(buttons, text="Device Only", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat",
                  padx=16, pady=6, cursor="hand2", command=lambda: choose("device")).pack(side="left")
        tk.Button(buttons, text="Full Profile", bg=ACCENT2, fg=DARK_BG, font=FONT_HEAD, relief="flat",
                  padx=16, pady=6, cursor="hand2", command=lambda: choose("full")).pack(side="left", padx=(8, 0))
        tk.Button(buttons, text="Cancel", bg=MID_BG, fg=TEXT_SEC, font=FONT_UI, relief="flat",
                  padx=16, pady=6, cursor="hand2", command=dialog.destroy).pack(side="left", padx=(8, 0))
        dialog.update_idletasks()
        position_x, position_y = centered_position_on_parent(self, dialog.winfo_reqwidth(), dialog.winfo_reqheight())
        dialog.geometry(f"+{position_x}+{position_y}")
        self.wait_window(dialog)
        return result["scope"]

    def _open_device_sub_tab_type(self):
        """The Helios type of the open Devices sub tab, or None when the open sub tab is not a
        device type (e.g. Collisions)."""
        notebook = getattr(self, "_devices_notebook", None)
        if notebook is None:
            return None
        try:
            open_label = notebook.tab(notebook.select(), "text")
        except tk.TclError:
            return None
        return next((helios_type for helios_type, label in TAB_LABELS.items() if label == open_label), None)

    def _apply_descriptions(self):
        """Set Descriptions button: ask Device Only (the open device sub tab) or Full Profile
        (every device), then set the descriptions from DESCRIPTION_BY_TYPE for that scope."""
        scope = self._ask_description_scope()
        if scope is None:
            return
        only_type = None
        if scope == "device":
            only_type = self._open_device_sub_tab_type()
            if only_type is None:
                messagebox.showinfo("Set Descriptions",
                                    "Open a device sub tab (for example Push Button) first, or choose Full Profile.",
                                    parent=self)
                return
        self._set_descriptions(only_type)

    def _set_descriptions(self, only_type=None):
        """Set every function's description from DESCRIPTION_BY_TYPE, keyed by its helios type
        (only the functions of only_type when it is given). ScaledNetworkValue (mapped to
        None) is left untouched, so it stays blank as before."""
        self._sync_header_to_data()
        self._push_undo_state()
        changed = 0
        for function in self._data["functions"]:
            if only_type is not None and function.get("heliosType", "") != only_type:
                continue
            desc = DESCRIPTION_BY_TYPE.get(function.get("heliosType", ""))
            if desc is None:                 # ScaledNetworkValue / unknown: leave as-is
                continue
            if function.get("description", "") != desc:
                function["description"] = desc
                changed += 1
        self._refresh_all()
        where = f"the {TAB_LABELS[only_type]} tab" if only_type is not None else "the full profile"
        messagebox.showinfo(
            "Set Descriptions",
            f"Updated {changed} description"
            f"{'s' if changed != 1 else ''} in {where}.",
            parent=self)

    def profile_device_names(self):
        """Every device name used in the profile, alphabetically, without repeats."""
        names = {str(function.get("device", "")).strip() for function in self._data.get("functions", [])}
        return sorted((name for name in names if name), key=str.lower)

    def _change_device_id(self, helios_type):
        """Change Device ID button: list the devices selected in this tab (all of the tab's devices
        when none is selected) in a Selection window, and open the Change Device ID dialog."""
        existing_window = getattr(self, "_change_device_dialog", None)
        if existing_window is not None and existing_window.winfo_exists():
            existing_window.close()
        tree = self._trees[helios_type]
        indices = self._selected_indices(tree)
        if not indices:
            indices = [int(tree.item(item_id, "tags")[0]) for item_id in tree.get_children()
                       if tree.item(item_id, "tags")]
        functions = [self._data["functions"][index] for index in indices]
        if not functions:
            messagebox.showinfo("Change Device ID", "There are no devices in this tab.", parent=self)
            return
        entries = []
        for position, function in enumerate(functions):
            entries.append((str(position), {
                "Arg#": str(first_export(function).get("id", "")), "Name": function.get("name", ""),
                "Device": function.get("device", ""), "Device ID": str(get_primary_device_id(function)),
                "Type": TAB_LABELS.get(function.get("heliosType", ""), ""),
                "Action ID": str(get_primary_action_id(function)), "_function": function}))
        selection_window = SelectionWindow(self, entries, CHANGE_DEVICE_COLUMNS, CHANGE_DEVICE_COLUMN_WIDTHS)
        dialog = ChangeDeviceIdDialog(self, selection_window, self.profile_device_names())
        self._change_device_dialog = dialog
        center_over(self, dialog)
        place_beside(dialog, selection_window, "right")

    def apply_device_change(self, functions, new_name, new_id):
        """Give each of `functions` the device name new_name and (when not blank) the device ID
        new_id, as one undo step; entries that are no longer in the profile are skipped.
        Returns how many were changed."""
        live = [function for function in functions
                if any(function is current for current in self._data["functions"])]
        if not live:
            return 0
        self._push_undo_state()
        for function in live:
            function["device"] = new_name
            if new_id:
                set_primary_device_id(function, new_id)
        self._sort_functions()
        self._refresh_all()
        self._update_max_id()
        return len(live)

    def _mark_saved(self, function):
        """`function` was just added or edited: it gets the star of its device category (the star
        stays on it until another function of that category is added or edited)."""
        function["_saved_session_index"] = self._next_saved_session_index
        self._next_saved_session_index += 1
        self._last_saved_function = function

    def _add_entry(self, helios_type):
        """Add Entry: open the Add dialog (pre-filled with the last device used) and add the
        result with an undo step."""
        self._sync_header_to_data()
        # Pre-fill the device name + id with whatever was on the last entry added
        # this session, so a run of additions to the same device doesn't require
        # retyping it each time.
        seed = None
        if self._last_added_device or self._last_added_device_id:
            seed = make_blank_entry(helios_type)
            seed["device"] = self._last_added_device
            set_primary_device_id(seed, self._last_added_device_id)
        dialog = EntryDialog(self, f"Add — {TAB_LABELS[helios_type]}", helios_type,
                             existing=seed, functions=self._data["functions"])
        self.wait_window(dialog)
        if dialog.result:
            self._push_undo_state()
            self._data["functions"].append(dialog.result)
            dialog.result[ADDED_FLAG] = True
            self._mark_saved(dialog.result)
            # Remember this entry for future Add / Duplicate actions.
            self._last_added_device = dialog.result.get("device", "")
            self._last_added_device_id = get_primary_device_id(dialog.result)
            self._last_added_function = dialog.result
            # Re-sort by device id then action id on every add. This reorders the
            # whole list, so refresh all tabs to rebuild their row indices.
            self._sort_functions()
            self._refresh_all()

    def _edit_entry(self, helios_type):
        """Edit the selected function in the Edit dialog and store the changes with an undo
        step."""
        tree = self._trees[helios_type]
        selection = tree.selection()
        if not selection:
            messagebox.showinfo("No Selection", "Select a row to edit.", parent=self)
            return
        if len(selection) > 1:
            messagebox.showinfo("Select One",
                                "Edit works on a single row — select just one.\n"
                                "(Use Change Type to retype several at once.)",
                                parent=self)
            return
        item_id = selection[0]
        tags = tree.item(item_id, "tags")
        function_index = int(tags[0]) if tags else -1
        if function_index < 0:
            return
        entry = self._data["functions"][function_index]
        dialog = EntryDialog(self, f"Edit — {TAB_LABELS[helios_type]}", helios_type, existing=entry,
                             functions=self._data["functions"], edit_index=function_index)
        self.wait_window(dialog)
        if dialog.result:
            self._push_undo_state()
            if entry.get(ADDED_FLAG):            # still added since the last save after an edit
                dialog.result[ADDED_FLAG] = True
            self._mark_saved(dialog.result)
            self._data["functions"][function_index] = dialog.result
            self._refresh_all()

    @staticmethod
    def _selected_indices(tree):
        """Function indices behind the currently selected rows of `tree`
        (each row stores its index as its first tag)."""
        indices = []
        for item_id in tree.selection():
            tags = tree.item(item_id, "tags")
            index = int(tags[0]) if tags else -1
            if index >= 0:
                indices.append(index)
        return indices

    def _delete_prompt(self, indices):
        """The confirmation question for Delete: names the function when one is selected, or gives
        the count when several are."""
        if len(indices) == 1:
            entry = self._data["functions"][indices[0]]
            return (f"Delete '{entry.get('name','')}' ({entry.get('device','')})?"
                    "\nThis cannot be undone.")
        return f"Delete {len(indices)} selected function(s)?\nThis cannot be undone."

    def _delete_entry(self, helios_type):
        """Delete the selected functions after confirmation (with an undo step)."""
        indices = self._selected_indices(self._trees[helios_type])
        if not indices:
            messagebox.showinfo("No Selection", "Select one or more rows to delete.",
                                parent=self)
            return
        if messagebox.askyesno("Confirm Delete", self._delete_prompt(indices), parent=self):
            self._push_undo_state()
            # Pop from the highest index down so earlier indices stay valid.
            for index in sorted(indices, reverse=True):
                self._data["functions"].pop(index)
            # Removal renumbers every function, so rebuild all tabs.
            self._refresh_all()

    def _ask_new_type(self, indices):
        """Prompt for the destination type for the selected rows; returns the
        chosen helios type, or None if the dialog was cancelled."""
        first_entry = self._data["functions"][indices[0]]
        dialog = ChangeTypeDialog(self, first_entry, count=len(indices))
        self.wait_window(dialog)
        return dialog.result

    @staticmethod
    def _carried_device_kept(carried_device, new_entry):
        """Change Type: True when the converted function still has the device id it had before, so
        the message can say the id was carried over."""
        return (carried_device not in ("", None)
                and get_primary_device_id(new_entry) not in ("", None))

    @staticmethod
    def _carried_action_kept(carried_action, new_entry):
        """Change Type: True when the converted function still has the action id it had before, so
        the message can say the id was carried over."""
        return (carried_action not in ("", None)
                and get_primary_action_id(new_entry) not in ("", None))

    def _convert_indices_to_type(self, indices, new_type):
        """Convert each function at `indices` to `new_type` in place, skipping
        ones already of that type. Returns (converted, kept_device, kept_action)."""
        converted = 0
        kept_device = False
        kept_action = False
        for index in indices:
            entry = self._data["functions"][index]
            if entry.get("heliosType", "") == new_type:
                continue
            carried_device = get_primary_device_id(entry)
            carried_action = get_primary_action_id(entry)
            new_entry = convert_entry_type(entry, new_type)
            self._mark_saved(new_entry)          # new in its category: it takes that category's star
            self._data["functions"][index] = new_entry
            converted += 1
            if self._carried_device_kept(carried_device, new_entry):
                kept_device = True
            if self._carried_action_kept(carried_action, new_entry):
                kept_action = True
        return converted, kept_device, kept_action

    @staticmethod
    def _carried_ids_note(kept_device, kept_action):
        """Change Type: the sentence telling which ids (device id, action id, both or none) the
        converted functions kept, for the confirmation message."""
        if kept_device and kept_action:
            return ", plus the device and action IDs.\n\n"
        if kept_device:
            return ", plus the device ID.\n\n"
        if kept_action:
            return ", plus the action ID.\n\n"
        return ".\n\n"

    def _show_type_changed(self, converted, new_type, indices, kept_device, kept_action):
        """Tell the user what Change Type did (how many functions, and which ids were kept)."""
        if converted == 1:
            head = (f"'{self._data['functions'][indices[0]].get('name','')}' "
                    f"is now a {TAB_LABELS[new_type]}.")
        else:
            head = f"Changed {converted} function(s) to {TAB_LABELS[new_type]}."
        note = self._carried_ids_note(kept_device, kept_action)
        messagebox.showinfo(
            "Type Changed",
            head + "\n\nKept: device, name and Export ID(Arg)" + note
            + "Description was reset to the new type's default. Other fields were reset to defaults — use Edit to fill them in.",
            parent=self)

    def _change_type(self, helios_type):
        """Change the helios type of every selected function. Preserves common
        fields + export id, resets type-specific fields, then moves the rows to
        the destination type's tab and selects them there."""
        indices = self._selected_indices(self._trees[helios_type])
        if not indices:
            messagebox.showinfo("No Selection",
                                "Select one or more rows to change their type.",
                                parent=self)
            return

        new_type = self._ask_new_type(indices)
        if not new_type:
            return

        self._push_undo_state()
        converted, kept_device, kept_action = self._convert_indices_to_type(indices, new_type)
        if converted == 0:
            messagebox.showinfo("No Change",
                                "The selected function(s) are already that type.",
                                parent=self)
            return

        # The rows leave the old tab and appear in the new type's tab.
        self._refresh_tab(helios_type)
        self._refresh_tab(new_type)
        # Surface the converted entries where the user can see them.
        self._select_tab(new_type)
        self._select_functions(new_type, indices)
        self._show_type_changed(converted, new_type, indices, kept_device, kept_action)

    def _select_tab(self, helios_type):
        """Bring the tab for helios type `helios_type` to the front (Devices ▸ that type)."""
        self._select_tab_by_label(TAB_LABELS[helios_type])

    def _select_function(self, helios_type, function_index):
        """Select (and scroll to) the row whose function index is `function_index`
        in the tree for helios type `helios_type`."""
        tree = self._trees.get(helios_type)
        if tree is None:
            return
        for item_id in tree.get_children():
            tags = tree.item(item_id, "tags")
            if tags and tags[0] == str(function_index):
                tree.selection_set(item_id)
                tree.focus(item_id)
                tree.see(item_id)
                return

    def _select_functions(self, helios_type, function_indices):
        """Select (and scroll to) every row whose function index is in
        `function_indices`, in the tree for helios type `helios_type`."""
        tree = self._trees.get(helios_type)
        if tree is None:
            return
        wanted = {str(index) for index in function_indices}
        to_select = []
        for item_id in tree.get_children():
            tags = tree.item(item_id, "tags")
            if tags and tags[0] in wanted:
                to_select.append(item_id)
        if to_select:
            tree.selection_set(to_select)
            tree.focus(to_select[0])
            tree.see(to_select[0])

    def _sort_by_column(self, helios_type, column):
        """Column header clicked: sort that type's table by the column (again to reverse)."""
        previous = self._sort_column_by_type.get(helios_type, (None, False))
        reverse = (not previous[1]) if previous[0] == column else False
        self._sort_column_by_type[helios_type] = (column, reverse)
        self._refresh_tab(helios_type)

    # ── refresh ────────────────────────────────────────────────────────────────
    @staticmethod
    def _tab_sort_key(function, sort_column):
        """Sort key for a flattened entry within a type tab. ID columns sort
        numerically (blank / non-numeric last); other columns sort
        case-insensitively; with no sort column, sort by device then name."""
        flat = flatten_entry(function)
        if not sort_column:
            return (
                0,
                0,
                f"{str(flat.get('device', '')).lower()}\x00{str(flat.get('name', '')).lower()}",
            )
        raw_text = flat.get(sort_column, "")
        if sort_column not in ID_COLUMNS:
            return (0, 0, str(raw_text).lower())
        text = str(raw_text).strip()
        if text.lstrip("+-").isdigit():
            return (0, int(text), "")
        return (1, 0, text.lower())

    def _update_tab_count(self, helios_type, count):
        """Show in a type's tab toolbar how many functions of that type the profile holds (e.g. "12
        Switches"), called whenever the tab is refreshed."""
        count_label = self._tab_count_labels.get(helios_type)
        if count_label is None:
            return
        plural = "" if count == 1 else "s"
        count_label.configure(text=f"{count} {TAB_LABELS[helios_type]}{plural}")

    def _row_values(self, function, latest_entry, column_ids):
        """Build the display tuple for one grid row. Device/Name are prettified
        for display only; the stored values are left untouched, and the most
        recently saved function gets a ★ marker."""
        flat = flatten_entry(function)
        display = dict(flat)
        device_label = prettify_label(flat.get("device", ""))
        if function is latest_entry:
            device_label = f"  {device_label}"
        display["device"] = device_label
        display["name"] = prettify_label(flat.get("name", ""))
        return tuple(display.get(column_id, "") for column_id in column_ids)

    def _refresh_tab(self, helios_type, entries=None, latest_entry=None):
        """Rebuild one device tab's rows.  `entries` / `latest_entry` are passed in by
        _refresh_all (worked out for every type in a single pass); when called on its own
        (e.g. after a header click) the tab finds its own entries."""
        tree = self._trees[helios_type]
        if entries is None:
            entries = self._entries_for(helios_type)
            latest_entry = find_last_saved_function(self, helios_type)
        self._update_tab_count(helios_type, len(entries))

        sort_column, reverse = self._sort_column_by_type.get(helios_type, (None, False))
        entries_sorted = sorted(
            entries, key=lambda index_and_function: self._tab_sort_key(index_and_function[1], sort_column),
            reverse=reverse)

        tree.delete(*tree.get_children())
        column_ids = [column[0] for column in get_columns(helios_type)]
        for row_number, (function_index, function) in enumerate(entries_sorted):
            values = self._row_values(function, latest_entry, column_ids)
            shade = "even" if row_number % 2 == 0 else "odd"
            tree.insert("", "end", values=values,
                        image=self._last_saved_star_image if function is latest_entry else "",
                        tags=(str(function_index), shade))

    def table_added_match_keys(self):
        """For the Table tab's Added column: every id combination held by a device of the
        profile (build_added_match_keys), built once and reused until the profile changes."""
        if self._added_match_keys is None:
            self._added_match_keys = build_added_match_keys(self._data.get("functions", []))
        return self._added_match_keys

    def add_built_device(self, new_function, review_first):
        """Add a device made by Build Device.  review_first opens the normal Add dialog
        pre-filled with it (all the usual checks); otherwise it is added as it is.
        Returns True when a device was added."""
        helios_type = new_function.get("heliosType", "")
        added_function = new_function
        if review_first:
            dialog = EntryDialog(self, f"Add — {TAB_LABELS[helios_type]}", helios_type,
                                 existing=new_function, functions=self._data["functions"])
            self.wait_window(dialog)
            added_function = dialog.result
        if not added_function:
            return False
        # same bookkeeping as _add_entry (including an Undo step)
        self._push_undo_state()
        self._data["functions"].append(added_function)
        added_function[ADDED_FLAG] = True
        self._mark_saved(added_function)
        self._last_added_device = added_function.get("device", "")
        self._last_added_device_id = get_primary_device_id(added_function)
        self._last_added_function = added_function
        self._sort_functions()
        self._refresh_all()                    # also turns the table row green
        return True

    def _entries_and_latest_by_type(self):
        """One pass over the profile: every function grouped by its type (with its index),
        and each type's most recently saved function (the one shown with a star).
        Replaces one full scan per type for the entries plus one per type for the star.
        The star rule matches find_last_saved_function: highest _saved_session_index,
        else the editor's last saved function when it has that type."""
        entries_by_type = {helios_type: [] for helios_type in HELIOS_TYPES}
        latest_by_type, latest_session_index = {}, {}
        for function_index, function in enumerate(self._data.get("functions", [])):
            helios_type = function.get("heliosType")
            type_entries = entries_by_type.get(helios_type)
            if type_entries is None:
                continue
            type_entries.append((function_index, function))
            saved_session_index = function.get("_saved_session_index", -1)
            if saved_session_index > latest_session_index.get(helios_type, -1):
                latest_session_index[helios_type] = saved_session_index
                latest_by_type[helios_type] = function
        last_saved_function = getattr(self, "_last_saved_function", None)
        if last_saved_function is not None:
            last_saved_type = last_saved_function.get("heliosType")
            if last_saved_type in entries_by_type and last_saved_type not in latest_by_type:
                latest_by_type[last_saved_type] = matching_function(
                    [function for _index, function in entries_by_type[last_saved_type]],
                    last_saved_function) or last_saved_function
        return entries_by_type, latest_by_type

    def _visible_tab_label(self):
        """The label of the innermost tab currently shown: a sub tab (e.g. 'Collisions',
        'Reference') when the main tab holds sub tabs, else the main tab ('' when none)."""
        try:
            main_label = self._main_notebook.tab(self._main_notebook.select(), "text")
        except Exception:
            return ""
        for holder_label, sub_notebook in self._sub_notebooks():
            if main_label == holder_label and sub_notebook is not None:
                try:
                    return sub_notebook.tab(sub_notebook.select(), "text")
                except Exception:
                    return main_label
        return main_label

    def _refresh_all(self):
        """Bring every view up to date after the profile changed.  The device tabs are
        filled from a single pass over the profile.  Full View (serialises the whole
        profile) and Collisions (draws a widget per collision) are only rebuilt when they
        are the visible tab; otherwise _on_tab_changed rebuilds them when they are opened."""
        self._added_match_keys = None          # the profile may have changed: rebuild on demand
        entries_by_type, latest_by_type = self._entries_and_latest_by_type()
        for helios_type in HELIOS_TYPES:
            self._refresh_tab(helios_type, entries_by_type[helios_type], latest_by_type.get(helios_type))
        visible_tab = self._visible_tab_label()
        if visible_tab == FULL_VIEW_TAB_LABEL:
            self._refresh_full_view()
        elif visible_tab == COLLISIONS_TAB_LABEL:
            self._refresh_collisions()
        self._update_max_id()
        self._update_total_count()
        if getattr(self, "_command_table_panel", None) is not None:
            self._command_table_panel.refresh_status()     # Added column / green rows
        if getattr(self, "_old_reference_panel", None) is not None:
            self._old_reference_panel.refresh_status()
        if getattr(self, "_argument_logger", None) is not None:
            self._argument_logger._render_grouped()
            self._argument_logger.refresh_interface_state()
        self._schedule_json_to_text()                  # live sync: the Text Editor copy follows

    def _update_total_count(self):
        """Header readout of how many functions exist across all types."""
        label = getattr(self, "_total_count_label", None)
        if label is not None:
            label.configure(text=str(len(self._data.get("functions", []))))

    # ── unsaved-change tracking ──────────────────────────────────────────────────
    def _compute_state_signature(self):
        """Serialise the current profile (header + functions, private bookkeeping
        fields stripped) so it can be compared against the last clean state to
        detect unsaved changes."""
        if getattr(self, "_header_vars", None):
            self._sync_header_to_data()
        try:
            return json.dumps(strip_private_fields(self._data), sort_keys=True)
        except Exception:
            return repr(self._data)

    def _mark_clean(self):
        """Record the current state as the saved baseline (call after new / open
        / save)."""
        self._clean_signature = self._compute_state_signature()
        if self._documents:
            self._documents[self._active_document_index]["clean_signature"] = self._clean_signature
            self._render_document_tabs()

    def _has_unsaved_changes(self):
        """True when the active profile differs from its last saved state."""
        return self._compute_state_signature() != getattr(self, "_clean_signature", None)

    def _ask_save_interface(self, title="Unsaved Interface Changes"):
        """The active interface has unsaved changes and something is about to replace or close
        it: ask Save first? (Yes saves it, No goes on without saving, Cancel stops).  Returns
        True to go on, False when cancelled or when the save did not happen."""
        if not self._has_unsaved_changes():
            return True
        name = os.path.basename(self._current_file) if self._current_file else "The new interface"
        answer = messagebox.askyesnocancel(
            title, f"{name} has unsaved changes.\n\nSave them first?", parent=self)
        if answer is None:
            return False
        if answer:
            self._save()
            return not self._has_unsaved_changes()
        return True

    def _confirm_discard_changes(self, title="Unsaved Changes"):
        """When there are unsaved changes, ask the user whether to continue
        without saving. Returns True to proceed, False to abort."""
        if not self._has_unsaved_changes():
            return True
        return messagebox.askyesno(
            title,
            "You have unsaved changes that will be lost.\n\n"
            "Continue without saving?",
            parent=self)

    def _on_exit(self):
        """Quit: the Table tab asks about its unsaved changes first, then one prompt
        covers every open document with unsaved changes."""
        if self._text_editor is not None and not self._text_editor.confirm_exit():
            return
        for reference_panel in (self._command_table_panel, self._old_reference_panel):
            if reference_panel is not None and not reference_panel.confirm_discard_changes(title="Exit"):
                return
        self._capture_active_document()
        if any(self._document_is_dirty(index) for index in range(len(self._documents))):
            proceed = messagebox.askyesno(
                "Exit",
                "One or more open files have unsaved changes.\n\nExit anyway?",
                parent=self)
            if not proceed:
                return
        self._argument_logger.close()
        self.destroy()

    def _on_tab_changed(self, _event=None):
        """Auto-refresh the Collisions / Full View tabs whenever
        they are brought to the front so they always reflect the current
        profile; the first time the Argument Logger tab is opened it checks its
        Export.lua hook."""
        try:
            main_label = self._main_notebook.tab(self._main_notebook.select(), "text")
        except tk.TclError:
            main_label = ""
        previous_main_label = self._last_main_tab_label
        self._last_main_tab_label = main_label
        if {previous_main_label, main_label} == {DEVICES_TAB_LABEL, TEXT_EDITOR_TAB_LABEL}:
            self._sync_saved_editor_changes()
        current = self._visible_tab_label()
        if current == COLLISIONS_TAB_LABEL:
            self._refresh_collisions()
        elif current == FULL_VIEW_TAB_LABEL:
            self._refresh_full_view()
        elif current == ARGUMENT_LOGGING_TAB_LABEL:
            self._argument_logger.on_shown()   # checks the Export.lua hook the first time

    def update_source_list(self, source_rows, file_variables=None):
        """Called by Generate: keep the Source rows and each file's variables, and show them."""
        self._source_rows = list(source_rows)
        self._source_file_variables = dict(file_variables or {})
        if self._source_panel is not None and self._source_panel.winfo_exists():
            self._source_panel.show_source_data(self._source_rows, self._source_file_variables)

    def update_viewport_list(self, viewport_calls):
        """Called by Table ▸ Generate…: keep the (viewport text, file path) list and show it."""
        self._viewport_calls = list(viewport_calls)
        if self._viewport_panel is not None:
            self._viewport_panel.show_viewport_calls(self._viewport_calls)

    def load_additional_viewports(self):
        """Table > Current Reference > Load additional viewports: ask for another folder, search
        its .lua files for viewport calls exactly as Generate does (find_viewport_calls) and add
        the viewports that are not listed yet to the Viewport tab; a viewport already listed is
        not repeated.  The list is saved with the reference table, which is marked unsaved."""
        chosen_folder = filedialog.askdirectory(title="Select a folder to search for additional viewports",
                                                mustexist=True, parent=self, initialdir=default_aircraft_folder())
        if not chosen_folder:
            return
        self.config(cursor="watch")
        self.update_idletasks()
        try:
            lua_file_paths = find_aircraft_files(os.path.abspath(chosen_folder))[0]
            found_calls = find_viewport_calls(sorted(lua_file_paths))
        except Exception as unexpected_error:           # keep the window alive on unexpected input
            messagebox.showerror("Load additional viewports",
                                 f"Something went wrong while searching:\n{unexpected_error}", parent=self)
            return
        finally:
            self.config(cursor="")
        merged_calls, added_count = merge_viewport_calls(self._viewport_calls, found_calls)
        if added_count:
            self.update_viewport_list(merged_calls)
            if self._command_table_panel is not None:
                self._command_table_panel.mark_unsaved()
        self._select_tab_by_label(VIEWPORT_TAB_LABEL)
        found_count = len({viewport_text for viewport_text, _file_path in found_calls})
        messagebox.showinfo(
            "Load additional viewports",
            f"{found_count} viewport{'' if found_count == 1 else 's'} found in:\n{chosen_folder}\n\n"
            f"{added_count} new viewport{'' if added_count == 1 else 's'} added, "
            f"{found_count - added_count} already listed.", parent=self)

    def apply_generated_vehicles(self, vehicle_names):
        """Called by Generate: put the vehicles found (make_flyable calls of entry.lua) in the
        header's Vehicles field, comma separated.  A profile opened from a file keeps the
        Vehicles of its file: the file's values win over the generator's."""
        if not vehicle_names:
            return
        self._sync_header_to_data()
        if self._current_file and self._data.get("vehicles"):
            return
        self._data["vehicles"] = list(vehicle_names)
        self._header_vars["vehicles_str"].set(", ".join(vehicle_names))

    # ── Profile menu ─────────────────────────────────────────────────────────
    def _profile_new(self):
        """Profile > New: ask for an aircraft folder, save and close the interface and the
        reference table that are open (_save_and_close_current_work; New stops when a save is
        cancelled), start a new interface with the folder's name as its Module, and generate
        the reference table from the folder.  Saving the new interface then suggests
        "DCS.<Module>.hif.json"."""
        panel = self._command_table_panel
        if panel is None:
            return
        chosen_folder = panel.ask_generation_folder()
        if not chosen_folder or not self._save_and_close_current_work():
            return
        if self._current_file or self._data.get("functions"):   # closing left another document in front
            self._new()
        self._header_vars["module"].set(chosen_folder_name(chosen_folder))
        self._sync_header_to_data()
        self._select_tab_by_label(COMMAND_TABLE_TAB_LABEL)
        panel.generate_table_from_chosen_folder(chosen_folder)

    def _save_and_close_current_work(self):
        """Save the active interface (when it has unsaved changes; Save As when it has no file)
        and the reference table (likewise), then close both: the interface's document tab is
        closed and the Reference tab is emptied.  Returns False - closing nothing - when a
        save was cancelled or failed, so no work is lost."""
        panel = self._command_table_panel
        if not self._ask_save_interface():
            return False
        if panel is not None and not panel.save_and_close_table():
            return False
        self._mark_clean()          # saved, or the user chose not to save: closes without asking again
        self._close_document(self._documents[self._active_document_index])
        return True

    def _profile_reset(self):
        """Profile > Reset (Ctrl+R): close every loaded file and clear all data - the open
        interfaces (JSON Controls), both reference tables with their Source / Viewport / Mismatched
        lists (Reference Data) and the Argument Logger (Aircraft Data).  Asks first, because
        unsaved changes are lost."""
        if not messagebox.askyesno(
                "Reset",
                "Reset closes every loaded file and clears all data from the JSON Controls, "
                "Reference Data and Aircraft Data tabs.\n\nUnsaved changes are lost. Continue?",
                parent=self):
            return
        for dialog_name in ("_change_device_dialog", "_package_dialog"):
            dialog = getattr(self, dialog_name, None)
            if dialog is not None and dialog.winfo_exists():
                dialog.destroy()
        for reference_panel in (self._command_table_panel, self._old_reference_panel):
            if reference_panel is not None and reference_panel.winfo_exists():
                reference_panel.close_table()
                reference_panel.loaded_file_contents = None
        self._capture_active_document()
        self._documents.clear()
        self._reset_to_new_profile()
        self._mark_clean()
        self._documents.append(self._make_document_record(replace_on_open=True))
        self._active_document_index = 0
        self._restore_document(0)
        self._render_document_tabs()
        self._argument_logger.reset_all()
        self._refresh_all()
        self.schedule_reference_comparison()

    def _profile_edit(self):
        """Profile > Edit: the interface's Open first, then the reference table's Load.  The
        values of the opened interface file are shown as they are in the file."""
        if self._open():
            self._run_table_action("load_table")

    def _profile_save(self):
        """Profile > Save: save the interface file, then the reference table (to its file, or
        through Save As when it has none).  An empty table that has no file is not saved, and
        a table that has not changed since it was last saved (or loaded) is not written again:
        then only the interface file is saved."""
        self._save()
        panel = self._command_table_panel
        if panel is None or not (panel.current_file_path or panel.table_view.get_children()):
            return
        if panel.table_unchanged_since_save():
            return
        panel.save_table()

    def _profile_package(self):
        """Profile > Package: open the Package dialog (or bring the open one to the front).  It
        needs nothing to be loaded: no interface, reference table or generated data.  When the
        active profile lists vehicles, the first one pre-fills the Aircraft field."""
        package_dialog = getattr(self, "_package_dialog", None)
        if package_dialog is not None and package_dialog.winfo_exists():
            package_dialog.show_in_front()
            return
        self._package_dialog = PackageDialog(self, default_aircraft=self._first_listed_vehicle())

    def _first_listed_vehicle(self):
        """The first name in the header's Vehicles field, or "" when the field is empty or the
        header is not available.  Reads the field only; nothing has to be loaded."""
        try:
            vehicles_text = self._header_vars["vehicles_str"].get()
        except (AttributeError, KeyError, tk.TclError):
            return ""
        return next((vehicle.strip() for vehicle in vehicles_text.split(",") if vehicle.strip()), "")

    def _profile_monitor_removal(self):
        r"""Profile > Monitor Removal: ask for a Helios profile (the dialog opens in
        Documents\Helios\Profiles), remove its unused monitors (remove_unused_monitors) and save
        the result under the same file name in Documents\Helios\Interface Editor\Profile Exports (created when missing)."""
        profile_path = filedialog.askopenfilename(
            title="Select the Helios profile to remove unused monitors from", filetypes=PROFILE_FILE_TYPES,
            initialdir=default_profile_folder(), parent=self)
        if not profile_path:
            return
        export_folder = default_export_folder()
        if export_folder is None:
            messagebox.showerror("Monitor Removal", "The Helios Profile Exports folder could not be created.", parent=self)
            return
        export_path = os.path.join(export_folder, os.path.basename(profile_path))
        if os.path.exists(export_path) and not messagebox.askyesno(
                "Monitor Removal", f"This file already exists:\n{export_path}\n\nReplace it?", parent=self):
            return
        try:
            removed_count, kept_count = remove_unused_monitors_from_file(profile_path, export_path)
        except OSError as file_error:
            messagebox.showerror("Monitor Removal", f"Could not process the file:\n{file_error}", parent=self)
            return
        messagebox.showinfo(
            "Monitor Removal",
            f"Removed {removed_count} unused monitor{'' if removed_count == 1 else 's'}, "
            f"kept {kept_count}.\n\nSaved:\n{export_path}", parent=self)

    def _profile_check_bindings(self):
        r"""Profile > Check Bindings (Ctrl+B): ask for a Helios profile (the dialog opens in
        Documents\Helios\Profiles) and list every device in it that has no binding, with the
        parent / child pathway to it (find_unbound_devices).  Monitors, viewports, panels, labels and
        images are not checked."""
        profile_path = filedialog.askopenfilename(
            title="Select the Helios profile to check for devices without bindings",
            filetypes=PROFILE_FILE_TYPES, initialdir=default_profile_folder(), parent=self)
        if not profile_path:
            return
        try:
            unbound = find_unbound_devices(read_profile_text(profile_path))
        except (OSError, ValueError) as file_error:
            messagebox.showerror("Check Bindings", f"Could not check the profile:\n{file_error}", parent=self)
            return
        UnboundDevicesDialog(self, profile_path, unbound)

    def _show_device_viewer(self):
        """JSON ▸ View Devices: open the device viewer (or bring the open one to the front,
        refreshed from the active profile)."""
        viewer = getattr(self, "_device_viewer_window", None)
        if viewer is not None and viewer.winfo_exists():
            viewer.reload_device_names()
            viewer.lift()
            return
        self._device_viewer_window = DeviceViewerWindow(self)

    def _run_table_action(self, action_name, panel_role=CURRENT_REFERENCE_ROLE):
        """Table menu: bring the Reference tab (or, for panel_role OLD_REFERENCE_ROLE, the
        Old References tab) to the front and run one of its actions
        (generate_table / load_table / save_table / save_table_as)."""
        if panel_role == OLD_REFERENCE_ROLE:
            panel, tab_label = self._old_reference_panel, OLD_REFERENCE_TAB_LABEL
        else:
            panel, tab_label = self._command_table_panel, COMMAND_TABLE_TAB_LABEL
        if panel is None:
            return
        self._select_tab_by_label(tab_label)            # Tables ▸ Reference / Old References
        getattr(panel, action_name)()

    # ── Reference / Old References comparison ─────────────────────────────────
    def _send_reference_to_logger(self):
        """Give the Argument Logger the rows of Tables > Reference (its Arg Names, Devices and
        Commands).  Runs after every change of that table: it is part of the idle-time
        comparison that every change schedules."""
        panel = self._command_table_panel
        if panel is None or not panel.winfo_exists():
            return
        table_rows = [row for _row_id, row in panel.rows_with_ids()]
        self._argument_logger.use_reference_rows(table_rows, panel.current_file_path, self._source_rows)

    def logger_seen_ids(self):
        """(Arg #s, (Device #, Command #) pairs) the Argument Logger has seen."""
        logger = getattr(self, "_argument_logger", None)
        return logger.seen_ids() if logger is not None else (set(), set())

    def refresh_reference_highlight(self):
        """The logger saw new values: recolour the orange rows of Reference."""
        panel = getattr(self, "_command_table_panel", None)
        if panel is not None and panel.winfo_exists():
            panel.update_logger_highlight()

    def save_editor_setting(self, key, value):
        """Remember one setting between runs (see load_editor_settings)."""
        self.editor_settings[key] = value
        settings_path = editor_settings_path()
        try:
            os.makedirs(os.path.dirname(settings_path), exist_ok=True)
            with open(settings_path, "w", encoding="utf-8") as settings_file:
                json.dump(self.editor_settings, settings_file, indent=4)
        except OSError as error:
            messagebox.showwarning(
                "Settings Not Saved",
                f"The setting could not be saved to:\n{settings_path}\n\n{error}",
                parent=self)

    def current_reference_info(self):
        """(whether Tables > Reference holds rows, the aircraft its table is for or None)."""
        panel = self._command_table_panel
        if panel is None or not panel.winfo_exists():
            return False, None
        return bool(panel.table_view.get_children()), getattr(panel, "table_aircraft", None)

    def reference_load_allowed(self, table_aircraft):
        """Asked by Tables > Reference before it loads a table (see
        ArgumentLoggerPanel.reference_load_allowed)."""
        return self._argument_logger.reference_load_allowed(table_aircraft)

    def reference_table_loaded(self, panel):
        """The user loaded or generated a table in Tables > Reference: the Argument Logger runs
        its name search once.  A table the logger generated itself is not searched again."""
        if self._logger_generating_reference:
            return
        self._argument_logger.on_reference_loaded(getattr(panel, "table_aircraft", None))

    def generate_reference_for_logger(self, aircraft_folder):
        """The Argument Logger needs the table of the aircraft being flown: generate Tables >
        Reference from aircraft_folder, as Table > Generate does.  Unsaved changes in the open
        table are offered for saving first (Cancel keeps the table and generates nothing).  Returns True when a table was made."""
        panel = self._command_table_panel
        if panel is None or not panel.winfo_exists():
            return False
        self._select_tab_by_label(COMMAND_TABLE_TAB_LABEL)
        if not panel.confirm_discard_changes(title="Generate Reference Table"):
            return False                              # cancelled: the current table is kept
        panel.close_table()
        self._logger_generating_reference = True
        try:
            return panel.generate_table_from_chosen_folder(aircraft_folder)
        finally:
            self._logger_generating_reference = False

    def build_devices_for_logger(self, id_rows):
        """Add Device(s) in the logger's Grouped Commands: select the rows of Tables >
        Reference whose (Arg #, Device #, Command #) are in id_rows, show that tab and run
        Build Device on them.  Returns the number of rows selected (0: none were found)."""
        panel = self._command_table_panel
        if panel is None or not panel.winfo_exists():
            return 0
        wanted_ids = {tuple(normalize_id_text(value) for value in ids) for ids in id_rows}
        matched_row_ids = [row_id for row_id in panel.table_view.get_children()
                           if panel.row_id_texts(row_id) in wanted_ids]
        if not matched_row_ids:
            return 0
        self._select_tab_by_label(COMMAND_TABLE_TAB_LABEL)
        panel.table_view.selection_set(matched_row_ids)
        panel.table_view.see(matched_row_ids[0])
        self.update_idletasks()
        panel.build_device_from_selected_row()
        return len(matched_row_ids)

    def apply_found_arg_names(self, found_rows, arg_kinds):
        """The Argument Logger found names for arguments the Reference table leaves unnamed
        (found_rows in the table format; arg_kinds {Arg #: "cockpit" / "draw" / "both"}).
        Reference rows with that Arg # and no Arg Name (or only the number) get the name; an
        argument with no row gets a new row.  A draw-only argument never renames a cockpit row
        of the same number: it gets its own row.  The table is marked unsaved.  Returns
        (rows named, rows added)."""
        panel = self._command_table_panel
        if panel is None or not panel.winfo_exists():
            return 0, 0
        panel.finish_cell_edit(True)
        rows_by_arg = {}
        for row_id, table_row in panel.rows_with_ids():
            rows_by_arg.setdefault(normalize_id_text(table_row.get("Arg #", "")), []).append((row_id, table_row))
        named_count = added_count = 0
        for found_row in found_rows:
            arg_text = found_row["Arg #"]
            matching_rows = rows_by_arg.get(normalize_id_text(arg_text), [])
            if arg_kinds.get(arg_text) != "draw" and matching_rows:
                named_count += self._name_unnamed_rows(panel, matching_rows, arg_text, found_row["Arg Name"])
                continue
            panel.table_view.insert("", tk.END, values=panel.row_to_cell_texts(found_row))
            added_count += 1
        if named_count or added_count:
            panel.mark_unsaved()
        return named_count, added_count

    @staticmethod
    def _name_unnamed_rows(panel, matching_rows, arg_text, arg_name) -> int:
        """Give the rows with no Arg Name (or only the number) the found name; returns how many changed."""
        named_count = 0
        for row_id, table_row in matching_rows:
            current_name = table_row.get("Arg Name", "").strip()
            if (not current_name or current_name == arg_text) and panel.set_cell_text(row_id, "Arg Name", arg_name):
                named_count += 1
        return named_count

    def schedule_reference_comparison(self):
        """Ask for refresh_reference_comparison to run once the window is idle.  Many changes
        in a row (a Generate, an Update, a profile refresh) then cost one comparison."""
        if not self._reference_comparison_pending:
            self._reference_comparison_pending = True
            self.after_idle(self.refresh_reference_comparison)

    def refresh_reference_comparison(self):
        """Compare Reference with Old References (compare_reference_tables, O(rows)) when both
        hold rows: fill the Mismatched tab and colour the mismatched rows of both tables
        blue.  When either table is empty there are no mismatches."""
        self._reference_comparison_pending = False
        self._send_reference_to_logger()
        current_panel, old_panel = self._command_table_panel, self._old_reference_panel
        if current_panel is None or old_panel is None or not current_panel.winfo_exists() \
                or not old_panel.winfo_exists():
            return
        new_rows_with_ids, old_rows_with_ids = current_panel.rows_with_ids(), old_panel.rows_with_ids()
        if new_rows_with_ids and old_rows_with_ids:
            mismatch_records, mismatched_new_ids, mismatched_old_ids = compare_reference_tables(
                new_rows_with_ids, old_rows_with_ids)
        else:
            mismatch_records, mismatched_new_ids, mismatched_old_ids = [], set(), set()
        current_panel.mismatched_row_ids = mismatched_new_ids
        old_panel.mismatched_row_ids = mismatched_old_ids
        current_panel.apply_row_colors()
        old_panel.apply_row_colors()
        if self._mismatched_panel is not None and self._mismatched_panel.winfo_exists():
            self._mismatched_panel.show_mismatches(mismatch_records)

    def update_old_reference_values(self, mismatch_records):
        """Mismatched ▸ Update: copy the new values of the given mismatch records into
          * the Old References rows:  only-arg rows get the new Arg #; other rows get the new
            Arg #, Device, Device # and Command #;
          * the profile's devices that hold the OLD ids of those rows (found with the same
            matching as the Added column): their Export ID(Arg) and, for rows that are not
            only-arg, their device name, device ids and action ids.
        Every change is planned from the original values first and then applied in one go,
        so swapped numbers cannot chain.  One Undo step covers the device changes."""
        self.refresh_reference_comparison()             # make sure the records are current
        old_panel = self._old_reference_panel
        functions_by_key = build_functions_by_match_key(self._data.get("functions", []))
        planned_changes = {}                            # id(function) -> [function, exports, devices, actions, name]
        old_rows_changed = 0
        for mismatch_record in mismatch_records:
            old_rows_changed += self._update_old_reference_row(old_panel, mismatch_record)
            self._plan_device_changes(planned_changes, functions_by_key, mismatch_record)
        devices_changed = self._apply_planned_device_changes(planned_changes)
        if old_rows_changed:
            old_panel.mark_unsaved()
        if devices_changed:
            self._sort_functions()
            self._refresh_all()                         # also re-checks Added and the comparison
        else:
            self.schedule_reference_comparison()
        messagebox.showinfo("Update", f"Updated {old_rows_changed} Old References row(s) and "
                                         f"{devices_changed} device(s).", parent=self)

    @staticmethod
    def _update_old_reference_row(old_panel, mismatch_record):
        """Write a record's new values into its Old References row; 1 when anything changed."""
        old_row_id = mismatch_record["old_row_id"]
        row_changed = old_panel.set_cell_text(old_row_id, "Arg #", mismatch_record["New Arg #"])
        if not mismatch_record["only_arg"]:
            for column in ("Device", "Device #", "Command #"):
                row_changed = old_panel.set_cell_text(old_row_id, column, mismatch_record["New " + column]) or row_changed
        return row_changed

    @staticmethod
    def _plan_device_changes(planned_changes, functions_by_key, mismatch_record):
        """Add to planned_changes what each device holding the record's OLD ids must change to."""
        old_arg = normalize_id_text(mismatch_record["Old Arg #"])
        old_device_number = normalize_id_text(mismatch_record["Old Device #"])
        old_command_number = normalize_id_text(mismatch_record["Old Command #"])
        if mismatch_record["only_arg"]:
            old_key = table_row_match_key(old_arg, "", "")
        else:
            old_key = table_row_match_key(old_arg, old_device_number, old_command_number)
        for function in (functions_by_key.get(old_key, []) if old_key else []):
            plan = planned_changes.setdefault(id(function), [function, {}, {}, {}, None])
            HeliosEditor._add_record_to_plan(plan, mismatch_record)

    @staticmethod
    def _add_record_to_plan(plan, mismatch_record):
        """Put a record's old -> new arg, device and command numbers (and new device name) into
        one device's plan [function, arg changes, device changes, command changes, new name]."""
        old_arg, new_arg = normalize_id_text(mismatch_record["Old Arg #"]), normalize_id_text(mismatch_record["New Arg #"])
        if old_arg and new_arg and old_arg != new_arg:
            plan[1][old_arg] = new_arg
        if mismatch_record["only_arg"]:
            return
        old_device_number = normalize_id_text(mismatch_record["Old Device #"])
        new_device_number = normalize_id_text(mismatch_record["New Device #"])
        old_command_number = normalize_id_text(mismatch_record["Old Command #"])
        new_command_number = normalize_id_text(mismatch_record["New Command #"])
        if old_device_number and new_device_number and old_device_number != new_device_number:
            plan[2][old_device_number] = new_device_number
        if old_command_number and new_command_number and old_command_number != new_command_number:
            plan[3][old_command_number] = new_command_number
        new_device_name = mismatch_record["New Device"].strip()
        if new_device_name and new_device_name != mismatch_record["Old Device"].strip():
            plan[4] = new_device_name

    def _apply_planned_device_changes(self, planned_changes):
        """Apply the planned changes (one Undo step); returns how many devices changed."""
        if not planned_changes:
            return 0
        self._push_undo_state()
        devices_changed = 0
        for function, export_changes, device_changes, action_changes, new_device_name in planned_changes.values():
            function_changed = replace_function_ids(function, export_changes, device_changes, action_changes)
            if new_device_name and function.get("device") != new_device_name:
                function["device"] = new_device_name
                function_changed = True
            devices_changed += function_changed
        return devices_changed

    # ── file ops ───────────────────────────────────────────────────────────────
    @staticmethod
    def _is_helios_interface_path(path):
        """True for a file named Helios.<name>.hif.json or DCS.<name>.hif.json."""
        name = os.path.basename(path).casefold()
        suffix = ".hif.json"
        for prefix in ("helios.", "dcs."):
            if name.startswith(prefix):
                return name.endswith(suffix) and bool(name[len(prefix):-len(suffix)])
        return False

    def _ask_yes_no_within_main_window(self, title, prompt):
        """A Yes / No question shown centred over the main window; True for Yes."""
        self.update_idletasks()
        parent_width = max(1, self.winfo_width())
        parent_height = max(1, self.winfo_height())
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.transient(self)
        dialog.title(title)
        dialog.configure(bg=PANEL_BG)
        dialog.resizable(False, False)

        tk.Label(
            dialog,
            text=prompt,
            bg=PANEL_BG,
            fg=TEXT_PRI,
            font=FONT_UI,
            justify="left",
            wraplength=max(180, min(560, parent_width - 100)),
        ).pack(fill="x", padx=18, pady=(18, 12))

        result = {"answer": False}

        def finish(answer):
            """Store the answer and close the question."""
            result["answer"] = answer
            dialog.destroy()

        buttons = tk.Frame(dialog, bg=PANEL_BG)
        buttons.pack(fill="x", padx=18, pady=(0, 16))
        tk.Button(
            buttons,
            text="No",
            bg=MID_BG,
            fg=TEXT_SEC,
            activebackground=MID_BG,
            activeforeground=TEXT_PRI,
            relief="flat",
            padx=18,
            pady=5,
            command=lambda: finish(False),
        ).pack(side="right")
        yes_button = tk.Button(
            buttons,
            text="Yes",
            bg=ACCENT,
            fg=DARK_BG,
            activebackground=ACCENT,
            activeforeground=DARK_BG,
            relief="flat",
            padx=18,
            pady=5,
            command=lambda: finish(True),
        )
        yes_button.pack(side="right", padx=(0, 8))
        dialog.protocol("WM_DELETE_WINDOW", lambda: finish(False))
        dialog.bind("<Escape>", lambda _event: finish(False))
        dialog.bind("<Return>", lambda _event: finish(True))
        dialog.update_idletasks()

        margin = 24
        width = min(dialog.winfo_reqwidth(), max(1, parent_width - 2 * margin))
        height = min(dialog.winfo_reqheight(), max(1, parent_height - 2 * margin))
        position_x = self.winfo_rootx() + (parent_width - width) // 2
        position_y = self.winfo_rooty() + (parent_height - height) // 2
        dialog.geometry(f"{width}x{height}+{position_x}+{position_y}")
        dialog.deiconify()
        dialog.grab_set()
        yes_button.focus_set()
        self.wait_window(dialog)
        return result["answer"]

    def _open_text_editor_files(self):
        """Ask for text files and open them in the Text Editor."""
        paths = filedialog.askopenfilenames(
            title="Open Text Files",
            filetypes=TEXT_EDITOR_FILE_TYPES,
            parent=self,
        )
        for path in paths:
            self._text_editor.open_path(path)
            path_key = self._sync_path_key(path)
            opened = any(
                self._sync_path_key(document.get("path")) == path_key
                for document in self._text_editor.documents
            )
            if not opened or not self._is_helios_interface_path(path):
                continue
            if self._ask_yes_no_within_main_window(
                    "Also Open in JSON Devices?",
                    f"{os.path.basename(path)} appears to be a Helios interface file.\n\n"
                    "Would you also like to open it in JSON Devices?"):
                self._open_json_counterpart(path)

    def _open_json_counterpart(self, path):
        """Open the JSON document of a file in the JSON Controls tab (or select it when already open)."""
        path_key = self._sync_path_key(path)
        existing = next(
            (document for document in self._documents
             if self._sync_path_key(document.get("current_file")) == path_key),
            None,
        )
        if existing is not None:
            self._select_document(existing)
            return True
        return self._open_path(path)

    def _new(self):
        """JSON > New: store the active document, add a new empty profile (source User, type DCS,
        no functions) as its own document tab, show it, and take it as the saved baseline so an
        untouched new document is not reported as unsaved. Reuse the clean automatic Untitled
        placeholder when possible."""
        self._capture_active_document()
        if self._is_replaceable_auto_untitled():
            self._documents[0]["replace_on_open"] = False
            self._mark_clean()
            return
        blank_data = {
            "source": "User", "version": "Initial", "commit": "", "type": "DCS",
            "name": "", "module": "", "vehicles": [], "functions": []
        }
        document = self._make_document_record(
            data=blank_data,
            current_file=None,
            clean_signature=self._document_signature(blank_data))
        document.update({
            "last_added_device": "",
            "last_added_device_id": "",
            "last_added_function": None,
            "last_saved_function": None,
            "next_saved_session_index": 1,
            "next_created_session_index": 1,
            "undo_stack": [],
            "redo_stack": [],
        })
        self._documents.append(document)
        self._restore_document(len(self._documents) - 1)
        # The header fills in the profile name ("DCS") when the document is shown, so the
        # blank document is only complete now: take it as the saved baseline (like Open
        # does) so an untouched new document is not reported as having unsaved changes.
        self._mark_clean()

    def _reset_to_new_profile(self):
        """Start a fresh, empty profile without prompting (the caller has
        already confirmed, e.g. the import-into-a-new-profile path)."""
        self._data = {"source": "User", "version": "Initial", "commit": "", "type": "DCS",
                      "name": "", "module": "", "vehicles": [], "functions": []}
        self._current_file = None
        self._last_added_device = ""
        self._last_added_device_id = ""
        self._last_added_function = None
        self._last_saved_function = None
        self._next_saved_session_index = 1
        self._next_created_session_index = 1
        self._undo_stack = []
        self._redo_stack = []
        self._update_window_title()
        self._sync_data_to_header()
        if self._documents:
            self._capture_active_document()
            self._render_document_tabs()

    def _open(self):
        r"""JSON > Open: choose a JSON profile and open it in a new document tab.  The dialog
        opens in Documents\Helios\Interfaces\HeliosInterfaces (default_interface_folder,
        created when missing) - the same folder Save starts in.  Returns True when a file was
        chosen."""
        path = filedialog.askopenfilename(
            title="Open Interface",
            filetypes=INTERFACE_FILE_TYPES,
            initialdir=default_interface_folder(),
            parent=self)
        if path and self._open_path(path):
            self._text_editor.open_path(path)           # also loaded into the Text Editor
        return bool(path)

    def _on_file_drop(self, event):
        """JSON files dropped on the window (drag and drop): open each in its own document tab."""
        paths = self.tk.splitlist(event.data)
        json_paths = [path for path in paths if path.lower().endswith(".json")]
        if not json_paths:
            messagebox.showerror("Open Failed", "Drop one or more JSON files.", parent=self)
            return
        for path in json_paths:
            if self._open_path(path):
                self._text_editor.open_path(path)       # also loaded into the Text Editor

    def _open_path(self, path):
        """Open a profile file as a new document tab: numeric text turned back into numbers,
        action-id keys normalised, missing vehicles / functions lists added, functions sorted
        by device and action id; the file becomes the saved baseline.  An untouched automatic
        Untitled document is replaced rather than retained. Errors are shown."""
        path_key = self._sync_path_key(path)
        reopen_index = next((index for index, document in enumerate(self._documents)
                             if document.get("current_file")
                             and self._sync_path_key(document.get("current_file")) == path_key), None)
        if reopen_index is not None and not self._confirm_reopen_dirty_document(path, reopen_index):
            return False
        try:
            loaded = self._read_profile_file(path)
            self._capture_active_document()
            document = self._make_opened_document(loaded, path)
            document_index = self._place_opened_document(document, reopen_index)
            self._restore_document(document_index)
            # Auto-sort loaded items by device id then action id before display.
            self._sort_functions()
            self._refresh_all()
            # A just-opened profile is the new clean baseline.
            self._mark_clean()
            return True
        except Exception as error:
            messagebox.showerror("Open Failed", str(error), parent=self)
            return False

    def _confirm_reopen_dirty_document(self, path, reopen_index) -> bool:
        """The file is already open: opening it again reloads it from disk, which would overwrite
        unsaved changes made in that tab, so ask whether to save them first.  False = do not open."""
        self._capture_active_document()
        if not self._document_is_dirty(reopen_index):
            return True
        self._select_document(self._documents[reopen_index])
        answer = messagebox.askyesnocancel(
            "Unsaved Interface Changes",
            f"{os.path.basename(path)} is already open and has unsaved changes. Opening it again "
            "replaces them with the file on disk.\n\nSave them first?", parent=self)
        if answer is None:
            return False
        if answer:
            self._save()
            if self._has_unsaved_changes():
                return False
        return True

    @staticmethod
    def _read_profile_file(path):
        """The profile JSON in a file, with numeric text cast back to numbers, action-id keys
        normalised and the vehicles / functions lists present."""
        with open(path, "r", encoding="utf-8") as handle:
            loaded = json.load(handle)
        loaded = cast_strings_to_numbers(loaded)
        loaded = normalize_action_id_keys(loaded)
        if "vehicles" not in loaded:
            loaded["vehicles"] = []
        if "functions" not in loaded:
            loaded["functions"] = []
        return loaded

    def _make_opened_document(self, loaded, path):
        """A fresh document record for a profile just read from path."""
        document = self._make_document_record(
            data=loaded,
            current_file=path,
            clean_signature=self._document_signature(loaded))
        document.update({
            "last_added_device": "",
            "last_added_device_id": "",
            "last_added_function": None,
            "last_saved_function": None,
            "next_created_session_index": 1,
            "undo_stack": [],
            "redo_stack": [],
        })
        return document

    def _place_opened_document(self, document, reopen_index) -> int:
        """Put the document where it belongs (replacing the one reopened, or an untouched automatic
        Untitled one, else appended); returns its index."""
        replace_placeholder = self._is_replaceable_auto_untitled()
        if reopen_index is not None:
            self._documents[reopen_index] = document
            return reopen_index
        if replace_placeholder:
            self._documents[self._active_document_index] = document
            return self._active_document_index
        self._documents.append(document)
        return len(self._documents) - 1

    # ── DCS Lua import ───────────────────────────────────────────────────────────
    # def _import_dcs_folder(self):
    #     """Compile a DCS Cockpit folder of clickabledata Lua (+ devices/
    #     command_defs/draw_args) into Helios functions and load them into the
    #     editor. The chosen folder and all of its subfolders are searched for the
    #     appropriate files."""
    #     if not self._confirm_discard_changes(title="Import"):
    #         return
    #     folder = filedialog.askdirectory(
    #         title="Select DCS Cockpit folder (clickabledata.lua and supporting files; subfolders are searched)")
    #     if not folder:
    #         return
    #     try:
    #         from parser_engine import convert_clickabledata_to_hif
    #     except Exception as error:
    #         messagebox.showerror(
    #             "Import unavailable",
    #             "Could not load the DCS Lua compiler.\n\n"
    #             "Make sure 'parser_engine.py' "
    #             "is in the same folder as this program.\n\n"
    #             f"Details: {error}")
    #         return

    #     # Use the currently loaded profile as a label/style reference when it
    #     # already contains functions; otherwise the compiler auto-detects a
    #     # sibling .json in the folder.
    #     reference = self._data if self._data.get("functions") else None
    #     try:
    #         functions, result = convert_clickabledata_to_hif(
    #             folder, reference=reference, strip_source_notes=True)
    #     except FileNotFoundError as error:
    #         messagebox.showerror("No clickabledata found", str(error))
    #         return
    #     except Exception as error:
    #         messagebox.showerror("Import Failed", str(error))
    #         return

    #     self._ingest_imported_functions(functions, result, source=folder)

    def _apply_import_merge(self, functions, source):
        """Decide how to bring `functions` in (new profile vs append) and apply
        it. Returns False if the user cancelled, True otherwise."""
        existing = self._data.get("functions", [])
        if not existing:
            self._data["functions"] = list(functions)
            return True
        choice = messagebox.askyesnocancel(
            "Import",
            f"Compiled {len(functions)} function(s) from:\n{source}\n\n"
            f"Your profile already has {len(existing)} function(s).\n\n"
            "Do you want to import into a NEW profile?\n\n"
            "Yes  = start a new profile (the current data is cleared)\n"
            "No   = add the imported set to the current profile\n"
            "Cancel = abort import",
            parent=self)
        if choice is None:
            return False
        if choice:
            # Start a fresh profile, then load the imported set into it.
            self._reset_to_new_profile()
            self._data["functions"] = list(functions)
        else:
            self._data["functions"] = existing + list(functions)
        return True

    @staticmethod
    def _append_warning_lines(lines, warnings):
        """Add up to six warnings (and a count of the rest) to a message."""
        lines.append("")
        lines.append(f"Warnings ({len(warnings)}):")
        lines.extend("  • " + warning for warning in warnings[:6])
        if len(warnings) > 6:
            lines.append(f"  …and {len(warnings) - 6} more.")
        lines.append("")
        lines.append("Tip: IDs (device/action/arg) come straight from the "
                     "Lua and are reliable. Device labels, switch position "
                     "names and axis ranges are best-effort — review them "
                     "in the tabs and adjust as needed.")

    @staticmethod
    def _import_summary_lines(functions, result):
        """The text shown after importing functions: how many functions, devices, command tables
        and elements were read, how many unused devices / unpaired args / unpaired commands were
        added and as what, the most used helper functions, and up to six warnings."""
        lines = [
            f"Imported {len(functions)} function(s).",
            f"Devices resolved: {result.device_count}",
            f"Command tables:   {result.command_table_count}",
            f"Elements parsed:  {result.element_count}",
        ]
        if getattr(result, "unused_device_buttons", 0):
            lines.append(f"Unused devices →  {result.unused_device_buttons} "
                         "added as PushButtons")
        if getattr(result, "unpaired_arg_axes", 0):
            lines.append(f"Unpaired draw-args → {result.unpaired_arg_axes} "
                         "reassigned as Axes")
        if getattr(result, "unpaired_command_buttons", 0):
            lines.append(f"Unpaired commands → {result.unpaired_command_buttons} "
                         "reassigned as PushButtons")
        if result.helper_counts:
            top = sorted(result.helper_counts.items(), key=lambda item: -item[1])[:6]
            lines.append("Top helpers: "
                         + ", ".join(f"{helper}×{count}" for helper, count in top))
        if result.warnings:
            HeliosEditor._append_warning_lines(lines, result.warnings)
        return lines

    def _ingest_imported_functions(self, functions, result, source=""):
        """Merge compiled functions into the profile after asking the user how,
        then refresh the UI and report a summary."""
        if not functions:
            messagebox.showwarning(
                "Nothing imported",
                "The compiler ran but produced no functions.\n\n"
                + ("\n".join(result.warnings[:8]) if result.warnings else ""),
                parent=self)
            return

        for function in functions:
            function[ADDED_FLAG] = True
        if not self._apply_import_merge(functions, source):
            return

        # Keep the device-then-action ordering for the bulk add too.
        self._sort_functions()
        self._refresh_all()
        messagebox.showinfo("DCS Lua Import",
                            "\n".join(self._import_summary_lines(functions, result)),
                            parent=self)

    def _save(self):
        """JSON > Save: ask for the sort order and save to the current file (Save As when there
        is none)."""
        if not self._current_file:
            self._save_as()
            return
        method = self._ask_save_sort_method()
        if method is None:
            return
        self._set_sort_method(method)
        self._write(self._current_file)

    def _save_as_helios_type(self):
        """JSON > Save As Helios Type: Save As with the file name starting "Helios."."""
        self._save_as(prefix=HELIOS_FILE_PREFIX)

    def _save_as_dcs_type(self):
        """JSON > Save As DCS Type: Save As with the file name starting "DCS."."""
        self._save_as(prefix=INTERFACE_FILE_PREFIX)

    def _save_as(self, prefix=None):
        """JSON > Save As: ask for the sort order and a file name, then save.  The dialog opens in
        the profile's own folder, else Documents\\Helios\\Interfaces\\HeliosInterfaces
        (default_interface_folder, created when missing).  A new interface (one without a file)
        is offered the name "DCS.<Module>.hif.json" (interface_file_name); a new interface
        is always saved with ".hif.json" at the end, even when the name is typed without it.  With `prefix`
        ("DCS." / "Helios.", from Save As DCS Type / Helios Type) the first part of the offered
        name is changed to it, whether the name comes from the module or the current file."""
        method = self._ask_save_sort_method()
        if method is None:
            return
        self._set_sort_method(method)
        suggested_name = ("" if self._current_file
                          else interface_file_name(self._header_vars["module"].get(), prefix))
        initial_file = suggested_name or (os.path.basename(self._current_file) if self._current_file else "")
        if prefix:
            initial_file = swap_interface_prefix(initial_file, prefix)
        path = filedialog.asksaveasfilename(
            title="Save Interface",
            defaultextension=".json",
            filetypes=INTERFACE_SAVE_FILE_TYPES,
            initialdir=dialog_start_folder(self._current_file, default_interface_folder),
            initialfile=initial_file,
            parent=self)
        if not path:
            return
        if not self._current_file or prefix:
            path = with_interface_extension(path)   # a new interface is saved as <name>.hif.json
        elif not path.lower().endswith(".json"):
            path += ".json"                      # an interface is always saved as a .json file
        was_new_interface = not self._current_file
        self._current_file = path
        self._write(path, new_interface=was_new_interface)
        self._update_window_title()

    def _current_sort_key(self):
        """The sort-key function for the active save / Full View ordering."""
        return SORT_METHODS.get(self._sort_method, SORT_METHODS["deviceaction"])[1]

    def _set_sort_method(self, method):
        """Switch the active ordering, keep the Full View toggle in sync, and
        re-render the Full View."""
        if method not in SORT_METHODS:
            return
        self._sort_method = method
        var = getattr(self, "_sort_method_var", None)
        if var is not None and var.get() != method:
            var.set(method)
        self._refresh_full_view()

    def _ask_save_sort_method(self):
        """Modal prompt: how should functions be ordered in the saved file?
        Returns the chosen method key, or None if the user cancels."""
        dialog = tk.Toplevel(self)
        dialog.transient(self)
        dialog.title("Save — Sort Order")
        dialog.configure(bg=DARK_BG)
        dialog.resizable(False, False)
        dialog.grab_set()

        tk.Label(dialog, text="Order functions in the saved file by:", bg=DARK_BG,
                 fg=TEXT_HEAD, font=FONT_HEAD).pack(anchor="w", padx=18, pady=(16, 10))

        choice = tk.StringVar(value=self._sort_method)
        for key, (label, _sort_function) in SORT_METHODS.items():
            tk.Radiobutton(dialog, text=label, variable=choice, value=key,
                           bg=DARK_BG, fg=TEXT_PRI, selectcolor=MID_BG,
                           activebackground=DARK_BG, activeforeground=ACCENT,
                           font=FONT_UI, anchor="w").pack(anchor="w", padx=24, pady=2)

        result = {"method": None}

        def confirm():
            """Save button of the sort-order dialog: remember the choice and close."""
            result["method"] = choice.get()
            dialog.destroy()

        buttons = tk.Frame(dialog, bg=DARK_BG)
        buttons.pack(fill="x", padx=18, pady=(14, 16))
        tk.Button(buttons, text="✓  Save", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD,
                  relief="flat", padx=16, pady=5, cursor="hand2",
                  command=confirm).pack(side="right", padx=(6, 0))
        tk.Button(buttons, text="✕  Cancel", bg=MID_BG, fg=TEXT_SEC, font=FONT_UI,
                  relief="flat", padx=16, pady=5, cursor="hand2",
                  command=dialog.destroy).pack(side="right")

        dialog.update_idletasks()
        width, height = dialog.winfo_reqwidth(), dialog.winfo_reqheight()
        position_x, position_y = centered_position_on_parent(self, width, height)
        dialog.geometry(f"+{position_x}+{position_y}")

        self.wait_window(dialog)
        return result["method"]

    def _build_save_payload(self):
        """Build the exact dict written to disk on Save: prettified device/name
        labels, functions ordered by the active sort method, and every number
        cast to a string. Shared by the writer and the read-only Full View tab
        so the two always agree."""
        self._sync_header_to_data()
        payload = strip_private_fields(copy.deepcopy(self._data))

        # Prettify the Device and Name of every function on the way out, so the
        # saved file carries the cleaned-up labels (matches what the grid shows).
        # Also coerce the designated value fields (Switch positions, Axis bounds,
        # PushButton push/release values, ScaledNetworkValue calibration points)
        # to floats so the canonical SPECIAL_FLOAT_STRINGS form is applied even
        # when the source stored them as bare integers.
        for function in payload["functions"]:
            function["device"] = prettify_label(function.get("device", ""))
            function["name"] = prettify_label(function.get("name", ""))
            ensure_default_fields(function)
            normalize_special_floats(function)
            normalize_scaled_for_export(function)

        # Order by whichever method is active (device/action, or device-name then
        # name) — the same ordering the Full View shows.
        payload["functions"] = sorted(payload["functions"], key=self._current_sort_key())

        # On save, cast every numeric value to a string throughout the file.
        return cast_numbers_to_strings(payload)

    def _confirm_save_despite_collisions(self) -> bool:
        """True when the profile has no collisions or the person chose to save anyway."""
        groups = self._find_collisions(self._data.get("functions", []))
        if not groups:
            return True
        involved_count = sum(len(group["entries"]) for group in groups)
        return messagebox.askyesno(
            "Collisions Detected",
            f"This profile has {len(groups)} collision"
            f"{'' if len(groups) == 1 else 's'} "
            f"involving {involved_count} function"
            f"{'' if involved_count == 1 else 's'} "
            "(shared Export ID(Arg), or Device ID + Action ID).\n\n"
            "These are listed on the Collisions tab.\n\n"
            "Do you want to proceed with saving anyway?",
            parent=self)

    @staticmethod
    def _new_interface_script_note(path) -> str:
        """Create the .lua script of a new interface; the text telling how that went."""
        try:
            script_path = create_interface_script(path)
        except OSError as script_error:
            return f"\n\nThe script could not be created:\n{script_error}"
        return f"\n\nScript created:\n{script_path}" if script_path else ""

    def _write(self, path, new_interface=False):
        """Write the profile to path in Helios format, first asking whether to continue when
        collisions exist; marks the document saved."""
        if not self._confirm_save_despite_collisions():
            return False
        saved_payload = self._build_save_payload()
        try:
            with open(path, "w", encoding="utf-8") as profile_file:
                json.dump(saved_payload, profile_file, indent=2)
            self._mark_clean()                   # a successful save makes the current state the clean baseline
            self._pending_saved_editor_syncs[self._sync_path_key(path)] = {
                "source": "json",
                "path": path,
                "content": json.dumps(saved_payload, indent=2),
            }
            self._sync_saved_editor_changes()    # the Text Editor copy takes the saved file at once
            script_note = self._new_interface_script_note(path) if new_interface else ""
            messagebox.showinfo("Saved", f"File saved:\n{path}{script_note}", parent=self)
        except Exception as error:
            messagebox.showerror("Save Failed", str(error), parent=self)
            return False
        self._offer_recently_added_devices(saved_payload)
        return True

    def _offer_recently_added_devices(self, saved_payload=None):
        """After a successful save: when devices were added since the last save, ask whether to
        list them (popup table), then start counting again from this save."""
        added = [function for function in self._data.get("functions", []) if function.get(ADDED_FLAG)]
        if added and messagebox.askyesno(
                "Recently Added Devices",
                f"{len(added)} device{'' if len(added) == 1 else 's'} added since the last save.\n\n"
                "Would you like a list of them?", parent=self):
            self._show_recently_added_devices(added)
        for function in self._data.get("functions", []):
            function.pop(ADDED_FLAG, None)

    @staticmethod
    def recently_added_rows(added_functions):
        """(Device Name, Name, Device Type) for each added device, sorted by device type and
        then name (then device name), the labels as the saved file shows them."""
        rows = [(prettify_label(function.get("device", "")),
                 prettify_label(function.get("name", "")),
                 TAB_LABELS.get(function.get("heliosType", ""), function.get("heliosType", "")))
                for function in added_functions]
        return sorted(rows, key=lambda row: (row[2].lower(), row[1].lower(), row[0].lower()))

    def _show_recently_added_devices(self, added_functions):
        """Popup with a table of the devices added since the last save."""
        rows = self.recently_added_rows(added_functions)
        window = tk.Toplevel(self)
        window.transient(self)
        window.title(f"Recently Added Devices  ({len(rows)})")
        window.configure(bg=PANEL_BG)
        width, height = 640, 380
        position_x, position_y = centered_position_on_parent(self, width, height)
        window.geometry(f"{width}x{height}+{position_x}+{position_y}")
        container = tk.Frame(window, bg=PANEL_BG)
        container.pack(fill="both", expand=True, padx=8, pady=8)
        scrollbar = ttk.Scrollbar(container, orient="vertical")
        table = ttk.Treeview(container, columns=("device", "name", "type"), show="headings",
                             selectmode="browse", yscrollcommand=scrollbar.set)
        scrollbar.configure(command=table.yview)
        for column_id, heading, column_width in (("device", "Device Name", 190),
                                                 ("name", "Name", 270), ("type", "Device Type", 140)):
            table.heading(column_id, text=heading, anchor="w")
            table.column(column_id, width=column_width, minwidth=60, stretch=True, anchor="w")
        table.tag_configure("even", background=ROW_EVEN)
        table.tag_configure("odd", background=ROW_ODD)
        scrollbar.pack(side="right", fill="y")
        table.pack(side="left", fill="both", expand=True)
        for row_number, row in enumerate(rows):
            table.insert("", "end", values=row, tags=("even" if row_number % 2 == 0 else "odd",))
        self._recently_added_table = table                       # (kept for tests)
        tk.Button(window, text="Close", bg=ACCENT, fg=DARK_BG, font=FONT_HEAD, relief="flat",
                  padx=16, pady=4, cursor="hand2", command=window.destroy).pack(side="bottom", pady=(0, 8))


if __name__ == "__main__":
    app = HeliosEditor()
    app.mainloop()
