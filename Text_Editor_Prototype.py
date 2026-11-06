"""Standalone Tkinter text editor prototype for eventual Helios integration."""

import difflib
import os
import re
import tkinter as tk
from collections import Counter
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
import tkinter.font as tkfont


APP_TITLE = "Helios Text Editor Prototype"
TEXT_FONT = ("Consolas", 10)
UI_FONT = ("Segoe UI", 9)
LINE_NUMBER_FONT = ("Consolas", 9)
TAB_WIDTH = 4

THEMES = {
    "Default Palette": {
        "window": "#f0f0f0",
        "panel": "#f0f0f0",
        "tab": "#e5e5e5",
        "text_bg": "#ffffff",
        "text_fg": "#202020",
        "gutter_bg": "#e9e9e9",
        "gutter_fg": "#707070",
        "selection": "#b7d7f5",
        "bookmark": "#0078d7",
        "find": "#ffe082",
        "added": "#cdeed6",
        "removed": "#fde7e9",
        "changed": "#fff1a8",
        "border": "#adadad",
        "accent": "#0078d7",
    },
    "Dark Mode - Default": {
        "window": "#1a1f2e",
        "panel": "#1e2436",
        "tab": "#252b3b",
        "text_bg": "#252b3b",
        "text_fg": "#e8eaf0",
        "gutter_bg": "#202638",
        "gutter_fg": "#8b92a8",
        "selection": "#3a5a8c",
        "bookmark": "#4a9eff",
        "find": "#806820",
        "added": "#1f4a2e",
        "removed": "#4a1a2a",
        "changed": "#5a4a12",
        "border": "#363d52",
        "accent": "#4a9eff",
    },
    "Dark Mode - Grayscale": {
        "window": "#202020",
        "panel": "#242424",
        "tab": "#2b2b2b",
        "text_bg": "#2b2b2b",
        "text_fg": "#e8e8e8",
        "gutter_bg": "#252525",
        "gutter_fg": "#a0a0a0",
        "selection": "#505050",
        "bookmark": "#4a9eff",
        "find": "#806820",
        "added": "#1f4a2e",
        "removed": "#4a1a2a",
        "changed": "#5a4a12",
        "border": "#454545",
        "accent": "#c4c4c4",
    },
}

FILE_TYPES = [
    ("Text and source files", "*.txt *.py *.json *.lua *.xml *.ini *.cfg *.csv *.md *.log"),
    ("All files", "*.*"),
]


def read_text_file(path):
    """Read a text file while retaining its encoding and predominant newline style."""
    data = Path(path).read_bytes()
    if data.startswith((b"\xff\xfe\x00\x00", b"\x00\x00\xfe\xff")):
        encoding = "utf-32"
    elif data.startswith((b"\xff\xfe", b"\xfe\xff")):
        encoding = "utf-16"
    elif data.startswith(b"\xef\xbb\xbf"):
        encoding = "utf-8-sig"
    else:
        try:
            data.decode("utf-8")
            encoding = "utf-8"
        except UnicodeDecodeError:
            try:
                data.decode("cp1252")
                encoding = "cp1252"
            except UnicodeDecodeError:
                encoding = "latin-1"

    text = data.decode(encoding)
    if "\x00" in text and not encoding.startswith(("utf-16", "utf-32")):
        raise UnicodeError("This file appears to contain binary data, not editable text.")
    newline_counts = Counter(re.findall(r"\r\n|\r|\n", text))
    newline = newline_counts.most_common(1)[0][0] if newline_counts else os.linesep
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    return normalized, encoding, newline


class LineNumberedText(ttk.Frame):
    """A Tk Text widget with a synchronized line-number gutter and scrollbars."""

    def __init__(self, parent, theme, readonly=False, app=None):
        super().__init__(parent)
        self.theme = theme
        self.readonly = readonly
        self.app = app
        self.frame_style = "TFrame" if getattr(app, "embedded", False) else "Editor.TFrame"
        self._redraw_after_id = None
        self.bind("<Destroy>", self._cancel_scheduled_redraw, add="+")
        self.bookmark_marks = set()
        self._next_bookmark_mark = 1
        self.text_font = tkfont.Font(self, font=TEXT_FONT)
        self.number_font = tkfont.Font(self, font=LINE_NUMBER_FONT)
        self.gutter = tk.Canvas(self, width=48, highlightthickness=0, bd=0)
        self.text = tk.Text(
            self,
            wrap="none",
            undo=True,
            maxundo=-1,
            autoseparators=True,
            font=self.text_font,
            tabs=(self.text_font.measure(" " * TAB_WIDTH),),
            padx=6,
            pady=4,
            borderwidth=0,
            highlightthickness=0,
        )
        self.vertical_scrollbar = ttk.Scrollbar(self, orient="vertical", command=self.text.yview)
        self.horizontal_scrollbar = ttk.Scrollbar(self, orient="horizontal", command=self.text.xview)
        self.text.configure(yscrollcommand=self._on_vertical_scroll,
                            xscrollcommand=self.horizontal_scrollbar.set)
        self.gutter.grid(row=0, column=0, sticky="ns")
        self.text.grid(row=0, column=1, sticky="nsew")
        self.vertical_scrollbar.grid(row=0, column=2, sticky="ns")
        self.horizontal_scrollbar.grid(row=1, column=1, sticky="ew")
        self.rowconfigure(0, weight=1)
        self.columnconfigure(1, weight=1)
        self.text.bind("<Configure>", self._schedule_redraw, add="+")
        self.text.bind("<KeyRelease>", self._schedule_redraw, add="+")
        self.text.bind("<<Modified>>", self._on_modified)
        self.text.edit_modified(False)
        self.context_menu = tk.Menu(self.text, tearoff=False)
        if app is not None and not readonly:
            self.context_menu.add_command(
                label="Cut", command=self._cut, accelerator="Ctrl+X")
            self.context_menu.add_command(
                label="Copy", command=self._copy, accelerator="Ctrl+C")
            self.context_menu.add_command(
                label="Paste", command=self._paste, accelerator="Ctrl+V")
            self.context_menu.add_separator()
            self.context_menu.add_command(
                label="Undo", command=self._undo, accelerator="Ctrl+Z")
            self.context_menu.add_command(
                label="Redo", command=self._redo, accelerator="Ctrl+Y")
            self.context_menu.add_separator()
            self.context_menu.add_command(
                label="Select All", command=app._select_all, accelerator="Ctrl+A")
            self.context_menu.add_command(
                label="Find…", command=app.show_find, accelerator="Ctrl+F")
            self.context_menu.add_command(
                label="Find Next", command=app._find_next, accelerator="F3")
        else:
            self.context_menu.add_command(label="Copy", command=self._copy)
            self.context_menu.add_command(
                label="Paste", command=self._paste, state="disabled" if readonly else "normal")
            self.context_menu.add_separator()
            self.context_menu.add_command(
                label="Undo", command=self._undo, state="disabled" if readonly else "normal")
            self.context_menu.add_command(
                label="Redo", command=self._redo, state="disabled" if readonly else "normal")
        self.text.bind("<Button-3>", self._show_context_menu, add="+")
        if app is not None and not readonly:
            for sequence, action in (
                    ("<Control-a>", app._select_all),
                    ("<Control-Tab>", app._next_tab),
                    ("<Control-Shift-Tab>", app._previous_tab)):
                self.text.bind(
                    sequence,
                    lambda _event, callback=action: app._run_shortcut(callback),
                    add="+",
                )
        if not readonly:
            self.gutter.bind("<Button-1>", self._toggle_bookmark)
        self.apply_theme(theme)
        if readonly:
            self.text.configure(undo=False)

    def _undo(self):
        try:
            self.text.edit_undo()
        except tk.TclError:
            pass

    def _redo(self):
        try:
            self.text.edit_redo()
        except tk.TclError:
            pass

    def _cut(self):
        self.text.focus_set()
        self.text.event_generate("<<Cut>>")

    def _copy(self):
        self.text.focus_set()
        self.text.event_generate("<<Copy>>")

    def _paste(self):
        self.text.focus_set()
        self.text.event_generate("<<Paste>>")

    def _show_context_menu(self, event):
        self.text.focus_set()
        try:
            self.context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.context_menu.grab_release()
        return "break"

    def _on_vertical_scroll(self, first, last):
        self.vertical_scrollbar.set(first, last)
        self._redraw_line_numbers()

    def _schedule_redraw(self, _event=None):
        if self._redraw_after_id is None and self.winfo_exists():
            self._redraw_after_id = self.after_idle(self._run_scheduled_redraw)

    def _run_scheduled_redraw(self):
        self._redraw_after_id = None
        self._redraw_line_numbers()

    def _cancel_scheduled_redraw(self, event):
        if event.widget is self and self._redraw_after_id is not None:
            try:
                self.after_cancel(self._redraw_after_id)
            except tk.TclError:
                pass
            self._redraw_after_id = None

    def _bookmark_center_x(self, line, gutter_width):
        number_right = 6 + self.number_font.measure(str(line))
        return (number_right + gutter_width) / 2

    def _toggle_bookmark(self, event):
        try:
            line = int(self.text.index(f"@0,{event.y}").split(".")[0])
        except tk.TclError:
            return "break"
        if self.text.dlineinfo(f"{line}.0") is None:
            return "break"
        gutter_width = self.gutter.winfo_width()
        marker_x = self._bookmark_center_x(line, gutter_width)
        if abs(event.x - marker_x) > 8:
            if event.x <= 9 + self.number_font.measure(str(line)):
                self.text.tag_remove("sel", "1.0", "end")
                self.text.tag_add("sel", f"{line}.0", f"{line + 1}.0")
                self.text.mark_set("insert", f"{line}.0")
                self.text.see(f"{line}.0")
                self.text.focus_set()
            return "break"
        existing_mark = next(
            (mark for mark in self.bookmark_marks
             if int(self.text.index(mark).split(".")[0]) == line),
            None,
        )
        if existing_mark is not None:
            self.text.mark_unset(existing_mark)
            self.bookmark_marks.remove(existing_mark)
        else:
            mark = f"bookmark_{self._next_bookmark_mark}"
            self._next_bookmark_mark += 1
            self.text.mark_set(mark, f"{line}.0")
            self.text.mark_gravity(mark, "right")
            self.bookmark_marks.add(mark)
        self._schedule_redraw()
        return "break"

    def _redraw_line_numbers(self):
        if not self.winfo_exists():
            return
        self.gutter.delete("all")
        line_count = int(self.text.index("end-1c").split(".")[0])
        digits = len(str(max(1, line_count)))
        gutter_width = max(48, self.number_font.measure("9" * digits) + 30)
        self.gutter.configure(width=gutter_width, bg=self.theme["gutter_bg"])
        bookmark_lines = {
            int(self.text.index(mark).split(".")[0]) for mark in self.bookmark_marks
        }
        try:
            line = int(self.text.index("@0,0").split(".")[0])
        except tk.TclError:
            return
        while True:
            line_info = self.text.dlineinfo(f"{line}.0")
            if line_info is None or line_info[1] >= self.text.winfo_height():
                break
            if line in bookmark_lines:
                center_y = line_info[1] + line_info[3] / 2
                marker_x = self._bookmark_center_x(line, gutter_width)
                self.gutter.create_oval(
                    marker_x - 5,
                    center_y - 5,
                    marker_x + 5,
                    center_y + 5,
                    fill=self.theme["bookmark"],
                    outline=self.theme["bookmark"],
                    tags=("bookmark",),
                )
            self.gutter.create_text(
                6,
                line_info[1],
                anchor="nw",
                text=str(line),
                fill=self.theme["gutter_fg"],
                font=self.number_font,
                tags=("line_number",),
            )
            line += 1

    def _on_modified(self, _event=None):
        if self.text.edit_modified():
            self.text.edit_modified(False)
            if not self.readonly:
                self.event_generate("<<DocumentChanged>>", when="tail")
            self._schedule_redraw()

    def apply_theme(self, theme):
        self.theme = theme
        self.configure(style=self.frame_style)
        self.context_menu.configure(
            bg=theme["tab"],
            fg=theme["text_fg"],
            activebackground=theme["accent"],
            activeforeground=theme["text_fg"],
        )
        self.gutter.configure(bg=theme["gutter_bg"])
        self.text.configure(
            bg=theme["text_bg"],
            fg=theme["text_fg"],
            insertbackground=theme["text_fg"],
            selectbackground=theme["selection"],
            selectforeground=theme["text_fg"],
        )
        self.text.tag_configure("find_match", background=theme["find"])
        self.text.tag_configure("compare_added", background=theme["added"])
        self.text.tag_configure("compare_removed", background=theme["removed"])
        self.text.tag_configure("compare_changed", background=theme["changed"])
        self._schedule_redraw()


class TextEditorPrototype:
    def __init__(self, root, parent=None, embedded=False, theme=None,
                 create_initial_document=True):
        self.root = root.winfo_toplevel()
        self.parent = parent if parent is not None else root
        self.embedded = embedded
        if not embedded:
            self.root.title(APP_TITLE)
            self.root.geometry("1100x760")
        self.documents = []
        self.theme_name = "Default Palette"
        self.theme = theme or THEMES[self.theme_name]
        self.find_window = None
        self.find_context_menu = None
        self.find_context_entry = None
        self.find_entry = None
        self.replace_find_entry = None
        self.replace_with_entry = None
        self.find_tabs = None
        self.find_tab = None
        self.replace_tab = None
        self.find_var = None
        self.replace_with_var = None
        self.match_case = None
        if not embedded:
            self._setup_styles()
            self._build_menu()
        self.notebook = ttk.Notebook(self.parent)
        self.notebook.pack(
            fill="both", expand=True,
            padx=0 if embedded else 6,
            pady=(0, 0) if embedded else (0, 4),
        )
        self.status = ttk.Label(self.parent, anchor="w", padding=(8, 3))
        self.status.pack(fill="x")
        self.notebook.bind("<<NotebookTabChanged>>", self._update_title)
        self.notebook.bind("<Button-1>", self._on_tab_click, add="+")
        self.notebook.bind(
            "<Control-Tab>", lambda _event: self._run_shortcut(self._next_tab), add="+")
        self.notebook.bind(
            "<Control-Shift-Tab>",
            lambda _event: self._run_shortcut(self._previous_tab),
            add="+",
        )
        if not embedded:
            self.root.protocol("WM_DELETE_WINDOW", self._on_exit)
            self._bind_shortcuts()
        if create_initial_document:
            self.new_document(replace_on_open=True)

    def _setup_styles(self):
        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("TFrame", background=self.theme["panel"])
        style.configure("TLabel", background=self.theme["panel"], foreground=self.theme["text_fg"],
                        font=UI_FONT)
        style.configure("TNotebook", background=self.theme["window"], borderwidth=0)
        style.configure("TNotebook.Tab", background=self.theme["tab"], foreground=self.theme["text_fg"],
                        font=UI_FONT, padding=(10, 6))
        style.map("TNotebook.Tab",
                  background=[("selected", self.theme["panel"])],
                  foreground=[("selected", self.theme["accent"])])
        style.configure("Find.TNotebook", background=self.theme["window"], borderwidth=0)
        style.configure(
            "Find.TNotebook.Tab",
            background=self.theme["tab"],
            foreground=self.theme["text_fg"],
            font=UI_FONT,
            padding=(10, 6),
            borderwidth=1,
            bordercolor=self.theme["border"],
            lightcolor=self.theme["tab"],
            darkcolor=self.theme["tab"],
        )
        style.map(
            "Find.TNotebook.Tab",
            background=[("selected", self.theme["selection"])],
            foreground=[("selected", self.theme["text_fg"])],
            font=[("selected", (UI_FONT[0], UI_FONT[1], "bold"))],
            borderwidth=[("selected", 2)],
        )
        style.configure("Vertical.TScrollbar", background=self.theme["tab"],
                        troughcolor=self.theme["window"], bordercolor=self.theme["border"])
        style.configure("Horizontal.TScrollbar", background=self.theme["tab"],
                        troughcolor=self.theme["window"], bordercolor=self.theme["border"])
        style.configure("Editor.TFrame", background=self.theme["panel"])
        self.root.configure(bg=self.theme["window"])

    def _build_menu(self, menu_bar=None, menu_options=None, action_handler=None):
        standalone = menu_bar is None
        if menu_options is None:
            menu_options = {
                "tearoff": False,
                "bg": self.theme["tab"],
                "fg": self.theme["text_fg"],
                "activebackground": self.theme["accent"],
                "activeforeground": self.theme["text_fg"],
                "font": UI_FONT,
            }
        if standalone:
            menu_bar = tk.Menu(self.root, **menu_options)

        def invoke(method, *args):
            if action_handler is not None:
                return action_handler(method, *args)
            return getattr(self, method)(*args)

        text_editor_menu = tk.Menu(menu_bar, **menu_options)
        text_editor_menu.add_command(
            label="New", command=lambda: invoke("new_document"), accelerator="Ctrl+N")
        text_editor_menu.add_command(
            label="Open…", command=lambda: invoke("open_files"), accelerator="Ctrl+O")
        text_editor_menu.add_separator()
        text_editor_menu.add_command(
            label="Save", command=lambda: invoke("save_current"), accelerator="Ctrl+S")
        text_editor_menu.add_command(
            label="Save As…", command=lambda: invoke("save_current_as"),
            accelerator="Ctrl+Shift+S")
        text_editor_menu.add_separator()
        text_editor_menu.add_command(
            label="Close Tab", command=lambda: invoke("close_current"), accelerator="Ctrl+W")
        if not self.embedded:
            text_editor_menu.add_command(label="Exit", command=self._on_exit)

        edit_menu = tk.Menu(text_editor_menu, **menu_options)
        edit_menu.add_command(
            label="Undo", command=lambda: invoke("_undo_current"), accelerator="Ctrl+Z")
        edit_menu.add_command(
            label="Redo", command=lambda: invoke("_redo_current"), accelerator="Ctrl+Y")
        edit_menu.add_separator()
        edit_menu.add_command(
            label="Cut", command=lambda: invoke("_text_event", "<<Cut>>"))
        edit_menu.add_command(
            label="Copy", command=lambda: invoke("_text_event", "<<Copy>>"))
        edit_menu.add_command(
            label="Paste", command=lambda: invoke("_text_event", "<<Paste>>"))
        edit_menu.add_command(
            label="Select All", command=lambda: invoke("_select_all"), accelerator="Ctrl+A")
        edit_menu.add_separator()
        edit_menu.add_command(
            label="Find…", command=lambda: invoke("show_find"), accelerator="Ctrl+F")
        edit_menu.add_command(
            label="Find Next", command=lambda: invoke("_find_next"), accelerator="F3")
        text_editor_menu.add_separator()
        text_editor_menu.add_cascade(label="Edit", menu=edit_menu)

        tools_menu = tk.Menu(text_editor_menu, **menu_options)
        tools_menu.add_command(
            label="Compare Current with File…", command=lambda: invoke("compare_with_file"))
        text_editor_menu.add_cascade(label="Tools", menu=tools_menu)

        menu_bar.add_cascade(label="Text Editor", menu=text_editor_menu)
        if standalone:
            self.root.configure(menu=menu_bar)
        self.menus = (menu_bar, text_editor_menu, edit_menu, tools_menu)
        return text_editor_menu

    def _bind_shortcuts(self):
        bindings = {
            "<Control-n>": self.new_document,
            "<Control-o>": self.open_files,
            "<Control-s>": self.save_current,
            "<Control-Shift-S>": self.save_current_as,
            "<Control-w>": self.close_current,
            "<Control-f>": self.show_find,
            "<F3>": self._find_next,
            "<Control-z>": self._undo_current,
            "<Control-y>": self._redo_current,
            "<Control-a>": self._select_all,
            "<Control-Tab>": self._next_tab,
            "<Control-Shift-Tab>": self._previous_tab,
        }
        for sequence, callback in bindings.items():
            self.root.bind_all(sequence, lambda _event, action=callback: self._run_shortcut(action))

    def _run_shortcut(self, action):
        action()
        return "break"

    def new_document(self, _event=None, replace_on_open=False):
        editor = LineNumberedText(self.notebook, self.theme, app=self)
        document = {
            "frame": editor,
            "editor": editor,
            "path": None,
            "encoding": "utf-8",
            "newline": os.linesep,
            "saved_content": "",
            "dirty": False,
            "replace_on_open": replace_on_open,
        }
        editor.pack(fill="both", expand=True)
        editor.bind("<<DocumentChanged>>",
                    lambda _event, current=document: self._document_changed(current))
        self.documents.append(document)
        self.notebook.add(editor, text="Untitled")
        self.notebook.select(editor)
        editor.text.focus_set()
        editor.text.bind("<KeyRelease>", self._update_title, add="+")
        self._refresh_tab_labels()
        self._update_title()
        return document

    def _current_document(self):
        selected = self.notebook.select()
        return next((document for document in self.documents
                     if str(document["frame"]) == selected), None)

    def _document_changed(self, document):
        content = document["editor"].text.get("1.0", "end-1c")
        document["dirty"] = content != document["saved_content"]
        self._refresh_tab_labels()
        self._update_title()

    def _refresh_tab_labels(self):
        untitled = [document for document in self.documents if document["path"] is None]
        for document in self.documents:
            if document["path"] is not None:
                label = Path(document["path"]).name
            elif len(untitled) == 1:
                label = "Untitled"
            else:
                label = f"Untitled {untitled.index(document) + 1}"
            if document["dirty"]:
                label += " *"
            label += "  ×"
            self.notebook.tab(document["frame"], text=label)

    def _on_tab_click(self, event):
        try:
            tab_index = self.notebook.index(f"@{event.x},{event.y}")
        except tk.TclError:
            return
        right = event.x
        while right + 1 < self.notebook.winfo_width():
            try:
                adjacent_tab = self.notebook.index(f"@{right + 1},{event.y}")
            except tk.TclError:
                break
            if adjacent_tab != tab_index:
                break
            right += 1
        if event.x < right - 22:
            return
        tab_path = self.notebook.tabs()[tab_index]
        document = next(
            (item for item in self.documents if str(item["frame"]) == tab_path),
            None,
        )
        self._close_document(document)
        return "break"

    def _update_title(self, _event=None):
        document = self._current_document()
        if document is None:
            if not self.embedded:
                self.root.title(APP_TITLE)
            self.status.configure(text="No document")
            return
        label = Path(document["path"]).name if document["path"] else "Untitled"
        if not self.embedded:
            self.root.title(f"{APP_TITLE} — {label}{' *' if document['dirty'] else ''}")
        line, column = document["editor"].text.index("insert").split(".")
        self.status.configure(
            text=f"{document['encoding']}    {document['newline'].replace(chr(13), 'CR').replace(chr(10), 'LF')}    "
                 f"Line {line}, Column {int(column) + 1}")

    def open_files(self, _event=None):
        paths = filedialog.askopenfilenames(
            title="Open Text Files", filetypes=FILE_TYPES, parent=self.root)
        for path in paths:
            self.open_path(path)

    def open_path(self, path):
        path = str(Path(path).resolve())
        existing = next((document for document in self.documents
                         if document["path"] and os.path.normcase(document["path"]) == os.path.normcase(path)),
                        None)
        if existing:
            self.notebook.select(existing["frame"])
            return
        try:
            content, encoding, newline = read_text_file(path)
        except (OSError, UnicodeError) as error:
            messagebox.showerror("Open Failed", str(error), parent=self.root)
            return
        document = next(
            (
                candidate for candidate in self.documents
                if candidate["replace_on_open"]
                and candidate["path"] is None
                and not candidate["dirty"]
                and candidate["editor"].text.get("1.0", "end-1c") == ""
            ),
            None,
        )
        if document is None:
            document = self.new_document()
        document["path"] = path
        document["encoding"] = encoding
        document["newline"] = newline
        document["saved_content"] = content
        document["replace_on_open"] = False
        text_widget = document["editor"].text
        text_widget.insert("1.0", content)
        text_widget.edit_modified(False)
        document["dirty"] = False
        self.notebook.select(document["frame"])
        self._refresh_tab_labels()
        self._update_title()

    def _save_document(self, document, save_as=False):
        if document is None:
            return False
        path = document["path"]
        if save_as or path is None:
            path = filedialog.asksaveasfilename(
                title="Save Text File",
                defaultextension=".txt",
                filetypes=FILE_TYPES,
                initialfile=Path(path).name if path else "",
                parent=self.root,
            )
            if not path:
                return False
        text = document["editor"].text.get("1.0", "end-1c")
        if document["newline"] != "\n":
            text = text.replace("\n", document["newline"])
        try:
            Path(path).write_bytes(text.encode(document["encoding"]))
        except (OSError, UnicodeError) as error:
            messagebox.showerror("Save Failed", str(error), parent=self.root)
            return False
        document["path"] = str(Path(path).resolve())
        document["saved_content"] = text
        document["dirty"] = False
        document["editor"].text.edit_modified(False)
        self._refresh_tab_labels()
        self._update_title()
        return True

    def save_current(self, _event=None):
        return self._save_document(self._current_document())

    def save_current_as(self, _event=None):
        return self._save_document(self._current_document(), save_as=True)

    def _confirm_close(self, document):
        if not document["dirty"]:
            return True
        name = Path(document["path"]).name if document["path"] else "Untitled"
        choice = messagebox.askyesnocancel(
            "Unsaved Changes",
            f"Save changes to {name} before closing?",
            parent=self.root,
        )
        if choice is None:
            return False
        return self._save_document(document) if choice else True

    def close_current(self, _event=None):
        return self._close_document(self._current_document())

    def _close_document(self, document):
        if document is None or not self._confirm_close(document):
            return False
        was_selected = self.notebook.select() == str(document["frame"])
        old_index = self.notebook.index(document["frame"])
        self.notebook.forget(document["frame"])
        document["editor"].destroy()
        self.documents.remove(document)
        if not self.documents:
            self.new_document(replace_on_open=True)
        elif was_selected:
            self.notebook.select(min(old_index, len(self.documents) - 1))
        self._refresh_tab_labels()
        self._update_title()
        return True

    def _on_exit(self):
        if not self.confirm_exit():
            return
        self.root.destroy()

    def confirm_exit(self):
        for document in list(self.documents):
            if not self._confirm_close(document):
                return False
        return True

    def export_state(self):
        selected_index = self.notebook.index("current") if self.documents else 0
        documents = []
        for document in self.documents:
            text = document["editor"].text
            documents.append({
                "path": document["path"],
                "encoding": document["encoding"],
                "newline": document["newline"],
                "saved_content": document["saved_content"],
                "dirty": document["dirty"],
                "replace_on_open": document["replace_on_open"],
                "content": text.get("1.0", "end-1c"),
                "insert": text.index("insert"),
                "selection": tuple(map(str, text.tag_ranges("sel"))),
                "bookmarks": sorted(
                    int(text.index(mark).split(".")[0])
                    for mark in document["editor"].bookmark_marks
                ),
            })

        find_visible = (
            self.find_window is not None
            and self.find_window.winfo_exists()
            and self.find_window.state() != "withdrawn"
        )
        find_state = {
            "visible": find_visible,
            "query": self.find_var.get() if self.find_var is not None else "",
            "replacement": (
                self.replace_with_var.get() if self.replace_with_var is not None else ""
            ),
            "match_case": self.match_case.get() if self.match_case is not None else False,
            "replace_tab": (
                self.find_tabs.index("current") == 1
                if self.find_tabs is not None and self.find_tabs.winfo_exists()
                else False
            ),
        }
        if self.find_window is not None and self.find_window.winfo_exists():
            self.find_window.destroy()
        self.find_window = None
        self.find_context_menu = None
        self.find_context_entry = None
        self.find_entry = None
        self.replace_find_entry = None
        self.replace_with_entry = None
        self.find_var = None
        self.replace_with_var = None
        self.match_case = None
        return {
            "documents": documents,
            "selected_index": selected_index,
            "find": find_state,
        }

    def restore_state(self, state):
        for item in state.get("documents", []):
            document = self.new_document(
                replace_on_open=item.get("replace_on_open", False))
            document.update({
                "path": item.get("path"),
                "encoding": item.get("encoding", "utf-8"),
                "newline": item.get("newline", os.linesep),
                "saved_content": item.get("saved_content", ""),
                "dirty": item.get("dirty", False),
                "replace_on_open": item.get("replace_on_open", False),
            })
            editor = document["editor"]
            text = editor.text
            content = item.get("content", "")
            if content:
                text.insert("1.0", content)
            text.edit_modified(False)
            for bookmark_index, line in enumerate(item.get("bookmarks", []), start=1):
                mark = f"bookmark_{bookmark_index}"
                text.mark_set(mark, f"{line}.0")
                text.mark_gravity(mark, "right")
                editor.bookmark_marks.add(mark)
            editor._next_bookmark_mark = len(editor.bookmark_marks) + 1
            try:
                text.mark_set("insert", item.get("insert", "1.0"))
                for start, end in zip(
                        item.get("selection", ())[::2],
                        item.get("selection", ())[1::2]):
                    text.tag_add("sel", start, end)
            except tk.TclError:
                text.mark_set("insert", "1.0")
            editor._schedule_redraw()

        if not self.documents:
            self.new_document(replace_on_open=True)
        self.notebook.select(min(state.get("selected_index", 0), len(self.documents) - 1))
        self._refresh_tab_labels()
        self._update_title()

        find_state = state.get("find", {})
        if find_state.get("visible"):
            self.show_find()
            self.find_var.set(find_state.get("query", ""))
            self.replace_with_var.set(find_state.get("replacement", ""))
            self.match_case.set(find_state.get("match_case", False))
            if find_state.get("replace_tab"):
                self.find_tabs.select(self.replace_tab)

    def _active_text(self):
        document = self._current_document()
        return document["editor"].text if document else None

    def _text_event(self, event_name):
        text = self._active_text()
        if text is not None:
            text.event_generate(event_name)
            text.focus_set()

    def _undo_current(self):
        text = self._active_text()
        if text is not None:
            try:
                text.edit_undo()
            except tk.TclError:
                pass

    def _redo_current(self):
        text = self._active_text()
        if text is not None:
            try:
                text.edit_redo()
            except tk.TclError:
                pass

    def _select_all(self):
        text = self._active_text()
        if text is not None:
            text.tag_add("sel", "1.0", "end-1c")
            text.mark_set("insert", "1.0")
            text.see("insert")
            text.focus_set()

    def _next_tab(self):
        if self.documents:
            index = self.notebook.index("current")
            self.notebook.select((index + 1) % len(self.documents))

    def _previous_tab(self):
        if self.documents:
            index = self.notebook.index("current")
            self.notebook.select((index - 1) % len(self.documents))

    def _position_find_window(self):
        self.root.update_idletasks()
        self.find_window.update_idletasks()
        root_x = self.root.winfo_rootx()
        root_y = self.root.winfo_rooty()
        root_width = self.root.winfo_width()
        root_height = self.root.winfo_height()
        window_width = self.find_window.winfo_reqwidth()
        window_height = self.find_window.winfo_reqheight()
        target_x = root_x + max((root_width - window_width) // 2, 0)
        target_y = root_y + max((root_height - window_height) // 2, 0)
        self.find_window.geometry(f"+{target_x}+{target_y}")
        self.find_window.update_idletasks()
        x = target_x * 2 - self.find_window.winfo_rootx()
        y = target_y * 2 - self.find_window.winfo_rooty()
        self.find_window.geometry(f"+{x}+{y}")

    def show_find(self, _event=None):
        if self.find_window is not None and self.find_window.winfo_exists():
            self.find_window.deiconify()
            self._position_find_window()
            self.find_window.lift()
            current_tab = self.find_tabs.select()
            if current_tab == str(self.replace_tab):
                self.replace_find_entry.focus_set()
            else:
                self.find_entry.focus_set()
            return
        self.find_window = tk.Toplevel(self.root)
        self.find_window.withdraw()
        self.find_window.title("Find and Replace")
        self.find_window.transient(self.root)
        self.find_window.resizable(False, False)
        body = ttk.Frame(self.find_window, padding=10)
        body.grid(row=0, column=0, sticky="nsew")
        self.find_var = tk.StringVar(master=self.find_window, value="")
        self.replace_with_var = tk.StringVar(master=self.find_window, value="")
        self.find_tabs = ttk.Notebook(body, style="Find.TNotebook")
        self.find_tabs.grid(row=0, column=0, sticky="nsew")
        self.find_tab = ttk.Frame(self.find_tabs, padding=8)
        self.replace_tab = ttk.Frame(self.find_tabs, padding=8)
        self.find_tabs.add(self.find_tab, text="Find")
        self.find_tabs.add(self.replace_tab, text="Replace")

        ttk.Label(self.find_tab, text="Find What:").grid(row=0, column=0, sticky="w")
        self.find_entry = ttk.Entry(self.find_tab, textvariable=self.find_var, width=36)
        self.find_entry.grid(row=0, column=1, columnspan=2, sticky="ew", padx=(8, 0))
        self.match_case = tk.BooleanVar(master=self.find_window, value=False)
        ttk.Checkbutton(self.find_tab, text="Match case", variable=self.match_case).grid(
            row=1, column=1, sticky="w", pady=(8, 0))
        ttk.Button(self.find_tab, text="Previous",
                   command=lambda: self._find_next(backwards=True)).grid(
            row=2, column=1, sticky="e", pady=(10, 0), padx=(0, 6))
        ttk.Button(self.find_tab, text="Find Next", command=self._find_next).grid(
            row=2, column=2, sticky="e", pady=(10, 0))

        ttk.Label(self.replace_tab, text="Find What:").grid(row=0, column=0, sticky="w")
        self.replace_find_entry = ttk.Entry(
            self.replace_tab, textvariable=self.find_var, width=36)
        self.replace_find_entry.grid(row=0, column=1, sticky="ew", padx=(8, 0))
        ttk.Label(self.replace_tab, text="Replace With:").grid(
            row=1, column=0, sticky="w", pady=(8, 0))
        self.replace_with_entry = ttk.Entry(
            self.replace_tab, textvariable=self.replace_with_var, width=36)
        self.replace_with_entry.grid(
            row=1, column=1, sticky="ew", padx=(8, 0), pady=(8, 0))
        replace_buttons = ttk.Frame(self.replace_tab)
        replace_buttons.grid(row=2, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(replace_buttons, text="Find Next", command=self._find_next).pack(
            side="left", padx=(0, 6))
        ttk.Button(replace_buttons, text="Replace", command=self._replace_current).pack(
            side="left", padx=(0, 6))
        ttk.Button(replace_buttons, text="Replace All", command=self._replace_all).pack(side="left")
        self.find_tab.columnconfigure(1, weight=1)
        self.replace_tab.columnconfigure(1, weight=1)
        self.find_entry.bind("<Return>", lambda _event: self._find_next())
        self.find_entry.bind("<Shift-Return>", lambda _event: self._find_next(backwards=True))
        self.replace_find_entry.bind("<Return>", lambda _event: self._find_next())
        self.replace_with_entry.bind("<Return>", lambda _event: self._replace_current())
        self.find_window.protocol("WM_DELETE_WINDOW", self.find_window.withdraw)
        self.find_context_menu = tk.Menu(
            self.find_window,
            tearoff=False,
            bg=self.theme["tab"],
            fg=self.theme["text_fg"],
            activebackground=self.theme["accent"],
            activeforeground=self.theme["text_fg"],
            font=UI_FONT,
        )
        self.find_context_menu.add_command(
            label="Cut", command=lambda: self._find_entry_event("<<Cut>>"),
            accelerator="Ctrl+X")
        self.find_context_menu.add_command(
            label="Copy", command=lambda: self._find_entry_event("<<Copy>>"),
            accelerator="Ctrl+C")
        self.find_context_menu.add_command(
            label="Paste", command=lambda: self._find_entry_event("<<Paste>>"),
            accelerator="Ctrl+V")
        self.find_context_menu.add_separator()
        self.find_context_menu.add_command(
            label="Undo", state="disabled", accelerator="Ctrl+Z")
        self.find_context_menu.add_command(
            label="Redo", state="disabled", accelerator="Ctrl+Y")
        self.find_context_menu.add_separator()
        self.find_context_menu.add_command(
            label="Select All", command=self._select_find_entry_text,
            accelerator="Ctrl+A")
        self.find_context_menu.add_command(
            label="Find…", command=self._focus_find_tab, accelerator="Ctrl+F")
        self.find_context_menu.add_command(
            label="Find Next", command=self._find_next, accelerator="F3")
        self.find_entry.bind("<Button-3>", self._show_find_context_menu, add="+")
        self.replace_find_entry.bind("<Button-3>", self._show_find_context_menu, add="+")
        self.replace_with_entry.bind("<Button-3>", self._show_find_context_menu, add="+")
        self.find_window.deiconify()
        self._position_find_window()
        self.find_entry.focus_set()

    def _show_find_context_menu(self, event):
        self.find_context_entry = event.widget
        self.find_context_menu.configure(
            bg=self.theme["tab"],
            fg=self.theme["text_fg"],
            activebackground=self.theme["accent"],
            activeforeground=self.theme["text_fg"],
        )
        try:
            self.find_context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.find_context_menu.grab_release()
        return "break"

    def _find_entry_event(self, event_name):
        if self.find_context_entry is not None:
            self.find_context_entry.focus_set()
            self.find_context_entry.event_generate(event_name)

    def _select_find_entry_text(self):
        if self.find_context_entry is not None:
            self.find_context_entry.focus_set()
            self.find_context_entry.selection_range(0, "end")

    def _focus_find_tab(self):
        self.find_tabs.select(self.find_tab)
        self.find_entry.focus_set()

    def _find_next(self, backwards=False):
        text = self._active_text()
        query = self.find_var.get() if self.find_var and self.find_var.get() else ""
        if text is None or not query:
            return False
        text.tag_remove("find_match", "1.0", "end")
        insert = text.index("insert")
        options = {"nocase": not self.match_case.get() if self.match_case else True}
        if backwards:
            match = text.search(query, insert, stopindex="1.0", backwards=True, **options)
            if not match:
                match = text.search(query, "end-1c", stopindex=insert, backwards=True, **options)
        else:
            match = text.search(query, insert, stopindex="end", **options)
            if not match:
                match = text.search(query, "1.0", stopindex=insert, **options)
        if not match:
            self.status.configure(text=f"Not found: {query}")
            return False
        end = f"{match}+{len(query)}c"
        text.tag_add("find_match", match, end)
        text.mark_set("insert", end if not backwards else match)
        text.see(match)
        text.focus_set()
        return True

    def _replace_current(self):
        text = self._active_text()
        query = self.find_var.get() if self.find_var else ""
        if text is None or not query:
            return
        ranges = text.tag_ranges("find_match")
        if len(ranges) != 2:
            if not self._find_next():
                return
            ranges = text.tag_ranges("find_match")
        if len(ranges) != 2:
            return
        start, end = ranges
        matched_text = text.get(start, end)
        matches = (matched_text == query if self.match_case.get()
                   else matched_text.casefold() == query.casefold())
        if not matches:
            if not self._find_next():
                return
            ranges = text.tag_ranges("find_match")
            if len(ranges) != 2:
                return
            start, end = ranges
        replacement = self.replace_with_var.get()
        autoseparators = text.cget("autoseparators")
        text.configure(autoseparators=False)
        try:
            text.edit_separator()
            text.tag_remove("find_match", start, end)
            text.delete(start, end)
            text.insert(start, replacement)
            text.mark_set("insert", f"{start}+{len(replacement)}c")
            text.edit_separator()
        finally:
            text.configure(autoseparators=autoseparators)
        if not self._find_next():
            self.status.configure(text=f"Replaced one occurrence of {query}.")

    def _replace_all(self):
        text = self._active_text()
        query = self.find_var.get() if self.find_var else ""
        if text is None or not query:
            return
        replacement = self.replace_with_var.get()
        options = {"nocase": not self.match_case.get()}
        text.tag_remove("find_match", "1.0", "end")
        autoseparators = text.cget("autoseparators")
        text.configure(autoseparators=False)
        start = "1.0"
        count = 0
        try:
            text.edit_separator()
            while True:
                match = text.search(query, start, stopindex="end", **options)
                if not match:
                    break
                end = f"{match}+{len(query)}c"
                text.delete(match, end)
                text.insert(match, replacement)
                count += 1
                start = f"{match}+{len(replacement)}c"
            text.edit_separator()
        finally:
            text.configure(autoseparators=autoseparators)
        if count:
            text.mark_set("insert", start)
            text.see(start)
            self.status.configure(text=f"Replaced {count} occurrence(s) of {query}.")
        else:
            self.status.configure(text=f"No matches found for {query}.")

    def compare_with_file(self):
        document = self._current_document()
        if document is None:
            return
        path = filedialog.askopenfilename(
            title="Compare with Text File", filetypes=FILE_TYPES, parent=self.root)
        if not path:
            return
        try:
            other_text, _encoding, _newline = read_text_file(path)
        except (OSError, UnicodeError) as error:
            messagebox.showerror("Compare Failed", str(error), parent=self.root)
            return
        current_text = document["editor"].text.get("1.0", "end-1c")
        self._show_comparison(
            Path(document["path"]).name if document["path"] else "Untitled",
            current_text,
            Path(path).name,
            other_text,
        )

    def _show_comparison(self, left_name, left_text, right_name, right_text):
        window = tk.Toplevel(self.root)
        window.title(f"Compare — {left_name} ↔ {right_name}")
        window.geometry("1200x760")
        container = ttk.Frame(window, padding=6)
        container.pack(fill="both", expand=True)
        container.columnconfigure(0, weight=1)
        container.columnconfigure(1, weight=1)
        container.rowconfigure(1, weight=1)
        ttk.Label(container, text=left_name).grid(row=0, column=0, sticky="w", padx=(0, 4), pady=(0, 4))
        ttk.Label(container, text=right_name).grid(row=0, column=1, sticky="w", padx=(4, 0), pady=(0, 4))
        left_editor = LineNumberedText(container, self.theme, readonly=True)
        right_editor = LineNumberedText(container, self.theme, readonly=True)
        left_editor.grid(row=1, column=0, sticky="nsew", padx=(0, 3))
        right_editor.grid(row=1, column=1, sticky="nsew", padx=(3, 0))

        left_lines = left_text.splitlines()
        right_lines = right_text.splitlines()
        left_display = []
        right_display = []
        operations = []
        matcher = difflib.SequenceMatcher(None, left_lines, right_lines, autojunk=False)
        for tag, left_start, left_end, right_start, right_end in matcher.get_opcodes():
            left_chunk = left_lines[left_start:left_end]
            right_chunk = right_lines[right_start:right_end]
            row_count = max(len(left_chunk), len(right_chunk))
            for offset in range(row_count):
                left_display.append((left_chunk[offset] if offset < len(left_chunk) else "", tag))
                right_display.append((right_chunk[offset] if offset < len(right_chunk) else "", tag))
                operations.append(tag)

        for editor, lines, side in (
                (left_editor, left_display, "left"),
                (right_editor, right_display, "right")):
            widget = editor.text
            for row, (line, operation) in enumerate(lines, start=1):
                widget.insert("end", line + "\n")
                if operation == "replace":
                    widget.tag_add("compare_changed", f"{row}.0", f"{row}.end")
                elif operation == "delete" and side == "left":
                    widget.tag_add("compare_removed", f"{row}.0", f"{row}.end")
                elif operation == "insert" and side == "right":
                    widget.tag_add("compare_added", f"{row}.0", f"{row}.end")
            widget.edit_modified(False)
            widget.configure(state="disabled")
        changed = sum(1 for operation in operations if operation != "equal")
        ttk.Label(container, text=f"{changed} changed line pair(s)").grid(
            row=2, column=0, columnspan=2, sticky="w", pady=(6, 0))

    def set_theme(self, name):
        if name not in THEMES:
            return
        self.theme_name = name
        self.theme = THEMES[name]
        self._setup_styles()
        menu_options = {
            "bg": self.theme["tab"],
            "fg": self.theme["text_fg"],
            "activebackground": self.theme["accent"],
            "activeforeground": self.theme["text_fg"],
        }
        for menu in self.menus:
            menu.configure(**menu_options)
        for document in self.documents:
            document["editor"].apply_theme(self.theme)


def main():
    root = tk.Tk()
    TextEditorPrototype(root)
    root.mainloop()


if __name__ == "__main__":
    main()
