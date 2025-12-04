from tkinter import ttk
import tkinter as tk

# Color Palette
PASTEL_GREEN_BG = "#E8F5E9"       # Light green background
PASTEL_GREEN_ACCENT = "#A5D6A7"   # Stronger green for headers/active
PASTEL_GREEN_FG = "#1B5E20"       # Dark green text

PASTEL_ORANGE_BG = "#FFF3E0"      # Light orange background (Inventory)
PASTEL_ORANGE_ACCENT = "#FFCC80"  # Stronger orange
PASTEL_ORANGE_FG = "#E65100"      # Dark orange text

DEFAULT_FONT = ("Segoe UI", 10)
LARGE_FONT = ("Segoe UI", 14)
TOUCH_PADDING = 10
NORMAL_PADDING = 2

class StyleManager:
    def __init__(self, root, touch_mode=False):
        self.root = root
        self.touch_mode = touch_mode
        self.style = ttk.Style(root)
        self.apply_theme()

    def set_touch_mode(self, enabled):
        self.touch_mode = enabled
        self.apply_theme()

    def apply_theme(self):
        self.style.theme_use('clam')

        # Dimensions based on touch mode
        base_font_size = 14 if self.touch_mode else 10
        base_padding = TOUCH_PADDING if self.touch_mode else NORMAL_PADDING
        row_height = 40 if self.touch_mode else 25

        base_font = ("Segoe UI", base_font_size)
        bold_font = ("Segoe UI", base_font_size, "bold")

        # --- GENERAL STYLES (Green Theme) ---
        self.style.configure(".",
                             background=PASTEL_GREEN_BG,
                             foreground=PASTEL_GREEN_FG,
                             font=base_font)

        self.style.configure("TLabel", background=PASTEL_GREEN_BG, foreground=PASTEL_GREEN_FG)
        self.style.configure("TButton", background=PASTEL_GREEN_ACCENT, padding=base_padding)
        self.style.configure("TEntry", fieldbackground="white", padding=base_padding)
        self.style.configure("TCombobox", padding=base_padding)

        # Notebook
        self.style.configure("TNotebook", background=PASTEL_GREEN_BG)
        self.style.configure("TNotebook.Tab",
                             padding=[base_padding*2, base_padding],
                             font=bold_font,
                             background=PASTEL_GREEN_ACCENT)
        self.style.map("TNotebook.Tab", background=[("selected", PASTEL_GREEN_BG)])

        # Treeview
        self.style.configure("Treeview",
                             background="white",
                             fieldbackground="white",
                             foreground="black",
                             rowheight=row_height,
                             font=base_font)
        self.style.configure("Treeview.Heading",
                             background=PASTEL_GREEN_ACCENT,
                             font=bold_font,
                             padding=base_padding)

        # LabelFrame
        self.style.configure("TLabelframe", background=PASTEL_GREEN_BG, foreground=PASTEL_GREEN_FG)
        self.style.configure("TLabelframe.Label", background=PASTEL_GREEN_BG, foreground=PASTEL_GREEN_FG, font=bold_font)

        # --- SPECIAL STYLES ---

        # Inventory (Orange Theme)
        self.style.configure("Inventory.TFrame", background=PASTEL_ORANGE_BG)
        self.style.configure("Inventory.TLabel", background=PASTEL_ORANGE_BG, foreground=PASTEL_ORANGE_FG)
        self.style.configure("Inventory.TLabelframe", background=PASTEL_ORANGE_BG, foreground=PASTEL_ORANGE_FG)
        self.style.configure("Inventory.TLabelframe.Label", background=PASTEL_ORANGE_BG, foreground=PASTEL_ORANGE_FG, font=bold_font)

        # Since buttons and other widgets might sit on the orange background, we might need styles for them too
        # But 'clam' theme buttons usually have their own background.
        # However, labels need to match the parent frame.

        # Sales (Green Theme - Default, but explicit)
        self.style.configure("Sales.TFrame", background=PASTEL_GREEN_BG)

        # Buttons
        self.style.configure("Accent.TButton", background="#66BB6A", foreground="white", font=bold_font)
        self.style.map("Accent.TButton", background=[("active", "#4CAF50")])

        self.style.configure("Danger.TButton", background="#EF5350", foreground="white", font=bold_font)
        self.style.map("Danger.TButton", background=[("active", "#D32F2F")])
