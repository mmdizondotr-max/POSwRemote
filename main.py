import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import os
import datetime
import json
import sys
import shutil
import threading
import time
import random
import socket
import queue
import secrets
import re
from typing import Optional, List, Dict, Any, Tuple, Union, Set
from PIL import Image, ImageTk
from style_manager import StyleManager

# pyinstaller --onefile --noconsole --splash splash_image2.png main.py

# --- CONFIGURATION CONSTANTS ---
APP_DATA_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "MMD_POS_System")
BACKUP_DIR = os.path.join(APP_DATA_DIR, "backups")

# Ensure app data directories exist
if not os.path.exists(APP_DATA_DIR):
    os.makedirs(APP_DATA_DIR)
if not os.path.exists(BACKUP_DIR):
    os.makedirs(BACKUP_DIR)

RECEIPT_FOLDER = "receipts"
INVENTORY_FOLDER = "inventoryreceipts"
SUMMARY_FOLDER = "summaryreceipts"
CORRECTION_FOLDER = "correctionreceipts"
DATA_FILE = "products.xlsx"
CONFIG_FILE = os.path.join(APP_DATA_DIR, "config.json")
LEDGER_FILE = os.path.join(APP_DATA_DIR, "ledger.json")
APP_TITLE = "MMD Inventory Tracker v15.0"  # Refactored Version

# --- EMAIL CONFIGURATION ---
SMTP_SERVER = "smtp.gmail.com"
SMTP_PORT = 587
SENDER_EMAIL = "mmdpos.diz@gmail.com"
SENDER_PASSWORD = "wvdg kkka myuk inve"

# Ensure folders exist
for folder in [RECEIPT_FOLDER, INVENTORY_FOLDER, SUMMARY_FOLDER, CORRECTION_FOLDER]:
    if not os.path.exists(folder):
        os.makedirs(folder)

# --- UTILS ---
def truncate_product_name(name: str) -> str:
    if len(name) > 30:
        return name[:15] + name[-15:]
    return name

# --- DEPENDENCY CONTAINER ---
class AppModules:
    """
    Holds references to lazily imported modules to allow strict typing hints
    and organized access without global pollution.
    """
    pd: Any = None
    canvas: Any = None
    letter: Any = None
    inch: Any = None
    PdfReader: Any = None
    ntplib: Any = None
    Flask: Any = None
    request: Any = None
    jsonify: Any = None
    render_template_string: Any = None
    qrcode: Any = None
    smtplib: Any = None
    ssl: Any = None
    MIMEText: Any = None
    MIMEMultipart: Any = None
    MIMEBase: Any = None
    encoders: Any = None

    @classmethod
    def is_loaded(cls) -> bool:
        return cls.pd is not None

# --- DATA STRUCTURES ---
class TransactionItem(Dict):
    """Type hint helper for transaction items"""
    name: str
    price: float
    qty: int
    category: str
    subtotal: Optional[float]
    # ... other fields allow dynamic keys

# --- DATA MANAGER ---
class DataManager:
    """
    Handles all data persistence, calculation, and product management.
    Separates logic from UI.
    """
    def __init__(self, modules: AppModules):
        self.mod = modules
        self.products_df: Any = None  # Pandas DataFrame
        self.ledger: List[Dict] = []
        self.product_history: List[Dict] = []
        self.summary_count: int = 0
        self.shortcuts_asked: bool = False
        self.business_name: str = "My Business"
        self.startup_stats: Dict = {}

        # Caches
        self.stock_cache: Dict[str, Dict] = {}
        self.name_lookup_cache: Dict[str, Dict] = {}
        self.display_name_map: Dict[str, str] = {}  # Full Name -> Smart Display Name
        self.config: Dict = {}

        self.load_config()
        self.create_rolling_backup()
        self.load_ledger()
        self.load_products()
        self.refresh_stock_cache()

    def load_config(self) -> None:
        default = {
            "startup": False,
            "splash_img": "",
            "cached_business_name": "My Business",
            "previous_products": [],
            "recipient_email": "",
            "last_bi_date": "",
            "touch_mode": False,
            "last_email_sync": ""
        }
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r') as f:
                    self.config = json.load(f)
            except:
                self.config = default
        else:
            self.config = default

    def save_config(self) -> None:
        try:
            with open(CONFIG_FILE, 'w') as f:
                json.dump(self.config, f)
        except Exception as e:
            print(f"Config Save Error: {e}")

    def load_ledger(self) -> None:
        if os.path.exists(LEDGER_FILE):
            try:
                with open(LEDGER_FILE, 'r') as f:
                    data = json.load(f)
                    if isinstance(data, list):
                        self.ledger = data
                        self.summary_count = 0
                        self.shortcuts_asked = False
                        self.product_history = []
                    elif isinstance(data, dict):
                        self.ledger = data.get("transactions", [])
                        self.summary_count = data.get("summary_count", 0)
                        self.shortcuts_asked = data.get("shortcuts_asked", False)
                        self.product_history = data.get("product_history", [])
            except:
                self.ledger = []
                self.product_history = []

        # Optimization: Pre-parse dates could happen here if we used custom objects,
        # but to keep JSON compatibility simple, we'll parse on demand or keep a shadow index if needed.
        # For <10k records, on-demand parsing in calculate_stats is usually fine, but let's be careful.

    def create_rolling_backup(self) -> None:
        """Creates a rolling backup of the ledger file."""
        if not os.path.exists(LEDGER_FILE):
            return

        try:
            timestamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
            backup_name = f"ledger_backup_{timestamp}.json"
            backup_path = os.path.join(BACKUP_DIR, backup_name)

            shutil.copy2(LEDGER_FILE, backup_path)

            # Cleanup old backups (Keep 10 most recent)
            backups = [
                os.path.join(BACKUP_DIR, f)
                for f in os.listdir(BACKUP_DIR)
                if f.startswith("ledger_backup_") and f.endswith(".json")
            ]
            backups.sort(key=os.path.getctime)

            while len(backups) > 10:
                os.remove(backups.pop(0))

        except Exception as e:
            print(f"Backup Error: {e}")

    def save_ledger(self) -> None:
        try:
            data = {
                "transactions": self.ledger,
                "summary_count": self.summary_count,
                "shortcuts_asked": self.shortcuts_asked,
                "product_history": self.product_history
            }

            # Atomic Write
            temp_file = LEDGER_FILE + ".tmp"
            with open(temp_file, 'w') as f:
                json.dump(data, f, indent=2)
                f.flush()
                os.fsync(f.fileno())

            os.replace(temp_file, LEDGER_FILE)

        except Exception as e:
            messagebox.showerror("Save Error", f"Could not save database: {e}")

    def load_products(self) -> None:
        pd = self.mod.pd
        req_cols = ["Business Name", "Product Category", "Product Name", "Price"]

        if not os.path.exists(DATA_FILE):
            df = pd.DataFrame(columns=req_cols)
            df.loc[0] = ["My Business", "General", "Sample Product", 100.00]
            try:
                df.to_excel(DATA_FILE, index=False)
            except:
                pass

        raw_df = pd.DataFrame()
        try:
            raw_df = pd.read_excel(DATA_FILE)
            raw_df.columns = raw_df.columns.str.strip()
        except Exception as e:
            messagebox.showerror("Load Error", f"Error reading Excel: {e}")
            self.products_df = pd.DataFrame(columns=req_cols)
            return

        # --- Data Cleanup & Normalization ---
        def clean_text(text_val, is_product_name=False):
            if pd.isna(text_val): return ""
            s = str(text_val).upper()
            s = s.replace("'", "")       # Remove apostrophes
            s = s.replace("\n", " ")     # Single line
            s = re.sub(r'\s+', ' ', s)   # Remove double spaces
            if is_product_name:
                # Remove spaces between numbers and common units
                s = re.sub(r'(\d+)\s+(MG|G|KG|ML|L|OZ|LB|CM|M|MM|PCS)\b', r'\1\2', s)
            return s.strip()

        cleaned_count = 0
        if 'Product Name' in raw_df.columns:
            def clean_and_count(x):
                nonlocal cleaned_count
                orig = str(x)
                new = clean_text(x, is_product_name=True)
                # Count if effectively changed (ignoring NaN vs "" diff if original was nan)
                if pd.notna(x) and orig != new:
                    cleaned_count += 1
                return new
            raw_df['Product Name'] = raw_df['Product Name'].apply(clean_and_count)

        if 'Product Category' in raw_df.columns:
            raw_df['Product Category'] = raw_df['Product Category'].apply(clean_text)

        if 'Remarks' not in raw_df.columns:
            raw_df['Remarks'] = ""

        # Business Name Logic & Cleanup
        if "Business Name" in raw_df.columns:
            # Find first non-empty value
            first_val = "My Business"
            found_idx = -1

            # Search for first valid string
            for idx, val in enumerate(raw_df["Business Name"]):
                s_val = str(val).strip()
                if s_val and s_val.lower() != "nan":
                    first_val = s_val
                    found_idx = idx
                    break

            # If nothing found, try config or keep default
            if found_idx == -1:
                first_val = self.config.get("cached_business_name", "My Business")

            self.business_name = first_val
            self.config["cached_business_name"] = first_val

        valid_products = []
        seen_names = set()
        rejected_details = []

        # Temporary lists for sorting
        valid_rows_list = []
        error_rows_list = []

        for index, row in raw_df.iterrows():
            cat = str(row.get('Product Category', ''))
            name = str(row.get('Product Name', ''))
            raw_price = row.get('Price', 0)

            try:
                price = float(raw_price)
            except:
                price = 0.0

            rejection_reason = None
            if price <= 0 or pd.isna(raw_price): rejection_reason = "Price <= 0"
            elif not cat or cat == 'NAN': rejection_reason = "Invalid Category"
            elif not name or name == 'NAN': rejection_reason = "Invalid Name"
            elif name in seen_names: rejection_reason = "Duplicate Name"

            # Construct row dict for reconstruction
            row_dict = row.to_dict()

            if rejection_reason is None:
                seen_names.add(name)

                # Ensure Business Name is populated in memory even if empty in file row
                raw_b_name = str(row.get('Business Name', ''))
                if not raw_b_name or raw_b_name.lower() == 'nan':
                    b_name = self.business_name
                else:
                    b_name = raw_b_name

                entry = {
                    "Business Name": b_name,
                    "Product Category": cat,
                    "Product Name": name,
                    "Price": price
                }
                valid_products.append(entry)

                # Populate Lookup Cache
                self.name_lookup_cache[name] = entry
                truncated = truncate_product_name(name)
                self.name_lookup_cache[truncated] = entry

                # Clear remarks
                row_dict['Remarks'] = ""
                valid_rows_list.append(row_dict)
            else:
                rejected_details.append({"name": name, "reason": rejection_reason})
                row_dict['Remarks'] = rejection_reason
                error_rows_list.append(row_dict)

        # Sort Logic: Errors first, then valid. Both sorted by Category -> Name
        def sort_helper(r):
            return (str(r.get('Product Category', '')), str(r.get('Product Name', '')))

        error_rows_list.sort(key=sort_helper)
        valid_rows_list.sort(key=sort_helper)

        final_rows = error_rows_list + valid_rows_list
        raw_df = pd.DataFrame(final_rows)

        try:
            # Ensure column order matches standard
            if not raw_df.empty:
                cols = ["Business Name", "Product Category", "Product Name", "Price", "Remarks"]
                # Keep other columns if they exist
                existing_cols = [c for c in raw_df.columns if c not in cols]
                final_cols = cols + existing_cols
                # Reindex safely
                raw_df = raw_df.reindex(columns=final_cols)

            # --- Business Name Cleanup (Visual in File) ---
            # Ensure only the first row (A2) has the business name, others empty.
            if "Business Name" in raw_df.columns:
                raw_df["Business Name"] = ""
                if not raw_df.empty:
                    raw_df.at[0, "Business Name"] = self.business_name

            raw_df.to_excel(DATA_FILE, index=False)

            # Post-processing: Apply Number Format
            import openpyxl
            wb = openpyxl.load_workbook(DATA_FILE)
            ws = wb.active

            # Find Price column index (1-based)
            price_col_idx = None
            for idx, cell in enumerate(ws[1], 1):
                if cell.value and str(cell.value).strip() == "Price":
                    price_col_idx = idx
                    break

            if price_col_idx:
                for row in ws.iter_rows(min_row=2, min_col=price_col_idx, max_col=price_col_idx):
                    for cell in row:
                        cell.number_format = '0.00'

            wb.save(DATA_FILE)

        except Exception as e:
            print(f"Failed to update products.xlsx: {e}")

        # --- Smart Display Name Resolution ---
        self.resolve_display_names(valid_products)

        # Populate Display Name Map (Full Name -> Smart Name)
        self.display_name_map = {}
        for p in valid_products:
            if '_display_name' in p:
                self.display_name_map[p['Product Name']] = p['_display_name']

        self.products_df = pd.DataFrame(valid_products)

        # --- Product History Versioning ---
        current_list = self.products_df.to_dict('records')

        should_save_history = False
        if not self.product_history:
            should_save_history = True
        else:
            # Compare with latest
            # Simple check: json dumps comparison to ensure deep equality including order if sorted,
            # but list order matters in excel, so direct comparison is fine.
            # However, we must ensure we are comparing compatible structures.
            # 'records' gives list of dicts.
            last_version = self.product_history[-1].get('items', [])
            if current_list != last_version:
                should_save_history = True

        if should_save_history and current_list:
            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.product_history.append({
                "timestamp": timestamp,
                "items": current_list
            })
            # Keep only last 4 versions (Current + 3 past)
            if len(self.product_history) > 4:
                self.product_history = self.product_history[-4:]
            self.save_ledger()

        # Stats
        previous_products = set(self.config.get("previous_products", []))
        current_products = set(seen_names)
        self.startup_stats = {
            "total": len(valid_products),
            "new": len(current_products - previous_products),
            "rejected": len(rejected_details),
            "phased_out": len(previous_products - current_products),
            "rejected_details": rejected_details,
            "cleaned_names": cleaned_count
        }
        self.config["previous_products"] = list(seen_names)
        self.save_config()

    def add_transaction(self, t_type: str, filename: str, items: List[Dict],
                        timestamp: Optional[str] = None, ref_type: str = None,
                        ref_filename: str = None) -> None:
        if not timestamp:
            timestamp = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')

        transaction = {
            "type": t_type,
            "timestamp": timestamp,
            "filename": filename,
            "items": items
        }
        if ref_type: transaction['ref_type'] = ref_type
        if ref_filename: transaction['ref_filename'] = ref_filename

        self.create_rolling_backup()
        self.ledger.append(transaction)
        self.save_ledger()
        self.refresh_stock_cache()

    def refresh_stock_cache(self) -> None:
        self.stock_cache, _, _, _ = self.calculate_stats(None)

    def calculate_stats(self, period_filter: Optional[Tuple[datetime.datetime, datetime.datetime]]) \
            -> Tuple[Dict, int, int, List[str]]:
        """
        Calculates inventory stats.
        Optimization: We parse dates inside the loop.
        """
        stats = {}
        in_count = 0
        out_count = 0
        corrections_in_period = []

        # Optimization: cache the date format string
        date_fmt = "%Y-%m-%d %H:%M:%S"

        for transaction in self.ledger:
            try:
                # Type Check
                t_type = transaction.get('type')
                if not t_type: continue

                # Filter by Period
                if period_filter:
                    ts_str = transaction.get('timestamp')
                    try:
                        dt = datetime.datetime.strptime(ts_str, date_fmt)
                    except:
                        dt = datetime.datetime.now()

                    s, e = period_filter
                    if not (s <= dt <= e):
                        continue

                    if t_type == 'correction':
                        corrections_in_period.append(transaction.get('filename', 'Unknown'))

                # Aggregate Logic
                if t_type == 'inventory':
                    in_count += 1
                elif t_type == 'sales':
                    out_count += 1

                ref_type = transaction.get('ref_type')

                for item in transaction.get('items', []):
                    name = item.get('name', 'Unknown')
                    qty = int(item.get('qty', 0))
                    price = float(item.get('price', 0))

                    if name not in stats:
                        stats[name] = {'name': name, 'in': 0, 'out': 0, 'sales_lines': [], 'in_lines': []}

                    if t_type == 'sales':
                        amt = float(item.get('subtotal', 0))
                        stats[name]['out'] += qty
                        stats[name]['sales_lines'].append({'price': price, 'qty': qty, 'amt': amt})
                    elif t_type == 'inventory':
                        stats[name]['in'] += qty
                        stats[name]['in_lines'].append({'price': price, 'qty': qty})
                    elif t_type == 'correction':
                        if ref_type == 'sales':
                            stats[name]['out'] += qty
                            amt = qty * price
                            stats[name]['sales_lines'].append({'price': price, 'qty': qty, 'amt': amt})
                        elif ref_type == 'inventory':
                            stats[name]['in'] += qty
                            stats[name]['in_lines'].append({'price': price, 'qty': qty})

            except Exception:
                continue

        return stats, in_count, out_count, corrections_in_period

    def get_product_list(self) -> List[Dict]:
        if self.products_df is None or self.products_df.empty:
            return []
        return self.products_df.to_dict('records')

    def get_product_details_by_str(self, selection_string: str) -> Tuple[str, str, float, str]:
        """Returns (code, name, price, category)"""
        if not selection_string: return "", None, 0, "Uncategorized"

        # Try direct lookup in cache (Exact Full Name or Truncated Name)
        if selection_string in self.name_lookup_cache:
            item = self.name_lookup_cache[selection_string]
            return "", item['Product Name'], float(item['Price']), item['Product Category']

        # Try parsing "Name (Price)" format
        try:
            name_part = selection_string.rsplit(" (", 1)[0]
        except:
            name_part = selection_string

        if name_part in self.name_lookup_cache:
            item = self.name_lookup_cache[name_part]
            return "", item['Product Name'], float(item['Price']), item['Product Category']

        # Fallback for old items not in current product list but in ledger (Phased Out)
        # We rely on what was passed if possible, or return Phased Out
        return "", "Unknown Item", 0.0, "Phased Out"

    def get_stock_level(self, name: str) -> int:
        st = self.stock_cache.get(name, {'in': 0, 'out': 0})
        return st['in'] - st['out']

    def resolve_display_names(self, product_list: List[Dict]) -> None:
        """
        Generates distinct display names for products to avoid ambiguity in dropdowns.
        Updates 'product_list' in-place with a '_display_name' key.
        """
        # Group by initial 30-char truncation
        groups = {}
        for p in product_list:
            name = p['Product Name']
            trunc = truncate_product_name(name)
            if trunc not in groups: groups[trunc] = []
            groups[trunc].append(p)

        # Limits to try for collision resolution
        limits = [45, 60, 100, 200]

        for key, group in groups.items():
            if len(group) == 1:
                p = group[0]
                p['_display_name'] = key
                self.name_lookup_cache[key] = p
            else:
                # Collision detected: Try to resolve by increasing limit
                current_limit_idx = 0
                resolved = False
                current_group = group

                while not resolved and current_limit_idx < len(limits):
                    limit = limits[current_limit_idx]
                    sub_groups = {}

                    for p in current_group:
                        full_name = p['Product Name']
                        if len(full_name) > limit:
                             half = limit // 2
                             new_name = full_name[:half] + full_name[-half:]
                        else:
                             new_name = full_name

                        if new_name not in sub_groups: sub_groups[new_name] = []
                        sub_groups[new_name].append(p)

                    max_collision_size = max(len(sg) for sg in sub_groups.values())
                    if max_collision_size == 1:
                        resolved = True
                        for name_ver, items in sub_groups.items():
                            p = items[0]
                            p['_display_name'] = name_ver
                            self.name_lookup_cache[name_ver] = p
                    else:
                        current_limit_idx += 1

                if not resolved:
                    # Fallback: Use full name if still colliding (should be distinct per validation)
                    for p in current_group:
                        full = p['Product Name']
                        p['_display_name'] = full
                        self.name_lookup_cache[full] = p

# --- REPORT MANAGER ---
class ReportManager:
    """
    Handles PDF generation.
    """
    def __init__(self, modules: AppModules, business_name: str, session_user: str, data_manager: Optional[DataManager] = None):
        self.mod = modules
        self.business_name = business_name
        self.session_user = session_user
        self.data_manager = data_manager

    def generate_grouped_pdf(self, filepath: str, title: str, date_str: str, items: List[Dict],
                             col_headers: List[str], col_pos: List[float], is_summary: bool = False,
                             extra_info: str = "", subtotal_indices: List[int] = None,
                             is_inventory: bool = False, correction_list: List[str] = None,
                             is_bi: bool = False, canvas_obj: Any = None) -> bool:
        try:
            canvas = self.mod.canvas
            letter = self.mod.letter
            inch = self.mod.inch

            if canvas_obj:
                c = canvas_obj
            else:
                c = canvas.Canvas(filepath, pagesize=letter)

            width, height = letter
            y = height - 1 * inch

            # Header
            c.setFont("Helvetica-Bold", 18)
            c.drawString(1 * inch, y, self.business_name)
            y -= 0.35 * inch
            c.setFont("Helvetica-Bold", 14)
            c.drawString(1 * inch, y, title)
            y -= 0.25 * inch
            c.setFont("Helvetica", 9)
            c.drawString(1 * inch, y, APP_TITLE)
            y -= 0.2 * inch
            c.setFont("Helvetica", 10)
            c.drawString(1 * inch, y, f"Date: {date_str}")
            y -= 0.2 * inch
            c.drawString(1 * inch, y, f"User: {self.session_user}")
            if extra_info:
                y -= 0.2 * inch
                c.drawString(1 * inch, y, extra_info)
            y -= 0.5 * inch

            # Columns
            c.setFont("Helvetica-Bold", 9)
            for i, h in enumerate(col_headers):
                c.drawString(col_pos[i] * inch, y, h)
            c.line(1 * inch, y - 5, 7.5 * inch, y - 5)
            y -= 20

            def sort_key(x):
                cat = x.get('category', 'Uncategorized')
                if cat == "Phased Out": cat = "zzz_Phased Out"
                return (cat, x['name'])

            sorted_items = sorted(items, key=sort_key)
            current_cat = None
            cat_sums = [0.0] * len(col_headers)
            grand_sums = [0.0] * len(col_headers)

            for item in sorted_items:
                if y < 1 * inch:
                    c.showPage()
                    y = height - 1 * inch

                cat = item.get('category', 'Uncategorized')
                if cat != current_cat:
                    # Subtotal Logic
                    if current_cat is not None:
                        if not is_inventory and not "qty_final" in item:
                            c.setFont("Helvetica-Bold", 9)
                            c.line(col_pos[-1] * inch - 0.5 * inch, y + 2, 7.5 * inch, y + 2)
                            if subtotal_indices:
                                for idx in subtotal_indices:
                                    if idx < len(col_pos):
                                        val = cat_sums[idx]
                                        is_float = (is_summary and idx in [1, 5]) or (not is_summary and idx in [1, 3])
                                        txt = f"{val:.2f}" if is_float else f"{int(val)}"
                                        c.drawString(col_pos[idx] * inch, y - 10, txt)
                            c.drawString(col_pos[-1] * inch - 0.7 * inch, y - 10, "Subtotal:")
                            y -= 30
                        else:
                            y -= 10

                    c.setFont("Helvetica-Bold", 11)
                    c.setFillColor("blue")
                    c.drawString(1 * inch, y, f"Category: {cat}")
                    c.setFillColor("black")
                    y -= 15
                    current_cat = cat
                    cat_sums = [0.0] * len(col_headers)

                c.setFont("Helvetica", 9)
                row_vals = []
                row_txt = []

                # Resolve Name
                raw_name = item.get('name', 'Unknown')
                display_name = raw_name

                # Smart Name Lookup
                if self.data_manager and raw_name in self.data_manager.display_name_map:
                    display_name = self.data_manager.display_name_map[raw_name]

                # Safety Truncation (40 chars max)
                if len(display_name) > 40:
                    display_name = display_name[:20] + "..." + display_name[-17:]

                # Determine Row Data based on context
                if is_bi:
                    row_txt = [display_name, str(int(item['qty']))]
                    row_vals = [0, item['qty']]
                elif is_summary:
                    price_txt = f"{item['price']:.2f}" if item['price'] > 0 else "-"
                    row_txt = [display_name, price_txt, str(int(item['in'])),
                               str(int(item['out'])), str(int(item['remaining'])), f"{item['sales']:.2f}"]
                    row_vals = [0, 0, item['in'], item['out'], item['remaining'], item['sales']]
                elif "subtotal" in item:
                    row_txt = [display_name, f"{item['price']:.2f}", str(int(item['qty'])),
                               f"{item['subtotal']:.2f}"]
                    row_vals = [0, 0, item['qty'], item['subtotal']]
                elif "new_stock" in item:
                    row_txt = [display_name, f"{item.get('price', 0):.2f}", f"{int(item['qty'])}",
                               str(int(item.get('new_stock', 0)))]
                    row_vals = [0, 0, item['qty'], 0]
                elif "qty_final" in item:
                    row_txt = [display_name, str(int(item['qty_orig'])), f"{int(item['qty']):+}",
                               str(int(item['qty_final']))]
                    row_vals = [0, 0, item['qty'], 0]
                else:
                    row_txt = [display_name, f"{item.get('price', 0):.2f}", f"{int(item['qty'])}"]
                    row_vals = [0, 0, item['qty']]

                for i, txt in enumerate(row_txt):
                    c.drawString(col_pos[i] * inch, y, txt)

                for i, val in enumerate(row_vals):
                    cat_sums[i] += val
                    grand_sums[i] += val

                y -= 15

            # Final Subtotal for last category
            if current_cat is not None and not is_inventory and not is_bi and not "qty_final" in (items[0] if items else {}):
                c.setFont("Helvetica-Bold", 9)
                c.line(col_pos[-1] * inch - 0.5 * inch, y + 2, 7.5 * inch, y + 2)
                if subtotal_indices:
                    for idx in subtotal_indices:
                        if idx < len(col_pos):
                            val = cat_sums[idx]
                            is_float = (is_summary and idx in [1, 5]) or (not is_summary and idx in [1, 3])
                            txt = f"{val:.2f}" if is_float else f"{int(val)}"
                            c.drawString(col_pos[idx] * inch, y - 10, txt)
                c.drawString(col_pos[-1] * inch - 0.7 * inch, y - 10, "Subtotal:")
                y -= 30

            # Grand Total
            if not is_bi:
                c.line(1 * inch, y + 10, 7.5 * inch, y + 10)
                c.setFont("Helvetica-Bold", 12)
                lbl = ""
                if is_summary:
                    lbl = f"TOTAL SALES: {grand_sums[5]:.2f}"
                elif items and "subtotal" in items[0]:
                    lbl = f"TOTAL AMOUNT: {grand_sums[3]:.2f}"
                elif is_inventory:
                    lbl = f"TOTAL ADDED: {int(grand_sums[2])}"
                c.drawString(4.5 * inch, y, lbl)

            # Corrections List (Summary only)
            if is_summary and correction_list:
                y -= 40
                if y < 1 * inch:
                    c.showPage()
                    y = height - 1 * inch
                c.setFont("Helvetica-Bold", 10)
                c.drawString(1 * inch, y, "Corrections included in this period:")
                y -= 15
                c.setFont("Helvetica", 9)
                for cf in correction_list:
                    if y < 0.5 * inch:
                        c.showPage()
                        y = height - 1 * inch
                    c.drawString(1.2 * inch, y, f"- {cf}")
                    y -= 12

            if not canvas_obj:
                c.save()
            return True
        except Exception as e:
            messagebox.showerror("PDF Error", str(e))
            return False

    def generate_catchup_report(self, filepath: str, intervals: List[Tuple[datetime.datetime, datetime.datetime]],
                                data_manager: 'DataManager', get_stats_func) -> bool:
        try:
            canvas = self.mod.canvas
            letter = self.mod.letter
            c = canvas.Canvas(filepath, pagesize=letter)

            for idx, (start, end) in enumerate(intervals):
                # Calculate stats for this specific interval
                # We reuse the logic from get_sum_data but we need to inject the period
                # Since get_sum_data is in POSSystem, we will need to replicate aggregation logic here or pass a callback
                # Ideally, we pass a callback that returns the formatted data rows for a given period

                rows, in_c, out_c, corr_list = get_stats_func(period=(start, end))

                title = f"CATCHUP SUMMARY ({idx+1}/3)"
                date_str = f"{start.strftime('%Y-%m-%d %H:%M')} to {end.strftime('%Y-%m-%d %H:%M')}"

                self.generate_grouped_pdf(
                    filepath="", # Not used when canvas_obj is passed
                    title=title,
                    date_str=date_str,
                    items=rows,
                    col_headers=["Product", "Price", "Added", "Sold", "Stock", "Sales"],
                    col_pos=[1.0, 4.5, 5.2, 5.9, 6.6, 7.3],
                    is_summary=True,
                    extra_info=f"Interval {idx+1} | In: {in_c} | Out: {out_c}",
                    subtotal_indices=[2, 3, 5],
                    correction_list=corr_list,
                    canvas_obj=c
                )
                c.showPage()

            c.save()
            return True
        except Exception as e:
            print(f"Catchup Report Error: {e}")
            return False

# --- EMAIL MANAGER ---
class EmailManager:
    """
    Handles background email sending.
    """
    def __init__(self, modules: AppModules):
        self.mod = modules
        self.last_email_time = 0

    def validate_email_format(self, email: str) -> bool:
        regex = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(regex, email) is not None

    def send_email_thread(self, recipient: str, subject: str, body: str,
                          attachment_paths: List[str] = None, is_test: bool = False,
                          on_success: Any = None, on_error: Any = None) -> None:
        def task():
            try:
                # Local imports for thread safety if needed, or use self.mod
                smtplib = self.mod.smtplib
                ssl = self.mod.ssl
                MIMEText = self.mod.MIMEText
                MIMEMultipart = self.mod.MIMEMultipart
                MIMEBase = self.mod.MIMEBase
                encoders = self.mod.encoders

                msg = MIMEMultipart()
                msg['From'] = SENDER_EMAIL
                msg['To'] = recipient
                msg['Subject'] = subject
                msg.attach(MIMEText(body, 'plain'))

                if attachment_paths:
                    for path in attachment_paths:
                        if os.path.exists(path):
                            filename = os.path.basename(path)
                            with open(path, "rb") as attachment:
                                part = MIMEBase("application", "octet-stream")
                                part.set_payload(attachment.read())
                            encoders.encode_base64(part)
                            part.add_header("Content-Disposition", f"attachment; filename= {filename}")
                            msg.attach(part)

                context = ssl.create_default_context()
                with smtplib.SMTP(SMTP_SERVER, SMTP_PORT) as server:
                    server.starttls(context=context)
                    server.login(SENDER_EMAIL, SENDER_PASSWORD)
                    server.sendmail(SENDER_EMAIL, recipient, msg.as_string())

                # Execute success callback if provided
                if on_success:
                    try:
                        # Schedule in main thread if it involves UI or critical data that shouldn't race
                        # But for config saving (simple file I/O), running in thread is acceptable
                        # as long as DataManager isn't thread-hostile.
                        # DataManager.save_config is just json.dump, which is atomic enough for this use case.
                        on_success()
                    except Exception as callback_err:
                        print(f"Email callback error: {callback_err}")

                print(f"Email sent successfully to {recipient}")

            except Exception as e:
                err_msg = str(e)
                if on_error: on_error(err_msg)
                print(f"Failed to send email: {err_msg}")

        threading.Thread(target=task, daemon=True).start()

    def trigger_summary_email(self, recipient: str, summary_pdf_path: str, ledger_path: str,
                              business_name: str, count: int, user: str, extra_body: str = "",
                              extra_attachments: List[str] = None, on_success: Any = None) -> None:
        if not recipient: return

        date_str = datetime.datetime.now().strftime("%Y%m%d")
        safe_biz_name = "".join(c for c in business_name if c.isalnum() or c in (' ', '_', '-')).strip()
        subject = f"[{count:04d}]_{APP_TITLE}_{safe_biz_name}_{date_str}"
        body = (f"Summary & Ledger.\n\n"
                f"User: {user}\n"
                f"Counter: {count:04d}\n"
                f"Time: {datetime.datetime.now()}\n\n"
                f"{extra_body}")

        attachments = [summary_pdf_path, ledger_path]
        if extra_attachments:
            attachments.extend(extra_attachments)

        self.send_email_thread(recipient, subject, body, attachments, on_success=on_success)

# --- WEB SERVER THREAD ---
class WebServerThread(threading.Thread):
    def __init__(self, modules: AppModules, task_queue: queue.Queue, port: int,
                 data_manager_provider: Any, token_provider: Any):
        super().__init__()
        self.mod = modules
        self.task_queue = task_queue
        self.port = port
        self.get_data_manager = data_manager_provider
        self.get_token = token_provider
        self.app = self.mod.Flask(__name__)
        self.daemon = True

        import logging
        log = logging.getLogger('werkzeug')
        log.setLevel(logging.ERROR)

        self.setup_routes()

    def setup_routes(self):
        @self.app.route('/')
        def index():
            token = self.mod.request.args.get('token')
            current_valid_token = self.get_token()
            if not token or token != current_valid_token:
                return "<h1>403 Forbidden</h1><p>Invalid or Expired QR Code.</p>", 403
            return self.mod.render_template_string(MOBILE_HTML_TEMPLATE, token=current_valid_token)

        @self.app.route('/get_products')
        def get_products():
            token = self.mod.request.args.get('token')
            if not token or token != self.get_token():
                return self.mod.jsonify({"error": "Unauthorized"}), 403

            dm = self.get_data_manager()
            # dm is the DataManager instance
            prods_df = dm.products_df

            prods = prods_df.to_dict(orient='records')
            cleaned_prods = []
            for p in prods:
                name = p.get('Product Name', 'Unknown')
                current_qty = dm.get_stock_level(name)

                cleaned_prods.append({
                    "name": name,
                    "price": float(p.get('Price', 0)),
                    "category": p.get('Product Category', 'General'),
                    "stock": int(current_qty)
                })
            return self.mod.jsonify({"business": dm.business_name, "products": cleaned_prods})

        @self.app.route('/submit_transaction', methods=['POST'])
        def submit():
            token = self.mod.request.args.get('token')
            if not token or token != self.get_token():
                return self.mod.jsonify({"error": "Unauthorized"}), 403

            data = self.mod.request.json
            mode = data.get('mode')
            items = data.get('items', [])

            # Server-side stock validation
            if mode == 'sales':
                dm = self.get_data_manager()
                for item in items:
                    name = item.get('name')
                    req_qty = int(item.get('qty', 0))
                    avail = dm.get_stock_level(name)
                    if req_qty > avail:
                        return self.mod.jsonify({"status": "error",
                                        "message": f"Stock change detected! Only {int(avail)} remaining for {name}."})

            client_ip = self.mod.request.remote_addr
            self.task_queue.put({"type": "web_transaction", "data": data, "ip": client_ip})
            return self.mod.jsonify({"status": "success", "message": "Queued"})

    def run(self):
        try:
            self.app.run(host='0.0.0.0', port=self.port, threaded=True)
        except Exception as e:
            print(f"Web Server Error: {e}")

# --- MAIN SYSTEM GUI ---
class POSSystem:
    def __init__(self, root: tk.Tk, username: str, splash: Any, modules: AppModules):
        self.root = root
        self.mod = modules
        self.root.title(APP_TITLE)
        self.root.geometry("1100x750")
        self.root.minsize(800, 500)
        try:
            self.root.state('zoomed')
        except:
            self.root.attributes('-zoomed', True)

        # Session
        login_time = datetime.datetime.now().strftime("%H%M%S")
        self.session_user = f"{username}-{login_time}"

        # Initialize Managers
        if splash: splash.update_status("Loading Data Manager...")
        self.data_manager = DataManager(self.mod)
        self.touch_mode = self.data_manager.config.get("touch_mode", False)

        self.report_manager = ReportManager(self.mod, self.data_manager.business_name, self.session_user, self.data_manager)
        self.email_manager = EmailManager(self.mod)

        # Carts & UI State
        self.sales_cart: List[Dict] = []
        self.inventory_cart: List[Dict] = []
        self.correction_cart: List[Dict] = []
        self.remote_requests: List[Dict] = []
        self.lws_sidebars: Dict[str, ttk.Frame] = {}

        # Web Server State
        self.web_queue = queue.Queue()
        self.local_ip = self.get_local_ip()
        self.web_port = self.find_free_port()
        self.connected_devices: Dict[str, int] = {}
        self.session_token = secrets.token_hex(4)
        self.web_thread = None
        self.web_server_running = False

        # Build UI
        if splash: splash.update_status("Building UI...")
        self.setup_ui()
        self.show_startup_report()

        # Tasks
        self.root.after(1000, self.check_beginning_inventory_reminder)
        self.root.after(2000, self.check_shortcuts)
        self.root.after(100, self.process_web_queue)

    # --- UI SETUP ---
    def setup_ui(self):
        self.style_manager = StyleManager(self.root, self.touch_mode)

        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(expand=True, fill='both', padx=2, pady=2)

        self.tab_inventory = ttk.Frame(self.notebook)
        self.tab_pos = ttk.Frame(self.notebook)
        self.tab_correction = ttk.Frame(self.notebook)
        self.tab_summary = ttk.Frame(self.notebook)
        self.tab_settings = ttk.Frame(self.notebook)

        self.notebook.add(self.tab_inventory, text='INVENTORY')
        self.notebook.add(self.tab_pos, text='POS (SALES)')
        self.notebook.add(self.tab_correction, text='CORRECTION')
        self.notebook.add(self.tab_summary, text='SUMMARY')
        self.notebook.add(self.tab_settings, text='SETTINGS')

        self.setup_inventory_tab()
        self.setup_pos_tab()
        self.setup_correction_tab()
        self.setup_summary_tab()
        self.setup_settings_tab()

        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_change)

    def on_tab_change(self, event):
        self.data_manager.refresh_stock_cache()

        # Reset specific tab states
        if hasattr(self, 'pos_qty_var'): self.pos_qty_var.set(1)
        if hasattr(self, 'lbl_stock_avail'): self.lbl_stock_avail.config(text="")
        if hasattr(self, 'pos_dropdown'): self.pos_dropdown.set('')

        current_tab = self.notebook.tab(self.notebook.select(), "text")
        if current_tab == 'CORRECTION':
            self.refresh_correction_list()

    def get_dropdown_values(self) -> List[str]:
        # Helper to get formatted "Name (Price)" list
        if self.data_manager.products_df.empty: return []
        sorted_df = self.data_manager.products_df.sort_values(by=["Product Name"])
        # Use Smart Display Name if available, else fallback
        return sorted_df.apply(lambda x: f"{x.get('_display_name', truncate_product_name(x['Product Name']))} ({x['Price']:.2f})", axis=1).tolist()

    def setup_searchable_combobox(self, combo):
        """Enables typing to filter the combobox values."""
        # Attach a cache to the widget instance to avoid re-fetching on every key stroke
        combo._search_cache = []

        def on_focus(event):
            # Refresh cache when user focuses
            combo._search_cache = self.get_dropdown_values()

        def on_keyrelease(event):
            # Ignore navigation keys
            if event.keysym in ('Up', 'Down', 'Return', 'Tab', 'Left', 'Right', 'Escape'): return

            value = event.widget.get()

            # Lazy load if empty (should have been loaded on focus, but safety check)
            if not combo._search_cache:
                combo._search_cache = self.get_dropdown_values()

            all_values = combo._search_cache

            if value == '':
                combo['values'] = all_values
            else:
                filtered = [item for item in all_values if value.lower() in item.lower()]
                combo['values'] = filtered

        combo.bind('<FocusIn>', on_focus)
        combo.bind('<KeyRelease>', on_keyrelease)

    def show_startup_report(self):
        self.root.update()
        stats = self.data_manager.startup_stats

        if stats.get('rejected', 0) == 0:
            msg = (f"Business: {self.data_manager.business_name}\n"
                   f"Product Load Summary:\nTotal Loaded: {stats['total']}\n"
                   f"New Products: {stats['new']}\n"
                   f"Cleaned Names: {stats.get('cleaned_names', 0)}\n"
                   f"Rejected (Errors): {stats['rejected']}\n"
                   f"Phased-Out: {stats['phased_out']}")
            messagebox.showinfo("Startup Report", msg)
            return

        # Custom Dialog for Rejections
        win = tk.Toplevel(self.root)
        win.title("Startup Report")
        win.geometry("350x300")

        ttk.Label(win, text=f"Business: {self.data_manager.business_name}", font=("Segoe UI", 11, "bold")).pack(pady=10)

        f = ttk.Frame(win)
        f.pack(pady=5, padx=20, fill="x")

        ttk.Label(f, text=f"Total Loaded: {stats['total']}").pack(anchor="w")
        ttk.Label(f, text=f"New Products: {stats['new']}").pack(anchor="w")
        ttk.Label(f, text=f"Cleaned Names: {stats.get('cleaned_names', 0)}").pack(anchor="w")
        ttk.Label(f, text=f"Rejected (Errors): {stats['rejected']}", foreground="red", font=("Segoe UI", 9, "bold")).pack(anchor="w")
        ttk.Label(f, text=f"Phased-Out: {stats['phased_out']}").pack(anchor="w")

        def show_rejected():
            r_win = tk.Toplevel(win)
            r_win.title("Rejected Products")
            r_win.geometry("600x400")

            tree = ttk.Treeview(r_win, columns=("name", "reason"), show="headings")
            tree.heading("name", text="Product Name")
            tree.heading("reason", text="Reason")
            tree.column("name", width=350)
            tree.column("reason", width=200)
            tree.pack(fill="both", expand=True, padx=10, pady=10)

            for item in stats.get('rejected_details', []):
                tree.insert("", "end", values=(item['name'], item['reason']))

            ttk.Button(r_win, text="Close", command=r_win.destroy).pack(pady=10)

        ttk.Button(win, text="VIEW REJECTED PRODUCTS", command=show_rejected, style="Danger.TButton").pack(pady=15, ipadx=10)
        ttk.Button(win, text="OK", command=win.destroy).pack(pady=5, ipadx=20)

    # --- INVENTORY TAB ---
    def setup_inventory_tab(self):
        self.tab_inventory.config(style="Inventory.TFrame")
        self.setup_lws_sidebar(self.tab_inventory, "inventory")

        main_content = ttk.Frame(self.tab_inventory, style="Inventory.TFrame")
        main_content.pack(side="left", fill="both", expand=True)

        f = ttk.LabelFrame(main_content, text="Stock In", style="Inventory.TLabelframe")
        f.pack(fill="x", padx=5, pady=5)

        top_bar = ttk.Frame(f, style="Inventory.TFrame")
        top_bar.pack(fill="x", padx=5, pady=5)

        self.inv_prod_var = tk.StringVar()
        self.inv_dropdown = ttk.Combobox(top_bar, textvariable=self.inv_prod_var, width=45)
        self.inv_dropdown['values'] = self.get_dropdown_values()
        self.setup_searchable_combobox(self.inv_dropdown)
        self.inv_dropdown.pack(side="left", padx=5)

        ttk.Label(top_bar, text="Qty:", style="Inventory.TLabel").pack(side="left")
        self.inv_qty_var = tk.IntVar(value=1)
        ttk.Entry(top_bar, textvariable=self.inv_qty_var, width=5).pack(side="left", padx=5)
        ttk.Button(top_bar, text="Add", command=self.add_inv).pack(side="left", padx=10)

        tree_frame = ttk.Frame(main_content, style="Inventory.TFrame")
        tree_frame.pack(fill="both", expand=True, padx=5, pady=5)

        scrollbar = ttk.Scrollbar(tree_frame)
        scrollbar.pack(side="right", fill="y")

        self.inv_tree = ttk.Treeview(tree_frame, columns=("cat", "name", "price", "qty"), show="headings",
                                     yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.inv_tree.yview)
        self.inv_tree.heading("cat", text="Category")
        self.inv_tree.heading("name", text="Product")
        self.inv_tree.heading("price", text="Price")
        self.inv_tree.heading("qty", text="Qty")
        self.inv_tree.pack(fill="both", expand=True)

        b = ttk.Frame(main_content, style="Inventory.TFrame")
        b.pack(fill="x", padx=5, pady=10)
        ttk.Button(b, text="COMMIT STOCK", command=self.commit_inv, style="Accent.TButton").pack(side="right", ipadx=10)
        ttk.Button(b, text="Clear", command=self.clear_inv).pack(side="right", padx=5)
        ttk.Button(b, text="Del Line", command=self.del_inv_line).pack(side="right", padx=5)

    def add_inv(self):
        sel, qty = self.inv_prod_var.get(), self.inv_qty_var.get()
        if not sel or qty <= 0: return
        _, name, price, cat = self.data_manager.get_product_details_by_str(sel)

        found = False
        for i in self.inventory_cart:
            if i['name'] == name and i['price'] == price:
                i['qty'] += qty
                found = True
                break
        if not found:
            self.inventory_cart.append({"code": "", "name": name, "price": price, "qty": qty, "category": cat})
        self.refresh_inv()

    def refresh_inv(self):
        for i in self.inv_tree.get_children(): self.inv_tree.delete(i)
        for i in sorted(self.inventory_cart, key=lambda x: (x['category'], x['name'])):
            self.inv_tree.insert("", "end", values=(i['category'], i['name'], f"{i['price']:.2f}", i['qty']))

    def del_inv_line(self):
        if not self.inv_tree.selection(): return
        name = self.inv_tree.item(self.inv_tree.selection()[0])['values'][1]
        self.inventory_cart = [i for i in self.inventory_cart if str(i['name']) != str(name)]
        self.refresh_inv()

    def clear_inv(self):
        self.inventory_cart = []
        self.refresh_inv()

    def commit_inv(self):
        if not self.inventory_cart: return
        now = datetime.datetime.now()
        date_str = now.strftime('%Y-%m-%d %H:%M:%S')
        fname = f"Inventory_{now.strftime('%Y%m%d-%H%M%S')}.pdf"

        # Calculate new stocks for receipt
        p_items = []
        for i in self.inventory_cart:
            curr_stock = self.data_manager.get_stock_level(i['name'])
            new_stock = curr_stock + i['qty']
            x = i.copy()
            x['new_stock'] = new_stock
            p_items.append(x)

        success = self.report_manager.generate_grouped_pdf(
            os.path.join(INVENTORY_FOLDER, fname),
            "INVENTORY RECEIPT", date_str, p_items,
            ["Item", "Price", "Qty Added", "New Stock"],
            [1.0, 4.5, 5.5, 6.5], subtotal_indices=[2], is_inventory=True
        )

        if success:
            self.data_manager.add_transaction("inventory", fname, self.inventory_cart, date_str)
            self.clear_inv()
            messagebox.showinfo("Success", f"Stock Added. Receipt: {fname}")

    # --- POS (SALES) TAB ---
    def setup_pos_tab(self):
        self.tab_pos.config(style="Sales.TFrame")
        self.setup_lws_sidebar(self.tab_pos, "sales")

        main_content = ttk.Frame(self.tab_pos, style="Sales.TFrame")
        main_content.pack(side="left", fill="both", expand=True)

        f = ttk.LabelFrame(main_content, text="Sale")
        f.pack(fill="x", padx=5, pady=5)

        input_row = ttk.Frame(f)
        input_row.pack(fill="x", padx=5, pady=5)

        self.pos_prod_var = tk.StringVar()
        self.pos_dropdown = ttk.Combobox(input_row, textvariable=self.pos_prod_var, width=45)
        self.pos_dropdown['values'] = self.get_dropdown_values()
        self.setup_searchable_combobox(self.pos_dropdown)
        self.pos_dropdown.pack(side="left", padx=5)
        self.pos_dropdown.bind("<<ComboboxSelected>>", self.on_pos_sel)

        ttk.Label(input_row, text="Qty:").pack(side="left")
        self.pos_qty_var = tk.IntVar(value=1)
        ttk.Entry(input_row, textvariable=self.pos_qty_var, width=5).pack(side="left", padx=2)
        ttk.Button(input_row, text="ADD", command=self.add_pos).pack(side="left", padx=10)

        self.lbl_stock_avail = ttk.Label(input_row, text="", foreground="blue", font=("Segoe UI", 9, "bold"))
        self.lbl_stock_avail.pack(side="left", padx=10)

        tree_frame = ttk.Frame(main_content)
        tree_frame.pack(fill="both", expand=True, padx=5, pady=5)

        scrollbar = ttk.Scrollbar(tree_frame)
        scrollbar.pack(side="right", fill="y")

        self.pos_tree = ttk.Treeview(tree_frame, columns=("cat", "name", "price", "qty", "sub"),
                                     show="headings", yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.pos_tree.yview)

        self.pos_tree.heading("cat", text="Cat")
        self.pos_tree.heading("name", text="Product")
        self.pos_tree.heading("price", text="Price")
        self.pos_tree.heading("qty", text="Qty")
        self.pos_tree.heading("sub", text="Sub")
        self.pos_tree.column("cat", width=80)
        self.pos_tree.column("price", width=60)
        self.pos_tree.column("qty", width=40)
        self.pos_tree.column("sub", width=70)
        self.pos_tree.pack(fill="both", expand=True)

        b = ttk.Frame(main_content)
        b.pack(fill="x", padx=5, pady=10)
        self.lbl_pos_total = ttk.Label(b, text="Total: 0.00", font=("Segoe UI", 14, "bold"), foreground="#d32f2f")
        self.lbl_pos_total.pack(side="left", padx=5)

        ttk.Button(b, text="CHECKOUT", command=self.checkout, style="Accent.TButton").pack(side="right", ipadx=20)
        ttk.Button(b, text="Clear", command=self.clear_pos).pack(side="right", padx=5)
        ttk.Button(b, text="Del", command=self.del_pos_line).pack(side="right", padx=5)

    def on_pos_sel(self, e):
        sel = self.pos_prod_var.get()
        if not sel: self.lbl_stock_avail.config(text=""); return

        _, name, _, _ = self.data_manager.get_product_details_by_str(sel)
        real_inv = self.data_manager.get_stock_level(name)
        in_cart = sum(i['qty'] for i in self.sales_cart if i['name'] == name)

        self.lbl_stock_avail.config(text=f"Stk: {int(real_inv - in_cart)}")

    def add_pos(self):
        sel, qty = self.pos_prod_var.get(), self.pos_qty_var.get()
        if not sel or qty <= 0: return
        _, name, price, cat = self.data_manager.get_product_details_by_str(sel)

        real_inv = self.data_manager.get_stock_level(name)
        cart_q = sum(i['qty'] for i in self.sales_cart if i['name'] == name)

        if (cart_q + qty) > real_inv:
            messagebox.showerror("Stock", f"Low Stock!\nAvail: {int(real_inv)}")
            return

        sub = price * qty
        found = False
        for i in self.sales_cart:
            if i['name'] == name:
                i['qty'] += qty
                i['subtotal'] += sub
                found = True
                break
        if not found:
            self.sales_cart.append({"code": "", "name": name, "price": price, "qty": qty, "subtotal": sub, "category": cat})

        self.refresh_pos()
        self.on_pos_sel(None)

    def refresh_pos(self):
        for i in self.pos_tree.get_children(): self.pos_tree.delete(i)
        tot = 0
        for i in sorted(self.sales_cart, key=lambda x: (x['category'], x['name'])):
            self.pos_tree.insert("", "end", values=(i['category'], i['name'], f"{i['price']:.2f}", i['qty'],
                                                    f"{i['subtotal']:.2f}"))
            tot += i['subtotal']
        self.lbl_pos_total.config(text=f"Total: {tot:.2f}")

    def del_pos_line(self):
        if not self.pos_tree.selection(): return
        name = self.pos_tree.item(self.pos_tree.selection()[0])['values'][1]
        self.sales_cart = [i for i in self.sales_cart if str(i['name']) != str(name)]
        self.refresh_pos()
        self.on_pos_sel(None)

    def clear_pos(self):
        self.sales_cart = []
        self.refresh_pos()
        self.on_pos_sel(None)

    def checkout(self):
        if not self.sales_cart: return
        now = datetime.datetime.now()
        date_str = now.strftime('%Y-%m-%d %H:%M:%S')
        fname = f"{now.strftime('%Y%m%d-%H%M%S')}.pdf"

        success = self.report_manager.generate_grouped_pdf(
            os.path.join(RECEIPT_FOLDER, fname),
            "SALES RECEIPT", date_str, self.sales_cart,
            ["Item", "Price", "Qty", "Total"],
            [1.0, 4.5, 5.5, 6.5], subtotal_indices=[2, 3]
        )

        if success:
            self.data_manager.add_transaction("sales", fname, self.sales_cart, date_str)
            self.clear_pos()
            messagebox.showinfo("Success", f"Saved: {fname}")

    # --- CORRECTION TAB ---
    def setup_correction_tab(self):
        paned = ttk.PanedWindow(self.tab_correction, orient="horizontal")
        paned.pack(fill="both", expand=True, padx=5, pady=5)

        frame_list = ttk.LabelFrame(paned, text="Step 1: Choose Receipt (Today)")
        paned.add(frame_list, weight=1)

        c_filter = ttk.Frame(frame_list)
        c_filter.pack(fill="x", padx=5, pady=5)
        ttk.Label(c_filter, text="Type:").pack(side="left")
        self.corr_type_var = tk.StringVar(value="sales")
        ttk.OptionMenu(c_filter, self.corr_type_var, "sales", "sales", "inventory",
                       command=lambda _: self.refresh_correction_list()).pack(side="left")
        ttk.Button(c_filter, text="Refresh", command=self.refresh_correction_list).pack(side="left", padx=5)

        self.corr_list_tree = ttk.Treeview(frame_list, columns=("time", "file"), show="headings")
        self.corr_list_tree.heading("time", text="Time")
        self.corr_list_tree.column("time", width=100)
        self.corr_list_tree.heading("file", text="Filename")
        self.corr_list_tree.pack(fill="both", expand=True, padx=5, pady=5)
        ttk.Button(frame_list, text="CHOOSE >>", command=self.load_receipt_for_correction).pack(fill="x", padx=5, pady=5)

        frame_editor = ttk.LabelFrame(paned, text="Step 2: Correct Quantities")
        paned.add(frame_editor, weight=2)

        self.lbl_corr_target = ttk.Label(frame_editor, text="No receipt selected", foreground="blue",
                                         font=("Segoe UI", 10, "bold"))
        self.lbl_corr_target.pack(padx=5, pady=5)

        self.corr_edit_tree = ttk.Treeview(frame_editor, columns=("name", "qty_orig", "qty_adj"), show="headings")
        self.corr_edit_tree.heading("name", text="Product")
        self.corr_edit_tree.heading("qty_orig", text="Orig Qty")
        self.corr_edit_tree.column("qty_orig", width=60)
        self.corr_edit_tree.heading("qty_adj", text="Adjustment (+/-)")
        self.corr_edit_tree.column("qty_adj", width=100)
        self.corr_edit_tree.pack(fill="both", expand=True, padx=5, pady=5)
        self.corr_edit_tree.bind("<Double-1>", self.ask_correction_val)

        ttk.Label(frame_editor, text="Double click 'Adjustment' to edit. Negative (-) removes items.",
                  font=("Segoe UI", 8)).pack()
        ttk.Button(frame_editor, text="FINALIZE CORRECTION", style="Danger.TButton",
                   command=self.finalize_correction).pack(fill="x", padx=20, pady=10)
        self.selected_transaction = None

    def refresh_correction_list(self):
        for i in self.corr_list_tree.get_children(): self.corr_list_tree.delete(i)
        target_type = self.corr_type_var.get()
        now_str = datetime.datetime.now().strftime("%Y-%m-%d")

        for trans in self.data_manager.ledger:
            if trans.get('type') == target_type:
                ts = trans.get('timestamp', '')
                if ts.startswith(now_str):
                    time_part = ts.split(' ')[1] if ' ' in ts else ts
                    self.corr_list_tree.insert("", "end", values=(time_part, trans.get('filename')),
                                               tags=(json.dumps(trans),))

    def load_receipt_for_correction(self):
        sel = self.corr_list_tree.selection()
        if not sel: return

        trans_str = self.corr_list_tree.item(sel[0], 'tags')[0]
        self.selected_transaction = json.loads(trans_str)
        self.lbl_corr_target.config(text=f"Editing: {self.selected_transaction['filename']}")

        for i in self.corr_edit_tree.get_children(): self.corr_edit_tree.delete(i)
        self.correction_cart = []
        for item in self.selected_transaction.get('items', []):
            c_item = item.copy()
            c_item['adjustment'] = 0
            self.correction_cart.append(c_item)
            self.corr_edit_tree.insert("", "end", values=(item['name'], item['qty'], 0))

    def ask_correction_val(self, event):
        if not self.selected_transaction: return
        sel = self.corr_edit_tree.selection()
        if not sel: return
        idx = self.corr_edit_tree.index(sel[0])
        item = self.correction_cart[idx]

        new_val = simpledialog.askinteger("Correction",
                                          f"Enter Adjustment for {item['name']}\n(Negative to reduce, Positive to add):",
                                          initialvalue=0, parent=self.root)
        if new_val is not None:
            self.correction_cart[idx]['adjustment'] = new_val
            self.corr_edit_tree.item(sel[0], values=(item['name'], item['qty'], new_val))

    def finalize_correction(self):
        if not self.selected_transaction: return
        adjustments = [i for i in self.correction_cart if i['adjustment'] != 0]
        if not adjustments: messagebox.showinfo("Info", "No adjustments made."); return
        if not messagebox.askyesno("Confirm", "This will modify the database. Proceed?"): return

        # Remove old correction PDF if exists for this reference (simplification)
        ref_file = self.selected_transaction['filename']
        # Note: logic to remove old correction entry in ledger is complex, keeping simple append for safety

        now = datetime.datetime.now()
        date_str = now.strftime('%Y-%m-%d %H:%M:%S')
        fname = f"Cor_{now.strftime('%Y%m%d-%H%M%S')}.pdf"

        pdf_items = []
        ledger_adjustment_items = []

        for item in self.correction_cart:
            orig = item['qty']
            adj = item['adjustment']
            final = orig + adj
            pdf_item = {"code": "", "name": item['name'], "price": item['price'], "qty": adj, "qty_orig": orig,
                        "qty_final": final, "category": item.get('category', 'Uncategorized')}
            pdf_items.append(pdf_item)
            if adj != 0:
                ledger_item = item.copy()
                ledger_item['qty'] = adj
                ledger_adjustment_items.append(ledger_item)

        success = self.report_manager.generate_grouped_pdf(
            os.path.join(CORRECTION_FOLDER, fname),
            "CORRECTION RECEIPT", date_str, pdf_items,
            ["Item", "Orig", "Adj", "Final"],
            [1.0, 4.5, 5.5, 6.5], is_summary=False, extra_info=f"Ref: {ref_file}"
        )

        if success:
            self.data_manager.add_transaction("correction", fname, ledger_adjustment_items,
                                              date_str, self.selected_transaction['type'], ref_file)

            for i in self.corr_edit_tree.get_children(): self.corr_edit_tree.delete(i)
            self.lbl_corr_target.config(text="No receipt selected")
            self.selected_transaction = None
            messagebox.showinfo("Success", f"Correction Saved: {fname}")

    # --- SUMMARY TAB ---
    def setup_summary_tab(self):
        f = ttk.Frame(self.tab_summary)
        f.pack(fill="x", padx=5, pady=5)

        ttk.Label(f, text="Period:").pack(side="left")
        self.report_type = tk.StringVar(value="All Time")
        ttk.OptionMenu(f, self.report_type, "All Time", "Daily", "Weekly", "Monthly", "All Time").pack(side="left", padx=5)

        self.chk_custom_date_var = tk.BooleanVar(value=False)
        self.chk_custom_date = ttk.Checkbutton(f, text="OTHER DATE", variable=self.chk_custom_date_var,
                                               command=self.toggle_custom_date)
        self.chk_custom_date.pack(side="left", padx=10)

        self.frame_custom_date = ttk.Frame(f)
        self.frame_custom_date.pack(side="left")

        current_year = datetime.datetime.now().year
        self.cmb_year = ttk.Combobox(self.frame_custom_date,
                                     values=[y for y in range(current_year - 5, current_year + 2)], width=5,
                                     state="disabled")
        self.cmb_year.set(current_year)
        self.cmb_year.pack(side="left", padx=1)

        self.cmb_month = ttk.Combobox(self.frame_custom_date, values=[str(m).zfill(2) for m in range(1, 13)], width=3,
                                      state="disabled")
        self.cmb_month.set(str(datetime.datetime.now().month).zfill(2))
        self.cmb_month.pack(side="left", padx=1)

        self.cmb_day = ttk.Combobox(self.frame_custom_date, values=[str(d).zfill(2) for d in range(1, 32)], width=3,
                                    state="disabled")
        self.cmb_day.set(str(datetime.datetime.now().day).zfill(2))
        self.cmb_day.pack(side="left", padx=1)

        ttk.Button(f, text="Refresh View", command=self.gen_view).pack(side="left", padx=10)
        ttk.Button(f, text="Gen PDF", command=self.gen_pdf).pack(side="left", padx=5)

        tree_frame = ttk.Frame(self.tab_summary)
        tree_frame.pack(fill="both", expand=True, padx=5, pady=5)
        scrollbar = ttk.Scrollbar(tree_frame)
        scrollbar.pack(side="right", fill="y")
        self.sum_tree = ttk.Treeview(tree_frame, columns=("cat", "name", "price", "in", "out", "rem", "sale"),
                                     show="headings", yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.sum_tree.yview)

        self.sum_tree.heading("cat", text="Cat")
        self.sum_tree.heading("name", text="Product")
        self.sum_tree.heading("price", text="Price")
        self.sum_tree.heading("in", text="In")
        self.sum_tree.heading("out", text="Out")
        self.sum_tree.heading("rem", text="Stk")
        self.sum_tree.heading("sale", text="Sales")
        for col in ["in", "out", "rem", "price"]: self.sum_tree.column(col, width=50)
        self.sum_tree.pack(fill="both", expand=True)
        self.lbl_sum_info = ttk.Label(self.tab_summary, text="Ready")
        self.lbl_sum_info.pack(pady=2)

    def toggle_custom_date(self):
        state = "readonly" if self.chk_custom_date_var.get() else "disabled"
        self.cmb_year.config(state=state)
        self.cmb_month.config(state=state)
        self.cmb_day.config(state=state)

    def get_period_dates(self):
        if self.chk_custom_date_var.get():
            try:
                y = int(self.cmb_year.get())
                m = int(self.cmb_month.get())
                d = int(self.cmb_day.get())
                anchor = datetime.datetime(y, m, d, 23, 59, 59)
            except ValueError:
                messagebox.showerror("Date Error", "Invalid Custom Date selected.")
                return None
        else:
            anchor = datetime.datetime.now().replace(microsecond=0)

        mode = self.report_type.get()
        if mode == "Daily": return anchor.replace(hour=0, minute=0, second=0), anchor
        if mode == "Weekly":
            start_of_week = (anchor - datetime.timedelta(days=anchor.weekday())).replace(hour=0, minute=0, second=0)
            return start_of_week, anchor
        if mode == "Monthly": return anchor.replace(day=1, hour=0, minute=0, second=0), anchor
        return None

    def get_sum_data(self, override_period=None):
        global_stats, _, _, _ = self.data_manager.calculate_stats(None)

        # Use filtered period if override_period provided, otherwise get from UI selection
        if override_period:
            period = override_period
        else:
            period = self.get_period_dates()

        period_stats, in_c, out_c, corr_list = self.data_manager.calculate_stats(period)

        rows = []
        all_names = set(self.data_manager.products_df['Product Name'].astype(str)) | set(global_stats.keys())

        for name in all_names:
            name = name.strip()
            g_data = global_stats.get(name, {'in': 0, 'out': 0})
            rem_stock = g_data['in'] - g_data['out']

            _, _, curr_price, cat = self.data_manager.get_product_details_by_str(f"{name}")
            p_data = period_stats.get(name, {'in': 0, 'out': 0, 'sales_lines': [], 'in_lines': []})

            price_map = {}
            # Aggregate by price point
            for line in p_data['sales_lines']:
                p = line['price']
                if p not in price_map: price_map[p] = {'in': 0, 'out': 0, 'sales': 0}
                price_map[p]['out'] += line['qty']
                price_map[p]['sales'] += line['amt']
            for line in p_data['in_lines']:
                p = line['price']
                if p not in price_map: price_map[p] = {'in': 0, 'out': 0, 'sales': 0}
                price_map[p]['in'] += line['qty']

            if not price_map: price_map[curr_price] = {'in': 0, 'out': 0, 'sales': 0}

            for price, data in price_map.items():
                show_rem = rem_stock if price == curr_price else 0

                # Filter Logic
                # If using override_period (catchup), we behave like a specific period report (hide zeros)
                # If UI selected "All Time", we show everything including zero movement items if they exist in inventory

                is_all_time = (self.report_type.get() == "All Time") and (override_period is None)

                if not is_all_time:
                    if data['in'] == 0 and data['out'] == 0: continue
                elif data['in'] == 0 and data['out'] == 0 and show_rem == 0 and name not in set(
                        self.data_manager.products_df['Product Name']):
                    continue

                if cat == "Phased Out" and name in global_stats: name = global_stats[name]['name'] + " (Old)"

                rows.append({
                    'code': "", 'category': cat, 'name': name, 'price': price,
                    'in': data['in'], 'out': data['out'], 'remaining': show_rem, 'sales': data['sales']
                })

        final_rows = []
        names_in_excel = set(self.data_manager.products_df['Product Name'].astype(str))
        for r in rows:
            is_active = (r['in'] > 0 or r['out'] > 0 or r['remaining'] > 0 or r['name'] in names_in_excel)
            if is_active: final_rows.append(r)

        return final_rows, in_c, out_c, corr_list

    def gen_view(self, override_period=None):
        data, in_c, out_c, corr_list = self.get_sum_data(override_period)
        for i in self.sum_tree.get_children(): self.sum_tree.delete(i)

        def sort_key(x):
            cat = x['category']
            if cat == "Phased Out": cat = "zzz_Phased Out"
            return (cat, x['name'])

        data = sorted(data, key=sort_key)
        tot = 0
        for s in data:
            self.sum_tree.insert("", "end",
                                 values=(s['category'], s['name'], f"{s['price']:.2f}", int(s['in']), int(s['out']),
                                         int(s['remaining']), f"{s['sales']:.2f}"))
            tot += s['sales']

        p_txt = self.report_type.get()
        if p_txt != "All Time":
            s, e = override_period if override_period else self.get_period_dates()
            if s and e:
                p_txt = f"{s.strftime('%m-%d')} to {e.strftime('%m-%d')}"
        self.lbl_sum_info.config(text=f"Period: {p_txt} | Sales: {tot:.2f}")
        return data, tot, p_txt, in_c, out_c, corr_list

    def gen_pdf(self):
        is_custom_date = self.chk_custom_date_var.get()
        data, tot, p_txt, in_c, out_c, corr_list = self.gen_view()
        now = datetime.datetime.now()

        prefix = "History" if is_custom_date else "Summary"
        fname = f"{prefix}-{now.strftime('%Y%m%d-%H%M%S')}.pdf"
        full_path = os.path.join(SUMMARY_FOLDER, fname)

        success = self.report_manager.generate_grouped_pdf(
            full_path, "INVENTORY & SALES SUMMARY",
            now.strftime('%Y-%m-%d %H:%M:%S'), data,
            ["Product", "Price", "Added", "Sold", "Stock", "Sales"],
            [1.0, 4.5, 5.2, 5.9, 6.6, 7.3], is_summary=True,
            extra_info=f"Period: {p_txt} | In: {in_c} | Out: {out_c}",
            subtotal_indices=[2, 3, 5], correction_list=corr_list
        )

        if success:
            if not is_custom_date:
                self.data_manager.summary_count += 1
                self.data_manager.save_ledger()

                recipient = self.data_manager.config.get("recipient_email", "").strip()
                if recipient:
                    extra_attachments = []

                    # CATCHUP LOGIC
                    catchup_start = self.get_catchup_start_time()
                    if catchup_start:
                        catchup_intervals = self.get_catchup_intervals(catchup_start, now)
                        if catchup_intervals:
                            catchup_fname = f"Catchup_{now.strftime('%Y%m%d-%H%M%S')}.pdf"
                            catchup_path = os.path.join(SUMMARY_FOLDER, catchup_fname)

                            # We pass get_sum_data (wrapper) to generate_catchup_report
                            # get_sum_data requires 'period' as override
                            # But get_sum_data signature is (self, override_period=None)
                            # so we can use a lambda
                            c_success = self.report_manager.generate_catchup_report(
                                catchup_path,
                                catchup_intervals,
                                self.data_manager,
                                lambda period: self.get_sum_data(override_period=period)
                            )
                            if c_success:
                                extra_attachments.append(catchup_path)

                    self.email_manager.trigger_summary_email(
                        recipient, full_path, LEDGER_FILE, self.data_manager.business_name,
                        self.data_manager.summary_count, self.session_user,
                        extra_attachments=extra_attachments,
                        on_success=self.update_email_sync_timestamp
                    )

                messagebox.showinfo("Success", f"Summary Generated & Sent.\nReceipt: {fname}")
            else:
                messagebox.showinfo("History Generated", f"Historical PDF Generated (No Email/Counter).\nFile: {fname}")

    def get_catchup_start_time(self) -> Optional[datetime.datetime]:
        """Finds the timestamp of the oldest unsent Summary/History receipt."""
        last_sync_str = self.data_manager.config.get("last_email_sync", "")
        last_sync_dt = None
        if last_sync_str:
            try:
                last_sync_dt = datetime.datetime.strptime(last_sync_str, "%Y-%m-%d %H:%M:%S")
            except:
                pass # Invalid or empty, treat as never synced (or start from beginning?)

        # Regex to match filenames like Summary-YYYYMMDD-HHMMSS.pdf
        # Note: History- files are usually manual and maybe shouldn't count?
        # User said "summarizes all Summary Receipts generated but were not sent".
        # Let's stick to "Summary-*" files which are the official automated ones.

        candidates = []
        try:
            for f in os.listdir(SUMMARY_FOLDER):
                if f.startswith("Summary-") and f.endswith(".pdf"):
                    # Extract date
                    try:
                        part = f.replace("Summary-", "").replace(".pdf", "")
                        dt = datetime.datetime.strptime(part, "%Y%m%d-%H%M%S")

                        if last_sync_dt is None or dt > last_sync_dt:
                            candidates.append(dt)
                    except:
                        pass
        except Exception as e:
            print(f"Error scanning summary folder: {e}")

        if not candidates:
            return None

        return min(candidates)

    def get_catchup_intervals(self, start: datetime.datetime, end: datetime.datetime) -> List[Tuple[datetime.datetime, datetime.datetime]]:
        total_duration = end - start
        if total_duration.total_seconds() < 60:
            return [] # Too short to bother

        segment = total_duration / 3

        i1_end = start + segment
        i2_end = i1_end + segment

        return [
            (start, i1_end),
            (i1_end, i2_end),
            (i2_end, end)
        ]

    def update_email_sync_timestamp(self):
        now_str = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.data_manager.config["last_email_sync"] = now_str
        self.data_manager.save_config()

    # --- SETTINGS TAB ---
    def setup_settings_tab(self):
        self.settings_notebook = ttk.Notebook(self.tab_settings)
        self.settings_notebook.pack(fill="both", expand=True, padx=5, pady=5)

        self.tab_settings_general = ttk.Frame(self.settings_notebook)
        self.tab_settings_web = ttk.Frame(self.settings_notebook)

        self.settings_notebook.add(self.tab_settings_general, text="General")
        self.settings_notebook.add(self.tab_settings_web, text="Web Server")

        # General
        f = ttk.LabelFrame(self.tab_settings_general, text="Settings")
        f.pack(fill="both", expand=True, padx=10, pady=10)

        self.chk_startup_var = tk.BooleanVar(value=self.data_manager.config.get("startup", False))
        ttk.Checkbutton(f, text="Launch at Startup", variable=self.chk_startup_var, command=self.toggle_startup).pack(pady=5, anchor="w")

        self.chk_touch_var = tk.BooleanVar(value=self.touch_mode)
        ttk.Checkbutton(f, text="Enable Touch Mode (Larger UI)", variable=self.chk_touch_var, command=self.toggle_touch_mode).pack(pady=5, anchor="w")

        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Label(f, text="Email Receipt Sync", font=("Segoe UI", 10, "bold")).pack(anchor="w")

        email_frame = ttk.Frame(f)
        email_frame.pack(anchor="w", pady=5, fill="x")
        ttk.Label(email_frame, text="Recipient Email:").pack(side="left")
        self.entry_email = ttk.Entry(email_frame, width=35)
        self.entry_email.insert(0, self.data_manager.config.get("recipient_email", ""))
        self.entry_email.pack(side="left", padx=5)
        ttk.Button(email_frame, text="Confirm & Test", command=self.verify_and_test_email).pack(side="left", padx=5)

        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Label(f, text="Visuals", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        ttk.Label(f, text="Splash Image:").pack(pady=(5, 0), anchor="w")
        self.entry_img = ttk.Entry(f, width=40)
        self.entry_img.insert(0, self.data_manager.config.get("splash_img", ""))
        self.entry_img.pack(pady=2, anchor="w")
        ttk.Button(f, text="Browse", command=self.browse_splash).pack(pady=2, anchor="w")
        ttk.Button(f, text="Save Visual Settings", command=self.save_display_settings).pack(pady=5, anchor="w")

        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Label(f, text="Backup / Restore", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        bf = ttk.Frame(f)
        bf.pack(anchor="w", pady=5)
        ttk.Button(bf, text="Backup (.json)", command=self.backup_data_json).pack(side="left", padx=5)
        ttk.Button(bf, text="Restore (.json)", command=self.restore_data_json).pack(side="left", padx=5)

        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Label(f, text="Maintenance", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        mf = ttk.Frame(f)
        mf.pack(anchor="w", pady=5)
        ttk.Button(mf, text="Harmonize Receipts", command=lambda: self.harmonize_receipts(silent=False)).pack(side="left", padx=5)
        ttk.Button(mf, text="Restore Products File", command=self.regenerate_products_file).pack(side="left", padx=5)

        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Button(f, text="Load Test (Dev)", command=self.run_load_test, style="Danger.TButton").pack(anchor="w", pady=5)

        # Web Server Panel
        self.setup_web_server_panel(self.tab_settings_web)

    def verify_and_test_email(self):
        email_input = self.entry_email.get().strip()
        if not email_input:
            self.data_manager.config["recipient_email"] = ""
            self.data_manager.save_config()
            messagebox.showinfo("Email Disabled", "Email field cleared.")
            return

        if not self.email_manager.validate_email_format(email_input):
            messagebox.showerror("Invalid Email", "Invalid format.")
            return

        self.data_manager.config["recipient_email"] = email_input
        self.data_manager.save_config()

        subject = f"Receipt Sync Confirmation - {APP_TITLE}"
        body = f"This email has been entered as recipient for {APP_TITLE} receipts by {self.session_user}."
        self.email_manager.send_email_thread(email_input, subject, body, is_test=True,
                                             on_success=lambda: messagebox.showinfo("Success", "Test email sent."),
                                             on_error=lambda e: messagebox.showerror("Error", str(e)))

    def browse_splash(self):
        path = filedialog.askopenfilename(filetypes=[("Image Files", "*.jpg *.png")])
        if path: self.entry_img.delete(0, tk.END); self.entry_img.insert(0, path)

    def save_display_settings(self):
        self.data_manager.config["splash_img"] = self.entry_img.get()
        self.data_manager.save_config()
        messagebox.showinfo("Success", "Saved.")

    def toggle_touch_mode(self):
        enabled = self.chk_touch_var.get()
        self.data_manager.config["touch_mode"] = enabled
        self.data_manager.save_config()
        self.style_manager.set_touch_mode(enabled)
        # Note: full effect requires restart, but we can try to re-apply styles
        messagebox.showinfo("Restart Required", "Please restart the application for Touch Mode changes to fully take effect.")

    def toggle_startup(self):
        startup_folder = os.path.join(os.getenv("APPDATA"), r"Microsoft\Windows\Start Menu\Programs\Startup")
        bat_path = os.path.join(startup_folder, "POS_System_Auto.bat")

        if self.chk_startup_var.get():
            try:
                exe_path = sys.executable if getattr(sys, 'frozen', False) else os.path.abspath(__file__)
                with open(bat_path, "w") as bat:
                    bat.write(f'start "" "{exe_path}"' if getattr(sys, 'frozen', False) else f'python "{exe_path}"')
                self.data_manager.config["startup"] = True
                self.data_manager.save_config()
                messagebox.showinfo("Startup", "Enabled.")
            except Exception as e:
                self.chk_startup_var.set(False)
                messagebox.showerror("Error", str(e))
        else:
            if os.path.exists(bat_path): os.remove(bat_path)
            self.data_manager.config["startup"] = False
            self.data_manager.save_config()
            messagebox.showinfo("Startup", "Disabled.")

    def backup_data_json(self):
        if not self.data_manager.ledger:
            messagebox.showinfo("Backup", "No data to backup.")
            return
        save_path = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON Database", "*.json")])
        if save_path:
            try:
                products_data = self.data_manager.get_product_list()
                data = {
                    "transactions": self.data_manager.ledger,
                    "summary_count": self.data_manager.summary_count,
                    "products_master": products_data,
                    "shortcuts_asked": self.data_manager.shortcuts_asked
                }
                with open(save_path, 'w') as f:
                    json.dump(data, f, indent=2)
                messagebox.showinfo("Backup", "Done.")
            except Exception as e:
                messagebox.showerror("Error", f"Backup failed: {e}")

    def restore_data_json(self):
        path = filedialog.askopenfilename(filetypes=[("JSON Database", "*.json")])
        if not path: return
        if not messagebox.askyesno("Confirm", "Overwrite data and REGENERATE receipts?"): return
        try:
            with open(path, 'r') as f:
                backup_data = json.load(f)

            # Restore logic coordinated via DataManager
            if isinstance(backup_data, list):
                self.data_manager.ledger = backup_data
                self.data_manager.summary_count = 0
            elif isinstance(backup_data, dict):
                self.data_manager.ledger = backup_data.get("transactions", [])
                self.data_manager.summary_count = backup_data.get("summary_count", 0)
                self.data_manager.shortcuts_asked = backup_data.get("shortcuts_asked", False)

                # Restore products if present (basic regen)
                products_master = backup_data.get("products_master", [])
                if products_master and self.mod.pd:
                    try:
                        new_df = self.mod.pd.DataFrame(products_master)
                        new_df.to_excel(DATA_FILE, index=False)
                        self.data_manager.load_products()
                        # Update UI
                        self.inv_dropdown['values'] = self.get_dropdown_values()
                        self.pos_dropdown['values'] = self.get_dropdown_values()
                    except Exception:
                        pass # Non-critical

            self.harmonize_receipts(silent=True)
            self.data_manager.save_ledger()
            self.data_manager.refresh_stock_cache()
            messagebox.showinfo("Success", f"Restored {len(self.data_manager.ledger)} records.")

        except Exception as e:
            messagebox.showerror("Error", f"Failed: {e}")

    def harmonize_receipts(self, silent: bool = False):
        if not silent:
            if not messagebox.askyesno("Confirm", "This will DELETE and REGENERATE all PDF receipts from the database.\nContinue?"):
                return

        try:
            # Regenerate Receipts
            for folder in [INVENTORY_FOLDER, RECEIPT_FOLDER, CORRECTION_FOLDER]:
                if os.path.exists(folder): shutil.rmtree(folder); os.makedirs(folder)

            for entry in self.data_manager.ledger:
                fname = entry.get('filename')
                date_str = entry.get('timestamp')
                items = entry.get('items', [])

                if entry['type'] == "inventory":
                    self.report_manager.generate_grouped_pdf(
                        os.path.join(INVENTORY_FOLDER, fname), "INVENTORY RECEIPT", date_str,
                        items, ["Item", "Price", "Qty Added", "New Stock"], [1.0, 4.5, 5.5, 6.5],
                        subtotal_indices=[2], is_inventory=True
                    )
                elif entry['type'] == "sales":
                    self.report_manager.generate_grouped_pdf(
                        os.path.join(RECEIPT_FOLDER, fname), "SALES RECEIPT", date_str, items,
                        ["Item", "Price", "Qty", "Total"], [1.0, 4.5, 5.5, 6.5],
                        subtotal_indices=[2, 3]
                    )
                elif entry['type'] == "correction":
                    pdf_items = []
                    for it in items:
                        pdf_items.append({
                            "code": "", "name": it['name'], "price": it['price'],
                            "qty_orig": 0, "qty": it['qty'], "qty_final": it['qty'],
                            "category": it.get('category')
                        })
                    self.report_manager.generate_grouped_pdf(
                        os.path.join(CORRECTION_FOLDER, fname), "CORRECTION RECEIPT", date_str,
                        pdf_items, ["Item", "Orig", "Adj", "Final"], [1.0, 4.5, 5.5, 6.5]
                    )

            if not silent:
                messagebox.showinfo("Success", "All receipts harmonized with ledger.")

        except Exception as e:
            if not silent:
                messagebox.showerror("Error", f"Harmonization Failed: {e}")
            else:
                raise e

    def regenerate_products_file(self):
        history = self.data_manager.product_history
        if not history or len(history) < 2:
            messagebox.showinfo("History", "No previous product versions available.")
            return

        # Show versions (excluding the very last one which is current)
        # candidates are history[:-1] if we assume the last one is always current.
        # But wait, history[-1] is the one loaded *now*.
        # If the user changed the file externally and opened the app, history[-1] matches the file.
        # The user wants "past 3 versions prior to the current version".

        # If we have [A, B, C, D(current)], we want user to pick from C, B, A.
        # So we slice history[:-1] and reverse it to show newest first.
        candidates = history[:-1]
        if not candidates:
             messagebox.showinfo("History", "No *past* versions available.")
             return

        # Create a simple dialog
        win = tk.Toplevel(self.root)
        win.title("Select Version")
        win.geometry("400x300")

        ttk.Label(win, text="Select a past version to restore:", font=("Segoe UI", 10, "bold")).pack(pady=10)

        tree = ttk.Treeview(win, columns=("ts", "count"), show="headings")
        tree.heading("ts", text="Timestamp")
        tree.heading("count", text="Items")
        tree.column("ts", width=200)
        tree.column("count", width=80)
        tree.pack(fill="both", expand=True, padx=10, pady=5)

        # Sort candidates newest first
        sorted_candidates = sorted(candidates, key=lambda x: x['timestamp'], reverse=True)

        # Limit to 3 as requested
        sorted_candidates = sorted_candidates[:3]

        for ver in sorted_candidates:
            tree.insert("", "end", values=(ver['timestamp'], len(ver['items'])), tags=(json.dumps(ver),))

        def restore():
            sel = tree.selection()
            if not sel: return

            data_str = tree.item(sel[0], 'tags')[0]
            version_data = json.loads(data_str)
            items = version_data.get('items', [])

            if not items:
                messagebox.showerror("Error", "Selected version has no items.")
                return

            if messagebox.askyesno("Confirm", f"Restore products from {version_data['timestamp']}?\nThis will overwrite products.xlsx."):
                try:
                    df = self.mod.pd.DataFrame(items)
                    # Ensure column order if possible, though not strictly required by load_products
                    # load_products expects Business Name, Product Category, Product Name, Price
                    df.to_excel(DATA_FILE, index=False)
                    self.data_manager.load_products()

                    # Update UI Dropdowns
                    self.inv_dropdown['values'] = self.get_dropdown_values()
                    self.pos_dropdown['values'] = self.get_dropdown_values()

                    messagebox.showinfo("Success", "Products restored and reloaded.")
                    win.destroy()
                except Exception as e:
                    messagebox.showerror("Error", f"Failed to restore: {e}")

        ttk.Button(win, text="Restore Selected", command=restore).pack(pady=10)

    def run_load_test(self):
        pwd = simpledialog.askstring("Load Test", "Enter Password:", show="*")
        if pwd != "migs": messagebox.showerror("Error", "Incorrect Password"); return
        if not messagebox.askyesno("WARNING",
                                   "This will DELETE ALL DATA and generate dummy data for the last 30 days.\n\nAre you sure?"): return

        self.data_manager.ledger = []
        self.data_manager.summary_count = 0
        for folder in [INVENTORY_FOLDER, RECEIPT_FOLDER, CORRECTION_FOLDER]:
            if os.path.exists(folder): shutil.rmtree(folder); os.makedirs(folder)

        if self.data_manager.products_df.empty:
            messagebox.showerror("Error", "No products loaded from products.xlsx")
            return

        products = []
        for _, row in self.data_manager.products_df.iterrows():
            products.append(
                {"name": row['Product Name'], "price": float(row['Price']), "category": row['Product Category']})

        stock_tracker = {p['name']: 0 for p in products}
        start_date = datetime.datetime.now() - datetime.timedelta(days=30)

        try:
            for day_offset in range(31):
                curr_date = start_date + datetime.timedelta(days=day_offset)
                date_str_base = curr_date.strftime("%Y-%m-%d")

                # Inventory Logic
                if day_offset % 7 == 0 or day_offset == 30:
                    inv_items = []
                    for p in products:
                        current_qty = stock_tracker[p['name']]
                        weekly_demand_est = 21
                        safety_stock = random.randint(10, 20)
                        target_level = weekly_demand_est + safety_stock
                        needed = target_level - current_qty
                        if needed > 0:
                            stock_tracker[p['name']] += needed
                            inv_items.append({"code": "", "name": p['name'], "price": p['price'], "qty": needed,
                                              "category": p['category'], "new_stock": stock_tracker[p['name']]})
                    if inv_items:
                        ts = f"{date_str_base} 08:00:00"
                        fname = f"Inventory_{curr_date.strftime('%Y%m%d')}-080000.pdf"

                        self.report_manager.generate_grouped_pdf(
                            os.path.join(INVENTORY_FOLDER, fname), "INVENTORY RECEIPT", ts,
                            inv_items, ["Item", "Price", "Qty Added", "New Stock"],
                            [1.0, 4.5, 5.5, 6.5], subtotal_indices=[2], is_inventory=True
                        )
                        self.data_manager.ledger.append(
                            {"type": "inventory", "timestamp": ts, "filename": fname, "items": inv_items})

                # Sales Logic
                num_sales = random.randint(5, 10)
                for s_i in range(num_sales):
                    sales_items = []
                    num_lines = random.randint(1, 5)
                    attempts = 0
                    while len(sales_items) < num_lines and attempts < 20:
                        attempts += 1
                        p = random.choice(products)
                        if any(x['name'] == p['name'] for x in sales_items): continue

                        qty = random.randint(1, 3)
                        if stock_tracker[p['name']] >= qty:
                            stock_tracker[p['name']] -= qty
                            sub = p['price'] * qty
                            sales_items.append(
                                {"code": "", "name": p['name'], "price": p['price'], "qty": qty, "subtotal": sub,
                                 "category": p['category']})

                    if sales_items:
                        hour = 9 + (s_i % 9)
                        minute = random.randint(0, 59)
                        ts = f"{date_str_base} {hour:02d}:{minute:02d}:{random.randint(10, 59)}"
                        fname = f"{curr_date.strftime('%Y%m%d')}-{hour:02d}{minute:02d}{random.randint(10, 59)}.pdf"

                        self.report_manager.generate_grouped_pdf(
                            os.path.join(RECEIPT_FOLDER, fname), "SALES RECEIPT", ts, sales_items,
                            ["Item", "Price", "Qty", "Total"], [1.0, 4.5, 5.5, 6.5],
                            subtotal_indices=[2, 3]
                        )
                        self.data_manager.ledger.append({"type": "sales", "timestamp": ts, "filename": fname, "items": sales_items})

            self.data_manager.save_ledger()
            self.data_manager.refresh_stock_cache()
            messagebox.showinfo("Load Test", "Simulation Complete.\nData overwritten.")

        except Exception as e:
            messagebox.showerror("Load Test Error", f"Simulation failed: {e}")

    # --- WEB SERVER GUI HELPERS ---
    def setup_web_server_panel(self, parent_frame):
        frame = ttk.Frame(parent_frame)
        frame.pack(fill="both", expand=True, padx=20, pady=20)

        left_panel = ttk.LabelFrame(frame, text="Connection Info")
        left_panel.pack(side="left", fill="both", expand=True, padx=10)

        self.lbl_url = ttk.Label(left_panel, text="Server URL:", font=("Segoe UI", 12))
        self.lbl_url.pack(pady=(20, 5))

        self.entry_url = ttk.Entry(left_panel, font=("Segoe UI", 10, "bold"), justify="center", width=40)
        self.entry_url.pack(pady=5)

        self.qr_lbl = tk.Label(left_panel, bg="white")
        self.qr_lbl.pack(pady=20, padx=20)

        ttk.Button(left_panel, text="Generate New QR (Revoke Old)", command=self.rotate_token).pack(pady=10)
        ttk.Label(left_panel, text="Scanning a new QR invalidates previous links.", foreground="red",
                  font=("Segoe UI", 9)).pack()

        right_panel = ttk.LabelFrame(frame, text="Connected Devices (Session)")
        right_panel.pack(side="right", fill="both", expand=True, padx=10)

        self.device_tree = ttk.Treeview(right_panel, columns=("ip", "count"), show="headings")
        self.device_tree.heading("ip", text="Device IP")
        self.device_tree.heading("count", text="Transactions")
        self.device_tree.column("ip", width=150)
        self.device_tree.column("count", width=100)
        self.device_tree.pack(fill="both", expand=True, padx=5, pady=5)

        self.qr_lbl.config(text="Click 'Generate New QR' to start LWS")

    def get_local_ip(self):
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("8.8.8.8", 80))
            ip = s.getsockname()[0]
            s.close()
            return ip
        except:
            return "127.0.0.1"

    def find_free_port(self):
        port = 5000
        while port < 5100:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                if s.connect_ex(('localhost', port)) != 0:
                    return port
                port += 1
        return 5000

    def start_web_server(self):
        if self.web_server_running: return

        # Dependency injection for the thread
        self.web_thread = WebServerThread(
            self.mod, self.web_queue, self.web_port,
            lambda: self.data_manager,
            lambda: self.session_token
        )
        self.web_thread.start()
        self.web_server_running = True
        self.show_remote_sidebars()

    def rotate_token(self):
        self.session_token = secrets.token_hex(4)
        if not self.web_server_running:
            self.start_web_server()
        self.generate_qr()
        self.refresh_connected_devices_table()

    def generate_qr(self):
        url = f"http://{self.local_ip}:{self.web_port}/?token={self.session_token}"
        self.entry_url.config(state="normal")
        self.entry_url.delete(0, tk.END)
        self.entry_url.insert(0, url)
        self.entry_url.config(state="readonly")

        qr = self.mod.qrcode.QRCode(box_size=10, border=4)
        qr.add_data(url)
        qr.make(fit=True)
        img = qr.make_image(fill="black", back_color="white")

        self.tk_qr = ImageTk.PhotoImage(img.resize((250, 250)))
        self.qr_lbl.config(image=self.tk_qr)

    def refresh_connected_devices_table(self):
        for i in self.device_tree.get_children():
            self.device_tree.delete(i)
        for ip, count in self.connected_devices.items():
            self.device_tree.insert("", "end", values=(ip, count))

    # --- LWS REQUEST HANDLING ---
    def setup_lws_sidebar(self, parent_frame, mode):
        sidebar_frame = ttk.Frame(parent_frame, width=250)
        sidebar_frame.pack(side="right", fill="y", padx=5, pady=5)
        sidebar_frame.pack_forget()
        sidebar_frame.pack_propagate(False)

        self.lws_sidebars[mode] = sidebar_frame
        lbl_title = ttk.Label(sidebar_frame, text="Remote Requests", font=("Segoe UI", 10, "bold"))
        lbl_title.pack(pady=5)

        tree_frame = ttk.Frame(sidebar_frame)
        tree_frame.pack(fill="both", expand=True)

        cols = ("time", "ip", "summary")
        tree = ttk.Treeview(tree_frame, columns=cols, show="headings")
        tree.heading("time", text="Time")
        tree.heading("ip", text="IP")
        tree.heading("summary", text="Total")
        tree.column("time", width=50)
        tree.column("ip", width=80)
        tree.column("summary", width=80)
        tree.pack(fill="both", expand=True)

        if mode == 'inventory':
            self.inv_req_tree = tree
        else:
            self.pos_req_tree = tree

        btn_frame = ttk.Frame(sidebar_frame)
        btn_frame.pack(pady=10)
        ttk.Button(btn_frame, text="Add to Cart", width=12,
                   command=lambda: self.action_remote_request(mode, "add_to_cart")).pack(side="left", padx=5)
        ttk.Button(btn_frame, text="✖", width=4,
                   command=lambda: self.action_remote_request(mode, "reject")).pack(side="left", padx=5)

    def show_remote_sidebars(self):
        for mode, frame in self.lws_sidebars.items():
            frame.pack(side="right", fill="y", padx=5, pady=5)

    def process_web_queue(self):
        try:
            while True:
                task = self.web_queue.get_nowait()
                if task['type'] == 'web_transaction':
                    self.handle_remote_transaction(task['data'], task['ip'])
        except queue.Empty:
            pass
        self.root.after(500, self.process_web_queue)

    def handle_remote_transaction(self, data, ip):
        if ip not in self.connected_devices:
            self.connected_devices[ip] = 0
        self.connected_devices[ip] += 1
        self.refresh_connected_devices_table()

        mode = data.get('mode')
        items = data.get('items', [])

        if not items: return
        now = datetime.datetime.now()

        request_id = secrets.token_hex(4)
        request_data = {
            "id": request_id,
            "ip": ip,
            "mode": mode,
            "timestamp": now,
            "items": items
        }

        # Double Check Stock for Safety
        if mode == 'sales':
             for i in items:
                 name = i['name']
                 req_qty = int(i['qty'])
                 avail = self.data_manager.get_stock_level(name)
                 if req_qty > avail:
                     print(f"Rejected invalid stock request from {ip}")
                     return

        self.remote_requests.append(request_data)
        self.refresh_remote_sidebars()

    def refresh_remote_sidebars(self):
        # Refresh Inventory Sidebar
        for i in self.inv_req_tree.get_children(): self.inv_req_tree.delete(i)
        for req in self.remote_requests:
            if req['mode'] == 'inventory':
                time_str = req['timestamp'].strftime('%H:%M')
                total_items = sum(int(x.get('qty', 0)) for x in req['items'])
                item_summary = f"{total_items} items"
                self.inv_req_tree.insert("", "end", values=(time_str, req['ip'], item_summary), tags=(req['id'],))

        # Refresh POS Sidebar
        for i in self.pos_req_tree.get_children(): self.pos_req_tree.delete(i)
        for req in self.remote_requests:
            if req['mode'] == 'sales':
                time_str = req['timestamp'].strftime('%H:%M')
                total_amt = sum(float(x.get('price', 0)) * int(x.get('qty', 0)) for x in req['items'])
                item_summary = f"{total_amt:.2f}"
                self.pos_req_tree.insert("", "end", values=(time_str, req['ip'], item_summary), tags=(req['id'],))

    def action_remote_request(self, mode, action):
        tree = self.inv_req_tree if mode == 'inventory' else self.pos_req_tree
        sel = tree.selection()
        if not sel: return

        req_id = tree.item(sel[0], 'tags')[0]
        req = next((r for r in self.remote_requests if r['id'] == req_id), None)
        if not req: return

        if action == "reject":
            if messagebox.askyesno("Reject", "Reject this request?"):
                self.remote_requests.remove(req)
                self.refresh_remote_sidebars()
        elif action == "add_to_cart":
            self.load_remote_request_to_cart(req)

    def load_remote_request_to_cart(self, req):
        mode = req['mode']
        items = req['items']

        processed_items = []
        for i in items:
            processed_items.append({
                "code": "",
                "name": i['name'],
                "price": float(i['price']),
                "qty": int(i['qty']),
                "subtotal": float(i.get('price', 0)) * int(i.get('qty', 0)),
                "category": i.get('category', 'General')
            })

        if mode == 'sales':
            warnings = []
            for i in processed_items:
                avail = self.data_manager.get_stock_level(i['name'])
                if i['qty'] > avail:
                    warnings.append(f"{i['name']} (Req: {i['qty']}, Avail: {int(avail)})")

            if warnings:
                msg = "Insufficient stock for:\n" + "\n".join(warnings) + "\n\nAdd to cart anyway?"
                if not messagebox.askyesno("Stock Warning", msg):
                    return

            self.sales_cart = processed_items
            self.refresh_pos()
            self.on_pos_sel(None)
            self.notebook.select(self.tab_pos)

        elif mode == 'inventory':
            self.inventory_cart = processed_items
            self.refresh_inv()
            self.notebook.select(self.tab_inventory)

        self.remote_requests.remove(req)
        self.refresh_remote_sidebars()

    # --- AUTO TASKS ---
    def check_shortcuts(self):
        if not self.data_manager.shortcuts_asked:
            if messagebox.askyesno("Desktop Shortcuts", "Create shortcuts for App and Summary Folder on Desktop?"):
                self.create_shortcuts()
            self.data_manager.shortcuts_asked = True
            self.data_manager.save_ledger()

    def create_shortcuts(self):
        try:
            desktop = os.path.normpath(os.path.join(os.environ['USERPROFILE'], 'Desktop'))
            exe_path = sys.executable if getattr(sys, 'frozen', False) else os.path.abspath(__file__)
            exe_dir = os.path.dirname(exe_path)
            link_name = f"{APP_TITLE}.lnk"
            self.create_shortcut_vbs(exe_path, os.path.join(desktop, link_name), working_dir=exe_dir)

            folder_path = os.path.abspath(SUMMARY_FOLDER)
            folder_link_name = "Summary Receipts.lnk"
            self.create_shortcut_vbs(folder_path, os.path.join(desktop, folder_link_name))
            messagebox.showinfo("Shortcuts", "Shortcuts created on Desktop.")
        except Exception as e:
            messagebox.showerror("Shortcut Error", f"Could not create shortcuts: {e}")

    def create_shortcut_vbs(self, target, link_path, working_dir=None):
        work_dir_line = f'oLink.WorkingDirectory = "{working_dir}"' if working_dir else ""
        vbs_content = f"""
            Set oWS = WScript.CreateObject("WScript.Shell")
            Set oLink = oWS.CreateShortcut("{link_path}")
            oLink.TargetPath = "{target}"
            {work_dir_line}
            oLink.Save
        """
        vbs_path = os.path.join(os.environ["TEMP"], "create_shortcut.vbs")
        with open(vbs_path, "w") as f:
            f.write(vbs_content)
        os.system(f'cscript //Nologo "{vbs_path}"')
        try:
            os.remove(vbs_path)
        except:
            pass

    def check_beginning_inventory_reminder(self):
        today_str = datetime.datetime.now().strftime("%Y-%m-%d")
        last_bi_date = self.data_manager.config.get("last_bi_date", "")
        if last_bi_date != today_str:
            self.generate_beginning_inventory_report()

    def generate_beginning_inventory_report(self):
        today = datetime.datetime.now()
        today_str = today.strftime("%Y-%m-%d")

        # Capture current state (Beginning Inventory)
        items = []
        # Get all known products
        all_products = self.data_manager.get_product_list()

        # Include any product that has stock in cache even if not in product list (unlikely but possible if phased out)
        cached_names = set(self.data_manager.stock_cache.keys())
        known_names = set(p['Product Name'] for p in all_products)

        for p in all_products:
            name = p['Product Name']
            cat = p['Product Category']
            qty = self.data_manager.get_stock_level(name)
            items.append({
                "name": name,
                "category": cat,
                "qty": qty,
                "price": 0, # Not used in BI
                "subtotal": 0 # Not used in BI
            })

        # Add items that are in stock but not in the product list (orphaned/phased out)
        for name in cached_names:
            if name not in known_names:
                qty = self.data_manager.get_stock_level(name)
                items.append({
                    "name": f"{name} (Old)",
                    "category": "Phased Out",
                    "qty": qty,
                    "price": 0,
                    "subtotal": 0
                })

        # FILTER: Show only items with POSITIVE stock (qty > 0)
        items = [i for i in items if i['qty'] > 0]

        fname = f"BI-{today.strftime('%Y%m%d')}.pdf"
        full_path = os.path.join(SUMMARY_FOLDER, fname)

        success = self.report_manager.generate_grouped_pdf(
            full_path, "BEGINNING INVENTORY",
            today.strftime('%Y-%m-%d %H:%M:%S'), items,
            ["Product", "Qty"],
            [1.0, 6.0], is_summary=False,
            extra_info=f"Start of Day: {today_str}",
            is_bi=True
        )

        if success:
            self.data_manager.summary_count += 1
            self.data_manager.save_ledger()
            self.data_manager.config["last_bi_date"] = today_str
            self.data_manager.save_config()

            recipient = self.data_manager.config.get("recipient_email", "").strip()
            if recipient:
                # Mock a summary email call but override subject/body via extra_body if possible,
                # or better yet, since trigger_summary_email generates a fixed subject format,
                # we might want to manually send it or accept the format.
                # The user asked for "Beginning Inventory" in subject/body.
                # trigger_summary_email uses "[count]_TITLE_BIZ_DATE" subject format.
                # I should manually send it to respect the "Beginning Inventory" requirement if trigger_summary_email is too rigid.

                # However, trigger_summary_email is convenient. Let's look at it.
                # Subject: [{count:04d}]_{APP_TITLE}_{safe_biz_name}_{date_str}
                # Body: "Summary & Ledger..."

                # I will call email_manager.send_email_thread directly to customize fully as requested.

                safe_biz_name = "".join(c for c in self.data_manager.business_name if c.isalnum() or c in (' ', '_', '-')).strip()
                subject = f"Beginning Inventory - {safe_biz_name} - {today_str}"
                body = (f"Beginning Inventory Report.\n\n"
                        f"User: {self.session_user}\n"
                        f"Counter: {self.data_manager.summary_count:04d}\n"
                        f"Date: {today_str}\n\n"
                        f"Please find the Beginning Inventory PDF and Ledger database attached.")

                self.email_manager.send_email_thread(
                    recipient, subject, body,
                    [full_path, LEDGER_FILE]
                )

            # Optional: Silent or unobtrusive notification
            # self.root.after(500, lambda: messagebox.showinfo("Info", "Beginning Inventory generated."))
            # User said "automatically". Usually implies silent, but I'll print to console or status if I had one.
            print(f"Beginning Inventory generated: {fname}")


# --- SPLASH SCREEN ---
class SplashScreen(tk.Toplevel):
    def __init__(self, root, img_path, business_name, app_title):
        super().__init__(root)
        self.overrideredirect(True)
        width, height = 400, 250
        screen_width = self.winfo_screenwidth()
        screen_height = self.winfo_screenheight()
        x = (screen_width // 2) - (width // 2)
        y = (screen_height // 2) - (height // 2)
        self.geometry(f"{width}x{height}+{int(x)}+{int(y)}")
        self.configure(bg="#2b2b2b")

        if img_path and os.path.exists(img_path):
            try:
                pil_img = Image.open(img_path).resize((180, 130), Image.Resampling.LANCZOS)
                self.img = ImageTk.PhotoImage(pil_img)
                tk.Label(self, image=self.img, bg="#2b2b2b").pack(pady=10)
            except:
                pass

        display_text = f"{business_name}\n{app_title}"
        tk.Label(self, text=display_text, font=("Segoe UI", 12, "bold"), fg="white", bg="#2b2b2b",
                 justify="center").pack(pady=5)
        self.status_lbl = tk.Label(self, text="Initializing...", font=("Segoe UI", 9), fg="lightgray", bg="#2b2b2b")
        self.status_lbl.pack(side="bottom", pady=15)
        self.update()

    def update_status(self, text):
        self.status_lbl.config(text=text)
        self.update()


# --- BOOTSTRAP ---
def launch_app():
    # Close PyInstaller Splash
    try:
        import pyi_splash
        pyi_splash.update_text("Starting Application...")
        pyi_splash.close()
    except ImportError:
        pass

    root = tk.Tk()
    root.withdraw()

    # Load basic config for splash
    cfg = {"splash_img": "", "cached_business_name": "MMD POS System"}
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r') as f:
                loaded_cfg = json.load(f)
                cfg.update(loaded_cfg)
        except:
            pass

    splash = SplashScreen(root, cfg.get("splash_img", ""), cfg.get("cached_business_name", ""), APP_TITLE)

    def loader():
        # Lazy Loading heavy modules
        try:
            splash.update_status("Loading Data Engine (pandas)...")
            import pandas as pd
            AppModules.pd = pd

            splash.update_status("Loading PDF Engine (reportlab)...")
            from reportlab.pdfgen import canvas
            from reportlab.lib.pagesizes import letter
            from reportlab.lib.units import inch
            AppModules.canvas = canvas
            AppModules.letter = letter
            AppModules.inch = inch

            splash.update_status("Loading Utils...")
            from pypdf import PdfReader
            import ntplib
            AppModules.PdfReader = PdfReader
            AppModules.ntplib = ntplib

            splash.update_status("Loading Web Server...")
            from flask import Flask, request, jsonify, render_template_string
            import qrcode
            AppModules.Flask = Flask
            AppModules.request = request
            AppModules.jsonify = jsonify
            AppModules.render_template_string = render_template_string
            AppModules.qrcode = qrcode

            splash.update_status("Loading Email Modules...")
            import smtplib
            import ssl
            from email.mime.text import MIMEText
            from email.mime.multipart import MIMEMultipart
            from email.mime.base import MIMEBase
            from email import encoders
            AppModules.smtplib = smtplib
            AppModules.ssl = ssl
            AppModules.MIMEText = MIMEText
            AppModules.MIMEMultipart = MIMEMultipart
            AppModules.MIMEBase = MIMEBase
            AppModules.encoders = encoders

        except Exception as e:
            messagebox.showerror("Critical Error", f"Missing Libraries: {e}")
            root.destroy()
            return

        splash.update_status("Starting Interface...")

        def login_logic():
            splash.destroy()
            user = simpledialog.askstring("Login", "User:", parent=root)
            if user:
                root.deiconify()
                # Inject modules into main system
                POSSystem(root, user, splash=None, modules=AppModules)
            else:
                root.destroy()

        root.after(500, login_logic)

    root.after(100, loader)
    root.mainloop()

# --- MOBILE HTML TEMPLATE ---
MOBILE_HTML_TEMPLATE = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>POS Remote</title>
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; background: #f2f2f2; margin: 0; padding: 0; transition: background 0.3s; }

        /* THEMES */
        body.sales-theme .header { background: #333; }
        body.sales-theme .btn-add { background: #007bff; }
        body.sales-theme .mode-btn.active { background: #333; color: white; border-bottom: 4px solid #007bff; }

        body.stock-theme { background: #fff3e0; }
        body.stock-theme .header { background: #e65100; }
        body.stock-theme .btn-add { background: #ef6c00; }
        body.stock-theme .mode-btn.active { background: #e65100; color: white; border-bottom: 4px solid white; }

        .header { color: white; padding: 15px; text-align: center; font-weight: bold; font-size: 1.2em; box-shadow: 0 2px 4px rgba(0,0,0,0.2); }
        .container { padding: 15px; }
        .card { background: white; padding: 15px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); margin-bottom: 15px; }
        select, input { width: 100%; padding: 12px; margin: 5px 0; border: 1px solid #ddd; border-radius: 4px; box-sizing: border-box; font-size: 16px; }
        button { width: 100%; padding: 12px; border: none; border-radius: 4px; font-size: 16px; font-weight: bold; cursor: pointer; margin-top: 10px; color: white; }

        .btn-success { background: #28a745; }
        .btn-danger { background: #dc3545; }

        .cart-item { display: flex; justify-content: space-between; padding: 10px 0; border-bottom: 1px solid #eee; }
        .mode-switch { display: flex; background: #ddd; }
        .mode-btn { flex: 1; padding: 15px; text-align: center; cursor: pointer; font-weight:bold; color: #555; transition: all 0.3s; }

        .stock-tag { font-size: 0.8em; color: #666; display: block; margin-bottom: 5px; text-align: right; }
        .error-overlay { position: fixed; top:0; left:0; width:100%; height:100%; background:white; color:red; display:flex; align-items:center; justify-content:center; font-size:1.5em; text-align:center; z-index:999; display:none;}
    </style>
</head>
<body class="sales-theme">
    <div id="auth-error" class="error-overlay">
        Session Expired or Invalid.<br>Please scan the QR code again.
    </div>

    <div class="header" id="header-title">POS REMOTE: SALES</div>

    <div class="mode-switch">
        <div class="mode-btn active" id="btn-sales" onclick="setMode('sales')">SALES</div>
        <div class="mode-btn" id="btn-stock" onclick="setMode('inventory')">STOCK IN</div>
    </div>

    <div class="container">
        <div class="card">
            <label>Select Product:</label>
            <select id="product-select" onchange="updateStockDisplay()"></select>
            <span id="stock-display" class="stock-tag">Checking stock...</span>

            <label>Quantity:</label>
            <input type="number" id="qty" value="1" min="1">

            <button class="btn-add" onclick="addToCart()">ADD TO CART</button>
        </div>

        <div class="card">
            <h3>Cart (<span id="mode-label">Sales</span>)</h3>
            <div id="cart-list"></div>
            <hr>
            <div style="text-align: right; font-weight: bold; font-size: 1.2em;">Total: <span id="total-amt">0.00</span></div>
            <button class="btn-success" onclick="submitTransaction()">REQUEST</button>
            <button class="btn-danger" style="margin-top:5px; background: #666;" onclick="clearCart()">CLEAR</button>
        </div>
    </div>

    <script>
        const AUTH_TOKEN = "{{ token }}";

        let products = [];
        let cart = [];
        let currentMode = 'sales';

        // Load Products with Token and Stock
        fetch('/get_products?token=' + AUTH_TOKEN)
        .then(r => {
            if (r.status === 403) throw new Error("Unauthorized");
            return r.json();
        })
        .then(data => {
            products = data.products; // Now includes 'stock' key
            const sel = document.getElementById('product-select');
            products.forEach(p => {
                let opt = document.createElement('option');
                opt.value = p.name;
                opt.text = p.name + ' (' + p.price + ')';
                sel.add(opt);
            });
            updateStockDisplay();
        })
        .catch(e => {
            document.getElementById('auth-error').style.display = 'flex';
        });

        function setMode(mode) {
            currentMode = mode;
            // Update UI Theme
            document.body.className = mode === 'sales' ? 'sales-theme' : 'stock-theme';

            document.getElementById('btn-sales').className = mode === 'sales' ? 'mode-btn active' : 'mode-btn';
            document.getElementById('btn-stock').className = mode === 'inventory' ? 'mode-btn active' : 'mode-btn';

            document.getElementById('mode-label').innerText = mode === 'sales' ? 'Sales' : 'Stock In';
            document.getElementById('header-title').innerText = mode === 'sales' ? 'POS REMOTE: SALES' : 'POS REMOTE: STOCK IN';

            cart = [];
            renderCart();
            updateStockDisplay();
        }

        function updateStockDisplay() {
            const name = document.getElementById('product-select').value;
            const prod = products.find(p => p.name === name);
            const display = document.getElementById('stock-display');

            if (prod) {
                if (currentMode === 'sales') {
                    // Check local cart to subtract from display
                    let inCart = 0;
                    let existing = cart.find(i => i.name === name);
                    if(existing) inCart = existing.qty;

                    let avail = prod.stock - inCart;
                    display.innerText = "Available Stock: " + avail;
                    display.style.color = avail < 5 ? "red" : "#666";
                } else {
                    display.innerText = "Current Stock: " + prod.stock + " (Adding Mode)";
                    display.style.color = "green";
                }
            }
        }

        function addToCart() {
            const name = document.getElementById('product-select').value;
            const qty = parseInt(document.getElementById('qty').value);
            if(qty < 1 || isNaN(qty)) return;

            const prod = products.find(p => p.name === name);
            if(!prod) return;

            // --- STOCK CHECK (Client Side) ---
            if (currentMode === 'sales') {
                let currentCartQty = 0;
                let existingItem = cart.find(i => i.name === name);
                if (existingItem) currentCartQty = existingItem.qty;

                if ((currentCartQty + qty) > prod.stock) {
                    alert("Insufficient Stock! You have " + prod.stock + " available.");
                    return;
                }
            }

            let existing = cart.find(i => i.name === name);
            if(existing) {
                existing.qty += qty;
                existing.subtotal = existing.qty * existing.price;
            } else {
                cart.push({
                    name: prod.name,
                    price: prod.price,
                    category: prod.category,
                    qty: qty,
                    subtotal: prod.price * qty
                });
            }
            renderCart();
            updateStockDisplay();
        }

        function renderCart() {
            const list = document.getElementById('cart-list');
            list.innerHTML = '';
            let total = 0;
            cart.forEach((item, index) => {
                total += item.subtotal;
                let div = document.createElement('div');
                div.className = 'cart-item';
                div.innerHTML = `<span>${item.name} x${item.qty}</span> <span>${item.subtotal.toFixed(2)}</span> <span style='color:red; cursor:pointer; margin-left:10px;' onclick='remItem(${index})'>[x]</span>`;
                list.appendChild(div);
            });
            document.getElementById('total-amt').innerText = total.toFixed(2);
        }

        function remItem(idx) {
            cart.splice(idx, 1);
            renderCart();
            updateStockDisplay();
        }

        function clearCart() {
            cart = [];
            renderCart();
            updateStockDisplay();
        }

        function submitTransaction() {
            if(cart.length === 0) return alert("Cart is empty");

            // Re-validate all items before sending (Client side double check)
            if (currentMode === 'sales') {
                for (let item of cart) {
                    let prod = products.find(p => p.name === item.name);
                    if (prod && item.qty > prod.stock) {
                        alert("Stock changed! " + item.name + " has insufficient quantity.");
                        return;
                    }
                }
            }

            if(!confirm("Submit this request to PC?")) return;

            // Submit with Token in URL
            fetch('/submit_transaction?token=' + AUTH_TOKEN, {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({mode: currentMode, items: cart})
            })
            .then(r => {
                if (r.status === 403) throw new Error("Unauthorized");
                return r.json();
            })
            .then(res => {
                if(res.status === 'success') {
                    alert("Success! Request sent to PC.");
                    cart = [];
                    renderCart();
                    // Refresh product list to get new stock levels
                    location.reload();
                } else {
                    alert("Error: " + res.message);
                }
            })
            .catch(e => {
                if (e.message === "Unauthorized") document.getElementById('auth-error').style.display = 'flex';
                else alert("Connection Error");
            });
        }
    </script>
</body>
</html>
"""

if __name__ == "__main__":
    launch_app()