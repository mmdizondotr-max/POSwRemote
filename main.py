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
import re  # Restore import re
from PIL import Image, ImageTk
from style_manager import StyleManager

# pyinstaller --onefile --noconsole --splash splash_image.png main.py

# --- CONFIGURATION ---
RECEIPT_FOLDER = "receipts"
INVENTORY_FOLDER = "inventoryreceipts"
SUMMARY_FOLDER = "summaryreceipts"
CORRECTION_FOLDER = "correctionreceipts"
DATA_FILE = "products.xlsx"
CONFIG_FILE = "config.json"
LEDGER_FILE = "ledger.json"
APP_TITLE = "MMD Portable PoS v13.0"  # Version Bump

# --- EMAIL SENDER CONFIGURATION ---
SMTP_SERVER = "smtp.gmail.com"
SMTP_PORT = 587
SENDER_EMAIL = "mmdpos.diz@gmail.com"
SENDER_PASSWORD = "wvdg kkka myuk inve"

# Placeholder for heavy modules
pd = None
canvas = None
letter = None
inch = None
Flask = None
request = None
jsonify = None
render_template_string = None
qrcode = None
smtplib = None
ssl = None
MIMEText = None
MIMEMultipart = None
MIMEBase = None
encoders = None

# Ensure folders exist
for folder in [RECEIPT_FOLDER, INVENTORY_FOLDER, SUMMARY_FOLDER, CORRECTION_FOLDER]:
    if not os.path.exists(folder):
        os.makedirs(folder)

# --- EMBEDDED MOBILE WEB APP (IMPROVED UI & LOGIC) ---
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


# --- WEB SERVER THREAD (UPDATED FOR STOCK CHECK) ---
class WebServerThread(threading.Thread):
    def __init__(self, task_queue, port, app_context_provider, auth_provider):
        super().__init__()
        self.task_queue = task_queue
        self.port = port
        self.get_context = app_context_provider
        self.get_auth_token = auth_provider
        self.app = Flask(__name__)
        self.daemon = True

        import logging
        log = logging.getLogger('werkzeug')
        log.setLevel(logging.ERROR)

        self.setup_routes()

    def setup_routes(self):
        @self.app.route('/')
        def index():
            token = request.args.get('token')
            current_valid_token = self.get_auth_token()
            if not token or token != current_valid_token:
                return "<h1>403 Forbidden</h1><p>Invalid or Expired QR Code. Please scan the new code on the PC.</p>", 403
            return render_template_string(MOBILE_HTML_TEMPLATE, token=current_valid_token)

        @self.app.route('/get_products')
        def get_products():
            token = request.args.get('token')
            if not token or token != self.get_auth_token():
                return jsonify({"error": "Unauthorized"}), 403

            ctx = self.get_context()
            prods_df = ctx['df']
            stock_cache = ctx.get('stock_cache', {})  # Access Stock Cache

            prods = prods_df.to_dict(orient='records')
            cleaned_prods = []
            for p in prods:
                name = p.get('Product Name', 'Unknown')
                # Calculate real stock for mobile
                stats = stock_cache.get(name, {'in': 0, 'out': 0})
                current_qty = stats['in'] - stats['out']

                cleaned_prods.append({
                    "name": name,
                    "price": float(p.get('Price', 0)),
                    "category": p.get('Product Category', 'General'),
                    "stock": int(current_qty)  # Send stock info
                })
            return jsonify({"business": ctx['business_name'], "products": cleaned_prods})

        @self.app.route('/submit_transaction', methods=['POST'])
        def submit():
            token = request.args.get('token')
            if not token or token != self.get_auth_token():
                return jsonify({"error": "Unauthorized"}), 403

            data = request.json
            mode = data.get('mode')
            items = data.get('items', [])

            # --- SERVER SIDE STOCK VALIDATION ---
            if mode == 'sales':
                ctx = self.get_context()
                stock_cache = ctx.get('stock_cache', {})
                for item in items:
                    name = item.get('name')
                    req_qty = int(item.get('qty', 0))
                    stats = stock_cache.get(name, {'in': 0, 'out': 0})
                    avail = stats['in'] - stats['out']
                    if req_qty > avail:
                        return jsonify({"status": "error",
                                        "message": f"Stock change detected! Only {int(avail)} remaining for {name}."})

            client_ip = request.remote_addr
            self.task_queue.put({"type": "web_transaction", "data": data, "ip": client_ip})
            return jsonify({"status": "success", "message": "Queued"})

    def run(self):
        try:
            self.app.run(host='0.0.0.0', port=self.port, threaded=True)
        except Exception as e:
            print(f"Web Server Error: {e}")


# --- MAIN SYSTEM ---
class POSSystem:
    def __init__(self, root, username, splash):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("1100x750")
        self.root.minsize(800, 500)
        try:
            self.root.state('zoomed')
        except:
            self.root.attributes('-zoomed', True)

        # Session Info
        login_time = datetime.datetime.now().strftime("%H%M%S")
        self.session_user = f"{username}-{login_time}"
        self.last_email_time = 0

        # Data & Config
        if splash: splash.update_status("Loading Config & Ledger...")
        self.config = self.load_config()
        self.touch_mode = self.config.get("touch_mode", False)
        self.ledger, self.summary_count, self.shortcuts_asked = self.load_ledger()

        if splash: splash.update_status("Loading Products...")
        self.products_df = pd.DataFrame()
        self.business_name = "My Business"
        self.load_products()

        if splash: splash.update_status("Calculating Stock...")
        self.current_stock_cache = {}
        self.refresh_stock_cache()

        # Carts
        self.sales_cart = []
        self.inventory_cart = []
        self.correction_cart = []
        self.remote_requests = [] # List to store pending remote requests
        self.lws_sidebars = {}

        # Web Server State
        self.web_queue = queue.Queue()
        self.local_ip = self.get_local_ip()
        self.web_port = self.find_free_port()
        self.connected_devices = {}
        self.session_token = secrets.token_hex(4)
        self.web_thread = None
        self.web_server_running = False

        # UI Setup
        self.setup_ui()
        self.show_startup_report()

        # Scheduled Tasks
        self.root.after(1000, self.check_beginning_inventory_reminder)
        self.root.after(2000, self.check_shortcuts)
        self.root.after(100, self.process_web_queue)

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

    # --- WEB SERVER LOGIC ---
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

        def get_context():
            # Injecting self.current_stock_cache so Web Thread can see real levels
            return {
                "df": self.products_df,
                "business_name": self.business_name,
                "stock_cache": self.current_stock_cache
            }

        def get_token():
            return self.session_token

        self.web_thread = WebServerThread(self.web_queue, self.web_port, get_context, get_token)
        self.web_thread.start()
        self.web_server_running = True
        self.show_remote_sidebars()

    def rotate_token(self):
        self.session_token = secrets.token_hex(4)
        if not self.web_server_running:
            self.start_web_server()
        self.generate_qr()
        self.refresh_connected_devices_table()

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
        now = self.get_time()

        # Add to remote requests list
        request_id = secrets.token_hex(4)
        request_data = {
            "id": request_id,
            "ip": ip,
            "mode": mode,
            "timestamp": now,
            "items": items
        }

        # Stock Check Logic for Sales is already done in Web Server Thread, but double check
        if mode == 'sales':
            stats, _, _, _ = self.calculate_stats(None)
            for i in items:
                 name = i['name']
                 req_qty = int(i['qty'])
                 hist = stats.get(name, {'in': 0, 'out': 0})
                 avail = hist['in'] - hist['out']
                 if req_qty > avail:
                     # This should have been caught by server, but if not, reject silently or log
                     print(f"Rejected invalid stock request from {ip}")
                     return

        self.remote_requests.append(request_data)
        self.refresh_remote_sidebars()

        # Notify user (optional sound or flash?)
        # messagebox.showinfo("New Request", f"New {mode} request from {ip}") # Too intrusive?

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
            # Check stock warning
            stats, _, _, _ = self.calculate_stats(None)
            warnings = []
            for i in processed_items:
                hist = stats.get(i['name'], {'in': 0, 'out': 0})
                avail = hist['in'] - hist['out']
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

        # QR is not generated initially now
        self.qr_lbl.config(text="Click 'Generate New QR' to start LWS")

    def generate_qr(self):
        url = f"http://{self.local_ip}:{self.web_port}/?token={self.session_token}"
        self.entry_url.config(state="normal")
        self.entry_url.delete(0, tk.END)
        self.entry_url.insert(0, url)
        self.entry_url.config(state="readonly")

        qr = qrcode.QRCode(box_size=10, border=4)
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

    # --- EXISTING DATA UTILITIES ---
    def load_config(self):
        default = {
            "startup": False,
            "splash_img": "",
            "cached_business_name": "My Business",
            "previous_products": [],
            "recipient_email": "",
            "last_bi_date": ""
        }
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r') as f:
                    return json.load(f)
            except:
                pass
        return default

    def save_config(self):
        with open(CONFIG_FILE, 'w') as f: json.dump(self.config, f)

    def load_ledger(self):
        if os.path.exists(LEDGER_FILE):
            try:
                with open(LEDGER_FILE, 'r') as f:
                    data = json.load(f)
                    if isinstance(data, list):
                        return data, 0, False
                    elif isinstance(data, dict):
                        return data.get("transactions", []), data.get("summary_count", 0), data.get("shortcuts_asked", False)
            except:
                return [], 0, False
        return [], 0, False

    def save_ledger(self):
        try:
            data = {"transactions": self.ledger, "summary_count": self.summary_count, "shortcuts_asked": self.shortcuts_asked}
            with open(LEDGER_FILE, 'w') as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not save database: {e}")

    def check_shortcuts(self):
        if not self.shortcuts_asked:
            if messagebox.askyesno("Desktop Shortcuts", "Create shortcuts for App and Summary Folder on Desktop?"):
                self.create_shortcuts()
            self.shortcuts_asked = True
            self.save_ledger()

    def create_shortcuts(self):
        try:
            desktop = os.path.normpath(os.path.join(os.environ['USERPROFILE'], 'Desktop'))

            # 1. App Shortcut
            exe_path = sys.executable if getattr(sys, 'frozen', False) else os.path.abspath(__file__)
            link_name = f"{APP_TITLE}.lnk"
            self.create_shortcut_vbs(exe_path, os.path.join(desktop, link_name))

            # 2. Summary Folder Shortcut
            folder_path = os.path.abspath(SUMMARY_FOLDER)
            folder_link_name = "Summary Receipts.lnk"
            self.create_shortcut_vbs(folder_path, os.path.join(desktop, folder_link_name))

            messagebox.showinfo("Shortcuts", "Shortcuts created on Desktop.")
        except Exception as e:
            messagebox.showerror("Shortcut Error", f"Could not create shortcuts: {e}")

    def create_shortcut_vbs(self, target, link_path):
        vbs_content = f"""
            Set oWS = WScript.CreateObject("WScript.Shell")
            Set oLink = oWS.CreateShortcut("{link_path}")
            oLink.TargetPath = "{target}"
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

    def get_time(self):
        return datetime.datetime.now()

    def load_products(self):
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
            return

        if "Business Name" in raw_df.columns and not raw_df.empty:
            val = str(raw_df.iloc[0]["Business Name"]).strip()
            if val and val.lower() != "nan":
                self.business_name = val
                self.config["cached_business_name"] = val

        valid_products = []
        seen_names = set()
        rejected_count = 0

        for index, row in raw_df.iterrows():
            cat = str(row.get('Product Category', '')).strip()
            name = str(row.get('Product Name', '')).strip()
            raw_price = row.get('Price', 0)
            try:
                price = float(raw_price)
            except:
                price = 0.0

            is_valid = True
            if price <= 0 or pd.isna(raw_price): is_valid = False
            if not cat or cat.lower() == 'nan': is_valid = False
            if name in seen_names: is_valid = False
            if not name or name.lower() == 'nan': is_valid = False

            if is_valid:
                seen_names.add(name)
                b_name = str(row.get('Business Name', self.business_name))
                valid_products.append({
                    "Business Name": b_name,
                    "Product Category": cat,
                    "Product Name": name,
                    "Price": price
                })
            else:
                rejected_count += 1

        self.products_df = pd.DataFrame(valid_products)
        previous_products = set(self.config.get("previous_products", []))
        current_products = set(seen_names)
        self.startup_stats = {
            "total": len(valid_products),
            "new": len(current_products - previous_products),
            "rejected": rejected_count,
            "phased_out": len(previous_products - current_products)
        }
        self.config["previous_products"] = list(seen_names)
        self.save_config()

    def show_startup_report(self):
        self.root.update()
        stats = self.startup_stats
        msg = (f"Business: {self.business_name}\n"
               f"Product Load Summary:\nTotal Loaded: {stats['total']}\n"
               f"New Products: {stats['new']}\nRejected (Errors): {stats['rejected']}\n"
               f"Phased-Out: {stats['phased_out']}")
        messagebox.showinfo("Startup Report", msg)

    def check_beginning_inventory_reminder(self):
        today_str = datetime.datetime.now().strftime("%Y-%m-%d")
        last_bi_date = self.config.get("last_bi_date", "")
        if last_bi_date != today_str:
            resp = messagebox.askyesno("Daily Reminder",
                                       "Beginning Inventory has not been generated for today.\n"
                                       "Do you want to generate now?")
            if resp: self.generate_beginning_inventory_report()

    def generate_beginning_inventory_report(self):
        today = datetime.datetime.now()
        yesterday = today - datetime.timedelta(days=1)
        start = yesterday.replace(hour=0, minute=0, second=0, microsecond=0)
        end = yesterday.replace(hour=23, minute=59, second=59, microsecond=0)
        period = (start, end)
        yesterday_str = yesterday.strftime("%Y-%m-%d")

        data, tot, p_txt, in_c, out_c, corr_list = self.gen_view(override_period=period)
        now = self.get_time()
        fname = f"Summary-{now.strftime('%Y%m%d-%H%M%S')}.pdf"
        full_path = os.path.join(SUMMARY_FOLDER, fname)

        success = self.generate_grouped_pdf(full_path, "INVENTORY & SALES SUMMARY",
                                            now.strftime('%Y-%m-%d %H:%M:%S'), data,
                                            ["Product", "Price", "Added", "Sold", "Stock", "Sales"],
                                            [1.0, 4.5, 5.2, 5.9, 6.6, 7.3], is_summary=True,
                                            extra_info=f"Period: {yesterday_str} (Daily) | In: {in_c} | Out: {out_c}",
                                            subtotal_indices=[2, 3, 5], correction_list=corr_list)
        if success:
            self.summary_count += 1
            self.save_ledger()
            self.config["last_bi_date"] = today.strftime("%Y-%m-%d")
            self.save_config()
            note = f"Note: This is an automated Beginning Inventory report for {yesterday_str}."
            self.trigger_email_send(full_path, extra_body=note)
            messagebox.showinfo("Auto-Gen",
                                f"Beginning Inventory for {yesterday_str} generated & emailed.\nReceipt: {fname}")

    def get_dropdown_values(self):
        if not self.products_df.empty:
            sorted_df = self.products_df.sort_values(by=["Product Category", "Product Name"])
            return sorted_df.apply(lambda x: f"{x['Product Name']} ({x['Price']:.2f})", axis=1).tolist()
        return []

    def get_product_details(self, selection_string):
        if not selection_string: return "", None, 0, "Uncategorized"
        exact_row = self.products_df[self.products_df['Product Name'] == selection_string]
        if not exact_row.empty:
            row = exact_row.iloc[0]
            return "", row['Product Name'], float(row['Price']), row['Product Category']
        try:
            name_part = selection_string.rsplit(" (", 1)[0]
        except:
            name_part = selection_string
        item_row = self.products_df[self.products_df['Product Name'] == name_part]
        if not item_row.empty:
            row = item_row.iloc[0]
            return "", row['Product Name'], float(row['Price']), row['Product Category']
        return "", "Unknown Item", 0.0, "Phased Out"

    def refresh_stock_cache(self):
        self.current_stock_cache, _, _, _ = self.calculate_stats(None)

    def on_tab_change(self, event):
        self.refresh_stock_cache()
        if hasattr(self, 'pos_qty_var'): self.pos_qty_var.set(1)
        if hasattr(self, 'lbl_stock_avail'): self.lbl_stock_avail.config(text="")
        if hasattr(self, 'pos_dropdown'): self.pos_dropdown.set('')
        current_tab = self.notebook.tab(self.notebook.select(), "text")
        if current_tab == 'CORRECTION': self.refresh_correction_list()

    def validate_email_format(self, email):
        regex = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(regex, email) is not None

    def send_email_thread(self, recipient, subject, body, attachment_paths=None, is_test=False):
        def task():
            try:
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
                if is_test:
                    self.root.after(0, lambda: messagebox.showinfo("Email Success", f"Test email sent to {recipient}"))
                else:
                    print(f"Email sent successfully to {recipient}")
            except Exception as e:
                err_msg = str(e)
                if is_test:
                    self.root.after(0, lambda: messagebox.showerror("Email Error", f"Failed to send: {err_msg}"))
                else:
                    print(f"Failed to send email: {err_msg}")

        threading.Thread(target=task, daemon=True).start()

    def trigger_email_send(self, summary_pdf_path, extra_body=""):
        recipient = self.config.get("recipient_email", "").strip()
        if not recipient or not self.validate_email_format(recipient): return
        date_str = datetime.datetime.now().strftime("%Y%m%d")
        safe_biz_name = "".join(c for c in self.business_name if c.isalnum() or c in (' ', '_', '-')).strip()
        subject = f"[{self.summary_count:04d}]_{APP_TITLE}_{safe_biz_name}_{date_str}"
        body = f"Summary & Ledger.\n\nUser: {self.session_user}\nCounter: {self.summary_count:04d}\nTime: {datetime.datetime.now()}\n\n{extra_body}"
        attachments = [summary_pdf_path, LEDGER_FILE]
        self.send_email_thread(recipient, subject, body, attachments, is_test=False)

    def calculate_stats(self, period_filter=None):
        stats = {}
        in_count = 0
        out_count = 0
        corrections_in_period = []
        for transaction in self.ledger:
            try:
                ts_str = transaction.get('timestamp')
                try:
                    dt = datetime.datetime.strptime(ts_str, "%Y-%m-%d %H:%M:%S")
                except:
                    dt = datetime.datetime.now()
                if period_filter:
                    s, e = period_filter
                    if not (s <= dt <= e): continue
                    if transaction.get('type') == 'correction':
                        corrections_in_period.append(transaction.get('filename', 'Unknown'))
                t_type = transaction.get('type')
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

    def generate_grouped_pdf(self, filepath, title, date_str, items, col_headers, col_pos, is_summary=False,
                             extra_info="", subtotal_indices=None, is_inventory=False, correction_list=None):
        try:
            c = canvas.Canvas(filepath, pagesize=letter)
            width, height = letter
            y = height - 1 * inch
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
            c.setFont("Helvetica-Bold", 9)
            for i, h in enumerate(col_headers): c.drawString(col_pos[i] * inch, y, h)
            c.line(1 * inch, y - 5, 7.5 * inch, y - 5)
            y -= 20

            def sort_key(x):
                cat = x.get('category', 'Uncategorized')
                if cat == "Phased Out": cat = "zzz_Phased Out"
                return (cat, x['name'])

            sorted_items = sorted(items, key=sort_key)
            current_cat = None
            cat_sums = [0] * len(col_headers)
            grand_sums = [0] * len(col_headers)

            for item in sorted_items:
                if y < 1 * inch:
                    c.showPage();
                    y = height - 1 * inch
                cat = item.get('category', 'Uncategorized')
                if cat != current_cat:
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
                    cat_sums = [0] * len(col_headers)
                c.setFont("Helvetica", 9)
                row_vals = []
                row_txt = []
                if is_summary:
                    price_txt = f"{item['price']:.2f}" if item['price'] > 0 else "-"
                    row_txt = [item['name'][:35], price_txt, str(int(item['in'])),
                               str(int(item['out'])), str(int(item['remaining'])), f"{item['sales']:.2f}"]
                    row_vals = [0, 0, item['in'], item['out'], item['remaining'], item['sales']]
                elif "subtotal" in item:
                    row_txt = [item['name'][:35], f"{item['price']:.2f}", str(int(item['qty'])),
                               f"{item['subtotal']:.2f}"]
                    row_vals = [0, 0, item['qty'], item['subtotal']]
                elif "new_stock" in item:
                    row_txt = [item['name'][:35], f"{item.get('price', 0):.2f}", f"{int(item['qty'])}",
                               str(int(item.get('new_stock', 0)))]
                    row_vals = [0, 0, item['qty'], 0]
                elif "qty_final" in item:
                    row_txt = [item['name'][:35], str(int(item['qty_orig'])), f"{int(item['qty']):+}",
                               str(int(item['qty_final']))]
                    row_vals = [0, 0, item['qty'], 0]
                else:
                    row_txt = [item['name'][:35], f"{item.get('price', 0):.2f}", f"{int(item['qty'])}"]
                    row_vals = [0, 0, item['qty']]
                for i, txt in enumerate(row_txt): c.drawString(col_pos[i] * inch, y, txt)
                for i, val in enumerate(row_vals):
                    cat_sums[i] += val
                    grand_sums[i] += val
                y -= 15
            if current_cat is not None and not is_inventory and not "qty_final" in items[0] if items else False:
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
            if is_summary and correction_list:
                y -= 40
                if y < 1 * inch: c.showPage(); y = height - 1 * inch
                c.setFont("Helvetica-Bold", 10)
                c.drawString(1 * inch, y, "Corrections included in this period:")
                y -= 15
                c.setFont("Helvetica", 9)
                for cf in correction_list:
                    if y < 0.5 * inch: c.showPage(); y = height - 1 * inch
                    c.drawString(1.2 * inch, y, f"- {cf}")
                    y -= 12
            c.save()
            return True
        except Exception as e:
            messagebox.showerror("Error", str(e))
            return False

    def setup_inventory_tab(self):
        # Apply Inventory Style (Orange)
        self.tab_inventory.config(style="Inventory.TFrame")

        # LWS Sidebar (Setup first to ensure correct packing order when shown)
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
        code, name, price, cat = self.get_product_details(sel)
        found = False
        for i in self.inventory_cart:
            if i['name'] == name and i['price'] == price:
                i['qty'] += qty
                found = True;
                break
        if not found: self.inventory_cart.append(
            {"code": "", "name": name, "price": price, "qty": qty, "category": cat})
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
        self.inventory_cart = [];
        self.refresh_inv()

    def commit_inv(self):
        if not self.inventory_cart: return
        now = self.get_time()
        date_str = now.strftime('%Y-%m-%d %H:%M:%S')
        fname = f"Inventory_{now.strftime('%Y%m%d-%H%M%S')}.pdf"
        stats, _, _, _ = self.calculate_stats(None)
        p_items = []
        for i in self.inventory_cart:
            hist = stats.get(i['name'], {'in': 0, 'out': 0})
            new_stock = (hist['in'] + i['qty']) - hist['out']
            x = i.copy();
            x['new_stock'] = new_stock;
            p_items.append(x)
        if self.generate_grouped_pdf(os.path.join(INVENTORY_FOLDER, fname), "INVENTORY RECEIPT",
                                     date_str, p_items, ["Item", "Price", "Qty Added", "New Stock"],
                                     [1.0, 4.5, 5.5, 6.5], subtotal_indices=[2], is_inventory=True):
            transaction = {"type": "inventory", "timestamp": date_str, "filename": fname, "items": self.inventory_cart}
            self.ledger.append(transaction);
            self.save_ledger()
            self.clear_inv();
            self.refresh_stock_cache()
            messagebox.showinfo("Success", f"Stock Added. Receipt: {fname}")

    def setup_pos_tab(self):
        # Sales Tab uses default Green Theme but we ensure it matches
        self.tab_pos.config(style="Sales.TFrame")

        # LWS Sidebar (Setup first to ensure correct packing order when shown)
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

        self.pos_tree.heading("cat", text="Cat");
        self.pos_tree.heading("name", text="Product")
        self.pos_tree.heading("price", text="Price");
        self.pos_tree.heading("qty", text="Qty");
        self.pos_tree.heading("sub", text="Sub")
        self.pos_tree.column("cat", width=80);
        self.pos_tree.column("price", width=60)
        self.pos_tree.column("qty", width=40);
        self.pos_tree.column("sub", width=70)
        self.pos_tree.pack(fill="both", expand=True)

        b = ttk.Frame(main_content)
        b.pack(fill="x", padx=5, pady=10)

        self.lbl_pos_total = ttk.Label(b, text="Total: 0.00", font=("Segoe UI", 14, "bold"), foreground="#d32f2f")
        self.lbl_pos_total.pack(side="left", padx=5)

        ttk.Button(b, text="CHECKOUT", command=self.checkout, style="Accent.TButton").pack(side="right", ipadx=20)
        ttk.Button(b, text="Clear", command=self.clear_pos).pack(side="right", padx=5)
        ttk.Button(b, text="Del", command=self.del_pos_line).pack(side="right", padx=5)

    def setup_lws_sidebar(self, parent_frame, mode):
        # Create a frame for the sidebar
        sidebar_frame = ttk.Frame(parent_frame, width=250)
        # Pack first to establish order, then hide
        sidebar_frame.pack(side="right", fill="y", padx=5, pady=5)
        sidebar_frame.pack_forget()
        sidebar_frame.pack_propagate(False) # Fixed width

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

        # Add to Cart Button (Replaces Check)
        ttk.Button(btn_frame, text="Add to Cart", width=12,
                   command=lambda: self.action_remote_request(mode, "add_to_cart")).pack(side="left", padx=5)

        # Reject Button (Cross)
        ttk.Button(btn_frame, text="✖", width=4,
                   command=lambda: self.action_remote_request(mode, "reject")).pack(side="left", padx=5)

    def show_remote_sidebars(self):
        for mode, frame in self.lws_sidebars.items():
            # Packing again with correct options should restore it in correct slot
            # because we packed it first in setup logic.
            frame.pack(side="right", fill="y", padx=5, pady=5)

    def hide_remote_sidebars(self):
        for mode, frame in self.lws_sidebars.items():
            frame.pack_forget()

    def action_remote_request(self, mode, action):
        tree = self.inv_req_tree if mode == 'inventory' else self.pos_req_tree
        sel = tree.selection()
        if not sel: return

        req_id = tree.item(sel[0], 'tags')[0]

        # Find request in list
        req = next((r for r in self.remote_requests if r['id'] == req_id), None)
        if not req: return

        if action == "reject":
            if messagebox.askyesno("Reject", "Reject this request?"):
                self.remote_requests.remove(req)
                self.refresh_remote_sidebars()
        elif action == "add_to_cart":
            self.load_remote_request_to_cart(req)

    def on_pos_sel(self, e):
        sel = self.pos_prod_var.get()
        if not sel: self.lbl_stock_avail.config(text=""); return
        code, name, price, cat = self.get_product_details(sel)
        stats = self.current_stock_cache.get(name, {'in': 0, 'out': 0})
        real_inv = stats['in'] - stats['out']
        in_cart = sum(i['qty'] for i in self.sales_cart if i['name'] == name)
        self.lbl_stock_avail.config(text=f"Stk: {int(real_inv - in_cart)}")

    def add_pos(self):
        sel, qty = self.pos_prod_var.get(), self.pos_qty_var.get()
        if not sel or qty <= 0: return
        code, name, price, cat = self.get_product_details(sel)
        stats = self.current_stock_cache.get(name, {'in': 0, 'out': 0})
        real = stats['in'] - stats['out']
        cart_q = sum(i['qty'] for i in self.sales_cart if i['name'] == name)
        if (cart_q + qty) > real: messagebox.showerror("Stock", f"Low Stock!\nAvail: {int(real)}"); return
        sub = price * qty
        found = False
        for i in self.sales_cart:
            if i['name'] == name: i['qty'] += qty; i['subtotal'] += sub; found = True; break
        if not found: self.sales_cart.append(
            {"code": "", "name": name, "price": price, "qty": qty, "subtotal": sub, "category": cat})
        self.refresh_pos();
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
        self.refresh_pos();
        self.on_pos_sel(None)

    def clear_pos(self):
        self.sales_cart = [];
        self.refresh_pos();
        self.on_pos_sel(None)

    def checkout(self):
        if not self.sales_cart: return
        now = self.get_time()
        date_str = now.strftime('%Y-%m-%d %H:%M:%S')
        fname = f"{now.strftime('%Y%m%d-%H%M%S')}.pdf"
        if self.generate_grouped_pdf(os.path.join(RECEIPT_FOLDER, fname), "SALES RECEIPT", date_str, self.sales_cart,
                                     ["Item", "Price", "Qty", "Total"], [1.0, 4.5, 5.5, 6.5], subtotal_indices=[2, 3]):
            transaction = {"type": "sales", "timestamp": date_str, "filename": fname, "items": self.sales_cart}
            self.ledger.append(transaction);
            self.save_ledger()
            self.clear_pos();
            self.refresh_stock_cache()
            messagebox.showinfo("Success", f"Saved: {fname}")

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
        self.corr_list_tree.heading("time", text="Time");
        self.corr_list_tree.column("time", width=100)
        self.corr_list_tree.heading("file", text="Filename")
        self.corr_list_tree.pack(fill="both", expand=True, padx=5, pady=5)
        ttk.Button(frame_list, text="CHOOSE >>", command=self.load_receipt_for_correction).pack(fill="x", padx=5,
                                                                                                pady=5)
        frame_editor = ttk.LabelFrame(paned, text="Step 2: Correct Quantities")
        paned.add(frame_editor, weight=2)
        self.lbl_corr_target = ttk.Label(frame_editor, text="No receipt selected", foreground="blue",
                                         font=("Segoe UI", 10, "bold"))
        self.lbl_corr_target.pack(padx=5, pady=5)
        self.corr_edit_tree = ttk.Treeview(frame_editor, columns=("name", "qty_orig", "qty_adj"), show="headings")
        self.corr_edit_tree.heading("name", text="Product");
        self.corr_edit_tree.heading("qty_orig", text="Orig Qty");
        self.corr_edit_tree.column("qty_orig", width=60);
        self.corr_edit_tree.heading("qty_adj", text="Adjustment (+/-)");
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
        for trans in self.ledger:
            if trans.get('type') == target_type:
                ts = trans.get('timestamp', '')
                if ts.startswith(now_str):
                    time_part = ts.split(' ')[1] if ' ' in ts else ts
                    self.corr_list_tree.insert("", "end", values=(time_part, trans.get('filename')),
                                               tags=(json.dumps(trans),))

    def load_receipt_for_correction(self):
        sel = self.corr_list_tree.selection()
        if not sel: return
        item = self.corr_list_tree.item(sel[0])
        trans_str = self.corr_list_tree.item(sel[0], 'tags')[0]
        self.selected_transaction = json.loads(trans_str)
        self.lbl_corr_target.config(text=f"Editing: {self.selected_transaction['filename']}")
        for i in self.corr_edit_tree.get_children(): self.corr_edit_tree.delete(i)
        self.correction_cart = []
        for item in self.selected_transaction.get('items', []):
            c_item = item.copy();
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
        ref_file = self.selected_transaction['filename']
        existing_corr_index = -1
        for idx, trans in enumerate(self.ledger):
            if trans.get('type') == 'correction' and trans.get('ref_filename') == ref_file:
                existing_corr_index = idx;
                break
        if existing_corr_index != -1:
            old_corr = self.ledger.pop(existing_corr_index)
            old_pdf = os.path.join(CORRECTION_FOLDER, old_corr['filename'])
            if os.path.exists(old_pdf):
                try:
                    os.remove(old_pdf)
                except:
                    pass
        now = self.get_time()
        date_str = now.strftime('%Y-%m-%d %H:%M:%S')
        fname = f"Cor_{now.strftime('%Y%m%d-%H%M%S')}.pdf"
        pdf_items = []
        ledger_adjustment_items = []
        for item in self.correction_cart:
            orig = item['qty'];
            adj = item['adjustment'];
            final = orig + adj
            pdf_item = {"code": "", "name": item['name'], "price": item['price'], "qty": adj, "qty_orig": orig,
                        "qty_final": final, "category": item.get('category', 'Uncategorized')}
            pdf_items.append(pdf_item)
            if adj != 0:
                ledger_item = item.copy();
                ledger_item['qty'] = adj
                ledger_adjustment_items.append(ledger_item)
        if self.generate_grouped_pdf(os.path.join(CORRECTION_FOLDER, fname), "CORRECTION RECEIPT",
                                     date_str, pdf_items, ["Item", "Orig", "Adj", "Final"],
                                     [1.0, 4.5, 5.5, 6.5], is_summary=False, extra_info=f"Ref: {ref_file}"):
            transaction = {"type": "correction", "ref_type": self.selected_transaction['type'],
                           "ref_filename": ref_file, "timestamp": date_str, "filename": fname,
                           "items": ledger_adjustment_items}
            self.ledger.append(transaction);
            self.save_ledger()
            for i in self.corr_edit_tree.get_children(): self.corr_edit_tree.delete(i)
            self.lbl_corr_target.config(text="No receipt selected")
            self.selected_transaction = None;
            self.refresh_stock_cache()
            messagebox.showinfo("Success", f"Correction Saved: {fname}")

    def setup_summary_tab(self):
        f = ttk.Frame(self.tab_summary)
        f.pack(fill="x", padx=5, pady=5)

        ttk.Label(f, text="Period:").pack(side="left")
        self.report_type = tk.StringVar(value="All Time")
        ttk.OptionMenu(f, self.report_type, "All Time", "Daily", "Weekly", "Monthly", "All Time").pack(side="left",
                                                                                                       padx=5)

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
        scrollbar = ttk.Scrollbar(tree_frame);
        scrollbar.pack(side="right", fill="y")
        self.sum_tree = ttk.Treeview(tree_frame, columns=("cat", "name", "price", "in", "out", "rem", "sale"),
                                     show="headings", yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.sum_tree.yview)
        self.sum_tree.heading("cat", text="Cat");
        self.sum_tree.heading("name", text="Product")
        self.sum_tree.heading("price", text="Price");
        self.sum_tree.heading("in", text="In");
        self.sum_tree.heading("out", text="Out");
        self.sum_tree.heading("rem", text="Stk");
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
                y = int(self.cmb_year.get());
                m = int(self.cmb_month.get());
                d = int(self.cmb_day.get())
                anchor = datetime.datetime(y, m, d, 23, 59, 59)
            except ValueError:
                messagebox.showerror("Date Error", "Invalid Custom Date selected.");
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
        global_stats, _, _, _ = self.calculate_stats(None)
        period = override_period if override_period else self.get_period_dates()
        period_stats, in_c, out_c, corr_list = self.calculate_stats(period)
        rows = []
        all_names = set(self.products_df['Product Name'].astype(str)) | set(global_stats.keys())
        for name in all_names:
            name = name.strip()
            g_data = global_stats.get(name, {'in': 0, 'out': 0})
            rem_stock = g_data['in'] - g_data['out']
            _, _, curr_price, cat = self.get_product_details(f"{name}")
            p_data = period_stats.get(name, {'in': 0, 'out': 0, 'sales_lines': [], 'in_lines': []})
            price_map = {}
            for line in p_data['sales_lines']:
                p = line['price']
                if p not in price_map: price_map[p] = {'in': 0, 'out': 0, 'sales': 0}
                price_map[p]['out'] += line['qty'];
                price_map[p]['sales'] += line['amt']
            for line in p_data['in_lines']:
                p = line['price']
                if p not in price_map: price_map[p] = {'in': 0, 'out': 0, 'sales': 0}
                price_map[p]['in'] += line['qty']
            if not price_map: price_map[curr_price] = {'in': 0, 'out': 0, 'sales': 0}
            for price, data in price_map.items():
                show_rem = rem_stock if price == curr_price else 0
                if self.report_type.get() != "All Time":
                    if data['in'] == 0 and data['out'] == 0: continue
                elif data['in'] == 0 and data['out'] == 0 and show_rem == 0 and name not in set(
                        self.products_df['Product Name']):
                    continue
                if cat == "Phased Out" and name in global_stats: name = global_stats[name]['name'] + " (Old)"
                rows.append(
                    {'code': "", 'category': cat, 'name': name, 'price': price, 'in': data['in'], 'out': data['out'],
                     'remaining': show_rem, 'sales': data['sales']})
        final_rows = []
        names_in_excel = set(self.products_df['Product Name'].astype(str))
        for r in rows:
            is_active = (r['in'] > 0 or r['out'] > 0 or r['remaining'] > 0 or r['name'] in names_in_excel)
            if is_active: final_rows.append(r)
        return final_rows, in_c, out_c, corr_list

    def gen_view(self, override_period=None):
        data, in_c, out_c, corr_list = self.get_sum_data(override_period)
        for i in self.sum_tree.get_children(): self.sum_tree.delete(i)

        def sort_key(x):
            cat = x['category'];
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
        now = self.get_time()

        prefix = "History" if is_custom_date else "Summary"
        fname = f"{prefix}-{now.strftime('%Y%m%d-%H%M%S')}.pdf"
        full_path = os.path.join(SUMMARY_FOLDER, fname)

        success = self.generate_grouped_pdf(full_path, "INVENTORY & SALES SUMMARY",
                                            now.strftime('%Y-%m-%d %H:%M:%S'), data,
                                            ["Product", "Price", "Added", "Sold", "Stock", "Sales"],
                                            [1.0, 4.5, 5.2, 5.9, 6.6, 7.3], is_summary=True,
                                            extra_info=f"Period: {p_txt} | In: {in_c} | Out: {out_c}",
                                            subtotal_indices=[2, 3, 5], correction_list=corr_list)
        if success:
            if not is_custom_date:
                self.summary_count += 1
                self.save_ledger()
                self.trigger_email_send(full_path)
                messagebox.showinfo("Success", f"Summary Generated & Sent.\nReceipt: {fname}")
            else:
                messagebox.showinfo("History Generated", f"Historical PDF Generated (No Email/Counter).\nFile: {fname}")

    def setup_settings_tab(self):
        # Create nested notebook
        self.settings_notebook = ttk.Notebook(self.tab_settings)
        self.settings_notebook.pack(fill="both", expand=True, padx=5, pady=5)

        self.tab_settings_general = ttk.Frame(self.settings_notebook)
        self.tab_settings_web = ttk.Frame(self.settings_notebook)

        self.settings_notebook.add(self.tab_settings_general, text="General")
        self.settings_notebook.add(self.tab_settings_web, text="Web Server")

        # --- General Settings ---
        f = ttk.LabelFrame(self.tab_settings_general, text="Settings")
        f.pack(fill="both", expand=True, padx=10, pady=10)

        self.chk_startup_var = tk.BooleanVar(value=self.config.get("startup", False))
        ttk.Checkbutton(f, text="Launch at Startup", variable=self.chk_startup_var, command=self.toggle_startup).pack(
            pady=5, anchor="w")

        # Touch Mode Toggle
        self.chk_touch_var = tk.BooleanVar(value=self.touch_mode)
        ttk.Checkbutton(f, text="Enable Touch Mode (Larger UI)", variable=self.chk_touch_var, command=self.toggle_touch_mode).pack(
            pady=5, anchor="w")

        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Label(f, text="Email Receipt Sync", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        email_frame = ttk.Frame(f)
        email_frame.pack(anchor="w", pady=5, fill="x")
        ttk.Label(email_frame, text="Recipient Email:").pack(side="left")
        self.entry_email = ttk.Entry(email_frame, width=35)
        self.entry_email.insert(0, self.config.get("recipient_email", ""))
        self.entry_email.pack(side="left", padx=5)
        ttk.Button(email_frame, text="Confirm & Test", command=self.verify_and_test_email).pack(side="left", padx=5)
        ttk.Label(f, text="(Valid email required for sync to function)", font=("Segoe UI", 8), foreground="gray").pack(
            anchor="w", pady=0)
        ttk.Separator(f, orient='horizontal').pack(fill='x', pady=10)
        ttk.Label(f, text="Visuals", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        ttk.Label(f, text="Splash Image:").pack(pady=(5, 0), anchor="w")
        self.entry_img = ttk.Entry(f, width=40)
        self.entry_img.insert(0, self.config.get("splash_img", ""))
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
        ttk.Button(f, text="Load Test (Dev)", command=self.run_load_test, style="Danger.TButton").pack(anchor="w",
                                                                                                       pady=5)

        # --- Web Server Settings ---
        self.setup_web_server_panel(self.tab_settings_web)

    def verify_and_test_email(self):
        email_input = self.entry_email.get().strip()
        if not email_input:
            self.config["recipient_email"] = "";
            self.save_config()
            messagebox.showinfo("Email Disabled", "Email field cleared. Sync disabled.");
            return
        if not self.validate_email_format(email_input):
            messagebox.showerror("Invalid Email",
                                 "The email address entered is not valid.\nSync features will not run.")
            self.config["recipient_email"] = "";
            self.save_config();
            return
        if not messagebox.askyesno("Confirm Email", f"Is this correct?\n\n{email_input}"): return
        self.config["recipient_email"] = email_input;
        self.save_config()
        current_time = time.time()
        if (current_time - self.last_email_time) < 60:
            messagebox.showinfo("Valid", "Email saved.\n(Test email skipped: Please wait 1 minute between tests)");
            return
        self.last_email_time = current_time
        subject = f"Receipt Sync Confirmation - {APP_TITLE}"
        body = f"This email has been entered as recipient for {APP_TITLE} receipts by {self.session_user}."
        self.send_email_thread(email_input, subject, body, attachment_paths=[], is_test=True)

    def browse_splash(self):
        path = filedialog.askopenfilename(filetypes=[("Image Files", "*.jpg *.png")])
        if path: self.entry_img.delete(0, tk.END); self.entry_img.insert(0, path)

    def save_display_settings(self):
        self.config["splash_img"] = self.entry_img.get()
        self.save_config();
        messagebox.showinfo("Success", "Saved.")

    def toggle_touch_mode(self):
        enabled = self.chk_touch_var.get()
        self.touch_mode = enabled
        self.config["touch_mode"] = enabled
        self.save_config()
        self.style_manager.set_touch_mode(enabled)

    def toggle_startup(self):
        startup_folder = os.path.join(os.getenv("APPDATA"), r"Microsoft\Windows\Start Menu\Programs\Startup")
        bat_path = os.path.join(startup_folder, "POS_System_Auto.bat")
        if self.chk_startup_var.get():
            try:
                exe_path = sys.executable if getattr(sys, 'frozen', False) else os.path.abspath(__file__)
                with open(bat_path, "w") as bat:
                    bat.write(f'start "" "{exe_path}"' if getattr(sys, 'frozen', False) else f'python "{exe_path}"')
                self.config["startup"] = True;
                self.save_config();
                messagebox.showinfo("Startup", "Enabled.")
            except Exception as e:
                self.chk_startup_var.set(False);
                messagebox.showerror("Error", str(e))
        else:
            if os.path.exists(bat_path): os.remove(bat_path)
            self.config["startup"] = False;
            self.save_config();
            messagebox.showinfo("Startup", "Disabled.")

    def backup_data_json(self):
        if not self.ledger: messagebox.showinfo("Backup", "No data to backup."); return
        save_path = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON Database", "*.json")])
        if save_path:
            try:
                products_data = self.products_df.to_dict('records') if not self.products_df.empty else []
                data = {"transactions": self.ledger, "summary_count": self.summary_count,
                        "products_master": products_data, "shortcuts_asked": self.shortcuts_asked}
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
            new_ledger = [];
            new_count = 0
            new_shortcuts_asked = False
            if isinstance(backup_data, list):
                new_ledger = backup_data;
                new_count = 0
            elif isinstance(backup_data, dict):
                new_ledger = backup_data.get("transactions", [])
                new_count = backup_data.get("summary_count", 0)
                new_shortcuts_asked = backup_data.get("shortcuts_asked", False)

            restored_prod_msg = ""
            products_master = backup_data.get("products_master", []) if isinstance(backup_data, dict) else []
            if products_master:
                try:
                    new_df = pd.DataFrame(products_master)
                    new_df.to_excel(DATA_FILE, index=False)
                    self.load_products()
                    self.inv_dropdown['values'] = self.get_dropdown_values()
                    self.pos_dropdown['values'] = self.get_dropdown_values()
                    restored_prod_msg = "Products.xlsx regenerated."
                except Exception as e:
                    restored_prod_msg = f"Failed to regen products: {e}"
            else:
                restored_prod_msg = "Products.xlsx NOT updated (old backup format)."

            for folder in [INVENTORY_FOLDER, RECEIPT_FOLDER, CORRECTION_FOLDER]:
                if os.path.exists(folder): shutil.rmtree(folder); os.makedirs(folder)
            count = 0
            self.ledger = new_ledger
            self.summary_count = new_count
            self.shortcuts_asked = new_shortcuts_asked
            self.save_ledger()
            for entry in self.ledger:
                fname = entry.get('filename');
                date_str = entry.get('timestamp');
                items = entry.get('items', [])
                if entry['type'] == "inventory":
                    self.generate_grouped_pdf(os.path.join(INVENTORY_FOLDER, fname), "INVENTORY RECEIPT", date_str,
                                              items, ["Item", "Price", "Qty Added", "New Stock"], [1.0, 4.5, 5.5, 6.5],
                                              subtotal_indices=[2], is_inventory=True)
                elif entry['type'] == "sales":
                    self.generate_grouped_pdf(os.path.join(RECEIPT_FOLDER, fname), "SALES RECEIPT", date_str, items,
                                              ["Item", "Price", "Qty", "Total"], [1.0, 4.5, 5.5, 6.5],
                                              subtotal_indices=[2, 3])
                elif entry['type'] == "correction":
                    pdf_items = []
                    for it in items:
                        pdf_items.append(
                            {"code": "", "name": it['name'], "price": it['price'], "qty_orig": 0, "qty": it['qty'],
                             "qty_final": it['qty'], "category": it.get('category')})
                    self.generate_grouped_pdf(os.path.join(CORRECTION_FOLDER, fname), "CORRECTION RECEIPT", date_str,
                                              pdf_items, ["Item", "Orig", "Adj", "Final"], [1.0, 4.5, 5.5, 6.5])
                count += 1
            self.refresh_stock_cache()
            messagebox.showinfo("Success",
                                f"Restored {count} records.\nSummary Counter: {self.summary_count}\n{restored_prod_msg}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed: {e}")

    def run_load_test(self):
        pwd = simpledialog.askstring("Load Test", "Enter Password:", show="*")
        if pwd != "migs": messagebox.showerror("Error", "Incorrect Password"); return
        if not messagebox.askyesno("WARNING",
                                   "This will DELETE ALL DATA and generate dummy data for the last 30 days.\n\nAre you sure?"): return
        self.ledger = [];
        self.summary_count = 0
        for folder in [INVENTORY_FOLDER, RECEIPT_FOLDER, CORRECTION_FOLDER]:
            if os.path.exists(folder): shutil.rmtree(folder); os.makedirs(folder)
        if self.products_df.empty: messagebox.showerror("Error", "No products loaded from products.xlsx"); return
        products = []
        for _, row in self.products_df.iterrows():
            products.append(
                {"name": row['Product Name'], "price": float(row['Price']), "category": row['Product Category']})
        stock_tracker = {p['name']: 0 for p in products}
        start_date = datetime.datetime.now() - datetime.timedelta(days=30)
        try:
            for day_offset in range(31):
                curr_date = start_date + datetime.timedelta(days=day_offset)
                date_str_base = curr_date.strftime("%Y-%m-%d")
                if day_offset % 7 == 0 or day_offset == 30:
                    inv_items = []
                    for p in products:
                        current_qty = stock_tracker[p['name']]
                        weekly_demand_est = 21;
                        safety_stock = random.randint(10, 20);
                        target_level = weekly_demand_est + safety_stock
                        needed = target_level - current_qty
                        if needed > 0:
                            stock_tracker[p['name']] += needed
                            inv_items.append({"code": "", "name": p['name'], "price": p['price'], "qty": needed,
                                              "category": p['category'], "new_stock": stock_tracker[p['name']]})
                    if inv_items:
                        ts = f"{date_str_base} 08:00:00"
                        fname = f"Inventory_{curr_date.strftime('%Y%m%d')}-080000.pdf"
                        self.generate_grouped_pdf(os.path.join(INVENTORY_FOLDER, fname), "INVENTORY RECEIPT", ts,
                                                  inv_items, ["Item", "Price", "Qty Added", "New Stock"],
                                                  [1.0, 4.5, 5.5, 6.5], subtotal_indices=[2], is_inventory=True)
                        self.ledger.append(
                            {"type": "inventory", "timestamp": ts, "filename": fname, "items": inv_items})
                num_sales = random.randint(5, 10)
                for s_i in range(num_sales):
                    sales_items = []
                    num_lines = random.randint(1, 5)
                    attempts = 0
                    while len(sales_items) < num_lines and attempts < 20:
                        attempts += 1;
                        p = random.choice(products)
                        if any(x['name'] == p['name'] for x in sales_items): continue
                        qty = random.randint(1, 3)
                        if stock_tracker[p['name']] >= qty:
                            stock_tracker[p['name']] -= qty;
                            sub = p['price'] * qty
                            sales_items.append(
                                {"code": "", "name": p['name'], "price": p['price'], "qty": qty, "subtotal": sub,
                                 "category": p['category']})
                    if sales_items:
                        hour = 9 + (s_i % 9);
                        minute = random.randint(0, 59)
                        ts = f"{date_str_base} {hour:02d}:{minute:02d}:{random.randint(10, 59)}"
                        fname = f"{curr_date.strftime('%Y%m%d')}-{hour:02d}{minute:02d}{random.randint(10, 59)}.pdf"
                        self.generate_grouped_pdf(os.path.join(RECEIPT_FOLDER, fname), "SALES RECEIPT", ts, sales_items,
                                                  ["Item", "Price", "Qty", "Total"], [1.0, 4.5, 5.5, 6.5],
                                                  subtotal_indices=[2, 3])
                        self.ledger.append({"type": "sales", "timestamp": ts, "filename": fname, "items": sales_items})
            self.save_ledger();
            self.refresh_stock_cache()
            messagebox.showinfo("Load Test", "Simulation Complete.\nData overwritten.")
        except Exception as e:
            messagebox.showerror("Load Test Error", f"Simulation failed: {e}")


def launch_app():
    # --- Close PyInstaller Splash (if active) ---
    try:
        import pyi_splash
        pyi_splash.update_text("Starting Application...")
        pyi_splash.close()
    except ImportError:
        pass

    root = tk.Tk()
    root.withdraw()
    cfg = {"splash_img": "", "cached_business_name": "MMD POS System"}
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r') as f:
                loaded_cfg = json.load(f);
                cfg.update(loaded_cfg)
        except:
            pass
    splash = SplashScreen(root, cfg.get("splash_img", ""), cfg.get("cached_business_name", ""), APP_TITLE)

    def loader():
        global pd, canvas, letter, inch, PdfReader, ntplib
        global Flask, request, jsonify, render_template_string, qrcode
        global smtplib, ssl, MIMEText, MIMEMultipart, MIMEBase, encoders

        try:
            splash.update_status("Loading Data Engine (pandas)...")
            import pandas as pd
            splash.update_status("Loading PDF Engine (reportlab)...")
            from reportlab.pdfgen import canvas;
            from reportlab.lib.pagesizes import letter;
            from reportlab.lib.units import inch
            splash.update_status("Loading Utils...")
            from pypdf import PdfReader;
            import ntplib

            splash.update_status("Loading Web Server...")
            from flask import Flask, request, jsonify, render_template_string
            import qrcode

            splash.update_status("Loading Email Modules...")
            import smtplib
            import ssl
            from email.mime.text import MIMEText
            from email.mime.multipart import MIMEMultipart
            from email.mime.base import MIMEBase
            from email import encoders

        except Exception as e:
            messagebox.showerror("Critical Error", f"Missing Libraries: {e}");
            root.destroy();
            return
        splash.update_status("Starting Interface...")

        def login_logic():
            splash.destroy();
            user = simpledialog.askstring("Login", "User:", parent=root)
            if user:
                root.deiconify();
                POSSystem(root, user, splash=None)
            else:
                root.destroy()

        root.after(500, login_logic)

    root.after(100, loader)
    root.mainloop()


if __name__ == "__main__":
    launch_app()