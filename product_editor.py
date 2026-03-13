import tkinter as tk
from tkinter import ttk, messagebox
import os
import datetime

class ProductEditor:
    def __init__(self, app):
        """
        :param app: The POSSystem instance from main.py
        """
        self.app = app
        self.root = app.root
        self.data_manager = app.data_manager
        self.report_manager = app.report_manager
        self.email_manager = app.email_manager
        self.all_data = []

    def show_editor_window(self):
        self.win = tk.Toplevel(self.root)
        self.win.title("Product Editor - History & Renaming Tool")
        self.win.geometry("1100x650")
        self.win.grab_set()

        # Customizing window icon if available
        try:
            if os.path.exists("icon.ico"):
                self.win.iconbitmap("icon.ico")
        except:
            pass

        # Main Container
        main_frame = ttk.Frame(self.win, padding=10)
        main_frame.pack(fill="both", expand=True)

        # Ribbon/Header
        header = ttk.Frame(main_frame)
        header.pack(fill="x", pady=(0, 10))
        ttk.Label(header, text="Product Renaming & Category Management", font=("Segoe UI", 12, "bold")).pack(side="left")
        ttk.Label(header, text=" (Updates all historical records automatically)", font=("Segoe UI", 10, "italic"), foreground="gray").pack(side="left")

        # Search Bar
        search_frame = ttk.LabelFrame(main_frame, text="Search Products", padding=5)
        search_frame.pack(fill="x", pady=5)
        
        self.search_var = tk.StringVar()
        self.search_var.trace("w", lambda *args: self.refresh_tree())
        search_entry = ttk.Entry(search_frame, textvariable=self.search_var, font=("Segoe UI", 11), width=50)
        search_entry.pack(side="left", padx=10, pady=5)
        search_entry.focus_set()
        
        ttk.Label(search_frame, text="Tip: You can search by Name or Category", font=("Segoe UI", 8)).pack(side="right", padx=10)

        # Table Section
        table_frame = ttk.Frame(main_frame)
        table_frame.pack(fill="both", expand=True)

        cols = ("cat", "name", "price", "in", "out", "stock")
        self.tree = ttk.Treeview(table_frame, columns=cols, show="headings", selectmode="browse")
        
        self.tree.heading("cat", text="Category")
        self.tree.heading("name", text="Product Name")
        self.tree.heading("price", text="Price")
        self.tree.heading("in", text="Total IN (All-Time)")
        self.tree.heading("out", text="Total OUT (All-Time)")
        self.tree.heading("stock", text="Current Stock")

        self.tree.column("cat", width=180, anchor="w")
        self.tree.column("name", width=420, anchor="w")
        self.tree.column("price", width=90, anchor="e")
        self.tree.column("in", width=120, anchor="center")
        self.tree.column("out", width=120, anchor="center")
        self.tree.column("stock", width=120, anchor="center")

        sb = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        
        # Bind double click
        self.tree.bind("<Double-1>", lambda e: self.on_edit_click())

        # Footer Buttons
        footer = ttk.Frame(main_frame, padding=(0, 10))
        footer.pack(fill="x")

        ttk.Button(footer, text="MASTER EDIT SELECTED", style="Accent.TButton", command=self.on_edit_click).pack(side="right", padx=5, ipadx=15, ipady=3)
        ttk.Button(footer, text="CLOSE", command=self.win.destroy).pack(side="right", padx=5)

        # Load initial data
        self.load_data()

    def load_data(self):
        """Fetches product stats and populates local storage."""
        # We use the app's calculation logic to get all-time stats
        stats, _, _, _, _ = self.data_manager.calculate_stats(None)
        
        self.all_data = []
        if self.data_manager.products_df is not None:
            # Using current products.xlsx as master list
            products = self.data_manager.products_df.to_dict('records')
            for p in products:
                name = str(p.get('Product Name', ''))
                cat = str(p.get('Product Category', 'GENERAL'))
                price = float(p.get('Price', 0.0))
                
                # Get sums from ledger stats
                s = stats.get(name, {'in': 0, 'out': 0})
                in_q = s['in']
                out_q = s['out']
                stock = in_q - out_q
                
                self.all_data.append({
                    "cat": cat,
                    "name": name,
                    "price": price,
                    "in": int(in_q),
                    "out": int(out_q),
                    "stock": int(stock)
                })
        
        self.refresh_tree()

    def refresh_tree(self):
        """Filters tree based on search variable."""
        query = self.search_var.get().lower()
        for i in self.tree.get_children():
            self.tree.delete(i)
            
        for d in self.all_data:
            if query in d['name'].lower() or query in d['cat'].lower():
                self.tree.insert("", "end", values=(
                    d['cat'], d['name'], f"{d['price']:.2f}", 
                    d['in'], d['out'], d['stock']
                ))

    def on_edit_click(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showwarning("Selection", "Please select a product from the table first.")
            return
            
        vals = self.tree.item(sel[0])['values']
        data = {
            "cat": vals[0],
            "name": vals[1],
            "in": vals[3],
            "out": vals[4],
            "stock": vals[5]
        }
        self.show_edit_dialog(data)

    def show_edit_dialog(self, data):
        dialog = tk.Toplevel(self.win)
        dialog.title(f"Master Edit: {data['name']}")
        dialog.geometry("450x480")
        dialog.grab_set()
        dialog.resizable(False, False)

        f = ttk.Frame(dialog, padding=25)
        f.pack(fill="both", expand=True)

        ttk.Label(f, text="ORIGINAL DETAILS", font=("Segoe UI", 9, "bold"), foreground="gray").pack(anchor="w")
        
        info_f = ttk.Frame(f)
        info_f.pack(fill="x", pady=(5, 0))
        ttk.Label(info_f, text="Category:", font=("Segoe UI", 10, "bold"), width=12).grid(row=0, column=0, sticky="w")
        ttk.Label(info_f, text=data['cat'], font=("Segoe UI", 10)).grid(row=0, column=1, sticky="w")
        ttk.Label(info_f, text="Product:", font=("Segoe UI", 10, "bold"), width=12).grid(row=1, column=0, sticky="w")
        ttk.Label(info_f, text=data['name'], font=("Segoe UI", 10)).grid(row=1, column=1, sticky="w")
        
        ttk.Separator(f, orient="horizontal").pack(fill="x", pady=20)

        style_bold = ("Segoe UI", 10, "bold")
        
        ttk.Label(f, text="NEW CATEGORY:", font=style_bold).pack(anchor="w")
        new_cat_var = tk.StringVar(value=data['cat'])
        new_cat_entry = ttk.Entry(f, textvariable=new_cat_var, font=("Segoe UI", 11))
        new_cat_entry.pack(fill="x", pady=(5, 15))

        ttk.Label(f, text="NEW PRODUCT NAME:", font=style_bold).pack(anchor="w")
        new_name_var = tk.StringVar(value=data['name'])
        new_name_entry = ttk.Entry(f, textvariable=new_name_var, font=("Segoe UI", 11))
        new_name_entry.pack(fill="x", pady=(5, 15))
        new_name_entry.focus_set()

        def on_finalize():
            new_cat = new_cat_var.get().strip().upper()
            new_name = new_name_var.get().strip().upper()

            if not new_cat or not new_name:
                messagebox.showerror("Error", "Both Category and Name are required.")
                return

            if new_cat == data['cat'] and new_name == data['name']:
                messagebox.showinfo("No Change", "Current and new details are identical. No action taken.")
                dialog.destroy()
                return

            # Check for name collision in current cache
            if new_name != data['name']:
                if new_name in self.data_manager.name_lookup_cache:
                    messagebox.showerror("Duplicate Name", f"A product named '{new_name}' already exists in the master database.")
                    return

            msg = (f"This action will PERMANENTLY RENAME this product across ALL historical records.\n\n"
                   f"CHANGE DETAILS:\n"
                   f"Category: {data['cat']} -> {new_cat}\n"
                   f"Name:     {data['name']} -> {new_name}\n\n"
                   f"Records to update: EVERY transaction in ledger.json containing this product.\n"
                   f"Stock Carryover:   {data['stock']} units will remain linked to the renamed product.\n\n"
                   f"The application will automatically close upon completion.\n\n"
                   f"Do you want to proceed?")
            
            if messagebox.askyesno("Confirm Master Edit", msg, icon="warning"):
                self.perform_master_edit(data, new_name, new_cat)
                dialog.destroy()

        ttk.Button(f, text="FINALIZE EDIT & RESTART", style="Accent.TButton", command=on_finalize).pack(fill="x", pady=(10, 0), ipadx=10, ipady=8)
        ttk.Button(f, text="CANCEL", command=dialog.destroy).pack(fill="x", pady=10)

    def perform_master_edit(self, old_data, new_name, new_cat):
        """Core logic to update ledger, excel, generate audit trail, and close."""
        old_name = old_data['name']
        old_cat = old_data['cat']
        in_q = old_data['in']
        out_q = old_data['out']
        
        pd = self.data_manager.mod.pd # Use pandas from injected modules
        
        try:
            # 1. Update ledger.json (Memory Transactions)
            # We must touch every item inEvery transaction to ensure renaming works for past records
            with self.data_manager._ledger_lock:
                update_count = 0
                for trans in self.data_manager.ledger:
                    trans_modified = False
                    for item in trans.get('items', []):
                        if item.get('name') == old_name:
                            item['name'] = new_name
                            if 'category' in item:
                                item['category'] = new_cat
                            trans_modified = True
                            update_count += 1
                        
                        # Handle base_product (promos)
                        if item.get('base_product') == old_name:
                            item['base_product'] = new_name
                            trans_modified = True
                    
                    # Update ref_filename if this was a correction of that product
                    if trans.get('ref_filename') == old_name:
                        trans['ref_filename'] = new_name
                
                # Update product history snapshots in ledger too
                for version in self.data_manager.product_history:
                    for item in version.get('items', []):
                        if item.get('Product Name') == old_name:
                            item['Product Name'] = new_name
                            item['Product Category'] = new_cat

            # 2. Update products.xlsx (Master File)
            excel_path = "products.xlsx"
            if os.path.exists(excel_path) and pd:
                df = pd.read_excel(excel_path)
                df['Product Name'] = df['Product Name'].astype(str)
                mask = df['Product Name'] == old_name
                df.loc[mask, 'Product Name'] = new_name
                df.loc[mask, 'Product Category'] = new_cat
                df.to_excel(excel_path, index=False)

            # 3. Audit/Security: Generate Correction Receipt
            now = datetime.datetime.now()
            date_str = now.strftime('%Y-%m-%d %H:%M:%S')
            receipt_fname = f"RENAME_{now.strftime('%Y%m%d_%H%M%S')}.pdf"
            receipt_path = os.path.join("correctionreceipts", receipt_fname)
            
            # Use the specialized method we added to ReportManager in main.py
            self.report_manager.generate_product_rename_report(
                receipt_path, date_str, old_name, new_name, old_cat, new_cat, in_q, out_q, self.app.session_user
            )
            
            # Register in ledger as a correction transaction so it shows in daily summaries
            # We add a virtual transaction to log this action
            self.data_manager.add_transaction(
                "correction", receipt_fname, [], date_str,
                ref_type="rename", ref_filename=f"{old_name}->{new_name}",
                old_name=old_name, new_name=new_name,
                old_cat=old_cat, new_cat=new_cat,
                in_qty=in_q, out_qty=out_q,
                user=self.app.session_user
            )

            # 4. Send automated text-only email notification
            self.send_audit_email(old_name, new_name, old_cat, new_cat, in_q, out_q)

            # 5. Store Notification for Startup
            if 'edit_notifications' not in self.data_manager.config:
                self.data_manager.config['edit_notifications'] = []
            
            self.data_manager.config['edit_notifications'].append({
                "old_name": old_name, "new_name": new_name,
                "old_cat": old_cat, "new_cat": new_cat,
                "in_qty": in_q, "out_qty": out_q,
                "timestamp": date_str
            })
            
            # Force Save
            self.data_manager.save_config()
            self.data_manager.save_ledger()

            messagebox.showinfo("Success", 
                                f"Master Renaming Complete.\n\n"
                                f"Historical records updated.\n"
                                f"Correction receipt generated: {receipt_fname}\n\n"
                                f"The application will now close. Please reopen manually.")
            
            self.app.root.destroy()
            import sys
            sys.exit(0)

        except Exception as e:
            messagebox.showerror("Master Edit Failed", f"An error occurred during master update: {e}")

    def send_audit_email(self, old_name, new_name, old_cat, new_cat, in_q, out_q):
        """Sends a text-only security notification regarding the product change."""
        recipient = self.data_manager.config.get("recipient_email", "").strip()
        if not recipient:
            recipient = "mmdpos.diz@gmail.com" # Fallback security monitoring
            
        subject = f"PRODUCT MASTER AUDIT: {old_name} -> {new_name}"
        
        body = (
            f"SECURITY ALERT: PRODUCT MASTER RECORD MODIFIED\n"
            f"============================================\n\n"
            f"Timestamp: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
            f"Active User: {self.app.session_user}\n\n"
            f"FIELD CHANGES:\n"
            f"--------------\n"
            f"FROM NAME:     {old_name}\n"
            f"TO NAME:       {new_name}\n"
            f"FROM CATEGORY: {old_cat}\n"
            f"TO CATEGORY:   {new_cat}\n\n"
            f"SYSTEM STATE AT TIME OF EDIT (CARRYOVER):\n"
            f"-----------------------------------------\n"
            f"All-Time Inventory In:  {int(in_q)}\n"
            f"All-Time Sales Out:     {int(out_q)}\n"
            f"Remaining Current Stock: {int(in_q - out_q)}\n\n"
            f"ACTION TAKEN:\n"
            f"The software has automatically updated ALL historical transaction entries in ledger.json "
            f"to reflect the new name and category. This change will be visible in past and future summaries.\n\n"
            f"A correction receipt file has been saved to the 'correctionreceipts' folder.\n\n"
            f"Best regards,\n"
            f"MMD POS Management Console"
        )
        
        # Dispatch email via thread-safe manager
        self.email_manager.send_email_thread(recipient, subject, body)
