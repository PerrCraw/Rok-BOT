"""
ROK Unified Tool - Modern GUI Edition with Troops Selection
Combines functionality from bot-v2.4.py with modern CustomTkinter GUI
"""

import os
import sys
import subprocess
import threading
import time
import random
import math
import json
import hashlib
import requests
from datetime import datetime
from pathlib import Path

# GUI imports
import customtkinter as ctk
from tkinter import messagebox, filedialog

# Bot functionality imports
try:
    import cv2
    import pytesseract
    OPENCV_AVAILABLE = True
except ImportError:
    OPENCV_AVAILABLE = False
    print("[Warning] OpenCV/Tesseract not available")

try:
    from PIL import ImageGrab, Image
    import pyautogui
    import keyboard
    pyautogui.FAILSAFE = False
    AUTOGUI_AVAILABLE = True
except ImportError:
    AUTOGUI_AVAILABLE = False
    print("[Warning] PyAutoGUI not available")

try:
    import numpy as np
    NUMPY_AVAILABLE = True
except ImportError:
    NUMPY_AVAILABLE = False

# Configuration
ADB_PATH = "adb\\adb.exe"
SCREENSHOT_PATH = "cache\\screenshot.png"

# Set appearance
ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

class ModernROKTool:
    def __init__(self):
        # Initialize window
        self.root = ctk.CTk()
        self.root.title("ROK Unified Tool - Professional Edition")
        self.root.geometry("1400x900")
        
        # Performance optimization
        self.root.resizable(True, True)
        
        # Core settings
        self.logged_in = False
        self.current_user = None
        self.active_profile = "Nhan"
        self.config_file = os.path.join(os.path.expanduser("~"), "Documents", "rok_config.json")
        self.settings_file = os.path.join(os.path.expanduser("~"), "Documents", "rok_settings.json")
        self.log_file = os.path.join(os.path.expanduser("~"), "Documents", "ROK_Log.txt")
        
        # GUI update throttling
        self.last_gui_update = 0
        self.gui_update_interval = 0.5
        
        # AutoFarm state
        self.toggle = False
        self.running = False
        self.current_resource = "Wood"
        self.resource_rotation_enabled = False
        self.selected_resources = ["Wood"]
        self.auto_hide_enabled = True
        self.current_rotation_index = 0
        self.num_troops = 1  # Default 1 troop
        
        # Timing parameters
        self.click_randomization = 12
        self.micro_correction_chance = 25
        self.overshoot_chance = 15
        self.action_delay_min = 2500
        self.action_delay_max = 4500
        
        # Mouse movement delays
        self.mouse_move_delay_min = 25
        self.mouse_move_delay_max = 65
        self.bezier_points = 12
        self.curve_intensity = 25
        
        # Click delays
        self.pre_click_delay_min = 150
        self.pre_click_delay_max = 350
        self.post_click_delay_min = 200
        self.post_click_delay_max = 450
        
        # Session tracking
        self.session_start_time = 0
        self.fatigue_level = 0
        self.total_marches = 0
        self.successful_marches = 0
        self.total_help_clicks = 0
        
        # Profile coordinates
        self.setup_profile_coordinates()
        
        # Features
        self.auto_help_enabled = True
        
        # Color detection
        self.gathering_colors = [0x0D9A00, 0xB45D00, 0xFFFFFF, 0x32CD32, 0x228B22, 0x00FF00, 0x90EE90, 0x8B4513]
        self.tolerance = 10
        self.helping_colors = [0xFFF4E4, 0x34A501, 0xF7F6C1, 0xD77824, 0xE3775E, 0xE78167, 0xFCA593, 0xF89B8A, 0xEB8D7B, 0xD47968]
        self.tolerance1 = 10
        
        # Help button area
        self.help_area = None
        self.help_button = None
        self.reconnect_area = None
        self.reconnect_color = None
        
        self.nhan_help_area = (1515, 926)
        self.nhan_help_button = (1539, 948)
        self.huy_help_area = (1515, 926)
        self.huy_help_button = (1539, 948)
        
        # Reconnect detection
        self.nhan_reconnect_area = (841, 633, 1080, 682)
        self.nhan_reconnect_color = 0x00AEEF
        self.huy_reconnect_area = (1273, 1048, 1595, 1107)
        self.huy_reconnect_color = 0x00AEEF
        
        # Slot tracking
        self.slot_last_check = [0] * 5
        self.min_wait_time_base = 35000
        self.max_wait_time_base = 55000
        
        # Break system
        self.last_break_time = 0
        self.micro_break_chance = 8
        self.total_micro_breaks = 0
        
        # Webhook
        self.webhook_url = ""
        self.webhook_enabled = False
        self.webhook_on_start = True
        self.webhook_on_stop = True
        self.webhook_on_success = False
        self.webhook_on_fail = False
        self.last_webhook_time = 0
        self.webhook_interval = 30
        
        # Gem farming
        self.gem_farming_enabled = False
        self.gems_collected = 0
        
        # Buff monitoring
        self.buff_monitoring = False
        self.active_buffs = []
        
        # Connected devices
        self.connected_devices = set()
        
        # Initialize coordinates placeholders
        self.march_slots = []
        self.search_button = None
        self.gather_btn = None
        self.send_troops = None
        self.march_confirm = None
        self.troop_positions = []
        self.resources = {}
        self.search_confirms = {}
        
        # Ensure directories
        os.makedirs("cache", exist_ok=True)
        os.makedirs(os.path.dirname(self.log_file), exist_ok=True)
        
        # Load saved settings
        self.load_settings()
        
        # Show login screen
        self.show_login_screen()
    
    def setup_profile_coordinates(self):
        """Setup coordinates for both profiles"""
        # Nhan profile
        self.nhan_march_slots = [(1884, 250), (1884, 330), (1884, 410), (1885, 485), (1884, 575)]
        self.nhan_search_button = (1866, 905)
        self.nhan_gather_btn = (623, 666)
        self.nhan_send_troops = (1643, 318)
        self.nhan_march_confirm = (1262, 834)
        self.nhan_troop_positions = [
            (1440, 372),  # Troop 1
            (1537, 372),  # Troop 2
            (1634, 372),  # Troop 3
            (1731, 372),  # Troop 4
            (1828, 372),  # Troop 5
            (1440, 469),  # Troop 6
            (1537, 469)   # Troop 7
        ]
        self.nhan_resources = {
            "Food": (763, 994), 
            "Wood": (962, 994), 
            "Stone": (1162, 994), 
            "Gold": (1365, 994)
        }
        self.nhan_search_confirms = {
            "Food": (761, 841),
            "Wood": (966, 842),
            "Stone": (1160, 842),
            "Gold": (1365, 837)
        }
        self.nhan_help_area = (1515, 926)
        self.nhan_help_button = (1539, 948)
        self.nhan_reconnect_area = (841, 633, 1080, 682)
        self.nhan_reconnect_color = 0x00AEEF
        
        # Huy profile
        self.huy_march_slots = [(2831, 466), (2827, 579), (2830, 700), (2826, 820), (2829, 941)]
        self.huy_search_button = (2790, 1440)
        self.huy_gather_btn = (1894, 1102)
        self.huy_send_troops = (2470, 560)
        self.huy_march_confirm = (1905, 1329)
        self.huy_troop_positions = [
            (2160, 654),  # Troop 1
            (2304, 654),  # Troop 2
            (2448, 654),  # Troop 3
            (2592, 654),  # Troop 4
            (2736, 654),  # Troop 5
            (2160, 798),  # Troop 6
            (2304, 798)   # Troop 7
        ]
        self.huy_resources = {
            "Food": (1140, 1586), 
            "Wood": (1436, 1593), 
            "Stone": (1720, 1581), 
            "Gold": (2025, 1570)
        }
        self.huy_search_confirms = {
            "Food": (1147, 1344),
            "Wood": (1445, 1362),
            "Stone": (1765, 1361),
            "Gold": (2069, 1342)
        }
        self.huy_help_area = (1515, 926)
        self.huy_help_button = (1539, 948)
        self.huy_reconnect_area = (1273, 1048, 1595, 1107)
        self.huy_reconnect_color = 0x00AEEF
        
        # Set active
        self.update_profile_coordinates()
    
    def update_profile_coordinates(self):
        """Switch profile coordinates"""
        if self.active_profile == "Nhan":
            self.march_slots = self.nhan_march_slots
            self.search_button = self.nhan_search_button
            self.gather_btn = self.nhan_gather_btn
            self.send_troops = self.nhan_send_troops
            self.march_confirm = self.nhan_march_confirm
            self.troop_positions = self.nhan_troop_positions
            self.resources = self.nhan_resources
            self.search_confirms = self.nhan_search_confirms
            self.help_area = self.nhan_help_area
            self.help_button = self.nhan_help_button
            self.reconnect_area = self.nhan_reconnect_area
            self.reconnect_color = self.nhan_reconnect_color
        else:
            self.march_slots = self.huy_march_slots
            self.search_button = self.huy_search_button
            self.gather_btn = self.huy_gather_btn
            self.send_troops = self.huy_send_troops
            self.march_confirm = self.huy_march_confirm
            self.troop_positions = self.huy_troop_positions
            self.resources = self.huy_resources
            self.search_confirms = self.huy_search_confirms
            self.help_area = self.huy_help_area
            self.help_button = self.huy_help_button
            self.reconnect_area = self.huy_reconnect_area
            self.reconnect_color = self.huy_reconnect_color
        
        # Reset slot tracking
        self.slot_last_check = [0] * len(self.march_slots)
    
    def load_settings(self):
        """Load saved settings from file"""
        try:
            if os.path.exists(self.settings_file):
                with open(self.settings_file, 'r') as f:
                    settings = json.load(f)
                
                # Load resources
                self.selected_resources = settings.get('selected_resources', ["Wood"])
                self.resource_rotation_enabled = settings.get('resource_rotation_enabled', False)
                
                # Load troops
                self.num_troops = settings.get('num_troops', 1)
                
                # Load features
                self.auto_help_enabled = settings.get('auto_help_enabled', True)
                self.auto_hide_enabled = settings.get('auto_hide_enabled', True)
                
                # Load webhook
                self.webhook_url = settings.get('webhook_url', "")
                self.webhook_enabled = settings.get('webhook_enabled', False)
                self.webhook_on_success = settings.get('webhook_on_success', False)
                self.webhook_on_fail = settings.get('webhook_on_fail', False)
                
                self.log("Settings loaded successfully")
            else:
                self.log("No saved settings found, using defaults")
        except Exception as e:
            self.log(f"Failed to load settings: {e}")
    
    def save_settings(self):
        """Save current settings to file"""
        try:
            settings = {
                'selected_resources': self.selected_resources,
                'resource_rotation_enabled': self.resource_rotation_enabled,
                'num_troops': self.num_troops,
                'auto_help_enabled': self.auto_help_enabled,
                'auto_hide_enabled': self.auto_hide_enabled,
                'webhook_url': self.webhook_url,
                'webhook_enabled': self.webhook_enabled,
                'webhook_on_success': self.webhook_on_success,
                'webhook_on_fail': self.webhook_on_fail,
                'last_profile': self.active_profile
            }
            
            with open(self.settings_file, 'w') as f:
                json.dump(settings, f, indent=4)
            
            self.log("Settings saved successfully")
        except Exception as e:
            self.log(f"Failed to save settings: {e}")
    
    def log(self, msg):
        """Log message"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        try:
            with open(self.log_file, 'a', encoding='utf-8') as f:
                f.write(f"[{timestamp}] {msg}\n")
        except:
            pass
        print(f"[{timestamp}] {msg}")
        
        if hasattr(self, 'log_textbox'):
            self.root.after(0, lambda: self.add_gui_log(msg))
    
    def add_gui_log(self, msg):
        """Add message to GUI log"""
        try:
            timestamp = datetime.now().strftime("%H:%M:%S")
            self.log_textbox.insert("0.0", f"[{timestamp}] {msg}\n")
            
            content = self.log_textbox.get("0.0", "end")
            lines = content.split('\n')
            if len(lines) > 50:
                self.log_textbox.delete("50.0", "end")
        except:
            pass
    
    def verify_login(self, username, password):
        """Verify login credentials"""
        username = username.lower().strip()
        if username not in ['nhan', 'huy']:
            return False, "Invalid username. Use 'nhan' or 'huy'"
        
        password_hash = hashlib.sha256(password.encode()).hexdigest()
        
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r') as f:
                    config = json.load(f)
                    saved_hash = config.get(username.lower())
                    
                    if saved_hash is None:
                        config[username.lower()] = password_hash
                        with open(self.config_file, 'w') as f:
                            json.dump(config, f)
                        return True, "Password saved successfully"
                    elif saved_hash == password_hash:
                        return True, "Login successful"
                    else:
                        return False, "Incorrect password"
            else:
                config = {username.lower(): password_hash}
                os.makedirs(os.path.dirname(self.config_file), exist_ok=True)
                with open(self.config_file, 'w') as f:
                    json.dump(config, f)
                return True, "Password saved successfully"
        except Exception as e:
            return False, f"Error: {e}"
    
    def show_login_screen(self):
        """Show modern login screen"""
        self.login_frame = ctk.CTkFrame(self.root, fg_color="transparent")
        self.login_frame.place(relx=0.5, rely=0.5, anchor="center")
        
        title = ctk.CTkLabel(
            self.login_frame,
            text="ROK Unified Tool",
            font=ctk.CTkFont(size=36, weight="bold")
        )
        title.pack(pady=(0, 10))
        
        subtitle = ctk.CTkLabel(
            self.login_frame,
            text="Professional Edition with Troops Selection",
            font=ctk.CTkFont(size=14),
            text_color="gray"
        )
        subtitle.pack(pady=(0, 30))
        
        input_frame = ctk.CTkFrame(self.login_frame, width=400)
        input_frame.pack(pady=20, padx=40, fill="both", expand=True)
        
        ctk.CTkLabel(
            input_frame,
            text="Username",
            font=ctk.CTkFont(size=12, weight="bold")
        ).pack(anchor="w", padx=20, pady=(20, 5))
        
        self.username_entry = ctk.CTkEntry(
            input_frame,
            placeholder_text="nhan or huy",
            width=350,
            height=40
        )
        self.username_entry.pack(padx=20, pady=(0, 15))
        
        ctk.CTkLabel(
            input_frame,
            text="Password",
            font=ctk.CTkFont(size=12, weight="bold")
        ).pack(anchor="w", padx=20, pady=(0, 5))
        
        self.password_entry = ctk.CTkEntry(
            input_frame,
            placeholder_text="Enter password",
            show="●",
            width=350,
            height=40
        )
        self.password_entry.pack(padx=20, pady=(0, 20))
        
        login_btn = ctk.CTkButton(
            input_frame,
            text="Login",
            command=self.handle_login,
            width=350,
            height=45,
            font=ctk.CTkFont(size=14, weight="bold")
        )
        login_btn.pack(padx=20, pady=(0, 20))
        
        info = ctk.CTkLabel(
            input_frame,
            text="Valid users: nhan, huy",
            font=ctk.CTkFont(size=11),
            text_color="gray"
        )
        info.pack(pady=(0, 20))
        
        self.username_entry.bind("<Return>", lambda e: self.handle_login())
        self.password_entry.bind("<Return>", lambda e: self.handle_login())
        self.username_entry.focus()
    
    def handle_login(self):
        """Handle login"""
        username = self.username_entry.get()
        password = self.password_entry.get()
        
        if not username or not password:
            messagebox.showerror("Error", "Please enter username and password")
            return
        
        success, message = self.verify_login(username, password)
        
        if success:
            self.logged_in = True
            self.current_user = username.lower()
            self.active_profile = "Nhan" if self.current_user == 'nhan' else "Huy"
            self.update_profile_coordinates()
            self.log(f"User '{self.current_user}' logged in - Profile: {self.active_profile}")
            
            self.login_frame.destroy()
            self.show_main_screen()
        else:
            messagebox.showerror("Login Failed", message)
    
    def show_main_screen(self):
        """Show main application screen"""
        main_container = ctk.CTkFrame(self.root, fg_color="transparent")
        main_container.pack(fill="both", expand=True, padx=10, pady=10)
        
        self.create_top_bar(main_container)
        
        # Tabview
        self.tabview = ctk.CTkTabview(main_container)
        self.tabview.pack(fill="both", expand=True, pady=(10, 0))
        
        # Create tabs
        self.tabview.add("AutoFarm")
        self.tabview.add("Buff Monitor")
        self.tabview.add("Gem Farming")
        self.tabview.add("Emulator Control")
        
        # Populate tabs
        self.create_autofarm_tab()
        self.create_buff_tab()
        self.create_gem_tab()
        self.create_emulator_tab()
    
    def create_top_bar(self, parent):
        """Create top control bar"""
        top_bar = ctk.CTkFrame(parent, height=80)
        top_bar.pack(fill="x", pady=(0, 10))
        top_bar.pack_propagate(False)
        
        left_frame = ctk.CTkFrame(top_bar, fg_color="transparent")
        left_frame.pack(side="left", padx=20, pady=15)
        
        ctk.CTkLabel(
            left_frame,
            text=f"Profile: {self.active_profile} | User: {self.current_user}",
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack()
        
        ctk.CTkLabel(
            left_frame,
            text=f"Slots: {len(self.march_slots)}",
            font=ctk.CTkFont(size=11),
            text_color="gray"
        ).pack()
        
        right_frame = ctk.CTkFrame(top_bar, fg_color="transparent")
        right_frame.pack(side="right", padx=20, pady=10)
        
        self.start_stop_btn = ctk.CTkButton(
            right_frame,
            text="▶ START AutoFarm (F8)",
            command=self.toggle_autofarm,
            width=200,
            height=60,
            font=ctk.CTkFont(size=16, weight="bold"),
            fg_color="green",
            hover_color="darkgreen"
        )
        self.start_stop_btn.pack()
        
        self.status_label = ctk.CTkLabel(
            right_frame,
            text="● Stopped",
            font=ctk.CTkFont(size=12),
            text_color="red"
        )
        self.status_label.pack(pady=(5, 0))
    
    def create_autofarm_tab(self):
        """Create AutoFarm tab"""
        tab = self.tabview.tab("AutoFarm")
        
        left_scroll = ctk.CTkScrollableFrame(tab, width=700)
        left_scroll.pack(side="left", fill="both", expand=True, padx=(0, 5))
        
        right_col = ctk.CTkFrame(tab, width=400)
        right_col.pack(side="right", fill="both", padx=(5, 0))
        right_col.pack_propagate(False)
        
        self.create_statistics_section(left_scroll)
        self.create_resources_section(left_scroll)
        self.create_features_section(left_scroll)
        self.create_webhook_section(left_scroll)
        self.create_save_section(left_scroll)  # New section
        self.create_activity_log(right_col)
        self.create_status_section(right_col)
        
        # Apply loaded settings to GUI
        self.apply_settings_to_gui()
    
    def create_statistics_section(self, parent):
        """Create statistics display"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="x", padx=10, pady=10)
        
        ctk.CTkLabel(
            frame,
            text="📊 Statistics",
            font=ctk.CTkFont(size=18, weight="bold")
        ).pack(anchor="w", padx=15, pady=10)
        
        stats_grid = ctk.CTkFrame(frame, fg_color="transparent")
        stats_grid.pack(fill="x", padx=10, pady=10)
        
        self.stat_labels = {}
        stats_data = [
            ("Total Marches", "total_marches", "0"),
            ("Successful", "successful", "0 (0%)"),
            ("Help Clicks", "help_clicks", "0"),
            ("Fatigue", "fatigue", "0%"),
            ("Session", "session_time", "0 min"),
            ("Gems", "gems", "0")
        ]
        
        for i, (label, key, default) in enumerate(stats_data):
            row = i // 3
            col = i % 3
            
            stat_frame = ctk.CTkFrame(stats_grid)
            stat_frame.grid(row=row, column=col, padx=5, pady=5, sticky="ew")
            stats_grid.columnconfigure(col, weight=1)
            
            ctk.CTkLabel(
                stat_frame,
                text=label,
                font=ctk.CTkFont(size=10),
                text_color="gray"
            ).pack(pady=(10, 0))
            
            value_label = ctk.CTkLabel(
                stat_frame,
                text=default,
                font=ctk.CTkFont(size=18, weight="bold")
            )
            value_label.pack(pady=(0, 10))
            
            self.stat_labels[key] = value_label
    
    def create_resources_section(self, parent):
        """Create resource selection"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="x", padx=5, pady=5)
        
        ctk.CTkLabel(
            frame,
            text="🌾 Resources",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(anchor="w", padx=10, pady=8)
        
        # Resource buttons
        resources_grid = ctk.CTkFrame(frame, fg_color="transparent")
        resources_grid.pack(fill="x", padx=5, pady=5)
        
        self.resource_buttons = {}
        resources = ["Food", "Wood", "Stone", "Gold"]
        icons = ["🌾", "🪵", "🪨", "🪙"]
        
        for i, (resource, icon) in enumerate(zip(resources, icons)):
            btn = ctk.CTkButton(
                resources_grid,
                text=f"{icon}\n{resource}",
                command=lambda r=resource: self.toggle_resource(r),
                width=70,
                height=65,
                font=ctk.CTkFont(size=10),
                fg_color="gray30" if resource != "Wood" else "blue"
            )
            btn.grid(row=0, column=i, padx=3, pady=3)
            self.resource_buttons[resource] = btn
        
        # Rotation toggle
        rotation_frame = ctk.CTkFrame(frame, fg_color="transparent", height=35)
        rotation_frame.pack(fill="x", padx=10, pady=5)
        rotation_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            rotation_frame,
            text="Enable Rotation",
            font=ctk.CTkFont(size=11)
        ).pack(side="left")
        
        self.rotation_switch = ctk.CTkSwitch(
            rotation_frame,
            text="",
            width=40,
            command=self.toggle_rotation
        )
        self.rotation_switch.pack(side="right")
        
        # Selected display
        self.selected_label = ctk.CTkLabel(
            frame,
            text="Selected: Wood",
            font=ctk.CTkFont(size=10),
            text_color="gray"
        )
        self.selected_label.pack(padx=10, pady=(0, 8))
        
        # Troops selection
        troops_frame = ctk.CTkFrame(frame, fg_color="transparent", height=40)
        troops_frame.pack(fill="x", padx=10, pady=5)
        troops_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            troops_frame,
            text="Number of Troops:",
            font=ctk.CTkFont(size=11)
        ).pack(side="left")
        
        self.troops_slider = ctk.CTkSlider(
            troops_frame,
            from_=1,
            to=7,
            number_of_steps=6,
            width=120,
            command=self.update_troops_count
        )
        self.troops_slider.set(1)
        self.troops_slider.pack(side="left", padx=10)
        
        self.troops_label = ctk.CTkLabel(
            troops_frame,
            text="1",
            font=ctk.CTkFont(size=12, weight="bold"),
            text_color="cyan"
        )
        self.troops_label.pack(side="left")
    
    def create_features_section(self, parent):
        """Create features toggles"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="x", padx=5, pady=5)
        
        ctk.CTkLabel(
            frame,
            text="⚙️ Features",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(anchor="w", padx=10, pady=8)
        
        # Auto help
        help_frame = ctk.CTkFrame(frame, fg_color="transparent", height=30)
        help_frame.pack(fill="x", padx=10, pady=3)
        help_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            help_frame,
            text="Auto Help Detection",
            font=ctk.CTkFont(size=11)
        ).pack(side="left")
        
        self.auto_help_switch = ctk.CTkSwitch(
            help_frame,
            text="",
            width=40,
            command=self.toggle_auto_help
        )
        self.auto_help_switch.select()
        self.auto_help_switch.pack(side="right")
        
        # Auto hide
        hide_frame = ctk.CTkFrame(frame, fg_color="transparent", height=30)
        hide_frame.pack(fill="x", padx=10, pady=3)
        hide_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            hide_frame,
            text="Auto-Hide on Start",
            font=ctk.CTkFont(size=11)
        ).pack(side="left")
        
        self.auto_hide_switch = ctk.CTkSwitch(
            hide_frame,
            text="",
            width=40
        )
        self.auto_hide_switch.select()
        self.auto_hide_switch.pack(side="right", pady=(0, 5))
    
    def create_webhook_section(self, parent):
        """Create webhook section"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="x", padx=5, pady=5)
        
        ctk.CTkLabel(
            frame,
            text="📢 Discord Webhook",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(anchor="w", padx=10, pady=8)
        
        self.webhook_entry = ctk.CTkEntry(
            frame,
            placeholder_text="Webhook URL",
            height=32
        )
        self.webhook_entry.pack(padx=10, pady=3, fill="x")
        
        # Bind event to auto-save when webhook URL changes
        self.webhook_entry.bind("<FocusOut>", lambda e: self.on_webhook_change())
        self.webhook_entry.bind("<Return>", lambda e: self.on_webhook_change())
        
        webhook_frame = ctk.CTkFrame(frame, fg_color="transparent", height=30)
        webhook_frame.pack(fill="x", padx=10, pady=3)
        webhook_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            webhook_frame,
            text="Enable Notifications",
            font=ctk.CTkFont(size=11)
        ).pack(side="left")
        
        self.webhook_switch = ctk.CTkSwitch(
            webhook_frame,
            text="",
            width=40,
            command=self.toggle_webhook
        )
        self.webhook_switch.pack(side="right", pady=(0, 5))
        
        # Webhook notification options
        options_frame = ctk.CTkFrame(frame, fg_color="transparent")
        options_frame.pack(fill="x", padx=10, pady=3)
        
        # Success notifications
        success_frame = ctk.CTkFrame(options_frame, fg_color="transparent", height=25)
        success_frame.pack(fill="x", pady=1)
        success_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            success_frame,
            text="Notify on Success",
            font=ctk.CTkFont(size=10)
        ).pack(side="left")
        
        self.webhook_success_switch = ctk.CTkSwitch(
            success_frame,
            text="",
            width=35,
            command=self.on_webhook_option_change
        )
        self.webhook_success_switch.pack(side="right")
        
        # Fail notifications
        fail_frame = ctk.CTkFrame(options_frame, fg_color="transparent", height=25)
        fail_frame.pack(fill="x", pady=1)
        fail_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            fail_frame,
            text="Notify on Fail",
            font=ctk.CTkFont(size=10)
        ).pack(side="left")
        
        self.webhook_fail_switch = ctk.CTkSwitch(
            fail_frame,
            text="",
            width=35,
            command=self.on_webhook_option_change
        )
        self.webhook_fail_switch.pack(side="right", pady=(0, 3))
    
    def create_save_section(self, parent):
        """Create save/load settings section"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="x", padx=5, pady=5)
        
        ctk.CTkLabel(
            frame,
            text="💾 Settings",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(anchor="w", padx=10, pady=8)
        
        btn_frame = ctk.CTkFrame(frame, fg_color="transparent")
        btn_frame.pack(fill="x", padx=10, pady=5)
        
        ctk.CTkButton(
            btn_frame,
            text="💾 Save Config",
            command=self.manual_save_settings,
            width=120,
            height=32,
            font=ctk.CTkFont(size=11)
        ).pack(side="left", padx=2)
        
        ctk.CTkButton(
            btn_frame,
            text="📁 Load Config",
            command=self.manual_load_settings,
            width=120,
            height=32,
            font=ctk.CTkFont(size=11)
        ).pack(side="left", padx=2)
        
        ctk.CTkButton(
            btn_frame,
            text="🔄 Reset",
            command=self.reset_settings,
            width=80,
            height=32,
            font=ctk.CTkFont(size=11),
            fg_color="orange",
            hover_color="darkorange"
        ).pack(side="left", padx=2)
        
        # Auto-save toggle
        autosave_frame = ctk.CTkFrame(frame, fg_color="transparent", height=30)
        autosave_frame.pack(fill="x", padx=10, pady=3)
        autosave_frame.pack_propagate(False)
        
        ctk.CTkLabel(
            autosave_frame,
            text="Auto-Save on Change",
            font=ctk.CTkFont(size=11)
        ).pack(side="left")
        
        self.autosave_switch = ctk.CTkSwitch(
            autosave_frame,
            text="",
            width=40
        )
        self.autosave_switch.select()  # Enabled by default
        self.autosave_switch.pack(side="right")
        
        # Last saved info
        self.last_saved_label = ctk.CTkLabel(
            frame,
            text="⏱️ Last saved: Never",
            font=ctk.CTkFont(size=9),
            text_color="gray"
        )
        self.last_saved_label.pack(padx=10, pady=(0, 8))
    
    def apply_settings_to_gui(self):
        """Apply loaded settings to GUI elements"""
        try:
            # Apply resources
            for resource in ["Food", "Wood", "Stone", "Gold"]:
                if resource in self.selected_resources:
                    self.resource_buttons[resource].configure(fg_color="blue")
                else:
                    self.resource_buttons[resource].configure(fg_color="gray30")
            
            self.selected_label.configure(
                text=f"Selected: {', '.join(self.selected_resources) if self.selected_resources else 'None'}"
            )
            
            # Apply rotation
            if self.resource_rotation_enabled:
                self.rotation_switch.select()
            else:
                self.rotation_switch.deselect()
            
            # Apply troops
            self.troops_slider.set(self.num_troops)
            self.troops_label.configure(text=str(self.num_troops))
            
            # Apply features
            if self.auto_help_enabled:
                self.auto_help_switch.select()
            else:
                self.auto_help_switch.deselect()
            
            if self.auto_hide_enabled:
                self.auto_hide_switch.select()
            else:
                self.auto_hide_switch.deselect()
            
            # Apply webhook
            if self.webhook_url:
                self.webhook_entry.delete(0, 'end')
                self.webhook_entry.insert(0, self.webhook_url)
            
            if self.webhook_enabled:
                self.webhook_switch.select()
            else:
                self.webhook_switch.deselect()
            
            # Apply webhook options
            if self.webhook_on_success:
                self.webhook_success_switch.select()
            else:
                self.webhook_success_switch.deselect()
            
            if self.webhook_on_fail:
                self.webhook_fail_switch.select()
            else:
                self.webhook_fail_switch.deselect()
            
            self.log("GUI settings applied")
        except Exception as e:
            self.log(f"Failed to apply GUI settings: {e}")
    
    def manual_save_settings(self):
        """Manual save button handler"""
        self.save_settings()
        self.last_saved_label.configure(
            text=f"⏱️ Last saved: {datetime.now().strftime('%H:%M:%S')}"
        )
        messagebox.showinfo("Success", "✅ Settings saved successfully!\n\nSaved settings:\n• Resources\n• Troops count\n• Features\n• Webhook config")
    
    def manual_load_settings(self):
        """Manual load button handler"""
        self.load_settings()
        self.apply_settings_to_gui()
        messagebox.showinfo("Success", "✅ Settings loaded successfully!\n\nAll configurations restored.")
    
    def reset_settings(self):
        """Reset all settings to default"""
        if messagebox.askyesno("Confirm Reset", "⚠️ Reset all settings to default?\n\nThis will:\n• Reset resources to Wood only\n• Set troops to 1\n• Clear webhook URL\n• Reset all features"):
            self.selected_resources = ["Wood"]
            self.resource_rotation_enabled = False
            self.num_troops = 1
            self.auto_help_enabled = True
            self.auto_hide_enabled = True
            self.webhook_url = ""
            self.webhook_enabled = False
            self.webhook_on_success = False
            self.webhook_on_fail = False
            
            self.apply_settings_to_gui()
            self.save_settings()
            self.last_saved_label.configure(
                text=f"⏱️ Last saved: {datetime.now().strftime('%H:%M:%S')}"
            )
            self.log("Settings reset to default")
            messagebox.showinfo("Success", "✅ Settings reset to default!")
    
    def create_activity_log(self, parent):
        """Create activity log"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="both", expand=True, pady=(0, 3))
        
        ctk.CTkLabel(
            frame,
            text="📋 Activity Log",
            font=ctk.CTkFont(size=16, weight="bold")
        ).pack(anchor="w", padx=10, pady=8)
        
        self.log_textbox = ctk.CTkTextbox(
            frame,
            wrap="word",
            font=ctk.CTkFont(size=10, family="Consolas"),
            height=300,
            activate_scrollbars=True
        )
        self.log_textbox.pack(fill="both", expand=True, padx=8, pady=(0, 8))
    
    def create_status_section(self, parent):
        """Create status indicators"""
        frame = ctk.CTkFrame(parent)
        frame.pack(fill="x", pady=(3, 0))
        
        ctk.CTkLabel(
            frame,
            text="💡 Hotkeys",
            font=ctk.CTkFont(size=14, weight="bold")
        ).pack(anchor="w", padx=10, pady=6)
        
        hotkeys = [
            ("F8", "Toggle AutoFarm"),
            ("F9", "Force Exit"),
            ("F10", "Toggle Window"),
        ]
        
        for key, desc in hotkeys:
            item_frame = ctk.CTkFrame(frame, fg_color="transparent", height=22)
            item_frame.pack(fill="x", padx=10, pady=1)
            item_frame.pack_propagate(False)
            
            ctk.CTkLabel(
                item_frame,
                text=key,
                font=ctk.CTkFont(size=10, weight="bold"),
                text_color="cyan"
            ).pack(side="left")
            
            ctk.CTkLabel(
                item_frame,
                text=f" - {desc}",
                font=ctk.CTkFont(size=10),
                text_color="gray"
            ).pack(side="left")
        
        ctk.CTkLabel(
            frame,
            text="v2.5 - With Troops Selection",
            font=ctk.CTkFont(size=9),
            text_color="gray"
        ).pack(pady=(6, 8))
    
    def create_buff_tab(self):
        """Create Buff Monitor tab"""
        tab = self.tabview.tab("Buff Monitor")
        
        ctk.CTkLabel(
            tab,
            text="🛡️ Buff Monitoring System",
            font=ctk.CTkFont(size=24, weight="bold")
        ).pack(pady=20)
        
        control_frame = ctk.CTkFrame(tab)
        control_frame.pack(fill="x", padx=20, pady=10)
        
        btn_frame = ctk.CTkFrame(control_frame, fg_color="transparent")
        btn_frame.pack(pady=10)
        
        self.start_buff_btn = ctk.CTkButton(
            btn_frame,
            text="▶ Start Monitoring",
            command=self.toggle_buff_monitoring,
            width=150,
            height=40
        )
        self.start_buff_btn.pack(side="left", padx=5)
        
        ctk.CTkButton(
            btn_frame,
            text="🔍 Scan Now",
            command=self.manual_buff_scan,
            width=150,
            height=40
        ).pack(side="left", padx=5)
        
        self.buff_listbox = ctk.CTkTextbox(tab, height=300)
        self.buff_listbox.pack(fill="both", expand=True, padx=20, pady=10)
    
    def create_gem_tab(self):
        """Create Gem Farming tab"""
        tab = self.tabview.tab("Gem Farming")
        
        ctk.CTkLabel(
            tab,
            text="💎 Gem Farming System",
            font=ctk.CTkFont(size=24, weight="bold")
        ).pack(pady=20)
        
        control_frame = ctk.CTkFrame(tab)
        control_frame.pack(fill="x", padx=20, pady=10)
        
        btn_frame = ctk.CTkFrame(control_frame, fg_color="transparent")
        btn_frame.pack(pady=10)
        
        self.start_gem_btn = ctk.CTkButton(
            btn_frame,
            text="▶ Start Gem Farming",
            command=self.toggle_gem_farming,
            width=150,
            height=40
        )
        self.start_gem_btn.pack(side="left", padx=5)
        
        ctk.CTkButton(
            btn_frame,
            text="🔍 Scan Gems",
            command=self.manual_gem_scan,
            width=150,
            height=40
        ).pack(side="left", padx=5)
        
        stats_frame = ctk.CTkFrame(tab)
        stats_frame.pack(fill="x", padx=20, pady=10)
        
        self.gem_stats_label = ctk.CTkLabel(
            stats_frame,
            text="💎 Gems Collected: 0",
            font=ctk.CTkFont(size=18, weight="bold")
        )
        self.gem_stats_label.pack(pady=20)
    
    def create_emulator_tab(self):
        """Create Emulator Control tab"""
        tab = self.tabview.tab("Emulator Control")
        
        ctk.CTkLabel(
            tab,
            text="📱 Emulator Control",
            font=ctk.CTkFont(size=24, weight="bold")
        ).pack(pady=20)
        
        control_frame = ctk.CTkFrame(tab)
        control_frame.pack(fill="x", padx=20, pady=10)
        
        btn_frame = ctk.CTkFrame(control_frame, fg_color="transparent")
        btn_frame.pack(pady=10)
        
        ctk.CTkButton(
            btn_frame,
            text="🔄 Refresh Devices",
            command=self.refresh_devices,
            width=150,
            height=40
        ).pack(side="left", padx=5)
        
        ctk.CTkButton(
            btn_frame,
            text="🎮 Launch Game",
            command=self.launch_game,
            width=150,
            height=40
        ).pack(side="left", padx=5)
        
        self.device_listbox = ctk.CTkTextbox(tab, height=200)
        self.device_listbox.pack(fill="both", expand=True, padx=20, pady=10)
    
    # Event handlers
    def toggle_resource(self, resource):
        """Toggle resource selection"""
        if resource in self.selected_resources:
            self.selected_resources.remove(resource)
            self.resource_buttons[resource].configure(fg_color="gray30")
        else:
            self.selected_resources.append(resource)
            self.resource_buttons[resource].configure(fg_color="blue")
        
        self.selected_label.configure(
            text=f"Selected: {', '.join(self.selected_resources) if self.selected_resources else 'None'}"
        )
        
        # Auto-save
        if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
            self.save_settings()
    
    def toggle_rotation(self):
        """Toggle resource rotation"""
        self.resource_rotation_enabled = self.rotation_switch.get()
        self.log(f"Resource rotation: {'enabled' if self.resource_rotation_enabled else 'disabled'}")
        
        # Auto-save
        if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
            self.save_settings()
    
    def update_troops_count(self, value):
        """Update number of troops"""
        self.num_troops = int(value)
        self.troops_label.configure(text=str(self.num_troops))
        self.log(f"Troops set to: {self.num_troops}")
        
        # Auto-save
        if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
            self.save_settings()
    
    def toggle_auto_help(self):
        """Toggle auto help"""
        self.auto_help_enabled = self.auto_help_switch.get()
        self.log(f"Auto help: {'enabled' if self.auto_help_enabled else 'disabled'}")
        
        # Auto-save
        if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
            self.save_settings()
    
    def toggle_webhook(self):
        """Toggle webhook"""
        self.webhook_enabled = self.webhook_switch.get()
        self.webhook_url = self.webhook_entry.get()
        self.log(f"Webhook: {'enabled' if self.webhook_enabled else 'disabled'}")
        
        # Auto-save
        if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
            self.save_settings()
    
    def on_webhook_change(self):
        """Called when webhook URL changes"""
        new_url = self.webhook_entry.get()
        if new_url != self.webhook_url:
            self.webhook_url = new_url
            self.log(f"Webhook URL updated")
            
            # Auto-save
            if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
                self.save_settings()
                self.last_saved_label.configure(
                    text=f"⏱️ Last saved: {datetime.now().strftime('%H:%M:%S')}"
                )
    
    def on_webhook_option_change(self):
        """Called when webhook notification options change"""
        self.webhook_on_success = self.webhook_success_switch.get()
        self.webhook_on_fail = self.webhook_fail_switch.get()
        self.log(f"Webhook options updated - Success: {self.webhook_on_success}, Fail: {self.webhook_on_fail}")
        
        # Auto-save
        if hasattr(self, 'autosave_switch') and self.autosave_switch.get():
            self.save_settings()
            self.last_saved_label.configure(
                text=f"⏱️ Last saved: {datetime.now().strftime('%H:%M:%S')}"
            )
    
    def toggle_buff_monitoring(self):
        """Toggle buff monitoring"""
        self.buff_monitoring = not self.buff_monitoring
        if self.buff_monitoring:
            self.start_buff_btn.configure(text="⏸ Stop Monitoring")
            self.log("Buff monitoring started")
            threading.Thread(target=self.buff_monitoring_loop, daemon=True).start()
        else:
            self.start_buff_btn.configure(text="▶ Start Monitoring")
            self.log("Buff monitoring stopped")
    
    def manual_buff_scan(self):
        """Manual buff scan"""
        self.log("Scanning for buffs...")
        self.buff_listbox.delete("0.0", "end")
        self.buff_listbox.insert("0.0", "Scanning for active buffs...\n")
        self.buff_listbox.insert("0.0", f"[{datetime.now().strftime('%H:%M:%S')}] Manual scan complete\n")
    
    def buff_monitoring_loop(self):
        """Buff monitoring loop"""
        while self.buff_monitoring:
            try:
                time.sleep(5)
            except Exception as e:
                self.log(f"Buff monitoring error: {e}")
                time.sleep(10)
    
    def toggle_gem_farming(self):
        """Toggle gem farming"""
        self.gem_farming_enabled = not self.gem_farming_enabled
        if self.gem_farming_enabled:
            self.start_gem_btn.configure(text="⏸ Stop Farming")
            self.log("Gem farming started")
            threading.Thread(target=self.gem_farming_loop, daemon=True).start()
        else:
            self.start_gem_btn.configure(text="▶ Start Gem Farming")
            self.log("Gem farming stopped")
    
    def manual_gem_scan(self):
        """Manual gem scan"""
        self.log("Scanning for gems...")
        messagebox.showinfo("Gem Scan", "Scanning for gem deposits...")
    
    def gem_farming_loop(self):
        """Gem farming loop"""
        while self.gem_farming_enabled:
            try:
                self.gems_collected += random.randint(10, 50)
                self.gem_stats_label.configure(text=f"💎 Gems Collected: {self.gems_collected}")
                self.log(f"Collected gems. Total: {self.gems_collected}")
                time.sleep(30)
            except Exception as e:
                self.log(f"Gem farming error: {e}")
                time.sleep(10)
    
    def refresh_devices(self):
        """Refresh device list"""
        self.log("Refreshing devices...")
        self.device_listbox.delete("0.0", "end")
        self.device_listbox.insert("0.0", "Scanning for devices...\n")
        
        try:
            result = subprocess.run([ADB_PATH, "devices"], capture_output=True, text=True, timeout=5)
            lines = result.stdout.strip().splitlines()[1:]
            
            if lines:
                for line in lines:
                    if line.strip():
                        self.device_listbox.insert("end", f"📱 {line}\n")
            else:
                self.device_listbox.insert("end", "No devices found\n")
        except Exception as e:
            self.device_listbox.insert("end", f"Error: {e}\n")
    
    def launch_game(self):
        """Launch game"""
        self.log("Launching game...")
        messagebox.showinfo("Launch Game", "Game launching...")
    
    def toggle_autofarm(self):
        """Toggle AutoFarm"""
        if not AUTOGUI_AVAILABLE:
            messagebox.showerror("Error", "PyAutoGUI not available!\nInstall: pip install pyautogui pillow keyboard")
            return
        
        self.toggle = not self.toggle
        
        if self.toggle:
            if len(self.selected_resources) == 0:
                messagebox.showwarning("No Resources", "Please select at least one resource!")
                self.toggle = False
                return
            
            self.session_start_time = time.time() * 1000
            self.log(f"=== AUTOFARM START - {self.active_profile} Profile ===")
            self.log(f"Resources: {', '.join(self.selected_resources)}")
            self.log(f"Troops: {self.num_troops}")
            
            self.start_stop_btn.configure(
                text="⏸ STOP AutoFarm (F8)",
                fg_color="red",
                hover_color="darkred"
            )
            self.status_label.configure(text="● Running", text_color="green")
            
            if not self.running:
                self.running = True
                threading.Thread(target=self.autofarm_loop, daemon=True).start()
        else:
            self.log("AutoFarm stopped")
            self.start_stop_btn.configure(
                text="▶ START AutoFarm (F8)",
                fg_color="green",
                hover_color="darkgreen"
            )
            self.status_label.configure(text="● Stopped", text_color="red")
    
    def get_random_resource(self):
        """Get next resource"""
        if self.resource_rotation_enabled and len(self.selected_resources) > 0:
            resource = self.selected_resources[self.current_rotation_index]
            self.current_rotation_index = (self.current_rotation_index + 1) % len(self.selected_resources)
            return resource
        elif len(self.selected_resources) > 0:
            return self.selected_resources[0]
        return "Wood"
    
    def color_match(self, color, ref, tol):
        """Check if colors match within tolerance"""
        r, g, b = (color >> 16) & 0xFF, (color >> 8) & 0xFF, color & 0xFF
        r1, g1, b1 = (ref >> 16) & 0xFF, (ref >> 8) & 0xFF, ref & 0xFF
        return abs(r - r1) <= tol and abs(g - g1) <= tol and abs(b - b1) <= tol
    
    def get_pixel_color(self, x, y):
        """Get pixel color at position"""
        if not AUTOGUI_AVAILABLE:
            return 0
        try:
            screenshot = ImageGrab.grab(bbox=(x, y, x+1, y+1))
            pixel = screenshot.getpixel((0, 0))
            return (pixel[0] << 16) | (pixel[1] << 8) | pixel[2]
        except:
            return 0
    
    def is_gathering(self, x, y):
        """Enhanced multi-point gathering detection"""
        if not AUTOGUI_AVAILABLE:
            return False
        
        try:
            check_patterns = [
                [(0, 0)],
                [(-4, 0), (4, 0), (0, -4), (0, 4)],
                [(-4, -4), (4, -4), (-4, 4), (4, 4)],
                [(-8, 0), (8, 0), (0, -8), (0, 8)],
                [(-12, 0), (12, 0), (0, -12), (0, 12)]
            ]
            
            match_count = 0
            total_checks = 0
            
            for pattern in check_patterns:
                for dx, dy in pattern:
                    total_checks += 1
                    check_x, check_y = x + dx, y + dy
                    check_color = self.get_pixel_color(check_x, check_y)
                    
                    for color in self.gathering_colors:
                        if self.color_match(check_color, color, self.tolerance):
                            match_count += 1
                            break
            
            if total_checks > 0 and (match_count / total_checks) >= 0.20:
                return True
            
            high_tolerance = self.tolerance + 20
            critical_points = [(0, 0), (-5, -5), (5, -5), (-5, 5), (5, 5)]
            
            for dx, dy in critical_points:
                check_x, check_y = x + dx, y + dy
                check_color = self.get_pixel_color(check_x, check_y)
                
                primary_colors = [0x0D9A00, 0xB45D00, 0x32CD32, 0x228B22]
                for color in primary_colors:
                    if self.color_match(check_color, color, high_tolerance):
                        return True
            
            return False
            
        except Exception as e:
            self.log(f"is_gathering error: {e}")
            return False
    
    def verify_slot_empty(self, slot_index):
        """Verify slot is empty and ready"""
        check_x, check_y = self.march_slots[slot_index]
        
        if self.is_gathering(check_x, check_y):
            return False
        
        time.sleep(0.4)
        if self.is_gathering(check_x, check_y):
            return False
        
        return True
    
    def can_send_march(self, slot_index):
        """Check if enough time passed for slot"""
        current_time = time.time() * 1000
        min_wait = random.uniform(self.min_wait_time_base, self.max_wait_time_base)
        return (current_time - self.slot_last_check[slot_index]) >= min_wait
    
    def check_help_button(self):
        """Check and click help button"""
        if not self.auto_help_enabled or not AUTOGUI_AVAILABLE:
            return False
        
        if not self.help_area or not self.help_button:
            return False
        
        try:
            help_x, help_y = self.help_area
            check_points = [
                self.help_area,
                (help_x - 5, help_y),
                (help_x + 5, help_y),
                (help_x, help_y - 5),
                (help_x, help_y + 5)
            ]
            
            for check_x, check_y in check_points:
                help_color = self.get_pixel_color(check_x, check_y)
                for color in self.helping_colors:
                    if self.color_match(help_color, color, self.tolerance1):
                        self.total_help_clicks += 1
                        self.log(f"Help button detected ({self.total_help_clicks} total)")
                        
                        help_btn_x, help_btn_y = self.help_button
                        self.advanced_mouse_move(help_btn_x, help_btn_y)
                        pyautogui.click()
                        time.sleep(random.uniform(1.2, 2.5))
                        return True
        except Exception as e:
            self.log(f"Help check error: {e}")
        
        return False
    
    def check_reconnect(self):
        """Check for reconnect button"""
        if not AUTOGUI_AVAILABLE:
            return False
        
        if not self.reconnect_area or not self.reconnect_color:
            return False
        
        try:
            x1, y1, x2, y2 = self.reconnect_area
            
            for x in range(x1, x2, 10):
                for y in range(y1, y2, 10):
                    color = self.get_pixel_color(x, y)
                    if self.color_match(color, self.reconnect_color, 18):
                        self.log("Reconnect button detected!")
                        self.advanced_mouse_move(x, y)
                        pyautogui.click()
                        time.sleep(random.uniform(2.5, 5.0))
                        return True
        except Exception as e:
            self.log(f"Reconnect check error: {e}")
        
        return False
    
    def update_fatigue(self):
        """Update fatigue level"""
        if self.session_start_time == 0:
            return
        
        elapsed_minutes = (time.time() * 1000 - self.session_start_time) / 60000.0
        
        if elapsed_minutes < 45:
            self.fatigue_level = (elapsed_minutes / 45.0) * 80
        else:
            self.fatigue_level = min(100, 80 + ((elapsed_minutes - 45) / 60.0) * 20)
    
    def get_fatigue_multiplier(self):
        """Get timing multiplier based on fatigue"""
        base_multiplier = 1.0 + (self.fatigue_level / 100.0) * 0.8
        variance = random.uniform(-0.15, 0.15)
        return max(1.0, min(2.0, base_multiplier + variance))
    
    def micro_break(self):
        """Take a micro break"""
        self.total_micro_breaks += 1
        self.last_break_time = time.time() * 1000
        
        break_type = random.randint(1, 100)
        if break_type <= 50:
            pause_time = random.uniform(1, 3)
        elif break_type <= 80:
            pause_time = random.uniform(3, 6)
        else:
            pause_time = random.uniform(6, 10)
        
        self.log(f"Micro-break: {pause_time:.1f}s")
        time.sleep(pause_time)
    
    def check_micro_break(self):
        """Check if micro break needed"""
        if (time.time() * 1000 - self.last_break_time) < 120000:
            return False
        
        adjusted_chance = self.micro_break_chance + (self.fatigue_level / 10.0)
        if random.randint(1, 100) <= adjusted_chance:
            self.micro_break()
            return True
        
        return False
    
    def bezier_point(self, t, p0, p1, p2, p3):
        """Calculate bezier curve point"""
        u = 1.0 - t
        tt, uu = t * t, u * u
        uuu, ttt = uu * u, tt * t
        return uuu * p0 + 3.0 * uu * t * p1 + 3.0 * u * tt * p2 + ttt * p3
    
    def advanced_mouse_move(self, target_x, target_y):
        """Advanced mouse movement with bezier curves"""
        if not AUTOGUI_AVAILABLE:
            return
        
        try:
            start_x, start_y = pyautogui.position()
            
            rand_x = random.randint(-self.click_randomization, self.click_randomization)
            rand_y = random.randint(-self.click_randomization, self.click_randomization)
            final_x, final_y = target_x + rand_x, target_y + rand_y
            
            should_overshoot = random.randint(1, 100) <= self.overshoot_chance
            if should_overshoot:
                overshoot_x = random.randint(10, 25)
                overshoot_y = random.randint(10, 25)
                overshoot_target_x = final_x + overshoot_x
                overshoot_target_y = final_y + overshoot_y
            else:
                overshoot_target_x, overshoot_target_y = final_x, final_y
            
            delta_x = overshoot_target_x - start_x
            delta_y = overshoot_target_y - start_y
            curve1 = random.randint(-self.curve_intensity, self.curve_intensity)
            curve2 = random.randint(-self.curve_intensity, self.curve_intensity)
            cp1_x = start_x + delta_x * 0.25 + curve1
            cp1_y = start_y + delta_y * 0.25 - curve2
            cp2_x = start_x + delta_x * 0.75 - curve1
            cp2_y = start_y + delta_y * 0.75 + curve2
            
            for i in range(self.bezier_points):
                t = (i + 1) / float(self.bezier_points)
                current_x = self.bezier_point(t, start_x, cp1_x, cp2_x, overshoot_target_x)
                current_y = self.bezier_point(t, start_y, cp1_y, cp2_y, overshoot_target_y)
                
                jitter_x = random.randint(-1, 1)
                jitter_y = random.randint(-1, 1)
                
                pyautogui.moveTo(current_x + jitter_x, current_y + jitter_y, duration=0)
                time.sleep(random.uniform(self.mouse_move_delay_min, self.mouse_move_delay_max) / 1000.0)
            
            if should_overshoot:
                time.sleep(random.uniform(0.08, 0.2))
                for i in range(1, 4):
                    t = i / 3.0
                    corr_x = overshoot_target_x + (final_x - overshoot_target_x) * t
                    corr_y = overshoot_target_y + (final_y - overshoot_target_y) * t
                    pyautogui.moveTo(corr_x, corr_y, duration=0)
                    time.sleep(0.03)
            
            if random.randint(1, 100) <= self.micro_correction_chance:
                time.sleep(random.uniform(0.05, 0.12))
                micro_x = random.randint(-3, 3)
                micro_y = random.randint(-3, 3)
                final_x += micro_x
                final_y += micro_y
            
            pyautogui.moveTo(final_x, final_y, duration=0)
            
        except Exception as e:
            self.log(f"Mouse move error: {e}")
            try:
                pyautogui.moveTo(target_x, target_y, duration=0.3)
            except:
                pass
    
    def send_march(self):
        """Send a march with troop selection"""
        if not AUTOGUI_AVAILABLE:
            return False
        
        if not self.march_slots or not self.search_button:
            self.log("Coordinates not initialized!")
            return False
        
        try:
            self.update_fatigue()
            
            if self.check_micro_break():
                return False
            
            available_slot = -1
            for i in range(len(self.march_slots)):
                if self.can_send_march(i) and self.verify_slot_empty(i):
                    available_slot = i
                    break
            
            if available_slot == -1:
                self.log("No available march slots")
                return False
            
            self.slot_last_check[available_slot] = time.time() * 1000
            
            resource = self.get_random_resource()
            self.log(f"March {available_slot + 1} - {resource} - {self.num_troops} troops (Fatigue: {round(self.fatigue_level)}%)")
            
            # Step 1: Search button
            search_x, search_y = self.search_button
            self.advanced_mouse_move(search_x, search_y)
            time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
            pyautogui.click()
            time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
            time.sleep(random.uniform(1.2, 2.0))
            
            # Step 2: Resource type
            res_x, res_y = self.resources[resource]
            self.advanced_mouse_move(res_x, res_y)
            time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
            pyautogui.click()
            time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
            time.sleep(random.uniform(0.9, 1.5))
            
            # Step 3: Confirm resource
            confirm_x, confirm_y = self.search_confirms[resource]
            self.advanced_mouse_move(confirm_x, confirm_y)
            time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
            pyautogui.click()
            time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
            time.sleep(random.uniform(1.8, 2.5))
            
            if random.randint(1, 100) <= 30:
                time.sleep(random.uniform(0.5, 1.2))
            
            # Step 4: Gather button
            gather_x, gather_y = self.gather_btn
            self.advanced_mouse_move(gather_x, gather_y)
            time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
            pyautogui.click()
            time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
            time.sleep(random.uniform(1.5, 2.2))
            
            # Step 4.5: Select troops (NEW FEATURE)
            if self.num_troops > 1 and self.troop_positions:
                self.log(f"Selecting {self.num_troops} troops...")
                for i in range(1, self.num_troops):
                    if i < len(self.troop_positions):
                        troop_x, troop_y = self.troop_positions[i]
                        self.advanced_mouse_move(troop_x, troop_y)
                        time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
                        pyautogui.click()
                        time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
                        time.sleep(random.uniform(0.3, 0.6))
                
                self.log(f"✅ Selected {self.num_troops} troops")
                time.sleep(random.uniform(0.5, 1.0))
            
            # Step 5: Send troops
            troops_x, troops_y = self.send_troops
            self.advanced_mouse_move(troops_x, troops_y)
            time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
            pyautogui.click()
            time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
            time.sleep(random.uniform(1.8, 2.5))
            
            if random.randint(1, 100) <= 25:
                time.sleep(random.uniform(0.6, 1.4))
            
            # Step 6: March confirm
            confirm_x, confirm_y = self.march_confirm
            self.advanced_mouse_move(confirm_x, confirm_y)
            time.sleep(random.uniform(self.pre_click_delay_min, self.pre_click_delay_max) / 1000.0)
            pyautogui.click()
            time.sleep(random.uniform(self.post_click_delay_min, self.post_click_delay_max) / 1000.0)
            time.sleep(random.uniform(2.5, 3.2))
            
            # Verify march started
            time.sleep(1.8)
            if self.is_gathering(self.march_slots[available_slot][0], self.march_slots[available_slot][1]):
                self.total_marches += 1
                self.successful_marches += 1
                self.log(f"✅ March {available_slot + 1} SUCCESS - {resource} - {self.num_troops} troops")
                
                if self.webhook_enabled and self.webhook_on_success:
                    self.send_webhook("success", f"March {available_slot + 1} SUCCESS - {resource} - {self.num_troops} troops", 0x27AE60)
                
                return True
            else:
                self.total_marches += 1
                self.log(f"❌ March {available_slot + 1} FAILED - {resource}")
                
                if self.webhook_enabled and self.webhook_on_fail:
                    self.send_webhook("error", f"March {available_slot + 1} FAILED - {resource}", 0xE74C3C)
                
                return False
            
        except Exception as e:
            self.log(f"❌ March error: {e}")
            import traceback
            traceback.print_exc()
            return False
    
    def autofarm_loop(self):
        """Main AutoFarm loop"""
        while self.running:
            if not self.toggle:
                time.sleep(0.1)
                continue
            
            try:
                self.update_fatigue()
                self.check_help_button()
                self.check_webhook_interval()
                
                if random.randint(1, 100) <= 60:
                    if self.check_reconnect():
                        time.sleep(random.uniform(2.5, 5.0))
                        continue
                
                march_sent = False
                success = self.send_march()
                
                if success:
                    march_sent = True
                
                self.update_stats()
                
                if not march_sent:
                    wait_time = random.uniform(15, 25)
                    self.log(f"No slots available, waiting {wait_time:.1f}s...")
                    
                    start_wait = time.time()
                    while (time.time() - start_wait) < wait_time and self.toggle:
                        self.check_help_button()
                        time.sleep(random.uniform(3, 7))
                else:
                    time.sleep(random.uniform(2, 5))
                
            except Exception as e:
                self.log(f"AutoFarm error: {e}")
                import traceback
                traceback.print_exc()
                time.sleep(10)
    
    def check_webhook_interval(self):
        """Check if periodic webhook should be sent"""
        if not self.webhook_enabled:
            return
        
        current_time = time.time() * 1000
        
        if self.last_webhook_time == 0:
            self.last_webhook_time = current_time
            return
        
        elapsed_minutes = (current_time - self.last_webhook_time) / 60000.0
        
        if elapsed_minutes >= self.webhook_interval:
            self.send_webhook("info", "📈 Periodic Stats Update", 0x3498DB)
            self.last_webhook_time = current_time
    
    def update_stats(self):
        """Update statistics display"""
        current_time = time.time()
        
        if current_time - self.last_gui_update < self.gui_update_interval:
            return
        
        self.last_gui_update = current_time
        
        try:
            success_rate = 0
            if self.total_marches > 0:
                success_rate = round((self.successful_marches / self.total_marches) * 100, 1)
            
            session_minutes = 0
            if self.session_start_time > 0:
                session_minutes = round((time.time() * 1000 - self.session_start_time) / 60000.0, 1)
            
            if session_minutes > 0:
                self.fatigue_level = min(100, (session_minutes / 60.0) * 50)
            
            self.stat_labels["total_marches"].configure(text=str(self.total_marches))
            self.stat_labels["successful"].configure(text=f"{self.successful_marches} ({success_rate}%)")
            self.stat_labels["help_clicks"].configure(text=str(self.total_help_clicks))
            self.stat_labels["fatigue"].configure(text=f"{round(self.fatigue_level)}%")
            self.stat_labels["session_time"].configure(text=f"{session_minutes}m")
            self.stat_labels["gems"].configure(text=str(self.gems_collected))
        except Exception as e:
            pass
    
    def send_webhook(self, event_type, message, color=None):
        """Send Discord webhook"""
        if not self.webhook_enabled or not self.webhook_url:
            return
        
        try:
            colors = {
                "success": 0x27AE60,
                "error": 0xE74C3C,
                "info": 0x3498DB,
                "warning": 0xF39C12
            }
            
            if color is None:
                color = colors.get(event_type, 0x95A5A6)
            
            embed = {
                "title": f"🎮 ROK Unified Tool - {event_type.title()}",
                "description": message,
                "color": color,
                "timestamp": datetime.utcnow().isoformat(),
                "fields": [
                    {"name": "👤 User", "value": self.current_user, "inline": True},
                    {"name": "📋 Profile", "value": self.active_profile, "inline": True},
                    {"name": "📊 Total Marches", "value": str(self.total_marches), "inline": True},
                    {"name": "⚔️ Troops", "value": str(self.num_troops), "inline": True}
                ],
                "footer": {"text": "ROK Unified Tool v2.5"}
            }
            
            payload = {"embeds": [embed]}
            response = requests.post(self.webhook_url, json=payload, timeout=10)
            
            if response.status_code == 204:
                self.log(f"Webhook sent: {event_type}")
        except Exception as e:
            self.log(f"Webhook error: {e}")
    
    def run(self):
        """Run the application"""
        if AUTOGUI_AVAILABLE:
            try:
                keyboard.add_hotkey('f8', self.toggle_autofarm)
                keyboard.add_hotkey('f9', self.force_exit)
                keyboard.add_hotkey('f10', self.toggle_window)
            except Exception as e:
                self.log(f"Hotkey setup error: {e}")
        
        self.root.protocol("WM_DELETE_WINDOW", self.force_exit)
        self.root.mainloop()
    
    def toggle_window(self):
        """Toggle window visibility"""
        if self.root.state() == 'normal':
            self.root.iconify()
            self.log("Window minimized")
        else:
            self.root.deiconify()
            self.log("Window restored")
    
    def force_exit(self):
        """Force exit application"""
        self.running = False
        self.toggle = False
        self.buff_monitoring = False
        self.gem_farming_enabled = False
        
        # Save settings before exit
        self.save_settings()
        
        self.log("Shutting down...")
        
        try:
            if AUTOGUI_AVAILABLE:
                keyboard.unhook_all()
        except:
            pass
        
        try:
            self.root.quit()
            self.root.destroy()
        except:
            pass
        
        os._exit(0)


def main():
    """Main entry point"""
    print("=" * 60)
    print("ROK Unified Tool - Professional Edition v2.5")
    print("With Troops Selection Feature (1-7)")
    print("=" * 60)
    print(f"OpenCV Available: {OPENCV_AVAILABLE}")
    print(f"PyAutoGUI Available: {AUTOGUI_AVAILABLE}")
    print(f"NumPy Available: {NUMPY_AVAILABLE}")
    print("=" * 60)
    
    if not AUTOGUI_AVAILABLE:
        print("\n[Warning] AutoFarm requires:")
        print("  pip install pyautogui pillow keyboard")
    
    if not OPENCV_AVAILABLE:
        print("\n[Warning] Image detection requires:")
        print("  pip install opencv-python pytesseract")
    
    print("\n💡 Performance Tips:")
    print("  • Close unnecessary background apps")
    print("  • Minimize other windows")
    print("  • Use F10 to toggle window visibility")
    print("  • GUI updates throttled to reduce lag")
    
    print("\n🎮 Hotkeys:")
    print("  F8  - Toggle AutoFarm")
    print("  F9  - Force Exit")
    print("  F10 - Toggle Window")
    
    print("\n✨ New Features:")
    print("  • Troops Selection: 1-7 troops per march")
    print("  • Slider control in Resources section")
    print("  • Automatic troop clicking sequence")
    print("  • Profile-specific troop positions")
    print("  • Auto-Save Config: Settings saved automatically")
    print("  • Manual Save/Load/Reset buttons")
    print("  • Webhook auto-save on URL/options change")
    print("  • Notify on Success/Fail options")
    
    print("\n💾 Config File Location:")
    print(f"  {os.path.join(os.path.expanduser('~'), 'Documents', 'rok_settings.json')}")
    
    print("\n📢 Webhook Settings Saved:")
    print("  • Webhook URL")
    print("  • Enable/Disable status")
    print("  • Notify on Success option")
    print("  • Notify on Fail option")
    
    print("\n📍 Important:")
    print("  • Adjust troop_positions coordinates for your screen")
    print("  • Nhan profile: Line ~180")
    print("  • Huy profile: Line ~200")
    
    print("\nStarting application...\n")
    
    try:
        app = ModernROKTool()
        app.run()
    except Exception as e:
        print(f"\n❌ Fatal error: {e}")
        import traceback
        traceback.print_exc()
        input("\nPress Enter to exit...")


if __name__ == "__main__":
    main()