import os
import sys
import subprocess
import threading
import time
import re
import random
import math
import tkinter as tk
from tkinter import ttk, messagebox
from datetime import datetime
import hashlib
import json
import requests

# Try to import optional dependencies
try:
    import cv2
    import pytesseract
    OPENCV_AVAILABLE = True
except ImportError:
    OPENCV_AVAILABLE = False
    print("[Warning] OpenCV/Tesseract not available - OCR features disabled")

try:
    from PIL import ImageGrab, Image
    import pyautogui
    import keyboard
    pyautogui.FAILSAFE = False
    AUTOGUI_AVAILABLE = True
except ImportError:
    AUTOGUI_AVAILABLE = False
    print("[Warning] PyAutoGUI/Keyboard not available - AutoFarm features disabled")

try:
    import numpy as np
    NUMPY_AVAILABLE = True
except ImportError:
    NUMPY_AVAILABLE = False

# Configuration
ADB_PATH = "adb\\adb.exe"
DATA_PATH = "data"
RESOURCE_PATH = "resource"
SCREENSHOT_PATH = "cache\\screenshot.png"
TESSERACT_PATH = r"tesseract-ocr\\tesseract.exe"

if OPENCV_AVAILABLE:
    pytesseract.pytesseract.tesseract_cmd = TESSERACT_PATH

class ROKUnifiedTool:
    def __init__(self):
        # Common settings
        self.logged_in = False
        self.current_user = None
        self.active_profile = "Nhan"
        self.config_file = os.path.join(os.path.expanduser("~"), "Documents", "rok_unified_config.json")
        self.log_file = os.path.join(os.path.expanduser("~"), "Documents", "ROK_Unified_Log.txt")
        
        # ADB/LDPlayer settings
        self.connected_devices = set()
        self.stop_gather_flag = False
        self.stop_clear_fog_flag = False
        
        # AutoFarm settings
        self.toggle = False
        self.running = False
        self.current_resource = "Wood"
        self.resource_rotation_enabled = False
        self.selected_resources = ["Wood"]
        self.current_rotation_index = 0
        self.auto_hide_enabled = True
        self.window_hidden = False

        # Timing parameters
        self.click_randomization = 12
        self.micro_correction_chance = 25
        self.overshoot_chance = 15
        self.human_delay_min = 100
        self.human_delay_max = 450
        self.action_delay_min = 1400
        self.action_delay_max = 3200
        self.wait_delay_min = 900
        self.wait_delay_max = 2200
        self.bezier_points = 8
        self.curve_intensity = 20
        self.mouse_move_delay_min = 15
        self.mouse_move_delay_max = 45
        
        # Session tracking
        self.session_start_time = 0
        self.session_actions_count = 0
        self.fatigue_level = 0
        self.last_break_time = 0
        self.micro_break_chance = 8
        self.total_marches = 0
        self.successful_marches = 0
        self.total_micro_breaks = 0
        self.total_help_clicks = 0
        
        # Color detection
        self.gathering_colors = [0x0D9A00, 0xB45D00, 0xFFFFFF, 0x32CD32, 0x228B22, 0x00FF00, 0x90EE90, 0x8B4513]
        self.tolerance = 30
        self.helping_colors = [0xFFF4E4, 0x34A501, 0xF7F6C1, 0xD77824, 0xE3775E, 0xE78167, 0xFCA593, 0xF89B8A, 0xEB8D7B, 0xD47968]
        self.tolerance1 = 10
        
        # Profile coordinates - Nhan
        self.nhan_march_slots = [(1884, 250), (1884, 330), (1884, 410), (1885, 485), (1884, 575)]
        self.nhan_reconnect_area = (841, 633, 1080, 682)
        self.nhan_reconnect_color = 0x00AEEF
        self.nhan_search_button = (1866, 905)
        self.nhan_search_confirms = {"Food": (761, 841), "Wood": (966, 842), "Stone": (1160, 842), "Gold": (1365, 837)}
        self.nhan_gather_btn = (623, 666)
        self.nhan_send_troops_btn = (1643, 318)
        self.nhan_march_confirm = (1262, 834)
        self.nhan_help_area = (1515, 926)
        self.nhan_help_button = (1539, 948)
        self.nhan_resources = {"Food": (763, 994), "Wood": (962, 994), "Stone": (1162, 994), "Gold": (1365, 994)}
        
        # Profile coordinates - Huy
        self.huy_march_slots = [(2831, 466), (2827, 579), (2830, 700), (2826, 820), (2829, 941)]
        self.huy_reconnect_area = (1273, 1048, 1595, 1107)
        self.huy_reconnect_color = 0x00AEEF
        self.huy_search_button = (2790, 1440)
        self.huy_search_confirms = {"Food": (1147, 1344), "Wood": (1445, 1362), "Stone": (1765, 1361), "Gold": (2069, 1342)}
        self.huy_gather_btn = (1894, 1102)
        self.huy_send_troops_btn = (2470, 560)
        self.huy_march_confirm = (1905, 1329)
        self.huy_help_area = (1515, 926)
        self.huy_help_button = (1539, 948)
        self.huy_resources = {"Food": (1140, 1586), "Wood": (1436, 1593), "Stone": (1720, 1581), "Gold": (2025, 1570)}
        
        # Active coordinates
        self.update_profile_coordinates()
        
        # Features
        self.auto_help_enabled = True
        self.slot_last_check = [0] * 5
        self.min_wait_time_base = 35000
        self.max_wait_time_base = 55000
        
        # Additional timing delays
        self.short_delay_min = 400
        self.short_delay_max = 1000
        self.medium_delay_min = 1200
        self.medium_delay_max = 2500
        self.long_delay_min = 2500
        self.long_delay_max = 5000
        
        # Webhook settings
        self.webhook_url = "https://discord.com/api/webhooks/1448573619663011944/MtSDLxx_sjh1oIh0Vg-x1kXOrWMq6ovbB8wGGZwDuoBodYlWejEwTuFbKOB7wLWf3nUD"
        self.webhook_enabled = False
        self.webhook_on_start = True
        self.webhook_on_stop = True
        self.webhook_on_success = False
        self.webhook_on_fail = False
        self.webhook_on_gather_start = True
        self.webhook_on_gather_complete = True
        self.webhook_on_clearfog_start = True
        self.webhook_on_clearfog_stop = True
        self.webhook_interval = 30
        self.last_webhook_time = 0
        
        # Emulator gathering stats
        self.emulator_marches_sent = 0
        self.emulator_gather_start_time = 0
        
        # GUI
        self.root = None
        self.menu_visible = False
        
        # Ensure directories
        self.ensure_directories()
        
    def hide_window(self):
        if self.root and not self.window_hidden:
            self.root.iconify()
            self.window_hidden = True
            self.log("Window hidden (auto-hide)")
    
    def show_window(self):
        if self.root and self.window_hidden:
            self.root.deiconify()
            self.root.lift()
            self.root.focus_force()
            self.window_hidden = False
            self.log("Window restored")
    
    def toggle_window_visibility(self):
        if self.window_hidden:
            self.show_window()
        else:
            self.hide_window()


    def ensure_directories(self):
        """Create required directories"""
        os.makedirs(os.path.dirname(SCREENSHOT_PATH), exist_ok=True)
        os.makedirs(DATA_PATH, exist_ok=True)
    
    def log(self, msg):
        """Log message to file"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        try:
            with open(self.log_file, 'a', encoding='utf-8') as f:
                f.write(f"[{timestamp}] {msg}\n")
        except Exception as e:
            # If file logging fails, at least print to console
            print(f"[{timestamp}] {msg}")
            print(f"Log error: {e}")
        
        # Always print to console as well
        print(f"[{timestamp}] {msg}")
    
    # ==================== Authentication ====================
    
    def load_saved_password(self, username):
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r') as f:
                    config = json.load(f)
                    return config.get(username.lower(), None)
        except:
            pass
        return None
    
    def save_password(self, username, password):
        try:
            config = {}
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r') as f:
                    config = json.load(f)
            password_hash = hashlib.sha256(password.encode()).hexdigest()
            config[username.lower()] = password_hash
            with open(self.config_file, 'w') as f:
                json.dump(config, f)
            return True
        except Exception as e:
            print(f"Error saving password: {e}")
            return False
    
    def verify_login(self, username, password):
        username = username.lower().strip()
        if username not in ['nhan', 'huy']:
            return False, "Invalid username. Use 'nhan' or 'huy'"
        password_hash = hashlib.sha256(password.encode()).hexdigest()
        saved_hash = self.load_saved_password(username)
        if saved_hash is None:
            self.save_password(username, password)
            return True, "Password saved successfully"
        elif saved_hash == password_hash:
            return True, "Login successful"
        else:
            return False, "Incorrect password"
    
    def perform_login(self, username, password):
        success, message = self.verify_login(username, password)
        if success:
            self.logged_in = True
            self.current_user = username.lower()
            self.active_profile = "Nhan" if self.current_user == 'nhan' else "Huy"
            self.update_profile_coordinates()
            self.log(f"User '{self.current_user}' logged in - Profile: {self.active_profile}")
            return True, message
        return False, message
    
    def update_profile_coordinates(self):
        if self.active_profile == "Nhan":
            self.march_slots = self.nhan_march_slots
            self.reconnect_area = self.nhan_reconnect_area
            self.reconnect_color = self.nhan_reconnect_color
            self.search_button = self.nhan_search_button
            self.search_confirms = self.nhan_search_confirms
            self.gather_btn = self.nhan_gather_btn
            self.send_troops_btn = self.nhan_send_troops_btn
            self.march_confirm = self.nhan_march_confirm
            self.help_area = self.nhan_help_area
            self.help_button = self.nhan_help_button
            self.resources = self.nhan_resources
            self.slot_last_check = [0, 0, 0, 0, 0]
        else:
            self.march_slots = self.huy_march_slots
            self.reconnect_area = self.huy_reconnect_area
            self.reconnect_color = self.huy_reconnect_color
            self.search_button = self.huy_search_button
            self.search_confirms = self.huy_search_confirms
            self.gather_btn = self.huy_gather_btn
            self.send_troops_btn = self.huy_send_troops_btn
            self.march_confirm = self.huy_march_confirm
            self.help_area = self.huy_help_area
            self.help_button = self.huy_help_button
            self.resources = self.huy_resources
            self.slot_last_check = [0, 0, 0, 0, 0]
    
    # ==================== ADB/LDPlayer Functions ====================
    
    def get_ldplayer_devices(self):
        try:
            result = subprocess.run([ADB_PATH, "devices"], capture_output=True, text=True, timeout=5)
            lines = result.stdout.strip().splitlines()[1:]
            devices = []
            for line in lines:
                if not line.strip():
                    continue
                parts = line.split()
                device_id = parts[0]
                if device_id.startswith("emulator-"):
                    devices.append(device_id)
            return devices
        except Exception as e:
            self.log(f"Error getting devices: {e}")
            return []
    
    def list_devices(self):
        devices = self.get_ldplayer_devices()
        data = []
        for dev in devices:
            status = "online" if dev in self.connected_devices else "offline"
            data.append((dev, status))
        return data
    
    def connect_device(self, device_id):
        try:
            port_num = int(device_id.split("-")[-1]) + 1
            ip_port = f"127.0.0.1:{port_num}"
            result = subprocess.run([ADB_PATH, "connect", ip_port], capture_output=True, text=True, timeout=10)
            if "connected" in result.stdout.lower() or "already" in result.stdout.lower():
                self.connected_devices.add(device_id)
                return True, "Connected"
            return False, result.stdout.strip()
        except Exception as e:
            return False, str(e)
    
    def disconnect_device(self, device_id):
        try:
            port_num = int(device_id.split("-")[-1]) + 1
            ip_port = f"127.0.0.1:{port_num}"
            subprocess.run([ADB_PATH, "disconnect", ip_port],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5)
            self.connected_devices.discard(device_id)
            return True, "Disconnected"
        except Exception as e:
            return False, str(e)
    
    def launch_game_on_device(self, device_id, package_name):
        try:
            subprocess.run([ADB_PATH, "-s", device_id, "shell", "monkey",
                           "-p", package_name, "-c", "android.intent.category.LAUNCHER", "1"],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            return True
        except:
            return False
    
    def close_game_on_device(self, device_id, package_name):
        try:
            subprocess.run([ADB_PATH, "-s", device_id, "shell", "am", "force-stop", package_name],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            return True
        except:
            return False
    
    # ADB Helper Functions
    def adb_screencap(self, device_id, output=SCREENSHOT_PATH):
        try:
            subprocess.run([ADB_PATH, "-s", device_id, "shell", "screencap", "-p", "/sdcard/screen.png"],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            subprocess.run([ADB_PATH, "-s", device_id, "pull", "/sdcard/screen.png", output],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
        except Exception as e:
            self.log(f"Screenshot error: {e}")
    
    def adb_tap(self, device_id, x, y):
        try:
            subprocess.run([ADB_PATH, "-s", device_id, "shell", "input", "tap", str(x), str(y)],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5)
        except Exception as e:
            self.log(f"Tap error: {e}")
    
    def find_image(self, target_path, screenshot_path=SCREENSHOT_PATH, threshold=0.85):
        if not OPENCV_AVAILABLE:
            return None
        try:
            if not os.path.exists(target_path):
                return None
            img_rgb = cv2.imread(screenshot_path)
            template = cv2.imread(target_path)
            if img_rgb is None or template is None:
                return None
            res = cv2.matchTemplate(img_rgb, template, cv2.TM_CCOEFF_NORMED)
            _, max_val, _, max_loc = cv2.minMaxLoc(res)
            if max_val >= threshold:
                center_x = int(max_loc[0] + template.shape[1] / 2)
                center_y = int(max_loc[1] + template.shape[0] / 2)
                return (center_x, center_y)
        except Exception as e:
            self.log(f"Image matching error: {e}")
        return None
    
    def convert_to_number(self, text):
        if not text:
            return 0
        text = text.upper().replace(" ", "").replace(",", "")
        match = re.match(r"(\d+(\.\d+)?)([KMB]?)", text)
        if not match:
            return 0
        num = float(match.group(1))
        suffix = match.group(3)
        if suffix == "K":
            num *= 1_000
        elif suffix == "M":
            num *= 1_000_000
        elif suffix == "B":
            num *= 1_000_000_000
        return int(num)
    
    def ocr_resources_auto(self, image_path):
        if not OPENCV_AVAILABLE:
            return {}
        try:
            img = cv2.imread(image_path)
            if img is None:
                return {}
            h, w, _ = img.shape
            x1, x2 = int(w * 0.63), int(w * 0.92)
            start_y = int(h * 0.33)
            row_height = int(h * 0.095)
            crops = {}
            keys = ["Food", "Wood", "Stone", "Gold"]
            for i, key in enumerate(keys):
                y1 = start_y + i * row_height
                y2 = y1 + row_height
                crop = img[y1:y2, x1:x2]
                gray = cv2.cvtColor(crop, cv2.COLOR_BGR2GRAY)
                gray = cv2.resize(gray, None, fx=2, fy=2, interpolation=cv2.INTER_CUBIC)
                _, thresh = cv2.threshold(gray, 160, 255, cv2.THRESH_BINARY)
                text = pytesseract.image_to_string(
                    thresh,
                    config="--psm 7 -c tessedit_char_whitelist=0123456789.,KMB"
                ).strip()
                match = re.search(r"[\d,]+(\.\d+)?[KMB]?", text)
                value = match.group(0) if match else text
                crops[key] = value
            return crops
        except Exception as e:
            self.log(f"OCR error: {e}")
            return {}
    
    def handle_disconnect_emulator(self, device_id, paths):
        if self.stop_gather_flag:
            return False
        try:
            self.adb_screencap(device_id)
            if self.find_image(paths["disconnect"], screenshot_path=SCREENSHOT_PATH, threshold=0.9):
                confirm_coord = self.find_image(paths["confirm"], screenshot_path=SCREENSHOT_PATH)
                if confirm_coord:
                    self.adb_tap(device_id, *confirm_coord)
                    time.sleep(30)
                else:
                    time.sleep(30)
        except Exception as e:
            self.log(f"Disconnect handling error: {e}")
        return True
    
    # Gather RSS Thread
    def gather_rss_thread(self, device_id, max_marches=6):
        try:
            self.stop_gather_flag = False
            self.emulator_marches_sent = 0
            self.emulator_gather_start_time = time.time()
            
            paths = {name: os.path.join(DATA_PATH, f"{name}.png") for name in
                     ["home", "map", "item", "task", "info", "exit", "find",
                      "food", "wood", "stone", "gold", "up", "down",
                      "search", "gather", "newtroop", "march",
                      "disconnect", "confirm"]}
            
            self.update_gather_log("🌸 Bắt đầu Thu thập Tài nguyên 🌸")
            self.log(f"=== GATHER RSS START - Device: {device_id} - Max Marches: {max_marches} ===")
            
            # Send webhook notification
            if self.webhook_enabled and self.webhook_on_gather_start:
                self.send_webhook("info", f"🌾 Gather RSS Started\n**Device:** {device_id}\n**Max Marches:** {max_marches}", 0x3498DB)
        except Exception as e:
            self.log(f"Gather thread initialization error: {e}")
            print(f"Gather thread initialization error: {e}")
            return
        
        try:
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            if home_coord := self.find_image(paths["home"], threshold=0.9):
                self.update_gather_log("Đang trở về thành phố...")
                self.adb_tap(device_id, *home_coord)
                time.sleep(5)
            else:
                self.update_gather_log("Đã ở trong thành phố.")
            
            time.sleep(5)
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            self.update_gather_log("Đang mở túi đồ...")
            item_coord = self.find_image(paths["item"])
            if not item_coord:
                self.update_gather_log("Không tìm thấy túi đồ, đang mở task và thử lại...")
                if task_coord := self.find_image(paths["task"]):
                    self.adb_tap(device_id, *task_coord)
                    time.sleep(5)
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    self.adb_screencap(device_id)
                    item_coord = self.find_image(paths["item"])
                if not item_coord:
                    self.update_gather_log("Không thể mở túi đồ!")
                    if self.webhook_enabled and self.webhook_on_fail:
                        self.send_webhook("error", f"❌ Gather RSS Failed\n**Reason:** Cannot open item bag", 0xE74C3C)
                    return
            
            self.adb_tap(device_id, *item_coord)
            time.sleep(5)
            
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            self.update_gather_log("Đang mở bảng tài nguyên...")
            if info_coord := self.find_image(paths["info"]):
                self.adb_tap(device_id, *info_coord)
                time.sleep(5)
            else:
                self.update_gather_log("Không tìm thấy nút thông tin!")
                if self.webhook_enabled and self.webhook_on_fail:
                    self.send_webhook("error", f"❌ Gather RSS Failed\n**Reason:** Cannot find info button", 0xE74C3C)
                return
            
            self.update_gather_log("Đang đọc số liệu tài nguyên...")
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            resources = self.ocr_resources_auto(SCREENSHOT_PATH)
            self.update_gather_log(f"Tài nguyên: {resources}")
            numeric_resources = {k: self.convert_to_number(v) for k, v in resources.items()}
            sorted_res = sorted(numeric_resources.items(), key=lambda x: x[1])
            
            # Send resource info via webhook
            if self.webhook_enabled:
                resource_text = "\n".join([f"**{k}:** {v}" for k, v in resources.items()])
                self.send_webhook("info", f"📊 Resources Detected\n{resource_text}", 0x9B59B6)
            
            self.update_gather_log("Đang trở về bản đồ...")
            for _ in range(2):
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                if exit_coord := self.find_image(paths["exit"]):
                    self.adb_tap(device_id, *exit_coord)
                    time.sleep(2)
                    self.adb_screencap(device_id)
            
            if map_coord := self.find_image(paths["map"]):
                self.adb_tap(device_id, *map_coord)
            time.sleep(5)
            
            count = 0
            while count < max_marches and not self.stop_gather_flag:
                res_name, res_value = sorted_res[count % len(sorted_res)]
                if res_value == 0:
                    self.update_gather_log(f"Không tìm thấy {res_name}, bỏ qua...")
                    count += 1
                    continue
                
                self.update_gather_log(f"Đạo quân {count + 1}/{max_marches} | Thu thập {res_name}")
                
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                
                self.adb_screencap(device_id)
                if not (find_coord := self.find_image(paths["find"])):
                    self.update_gather_log("Không tìm thấy nút tìm kiếm!")
                    break
                self.adb_tap(device_id, *find_coord)
                time.sleep(5)
                
                self.update_gather_log(f"Chọn {res_name}...")
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                
                self.adb_screencap(device_id)
                if not (res_coord := self.find_image(paths[res_name.lower()])):
                    self.update_gather_log(f"Không tìm thấy {res_name}!")
                    break
                self.adb_tap(device_id, *res_coord)
                time.sleep(5)
                
                self.update_gather_log("Đang tăng level mỏ...")
                for _ in range(6):
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    self.adb_screencap(device_id)
                    if up_coord := self.find_image(paths["up"]):
                        self.adb_tap(device_id, *up_coord)
                        time.sleep(0.25)
                
                self.update_gather_log("Đang tìm mỏ...")
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                
                self.adb_screencap(device_id)
                if not (search_coord := self.find_image(paths["search"])):
                    self.update_gather_log("Không thấy nút tìm mỏ!")
                    break
                self.adb_tap(device_id, *search_coord)
                
                found_gather = False
                max_attempts = 6
                for attempt in range(max_attempts):
                    if self.stop_gather_flag:
                        self.update_gather_log("Đã dừng thu thập tài nguyên!")
                        return
                    
                    time.sleep(5)
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    
                    self.adb_screencap(device_id)
                    if gather_coord := self.find_image(paths["gather"]):
                        self.adb_tap(device_id, *gather_coord)
                        found_gather = True
                        self.update_gather_log("Tìm thấy mỏ, tiến hành thu thập...")
                        break
                    else:
                        self.update_gather_log(f"Đang giảm level mỏ và tìm lại... ({attempt + 2}/{max_attempts})")
                        if down_coord := self.find_image(paths["down"]):
                            self.adb_tap(device_id, *down_coord)
                            time.sleep(0.25)
                        
                        if not self.handle_disconnect_emulator(device_id, paths):
                            return
                        
                        self.adb_screencap(device_id)
                        if search_coord := self.find_image(paths["search"]):
                            self.adb_tap(device_id, *search_coord)
                        else:
                            self.update_gather_log("Không tìm thấy nút tìm mỏ để thử lại!")
                            break
                
                if found_gather:
                    self.update_gather_log("Đang kiểm tra đạo quân...")
                    time.sleep(5)
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    
                    self.adb_screencap(device_id)
                    if newtroop_coord := self.find_image(paths["newtroop"]):
                        self.update_gather_log("Còn đạo quân, tiến hành gửi quân đi thu thập...")
                        self.adb_tap(device_id, *newtroop_coord)
                        time.sleep(5)
                        
                        if not self.handle_disconnect_emulator(device_id, paths):
                            return
                        
                        self.adb_screencap(device_id)
                        if march_coord := self.find_image(paths["march"]):
                            self.adb_tap(device_id, *march_coord)
                            self.update_gather_log("Đã gửi quân đi thu thập!")
                            self.emulator_marches_sent += 1
                            time.sleep(5)
                            count += 1
                            
                            # Send success webhook for each march
                            if self.webhook_enabled and self.webhook_on_success:
                                self.send_webhook("success", f"✅ March {count} Sent\n**Resource:** {res_name}\n**Device:** {device_id}", 0x27AE60)
                        else:
                            self.update_gather_log("Không thể gửi quân!")
                            if self.webhook_enabled and self.webhook_on_fail:
                                self.send_webhook("error", f"❌ Failed to send march {count + 1}", 0xE74C3C)
                            return
                    else:
                        self.update_gather_log("Hết đạo quân trống. Kết thúc!")
                        break
                else:
                    self.update_gather_log(f"Không tìm thấy mỏ {res_name}, chuyển sang lượt sau...")
                    count += 1
            
            # Calculate session time
            session_time = round((time.time() - self.emulator_gather_start_time) / 60.0, 1)
            
            if count >= max_marches:
                self.update_gather_log(f"Đã gửi đủ {max_marches} đạo quân. Hoàn thành!")
                self.log(f"Gather RSS completed: {self.emulator_marches_sent}/{max_marches} marches sent")
                
                # Send completion webhook
                if self.webhook_enabled and self.webhook_on_gather_complete:
                    self.send_webhook("success", f"🎉 Gather RSS Complete!\n**Marches Sent:** {self.emulator_marches_sent}/{max_marches}\n**Device:** {device_id}\n**Time:** {session_time} min", 0x27AE60)
            else:
                self.update_gather_log("Đã dừng thu thập tài nguyên!")
                self.log(f"Gather RSS stopped: {self.emulator_marches_sent}/{max_marches} marches sent")
                
                if self.webhook_enabled and self.webhook_on_stop:
                    self.send_webhook("warning", f"⏸️ Gather RSS Stopped\n**Marches Sent:** {self.emulator_marches_sent}/{max_marches}\n**Device:** {device_id}\n**Time:** {session_time} min", 0xF39C12)
        except Exception as e:
            error_msg = f"Lỗi: {str(e)}"
            self.update_gather_log(error_msg)
            self.log(f"Gather thread error: {e}")
            print(f"Gather thread error: {e}")
            import traceback
            traceback.print_exc()
            
            if self.webhook_enabled and self.webhook_on_fail:
                try:
                    self.send_webhook("error", f"❌ Gather RSS Error\n**Device:** {device_id}\n**Error:** {str(e)}", 0xE74C3C)
                except:
                    pass
        try:
            # Ensure buttons are re-enabled
            if self.root and hasattr(self, 'start_gather_btn'):
                try:
                    self.root.after(0, lambda: self.start_gather_btn.config(state=tk.NORMAL))
                    self.root.after(0, lambda: self.stop_gather_btn.config(state=tk.DISABLED))
                except Exception as e:
                    print(f"Button update error: {e}")
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            if home_coord := self.find_image(paths["home"], threshold=0.9):
                self.update_gather_log("Đang trở về thành phố...")
                self.adb_tap(device_id, *home_coord)
                time.sleep(5)
            else:
                self.update_gather_log("Đã ở trong thành phố.")
            
            time.sleep(5)
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            self.update_gather_log("Đang mở túi đồ...")
            item_coord = self.find_image(paths["item"])
            if not item_coord:
                self.update_gather_log("Không tìm thấy túi đồ, đang mở task và thử lại...")
                if task_coord := self.find_image(paths["task"]):
                    self.adb_tap(device_id, *task_coord)
                    time.sleep(5)
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    self.adb_screencap(device_id)
                    item_coord = self.find_image(paths["item"])
                if not item_coord:
                    self.update_gather_log("Không thể mở túi đồ!")
                    return
            
            self.adb_tap(device_id, *item_coord)
            time.sleep(5)
            
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            self.update_gather_log("Đang mở bảng tài nguyên...")
            if info_coord := self.find_image(paths["info"]):
                self.adb_tap(device_id, *info_coord)
                time.sleep(5)
            else:
                self.update_gather_log("Không tìm thấy nút thông tin!")
                return
            
            self.update_gather_log("Đang đọc số liệu tài nguyên...")
            if not self.handle_disconnect_emulator(device_id, paths):
                return
            
            self.adb_screencap(device_id)
            resources = self.ocr_resources_auto(SCREENSHOT_PATH)
            self.update_gather_log(f"Tài nguyên: {resources}")
            numeric_resources = {k: self.convert_to_number(v) for k, v in resources.items()}
            sorted_res = sorted(numeric_resources.items(), key=lambda x: x[1])
            
            self.update_gather_log("Đang trở về bản đồ...")
            for _ in range(2):
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                if exit_coord := self.find_image(paths["exit"]):
                    self.adb_tap(device_id, *exit_coord)
                    time.sleep(2)
                    self.adb_screencap(device_id)
            
            if map_coord := self.find_image(paths["map"]):
                self.adb_tap(device_id, *map_coord)
            time.sleep(5)
            
            count = 0
            while count < max_marches and not self.stop_gather_flag:
                res_name, res_value = sorted_res[count % len(sorted_res)]
                if res_value == 0:
                    self.update_gather_log(f"Không tìm thấy {res_name}, bỏ qua...")
                    count += 1
                    continue
                
                self.update_gather_log(f"Đạo quân {count + 1}/{max_marches} | Thu thập {res_name}")
                
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                
                self.adb_screencap(device_id)
                if not (find_coord := self.find_image(paths["find"])):
                    self.update_gather_log("Không tìm thấy nút tìm kiếm!")
                    return
                self.adb_tap(device_id, *find_coord)
                time.sleep(5)
                
                self.update_gather_log(f"Chọn {res_name}...")
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                
                self.adb_screencap(device_id)
                if not (res_coord := self.find_image(paths[res_name.lower()])):
                    self.update_gather_log(f"Không tìm thấy {res_name}!")
                    return
                self.adb_tap(device_id, *res_coord)
                time.sleep(5)
                
                self.update_gather_log("Đang tăng level mỏ...")
                for _ in range(6):
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    self.adb_screencap(device_id)
                    if up_coord := self.find_image(paths["up"]):
                        self.adb_tap(device_id, *up_coord)
                        time.sleep(0.25)
                
                self.update_gather_log("Đang tìm mỏ...")
                if not self.handle_disconnect_emulator(device_id, paths):
                    return
                
                self.adb_screencap(device_id)
                if not (search_coord := self.find_image(paths["search"])):
                    self.update_gather_log("Không thấy nút tìm mỏ!")
                    return
                self.adb_tap(device_id, *search_coord)
                
                found_gather = False
                max_attempts = 6
                for attempt in range(max_attempts):
                    if self.stop_gather_flag:
                        self.update_gather_log("Đã dừng thu thập tài nguyên!")
                        return
                    
                    time.sleep(5)
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    
                    self.adb_screencap(device_id)
                    if gather_coord := self.find_image(paths["gather"]):
                        self.adb_tap(device_id, *gather_coord)
                        found_gather = True
                        self.update_gather_log("Tìm thấy mỏ, tiến hành thu thập...")
                        break
                    else:
                        self.update_gather_log(f"Đang giảm level mỏ và tìm lại... ({attempt + 2}/{max_attempts})")
                        if down_coord := self.find_image(paths["down"]):
                            self.adb_tap(device_id, *down_coord)
                            time.sleep(0.25)
                        
                        if not self.handle_disconnect_emulator(device_id, paths):
                            return
                        
                        self.adb_screencap(device_id)
                        if search_coord := self.find_image(paths["search"]):
                            self.adb_tap(device_id, *search_coord)
                        else:
                            self.update_gather_log("Không tìm thấy nút tìm mỏ để thử lại!")
                            break
                
                if found_gather:
                    self.update_gather_log("Đang kiểm tra đạo quân...")
                    time.sleep(5)
                    if not self.handle_disconnect_emulator(device_id, paths):
                        return
                    
                    self.adb_screencap(device_id)
                    if newtroop_coord := self.find_image(paths["newtroop"]):
                        self.update_gather_log("Còn đạo quân, tiến hành gửi quân đi thu thập...")
                        self.adb_tap(device_id, *newtroop_coord)
                        time.sleep(5)
                        
                        if not self.handle_disconnect_emulator(device_id, paths):
                            return
                        
                        self.adb_screencap(device_id)
                        if march_coord := self.find_image(paths["march"]):
                            self.adb_tap(device_id, *march_coord)
                            self.update_gather_log("Đã gửi quân đi thu thập!")
                            time.sleep(5)
                            count += 1
                        else:
                            self.update_gather_log("Không thể gửi quân!")
                            return
                    else:
                        self.update_gather_log("Hết đạo quân trống. Kết thúc!")
                        return
                else:
                    self.update_gather_log(f"Không tìm thấy mỏ {res_name}, chuyển sang lượt sau...")
                    count += 1
            
            if count >= max_marches:
                self.update_gather_log(f"Đã gửi đủ {max_marches} đạo quân. Hoàn thành!")
            else:
                self.update_gather_log("Đã dừng thu thập tài nguyên!")
        except Exception as e:
            self.update_gather_log(f"Lỗi: {str(e)}")
            self.log(f"Gather thread error: {e}")
    
    # Clear Fog Thread
    def clear_fog_thread(self, device_id):
        try:
            self.stop_clear_fog_flag = False
            clearfog_start_time = time.time()
            clearfog_actions = 0
            
            self.log(f"=== CLEAR FOG START - Device: {device_id} ===")
            
            # Send webhook notification
            if self.webhook_enabled and self.webhook_on_clearfog_start:
                self.send_webhook("info", f"🗺️ Clear Fog Started\n**Device:** {device_id}", 0x3498DB)
        except Exception as e:
            self.log(f"Clear fog thread initialization error: {e}")
            print(f"Clear fog thread initialization error: {e}")
            return
        
        try:
            templates = {}
            for file in os.listdir(DATA_PATH):
                path = os.path.join(DATA_PATH, file)
                if file.endswith(".png") and os.path.isfile(path):
                    if OPENCV_AVAILABLE:
                        templates[file] = cv2.imread(path)
            
            def adb_screencap_local(device_id, output=SCREENSHOT_PATH):
                try:
                    with open(output, "wb") as f:
                        subprocess.run(
                            [ADB_PATH, "-s", device_id, "exec-out", "screencap", "-p"],
                            stdout=f, stderr=subprocess.DEVNULL, timeout=10
                        )
                except Exception as e:
                    self.log(f"Screenshot error: {e}")
            
            def adb_tap_local(device_id, x, y):
                try:
                    subprocess.run(
                        [ADB_PATH, "-s", device_id, "shell", "input", "tap", str(x), str(y)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=5
                    )
                except Exception as e:
                    self.log(f"Tap error: {e}")
            
            def find_image_local(filename, screenshot_path=SCREENSHOT_PATH, threshold=0.85):
                if not OPENCV_AVAILABLE:
                    return None
                try:
                    if filename not in templates:
                        return None
                    img_rgb = cv2.imread(screenshot_path)
                    template = templates[filename]
                    if img_rgb is None or template is None:
                        return None
                    res = cv2.matchTemplate(img_rgb, template, cv2.TM_CCOEFF_NORMED)
                    _, max_val, _, max_loc = cv2.minMaxLoc(res)
                    if max_val >= threshold:
                        cx = int(max_loc[0] + template.shape[1] / 2)
                        cy = int(max_loc[1] + template.shape[0] / 2)
                        return (cx, cy)
                except Exception as e:
                    self.log(f"Image matching error: {e}")
                return None
            
            def wait_and_click(filename, must=True, delay=1, threshold=0.85):
                while not self.stop_clear_fog_flag:
                    adb_screencap_local(device_id)
                    coord = find_image_local(filename, threshold=threshold)
                    if coord:
                        adb_tap_local(device_id, *coord)
                        time.sleep(delay)
                        return True
                    if not must:
                        return False
                    time.sleep(0.3)
                return False
            
            self.update_clearfog_log("🌸 Bắt đầu Clear Fog 🌸")
            
            while not self.stop_clear_fog_flag:
                adb_screencap_local(device_id)
                if (coord := find_image_local("home.png")):
                    adb_tap_local(device_id, *coord)
                    time.sleep(1.5)
                elif (coord := find_image_local("map.png")):
                    adb_tap_local(device_id, *coord)
                    time.sleep(1.5)
                    adb_screencap_local(device_id)
                    if (coord2 := find_image_local("home.png")):
                        adb_tap_local(device_id, *coord2)
                        time.sleep(1.5)
                
                adb_screencap_local(device_id)
                target = None
                for i in range(1, 4):
                    coord = find_image_local(f"{i}.png")
                    if coord:
                        target = coord
                        break
                if not target:
                    continue
                
                adb_tap_local(device_id, *target)
                time.sleep(1.5)
                wait_and_click("scout.png", must=False, delay=1.5)
                wait_and_click("explore.png", must=True, delay=1.5)
                
                adb_screencap_local(device_id)
                if not find_image_local("selected.png"):
                    if (coord := find_image_local("notselected.png")):
                        adb_tap_local(device_id, *coord)
                        time.sleep(0.8)
                
                wait_and_click("explore.png", must=True, delay=2)
                wait_and_click("send.png", must=True, delay=1.5)
                
                clearfog_actions += 1
                self.update_clearfog_log(f"Completed {clearfog_actions} fog clears")
                
                # Send periodic webhook updates
                if self.webhook_enabled and clearfog_actions % 10 == 0:
                    session_time = round((time.time() - clearfog_start_time) / 60.0, 1)
                    self.send_webhook("info", f"🗺️ Clear Fog Progress\n**Actions:** {clearfog_actions}\n**Time:** {session_time} min\n**Device:** {device_id}", 0x3498DB)
            
            # Calculate session time
            session_time = round((time.time() - clearfog_start_time) / 60.0, 1)
            
            self.update_clearfog_log("🛑 Đã dừng Clear Fog!")
            self.log(f"Clear Fog stopped: {clearfog_actions} actions in {session_time} min")
            
            # Send stop webhook
            if self.webhook_enabled and self.webhook_on_clearfog_stop:
                self.send_webhook("warning", f"⏸️ Clear Fog Stopped\n**Actions:** {clearfog_actions}\n**Time:** {session_time} min\n**Device:** {device_id}", 0xF39C12)
        except Exception as e:
            error_msg = f"Lỗi: {str(e)}"
            self.update_clearfog_log(error_msg)
            self.log(f"Clear fog thread error: {e}")
            print(f"Clear fog thread error: {e}")
            import traceback
            traceback.print_exc()
            
            if self.webhook_enabled and self.webhook_on_fail:
                try:
                    self.send_webhook("error", f"❌ Clear Fog Error\n**Device:** {device_id}\n**Error:** {str(e)}", 0xE74C3C)
                except:
                    pass
        finally:
            # Ensure buttons are re-enabled
            if self.root and hasattr(self, 'start_clearfog_btn'):
                try:
                    self.root.after(0, lambda: self.start_clearfog_btn.config(state=tk.NORMAL))
                    self.root.after(0, lambda: self.stop_clearfog_btn.config(state=tk.DISABLED))
                except Exception as e:
                    print(f"Button update error: {e}")
    
    # ==================== AutoFarm Functions ====================
    
    def color_match(self, color, ref, tol):
        r, g, b = (color >> 16) & 0xFF, (color >> 8) & 0xFF, color & 0xFF
        r1, g1, b1 = (ref >> 16) & 0xFF, (ref >> 8) & 0xFF, ref & 0xFF
        return abs(r - r1) <= tol and abs(g - g1) <= tol and abs(b - b1) <= tol
    
    def get_pixel_color(self, x, y):
        if not AUTOGUI_AVAILABLE:
            return 0
        screenshot = ImageGrab.grab(bbox=(x, y, x+1, y+1))
        pixel = screenshot.getpixel((0, 0))
        return (pixel[0] << 16) | (pixel[1] << 8) | pixel[2]
    
    def update_fatigue(self):
        if self.session_start_time == 0:
            return
        elapsed_minutes = (time.time() * 1000 - self.session_start_time) / 60000.0
        if elapsed_minutes < 45:
            self.fatigue_level = (elapsed_minutes / 45.0) * 80
        else:
            self.fatigue_level = min(100, 80 + ((elapsed_minutes - 45) / 60.0) * 20)
        if self.session_actions_count > 50:
            self.fatigue_level = min(100, self.fatigue_level + (self.session_actions_count - 50) / 10.0)
    
    def get_fatigue_multiplier(self):
        base_multiplier = 1.0 + (self.fatigue_level / 100.0) * 0.8
        variance = random.uniform(-0.15, 0.15)
        return max(1.0, min(2.0, base_multiplier + variance))
    
    def bezier_point(self, t, p0, p1, p2, p3):
        u = 1.0 - t
        tt, uu = t * t, u * u
        uuu, ttt = uu * u, tt * t
        return uuu * p0 + 3.0 * uu * t * p1 + 3.0 * u * tt * p2 + ttt * p3
    
    def advanced_mouse_move(self, target_x, target_y):
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
                time.sleep(random.uniform(0.05, 0.15))
                for i in range(1, 4):
                    t = i / 3.0
                    corr_x = overshoot_target_x + (final_x - overshoot_target_x) * t
                    corr_y = overshoot_target_y + (final_y - overshoot_target_y) * t
                    pyautogui.moveTo(corr_x, corr_y, duration=0)
                    time.sleep(0.02)
            
            if random.randint(1, 100) <= self.micro_correction_chance:
                time.sleep(random.uniform(0.03, 0.08))
                micro_x = random.randint(-3, 3)
                micro_y = random.randint(-3, 3)
                final_x += micro_x
                final_y += micro_y
            
            pyautogui.moveTo(final_x, final_y, duration=0)
        except Exception as e:
            print(f"Advanced mouse move error to ({target_x}, {target_y}): {e}")
            # Fallback to simple move
            try:
                pyautogui.moveTo(target_x, target_y, duration=0.2)
            except:
                pass
    
    def micro_break(self):
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
        self.update_stats()
    
    def check_micro_break(self):
        if (time.time() * 1000 - self.last_break_time) < 120000:
            return False
        adjusted_chance = self.micro_break_chance + (self.fatigue_level / 10.0)
        if random.randint(1, 100) <= adjusted_chance:
            self.micro_break()
            return True
        return False
    
    def random_short_sleep(self):
        multiplier = self.get_fatigue_multiplier()
        time.sleep((random.uniform(self.short_delay_min, self.short_delay_max) * multiplier) / 1000.0)
    
    def random_medium_sleep(self):
        multiplier = self.get_fatigue_multiplier()
        time.sleep((random.uniform(self.medium_delay_min, self.medium_delay_max) * multiplier) / 1000.0)
    
    def random_long_sleep(self):
        multiplier = self.get_fatigue_multiplier()
        time.sleep((random.uniform(self.long_delay_min, self.long_delay_max) * multiplier) / 1000.0)
    
    def random_action_sleep(self):
        multiplier = self.get_fatigue_multiplier()
        time.sleep((random.uniform(self.action_delay_min, self.action_delay_max) * multiplier) / 1000.0)
    
    def random_wait_sleep(self):
        multiplier = self.get_fatigue_multiplier()
        time.sleep((random.uniform(self.wait_delay_min, self.wait_delay_max) * multiplier) / 1000.0)
    
    def random_idle_action(self):
        action = random.randint(1, 100)
        if action <= 30:
            time.sleep(random.uniform(0.8, 2.0))
        elif action <= 60:
            time.sleep(random.uniform(2.0, 4.0))
        elif action <= 75:
            time.sleep(random.uniform(3.0, 6.0))
    
        if not AUTOGUI_AVAILABLE:
            return

        try:
            current_x, current_y = pyautogui.position()
            screen_width, screen_height = pyautogui.size()
        
            margin_x = int(screen_width * 0.1)
            margin_y = int(screen_height * 0.1)
        
            x = random.randint(margin_x, screen_width - margin_x)
            y = random.randint(margin_y, screen_height - margin_y)
        
            self.session_actions_count += 1
            self.advanced_mouse_move(x, y)
        
            multiplier = self.get_fatigue_multiplier()
            base_delay = random.uniform(self.human_delay_min, self.human_delay_max)
            time.sleep((base_delay * multiplier) / 1000.0)
        
        # Optional: Sometimes click, sometimes just move
            if random.randint(1, 100) <= 30:  # 30% chance to click
                pyautogui.click()
                time.sleep(random.uniform(0.06, 0.25))
        except Exception as e:
            print(f"Random idle action error: {e}")
    
    # ==================== COMPLETE GATHERING DETECTION FIX ====================
# Replace the existing is_gathering method and add these enhanced methods

# ==================== PASTE THESE METHODS INTO YOUR ROKUnifiedTool CLASS ====================
# Add these INSIDE the ROKUnifiedTool class, replacing the existing is_gathering method

    def is_gathering(self, x, y):
        """
        Enhanced multi-point gathering detection
        Checks a larger area with multiple sampling points
        """
        if not AUTOGUI_AVAILABLE:
            return False
        
        try:
            # Extended check patterns - center + rings
            check_patterns = [
                # Center point
                [(0, 0)],
                # Inner ring (4 points)
                [(-4, 0), (4, 0), (0, -4), (0, 4)],
                # Diagonal inner ring
                [(-4, -4), (4, -4), (-4, 4), (4, 4)],
                # Outer ring (8 points)
                [(-8, 0), (8, 0), (0, -8), (0, 8),
                 (-8, -8), (8, -8), (-8, 8), (8, 8)],
                # Extended points for larger indicators
                [(-12, 0), (12, 0), (0, -12), (0, 12)]
            ]
            
            match_count = 0
            total_checks = 0
            
            for pattern in check_patterns:
                for dx, dy in pattern:
                    total_checks += 1
                    check_x, check_y = x + dx, y + dy
                    check_color = self.get_pixel_color(check_x, check_y)
                    
                    # Check against all gathering colors
                    for color in self.gathering_colors:
                        if self.color_match(check_color, color, self.tolerance):
                            match_count += 1
                            break  # Found a match, move to next point
            
            # If we found matches in at least 20% of check points, troops are gathering
            match_threshold = 0.20
            if total_checks > 0 and (match_count / total_checks) >= match_threshold:
                return True
            
            # Additional check with higher tolerance for specific colors
            high_tolerance = self.tolerance + 20
            critical_points = [(0, 0), (-5, -5), (5, -5), (-5, 5), (5, 5)]
            
            for dx, dy in critical_points:
                check_x, check_y = x + dx, y + dy
                check_color = self.get_pixel_color(check_x, check_y)
                
                # Primary gathering colors (green and brown)
                primary_colors = [0x0D9A00, 0xB45D00, 0x32CD32, 0x228B22]
                for color in primary_colors:
                    if self.color_match(check_color, color, high_tolerance):
                        return True
            
            return False
            
        except Exception as e:
            self.log(f"is_gathering error at ({x}, {y}): {e}")
            return False

    def is_gathering_screenshot(self, x, y, radius=25):
        """
        Screenshot-based detection (more reliable but slower)
        Use this when pixel-based detection is unreliable
        """
        if not AUTOGUI_AVAILABLE:
            return False
        
        try:
            # Capture area around the point
            screenshot = ImageGrab.grab(bbox=(x - radius, y - radius, 
                                             x + radius, y + radius))
            
            # Count pixels matching gathering colors
            pixels = screenshot.load()
            width, height = screenshot.size
            
            match_count = 0
            total_pixels = width * height
            
            for px in range(width):
                for py in range(height):
                    pixel = pixels[px, py]
                    # Convert PIL RGB to hex
                    pixel_color = (pixel[0] << 16) | (pixel[1] << 8) | pixel[2]
                    
                    for color in self.gathering_colors:
                        if self.color_match(pixel_color, color, self.tolerance):
                            match_count += 1
                            break
            
            # If more than 15% of pixels match, consider it gathering
            if (match_count / total_pixels) >= 0.15:
                return True
            
            return False
            
        except Exception as e:
            self.log(f"is_gathering_screenshot error: {e}")
            return False

    def verify_slot_empty(self, slot_index):
        """
        Comprehensive verification that a slot is empty and ready for march
        Returns True if slot is EMPTY (not gathering)
        Returns False if slot is BUSY (gathering active)
        """
        check_x, check_y = self.march_slots[slot_index]
        
        # Method 1: Quick pixel check
        if self.is_gathering(check_x, check_y):
            self.log(f"Slot {slot_index + 1}: Gathering detected (pixel check)")
            return False
        
        # Method 2: Wait a moment and recheck (accounts for animation delays)
        time.sleep(0.4)
        if self.is_gathering(check_x, check_y):
            self.log(f"Slot {slot_index + 1}: Gathering detected (delayed check)")
            return False
        
        # Method 3: Screenshot-based verification for extra reliability
        if self.is_gathering_screenshot(check_x, check_y):
            self.log(f"Slot {slot_index + 1}: Gathering detected (screenshot check)")
            return False
        
        # All checks passed - slot is empty
        self.log(f"Slot {slot_index + 1}: Empty and ready")
        return True

    def verify_march_started(self, slot_index, max_attempts=3):
        """
        Verify that a march has successfully started
        Returns True if march is confirmed active
        """
        check_x, check_y = self.march_slots[slot_index]
        
        for attempt in range(max_attempts):
            # Wait for march to initialize
            time.sleep(1.0 + (attempt * 0.5))
            
            # Check if gathering indicators are present
            if self.is_gathering(check_x, check_y):
                self.log(f"Slot {slot_index + 1}: March confirmed (attempt {attempt + 1})")
                return True
            
            # Try screenshot method as backup
            if self.is_gathering_screenshot(check_x, check_y):
                self.log(f"Slot {slot_index + 1}: March confirmed via screenshot")
                return True
        
        self.log(f"Slot {slot_index + 1}: March failed to start")
        return False

    def debug_slot_colors(self, slot_index):
        """
        Debug helper to see what colors are being detected at a slot
        Call this to troubleshoot gathering detection issues
        """
        check_x, check_y = self.march_slots[slot_index]
        
        print(f"\n=== Debug Slot {slot_index + 1} at ({check_x}, {check_y}) ===")
        
        # Check center and surrounding points
        test_points = [
            (0, 0, "Center"),
            (-5, -5, "Top-Left"),
            (5, -5, "Top-Right"),
            (-5, 5, "Bottom-Left"),
            (5, 5, "Bottom-Right"),
            (0, -8, "Top"),
            (0, 8, "Bottom"),
            (-8, 0, "Left"),
            (8, 0, "Right")
        ]
        
        for dx, dy, label in test_points:
            px, py = check_x + dx, check_y + dy
            color = self.get_pixel_color(px, py)
            r = (color >> 16) & 0xFF
            g = (color >> 8) & 0xFF
            b = color & 0xFF
            
            # Check if it matches any gathering color
            matches = []
            for i, gc in enumerate(self.gathering_colors):
                if self.color_match(color, gc, self.tolerance):
                    matches.append(f"Color{i}")
            
            match_str = ", ".join(matches) if matches else "No match"
            print(f"{label:12} ({px:4}, {py:4}): RGB({r:3}, {g:3}, {b:3}) = 0x{color:06X} - {match_str}")
        
        # Overall status
        is_busy = self.is_gathering(check_x, check_y)
        print(f"\nStatus: {'GATHERING (Busy)' if is_busy else 'EMPTY (Ready)'}")
        print("=" * 60)

    # ==================== UPDATED send_march METHOD ====================
    # Replace your existing send_march method with this improved version

    def send_march(self, slot_index):
        if not AUTOGUI_AVAILABLE:
            return False

        try:
            self.update_fatigue()
            
            # Check for micro-break
            if self.check_micro_break():
                return False
            
            if not self.can_send_march(slot_index):
                self.log(f"Slot {slot_index + 1} in cooldown")
                return False
            
            # IMPROVED: Use enhanced verification
            if not self.verify_slot_empty(slot_index):
                self.log(f"Slot {slot_index + 1} already active, skipping")
                return False
            
            self.slot_last_check[slot_index] = time.time() * 1000
            res_x, res_y, confirm_x, confirm_y, res_name = self.get_random_resource()
            
            self.total_marches += 1
            self.log(f"March {slot_index + 1} - {res_name} (Fatigue: {round(self.fatigue_level)}%)")
            
            # Step 1: Click search button
            search_x, search_y = self.search_button
            self.advanced_mouse_move(search_x, search_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(0.9, 1.6))
            
            # Step 2: Click resource type
            self.advanced_mouse_move(res_x, res_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(0.7, 1.3))
            
            # Step 3: Click confirm resource
            self.advanced_mouse_move(confirm_x, confirm_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(1.3, 2.2))
            
            # Random micro pause
            if random.randint(1, 100) <= 25:
                time.sleep(random.uniform(0.3, 0.8))
            
            # Step 4: Click gather button
            gather_x, gather_y = self.gather_btn
            self.advanced_mouse_move(gather_x, gather_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(1.1, 1.9))
            
            # Step 5: Click send troops button
            troops_x, troops_y = self.send_troops_btn
            self.advanced_mouse_move(troops_x, troops_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(1.6, 2.3))
            
            # Random micro pause
            if random.randint(1, 100) <= 20:
                time.sleep(random.uniform(0.5, 1.0))
            
            # Step 6: Click march confirm
            confirm_march_x, confirm_march_y = self.march_confirm
            self.advanced_mouse_move(confirm_march_x, confirm_march_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(2.2, 2.8))
            
            # IMPROVED: Use enhanced verification
            if self.verify_march_started(slot_index):
                self.log(f"✅ March {slot_index + 1} SUCCESS - {res_name}")
                self.successful_marches += 1
                self.update_stats()
                if self.webhook_enabled and self.webhook_on_success:
                    self.send_webhook("success", f"✅ March {slot_index + 1} SUCCESS - {res_name}", 0x27AE60)
                return True
            else:
                self.log(f"❌ March {slot_index + 1} FAILED - {res_name}")
                self.update_stats()
                if self.webhook_enabled and self.webhook_on_fail:
                    self.send_webhook("error", f"❌ March {slot_index + 1} FAILED - {res_name}", 0xE74C3C)
                return False
            
        except Exception as e:
            self.log(f"Send march error: {e}")
            import traceback
            traceback.print_exc()
            return False


    # ==================== DEBUGGING HELPER ====================
    def debug_slot_colors(self, slot_index):
        """
        Debug helper to see what colors are being detected at a slot
        Call this to troubleshoot gathering detection issues
        """
        check_x, check_y = self.march_slots[slot_index]
        
        print(f"\n=== Debug Slot {slot_index + 1} at ({check_x}, {check_y}) ===")
        
        # Check center and surrounding points
        test_points = [
            (0, 0, "Center"),
            (-5, -5, "Top-Left"),
            (5, -5, "Top-Right"),
            (-5, 5, "Bottom-Left"),
            (5, 5, "Bottom-Right"),
            (0, -8, "Top"),
            (0, 8, "Bottom"),
            (-8, 0, "Left"),
            (8, 0, "Right")
        ]
        
        for dx, dy, label in test_points:
            px, py = check_x + dx, check_y + dy
            color = self.get_pixel_color(px, py)
            r = (color >> 16) & 0xFF
            g = (color >> 8) & 0xFF
            b = color & 0xFF
            
            # Check if it matches any gathering color
            matches = []
            for i, gc in enumerate(self.gathering_colors):
                if self.color_match(color, gc, self.tolerance):
                    matches.append(f"Color{i}")
            
            match_str = ", ".join(matches) if matches else "No match"
            print(f"{label:12} ({px:4}, {py:4}): RGB({r:3}, {g:3}, {b:3}) = 0x{color:06X} - {match_str}")
    
    def check_help_button(self):
        if not self.auto_help_enabled or not AUTOGUI_AVAILABLE:
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
                        time.sleep(random.uniform(1.2, 2.5))
                        self.update_stats()
                        return True
        except Exception as e:
            print(f"Help button check error: {e}")
        return False
    
    def check_reconnect(self):
        if not AUTOGUI_AVAILABLE:
            return False
        x1, y1, x2, y2 = self.reconnect_area
        for x in range(x1, x2, 10):
            for y in range(y1, y2, 10):
                color = self.get_pixel_color(x, y)
                if self.color_match(color, self.reconnect_color, 18):
                    self.advanced_mouse_move(x, y)
                    pyautogui.click()
                    self.log("Reconnect button clicked")
                    time.sleep(random.uniform(2.5, 5.0))
                    return True
        return False
    
    def get_random_resource(self):
        if self.resource_rotation_enabled and len(self.selected_resources) > 0:
            self.current_resource = self.selected_resources[self.current_rotation_index]
            self.current_rotation_index = (self.current_rotation_index + 1) % len(self.selected_resources)
            self.update_resource_display()
        elif len(self.selected_resources) > 0:
            self.current_resource = self.selected_resources[0]
        res_x, res_y = self.resources[self.current_resource]
        confirm_x, confirm_y = self.search_confirms[self.current_resource]
        return res_x, res_y, confirm_x, confirm_y, self.current_resource
    
    def can_send_march(self, slot_index):
        current_time = time.time() * 1000
        min_wait = random.uniform(self.min_wait_time_base, self.max_wait_time_base)
        return (current_time - self.slot_last_check[slot_index]) >= min_wait
    
    def send_march(self, slot_index):
        """
        Enhanced send_march with improved verification
        """
        if not AUTOGUI_AVAILABLE:
            return False
    
        try:
            self.update_fatigue()
        
            # Check for micro-break
            if self.check_micro_break():
                return False
        
            if not self.can_send_march(slot_index):
                self.log(f"Slot {slot_index + 1} in cooldown")
                return False
        
            # IMPROVED: Use enhanced verification to check if slot is busy
            if not self.verify_slot_empty(slot_index):
                self.log(f"Slot {slot_index + 1} already active, skipping")
                return False
        
            self.slot_last_check[slot_index] = time.time() * 1000
            res_x, res_y, confirm_x, confirm_y, res_name = self.get_random_resource()
            
            self.total_marches += 1
            self.log(f"March {slot_index + 1} - {res_name} (Fatigue: {round(self.fatigue_level)}%)")
            print(f"Starting march for slot {slot_index + 1}")
            
            # Step 1: Click search button
            print(f"Step 1: Clicking search button at {self.search_button}")
            search_x, search_y = self.search_button
            self.advanced_mouse_move(search_x, search_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(0.9, 1.6))
            
            # Step 2: Click resource type
            print(f"Step 2: Clicking resource {res_name} at ({res_x}, {res_y})")
            self.advanced_mouse_move(res_x, res_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(0.7, 1.3))
            
            # Step 3: Click confirm resource
            print(f"Step 3: Clicking confirm at ({confirm_x}, {confirm_y})")
            self.advanced_mouse_move(confirm_x, confirm_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(1.3, 2.2))
            
            # Random micro pause
            if random.randint(1, 100) <= 25:
                time.sleep(random.uniform(0.3, 0.8))
            
            # Step 4: Click gather button
            print(f"Step 4: Clicking gather button at {self.gather_btn}")
            gather_x, gather_y = self.gather_btn
            self.advanced_mouse_move(gather_x, gather_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(1.1, 1.9))
            
            # Step 5: Click send troops button
            print(f"Step 5: Clicking send troops at {self.send_troops_btn}")
            troops_x, troops_y = self.send_troops_btn
            self.advanced_mouse_move(troops_x, troops_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(1.6, 2.3))
            
            # Random micro pause
            if random.randint(1, 100) <= 20:
                time.sleep(random.uniform(0.5, 1.0))
            
            # Step 6: Click march confirm
            print(f"Step 6: Clicking march confirm at {self.march_confirm}")
            confirm_march_x, confirm_march_y = self.march_confirm
            self.advanced_mouse_move(confirm_march_x, confirm_march_y)
            time.sleep(random.uniform(0.08, 0.18))
            pyautogui.click()
            time.sleep(random.uniform(2.2, 2.8))
            
            # IMPROVED: Use enhanced verification to confirm march started
            print(f"Step 7: Verifying march started for slot {slot_index + 1}")
            if self.verify_march_started(slot_index):
                print(f"✅ March {slot_index + 1} SUCCESS - {res_name}")
                self.log(f"✅ March {slot_index + 1} SUCCESS - {res_name}")
                self.successful_marches += 1
                self.update_stats()
                if self.webhook_enabled and self.webhook_on_success:
                    self.send_webhook("success", f"✅ March {slot_index + 1} SUCCESS - {res_name}", 0x27AE60)
                return True
            else:
                print(f"❌ March {slot_index + 1} FAILED - {res_name}")
                self.log(f"❌ March {slot_index + 1} FAILED - {res_name}")
                self.update_stats()
                if self.webhook_enabled and self.webhook_on_fail:
                    self.send_webhook("error", f"❌ March {slot_index + 1} FAILED - {res_name}", 0xE74C3C)
                return False
            
        except Exception as e:
            self.log(f"Send march error: {e}")
            print(f"Send march error: {e}")
            import traceback
            traceback.print_exc()
            return False
                    
    def autofarm_loop(self):
        while self.running:
            if not self.toggle:
                time.sleep(0.1)
                continue
            
            self.update_fatigue()
            self.check_help_button()
            self.check_webhook_interval()
            
            if random.randint(1, 100) <= 60:
                if self.check_reconnect():
                    time.sleep(random.uniform(2.5, 5.0))
                    continue
            
            march_sent = False
            for i in range(len(self.march_slots)):
                time.sleep(random.uniform(0.7, 2.0))
                check_x, check_y = self.march_slots[i]
                if not self.is_gathering(check_x, check_y):
                    if self.send_march(i):
                        march_sent = True
                self.check_help_button()
            
            if not march_sent:
                wait_time = random.uniform(15, 25)
                start_wait = time.time()
                while (time.time() - start_wait) < wait_time and self.toggle:
                    self.check_help_button()
                    time.sleep(random.uniform(3, 7))
            
            time.sleep(random.uniform(2, 5))
    
    # ==================== Webhook Functions ====================
    
    def send_webhook(self, event_type, message, color=None):
        if not self.webhook_enabled or not self.webhook_url:
            return
        try:
            colors = {"success": 0x27AE60, "error": 0xE74C3C, "info": 0x3498DB, "warning": 0xF39C12}
            if color is None:
                color = colors.get(event_type, 0x95A5A6)
            
            success_rate = 0
            if self.total_marches > 0:
                success_rate = round((self.successful_marches / self.total_marches) * 100, 1)
            
            session_minutes = 0
            if self.session_start_time > 0:
                session_minutes = round((time.time() * 1000 - self.session_start_time) / 60000.0, 1)
            
            embed = {
                "title": f"🎮 ROK Unified Tool - {event_type.title()}",
                "description": message,
                "color": color,
                "timestamp": datetime.utcnow().isoformat(),
                "fields": [
                    {"name": "👤 User", "value": self.current_user, "inline": True},
                    {"name": "📋 Profile", "value": self.active_profile, "inline": True},
                    {"name": "🎯 Resource", "value": self.current_resource, "inline": True},
                    {"name": "📊 Total Marches", "value": str(self.total_marches), "inline": True},
                    {"name": "✅ Successful", "value": f"{self.successful_marches} ({success_rate}%)", "inline": True},
                    {"name": "⏱️ Session Time", "value": f"{session_minutes} min", "inline": True}
                ],
                "footer": {"text": "ROK Unified Tool"}
            }
            payload = {"embeds": [embed]}
            response = requests.post(self.webhook_url, json=payload, timeout=10)
            if response.status_code == 204:
                self.log(f"Webhook sent: {event_type}")
        except Exception as e:
            self.log(f"Webhook error: {str(e)}")
    
    def check_webhook_interval(self):
        if not self.webhook_enabled or not self.webhook_url:
            return
        current_time = time.time() * 1000
        if self.last_webhook_time == 0:
            self.last_webhook_time = current_time
            return
        elapsed_minutes = (current_time - self.last_webhook_time) / 60000.0
        if elapsed_minutes >= self.webhook_interval:
            self.send_webhook("info", f"📈 Periodic Stats Update")
            self.last_webhook_time = current_time
    
    # ==================== GUI Functions ====================
    
    def update_stats(self):
        if not self.root:
            return
        try:
            success_rate = 0
            if self.total_marches > 0:
                success_rate = round((self.successful_marches / self.total_marches) * 100, 1)
            session_minutes = 0
            if self.session_start_time > 0:
                session_minutes = round((time.time() * 1000 - self.session_start_time) / 60000.0, 1)
            
            self.stat_marches.config(text=f"Total Marches: {self.total_marches}")
            self.stat_success.config(text=f"Successful: {self.successful_marches} ({success_rate}%)")
            self.stat_helps.config(text=f"Help Clicks: {self.total_help_clicks}")
            self.stat_fatigue.config(text=f"Fatigue Level: {round(self.fatigue_level)}%")
            self.stat_time.config(text=f"Session Time: {session_minutes} min")
        except:
            pass
    
    def update_resource_display(self):
        if not self.root:
            return
        try:
            if len(self.selected_resources) > 0:
                resource_list = ", ".join(self.selected_resources)
                self.selected_res_text.config(text=f"Selected: {resource_list}")
            else:
                self.selected_res_text.config(text="Selected: None")
            
            if self.resource_rotation_enabled:
                self.current_res_text.config(text=f"Current: {self.current_resource} (Rotating)")
            else:
                self.current_res_text.config(text=f"Current: {self.current_resource}")
        except:
            pass
    
    def update_resource_selection(self):
        self.selected_resources = []
        if self.food_var.get():
            self.selected_resources.append("Food")
        if self.wood_var.get():
            self.selected_resources.append("Wood")
        if self.stone_var.get():
            self.selected_resources.append("Stone")
        if self.gold_var.get():
            self.selected_resources.append("Gold")
        
        if not self.resource_rotation_enabled and len(self.selected_resources) > 0:
            self.current_resource = self.selected_resources[0]
            self.current_rotation_index = 0
        self.update_resource_display()
    
    def toggle_rotation(self):
        self.resource_rotation_enabled = self.rotation_var.get()
        if self.resource_rotation_enabled and len(self.selected_resources) > 0:
            self.current_resource = self.selected_resources[0]
            self.current_rotation_index = 0
        self.update_resource_display()
    
    def toggle_auto_help(self):
        self.auto_help_enabled = self.auto_help_var.get()
    
    def toggle_autofarm(self):
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
            self.session_actions_count = 0
            self.fatigue_level = 0
            self.last_break_time = time.time() * 1000
            self.last_webhook_time = time.time() * 1000
            
            mode = "Rotation" if self.resource_rotation_enabled else "Fixed"
            resources = ", ".join(self.selected_resources)
            
            self.log(f"=== AUTOFARM START - {self.active_profile} Profile - {mode} Mode ===")
            self.log(f"Resources: {resources}")
            
            if self.webhook_enabled and self.webhook_on_start:
                self.send_webhook("info", f"🚀 AutoFarm Started\n**Profile:** {self.active_profile}\n**Mode:** {mode}\n**Resources:** {resources}", 0x3498DB)
            if self.auto_hide_enabled:
                self.root.after(500, self.hide_window)
            if not self.running:
                self.running = True
                threading.Thread(target=self.autofarm_loop, daemon=True).start()
        else:
            self.log("AutoFarm stopped")
            if self.auto_hide_enabled and self.window_hidden:
                self.show_window()
            
            if self.webhook_enabled and self.webhook_on_stop:
                self.send_webhook("warning", "⏸️ AutoFarm Stopped", 0xF39C12)
    def show_exit_stats(self):
        """Show final statistics before exit"""
        self.running = False
        self.toggle = False
        
        if self.session_start_time == 0:
            # No session to report
            return
        
        success_rate = 0
        if self.total_marches > 0:
            success_rate = round((self.successful_marches / self.total_marches) * 100, 1)
        session_minutes = round((time.time() * 1000 - self.session_start_time) / 60000.0, 1)
        final_fatigue = round(self.fatigue_level)
        resource_list = ", ".join(self.selected_resources) if self.selected_resources else "None"
        rotation_mode = "Enabled" if self.resource_rotation_enabled else "Disabled"
        
        self.log("=== SESSION END ===")
        self.log(f"Resources: {resource_list}")
        self.log(f"Rotation: {rotation_mode}")
        self.log(f"Duration: {session_minutes} minutes")
        self.log(f"Total: {self.total_marches}, Success: {self.successful_marches}, Rate: {success_rate}%")
        self.log(f"Help clicks: {self.total_help_clicks}")
        self.log(f"Final fatigue: {final_fatigue}%")
        
        if self.webhook_enabled:
            self.send_webhook("info", f"🏁 Session Complete\n**Duration:** {session_minutes} min\n**Success Rate:** {success_rate}%", 0x9B59B6)
        
        msg = f"""AutoFarm Session Statistics:

Resources: {resource_list}
Rotation: {rotation_mode}
Duration: {session_minutes} minutes

Total Marches: {self.total_marches}
Successful: {self.successful_marches}
Success Rate: {success_rate}%

Help Clicks: {self.total_help_clicks}
Final Fatigue: {final_fatigue}%

Profile: {self.active_profile} ({len(self.march_slots)} slots)"""
        
        messagebox.showinfo("ROK Unified Tool - Session Complete", msg)
    
    def refresh_devices(self):
        devices = self.list_devices()
        self.device_listbox.delete(0, tk.END)
        for dev, status in devices:
            icon = "🟢" if status == "online" else "🔴"
            self.device_listbox.insert(tk.END, f"{dev} - {icon} {status}")
    
    def connect_selected_devices(self):
        selection = self.device_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select devices to connect")
            return
        
        devices = self.list_devices()
        for idx in selection:
            device_id, _ = devices[idx]
            success, msg = self.connect_device(device_id)
            self.log(f"Connect {device_id}: {msg}")
        
        self.refresh_devices()
    
    def disconnect_selected_devices(self):
        selection = self.device_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select devices to disconnect")
            return
        
        devices = self.list_devices()
        for idx in selection:
            device_id, _ = devices[idx]
            success, msg = self.disconnect_device(device_id)
            self.log(f"Disconnect {device_id}: {msg}")
        
        self.refresh_devices()
    
    def launch_game(self):
        package = "com.lilithgame.roc.gp" if self.game_version_var.get() == "Global" else "com.rok.gp.vn"
        devices = self.list_devices()
        online_devices = [d for d, s in devices if s == "online"]
        
        if not online_devices:
            messagebox.showwarning("No Devices", "No online devices available")
            return
        
        count = 0
        for dev in online_devices:
            if self.launch_game_on_device(dev, package):
                count += 1
        
        messagebox.showinfo("Success", f"Launched game on {count} devices")
    
    def close_game(self):
        package = "com.lilithgame.roc.gp" if self.game_version_var.get() == "Global" else "com.rok.gp.vn"
        devices = self.list_devices()
        online_devices = [d for d, s in devices if s == "online"]
        
        if not online_devices:
            messagebox.showwarning("No Devices", "No online devices available")
            return
        
        count = 0
        for dev in online_devices:
            if self.close_game_on_device(dev, package):
                count += 1
        
        messagebox.showinfo("Success", f"Closed game on {count} devices")
    
    def show_login(self):
        login_win = tk.Tk()
        login_win.title("ROK Unified Tool - Login")
        login_win.geometry("400x300")
        login_win.configure(bg="#2C3E50")
        login_win.resizable(False, False)
        
        # Center window
        login_win.update_idletasks()
        x = (login_win.winfo_screenwidth() // 2) - 200
        y = (login_win.winfo_screenheight() // 2) - 150
        login_win.geometry(f"400x300+{x}+{y}")
        
        # Title
        title_frame = tk.Frame(login_win, bg="#1a252f", height=45)
        title_frame.pack(fill=tk.X)
        tk.Label(title_frame, text="ROK Unified Tool - Login", bg="#1a252f", fg="white", 
                font=("Arial", 13, "bold")).pack(pady=10)
        
        # Form
        form_frame = tk.Frame(login_win, bg="#2C3E50")
        form_frame.pack(expand=True, fill=tk.BOTH, padx=40, pady=30)
        
        tk.Label(form_frame, text="Username:", bg="#2C3E50", fg="white", 
                font=("Arial", 11)).pack(anchor=tk.W, pady=(0, 5))
        username_var = tk.StringVar()
        username_entry = tk.Entry(form_frame, textvariable=username_var, font=("Arial", 11), 
                                  bg="#34495E", fg="white", insertbackground="white")
        username_entry.pack(fill=tk.X, pady=(0, 15))
        
        tk.Label(form_frame, text="Password:", bg="#2C3E50", fg="white", 
                font=("Arial", 11)).pack(anchor=tk.W, pady=(0, 5))
        password_var = tk.StringVar()
        password_entry = tk.Entry(form_frame, textvariable=password_var, font=("Arial", 11), 
                                  bg="#34495E", fg="white", insertbackground="white", show="●")
        password_entry.pack(fill=tk.X, pady=(0, 20))
        
        status_label = tk.Label(form_frame, text="", bg="#2C3E50", font=("Arial", 9), wraplength=300)
        status_label.pack(pady=(0, 15))
        
        login_success = [False]
        
        def attempt_login():
            username = username_var.get()
            password = password_var.get()
            if not username or not password:
                status_label.config(text="Please enter username and password", fg="#E74C3C")
                return
            
            success, message = self.perform_login(username, password)
            if success:
                status_label.config(text=message, fg="#27AE60")
                login_success[0] = True
                login_win.after(1000, login_win.destroy)
            else:
                status_label.config(text=message, fg="#E74C3C")
        
        username_entry.bind('<Return>', lambda e: attempt_login())
        password_entry.bind('<Return>', lambda e: attempt_login())
        
        # Buttons
        btn_frame = tk.Frame(form_frame, bg="#2C3E50")
        btn_frame.pack()
        tk.Button(btn_frame, text="Login", command=attempt_login, bg="#27AE60", fg="white", 
                 font=("Arial", 11, "bold"), width=12, cursor="hand2").pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="Cancel", command=lambda: login_win.destroy(), bg="#E74C3C", 
                 fg="white", font=("Arial", 11, "bold"), width=12, cursor="hand2").pack(side=tk.LEFT, padx=5)
        
        tk.Label(form_frame, text="Valid users: nhan, huy", bg="#2C3E50", fg="#95A5A6", 
                font=("Arial", 8)).pack(pady=(10, 0))
        
        username_entry.focus()
        login_win.mainloop()
        return login_success[0]

    def toggle_auto_hide(self):
        """Toggle auto-hide feature"""
        self.auto_hide_enabled = self.auto_hide_var.get()
        status = "enabled" if self.auto_hide_enabled else "disabled"
        self.log(f"Auto-hide {status}")

    def create_gui(self):
        self.root = tk.Tk()
        self.root.iconphoto(True, tk.PhotoImage(file='rok_bot_icon_256x256.png'))
        self.root.title("ROK Unified Tool")
        self.root.geometry("900x700")
        self.root.configure(bg="#2C3E50")
        self.root.resizable(False, False)
        
        # Title
        title_frame = tk.Frame(self.root, bg="#1a252f", height=40)
        title_frame.pack(fill=tk.X)
        tk.Label(title_frame, text="ROK Unified Automation Tool", bg="#1a252f", fg="white", 
                font=("Arial", 12, "bold")).pack(pady=8)
        
        # Profile info
        profile_frame = tk.Frame(self.root, bg="#34495E")
        profile_frame.pack(fill=tk.X, padx=15, pady=8)
        tk.Label(profile_frame, text=f"Profile: {self.active_profile} | User: {self.current_user} | Slots: {len(self.march_slots)}", 
                bg="#34495E", fg="white", font=("Arial", 9, "bold")).pack(pady=4)
        
        # Notebook for tabs
        notebook = ttk.Notebook(self.root)
        notebook.pack(fill=tk.BOTH, expand=True, padx=15, pady=10)
        
        # Tab 1: AutoFarm
        autofarm_tab = tk.Frame(notebook, bg="#2C3E50")
        notebook.add(autofarm_tab, text="AutoFarm")
        
        # Tab 2: Emulator Control
        emulator_tab = tk.Frame(notebook, bg="#2C3E50")
        notebook.add(emulator_tab, text="Emulator Control")
        
        self.create_autofarm_tab(autofarm_tab)
        self.create_emulator_tab(emulator_tab)
        
        # Hotkeys
        if AUTOGUI_AVAILABLE:
            keyboard.add_hotkey('f8', self.toggle_autofarm)
            keyboard.add_hotkey('f9', self.force_exit)
            keyboard.add_hotkey('f10', self.toggle_window_visibility)

        self.menu_visible = True
        self.root.protocol("WM_DELETE_WINDOW", self.force_exit)
        self.root.mainloop()
    
    def create_autofarm_tab(self, parent):
        # Main content with 2 columns
        main_frame = tk.Frame(parent, bg="#2C3E50")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        left_frame = tk.Frame(main_frame, bg="#2C3E50")
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        right_frame = tk.Frame(main_frame, bg="#2C3E50")
        right_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        # Webhook Settings (Top of Left)
        webhook_frame = tk.LabelFrame(left_frame, text="Discord Webhook", bg="#2C3E50", fg="white", 
                                     font=("Arial", 10))
        webhook_frame.pack(fill=tk.X, pady=(0, 8))
        
        tk.Label(webhook_frame, text="Webhook URL:", bg="#2C3E50", fg="white", 
                font=("Arial", 8)).pack(anchor=tk.W, padx=5, pady=(4, 0))
        self.webhook_url_var = tk.StringVar(value=self.webhook_url)
        webhook_entry = tk.Entry(webhook_frame, textvariable=self.webhook_url_var, bg="#34495E", 
                                fg="white", font=("Arial", 8), insertbackground="white")
        webhook_entry.pack(fill=tk.X, padx=5, pady=(0, 4))
        
        webhook_options_frame = tk.Frame(webhook_frame, bg="#2C3E50")
        webhook_options_frame.pack(fill=tk.X, padx=5)
        
        self.webhook_enabled_var = tk.BooleanVar(value=False)
        tk.Checkbutton(webhook_options_frame, text="Enable", variable=self.webhook_enabled_var, 
                      command=self.toggle_webhook, bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 8)).grid(row=0, column=0, sticky=tk.W)
        self.webhook_start_var = tk.BooleanVar(value=True)
        tk.Checkbutton(webhook_options_frame, text="Start", variable=self.webhook_start_var, 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 8)).grid(row=0, column=1, padx=3, sticky=tk.W)
        self.webhook_stop_var = tk.BooleanVar(value=True)
        tk.Checkbutton(webhook_options_frame, text="Stop", variable=self.webhook_stop_var, 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 8)).grid(row=0, column=2, padx=3, sticky=tk.W)
        self.webhook_success_var = tk.BooleanVar(value=False)
        tk.Checkbutton(webhook_options_frame, text="Success", variable=self.webhook_success_var, 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 8)).grid(row=1, column=1, padx=3, sticky=tk.W)
        self.webhook_fail_var = tk.BooleanVar(value=False)
        tk.Checkbutton(webhook_options_frame, text="Fail", variable=self.webhook_fail_var, 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 8)).grid(row=1, column=2, padx=3, sticky=tk.W)
        
        test_btn_frame = tk.Frame(webhook_frame, bg="#2C3E50")
        test_btn_frame.pack(pady=4)
        tk.Button(test_btn_frame, text="Test Webhook", command=self.test_webhook, bg="#3498DB", 
                 fg="white", font=("Arial", 8), cursor="hand2", width=15).pack()
        
        # Resource Selection
        res_frame = tk.LabelFrame(left_frame, text="Resource Selection", bg="#2C3E50", fg="white", 
                                 font=("Arial", 10))
        res_frame.pack(fill=tk.BOTH, pady=(0, 8))
        
        check_frame = tk.Frame(res_frame, bg="#2C3E50")
        check_frame.pack(pady=4)
        
        self.food_var = tk.BooleanVar()
        self.wood_var = tk.BooleanVar(value=True)
        self.stone_var = tk.BooleanVar()
        self.gold_var = tk.BooleanVar()
        
        tk.Checkbutton(check_frame, text="🌾 Food", variable=self.food_var, 
                      command=self.update_resource_selection, bg="#2C3E50", fg="white", 
                      selectcolor="#34495E", font=("Arial", 9)).grid(row=0, column=0, padx=8)
        tk.Checkbutton(check_frame, text="🪵 Wood", variable=self.wood_var, 
                      command=self.update_resource_selection, bg="#2C3E50", fg="white", 
                      selectcolor="#34495E", font=("Arial", 9)).grid(row=0, column=1, padx=8)
        tk.Checkbutton(check_frame, text="🪨 Stone", variable=self.stone_var, 
                      command=self.update_resource_selection, bg="#2C3E50", fg="white", 
                      selectcolor="#34495E", font=("Arial", 9)).grid(row=0, column=2, padx=8)
        tk.Checkbutton(check_frame, text="🪙 Gold", variable=self.gold_var, 
                      command=self.update_resource_selection, bg="#2C3E50", fg="white", 
                      selectcolor="#34495E", font=("Arial", 9)).grid(row=0, column=3, padx=8)
        
        self.rotation_var = tk.BooleanVar()
        tk.Checkbutton(res_frame, text="Enable Resource Rotation", variable=self.rotation_var, 
                      command=self.toggle_rotation, bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 9)).pack(pady=4)
        
        self.current_res_text = tk.Label(res_frame, text="Current: Wood", bg="#2C3E50", fg="white", 
                                        font=("Arial", 8))
        self.current_res_text.pack()
        self.selected_res_text = tk.Label(res_frame, text="Selected: Wood", bg="#2C3E50", fg="white", 
                                         font=("Arial", 8))
        self.selected_res_text.pack(pady=(0, 4))
        
        # Features
        feat_frame = tk.LabelFrame(left_frame, text="Features", bg="#2C3E50", fg="white", 
                                  font=("Arial", 10))
        feat_frame.pack(fill=tk.BOTH)
        
        self.auto_help_var = tk.BooleanVar(value=True)
        tk.Checkbutton(feat_frame, text="Auto Help Detection", variable=self.auto_help_var, 
                      command=self.toggle_auto_help, bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 9)).pack(anchor=tk.W, padx=8, pady=2)
        self.auto_hide_var = tk.BooleanVar(value=True)
        
        tk.Checkbutton(feat_frame, text="Auto-Hide Window on Start", 
                      variable=self.auto_hide_var, 
                      command=self.toggle_auto_hide, 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 9)).pack(anchor=tk.W, padx=8, pady=2)
        
        for feat in ["• Bezier curve movement", "• Fatigue simulation", "• Anti-detection patterns"]:
            tk.Label(feat_frame, text=feat, bg="#2C3E50", fg="#BDC3C7", 
                    font=("Arial", 8)).pack(anchor=tk.W, padx=25, pady=1)
        
        # Statistics
        stats_frame = tk.LabelFrame(right_frame, text="Statistics", bg="#2C3E50", fg="white", 
                                   font=("Arial", 10))
        stats_frame.pack(fill=tk.BOTH, expand=True)
        
        self.stat_marches = tk.Label(stats_frame, text="Total Marches: 0", bg="#2C3E50", fg="white", 
                                     font=("Arial", 9))
        self.stat_marches.pack(anchor=tk.W, padx=10, pady=4)
        self.stat_success = tk.Label(stats_frame, text="Successful: 0 (0%)", bg="#2C3E50", fg="white", 
                                     font=("Arial", 9))
        self.stat_success.pack(anchor=tk.W, padx=10, pady=4)
        self.stat_helps = tk.Label(stats_frame, text="Help Clicks: 0", bg="#2C3E50", fg="white", 
                                  font=("Arial", 9))
        self.stat_helps.pack(anchor=tk.W, padx=10, pady=4)
        self.stat_fatigue = tk.Label(stats_frame, text="Fatigue Level: 0%", bg="#2C3E50", fg="white", 
                                     font=("Arial", 9))
        self.stat_fatigue.pack(anchor=tk.W, padx=10, pady=4)
        self.stat_time = tk.Label(stats_frame, text="Session Time: 0 min", bg="#2C3E50", fg="white", 
                                 font=("Arial", 9))
        self.stat_time.pack(anchor=tk.W, padx=10, pady=4)
           
        # Control buttons
        btn_frame = tk.Frame(parent, bg="#2C3E50")
        btn_frame.pack(pady=10)
        
        tk.Button(btn_frame, text="START AutoFarm (F8)", command=self.toggle_autofarm, 
                 bg="#27AE60", fg="white", font=("Arial", 11, "bold"), width=20, height=2, 
                 cursor="hand2").pack(side=tk.LEFT, padx=5)
    
    def toggle_webhook(self):
        self.webhook_enabled = self.webhook_enabled_var.get()
        self.webhook_url = self.webhook_url_var.get().strip()
        self.webhook_on_start = self.webhook_start_var.get()
        self.webhook_on_stop = self.webhook_stop_var.get()
        self.webhook_on_success = self.webhook_success_var.get()
        self.webhook_on_fail = self.webhook_fail_var.get()
        
        # Also update emulator-specific webhook settings
        self.webhook_on_gather_start = self.webhook_on_start
        self.webhook_on_gather_complete = True if self.webhook_enabled else False
        self.webhook_on_clearfog_start = self.webhook_on_start
        self.webhook_on_clearfog_stop = self.webhook_on_stop
        
        if self.webhook_enabled and not self.webhook_url:
            messagebox.showwarning("Webhook URL Required", "Please enter a Discord webhook URL")
            self.webhook_enabled = False
            self.webhook_enabled_var.set(False)
            return
        
        self.log(f"Webhook {'enabled' if self.webhook_enabled else 'disabled'}")
    
    def test_webhook(self):
        self.webhook_url = self.webhook_url_var.get().strip()
        if not self.webhook_url:
            messagebox.showwarning("No Webhook URL", "Please enter a Discord webhook URL first")
            return
        
        try:
            embed = {
                "title": "🧪 ROK Unified Tool - Test Webhook",
                "description": "This is a test message to verify your webhook is working correctly!",
                "color": 0x3498DB,
                "timestamp": datetime.utcnow().isoformat(),
                "fields": [
                    {"name": "👤 User", "value": self.current_user, "inline": True},
                    {"name": "📋 Profile", "value": self.active_profile, "inline": True},
                    {"name": "✅ Status", "value": "Connected", "inline": True}
                ],
                "footer": {"text": "ROK Unified Tool"}
            }
            payload = {"embeds": [embed]}
            response = requests.post(self.webhook_url, json=payload, timeout=10)
            
            if response.status_code == 204:
                messagebox.showinfo("Webhook Test", "✅ Webhook test successful!\nCheck your Discord channel.")
                self.log("Webhook test successful")
            else:
                messagebox.showerror("Webhook Test Failed", f"❌ Failed with status code: {response.status_code}")
                self.log(f"Webhook test failed: {response.status_code}")
        except Exception as e:
            messagebox.showerror("Webhook Error", f"❌ Error: {str(e)}")
            self.log(f"Webhook test error: {str(e)}")
    
    def create_emulator_tab(self, parent):
        # Main container
        container = tk.Frame(parent, bg="#2C3E50")
        container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Left side - Device List
        left_side = tk.Frame(container, bg="#2C3E50")
        left_side.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        device_frame = tk.LabelFrame(left_side, text="Emulator Devices", bg="#2C3E50", fg="white", 
                                    font=("Arial", 10))
        device_frame.pack(fill=tk.BOTH, expand=True)
        
        self.device_listbox = tk.Listbox(device_frame, height=10, bg="#34495E", fg="white", 
                                        selectmode=tk.MULTIPLE, font=("Arial", 9))
        self.device_listbox.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Control buttons
        btn_frame = tk.Frame(device_frame, bg="#2C3E50")
        btn_frame.pack(fill=tk.X, padx=5, pady=5)
        
        tk.Button(btn_frame, text="Refresh", command=self.refresh_devices, bg="#3498DB", fg="white", 
                 font=("Arial", 9), width=12, cursor="hand2").pack(side=tk.LEFT, padx=2)
        tk.Button(btn_frame, text="Connect", command=self.connect_selected_devices, bg="#27AE60", 
                 fg="white", font=("Arial", 9), width=12, cursor="hand2").pack(side=tk.LEFT, padx=2)
        tk.Button(btn_frame, text="Disconnect", command=self.disconnect_selected_devices, bg="#E74C3C", 
                 fg="white", font=("Arial", 9), width=12, cursor="hand2").pack(side=tk.LEFT, padx=2)
        
        # Game Control
        game_frame = tk.LabelFrame(left_side, text="Game Control", bg="#2C3E50", fg="white", 
                                  font=("Arial", 10))
        game_frame.pack(fill=tk.X, pady=(10, 0))
        
        version_frame = tk.Frame(game_frame, bg="#2C3E50")
        version_frame.pack(pady=5)
        
        self.game_version_var = tk.StringVar(value="Global")
        tk.Radiobutton(version_frame, text="Global", variable=self.game_version_var, value="Global", 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 9)).pack(side=tk.LEFT, padx=10)
        tk.Radiobutton(version_frame, text="VN", variable=self.game_version_var, value="VN", 
                      bg="#2C3E50", fg="white", selectcolor="#34495E", 
                      font=("Arial", 9)).pack(side=tk.LEFT, padx=10)
        
        game_btn_frame = tk.Frame(game_frame, bg="#2C3E50")
        game_btn_frame.pack(pady=5)
        
        tk.Button(game_btn_frame, text="Launch Game", command=self.launch_game, bg="#27AE60", fg="white", 
                 font=("Arial", 9), width=15, cursor="hand2").pack(side=tk.LEFT, padx=5)
        tk.Button(game_btn_frame, text="Close Game", command=self.close_game, bg="#E74C3C", fg="white", 
                 font=("Arial", 9), width=15, cursor="hand2").pack(side=tk.LEFT, padx=5)
        
        # Right side - Automation Functions
        right_side = tk.Frame(container, bg="#2C3E50")
        right_side.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        # Gather RSS
        gather_frame = tk.LabelFrame(right_side, text="Thu thập Tài nguyên (Gather RSS)", 
                                    bg="#2C3E50", fg="white", font=("Arial", 10))
        gather_frame.pack(fill=tk.BOTH, expand=True)
        
        march_frame = tk.Frame(gather_frame, bg="#2C3E50")
        march_frame.pack(pady=5)
        tk.Label(march_frame, text="Số đạo quân:", bg="#2C3E50", fg="white", 
                font=("Arial", 9)).pack(side=tk.LEFT, padx=5)
        self.marches_var = tk.StringVar(value="6")
        tk.Entry(march_frame, textvariable=self.marches_var, width=5, bg="#34495E", fg="white", 
                font=("Arial", 9), insertbackground="white").pack(side=tk.LEFT)
        
        gather_btn_frame = tk.Frame(gather_frame, bg="#2C3E50")
        gather_btn_frame.pack(pady=5)
        self.start_gather_btn = tk.Button(gather_btn_frame, text="Bắt đầu", command=self.start_gather, 
                                         bg="#27AE60", fg="white", font=("Arial", 9), width=12, 
                                         cursor="hand2")
        self.start_gather_btn.pack(side=tk.LEFT, padx=5)
        self.stop_gather_btn = tk.Button(gather_btn_frame, text="Dừng", command=self.stop_gather, 
                                        bg="#E74C3C", fg="white", font=("Arial", 9), width=12, 
                                        cursor="hand2", state=tk.DISABLED)
        self.stop_gather_btn.pack(side=tk.LEFT, padx=5)
        
        # Log area
        log_frame = tk.Frame(gather_frame, bg="#2C3E50")
        log_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        scrollbar = tk.Scrollbar(log_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.gather_log = tk.Text(log_frame, height=8, bg="#34495E", fg="white", 
                                 font=("Consolas", 8), yscrollcommand=scrollbar.set, 
                                 state=tk.DISABLED, wrap=tk.WORD)
        self.gather_log.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.gather_log.yview)
        
        # Clear Fog
        clearfog_frame = tk.LabelFrame(right_side, text="Clear Fog", bg="#2C3E50", fg="white", 
                                      font=("Arial", 10))
        clearfog_frame.pack(fill=tk.BOTH, expand=True, pady=(10, 0))
        
        clearfog_btn_frame = tk.Frame(clearfog_frame, bg="#2C3E50")
        clearfog_btn_frame.pack(pady=5)
        self.start_clearfog_btn = tk.Button(clearfog_btn_frame, text="Bắt đầu", 
                                           command=self.start_clearfog, bg="#27AE60", fg="white", 
                                           font=("Arial", 9), width=12, cursor="hand2")
        self.start_clearfog_btn.pack(side=tk.LEFT, padx=5)
        self.stop_clearfog_btn = tk.Button(clearfog_btn_frame, text="Dừng", 
                                          command=self.stop_clearfog, bg="#E74C3C", fg="white", 
                                          font=("Arial", 9), width=12, cursor="hand2", 
                                          state=tk.DISABLED)
        self.stop_clearfog_btn.pack(side=tk.LEFT, padx=5)
        
        # Log area
        clearfog_log_frame = tk.Frame(clearfog_frame, bg="#2C3E50")
        clearfog_log_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        clearfog_scrollbar = tk.Scrollbar(clearfog_log_frame)
        clearfog_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.clearfog_log = tk.Text(clearfog_log_frame, height=8, bg="#34495E", fg="white", 
                                   font=("Consolas", 8), yscrollcommand=clearfog_scrollbar.set, 
                                   state=tk.DISABLED, wrap=tk.WORD)
        self.clearfog_log.pack(fill=tk.BOTH, expand=True)
        clearfog_scrollbar.config(command=self.clearfog_log.yview)
        
        # Auto-refresh devices
        self.refresh_devices()
    
    def update_gather_log(self, message):
        if not self.root or not hasattr(self, 'gather_log'):
            print(f"[GATHER] {message}")
            return
        try:
            self.gather_log.config(state=tk.NORMAL)
            self.gather_log.insert(tk.END, f"{message}\n")
            self.gather_log.see(tk.END)
            self.gather_log.config(state=tk.DISABLED)
        except Exception as e:
            print(f"[GATHER] {message}")
    
    def update_clearfog_log(self, message):
        if not self.root or not hasattr(self, 'clearfog_log'):
            print(f"[CLEARFOG] {message}")
            return
        try:
            self.clearfog_log.config(state=tk.NORMAL)
            self.clearfog_log.insert(tk.END, f"{message}\n")
            self.clearfog_log.see(tk.END)
            self.clearfog_log.config(state=tk.DISABLED)
        except Exception as e:
            print(f"[CLEARFOG] {message}")
    
    def start_gather(self):
        if not OPENCV_AVAILABLE:
            messagebox.showerror("Error", "OpenCV not available!\nInstall: pip install opencv-python pytesseract")
            return
        
        devices = self.list_devices()
        online_devices = [d for d, s in devices if s == "online"]
        
        if not online_devices:
            messagebox.showwarning("No Devices", "No online devices available!")
            return
        
        try:
            max_marches = int(self.marches_var.get())
            if max_marches <= 0:
                raise ValueError
        except ValueError:
            messagebox.showwarning("Invalid Input", "Please enter a valid number of marches!")
            return
        
        # Select device
        if len(online_devices) > 1:
            device_window = tk.Toplevel(self.root)
            device_window.title("Select Device")
            device_window.geometry("300x250")
            device_window.configure(bg="#2C3E50")
            device_window.transient(self.root)
            device_window.grab_set()
            
            tk.Label(device_window, text="Select a device:", bg="#2C3E50", fg="white", 
                    font=("Arial", 10)).pack(pady=10)
            
            device_listbox = tk.Listbox(device_window, bg="#34495E", fg="white", font=("Arial", 9))
            device_listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
            
            for dev in online_devices:
                device_listbox.insert(tk.END, dev)
            
            selected_device = [None]
            
            def select():
                if device_listbox.curselection():
                    selected_device[0] = online_devices[device_listbox.curselection()[0]]
                    device_window.destroy()
            
            tk.Button(device_window, text="Select", command=select, bg="#27AE60", fg="white", 
                     font=("Arial", 9), width=15, cursor="hand2").pack(pady=10)
            
            device_window.wait_window()
            
            if not selected_device[0]:
                return
            device_id = selected_device[0]
        else:
            device_id = online_devices[0]
        
        # Start gathering
        if hasattr(self, 'start_gather_btn'):
            self.start_gather_btn.config(state=tk.DISABLED)
        if hasattr(self, 'stop_gather_btn'):
            self.stop_gather_btn.config(state=tk.NORMAL)
        if hasattr(self, 'gather_log'):
            self.gather_log.config(state=tk.NORMAL)
            self.gather_log.delete(1.0, tk.END)
            self.gather_log.config(state=tk.DISABLED)
        
        threading.Thread(target=self.gather_rss_thread, args=(device_id, max_marches), 
                        daemon=True).start()
    
    def stop_gather(self):
        self.stop_gather_flag = True
        if hasattr(self, 'stop_gather_btn'):
            self.stop_gather_btn.config(state=tk.DISABLED)
        if hasattr(self, 'start_gather_btn'):
            self.start_gather_btn.config(state=tk.NORMAL)
    
    def start_clearfog(self):
        if not OPENCV_AVAILABLE:
            messagebox.showerror("Error", "OpenCV not available!\nInstall: pip install opencv-python")
            return
        
        devices = self.list_devices()
        online_devices = [d for d, s in devices if s == "online"]
        
        if not online_devices:
            messagebox.showwarning("No Devices", "No online devices available!")
            return
        
        # Select device
        if len(online_devices) > 1:
            device_window = tk.Toplevel(self.root)
            device_window.title("Select Device")
            device_window.geometry("300x250")
            device_window.configure(bg="#2C3E50")
            device_window.transient(self.root)
            device_window.grab_set()
            
            tk.Label(device_window, text="Select a device:", bg="#2C3E50", fg="white", 
                    font=("Arial", 10)).pack(pady=10)
            
            device_listbox = tk.Listbox(device_window, bg="#34495E", fg="white", font=("Arial", 9))
            device_listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
            
            for dev in online_devices:
                device_listbox.insert(tk.END, dev)
            
            selected_device = [None]
            
            def select():
                if device_listbox.curselection():
                    selected_device[0] = online_devices[device_listbox.curselection()[0]]
                    device_window.destroy()
            
            tk.Button(device_window, text="Select", command=select, bg="#27AE60", fg="white", 
                     font=("Arial", 9), width=15, cursor="hand2").pack(pady=10)
            
            device_window.wait_window()
            
            if not selected_device[0]:
                return
            device_id = selected_device[0]
        else:
            device_id = online_devices[0]
        
        # Start clear fog
        if hasattr(self, 'start_clearfog_btn'):
            self.start_clearfog_btn.config(state=tk.DISABLED)
        if hasattr(self, 'stop_clearfog_btn'):
            self.stop_clearfog_btn.config(state=tk.NORMAL)
        if hasattr(self, 'clearfog_log'):
            self.clearfog_log.config(state=tk.NORMAL)
            self.clearfog_log.delete(1.0, tk.END)
            self.clearfog_log.config(state=tk.DISABLED)
        
        threading.Thread(target=self.clear_fog_thread, args=(device_id,), daemon=True).start()
    
    def stop_clearfog(self):
        self.stop_clear_fog_flag = True
        if hasattr(self, 'stop_clearfog_btn'):
            self.stop_clearfog_btn.config(state=tk.DISABLED)
        if hasattr(self, 'start_clearfog_btn'):
            self.start_clearfog_btn.config(state=tk.NORMAL)
    
    def force_exit(self):
        self.running = False
        self.toggle = False
        self.stop_gather_flag = True
        self.stop_clear_fog_flag = True
        
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
    
    def run(self):
        if not self.show_login():
            print("Login cancelled")
            return
        self.create_gui()

if __name__ == "__main__":
    print("ROK Unified Tool - Initializing...")
    print(f"OpenCV Available: {OPENCV_AVAILABLE}")
    print(f"PyAutoGUI Available: {AUTOGUI_AVAILABLE}")
    print(f"NumPy Available: {NUMPY_AVAILABLE}")
    
    if not AUTOGUI_AVAILABLE:
        print("\n[Warning] AutoFarm features require: pip install pyautogui pillow keyboard")
    
    app = ROKUnifiedTool()
    app.run()