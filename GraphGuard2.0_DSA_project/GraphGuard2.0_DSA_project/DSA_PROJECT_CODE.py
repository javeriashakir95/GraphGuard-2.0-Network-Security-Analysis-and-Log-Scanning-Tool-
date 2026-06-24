import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import matplotlib.pyplot as plt # type: ignore
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import networkx as nx
import random
import heapq
import time
from collections import deque, defaultdict
import json
import csv
import traceback
import numpy as np
import pandas as pd
from collections import defaultdict, Counter
import random
from datetime import datetime, timedelta
import os
import re

# Modern color theme
COLORS = {
    "primary": "#2E3440",
    "secondary": "#4C566A",
    "accent": "#5E81AC",
    "success": "#A3BE8C",
    "warning": "#EBCB8B",
    "danger": "#BF616A",
    "info": "#88C0D0",
    "dark": "#3B4252",
    "light": "#ECEFF4",
    "background": "#D8DEE9"
}

# Theme class for LogScannerPage compatibility
class Theme:
    PRIMARY = "#2E3440"
    SECONDARY = "#4C566A"
    ACCENT = "#5E81AC"
    SUCCESS = "#A3BE8C"
    WARNING = "#EBCB8B"
    DANGER = "#BF616A"
    INFO = "#88C0D0"
    DARK = "#3B4252"
    LIGHT = "#ECEFF4"
    BACKGROUND = "#D8DEE9"
    SURFACE = "#E5E9F0"
    TEXT_PRIMARY = "#2E3440"
    TEXT_SECONDARY = "#4C566A"

# App state for alerts
class AppState:
    def __init__(self):
        self.alerts = []
        self.last_action = ""

APP_STATE = AppState()

class NetworkNode:
    def __init__(self, node_id, node_type, ip_address, security_level):
        self.id = node_id
        self.type = node_type  # 'server', 'workstation', 'router', 'firewall'
        self.ip = ip_address
        self.security_level = security_level  # 1-10, 10 being most secure
        self.compromised = False
        self.risk_level = 0  # 0-10
        self.logs = []
        self.neighbors = {}  # {node_id: weight}
        
    def add_log(self, log_entry):
        self.logs.append(log_entry)
        
    def add_neighbor(self, neighbor_id, weight):
        self.neighbors[neighbor_id] = weight
        
    def __str__(self):
        return f"{self.type.capitalize()} {self.id} ({self.ip}) - Security: {self.security_level}"

class NetworkGraph:
    def __init__(self):
        self.nodes = {}
        self.adjacency_list = defaultdict(dict)
        
    def add_node(self, node):
        self.nodes[node.id] = node
        
    def add_edge(self, node1_id, node2_id, weight=1):
        self.adjacency_list[node1_id][node2_id] = weight
        self.adjacency_list[node2_id][node1_id] = weight
        self.nodes[node1_id].add_neighbor(node2_id, weight)
        self.nodes[node2_id].add_neighbor(node1_id, weight)
        
    def get_node(self, node_id):
        return self.nodes.get(node_id)
        
    def get_neighbors(self, node_id):
        return self.adjacency_list.get(node_id, {})
        
    def bfs_traversal(self, start_node_id):
        visited = set()
        queue = deque([start_node_id])
        traversal_order = []
        
        while queue:
            current_node = queue.popleft()
            if current_node not in visited:
                visited.add(current_node)
                traversal_order.append(current_node)
                for neighbor in self.adjacency_list[current_node]:
                    if neighbor not in visited:
                        queue.append(neighbor)
                        
        return traversal_order
        
    def dijkstra_shortest_path(self, start_node_id, target_node_id=None):
        distances = {node_id: float('inf') for node_id in self.nodes}
        distances[start_node_id] = 0
        previous_nodes = {node_id: None for node_id in self.nodes}
        priority_queue = [(0, start_node_id)]
        
        while priority_queue:
            current_distance, current_node = heapq.heappop(priority_queue)
            
            if current_distance > distances[current_node]:
                continue
                
            if target_node_id and current_node == target_node_id:
                break
                
            for neighbor, weight in self.adjacency_list[current_node].items():
                distance = current_distance + weight
                if distance < distances[neighbor]:
                    distances[neighbor] = distance
                    previous_nodes[neighbor] = current_node
                    heapq.heappush(priority_queue, (distance, neighbor))
                    
        # Reconstruct paths for all nodes
        paths = {}
        for node_id in self.nodes:
            if distances[node_id] == float('inf'):
                paths[node_id] = None
            else:
                path = []
                current = node_id
                while current is not None:
                    path.append(current)
                    current = previous_nodes[current]
                paths[node_id] = list(reversed(path))
                
        return distances, paths

class ThreatDetector:
    def __init__(self):
        self.threat_patterns = {
            "malware": ["suspicious_process", "unusual_port_activity", "file_encryption"],
            "ransomware": ["file_encryption", "bitcoin_address", "ransom_note"],
            "ddos": ["high_traffic_volume", "multiple_connections", "resource_exhaustion"],
            "phishing": ["suspicious_email", "credential_theft", "fake_login_page"],
            "brute_force": ["multiple_failed_logins", "password_guessing", "account_lockout"]
        }
        self.threat_signatures = self._build_threat_signatures()
        
    def _build_threat_signatures(self):
        signatures = {}
        for threat_type, patterns in self.threat_patterns.items():
            for pattern in patterns:
                signatures[pattern] = threat_type
        return signatures
        
    def scan_logs(self, node_logs):
        detected_threats = defaultdict(list)
        for log in node_logs:
            for signature, threat_type in self.threat_signatures.items():
                if signature in log.lower():
                    detected_threats[threat_type].append(log)
                    
        return detected_threats

class LogScannerPage(ttk.Frame):
    __name__ = "LogScannerPage"
    
    def __init__(self, parent, controller):
        super().__init__(parent, padding=12, style="Card.TFrame")  # Changed padding and style
        self.controller = controller
        self.pattern_db = {}
        self.loaded_logs = []
        self.scan_results = []
        self.current_file = None
        
        self._create_widgets()
        self._configure_treeview_tags()
        self._load_threat_patterns()
    
        
    def _create_widgets(self):
        # Header - Matching Alerts & Reports style
        header_frame = ttk.Frame(self, style="Card.TFrame")
        header_frame.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Label(header_frame, text="Log Scanner", 
                 font=("Arial", 18, "bold"),
                 foreground=COLORS["primary"]).pack(anchor="w", side=tk.LEFT)
        
        # Status indicator - Like Alerts page
        self.status_label = ttk.Label(header_frame, text="● READY", 
                                     foreground=COLORS["success"],
                                     font=('Arial', 12, 'bold'))
        self.status_label.pack(anchor="e", side=tk.RIGHT, padx=10)
        
        # Control buttons - Same style as Alerts page
        btn_frame = ttk.Frame(self, style="Card.TFrame")
        btn_frame.pack(fill=tk.X, pady=(0, 12))
        
        ttk.Button(btn_frame, text="Load Log File", 
                  command=self.load_log_file, style='Primary.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Start Scan", 
                  command=self.scan_logs, style='Success.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Clear Results", 
                  command=self.clear_results, style='Danger.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="View Patterns", 
                  command=self.show_patterns, style='Info.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Add Pattern", 
                  command=self.add_custom_pattern, style='Warning.TButton').pack(side=tk.LEFT, padx=5)
        
        # Main content area - Same layout as Alerts page
        content_frame = ttk.Frame(self, style="Card.TFrame")
        content_frame.pack(fill=tk.BOTH, expand=True)
        
        # Left side - Log Preview and Controls
        left_panel = ttk.LabelFrame(content_frame, text="Log Preview", padding="10", style='Card.TFrame')
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        # File info with better styling
        file_info_frame = ttk.Frame(left_panel, style="Card.TFrame")
        file_info_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.file_info = ttk.Label(file_info_frame, text="No file loaded", 
                                  font=("Arial", 10, "bold"),
                                  foreground=COLORS["secondary"])
        self.file_info.pack(anchor="w")
        
        # Text area with theme styling
        text_frame = ttk.Frame(left_panel)
        text_frame.pack(fill=tk.BOTH, expand=True)
        
        self.log_text = tk.Text(text_frame, wrap="word", 
                               font=('Consolas', 9),
                               bg=COLORS["light"],
                               fg=COLORS["primary"],
                               relief=tk.FLAT,
                               padx=10, pady=10,
                               selectbackground=COLORS["accent"])
        
        text_scrollbar = ttk.Scrollbar(text_frame, orient="vertical", 
                                      command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=text_scrollbar.set)
        
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        text_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Right side - Patterns and Results
        
        right_panel = ttk.Frame(content_frame, style="Card.TFrame", width=400)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, padx=(5, 0), expand=False)
        right_panel.pack_propagate(False) # Keep fixed width
        
        # Use Grid layout to force 50/50 vertical split
        right_panel.columnconfigure(0, weight=1)
        right_panel.rowconfigure(0, weight=1) # Patterns gets 50%
        right_panel.rowconfigure(1, weight=1) # Results gets 50%
        
        # --- Top Half: Patterns panel ---
        patterns_frame = ttk.LabelFrame(right_panel, text="Threat Patterns", padding="10", style='Card.TFrame')
        patterns_frame.grid(row=0, column=0, sticky="nsew", pady=(0, 5)) # grid instead of pack
        
        patterns_content = ttk.Frame(patterns_frame)
        patterns_content.pack(fill=tk.BOTH, expand=True)
        
        self.patterns_text = tk.Text(patterns_content, wrap="word",
                                    font=('Consolas', 9),
                                    bg=COLORS["light"],
                                    fg=COLORS["primary"],
                                    relief=tk.FLAT,
                                    padx=10, pady=10)
        
        patterns_scrollbar = ttk.Scrollbar(patterns_content, orient="vertical", 
                                          command=self.patterns_text.yview)
        self.patterns_text.configure(yscrollcommand=patterns_scrollbar.set)
        
        self.patterns_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        patterns_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # --- Bottom Half: Results panel ---
        results_frame = ttk.LabelFrame(right_panel, text="Scan Results", padding="10", style='Card.TFrame')
        results_frame.grid(row=1, column=0, sticky="nsew", pady=(5, 0)) # grid instead of pack
        
        # Treeview
        columns = ("Time", "Severity", "Pattern", "Line", "Match")
        self.results_tree = ttk.Treeview(results_frame, columns=columns, 
                                        show="headings", 
                                        selectmode="browse") 
                                        # Removed 'height=8' to allow auto-fill
        
        # Column configuration
        col_config = {
            "Time": {"width": 80, "anchor": "center"},
            "Severity": {"width": 90, "anchor": "center"},
            "Pattern": {"width": 120, "anchor": "center"},
            "Line": {"width": 60, "anchor": "center"},
            "Match": {"width": 150, "anchor": "w"}
        }
        
        for col in columns:
            self.results_tree.heading(col, text=col)
            self.results_tree.column(col, **col_config[col])
        
        # Scrollbar
        results_scrollbar = ttk.Scrollbar(results_frame, orient="vertical", 
                                         command=self.results_tree.yview)
        self.results_tree.configure(yscrollcommand=results_scrollbar.set)
        
        self.results_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        results_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Bind double-click for details
        self.results_tree.bind("<Double-1>", self.show_full_line)
        
        # Status bar at bottom - Like Alerts page
        status_frame = ttk.Frame(self, style="Card.TFrame", padding=10)
        status_frame.pack(fill=tk.X, side=tk.BOTTOM, pady=(15, 0))
        
        self.status_var = tk.StringVar(value="Ready to load log files")
        status_label = ttk.Label(status_frame, textvariable=self.status_var,
                               font=('Arial', 9),
                               foreground=COLORS["secondary"])
        status_label.pack(side=tk.LEFT)
        
    def _configure_treeview_tags(self):
        """Configure severity coloring matching Alerts page"""
        self.results_tree.tag_configure("critical", background='#ffcccc')
        self.results_tree.tag_configure("high", background='#ffe6cc')
        self.results_tree.tag_configure("medium", background='#fff0cc')
        self.results_tree.tag_configure("low", background='#e6f7ff')
        self.results_tree.tag_configure("info", background=COLORS["light"])
        
    def _load_threat_patterns(self):
        """Initialize threat signature database"""
        self.pattern_db = {
            "SQL_INJ_01": {"pattern": "'.*OR.*1=1", "severity": "HIGH", "type": "SQL Injection"},
            "SQL_INJ_02": {"pattern": "UNION.*SELECT", "severity": "HIGH", "type": "SQL Injection"},
            "SQL_INJ_03": {"pattern": "DROP.*TABLE", "severity": "CRITICAL", "type": "SQL Injection"},
            "BRUTE_01": {"pattern": "Failed password for", "severity": "HIGH", "type": "Brute Force"},
            "PORT_SCAN_01": {"pattern": "nmap.*-sS", "severity": "MEDIUM", "type": "Port Scan"},
            "XSS_01": {"pattern": "<script.*>", "severity": "HIGH", "type": "XSS"},
            "SUSPICIOUS_LOGIN": {"pattern": "login.*failed", "severity": "MEDIUM", "type": "Authentication"},
            "FILE_UPLOAD": {"pattern": "upload.*\\.(php|exe|jar)", "severity": "MEDIUM", "type": "File Upload"}
        }
        self.update_patterns_display()
        
    def update_patterns_display(self):
        """Update patterns display with clean formatting"""
        self.patterns_text.config(state="normal")
        self.patterns_text.delete("1.0", tk.END)
        
        # Group by type for better organization
        patterns_by_type = defaultdict(list)
        for pattern_id, pattern_info in self.pattern_db.items():
            patterns_by_type[pattern_info["type"]].append((pattern_id, pattern_info))
        
        for pattern_type, patterns in patterns_by_type.items():
            # Add colored headers based on severity
            self.patterns_text.insert(tk.END, f"🔍 {pattern_type}:\n", "header")
            for pattern_id, pattern_info in patterns:
                # Color code based on severity
                severity_tag = pattern_info['severity'].lower()
                line = f"  • {pattern_id}: {pattern_info['pattern']}\n"
                self.patterns_text.insert(tk.END, line, severity_tag)
            self.patterns_text.insert(tk.END, "\n")
        
        # Configure text tags for coloring
        self.patterns_text.tag_configure("header", font=('Arial', 9, 'bold'), 
                                       foreground=COLORS["primary"])
        self.patterns_text.tag_configure("critical", foreground=COLORS["danger"])
        self.patterns_text.tag_configure("high", foreground=COLORS["warning"])
        self.patterns_text.tag_configure("medium", foreground=COLORS["accent"])
        self.patterns_text.tag_configure("low", foreground=COLORS["success"])
        
        self.patterns_text.config(state="disabled")
        
    def load_log_file(self):
        """Load log file with professional file dialog"""
        filepath = filedialog.askopenfilename(
            title="Select Log File",
            filetypes=[
                ("Log files", "*.log"),
                ("Text files", "*.txt"),
                ("CSV files", "*.csv"),
                ("All files", "*.*")
            ]
        )
        
        if not filepath:
            return
        
        try:
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                self.loaded_logs = f.readlines()
            
            self.current_file = filepath
            self.update_log_preview()
            
            # Update UI with theme colors
            self.file_info.config(text=f"📁 Loaded: {os.path.basename(filepath)} ({len(self.loaded_logs)} lines)")
            self.status_var.set("✅ File loaded successfully - Ready to scan")
            self.status_label.config(text="● READY", foreground=COLORS["success"])
            
            # Add to alerts with proper styling
            alert = {
                "time": datetime.now().isoformat(timespec='seconds'),
                "type": "log_load",
                "message": f"Loaded log file: {os.path.basename(filepath)}",
                "node": "Log Scanner",
                "threat_score": 0.5,
                "path": "N/A",
                "status": "INFO",
                "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "logs": f"File: {filepath}, Lines: {len(self.loaded_logs)}"
            }
            APP_STATE.alerts.append(alert)
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load file: {e}")
            self.status_var.set(f"❌ Error loading file: {e}")
            self.status_label.config(text="● ERROR", foreground=COLORS["danger"])
            
    def update_log_preview(self):
        """Update log preview with theme styling"""
        self.log_text.config(state="normal")
        self.log_text.delete("1.0", tk.END)
        
        if not self.loaded_logs:
            self.log_text.insert(tk.END, "No log data available.\n\nLoad a log file to begin analysis.", "info")
            self.log_text.tag_configure("info", foreground=COLORS["secondary"], font=('Arial', 10, 'italic'))
        else:
            # Add some basic syntax highlighting
            for i, line in enumerate(self.loaded_logs[:100]):  # Show first 100 lines
                line = line.rstrip()
                if "ERROR" in line.upper():
                    self.log_text.insert(tk.END, line + "\n", "error")
                elif "WARN" in line.upper():
                    self.log_text.insert(tk.END, line + "\n", "warn")
                elif "INFO" in line.upper():
                    self.log_text.insert(tk.END, line + "\n", "info")
                else:
                    self.log_text.insert(tk.END, line + "\n")
            
            if len(self.loaded_logs) > 100:
                self.log_text.insert(tk.END, f"\n[... +{len(self.loaded_logs)-100} more lines]\n", "info")
        
        # Configure text tags for log coloring
        self.log_text.tag_configure("error", foreground=COLORS["danger"])
        self.log_text.tag_configure("warn", foreground=COLORS["warning"])
        self.log_text.tag_configure("info", foreground=COLORS["success"])
        
        self.log_text.config(state="disabled")
        
    def scan_logs(self):
        """Perform log scanning with theme updates"""
        if not self.loaded_logs:
            messagebox.showwarning("No Logs", "Please load a log file first!")
            return
        
        self.status_var.set("🔄 Scanning logs...")
        self.status_label.config(text="● SCANNING", foreground=COLORS["warning"])
        
        # Clear previous results
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
        
        self.scan_results = []
        threats_found = 0
        
        # Pre-compile patterns for performance
        compiled_patterns = {}
        for pattern_id, pattern_info in self.pattern_db.items():
            try:
                compiled_patterns[pattern_id] = re.compile(pattern_info["pattern"], re.IGNORECASE)
            except re.error:
                continue
        
        # Perform scan
        for line_num, line in enumerate(self.loaded_logs, 1):
            for pattern_id, compiled_pattern in compiled_patterns.items():
                if compiled_pattern.search(line):
                    threats_found += 1
                    pattern_info = self.pattern_db[pattern_id]
                    self.scan_results.append({
                        "line_number": line_num,
                        "pattern_id": pattern_id,
                        "pattern_type": pattern_info["type"],
                        "severity": pattern_info["severity"],
                        "matched_text": line.strip()[:80],
                        "full_line": line.strip(),
                        "timestamp": datetime.now().isoformat()
                    })
        
        self.display_scan_results()
        self.generate_alerts_from_scan()
        
        # Update status with theme colors
        if threats_found > 0:
            self.status_var.set(f"⚠️ Scan complete: {threats_found} threats found in {len(self.loaded_logs)} lines")
            self.status_label.config(text=f"● {threats_found} THREATS", foreground=COLORS["danger"])
            messagebox.showwarning("Scan Complete", 
                                 f"Scan completed. Found {threats_found} potential security threats.")
        else:
            self.status_var.set(f"✅ Scan complete: No threats detected in {len(self.loaded_logs)} lines")
            self.status_label.config(text="● CLEAN", foreground=COLORS["success"])
            messagebox.showinfo("Scan Complete", "Scan completed. No threats detected.")
            
    def display_scan_results(self):
        """Display results with theme coloring"""
        for result in self.scan_results:
            time_str = datetime.now().strftime("%H:%M:%S")
            
            self.results_tree.insert("", "end", values=(
                time_str,
                result["severity"],
                result["pattern_id"],
                result["line_number"],
                result["matched_text"]
            ), tags=(result["severity"].lower(),))

    def clear_results(self):
        """Clear scan results and reset the display"""
        # Clear the results tree
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
        
        # Clear scan results list
        self.scan_results = []
        
        # Update status
        self.status_var.set("Results cleared - Ready for new scan")
        self.status_label.config(text="● READY", foreground=COLORS["success"])
        
        # Add to alerts
        alert = {
            "time": datetime.now().isoformat(timespec='seconds'),
            "type": "log_clear",
            "message": "Cleared all scan results",
            "node": "Log Scanner",
            "threat_score": 0.1,
            "path": "N/A",
            "status": "INFO",
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "logs": "Scan results cleared from memory"
        }
        APP_STATE.alerts.append(alert)

    def show_patterns(self):
        """Show pattern information dialog"""
        pattern_text = "🔍 THREAT PATTERN DATABASE\n" + "="*40 + "\n\n"
        pattern_text += f"Total Patterns: {len(self.pattern_db)}\n\n"
    
        # Count by severity
        severity_count = defaultdict(int)
        for pattern_data in self.pattern_db.values():  # Changed variable name to avoid conflict
            severity_count[pattern_data["severity"]] += 1
    
        pattern_text += "📊 PATTERN DISTRIBUTION:\n"
        for severity, count in severity_count.items():
            pattern_text += f"• {severity}: {count} patterns\n"
    
    # Add pattern details
        pattern_text += "\n🔍 PATTERN DETAILS:\n"
        for pattern_id, pattern_data in self.pattern_db.items():
            pattern_text += f"• {pattern_id}: {pattern_data['pattern']} ({pattern_data['severity']})\n"
    
        messagebox.showinfo("Threat Patterns", pattern_text)

    def add_custom_pattern(self):
        """Add custom threat pattern"""
        pattern_id = simpledialog.askstring("Add Pattern", "Enter pattern ID:")
        if not pattern_id:
            return
            
        pattern = simpledialog.askstring("Add Pattern", "Enter regex pattern:")
        if not pattern:
            return
            
        # Validate regex
        try:
            re.compile(pattern)
        except re.error as e:
            messagebox.showerror("Invalid Pattern", f"Invalid regex pattern: {e}")
            return
            
        severity = simpledialog.askstring("Add Pattern", "Enter severity (CRITICAL/HIGH/MEDIUM/LOW):")
        if not severity or severity.upper() not in ["CRITICAL", "HIGH", "MEDIUM", "LOW"]:
            messagebox.showerror("Invalid Severity", "Severity must be CRITICAL, HIGH, MEDIUM, or LOW")
            return
            
        pattern_type = simpledialog.askstring("Add Pattern", "Enter pattern type:")
        if not pattern_type:
            return
            
        # Add to database
        self.pattern_db[pattern_id] = {
            "pattern": pattern,
            "severity": severity.upper(),
            "type": pattern_type
        }
        
        self.update_patterns_display()
        messagebox.showinfo("Success", f"Pattern '{pattern_id}' added successfully!")

    def show_full_line(self, event):
        """Show full log line when double-clicking a result"""
        selected = self.results_tree.selection()
        if not selected:
            return
            
        item = selected[0]
        values = self.results_tree.item(item, "values")
        
        if values and len(values) >= 5:
            line_num = values[3]  # Line number is 4th column
            pattern = values[2]   # Pattern is 3rd column
            
            # Find the full line
            full_line = ""
            if self.loaded_logs and line_num.isdigit():
                line_idx = int(line_num) - 1
                if 0 <= line_idx < len(self.loaded_logs):
                    full_line = self.loaded_logs[line_idx].strip()
            
            # Show in message box
            messagebox.showinfo(
                "Full Log Line", 
                f"Line {line_num} - Pattern: {pattern}\n\n{full_line}"
            )

    def generate_alerts_from_scan(self):
        """Generate alerts from scan results"""
        if not self.scan_results:
            return
            
        for result in self.scan_results:
            # Convert severity to threat score
            severity_map = {"CRITICAL": 90, "HIGH": 75, "MEDIUM": 50, "LOW": 25}
            threat_score = severity_map.get(result["severity"], 50)
            
            alert = {
                "time": result["timestamp"],
                "type": "log_scan",
                "message": f"Threat detected: {result['pattern_type']}",
                "node": f"Log Line {result['line_number']}",
                "threat_score": threat_score,
                "path": f"Pattern: {result['pattern_id']}",
                "status": "active",
                "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "logs": result["full_line"][:100],
                "attack_type": result["pattern_type"],
                "security_level": 5,
                "logs_count": 1,
                "detection": "Pattern Matching",
                "recommendations": [
                    "Review the detected log line",
                    "Check for false positives",
                    "Update pattern database if needed"
                ]
            }
            APP_STATE.alerts.append(alert)

    def on_show(self):
        """Called when the page is shown"""
        return "Log Scanner — Ready"

class AlertsReportsPage(ttk.Frame):
    __name__ = "AlertsReportsPage"
    
    def __init__(self, parent, controller):
        super().__init__(parent, padding=12, style="Card.TFrame")
        self.controller = controller
        
        # Header
        header_frame = ttk.Frame(self, style="Card.TFrame")
        header_frame.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Label(header_frame, text="Alerts & Reports", 
                 font=("Arial", 18, "bold"),
                 foreground=COLORS["primary"]).pack(anchor="w", side=tk.LEFT)
        
        # Status indicator
        self.status_label = ttk.Label(header_frame, text="● ACTIVE ALERTS", 
                                     foreground=COLORS["warning"],
                                     font=('Arial', 12, 'bold'))
        self.status_label.pack(anchor="e", side=tk.RIGHT, padx=10)
        
        
        # Control buttons
        btn_frame = ttk.Frame(self, style="Card.TFrame")
        btn_frame.pack(fill=tk.X, pady=(0, 12))
        
        ttk.Button(btn_frame, text="Export to CSV", 
                  command=self.export_to_csv, style='Primary.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Clear Alerts", 
                  command=self.clear_alerts_data, style='Danger.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Refresh Alerts", 
                  command=self.refresh_alerts, style='Success.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Generate Sample Data", 
                  command=self.generate_sample_alerts, style='Warning.TButton').pack(side=tk.LEFT, padx=5)
        
        # Main content area
        content_frame = ttk.Frame(self, style="Card.TFrame")
        content_frame.pack(fill=tk.BOTH, expand=True)
        
        # Left side - Table
        table_frame = ttk.LabelFrame(content_frame, text="Security Alerts", padding="10", style='Card.TFrame')
        table_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        columns = ("Time", "Node", "Threat Score", "Attack Path", "Status", "Action")
        
        self.tree = ttk.Treeview(table_frame, columns=columns, show="headings", selectmode="browse")
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        col_widths = {"Time": 120, "Node": 100, "Threat Score": 100, "Attack Path": 200, "Status": 100, "Action": 120}
        
        for col in columns:
            self.tree.heading(col, text=col, command=lambda c=col: self.sort_by(c))
            self.tree.column(col, width=col_widths.get(col, 100), anchor="center")

        # Add scrollbar to table
        scrollbar = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.configure(yscroll=scrollbar.set)
        
        # Configure treeview tags for different statuses
        self.tree.tag_configure('critical', background='#ffcccc')
        self.tree.tag_configure('high', background='#ffe6cc')
        self.tree.tag_configure('medium', background='#fff0cc')
        self.tree.tag_configure('low', background='#e6f7ff')
        self.tree.tag_configure('resolved', background=COLORS["success"], foreground='white')
        
        # Right side - Details and Analytics
        right_frame = ttk.Frame(content_frame, style="Card.TFrame", width=400)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, padx=(5, 0), expand=False)
        right_frame.pack_propagate(False)
        
        # Alert Details
        detail_frame = ttk.LabelFrame(right_frame, text="Alert Details", padding="10", style='Card.TFrame')
        detail_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.detail_text = tk.Text(detail_frame, height=8, wrap="word", state="disabled", 
                                  font=('Arial', 9),
                                  bg=COLORS["light"],
                                  fg=COLORS["primary"],
                                  relief=tk.FLAT,
                                  padx=10, pady=10)
        self.detail_text.pack(fill=tk.BOTH, expand=True)
        
        # Analytics Frame
        analytics_frame = ttk.LabelFrame(right_frame, text="Threat Analytics", padding="10", style='Card.TFrame')
        analytics_frame.pack(fill=tk.BOTH, expand=True)
        
        self.analytics_text = tk.Text(analytics_frame, height=6, wrap="word", state="disabled",
                                     font=('Arial', 9),
                                     bg=COLORS["light"],
                                     fg=COLORS["primary"],
                                     relief=tk.FLAT,
                                     padx=10, pady=10)
        self.analytics_text.pack(fill=tk.BOTH, expand=True)
        
        # Bind events
        self.tree.bind("<<TreeviewSelect>>", self.show_details)
        self.tree.bind('<ButtonRelease-1>', self.check_action_click)
        
        self.alert_list = []
        self.load_alerts(APP_STATE.alerts)
        self.update_analytics()

    def generate_sample_alerts(self):
        """Generate sample alert data for demonstration"""
        sample_alerts = []
        attack_types = ["malware", "ransomware", "ddos", "phishing", "brute_force"]
        nodes = [f"Node_{i}" for i in range(1, 11)]
        statuses = ["active", "active", "active", "investigating", "resolved"]
    
        for i in range(15):
            alert = {
                "time": (datetime.now() - timedelta(minutes=random.randint(1, 120))).isoformat(),
                "node": random.choice(nodes),
                "threat_score": random.randint(20, 95),
                "path": " -> ".join(random.sample(nodes, min(3, len(nodes)))),
                "status": random.choice(statuses),
                "attack_type": random.choice(attack_types),
                "security_level": random.randint(3, 10),
                "logs_count": random.randint(1, 15),
                "detection": random.choice(["Pattern Matching", "Behavioral Analysis", "Signature Detection"]),
                "recommendations": [
                    "Isolate affected node",
                    "Update security policies",
                    "Run deep scan",
                    "Review access logs"
                ]
            }
            sample_alerts.append(alert)
    
        APP_STATE.alerts = sample_alerts
        self.load_alerts(APP_STATE.alerts)
        self.update_analytics()
        messagebox.showinfo("Sample Data", "Generated 15 sample alerts for demonstration.")

    def load_alerts(self, alert_list):
        self.alert_list = alert_list
        self.clear_alerts_view()
        
        for alert in alert_list:
            node = alert.get("node", "")
            score = alert.get("threat_score", 0)
            path = alert.get("path", "")
            status = alert.get("status", "medium").lower()
            
            # Safely parse time
            try:
                time_obj = datetime.fromisoformat(alert.get("time", datetime.now().isoformat()))
            except ValueError:
                time_obj = datetime.now()
                
            time_str = time_obj.strftime("%H:%M:%S")
            
            # Determine tag based on status and score
            tag = status
            if status == "active":
                if score >= 80:
                    tag = "critical"
                elif score >= 60:
                    tag = "high"
                elif score >= 40:
                    tag = "medium"
                else:
                    tag = "low"
            
            self.tree.insert("", "end", 
                             values=(time_str, node, score, path, status.capitalize(), "View/Highlight"), 
                             tags=(tag,))
        
        self.update_status_indicator()

    def sort_by(self, column):
        col_map = {"Time": 0, "Node": 1, "Threat Score": 2, "Attack Path": 3, "Status": 4, "Action": 5}
        
        if column not in col_map:
            return
            
        data = [(self.tree.set(child, column), child) for child in self.tree.get_children()]
        
        is_numeric = column == "Threat Score"
        
        try:
            if is_numeric:
                data.sort(key=lambda t: float(t[0]), reverse=True)  # Highest scores first
            else:
                data.sort(key=lambda t: t[0], reverse=False)
        except ValueError:
            data.sort(key=lambda t: t[0], reverse=False)
            
        for index, (val, child) in enumerate(data):
            self.tree.move(child, "", index)

    def check_action_click(self, event):
        """Checks if the user clicked inside the 'Action' column and triggers highlight."""
        region = self.tree.identify("region", event.x, event.y)
        if region != "cell":
            return
        
        column = self.tree.identify_column(event.x)
        try:
            col_text = self.tree.heading(column)['text']
        except tk.TclError:
            return
            
        if col_text == "Action":
            item = self.tree.identify_row(event.y)
            if item:
                item_values = self.tree.item(item, "values")
                if item_values and len(item_values) > 1:
                    node = item_values[1]
                    self.highlight_node(node)

    def highlight_node(self, node):
        """Highlight node in network visualization"""
        messagebox.showinfo("Highlight Node", 
                           f"Would highlight node: {node} in network visualization.\n\nThis feature integrates with the main network view to focus on the selected node.")

    def show_details(self, event):
        selected = self.tree.selection()
        if not selected:
            self.detail_text.config(state="normal")
            self.detail_text.delete("1.0", tk.END)
            self.detail_text.config(state="disabled")
            return
            
        values = self.tree.item(selected[0])["values"]
        if not values or len(values) < 6:
            return

        time_str, node, score, path, status, _ = values
        
        # Find the full alert object
        full_alert = next((alert for alert in self.alert_list 
                           if alert.get("node") == node 
                           and datetime.fromisoformat(alert.get("time")).strftime("%H:%M:%S") == time_str), None)

        # Create detailed report
        details = f"🔍 ALERT DETAILS\n{'='*40}\n"
        details += f"⏰ Time: {time_str}\n"
        details += f"🖥️  Node: {node}\n"
        details += f"⚠️  Threat Score: {score}/100\n"
        details += f"🛣️  Attack Path: {path}\n"
        details += f"📊 Status: {status}\n"
        
        if full_alert:
            details += f"\n📋 ADDITIONAL INFO:\n"
            details += f"🔒 Security Level: {full_alert.get('security_level', 'N/A')}\n"
            details += f"🎯 Attack Type: {full_alert.get('attack_type', 'N/A')}\n"
            details += f"📝 Logs Found: {full_alert.get('logs_count', 0)}\n"
            details += f"🔍 Detection Method: {full_alert.get('detection', 'Pattern Matching')}\n"
            
            recommendations = full_alert.get('recommendations', [])
            if recommendations:
                details += f"\n💡 RECOMMENDATIONS:\n"
                for rec in recommendations:
                    details += f"• {rec}\n"

        self.detail_text.config(state="normal")
        self.detail_text.delete("1.0", tk.END)
        self.detail_text.insert(tk.END, details)
        self.detail_text.config(state="disabled")

    def export_to_csv(self):
        if not self.alert_list:
            messagebox.showwarning("No Data", "No alerts to export!")
            return
            
        filepath = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
            title="Export Alerts to CSV"
        )
        
        if not filepath:
            return
            
        try:
            with open(filepath, "w", newline="", encoding='utf-8') as f:
                writer = csv.writer(f)
                # Enhanced header with more details
                writer.writerow(["Timestamp", "Time", "Node", "Threat_Score", "Attack_Path", "Status", 
                               "Attack_Type", "Security_Level", "Logs_Count", "Detection_Method"])
                
                for alert in self.alert_list:
                    try:
                        time_obj = datetime.fromisoformat(alert.get("time", datetime.now().isoformat()))
                        time_display = time_obj.strftime("%H:%M:%S")
                        timestamp = time_obj.isoformat()
                    except ValueError:
                        time_display = "N/A"
                        timestamp = "N/A"
                        
                    writer.writerow([
                        timestamp,
                        time_display,
                        alert.get("node", ""),
                        alert.get("threat_score", ""),
                        alert.get("path", ""),
                        alert.get("status", ""),
                        alert.get("attack_type", ""),
                        alert.get("security_level", ""),
                        alert.get("logs_count", 0),
                        alert.get("detection", "Pattern Matching")
                    ])
                    
            messagebox.showinfo("Export Complete", 
                              f"Alerts successfully exported to:\n{filepath}\n\nTotal records: {len(self.alert_list)}")
        except Exception as e:
            messagebox.showerror("Export Error", f"Failed to export file:\n{str(e)}")

    def clear_alerts_view(self):
        """Clears only the Treeview items and detail box."""
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.detail_text.config(state="normal")
        self.detail_text.delete("1.0", tk.END)
        self.detail_text.config(state="disabled")

    def clear_alerts_data(self):
        """Clears the Treeview items, detail box, and the data list in AppState."""
        if not self.alert_list:
            messagebox.showinfo("No Alerts", "There are no alerts to clear.")
            return
            
        if messagebox.askyesno("Confirm Clear", "Are you sure you want to clear all alerts? This action cannot be undone."):
            self.clear_alerts_view()
            self.alert_list = []
            APP_STATE.alerts = []
            self.update_analytics()
            self.update_status_indicator()
            messagebox.showinfo("Alerts Cleared", "All alerts have been removed from memory and the view.")

    def refresh_alerts(self):
        self.load_alerts(APP_STATE.alerts)
        self.update_analytics()
        messagebox.showinfo("Refresh Complete", f"Alerts refreshed successfully!\nTotal alerts: {len(APP_STATE.alerts)}")

    def generate_sample_alerts(self):
        """Generate sample alert data for demonstration"""
        sample_alerts = []
        attack_types = ["malware", "ransomware", "ddos", "phishing", "brute_force"]
        nodes = [f"Node_{i}" for i in range(1, 11)]
        statuses = ["active", "active", "active", "investigating", "resolved"]
        
        for i in range(15):
            alert = {
                "time": (datetime.now() - timedelta(minutes=random.randint(1, 120))).isoformat(),
                "node": random.choice(nodes),
                "threat_score": random.randint(20, 95),
                "path": " -> ".join(random.sample(nodes, min(3, len(nodes)))),
                "status": random.choice(statuses),
                "attack_type": random.choice(attack_types),
                "security_level": random.randint(3, 10),
                "logs_count": random.randint(1, 15),
                "detection": random.choice(["Pattern Matching", "Behavioral Analysis", "Signature Detection"]),
                "recommendations": [
                    "Isolate affected node",
                    "Update security policies",
                    "Run deep scan",
                    "Review access logs"
                ]
            }
            sample_alerts.append(alert)
        
        APP_STATE.alerts = sample_alerts
        self.load_alerts(APP_STATE.alerts)
        self.update_analytics()
        messagebox.showinfo("Sample Data", "Generated 15 sample alerts for demonstration.")

    def update_analytics(self):
        """Update the analytics panel with threat statistics"""
        if not self.alert_list:
            analytics_text = "📊 THREAT ANALYTICS\n" + "="*30 + "\n\nNo alerts to analyze.\n\nGenerate sample data or run simulations to see analytics here."
        else:
            total_alerts = len(self.alert_list)
            active_alerts = len([a for a in self.alert_list if a.get('status') == 'active'])
            high_risk = len([a for a in self.alert_list if a.get('threat_score', 0) >= 70])
            avg_score = sum(a.get('threat_score', 0) for a in self.alert_list) / total_alerts
            
            # Count by attack type
            attack_counts = {}
            for alert in self.alert_list:
                attack_type = alert.get('attack_type', 'unknown')
                attack_counts[attack_type] = attack_counts.get(attack_type, 0) + 1
            
            analytics_text = "📊 THREAT ANALYTICS\n" + "="*30 + "\n"
            analytics_text += f"📈 Total Alerts: {total_alerts}\n"
            analytics_text += f"🔴 Active Alerts: {active_alerts}\n"
            analytics_text += f"⚠️  High Risk: {high_risk}\n"
            analytics_text += f"📊 Avg Threat Score: {avg_score:.1f}/100\n\n"
            
            analytics_text += "🎯 ATTACK DISTRIBUTION:\n"
            for attack_type, count in attack_counts.items():
                percentage = (count / total_alerts) * 100
                analytics_text += f"• {attack_type}: {count} ({percentage:.1f}%)\n"
        
        self.analytics_text.config(state="normal")
        self.analytics_text.delete("1.0", tk.END)
        self.analytics_text.insert(tk.END, analytics_text)
        self.analytics_text.config(state="disabled")

    def update_status_indicator(self):
        """Update the status indicator based on current alerts"""
        if not self.alert_list:
            self.status_label.config(text="● NO ALERTS", foreground=COLORS["success"])
        else:
            active_alerts = len([a for a in self.alert_list if a.get('status') == 'active'])
            if active_alerts > 0:
                self.status_label.config(text=f"● {active_alerts} ACTIVE ALERTS", foreground=COLORS["danger"])
            else:
                self.status_label.config(text="● ALL RESOLVED", foreground=COLORS["success"])

    def on_show(self):
        self.refresh_alerts()
        return "Alerts — Ready"

class AnalyticsPage(ttk.Frame):
    __name__ = "AnalyticsPage"
    
    def __init__(self, parent, controller):
        super().__init__(parent, padding=12, style="Card.TFrame")
        self.controller = controller
        self.analytics_data = {}
        
        self._create_widgets()
        self._setup_charts()
        
    def _create_widgets(self):
        # Header
        header_frame = ttk.Frame(self, style="Card.TFrame")
        header_frame.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Label(header_frame, text="Security Analytics", 
                 font=("Arial", 18, "bold"),
                 foreground=COLORS["primary"]).pack(anchor="w", side=tk.LEFT)
        
        # Status indicator
        self.status_label = ttk.Label(header_frame, text="● ANALYTICS READY", 
                                     foreground=COLORS["info"],
                                     font=('Arial', 12, 'bold'))
        self.status_label.pack(anchor="e", side=tk.RIGHT, padx=10)
        
        # Control buttons
        btn_frame = ttk.Frame(self, style="Card.TFrame")
        btn_frame.pack(fill=tk.X, pady=(0, 12))
        
        ttk.Button(btn_frame, text="Refresh Analytics", 
                  command=self.refresh_analytics, style='Primary.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Export Report", 
                  command=self.export_analytics_report, style='Success.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Generate Sample Data", 
                  command=self.generate_sample_analytics, style='Warning.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Clear Analytics", 
                  command=self.clear_analytics, style='Danger.TButton').pack(side=tk.LEFT, padx=5)
        
        # Main content area with tabs
        self.analytics_notebook = ttk.Notebook(self)
        self.analytics_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Overview Tab
        self.overview_frame = ttk.Frame(self.analytics_notebook, style="Card.TFrame")
        self.analytics_notebook.add(self.overview_frame, text="Overview")
        self._setup_overview_tab()
        
        # Threat Intelligence Tab
        self.threat_frame = ttk.Frame(self.analytics_notebook, style="Card.TFrame")
        self.analytics_notebook.add(self.threat_frame, text="Threat Intelligence")
        self._setup_threat_tab()
        
        # Network Health Tab
        self.health_frame = ttk.Frame(self.analytics_notebook, style="Card.TFrame")
        self.analytics_notebook.add(self.health_frame, text="Network Health")
        self._setup_health_tab()
        
        # Performance Metrics Tab
        self.performance_frame = ttk.Frame(self.analytics_notebook, style="Card.TFrame")
        self.analytics_notebook.add(self.performance_frame, text="Performance")
        self._setup_performance_tab()
        
        # Status bar
        status_frame = ttk.Frame(self, style="Card.TFrame", padding=10)
        status_frame.pack(fill=tk.X, side=tk.BOTTOM, pady=(15, 0))
        
        self.status_var = tk.StringVar(value="Analytics dashboard ready - Load data to begin")
        status_label = ttk.Label(status_frame, textvariable=self.status_var,
                               font=('Arial', 9),
                               foreground=COLORS["secondary"])
        status_label.pack(side=tk.LEFT)
        
    def _setup_overview_tab(self):
        """Setup the overview tab with key metrics and charts"""
        # Create a grid layout for overview
        overview_container = ttk.Frame(self.overview_frame)
        overview_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Top row - Key Metrics
        metrics_frame = ttk.Frame(overview_container)
        metrics_frame.pack(fill=tk.X, pady=(0, 15))
        
        # Key metrics cards
        metrics_data = [
            {"title": "Total Alerts", "value": "0", "color": COLORS["primary"], "icon": "📊"},
            {"title": "Active Threats", "value": "0", "color": COLORS["danger"], "icon": "⚠️"},
            {"title": "Network Nodes", "value": "0", "color": COLORS["info"], "icon": "🌐"},
            {"title": "Security Score", "value": "0%", "color": COLORS["success"], "icon": "🛡️"}
        ]
        
        self.metric_labels = {}
        for i, metric in enumerate(metrics_data):
            card = ttk.LabelFrame(metrics_frame, text=metric["title"], padding="15", style='Card.TFrame')
            card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
            
            # Icon and value
            icon_label = ttk.Label(card, text=metric["icon"], font=('Arial', 16))
            icon_label.pack(anchor=tk.W)
            
            value_label = ttk.Label(card, text=metric["value"], 
                                  font=('Arial', 20, 'bold'),
                                  foreground=metric["color"])
            value_label.pack(anchor=tk.W, pady=(5, 0))
            
            self.metric_labels[metric["title"]] = value_label
        
        # Middle row - Charts
        charts_frame = ttk.Frame(overview_container)
        charts_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Left chart - Alert Trends
        left_chart_frame = ttk.LabelFrame(charts_frame, text="Alert Trends (Last 7 Days)", padding="10", style='Card.TFrame')
        left_chart_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        self.trend_fig, self.trend_ax = plt.subplots(figsize=(6, 4), facecolor=COLORS["light"])
        self.trend_canvas = FigureCanvasTkAgg(self.trend_fig, left_chart_frame)
        self.trend_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Right chart - Threat Distribution
        right_chart_frame = ttk.LabelFrame(charts_frame, text="Threat Distribution", padding="10", style='Card.TFrame')
        right_chart_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        self.distribution_fig, self.distribution_ax = plt.subplots(figsize=(6, 4), facecolor=COLORS["light"])
        self.distribution_canvas = FigureCanvasTkAgg(self.distribution_fig, right_chart_frame)
        self.distribution_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Bottom row - Recent Activity
        activity_frame = ttk.LabelFrame(overview_container, text="Recent Security Events", padding="10", style='Card.TFrame')
        activity_frame.pack(fill=tk.X, pady=(10, 0))
        
        # Treeview for recent events
        columns = ("Time", "Event Type", "Severity", "Node", "Description")
        self.activity_tree = ttk.Treeview(activity_frame, columns=columns, show="headings", height=6)
        
        col_config = {
            "Time": {"width": 120, "anchor": "center"},
            "Event Type": {"width": 120, "anchor": "center"},
            "Severity": {"width": 80, "anchor": "center"},
            "Node": {"width": 100, "anchor": "center"},
            "Description": {"width": 200, "anchor": "w"}
        }
        
        for col in columns:
            self.activity_tree.heading(col, text=col)
            self.activity_tree.column(col, **col_config[col])
        
        scrollbar = ttk.Scrollbar(activity_frame, orient="vertical", command=self.activity_tree.yview)
        self.activity_tree.configure(yscrollcommand=scrollbar.set)
        
        self.activity_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Configure treeview tags
        self.activity_tree.tag_configure("critical", background='#ffcccc')
        self.activity_tree.tag_configure("high", background='#ffe6cc')
        self.activity_tree.tag_configure("medium", background='#fff0cc')
        self.activity_tree.tag_configure("low", background='#e6f7ff')
        
    def _setup_threat_tab(self):
        """Setup threat intelligence tab"""
        threat_container = ttk.Frame(self.threat_frame)
        threat_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Left side - Threat metrics
        left_panel = ttk.Frame(threat_container)
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        # Threat level gauge
        threat_gauge_frame = ttk.LabelFrame(left_panel, text="Overall Threat Level", padding="15", style='Card.TFrame')
        threat_gauge_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.threat_gauge_fig, self.threat_gauge_ax = plt.subplots(figsize=(6, 3), facecolor=COLORS["light"])
        self.threat_gauge_canvas = FigureCanvasTkAgg(self.threat_gauge_fig, threat_gauge_frame)
        self.threat_gauge_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Top attack vectors
        vectors_frame = ttk.LabelFrame(left_panel, text="Top Attack Vectors", padding="15", style='Card.TFrame')
        vectors_frame.pack(fill=tk.BOTH, expand=True)
        
        self.vectors_tree = ttk.Treeview(vectors_frame, columns=("Vector", "Count", "Risk"), show="headings", height=8)
        self.vectors_tree.heading("Vector", text="Attack Vector")
        self.vectors_tree.heading("Count", text="Count")
        self.vectors_tree.heading("Risk", text="Risk Level")
        
        self.vectors_tree.column("Vector", width=150, anchor="w")
        self.vectors_tree.column("Count", width=80, anchor="center")
        self.vectors_tree.column("Risk", width=100, anchor="center")
        
        scrollbar = ttk.Scrollbar(vectors_frame, orient="vertical", command=self.vectors_tree.yview)
        self.vectors_tree.configure(yscrollcommand=scrollbar.set)
        
        self.vectors_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Right side - Threat timeline
        right_panel = ttk.Frame(threat_container)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        timeline_frame = ttk.LabelFrame(right_panel, text="Threat Activity Timeline (24h)", padding="10", style='Card.TFrame')
        timeline_frame.pack(fill=tk.BOTH, expand=True)
        
        self.timeline_fig, self.timeline_ax = plt.subplots(figsize=(6, 8), facecolor=COLORS["light"])
        self.timeline_canvas = FigureCanvasTkAgg(self.timeline_fig, timeline_frame)
        self.timeline_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
    def _setup_health_tab(self):
        """Setup network health tab"""
        health_container = ttk.Frame(self.health_frame)
        health_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Network status overview
        status_frame = ttk.LabelFrame(health_container, text="Network Health Status", padding="15", style='Card.TFrame')
        status_frame.pack(fill=tk.X, pady=(0, 10))
        
        # Health metrics in a grid
        metrics_grid = ttk.Frame(status_frame)
        metrics_grid.pack(fill=tk.X)
        
        health_metrics = [
            ("Node Health", "95%", COLORS["success"]),
            ("Connectivity", "98%", COLORS["success"]),
            ("Security Compliance", "82%", COLORS["warning"]),
            ("Patch Level", "78%", COLORS["warning"]),
            ("Incident Response", "90%", COLORS["success"]),
            ("Backup Status", "85%", COLORS["info"])
        ]
        
        self.health_labels = {}
        for i, (title, value, color) in enumerate(health_metrics):
            row = i // 3
            col = i % 3
            
            metric_frame = ttk.Frame(metrics_grid)
            metric_frame.grid(row=row, column=col, padx=10, pady=5, sticky="ew")
            
            ttk.Label(metric_frame, text=title, font=('Arial', 9)).pack(anchor=tk.W)
            value_label = ttk.Label(metric_frame, text=value, font=('Arial', 14, 'bold'), foreground=color)
            value_label.pack(anchor=tk.W)
            
            self.health_labels[title] = value_label
        
        # Charts row
        charts_frame = ttk.Frame(health_container)
        charts_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Node security levels
        security_frame = ttk.LabelFrame(charts_frame, text="Node Security Levels", padding="10", style='Card.TFrame')
        security_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        self.security_fig, self.security_ax = plt.subplots(figsize=(6, 4), facecolor=COLORS["light"])
        self.security_canvas = FigureCanvasTkAgg(self.security_fig, security_frame)
        self.security_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Risk distribution
        risk_frame = ttk.LabelFrame(charts_frame, text="Risk Distribution", padding="10", style='Card.TFrame')
        risk_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        self.risk_fig, self.risk_ax = plt.subplots(figsize=(6, 4), facecolor=COLORS["light"])
        self.risk_canvas = FigureCanvasTkAgg(self.risk_fig, risk_frame)
        self.risk_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
    def _setup_performance_tab(self):
        """Setup performance metrics tab"""
        performance_container = ttk.Frame(self.performance_frame)
        performance_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Performance metrics
        metrics_frame = ttk.LabelFrame(performance_container, text="System Performance", padding="15", style='Card.TFrame')
        metrics_frame.pack(fill=tk.X, pady=(0, 10))
        
        # Performance indicators
        perf_metrics = [
            ("Scan Performance", "High", COLORS["success"], "⚡"),
            ("Detection Accuracy", "92%", COLORS["success"], "🎯"),
            ("False Positive Rate", "3.2%", COLORS["warning"], "📊"),
            ("Response Time", "45ms", COLORS["success"], "⏱️"),
            ("System Uptime", "99.8%", COLORS["success"], "🔼"),
            ("Data Processed", "2.1GB", COLORS["info"], "💾")
        ]
        
        perf_grid = ttk.Frame(metrics_frame)
        perf_grid.pack(fill=tk.X)
        
        self.perf_labels = {}
        for i, (title, value, color, icon) in enumerate(perf_metrics):
            row = i // 3
            col = i % 3
            
            perf_frame = ttk.Frame(perf_grid)
            perf_frame.grid(row=row, column=col, padx=10, pady=5, sticky="ew")
            
            # Icon and title
            icon_frame = ttk.Frame(perf_frame)
            icon_frame.pack(anchor=tk.W)
            
            ttk.Label(icon_frame, text=icon, font=('Arial', 12)).pack(side=tk.LEFT)
            ttk.Label(icon_frame, text=title, font=('Arial', 9)).pack(side=tk.LEFT, padx=(5, 0))
            
            value_label = ttk.Label(perf_frame, text=value, font=('Arial', 14, 'bold'), foreground=color)
            value_label.pack(anchor=tk.W)
            
            self.perf_labels[title] = value_label
        
        # Performance charts
        charts_frame = ttk.Frame(performance_container)
        charts_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Response time chart
        response_frame = ttk.LabelFrame(charts_frame, text="Response Time Trends", padding="10", style='Card.TFrame')
        response_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        self.response_fig, self.response_ax = plt.subplots(figsize=(6, 4), facecolor=COLORS["light"])
        self.response_canvas = FigureCanvasTkAgg(self.response_fig, response_frame)
        self.response_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Resource usage
        resource_frame = ttk.LabelFrame(charts_frame, text="Resource Utilization", padding="10", style='Card.TFrame')
        resource_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(5, 0))
        
        self.resource_fig, self.resource_ax = plt.subplots(figsize=(6, 4), facecolor=COLORS["light"])
        self.resource_canvas = FigureCanvasTkAgg(self.resource_fig, resource_frame)
        self.resource_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
    def _setup_charts(self):
        """Initialize empty charts"""
        self._create_empty_chart(self.trend_ax, "Alert trends data will appear here")
        self._create_empty_chart(self.distribution_ax, "Threat distribution data will appear here")
        self._create_empty_chart(self.threat_gauge_ax, "Threat level gauge will appear here")
        self._create_empty_chart(self.timeline_ax, "Threat timeline data will appear here")
        self._create_empty_chart(self.security_ax, "Security levels data will appear here")
        self._create_empty_chart(self.risk_ax, "Risk distribution data will appear here")
        self._create_empty_chart(self.response_ax, "Response time data will appear here")
        self._create_empty_chart(self.resource_ax, "Resource usage data will appear here")
        
    def _create_empty_chart(self, ax, message):
        """Create an empty chart with a message"""
        ax.clear()
        ax.text(0.5, 0.5, message, ha='center', va='center', transform=ax.transAxes, fontsize=12)
        ax.set_facecolor(COLORS["light"])
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_visible(False)

    # ADD THE MISSING METHODS HERE:

    def generate_sample_analytics(self):
        """Generate sample analytics data for demonstration"""
        try:
            # Create sample alerts data if none exists
            if not APP_STATE.alerts:
                sample_alerts = []
                attack_types = ["malware", "ransomware", "ddos", "phishing", "brute_force"]
                nodes = [f"Node_{i}" for i in range(1, 11)]
                
                for i in range(15):
                    alert = {
                        "time": (datetime.now() - timedelta(minutes=random.randint(1, 120))).isoformat(),
                        "node": random.choice(nodes),
                        "threat_score": random.randint(20, 95),
                        "path": " -> ".join(random.sample(nodes, min(3, len(nodes)))),
                        "status": random.choice(["active", "active", "investigating", "resolved"]),
                        "attack_type": random.choice(attack_types),
                        "security_level": random.randint(3, 10),
                        "logs_count": random.randint(1, 15),
                        "detection": random.choice(["Pattern Matching", "Behavioral Analysis", "Signature Detection"]),
                        "recommendations": [
                            "Isolate affected node",
                            "Update security policies", 
                            "Run deep scan",
                            "Review access logs"
                        ]
                    }
                    sample_alerts.append(alert)
                
                APP_STATE.alerts = sample_alerts
            
            # Create sample network if none exists
            if not hasattr(self.controller, 'network') or not self.controller.network.nodes:
                self.controller.create_sample_network()
            
            # Refresh analytics with the sample data
            self.refresh_analytics()
            
            self.status_var.set("✅ Sample analytics data generated successfully")
            self.status_label.config(text="● SAMPLE DATA", foreground=COLORS["success"])
            
            messagebox.showinfo("Sample Data", 
                              "Sample analytics data generated successfully!\n\n"
                              "• 15 sample alerts created\n"
                              "• Sample network topology generated\n"
                              "• All charts populated with sample data")
                              
        except Exception as e:
            messagebox.showerror("Error", f"Failed to generate sample data: {str(e)}")
            self.status_var.set(f"❌ Error generating sample data: {str(e)}")

    def export_analytics_report(self):
        """Export analytics report to a file"""
        if not self.analytics_data:
            messagebox.showwarning("No Data", "No analytics data to export!")
            return
            
        try:
            filepath = filedialog.asksaveasfilename(
                defaultextension=".txt",
                filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
                title="Export Analytics Report"
            )
            
            if not filepath:
                return
                
            # Generate comprehensive report
            report = "GRAPHGUARD SECURITY ANALYTICS REPORT\n"
            report += "=" * 50 + "\n"
            report += f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
            
            metrics = self.analytics_data.get("metrics", {})
            report += "KEY METRICS:\n"
            report += f"- Total Alerts: {metrics.get('total_alerts', 0)}\n"
            report += f"- Active Threats: {metrics.get('active_threats', 0)}\n"
            report += f"- Network Nodes: {metrics.get('network_nodes', 0)}\n"
            report += f"- Security Score: {metrics.get('security_score', 0)}%\n"
            report += f"- Compromised Nodes: {metrics.get('compromised_nodes', 0)}\n\n"
            
            threat_analysis = self.analytics_data.get("threat_analysis", {})
            report += "THREAT ANALYSIS:\n"
            for attack_type, count in threat_analysis.get('attack_counts', {}).items():
                report += f"- {attack_type}: {count} occurrences\n"
                
            severity_counts = threat_analysis.get('severity_counts', {})
            if severity_counts:
                report += "\nSEVERITY DISTRIBUTION:\n"
                for severity, count in severity_counts.items():
                    report += f"- {severity.capitalize()}: {count} alerts\n"
                    
            # Performance metrics
            performance = self.analytics_data.get("performance", {})
            if performance:
                report += "\nPERFORMANCE METRICS:\n"
                for metric, value in performance.items():
                    report += f"- {metric.replace('_', ' ').title()}: {value}\n"
            
            # Write to file
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(report)
                
            messagebox.showinfo("Export Complete", 
                              f"Analytics report successfully exported to:\n{filepath}")
                              
        except Exception as e:
            messagebox.showerror("Export Error", f"Failed to export report: {str(e)}")

    def refresh_analytics(self):
        """Refresh analytics with current data"""
        try:
            # Get data from app state and network
            alerts_data = APP_STATE.alerts
            network_data = self.controller.network if hasattr(self.controller, 'network') else None
            
            if not alerts_data and not network_data:
                self.status_var.set("No data available - Generate sample data or run simulations")
                return
            
            # Process analytics data
            self._process_analytics_data(alerts_data, network_data)
            
            # Update all visualizations
            self._update_overview_tab()
            self._update_threat_tab()
            self._update_health_tab()
            self._update_performance_tab()
            
            self.status_var.set("✅ Analytics updated successfully")
            self.status_label.config(text="● DATA LOADED", foreground=COLORS["success"])
            
        except Exception as e:
            self.status_var.set(f"❌ Error updating analytics: {str(e)}")
            self.status_label.config(text="● ERROR", foreground=COLORS["danger"])

    def _process_analytics_data(self, alerts_data, network_data):
        """Process raw data into analytics format with better sample data"""
        self.analytics_data = {
            "alerts": alerts_data,
            "network": network_data,
            "timestamp": datetime.now()
        }
        
        # Calculate key metrics
        total_alerts = len(alerts_data)
        active_threats = len([a for a in alerts_data if a.get('status') == 'active'])
        
        # Network metrics
        if network_data and hasattr(network_data, 'nodes'):
            network_nodes = len(network_data.nodes)
            compromised_nodes = sum(1 for node in network_data.nodes.values() if node.compromised)
            security_score = self._calculate_security_score(network_data, alerts_data)
        else:
            network_nodes = 15  # Default sample value
            compromised_nodes = 0
            security_score = 61  # Default sample value like in image
            
        self.analytics_data["metrics"] = {
            "total_alerts": total_alerts or 8,  # Use sample if no data
            "active_threats": active_threats or 7,  # Use sample if no data
            "network_nodes": network_nodes,
            "security_score": security_score,
            "compromised_nodes": compromised_nodes
        }
        
        # Threat analysis with better sample data
        self.analytics_data["threat_analysis"] = self._analyze_threats(alerts_data)
        
        # Ensure we have daily counts for the trend chart
        if not self.analytics_data["threat_analysis"].get("daily_counts"):
            today = datetime.now()
            daily_counts = {}
            for i in range(7):
                date = today - timedelta(days=6-i)  # Last 7 days
                date_str = date.strftime("%Y-%m-%d")
                # Sample data similar to image
                sample_values = [3, 5, 2, 8, 4, 1, 6]
                daily_counts[date_str] = sample_values[i]
            self.analytics_data["threat_analysis"]["daily_counts"] = daily_counts
        
        # Performance metrics
        self.analytics_data["performance"] = self._calculate_performance_metrics()

    def _calculate_security_score(self, network_data, alerts_data):
        """Calculate overall security score (0-100)"""
        if not network_data.nodes:
            return 0
            
        base_score = 100
        
        # Deductions for compromised nodes
        compromised_penalty = len([n for n in network_data.nodes.values() if n.compromised]) * 10
        base_score -= compromised_penalty
        
        # Deductions for high-risk alerts
        high_risk_alerts = len([a for a in alerts_data if a.get('threat_score', 0) > 70])
        base_score -= high_risk_alerts * 5
        
        # Bonus for high security nodes
        high_security_nodes = len([n for n in network_data.nodes.values() if n.security_level >= 8])
        base_score += high_security_nodes * 2
        
        return max(0, min(100, base_score))

    def _analyze_threats(self, alerts_data):
        """Analyze threat patterns and trends"""
        if not alerts_data:
            return {}
            
        # Count by attack type
        attack_counts = Counter()
        severity_counts = {"critical": 0, "high": 0, "medium": 0, "low": 0}
        
        for alert in alerts_data:
            attack_type = alert.get('attack_type', 'unknown')
            attack_counts[attack_type] += 1
            
            # Categorize by threat score
            score = alert.get('threat_score', 0)
            if score >= 80:
                severity_counts["critical"] += 1
            elif score >= 60:
                severity_counts["high"] += 1
            elif score >= 40:
                severity_counts["medium"] += 1
            else:
                severity_counts["low"] += 1
                
        # Timeline analysis (last 7 days)
        today = datetime.now()
        daily_counts = {}
        for i in range(7):
            date = today - timedelta(days=i)
            date_str = date.strftime("%Y-%m-%d")
            daily_counts[date_str] = 0
            
        for alert in alerts_data:
            try:
                alert_time = datetime.fromisoformat(alert.get('time', ''))
                date_str = alert_time.strftime("%Y-%m-%d")
                if date_str in daily_counts:
                    daily_counts[date_str] += 1
            except:
                continue
                
        return {
            "attack_counts": dict(attack_counts),
            "severity_counts": severity_counts,
            "daily_counts": daily_counts,
            "top_threats": attack_counts.most_common(5)
        }

    def _calculate_performance_metrics(self):
        """Calculate performance metrics"""
        # Simulated performance data - in real app, this would come from actual measurements
        return {
            "scan_performance": random.choice(["High", "Medium", "Low"]),
            "detection_accuracy": f"{random.randint(85, 98)}%",
            "false_positive_rate": f"{random.uniform(1.5, 5.0):.1f}%",
            "response_time": f"{random.randint(30, 100)}ms",
            "system_uptime": f"{random.uniform(99.5, 99.9):.1f}%",
            "data_processed": f"{random.uniform(1.5, 3.0):.1f}GB"
        }

    def clear_analytics(self):
        """Clear analytics data and reset displays"""
        self.analytics_data = {}
        
        # Reset all charts
        self._setup_charts()
        
        # Clear treeviews
        for item in self.activity_tree.get_children():
            self.activity_tree.delete(item)
        for item in self.vectors_tree.get_children():
            self.vectors_tree.delete(item)
            
        # Reset metrics
        for label in self.metric_labels.values():
            label.config(text="0")
        for label in self.health_labels.values():
            label.config(text="0%")
        for label in self.perf_labels.values():
            label.config(text="N/A")
            
        self.status_var.set("Analytics data cleared")
        self.status_label.config(text="● READY", foreground=COLORS["info"])

    def on_show(self):
        """Called when the page is shown"""
        self.refresh_analytics()
        return "Analytics — Ready"

    # ADD THE CHART UPDATE METHODS HERE:

    def _update_overview_tab(self):
        """Update the overview tab with current data"""
        metrics = self.analytics_data.get("metrics", {})
        
        # Update key metrics
        self.metric_labels["Total Alerts"].config(text=str(metrics.get("total_alerts", 0)))
        self.metric_labels["Active Threats"].config(text=str(metrics.get("active_threats", 0)))
        self.metric_labels["Network Nodes"].config(text=str(metrics.get("network_nodes", 0)))
        self.metric_labels["Security Score"].config(text=f"{metrics.get('security_score', 0)}%")
        
        # Update trend chart
        self._update_trend_chart()
        
        # Update distribution chart
        self._update_distribution_chart()
        
        # Update recent activity
        self._update_recent_activity()

    def _update_trend_chart(self):
        """Update the alert trends chart to match the image style"""
        self.trend_ax.clear()
        
        threat_analysis = self.analytics_data.get("threat_analysis", {})
        daily_counts = threat_analysis.get("daily_counts", {})
        
        if daily_counts:
            # Sort dates chronologically
            dates = sorted(daily_counts.keys())
            counts = [daily_counts[date] for date in dates]
            
            # Use shorter date labels (day names or numbers)
            short_dates = []
            for date_str in dates:
                try:
                    date_obj = datetime.strptime(date_str, "%Y-%m-%d")
                    short_dates.append(date_obj.strftime("%a"))  # Mon, Tue, etc.
                except:
                    short_dates.append(date_str[-5:])  # Fallback to mm-dd
            
            # Create bar chart with styling from the image
            bars = self.trend_ax.bar(short_dates, counts, 
                                   color=COLORS["accent"],
                                   alpha=0.8,
                                   width=0.6)
            
            self.trend_ax.set_title("Daily Alert Trends", fontweight='bold', pad=10)
            self.trend_ax.set_ylabel("Number of Alerts")
            
            # Set y-axis to show specific values like in the image (0, 2, 4, 6, 8)
            max_count = max(counts) if counts else 8
            y_max = max(8, ((max_count // 2) + 1) * 2)  # Round up to even number
            self.trend_ax.set_ylim(0, y_max)
            self.trend_ax.set_yticks(range(0, y_max + 1, 2))
            
            # Add value labels on top of bars
            for bar, count in zip(bars, counts):
                height = bar.get_height()
                if height > 0:  # Only show label if value > 0
                    self.trend_ax.text(bar.get_x() + bar.get_width()/2., height,
                                     f'{count}', ha='center', va='bottom', fontweight='bold')
            
            # Remove spines for cleaner look
            self.trend_ax.spines['top'].set_visible(False)
            self.trend_ax.spines['right'].set_visible(False)
            
        else:
            # Sample data for demonstration when no real data exists
            days = ['Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat', 'Sun']
            sample_counts = [3, 5, 2, 8, 4, 1, 6]
            
            bars = self.trend_ax.bar(days, sample_counts, 
                                   color=COLORS["accent"],
                                   alpha=0.8,
                                   width=0.6)
            
            self.trend_ax.set_title("Daily Alert Trends", fontweight='bold', pad=10)
            self.trend_ax.set_ylabel("Number of Alerts")
            self.trend_ax.set_ylim(0, 8)
            self.trend_ax.set_yticks(range(0, 9, 2))
            
            # Add value labels
            for bar, count in zip(bars, sample_counts):
                height = bar.get_height()
                self.trend_ax.text(bar.get_x() + bar.get_width()/2., height,
                                 f'{count}', ha='center', va='bottom', fontweight='bold')
            
            # Clean up spines
            self.trend_ax.spines['top'].set_visible(False)
            self.trend_ax.spines['right'].set_visible(False)
            
        self.trend_ax.set_facecolor(COLORS["light"])
        self.trend_canvas.draw()

    def _update_distribution_chart(self):
        """Update the threat distribution chart"""
        self.distribution_ax.clear()
        
        threat_analysis = self.analytics_data.get("threat_analysis", {})
        attack_counts = threat_analysis.get("attack_counts", {})
        
        if attack_counts:
            labels = list(attack_counts.keys())
            sizes = list(attack_counts.values())
            colors = [COLORS["danger"], COLORS["warning"], COLORS["info"], COLORS["accent"], COLORS["success"]]
            
            # Use available colors, repeat if necessary
            chart_colors = colors * (len(labels) // len(colors) + 1)
            chart_colors = chart_colors[:len(labels)]
            
            wedges, texts, autotexts = self.distribution_ax.pie(sizes, labels=labels, colors=chart_colors, 
                                                              autopct='%1.1f%%', startangle=90)
            
            # Style the text
            for autotext in autotexts:
                autotext.set_color('white')
                autotext.set_fontweight('bold')
                
            self.distribution_ax.set_title("Threat Type Distribution", fontweight='bold')
        else:
            self._create_empty_chart(self.distribution_ax, "No distribution data available")
            
        self.distribution_ax.set_facecolor(COLORS["light"])
        self.distribution_canvas.draw()

    def _update_recent_activity(self):
        """Update the recent activity treeview"""
        # Clear existing items
        for item in self.activity_tree.get_children():
            self.activity_tree.delete(item)
            
        alerts_data = self.analytics_data.get("alerts", [])
        
        # Show most recent alerts
        recent_alerts = sorted(alerts_data, 
                             key=lambda x: datetime.fromisoformat(x.get('time', '2000-01-01')), 
                             reverse=True)[:10]
        
        for alert in recent_alerts:
            try:
                time_str = datetime.fromisoformat(alert.get('time', '')).strftime("%H:%M:%S")
            except:
                time_str = "Unknown"
                
            event_type = alert.get('attack_type', 'Unknown')
            node = alert.get('node', 'Unknown')
            description = alert.get('message', 'No description')
            
            # Determine severity tag
            score = alert.get('threat_score', 0)
            if score >= 80:
                severity = "CRITICAL"
                tag = "critical"
            elif score >= 60:
                severity = "HIGH"
                tag = "high"
            elif score >= 40:
                severity = "MEDIUM"
                tag = "medium"
            else:
                severity = "LOW"
                tag = "low"
                
            self.activity_tree.insert("", "end", 
                                    values=(time_str, event_type, severity, node, description),
                                    tags=(tag,))

    def _update_threat_tab(self):
        """Update the threat intelligence tab"""
        # Update threat gauge
        self._update_threat_gauge()
        
        # Update attack vectors
        self._update_attack_vectors()
        
        # Update threat timeline
        self._update_threat_timeline()

    def _update_threat_gauge(self):
        """Update the threat level gauge to show percentage like in image"""
        self.threat_gauge_ax.clear()
        
        metrics = self.analytics_data.get("metrics", {})
        security_score = metrics.get("security_score", 0)
        threat_level = 100 - security_score  # Invert for threat level
        
        # Create a simple text-based gauge like in the image
        self.threat_gauge_ax.text(0.5, 0.7, f"Current Threat Level: {threat_level:.0f}%", 
                                ha='center', va='center', fontsize=14, fontweight='bold',
                                transform=self.threat_gauge_ax.transAxes)
        
        # Create a simple progress bar
        bar_height = 0.3
        bar_width = 0.8
        self.threat_gauge_ax.add_patch(plt.Rectangle((0.1, 0.4), bar_width, bar_height, 
                                                   fill=False, edgecolor=COLORS["secondary"], linewidth=2))
        
        # Fill based on threat level
        fill_width = (threat_level / 100) * bar_width
        fill_color = COLORS["danger"] if threat_level > 50 else COLORS["warning"] if threat_level > 25 else COLORS["success"]
        self.threat_gauge_ax.add_patch(plt.Rectangle((0.1, 0.4), fill_width, bar_height, 
                                                   color=fill_color, alpha=0.7))
        
        # Add threat level labels
        self.threat_gauge_ax.text(0.1, 0.35, "Low", ha='left', va='top', fontsize=10)
        self.threat_gauge_ax.text(0.5, 0.35, "Medium", ha='center', va='top', fontsize=10)
        self.threat_gauge_ax.text(0.9, 0.35, "High", ha='right', va='top', fontsize=10)
        
        self.threat_gauge_ax.set_xlim(0, 1)
        self.threat_gauge_ax.set_ylim(0, 1)
        self.threat_gauge_ax.set_xticks([])
        self.threat_gauge_ax.set_yticks([])
        self.threat_gauge_ax.set_facecolor(COLORS["light"])
        
        # Remove all spines
        for spine in self.threat_gauge_ax.spines.values():
            spine.set_visible(False)
            
        self.threat_gauge_canvas.draw()

    def _update_attack_vectors(self):
        """Update the attack vectors table to ensure it's visible"""
        for item in self.vectors_tree.get_children():
            self.vectors_tree.delete(item)
            
        threat_analysis = self.analytics_data.get("threat_analysis", {})
        attack_counts = threat_analysis.get("attack_counts", {})
        
        if attack_counts:
            for vector, count in attack_counts.items():
                # Determine risk level based on count
                if count > 10:
                    risk = "High"
                elif count > 5:
                    risk = "Medium" 
                else:
                    risk = "Low"
                    
                self.vectors_tree.insert("", "end", values=(vector, count, risk))
        else:
            # Add sample data to ensure the table is visible
            sample_vectors = [
                ("unknown", 1, "Low"),
                ("phishing", 3, "Medium"), 
                ("malware", 2, "Low"),
                ("brute_force", 5, "Medium"),
                ("ddos", 1, "Low")
            ]
            
            for vector, count, risk in sample_vectors:
                self.vectors_tree.insert("", "end", values=(vector, count, risk))

    def _update_threat_timeline(self):
        """Update the threat timeline chart to match the image style"""
        self.timeline_ax.clear()
        
        # Generate sample timeline data matching the image style
        hours = [f"{i:02d}:00" for i in range(24)]
        
        # Create a timeline that shows activity peaks like in the image
        timeline_data = [0] * 24
        # Add some random peaks to simulate threat activity
        peak_hours = [2, 8, 14, 19, 22]  # Common attack hours
        for hour in peak_hours:
            timeline_data[hour] = random.randint(3, 7)
        
        # Create the area chart
        self.timeline_ax.fill_between(range(24), timeline_data, 
                                    color=COLORS["danger"], alpha=0.3)
        self.timeline_ax.plot(range(24), timeline_data, 
                            color=COLORS["danger"], linewidth=2, marker='o', markersize=4)
        
        self.timeline_ax.set_title("Threat Activity Timeline (24h)", fontweight='bold', pad=10)
        self.timeline_ax.set_xlabel("Time")
        self.timeline_ax.set_ylabel("Threat Level")
        
        # Set x-axis to show every 4 hours
        self.timeline_ax.set_xticks(range(0, 24, 4))
        self.timeline_ax.set_xticklabels([f"{i:02d}:00" for i in range(0, 24, 4)])
        
        # Set y-axis similar to image
        self.timeline_ax.set_ylim(0, 8)
        self.timeline_ax.set_yticks(range(0, 9, 2))
        
        # Add horizontal grid lines
        self.timeline_ax.grid(True, axis='y', alpha=0.3, linestyle='--')
        self.timeline_ax.grid(True, axis='x', alpha=0.1)
        
        # Remove top and right spines
        self.timeline_ax.spines['top'].set_visible(False)
        self.timeline_ax.spines['right'].set_visible(False)
        
        self.timeline_ax.set_facecolor(COLORS["light"])
        self.timeline_canvas.draw()

    def _update_health_tab(self):
        """Update the network health tab"""
        metrics = self.analytics_data.get("metrics", {})
        network_data = self.analytics_data.get("network")
        
        # Update health metrics
        if network_data and hasattr(network_data, 'nodes'):
            total_nodes = len(network_data.nodes)
            compromised = len([n for n in network_data.nodes.values() if n.compromised])
            healthy_nodes = total_nodes - compromised
            
            node_health = (healthy_nodes / total_nodes * 100) if total_nodes > 0 else 0
            connectivity = random.randint(95, 99)
            security_compliance = random.randint(75, 90)
            patch_level = random.randint(70, 85)
            incident_response = random.randint(85, 95)
            backup_status = random.randint(80, 90)
            
            self.health_labels["Node Health"].config(text=f"{node_health:.0f}%")
            self.health_labels["Connectivity"].config(text=f"{connectivity}%")
            self.health_labels["Security Compliance"].config(text=f"{security_compliance}%")
            self.health_labels["Patch Level"].config(text=f"{patch_level}%")
            self.health_labels["Incident Response"].config(text=f"{incident_response}%")
            self.health_labels["Backup Status"].config(text=f"{backup_status}%")
        
        # Update security levels chart
        self._update_security_levels_chart()
        
        # Update risk distribution chart
        self._update_risk_distribution_chart()

    def _update_security_levels_chart(self):
        """Update the node security levels chart"""
        self.security_ax.clear()
        
        network_data = self.analytics_data.get("network")
        
        if network_data and hasattr(network_data, 'nodes'):
            security_levels = [node.security_level for node in network_data.nodes.values()]
            
            # Create histogram of security levels
            bins = range(1, 12)  # 1-10 plus one extra
            self.security_ax.hist(security_levels, bins=bins, color=COLORS["accent"], alpha=0.7, edgecolor='black')
            self.security_ax.set_xlabel('Security Level (1-10)')
            self.security_ax.set_ylabel('Number of Nodes')
            self.security_ax.set_title('Node Security Level Distribution', fontweight='bold')
            self.security_ax.set_xticks(range(1, 11))
        else:
            self._create_empty_chart(self.security_ax, "No network data available")
            
        self.security_ax.set_facecolor(COLORS["light"])
        self.security_canvas.draw()

    def _update_risk_distribution_chart(self):
        """Update the risk distribution chart"""
        self.risk_ax.clear()
        
        network_data = self.analytics_data.get("network")
        
        if network_data and hasattr(network_data, 'nodes'):
            risk_levels = [node.risk_level for node in network_data.nodes.values()]
            risk_categories = {'Low (0-3)': 0, 'Medium (4-6)': 0, 'High (7-10)': 0}
            
            for risk in risk_levels:
                if risk <= 3:
                    risk_categories['Low (0-3)'] += 1
                elif risk <= 6:
                    risk_categories['Medium (4-6)'] += 1
                else:
                    risk_categories['High (7-10)'] += 1
                    
            categories = list(risk_categories.keys())
            counts = list(risk_categories.values())
            colors = [COLORS["success"], COLORS["warning"], COLORS["danger"]]
            
            bars = self.risk_ax.bar(categories, counts, color=colors, alpha=0.8)
            self.risk_ax.set_title('Node Risk Level Distribution', fontweight='bold')
            self.risk_ax.set_ylabel('Number of Nodes')
            
            # Add value labels on bars
            for bar, count in zip(bars, counts):
                height = bar.get_height()
                self.risk_ax.text(bar.get_x() + bar.get_width()/2., height,
                                f'{count}', ha='center', va='bottom')
        else:
            self._create_empty_chart(self.risk_ax, "No risk data available")
            
        self.risk_ax.set_facecolor(COLORS["light"])
        self.risk_canvas.draw()

    def _update_performance_tab(self):
        """Update the performance metrics tab"""
        performance_data = self.analytics_data.get("performance", {})
        
        # Update performance metrics
        for title, label in self.perf_labels.items():
            value = performance_data.get(title.lower().replace(" ", "_"), "N/A")
            label.config(text=value)
            
        # Update response time chart
        self._update_response_time_chart()
        
        # Update resource usage chart
        self._update_resource_usage_chart()

    def _update_response_time_chart(self):
        """Update the response time trends chart"""
        self.response_ax.clear()
        
        # Simulated response time data
        hours = [f"{i:02d}:00" for i in range(24)]
        response_times = [random.randint(30, 100) for _ in range(24)]
        
        self.response_ax.plot(hours, response_times, marker='o', color=COLORS["info"], linewidth=2)
        self.response_ax.fill_between(hours, response_times, alpha=0.3, color=COLORS["info"])
        self.response_ax.set_title('Response Time Trends (24h)', fontweight='bold')
        self.response_ax.set_ylabel('Response Time (ms)')
        self.response_ax.set_xlabel('Time of Day')
        self.response_ax.tick_params(axis='x', rotation=45)
        self.response_ax.grid(True, alpha=0.3)
        
        self.response_ax.set_facecolor(COLORS["light"])
        self.response_canvas.draw()

    def _update_resource_usage_chart(self):
        """Update the resource utilization chart"""
        self.resource_ax.clear()
        
        # Simulated resource usage data
        resources = ['CPU', 'Memory', 'Disk', 'Network']
        usage = [random.randint(40, 85) for _ in range(4)]
        colors = [COLORS["accent"], COLORS["info"], COLORS["warning"], COLORS["success"]]
        
        bars = self.resource_ax.bar(resources, usage, color=colors, alpha=0.8)
        self.resource_ax.set_title('Resource Utilization', fontweight='bold')
        self.resource_ax.set_ylabel('Usage (%)')
        self.resource_ax.set_ylim(0, 100)
        
        # Add value labels on bars
        for bar, use in zip(bars, usage):
            height = bar.get_height()
            self.resource_ax.text(bar.get_x() + bar.get_width()/2., height,
                                f'{use}%', ha='center', va='bottom')
                
        self.resource_ax.set_facecolor(COLORS["light"])
        self.resource_canvas.draw()

def _update_threat_timeline(self):
    """Update the threat timeline chart to match the image style"""
    self.timeline_ax.clear()
    
    # Generate sample timeline data matching the image style
    hours = [f"{i:02d}:00" for i in range(24)]
    
    # Create a timeline that shows activity peaks like in the image
    timeline_data = [0] * 24
    # Add some random peaks to simulate threat activity
    peak_hours = [2, 8, 14, 19, 22]  # Common attack hours
    for hour in peak_hours:
        timeline_data[hour] = random.randint(3, 7)
    
    # Create the area chart
    self.timeline_ax.fill_between(range(24), timeline_data, 
                                color=COLORS["danger"], alpha=0.3)
    self.timeline_ax.plot(range(24), timeline_data, 
                        color=COLORS["danger"], linewidth=2, marker='o', markersize=4)
    
    self.timeline_ax.set_title("Threat Activity Timeline (24h)", fontweight='bold', pad=10)
    self.timeline_ax.set_xlabel("Time")
    self.timeline_ax.set_ylabel("Threat Level")
    
    # Set x-axis to show every 4 hours
    self.timeline_ax.set_xticks(range(0, 24, 4))
    self.timeline_ax.set_xticklabels([f"{i:02d}:00" for i in range(0, 24, 4)])
    
    # Set y-axis similar to image
    self.timeline_ax.set_ylim(0, 8)
    self.timeline_ax.set_yticks(range(0, 9, 2))
    
    # Add horizontal grid lines
    self.timeline_ax.grid(True, axis='y', alpha=0.3, linestyle='--')
    self.timeline_ax.grid(True, axis='x', alpha=0.1)
    
    # Remove top and right spines
    self.timeline_ax.spines['top'].set_visible(False)
    self.timeline_ax.spines['right'].set_visible(False)
    
    self.timeline_ax.set_facecolor(COLORS["light"])
    self.timeline_canvas.draw()

def _update_threat_gauge(self):
    """Update the threat level gauge to show percentage like in image"""
    self.threat_gauge_ax.clear()
    
    metrics = self.analytics_data.get("metrics", {})
    security_score = metrics.get("security_score", 0)
    threat_level = 100 - security_score  # Invert for threat level
    
    # Create a simple text-based gauge like in the image
    self.threat_gauge_ax.text(0.5, 0.7, f"Current Threat Level: {threat_level:.0f}%", 
                            ha='center', va='center', fontsize=14, fontweight='bold',
                            transform=self.threat_gauge_ax.transAxes)
    
    # Create a simple progress bar
    bar_height = 0.3
    bar_width = 0.8
    self.threat_gauge_ax.add_patch(plt.Rectangle((0.1, 0.4), bar_width, bar_height, 
                                               fill=False, edgecolor=COLORS["secondary"], linewidth=2))
    
    # Fill based on threat level
    fill_width = (threat_level / 100) * bar_width
    fill_color = COLORS["danger"] if threat_level > 50 else COLORS["warning"] if threat_level > 25 else COLORS["success"]
    self.threat_gauge_ax.add_patch(plt.Rectangle((0.1, 0.4), fill_width, bar_height, 
                                               color=fill_color, alpha=0.7))
    
    # Add threat level labels
    self.threat_gauge_ax.text(0.1, 0.35, "Low", ha='left', va='top', fontsize=10)
    self.threat_gauge_ax.text(0.5, 0.35, "Medium", ha='center', va='top', fontsize=10)
    self.threat_gauge_ax.text(0.9, 0.35, "High", ha='right', va='top', fontsize=10)
    
    self.threat_gauge_ax.set_xlim(0, 1)
    self.threat_gauge_ax.set_ylim(0, 1)
    self.threat_gauge_ax.set_xticks([])
    self.threat_gauge_ax.set_yticks([])
    self.threat_gauge_ax.set_facecolor(COLORS["light"])
    
    # Remove all spines
    for spine in self.threat_gauge_ax.spines.values():
        spine.set_visible(False)
        
    self.threat_gauge_canvas.draw()

def _update_attack_vectors(self):
    """Update the attack vectors table to ensure it's visible"""
    for item in self.vectors_tree.get_children():
        self.vectors_tree.delete(item)
        
    threat_analysis = self.analytics_data.get("threat_analysis", {})
    attack_counts = threat_analysis.get("attack_counts", {})
    
    if attack_counts:
        for vector, count in attack_counts.items():
            # Determine risk level based on count
            if count > 10:
                risk = "High"
            elif count > 5:
                risk = "Medium" 
            else:
                risk = "Low"
                
            self.vectors_tree.insert("", "end", values=(vector, count, risk))
    else:
        # Add sample data to ensure the table is visible
        sample_vectors = [
            ("unknown", 1, "Low"),
            ("phishing", 3, "Medium"), 
            ("malware", 2, "Low"),
            ("brute_force", 5, "Medium"),
            ("ddos", 1, "Low")
        ]
        
        for vector, count, risk in sample_vectors:
            self.vectors_tree.insert("", "end", values=(vector, count, risk))
    
    def _update_threat_tab(self):
        """Update the threat intelligence tab"""
        # Update threat gauge
        self._update_threat_gauge()
        
        # Update attack vectors
        self._update_attack_vectors()
        
        # Update threat timeline
        self._update_threat_timeline()
        
    def _update_threat_gauge(self):
        """Update the threat level gauge"""
        self.threat_gauge_ax.clear()
        
        metrics = self.analytics_data.get("metrics", {})
        security_score = metrics.get("security_score", 0)
        threat_level = 100 - security_score  # Invert for threat level
        
        # Create gauge chart
        categories = ['Low', 'Medium', 'High', 'Critical']
        colors = [COLORS["success"], COLORS["warning"], COLORS["danger"], COLORS["primary"]]
        
        # Simple gauge indicator
        self.threat_gauge_ax.barh(0, threat_level, color=colors[2] if threat_level > 50 else colors[1] if threat_level > 25 else colors[0])
        self.threat_gauge_ax.set_xlim(0, 100)
        self.threat_gauge_ax.set_yticks([])
        self.threat_gauge_ax.set_xlabel('Threat Level')
        self.threat_gauge_ax.set_title(f'Current Threat Level: {threat_level:.0f}%', fontweight='bold')
        
        # Add threshold lines
        self.threat_gauge_ax.axvline(x=25, color=COLORS["secondary"], linestyle='--', alpha=0.7)
        self.threat_gauge_ax.axvline(x=50, color=COLORS["secondary"], linestyle='--', alpha=0.7)
        self.threat_gauge_ax.axvline(x=75, color=COLORS["secondary"], linestyle='--', alpha=0.7)
        
        self.threat_gauge_ax.set_facecolor(COLORS["light"])
        self.threat_gauge_canvas.draw()
        
    def _update_attack_vectors(self):
        """Update the attack vectors treeview"""
        for item in self.vectors_tree.get_children():
            self.vectors_tree.delete(item)
            
        threat_analysis = self.analytics_data.get("threat_analysis", {})
        attack_counts = threat_analysis.get("attack_counts", {})
        
        for vector, count in attack_counts.items():
            # Determine risk level based on count
            if count > 10:
                risk = "High"
            elif count > 5:
                risk = "Medium"
            else:
                risk = "Low"
                
            self.vectors_tree.insert("", "end", values=(vector, count, risk))
        
    def _update_threat_timeline(self):
        """Update the threat timeline chart"""
        self.timeline_ax.clear()
        
        alerts_data = self.analytics_data.get("alerts", [])
        
        if alerts_data:
            # Group alerts by hour for the last 24 hours
            hourly_counts = {}
            for i in range(24):
                hour = (datetime.now() - timedelta(hours=i)).strftime("%H:00")
                hourly_counts[hour] = 0
                
            for alert in alerts_data:
                try:
                    alert_time = datetime.fromisoformat(alert.get('time', ''))
                    hour_str = alert_time.strftime("%H:00")
                    if hour_str in hourly_counts:
                        hourly_counts[hour_str] += 1
                except:
                    continue
                    
            hours = list(hourly_counts.keys())[::-1]
            counts = list(hourly_counts.values())[::-1]
            
            self.timeline_ax.plot(hours, counts, marker='o', color=COLORS["danger"], linewidth=2)
            self.timeline_ax.fill_between(hours, counts, alpha=0.3, color=COLORS["danger"])
            self.timeline_ax.set_title("Threat Activity Timeline (24h)", fontweight='bold')
            self.timeline_ax.set_ylabel("Number of Alerts")
            self.timeline_ax.tick_params(axis='x', rotation=45)
        else:
            self._create_empty_chart(self.timeline_ax, "No timeline data available")
            
        self.timeline_ax.set_facecolor(COLORS["light"])
        self.timeline_canvas.draw()
        
    def _update_health_tab(self):
        """Update the network health tab"""
        metrics = self.analytics_data.get("metrics", {})
        network_data = self.analytics_data.get("network")
        
        # Update health metrics
        if network_data and hasattr(network_data, 'nodes'):
            total_nodes = len(network_data.nodes)
            compromised = len([n for n in network_data.nodes.values() if n.compromised])
            healthy_nodes = total_nodes - compromised
            
            node_health = (healthy_nodes / total_nodes * 100) if total_nodes > 0 else 0
            connectivity = random.randint(95, 99)
            security_compliance = random.randint(75, 90)
            patch_level = random.randint(70, 85)
            incident_response = random.randint(85, 95)
            backup_status = random.randint(80, 90)
            
            self.health_labels["Node Health"].config(text=f"{node_health:.0f}%")
            self.health_labels["Connectivity"].config(text=f"{connectivity}%")
            self.health_labels["Security Compliance"].config(text=f"{security_compliance}%")
            self.health_labels["Patch Level"].config(text=f"{patch_level}%")
            self.health_labels["Incident Response"].config(text=f"{incident_response}%")
            self.health_labels["Backup Status"].config(text=f"{backup_status}%")
        
        # Update security levels chart
        self._update_security_levels_chart()
        
        # Update risk distribution chart
        self._update_risk_distribution_chart()
        
    def _update_security_levels_chart(self):
        """Update the node security levels chart"""
        self.security_ax.clear()
        
        network_data = self.analytics_data.get("network")
        
        if network_data and hasattr(network_data, 'nodes'):
            security_levels = [node.security_level for node in network_data.nodes.values()]
            
            # Create histogram of security levels
            bins = range(1, 12)  # 1-10 plus one extra
            self.security_ax.hist(security_levels, bins=bins, color=COLORS["accent"], alpha=0.7, edgecolor='black')
            self.security_ax.set_xlabel('Security Level (1-10)')
            self.security_ax.set_ylabel('Number of Nodes')
            self.security_ax.set_title('Node Security Level Distribution', fontweight='bold')
            self.security_ax.set_xticks(range(1, 11))
        else:
            self._create_empty_chart(self.security_ax, "No network data available")
            
        self.security_ax.set_facecolor(COLORS["light"])
        self.security_canvas.draw()
        
    def _update_risk_distribution_chart(self):
        """Update the risk distribution chart"""
        self.risk_ax.clear()
        
        network_data = self.analytics_data.get("network")
        
        if network_data and hasattr(network_data, 'nodes'):
            risk_levels = [node.risk_level for node in network_data.nodes.values()]
            risk_categories = {'Low (0-3)': 0, 'Medium (4-6)': 0, 'High (7-10)': 0}
            
            for risk in risk_levels:
                if risk <= 3:
                    risk_categories['Low (0-3)'] += 1
                elif risk <= 6:
                    risk_categories['Medium (4-6)'] += 1
                else:
                    risk_categories['High (7-10)'] += 1
                    
            categories = list(risk_categories.keys())
            counts = list(risk_categories.values())
            colors = [COLORS["success"], COLORS["warning"], COLORS["danger"]]
            
            bars = self.risk_ax.bar(categories, counts, color=colors, alpha=0.8)
            self.risk_ax.set_title('Node Risk Level Distribution', fontweight='bold')
            self.risk_ax.set_ylabel('Number of Nodes')
            
            # Add value labels on bars
            for bar, count in zip(bars, counts):
                height = bar.get_height()
                self.risk_ax.text(bar.get_x() + bar.get_width()/2., height,
                                f'{count}', ha='center', va='bottom')
        else:
            self._create_empty_chart(self.risk_ax, "No risk data available")
            
        self.risk_ax.set_facecolor(COLORS["light"])
        self.risk_canvas.draw()
        
    def _update_performance_tab(self):
        """Update the performance metrics tab"""
        performance_data = self.analytics_data.get("performance", {})
        
        # Update performance metrics
        for title, label in self.perf_labels.items():
            value = performance_data.get(title.lower().replace(" ", "_"), "N/A")
            label.config(text=value)
            
        # Update response time chart
        self._update_response_time_chart()
        
        # Update resource usage chart
        self._update_resource_usage_chart()
        
    def _update_response_time_chart(self):
        """Update the response time trends chart"""
        self.response_ax.clear()
        
        # Simulated response time data
        hours = [f"{i:02d}:00" for i in range(24)]
        response_times = [random.randint(30, 100) for _ in range(24)]
        
        self.response_ax.plot(hours, response_times, marker='o', color=COLORS["info"], linewidth=2)
        self.response_ax.fill_between(hours, response_times, alpha=0.3, color=COLORS["info"])
        self.response_ax.set_title('Response Time Trends (24h)', fontweight='bold')
        self.response_ax.set_ylabel('Response Time (ms)')
        self.response_ax.set_xlabel('Time of Day')
        self.response_ax.tick_params(axis='x', rotation=45)
        self.response_ax.grid(True, alpha=0.3)
        
        self.response_ax.set_facecolor(COLORS["light"])
        self.response_canvas.draw()
        
    def _update_resource_usage_chart(self):
        """Update the resource utilization chart"""
        self.resource_ax.clear()
        
        # Simulated resource usage data
        resources = ['CPU', 'Memory', 'Disk', 'Network']
        usage = [random.randint(40, 85) for _ in range(4)]
        colors = [COLORS["accent"], COLORS["info"], COLORS["warning"], COLORS["success"]]
        
        bars = self.resource_ax.bar(resources, usage, color=colors, alpha=0.8)
        self.resource_ax.set_title('Resource Utilization', fontweight='bold')
        self.resource_ax.set_ylabel('Usage (%)')
        self.resource_ax.set_ylim(0, 100)
        
        # Add value labels on bars
        for bar, use in zip(bars, usage):
            height = bar.get_height()
            self.resource_ax.text(bar.get_x() + bar.get_width()/2., height,
                                f'{use}%', ha='center', va='bottom')
                
        self.resource_ax.set_facecolor(COLORS["light"])
        self.resource_canvas.draw()

    def generate_sample_analytics(self):
        """Generate sample analytics data for demonstration"""
        try:
            # Create sample alerts data if none exists
            if not APP_STATE.alerts:
                sample_alerts = []
                attack_types = ["malware", "ransomware", "ddos", "phishing", "brute_force"]
                nodes = [f"Node_{i}" for i in range(1, 11)]
            
                for i in range(15):
                    alert = {
                        "time": (datetime.now() - timedelta(minutes=random.randint(1, 120))).isoformat(),
                        "node": random.choice(nodes),
                        "threat_score": random.randint(20, 95),
                        "path": " -> ".join(random.sample(nodes, min(3, len(nodes)))),
                        "status": random.choice(["active", "active", "investigating", "resolved"]),
                        "attack_type": random.choice(attack_types),
                        "security_level": random.randint(3, 10),
                        "logs_count": random.randint(1, 15),
                        "detection": random.choice(["Pattern Matching", "Behavioral Analysis", "Signature Detection"]),
                        "recommendations": [
                            "Isolate affected node",
                            "Update security policies", 
                            "Run deep scan",
                            "Review access logs"
                        ]
                    }
                    sample_alerts.append(alert)
            
                APP_STATE.alerts = sample_alerts
        
            # Create sample network if none exists
            if not hasattr(self.controller, 'network') or not self.controller.network.nodes:
                self.controller.create_sample_network()
        
            # Refresh analytics with the sample data
            self.refresh_analytics()
        
            self.status_var.set("✅ Sample analytics data generated successfully")
            self.status_label.config(text="● SAMPLE DATA", foreground=COLORS["success"])
        
            messagebox.showinfo("Sample Data", 
                              "Sample analytics data generated successfully!\n\n"
                              "• 15 sample alerts created\n"
                              "• Sample network topology generated\n"
                              "• All charts populated with sample data")
                          
        except Exception as e:
            messagebox.showerror("Error", f"Failed to generate sample data: {str(e)}")
            self.status_var.set(f"❌ Error generating sample data: {str(e)}")

    def export_analytics_report(self):
        """Export analytics report"""
        if not self.analytics_data:
            messagebox.showwarning("No Data", "No analytics data to export!")
            return
            
        try:
            # Simple text report for demonstration
            report = "GRAPHGUARD SECURITY ANALYTICS REPORT\n"
            report += "=" * 50 + "\n"
            report += f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
            
            metrics = self.analytics_data.get("metrics", {})
            report += "KEY METRICS:\n"
            report += f"- Total Alerts: {metrics.get('total_alerts', 0)}\n"
            report += f"- Active Threats: {metrics.get('active_threats', 0)}\n"
            report += f"- Network Nodes: {metrics.get('network_nodes', 0)}\n"
            report += f"- Security Score: {metrics.get('security_score', 0)}%\n\n"
            
            threat_analysis = self.analytics_data.get("threat_analysis", {})
            report += "THREAT ANALYSIS:\n"
            for attack_type, count in threat_analysis.get('attack_counts', {}).items():
                report += f"- {attack_type}: {count} occurrences\n"
                
            # Show in message box (in real app, this would save to file)
            messagebox.showinfo("Analytics Report", 
                              f"Analytics report generated successfully!\n\n"
                              f"Total alerts: {metrics.get('total_alerts', 0)}\n"
                              f"Security score: {metrics.get('security_score', 0)}%\n"
                              f"Active threats: {metrics.get('active_threats', 0)}")
                              
        except Exception as e:
            messagebox.showerror("Export Error", f"Failed to generate report: {str(e)}")
            
    def clear_analytics(self):
        """Clear analytics data and reset displays"""
        self.analytics_data = {}
        
        # Reset all charts
        self._setup_charts()
        
        # Clear treeviews
        for item in self.activity_tree.get_children():
            self.activity_tree.delete(item)
        for item in self.vectors_tree.get_children():
            self.vectors_tree.delete(item)
            
        # Reset metrics
        for label in self.metric_labels.values():
            label.config(text="0")
        for label in self.health_labels.values():
            label.config(text="0%")
        for label in self.perf_labels.values():
            label.config(text="N/A")
            
        self.status_var.set("Analytics data cleared")
        self.status_label.config(text="● READY", foreground=COLORS["info"])
        
    def on_show(self):
        """Called when the page is shown"""
        self.refresh_analytics()
        return "Analytics — Ready"

class GraphGuardApp:
    def __init__(self, root):
        self.root = root
        self.root.title("GraphGuard 2.0 - Cybersecurity Network Simulator")
        self.root.geometry("1400x900")
        self.root.configure(bg=COLORS["background"])
        
        # Apply a modern theme
        self.style = ttk.Style()
        self.style.theme_use('clam')
        self.configure_styles()
        
        self.network = NetworkGraph()
        self.threat_detector = ThreatDetector()
        self.selected_node = None
        self.attack_in_progress = False
        self.current_page = 0
        
        # Attack type variable
        self.attack_type = tk.StringVar(value="malware")
        
        # Make APP_STATE accessible to pages
        self.APP_STATE = AppState()
        
        self.setup_gui()
        self.create_sample_network()
        
    def configure_styles(self):
        # Configure custom styles for ttk widgets
        self.style.configure('Title.TLabel', 
                           background=COLORS["primary"],
                           foreground=COLORS["light"],
                           font=('Arial', 18, 'bold'),
                           padding=10)
        
        self.style.configure('Card.TFrame',
                           background=COLORS["light"],
                           relief='raised',
                           borderwidth=1)
        
        self.style.configure('Primary.TButton',
                           background=COLORS["accent"],
                           foreground=COLORS["light"],
                           font=('Arial', 10, 'bold'),
                           focuscolor='none')
        
        self.style.map('Primary.TButton',
                      background=[('active', COLORS["info"]),
                                 ('pressed', COLORS["secondary"])])
        
        self.style.configure('Success.TButton',
                           background=COLORS["success"],
                           foreground=COLORS["primary"],
                           font=('Arial', 10, 'bold'))
        
        self.style.configure('Danger.TButton',
                           background=COLORS["danger"],
                           foreground=COLORS["light"],
                           font=('Arial', 10, 'bold'))
        
        self.style.configure('Warning.TButton',
                           background=COLORS["warning"],
                           foreground=COLORS["primary"],
                           font=('Arial', 10, 'bold'))
        
        self.style.configure('Info.TButton',
                           background=COLORS["info"],
                           foreground=COLORS["primary"],
                           font=('Arial', 10, 'bold'))
        
        self.style.configure('Sidebar.TFrame',
                           background=COLORS["primary"])
        
        self.style.configure('Sidebar.TButton',
                           background=COLORS["primary"],
                           foreground=COLORS["light"],
                           font=('Arial', 11),
                           anchor='w',
                           padding=(15, 10))
        
        self.style.map('Sidebar.TButton',
                      background=[('active', COLORS["secondary"]),
                                 ('pressed', COLORS["dark"])])
    
    def setup_gui(self):
        # Create main frames with modern layout
        main_container = ttk.Frame(self.root)
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # Sidebar with navigation
        self.setup_sidebar(main_container)
        
        # Content area
        content_frame = ttk.Frame(main_container, style='Card.TFrame')
        content_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Header
        header_frame = ttk.Frame(content_frame, style='Title.TLabel')
        header_frame.pack(fill=tk.X, padx=10, pady=10)
        
        ttk.Label(header_frame, text="GraphGuard 2.0", style='Title.TLabel').pack(side=tk.LEFT)
        
        # Status indicator
        status_frame = ttk.Frame(header_frame)
        status_frame.pack(side=tk.RIGHT, padx=10)
        self.status_label = ttk.Label(status_frame, text="● SECURE", 
                                     foreground=COLORS["success"],
                                     font=('Arial', 12, 'bold'))
        self.status_label.pack()
        
        # Main content area with tabs
        self.setup_main_content(content_frame)
        
    def setup_sidebar(self, parent):
        sidebar = ttk.Frame(parent, style='Sidebar.TFrame', width=200)
        sidebar.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        sidebar.pack_propagate(False)
        
        # Logo/Title
        logo_frame = ttk.Frame(sidebar, style='Sidebar.TFrame')
        logo_frame.pack(fill=tk.X, pady=(10, 20))
        
        ttk.Label(logo_frame, text="GraphGuard", 
                 font=('Arial', 16, 'bold'),
                 background=COLORS["primary"],
                 foreground=COLORS["light"]).pack(pady=10)
        
        ttk.Label(logo_frame, text="Cybersecurity Platform", 
                 font=('Arial', 10),
                 background=COLORS["primary"],
                 foreground=COLORS["info"]).pack()
        
        # Navigation buttons - Updated to include Log Scanner
        nav_buttons = [
            ("🏠 Dashboard", self.show_dashboard),
            ("🌐 Local Network", self.show_local_network),
            ("⚡ Simulate Attack", self.simulate_attack),
            ("🚨 Alerts & Reports", self.show_alerts_reports),
            ("🔍 Scan Logs", self.show_log_scanner),  
            ("📊 Analytics", self.show_analytics),
        ]
        
        for text, command in nav_buttons:
            btn = ttk.Button(sidebar, text=text, command=command, style='Sidebar.TButton')
            btn.pack(fill=tk.X, padx=10, pady=5)
        
        # Footer with version info
        footer_frame = ttk.Frame(sidebar, style='Sidebar.TFrame')
        footer_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=10)
        
        ttk.Label(footer_frame, text="v2.0.1", 
                 font=('Arial', 8),
                 background=COLORS["primary"],
                 foreground=COLORS["info"]).pack()
    
    def setup_main_content(self, parent):
        # Create notebook for tabbed interface
        self.notebook = ttk.Notebook(parent)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Dashboard Tab
        self.dashboard_frame = ttk.Frame(self.notebook, style='Card.TFrame')
        self.notebook.add(self.dashboard_frame, text="Dashboard")
        self.setup_dashboard(self.dashboard_frame)
        
        # Network Visualization Tab
        self.network_frame = ttk.Frame(self.notebook, style='Card.TFrame')
        self.notebook.add(self.network_frame, text="Network Topology")
        self.setup_network_visualization(self.network_frame)
        
        # Alerts & Reports Tab
        self.alerts_frame = AlertsReportsPage(self.notebook, self)
        self.notebook.add(self.alerts_frame, text="Alerts & Reports")
        
        # Log Scanner Tab - NEW
        self.log_scanner_frame = LogScannerPage(self.notebook, self)
        self.notebook.add(self.log_scanner_frame, text="Log Scanner")
    
        # Analytics Tab - NEW
        self.analytics_frame = AnalyticsPage(self.notebook, self)
        self.notebook.add(self.analytics_frame, text="Analytics")
        
        # Network Logs Tab (existing logs functionality)
        self.logs_frame = ttk.Frame(self.notebook, style='Card.TFrame')
        self.notebook.add(self.logs_frame, text="Network Logs")
        self.setup_logs_tab(self.logs_frame)
    
    def setup_dashboard(self, parent):
        # Create a grid of dashboard cards
        cards_frame = ttk.Frame(parent)
        cards_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Top row of cards
        top_frame = ttk.Frame(cards_frame)
        top_frame.pack(fill=tk.X, pady=10)
        
        # Network Status Card
        status_card = ttk.LabelFrame(top_frame, text="Network Status", padding="15")
        status_card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        ttk.Label(status_card, text="Total Nodes", font=('Arial', 12)).pack(anchor=tk.W)
        self.total_nodes_label = ttk.Label(status_card, text="0", font=('Arial', 24, 'bold'), foreground=COLORS["accent"])
        self.total_nodes_label.pack(anchor=tk.W, pady=5)
        
        ttk.Label(status_card, text="Compromised", font=('Arial', 12)).pack(anchor=tk.W)
        self.compromised_label = ttk.Label(status_card, text="0", font=('Arial', 24, 'bold'), foreground=COLORS["danger"])
        self.compromised_label.pack(anchor=tk.W, pady=5)
        
        # Threat Level Card
        threat_card = ttk.LabelFrame(top_frame, text="Threat Level", padding="15")
        threat_card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        self.threat_level_label = ttk.Label(threat_card, text="LOW", font=('Arial', 24, 'bold'), foreground=COLORS["success"])
        self.threat_level_label.pack(pady=10)
        
        # Recent Activity Card
        activity_card = ttk.LabelFrame(top_frame, text="Recent Activity", padding="15")
        activity_card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        self.activity_text = tk.Text(activity_card, height=8, width=30, font=('Arial', 9))
        scrollbar = ttk.Scrollbar(activity_card, command=self.activity_text.yview)
        self.activity_text.configure(yscrollcommand=scrollbar.set)
        self.activity_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Quick Actions
        actions_frame = ttk.LabelFrame(cards_frame, text="Quick Actions", padding="15")
        actions_frame.pack(fill=tk.X, pady=10)
        
        action_buttons = [
            ("Create Sample Network", self.create_sample_network, 'Primary.TButton'),
            ("Simulate Attack", self.simulate_attack, 'Danger.TButton'),
            ("Scan Network Logs", self.scan_network_logs, 'Warning.TButton'),  # Updated name
            ("Reset Simulation", self.reset_simulation, 'Success.TButton')
        ]
        
        for text, command, style in action_buttons:
            btn = ttk.Button(actions_frame, text=text, command=command, style=style)
            btn.pack(side=tk.LEFT, padx=5, pady=5)
    
    def setup_network_visualization(self, parent):
        # Control panel for network
        control_frame = ttk.Frame(parent)
        control_frame.pack(fill=tk.X, padx=10, pady=10)
        
        ttk.Button(control_frame, text="Load Network", 
                  command=self.load_network, style='Primary.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Save Network", 
                  command=self.save_network, style='Primary.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Clear Network", 
                  command=self.clear_network, style='Danger.TButton').pack(side=tk.LEFT, padx=5)
        
        # Attack type selection
        attack_frame = ttk.Frame(control_frame)
        attack_frame.pack(side=tk.RIGHT, padx=10)
        
        ttk.Label(attack_frame, text="Attack Type:").pack(side=tk.LEFT)
        attack_types = ["malware", "ransomware", "ddos", "phishing", "brute_force"]
        attack_combo = ttk.Combobox(attack_frame, textvariable=self.attack_type, values=attack_types, state="readonly", width=12)
        attack_combo.pack(side=tk.LEFT, padx=5)
        
        # Visualization area
        viz_frame = ttk.Frame(parent)
        viz_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.fig, self.ax = plt.subplots(figsize=(10, 8), facecolor=COLORS["light"])
        self.canvas = FigureCanvasTkAgg(self.fig, viz_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Connect click event
        self.canvas.mpl_connect("button_press_event", self.on_click)
        
        # Node info panel
        info_frame = ttk.LabelFrame(viz_frame, text="Node Details", padding="10")
        info_frame.pack(fill=tk.X, pady=10)
        
        self.node_info_text = tk.Text(info_frame, height=8, width=30, font=('Arial', 9))
        scrollbar = ttk.Scrollbar(info_frame, command=self.node_info_text.yview)
        self.node_info_text.configure(yscrollcommand=scrollbar.set)
        self.node_info_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
    
    def setup_logs_tab(self, parent):
        logs_control_frame = ttk.Frame(parent)
        logs_control_frame.pack(fill=tk.X, padx=10, pady=10)
        
        ttk.Button(logs_control_frame, text="Scan Selected Node", 
                  command=self.scan_selected_logs, style='Primary.TButton').pack(side=tk.LEFT, padx=5)
        ttk.Button(logs_control_frame, text="Scan All Logs", 
                  command=self.scan_all_logs, style='Warning.TButton').pack(side=tk.LEFT, padx=5)
        
        # Logs display area
        logs_frame = ttk.Frame(parent)
        logs_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.logs_text = tk.Text(logs_frame, height=20, width=80, font=('Consolas', 9))
        scrollbar = ttk.Scrollbar(logs_frame, command=self.logs_text.yview)
        self.logs_text.configure(yscrollcommand=scrollbar.set)
        
        self.logs_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
    
    def show_log_scanner(self):
        """Show the Log Scanner page"""
        self.notebook.select(3)  # Select the Log Scanner tab (4th tab)
        # Update the page status
        status = self.log_scanner_frame.on_show()
        self.status_label.config(text=f"● {status}")
    
    def show_alerts_reports(self):
        """Show the Alerts & Reports page"""
        self.notebook.select(2)  # Select the Alerts & Reports tab
    
    def show_dashboard(self):
        self.notebook.select(0)
    
    def show_local_network(self):
        self.notebook.select(1)
    
    def show_analytics(self):
        """Show the Analytics page"""
        self.notebook.select(4)  # Select the Analytics tab (5th tab)
        # Update the page status
        status = self.analytics_frame.on_show()
        self.status_label.config(text=f"● {status}")
    
    def simulate_attack(self):
        if not self.network.nodes:
            messagebox.showerror("Error", "No network to simulate attack on!")
            return
            
        self.attack_in_progress = True
        
        # Switch to network visualization tab
        self.notebook.select(1)
        
        attack_type = self.attack_type.get()
        
        # Select random starting point for attack
        start_node_id = random.choice(list(self.network.nodes.keys()))
        start_node = self.network.get_node(start_node_id)
        start_node.compromised = True
        start_node.risk_level = 10
        start_node.add_log(f"Initial compromise: {attack_type} attack detected")
        
        # Use BFS to simulate attack propagation
        visited = set()
        queue = deque([(start_node_id, 0)])  # (node_id, propagation_step)
        
        while queue:
            current_node_id, step = queue.popleft()
            if current_node_id in visited:
                continue
                
            visited.add(current_node_id)
            current_node = self.network.get_node(current_node_id)
            
            # Skip if we've reached maximum propagation
            if step > 5:  # Limit propagation steps
                continue
                
            # Process neighbors
            for neighbor_id in self.network.get_neighbors(current_node_id):
                if neighbor_id not in visited:
                    neighbor = self.network.get_node(neighbor_id)
                    
                    # Calculate risk based on security level and connection weight
                    connection_risk = self.network.adjacency_list[current_node_id][neighbor_id]
                    security_factor = neighbor.security_level / 10
                    infection_probability = (1 - security_factor) * (connection_risk / 10)
                    
                    # Random chance based on probability
                    if random.random() < infection_probability:
                        neighbor.compromised = True
                        neighbor.risk_level = max(neighbor.risk_level, 10 - step)
                        neighbor.add_log(f"Infected from {current_node_id} via {attack_type}")
                        queue.append((neighbor_id, step + 1))
                    else:
                        # Even if not compromised, increase risk
                        risk_increase = min(5, int(infection_probability * 10))
                        neighbor.risk_level = min(10, neighbor.risk_level + risk_increase)
                        neighbor.add_log(f"Suspicious activity from {current_node_id}")
                        
            # Update visualization progressively
            self.draw_network()
            self.update_dashboard()
            self.root.update()
            time.sleep(0.5)  # Slow down for visualization
            
        messagebox.showinfo("Attack Simulation", f"{attack_type} attack simulation completed!")
        self.attack_in_progress = False
    
    def scan_network_logs(self):
        """Scan network logs (renamed from scan_logs)"""
        # Switch to network logs tab
        self.notebook.select(4)  # Now Network Logs is 5th tab
        self.scan_all_logs()
    
    def scan_all_logs(self):
        self.logs_text.delete(1.0, tk.END)
        
        if not self.network.nodes:
            self.logs_text.insert(tk.END, "No network data available.\n")
            return
            
        total_threats = 0
        for node_id, node in self.network.nodes.items():
            threats = self.threat_detector.scan_logs(node.logs)
            if threats:
                total_threats += sum(len(logs) for logs in threats.values())
                self.logs_text.insert(tk.END, f"\n=== Threats detected on {node_id} ===\n")
                for threat_type, logs in threats.items():
                    self.logs_text.insert(tk.END, f"{threat_type.upper()}: {len(logs)} occurrences\n")
                    for log in logs[-3:]:  # Show last 3 logs for each threat type
                        self.logs_text.insert(tk.END, f"  - {log}\n")
        
        if total_threats == 0:
            self.logs_text.insert(tk.END, "No threats detected in network logs.\n")
        else:
            self.logs_text.insert(tk.END, f"\nTotal threats detected: {total_threats}\n")
    
    def scan_selected_logs(self):
        if not self.selected_node:
            messagebox.showwarning("Warning", "Please select a node first.")
            return
            
        node = self.network.get_node(self.selected_node)
        self.logs_text.delete(1.0, tk.END)
        self.logs_text.insert(tk.END, f"Scanning logs for {self.selected_node}...\n\n")
        
        threats = self.threat_detector.scan_logs(node.logs)
        if threats:
            self.logs_text.insert(tk.END, f"THREATS DETECTED:\n")
            for threat_type, logs in threats.items():
                self.logs_text.insert(tk.END, f"\n{threat_type.upper()} ({len(logs)} occurrences):\n")
                for log in logs:
                    self.logs_text.insert(tk.END, f"  - {log}\n")
        else:
            self.logs_text.insert(tk.END, "No threats detected in node logs.\n")
    
    def create_sample_network(self):
        self.network = NetworkGraph()
        
        # Create nodes
        node_types = ["server", "workstation", "router", "firewall"]
        for i in range(1, 16):
            node_type = random.choice(node_types)
            ip = f"192.168.1.{i}"
            security_level = random.randint(3, 10)
            node = NetworkNode(f"Node_{i}", node_type, ip, security_level)
            self.network.add_node(node)
            
        # Create edges with random weights
        nodes = list(self.network.nodes.keys())
        for i in range(20):
            node1 = random.choice(nodes)
            node2 = random.choice(nodes)
            if node1 != node2 and node2 not in self.network.get_neighbors(node1):
                weight = random.randint(1, 10)
                self.network.add_edge(node1, node2, weight)
                
        self.reset_simulation()
        self.draw_network()
        messagebox.showinfo("Success", "Sample network created successfully!")
    
    def draw_network(self):
        self.ax.clear()
        
        if not self.network.nodes:
            self.ax.text(0.5, 0.5, "No Network Data\nCreate or Load a Network", 
                        ha='center', va='center', transform=self.ax.transAxes, fontsize=14)
            self.ax.set_facecolor(COLORS["light"])
            self.canvas.draw()
            return
        
        # Create a graph for visualization
        G = nx.Graph()
        for node_id, node in self.network.nodes.items():
            G.add_node(node_id, type=node.type, compromised=node.compromised, risk=node.risk_level)
            
        for node1_id, neighbors in self.network.adjacency_list.items():
            for node2_id, weight in neighbors.items():
                G.add_edge(node1_id, node2_id, weight=weight)
                
        # Use spring layout for better visualization
        self.node_positions = nx.spring_layout(G, k=3, iterations=50)
        
        # Color nodes based on status and type
        node_colors = []
        node_sizes = []
        for node_id in G.nodes():
            node = self.network.get_node(node_id)
            if node.compromised:
                node_colors.append(COLORS["danger"])
                node_sizes.append(700)
            elif node.risk_level > 5:
                node_colors.append(COLORS["warning"])
                node_sizes.append(600)
            elif node.risk_level > 0:
                node_colors.append(COLORS["info"])
                node_sizes.append(500)
            else:
                # Color by node type
                if node.type == "server":
                    node_colors.append(COLORS["success"])
                elif node.type == "firewall":
                    node_colors.append(COLORS["accent"])
                elif node.type == "router":
                    node_colors.append("#D08770")  # Complementary color
                else:  # workstation
                    node_colors.append(COLORS["secondary"])
                node_sizes.append(500)
                
        # Draw the network
        nx.draw_networkx_nodes(G, self.node_positions, node_color=node_colors, 
                              node_size=node_sizes, alpha=0.9, edgecolors='black', linewidths=1)
        nx.draw_networkx_edges(G, self.node_positions, alpha=0.5, edge_color='gray', width=2)
        nx.draw_networkx_labels(G, self.node_positions, font_size=8, font_weight='bold')
        
        # Draw edge weights
        edge_labels = nx.get_edge_attributes(G, 'weight')
        nx.draw_networkx_edge_labels(G, self.node_positions, edge_labels=edge_labels, font_size=7)
        
        # Highlight selected node
        if self.selected_node and self.selected_node in G.nodes():
            nx.draw_networkx_nodes(G, self.node_positions, nodelist=[self.selected_node], 
                                  node_color='green', node_size=800, alpha=0.7)
            
        self.ax.set_title("Network Topology - GraphGuard 2.0", fontsize=14, fontweight='bold')
        self.ax.set_facecolor(COLORS["light"])
        self.ax.axis('off')
        self.canvas.draw()
        
        # Update dashboard
        self.update_dashboard()
    
    def update_dashboard(self):
        if not self.network.nodes:
            return
            
        total_nodes = len(self.network.nodes)
        compromised_nodes = sum(1 for node in self.network.nodes.values() if node.compromised)
        
        self.total_nodes_label.config(text=str(total_nodes))
        self.compromised_label.config(text=str(compromised_nodes))
        
        # Update threat level
        threat_level = "LOW"
        threat_color = COLORS["success"]
        if compromised_nodes > 0:
            threat_level = "HIGH"
            threat_color = COLORS["danger"]
            self.status_label.config(text="● THREAT DETECTED", foreground=COLORS["danger"])
        elif any(node.risk_level > 5 for node in self.network.nodes.values()):
            threat_level = "MEDIUM"
            threat_color = COLORS["warning"]
            self.status_label.config(text="● SUSPICIOUS ACTIVITY", foreground=COLORS["warning"])
        else:
            self.status_label.config(text="● SECURE", foreground=COLORS["success"])
            
        self.threat_level_label.config(text=threat_level, foreground=threat_color)
        
        # Update recent activity
        self.activity_text.delete(1.0, tk.END)
        all_logs = []
        for node in self.network.nodes.values():
            for log in node.logs[-2:]:  # Get last 2 logs from each node
                all_logs.append(f"{node.id}: {log}")
                
        # Show most recent logs
        for log in all_logs[-10:]:
            self.activity_text.insert(tk.END, f"• {log}\n")
    
    def on_click(self, event):
        if event.inaxes != self.ax:
            return
            
        # Find the closest node
        min_dist = float('inf')
        clicked_node = None
        
        for node_id, pos in self.node_positions.items():
            dist = (event.xdata - pos[0])**2 + (event.ydata - pos[1])**2
            if dist < min_dist and dist < 0.1:  # Threshold for clicking
                min_dist = dist
                clicked_node = node_id
                
        if clicked_node:
            self.selected_node = clicked_node
            self.display_node_info(clicked_node)
            self.draw_network()
    
    def display_node_info(self, node_id):
        node = self.network.get_node(node_id)
        if not node:
            return
            
        self.node_info_text.delete(1.0, tk.END)
        info = f"Node ID: {node.id}\n"
        info += f"Type: {node.type}\n"
        info += f"IP: {node.ip}\n"
        info += f"Security Level: {node.security_level}\n"
        info += f"Compromised: {node.compromised}\n"
        info += f"Risk Level: {node.risk_level}\n"
        info += f"Neighbors: {len(node.neighbors)}\n"
        
        # Show recent logs
        info += "\nRecent Logs:\n"
        for log in node.logs[-5:]:
            info += f"- {log}\n"
            
        # Show detected threats
        threats = self.threat_detector.scan_logs(node.logs)
        if threats:
            info += "\nDetected Threats:\n"
            for threat_type, logs in threats.items():
                info += f"- {threat_type}: {len(logs)} occurrences\n"
                
        self.node_info_text.insert(1.0, info)
    
    def reset_simulation(self):
        for node in self.network.nodes.values():
            node.compromised = False
            node.risk_level = 0
            node.logs = []
            
        self.selected_node = None
        self.attack_in_progress = False
        self.draw_network()
        self.node_info_text.delete(1.0, tk.END)
        self.status_label.config(text="● SECURE", foreground=COLORS["success"])
    
    def load_network(self):
        filename = filedialog.askopenfilename(
            title="Load Network",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not filename:
            return
            
        try:
            with open(filename, 'r') as f:
                data = json.load(f)
                
            self.network = NetworkGraph()
            
            # Load nodes
            for node_data in data['nodes']:
                node = NetworkNode(
                    node_data['id'],
                    node_data['type'],
                    node_data['ip'],
                    node_data['security_level']
                )
                node.compromised = node_data.get('compromised', False)
                node.risk_level = node_data.get('risk_level', 0)
                node.logs = node_data.get('logs', [])
                self.network.add_node(node)
                
            # Load edges
            for edge in data['edges']:
                self.network.add_edge(edge['node1'], edge['node2'], edge['weight'])
                
            self.reset_simulation()
            messagebox.showinfo("Success", "Network loaded successfully!")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load network: {str(e)}")
            
    def save_network(self):
        if not self.network.nodes:
            messagebox.showerror("Error", "No network to save!")
            return
            
        filename = filedialog.asksaveasfilename(
            title="Save Network",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not filename:
            return
            
        try:
            data = {
                'nodes': [],
                'edges': []
            }
            
            # Save nodes
            for node_id, node in self.network.nodes.items():
                node_data = {
                    'id': node.id,
                    'type': node.type,
                    'ip': node.ip,
                    'security_level': node.security_level,
                    'compromised': node.compromised,
                    'risk_level': node.risk_level,
                    'logs': node.logs
                }
                data['nodes'].append(node_data)
                
            # Save edges
            for node1_id, neighbors in self.network.adjacency_list.items():
                for node2_id, weight in neighbors.items():
                    # Avoid duplicates
                    if node1_id < node2_id:
                        data['edges'].append({
                            'node1': node1_id,
                            'node2': node2_id,
                            'weight': weight
                        })
                        
            with open(filename, 'w') as f:
                json.dump(data, f, indent=2)
                
            messagebox.showinfo("Success", "Network saved successfully!")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save network: {str(e)}")
            
    def clear_network(self):
        if messagebox.askyesno("Confirm", "Are you sure you want to clear the network?"):
            self.network = NetworkGraph()
            self.reset_simulation()

def main():
    root = tk.Tk()
    app = GraphGuardApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()