#!/usr/bin/env python3
import sys
import os
import csv
import re
from urllib.parse import urlparse

def format_color(text, color_code):
    """Formats text with ANSI escape codes for terminal color."""
    if sys.stdout.isatty():
        return f"\033[{color_code}m{text}\033[0m"
    return text

def strip_ansi(text):
    """Strips ANSI escape sequences from a string to ensure clean log files."""
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    return ansi_escape.sub('', text)

VALID_SERVLETS = {
    "RegistrazioneServlet",
    "landingpage",
    "UtenteServlet",
    "ProdottiPerCategoriaServlet",
    "ProdottoServlet",
    "WishlistServlet",
    "RicercaServlet",
    "ConfrontaServlet",
    "AggiungiCarrelloServlet",
    "EditCarrello",
    "CheckOutServlet",
    "RecensioniServlet",
    "logoutServlet",
    "LoginServlet"
}

def get_servlet_name(url, label):
    """Extracts servlet name from JTL label or URL path segment, validated against known servlets."""
    # 1. Match against known JTL label patterns (most robust and reliable)
    if label:
        label_lower = label.lower()
        if "registrazione" in label_lower:
            return "RegistrazioneServlet"
        elif "landing" in label_lower:
            return "landingpage"
        elif "utente" in label_lower:
            return "UtenteServlet"
        elif "categoria" in label_lower:
            return "ProdottiPerCategoriaServlet"
        elif "prodotto" in label_lower:
            return "ProdottoServlet"
        elif "wishlist" in label_lower:
            return "WishlistServlet"
        elif "ricerca" in label_lower:
            return "RicercaServlet"
        elif "confronta" in label_lower:
            return "ConfrontaServlet"
        elif "aggiungi a carrello" in label_lower:
            return "AggiungiCarrelloServlet"
        elif "edit carrello" in label_lower:
            return "EditCarrello"
        elif "check out" in label_lower or "checkout" in label_lower:
            return "CheckOutServlet"
        elif "recensione" in label_lower:
            return "RecensioniServlet"
        elif "logout" in label_lower:
            return "logoutServlet"
        elif "login" in label_lower:
            return "LoginServlet"

    # 2. Fallback to extracting from the URL path segment
    if url:
        try:
            path = urlparse(url).path
            segments = [s for s in path.split("/") if s]
            if segments:
                first_seg = segments[0]
                # Skip Java context path
                if first_seg in ["2chance_war", "2chance"] and len(segments) > 1:
                    first_seg = segments[1]
                if first_seg in VALID_SERVLETS:
                    return first_seg
        except Exception:
            pass
            
    return "Unknown"

def find_matching_jtl(csv_path, jmeter_logs_dir):
    """Finds the corresponding JTL log matching the timestamp in the CSV filename."""
    basename = os.path.basename(csv_path)
    ts_match = re.search(r'(\d{4}_\d{2}_\d{2}_\d{2}_\d{2}_\d{2})', basename)
    if not ts_match:
        return None
    timestamp = ts_match.group(1)
    
    if not os.path.exists(jmeter_logs_dir):
        return None
        
    for f in os.listdir(jmeter_logs_dir):
        if timestamp in f and f.endswith(".jtl"):
            return os.path.join(jmeter_logs_dir, f)
            
    return None

def parse_jtl(jtl_path):
    """Parses a JTL file and extracts valid request intervals, discarding malformed or corrupted rows."""
    intervals = []
    if not jtl_path or not os.path.exists(jtl_path):
        return intervals
        
    with open(jtl_path, mode='r', encoding='utf-8') as f:
        reader = csv.reader(f)
        try:
            headers = next(reader)
        except StopIteration:
            return intervals
            
        headers = [h.strip() for h in headers]
        
        ts_idx = next((i for i, h in enumerate(headers) if h.lower() == "timestamp"), None)
        elapsed_idx = next((i for i, h in enumerate(headers) if h.lower() == "elapsed"), None)
        if ts_idx is None or elapsed_idx is None:
            return intervals
            
        label_idx = next((i for i, h in enumerate(headers) if h.lower() == "label"), None)
        url_idx = next((i for i, h in enumerate(headers) if h.lower() == "url"), None)
        
        for row in reader:
            # Drop empty or malformed rows resulting from concurrent write interleaving
            if not row or len(row) != len(headers):
                continue
            try:
                start_ms = int(row[ts_idx])
                elapsed = int(row[elapsed_idx])
                end_ms = start_ms + elapsed
                
                label = row[label_idx] if (label_idx is not None and label_idx < len(row)) else ""
                url = row[url_idx] if (url_idx is not None and url_idx < len(row)) else ""
                
                servlet = get_servlet_name(url, label)
                # Only analyze requests mapping to our 14 recognized backend servlets
                if servlet == "Unknown" or servlet not in VALID_SERVLETS:
                    continue
                    
                intervals.append({
                    'servlet': servlet,
                    'start_ms': start_ms,
                    'end_ms': end_ms,
                    'elapsed': elapsed
                })
            except Exception:
                continue
    return intervals

def analyze_csv(file_path):
    if not os.path.exists(file_path):
        print(format_color(f"Errore: Il file '{file_path}' non esiste.", "31;1"))
        return

    # Set up folders relative to script location or CSV location
    script_dir = os.path.dirname(os.path.abspath(__file__))
    csv_dir = os.path.dirname(os.path.abspath(file_path))
    if os.path.basename(csv_dir) == "energibridge_logs":
        base_dir = os.path.dirname(csv_dir)
    else:
        base_dir = script_dir

    jmeter_logs_dir = os.path.join(base_dir, "jmeter_logs")
    system_logs_dir = os.path.join(base_dir, "extractor_logs", "performance_system_testing_logs")
    unit_logs_dir = os.path.join(base_dir, "extractor_logs", "performance_unit_testing_logs")

    os.makedirs(system_logs_dir, exist_ok=True)
    os.makedirs(unit_logs_dir, exist_ok=True)

    # Determine base filename for output logs
    csv_basename = os.path.basename(file_path)
    ts_match = re.search(r'(\d{4}_\d{2}_\d{2}_\d{2}_\d{2}_\d{2})', csv_basename)
    timestamp = ts_match.group(1) if ts_match else "unknown"
    
    type_match = re.search(r'log_([a-zA-Z0-9]+)_energy', csv_basename)
    test_type = type_match.group(1) if type_match else "testing"
    
    out_filename = f"log_{test_type}_extractor_{timestamp}.log"
    system_out_path = os.path.join(system_logs_dir, out_filename)
    unit_out_path = os.path.join(unit_logs_dir, out_filename)

    # Read EnergiBridge CSV
    with open(file_path, mode='r', encoding='utf-8') as f:
        reader = csv.reader(f)
        try:
            headers = next(reader)
        except StopIteration:
            print(format_color("Errore: Il file CSV e vuoto.", "31;1"))
            return
        eb_rows = list(reader)

    headers = [h.strip() for h in headers]

    try:
        time_idx = headers.index("Time")
    except ValueError:
        time_idx = None

    cpu_energy_idx = next((i for i, h in enumerate(headers) if "CPU_ENERGY" in h), None)
    core_energy_idx = next((i for i, h in enumerate(headers) if "CORE0_ENERGY" in h or "PPO_ENERGY" in h), None)
    cpu_usage_idxs = [i for i, h in enumerate(headers) if "CPU_USAGE_" in h]
    cpu_freq_idxs = [i for i, h in enumerate(headers) if "CPU_FREQUENCY_" in h]
    used_mem_idx = next((i for i, h in enumerate(headers) if "USED_MEMORY" in h), None)

    # 1. Parse Eb Rows for Analysis
    eb_data = []

    for row in eb_rows:
        if not row:
            continue
        try:
            t_val = float(row[time_idx]) if (time_idx is not None and time_idx < len(row) and row[time_idx]) else None
            
            cpu_e = float(row[cpu_energy_idx]) if (cpu_energy_idx is not None and cpu_energy_idx < len(row) and row[cpu_energy_idx]) else None
            core_e = float(row[core_energy_idx]) if (core_energy_idx is not None and core_energy_idx < len(row) and row[core_energy_idx]) else None
            
            usages = [float(row[idx]) for idx in cpu_usage_idxs if idx < len(row) and row[idx]]
            avg_u = sum(usages) / len(usages) if usages else 0.0
            
            freqs = [float(row[idx]) for idx in cpu_freq_idxs if idx < len(row) and row[idx]]
            avg_f = sum(freqs) / len(freqs) if freqs else 0.0
            
            mem_b = float(row[used_mem_idx]) if (used_mem_idx is not None and used_mem_idx < len(row) and row[used_mem_idx]) else 0.0
            mem_gb = mem_b / (1024.0 ** 3)
            
            eb_data.append({
                'time_ms': t_val,
                'cpu_energy': cpu_e,
                'core_energy': core_e,
                'cpu_usage': avg_u,
                'cpu_freq': avg_f,
                'ram_usage_gb': mem_gb
            })
        except ValueError:
            continue

    if not eb_data:
        print(format_color("Errore: Nessun dato valido trovato nel CSV.", "31;1"))
        return

    # Find and parse JTL intervals early to align timestamps if needed
    jtl_path = find_matching_jtl(file_path, jmeter_logs_dir)
    jtl_intervals = parse_jtl(jtl_path) if jtl_path else []

    # Align timestamps if time_ms is estimated/missing
    current_est_time = eb_data[0]['time_ms'] if eb_data[0]['time_ms'] is not None else (jtl_intervals[0]['start_ms'] if jtl_intervals else 0.0)
    for rec in eb_data:
        if rec['time_ms'] is None:
            rec['time_ms'] = current_est_time
            current_est_time += 200.0
        else:
            current_est_time = rec['time_ms']

    # Calculate time steps and energy deltas with noise filtering
    for k in range(len(eb_data)):
        rec = eb_data[k]
        rec['delta_t'] = 0.0
        rec['delta_E_CPU'] = 0.0
        rec['delta_E_Core'] = 0.0
        
        if k > 0:
            prev_rec = eb_data[k - 1]
            delta_t = (rec['time_ms'] - prev_rec['time_ms']) / 1000.0
            if delta_t > 0:
                rec['delta_t'] = delta_t
                
                # CPU Energy Delta with Noise Filtering (< 55 W)
                if rec['cpu_energy'] is not None and prev_rec['cpu_energy'] is not None:
                    diff_cpu = rec['cpu_energy'] - prev_rec['cpu_energy']
                    if 0 <= diff_cpu <= 55.0 * delta_t:
                        rec['delta_E_CPU'] = diff_cpu
                        
                # Core Energy Delta with Noise Filtering (< 45 W)
                if rec['core_energy'] is not None and prev_rec['core_energy'] is not None:
                    diff_core = rec['core_energy'] - prev_rec['core_energy']
                    if 0 <= diff_core <= 45.0 * delta_t:
                        rec['delta_E_Core'] = diff_core

    # Calculate Global metrics
    duration_sec = sum(rec['delta_t'] for rec in eb_data)
    if duration_sec <= 0:
        duration_sec = 0.001

    total_cpu_energy = sum(rec['delta_E_CPU'] for rec in eb_data)
    avg_cpu_power = total_cpu_energy / duration_sec
    total_core_energy = sum(rec['delta_E_Core'] for rec in eb_data)

    avg_cpu_usage = sum(rec['cpu_usage'] for rec in eb_data) / len(eb_data) if eb_data else 0.0
    peak_cpu_usage = max(rec['cpu_usage'] for rec in eb_data) if eb_data else 0.0
    avg_cpu_freq = sum(rec['cpu_freq'] for rec in eb_data) / len(eb_data) if eb_data else 0.0
    avg_mem_usage = sum(rec['ram_usage_gb'] for rec in eb_data) / len(eb_data) if eb_data else 0.0
    peak_mem_usage = max(rec['ram_usage_gb'] for rec in eb_data) if eb_data else 0.0

    # Format global report
    global_report_lines = []
    global_report_lines.append(format_color(f"\n=== Analisi Energetica di EnergiBridge ===", "36;1"))
    global_report_lines.append(f"Elaborazione file: {file_path}")
    global_report_lines.append("=" * 45)
    global_report_lines.append(f"Durata Workload Profiled: {duration_sec:.2f} secondi (~{duration_sec/60.0:.2f} minuti)")
    global_report_lines.append("-" * 45)

    header_fmt = "{:<30} | {:<12} | {:<8}"
    row_fmt = "{:<30} | " + format_color("{:<12}", "32;1") + " | {:<8}"
    
    global_report_lines.append(format_color(header_fmt.format("Metrica di Sostenibilita", "Valore", "Unita"), "1"))
    global_report_lines.append("-" * 56)
    global_report_lines.append(row_fmt.format("Energia CPU Package", f"{total_cpu_energy:.2f}", "Joules (J)"))
    global_report_lines.append(row_fmt.format("Potenza Media CPU Package", f"{avg_cpu_power:.2f}", "Watt (W)"))
    global_report_lines.append(row_fmt.format("Energia PPO (Core)", f"{total_core_energy:.2f}", "Joules (J)"))
    global_report_lines.append(row_fmt.format("CPU Usage (Media)", f"{avg_cpu_usage:.2f}", "Percentuale (%)"))
    global_report_lines.append(row_fmt.format("CPU Usage (Picco)", f"{peak_cpu_usage:.2f}", "Percentuale (%)"))
    global_report_lines.append(row_fmt.format("Frequenza Media CPU", f"{avg_cpu_freq:.2f}", "MHz"))
    global_report_lines.append(row_fmt.format("Memoria RAM Usata (Media)", f"{avg_mem_usage:.2f}", "Gigabyte (GB)"))
    global_report_lines.append(row_fmt.format("Memoria RAM Usata (Picco)", f"{peak_mem_usage:.2f}", "Gigabyte (GB)"))
    global_report_lines.append("=" * 56)
    global_report_lines.append(format_color("Analisi completata con successo.", "32"))

    global_report = "\n".join(global_report_lines)

    # 2. Servlet-Specific Unit Analysis
    unit_report_lines = []
    
    if not jtl_path:
        warning_msg = f"Attenzione: File JTL corrispondente per il timestamp '{timestamp}' non trovato in '{jmeter_logs_dir}'. Impossibile calcolare le metriche per i singoli servlet."
        unit_report_lines.append(format_color(warning_msg, "33"))
        servlet_stats = {}
    elif not jtl_intervals:
        warning_msg = f"Attenzione: Nessun intervallo valido trovato nel file JTL '{jtl_path}'. Impossibile calcolare le metriche per i singoli servlet."
        unit_report_lines.append(format_color(warning_msg, "33"))
        servlet_stats = {}
    else:
        jtl_intervals.sort(key=lambda x: x['start_ms'])
        
        distinct_servlets = sorted(list(set(r['servlet'] for r in jtl_intervals)))
        
        servlet_metrics = {}
        for s in distinct_servlets:
            servlet_metrics[s] = {
                'cpu_energy': 0.0,
                'core_energy': 0.0,
                'cpu_usages': [],
                'cpu_freqs': [],
                'ram_usages': [],
                'active_duration': 0.0,
                'request_elapsed_times': []
            }
            
        for r in jtl_intervals:
            s = r['servlet']
            servlet_metrics[s]['request_elapsed_times'].append(r['elapsed'])

        # Slice attribution sweep-line algorithm (O(N + M))
        active_pool = []
        j_idx = 0
        num_jtl = len(jtl_intervals)
        
        for k in range(1, len(eb_data)):
            prev_rec = eb_data[k - 1]
            curr_rec = eb_data[k]
            
            T_prev = prev_rec['time_ms']
            T_curr = curr_rec['time_ms']
            
            delta_t = curr_rec['delta_t']
            if delta_t <= 0:
                continue
                
            delta_E_CPU = curr_rec['delta_E_CPU']
            delta_E_Core = curr_rec['delta_E_Core']
                    
            # Add newly active JTL requests to active_pool
            while j_idx < num_jtl and jtl_intervals[j_idx]['start_ms'] <= T_curr:
                active_pool.append(jtl_intervals[j_idx])
                j_idx += 1
                
            # Retain only JTL requests that cover this slice
            active_pool = [r for r in active_pool if r['end_ms'] >= T_prev]
            
            N = len(active_pool)
            if N > 0:
                cpu_share = delta_E_CPU / N
                core_share = delta_E_Core / N
                
                active_servlets_in_slice = set()
                for req in active_pool:
                    s = req['servlet']
                    servlet_metrics[s]['cpu_energy'] += cpu_share
                    servlet_metrics[s]['core_energy'] += core_share
                    active_servlets_in_slice.add(s)
                    
                for s in active_servlets_in_slice:
                    servlet_metrics[s]['cpu_usages'].append(curr_rec['cpu_usage'])
                    servlet_metrics[s]['cpu_freqs'].append(curr_rec['cpu_freq'])
                    servlet_metrics[s]['ram_usages'].append(curr_rec['ram_usage_gb'])
                    servlet_metrics[s]['active_duration'] += delta_t

        servlet_stats = {}
        for s, data in servlet_metrics.items():
            total_reqs = len(data['request_elapsed_times'])
            avg_resp = sum(data['request_elapsed_times']) / total_reqs if total_reqs > 0 else 0.0
            active_dur = data['active_duration']
            
            cpu_e = data['cpu_energy']
            core_e = data['core_energy']
            
            avg_power = cpu_e / active_dur if active_dur > 0.0 else 0.0
            avg_usage = sum(data['cpu_usages']) / len(data['cpu_usages']) if data['cpu_usages'] else 0.0
            peak_usage = max(data['cpu_usages']) if data['cpu_usages'] else 0.0
            avg_freq = sum(data['cpu_freqs']) / len(data['cpu_freqs']) if data['cpu_freqs'] else 0.0
            avg_ram = sum(data['ram_usages']) / len(data['ram_usages']) if data['ram_usages'] else 0.0
            peak_ram = max(data['ram_usages']) if data['ram_usages'] else 0.0
            
            servlet_stats[s] = {
                'requests': total_reqs,
                'avg_resp_time_ms': avg_resp,
                'cpu_energy_j': cpu_e,
                'avg_cpu_power_w': avg_power,
                'core_energy_j': core_e,
                'avg_cpu_usage_pct': avg_usage,
                'peak_cpu_usage_pct': peak_usage,
                'avg_cpu_freq_mhz': avg_freq,
                'avg_ram_usage_gb': avg_ram,
                'peak_ram_usage_gb': peak_ram
            }

        unit_report_lines.append(format_color("=== Analisi Energetica per Singolo Servlet ===", "36;1"))
        unit_report_lines.append(f"Elaborazione file: {file_path}")
        unit_report_lines.append(f"File JTL correlato: {jtl_path}")
        unit_report_lines.append("=" * 155)
        
        tbl_header_fmt = "{:<28} | {:<8} | {:<18} | {:<14} | {:<13} | {:<15} | {:<12} | {:<12} | {:<12} | {:<12}"
        tbl_row_fmt = "{:<28} | {:<8} | {:<18.2f} | " + format_color("{:<14.2f}", "32;1") + " | {:<13.2f} | {:<15.2f} | {:<12.2f} | {:<12.2f} | {:<12.2f} | {:<12.2f}"
        
        unit_report_lines.append(format_color(tbl_header_fmt.format("Servlet", "Requests", "Avg Resp Time (ms)", "CPU Energy (J)", "Avg Power (W)", "Core Energy (J)", "Avg CPU (%)", "Peak CPU (%)", "Avg RAM (GB)", "Peak RAM (GB)"), "1"))
        unit_report_lines.append("-" * 155)
        
        # Sort by CPU energy descending
        sorted_servlets = sorted(servlet_stats.items(), key=lambda x: x[1]['cpu_energy_j'], reverse=True)
        for s, stats in sorted_servlets:
            unit_report_lines.append(tbl_row_fmt.format(
                s,
                stats['requests'],
                stats['avg_resp_time_ms'],
                stats['cpu_energy_j'],
                stats['avg_cpu_power_w'],
                stats['core_energy_j'],
                stats['avg_cpu_usage_pct'],
                stats['peak_cpu_usage_pct'],
                stats['avg_ram_usage_gb'],
                stats['peak_ram_usage_gb']
            ))
        unit_report_lines.append("=" * 155)
        unit_report_lines.append(format_color("Analisi di unita completata con successo.", "32"))

    unit_report = "\n".join(unit_report_lines)

    # 3. Print both reports to stdout
    print(global_report)
    print(unit_report)

    # 4. Save clean reports (without ANSI colors) to files
    clean_global_report = strip_ansi(global_report)
    clean_unit_report = strip_ansi(unit_report)
    
    with open(system_out_path, 'w', encoding='utf-8') as sf:
        sf.write(clean_global_report)
    print(f"\nReport globale salvato in: {system_out_path}")

    with open(unit_out_path, 'w', encoding='utf-8') as uf:
        uf.write(clean_unit_report)
    print(f"Report di unita salvato in: {unit_out_path}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(format_color("Utilizzo: python energibridge_metrics_extractor.py <percorso_file_csv>", "33"))
        sys.exit(1)
    
    csv_file = sys.argv[1]
    analyze_csv(csv_file)
