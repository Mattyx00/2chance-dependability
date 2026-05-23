#!/usr/bin/env python3
import sys
import os
import re
import csv
import json
import subprocess
import time
import shutil

def format_color(text, color_code):
    """Formats text with ANSI escape codes for terminal color."""
    if sys.stdout.isatty():
        return f"\033[{color_code}m{text}\033[0m"
    return text

def find_energibridge():
    """Locates the EnergiBridge executable on Windows or search path."""
    default_path = r"C:\Program Files\EnergiBridge\energibridge.exe"
    if os.path.exists(default_path):
        return default_path
    
    path_eb = shutil.which("energibridge")
    if path_eb:
        return path_eb
        
    return None

def get_class_package(java_file_path):
    """Reads a Java file and returns its package declaration."""
    with open(java_file_path, 'r', encoding='utf-8') as f:
        content = f.read()
        match = re.search(r'package\s+([a-zA-Z0-9_\.]+)\s*;', content)
        if match:
            return match.group(1)
    return None

def check_and_compile():
    """Checks for target/benchmarks.jar and compiles if not found."""
    jar_path = "target/benchmarks.jar"
    if not os.path.exists(jar_path):
        print(format_color("JMH jar (target/benchmarks.jar) non trovato. Avvio della compilazione Maven...", "33"))
        res = subprocess.run(["mvn", "clean", "package", "-DskipTests"], shell=True)
        if res.returncode != 0:
            print(format_color("Errore durante la compilazione Maven.", "31;1"))
            sys.exit(1)
        print(format_color("Compilazione completata con successo.", "32"))

def get_benchmark_methods(fully_qualified_class):
    """Retrieves all benchmark methods inside a given class using JMH -l."""
    print(format_color(f"Recupero dei microbenchmark per {fully_qualified_class}...", "36"))
    res = subprocess.run(["java", "-jar", "target/benchmarks.jar", fully_qualified_class, "-l"], capture_output=True, text=True, shell=False)
    if res.returncode != 0:
        print(format_color(f"Errore nel recupero dei benchmark per {fully_qualified_class}: {res.stderr}", "31;1"))
        return []
    
    methods = []
    for line in res.stdout.splitlines():
        line = line.strip()
        if line.startswith(fully_qualified_class + "."):
            methods.append(line)
    return methods

def parse_eb_csv(csv_path):
    """Reads and parses an EnergiBridge CSV file, filtering out RAPL noise."""
    if not os.path.exists(csv_path):
        return None
        
    with open(csv_path, mode='r', encoding='utf-8') as f:
        reader = csv.reader(f)
        try:
            headers = [h.strip() for h in next(reader)]
        except StopIteration:
            return None
        rows = list(reader)
        
    if not rows:
        return None
        
    try:
        time_idx = headers.index("Time")
    except ValueError:
        time_idx = None
        
    cpu_energy_idx = next((i for i, h in enumerate(headers) if "CPU_ENERGY" in h), None)
    core_energy_idx = next((i for i, h in enumerate(headers) if "CORE0_ENERGY" in h or "PPO_ENERGY" in h), None)
    cpu_usage_idxs = [i for i, h in enumerate(headers) if "CPU_USAGE_" in h]
    cpu_freq_idxs = [i for i, h in enumerate(headers) if "CPU_FREQUENCY_" in h]
    used_mem_idx = next((i for i, h in enumerate(headers) if "USED_MEMORY" in h), None)
    
    eb_data = []
    for row in rows:
        if not row or len(row) == 0:
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
        except (ValueError, IndexError):
            continue
            
    if not eb_data:
        return None
        
    # Align timestamps if estimated/missing
    current_est_time = eb_data[0]['time_ms'] if eb_data[0]['time_ms'] is not None else 0.0
    for rec in eb_data:
        if rec['time_ms'] is None:
            rec['time_ms'] = current_est_time
            current_est_time += 200.0
        else:
            current_est_time = rec['time_ms']
            
    # Calculate delta times and energy deltas with noise filtering
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
                
                # CPU Energy Noise Filter (< 250 W)
                if rec['cpu_energy'] is not None and prev_rec['cpu_energy'] is not None:
                    diff_cpu = rec['cpu_energy'] - prev_rec['cpu_energy']
                    if 0 <= diff_cpu <= 250.0 * delta_t:
                        rec['delta_E_CPU'] = diff_cpu
                        
                # Core Energy Noise Filter (< 150 W)
                if rec['core_energy'] is not None and prev_rec['core_energy'] is not None:
                    diff_core = rec['core_energy'] - prev_rec['core_energy']
                    if 0 <= diff_core <= 150.0 * delta_t:
                        rec['delta_E_Core'] = diff_core
                        
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
    
    return {
        'duration_sec': duration_sec,
        'cpu_energy_j': total_cpu_energy,
        'avg_power_w': avg_cpu_power,
        'core_energy_j': total_core_energy,
        'avg_cpu_usage_pct': avg_cpu_usage,
        'peak_cpu_usage_pct': peak_cpu_usage,
        'avg_cpu_freq_mhz': avg_cpu_freq,
        'avg_ram_usage_gb': avg_mem_usage,
        'peak_ram_usage_gb': peak_mem_usage
    }

def parse_jmh_json(json_path):
    """Parses JMH JSON output report to fetch performance timings."""
    scores = {}
    if not os.path.exists(json_path):
        return scores
    try:
        with open(json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        for entry in data:
            bench_name = entry.get("benchmark", "")
            method_name = bench_name.split(".")[-1]
            primary_metric = entry.get("primaryMetric", {})
            score = primary_metric.get("score", 0.0)
            unit = primary_metric.get("scoreUnit", "ms/op")
            scores[method_name] = (score, unit)
    except Exception as e:
        print(format_color(f"Attenzione: Errore nel parsing del file JSON JMH: {e}", "33"))
    return scores

def main():
    if len(sys.argv) < 2:
        print(format_color("Utilizzo: python run_jmh_energy_profiler.py <cartella_classi_jmh>", "33"))
        print("Esempio: python src/jmh/run_jmh_energy_profiler.py src/jmh/java/model/dao")
        sys.exit(1)
        
    input_dir = os.path.abspath(sys.argv[1])
    if not os.path.isdir(input_dir):
        print(format_color(f"Errore: La cartella '{input_dir}' non esiste.", "31;1"))
        sys.exit(1)
        
    eb_path = find_energibridge()
    if not eb_path:
        print(format_color("Errore: EnergiBridge non trovato. Assicurarsi che sia installato in 'C:\\Program Files\\EnergiBridge\\energibridge.exe' o disponibile su PATH.", "31;1"))
        sys.exit(1)
        
    print(format_color(f"=== Avvio Profilatore Energetico JMH ===", "36;1"))
    print(f"Cartella sorgente JMH: {input_dir}")
    print(f"Path EnergiBridge: {eb_path}")
    print(format_color("Nota: Assicurarsi che i container Docker (webapp, mysql-db) siano attivi per evitare eccezioni di connessione JDBC.", "33"))
    print("-" * 50)
    
    # 1. Compile JMH suite if target/benchmarks.jar does not exist
    check_and_compile()
    
    # 2. Discover target benchmark java files
    java_files = [os.path.join(input_dir, f) for f in os.listdir(input_dir) if f.endswith("Benchmark.java")]
    if not java_files:
        print(format_color(f"Nessuna classe Benchmark trovata in '{input_dir}'", "33"))
        sys.exit(0)
        
    # Define directories relative to input folder
    eb_logs_base = os.path.join(input_dir, "energibridge_logs")
    jmh_logs_dir = os.path.join(input_dir, "jmh_logs")
    extractor_logs_dir = os.path.join(input_dir, "extractor_logs")
    
    os.makedirs(eb_logs_base, exist_ok=True)
    os.makedirs(jmh_logs_dir, exist_ok=True)
    os.makedirs(extractor_logs_dir, exist_ok=True)
    
    # Create subfolder in extractor_logs matching jmeter structure
    performance_unit_logs_dir = os.path.join(extractor_logs_dir, "performance_unit_testing_logs")
    os.makedirs(performance_unit_logs_dir, exist_ok=True)
    
    for jf in java_files:
        class_name = os.path.basename(jf).replace(".java", "")
        pkg = get_class_package(jf)
        if not pkg:
            print(format_color(f"Attenzione: Impossibile trovare il package dichiarazione in {jf}", "33"))
            continue
            
        fqn_class = f"{pkg}.{class_name}"
        print("\n" + "=" * 80)
        print(format_color(f"Elaborazione classe: {class_name} ({fqn_class})", "36;1"))
        print("=" * 80)
        
        # Determine benchmark methods for this class
        methods = get_benchmark_methods(fqn_class)
        if not methods:
            print(format_color(f"Nessun benchmark trovato per la classe {fqn_class}.", "33"))
            continue
            
        # Create subfolder for EnergiBridge logs under this class name
        class_eb_dir = os.path.join(eb_logs_base, class_name)
        os.makedirs(class_eb_dir, exist_ok=True)
        
        timestamp = time.strftime("%Y_%m_%d_%H_%M_%S")
        
        # A. Execute the whole class in JMH to save performance reports (JSON and text)
        json_report = os.path.join(jmh_logs_dir, f"log_{class_name}_{timestamp}.json")
        text_report = os.path.join(jmh_logs_dir, f"log_{class_name}_testing_output_{timestamp}.log")
        
        print(format_color(f"\nAvvio JMH per recuperare i tempi medi (f=1, wi=2, i=2)...", "32"))
        jmh_cmd = [
            "java", "-jar", "target/benchmarks.jar", fqn_class,
            "-f", "1", "-wi", "2", "-i", "2",
            "-rf", "json", "-rff", json_report,
            "-o", text_report
        ]
        subprocess.run(jmh_cmd, shell=False)
        
        # B. Run each method individually under EnergiBridge
        eb_results = {}
        for m_fqn in methods:
            method_simple_name = m_fqn.split(".")[-1]
            csv_path = os.path.join(class_eb_dir, f"{method_simple_name}.csv")
            
            print(format_color(f"\n[EnergiBridge] Esecuzione di: {method_simple_name}...", "35"))
            eb_cmd = [
                eb_path, "-o", csv_path, "--",
                "java", "-jar", "target/benchmarks.jar", m_fqn,
                "-f", "1", "-wi", "2", "-i", "2"
            ]
            res = subprocess.run(eb_cmd, shell=False)
            if res.returncode != 0:
                print(format_color(f"Attenzione: EnergiBridge non e riuscito a profilare '{method_simple_name}'. Verificare i permessi amministratore.", "31;1"))
                continue
                
            # Parse the generated CSV file
            stats = parse_eb_csv(csv_path)
            if stats:
                eb_results[method_simple_name] = stats
            else:
                print(format_color(f"Attenzione: Impossibile decodificare dati energetici validi da {csv_path}", "33"))
                
        # C. Merge time results from JSON and energy results from CSV to generate unified report
        jmh_scores = parse_jmh_json(json_report)
        
        if eb_results:
            print("\n" + "-" * 80)
            print(format_color(f"Generazione report consolidato per {class_name}...", "36"))
            print("-" * 80)
            
            report_lines = []
            report_lines.append("=== Analisi Energetica per Singolo Microbenchmark ===")
            report_lines.append(f"Elaborazione classe JMH: {class_name}")
            report_lines.append(f"File JMH JSON correlato: {json_report}")
            report_lines.append("=" * 175)
            
            tbl_header_fmt = "{:<45} | {:<20} | {:<14} | {:<13} | {:<15} | {:<12} | {:<12} | {:<12} | {:<12}"
            tbl_row_fmt = "{:<45} | {:<20} | {:<14.2f} | {:<13.2f} | {:<15.2f} | {:<12.2f} | {:<12.2f} | {:<12.2f} | {:<12.2f}"
            
            report_lines.append(tbl_header_fmt.format(
                "Microbenchmark", "Avg Time (ms/op)", "CPU Energy (J)", "Avg Power (W)", "Core Energy (J)", "Avg CPU (%)", "Peak CPU (%)", "Avg RAM (GB)", "Peak RAM (GB)"
            ))
            report_lines.append("-" * 175)
            
            for m_name, eb_stats in eb_results.items():
                score_val, score_unit = jmh_scores.get(m_name, (0.0, "ms/op"))
                score_str = f"{score_val:.4f}"
                
                report_lines.append(tbl_row_fmt.format(
                    m_name,
                    score_str,
                    eb_stats['cpu_energy_j'],
                    eb_stats['avg_power_w'],
                    eb_stats['core_energy_j'],
                    eb_stats['avg_cpu_usage_pct'],
                    eb_stats['peak_cpu_usage_pct'],
                    eb_stats['avg_ram_usage_gb'],
                    eb_stats['peak_ram_usage_gb']
                ))
            report_lines.append("=" * 175)
            report_lines.append("Analisi di unita completata con successo.")
            
            report_content = "\n".join(report_lines)
            
            # Print to stdout
            print(report_content)
            
            # Save report log in extractor_logs
            out_filename = f"log_{class_name}_extractor_{timestamp}.log"
            out_report_path1 = os.path.join(extractor_logs_dir, out_filename)
            out_report_path2 = os.path.join(performance_unit_logs_dir, out_filename)
            
            with open(out_report_path1, 'w', encoding='utf-8') as f:
                f.write(report_content)
            with open(out_report_path2, 'w', encoding='utf-8') as f:
                f.write(report_content)
                
            print(format_color(f"\nReport energetico per {class_name} salvato in: {out_report_path1}", "32"))
            print(format_color(f"Report energetico per {class_name} salvato in: {out_report_path2}", "32"))
        else:
            print(format_color(f"Nessun dato energetico profilato per la classe {class_name}.", "33"))

if __name__ == "__main__":
    main()
