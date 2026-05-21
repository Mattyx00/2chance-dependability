#!/usr/bin/env python3
import sys
import os
import csv

def format_color(text, color_code):
    """Formats text with ANSI escape codes for terminal color."""
    if sys.stdout.isatty():
        return f"\033[{color_code}m{text}\033[0m"
    return text

def analyze_csv(file_path):
    if not os.path.exists(file_path):
        print(format_color(f"Errore: Il file '{file_path}' non esiste.", "31;1"))
        return

    print(format_color(f"\n=== Analisi Energetica di EnergiBridge ===", "36;1"))
    print(f"Elaborazione file: {file_path}")
    print("=" * 45)

    with open(file_path, mode='r', encoding='utf-8') as f:
        reader = csv.reader(f)
        try:
            headers = next(reader)
        except StopIteration:
            print(format_color("Errore: Il file CSV e vuoto.", "31;1"))
            return

        headers = [h.strip() for h in headers]

        try:
            time_idx = headers.index("Time")
        except ValueError:
            time_idx = None
            print(format_color("Attenzione: Colonna 'Time' non trovata. Verra stimata tramite il numero di righe.", "33"))

        cpu_energy_idx = next((i for i, h in enumerate(headers) if "CPU_ENERGY" in h), None)
        core_energy_idx = next((i for i, h in enumerate(headers) if "CORE0_ENERGY" in h or "PPO_ENERGY" in h), None)

        cpu_usage_idxs = [i for i, h in enumerate(headers) if "CPU_USAGE_" in h]
        cpu_freq_idxs = [i for i, h in enumerate(headers) if "CPU_FREQUENCY_" in h]
        used_mem_idx = next((i for i, h in enumerate(headers) if "USED_MEMORY" in h), None)

        times = []
        cpu_energies = []
        core_energies = []
        row_cpu_usages = []
        row_cpu_freqs = []
        row_mem_usages = []

        row_count = 0
        for row_num, row in enumerate(reader, start=2):
            if not row:
                continue
            
            try:
                if time_idx is not None:
                    times.append(float(row[time_idx]))
                
                if cpu_energy_idx is not None:
                    cpu_energies.append(float(row[cpu_energy_idx]))
                
                if core_energy_idx is not None:
                    core_energies.append(float(row[core_energy_idx]))

                if cpu_usage_idxs:
                    usages = [float(row[idx]) for idx in cpu_usage_idxs if row[idx]]
                    if usages:
                        row_cpu_usages.append(sum(usages) / len(usages))

                if cpu_freq_idxs:
                    freqs = [float(row[idx]) for idx in cpu_freq_idxs if row[idx]]
                    if freqs:
                        row_cpu_freqs.append(sum(freqs) / len(freqs))

                if used_mem_idx is not None and row[used_mem_idx]:
                    mem_bytes = float(row[used_mem_idx])
                    row_mem_usages.append(mem_bytes / (1024.0 ** 3))

                row_count += 1
            except ValueError as e:
                continue

        if row_count == 0:
            print(format_color("Errore: Nessun dato valido trovato nel CSV.", "31;1"))
            return

        if time_idx is not None and len(times) > 1:
            duration_sec = (times[-1] - times[0]) / 1000.0
        else:
            duration_sec = row_count * 0.2

        if duration_sec <= 0:
            duration_sec = 0.001

        if cpu_energy_idx is not None and len(cpu_energies) > 1:
            total_cpu_energy = cpu_energies[-1] - cpu_energies[0]
            if total_cpu_energy < 0:
                total_cpu_energy = max(cpu_energies) - min(cpu_energies)
        else:
            total_cpu_energy = 0.0

        avg_cpu_power = total_cpu_energy / duration_sec

        if core_energy_idx is not None and len(core_energies) > 1:
            total_core_energy = core_energies[-1] - core_energies[0]
            if total_core_energy < 0:
                total_core_energy = max(core_energies) - min(core_energies)
        else:
            total_core_energy = 0.0

        if row_cpu_usages:
            avg_cpu_usage = sum(row_cpu_usages) / len(row_cpu_usages)
            peak_cpu_usage = max(row_cpu_usages)
        else:
            avg_cpu_usage = 0.0
            peak_cpu_usage = 0.0

        if row_cpu_freqs:
            avg_cpu_freq = sum(row_cpu_freqs) / len(row_cpu_freqs)
        else:
            avg_cpu_freq = 0.0

        if row_mem_usages:
            avg_mem_usage = sum(row_mem_usages) / len(row_mem_usages)
            peak_mem_usage = max(row_mem_usages)
        else:
            avg_mem_usage = 0.0
            peak_mem_usage = 0.0

        print(f"Durata Workload Profiled: {duration_sec:.2f} secondi (~{duration_sec/60.0:.2f} minuti)")
        print("-" * 45)

        header_fmt = "{:<30} | {:<12} | {:<8}"
        row_fmt = "{:<30} | " + format_color("{:<12}", "32;1") + " | {:<8}"
        
        print(format_color(header_fmt.format("Metrica di Sostenibilita", "Valore", "Unita"), "1"))
        print("-" * 56)
        
        print(row_fmt.format("Energia CPU Package", f"{total_cpu_energy:.2f}", "Joules (J)"))
        print(row_fmt.format("Potenza Media CPU Package", f"{avg_cpu_power:.2f}", "Watt (W)"))
        print(row_fmt.format("Energia PPO (Core)", f"{total_core_energy:.2f}", "Joules (J)"))
        print(row_fmt.format("CPU Usage (Media)", f"{avg_cpu_usage:.2f}", "Percentuale (%)"))
        print(row_fmt.format("CPU Usage (Picco)", f"{peak_cpu_usage:.2f}", "Percentuale (%)"))
        print(row_fmt.format("Frequenza Media CPU", f"{avg_cpu_freq:.2f}", "MHz"))
        print(row_fmt.format("Memoria RAM Usata (Media)", f"{avg_mem_usage:.2f}", "Gigabyte (GB)"))
        print(row_fmt.format("Memoria RAM Usata (Picco)", f"{peak_mem_usage:.2f}", "Gigabyte (GB)"))
        
        print("=" * 56)
        print(format_color("Analisi completata con successo.", "32"))

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(format_color("Utilizzo: python energibridge_metrics_extractor.py <percorso_file_csv>", "33"))
        sys.exit(1)
    
    csv_file = sys.argv[1]
    analyze_csv(csv_file)
