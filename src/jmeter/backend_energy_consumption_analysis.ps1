param (
    [Parameter(Mandatory = $false)]
    [ValidateSet("load", "soak", "spike", "stepup")]
    [string]$Type
)

if (-not $Type) {
    Write-Host "Utilizzo dello script: inserire come parametro il tipo di test da lanciare." -ForegroundColor Yellow
    Write-Host "Esempio: .\backend_energy_consumption_analysis.ps1 -Type load" -ForegroundColor Yellow
    Write-Host ""
    Write-Host "I test disponibili sono:"
    Write-Host "  - load  : (Load Testing) Carico di picco controllato"
    Write-Host "  - soak  : (Soak Testing) Lungo periodo per scovare Memory Leak"
    Write-Host "  - spike : (Spike Testing) Ondata improvvisa di traffico"
    Write-Host "  - stepup: (Step-Up Testing) Stress test preventivo per trovare il Punto di Rottura C"
    exit
}

# Ensure log folders exist
$JmeterLogsDir = Join-Path $PSScriptRoot "jmeter_logs"
$EnergibridgeLogsDir = Join-Path $PSScriptRoot "energibridge_logs"
$ExtractorLogsDir = Join-Path $PSScriptRoot "extractor_logs"

if (-not (Test-Path $JmeterLogsDir)) {
    New-Item -ItemType Directory -Path $JmeterLogsDir -Force | Out-Null
}
if (-not (Test-Path $EnergibridgeLogsDir)) {
    New-Item -ItemType Directory -Path $EnergibridgeLogsDir -Force | Out-Null
}
if (-not (Test-Path $ExtractorLogsDir)) {
    New-Item -ItemType Directory -Path $ExtractorLogsDir -Force | Out-Null
}

# Navigate to project root to allow docker-compose commands to run from anywhere
$ProjectRoot = Split-Path (Split-Path $PSScriptRoot -Parent) -Parent
Push-Location $ProjectRoot

Write-Host "Resetting Docker environment..." -ForegroundColor Yellow
docker-compose down
docker-compose up -d
docker-compose restart webapp mysql-db
Write-Host "Waiting 10 seconds for the application to fully initialize..." -ForegroundColor Yellow
Start-Sleep -Seconds 10

$Timestamp = Get-Date -Format "yyyy_MM_dd_HH_mm_ss"

switch ($Type) {
    "load" {
        # 1. Esecuzione del LOAD TESTING (Carico di picco controllato)
        # Sintonizzato a 32 utenti concorrenti (Capacità Nominale C basata su test Step-Up con SLA latenza < 1200ms)
        $CsvPath = "$EnergibridgeLogsDir\log_load_energy_$Timestamp.csv"
        $JtlPath = "/tests/jmeter_logs/log_load_$Timestamp.jtl"
        $LogPath = "$JmeterLogsDir\log_load_testing_output_$Timestamp.log"
        $ExtractorLogPath = "$ExtractorLogsDir\log_load_extractor_$Timestamp.log"

        Write-Host "Avvio Load Testing tramite Docker con profilazione EnergiBridge..." -ForegroundColor Cyan
        & "C:\Program Files\EnergiBridge\energibridge.exe" -o "$CsvPath" -- docker-compose exec jmeter jmeter -n -t /tests/2chance_performance_system_testing.jmx -l "$JtlPath" -Jhost=webapp -Jcontext=/ -Jthreads=32 -Jrampup=32 -Jduration=600 | Tee-Object -FilePath "$LogPath"

        # Esecuzione dell'analisi energetica automatica
        Write-Host "Avvio dell'analisi energetica sul file generato..." -ForegroundColor Yellow
        python "$PSScriptRoot\energibridge_metrics_extractor.py" "$CsvPath" | Tee-Object -FilePath "$ExtractorLogPath"
    }
    "soak" {
        # 2. Esecuzione del SOAK TESTING (Lungo periodo per scovare Memory Leak)
        # Sintonizzato a 16 utenti costanti (50% di C) per 2 ore per valutare la stabilità della JVM e Garbage Collection
        $CsvPath = "$EnergibridgeLogsDir\log_soak_energy_$Timestamp.csv"
        $JtlPath = "/tests/jmeter_logs/log_soak_$Timestamp.jtl"
        $LogPath = "$JmeterLogsDir\log_soak_testing_output_$Timestamp.log"
        $ExtractorLogPath = "$ExtractorLogsDir\log_soak_extractor_$Timestamp.log"

        Write-Host "Avvio Soak Testing tramite Docker con profilazione EnergiBridge..." -ForegroundColor Cyan
        & "C:\Program Files\EnergiBridge\energibridge.exe" -o "$CsvPath" -- docker-compose exec jmeter jmeter -n -t /tests/2chance_performance_system_testing.jmx -l "$JtlPath" -Jhost=webapp -Jcontext=/ -Jthreads=16 -Jrampup=16 -Jduration=7200 | Tee-Object -FilePath "$LogPath"

        # Esecuzione dell'analisi energetica automatica
        Write-Host "Avvio dell'analisi energetica sul file generato..." -ForegroundColor Yellow
        python "$PSScriptRoot\energibridge_metrics_extractor.py" "$CsvPath" | Tee-Object -FilePath "$ExtractorLogPath"
    }
    "spike" {
        # 3. Esecuzione del SPIKE TESTING (Ondata improvvisa di traffico)
        # Sintonizzato a 48 utenti concorrenti (150% di C) creati in 5 secondi per verificare la reazione al sovraccarico
        $CsvPath = "$EnergibridgeLogsDir\log_spike_energy_$Timestamp.csv"
        $JtlPath = "/tests/jmeter_logs/log_spike_$Timestamp.jtl"
        $LogPath = "$JmeterLogsDir\log_spike_testing_output_$Timestamp.log"
        $ExtractorLogPath = "$ExtractorLogsDir\log_spike_extractor_$Timestamp.log"

        Write-Host "Avvio Spike Testing tramite Docker con profilazione EnergiBridge..." -ForegroundColor Cyan
        & "C:\Program Files\EnergiBridge\energibridge.exe" -o "$CsvPath" -- docker-compose exec jmeter jmeter -n -t /tests/2chance_performance_system_testing.jmx -l "$JtlPath" -Jhost=webapp -Jcontext=/ -Jthreads=48 -Jrampup=5 -Jduration=120 | Tee-Object -FilePath "$LogPath"

        # Esecuzione dell'analisi energetica automatica
        Write-Host "Avvio dell'analisi energetica sul file generato..." -ForegroundColor Yellow
        python "$PSScriptRoot\energibridge_metrics_extractor.py" "$CsvPath" | Tee-Object -FilePath "$ExtractorLogPath"
    }
    "stepup" {
        # 4. Esecuzione dello STEP-UP TESTING (Stress test preventivo per trovare il Punto di Rottura C)
        # Incrementa linearmente fino a 120 utenti concorrenti in 10 minuti per individuare la soglia di saturazione
        $CsvPath = "$EnergibridgeLogsDir\log_stepup_energy_$Timestamp.csv"
        $JtlPath = "/tests/jmeter_logs/log_stepup_$Timestamp.jtl"
        $LogPath = "$JmeterLogsDir\log_stepup_testing_analysis_$Timestamp.log"
        $ExtractorLogPath = "$ExtractorLogsDir\log_stepup_extractor_$Timestamp.log"

        Write-Host "Avvio Step-Up Stress Testing tramite Docker con profilazione EnergiBridge..." -ForegroundColor Cyan
        & "C:\Program Files\EnergiBridge\energibridge.exe" -o "$CsvPath" -- docker-compose exec jmeter jmeter -n -t /tests/2chance_performance_system_testing.jmx -l "$JtlPath" -Jhost=webapp -Jcontext=/ -Jthreads=120 -Jrampup=600 -Jduration=600 | Tee-Object -FilePath "$LogPath"

        # Esecuzione dell'analisi energetica automatica
        Write-Host "Avvio dell'analisi energetica sul file generato..." -ForegroundColor Yellow
        python "$PSScriptRoot\energibridge_metrics_extractor.py" "$CsvPath" | Tee-Object -FilePath "$ExtractorLogPath"
    }
}

Pop-Location
