#!/bin/bash
# Script per eseguire scansioni GitGuardian sul progetto 2chance-dependability
# Uso: ./security-scan.sh [opzione]

set -e

echo "🔍 GitGuardian Security Scanner"
echo "================================"
echo ""

# Funzione per scansionare file correnti
scan_current_files() {
    echo "📂 Scansionando file correnti (working directory)..."
    ggshield secret scan path . --recursive
}

# Funzione per scansionare ultimi commit
scan_recent_commits() {
    local num_commits=${1:-10}
    echo "📜 Scansionando ultimi $num_commits commit..."
    ggshield secret scan repo . --commit-range HEAD~$num_commits...HEAD
}

# Funzione per scansionare ultimo commit
scan_last_commit() {
    echo "📝 Scansionando ultimo commit..."
    ggshield secret scan commit HEAD
}

# Funzione per scansionare file staged (pre-commit)
scan_staged() {
    echo "📋 Scansionando file staged..."
    ggshield secret scan pre-commit
}

# Menu
case "${1:-current}" in
    current|files)
        scan_current_files
        ;;
    commits)
        scan_recent_commits "${2:-10}"
        ;;
    last)
        scan_last_commit
        ;;
    staged|pre-commit)
        scan_staged
        ;;
    help|--help|-h)
        echo "Uso: $0 [opzione] [parametri]"
        echo ""
        echo "Opzioni:"
        echo "  current, files     Scansiona file correnti (default)"
        echo "  commits [N]        Scansiona ultimi N commit (default: 10)"
        echo "  last               Scansiona solo ultimo commit"
        echo "  staged             Scansiona file staged per commit"
        echo "  help               Mostra questo messaggio"
        echo ""
        echo "Esempi:"
        echo "  $0                    # Scansiona file correnti"
        echo "  $0 current            # Scansiona file correnti"
        echo "  $0 commits 20         # Scansiona ultimi 20 commit"
        echo "  $0 last               # Scansiona ultimo commit"
        echo "  $0 staged             # Scansiona file staged"
        ;;
    *)
        echo "❌ Opzione non valida: $1"
        echo "Usa '$0 help' per vedere le opzioni disponibili"
        exit 1
        ;;
esac

echo ""
echo "✅ Scansione completata!"
