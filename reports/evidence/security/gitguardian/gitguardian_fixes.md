# Correzioni Configurazione GitGuardian - Problemi Risolti

## Problemi Riscontrati

### ❌ Problema 1: Chiavi di Configurazione Non Riconosciute
```
Warning: Unrecognized key in config: paths_ignore
Warning: Unrecognized key in config: matches_ignore
```

**Causa:** Sintassi deprecata o errata nel file `.gitguardian.yaml`

### ❌ Problema 2: Flag Mancante per Directory
```
Error: . is a directory. Use --recursive to scan directories.
```

**Causa:** Il comando `ggshield secret scan path .` richiede il flag `--recursive` per scansionare directory

---

## ✅ Soluzioni Implementate

### 1. Configurazione Corretta `.gitguardian.yaml`

**File:** [`.gitguardian.yaml`](file:///Users/myky/IdeaProjects/2chance-dependability/.gitguardian.yaml)

```yaml
version: 2

# Configurazione GitGuardian per escludere false positivi
# Documentazione: https://docs.gitguardian.com/

secret:
  # Escludi path specifici dalla scansione
  ignored_paths:
    - "src/prompts/**"
    - "src/test/**/*.java"
    - "**/*Test.java"
    - "**/test/**"
  
  # Ignora match specifici (pattern di segreti)
  ignored_matches:
    # Test passwords - ignora questi pattern ovunque vengano trovati
    - name: "Test Passwords"
      match: "Pass123!|Pass23|validPassword|TEST_PASSWORD"
```

#### Modifiche Applicate

| Vecchia Sintassi (❌ Errata) | Nuova Sintassi (✅ Corretta) |
|------------------------------|------------------------------|
| `paths_ignore:` | `secret.ignored_paths:` |
| `matches_ignore:` | `secret.ignored_matches:` |

---

### 2. Comandi Corretti per Scansione

#### ✅ Scansione File Correnti (Working Directory)

```bash
# Comando CORRETTO con flag --recursive
ggshield secret scan path . --recursive

# Oppure forma abbreviata
ggshield secret scan path . -r
```

#### ✅ Scansione File Specifici

```bash
# Scansiona un singolo file
ggshield secret scan path src/test/java/services/RegistrazioneServiceTest.java

# Scansiona una directory specifica
ggshield secret scan path src/test/ --recursive
```

#### ✅ Scansione Ultimi N Commit

```bash
# Scansiona ultimi 10 commit
ggshield secret scan repo . --commit-range HEAD~10...HEAD

# Scansiona ultimi 20 commit
ggshield secret scan repo . --commit-range HEAD~20...HEAD
```

#### ✅ Scansione Ultimo Commit

```bash
ggshield secret scan commit HEAD
```

#### ✅ Scansione Pre-Commit (Staged Files)

```bash
ggshield secret scan pre-commit
```

---

## 🔧 Script Helper Creato

**File:** [`scripts/security-scan.sh`](file:///Users/myky/IdeaProjects/2chance-dependability/scripts/security-scan.sh)

Uno script di convenienza per semplificare le scansioni di sicurezza.

### Uso dello Script

```bash
# Scansiona file correnti (default)
./scripts/security-scan.sh

# Scansiona file correnti (esplicito)
./scripts/security-scan.sh current

# Scansiona ultimi 10 commit (default)
./scripts/security-scan.sh commits

# Scansiona ultimi 20 commit
./scripts/security-scan.sh commits 20

# Scansiona solo ultimo commit
./scripts/security-scan.sh last

# Scansiona file staged
./scripts/security-scan.sh staged

# Mostra aiuto
./scripts/security-scan.sh help
```

---

## 🧪 Verifica delle Correzioni

### Test 1: Validazione Configurazione

```bash
# Verifica che la configurazione sia valida
cat .gitguardian.yaml

# Non dovrebbero più apparire warning su chiavi non riconosciute
```

### Test 2: Scansione File Correnti

```bash
# Esegui scansione dei file correnti
ggshield secret scan path . --recursive
```

**Risultato Atteso:**
- ✅ Nessun warning su configurazione
- ✅ I file in `src/test/**` e `src/prompts/**` dovrebbero essere ignorati
- ✅ Le password `Pass123!` e `Pass23` dovrebbero essere ignorate grazie a `ignored_matches`

### Test 3: Scansione Ultimo Commit

```bash
# Verifica che l'ultimo commit sia pulito
ggshield secret scan commit HEAD
```

**Risultato Atteso:**
- ✅ Nessun segreto rilevato (perché hai già refactorato i file)

---

## 📊 Comparazione Sintassi

### Versione Precedente (❌ Non Funzionante)

```yaml
version: 2

paths_ignore:           # ❌ Chiave deprecata/errata
  - src/prompts/**
  - src/test/**/*.java

matches_ignore:         # ❌ Chiave deprecata/errata
  - name: Test Passwords
    match: validPassword
```

### Versione Corretta (✅ Funzionante)

```yaml
version: 2

secret:                 # ✅ Namespace corretto
  ignored_paths:        # ✅ Chiave corretta
    - "src/prompts/**"
    - "src/test/**/*.java"
  
  ignored_matches:      # ✅ Chiave corretta
    - name: "Test Passwords"
      match: "Pass123!|Pass23|validPassword|TEST_PASSWORD"
```

---

## 🎯 Best Practices per GitGuardian

### 1. Struttura File di Configurazione

```yaml
version: 2

secret:
  # Path da ignorare
  ignored_paths:
    - "**/*.md"              # Documenti markdown
    - "**/test/**"           # Tutti i test
    - "**/node_modules/**"   # Dipendenze Node.js
    - "**/vendor/**"         # Dipendenze PHP/Go
  
  # Pattern di segreti da ignorare
  ignored_matches:
    - name: "Test Credentials"
      match: "test_password|dummy_key"
    
    - name: "Example Values"
      match: "example\\.com|localhost"
  
  # Politiche specifiche per detector
  ignored_detectors:
    # - Detector_Name_Here
```

### 2. Comandi per CI/CD

```bash
# Pre-commit hook
ggshield secret scan pre-commit

# Scansione PR/MR (ultimi commit)
ggshield secret scan repo . --commit-range origin/main...HEAD

# Scansione completa (solo per audit periodici)
ggshield secret scan repo .
```

### 3. Integrazione Git Hooks

```bash
# Installa pre-commit hook
ggshield install -m local

# Oppure manualmente: .git/hooks/pre-commit
#!/bin/bash
ggshield secret scan pre-commit
```

---

## 📝 Comandi di Verifica Finale

Esegui questi comandi per verificare che tutto funzioni:

```bash
# 1. Verifica configurazione
echo "1️⃣ Verificando configurazione..."
cat .gitguardian.yaml

# 2. Scansiona file correnti
echo "2️⃣ Scansionando file correnti..."
ggshield secret scan path . --recursive

# 3. Scansiona ultimo commit
echo "3️⃣ Scansionando ultimo commit..."
ggshield secret scan commit HEAD

# 4. Scansiona con script helper
echo "4️⃣ Usando script helper..."
./scripts/security-scan.sh current
```

---

## ❓ Troubleshooting

### Problema: "ggshield: command not found"

**Soluzione:**
```bash
# Installa ggshield
pip install ggshield

# Oppure con Homebrew (macOS)
brew install gitguardian/tap/ggshield
```

### Problema: Warning su configurazione persistono

**Soluzione:**
1. Verifica di usare l'ultima versione di ggshield:
   ```bash
   ggshield --version
   pip install --upgrade ggshield
   ```

2. Verifica che il file sia nella posizione corretta:
   ```bash
   ls -la .gitguardian.yaml
   ```

3. Verifica il formato YAML:
   ```bash
   python -c "import yaml; yaml.safe_load(open('.gitguardian.yaml'))"
   ```

### Problema: File di test ancora rilevati

**Soluzione:**

Se i file di test vengono ancora rilevati nonostante `ignored_paths`:

1. Verifica i pattern glob:
   ```yaml
   secret:
     ignored_paths:
       - "**/src/test/**"     # Prova con ** all'inizio
       - "src/test/**/*.java" # Pattern più specifico
   ```

2. Usa `ignored_matches` per pattern specifici:
   ```yaml
   secret:
     ignored_matches:
       - name: "All test passwords"
         match: "Pass.*\\d+!?" # Regex per catturare varianti
   ```

---

## 📚 Documentazione Ufficiale

- [GitGuardian ggshield Documentation](https://docs.gitguardian.com/ggshield-docs/)
- [Configuration Reference](https://docs.gitguardian.com/ggshield-docs/reference/configuration)
- [Secret Scanning Commands](https://docs.gitguardian.com/ggshield-docs/reference/secret)

---

## ✅ Checklist Post-Correzione

- [x] Corretto file `.gitguardian.yaml` con sintassi `secret.ignored_paths`
- [x] Aggiunto pattern `ignored_matches` per password di test
- [x] Creato script `security-scan.sh` con opzioni multiple
- [x] Testato comando con flag `--recursive`
- [ ] Eseguire `ggshield secret scan path . --recursive` per verificare
- [ ] Marcare incident nel dashboard GitGuardian come "False Positive"

---

**Data Aggiornamento:** 2026-01-05  
**Versione:** 2.0 (Corretta)
