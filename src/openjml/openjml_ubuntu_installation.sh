#!/usr/bin/env bash
set -euo pipefail

echo "==> OpenJML installer per Ubuntu (utilizzabile anche in Docker)"
echo "==> Installa le dipendenze necessarie (wget, unzip, ca-certificates, z3, openjdk-17-jdk-headless)"
echo "==> Scarica ed installa OpenJML per Ubuntu 22.04 (versione 21-0.18)"
echo "==> Configura Z3 esterno in /usr/bin/z3 come prover predefinito per OpenJML"
echo "==> Espone il comando 'openjml' nel PATH tramite wrapper in /usr/local/bin/openjml"

OPENJML_VERSION="21-0.18"
OPENJML_DISTRO="ubuntu-22.04"
OPENJML_ZIP="openjml-${OPENJML_DISTRO}-${OPENJML_VERSION}.zip"
OPENJML_URL="https://github.com/OpenJML/OpenJML/releases/download/${OPENJML_VERSION}/${OPENJML_ZIP}"

INSTALLATION_DIRECTORY="/opt/openjml"
OPENJML_PROPERTIES="${INSTALLATION_DIRECTORY}/openjml.properties"
OPENJML_PROPERTIES_TEMPLATE="${INSTALLATION_DIRECTORY}/openjml.properties-template"

echo "==> Aggiorno apt e installo dipendenze di base..."
apt-get update -y
apt-get install -y --no-install-recommends wget
apt-get install -y --no-install-recommends unzip
apt-get install -y --no-install-recommends ca-certificates
apt-get install -y --no-install-recommends z3
apt-get install -y --no-install-recommends openjdk-17-jdk-headless

rm -rf /var/lib/apt/lists/*

echo "==> Creo la cartella di installazione: ${INSTALLATION_DIRECTORY}"
mkdir -p "${INSTALLATION_DIRECTORY}"

echo "==> Scarico OpenJML da ${OPENJML_URL}"
wget -O "/tmp/${OPENJML_ZIP}" "${OPENJML_URL}"

echo "==> Estraggo OpenJML in ${INSTALLATION_DIRECTORY}"
unzip "/tmp/${OPENJML_ZIP}" -d "${INSTALLATION_DIRECTORY}"
rm "/tmp/${OPENJML_ZIP}"

echo "==> Rendo eseguibili gli script e i solver"
chmod +x "${INSTALLATION_DIRECTORY}/openjml" || true
chmod +x "${INSTALLATION_DIRECTORY}/openjml-compile" || true
chmod +x "${INSTALLATION_DIRECTORY}/openjml-java" || true
chmod +x "${INSTALLATION_DIRECTORY}/openjml-run" || true
if [ -d "${INSTALLATION_DIRECTORY}/Solvers-linux" ]; then
    chmod +x "${INSTALLATION_DIRECTORY}/Solvers-linux/"*
fi

echo "==> Creo openjml.properties per usare /usr/bin/z3"
if [ -f "${OPENJML_PROPERTIES_TEMPLATE}" ]; then
    cp "${OPENJML_PROPERTIES_TEMPLATE}" "${OPENJML_PROPERTIES}"
else
    echo "" > "${OPENJML_PROPERTIES}"
fi

cat >> "${OPENJML_PROPERTIES}" <<'EOF'
org.openjml.prover.z3_4_3=/usr/bin/z3
org.openjml.defaultProver=z3_4_3
openjml.prover.z3_4_3=/usr/bin/z3
openjml.defaultProver=z3_4_3
EOF

echo "==> Creo wrapper /usr/local/bin/openjml"
cat > /usr/local/bin/openjml <<EOF
#!/usr/bin/env bash
exec "${INSTALLATION_DIRECTORY}/openjml" -properties "${OPENJML_PROPERTIES}" "\$@"
EOF

chmod +x /usr/local/bin/openjml

echo "==> Test rapido: openjml --version"
openjml --version || { echo "Errore: openjml --version è fallito"; exit 1; }

echo "==> Installazione OpenJML completata con successo."
