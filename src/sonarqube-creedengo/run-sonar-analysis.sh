#!/bin/bash
# Script to run SonarQube analysis for 2Chance with Creedengo
# Usage: ./run-sonar-analysis.sh [sonar_token]

set -e

# Resolve directories
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
TOKEN_FILE="${PROJECT_ROOT}/.sonarqube_token"

if [ -f "$TOKEN_FILE" ]; then
    SONAR_TOKEN=$(cat "$TOKEN_FILE" | tr -d '\r\n[:space:]')
    echo "Token loaded from $TOKEN_FILE"
elif [ -f ".sonarqube_token" ]; then
    SONAR_TOKEN=$(cat ".sonarqube_token" | tr -d '\r\n[:space:]')
    echo "Token loaded from local .sonarqube_token"
else
    echo "Error: No SonarQube token found."
    echo "Please create .sonarqube_token in the project root or provide a token as an argument."
    exit 1
fi

SONAR_HOST=${2:-"http://localhost:9000"}

echo "Running SonarQube Code Analysis..."
echo "====================================="
echo "SonarQube Host: ${SONAR_HOST}"
echo "Using Token: ${SONAR_TOKEN:0:10}..."
echo ""

# Run Maven SonarQube Scanner
mvn clean verify sonar:sonar \
  "-Dsonar.host.url=${SONAR_HOST}" \
  "-Dsonar.token=${SONAR_TOKEN}"

echo ""
echo "Analysis complete! Check the results on the dashboard:"
echo "${SONAR_HOST}/dashboard?id=groupId:2chance"
