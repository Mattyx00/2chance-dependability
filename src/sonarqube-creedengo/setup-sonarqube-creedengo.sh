#!/bin/bash
# Script to automate SonarQube and Creedengo plugin installation via Docker.
# Usage: ./setup-sonarqube-creedengo.sh [plugin_version]

set -e

PLUGIN_VERSION=${1:-"2.1.2"}
JAR_NAME="creedengo-java-plugin-${PLUGIN_VERSION}.jar"
JAR_PATH="plugin/${JAR_NAME}"
DOWNLOAD_URL="https://github.com/green-code-initiative/creedengo-java/releases/download/${PLUGIN_VERSION}/${JAR_NAME}"
CONTAINER_NAME="sonarqube-sse"

echo "Starting SonarQube + Creedengo Plugin Setup"
echo "==============================================="
echo "Plugin version: ${PLUGIN_VERSION}"
echo ""

# 1. Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "Error: docker command could not be found. Please install Docker."
    exit 1
fi

# 2. Check if jar is available locally, if not download it
if [ ! -f "$JAR_PATH" ]; then
    echo "Plugin jar not found locally at $JAR_PATH. Downloading from GitHub..."
    mkdir -p plugin
    if command -v curl &> /dev/null; then
        curl -L -o "$JAR_PATH" "$DOWNLOAD_URL"
    elif command -v wget &> /dev/null; then
        wget -O "$JAR_PATH" "$DOWNLOAD_URL"
    else
        echo "Error: Neither curl nor wget was found. Please download the JAR manually and place it in 'plugin/' directory."
        exit 1
    fi
    echo "Downloaded $JAR_NAME"
fi

# 3. Check if container already exists
if docker ps -a --format '{{.Names}}' | grep -Eq "^${CONTAINER_NAME}\$"; then
    echo "Container '${CONTAINER_NAME}' already exists. Stopping and removing it..."
    docker stop "$CONTAINER_NAME" || true
    docker rm "$CONTAINER_NAME" || true
fi

# 4. Spin up SonarQube Community Container
echo "Spinning up SonarQube container '${CONTAINER_NAME}'..."
docker run -d --name "$CONTAINER_NAME" -p 9000:9000 sonarqube:community

# 5. Wait for SonarQube directories to initialize (approx. 10-15 seconds before copy)
echo "Waiting for SonarQube to initialize (15s)..."
sleep 15

# 6. Copy Creedengo Plugin into the container
echo "Copying plugin jar into SonarQube extensions directory..."
docker cp "$JAR_PATH" "${CONTAINER_NAME}:/opt/sonarqube/extensions/plugins/"

# 7. Restart SonarQube to load the plugin
echo "Restarting SonarQube container to apply changes..."
docker restart "$CONTAINER_NAME"

echo ""
echo "SonarQube and Creedengo plugin setup completed successfully!"
echo "Access SonarQube at: http://localhost:9000 (Default credentials: admin/admin)"
