#!/bin/bash

# Color codes
GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Check if URL path is provided
if [ -z "$1" ]; then
    echo -e "${RED}Error: No URL path provided.${NC}"
    echo "Usage: $0 <url_path>"
    echo "Example: $0 /index.jsp"
    exit 1
fi

URL_PATH="$1"

# Ensure URL path starts with a slash
if [[ ! "$URL_PATH" =~ ^/ ]]; then
    URL_PATH="/${URL_PATH}"
fi

echo -e "${BLUE}Starting EcoIndex analysis for:${NC} http://host.docker.internal:8080${URL_PATH}"

# Run ecoindex-cli via Docker
# --add-host=host.docker.internal:host-gateway is added to support host.docker.internal on Linux hosts
docker run --rm -t \
    --add-host=host.docker.internal:host-gateway \
    cnumr/ecoindex-cli analyze \
    --url "http://host.docker.internal:8080${URL_PATH}"

if [ $? -eq 0 ]; then
    echo -e "${GREEN}EcoIndex analysis completed successfully.${NC}"
else
    echo -e "${RED}EcoIndex analysis failed.${NC}"
    exit 1
fi
