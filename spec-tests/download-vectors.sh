#!/usr/bin/env bash
set -euo pipefail

VERSION="v1.6.1"
BASE_URL="https://github.com/ethereum/consensus-specs/releases/download/${VERSION}"
DEST_DIR="${SPEC_TESTS_DIR:-$(dirname "$0")/../target/spec-tests/${VERSION}}"

download_and_extract() {
    local archive="$1"
    local dir_name="${archive%.tar.gz}"
    local dest="${DEST_DIR}/${dir_name}"
    local sentinel="${dest}/.extracted"

    if [ -f "$sentinel" ]; then
        echo "${archive}: already extracted at ${dest}"
        return
    fi

    echo "${archive}: downloading from ${BASE_URL}/${archive}..."
    mkdir -p "$dest"
    curl -sL "${BASE_URL}/${archive}" | tar xz -C "$dest"
    touch "$sentinel"
    echo "${archive}: extracted to ${dest}"
}

download_and_extract "general.tar.gz"
download_and_extract "mainnet.tar.gz"
download_and_extract "minimal.tar.gz"

echo "All spec test vectors ready at ${DEST_DIR}"
