#!/usr/bin/env bash
set -euo pipefail

CONSENSUS_VERSION="v1.7.0-alpha.13"
CONSENSUS_BASE_URL="https://github.com/ethereum/consensus-specs/releases/download/${CONSENSUS_VERSION}"

SSZ_SPECS_VERSION="v0.1.0"
SSZ_SPECS_BASE_URL="https://github.com/ethereum/ssz-specs/releases/download/${SSZ_SPECS_VERSION}"

HERE="$(dirname "$0")"
CONSENSUS_DEST="${SPEC_TESTS_DIR:-${HERE}/../target/spec-tests/${CONSENSUS_VERSION}}"
SSZ_SPECS_DEST="${SSZ_SPECS_DIR:-${HERE}/../target/spec-tests/ssz-specs/${SSZ_SPECS_VERSION}}"

# Download `archive` from `base_url` into `dest`, skipping the work when the
# sentinel written by a previous run is already there.
download_and_extract() {
    local base_url="$1"
    local archive="$2"
    local dest="$3"
    local sentinel="${dest}/.extracted"

    if [ -f "$sentinel" ]; then
        echo "${archive}: already extracted at ${dest}"
        return
    fi

    echo "${archive}: downloading from ${base_url}/${archive}..."
    mkdir -p "$dest"
    curl -sL "${base_url}/${archive}" | tar xz -C "$dest"
    touch "$sentinel"
    echo "${archive}: extracted to ${dest}"
}

# consensus-specs: the ssz_generic and ssz_static suites (~1.25GB).
for archive in general mainnet minimal; do
    download_and_extract \
        "$CONSENSUS_BASE_URL" \
        "${archive}.tar.gz" \
        "${CONSENSUS_DEST}/${archive}"
done

# ssz-specs: the standalone SSZ suite covering EIP-7495/7916/8016 (~22KB).
download_and_extract \
    "$SSZ_SPECS_BASE_URL" \
    "ssz-test-vectors-${SSZ_SPECS_VERSION}.tar.gz" \
    "$SSZ_SPECS_DEST"

echo "Consensus spec test vectors ready at ${CONSENSUS_DEST}"
echo "ssz-specs test vectors ready at ${SSZ_SPECS_DEST}"
