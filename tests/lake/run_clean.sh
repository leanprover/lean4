#!/usr/bin/env bash
set -euo pipefail

# Ensure this runs from the lake test directory
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

TEST_DIR="$1"; shift
cd "$TEST_DIR"
source clean.sh
