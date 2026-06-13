#!/usr/bin/env bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: write_config_stub.sh <include-dir>" >&2
  exit 1
fi

INCLUDE_DIR="$1"
LEAN_INCLUDE_DIR="$INCLUDE_DIR/lean"

mkdir -p "$LEAN_INCLUDE_DIR"

cat > "$LEAN_INCLUDE_DIR/config.h" <<'EOF'
#pragma once
#include <lean/version.h>

#define LEAN_IS_STAGE0 0
EOF
