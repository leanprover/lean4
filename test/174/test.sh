#!/usr/bin/env bash
set -euxo pipefail

./clean.sh
LAKE=${LAKE:-../../build/bin/lake}
$LAKE build -v
