#!/usr/bin/env bash
set -euo pipefail
LAKE=${LAKE:-../../.lake/build/bin/lake}
$LAKE -d ../.. build Lake.Toml
$LAKE env lean --run Test.lean
