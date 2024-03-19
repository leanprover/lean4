#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test Lean -> TOML translation
$LAKE translate-config -f lakefile.lean toml out.produced.toml
diff --strip-trailing-cr out.expected.toml out.produced.toml
rm out.produced.toml

# Test idempotency of TOML translation
$LAKE translate-config -f out.expected.toml toml out.produced.toml
diff --strip-trailing-cr out.expected.toml out.produced.toml
