#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test Lean to TOML translation
$LAKE translate-config -f source.lean toml out.produced.toml 2>&1 | diff - /dev/null
diff --strip-trailing-cr out.expected.toml out.produced.toml
rm out.produced.toml

# Test idempotency of TOML translation
$LAKE translate-config -f out.expected.toml toml out.produced.toml 2>&1 | diff - /dev/null
diff --strip-trailing-cr out.expected.toml out.produced.toml

# Test TOML to Lean translation
$LAKE translate-config -f source.toml lean out.produced.lean 2>&1 | diff - /dev/null
diff --strip-trailing-cr out.expected.lean out.produced.lean
rm out.produced.lean

# Test idempotency of Lean translation
$LAKE translate-config -f out.expected.lean lean out.produced.lean 2>&1 | diff - /dev/null
diff --strip-trailing-cr out.expected.lean out.produced.lean

# Test produced TOML round-trips
$LAKE translate-config -f out.produced.toml lean bridge.produced.lean 2>&1 | diff - /dev/null
$LAKE translate-config -f bridge.produced.lean toml roundtrip.produced.toml 2>&1 | diff - /dev/null
diff --strip-trailing-cr out.produced.toml roundtrip.produced.toml

# Test produced Lean round-trips
$LAKE translate-config -f out.produced.lean toml bridge.produced.toml 2>&1 | diff - /dev/null
$LAKE translate-config -f bridge.produced.toml lean roundtrip.produced.lean 2>&1 | diff - /dev/null
diff --strip-trailing-cr out.produced.lean roundtrip.produced.lean

# Test source rename
cp source.lean lakefile.lean
$LAKE translate-config toml | diff - /dev/null
test -f lakefile.lean.bak
test -f lakefile.toml
