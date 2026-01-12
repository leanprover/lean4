#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test Lean to TOML translation
test_no_out translate-config -f source.lean toml out.produced.toml
test_cmd diff --strip-trailing-cr out.expected.toml out.produced.toml
test_cmd rm out.produced.toml

# Test idempotency of TOML translation
test_no_out translate-config -f out.expected.toml toml out.produced.toml
test_cmd diff --strip-trailing-cr out.expected.toml out.produced.toml

# Test TOML to Lean translation
test_no_out translate-config -f source.toml lean out.produced.lean
test_cmd diff --strip-trailing-cr out.expected.lean out.produced.lean
test_cmd rm out.produced.lean

# Test idempotency of Lean translation
test_no_out translate-config -f out.expected.lean lean out.produced.lean
test_cmd diff --strip-trailing-cr out.expected.lean out.produced.lean

# Test produced TOML round-trips
test_no_out translate-config -f out.produced.toml lean bridge.produced.lean
test_no_out translate-config -f bridge.produced.lean toml roundtrip.produced.toml
test_cmd diff --strip-trailing-cr out.produced.toml roundtrip.produced.toml

# Test produced Lean round-trips
test_no_out translate-config -f out.produced.lean toml bridge.produced.toml
test_no_out translate-config -f bridge.produced.toml lean roundtrip.produced.lean
test_cmd diff --strip-trailing-cr out.produced.lean roundtrip.produced.lean

# Test source rename
test_cmd cp source.lean lakefile.lean
test_no_out translate-config toml
test_exp -f lakefile.lean.bak
test_exp -f lakefile.toml

# Cleanup
rm -f produced.out
