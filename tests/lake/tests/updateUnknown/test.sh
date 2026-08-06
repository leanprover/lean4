#!/usr/bin/env bash
source ../common.sh
./clean.sh

# Test that `lake update <pkg>` errors on unknown package names (typos and
# case mismatches). Names that are current root requires or already in the
# manifest are accepted (so selective update can still drop a removed require).
# https://github.com/leanprover/lean4/issues/12005
# https://github.com/leanprover/lean4/issues/2772

# Completely unknown package name
test_err "unknown package \`does-not-exist\`" update does-not-exist

# Case mismatch (package names are case-sensitive)
test_err "unknown package \`Dep\`" update Dep

# Mix of valid and invalid: still errors before updating
test_err "unknown package \`missing\`" update dep missing

# Valid selective update and bare update still succeed
test_run update dep --keep-toolchain

# A package already in the manifest remains a valid selective target after its
# require is removed; the update then removes it from the manifest.
cp lakefile.toml lakefile.toml.bak
printf 'name = "test"\n' > lakefile.toml
test_run update dep --keep-toolchain
mv lakefile.toml.bak lakefile.toml

test_run update --keep-toolchain

# Cleanup
./clean.sh
