#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test content-stable module archives via leantar -s (strip hash) and -j -
# (reinject). See https://github.com/leanprover/lean4/issues/13996.

# Hermetic, workspace-local artifact cache: an empty `LAKE_CACHE_DIR` disables the
# system cache, so all artifacts and mappings live under `.lake/cache`. The package
# enables the artifact cache and `restoreAllArtifacts` (see lakefile.toml).
export LAKE_CACHE_DIR=

# Create a Git-ignored `Test/A.lean` to edit later
cat > Test/A.lean << 'EOF'
module
public def a : Nat := 1
EOF

# The set of bundle (`.ltar`) content hashes referenced by a mapping file.
bundles() { grep -oE '[0-9a-f]{16}\.ltar' "$1" | sort -u; }

# A build populates the cache and emits a mapping referencing bundles.
test_run build -o .lake/out1.jsonl
test_cmd ls .lake/cache/artifacts/*.ltar
bundles .lake/out1.jsonl > .lake/bundles1.txt
test_exp -s .lake/bundles1.txt

# An input-only edit (comment appended) changes the input hash but no output, so
# the bundle hashes are unchanged even though the mapping entry moves.
printf '\n-- a cosmetic comment; does not change any output\n' >> Test/A.lean
test_run build -o .lake/out2.jsonl
bundles .lake/out2.jsonl > .lake/bundles2.txt
test_cmd diff .lake/bundles1.txt .lake/bundles2.txt
test_cmd_fails diff .lake/out1.jsonl .lake/out2.jsonl

# Consume a bundle-only cache: fetch, unpack with hash reinjection, verify.
test_run cache stage .lake/out2.jsonl .lake/staging
test_cmd ls .lake/staging/*.ltar
rm -rf .lake/cache .lake/build
test_run cache unstage .lake/staging
test_cmd_fails ls .lake/cache/artifacts/*.olean   # no individual artifacts present
test_out "leantar" build -v                       # bundles are unpacked
test_run build --no-build --rehash                # outputs verify as up-to-date
# The unpacked trace carries the input hash leantar reinjected from `-j -`, so it
# matches the mapping key the archive was fetched under.
if command -v jq > /dev/null; then # skip if no jq found
  dep=$(jq -r '.depHash' .lake/build/lib/lean/Test/A.trace)
  match_text "$dep" .lake/staging/outputs.jsonl
fi

# Cleanup
rm -f produced.out
