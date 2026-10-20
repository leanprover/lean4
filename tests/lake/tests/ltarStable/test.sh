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

# Output tracking in a later invocation must reuse the restored bundles rather
# than repack them, reproducing the mapping the archives were fetched under.
test_not_out "leantar" build --no-build -v -o .lake/plain-restored.jsonl
sort .lake/out2.jsonl > .lake/expected.jsonl
sort .lake/plain-restored.jsonl > .lake/actual.jsonl
test_cmd diff .lake/expected.jsonl .lake/actual.jsonl

# An archive-only cache must preserve its bundles, including when the cache is
# read-only. Neither immediate nor subsequent output tracking should repack them.
for config in lakefile.toml readonly.toml; do
  rm -rf .lake/cache .lake/build
  test_run cache unstage .lake/staging
  test_out "leantar" -f "$config" build --no-build -v -o .lake/restored.jsonl
  no_match_text "leantar -s" produced.out
  for module in Test Test/A Test/B; do
    test_exp -f ".lake/build/ir/$module.ltar"
  done
  test_not_out "leantar" -f "$config" build --no-build -v -o .lake/reused.jsonl
  sort .lake/out2.jsonl > .lake/expected.jsonl
  sort .lake/restored.jsonl > .lake/actual.jsonl
  test_cmd diff .lake/expected.jsonl .lake/actual.jsonl
  sort .lake/reused.jsonl > .lake/actual.jsonl
  test_cmd diff .lake/expected.jsonl .lake/actual.jsonl
done

# Preserving an archive must not retain stale outputs after its source changes.
printf '\npublic def changed : Nat := 2\n' >> Test/A.lean
test_out "Built Test.A" build -v -o .lake/changed.jsonl
bundles .lake/changed.jsonl > .lake/changed-bundles.txt
test_cmd_fails diff .lake/bundles2.txt .lake/changed-bundles.txt
test_not_out "leantar" build --no-build -v -o .lake/changed-reused.jsonl
sort .lake/changed.jsonl > .lake/expected.jsonl
sort .lake/changed-reused.jsonl > .lake/actual.jsonl
test_cmd diff .lake/expected.jsonl .lake/actual.jsonl

# Cleanup
rm -f produced.out
