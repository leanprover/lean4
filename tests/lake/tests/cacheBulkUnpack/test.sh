#!/usr/bin/env bash
source ../common.sh
./clean.sh
copy_to_work lakefile.toml src

export LAKE_CACHE_DIR="$PWD/cache"
export LAKE_CONFIG="$PWD/services.toml"
# Every artifact is already cached, so this test needs no server or network.
cat > services.toml <<'EOF'
[[cache.service]]
name = "local"
type = "s3"
artifactEndpoint = "http://127.0.0.1:1"
revisionEndpoint = "http://127.0.0.1:1"
EOF

# Duplicate basenames, Unicode module names, and custom source/output paths.
test_run build -o outputs.jsonl
test_cmd rm -rf out
restore() { "$LAKE" cache get outputs.jsonl --scope=test --service=local --unpack "$@"; }
test_cmd restore
test_exp -f out/lib/Foo/A/Basic.olean
test_exp -f out/lib/Foo/B/Basic.olean
test_exp -f out/lib/Foo/α.olean
test_exp -f out/lib/Foo/a.b.olean
test_exp -f out/ir/Foo/A/Basic.c
test_exp -f out/ir/Foo/A/Basic.ltar
test_not_out Unpacked build --no-build
# Re-publication reuses the original archives rather than packing new bundles.
test_not_out Packed build -o after.jsonl
sort outputs.jsonl > before.sorted
sort after.jsonl > after.sorted
test_cmd cmp before.sorted after.sorted

# Default configuration reads the shared cache without writing to it. Cleaning
# this checkout must not remove mappings needed here or in another checkout.
sed '/enableArtifactCache/d' lakefile.toml > read-only.toml
test_cmd rm -rf out
test_run -f read-only.toml cache get outputs.jsonl --scope=test --service=local --unpack
test_not_out Unpacked -f read-only.toml build --no-build
test_cmd rm -rf out
test_out Unpacked -f read-only.toml build --no-build

# Existing build directories are left alone.
test_out 'build directory already exists' -v cache get outputs.jsonl --scope=test --service=local --unpack

# An archive cannot make a deleted source importable.
test_cmd rm -rf out
mv src/Foo/B/Basic.lean deleted.lean
test_cmd restore
test_exp ! -f out/lib/Foo/B/Basic.olean
test_err 'bad import' build --no-build
mv deleted.lean src/Foo/B/Basic.lean

# Changed exported types must invalidate both the source and its importer.
test_cmd rm -rf out
echo 'def Foo.A.value : Int := 1' > src/Foo/A/Basic.lean
test_cmd restore
test_err 'needs to be rebuilt' build --no-build
test_err 'Type mismatch' build

# Overlapping historical entries fall back without installing any outputs.
test_run build Foo.A.Basic -o newer.jsonl
test_cmd rm -rf out
{ cat outputs.jsonl; tail -n +2 newer.jsonl; } > overlap.jsonl
test_out 'overlapping archives' -v cache get overlap.jsonl --scope=test --service=local --unpack
test_exp ! -e out

test_err '`--unpack` cannot be combined' cache get --unpack --mappings-only

# A failed batch extraction leaves the ordinary cache usable and installs nothing.
test_cmd rm -rf out
printf 'invalid archive' > cache/artifacts/0000000000000001.ltar
{ head -n 1 outputs.jsonl; echo '["1234567890abcdef","0000000000000001.ltar"]'; } > invalid.jsonl
test_out 'leantar exited' cache get invalid.jsonl --scope=test --service=local --unpack
test_exp ! -e out
