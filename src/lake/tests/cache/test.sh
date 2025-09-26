#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the functionality of the Lake artifact cache

# Store Lake cache in a local directory
TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$TEST_DIR/.lake/cache"
export LAKE_CACHE_DIR="$CACHE_DIR"

# Verify packages without `enableArtifactCache` do not use the cache by default
test_run build -f unset.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify they also do not if `LAKE_ARTIFACT_CACHE` is set to `false`
LAKE_ARTIFACT_CACHE=false test_run build -f unset.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify packages with `enableArtifactCache` set to `false``
# also do not if `LAKE_ARTIFACT_CACHE` is set to `true`
LAKE_ARTIFACT_CACHE=true test_run build -f disabled.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify that packages without `enableArtifactCache` and
# `LAKE_ARTIFACT_CACHE` is set to `true` do use the cache
LAKE_ARTIFACT_CACHE=true test_run build -f unset.toml Test:static
test_exp -d "$CACHE_DIR"
./clean.sh

# Ensure a build runs properly with some artifacts cached
test_run build Test:static
test_run build Test:static --no-build --wfail

# Test replay of a cached build
test_out 'Replayed Test:c.o' build +Test:o -v

# Verify that a rebuild with the cache disabled is a no-op
touch .lake/build/ir/Test.c # avoid mod time fallback if trace is missing
test_run -f disabled.toml build +Test:o --no-build --wfail
test_run -f disabled.toml build Test:static --no-build --wfail

# Verify the cache directory structure was created
test_exp -d "$CACHE_DIR"
test_exp -d "$CACHE_DIR/outputs"
test_exp -d "$CACHE_DIR/artifacts"

# Copy the basic mappings for later
test_cmd cp -r "$CACHE_DIR/outputs" .lake/backup-outputs

# Checked that the cached artifact is in the expected location
# and equivalent to the standard artifact
local_art="$($LAKE -f disabled.toml query +Test:o)"
cache_art="$($LAKE query +Test:o)"
test_exp "$(norm_dirname "$cache_art")" = "$CACHE_DIR/artifacts"
test_exp "$cache_art" != "$local_art"
test_cmd cmp -s "$cache_art" "$local_art"

# Verify supported artifacts end up in the cache directory
test_run build \
  test:exe Test:static Test:shared +Test:o.export +Test:o.noexport +Module
test_cached() {
  target="$1"; shift
  art="$($LAKE query $target)"
  echo "${1:-?} artifact cached: $target -> $art"
  test ${1:-} "$(norm_dirname "$art")" = "$CACHE_DIR/artifacts"
}
test_cached test:exe !
test_cached Test:static !
test_cached Test:shared !
test_cached +Test:o.export
test_cached +Test:o.noexport
test_cached +Test:dynlib !
test_cached +Test:olean
test_cached +Test:ilean !
test_cached +Test:c
test_cached +Module:olean
test_cached +Module:olean.server
test_cached +Module:olean.private
test_cached +Module:ir

# Verify no `.hash` files end up in the cache directory
check_diff /dev/null <(ls -1 "$CACHE_DIR/*.hash" 2>/dev/null)

# Verify that the executable has the right permissions to be run
test_run exe test

# Verify that fetching from the cache creates a trace file that does not replay
touch Ignored.lean
test_out "Fetched Ignored" -v build +Ignored
test_exp -f .lake/build/lib/lean/Ignored.trace
test_out "Fetched Ignored" -v build +Ignored

# Verify that modifications invalidate the cache
echo "def foo := ()" > Ignored.lean
test_out "Built Ignored" -v build +Ignored

# Verify module ileans are restored from the cache
test_run build +Test --no-build
test_cmd rm .lake/build/lib/lean/Test.ilean
test_out "restored artifact from cache" -v build +Test --no-build
test_exp -f .lake/build/lib/lean/Test.ilean

# Verify that things work properly if the cached artifact is removed
test_cmd rm "$cache_art"
test_out "⚠ [4/4] Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached
test_cmd rm -r "$CACHE_DIR/outputs"
test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached

# Verify that upstream cache mappings are restored
test_out "Replayed Test:c.o" build Test:static -v --no-build
check_diff <(ls .lake/backup-outputs) <(ls "$CACHE_DIR/outputs")

# Verify that things work properly if the local artifact is removed
test_cmd rm "$local_art"
test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_cmd rm "$local_art.trace"
test_out "Fetched Test:c.o" build +Test:o -v --no-build

# Verify that if the input cache is missing,
# the cached artifact is still used via the output hash in the trace
test_cmd rm -r "$CACHE_DIR/outputs" .lake/build/ir/Test.c
test_run -v build +Test:c --no-build

# Verify that the olean does need to be present in the build directory
test_cmd rm .lake/build/lib/lean/Test.olean .lake/build/lib/lean/Test/Imported.olean
test_run -v build +Test.Imported --no-build --wfail
test_run -v build +Test

# Test producing an output mappings file
test_run build Test -o .lake/outputs.jsonl
test_exp -f .lake/outputs.jsonl
test_cmd_eq 3 wc -l < .lake/outputs.jsonl
test_run build Test:static -o .lake/outputs.jsonl
test_cmd_eq 6 wc -l < .lake/outputs.jsonl

# Verify all artifacts end up in the cache directory with `restoreAllArtifacts`
test_cmd cp -r "$CACHE_DIR" .lake/cache-backup
test_cmd rm -rf "$CACHE_DIR"
test_run build -R -KrestoreAll=true \
  test:exe Test:static Test:shared +Test:o.export +Test:o.noexport +Module
test_cached test:exe !
test_cached Test:static !
test_cached Test:shared !
test_cached +Test:o.export !
test_cached +Test:o.noexport !
test_cached +Test:dynlib !
test_cached +Test:olean !
test_cached +Test:ilean !
test_cached +Test:c !
test_cached +Module:olean !
test_cached +Module:olean.server !
test_cached +Module:olean.private !
test_cached +Module:ir !

# Cleanup
rm -f produced.out Ignored.lean
