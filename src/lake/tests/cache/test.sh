#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the functionality of the Lake artifact cache

TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$TEST_DIR/.lake/cache"

# Verify packages without `enableArtifactCache` do not use the cache by default
LAKE_CACHE_DIR="$CACHE_DIR" test_run build -f unset.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify they also do not if `LAKE_ARTIFACT_CACHE` is set to `false`
LAKE_CACHE_DIR="$CACHE_DIR" LAKE_ARTIFACT_CACHE=false \
  test_run build -f unset.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify packages with `enableArtifactCache` set to `false``
# also do not if `LAKE_ARTIFACT_CACHE` is set to `true`
LAKE_CACHE_DIR="$CACHE_DIR" LAKE_ARTIFACT_CACHE=true \
  test_run build -f disabled.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify that packages without `enableArtifactCache` and
# `LAKE_ARTIFACT_CACHE` is set to `true` do use the cache
LAKE_CACHE_DIR="$CACHE_DIR" LAKE_ARTIFACT_CACHE=true \
  test_run build -f unset.toml Test:static
test_exp -d "$CACHE_DIR"
./clean.sh

# Ensure a build runs properly with some artifacts cached
LAKE_CACHE_DIR="$CACHE_DIR" test_run build Test:static
LAKE_CACHE_DIR="$CACHE_DIR" test_run build Test:static --no-build --wfail

# Test replay of a cached build
LAKE_CACHE_DIR="$CACHE_DIR" test_out 'Replayed Test:c.o' build +Test:o -v

# Verify that a rebuild with the cache disabled is a no-op
touch .lake/build/ir/Test.c # avoid mod time fallback if trace is missing
LAKE_CACHE_DIR= test_run build +Test:o --no-build --wfail
LAKE_CACHE_DIR= test_run build Test:static --no-build --wfail

# Verify the cache directory structure was created
test_exp -d "$CACHE_DIR"
test_exp -d "$CACHE_DIR/inputs"
test_exp -s "$CACHE_DIR/inputs/test.jsonl"
test_exp -d "$CACHE_DIR/artifacts"

# Copy the basic inputs for later
cp "$CACHE_DIR/inputs/test.jsonl" .lake/backup-inputs.json

# Checked that the cached artifact is in the expected location
# and equivalent to the standard artifact
local_art="$(LAKE_CACHE_DIR= $LAKE query +Test:o)"
cache_art="$(LAKE_CACHE_DIR="$CACHE_DIR" $LAKE query +Test:o)"
test_exp "$(dirname -- "$cache_art")" = "$CACHE_DIR/artifacts"
test_exp "$cache_art" != "$local_art"
test_cmd cmp -s "$cache_art" "$local_art"

# Verify supported artifacts end up in the cache directory
LAKE_CACHE_DIR="$CACHE_DIR" test_run build test:exe Test:static Test:shared +Test:o.export +Test:o.noexport
test_cached() {
  target="$1"; shift
  art="$(LAKE_CACHE_DIR="$CACHE_DIR" $LAKE query $target)"
  echo "${1:-?} artifact cached: $target -> $art"
  test ${1:-} "$(dirname -- "$art")" = "$CACHE_DIR/artifacts"
}
test_cached test:exe
test_cached Test:static
test_cached Test:shared !
test_cached +Test:o.export
test_cached +Test:o.noexport
test_cached +Test:dynlib !
test_cached +Test:olean
test_cached +Test:ilean !
test_cached +Test:c

# Verify no `.hash` files end up in the cache directory
check_diff /dev/null <(ls -1 "$CACHE_DIR/*.hash" 2>/dev/null)

# Verify that the executable has the right permissions to be run
LAKE_CACHE_DIR="$CACHE_DIR" test_run exe test

# Verify that fetching from the cache creates a trace file that does not replay
touch Ignored.lean
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Fetched Ignored" -v build +Ignored
test_exp -f .lake/build/lib/lean/Ignored.trace
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Fetched Ignored" -v build +Ignored

# Verify that modifications invalidate the cache
echo "def foo := ()" > Ignored.lean
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Built Ignored" -v build +Ignored

# Verify module ileans are restored from the cache
LAKE_CACHE_DIR="$CACHE_DIR" test_run build +Test --no-build
test_cmd rm .lake/build/lib/lean/Test.ilean
LAKE_CACHE_DIR="$CACHE_DIR" test_out "restored artifact from cache" -v build +Test --no-build
test_exp -f .lake/build/lib/lean/Test.ilean

# Verify that things work properly if the cached artifact is removed
test_cmd rm "$cache_art"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "⚠ [4/4] Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached
test_cmd rm "$CACHE_DIR/inputs/test.jsonl"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached

# Verify that the upstream input graph is restored
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Replayed Test:c.o" build Test:static -v --no-build
check_diff .lake/backup-inputs.json "$CACHE_DIR/inputs/test.jsonl"

# Verify that things work properly if the local artifact is removed
test_cmd rm "$local_art"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_cmd rm "$local_art.trace"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Fetched Test:c.o" build +Test:o -v --no-build

# Verify that if the input cache is missing,
# the cached artifact is still used via the output hash in the trace
test_cmd rm "$CACHE_DIR/inputs/test.jsonl" .lake/build/ir/Test.c
LAKE_CACHE_DIR="$CACHE_DIR" test_run -v build +Test:c --no-build

# Verify that the olean does need to be present in the build directory
test_cmd rm .lake/build/lib/lean/Test.olean .lake/build/lib/lean/Test/Imported.olean
LAKE_CACHE_DIR="$CACHE_DIR" test_run -v build +Test.Imported --no-build --wfail
LAKE_CACHE_DIR="$CACHE_DIR" test_run -v build +Test

# Cleanup
rm -f produced.out Ignored.lean
