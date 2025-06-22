#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the functionality of the Lake artifact cache

TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$TEST_DIR/.lake/cache"

# Ensure packages without `enableArtifactCache` do not use the cache
LAKE_CACHE_DIR="$CACHE_DIR" test_run build -f disabled.toml Test:static
test_exp ! -d "$CACHE_DIR"
./clean.sh

# Ensure a build runs properly with some artifacts cached
LAKE_CACHE_DIR="$CACHE_DIR" test_run build Test:static
LAKE_CACHE_DIR="$CACHE_DIR" test_run build Test:static --no-build

# Test replay of a cached build
LAKE_CACHE_DIR="$CACHE_DIR" test_out 'Replayed Test:c.o' build +Test:o -v

# Verify that a rebuild with the cache disabled is a no-op
touch .lake/build/ir/Test.c # avoid mod time fallback if trace is missing
LAKE_CACHE_DIR= test_run build +Test:o --no-build
LAKE_CACHE_DIR= test_run build Test:static --no-build

# Verify the cache directory structure was created
test_exp -d "$CACHE_DIR"
test_exp -d "$CACHE_DIR/inputs"
test_exp -n `cat "$CACHE_DIR/inputs/test.jsonl"`
test_exp -d "$CACHE_DIR/artifacts"

# Checked that the cached artifact is in the expected location
# and equivalent to the standard artifact
local_art="$(LAKE_CACHE_DIR= $LAKE query +Test:o)"
cache_art="$(LAKE_CACHE_DIR="$CACHE_DIR" $LAKE query +Test:o)"
test_exp "$(dirname -- "$cache_art")" = "$CACHE_DIR/artifacts"
test_exp "$cache_art" != "$local_art"
test_cmd cmp -s "$cache_art" "$local_art"

# Verify that things work properly if the cached artifact is removed
test_cmd rm "$cache_art"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "⚠ [3/3] Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached
test_cmd rm "$CACHE_DIR/inputs/test.jsonl"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached

# Verify that things work properly if the local artifact is removed
test_cmd rm "$local_art"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_cmd rm "$local_art.trace"
LAKE_CACHE_DIR="$CACHE_DIR" test_out "Fetched Test:c.o" build +Test:o -v --no-build

# Cleanup
rm -f produced.out
