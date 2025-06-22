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
cached_art="$(LAKE_CACHE_DIR="$CACHE_DIR" $LAKE query +Test:o)"
uncached_art="$(LAKE_CACHE_DIR= $LAKE query +Test:o)"
test_exp "$(dirname -- "$cached_art")" = "$CACHE_DIR/artifacts"
test_exp "$cached_art" != "$uncached_art"
test_cmd cmp -s "$cached_art" "$uncached_art"

# Cleanup
rm -f produced.out
