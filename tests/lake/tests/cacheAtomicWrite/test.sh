#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that caching never reads or removes another publisher's temporary file

TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$(norm_path "$TEST_DIR")/.lake/cache"
export LAKE_CACHE_DIR="$CACHE_DIR"

# Cache the artifact once to learn its path
test_run build text
art=$("$LAKE" query text)
test_exp "$(norm_dirname "$art")" = "$CACHE_DIR/artifacts"
test_cmd diff -u fixtures/source.txt "$art"
tmp="$CACHE_DIR/artifacts/.lake-cache-$$-1.tmp"

# Leave a different owner's staging file in place while re-caching the artifact.
check_recovery() {
  rm -rf .lake/build "$CACHE_DIR/outputs"
  rm -f "$art"
  cat "$1" > "$tmp"
  test_run build text
  test_cmd diff -u fixtures/source.txt "$art"
  test_cmd diff -u "$1" "$tmp"
  rm -f "$tmp"
}

echo "# TEST: another publisher's temporary file"
check_recovery fixtures/source.txt

# Include hidden staging files in the completed-invocation check.
check_diff /dev/null <(find "$CACHE_DIR/artifacts" -name '.lake-cache-*.tmp' -print)

# Cleanup
rm -f produced.out
