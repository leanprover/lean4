#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that caching a text artifact recovers from a temporary file
# left behind by an interrupted write to the Lake artifact cache

TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$(norm_path "$TEST_DIR")/.lake/cache"
export LAKE_CACHE_DIR="$CACHE_DIR"

# Cache the artifact once to learn its path
test_run build text
art=$("$LAKE" query text)
test_exp "$(norm_dirname "$art")" = "$CACHE_DIR/artifacts"
test_cmd diff -u fixtures/source.txt "$art"
tmp="$art.part.tmp"

# Plants the given file as the temporary file of a fresh save,
# re-caches the artifact, and verifies the result
check_recovery() {
  rm -rf .lake/build "$CACHE_DIR/outputs"
  rm -f "$art"
  cat "$1" > "$tmp"
  test_run build text
  test_cmd diff -u fixtures/source.txt "$art"
  test_exp ! -e "$tmp"
}

echo "# TEST: complete temporary file"
check_recovery fixtures/source.txt
echo "# TEST: empty temporary file"
check_recovery fixtures/empty.txt
echo "# TEST: truncated temporary file"
check_recovery fixtures/truncated.txt
echo "# TEST: temporary file cut mid-character"
check_recovery fixtures/midchar.txt
echo "# TEST: oversized temporary file"
check_recovery fixtures/oversized.txt

# Test that downloading an artifact leaves no temporary files behind
# and publishes nothing on a hash mismatch
dl=.lake/cache/artifacts/download.art

echo "# TEST: download over leftover temporary files"
rm -f "$dl"
cat fixtures/truncated.txt > "$dl.tmp"
cat fixtures/truncated.txt > "$dl.part.tmp"
test_run script run download source.txt "$dl"
test_cmd diff -u fixtures/source.txt "$dl"
test_exp ! -e "$dl.tmp"
test_exp ! -e "$dl.part.tmp"

echo "# TEST: download with hash mismatch"
rm -f "$dl"
test_err "hash mismatch" script run download truncated.txt "$dl"
test_exp ! -e "$dl"
test_exp ! -e "$dl.part.tmp"
# The mismatched download is kept
rm -f "$dl.tmp"

# Verify no temporary files are left in the cache
check_diff /dev/null <(ls -1 "$CACHE_DIR"/artifacts/*.tmp 2>/dev/null)

# Cleanup
rm -f produced.out
