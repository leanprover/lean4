#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the functionality of the Reservoir (or other remote) cache

# Check necessary environment variables art set
if [ -z "${LAKE_CACHE_KEY:-}" ]; then
  echo "Must be run with LAKE_CACHE_KEY set"
  exit 1
fi
TEST_ARTIFACT_ENDPOINT="${TEST_ARTIFACT_ENDPOINT:-$TEST_ENDPOINT/a0}"
TEST_REVISION_ENDPOINT="${TEST_REVISION_ENDPOINT:-$TEST_ENDPOINT/r0}"
TEST_CDN_ENDPOINT="${TEST_CDN_ENDPOINT:-https://reservoir.lean-cache.cloud}"
TEST_CDN_ARTIFACT_ENDPOINT="${TEST_CDN_ARTIFACT_ENDPOINT:-$TEST_CDN_ENDPOINT/a0}"
TEST_CDN_REVISION_ENDPOINT="${TEST_CDN_REVISION_ENDPOINT:-$TEST_CDN_ENDPOINT/r0}"

with_upload_endpoints() {
  LAKE_CACHE_ARTIFACT_ENDPOINT="$TEST_ARTIFACT_ENDPOINT" \
  LAKE_CACHE_REVISION_ENDPOINT="$TEST_REVISION_ENDPOINT" \
  "$@"
}

with_cdn_endpoints() {
  LAKE_CACHE_ARTIFACT_ENDPOINT="$TEST_CDN_ARTIFACT_ENDPOINT" \
  LAKE_CACHE_REVISION_ENDPOINT="$TEST_CDN_REVISION_ENDPOINT" \
  "$@"
}

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the repository on each test.
init_git

# Store Lake cache in a local directory
TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$TEST_DIR/.lake/cache"
export LAKE_CACHE_DIR="$CACHE_DIR"

echo "# TESTS"

# Tests that `cache put` errors without scope and/or endpoint
test_err 'the `--scope` option must be set for `cache put`' cache put bogus.jsonl
test_err 'environment variable must be set for `cache put`' cache put bogus.jsonl --scope=bogus
test_err 'environment variable must be set for `cache get`' cache get

# Test lookup failure
with_cdn_endpoints test_err "outputs not found for revision" cache get --scope="bogus"

# Test cache put/get with a custom endpoint
test_run build +Test -o .lake/outputs.jsonl
test_exp -f .lake/outputs.jsonl
test_cmd_eq 2 wc -l < .lake/outputs.jsonl
with_upload_endpoints test_run cache put .lake/outputs.jsonl --scope="test"
test_cmd rm -rf .lake/cache
with_cdn_endpoints test_run cache get
test_run build +Test --no-build

# Test that outputs and artifacts are not re-downloaded
# also, test the use of the `--scope` option
with_cdn_endpoints test_not_out "downloading" cache get
with_cdn_endpoints test_not_out "downloading" cache get --scope="test"

# Cleanup
rm -rf .git produced.out
