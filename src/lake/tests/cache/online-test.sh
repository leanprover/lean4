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
export LAKE_CACHE_DIR="$TEST_DIR/.lake/cache"

echo "# TESTS"

# Test `cache get` command errors for bad configurations
with_cdn_endpoints test_err 'the `--scope` option must be set' cache get
LAKE_CACHE_ARTIFACT_ENDPOINT=bogus test_err 'both environment variables must be set' cache get
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'both environment variables must be set' cache get

# Test `cache put` command errors for bad configurations
test_err 'the `--scope` option must be set' cache put bogus.jsonl
test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope=bogus
LAKE_CACHE_KEY= test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope=bogus
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope=bogus
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope=bogus

# Test lookup failure
with_cdn_endpoints test_err "outputs not found for revision" cache get --scope="bogus"

# Test `cache get` skipping non-Reservoir dependencies
test_run -f  non-reservoir.toml update
test_out 'hello: skipping non-Reservoir dependency' -f non-reservoir.toml cache get

# Test cache put/get with a custom endpoint
test_run build +Test -o .lake/outputs.jsonl
test_exp -f .lake/outputs.jsonl
test_cmd_eq 3 wc -l < .lake/outputs.jsonl
with_upload_endpoints test_run cache put .lake/outputs.jsonl --scope="test"
test_cmd rm -rf .lake/build "$LAKE_CACHE_DIR"
with_cdn_endpoints test_err 'failed to download some artifacts' \
  cache get .lake/outputs.jsonl --scope="bogus"
with_cdn_endpoints test_run cache get .lake/outputs.jsonl --scope="test"
test_run build +Test --no-build

# Test that outputs and artifacts are not re-downloaded
with_cdn_endpoints test_not_out "downloading" cache get .lake/outputs.jsonl --scope="test"
with_cdn_endpoints test_not_out "downloading artifact" cache get --scope="test"
with_cdn_endpoints test_not_out "downloading" cache get --scope="test"

# Test Reservoir download
test_run -f reservoir2.toml update --keep-toolchain
test_out "the artifact cache is not enabled for this package" \
  -d .lake/packages/Cli build -o "$TEST_DIR/.lake/cli-outputs.jsonl"
LAKE_ARTIFACT_CACHE=true test_run -d .lake/packages/Cli \
  build -o "$TEST_DIR/.lake/cli-outputs.jsonl" --no-build
with_upload_endpoints test_run -d .lake/packages/Cli \
  cache put "$TEST_DIR/.lake/cli-outputs.jsonl" --scope "leanprover/lean4-cli"
test_cmd rm -rf .lake/packages/Cli/.lake/build "$LAKE_CACHE_DIR"
test_fails -f reservoir.toml build @Cli --no-build
test_err "failed to download artifacts for some dependencies" \
  -f reservoir2.toml cache get
test_run -f reservoir.toml cache get
test_run -f reservoir.toml build @Cli --no-build

# Cleanup
rm -rf .git produced.out
