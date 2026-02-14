#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the functionality of the Reservoir (or other remote) cache

# Check necessary environment variables art set
if [ -z "${LAKE_CACHE_KEY:-}" ]; then
  echo "Must be run with LAKE_CACHE_KEY set"
  exit 1
fi
if [ -z "${TEST_ENDPOINT:-}" ]; then
  echo "Must be run with TEST_ENDPOINT set"
  exit 1
fi
TEST_ARTIFACT_ENDPOINT="${TEST_ARTIFACT_ENDPOINT:-$TEST_ENDPOINT/a0}"
TEST_REVISION_ENDPOINT="${TEST_REVISION_ENDPOINT:-$TEST_ENDPOINT/r0}"
TEST_CDN_ENDPOINT="${TEST_CDN_ENDPOINT:-https://reservoir.lean-cache.cloud}"
TEST_CDN_ARTIFACT_ENDPOINT="${TEST_CDN_ARTIFACT_ENDPOINT:-$TEST_CDN_ENDPOINT/a0}"
TEST_CDN_REVISION_ENDPOINT="${TEST_CDN_REVISION_ENDPOINT:-$TEST_CDN_ENDPOINT/r0}"
TEST_RESERVOIR_URL="${TEST_RESERVOIR_URL:-https://reservoir.lean-lang.org}"
export RESERVOIR_API_URL="$TEST_RESERVOIR_URL/api/v0"

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

with_bogus_endpoints() {
  LAKE_CACHE_ARTIFACT_ENDPOINT=https://example.com \
  LAKE_CACHE_REVISION_ENDPOINT=https://example.com \
  "$@"
}

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the repository on each test.
init_git

# Store Lake cache in a local directory
TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
export LAKE_CACHE_DIR="$TEST_DIR/.lake/cache"

# Ensure that Lake is run without a toolchain name
# (so toolchain does not end up in the cache)
export ELAN_TOOLCHAIN=

echo "# TESTS"

# Test `--repo` validation
test_err "must contain exactly one '/'" cache get --repo='invalid'
test_err 'invalid characters in repository name' cache get --repo='!/invalid'

# Test `cache get` command errors for bad configurations
test_err 'the `--platform` and `--toolchain` options do nothing' \
  cache get bogus.jsonl --scope='bogus' --platform='bogus' --wfail
test_err 'the `--platform` and `--toolchain` options do nothing' \
  cache get bogus.jsonl --scope='bogus' --toolchain='bogus' --wfail
test_err 'a custom endpoint must be set (not Reservoir)' cache get --scope='bogus'
with_cdn_endpoints test_err 'the `--scope` or `--repo` option must be set' cache get
LAKE_CACHE_ARTIFACT_ENDPOINT=bogus test_err 'both environment variables must be set' cache get
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'both environment variables must be set' cache get

# Test `cache put` command errors for bad configurations
with_upload_endpoints test_err 'the `--scope` or `--repo` option must be set' cache put bogus.jsonl
test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope='bogus'
LAKE_CACHE_KEY= test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope='bogus'
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope='bogus'
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope='bogus'

# Test revision failure (with Reservoir)
REV=$(git rev-parse HEAD)
test_err "revision not found" cache get --repo='leanprover/bogus' --rev='bogus'
test_err "outputs not found for revision" cache get --repo='leanprover/bogus' --rev=$REV

# Test `cache get` skipping non-Reservoir dependencies
test_run -f non-reservoir.toml update
test_out 'hello: skipping non-Reservoir dependency' -f non-reservoir.toml cache get

# Build artifacts
test_run build +Test -o .lake/outputs.jsonl
test_exp -f .lake/outputs.jsonl
test_cmd_eq 3 wc -l < .lake/outputs.jsonl
test_cmd cp -r .lake/cache .lake/cache-backup

# Test fetch from invalid URL
with_bogus_endpoints test_err "failed to upload artifact" \
  cache put .lake/outputs.jsonl --scope='!/test'

# Test cache put/get with a custom endpoint
with_upload_endpoints test_run cache put .lake/outputs.jsonl --scope='!/test'
test_cmd rm -rf .lake/build "$LAKE_CACHE_DIR"
with_cdn_endpoints test_err 'failed to download some artifacts' \
  cache get .lake/outputs.jsonl --scope='!/bogus'
with_cdn_endpoints test_run cache get .lake/outputs.jsonl --scope='!/test'
test_run build +Test --no-build

# Test that outputs and artifacts are not re-downloaded
with_cdn_endpoints test_not_out "downloading" cache get .lake/outputs.jsonl --scope='!/test'
with_cdn_endpoints test_not_out "downloading artifact" cache get --scope='!/test'
with_cdn_endpoints test_not_out "downloading" cache get --scope='!/test'

# Test that the revision cache directory for the package is properly created
test_exp -d $LAKE_CACHE_DIR/revisions/test

# Test `--force-download`
with_cdn_endpoints test_out "downloading" cache get --scope='!/test' --force-download

# Test cache put/get with a set platform/toolchain
with_upload_endpoints test_run cache put .lake/outputs.jsonl \
  --repo='leanprover/test' --platform=foo --toolchain=bar
test_cmd rm -rf .lake/build "$LAKE_CACHE_DIR"
with_cdn_endpoints test_run cache get \
  --repo='leanprover/test' --platform=foo --toolchain=bar
test_run build +Test --no-build
test_cmd rm -rf .lake/build "$LAKE_CACHE_DIR"
test_run cache get \
  --repo='leanprover/test' --platform=foo --toolchain=bar
test_run build +Test --no-build

# Test dirty work tree warnings
test_cmd touch Ignored.lean
test_cmd git add -f Ignored.lean
with_upload_endpoints test_err "package has changes" --wfail \
  cache put .lake/outputs.jsonl --repo='leanprover/bogus'
test_err "package has changes" --wfail cache get --repo='leanprover/bogus'
test_cmd git commit -m "v2"

# Test revision search
test_cmd rm -rf .lake/build "$LAKE_CACHE_DIR"
with_cdn_endpoints test_err "no outputs found" --wfail cache get --scope='!/test' --max-revs=1
with_cdn_endpoints test_run cache get --scope='!/test'
test_run build +Test --no-build

# Test Reservoir download
test_run -f reservoir2.toml update --keep-toolchain
test_out "the artifact cache is not enabled for this package" \
  -d .lake/packages/Cli build -o "$TEST_DIR/.lake/cli-outputs.jsonl"
LAKE_ARTIFACT_CACHE=true test_run -d .lake/packages/Cli \
  build -o "$TEST_DIR/.lake/cli-outputs.jsonl" --no-build
with_upload_endpoints test_run -d .lake/packages/Cli \
  cache put "$TEST_DIR/.lake/cli-outputs.jsonl" --repo=leanprover/lean4-cli
test_cmd rm -rf .lake/packages/Cli/.lake/build "$LAKE_CACHE_DIR"
test_fails -f reservoir.toml build @Cli --no-build
test_err "failed to download artifacts for some dependencies" \
  -f reservoir2.toml cache get --max-revs=1
test_run -f reservoir.toml cache get --max-revs=1
test_run -f reservoir.toml build @Cli --no-build

# Test Reservoir with `--repo` uses GitHub scope
test_cmd rm -rf .lake/cache
test_run -d .lake/packages/Cli cache get --repo=leanprover/lean4-cli --max-revs=1
test_run -d .lake/packages/Cli build --no-build

# Cleanup
rm -rf .git produced.out
