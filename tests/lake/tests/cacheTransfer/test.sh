#!/usr/bin/env bash
# Copyright (c) 2026 Lean FRO. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Mac Malone, Claude Code
source ../common.sh

./clean.sh

# Test artifact transfers to and from a remote cache using a mock server.
# The online cache test covers the same operations against Reservoir,
# but needs credentials and network access, so it cannot be run in CI.

PYTHON="${PYTHON:-python3}"

# The mock server and Lake's uploads have requirements CI may not satisfy
if ! "$PYTHON" -c 'import sys; sys.exit(sys.version_info < (3, 11))' 2> /dev/null; then
  echo "SKIPPED: $PYTHON 3.11 or later not found"
  exit 0
fi
if ! curl --help all 2> /dev/null | grep -q -- '--aws-sigv4'; then
  echo "SKIPPED: curl does not support '--aws-sigv4'"
  exit 0
fi

# The cache map schema version (see `Lake.CacheMap.schemaVersion`)
SCHEMA_VER=2026-03-17

TEST_DIR="$(norm_path "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)")"
WORK_DIR="$TEST_DIR/work"
STORE_DIR="$WORK_DIR/store"
CACHE_DIR="$WORK_DIR/cache"
SERVER_LOG="$WORK_DIR/server.log"
PORT_FILE="$WORK_DIR/port"

# Copy test data to a working directory to avoid initializing a Git repository
# inside the checked-in source tree
mkdir -p "$WORK_DIR"
cp -r lakefile.toml non-reservoir.toml dep.toml BadCurl.lean Test.lean Test dep "$WORK_DIR/"
cd "$WORK_DIR"

echo "# SETUP"

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the repository on each test.
init_git

# Serve the mock cache on a free port, recorded in `$PORT_FILE` once it is up
"$PYTHON" "$TEST_DIR/server.py" --store "$STORE_DIR" --port-file "$PORT_FILE" \
  >> "$SERVER_LOG" 2>&1 &
SERVER_PID=$!
trap 'kill $SERVER_PID 2> /dev/null' EXIT
# Since the server is a separate process, the port it binds has to be waited on
while [ ! -s "$PORT_FILE" ]; do
  if ! kill -0 "$SERVER_PID" 2> /dev/null; then
    echo "FAILURE: the mock server exited"
    cat "$SERVER_LOG"
    exit 1
  fi
  sleep 0.1
done
URL="http://127.0.0.1:$(cat "$PORT_FILE")"
echo "URL=$URL"

# Point the configured cache services at the mock server.
# Copied after the commit above so that it does not dirty the work tree.
cp "$TEST_DIR/services.toml" "$TEST_DIR/no-services.toml" .
sed_i "s|%URL%|$URL|g" services.toml

# The option validation below expects no configured service, as in a default
# installation; the transfer tests switch to the mock services
export LAKE_CONFIG="$WORK_DIR/no-services.toml"
export LAKE_CACHE_DIR="$CACHE_DIR"
export LAKE_CACHE_KEY="mock:key"
# Point the default (Reservoir) service at the mock server as well,
# so that no part of this test can reach the network
export RESERVOIR_API_URL="$URL/ok/api/v1"
# Ensure Lake is run without a toolchain name
# (so the toolchain does not end up in cache paths)
export ELAN_TOOLCHAIN=

# The `Test` library transfers one bundle per module, each of which a
# build unpacks into an olean, an ilean, and a C file
NUM_ARTS=2
NUM_REPLAY_ARTS=8

# The `dep` package's library has a single module
NUM_DEP_ARTS=1
NUM_DEP_REPLAY_ARTS=4

# Runs a command with the cache endpoints set through the environment,
# which is the deprecated alternative to a configured service
with_endpoints() {
  LAKE_CACHE_ARTIFACT_ENDPOINT="$URL/ok/a0" \
  LAKE_CACHE_REVISION_ENDPOINT="$URL/ok/r0" \
  "$@"
}

# Counts artifacts, ignoring the temporary files a failed transfer leaves behind
test_artifacts() {
  expected="$1"; dir="${2:-$CACHE_DIR/artifacts}"
  actual="$({ ls -1 "$dir" 2> /dev/null || true; } | { grep -cv '\.tmp$' || true; })"
  echo "? artifacts in $dir ($actual) = $expected"
  test "$actual" = "$expected"
}

echo "# VALIDATION TESTS"

# Verify `--repo` validation
test_err "must contain exactly one '/'" cache get --repo='invalid'
test_err 'invalid characters in repository name' cache get --repo='!/invalid'

# Verify `--mappings-only` validation
test_err '`--mappings-only` is not supported' cache get --mappings-only bogus.jsonl
with_endpoints test_err '`--mappings-only` requires services' cache get --mappings-only

# Verify `--service` validation
test_err 'service `bogus` not found in system configuration' \
  cache get --service='bogus'
test_err 'service `bogus` not found in system configuration' \
  cache put bogus.jsonl --scope='bogus' --service='bogus'

# Verify `cache get` rejects bad configurations
test_err '`--no-overwrite` is not supported for `cache get`' \
  cache get --no-overwrite
test_err 'the `--platform` and `--toolchain` options do nothing' \
  cache get bogus.jsonl --scope='bogus' --platform='bogus' --wfail
test_err 'the `--platform` and `--toolchain` options do nothing' \
  cache get bogus.jsonl --scope='bogus' --toolchain='bogus' --wfail
test_err 'the `--rev` option does nothing' \
  cache get bogus.jsonl --scope='bogus' --rev='bogus' --wfail
test_err 'a custom endpoint must be set (not Reservoir)' cache get --scope='bogus'
test_err 'unknown package `bogus`' cache get --package='bogus'
test_err 'the `--rev` option is not supported for a multi-package Reservoir `cache get`' \
  cache get --rev=bogus
with_endpoints test_err 'the `--scope` or `--repo` option must be set' cache get
LAKE_CACHE_ARTIFACT_ENDPOINT=bogus test_err 'both environment variables must be set' cache get
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'both environment variables must be set' cache get

# Verify `cache put` rejects bad configurations
with_endpoints test_err 'the `--scope` or `--repo` option must be set' cache put bogus.jsonl
test_err 'the `--package` option is not supported for `cache put`' \
  cache put bogus.jsonl --scope='bogus' --package='bogus'
test_err 'the `--rev` option is not supported for `cache put`' \
  cache put bogus.jsonl --scope='bogus' --rev=bogus
test_err 'the `--service` option must be set' \
  cache put bogus.jsonl --scope='bogus'
LAKE_CACHE_KEY= test_err 'the `--service` option must be set' \
  cache put bogus.jsonl --scope='bogus'
LAKE_CACHE_ARTIFACT_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope='bogus'
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put bogus.jsonl --scope='bogus'

# Verify `cache put-staged` rejects bad configurations
with_endpoints test_err 'the `--scope` or `--repo` option must be set' \
  cache put-staged bogus
test_err 'the `--package` option does nothing for `cache put-staged`' \
  cache put-staged bogus --scope='bogus' --package='bogus'
test_err 'the `--service` option must be set' \
  cache put-staged bogus --scope='bogus'
LAKE_CACHE_KEY= test_err 'the `--service` option must be set' \
  cache put-staged bogus --scope='bogus'
LAKE_CACHE_ARTIFACT_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put-staged bogus --scope='bogus'
LAKE_CACHE_REVISION_ENDPOINT=bogus test_err 'these environment variables must be set' \
  cache put-staged bogus --scope='bogus'

# Verify `cache add` rejects bad configurations
test_err '`--scope` and `--repo` require `--service`' \
  cache add bogus.jsonl --scope='bogus'
test_err '`--scope` and `--repo` require `--service`' \
  cache add bogus.jsonl --repo='leanprover/bogus'
test_err 'unknown package `bogus`' cache add bogus.jsonl --package='bogus'
# The package is selected with `--package`, not a positional argument
test_err 'unexpected arguments: bogus' cache add bogus.jsonl bogus

# Verify a revision that cannot be resolved or has no outputs is reported
test_err 'revision not found' cache get --repo='leanprover/bogus' --rev='bogus'
test_err 'outputs not found for revision' \
  cache get --repo='leanprover/bogus' --rev="$(git rev-parse HEAD)"

# Verify dependencies that are not on Reservoir are skipped
test_run -f non-reservoir.toml update
test_out 'hello: skipping non-Reservoir dependency' -f non-reservoir.toml cache get
# Verify such a dependency is an error when selected with `--package`
test_err 'hello: not a Reservoir dependency' \
  -f non-reservoir.toml cache get --package=hello
test_run update

echo "# TRANSFER TESTS"

# The remaining tests transfer artifacts through the mock services
export LAKE_CONFIG="$WORK_DIR/services.toml"

# Build the package and record its outputs
test_run build Test -o outputs.jsonl
test_exp -s outputs.jsonl

# Verify artifacts and outputs are uploaded to the default upload service
test_run cache put outputs.jsonl --scope=test
REV="$(git rev-parse HEAD)"
test_exp -f "$STORE_DIR/r0/test/$REV.jsonl"
test_cmd cmp -s outputs.jsonl "$STORE_DIR/r0/test/$REV.jsonl"
test_artifacts "$NUM_ARTS" "$STORE_DIR/a0/test"

# Verify a rejected artifact upload is reported
test_err 'failed to upload artifact' cache put outputs.jsonl --scope=test --service=deny
# Verify a rejected outputs upload is reported
test_err 'failed to upload artifact' cache put outputs.jsonl --scope=test --service=denyRevisions

# Verify a workspace can be restored from the remote cache
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_out 'downloaded artifact' cache get --scope=test --service=ok
test_artifacts "$NUM_ARTS"
test_exp -d "$CACHE_DIR/revisions/test"
test_run build Test --no-build

# Verify cached outputs and artifacts are not fetched again
test_not_out 'downloading' cache get --scope=test --service=ok
# Verify `--force-download` fetches them regardless
test_out 'downloading build outputs' cache get --scope=test --service=ok --force-download
# Verify it does so for a set revision as well
test_out 'downloading build outputs' \
  cache get --scope=test --service=ok --rev=HEAD --force-download

# Verify a missing artifact fails the transfer,
# leaving the artifacts that did transfer in the cache
test_cmd rm -rf .lake/build "$CACHE_DIR"
MISSING="$(ls -1 "$STORE_DIR/a0/test" | head -1)"
test_cmd mv "$STORE_DIR/a0/test/$MISSING" "$WORK_DIR/$MISSING"
test_err 'failed to download some artifacts' cache get --scope=test --service=ok
match_text 'status code: 404' produced.out
test_artifacts $((NUM_ARTS - 1))
# Verify the failure did not poison the cache
test_cmd mv "$WORK_DIR/$MISSING" "$STORE_DIR/a0/test/$MISSING"
test_run cache get --scope=test --service=ok
test_artifacts "$NUM_ARTS"
test_run build Test --no-build

# Verify an artifact whose response carries no body is reported like any other
# failed transfer, without discarding the artifacts that did transfer.
# https://github.com/leanprover/lean4/issues/14698
test_cmd rm -rf .lake/build "$CACHE_DIR"
ART="$(ls -1 "$STORE_DIR/a0/test" | head -1)"
cat > empty-outputs.jsonl << EOF
"$SCHEMA_VER"
["aaaaaaaaaaaaaaaa","${ART%.art}.ltar"]
["bbbbbbbbbbbbbbbb","0123456789abcdef.ltar"]
EOF
test_err 'failed to download some artifacts' cache get empty-outputs.jsonl \
  --scope=test --service=empty
test_artifacts 1

# Verify a corrupted download is not adopted as an artifact
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'hash mismatch' cache get --scope=test --service=corrupt
test_artifacts 0
test_run cache get --scope=test --service=ok
test_artifacts "$NUM_ARTS"
test_run build Test --no-build

# Verify a truncated download is detected even though its headers
# report success (a status code alone does not imply a complete transfer)
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'failed to download some artifacts' cache get --scope=test --service=truncate
match_text 'status code: 200' produced.out
test_artifacts 0
test_run cache get --scope=test --service=ok
test_run build Test --no-build

# Verify a transfer that leaves no output file is reported
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'failed to download artifact' cache get --scope=test --service=reset
test_artifacts 0
test_run cache get --scope=test --service=ok
test_run build Test --no-build

# Verify the transfers that `curl` itself misreports,
# which no server response can produce.
# Lake runs the `CURL` command, if set, which is the only way to reach the mock
# on Windows, where `PATH` cannot shadow the system `curl`.
test_run build curl
CURL_MOCK="$($LAKE query curl:exe)"
CURL_REAL="$(type -P curl)"
# Nothing reports an error here,
# but the count of transfers detects it.
test_cmd rm -rf "$CACHE_DIR"
CURL="$CURL_MOCK" BAD_CURL=quiet test_err 'failed to download some artifacts' \
  cache get outputs.jsonl --scope=test --service=ok
test_artifacts 0
# Every artifact arrives complete,
# but the reported transfer error marks them unusable.
test_cmd rm -rf "$CACHE_DIR"
CURL="$CURL_MOCK" BAD_CURL=exitcode REAL_CURL="$CURL_REAL" \
  test_err 'failed to download artifact' cache get outputs.jsonl --scope=test --service=ok
test_artifacts 0
# Every artifact is reported as transferred but none was written,
# which must be reported rather than abort the batch
# https://github.com/leanprover/lean4/issues/14698
test_cmd rm -rf "$CACHE_DIR"
CURL="$CURL_MOCK" BAD_CURL=nofile REAL_CURL="$CURL_REAL" BAD_CURL_DIR="$CACHE_DIR/artifacts" \
  test_err 'failed to download some artifacts' cache get outputs.jsonl --scope=test --service=ok
test_artifacts 0

# Verify an error response is reported along with its body
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'unexpected response' cache get --scope=test --service=denyArtifacts
match_text 'AccessDenied' produced.out
test_artifacts 0

# Verify a rejected outputs download is reported
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'output lookup failed' cache get --scope=test --service=deny

# Verify a revision without outputs is reported
test_cmd git commit --allow-empty -m "no outputs"
test_err 'no outputs found' cache get --scope=test --service=ok --max-revs=1
# Verify the revision search finds the outputs of an earlier revision
test_run cache get --scope=test --service=ok
test_artifacts "$NUM_ARTS"
test_run build Test --no-build

# Verify artifacts sharing a content hash are downloaded once
# and copied locally for each extension
test_cmd rm -rf .lake/build "$CACHE_DIR"
ART="$(ls -1 "$STORE_DIR/a0/test" | head -1)"
HASH="${ART%.art}"
cat > dup-outputs.jsonl << EOF
"$SCHEMA_VER"
["aaaaaaaaaaaaaaaa","$HASH.o"]
["bbbbbbbbbbbbbbbb","$HASH.dup"]
EOF
: > "$SERVER_LOG"
test_run cache get dup-outputs.jsonl --scope=test --service=ok
test_exp -f "$CACHE_DIR/artifacts/$HASH.o"
test_exp -f "$CACHE_DIR/artifacts/$HASH.dup"
test_cmd cmp -s "$CACHE_DIR/artifacts/$HASH.o" "$CACHE_DIR/artifacts/$HASH.dup"
# Copies, not hard links, which would break cache permissions and pruning
test_exp "$(stat_ch "$CACHE_DIR/artifacts/$HASH.dup")" = 1
test_cmd_eq 1 grep -c "GET /ok/a0/test/$ART" "$SERVER_LOG"

# Verify artifacts missing from the local cache are fetched on demand
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_run cache get --scope=test --service=ok
test_cmd rm -rf .lake/build "$CACHE_DIR/artifacts"
test_out 'downloaded artifact' -v build Test --no-build
test_artifacts "$NUM_REPLAY_ARTS"

# Verify a corrupted on-demand fetch is reported
test_cmd rm -rf .lake/build "$CACHE_DIR/artifacts"
test_run cache add outputs.jsonl --scope=test --service=corrupt
test_err 'hash mismatch' build Test --no-build
test_artifacts 0

# Verify a repository scope is uploaded under its platform and toolchain
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_run build Test -o outputs.jsonl
REV="$(git rev-parse HEAD)"
test_run cache put outputs.jsonl --repo=leanprover/test --platform=foo --toolchain=bar
test_exp -f "$STORE_DIR/r0/leanprover/test/pt/foo/tc/bar/$REV.jsonl"
test_run cache put outputs.jsonl --repo=leanprover/test

# Verify a repository scope is downloaded through the Reservoir API
test_cmd rm -rf .lake/build "$CACHE_DIR"
: > "$SERVER_LOG"
test_out 'downloaded artifact' cache get --repo=leanprover/test
match_text "POST /ok/api/v1/repositories/leanprover/test/artifacts" "$SERVER_LOG"
test_artifacts "$NUM_ARTS"
test_run build Test --no-build

# Verify `--package` fetches a single dependency through Reservoir,
# using that dependency's scope and revision
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_run -f dep.toml update
test_run -d dep build Dep -o dep-outputs.jsonl
test_run -d dep cache put dep-outputs.jsonl --repo=leanprover/dep
test_cmd rm -rf dep/.lake/build .lake/build "$CACHE_DIR"
: > "$SERVER_LOG"
# The other dependencies are left alone, so none is reported as skipped
test_not_out 'skipping non-Reservoir dependency' -f dep.toml cache get --package=dep
match_text "POST /ok/api/v1/packages/leanprover/dep/artifacts" "$SERVER_LOG"
test_exp -d "$CACHE_DIR/revisions/dep"
test_artifacts "$NUM_DEP_ARTS"
test_run -f dep.toml build @dep/Dep --no-build

# Verify `--rev` looks up only that revision for the selected package,
# rather than backtracking from its head revision
test_cmd rm -rf dep/.lake/build .lake/build "$CACHE_DIR"
test_err 'outputs not found for revision' \
  -f dep.toml cache get --package=dep --rev=HEAD~1
test_artifacts 0
test_run -f dep.toml cache get --package=dep --rev=HEAD
test_artifacts "$NUM_DEP_ARTS"
test_run -f dep.toml build @dep/Dep --no-build

# Verify `--package` also selects the dependency for a custom endpoint scope,
# where `--rev` resolves within that dependency's repository
test_run -d dep cache put dep-outputs.jsonl --scope=dep
test_cmd rm -rf dep/.lake/build .lake/build "$CACHE_DIR"
test_run -f dep.toml cache get --package=dep --scope=dep --service=ok --rev=HEAD
test_exp -d "$CACHE_DIR/revisions/dep"
test_artifacts "$NUM_DEP_ARTS"
test_run -f dep.toml build @dep/Dep --no-build

# Verify `--package` selects the dependency for a mappings file as well,
# which is otherwise loaded into the root package's local scope
test_cmd rm -rf dep/.lake/build .lake/build "$CACHE_DIR"
test_run -f dep.toml cache get dep-outputs.jsonl --package=dep --scope=dep --service=ok
test_exp -d "$CACHE_DIR/outputs/dep"
test_exp ! -e "$CACHE_DIR/outputs/test"
test_artifacts "$NUM_DEP_ARTS"
test_run -f dep.toml build @dep/Dep --no-build

# Verify `cache add` attaches mappings to the selected package,
# whose artifacts are then fetched on demand
test_cmd rm -rf dep/.lake/build .lake/build "$CACHE_DIR"
test_run -f dep.toml cache add dep-outputs.jsonl --package=dep --scope=dep --service=ok
test_artifacts 0
test_out 'downloaded artifact' -f dep.toml -v build @dep/Dep --no-build
test_artifacts "$NUM_DEP_REPLAY_ARTS"
test_run update

# Verify a malformed artifact URL lookup is reported
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'Incorrect number of results' cache get --repo=leanprover/test --service=badCount
# Verify a Reservoir API error is reported
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_err 'Reservoir error' cache get --repo=leanprover/test --service=apiError

# Verify `--mappings-only` fetches outputs but no artifacts,
# leaving the artifacts to be fetched on demand
test_cmd rm -rf .lake/build "$CACHE_DIR"
: > "$SERVER_LOG"
test_run cache get --repo=leanprover/test --mappings-only
test_artifacts 0
test_out 'downloaded artifact' -v build Test --no-build
match_text "GET /ok/api/v1/repositories/leanprover/test/artifacts/" "$SERVER_LOG"
test_artifacts "$NUM_REPLAY_ARTS"

# Verify staged artifacts can be uploaded and downloaded
test_cmd rm -rf staging
test_run cache stage outputs.jsonl staging
test_run cache put-staged staging --scope=staged
test_exp -f "$STORE_DIR/r0/staged/$REV.jsonl"
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_run cache get --scope=staged --service=ok
test_artifacts "$NUM_ARTS"
test_run build Test --no-build

# Verify staged outputs can be uploaded for another revision,
# which `cache get --rev` then fetches instead of those of the head revision
OLD_REV="$(git rev-parse HEAD~1)"
test_run cache put-staged staging --scope=staged --rev="$OLD_REV"
test_exp -f "$STORE_DIR/r0/staged/$OLD_REV.jsonl"
test_cmd rm -rf .lake/build "$CACHE_DIR"
test_out "for revision $OLD_REV" cache get --scope=staged --service=ok --rev="$OLD_REV"
test_artifacts "$NUM_ARTS"
test_run build Test --no-build
