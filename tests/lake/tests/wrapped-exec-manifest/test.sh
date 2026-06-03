#!/usr/bin/env bash
# Verifies that the manifest Lake writes when LAKE_WRAPPED_EXEC is set
# has the documented shape: required top-level fields, the lean source
# + setup.json in `inputs`, the expected oleans in `outputs`, etc.
#
# Strategy: point the env var at a wrapper that captures the manifest
# and exits non-zero. The build fails — that's expected — but we now
# have the manifest on disk and can inspect it.
source ../common.sh

chmod +x ./wrapper-capture.sh ./clean.sh
./clean.sh

CAPTURED_MANIFEST="$PWD/manifest.json"
export CAPTURED_MANIFEST
export LAKE_WRAPPED_EXEC="$PWD/wrapper-capture.sh"

# Build will fail (wrapper exits 71); ignore Lake's exit. We only need
# the captured manifest to exist.
"$LAKE" build || true

if [[ ! -s manifest.json ]]; then
  echo "FAILURE: wrapper did not capture a manifest"
  exit 1
fi

# Pretty-print the captured manifest if anything below fails. Quiet
# on the success path so CI logs stay clean.
fail() {
  echo "FAILURE: $1"
  echo "Captured manifest:"
  jq . manifest.json
  exit 1
}

assert_field() {
  jq -e "has(\"$1\")" manifest.json > /dev/null \
    || fail "manifest missing top-level field '$1'"
}

assert_jq_true() {
  local description="$1" expr="$2"
  jq -e "$expr" manifest.json > /dev/null \
    || fail "$description"
}

assert_inputs_endswith() {
  jq -e --arg s "$1" '[.inputs[] | select(endswith($s))] | length > 0' manifest.json > /dev/null \
    || fail "manifest.inputs has no entry ending with '$1'"
}

assert_outputs_endswith() {
  jq -e --arg s "$1" '[.outputs[] | select(endswith($s))] | length > 0' manifest.json > /dev/null \
    || fail "manifest.outputs has no entry ending with '$1'"
}

assert_field_eq() {
  local field="$1" expected="$2"
  local actual
  actual=$(jq -r ".$field" manifest.json)
  [[ "$actual" == "$expected" ]] \
    || fail "manifest.$field = '$actual', expected '$expected'"
}

assert_field_nonempty() {
  local v
  v=$(jq -r ".$1" manifest.json)
  [[ -n "$v" && "$v" != "null" ]] \
    || fail "manifest.$1 is empty/null"
}

# --- assertions on the manifest shape ---

for f in job_id cmd args env cwd inputs outputs workspace lake_home toolchain toolchain_root; do
  assert_field "$f"
done

# job_id derives from `{pkg.baseName}_{mod.name}`.
assert_field_eq job_id "wrappedExecManifest_Onlymod"

# cmd should be a `lean` binary (path ending in /lean or the bare name).
cmd=$(jq -r '.cmd' manifest.json)
[[ "$cmd" == *"/lean" || "$cmd" == "lean" ]] \
  || fail "cmd = '$cmd' does not look like a lean binary"

# inputs: the source file + the per-module setup.json must both appear.
assert_inputs_endswith 'Onlymod.lean'
assert_inputs_endswith '.setup.json'

# outputs: the olean + ilean for this module must both appear.
assert_outputs_endswith 'Onlymod.olean'
assert_outputs_endswith 'Onlymod.ilean'

# args must include the source-file path that appears in inputs (i.e.
# `lean` is being asked to compile what we declared).
src=$(jq -r '.inputs[] | select(endswith("Onlymod.lean"))' manifest.json)
assert_jq_true "manifest.args does not include the source file" \
  ".args | any(. == \"$src\")"

# env should at least set LEAN_PATH.
assert_jq_true "manifest.env does not set LEAN_PATH" '.env | has("LEAN_PATH")'

# The four Lake roots Lake hands the wrapper must all be populated.
for k in workspace lake_home toolchain toolchain_root; do
  assert_field_nonempty "$k"
done

echo "wrapped-exec manifest: shape checks pass."
./clean.sh
