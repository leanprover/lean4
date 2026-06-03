#!/usr/bin/env bash
# Verifies that the manifest Lake writes when LAKE_WRAPPED_EXEC is set
# has the documented shape: required top-level fields, a Lean source +
# setup.json in `inputs`, and an .olean in `outputs`.
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
echo "Captured manifest:"
jq . manifest.json

# --- assertions on the manifest shape ---

assert_field() {
  local key="$1"
  if ! jq -e "has(\"$key\")" manifest.json > /dev/null; then
    echo "FAILURE: manifest missing top-level field '$key'"
    exit 1
  fi
}

assert_inputs_endswith() {
  local suffix="$1"
  if ! jq -e --arg s "$suffix" '[.inputs[] | select(endswith($s))] | length > 0' manifest.json > /dev/null; then
    echo "FAILURE: manifest.inputs has no entry ending with '$suffix'"
    exit 1
  fi
}

assert_outputs_endswith() {
  local suffix="$1"
  if ! jq -e --arg s "$suffix" '[.outputs[] | select(endswith($s))] | length > 0' manifest.json > /dev/null; then
    echo "FAILURE: manifest.outputs has no entry ending with '$suffix'"
    exit 1
  fi
}

for f in job_id cmd args env cwd inputs outputs workspace lake_home toolchain toolchain_root; do
  assert_field "$f"
done

# job_id derives from `{pkg.baseName}_{mod.name}` — for this fixture, expect "wrappedExecManifest_Onlymod".
expected_job_id="wrappedExecManifest_Onlymod"
actual_job_id=$(jq -r '.job_id' manifest.json)
if [[ "$actual_job_id" != "$expected_job_id" ]]; then
  echo "FAILURE: job_id = '$actual_job_id', expected '$expected_job_id'"
  exit 1
fi

# cmd should end in '/lean'.
cmd=$(jq -r '.cmd' manifest.json)
if [[ "$cmd" != *"/lean" && "$cmd" != "lean" ]]; then
  echo "FAILURE: cmd = '$cmd' does not look like a lean binary"
  exit 1
fi

# inputs should contain the source file and the setup.json.
assert_inputs_endswith 'Onlymod.lean'
assert_inputs_endswith '.setup.json'

# outputs should contain the .olean + .ilean for Onlymod.
assert_outputs_endswith 'Onlymod.olean'
assert_outputs_endswith 'Onlymod.ilean'

# args should include the source file path that appears in inputs.
src=$(jq -r '.inputs[] | select(endswith("Onlymod.lean"))' manifest.json)
if ! jq -e --arg s "$src" '.args | any(. == $s)' manifest.json > /dev/null; then
  echo "FAILURE: manifest.args does not include the source file"
  exit 1
fi

# env should at least set LEAN_PATH.
if ! jq -e '.env | has("LEAN_PATH")' manifest.json > /dev/null; then
  echo "FAILURE: manifest.env does not set LEAN_PATH"
  exit 1
fi

# workspace + lake_home + toolchain + toolchain_root should be non-empty absolute paths.
for k in workspace lake_home toolchain toolchain_root; do
  v=$(jq -r ".$k" manifest.json)
  if [[ -z "$v" || "$v" == "null" ]]; then
    echo "FAILURE: manifest.$k is empty/null"
    exit 1
  fi
done

echo "wrapped-exec manifest: shape checks pass."

./clean.sh
