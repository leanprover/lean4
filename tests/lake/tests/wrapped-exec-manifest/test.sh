#!/usr/bin/env bash
# Verifies that the manifest Lake writes when LAKE_WRAPPED_EXEC is set
# has the documented shape: required top-level fields, the lean source
# + setup.json + the transitive import-artifact closure in `inputs`,
# the argv-named outputs plus module-system companions in `outputs`.
#
# Strategy: point the env var at a wrapper that captures each manifest
# (keyed by job_id) and then passes through to the real command, so the
# build proceeds through `Dep` (a module-system module) to `Onlymod`
# (a non-module importer of `Dep`) and we can inspect both manifests.
source ../common.sh

# These tests need the wrapper to actually be invoked: with a warm Lake
# artifact cache the modules are restored without any lean job running
# and no wrapper dispatch happens. Pin the cache off for hermeticity.
export LAKE_ARTIFACT_CACHE=false

chmod +x ./wrapper-capture.sh ./clean.sh
./clean.sh

CAPTURE_DIR="$PWD/manifests"
mkdir -p "$CAPTURE_DIR"
export CAPTURE_DIR
export LAKE_WRAPPED_EXEC="$PWD/wrapper-capture.sh"

test_run build

DEP_MANIFEST="$CAPTURE_DIR/wrappedExecManifest_Dep.json"
MOD_MANIFEST="$CAPTURE_DIR/wrappedExecManifest_Onlymod.json"

for m in "$DEP_MANIFEST" "$MOD_MANIFEST"; do
  [[ -s "$m" ]] || { echo "FAILURE: wrapper did not capture $m"; ls "$CAPTURE_DIR"; exit 1; }
done

# Pretty-print the manifest under scrutiny if anything below fails.
# Quiet on the success path so CI logs stay clean.
fail() {
  echo "FAILURE: $1"
  echo "Manifest ($M):"
  jq . "$M"
  exit 1
}

assert_jq_true() {
  local description="$1" expr="$2"
  jq -e "$expr" "$M" > /dev/null || fail "$description"
}

assert_inputs_endswith() {
  assert_jq_true "manifest.inputs has no entry ending with '$1'" \
    "[.inputs[] | select(endswith(\"$1\"))] | length > 0"
}

assert_outputs_endswith() {
  assert_jq_true "manifest.outputs has no entry ending with '$1'" \
    "[.outputs[] | select(endswith(\"$1\"))] | length > 0"
}

# --- shape assertions, common to both manifests ---

check_shape() {
  M="$1"
  local cmdname="${2:-lean}"
  # The manifest schema is exactly these fields — the spawn recipe plus
  # the declared I/O sets. Pin the full key set so any schema change has
  # to be made consciously (and bump schema_version).
  assert_jq_true "manifest key set is not the documented v1 schema" '
    keys == ["args", "cmd", "cwd", "env", "inputs", "job_id", "outputs", "schema_version"]
  '
  assert_jq_true "schema_version != 1" '.schema_version == 1'
  assert_jq_true "manifest.env does not set LEAN_PATH" '.env | has("LEAN_PATH")'
  local cmd
  cmd=$(jq -r '.cmd' "$M")
  [[ "$cmd" == *"/$cmdname" || "$cmd" == "$cmdname" ]] \
    || fail "cmd = '$cmd' does not look like a $cmdname binary"
  # Sandbox wrappers compute their redirect table as `outputs ∩ args`:
  # every output path named in argv must appear in `outputs` as a
  # byte-identical string.
  assert_jq_true "an argv-named output is missing from outputs (byte-identity broken)" '
    .outputs as $outs
    | [.args as $a | range(0; $a|length)
       | select($a[.] == "-o" or $a[.] == "-i" or $a[.] == "-c" or $a[.] == "-b")
       | $a[. + 1]]
    | all(. as $p | $outs | index($p) != null)
  '
}

check_shape "$DEP_MANIFEST"
check_shape "$MOD_MANIFEST"

# --- Dep (module-system module): companion outputs ---

M="$DEP_MANIFEST"
assert_jq_true "job_id != wrappedExecManifest_Dep" '.job_id == "wrappedExecManifest_Dep"'
assert_inputs_endswith 'Dep.lean'
assert_inputs_endswith '.setup.json'
assert_outputs_endswith 'Dep.olean'
assert_outputs_endswith 'Dep.ilean'
# Module-system companions lean derives from the `-o` path; they never
# appear in argv but a wrapper must know to ship/relocate them.
assert_outputs_endswith 'Dep.olean.server'
assert_outputs_endswith 'Dep.olean.private'
assert_outputs_endswith 'Dep.ir'

# --- Onlymod (imports Dep): transitive import closure in inputs ---

M="$MOD_MANIFEST"
assert_jq_true "job_id != wrappedExecManifest_Onlymod" '.job_id == "wrappedExecManifest_Onlymod"'
assert_inputs_endswith 'Onlymod.lean'
assert_inputs_endswith '.setup.json'
assert_outputs_endswith 'Onlymod.olean'
assert_outputs_endswith 'Onlymod.ilean'
# The full artifact set of the imported module must be declared: lean's
# loader may follow non-exported references, so the closure contributes
# `allArts` (olean + ir + olean.server + olean.private) per module-system
# import, not just the exported view.
assert_inputs_endswith 'Dep.olean'
assert_inputs_endswith 'Dep.ir'
assert_inputs_endswith 'Dep.olean.server'
assert_inputs_endswith 'Dep.olean.private'
# args must include the source-file path that appears in inputs (i.e.
# `lean` is being asked to compile what we declared).
src=$(jq -r '.inputs[] | select(endswith("Onlymod.lean"))' "$M")
assert_jq_true "manifest.args does not include the source file" \
  ".args | any(. == \"$src\")"

# --- Postponed (compiler.postponeCompile): split lean/leanir jobs ---

test_run build Postponed

PP_MANIFEST="$CAPTURE_DIR/wrappedExecManifest_Postponed.json"
IR_MANIFEST="$CAPTURE_DIR/wrappedExecManifest_Postponed:leanir.json"
for m in "$PP_MANIFEST" "$IR_MANIFEST"; do
  [[ -s "$m" ]] || { echo "FAILURE: wrapper did not capture $m"; ls "$CAPTURE_DIR"; exit 1; }
done

check_shape "$PP_MANIFEST"
check_shape "$IR_MANIFEST" leanir

# The lean job defers .ir/.c to leanir; its outputs must say so.
M="$PP_MANIFEST"
assert_outputs_endswith 'Postponed.olean'
assert_outputs_endswith 'Postponed.olean.server'
assert_outputs_endswith 'Postponed.olean.private'
assert_jq_true "lean job in postpone mode must not declare the deferred .ir/.c" '
  [.outputs[] | select(endswith("Postponed.ir") or endswith("Postponed.c"))] | length == 0
'

# The leanir job produces exactly the deferred outputs, reading the
# setup file and the artifacts the lean step produced.
M="$IR_MANIFEST"
assert_jq_true "job_id != wrappedExecManifest_Postponed:leanir" \
  '.job_id == "wrappedExecManifest_Postponed:leanir"'
assert_outputs_endswith 'Postponed.ir'
assert_outputs_endswith 'Postponed.c'
assert_jq_true "leanir job must declare exactly the .ir and .c outputs" '.outputs | length == 2'
assert_inputs_endswith '.setup.json'
assert_inputs_endswith 'Postponed.olean'
assert_inputs_endswith 'Postponed.olean.private'

echo "wrapped-exec manifest: shape checks pass."
./clean.sh
