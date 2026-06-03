#!/usr/bin/env bash
# Non-happy-path coverage for the wrapped-exec hook.
#
#   (1) Wrapper compile-failure propagation. Lake invokes a wrapper
#       that simulates a lean compile error (non-zero exit + recognisable
#       stderr line). Lake must exit non-zero and surface the stderr
#       verbatim, exactly as it would for a real lean failure.
#
#   (2) Wrapper binary not found, no temp-manifest leak. Lake invokes
#       a path that doesn't exist. Lake must (a) fail with a useful
#       error message, (b) not leak the per-job temp manifest — exercises
#       the cleanup-on-spawn-failure branch of runViaWrapper.
#
# Both subcases use a private TMPDIR so file counts aren't polluted by
# concurrent processes.
source ../common.sh

chmod +x ./wrapper-fail.sh ./clean.sh

# Helpers: each assertion reads as its actual claim, not its mechanism.
assert_contains() {
  local needle="$1" haystack="$2"
  echo "$haystack" | grep -q -- "$needle" \
    || { echo "FAILURE: expected output to contain '$needle'"; echo "$haystack"; exit 1; }
}

assert_not_contains() {
  local needle="$1" haystack="$2"
  ! echo "$haystack" | grep -q -- "$needle" \
    || { echo "FAILURE: output unexpectedly contained '$needle'"; echo "$haystack"; exit 1; }
}

reset_state() {
  ./clean.sh
  mkdir -p tmp
}

reset_state
export TMPDIR="$PWD/tmp"

# ----------------------------------------------------------------------
# (1) Compile-failure propagation
# ----------------------------------------------------------------------
echo "--- (1) wrapper compile-failure propagation ---"
out=$(LAKE_WRAPPED_EXEC="$PWD/wrapper-fail.sh" "$LAKE" build 2>&1 || true)

assert_not_contains '^Build completed successfully' "$out"
assert_contains 'simulated compile failure from wrapper' "$out"
assert_contains 'Lean exited with code 1'              "$out"
echo "(1) PASS: wrapper exit + stderr propagated correctly."

# ----------------------------------------------------------------------
# (2) Wrapper not found, no manifest leak
# ----------------------------------------------------------------------
reset_state
echo "--- (2) wrapper-not-found, manifest cleanup ---"

count_temp_manifests() {
  find "$TMPDIR" -maxdepth 1 -name 'lake-wrapped-*' 2>/dev/null | wc -l | tr -d ' '
}
before=$(count_temp_manifests)

out=$(LAKE_WRAPPED_EXEC="/nonexistent/wrapper-path" "$LAKE" build 2>&1 || true)

assert_not_contains '^Build completed successfully' "$out"
# The exact spawn-failure error surface is platform-dependent; accept
# any of the typical wordings.
echo "$out" | grep -qE "could not execute external process|No such file|Lean exited with code" \
  || { echo "FAILURE: expected a useful error about the missing wrapper"; echo "$out"; exit 1; }

after=$(count_temp_manifests)
[[ "$before" == "$after" ]] \
  || { echo "FAILURE: temp manifest leak: $before → $after files in $TMPDIR"; find "$TMPDIR" -maxdepth 1 -name 'lake-wrapped-*'; exit 1; }
echo "(2) PASS: useful error reported, no manifest leak ($before manifests in $TMPDIR before+after)."

./clean.sh
