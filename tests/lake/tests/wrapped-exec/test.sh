#!/usr/bin/env bash
# Verifies the LAKE_WRAPPED_EXEC hook is inert under a passthrough wrapper:
# a build through `wrapper-passthrough.sh` must produce byte-identical
# artifacts to a build with the env var unset, and a follow-up rebuild
# (with the env var unset again) must be a no-op — exercising Lake's
# trace logic against wrapper-produced outputs.
source ../common.sh

# These tests need the wrapper to actually be invoked: with a warm Lake
# artifact cache the modules are restored without any lean job running
# and no wrapper dispatch happens. Pin the cache off for hermeticity.
export LAKE_ARTIFACT_CACHE=false

chmod +x ./wrapper-passthrough.sh ./clean.sh

# Hash every artifact Lake actually CONSULTS on rebuild — the four file
# kinds `lean` writes from a `lean_module` build of a Lean-side module
# (the `.c` and `.ir` are skipped: they go through a separate downstream
# `leanir` step, and Lake's trace logic keys off the olean/ilean/server/
# private set).
capture_sums() {
  ( cd .lake/build/lib/lean \
    && find . -type f \
        \( -name '*.olean' -o -name '*.ilean' \
        -o -name '*.olean.server' -o -name '*.olean.private' \) \
        -print0 \
    | sort -z \
    | xargs -0 shasum -a 256 )
}

# --- baseline: build with the hook OFF ---
./clean.sh
test_run build
capture_sums > unwrapped.sums

# --- same target under the passthrough wrapper ---
./clean.sh
LAKE_WRAPPED_EXEC="$PWD/wrapper-passthrough.sh" test_run build
capture_sums > wrapped.sums

# Both runs MUST produce the same artifacts.
if ! diff -u unwrapped.sums wrapped.sums; then
  echo "FAILURE: wrapped-exec passthrough produced different artifacts"
  exit 1
fi
echo "wrapped-exec passthrough: artifacts byte-identical to baseline."

# Follow-up rebuild with the env var unset should be a no-op — confirms
# the wrapper-produced trace sidecars are recognised as up-to-date by
# the unwrapped path. If wrapper outputs were stale or incomplete, lake
# would re-run a "Built X" job here.
"$LAKE" build > rebuild.out 2>&1
if grep -E '^✔ \[[0-9]+/[0-9]+\] Built ' rebuild.out > /dev/null; then
  echo "FAILURE: follow-up rebuild built modules — wrapper outputs not trace-equivalent"
  cat rebuild.out
  rm -f rebuild.out unwrapped.sums wrapped.sums produced.out
  exit 1
fi
echo "wrapped-exec follow-up rebuild: no-op as expected."

rm -f rebuild.out unwrapped.sums wrapped.sums produced.out
