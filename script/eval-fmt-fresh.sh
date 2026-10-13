#!/usr/bin/env bash
#
# Evaluate a change to the auto-formatter by formatting core twice from the same
# unformatted input and diffing the two results.
#
# This is the layout-preserving variant of `scripts/eval-fmt.sh`. That script
# chains its two runs: the second one formats the output of the first, so it
# sees core as laid out by the baseline formatter rather than as laid out in the
# repository. Formatter changes that depend on the layout of their input -- e.g.
# anything that inspects whether a node was already on a single line -- are
# therefore evaluated against the wrong input there. (The two scripts agree once
# core is a fixpoint of the baseline formatter, since then the baseline run is a
# no-op.) Here both runs get the exact same input, so the delta is the true
# difference between the two formatters on core. Both scripts do the same two
# builds and two formatter runs.
#
# Given a jj change F that contains the formatter changes you want to evaluate,
# this script:
#   1. Creates a new change on top of F's parent (F without the formatter change).
#   2. Builds Lean there and formats core                      -> baseline run.
#   3. Builds Lean at F (with the formatter change).
#   4. Creates a sibling change, again on top of F's parent, and formats core
#      there with F's build                                    -> evaluation run.
#   5. Creates a change on top of the baseline run holding the evaluation run's
#      content.
#
# The final change (@) then contains ONLY the delta between the two runs, i.e.
# exactly what your change does to core.
#
# A run formats each `.lean` file under `src/` in place with a separate `lean`
# process that runs `tests/fmt/run_test.lean` from the revision that was built.
#
# Usage:
#   scripts/eval-fmt-fresh.sh [FMT_REV] [BASE_REV]
#
#   FMT_REV    Revision of the change to evaluate. Default: @- (previous change).
#   BASE_REV   Revision to compare against, i.e. the baseline the formatter is
#              run on without FMT_REV's change. Default: the parent of FMT_REV.
#
# Environment:
#   LEAN_NUM_THREADS   Files to format in parallel, and threads per file.
#                      Default: 40.
#   FMT_EVAL_LOG_DIR   Where to write logs. Default: `build/fmt-eval-logs`
#                      (inside `build/`, which is ignored, so the logs are not
#                      snapshotted into the changes this script creates).

set -euo pipefail

FMT_REV="${1:-@-}"
BASE_REV="${2:-}"
: "${LEAN_NUM_THREADS:=40}"
export LEAN_NUM_THREADS

ROOT=$(jj root)
NPROC=$(command -v nproc >/dev/null && nproc || sysctl -n hw.logicalcpu)
STAGE1="$ROOT/build/release/stage1"
LEAN="$STAGE1/bin/lean"
# `lean` does not link Lake, so Lake's builtin formatters only register when
# Lake is loaded as a plugin.
case "$OSTYPE" in
  darwin*) LAKE_PLUGIN="$STAGE1/lib/lean/libLake_shared.dylib" ;;
  *)       LAKE_PLUGIN="$STAGE1/lib/lean/libLake_shared.so" ;;
esac
export LEAN LAKE_PLUGIN
RUNNER=tests/fmt/run_test.lean

LOG_DIR="${FMT_EVAL_LOG_DIR:-$ROOT/build/fmt-eval-logs}/$(date +%Y%m%d-%H%M%S)"
mkdir -p "$LOG_DIR"

# Resolve stable change IDs up front, because @-relative revsets shift as we
# create new changes below.
resolve() { jj log --no-graph -r "$1" -T 'change_id.short()'; }

FMT_CHANGE=$(resolve "$FMT_REV")
BASE_CHANGE=$(resolve "${BASE_REV:-${FMT_CHANGE}-}")

# Taken from the built revision so that the runner matches its formatter API.
# The working copy of the evaluation run has the baseline's runner.
jj file show -r "$BASE_CHANGE" "$RUNNER" > "$LOG_DIR/baseline-runner.lean"
jj file show -r "$FMT_CHANGE" "$RUNNER" > "$LOG_DIR/eval-runner.lean"

build() {
  local log="$LOG_DIR/$1-build.log"
  echo ">>> building Lean (make -j$NPROC -C $ROOT/build/release), logging to $log"
  make -j"$NPROC" -C "$ROOT/build/release" 2>&1 | tee "$log"
}

# Usage: fmt_file RUNNER TOTAL INDEX FILE
# Formats FILE in place. A file that fails to format is left unchanged.
fmt_file() {
  local runner=$1 total=$2 i=$3 file=$4
  local out rc=0
  out=$(mktemp)
  "$LEAN" -Dlinter.all=false --plugin="$LAKE_PLUGIN" --run "$runner" "$file" \
    > "$out" 2> "$out.err" || rc=$?
  if [ "$rc" -eq 0 ]; then
    cat "$out" > "$file"
    echo "Formatted $file ($i/$total)"
  else
    {
      echo "Failed to format $file ($i/$total)"
      echo "  exit code $rc"
      sed 's/^/  /' "$out.err"
    } >&2
  fi
  rm -f "$out" "$out.err"
}
export -f fmt_file

run_fmt() {
  local runner="$LOG_DIR/$1-runner.lean"
  local log="$LOG_DIR/$1-fmt.log"
  local failedLog="$LOG_DIR/$1-fmt-failures.log"
  local files
  mapfile -t files < <(cd "$ROOT" && jj file list 'glob:src/**/*.lean')
  echo ">>> formatting ${#files[@]} files, $LEAN_NUM_THREADS in parallel, with $runner"
  echo ">>> logging to $log"
  local rc=0
  (
    cd "$ROOT"
    for i in "${!files[@]}"; do printf '%s\0%s\0' "$((i + 1))" "${files[i]}"; done |
      xargs -0 -n 2 -P "$LEAN_NUM_THREADS" bash -c 'fmt_file "$@"' _ "$runner" "${#files[@]}"
  ) 2>&1 | tee "$log" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo ">>> formatter driver exited with status $rc (continuing)"
  fi
  # A file that fails to format is left unchanged, which shows up in the
  # delta as a spurious whole-file revert of the other run's formatting. These
  # failures are per-run, so both runs need to be checked.
  grep '^Failed to format ' "$log" > "$failedLog" || true
  local failedCount
  failedCount=$(( $(wc -l < "$failedLog") ))
  if [ "$failedCount" -gt 0 ]; then
    echo ">>> WARNING: $failedCount file(s) failed to format and were left unchanged:"
    sed 's/^/      /' "$failedLog"
    echo ">>> They pollute the delta; see $failedLog"
  else
    echo ">>> all files formatted successfully"
  fi
}

echo "=== Evaluating formatter change $FMT_CHANGE (parent: $BASE_CHANGE) ==="
echo "=== Logs: $LOG_DIR ==="

# --- Baseline: format core WITHOUT the formatter change -----------------------
echo
echo "=== [1/2] Baseline run (without $FMT_CHANGE) ==="
jj new "$BASE_CHANGE" -m "fmt baseline: core formatted without $FMT_CHANGE"
BASELINE_RUN=$(resolve @)
build baseline
run_fmt baseline
echo ">>> baseline run recorded in change $BASELINE_RUN"

# --- Evaluation: format the same input WITH the formatter change --------------
echo
echo "=== [2/2] Evaluation run (with $FMT_CHANGE) ==="
# Build the binary WITH the formatter change; the resulting on-disk binary is
# what we use for the second run.
jj edit "$FMT_CHANGE"
build eval
# Sibling of the baseline run rather than a child, so that both runs format
# core exactly as it is committed in $BASE_CHANGE.
jj new "$BASE_CHANGE" -m "fmt eval: core formatted with $FMT_CHANGE"
EVAL_RUN=$(resolve @)
run_fmt eval
echo ">>> evaluation run recorded in change $EVAL_RUN"

# --- Delta --------------------------------------------------------------------
# A change parented on the baseline run but holding the evaluation run's content,
# so that its own diff is precisely the difference between the two runs.
jj new "$BASELINE_RUN" -m "fmt eval: delta from $FMT_CHANGE"
DELTA_RUN=$(resolve @)
jj restore --from "$EVAL_RUN"

{
  echo
  echo "=== Done ==="
  echo "Baseline run:   $BASELINE_RUN"
  echo "Evaluation run: $EVAL_RUN"
  echo "Delta:          $DELTA_RUN (current change @)"
  echo "Logs:           $LOG_DIR"

  # Files that only one of the two runs failed on are unformatted on that side,
  # so their whole-file diff is an artifact rather than an effect of the change.
  sed 's/^Failed to format //; s| ([0-9]*/[0-9]*)$||' "$LOG_DIR"/*-fmt-failures.log \
    | sort -u > "$LOG_DIR/all-failures.log"
  if [ -s "$LOG_DIR/all-failures.log" ]; then
    echo
    echo "WARNING: files that failed to format in at least one run, and whose diff in"
    echo "the delta is therefore an artifact rather than an effect of $FMT_CHANGE:"
    sed 's/^/  /' "$LOG_DIR/all-failures.log"
    echo "Reformat them individually with each build, or rerun the script, before"
    echo "reading the delta."
  fi

  echo
  echo "The delta produced by $FMT_CHANGE:"
  jj diff --stat -r @
  echo
  echo "Full effect of the updated formatter on core:"
  echo "  jj diff --from $BASE_CHANGE --to $EVAL_RUN"
} 2>&1 | tee "$LOG_DIR/summary.log"
