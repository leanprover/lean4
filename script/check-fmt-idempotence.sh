#!/usr/bin/env bash
#
# Check that the auto-formatter is idempotent on core by formatting core twice,
# with the second run formatting the output of the first.
#
# Given a jj change F that contains the formatter to check, this script:
#   1. Creates a new change on top of F.
#   2. Builds Lean there and formats core                      -> first run.
#   3. Creates a change on top of the first run and formats core there again
#      with the same build                                     -> second run.
#
# The final change (@) then contains ONLY what the second run changed. It is
# empty if and only if the formatter is idempotent on core.
#
# The second run formats only the files that the first run formatted
# successfully. A file that fails in the first run is left unchanged, so the
# second run on it would be a first formatting, not a check of idempotence.
#
# A run formats each `.lean` file under `src/` in place with a separate `lean`
# process that runs `tests/fmt/run_test.lean` from F.
#
# Usage:
#   scripts/check-fmt-idempotence.sh [FMT_REV]
#
#   FMT_REV    Revision whose formatter is checked, on core as committed in
#              FMT_REV. Default: @- (previous change).
#
# Environment:
#   LEAN_NUM_THREADS   Files to format in parallel, and threads per file.
#                      Default: 40.
#   FMT_EVAL_LOG_DIR   Where to write logs. Default: `build/fmt-eval-logs`
#                      (inside `build/`, which is ignored, so the logs are not
#                      snapshotted into the changes this script creates).
#
# Exits with status 1 if the second run changed core.

set -euo pipefail

FMT_REV="${1:-@-}"
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

LOG_DIR="${FMT_EVAL_LOG_DIR:-$ROOT/build/fmt-eval-logs}/idempotence-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$LOG_DIR"

# Resolve stable change IDs up front, because @-relative revsets shift as we
# create new changes below.
resolve() { jj log --no-graph -r "$1" -T 'change_id.short()'; }

FMT_CHANGE=$(resolve "$FMT_REV")

# Copied out of the working copy so that neither run can format the runner.
jj file show -r "$FMT_CHANGE" "$RUNNER" > "$LOG_DIR/runner.lean"

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

# Usage: run_fmt NAME FILE_LIST
# Formats each file in FILE_LIST (one path per line, relative to $ROOT) and
# writes the files that formatted successfully to $LOG_DIR/NAME-formatted.txt.
run_fmt() {
  local runner="$LOG_DIR/runner.lean"
  local log="$LOG_DIR/$1-fmt.log"
  local failedLog="$LOG_DIR/$1-fmt-failures.log"
  local files
  mapfile -t files < "$2"
  : > "$failedLog"
  if [ "${#files[@]}" -eq 0 ]; then
    echo ">>> no files to format"
    : > "$LOG_DIR/$1-formatted.txt"
    return
  fi
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
  sed -n 's/^Formatted \(.*\) ([0-9]*\/[0-9]*)$/\1/p' "$log" | sort > "$LOG_DIR/$1-formatted.txt"
  grep '^Failed to format ' "$log" > "$failedLog" || true
  local failedCount
  failedCount=$(( $(wc -l < "$failedLog") ))
  if [ "$failedCount" -gt 0 ]; then
    echo ">>> WARNING: $failedCount file(s) failed to format and were left unchanged:"
    sed 's/^/      /' "$failedLog"
    echo ">>> see $failedLog"
  else
    echo ">>> all files formatted successfully"
  fi
}

echo "=== Checking idempotence of the formatter in $FMT_CHANGE ==="
echo "=== Logs: $LOG_DIR ==="

# --- First run: format core as committed in FMT_CHANGE --------------------------
echo
echo "=== [1/2] First run ==="
jj new "$FMT_CHANGE" -m "fmt idempotence: core formatted once with $FMT_CHANGE"
FIRST_RUN=$(resolve @)
echo ">>> building Lean (make -j$NPROC -C $ROOT/build/release), logging to $LOG_DIR/build.log"
make -j"$NPROC" -C "$ROOT/build/release" 2>&1 | tee "$LOG_DIR/build.log"
(cd "$ROOT" && jj file list 'glob:src/**/*.lean') > "$LOG_DIR/first-input.txt"
run_fmt first "$LOG_DIR/first-input.txt"
echo ">>> first run recorded in change $FIRST_RUN"

# --- Second run: format the output of the first run with the same build ---------
echo
echo "=== [2/2] Second run ==="
jj new "$FIRST_RUN" -m "fmt idempotence: delta of formatting core twice with $FMT_CHANGE"
SECOND_RUN=$(resolve @)
run_fmt second "$LOG_DIR/first-formatted.txt"
echo ">>> second run recorded in change $SECOND_RUN"

{
  echo
  echo "=== Done ==="
  echo "First run:  $FIRST_RUN"
  echo "Second run: $SECOND_RUN (current change @)"
  echo "Logs:       $LOG_DIR"

  if [ -s "$LOG_DIR/first-fmt-failures.log" ]; then
    echo
    echo "NOTE: files that failed to format in the first run, and that this script"
    echo "therefore did not check for idempotence:"
    sed 's/^Failed to format //; s| ([0-9]*/[0-9]*)$||; s/^/  /' "$LOG_DIR/first-fmt-failures.log"
  fi

  # The first run formatted these files successfully, so the formatter rejects
  # its own output: a violation of idempotence that the delta does not show.
  if [ -s "$LOG_DIR/second-fmt-failures.log" ]; then
    echo
    echo "NOT IDEMPOTENT: files that the formatter cannot format again after the first"
    echo "run (details in $LOG_DIR/second-fmt-failures.log):"
    sed 's/^Failed to format //; s| ([0-9]*/[0-9]*)$||; s/^/  /' "$LOG_DIR/second-fmt-failures.log"
  fi

  echo
  if [ "$(jj log --no-graph -r "$SECOND_RUN" -T 'empty')" = true ]; then
    echo "The second run changed nothing."
  else
    echo "NOT IDEMPOTENT: the second run changed core:"
    jj diff --stat -r "$SECOND_RUN"
    echo
    echo "Full delta:"
    echo "  jj diff --git -r $SECOND_RUN"
  fi
} 2>&1 | tee "$LOG_DIR/summary.log"

if [ "$(jj log --no-graph -r "$SECOND_RUN" -T 'empty')" != true ] ||
   [ -s "$LOG_DIR/second-fmt-failures.log" ]; then
  exit 1
fi
