set -eo pipefail

ulimit -S -s ${TEST_STACK_SIZE:-8192}

DIFF="diff -au --strip-trailing-cr --color=always"

# Temporary directory to store unnamed output files
TMP_DIR="$(mktemp --tmpdir --directory lean4-test-suite.XXXXXXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

function fail {
  echo "TEST FAILED: $1"
  exit 1
}

function check_exit_is_success {
  if [[ $EXIT != 0 ]]; then
    fail "Expected command to succeed, got exit code $EXIT"
  fi
}

function check_exit_is_fail {
  if [[ $EXIT == 0 ]]; then
    fail "Expected command to fail, got exit code $EXIT"
  fi
}

function check_exit_is {
  if [[ $1 == "nonzero" ]]; then
    check_exit_is_fail
  elif [[ $EXIT != $1 ]]; then
    fail "Expected exit code $1, got exit code $EXIT"
  fi
}

function check_out_contains {
  if ! grep -Fq "$1" "$CAPTURED.out.produced"; then
    fail "Expected output to contain '$1'"
  fi
}

function check_out_matches {
  if ! grep -Eq "$1" "$CAPTURED.out.produced"; then
    fail "Expected output to match regex '$1'"
  fi
}

function check_out_file {
  if [[ -f "$CAPTURED.out.ignored" ]]; then
    echo "Output ignored, skipping check"
  elif [[ -f "$CAPTURED.out.expected" ]]; then
    $DIFF -- "$CAPTURED.out.expected" "$CAPTURED.out.produced" || fail "Unexpected output"
  else
    echo -n | $DIFF -- - "$CAPTURED.out.produced" || fail "Unexpected output"
  fi
}

# Run a command.
# Sets $EXIT to the exit code.
function run_only {
  EXIT=0; (set -x; "${@}") || EXIT="$?"
}

# Run a command, failing if the command fails.
# Sets $EXIT to the exit code.
function run {
  run_only "${@}"
  check_exit_is_success
}

# Run a command, failing if the command succeeds.
# Sets $EXIT to the exit code.
function run_fail {
  run_only "${@}"
  check_exit_is_fail
}

# Run a command, failing if the exit code does not match the expected value.
# Sets $EXIT to the exit code.
function run_exit {
  EXPECTED="$1"; shift
  run_only "${@}"
  check_exit_is "$EXPECTED"
}

# Run a command, capturing its output.
# The first argument specifies the output file path.
# If it is empty, a temporary file is used.
# Sets $EXIT to the exit code and $CAPTURED to the output file path.
function capture_only {
  # No need to mktemp the file to prevent collisions during parallel test runs
  # since $TMP_DIR is already specific to this test run.
  CAPTURED="${1:-"$TMP_DIR/tmp"}"; shift
  EXIT=0; (set -x; "${@}" > "$CAPTURED.out.produced" 2>&1) || EXIT="$?"
  cat "$CAPTURED.out.produced"
}

# Run a command, capturing its output and failing if the command fails.
# Sets $EXIT to the exit code and $CAPTURED to the output file path.
function capture {
  capture_only "" "${@}"
  check_exit_is_success
}

# Run a command, capturing its output and failing if the command succeeds.
# Sets $EXIT to the exit code and $CAPTURED to the output file path.
function capture_fail {
  capture_only "" "${@}"
  check_exit_is_fail
}

# Run a command, capturing its output and failing if the command does not match the expected exit code.
# Sets $EXIT to the exit code and $CAPTURED to the output file path.
function capture_exit {
  EXPECTED="$1"; shift
  capture_only "" "${@}"
  check_exit_is "$EXPECTED"
}

function source_init {
  if [[ -f "$1.init.sh" ]]; then
    source "$1.init.sh"
  fi
}

# Append `--incr-load=...` to TEST_LEAN_ARGS if `$1`'s parsed header matches
# one of the prebuilt snapshots exactly. The Lean snapshot is built from the
# bytes `import Lean\n`; the Init snapshot from empty input. The file must
# match byte-for-byte at the header level; if it doesn't, the loader takes
# the slow path which costs the snapshot env *plus* a fresh import.
function maybe_use_lean_header_snapshot {
  [[ "${LEAN_HEADER_SNAPSHOTS:-}" == 0 ]] && return
  [[ -z "${LEAN_HEADER_SNAPSHOTS:-}" && -z "${TEST_CTEST:-}" ]] && return
  # File kinds that are not supported yet; we should add `module` snapshots when
  # we have ported a significant number of tests
  grep -qE '^(module|prelude)$' "$1" && return
  local snap=
  if awk 'NR==1 { if ($0 != "import Lean") exit 1; n=1; next }
          /^import / { exit 1 }
          END { if (n != 1) exit 1 }' "$1"; then
    snap=${LEAN_HEADER_SNAPSHOT_LEAN:-}
  elif ! grep -qE '^import ' "$1"; then
    snap=${LEAN_HEADER_SNAPSHOT_INIT:-}
  fi
  if [[ -n "$snap" ]]; then
    TEST_LEAN_ARGS+=("--incr-load=$snap")
  fi
}

function run_before {
  if [[ -f "$1.before.sh" ]]; then
    bash -- "$1.before.sh" || fail "$1.before.sh failed"
  fi
}

function run_after {
  if [[ -f "$1.after.sh" ]]; then
    bash -- "$1.after.sh" || fail "$1.after.sh failed"
  fi
}

# mvar suffixes like in `?m.123` are deterministic but prone to change on minor changes, so strip them
function normalize_mvar_suffixes {
  # Sed on macOS does not support \w.
  perl -p -i -e 's/(\?(\w|_\w+))\.[0-9]+/\1/g' "$CAPTURED.out.produced"
}

# similarly, links to the language reference may have URL components depending on the toolchain, so normalize those
function normalize_reference_urls {
  perl -p -i -e 's#https://lean-lang\.org/doc/reference/(v?[0-9.]+(-rc[0-9]+)?|latest)#REFERENCE#g' "$CAPTURED.out.produced"
}

function normalize_measurements {
  # Sed on macOS does not support \S.
  perl -p -i -e 's/^measurement: (\S+) \S+( \S+)?$/measurement: \1 .../' "$CAPTURED.out.produced"
}

function extract_measurements {
  set +o pipefail # grep will exit with 1 if there are no matches
  grep -E '^measurement: \S+ \S+( \S+)?$' "$CAPTURED.out.produced" \
    | jq -R --arg topic "$1" 'split(" ") | { metric: "\($topic)//\(.[1])", value: .[2]|tonumber, unit: .[3] }' -c \
    >> "$CAPTURED.measurements.jsonl"
  set -o pipefail

  normalize_measurements "$CAPTURED"
}

function set_stack_size_to_maximum {
  # On macOS, `ulimit -s unlimited` fails with `Operation not permitted` because
  # the hard limit is a certain number, not `unlimited` like on Linux.
  echo "Setting stack size to $(ulimit -H -s)"
  ulimit -s "$(ulimit -H -s)"
}
