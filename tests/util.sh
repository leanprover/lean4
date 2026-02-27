set -eu

DIFF="diff -au --strip-trailing-cr --color=always"
ulimit -S -s ${TEST_STACK_SIZE:-8192}

function fail {
  echo "$1"
  exit 1
}

function fail_if_success {
  if "$@"; then
    fail "unexpected success: $*"
  fi
}

function source_init {
  if [[ -f "$1.init.sh" ]]; then
    source "$1.init.sh"
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

function exec_capture {
  # backtraces are system-specific, strip them (might be captured in `#guard_msgs`)
  ERROR=0
  LEAN_BACKTRACE=0 "${@:2}" > "$1.out.produced" 2>&1 || ERROR="$?"
  echo "$ERROR" > "$1.exit.produced"
}

function check_exit {
  if [[ -f "$1.exit.expected" ]]; then
    EXPECTED="$(< "$1.exit.expected")"
  else
    EXPECTED="${2:-0}"
  fi

  ACTUAL="$(< "$1.exit.produced")"

  if [[ "$EXPECTED" == "nonzero" ]]; then
    if [[ "$ACTUAL" == "0" ]]; then
      fail "$1: Expected nonzero exit code, got 0"
    fi
  elif [[ "$EXPECTED" != "$ACTUAL" ]]; then
    fail "$1: Expected exit code $EXPECTED, got $ACTUAL"
  fi
}

function check_out {
  if [[ -f "$1.out.ignored" ]]; then
    echo "Output ignored, skipping check"
  elif [[ -f "$1.out.expected" ]]; then
    $DIFF -- "$1.out.expected" "$1.out.produced" || fail "$1: Unexpected output"
  else
    echo -n | $DIFF -- - "$1.out.produced" || fail "$1: Unexpected output"
  fi
}

# mvar suffixes like in `?m.123` are deterministic but prone to change on minor changes, so strip them
function normalize_mvar_suffixes {
  # Sed on macOS does not support \w.
  perl -p -i -e 's/(\?(\w|_\w+))\.[0-9]+/\1/g' "$1.out.produced"
}

# similarly, links to the language reference may have URL components depending on the toolchain, so normalize those
function normalize_reference_urls {
  perl -p -i -e 's#https://lean-lang\.org/doc/reference/(v?[0-9.]+(-rc[0-9]+)?|latest)#REFERENCE#g' "$1.out.produced"
}

function normalize_measurements {
  # Sed on macOS does not support \S.
  perl -p -i -e 's/^measurement: (\S+) \S+( \S+)?$/measurement: \1 .../' "$1.out.produced"
}

function extract_measurements {
  grep -E '^measurement: \S+ \S+( \S+)?$' "$1.out.produced" \
    | jq -R --arg topic "$2" 'split(" ") | { metric: "\($topic)//\(.[1])", value: .[2]|tonumber, unit: .[3] }' -c \
    >> "$1.measurements.jsonl"

  normalize_measurements "$1"
}

function set_stack_size_to_maximum {
  # On macOS, `ulimit -s unlimited` fails with `Operation not permitted` because
  # the hard limit is a certain number, not `unlimited` like on Linux.
  echo "Setting stack size to $(ulimit -H -s)"
  ulimit -s "$(ulimit -H -s)"
}
