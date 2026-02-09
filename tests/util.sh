set -eu

DIFF="diff -u --color=always"

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
    $DIFF -- "$1.exit.expected" "$1.exit.produced" || fail "$1: Unexpected exit code"
  else
    echo "${2:-0}" | $DIFF -- - "$1.exit.produced" || fail "$1: Unexpected exit code"
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
  sed -i -E 's/(\?(\w|_\w+))\.[0-9]+/\1/g' "$1.out.produced"
}

# similarly, links to the language reference may have URL components depending on the toolchain, so normalize those
function normalize_reference_urls {
  sed -i -E 's#https://lean-lang\.org/doc/reference/(v?[0-9.]+(-rc[0-9]+)?|latest)#REFERENCE#g' "$1.out.produced"
}

function normalize_measurements {
  sed -i -E 's/^measurement: (\S+) \S+( \S+)?$/measurement: \1 .../' "$1.out.produced"
}

function extract_measurements {
  grep -E '^measurement: \S+ \S+( \S+)?$' "$1.out.produced" \
    | jq -R --arg topic "$2" 'split(" ") | { metric: "\($topic)//\(.[1])", value: .[2]|tonumber, unit: .[3] }' -c \
    >> "$1.measurements.jsonl"

  normalize_measurements "$1"
}
