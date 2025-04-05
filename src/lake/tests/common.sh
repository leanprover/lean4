set -euo pipefail

LAKE=${LAKE:-lake}

if [ "${OS:-}" = Windows_NT ]; then
LIB_PREFIX=
SHARED_LIB_EXT=dll
elif [ "`uname`" = Darwin ]; then
LIB_PREFIX=lib
SHARED_LIB_EXT=dylib
else
LIB_PREFIX=lib
SHARED_LIB_EXT=so
fi

test_run() {
  echo "[COMMAND]"
  echo "$> lake" "$@"
  if $LAKE "$@" >produced.out 2>&1; then
    rc=$?
  else
    rc=$?
  fi
  echo "Lake exited with code $rc"
  echo "[OUTPUT]"
  cat produced.out
  return $rc
}

match_out() {
  expected=$1; shift
  echo "[MATCH \"$expected\"]"
  if grep --color -F -- "$expected" produced.out; then
    return 0
  else
    echo "No match found."
    return 1
  fi
}

test_out() {
  expected=$1; shift
  if test_run "$@"; then rc=$?; else rc=$?; fi
  match_out "$expected"
  return $rc
}

test_err() {
  expected=$1; shift
  if test_run "$@"; then rc=$?; else rc=$?; fi
  if match_out "$expected"; then
    if [ $rc != 1 ]; then
      echo "[OUTCOME]"
      echo "Lake unexpectedly succeeded."
      return 1
    fi
  fi
}

test_maybe_err() {
  expected=$1; shift
  test_run "$@" || true
  match_out "$expected"
}

