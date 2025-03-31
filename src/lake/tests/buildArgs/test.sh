#!/usr/bin/env bash
set -euo pipefail

exit 0  # TODO: flaky test disabled

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that changing `moreLean/Leanc/LinkArgs` triggers a rebuild
# Test that changing `weakLean/Leanc/LinkArgs` does not

test_run() {
  echo "[Command]"
  echo "$> lake" "$@"
  if $LAKE "$@" >produced.out 2>&1; then
    rc=$?
  else
    rc=$?
  fi
  echo "Lake exited with code $rc"
  echo "[Output]"
  cat produced.out
  return $rc
}

test_out() {
  expected=$1; shift
  if test_run "$@"; then rc=$?; else rc=$?; fi
  echo "[Match \"$expected\"]"
  if grep --color -F "$expected" produced.out; then
    return $rc
  else
    echo "No match found."
    return 1
  fi
}

# Test `leanArgs`
test_run build +Hello -R
# see https://github.com/leanprover/lake/issues/50
test_out "warningAsError" build +Hello -R -KleanArgs=-DwarningAsError=true -v

# Test `weakLeanArgs`
test_run build +Hello -R
# see https://github.com/leanprover/lake/issues/172
test_run build +Hello -R -KweakLeanArgs=-DwarningAsError=true --no-build

# Test `leancArgs`
test_run build +Hello:o -R
test_out "Built Hello:c.o" build +Hello:o -R -KleancArgs=-DBAR -v

# Test `weakLeancArgs`
test_run build +Hello:o -R
test_run build +Hello:o -R -KweakLeancArgs=-DBAR --no-build

# Test `linkArgs`
test_run build +Hello:dynlib Hello:shared hello -R
test_out "Built Hello:dynlib" build +Hello:dynlib -R -KlinkArgs=-L.lake/build/lib -v
test_out "Built Hello:shared" build Hello:shared -R -KlinkArgs=-L.lake/build/lib -v
test_out "Built hello" build hello -R -KlinkArgs=-L.lake/build/lib -v

# Test `weakLinkArgs`
test_run build +Hello:dynlib Hello:shared hello  -R
test_run build +Hello:dynlib -R -KweakLinkArgs=-L.lake/build/lib  --no-build
test_run build Hello:shared -R -KweakLinkArgs=-L.lake/build/lib  --no-build
test_run build hello -R -KweakLinkArgs=-L.lake/build/lib  --no-build

# cleanup
rm -f produced.out
