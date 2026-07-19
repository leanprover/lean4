#!/usr/bin/env bash
source ../common.sh

# Exercises `lake lint --record-exceptions`: every builtin-linter warning is
# silenced in place by inserting a `set_option <linter> false in` line before the
# offending declaration. Covers both linter flavours:
#   * a text linter (`linter.unusedVariables`) recorded from its `lintLogExt`
#     entry's stored position, and
#   * an env linter (`linter.dummyMarker`, defined in `Linters.lean`) recorded
#     via `findDeclarationRanges?` + the workspace source-search-path lookup.

./clean.sh
./setup.sh

marker='recorded by'

# Asserts the recorded `set_option` for $1 is immediately followed by a line
# mentioning $2 (i.e. it was inserted directly before that declaration).
assert_precedes() {
  echo "? '$1' precedes '$2'"
  if grep -A1 -E "set_option $1 false in" Violations.lean | grep -qF -- "$2"; then
    return 0
  else
    echo "FAILURE: '$1' exception was not inserted before '$2'"
    cat Violations.lean
    return 1
  fi
}

# --- Baseline: the violations are present before recording. ---
lake_out lint --builtin-lint Violations || true
match_pat 'Variable name `unusedLocal` is not explicitly referenced' produced.out
match_pat 'fooDummyMarker' produced.out
match_pat "declaration name ends with 'DummyMarker'" produced.out
# The env linter also reaches the indented, namespaced declaration.
match_pat 'nestedDummyMarker' produced.out

# --- Record exceptions. ---
# `--record-exceptions` implies `--builtin-lint`. It succeeds (exit 0) as long as
# every warning could be located, even though violations were found, and reports
# what it edited. All three warnings (one text, two env) are recorded at once.
lake_out lint --record-exceptions Violations
match_pat 'recording 3 exceptions in .*Violations.lean' produced.out

# --- The source now carries one `set_option <linter> false in` per warning. ---
# Each recorded line is tagged with the marker comment...
test_cmd test "$(grep -c -- "$marker" Violations.lean)" = 3
# ...and sits directly before the declaration it silences.
assert_precedes 'linter.unusedVariables' 'def unusedVarHere'
assert_precedes 'linter.dummyMarker' 'def fooDummyMarker'
assert_precedes 'linter.dummyMarker' 'def nestedDummyMarker'
# The indented declaration keeps its leading whitespace.
match_pat '^  set_option linter.dummyMarker false in ' Violations.lean

# --- Re-linting now passes: every warning is silenced. ---
lake_out lint --builtin-lint Violations || true
match_pat 'Linting passed for Violations' produced.out
no_match_pat 'is not explicitly referenced' produced.out
no_match_pat "declaration name ends with 'DummyMarker'" produced.out

# --- Idempotent: a second recording pass finds nothing new to record. ---
lake_out lint --record-exceptions Violations || true
no_match_pat 'recording .* exception' produced.out
# The file is unchanged: still exactly three recorded exceptions, no duplicates.
test_cmd test "$(grep -c -- "$marker" Violations.lean)" = 3
