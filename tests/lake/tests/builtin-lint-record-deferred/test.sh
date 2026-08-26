#!/usr/bin/env bash
source ../common.sh

# Exercises `lake lint --record-exceptions` for deferred docstring checks
# (`linter.doc.deferred`): a failing forward reference is silenced in place by
# inserting a `set_option linter.doc.deferred false in` line before the flagged
# docstring. Covers both site kinds:
#   * a declaration docstring, recorded via `findDeclarationRanges?` (the
#     declaration range starts at the `/--` line), and
#   * Verso module docstrings, recorded via their snippet's declaration range;
#     two snippets exercise a nonzero site index.

./clean.sh
./setup.sh

marker='recorded by'

# Asserts the recorded `set_option` for $1 is immediately followed by a line
# mentioning $2 (i.e. it was inserted directly before that docstring).
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

# Asserts the docstring mentioning $1 got no recorded exception (the line before
# it is not a `set_option ... false in`).
assert_not_recorded() {
  echo "? '$1' has no recorded exception"
  if grep -B1 -F -- "$1" Violations.lean | grep -qE 'set_option .* false in'; then
    echo "FAILURE: '$1' unexpectedly got a recorded exception"
    cat Violations.lean
    return 1
  fi
}

# --- Baseline: the three unresolvable references fail; the resolvable one does not. ---
lake_out lint --builtin-lint Violations || true
match_pat 'Nat.firstMissingXYZ' produced.out
match_pat 'Nat.secondMissingXYZ' produced.out
match_pat 'Nat.declMissingXYZ' produced.out
match_pat 'module docstring #1' produced.out
match_pat 'module docstring #2' produced.out
match_pat 'declForwardRef' produced.out
# The resolvable reference produces no diagnostic.
no_match_pat 'Nat\.zero' produced.out
no_match_pat 'goodForwardRef' produced.out

# --- Record exceptions. ---
# It succeeds (exit 0) as long as every failing check could be located, even
# though violations were found, and reports what it edited.
lake_out lint --record-exceptions Violations
match_pat 'recording 3 exceptions in .*Violations.lean' produced.out

# --- The source now carries one `set_option ... false in` per failing check. ---
# Each recorded line is tagged with the marker comment...
test_cmd test "$(grep -c -- "$marker" Violations.lean)" = 3
# ...and sits directly before the docstring it silences.
assert_precedes 'linter.doc.deferred' 'Nat.firstMissingXYZ'
assert_precedes 'linter.doc.deferred' 'Nat.secondMissingXYZ'
assert_precedes 'linter.doc.deferred' 'Nat.declMissingXYZ'
# The resolvable reference is left untouched.
assert_not_recorded 'Nat.zero'

# --- Re-linting now passes: every failing check is silenced. ---
test_run lint --builtin-lint Violations
lake_out lint --builtin-lint Violations
no_match_pat 'MissingXYZ' produced.out

# --- Idempotent: a second recording pass finds nothing new to record. ---
lake_out lint --record-exceptions Violations || true
no_match_pat 'recording .* exception' produced.out
# The file is unchanged: still exactly three recorded exceptions, no duplicates.
test_cmd test "$(grep -c -- "$marker" Violations.lean)" = 3
