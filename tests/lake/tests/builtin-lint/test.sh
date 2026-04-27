#!/usr/bin/env bash
source ../common.sh

./clean.sh
cp -r input/* .

# --builtin-lint should fail with a clear message when oleans are not built
lake_out lint --builtin-lint || true
match_pat 'out of date oleans' produced.out

# up-to-date check is per-module: building only Clean should let us lint Clean
test_run build Clean
test_run lint --builtin-only Clean

# but linting Main (not yet built) should still fail the up-to-date check
lake_out lint --builtin-only Main || true
match_pat 'out of date oleans' produced.out

test_run build

# --builtin-lint should detect the defLemma violation in Main (the default target)
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a def, should be a lemma/theorem' produced.out
# `@[reducible, instance]` on a `def` of Prop type keeps it a `def`, so flag it.
match_pat 'reducibleInstShouldBeTheorem' produced.out
# Plain `instance` of Prop type is elaborated as a theorem; it should not be flagged.
no_match_pat 'plainInstIsOk' produced.out

# --builtin-lint should also detect the checkUnivs violation
match_pat 'badUnivDecl' produced.out
match_pat 'only occur together' produced.out
# builtin_nolint checkUnivs should suppress the warning
no_match_pat 'badUnivSkipped' produced.out

# --lint-only defLemma should run only the defLemma linter
lake_out lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badUnivDecl' produced.out

# Clean module has no violations; exit code should be 0
test_run lint --builtin-only Clean

# Without --clippy, the clippy linter should not run
lake_out lint --builtin-only ClippyViolations || true
no_match_pat 'badNameClippy' produced.out

# --clippy should run only non-default (clippy) linters
lake_out lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out
match_pat "declaration name ends with 'Clippy'" produced.out
# --clippy should not run default linters
no_match_pat 'shouldBeTheorem' produced.out

# --lint-all should run both default and clippy linters
lake_out lint --lint-all ClippyViolations || true
match_pat 'badNameClippy' produced.out

# Multiple --lint-only flags accumulate: both named linters should run
lake_out lint --lint-only defLemma --lint-only checkUnivs || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'badUnivDecl' produced.out
no_match_pat 'badNameClippy' produced.out

# Last-wins: --clippy overrides a prior --lint-all and clears --lint-only
lake_out lint --lint-all --lint-only defLemma --clippy || true
match_pat 'badNameClippy' produced.out
no_match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badUnivDecl' produced.out

# Last-wins: --lint-all overrides a prior --clippy (both default and clippy run)
lake_out lint --clippy --lint-all || true
match_pat 'badNameClippy' produced.out
match_pat 'shouldBeTheorem' produced.out

# Last-wins: --clippy clears a previously accumulated --lint-only
lake_out lint --lint-only defLemma --clippy || true
match_pat 'badNameClippy' produced.out
no_match_pat 'shouldBeTheorem' produced.out

# --lint-only after --clippy: the named linter runs (selection ignores scope)
lake_out lint --clippy --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badNameClippy' produced.out

# --builtin-only should skip the lint driver
lake_out lint -f with-driver.lean --builtin-only Main || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'lint-driver:' produced.out

# --- builtinLint package configuration tests ---

# Default (builtinLint unset / none): check-lint fails (same as false for now)
test_fails check-lint

# Default: lake lint errors when no lintDriver and builtinLint is unset
lake_out lint || true
match_pat 'no lint driver configured' produced.out

# Default: lake lint --builtin-lint overrides and runs builtin lints
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# --clippy implicitly enables builtin lint
lake_out lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out

# --lint-only implicitly enables builtin lint
lake_out lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = false: check-lint fails (no lint driver and builtin linting disabled)
sed_i 's/^name = .*/&\nbuiltinLint = false/' lakefile.toml
test_fails check-lint

# builtinLint = false: lake lint errors
lake_out lint || true
match_pat 'no lint driver configured' produced.out

# builtinLint = false with --builtin-lint flag: overrides and runs builtin lints
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = true: check-lint succeeds even without a lint driver
sed_i 's/builtinLint = false/builtinLint = true/' lakefile.toml
test_run check-lint

# builtinLint = true: lake lint runs builtin lints
lake_out lint || true
match_pat 'shouldBeTheorem' produced.out

# Restore original lakefile
cp input/lakefile.toml lakefile.toml

# --- builtinLint = true with a lint driver ---

# builtinLint = true + lint driver + clean module: both builtin lints and driver run
lake_out lint -f with-driver.lean Clean || true
match_pat 'Linting passed for Clean' produced.out
match_pat 'lint-driver:' produced.out

# builtinLint = true + lint driver + violations: both run, exit code is nonzero
lake_out lint -f with-driver.lean Main || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'lint-driver:' produced.out

# builtinLint = true + lint driver: check-lint succeeds
test_run -f with-driver.lean check-lint
