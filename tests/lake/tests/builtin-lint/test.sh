#!/usr/bin/env bash
source ../common.sh

./clean.sh

# --builtin-lint drives the build itself; we do not need to `lake build` first.
# Linting Clean should succeed (no violations) and implicitly build Clean.
test_run lint --builtin-only Clean

# --- Text linter capture (persistent lint log) ---

# Default scope: `linter.unusedVariables` (defValue=true) fires during the build,
# is captured in `lintLogExt`, and is re-emitted by `lake lint` post-build.
# `linter.missingDocs` (defValue=false) must NOT fire without --lint-all/--lint-only.
lake_out lint --builtin-only TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
no_match_pat 'missing doc string' produced.out

# --lint-all enables all linters, so missingDocs fires too.
lake_out lint --lint-all TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out

# --lint-only filters entries by suffix match against the linter name.
lake_out lint --lint-only missingDocs TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
no_match_pat 'is not explicitly referenced' produced.out

lake_out lint --lint-only unusedVariables TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
no_match_pat 'missing doc string' produced.out

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

# --- Transitive-import behaviour ---
# `Main` (a default target) imports `Main.Sub`. Both live under the `Main.*`
# module-name prefix, so `getDeclsInPackage Main` covers them and
# `collectTextLints` filters by `Main.isPrefixOf mod`. Overrides are keyed by
# package, so passing any module of a package flips the flag for every module
# in that package.

# Env linters run post-build against `importModules`-loaded decls, so
# `defLemma` catches `shouldBeTheoremInSub` regardless of override scope.
lake_out lint --builtin-lint Main || true
match_pat 'shouldBeTheoremInSub' produced.out

# `linter.unusedVariables` (defValue=true) fires on every build, so its entry
# lands in `Main.Sub.olean` unconditionally.
match_pat 'Variable name `unusedInSub` is not explicitly referenced' produced.out

# Explicit arg with --lint-all: the override applies to the whole package of
# `Main`, so `Main.Sub` is also built with `linter.all=true` and the
# missingDocs warning IS captured.
lake_out lint --lint-all Main || true
match_pat 'missing doc string for public def undocumentedInSub' produced.out

# No args: override is keyed by the root package; same effect on Main.Sub.
lake_out lint --lint-all || true
match_pat 'missing doc string for public def undocumentedInSub' produced.out

# Clean module has no violations; exit code should be 0
test_run lint --builtin-only Clean

# Without --extra, the extra linters (both the env linter and the dummy extra
# text linter in Linters.lean) must not run. Default linters still do, so the
# `defLemma` violation in this file fires.
lake_out lint --builtin-only ExtraViolations || true
no_match_pat 'badNameExtra' produced.out
no_match_pat 'extra text linter saw a declaration' produced.out
# Builtin extra text linter `unnecessarySeqFocus` is non-default, so silent.
no_match_pat 'tac1 <;> tac2' produced.out
# Builtin extra text linter `dupNamespace` is non-default, so it stays silent.
no_match_pat 'Dup.Dup.violation' produced.out
# Builtin extra text linter `unreachableTactic` is non-default, so silent.
no_match_pat 'this tactic is never executed' produced.out
# Default env linter `defLemma` runs and flags the def-of-Prop in this file.
match_pat 'shouldBeTheoremUnderExtra' produced.out

# --extra should run default linters together with the non-default (extra)
# ones, including the extra text linter which tags warnings with `linter.extra`.
lake_out lint --extra ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat "declaration name ends with 'Extra'" produced.out
match_pat 'extra text linter saw a declaration' produced.out
# Builtin extra text linter `unnecessarySeqFocus` fires under --extra: its
# tag `linter.extra.unnecessarySeqFocus` is matched by the `linter.extra`
# prefix filter.
match_pat 'tac1 <;> tac2' produced.out
# Builtin `dupNamespace` extra text linter fires under --extra.
match_pat 'Dup.Dup.violation' produced.out
match_pat "namespace .*Dup.* is duplicated" produced.out
# Builtin `unreachableTactic` extra text linter fires under --extra.
match_pat 'this tactic is never executed' produced.out
# --extra also runs default linters, so `defLemma` flags this file's violation.
match_pat 'shouldBeTheoremUnderExtra' produced.out

# --extra on TextLints: default `linter.unusedVariables` fires (default
# linters run under --extra). `linter.missingDocs` is still off-by-default
# and only enabled by `--lint-all`/`--lint-only`.
lake_out lint --extra TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
no_match_pat 'missing doc string' produced.out

# --lint-all should run both default and extra linters, for both the
# declaration-linter flow (badNameExtra from `dummyExtra`) and the text-linter
# flow (the `linter.extra`-tagged warning from `dummyExtraTextLinter`).
lake_out lint --lint-all ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'extra text linter saw a declaration' produced.out
match_pat 'tac1 <;> tac2' produced.out
match_pat 'this tactic is never executed' produced.out

# --lint-only unnecessarySeqFocus runs only the extra text linter.
lake_out lint --lint-only unnecessarySeqFocus ExtraViolations || true
match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'badNameExtra' produced.out
no_match_pat 'Dup.Dup.violation' produced.out

# --lint-only dupNamespace runs only the builtin extra `dupNamespace` text linter.
lake_out lint --lint-only dupNamespace ExtraViolations || true
match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'badNameExtra' produced.out
no_match_pat 'shouldBeTheorem' produced.out

# Multiple --lint-only flags accumulate: both named linters should run
lake_out lint --lint-only defLemma --lint-only checkUnivs || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'badUnivDecl' produced.out
no_match_pat 'badNameExtra' produced.out

# Last-wins: --extra overrides a prior --lint-all and clears --lint-only.
# Since --extra runs both default and extra linters, the default `defLemma`
# violation in ExtraViolations.lean fires too.
lake_out lint --lint-all --lint-only defLemma --extra || true
match_pat 'badNameExtra' produced.out
match_pat 'shouldBeTheoremUnderExtra' produced.out

# Last-wins: --lint-all overrides a prior --extra (default + extra still run,
# plus any disabled-by-default linters via `linter.all=true`).
lake_out lint --extra --lint-all || true
match_pat 'badNameExtra' produced.out
match_pat 'shouldBeTheorem' produced.out

# Last-wins: --extra clears a previously accumulated --lint-only. Default
# linters still run under --extra, so `defLemma` fires on its file's violation.
lake_out lint --lint-only defLemma --extra || true
match_pat 'badNameExtra' produced.out
match_pat 'shouldBeTheoremUnderExtra' produced.out

# --lint-only after --extra: the named linter runs (selection ignores scope)
lake_out lint --extra --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out
no_match_pat 'badNameExtra' produced.out

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

# --extra implicitly enables builtin lint
lake_out lint --extra ExtraViolations || true
match_pat 'badNameExtra' produced.out

# --lint-only implicitly enables builtin lint
lake_out lint --lint-only defLemma || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = false: check-lint fails (no lint driver and builtin linting disabled)
test_fails -f lakefile-builtin-false.toml check-lint

# builtinLint = false: lake lint errors
lake_out -f lakefile-builtin-false.toml lint || true
match_pat 'no lint driver configured' produced.out

# builtinLint = false with --builtin-lint flag: overrides and runs builtin lints
lake_out -f lakefile-builtin-false.toml lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out

# builtinLint = true: check-lint succeeds even without a lint driver
test_run -f lakefile-builtin-true.toml check-lint

# builtinLint = true: lake lint runs builtin lints
lake_out -f lakefile-builtin-true.toml lint || true
match_pat 'shouldBeTheorem' produced.out

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

# --- Non-root package as a lint target ---
# `Dep` lives in a path-based dependency (`dep`), not in the root package.
# Specifying it on the command line must key the linter option override by
# the *dep* package's baseName, not the root's, so that `linter.all=true`
# reaches `Dep` during build and `missingDocs` is captured in its olean.
lake_out lint --lint-all Dep || true
match_pat 'missing doc string for public def undocumentedInDep' produced.out

# Baseline: without `--lint-all`, no override is injected, so `missingDocs`
# stays at its default (off) and produces no entry for `Dep`.
lake_out lint --builtin-only Dep || true
no_match_pat 'missing doc string for public def undocumentedInDep' produced.out
