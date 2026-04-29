#!/usr/bin/env bash
source ../common.sh

./clean.sh
cp -r input/* .

# --builtin-lint drives the build itself; we do not need to `lake build` first.
# Linting Clean should succeed (no violations) and implicitly build Clean.
test_run lint --builtin-only Clean

# --- Text linter capture (persistent lint log) ---

# Default scope: `linter.unusedVariables` (defValue=true) fires during the build,
# is captured in `lintLogExt`, and is re-emitted by `lake lint` post-build.
# `linter.missingDocs` (defValue=false) must NOT fire without --lint-all/--lint-only.
lake_out lint --builtin-only TextLints || true
match_pat 'unused variable `unusedLet`' produced.out
no_match_pat 'missing doc string' produced.out

# --lint-all enables all linters, so missingDocs fires too.
lake_out lint --lint-all TextLints || true
match_pat 'unused variable `unusedLet`' produced.out
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out

# --lint-only filters entries by suffix match against the linter name.
lake_out lint --lint-only missingDocs TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
no_match_pat 'unused variable' produced.out

lake_out lint --lint-only unusedVariables TextLints || true
match_pat 'unused variable `unusedLet`' produced.out
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
match_pat 'unused variable `unusedInSub`' produced.out

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

# Without --clippy, the clippy linters (both the env linter and the dummy clippy
# text linter in Linters.lean) must not run.
lake_out lint --builtin-only ClippyViolations || true
no_match_pat 'badNameClippy' produced.out
no_match_pat 'clippy text linter saw a declaration' produced.out
# Builtin clippy env linter `dupNamespace` is non-default, so it stays silent.
no_match_pat 'Dup.Dup.violation' produced.out

# --clippy should run only non-default (clippy) linters, including the clippy
# text linter which tags its warnings with `linter.clippy`.
lake_out lint --clippy ClippyViolations || true
match_pat 'badNameClippy' produced.out
match_pat "declaration name ends with 'Clippy'" produced.out
match_pat 'clippy text linter saw a declaration' produced.out
# Builtin `dupNamespace` env linter fires under --clippy.
match_pat 'Dup.Dup.violation' produced.out
match_pat "namespace .*Dup.* is duplicated" produced.out
# --clippy should not run default linters
no_match_pat 'shouldBeTheorem' produced.out

# --clippy on TextLints: the default `linter.unusedVariables` entry is filtered
# out because its tag is not `linter.clippy`. The file has no clippy-tagged
# linter, so the clippy-scope text-linter output should be empty.
lake_out lint --clippy TextLints || true
no_match_pat 'unused variable' produced.out
no_match_pat 'missing doc string' produced.out

# --lint-all should run both default and clippy linters, for both the
# declaration-linter flow (badNameClippy from `dummyClippy`) and the text-linter
# flow (the `linter.clippy`-tagged warning from `dummyClippyTextLinter`).
lake_out lint --lint-all ClippyViolations || true
match_pat 'badNameClippy' produced.out
match_pat 'clippy text linter saw a declaration' produced.out
match_pat 'Dup.Dup.violation' produced.out

# --lint-only dupNamespace runs only the builtin clippy `dupNamespace` env linter.
lake_out lint --lint-only dupNamespace ClippyViolations || true
match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'badNameClippy' produced.out
no_match_pat 'shouldBeTheorem' produced.out

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
