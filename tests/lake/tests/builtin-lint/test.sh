#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Builtin linting is now driven entirely by linter *options*. Which linters run
# on a declaration is decided by the linter options in effect when that
# declaration was built (its snapshot for env linters; `lintLogExt` for text
# linters). `--linters=<spec>` overrides those options for the lint build:
# `linter.X` enables, `-linter.X` disables, entries are comma-separated and
# repeatable, last-wins for the same linter. There is no longer an "only" mode.

# --builtin-lint drives the build itself; we do not need to `lake build` first.
# Linting Clean should succeed (no violations) and implicitly build Clean.
test_run lint --builtin-only Clean

# --- Text linter capture (persistent lint log) ---

# Default options: `linter.unusedVariables` (defValue=true) fires during the
# build, is captured in `lintLogExt`, and is re-emitted by `lake lint`.
# `linter.missingDocs` (defValue=false) must NOT fire without being enabled.
lake_out lint --builtin-only TextLints || true
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out
no_match_pat 'missing doc string' produced.out

# `--linters=linter.missingDocs` enables missingDocs; the default-on
# unusedVariables keeps firing too.
lake_out lint --linters=linter.missingDocs TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out

# Disabling a default-on linter: `-linter.unusedVariables` turns it off while
# `linter.missingDocs` is enabled.
lake_out lint --linters=linter.missingDocs,-linter.unusedVariables TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
no_match_pat 'is not explicitly referenced' produced.out

# `--linters=linter.all` enables every linter, so missingDocs fires too.
lake_out lint --linters=linter.all TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out

# --- defProp / checkUnivs (enabled via `set_option` in the source) ---

# --builtin-lint should detect the defProp violation in Main (the default target)
lake_out lint --builtin-lint || true
match_pat 'shouldBeTheorem' produced.out
match_pat 'is a proposition; use `theorem` instead of `def`' produced.out
# `@[reducible, instance]` on a `def` of Prop type keeps it a `def`, so flag it.
match_pat 'reducibleInstShouldBeTheorem' produced.out
# Plain `instance` of Prop type is elaborated as a theorem; it should not be flagged.
no_match_pat 'plainInstIsOk' produced.out

# --builtin-lint should also detect the checkUnivs violation
match_pat 'badUnivDecl' produced.out
match_pat 'only occur together' produced.out
# Per-declaration `set_option linter.checkUnivs false in` suppresses the warning
# (the replacement for the old `builtin_nolint` attribute).
no_match_pat 'badUnivSkipped' produced.out

# --- Transitive-import behaviour ---
# `Main` (a default target) imports `Main.Sub`. Both live under the `Main.*`
# module-name prefix, so `getDeclsInPackage Main` covers them and
# `collectTextLints` filters by `Main.isPrefixOf mod`. Overrides are keyed by
# package, so passing any module of a package flips the option for every module
# in that package.

# `defProp` runs during the build of each module, so its warning for
# `shouldBeTheoremInSub` is captured in `Main.Sub`'s lint log and re-emitted
# via `collectTextLints` when `Main` is linted.
lake_out lint --builtin-lint Main || true
match_pat 'shouldBeTheoremInSub' produced.out

# `linter.unusedVariables` (defValue=true) fires on every build, so its entry
# lands in `Main.Sub.olean` unconditionally.
match_pat 'Variable name `unusedInSub` is not explicitly referenced' produced.out

# Explicit arg with `--linters=linter.missingDocs`: the override applies to the
# whole package of `Main`, so `Main.Sub` is also built with missingDocs enabled
# and its warning IS captured.
lake_out lint --linters=linter.missingDocs Main || true
match_pat 'missing doc string for public def undocumentedInSub' produced.out

# No args: override is keyed by the root package; same effect on Main.Sub.
lake_out lint --linters=linter.all || true
match_pat 'missing doc string for public def undocumentedInSub' produced.out

# --- Env linter + extra text linters ---

# Default options: the extra linters and the dummy env linter stay silent.
# Default linters still run, so the `defProp` violation in this file fires.
lake_out lint --builtin-only ExtraViolations || true
no_match_pat 'badNameExtra' produced.out
no_match_pat 'extra text linter saw a declaration' produced.out
no_match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'this tactic is never executed' produced.out
match_pat 'shouldBeTheoremUnderExtra' produced.out

# `--linters=linter.extra` enables the `linter.extra` set: the builtin extra
# text linters (members of the set) and the dummy extra text linter (gated
# directly on `linter.extra`).
lake_out lint --linters=linter.extra ExtraViolations || true
match_pat 'extra text linter saw a declaration' produced.out
# `unnecessarySeqFocus` fires via its `linter.extra` set membership.
match_pat 'tac1 <;> tac2' produced.out
# `dupNamespace` fires via its `linter.extra` set membership.
match_pat 'Dup.Dup.violation' produced.out
match_pat "namespace .*Dup.* is duplicated" produced.out
# `unreachableTactic` fires via its `linter.extra` set membership.
match_pat 'this tactic is never executed' produced.out
# Default linters still run, so `defProp` flags this file's violation.
match_pat 'shouldBeTheoremUnderExtra' produced.out
# `linter.extra` does NOT enable the env linter — that has its own option.
no_match_pat "declaration name ends with 'Extra'" produced.out

# `--linters=linter.dummyExtra` enables the dummy ENV linter (snapshot-driven).
lake_out lint --linters=linter.dummyExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat "declaration name ends with 'Extra'" produced.out
# `skippedNameExtra` opts out via `set_option linter.dummyExtra false in`, so
# even with the linter enabled it is not reported.
no_match_pat 'skippedNameExtra' produced.out

# `--linters=linter.all` enables both the extra set and the env linter.
lake_out lint --linters=linter.all ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'extra text linter saw a declaration' produced.out
match_pat 'tac1 <;> tac2' produced.out
match_pat 'this tactic is never executed' produced.out

# Enabling a single extra text linter by name (set membership not required).
lake_out lint --linters=linter.extra.unnecessarySeqFocus ExtraViolations || true
match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'badNameExtra' produced.out
no_match_pat 'Dup.Dup.violation' produced.out

lake_out lint --linters=linter.extra.dupNamespace ExtraViolations || true
match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'badNameExtra' produced.out
no_match_pat 'tac1 <;> tac2' produced.out

# Multiple comma-separated entries accumulate.
lake_out lint --linters=linter.dummyExtra,linter.extra.dupNamespace ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'tac1 <;> tac2' produced.out

# Multiple `--linters` flags accumulate across occurrences.
lake_out lint --linters=linter.dummyExtra --linters=linter.extra.dupNamespace ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'Dup.Dup.violation' produced.out

# Last-wins within a single spec: a later entry overrides an earlier one.
lake_out lint --linters=linter.dummyExtra,-linter.dummyExtra ExtraViolations || true
no_match_pat "declaration name ends with 'Extra'" produced.out

# Last-wins across flags: the later `--linters` entry wins for the same linter.
lake_out lint --linters=linter.dummyExtra --linters=-linter.dummyExtra ExtraViolations || true
no_match_pat "declaration name ends with 'Extra'" produced.out

# --- Short `.linterName` spelling ---
# A leading `.` is sugar for the `linter.` prefix, so `.X` means `linter.X`.
# These mirror the long-form assertions above to prove the spellings are equivalent.

# `.missingDocs` enables missingDocs just like `linter.missingDocs`.
lake_out lint --linters=.missingDocs TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out

# Short form with a `-` prefix disables: `-.unusedVariables` turns off the
# default-on linter while `.missingDocs` enables missingDocs.
lake_out lint --linters=.missingDocs,-.unusedVariables TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
no_match_pat 'is not explicitly referenced' produced.out

# `.all` enables every linter, so missingDocs fires too.
lake_out lint --linters=.all TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
match_pat 'Variable name `unusedLet` is not explicitly referenced' produced.out

# Short form for the dummy ENV linter: `.dummyExtra` == `linter.dummyExtra`.
lake_out lint --linters=.dummyExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat "declaration name ends with 'Extra'" produced.out

# Short form for a nested name: `.extra.unnecessarySeqFocus`.
lake_out lint --linters=.extra.unnecessarySeqFocus ExtraViolations || true
match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'badNameExtra' produced.out

# Short and long spellings mix freely within a single spec.
lake_out lint --linters=.dummyExtra,linter.extra.dupNamespace ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'tac1 <;> tac2' produced.out

# --- `--lint-only`: restrict OUTPUT to exactly the linters the options enable ---
# `--lint-only` takes the same spec as `--linters` and enables those linters for
# the build in the same way, but it additionally suppresses every linter the spec
# does not *positively* enable (the linter's own default value is ignored). So
# unlike `--linters`, default-on linters that aren't named do not appear. Note
# `ExtraViolations.lean` forces `set_option linter.defProp true`, so `defProp`
# fires during the build regardless — only the display filter can hide it.

# NOTE: `shouldBeTheoremUnderExtra` is an ambiguous marker — its *name* ends in
# "Extra", so the `dummyExtra` env linter also flags it. To probe `defProp`
# specifically (the default-on linter we expect only-mode to hide), match its own
# message `is a proposition` instead of the declaration name.

# Headline contrast with `--linters=.missingDocs` above (which keeps the
# default-on `unusedVariables`): `--lint-only` shows missingDocs and nothing else.
lake_out lint --lint-only=linter.missingDocs TextLints || true
match_pat 'missing doc string for public def undocumentedPublicDef' produced.out
no_match_pat 'is not explicitly referenced' produced.out

# Env linter only: `dummyExtra` fires, but the default-on `defProp` violation is
# suppressed — `linter.defProp` is not whitelisted. (`shouldBeTheoremUnderExtra`
# still appears, flagged by `dummyExtra` for ending in "Extra", not by defProp.)
lake_out lint --lint-only=linter.dummyExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat "declaration name ends with 'Extra'" produced.out
no_match_pat 'is a proposition' produced.out
no_match_pat 'extra text linter saw a declaration' produced.out
no_match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'Dup.Dup.violation' produced.out
# Per-declaration opt-out is still respected even in only-mode.
no_match_pat 'skippedNameExtra' produced.out

# Group expansion: `linter.extra` enables its members for display, but the
# default `defProp` stays suppressed (contrast `--linters=linter.extra` above,
# which keeps it).
lake_out lint --lint-only=linter.extra ExtraViolations || true
match_pat 'extra text linter saw a declaration' produced.out
match_pat 'tac1 <;> tac2' produced.out
match_pat 'Dup.Dup.violation' produced.out
match_pat 'this tactic is never executed' produced.out
no_match_pat 'is a proposition' produced.out
# The env linter is not a member of `linter.extra`, so it stays silent.
no_match_pat "declaration name ends with 'Extra'" produced.out

# A single member by name shows only that linter.
lake_out lint --lint-only=linter.extra.unnecessarySeqFocus ExtraViolations || true
match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'Dup.Dup.violation' produced.out
no_match_pat 'extra text linter saw a declaration' produced.out
no_match_pat 'badNameExtra' produced.out
no_match_pat 'is a proposition' produced.out

# `linter.all` enables everything, so only-mode then shows the defaults too,
# including the `defProp` violation.
lake_out lint --lint-only=linter.all ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'extra text linter saw a declaration' produced.out
match_pat 'tac1 <;> tac2' produced.out
match_pat 'is a proposition' produced.out

# Carve-out within a single spec: `linter.all` minus `linter.defProp` shows
# everything except the `defProp` message. (`badNameExtra` still comes from the
# env linter, enabled via `linter.all`.)
lake_out lint --lint-only=linter.all,-linter.defProp ExtraViolations || true
match_pat 'badNameExtra' produced.out
match_pat 'tac1 <;> tac2' produced.out
no_match_pat 'is a proposition' produced.out

# A trailing `--lint-only` flushes the preceding `--linters` spec: only
# `unusedVariables` remains, so `missingDocs` (from `--linters`) is dropped.
lake_out lint --linters=linter.missingDocs --lint-only=linter.unusedVariables TextLints || true
match_pat 'is not explicitly referenced' produced.out
no_match_pat 'missing doc string' produced.out

# Short `.linterName` spelling works for `--lint-only` too.
lake_out lint --lint-only=.dummyExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out
no_match_pat 'is a proposition' produced.out

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

# --linters implicitly enables builtin lint
lake_out lint --linters=linter.dummyExtra ExtraViolations || true
match_pat 'badNameExtra' produced.out

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

# builtinLint = true + lint driver + clean module: both builtin lints and driver run.
# `Clean` does not import the dummy env linter, so no env linters are registered
# in its environment and the builtin-lint pass reports "No environment linters
# were run" rather than "Linting passed".
lake_out lint -f with-driver.lean Clean || true
match_pat 'No environment linters were run for Clean' produced.out
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
# the *dep* package's baseName, not the root's, so that `linter.missingDocs`
# reaches `Dep` during build and the warning is captured in its olean.
lake_out lint --linters=linter.missingDocs Dep || true
match_pat 'missing doc string for public def undocumentedInDep' produced.out

# Baseline: without the override, `missingDocs` stays at its default (off) and
# produces no entry for `Dep`.
lake_out lint --builtin-only Dep || true
no_match_pat 'missing doc string for public def undocumentedInDep' produced.out
