#!/usr/bin/env bash
source ../common.sh

# Verifies the `--checks` CLI flag and the `lintChecks` package configuration
# for `lake lint --builtin-lint`. A checks module contains `@[builtin_env_linter]`
# declarations; it is built as part of the lint build and imported alongside each
# lint root, so the lint targets themselves do not need to import it. A checks
# module is itself exempt from linting unless it is also listed as a lint target.

./clean.sh

# Baseline: without `--checks`, `Main` does not (transitively) import any env
# linter, so nothing is registered and nothing is flagged.
lake_out lint --builtin-only Main || true
match_pat 'No environment linters were run for Main' produced.out
no_match_pat 'shouldBeFlaggedDummyMarker' produced.out

# --- Checks module in a sibling library ---

# `--checks=Linters` builds `Linters`, imports it alongside `Main`, and its
# dummy env linter flags the violation in `Main`.
lake_out lint --builtin-only --checks=Linters Main || true
match_pat 'shouldBeFlaggedDummyMarker' produced.out
match_pat "name ends with 'DummyMarker'" produced.out

# `--checks` implies builtin linting (no explicit `--builtin-lint` needed).
lake_out lint --checks=Linters Main || true
match_pat 'shouldBeFlaggedDummyMarker' produced.out

# --- Checks module under the lint root ---

# `Main.Rules` lives under the `Main.*` prefix but is used as a checks module:
# its linter runs on `Main`'s declarations, yet its own declarations (and its
# text-lint warnings) are exempt because it is not listed as a lint target.
lake_out lint --builtin-only --checks=Main.Rules Main || true
match_pat 'mainViolationRulesMarker' produced.out
no_match_pat 'insideChecksRulesMarker' produced.out
no_match_pat 'unusedInRules' produced.out

# Listing the checks module as a lint target removes the exemption.
lake_out lint --builtin-only --checks=Main.Rules Main Main.Rules || true
match_pat 'mainViolationRulesMarker' produced.out
match_pat 'insideChecksRulesMarker' produced.out
match_pat 'Variable name `unusedInRules` is not explicitly referenced' produced.out

# Comma-separated specs accumulate: both linters run on `Main`.
lake_out lint --builtin-only --checks=Linters,Main.Rules Main || true
match_pat 'shouldBeFlaggedDummyMarker' produced.out
match_pat 'mainViolationRulesMarker' produced.out
no_match_pat 'insideChecksRulesMarker' produced.out

# --- `lintChecks` package configuration ---

# The configured checks module is picked up without any CLI flag.
lake_out lint -f lakefile-config.toml --builtin-only Main || true
match_pat 'shouldBeFlaggedDummyMarker' produced.out

# CLI `--checks` accumulates with the configuration.
lake_out lint -f lakefile-config.toml --builtin-only --checks=Main.Rules Main || true
match_pat 'shouldBeFlaggedDummyMarker' produced.out
match_pat 'mainViolationRulesMarker' produced.out

# --- Error handling ---

# An unknown checks module is a hard error before any linting happens.
test_err 'NoSuchChecks' lint --builtin-only --checks=NoSuchChecks Main
