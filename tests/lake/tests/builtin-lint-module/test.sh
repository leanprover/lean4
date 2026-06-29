#!/usr/bin/env bash
source ../common.sh

# Verifies `lake lint --builtin-lint` on module-system targets. The top-level
# module is loaded at `OLeanLevel.exported` (the "public" level), and we want
# both env-linter and text-linter (lintLogExt) results to be preserved.
#
# Uses a dummy env linter defined in `Linters.lean` so this test does not
# couple to the behaviour of any production env linter (`defLemma`,
# `checkUnivs`, ...).

./clean.sh

# Clean module-system file: builtin lint must succeed.
test_run lint --builtin-only Clean

lake_out lint --builtin-only Main || true

# Dummy env linter (default-on, name-only test) flags the public def. This
# proves env linters still see imported public decls at `.exported`.
match_pat 'shouldBeFlaggedDummyMarker' produced.out
match_pat "name ends with 'DummyMarker'" produced.out

# `linter.unusedVariables` (default-on) entries land in `lintLogExt` during
# the build. `lintLogExt` writes uniform OLean entries, so its data must
# survive loading at `.exported`. The warning on a *public* def is replayed:
match_pat 'Variable name `publicUnusedLet` is not explicitly referenced' produced.out

# And — crucially — the warning on a *private* def is also replayed: even
# though private decls are elided from `env.constants` at `.exported`, the
# `lintLogExt` entry is keyed by module index, not by declaration, so the
# text-linter warning survives the level change.
match_pat 'Variable name `privateUnusedLet` is not explicitly referenced' produced.out
