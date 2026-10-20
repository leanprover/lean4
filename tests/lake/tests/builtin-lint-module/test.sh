#!/usr/bin/env bash
source ../common.sh

# Verifies `lake lint --builtin-lint` on module-system targets. The top-level
# module is loaded at `OLeanLevel.server`, and we want both env-linter and
# text-linter (lintLogExt) results to be preserved.
#
# Uses a dummy env linter defined in `Linters.lean` so this test does not
# couple to the behaviour of any production env linter (`defLemma`,
# `checkUnivs`, ...).

./clean.sh

# Clean module-system file: builtin lint must succeed.
test_run lint --builtin-only Clean

lake_out lint --builtin-only Main || true

# Dummy env linter (default-on, name-only test) flags the public def. This
# proves env linters still see imported public decls.
match_pat 'shouldBeFlaggedDummyMarker' produced.out
match_pat "name ends with 'DummyMarker'" produced.out

# Private decls are elided from `env.constants` at `.server`, so env linters
# must not see (and hence not flag) the private def, even though its name
# also matches the dummy linter's pattern.
no_match_pat 'shouldNotBeFlaggedPrivateDummyMarker' produced.out

# `linter.unusedVariables` (default-on) entries land in `lintLogExt` during
# the build. `lintLogExt` persists its entries at the `server` OLean level
# (not `exported`), so they are only visible because the lint driver imports
# at `.server`. The warning on a *public* def is replayed:
match_pat 'Variable name `publicUnusedLet` is not explicitly referenced' produced.out

# And — crucially — the warning on a *private* def is also replayed: even
# though private decls are elided from `env.constants` at `.server`, the
# `lintLogExt` entry is keyed by module index, not by declaration, so the
# text-linter warning is still recoverable.
match_pat 'Variable name `privateUnusedLet` is not explicitly referenced' produced.out
