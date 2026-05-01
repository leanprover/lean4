-- `linter.unusedVariables` has `defValue := true`, so it fires during the normal
-- build that backs `lake lint --builtin-lint`. The warning is captured in the
-- olean via `lintLogExt` and re-emitted by `lake lint`.
def unusedVarFixture : Nat :=
  let unusedLet := 5
  3

-- `linter.missingDocs` has `defValue := false`, so it only fires when Lake's
-- build is invoked with `linter.all = true` (i.e. `--lint-all` or `--lint-only`).
-- This public def has no docstring and will be flagged accordingly.
def undocumentedPublicDef : Nat := 42
