-- Env-linter violation: `def` on a Prop — should be caught by `defLemma`
-- regardless of build-time options, since env linters run post-build.
def shouldBeTheoremInSub : 1 = 1 := rfl

-- Default text-linter violation: `linter.unusedVariables` has `defValue := true`,
-- so it fires on any build and the warning lands in Main.Sub.olean unconditionally.
def unusedVarInSub : Nat :=
  let unusedInSub := 7
  3

-- Non-default text-linter violation: `linter.missingDocs` has `defValue := false`,
-- so it only fires when the module was compiled with `linter.all = true`. Under
-- the current per-module override scheme, Main.Sub does NOT get that flag
-- (only `Main` does), so this warning will be absent from Main.Sub.olean.
def undocumentedInSub : Nat := 99
