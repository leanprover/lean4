-- `linter.defProp` is off by default for bootstrapping reasons; enable it
-- here so this transitive-import test still captures the violation in the
-- module's lint log.
set_option linter.defProp true

-- `def` on a Prop — caught by the `defProp` linter at build time.
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
