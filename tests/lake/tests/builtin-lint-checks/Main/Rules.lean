module

public import Lean.Data.Options
public import Lean.Linter.Init
public meta import Lean.Linter.EnvLinter

meta section
open Lean Meta Lean.Linter

public register_option linter.rulesMarker : Bool := {
  defValue := true
  descr := "(test) flag declarations whose name ends with 'RulesMarker'"
}
initialize addEnvLinterOption linter.rulesMarker

@[builtin_env_linter linter.rulesMarker]
public def rulesEnvLinter : EnvLinter.EnvLinter where
  noErrorsFound := "No rules linter violations found."
  errorsFound := "RULES LINTER VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "RulesMarker" then
      return some "name ends with 'RulesMarker'"
    return none

end

-- A violation and a text-lint trigger *inside* the checks module: these must
-- only be reported when `Main.Rules` is itself listed as a lint target.
public def insideChecksRulesMarker : Nat := 3

public def rulesUnusedVarFixture : Nat :=
  let unusedInRules := 7
  3
