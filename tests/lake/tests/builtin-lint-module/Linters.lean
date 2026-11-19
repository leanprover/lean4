module

public import Lean.Data.Options
public import Lean.Linter.Init
public meta import Lean.Linter.EnvLinter

meta section
open Lean Meta Lean.Linter

public register_option linter.dummyMarker : Bool := {
  defValue := true
  descr := "(test) flag declarations whose name ends with 'DummyMarker'"
}
initialize addEnvLinterOption linter.dummyMarker

@[builtin_env_linter linter.dummyMarker]
public def dummyEnvLinter : EnvLinter.EnvLinter where
  noErrorsFound := "No dummy linter violations found."
  errorsFound := "DUMMY LINTER VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "DummyMarker" then
      return some "name ends with 'DummyMarker'"
    return none

end
