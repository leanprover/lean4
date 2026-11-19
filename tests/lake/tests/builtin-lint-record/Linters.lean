import Lean.Linter.EnvLinter

open Lean Meta Lean.Linter

/-- Option gating the dummy env linter; on by default so it fires during the
build without needing `--linters`. -/
register_option linter.dummyMarker : Bool := {
  defValue := true
  descr := "(test) flag declarations whose name ends with 'DummyMarker'"
}

initialize addEnvLinterOption linter.dummyMarker

-- A dummy env linter flagging any declaration whose name ends with "DummyMarker".
-- Exercises the env-linter recording path (`findDeclarationRanges?` +
-- source-search-path lookup) independently of any production env linter.
@[builtin_env_linter linter.dummyMarker]
public meta def dummyMarker : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'DummyMarker' found."
  errorsFound := "DUMMY MARKER VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "DummyMarker" then
      return some "declaration name ends with 'DummyMarker'"
    return none
