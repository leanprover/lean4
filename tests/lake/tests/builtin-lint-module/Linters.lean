module

public meta import Lean.Linter.EnvLinter

open Lean Meta Lean.Linter

/-- Dummy env linter for the `lake lint --builtin-lint` module-system test.
Default scope (no `extra`), and the test reads only the declaration name so
it does not depend on whether bodies are exposed at the `.exported` import
level. Flags any declaration whose name ends with the marker suffix. -/
@[builtin_env_linter] public meta def dummyEnvLinter : EnvLinter.EnvLinter where
  noErrorsFound := "No dummy linter violations found."
  errorsFound := "DUMMY LINTER VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "DummyMarker" then
      return some "name ends with 'DummyMarker'"
    return none
