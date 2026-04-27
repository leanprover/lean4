import Lean.Linter.EnvLinter

open Lean Meta

-- A dummy clippy linter that flags any declaration whose name ends with "Clippy".
@[builtin_env_linter clippy] public meta def dummyClippy : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'Clippy' found."
  errorsFound := "CLIPPY VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "Clippy" then
      return some "declaration name ends with 'Clippy'"
    return none
