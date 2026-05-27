import Lean.Linter.EnvLinter

open Lean Meta Lean.Linter Lean.Elab.Command

-- A dummy extra linter that flags any declaration whose name ends with "Extra".
@[builtin_env_linter extra] public meta def dummyExtra : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'Extra' found."
  errorsFound := "EXTRA VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "Extra" then
      return some "declaration name ends with 'Extra'"
    return none

-- A dummy extra text linter: fires on every `declaration` command, but only
-- when `linter.extra = true`. Tags its warnings with `linter.extra` via
-- `logLint`, which is how `lake lint --extra` identifies extra-scope entries.
def dummyExtraTextLinter : Linter where
  run _ cmdStx := do
    unless getLinterExtra (← getLinterOptions) do return
    unless cmdStx.getKind == ``Lean.Parser.Command.declaration do return
    logLint linter.extra cmdStx m!"extra text linter saw a declaration"

initialize addLinter dummyExtraTextLinter
