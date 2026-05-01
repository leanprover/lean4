import Lean.Linter.EnvLinter

open Lean Meta Lean.Linter Lean.Elab.Command

-- A dummy clippy linter that flags any declaration whose name ends with "Clippy".
@[builtin_env_linter clippy] public meta def dummyClippy : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'Clippy' found."
  errorsFound := "CLIPPY VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "Clippy" then
      return some "declaration name ends with 'Clippy'"
    return none

-- A dummy clippy text linter: fires on every `declaration` command, but only
-- when `linter.clippy = true`. Tags its warnings with `linter.clippy` via
-- `logLint`, which is how `lake lint --clippy` identifies clippy-scope entries.
def dummyClippyTextLinter : Linter where
  run cmdStx := do
    unless getLinterClippy (← getLinterOptions) do return
    unless cmdStx.getKind == ``Lean.Parser.Command.declaration do return
    logLint linter.clippy cmdStx m!"clippy text linter saw a declaration"

initialize addLinter dummyClippyTextLinter
