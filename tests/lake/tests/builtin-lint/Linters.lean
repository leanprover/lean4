import Lean.Linter.EnvLinter

open Lean Meta Lean.Linter Lean.Elab.Command

/-- Option gating the dummy env linter; off by default. Enabled per build via
`--linters=linter.dummyExtra` (or `--linters=linter.all`). -/
register_option linter.dummyExtra : Bool := {
  defValue := false
  descr := "(test) flag declarations whose name ends with 'Extra'"
}

initialize addEnvLinterOption linter.dummyExtra

-- A dummy env linter that flags any declaration whose name ends with "Extra".
-- It runs on a declaration iff `linter.dummyExtra` was enabled when that
-- declaration was built (recorded in the per-declaration snapshot).
@[builtin_env_linter linter.dummyExtra]
public meta def dummyExtra : Lean.Linter.EnvLinter.EnvLinter where
  noErrorsFound := "No declarations ending with 'Extra' found."
  errorsFound := "EXTRA VIOLATIONS:"
  test declName := do
    if declName.toString.endsWith "Extra" then
      return some "declaration name ends with 'Extra'"
    return none

-- A dummy extra text linter: fires on every `declaration` command, but only
-- when `linter.extra = true`. Tags its warnings with `linter.extra` via
-- `logLint`, so it is enabled by `--linters=linter.extra`.
def dummyExtraTextLinter : Linter where
  run cmdStx := do
    unless getLinterValue linter.extra (← getLinterOptions) do return
    unless cmdStx.getKind == ``Lean.Parser.Command.declaration do return
    logLint linter.extra cmdStx m!"extra text linter saw a declaration"

initialize addLinter dummyExtraTextLinter
