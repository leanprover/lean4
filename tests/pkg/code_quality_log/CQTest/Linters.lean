import Lean

/-!
Registers `linter.cqTest`, a regular linter that logs one code quality entry (named after the
declaration) for every declaration command via `logCodeQualityEntryIf`, and defines
`#inspect_cq_entries`, which awaits the per-command capture tasks in
`Command.State.codeQualityEntryTasks` and reports what they contain.
-/

open Lean Elab Command Linter

register_option linter.cqTest : Bool := {
  defValue := true
  descr := "enable the code quality test linter"
}

initialize addLinter {
  name := `linter.cqTest
  run := fun stx => do
    if stx.isOfKind ``Lean.Parser.Command.declaration then
      if let some declId := stx.find? (·.isOfKind ``Lean.Parser.Command.declId) then
        logCodeQualityEntryIf linter.cqTest {
          name := toString declId[0].getId
          source := .declaration (← getMainModule) declId[0].getId
          value := .scalar 1.0
        }
}

/--
Reports, for the commands elaborated so far: the number of captured entries per command, the
captured entry names in command order, and the size of the in-scope `codeQualityLogExt` state.
The latter must stay `0`: linter env changes are discarded, so entries reach the final
environment only through the capture tasks merged in `runFrontend`.
-/
elab "#inspect_cq_entries" : command => do
  let tasks := (← get).codeQualityEntryTasks
  logInfo m!"per-command entry counts: {tasks.map (·.get.size)}"
  logInfo m!"captured entries: {tasks.flatMap (·.get) |>.map (·.name)}"
  logInfo m!"entries in current env: {(codeQualityLogExt.getState (← getEnv)).size}"
