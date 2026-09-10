import Lean

/-!
Registers two linters that log code quality entries:

* `linter.cqTest`, a regular linter that, for every declaration command, logs one entry named
  after the declaration via `logCodeQualityEntryIf` (attributed to `linter.cqTest` and gated by
  it) plus one unattributed entry named `raw:<decl>` via `logCodeQualityEntry` (recorded even
  when the option is off);
* a stateful linter that logs one attributed entry per declaration, named `stateful:<decl>:<n>`
  where `n` is the running declaration count threaded through its persistent state across
  commands.

Also defines `#inspect_cq_entries`, which awaits the per-command capture tasks in
`Command.State.codeQualityEntryTasks` and reports what they contain. Every command contributes
three tasks, in order: regular linters, module linters (empty except on the terminal command),
and stateful linters. Entries are shown as `<linter option>/<entry name>`, with `_` for
unattributed entries.
-/

open Lean Elab Command Linter

register_option linter.cqTest : Bool := {
  defValue := true
  descr := "enable the code quality test linters"
}

/-- The identifier of a declaration command, if `stx` is one. -/
def declName? (stx : Syntax) : Option Name := do
  guard <| stx.isOfKind ``Lean.Parser.Command.declaration
  let declId ← stx.find? (·.isOfKind ``Lean.Parser.Command.declId)
  return declId[0].getId

initialize addLinter {
  name := `linter.cqTest
  run := fun stx => do
    if let some n := declName? stx then
      logCodeQualityEntryIf linter.cqTest {
        name := toString n
        source := .declaration (← getMainModule) n
        value := .scalar 1.0
      }
      logCodeQualityEntry {
        name := s!"raw:{n}"
        source := .declaration (← getMainModule) n
        value := .scalar 1.0
      }
}

initialize
  let _ ← registerStatefulLinter (τ := Unit) (0 : Nat)
    (post := fun stx count _ _ _ => do
      let some n := declName? stx | return count
      let count := count + 1
      logCodeQualityEntryIf linter.cqTest {
        name := s!"stateful:{n}:{count}"
        source := .declaration (← getMainModule) n
        value := .scalar count.toFloat
      }
      return count)

/--
Reports, for the commands elaborated so far: the number of captured entries per task (three tasks
per command: regular, module, and stateful linters), the captured entry names in task order, and
the size of the in-scope `codeQualityLogExt` state. The latter must stay `0`: linter env changes
are discarded, so entries reach the final environment only through the capture tasks merged in
`runFrontend`.
-/
elab "#inspect_cq_entries" : command => do
  let tasks := (← get).codeQualityEntryTasks
  let describe (e : CodeQualityLogEntry) : String :=
    s!"{(e.linter?.map toString).getD "_"}/{e.entry.name}"
  logInfo m!"per-command entry counts: {tasks.map (·.get.size)}"
  let described := tasks.flatMap (·.get) |>.map describe
  logInfo m!"captured entries: [{", ".intercalate described.toList}]"
  logInfo m!"entries in current env: {(codeQualityLogExt.getState (← getEnv)).size}"
