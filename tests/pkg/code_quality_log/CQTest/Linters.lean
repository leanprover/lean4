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

Also defines `#inspect_cq_state`, which checks that neither the capture tasks in
`Command.State.codeQualityEntryTasks` nor the entries in `codeQualityLogExt` leak from one command
into the next. The entries reach the final environment only through the per-command capture
tasks merged in `runFrontend`; `PrintEntries.lean` checks what was persisted.
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
Reports the number of capture tasks in the command state and the size of the in-scope
`codeQualityLogExt` state. Both must stay `0`: the language processor starts every command with
an empty task array (the tasks of preceding commands live in their snapshots) and linter env
changes are discarded.
-/
elab "#inspect_cq_state" : command => do
  logInfo m!"capture tasks in state: {(← get).codeQualityEntryTasks.size}"
  logInfo m!"entries in current env: {(codeQualityLogExt.getState (← getEnv)).size}"
