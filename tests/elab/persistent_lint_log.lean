import Lean

open Lean

/-! ## Tests for the persistent lint log extension -/

/--
Builds a `MessageLog` containing a single tagged warning whose `MessageData.kind` is
`linter.dummy`, runs `Linter.recordLints`, and returns the resulting extension state.
-/
def testRecordLints : CoreM (Array (Name × String)) := do
  let env ← getEnv
  let tagged : MessageData := .tagged `linter.dummy (m!"unused variable 'x'")
  let msg : Message := {
    fileName := "Test.lean"
    pos := ⟨3, 5⟩
    severity := .warning
    data := tagged
  }
  let log : MessageLog := MessageLog.empty.add msg
  let env ← Linter.recordLints env log
  return (Linter.lintLogExt.getState env).map fun e =>
    (e.linter, e.message.data)

/-- info: #[(`linter.dummy, "unused variable 'x'")] -/
#guard_msgs in
#eval testRecordLints

/-- Untagged messages must be ignored. -/
def testRecordLintsIgnoresUntagged : CoreM Nat := do
  let env ← getEnv
  let msg : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .error
    data := m!"plain error with no tag"
  }
  let log : MessageLog := MessageLog.empty.add msg
  let env ← Linter.recordLints env log
  return (Linter.lintLogExt.getState env).size

/-- info: 0 -/
#guard_msgs in
#eval testRecordLintsIgnoresUntagged

/-- Multiple tagged messages are all recorded, in log order. -/
def testRecordLintsMultiple : CoreM (Array Name) := do
  let env ← getEnv
  let mk (kind : Name) (txt : String) : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .warning
    data := .tagged kind (m!"{txt}")
  }
  let log : MessageLog :=
    MessageLog.empty
      |>.add (mk `linter.a "a")
      |>.add (mk `linter.b "b")
      |>.add (mk `linter.a "a2")
  let env ← Linter.recordLints env log
  return (Linter.lintLogExt.getState env).map (·.linter)

/-- info: #[`linter.a, `linter.b, `linter.a] -/
#guard_msgs in
#eval testRecordLintsMultiple
