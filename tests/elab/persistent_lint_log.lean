import Lean

open Lean

/-! ## Tests for the persistent lint log extension -/

/-- Build a linter-shaped `MessageData`: the outer tag is the linter option name and
the inner tag is `Linter.linterMessageTag`, matching what `Linter.logLint` produces. -/
def mkLinterMsg (kind : Name) (body : MessageData) : MessageData :=
  .tagged kind (.tagged Linter.linterMessageTag body)

/--
Builds a `MessageLog` containing a single linter-shaped warning whose `MessageData.kind` is
`linter.dummy`, runs `Linter.recordLints`, and returns the resulting extension state.
-/
def testRecordLints : CoreM (Array (Name × String)) := do
  let env ← getEnv
  let msg : Message := {
    fileName := "Test.lean"
    pos := ⟨3, 5⟩
    severity := .warning
    data := mkLinterMsg `linter.dummy m!"unused variable 'x'"
  }
  let log : MessageLog := MessageLog.empty.add msg
  let env ← Linter.recordLints default env #[(none, log)]
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
  let env ← Linter.recordLints default env #[(none, log)]
  return (Linter.lintLogExt.getState env).size

/-- info: 0 -/
#guard_msgs in
#eval testRecordLintsIgnoresUntagged

/-- Tagged messages that were not produced by a linter (e.g. named errors,
unknown-identifier messages) must not be recorded. -/
def testRecordLintsIgnoresNonLinterTags : CoreM Nat := do
  let env ← getEnv
  let msg : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .error
    data := .tagged `lean.unknownIdentifier m!"unknown identifier 'foo'"
  }
  let log : MessageLog := MessageLog.empty.add msg
  let env ← Linter.recordLints default env #[(none, log)]
  return (Linter.lintLogExt.getState env).size

/-- info: 0 -/
#guard_msgs in
#eval testRecordLintsIgnoresNonLinterTags

/-- Multiple linter-shaped messages are all recorded, in log order. -/
def testRecordLintsMultiple : CoreM (Array Name) := do
  let env ← getEnv
  let mk (kind : Name) (txt : String) : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .warning
    data := mkLinterMsg kind m!"{txt}"
  }
  let log : MessageLog :=
    MessageLog.empty
      |>.add (mk `linter.a "a")
      |>.add (mk `linter.b "b")
      |>.add (mk `linter.a "a2")
  let env ← Linter.recordLints default env #[(none, log)]
  return (Linter.lintLogExt.getState env).map (·.linter)

/-- info: #[`linter.a, `linter.b, `linter.a] -/
#guard_msgs in
#eval testRecordLintsMultiple
