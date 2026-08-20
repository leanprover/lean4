import Lean

open Lean Lean.Linter

/-!
## Tests for the persistent code quality log extension

Code quality entries are logged by `Lean.Linter.logCodeQualityEntry` as silent messages carrying
an `MessageData.ofCodeQualityEntry` constructor, tagged with the producing linter's option name.
`Lean.Linter.recordLints` extracts them and persists them into `codeQualityLogExt` together with
the linter name (without position information), keeping them out of `lintLogExt`.
-/

/-- Build a message shaped like the output of `Linter.logCodeQualityEntry`, including the
`.withContext` wrapper that `addMessageContext` adds in `logAt`. -/
def mkCQMessage (linter : Name) (e : CodeQuality.Entry) : CoreM Message := do
  let data ← addMessageContext <| .ofCodeQualityEntry e <| .tagged linter <|
    .tagged codeQualityMessageTag .nil
  return {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .information
    isSilent := true
    data
  }

/--
Records a single code-quality-shaped message and returns the recorded (linter, metric) pairs
together with the size of the lint log, which must stay empty.
-/
def testRecordCodeQualityEntry : CoreM (Array (Name × String) × Nat) := do
  let e : CodeQuality.Entry :=
    { name := "dummy_metric", source := .module `Test, value := .scalar 1.0 }
  let log := MessageLog.empty.add (← mkCQMessage `linter.dummy e)
  let env ← Linter.recordLints default (← getEnv) #[(none, log)]
  return ((codeQualityLogExt.getState env).map fun r => (r.linter, r.entry.name),
          (lintLogExt.getState env).size)

/-- info: (#[(`linter.dummy, "dummy_metric")], 0) -/
#guard_msgs in
#eval testRecordCodeQualityEntry

/-- Multiple entries across commands are recorded in log order, each keyed by its linter. -/
def testRecordCodeQualityEntryMultiple : CoreM (Array (Name × String)) := do
  let mk (linter : Name) (name : String) : CoreM Message :=
    mkCQMessage linter { name, source := .module `Test, value := .scalar 1.0 }
  let log₁ := MessageLog.empty.add (← mk `linter.one "a") |>.add (← mk `linter.two "b")
  let log₂ := MessageLog.empty.add (← mk `linter.one "c")
  let env ← Linter.recordLints default (← getEnv) #[(none, log₁), (none, log₂)]
  return (codeQualityLogExt.getState env).map fun r => (r.linter, r.entry.name)

/-- info: #[(`linter.one, "a"), (`linter.two, "b"), (`linter.one, "c")] -/
#guard_msgs in
#eval testRecordCodeQualityEntryMultiple

/-- A code-quality message without a linter-name tag has an anonymous kind and is dropped. -/
def testRecordCodeQualityDropsUntagged : CoreM Nat := do
  let e : CodeQuality.Entry :=
    { name := "untagged_metric", source := .module `Test, value := .scalar 1.0 }
  let data ← addMessageContext <| .ofCodeQualityEntry e <| .tagged codeQualityMessageTag .nil
  let msg : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .information
    isSilent := true
    data
  }
  let env ← Linter.recordLints default (← getEnv) #[(none, MessageLog.empty.add msg)]
  return (codeQualityLogExt.getState env).size

/-- info: 0 -/
#guard_msgs in
#eval testRecordCodeQualityDropsUntagged

/-- Linter warnings and plain messages must not be recorded as code quality entries. -/
def testRecordCodeQualityIgnoresOthers : CoreM Nat := do
  let lintMsg : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .warning
    data := .tagged `linter.dummy (.tagged linterMessageTag m!"unused variable 'x'")
  }
  let plainMsg : Message := {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .error
    data := m!"plain error"
  }
  let log := MessageLog.empty.add lintMsg |>.add plainMsg
  let env ← Linter.recordLints default (← getEnv) #[(none, log)]
  return (codeQualityLogExt.getState env).size

/-- info: 0 -/
#guard_msgs in
#eval testRecordCodeQualityIgnoresOthers
