import Lean

open Lean Lean.Linter

/-!
## Tests for the persistent code quality log extension

Code quality entries are logged by `Lean.Linter.logCodeQualityEntry` as silent messages carrying
an `MessageData.ofCodeQualityEntry` constructor. `Lean.Linter.recordLints` extracts them and
persists them into `codeQualityLogExt` (without position information), keeping them out of
`lintLogExt`.
-/

/-- Build a message shaped like the output of `Linter.logCodeQualityEntry`, including the
`.withContext` wrapper that `addMessageContext` adds in `logAt`. -/
def mkCQMessage (e : CodeQuality.Entry) : CoreM Message := do
  let data ← addMessageContext <| .ofCodeQualityEntry e <| .tagged codeQualityMessageTag .nil
  return {
    fileName := "Test.lean"
    pos := ⟨1, 1⟩
    severity := .information
    isSilent := true
    data
  }

/--
Records a single code-quality-shaped message and returns the recorded entry names together with
the size of the lint log, which must stay empty.
-/
def testRecordCodeQualityEntry : CoreM (Array String × Nat) := do
  let e : CodeQuality.Entry :=
    { name := "dummy_metric", source := .module `Test, value := .scalar 1.0 }
  let log := MessageLog.empty.add (← mkCQMessage e)
  let env ← Linter.recordLints default (← getEnv) #[(none, log)]
  return ((codeQualityLogExt.getState env).map (·.name), (lintLogExt.getState env).size)

/-- info: (#["dummy_metric"], 0) -/
#guard_msgs in
#eval testRecordCodeQualityEntry

/-- Multiple entries across commands are recorded in log order. -/
def testRecordCodeQualityEntryMultiple : CoreM (Array String) := do
  let mk (name : String) : CoreM Message :=
    mkCQMessage { name, source := .module `Test, value := .scalar 1.0 }
  let log₁ := MessageLog.empty.add (← mk "a") |>.add (← mk "b")
  let log₂ := MessageLog.empty.add (← mk "c")
  let env ← Linter.recordLints default (← getEnv) #[(none, log₁), (none, log₂)]
  return (codeQualityLogExt.getState env).map (·.name)

/-- info: #["a", "b", "c"] -/
#guard_msgs in
#eval testRecordCodeQualityEntryMultiple

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
