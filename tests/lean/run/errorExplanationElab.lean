import Lean.ErrorExplanation
import Lean.Meta.Basic
open Lean Meta

/-!
# Error explanation non-interactive elaboration tests

Tests the elaborators for `register_error_explanation` and named-error macros.
-/

/-! ## Name and metadata -/

def dummyMetadata : ErrorExplanation.Metadata := {
  summary := "A removed error"
  sinceVersion := "4.21.0"
}

/-- Example -/
register_error_explanation lean.foo {
  summary := "A removed error."
  sinceVersion := "4.0.0"
  removedVersion? := "4.21.0"
}

/-- error: Cannot add explanation: An error explanation already exists for `lean.foo` -/
#guard_msgs in
/-- Duplicate -/
register_error_explanation lean.foo dummyMetadata

/--
error: Invalid name `TopLevelName`: Error explanation names must have two components

Note: The first component of an error explanation name identifies the package from which the error originates, and the second identifies the error itself.
-/
#guard_msgs in
/-- Invalid -/
register_error_explanation TopLevelName dummyMetadata

macro "register_bad_error_explanation" : command =>
  `(/-- -/ register_error_explanation Lean.MacroScoped { summary := "", sinceVersion := "" })
/--
error: Invalid name `Lean.MacroScoped✝`: Error explanations cannot have inaccessible names. This error often occurs when an error explanation is generated using a macro.
-/
#guard_msgs in
register_bad_error_explanation

/-- Example -/
register_error_explanation lean.bar {
  summary := "An error."
  sinceVersion := "4.21.0"
}

/-- warning: The error name `lean.foo` was removed in Lean version 4.21.0 and should not be used. -/
#guard_msgs in
example : MetaM Unit := throwNamedError lean.foo "Error"

example : MetaM Unit := throwNamedError lean.bar "foo"

/-! ## Message data tests -/

def logErrorNames (x : MetaM Unit) : MetaM Unit := do
  Core.setMessageLog {}
  x
  let log ← Core.getMessageLog
  let mut newLog := {}
  for msg in log.toArray do
    newLog := newLog.add <|
      if let some errorName := msg.errorName? then
        { msg with data := m!"({errorName}) " ++ msg.data }
      else
        msg
  Core.setMessageLog newLog

/--
error: (lean.bar) Logged error
---
error: (lean.bar) Logged error with ref
---
warning: (lean.bar) Logged warning
---
warning: (lean.bar) Logged warning with ref
-/
#guard_msgs in
run_meta logErrorNames do
  logNamedError lean.bar m!"Logged error"
  logNamedErrorAt (← getRef) lean.bar m!"Logged error with ref"
  logNamedWarning lean.bar m!"Logged warning"
  logNamedWarningAt (← getRef) lean.bar m!"Logged warning with ref"

/-- error: (lean.bar) Thrown error -/
#guard_msgs in
run_meta logErrorNames do
  try
    throwNamedError lean.bar "Thrown error"
  catch e =>
    logError e.toMessageData

/-- error: (lean.bar) Thrown error with ref -/
#guard_msgs in
run_meta logErrorNames do
  try
    throwNamedErrorAt (← getRef) lean.bar "Thrown error with ref"
  catch e =>
    logError e.toMessageData

/-! # Message name in serialized output -/

def withReportedOutput (x : MetaM α) : MetaM Unit := do
  Core.resetMessageLog
  discard <| x
  let (res, fileName) ← IO.FS.withIsolatedStreams do
    let msgs := (← getThe Core.State).messages
    let fileName := msgs.toList[0]!.fileName
    discard <| Language.reportMessages msgs {}
    pure fileName
  Core.resetMessageLog
  -- We need to omit the path to the file, since that's host-dependent; also drop line
  -- number to avoid noise
  let dropped := res.splitOn fileName |>.map (fun (s : String) => s.dropWhile (· != ' '))
  logInfo ("".intercalate dropped)

/--
info:  error(lean.bar): function is noncomputable
 warning(lean.bar): function is noncomputable
-/
#guard_msgs in
run_meta withReportedOutput do
  let msg := "function is noncomputable"
  logNamedError lean.bar msg
  logNamedWarning lean.bar msg
