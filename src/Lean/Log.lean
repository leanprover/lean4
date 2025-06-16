/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.Sorry
import Lean.Message

namespace Lean

/--
The `MonadLog` interface for logging error messages.
-/
class MonadLog (m : Type → Type) extends MonadFileMap m where
  /-- Return the current reference syntax being used to provide position information. -/
  getRef       : m Syntax
  /-- The name of the file being processed. -/
  getFileName  : m String
  /-- Return `true` if errors have been logged. -/
  hasErrors    : m Bool
  /-- Log a new message. -/
  logMessage   : Message → m Unit

export MonadLog (getFileName logMessage)

instance (m n) [MonadLift m n] [MonadLog m] : MonadLog n where
  getRef      := liftM (MonadLog.getRef : m _)
  getFileMap  := liftM (getFileMap : m _)
  getFileName := liftM (getFileName : m _)
  hasErrors   := liftM (MonadLog.hasErrors : m _)
  logMessage  := fun msg => liftM (logMessage msg : m _ )

variable [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]

/--
Return the position (as `String.pos`) associated with the current reference syntax (i.e., the syntax object returned by `getRef`.)
-/
def getRefPos : m String.Pos := do
  let ref ← MonadLog.getRef
  return ref.getPos?.getD 0

/--
Return the line and column numbers associated with the current reference syntax (i.e., the syntax object returned by `getRef`.)
-/
def getRefPosition : m Position := do
  let fileMap ← getFileMap
  return fileMap.toPosition (← getRefPos)

/-- If `warningAsError` is set to `true`, then warning messages are treated as errors. -/
register_builtin_option warningAsError : Bool := {
  defValue := false
  descr    := "treat warnings as errors"
}

/--
Log the message `msgData` at the position provided by `ref` with the given `severity`.
If `getRef` has position information but `ref` does not, we use `getRef`.
We use the `fileMap` to find the line and column numbers for the error message.
-/
def logAt (ref : Syntax) (msgData : MessageData)
    (severity : MessageSeverity := MessageSeverity.error) (isSilent : Bool := false) : m Unit :=
  unless severity == .error && msgData.hasSyntheticSorry do
    let severity := if severity == .warning && warningAsError.get (← getOptions) then .error else severity
    let ref    := replaceRef ref (← MonadLog.getRef)
    let pos    := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    let fileMap ← getFileMap
    let msgData ← addMessageContext msgData
    logMessage {
      fileName := (← getFileName)
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      data := msgData
      severity
      isSilent
    }

/-- Log a new error message using the given message data. The position is provided by `ref`. -/
def logErrorAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.error

/-- Log a new warning message using the given message data. The position is provided by `ref`. -/
def logWarningAt [MonadOptions m] (ref : Syntax) (msgData : MessageData) : m Unit := do
  logAt ref msgData .warning

/-- Log a new information message using the given message data. The position is provided by `ref`. -/
def logInfoAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.information

/-- Log a new error/warning/information message using the given message data and `severity`. The position is provided by `getRef`. -/
def log (msgData : MessageData) (severity : MessageSeverity := MessageSeverity.error): m Unit := do
  let ref ← MonadLog.getRef
  logAt ref msgData severity

/-- Log a new error message using the given message data. The position is provided by `getRef`. -/
def logError (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.error

/-- Log a new warning message using the given message data. The position is provided by `getRef`. -/
def logWarning [MonadOptions m] (msgData : MessageData) : m Unit := do
  log msgData (if warningAsError.get (← getOptions) then .error else .warning)

/-- Log a new information message using the given message data. The position is provided by `getRef`. -/
def logInfo (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.information

/-- Log the error message "unknown declaration" -/
def logUnknownDecl (declName : Name) : m Unit :=
  logError m!"unknown declaration '{declName}'"

end Lean
