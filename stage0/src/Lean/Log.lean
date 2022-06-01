/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Sorry

namespace Lean

class MonadLog (m : Type → Type) extends MonadFileMap m where
  getRef       : m Syntax
  getFileName  : m String
  logMessage   : Message → m Unit

export MonadLog (getFileName logMessage)

instance (m n) [MonadLift m n] [MonadLog m] : MonadLog n where
  getRef      := liftM (MonadLog.getRef : m _)
  getFileMap  := liftM (getFileMap : m _)
  getFileName := liftM (getFileName : m _)
  logMessage  := fun msg => liftM (logMessage msg : m _ )

variable [Monad m] [MonadLog m] [AddMessageContext m]

def getRefPos : m String.Pos := do
  let ref ← MonadLog.getRef
  return ref.getPos?.getD 0

def getRefPosition : m Position := do
  let fileMap ← getFileMap
  return fileMap.toPosition (← getRefPos)

def logAt (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity := MessageSeverity.error): m Unit :=
  unless severity == MessageSeverity.error && msgData.hasSyntheticSorry do
    let ref    := replaceRef ref (← MonadLog.getRef)
    let pos    := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    let fileMap ← getFileMap
    let msgData ← addMessageContext msgData
    logMessage { fileName := (← getFileName), pos := fileMap.toPosition pos, endPos := fileMap.toPosition endPos, data := msgData, severity := severity }

def logErrorAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.error

def logWarningAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.warning

def logInfoAt (ref : Syntax) (msgData : MessageData) : m Unit :=
  logAt ref msgData MessageSeverity.information

def log (msgData : MessageData) (severity : MessageSeverity := MessageSeverity.error): m Unit := do
  let ref ← MonadLog.getRef
  logAt ref msgData severity

def logError (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.error

def logWarning (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.warning

def logInfo (msgData : MessageData) : m Unit :=
  log msgData MessageSeverity.information

def logTrace (cls : Name) (msgData : MessageData) : m Unit := do
  logInfo (MessageData.tagged cls m!"[{cls}] {msgData}")

def logUnknownDecl (declName : Name) : m Unit :=
  logError m!"unknown declaration '{declName}'"

end Lean
