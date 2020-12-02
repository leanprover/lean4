/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Util
import Lean.Elab.Exception

namespace Lean.Elab

class MonadLog (m : Type → Type) where
  getRef       : m Syntax
  getFileMap   : m FileMap
  getFileName  : m String
  logMessage   : Message → m Unit

instance (m n) [MonadLog m] [MonadLift m n] : MonadLog n := {
  getRef      := liftM (MonadLog.getRef : m _),
  getFileMap  := liftM (MonadLog.getFileMap : m _),
  getFileName := liftM (MonadLog.getFileName : m _),
  logMessage  := fun msg => liftM (MonadLog.logMessage msg : m _ )
}

export MonadLog (getFileMap getFileName logMessage)

variables {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m]

def getRefPos : m String.Pos := do
  let ref ← MonadLog.getRef
  return ref.getPos.getD 0

def getRefPosition : m Position := do
  let fileMap ← getFileMap
  return fileMap.toPosition (← getRefPos)

def logAt (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity := MessageSeverity.error): m Unit := do
  let ref  := replaceRef ref (← MonadLog.getRef)
  let pos  := ref.getPos.getD 0
  let fileMap ← getFileMap
  let msgData ← addMessageContext msgData
  logMessage { fileName := (← getFileName), pos := fileMap.toPosition pos, data := msgData, severity := severity }

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

def logException [MonadLiftT IO m] (ex : Exception) : m Unit := do
  match ex with
  | Exception.error ref msg => logErrorAt ref msg
  | Exception.internal id _ =>
    unless id == abortExceptionId do
      let name ← id.getName
      logError m!"internal exception: {name}"

def logTrace (cls : Name) (msgData : MessageData) : m Unit := do
  logInfo (MessageData.tagged cls msgData)

@[inline] def trace [MonadOptions m] (cls : Name) (msg : Unit → MessageData) : m Unit := do
  if checkTraceOption (← getOptions) cls then
    logTrace cls (msg ())

def logDbgTrace [MonadOptions m] (msg : MessageData) : m Unit := do
  trace `Elab.debug fun _ => msg

end Lean.Elab
