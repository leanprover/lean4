/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Util
import Lean.Elab.Exception

namespace Lean
namespace Elab

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
Core.replaceRef ref oldRef

class MonadPosInfo (m : Type → Type) :=
(getFileMap   : m FileMap)
(getFileName  : m String)
(getRef       : m Syntax)
(addContext   : MessageData → m MessageData)

export MonadPosInfo (getFileMap getFileName getRef)

class MonadLog (m : Type → Type) extends MonadPosInfo m :=
(logMessage   : Message → m Unit)

export MonadLog (logMessage)

variables {m : Type → Type} [Monad m]

def getRefPos [MonadPosInfo m] : m String.Pos := do
ref ← getRef;
pure $ ref.getPos.getD 0

def getRefPosition [MonadPosInfo m] : m Position := do
pos ← getRefPos;
fileMap ← getFileMap;
pure $ fileMap.toPosition pos

def mkMessageAt [MonadPosInfo m] (msgData : MessageData) (severity : MessageSeverity) (pos : String.Pos) : m Message := do
fileMap ← getFileMap;
fileName ← getFileName;
let pos := fileMap.toPosition pos;
msgData ← MonadPosInfo.addContext msgData;
pure { fileName := fileName, pos := pos, data := msgData, severity := severity }

def mkMessage [MonadPosInfo m] (msgData : MessageData) (severity : MessageSeverity) : m Message := do
pos ← getRefPos;
mkMessageAt msgData severity pos

def logAt [MonadLog m] (pos : String.Pos) (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
msg ← mkMessageAt msgData severity pos;
logMessage msg

def logInfoAt [MonadLog m] (pos : String.Pos) (msgData : MessageData) : m Unit :=
logAt pos MessageSeverity.information msgData

def log [MonadLog m] (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
pos ← getRefPos;
logAt pos severity msgData

def logError [MonadLog m] (msgData : MessageData) : m Unit :=
log MessageSeverity.error msgData

def logWarning [MonadLog m] (msgData : MessageData) : m Unit :=
log MessageSeverity.warning msgData

def logInfo [MonadLog m] (msgData : MessageData) : m Unit :=
log MessageSeverity.information msgData

def throwError {α} [MonadPosInfo m] [MonadExcept Exception m] (msgData : MessageData) : m α := do
msg ← mkMessage msgData MessageSeverity.error;
throw (Exception.error msg)

end Elab
end Lean
