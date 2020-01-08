/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Util
import Init.Lean.Elab.Exception

namespace Lean
namespace Elab

class MonadPosInfo (m : Type → Type) :=
(getFileMap  {} : m FileMap)
(getFileName {} : m String)
(getCmdPos   {} : m String.Pos)
(addContext  {} : MessageData → m MessageData)

export MonadPosInfo (getFileMap getFileName getCmdPos)

class MonadLog (m : Type → Type) extends MonadPosInfo m :=
(logMessage  {} : Message → m Unit)

export MonadLog (logMessage)

variables {m : Type → Type} [Monad m]

def getPosition [MonadPosInfo m] (pos : Option String.Pos := none) : m Position := do
fileMap ← getFileMap;
cmdPos ← getCmdPos;
pure $ fileMap.toPosition (pos.getD cmdPos)

def mkMessageAt [MonadPosInfo m] (msgData : MessageData) (severity : MessageSeverity) (pos : Option String.Pos := none) : m Message := do
fileMap ← getFileMap;
fileName ← getFileName;
cmdPos ← getCmdPos;
let pos := fileMap.toPosition (pos.getD cmdPos);
msgData ← MonadPosInfo.addContext msgData;
pure { fileName := fileName, pos := pos, data := msgData, severity := severity }

def getPos [MonadPosInfo m] (stx : Syntax) : m String.Pos :=
match stx.getPos with
| some p => pure p
| none   => getCmdPos

def mkMessage [MonadPosInfo m] (msgData : MessageData) (severity : MessageSeverity) (stx : Syntax) : m Message := do
pos ← getPos stx;
mkMessageAt msgData severity pos

def logAt [MonadLog m] (pos : String.Pos) (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
msg ← mkMessageAt msgData severity pos;
logMessage msg

def logInfoAt [MonadLog m] (pos : String.Pos) (msgData : MessageData) : m Unit :=
logAt pos MessageSeverity.information msgData

def log [MonadLog m] (stx : Syntax) (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
pos ← getPos stx;
logAt pos severity msgData

def logError [MonadLog m] (stx : Syntax) (msgData : MessageData) : m Unit :=
log stx MessageSeverity.error msgData

def logWarning [MonadLog m] (stx : Syntax) (msgData : MessageData) : m Unit :=
log stx MessageSeverity.warning msgData

def logInfo [MonadLog m] (stx : Syntax) (msgData : MessageData) : m Unit :=
log stx MessageSeverity.information msgData

def throwError {α} [MonadPosInfo m] [MonadExcept Exception m] (ref : Syntax) (msgData : MessageData) : m α := do
msg ← mkMessage msgData MessageSeverity.error ref; throw msg

def throwErrorUsingCmdPos {α} [MonadPosInfo m] [MonadExcept Exception m] (msgData : MessageData) : m α := do
cmdPos ← getCmdPos;
msg ← mkMessageAt msgData MessageSeverity.error cmdPos;
throw msg

end Elab
end Lean
