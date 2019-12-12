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

class MonadLog (m : Type → Type) :=
(logMessage  {} : Message → m Unit)
(getFileMap  {} : m FileMap)
(getFileName {} : m String)
(getCmdPos   {} : m String.Pos)

export MonadLog (logMessage getFileMap getFileName getCmdPos)

variables {m : Type → Type} [Monad m] [MonadLog m]

def getPosition (pos : Option String.Pos := none) : m Position := do
fileMap ← getFileMap;
cmdPos ← getCmdPos;
pure $ fileMap.toPosition (pos.getD cmdPos)

def mkMessageAt (msgData : MessageData) (severity : MessageSeverity) (pos : Option String.Pos := none) : m Message := do
fileMap ← getFileMap;
fileName ← getFileName;
cmdPos ← getCmdPos;
let pos := fileMap.toPosition (pos.getD cmdPos);
pure { fileName := fileName, pos := pos, data := msgData, severity := severity }

def getPos (stx : Syntax) : m String.Pos :=
match stx.getPos with
| some p => pure p
| none   => getCmdPos

def mkMessage (msgData : MessageData) (severity : MessageSeverity) (stx : Syntax) : m Message := do
pos ← getPos stx;
mkMessageAt msgData severity pos

def logAt (pos : String.Pos) (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
msg ← mkMessageAt msgData severity pos;
logMessage msg

def logInfoAt (pos : String.Pos) (msgData : MessageData) : m Unit :=
logAt pos MessageSeverity.information msgData

def log (stx : Syntax) (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
pos ← getPos stx;
logAt pos severity msgData

def logError (stx : Syntax) (msgData : MessageData) : m Unit :=
log stx MessageSeverity.error msgData

def logWarning (stx : Syntax) (msgData : MessageData) : m Unit :=
log stx MessageSeverity.warning msgData

def logInfo (stx : Syntax) (msgData : MessageData) : m Unit :=
log stx MessageSeverity.information msgData

def logUnknownDecl (stx : Syntax) (declName : Name) : m Unit :=
logError stx ("unknown declaration '" ++ toString declName ++ "'")

end Elab
end Lean
