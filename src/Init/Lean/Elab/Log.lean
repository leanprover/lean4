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

def getPosition (pos : Option String.Pos := none) : m Position :=
do fileMap ← getFileMap;
   cmdPos ← getCmdPos;
   pure $ fileMap.toPosition (pos.getD cmdPos)

def mkMessage (msg : MessageData) (pos : Option String.Pos := none) : m Message :=
do fileMap ← getFileMap;
   fileName ← getFileName;
   cmdPos ← getCmdPos;
   let pos := fileMap.toPosition (pos.getD cmdPos);
   pure { fileName := fileName, pos := pos, data := msg }

def logErrorAt (pos : String.Pos) (errorMsg : String) : m Unit :=
do msg ← mkMessage errorMsg pos; logMessage msg

def logErrorUsingCmdPos (errorMsg : String) : m Unit :=
do cmdPos ← getCmdPos;
   logErrorAt cmdPos errorMsg

def getPos (stx : Syntax) : m String.Pos :=
match stx.getPos with
| some p => pure p
| none   => getCmdPos

def logError (stx : Syntax) (errorMsg : String) : m Unit :=
do pos ← getPos stx;
   logErrorAt pos errorMsg

def logElabException (e : Exception) : m Unit :=
match e with
| Exception.silent    => pure () -- do nothing since message was already logged
| Exception.msg m     => logMessage m
| Exception.io e      => do msg ← mkMessage (toString e); logMessage msg
| Exception.other e   => do msg ← mkMessage e; logMessage msg
| Exception.meta e    => do msg ← mkMessage e.toMessageData; logMessage msg
| Exception.kernel e  =>
  match e with
  | KernelException.other msg => do msg ← mkMessage msg; logMessage msg
  | _                         => do msg ← mkMessage "kernel exception"; logMessage msg -- TODO(pretty print them)

def logErrorAndThrow {α} [MonadExcept Exception m] (stx : Syntax) (errorMsg : String) : m α :=
do logError stx errorMsg;
   throw Exception.silent

def logUnknownDecl (stx : Syntax) (declName : Name) : m Unit :=
logError stx ("unknown declaration '" ++ toString declName ++ "'")

end Elab
end Lean
