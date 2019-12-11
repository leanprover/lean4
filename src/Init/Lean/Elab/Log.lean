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

def mkMessage (msgData : MessageData) (severity : MessageSeverity) (pos : Option String.Pos := none) : m Message := do
fileMap ← getFileMap;
fileName ← getFileName;
cmdPos ← getCmdPos;
let pos := fileMap.toPosition (pos.getD cmdPos);
pure { fileName := fileName, pos := pos, data := msgData, severity := severity }

def getPos (stx : Syntax) : m String.Pos :=
match stx.getPos with
| some p => pure p
| none   => getCmdPos

def logAt (pos : String.Pos) (severity : MessageSeverity) (msgData : MessageData) : m Unit := do
msg ← mkMessage msgData severity pos;
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

def logErrorUsingCmdPos (msgData : MessageData) : m Unit := do
cmdPos ← getCmdPos;
logAt cmdPos MessageSeverity.error msgData

def logElabException (e : Exception) : m Unit :=
match e with
| Exception.silent    => pure () -- do nothing since message was already logged
| Exception.msg m     => logMessage m
| Exception.io e      => logErrorUsingCmdPos (toString e)
| Exception.other e   => logErrorUsingCmdPos e
| Exception.meta e    => logErrorUsingCmdPos e.toMessageData
| Exception.kernel e  => logErrorUsingCmdPos e.toMessageData

def logErrorAndThrow {α} [MonadExcept Exception m] (stx : Syntax) (errorMsg : MessageData) : m α := do
logError stx errorMsg;
throw Exception.silent

def logUnknownDecl (stx : Syntax) (declName : Name) : m Unit :=
logError stx ("unknown declaration '" ++ toString declName ++ "'")

private def resetTraceState {m : Type → Type} [Monad m] [SimpleMonadTracerAdapter m] : m TraceState := do
trace ← SimpleMonadTracerAdapter.getTraceState;
SimpleMonadTracerAdapter.setTraceState {};
pure trace

private def saveNewTraceAsMessagesAt {m : Type → Type} [Monad m] [MonadLog m] [SimpleMonadTracerAdapter m]
    (pos : String.Pos) (oldTraceState : TraceState) : m Unit := do
traces ← SimpleMonadTracerAdapter.getTraces;
traces.forM $ logInfoAt pos;
SimpleMonadTracerAdapter.setTraceState oldTraceState

@[inline] def tracingAtPos {α} {m : Type → Type} [Monad m] [MonadExcept Exception m] [MonadLog m] [SimpleMonadTracerAdapter m]
    (pos : String.Pos) (x : m α) : m α := do
oldTraceState ← resetTraceState;
finally x (saveNewTraceAsMessagesAt pos oldTraceState)

/-- If `ref` provides position information, then execute `x` and save generated trace messages in the `MessageLog` using the position.
    Otherwise, just execute `x` -/
@[inline] def tracingAt {α} {m : Type → Type} [Monad m] [MonadExcept Exception m] [MonadLog m] [SimpleMonadTracerAdapter m] (ref : Syntax) (x : m α) : m α :=
match ref.getPos with
| none     => x
| some pos => tracingAtPos pos x

end Elab
end Lean
