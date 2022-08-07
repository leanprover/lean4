/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
import Lean.Message
import Lean.MonadEnv

namespace Lean

open Std (PersistentArray)

structure TraceElem where
  ref : Syntax
  msg : MessageData
  deriving Inhabited

structure TraceState where
  traces  : PersistentArray TraceElem := {}
  deriving Inhabited

builtin_initialize inheritedTraceOptions : IO.Ref (Std.HashSet Name) ← IO.mkRef ∅

class MonadTrace (m : Type → Type) where
  modifyTraceState : (TraceState → TraceState) → m Unit
  getTraceState    : m TraceState

export MonadTrace (getTraceState modifyTraceState)

instance (m n) [MonadLift m n] [MonadTrace m] : MonadTrace n where
  modifyTraceState := fun f => liftM (modifyTraceState f : m _)
  getTraceState    := liftM (getTraceState : m _)

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadOptions m] [MonadLiftT IO m]

def printTraces : m Unit := do
  for {msg, ..} in (← getTraceState).traces do
    IO.println (← msg.format)

def resetTraceState : m Unit :=
  modifyTraceState (fun _ => {})

private def checkTraceOption (inherited : Std.HashSet Name) (opts : Options) (cls : Name) : Bool :=
  !opts.isEmpty && go (`trace ++ cls)
where
  go (opt : Name) : Bool :=
    if let some enabled := opts.get? opt then
      enabled
    else if let .str parent _ := opt then
      inherited.contains opt && go parent
    else
      false

def isTracingEnabledFor (cls : Name) : m Bool := do
  let inherited ← (inheritedTraceOptions.get : IO _)
  pure (checkTraceOption inherited (← getOptions) cls)

@[inline] def getTraces : m (PersistentArray TraceElem) := do
  let s ← getTraceState
  pure s.traces

@[inline] def modifyTraces (f : PersistentArray TraceElem → PersistentArray TraceElem) : m Unit :=
  modifyTraceState fun s => { s with traces := f s.traces }

@[inline] def setTraceState (s : TraceState) : m Unit :=
  modifyTraceState fun _ => s

private def addNode (oldTraces : PersistentArray TraceElem) (cls : Name) (ref : Syntax) : m Unit :=
  modifyTraces fun traces =>
    if traces.isEmpty then
      oldTraces
    else
      let d := .trace cls "" (traces.toArray.map fun elem => elem.msg) (collapsed := true)
      oldTraces.push { ref := ref, msg := d }

private def getResetTraces : m (PersistentArray TraceElem) := do
  let oldTraces ← getTraces
  modifyTraces fun _ => {}
  pure oldTraces

section
variable [MonadRef m] [AddMessageContext m] [MonadOptions m]

def addRawTrace (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  modifyTraces (·.push { ref, msg })

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  modifyTraces (·.push { ref, msg := .trace cls msg #[] })

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : m Unit := do
  if (← isTracingEnabledFor cls) then
    addTrace cls (msg ())

@[inline] def traceM (cls : Name) (mkMsg : m MessageData) : m Unit := do
  if (← isTracingEnabledFor cls) then
    let msg ← mkMsg
    addTrace cls msg

@[inline] def traceCtx [MonadFinally m] (cls : Name) (ctx : m α) : m α := do
  let b ← isTracingEnabledFor cls
  if !b then
    ctx
  else
    let ref ← getRef
    let oldCurrTraces ← getResetTraces
    try ctx finally addNode oldCurrTraces cls ref

private def addTraceNode (oldTraces : PersistentArray TraceElem)
    (cls : Name) (ref : Syntax) (msg : MessageData) (collapsed : Bool) : m Unit :=
  withRef ref do
  let msg ← addMessageContext msg
  modifyTraces fun newTraces =>
    oldTraces.push { ref, msg := .trace cls msg (newTraces.toArray.map (·.msg)) collapsed }

def withTraceNode [MonadExcept ε m] (cls : Name) (msg : Except ε α → m MessageData) (k : m α)
    (collapsed := true) : m α := do
  if !(← isTracingEnabledFor cls) then
    k
  else
    let ref ← getRef
    let oldTraces ← getResetTraces
    let res ← observing k
    addTraceNode oldTraces cls ref (← msg res) collapsed
    MonadExcept.ofExcept res

def withTraceNode' [MonadExcept Exception m] (cls : Name) (k : m (α × MessageData)) (collapsed := true) : m α :=
  let msg := fun
    | .ok (_, msg) => return msg
    | .error err => return err.toMessageData
  Prod.fst <$> withTraceNode cls msg k collapsed

end

def registerTraceClass (traceClassName : Name) (inherited := false) : IO Unit := do
  let optionName := `trace ++ traceClassName
  registerOption optionName {
    group := "trace"
    defValue := false
    descr := "enable/disable tracing for the given module and submodules"
  }
  if inherited then
    inheritedTraceOptions.modify (·.insert optionName)

macro "trace[" id:ident "]" s:(interpolatedStr(term) <|> term) : doElem => do
  let msg ← if s.raw.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isTracingEnabledFor cls) then
      Lean.addTrace cls $msg)

def bombEmoji := "💥"
def checkEmoji := "✅"
def crossEmoji := "❌"

def exceptBoolEmoji : Except ε Bool → String
  | .error _ => bombEmoji
  | .ok true => checkEmoji
  | .ok false => crossEmoji

def exceptOptionEmoji : Except ε (Option α) → String
  | .error _ => bombEmoji
  | .ok (some _) => checkEmoji
  | .ok none => crossEmoji

end Lean
