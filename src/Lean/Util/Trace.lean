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
  enabled : Bool := true
  traces  : PersistentArray TraceElem := {}
  deriving Inhabited


class MonadTrace (m : Type → Type) where
  modifyTraceState : (TraceState → TraceState) → m Unit
  getTraceState    : m TraceState

export MonadTrace (getTraceState modifyTraceState)

instance (m n) [MonadLift m n] [MonadTrace m] : MonadTrace n where
  modifyTraceState := fun f => liftM (modifyTraceState f : m _)
  getTraceState    := liftM (getTraceState : m _)

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m]

def printTraces {m} [Monad m] [MonadTrace m] [MonadLiftT IO m] : m Unit := do
  for {msg, ..} in (← getTraceState).traces do
    IO.println (← msg.format)

def resetTraceState {m} [MonadTrace m] : m Unit :=
  modifyTraceState (fun _ => {})

private def checkTraceOptionAux (opts : Options) : Name → Bool
  | n@(.str p _) => opts.getBool n || (!opts.contains n && checkTraceOptionAux opts p)
  | _            => false

def checkTraceOption (opts : Options) (cls : Name) : Bool :=
  if opts.isEmpty then false
  else checkTraceOptionAux opts (`trace ++ cls)

private def checkTraceOptionM [MonadOptions m] (cls : Name) : m Bool :=
  return checkTraceOption (← getOptions) cls

@[inline] def isTracingEnabledFor [MonadOptions m] (cls : Name) : m Bool := do
  let s ← getTraceState
  if !s.enabled then pure false
  else checkTraceOptionM cls

@[inline] def enableTracing (b : Bool) : m Bool := do
  let s ← getTraceState
  let oldEnabled := s.enabled
  modifyTraceState fun s => { s with enabled := b }
  pure oldEnabled

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

private def addTraceOptions (msg : MessageData) : MessageData :=
  match msg with
  | MessageData.withContext ctx msg => MessageData.withContext { ctx with opts := ctx.opts.setBool `pp.analyze false } msg
  | msg => msg

def addRawTrace (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  let msg := addTraceOptions msg
  modifyTraces (·.push { ref, msg })

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  let msg := addTraceOptions msg
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
    let old ← enableTracing false
    try ctx finally enableTracing old
  else
    let ref ← getRef
    let oldCurrTraces ← getResetTraces
    try ctx finally addNode oldCurrTraces cls ref

private def addTraceNode (oldTraces : PersistentArray TraceElem)
    (cls : Name) (ref : Syntax) (msg : MessageData) (collapsed : Bool) : m Unit :=
  withRef ref do
  let msg ← addMessageContext msg
  let msg := addTraceOptions msg
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

def registerTraceClass (traceClassName : Name) : IO Unit :=
  registerOption (`trace ++ traceClassName) { group := "trace", defValue := false, descr := "enable/disable tracing for the given module and submodules" }

macro "trace[" id:ident "]" s:(interpolatedStr(term) <|> term) : doElem => do
  let msg ← if s.raw.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isTracingEnabledFor cls) then
      Lean.addTrace cls $msg)

private def withNestedTracesFinalizer [Monad m] [MonadTrace m] (ref : Syntax) (currTraces : PersistentArray TraceElem) : m Unit := do
  modifyTraces fun traces =>
    if traces.size == 0 then
      currTraces
    else if traces.size == 1 && traces[0]!.msg.isNest then
      currTraces ++ traces -- No nest of nest
    else
      let d := traces.foldl (init := MessageData.nil) fun d elem =>
        if d.isNil then elem.msg else m!"{d}\n{elem.msg}"
      currTraces.push { ref := ref, msg := MessageData.nestD d }

@[inline] def withNestedTraces [Monad m] [MonadFinally m] [MonadTrace m] [MonadRef m] (x : m α) : m α := do
  let currTraces ← getTraces
  modifyTraces fun _ => {}
  let ref ← getRef
  try x finally withNestedTracesFinalizer ref currTraces

end Lean
