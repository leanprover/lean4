/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
import Lean.Message
import Lean.MonadEnv
universe u

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

namespace TraceState

private def toFormat (traces : PersistentArray TraceElem) (sep : Format) : IO Format :=
  traces.size.foldM
    (fun i r => do
      let curr ← (traces.get! i).msg.format
      pure $ if i > 0 then r ++ sep ++ curr else r ++ curr)
    Format.nil

end TraceState

class MonadTrace (m : Type → Type) where
  modifyTraceState : (TraceState → TraceState) → m Unit
  getTraceState    : m TraceState

export MonadTrace (getTraceState modifyTraceState)

instance (m n) [MonadLift m n] [MonadTrace m] : MonadTrace n where
  modifyTraceState := fun f => liftM (modifyTraceState f : m _)
  getTraceState    := liftM (getTraceState : m _)

variable {α : Type} {m : Type → Type} [Monad m] [MonadTrace m]

def printTraces {m} [Monad m] [MonadTrace m] [MonadLiftT IO m] : m Unit := do
  let traceState ← getTraceState
  traceState.traces.forM fun m => do
    let d ← m.msg.format
    IO.println d

def resetTraceState {m} [MonadTrace m] : m Unit :=
  modifyTraceState (fun _ => {})

private def checkTraceOptionAux (opts : Options) : Name → Bool
  | n@(Name.str p _ _) => opts.getBool n || (!opts.contains n && checkTraceOptionAux opts p)
  | _                  => false

def checkTraceOption (opts : Options) (cls : Name) : Bool :=
  if opts.isEmpty then false
  else checkTraceOptionAux opts (`trace ++ cls)

private def checkTraceOptionM [MonadOptions m] (cls : Name) : m Bool := do
  let opts ← getOptions
  pure $ checkTraceOption opts cls

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
      let d := MessageData.tagged (cls ++ `_traceCtx) (MessageData.node (traces.toArray.map fun elem => elem.msg))
      oldTraces.push { ref := ref, msg := d }

private def getResetTraces : m (PersistentArray TraceElem) := do
  let oldTraces ← getTraces
  modifyTraces fun _ => {}
  pure oldTraces

section
variable [MonadRef m] [AddMessageContext m] [MonadOptions m]

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  let msg := addTraceOptions msg
  modifyTraces fun traces => traces.push { ref := ref, msg := MessageData.tagged (cls ++ `_traceMsg) m!"[{cls}] {msg}" }
where
  addTraceOptions : MessageData → MessageData
    | MessageData.withContext ctx msg => MessageData.withContext { ctx with opts := ctx.opts.setBool `pp.analyze false } msg
    | msg => msg

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

-- TODO: delete after fix old frontend
def MonadTracer.trace (cls : Name) (msg : Unit → MessageData) : m Unit :=
  Lean.trace cls msg

end

def registerTraceClass (traceClassName : Name) : IO Unit :=
  registerOption (`trace ++ traceClassName) { group := "trace", defValue := false, descr := "enable/disable tracing for the given module and submodules" }

macro "trace[" id:ident "]" s:(interpolatedStr(term) <|> term) : doElem => do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $s) else `(($s : MessageData))
  `(doElem| do
    let cls := $(quote id.getId)
    if (← Lean.isTracingEnabledFor cls) then
      Lean.addTrace cls $msg)

private def withNestedTracesFinalizer [Monad m] [MonadTrace m] (ref : Syntax) (currTraces : PersistentArray TraceElem) : m Unit := do
  modifyTraces fun traces =>
    if traces.size == 0 then
      currTraces
    else if traces.size == 1 && traces[0].msg.isNest then
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
