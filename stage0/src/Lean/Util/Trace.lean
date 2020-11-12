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

structure TraceElem :=
  (ref : Syntax)
  (msg : MessageData)

instance : Inhabited TraceElem :=
  ⟨⟨arbitrary _, arbitrary _⟩⟩

structure TraceState :=
  (enabled : Bool := true)
  (traces  : PersistentArray TraceElem := {})

namespace TraceState

instance : Inhabited TraceState := ⟨{}⟩

private def toFormat (traces : PersistentArray TraceElem) (sep : Format) : IO Format :=
  traces.size.foldM
    (fun i r => do
      let curr ← (traces.get! i).msg.format
      pure $ if i > 0 then r ++ sep ++ curr else r ++ curr)
    Format.nil

end TraceState

class MonadTrace (m : Type → Type) :=
  (modifyTraceState : (TraceState → TraceState) → m Unit)
  (getTraceState    : m TraceState)

export MonadTrace (getTraceState modifyTraceState)

instance (m n) [MonadTrace m] [MonadLift m n] : MonadTrace n :=
  { modifyTraceState := fun f => liftM (modifyTraceState f : m _),
    getTraceState    := liftM (getTraceState : m _) }

variables {α : Type} {m : Type → Type} [Monad m] [MonadTrace m]

def printTraces {m} [Monad m] [MonadTrace m] [MonadIO m] : m Unit := do
  let traceState ← getTraceState
  traceState.traces.forM fun m => do
    let d ← liftIO m.msg.format
    liftIO $ IO.println d

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
      let d := MessageData.tagged cls (MessageData.node (traces.toArray.map fun elem => elem.msg))
      oldTraces.push { ref := ref, msg := d }

private def getResetTraces : m (PersistentArray TraceElem) := do
  let oldTraces ← getTraces
  modifyTraces fun _ => {}
  pure oldTraces

section
variables [Ref m] [AddMessageContext m] [MonadOptions m]

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
  let ref ← getRef
  let msg ← addMessageContext msg
  modifyTraces fun traces => traces.push { ref := ref, msg := MessageData.tagged cls msg }

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

macro:max "trace!" id:term:max msg:term : term =>
  `(trace $id fun _ => ($msg : MessageData))

syntax "trace[" ident "]!" (interpolatedStr(term) <|> term) : term

macro_rules
  | `(trace[$id]! $s) =>
    if s.getKind == interpolatedStrKind then
      `(Lean.trace $(quote id.getId) fun _ => msg! $s)
    else
      `(Lean.trace $(quote id.getId) fun _ => ($s : MessageData))

variables {α : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadOptions m] [Ref m]

def withNestedTraces [MonadFinally m] (x : m α) : m α := do
  let s ← getTraceState
  if !s.enabled then
    x
  else
    let currTraces ← getTraces
    modifyTraces fun _ => {}
    let ref ← getRef
    try
      x
    finally
      modifyTraces fun traces =>
        if traces.size == 0 then
          currTraces
        else if traces.size == 1 && traces[0].msg.isNest then
          currTraces ++ traces -- No nest of nest
        else
          let d := traces.foldl (init := MessageData.nil) fun d elem =>
            if d.isNil then elem.msg else msg!"{d}\n{elem.msg}"
          currTraces.push { ref := ref, msg := MessageData.nestD d }

end Lean
