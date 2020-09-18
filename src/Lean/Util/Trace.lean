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

structure TraceState :=
(enabled : Bool := true)
(traces  : PersistentArray MessageData := {})

namespace TraceState

instance : Inhabited TraceState := ⟨{}⟩

private def toFormat (traces : PersistentArray MessageData) (sep : Format) : IO Format :=
traces.size.foldM
  (fun i r => do
    curr ← (traces.get! i).format;
    pure $ if i > 0 then r ++ sep ++ curr else r ++ curr)
  Format.nil

end TraceState

class MonadTrace (m : Type → Type) :=
(modifyTraceState : (TraceState → TraceState) → m Unit)
(getTraceState    : m TraceState)

export MonadTrace (getTraceState modifyTraceState)

instance monadTraceTrans (m n) [MonadTrace m] [MonadLift m n] : MonadTrace n :=
{ modifyTraceState := fun f => liftM (modifyTraceState f : m _),
  getTraceState    := liftM (getTraceState : m _) }

variables {α : Type} {m : Type → Type} [Monad m] [MonadTrace m]

def printTraces {m} [Monad m] [MonadTrace m] [MonadIO m] : m Unit := do
traceState ← getTraceState;
traceState.traces.forM $ fun m => do d ← liftIO m.format; liftIO $ IO.println d

def resetTraceState {m} [MonadTrace m] : m Unit :=
modifyTraceState (fun _ => {})

private def checkTraceOptionAux (opts : Options) : Name → Bool
| n@(Name.str p _ _) => opts.getBool n || (!opts.contains n && checkTraceOptionAux p)
| _                  => false

def checkTraceOption (opts : Options) (cls : Name) : Bool :=
if opts.isEmpty then false
else checkTraceOptionAux opts (`trace ++ cls)

private def checkTraceOptionM [MonadOptions m] (cls : Name) : m Bool := do
opts ← getOptions;
pure $ checkTraceOption opts cls

@[inline] def isTracingEnabledFor [MonadOptions m] (cls : Name) : m Bool := do
s ← getTraceState;
if !s.enabled then pure false
else checkTraceOptionM cls

@[inline] def enableTracing (b : Bool) : m Bool := do
s ← getTraceState;
let oldEnabled := s.enabled;
modifyTraceState $ fun s => { s with enabled := b };
pure oldEnabled

@[inline] def getTraces : m (PersistentArray MessageData) := do
s ← getTraceState; pure s.traces

@[inline] def modifyTraces (f : PersistentArray MessageData → PersistentArray MessageData) : m Unit :=
modifyTraceState $ fun s => { s with traces := f s.traces }

@[inline] def setTrace (f : PersistentArray MessageData → PersistentArray MessageData) : m Unit :=
modifyTraceState $ fun s => { s with traces := f s.traces }

@[inline] def setTraceState (s : TraceState) : m Unit :=
modifyTraceState $ fun _ => s

private def addNode (oldTraces : PersistentArray MessageData) (cls : Name) : m Unit :=
modifyTraces $ fun traces =>
  let d := MessageData.tagged cls (MessageData.node traces.toArray);
  oldTraces.push d

private def getResetTraces : m (PersistentArray MessageData) := do
oldTraces ← getTraces;
modifyTraces $ fun _ => {};
pure oldTraces

section
variables [AddMessageContext m] [MonadOptions m]

def addTrace (cls : Name) (msg : MessageData) : m Unit := do
msg ← addMessageContext msg;
modifyTraces $ fun traces => traces.push (MessageData.tagged cls msg)

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : m Unit :=
whenM (isTracingEnabledFor cls) (addTrace cls (msg ()))

@[inline] def traceM (cls : Name) (mkMsg : m MessageData) : m Unit :=
whenM (isTracingEnabledFor cls) (do msg ← mkMsg; addTrace cls msg)

@[inline] def traceCtx [MonadFinally m] (cls : Name) (ctx : m α) : m α := do
b ← isTracingEnabledFor cls;
if !b then do old ← enableTracing false; finally ctx (enableTracing old)
else do
  oldCurrTraces ← getResetTraces;
  finally ctx (addNode oldCurrTraces cls)

-- TODO: delete after fix old frontend
def MonadTracer.trace (cls : Name) (msg : Unit → MessageData) : m Unit :=
trace cls msg

end

def registerTraceClass (traceClassName : Name) : IO Unit :=
registerOption (`trace ++ traceClassName) { group := "trace", defValue := false, descr := "enable/disable tracing for the given module and submodules" }

end Lean

new_frontend

namespace Lean

macro:max "trace!" id:term:max msg:term : term => `(trace $id fun _ => ($msg : MessageData))

end Lean
