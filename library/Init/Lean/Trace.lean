/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Lean.Message
universe u

namespace Lean

class MonadTracer (m : Type → Type u) :=
(traceCtx {α} : Name → m α → m α)
(trace {} : Name → (Unit → MessageData) → m PUnit)

class MonadTracerAdapter (m : Type → Type) :=
(isTracingEnabledFor {} : Name → m Bool)
(enableTracing {} : Bool → m Unit)
(getTraces {} : m (Array MessageData))
(modifyTraces {} : (Array MessageData → Array MessageData) → m Unit)

namespace MonadTracerAdapter

section
variables {m : Type → Type}
variables [Monad m] [MonadTracerAdapter m]
variables {α : Type}

private def addNode (oldTraces : Array MessageData) (cls : Name) : m Unit :=
modifyTraces $ fun traces =>
  let d := MessageData.tagged cls (MessageData.node traces);
  oldTraces.push d

private def getResetTraces : m (Array MessageData) :=
do oldTraces ← getTraces;
   modifyTraces $ fun _ => #[];
   pure oldTraces

private def addTrace (cls : Name) (msg : MessageData) : m Unit :=
modifyTraces $ fun traces => traces.push (MessageData.tagged cls msg)

@[inline] protected def trace (cls : Name) (msg : Unit → MessageData) : m Unit :=
mwhen (isTracingEnabledFor cls) (addTrace cls (msg ()))

@[inline] def traceCtx (cls : Name) (ctx : m α) : m α :=
do b ← isTracingEnabledFor cls;
   if !b then do enableTracing true; a ← ctx; enableTracing false; pure a
   else do
     oldCurrTraces ← getResetTraces;
     a ← ctx;
     addNode oldCurrTraces cls;
     pure a

end

section
variables {ε : Type} {m : Type → Type}
variables [MonadExcept ε m] [Monad m] [MonadTracerAdapter m]
variables {α : Type}

/- Version of `traceCtx` with exception handling support. -/
@[inline] protected def traceCtxExcept (cls : Name) (ctx : m α) : m α :=
do b ← isTracingEnabledFor cls;
   if !b then do
     enableTracing true;
     catch
       (do a ← ctx; enableTracing false; pure a)
       (fun e => do enableTracing false; throw e)
   else do
     oldCurrTraces ← getResetTraces;
     catch
       (do a ← ctx; addNode oldCurrTraces cls; pure a)
       (fun e => do addNode oldCurrTraces cls; throw e)
end

end MonadTracerAdapter

instance monadTracerAdapter {m : Type → Type} [Monad m] [MonadTracerAdapter m] : MonadTracer m :=
{ traceCtx := @MonadTracerAdapter.traceCtx _ _ _,
  trace    := @MonadTracerAdapter.trace _ _ _ }

instance monadTracerAdapterExcept {ε : Type} {m : Type → Type} [Monad m] [MonadExcept ε m] [MonadTracerAdapter m] : MonadTracer m :=
{ traceCtx := @MonadTracerAdapter.traceCtxExcept _ _ _ _ _,
  trace    := @MonadTracerAdapter.trace _ _ _ }

structure TraceState :=
(enabled : Bool := true)
(traces  : Array MessageData := #[])

namespace TraceState

instance : Inhabited TraceState := ⟨{}⟩

instance : HasFormat TraceState := ⟨fun s => Format.joinArraySep s.traces Format.line⟩

instance : HasToString TraceState := ⟨toString ∘ fmt⟩

end TraceState

class SimpleMonadTracerAdapter (m : Type → Type) :=
(getOptions {}       : m Options)
(modifyTraceState {} : (TraceState → TraceState) → m Unit)
(getTraceState {}    : m TraceState)

namespace SimpleMonadTracerAdapter
variables {m : Type → Type} [Monad m] [SimpleMonadTracerAdapter m]

private def checkTraceOptionAux (opts : Options) : Name → Bool
| n@(Name.mkString p _) => opts.getBool n || (!opts.contains n && checkTraceOptionAux p)
| _                     => false

private def checkTraceOption (optName : Name) : m Bool :=
do opts ← getOptions;
   if opts.isEmpty then pure false
   else pure $ checkTraceOptionAux opts optName

@[inline] def isTracingEnabledFor (cls : Name) : m Bool :=
do s ← getTraceState;
   if !s.enabled then pure false
   else checkTraceOption (`trace ++ cls)

@[inline] def enableTracing (b : Bool) : m Unit :=
modifyTraceState $ fun s => { enabled := b, .. s }

@[inline] def getTraces : m (Array MessageData) :=
do s ← getTraceState; pure s.traces

@[inline] def modifyTraces (f : Array MessageData → Array MessageData) : m Unit :=
modifyTraceState $ fun s => { traces := f s.traces, .. s }

end SimpleMonadTracerAdapter

instance simpleMonadTracerAdapter {m : Type → Type} [SimpleMonadTracerAdapter m] [Monad m] : MonadTracerAdapter m :=
{ isTracingEnabledFor := @SimpleMonadTracerAdapter.isTracingEnabledFor _ _ _,
  enableTracing       := @SimpleMonadTracerAdapter.enableTracing _ _ _,
  getTraces           := @SimpleMonadTracerAdapter.getTraces _ _ _,
  modifyTraces        := @SimpleMonadTracerAdapter.modifyTraces _ _ _ }

export MonadTracer (traceCtx trace)

/-
Recipe for adding tracing support for a monad `M`.

1- Define the instance `SimpleMonadTracerAdapter M` by showing how to retrieve `Options` and
   get/modify `TraceState` object.

2- The `Options` control whether tracing commands are ignored or not.

3- The macro `trace! <cls> <msg>` adds the trace message `<msg>` if `<cls>` is activate and tracing is enabled.

4- We activate the tracing class `<cls>` by setting option `trace.<cls>` to true. If a prefix `p` of `trace.<cls>` is
   set to true, and there isn't a longer prefix `p'` set to false, then `<cls>` is also considered active.

5- `traceCtx <cls> <action>` groups all messages generated by `<action>` into a single `MessageData.node`.
    If `<cls> is not activate, then (all) tracing is disabled while executing `<action>`. This feature is
    useful for the following scenario:
     a) We have a tactic called `mysimp` which uses trace class `mysimp`.
     b) `mysimp invokes the unifier module which uses trace class `unify`.
     c) In the beginning of `mysimp`, we use `traceCtx`.
    In this scenario, by not enabling `mysimp` we also disable the `unify` trace messages produced
    by executing `mysimp`.
-/

end Lean
