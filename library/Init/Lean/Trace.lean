/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Lean.Format
import Init.Data.RBMap
import Init.Lean.Position
import Init.Lean.Name
import Init.Lean.Options

universe u

namespace Lean

inductive Message
| fromFormat (fmt : Format)

instance : HasCoe Format Message :=
⟨Message.fromFormat⟩

inductive Trace
| mk (msg : Message) (subtraces : List Trace)

partial def Trace.pp : Trace → Format
| Trace.mk (Message.fromFormat fmt) subtraces =>
fmt ++ Format.nest 2 (Format.join $ subtraces.map (fun t => Format.line ++ t.pp))

instance traceFormat : HasFormat Trace := ⟨Trace.pp⟩

namespace Trace

def TraceMap := RBMap Position Trace Position.lt

structure TraceState :=
(opts : Options)
(roots : TraceMap)
(curPos : Option Position)
(curTraces : List Trace)

def TraceT (m : Type → Type u) := StateT TraceState m

instance (m) [Monad m] : Monad (TraceT m) := inferInstanceAs (Monad (StateT TraceState m))

class MonadTracer (m : Type → Type u) :=
(traceRoot {α} : Position → Name → Message → (Unit → m α) → m α)
(traceCtx {α} : Name → Message → (Unit → m α) → m α)

export MonadTracer (traceRoot traceCtx)

def trace {m} [Monad m] [MonadTracer m] (cls : Name) (msg : Message) : m Unit :=
traceCtx cls msg (fun _ => pure ())

namespace TraceT
variables {α : Type} {m : Type → Type u} [Monad m]

def traceRoot (pos : Position) (cls : Name) (msg : Message) (ctx : Unit → StateT TraceState m α) : StateT TraceState m α :=
do s ← get;
   if s.opts.getBool cls then do {
     modify $ fun s => { curPos := pos, curTraces := [], ..s };
     a ← ctx ();
     modify $ fun s => { roots := s.roots.insert pos (Trace.mk msg s.curTraces), curTraces := [], ..s };
     pure a
   } else ctx ()

def traceCtx (cls : Name) (msg : Message) (ctx : Unit → StateT TraceState m α) : StateT TraceState m α :=
do s ← get;
   -- tracing enabled?
   match s.curPos with
   | none   => ctx ()
   | some _ =>
     -- Trace class enabled?
     if s.opts.getBool cls then do {
       let curTraces := s.curTraces;
       set { curTraces := [], .. s };
       a ← ctx ();
       modify $ fun s => { curTraces := curTraces ++ [Trace.mk msg s.curTraces], ..s };
       pure a
   } else do {
     let curPos := s.curPos;
     modify $ fun s => { curPos := none, .. s };
     a ← ctx ();
     modify $ fun s => { curPos := curPos, .. s };
     pure a
   }

end TraceT

instance tracerTraceT (m) [Monad m] : MonadTracer (TraceT m) :=
{ traceRoot := fun α => @TraceT.traceRoot α _ _,
  traceCtx  := fun α => @TraceT.traceCtx α _ _ }

instance tracerEx (m) {ε} [Monad m] [MonadTracer m] : MonadTracer (ExceptT ε m) :=
{ traceRoot := fun α pos cls msg ctx => (MonadTracer.traceRoot pos cls msg ctx : m (Except ε α)),
  traceCtx  := fun α cls msg ctx => (MonadTracer.traceCtx cls msg ctx : m (Except ε α)) }

def TraceT.run {m α} [Monad m] (opts : Options) (x : TraceT m α) : m (α × TraceMap) :=
do (a, st) ← StateT.run x {opts := opts, roots := RBMap.empty, curPos := none, curTraces := []};
   pure (a, st.roots)

end Trace
end Lean
