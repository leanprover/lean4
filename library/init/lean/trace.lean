/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.lean.format init.data.rbmap init.lean.position init.lean.name init.lean.options

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

namespace Trace

def TraceMap := RBMap Position Trace Position.lt

structure TraceState :=
(opts : Options)
(roots : TraceMap)
(curPos : Option Position)
(curTraces : List Trace)

abbrev TraceT (m : Type → Type u) := StateT TraceState m

instance (m) [Monad m] : Monad (TraceT m) := inferInstanceAs (Monad (StateT TraceState m))

class MonadTracer (m : Type → Type u) :=
(traceRoot {α} : Position → Name → Message → Thunk (m α) → m α)
(traceCtx {α} : Name → Message → Thunk (m α) → m α)

export MonadTracer (traceRoot traceCtx)

def Trace {m} [Monad m] [MonadTracer m] (cls : Name) (msg : Message) : m Unit :=
traceCtx cls msg (pure () : m Unit)

instance (m) [Monad m] : MonadTracer (TraceT m) :=
{ traceRoot := fun α pos cls msg ctx => do {
    st ← get;
    if st.opts.getBool cls = true then do {
      modify $ fun st => {curPos := pos, curTraces := [], ..st};
      a ← ctx.get;
      modify $ fun (st : TraceState) => {roots := st.roots.insert pos ⟨msg, st.curTraces⟩, ..st};
      pure a
    } else ctx.get
  },
  traceCtx := fun α cls msg ctx => do {
    st ← get;
    -- tracing enabled?
    some _ ← pure st.curPos | ctx.get;
    -- Trace class enabled?
    if st.opts.getBool cls = true then do {
      set {curTraces := [], ..st};
      a ← ctx.get;
      modify $ fun (st' : TraceState) => {curTraces := st.curTraces ++ [⟨msg, st'.curTraces⟩], ..st'};
      pure a
    } else
      -- disable tracing inside 'ctx'
      adaptState'
        (fun _ => {curPos := none, ..st})
        (fun st' => {curPos := st.curPos, ..st'})
        ctx.get
  }
}

def TraceT.run {m α} [Monad m] (opts : Options) (x : TraceT m α) : m (α × TraceMap) :=
do (a, st) ← StateT.run x {opts := opts, roots := RBMap.empty, curPos := none, curTraces := []};
   pure (a, st.roots)

end Trace
end Lean
