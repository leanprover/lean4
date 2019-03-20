/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.lean.format init.data.rbmap init.lean.position init.lean.name init.lean.options

universe u

namespace lean

inductive message
| fromFormat (fmt : format)

instance : hasCoe format message :=
⟨message.fromFormat⟩

inductive trace
| mk (msg : message) (subtraces : list trace)

def trace.pp : trace → format
| (trace.mk (message.fromFormat fmt) subtraces) :=
fmt ++ format.nest 2 (format.join $ subtraces.map (λ t, format.line ++ t.pp))

namespace trace

def traceMap := rbmap position trace (<)

structure traceState :=
(opts : options)
(roots : traceMap)
(curPos : option position)
(curTraces : list trace)

def traceT (m : Type → Type u) := stateT traceState m
local attribute [reducible] traceT

instance (m) [monad m] : monad (traceT m) := inferInstance

class monadTracer (m : Type → Type u) :=
(traceRoot {α} : position → name → message → thunk (m α) → m α)
(traceCtx {α} : name → message → thunk (m α) → m α)

export monadTracer (traceRoot traceCtx)

def trace {m} [monad m] [monadTracer m] (cls : name) (msg : message) : m unit :=
traceCtx cls msg (pure () : m unit)

instance (m) [monad m] : monadTracer (traceT m) :=
{ traceRoot := λ α pos cls msg ctx, do {
    st ← get,
    if st.opts.getBool cls = some tt then do {
      modify $ λ st, {curPos := pos, curTraces := [], ..st},
      a ← ctx.get,
      modify $ λ (st : traceState), {roots := st.roots.insert pos ⟨msg, st.curTraces⟩, ..st},
      pure a
    } else ctx.get
  },
  traceCtx := λ α cls msg ctx, do {
    st ← get,
    -- tracing enabled?
    some _ ← pure st.curPos | ctx.get,
    -- trace class enabled?
    if st.opts.getBool cls = some tt then do {
      put {curTraces := [], ..st},
      a ← ctx.get,
      modify $ λ (st' : traceState), {curTraces := st.curTraces ++ [⟨msg, st'.curTraces⟩], ..st'},
      pure a
    } else
      -- disable tracing inside 'ctx'
      adaptState'
        (λ _, {curPos := none, ..st})
        (λ st', {curPos := st.curPos, ..st'})
        ctx.get
  }
}

unsafe def traceT.run {m α} [monad m] (opts : options) (x : traceT m α) : m (α × traceMap) :=
do (a, st) ← stateT.run x {opts := opts, roots := mkRbmap _ _ _, curPos := none, curTraces := []},
   pure (a, st.roots)

end trace
end lean
