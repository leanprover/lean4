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
| from_format (fmt : format)

instance : has_coe format message :=
⟨message.from_format⟩

inductive trace
| mk (msg : message) (subtraces : list trace)

def trace.pp : trace → format
| (trace.mk (message.from_format fmt) subtraces) :=
fmt ++ format.nest 2 (format.join $ subtraces.map (λ t, format.line ++ t.pp))

namespace trace

def trace_map := rbmap position trace (<)

structure trace_state :=
(opts : options)
(roots : trace_map)
(cur_pos : option position)
(cur_traces : list trace)

def trace_t (m : Type → Type u) := state_t trace_state m
local attribute [reducible] trace_t

instance (m) [monad m] : monad (trace_t m) := infer_instance

class monad_tracer (m : Type → Type u) :=
(trace_root {α} : position → name → message → thunk (m α) → m α)
(trace_ctx {α} : name → message → thunk (m α) → m α)

export monad_tracer (trace_root trace_ctx)

def trace {m} [monad m] [monad_tracer m] (cls : name) (msg : message) : m unit :=
trace_ctx cls msg (pure () : m unit)

instance (m) [monad m] : monad_tracer (trace_t m) :=
{ trace_root := λ α pos cls msg ctx, do {
    st ← get,
    if st.opts.get_bool cls = some tt then do {
      modify $ λ st, {cur_pos := pos, cur_traces := [], ..st},
      a ← ctx.get,
      modify $ λ (st : trace_state), {roots := st.roots.insert pos ⟨msg, st.cur_traces⟩, ..st},
      pure a
    } else ctx.get
  },
  trace_ctx := λ α cls msg ctx, do {
    st ← get,
    -- tracing enabled?
    some _ ← pure st.cur_pos | ctx.get,
    -- trace class enabled?
    if st.opts.get_bool cls = some tt then do {
      put {cur_traces := [], ..st},
      a ← ctx.get,
      modify $ λ (st' : trace_state), {cur_traces := st.cur_traces ++ [⟨msg, st'.cur_traces⟩], ..st'},
      pure a
    } else
      -- disable tracing inside 'ctx'
      adapt_state'
        (λ _, {cur_pos := none, ..st})
        (λ st', {cur_pos := st.cur_pos, ..st'})
        ctx.get
  }
}

meta def trace_t.run {m α} [monad m] (opts : options) (x : trace_t m α) : m (α × trace_map) :=
do (a, st) ← state_t.run x {opts := opts, roots := mk_rbmap _ _ _, cur_pos := none, cur_traces := []},
   pure (a, st.roots)

end trace
end lean
