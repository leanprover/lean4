/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.lean.format init.meta.expr init.data.rbmap

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

--TODO: move this (and `pos` itself) into separate module
def pos.lt : pos → pos → Prop
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := (l₁, c₁) < (l₂, c₂)

instance pos.has_lt : has_lt pos := ⟨pos.lt⟩

instance pos.decidable_lt : Π (p₁ p₂ : pos), decidable (p₁ < p₂)
| ⟨l₁, c₁⟩ ⟨l₂, c₂⟩ := infer_instance_as $ decidable ((l₁, c₁) < (l₂, c₂))

def trace_map := rbmap pos trace (<)

structure trace_state :=
(roots : trace_map)
(cur_pos : pos)
(cur_traces : list trace)

def trace_t (m : Type → Type u) := state_t trace_state m
local attribute [reducible] trace_t

class monad_tracer (m : Type → Type u) :=
(trace_root {α} : pos → message → thunk (m α) → m α)
(trace_ctx {α} : message → thunk (m α) → m α)

export monad_tracer (trace_root trace_ctx)

def trace {m} [monad m] [monad_tracer m] (msg : message) : m unit :=
trace_ctx msg (pure ())

instance (m) [monad m] : monad_tracer (trace_t m) :=
{ trace_root := λ α pos msg ctx, do {
    modify $ λ st, {cur_pos := pos, cur_traces := [], ..st},
    a ← ctx (),
    modify $ λ (st : trace_state), {roots := st.roots.insert pos ⟨msg, st.cur_traces⟩, ..st},
    pure a
  },
  trace_ctx := λ α msg ctx, do {
    st ← get,
    put {cur_traces := [], ..st},
    a ← ctx (),
    modify $ λ (st' : trace_state), {cur_traces := st.cur_traces ++ [⟨msg, st'.cur_traces⟩], ..st'},
    pure a
  }
}

def trace_t.run {m α} [monad m] (x : trace_t m α) : m (α × trace_map) :=
do (a, st) ← state_t.run x {roots := mk_rbmap _ _ _, cur_pos := ⟨0, 0⟩, cur_traces := []},
   pure (a, st.roots)

def test : id trace_map :=
prod.snd <$> trace_t.run (
trace_root ⟨1, 0⟩ "type_context.is_def_eq trace" (
  trace_ctx "f 0 =?= f a (approximate mode)" (
    -- is_def_eq_detail
    trace_ctx "f 0 =?= f a" (
      trace "0 =?= a" >>
      trace "...failed"
    ) >>
    trace "...failed"
  )
))

--run_cmd tactic.trace $ format.join $ list.intersperse format.line $ test.to_list.map $ λ ⟨pos, tr⟩, to_fmt pos ++ ": " ++ tr.pp

end trace
end lean
