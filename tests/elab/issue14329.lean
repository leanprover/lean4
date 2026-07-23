import Lean

/-!
Regression test for #14329: the fused two-pass `instantiateMVars` (#12233) lost
sharing when a hypothesis introduced via `MVarId.assert`+`intro` (as done by
`MVarId.note`, `replaceLocalDecl`, `simp at h`, ...) is referenced several times
from deeper binder scopes. The pending value's occurrences of the hypothesis
fvar were each replaced by a fresh `lift_loose_bvars` copy of the (open)
substituted value, so per-step copies compounded multiplicatively and the final
instantiation was exponential in the number of steps (observed as OOM in
LNSym's `sym_n` tactic).

Each step below adds binder depth (`obtain` from an existential) and asserts a
hypothesis whose proof references the previous step's hypothesis three times.
With sharing preserved this elaborates instantly; with the sharing loss it needs
around 3^40 expression nodes and runs out of memory.
-/

open Lean Elab Tactic in
/-- Introduce `h := e` via `MVarId.note` (i.e. `assert` + `intro`), like many
tactics do; unlike the `have` tactic, this makes the proof term a delayed-mvar
application argument that `instantiateMVars` substitutes into the use sites. -/
elab "note_ " x:ident " := " t:term : tactic => withMainContext do
  let e ← elabTerm t none
  let g ← (← getMainGoal).note x.getId e
  replaceMainGoal [g.2]

axiom S : Type
axiom Rel : S → S → Prop
axiom ex : ∀ (s : S), ∃ t, Rel s t
axiom comb : ∀ {a b : S}, Rel a b → Rel a b → Rel a b → Rel a b

theorem test (s0 : S) : True := by
  obtain ⟨t, ht⟩ := ex s0
  note_ h := comb ht ht ht
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  trivial

/-- Variant where the previous step's hypotheses are referenced from several
different binder depths: this defeats plain memoization of the lifted copies,
so the copies compound even with a `(value, lift amount)` memo. -/
theorem test2 (s0 : S) : True := by
  obtain ⟨t, ht⟩ := ex s0
  note_ ha := comb ht ht ht
  note_ hb := comb ht ht ht
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  obtain ⟨t, ht⟩ := ex t
  note_ ha := comb ha hb ha
  obtain ⟨t, ht⟩ := ex t
  note_ hb := comb ha hb hb
  trivial
