import Lean

/-!
Regression test for the same-binder-depth part of #14329: the fused
`instantiateMVars` (#12233) substitutes fvars by values that may contain loose
bvars of enclosing binders, and every occurrence at a deeper binder depth
received a fresh `lift_loose_bvars` copy of the value. Hypotheses introduced
via `MVarId.assert`+`intro` (as done by `MVarId.note`, `replaceLocalDecl`,
`simp at h`, ...) and referenced several times produce exactly this shape, and
the copies compound multiplicatively along the chain of delayed assignments.

Each step below adds binder depth (`obtain` from an existential) and asserts a
hypothesis whose proof references the previous step's hypothesis three times —
all at the same binder depth, so memoizing the lifted copies makes all three
occurrences share one copy. With the memo this elaborates instantly; without
it, it needs around 3^40 expression nodes and runs out of memory.

The variant where the references sit at several different binder depths (which
memoization alone does not cover) is `issue14329b.lean`.
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
  obtain ⟨t, ht⟩ := ex t
  note_ h := comb h h h
  trivial
