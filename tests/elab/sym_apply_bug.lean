/-!
Tests for `Lean.Meta.Sym.BackwardRule.apply`: a backward rule with an instance argument that
cannot be synthesized must report the rule as inapplicable rather than leaving a loose instance
metavariable in the proof term (which surfaces as a kernel unresolved-metavariable error).
-/

inductive PlainRel {α : Sort u} (lhs rhs : α) : Prop where
  | intro

theorem plainFoo {σ : Sort u}  (pre rhs : σ → Prop) : PlainRel pre rhs :=
  PlainRel.intro

theorem plainFoo' {σ : Type u}  (pre rhs : σ → Prop) : PlainRel pre rhs :=
  PlainRel.intro

example (pre rhs : Nat → Prop) : PlainRel pre rhs := by
  sym => apply plainFoo

example (pre rhs : Nat → Prop) : PlainRel pre rhs := by
  sym => apply plainFoo'

theorem plainFoo'' {σ : Type u} {σ' : Type u} (pre rhs : σ → σ') : PlainRel pre rhs :=
  PlainRel.intro

theorem plainFoo''' {σ : Type u} {σ' : Type v} (pre rhs : σ → σ') : PlainRel pre rhs :=
  PlainRel.intro

set_option trace.Meta.debug true in
example (pre rhs : Nat → Prop) : PlainRel pre rhs := by
  sym => apply plainFoo'''

example (pre rhs : Nat → Prop) : PlainRel pre rhs := by
  sym => apply plainFoo''

-- An unsynthesizable instance argument makes `apply` fail rather than leaving a
-- loose instance metavariable in the proof.
/-- error: `apply` failed, rule is not applicable -/
#guard_msgs in
example : False := by sym => apply Inhabited.default
