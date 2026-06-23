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
