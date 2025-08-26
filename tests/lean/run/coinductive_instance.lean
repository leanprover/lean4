import Init.Internal.Order
open Lean.Order

def DefFunctor (r : α → α → Prop) (infSeq : α → Prop) : α → Prop :=
   λ x : α => ∃ y, r x y ∧ infSeq y

def def1 (r : α → α → Prop) : α → Prop := DefFunctor r (def1 r)
  coinductive_fixpoint monotonicity sorry

def def2 (r : α → α → Prop) : α → Prop := fun x => DefFunctor r (def2 r) x
  coinductive_fixpoint monotonicity sorry
