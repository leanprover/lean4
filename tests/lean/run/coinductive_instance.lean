import Init.Internal.Order
open Lean.Order

set_option trace.Elab.definition.partialFixpoint true


inductive InductiveFunctor (r : α → α → Prop) (infSeq : α → Prop) : α → Prop where
  | step {b} : r a b → infSeq b → InductiveFunctor r infSeq a

def DefFunctor (r : α → α → Prop) (infSeq : α → Prop) : α → Prop :=
   λ x : α => ∃ y, r x y ∧ infSeq y

#check InductiveFunctor
#check DefFunctor

def def1 (r : α → α → Prop) : α → Prop := DefFunctor r (def1 r)
  coinductive_fixpoint monotonicity sorry

#check def1.coinduct

def def2 (r : α → α → Prop) : α → Prop := fun x => DefFunctor r (def2 r) x
  coinductive_fixpoint monotonicity sorry

#check def2.coinduct
