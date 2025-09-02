set_option warn.sorry false

inductive T : Type u where
  | node : T → T

open Lean.Order

class O α where
  compare : α → α → Ordering

instance : PartialOrder (O α) := sorry

noncomputable instance : CCPO (O α) := sorry

def instOrdT : O T :=
  { compare := fun | .node x, .node y => (@O.compare _ instOrdT x y) }
partial_fixpoint monotonicity by sorry

structure S α where
  compare : α → α → Ordering

instance : PartialOrder (S α) := sorry

noncomputable instance : CCPO (S α) := sorry

def instST : S T :=
  { compare := fun | .node x, .node y => (@S.compare _ instST x y) }
partial_fixpoint monotonicity by sorry
