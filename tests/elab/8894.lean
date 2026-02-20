set_option warn.sorry false

open Lean.Order

def A : Type := Prop
def B : Type := Prop

instance : Lean.Order.PartialOrder A where
  rel := sorry
  rel_refl := sorry
  rel_trans := sorry
  rel_antisymm := sorry

instance : Lean.Order.PartialOrder B where
  rel := sorry
  rel_refl := sorry
  rel_trans := sorry
  rel_antisymm := sorry

instance : Lean.Order.CCPO A where
  has_csup := sorry

instance : Lean.Order.CCPO B where
  has_csup := sorry

/--
error: Could not prove 'tick' to be monotone in its recursive calls:
  Cannot eliminate recursive call in
    tock (n + 1)
-/
#guard_msgs in
mutual
  def tick (n : Nat): A :=
    tock (n + 1)
  partial_fixpoint

  def tock (n : Nat) : B :=
    tick (n + 1)
  partial_fixpoint
end

mutual
  def tick2 (n : Nat): A :=
    tock2 (n + 1)
  partial_fixpoint

  def tock2 (n : Nat) : A :=
    tick2 (n + 1)
  partial_fixpoint
end
