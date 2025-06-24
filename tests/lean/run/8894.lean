open Lean.Order

set_option trace.Elab.Tactic.monotonicity true

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
  csup := sorry
  csup_spec := sorry

instance : Lean.Order.CCPO B where
  csup := sorry
  csup_spec := sorry

-- instance : Lean.Order.CCPO Lean.Order.ReverseImplicationOrder where
--   csup := ReverseImplicationOrder.instCompleteLattice.sup
--   csup_spec _ := ReverseImplicationOrder.instCompleteLattice.sup_spec
-- instance : Lean.Order.CCPO Lean.Order.ImplicationOrder where
--   csup := ImplicationOrder.instCompleteLattice.sup
--   csup_spec _ := ImplicationOrder.instCompleteLattice.sup_spec


mutual
  def tick (n : Nat): A :=
    tock (n + 1)
  partial_fixpoint

  def tock (n : Nat) : A :=
    tick (n + 1)
  partial_fixpoint
end
