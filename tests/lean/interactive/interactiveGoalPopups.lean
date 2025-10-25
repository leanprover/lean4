/-- MyNat doc -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-- MyTrue doc -/
structure MyTrue : Prop where

/-- MyEq doc -/
inductive MyEq : α → α → Prop where
  | refl (a : α) : MyEq a a

theorem foo : (x : MyNat) → (h : MyEq x x) → MyTrue := by
  intro x h
  exact MyTrue.mk
--^ goals:withPopups
