/-!
 Test for a regression introduced by #11589
-/

section Mathlib.Order.Defs.LinearOrder

class LinearOrder (α : Type) extends Max α where

end Mathlib.Order.Defs.LinearOrder
section Mathlib.Data.Int.Order.Basic

instance instLinearOrder : LinearOrder Int where

end Mathlib.Data.Int.Order.Basic
section Mathlib.Order.Lattice

variable {α : Type}

class SemilatticeSup (α : Type) where
  sup : α → α → α

instance SemilatticeSup.toMax [SemilatticeSup α] : Max α where max a b := SemilatticeSup.sup a b

instance LinearOrder.toSemilatticeSup {α : Type} [LinearOrder α] : SemilatticeSup α where
  sup := max

end Mathlib.Order.Lattice

section Mathlib.Algebra.Order.Group.Unbundled.Abs

variable {α : Type} [SemilatticeSup α] [Neg α] {a b : α}

@[grind]
def abs (a : α) : α := max a (-a)

end Mathlib.Algebra.Order.Group.Unbundled.Abs

@[grind =] theorem max_def [Max α] [LE α] [DecidableLE α] (a b : α)
    : max a b = if a ≤ b then b else a :=
  sorry

theorem abs_lt_one_iff {a : Int} : abs a < 1 ↔ a = 0 := by
  grind
