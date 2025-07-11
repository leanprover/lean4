module

prelude
public import Std.Classes.Ord.New.LinearPreorder
public import Std.Classes.Ord.New.PartialOrder

public section

class LawfulLinearOrder (α : Type u) [Comparable α] extends LawfulLinearPreorder α, LawfulPartialOrder α

instance (α : Type u) [Ord α] [Comparable α] [LawfulOrd α] [LawfulLinearOrder α] :
    Std.LawfulEqOrd α where
  eq_of_compare h := by
    apply LawfulPartialOrder.toAntisymm.antisymm
    · simp [← Comparable.compare_isLE, h]
    · rw [Std.OrientedOrd.eq_swap, Ordering.swap_eq_eq] at h
      simp [← Comparable.compare_isLE, h]

instance (α : Type u) [Comparable α] [LawfulLinearPreorder α] [Std.Antisymm (α := α) (· ≤ ·)] :
    LawfulLinearOrder α where

instance (α : Type u) [Ord α] [Comparable α] [LawfulOrd α] [LawfulLinearPreorder α]
    [Std.LawfulEqOrd α] : Std.Antisymm (α := α) (· ≤ ·) where
  antisymm a b := by
    cases h : compare a b
    all_goals simp [← Comparable.compare_isLE, ← Std.LawfulEqOrd.compare_eq_iff_eq (α := α),
      Std.OrientedOrd.eq_swap (a := b), h]
