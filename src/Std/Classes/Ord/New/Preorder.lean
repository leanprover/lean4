module

prelude
public import Std.Classes.Ord.New.Comparable

public section

class LawfulPreorder (α : Type u) [PartiallyComparable α] extends LawfulPartiallyComparable α where
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  le_refl : ∀ a : α, a ≤ a

instance (α : Type u) [PartiallyComparable α] [LawfulPreorder α] :
    Trans (α := α) (· < ·) (· < ·) (· < ·) where
  trans {a b c} hab hbc := by
    rw [LawfulPartiallyComparable.lt_iff_le_not_ge] at *
    constructor
    · exact LawfulPreorder.le_trans _ _ _ hab.1 hbc.1
    · intro h
      have : c ≤ b := LawfulPreorder.le_trans _ _ _ h hab.1
      exact hbc.2 this
