module

prelude
public import Std.Classes.Ord.New.Comparable

public section

class LawfulPreorder (α : Type u) [PartiallyComparable α] where
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  le_refl : ∀ a : α, a ≤ a
