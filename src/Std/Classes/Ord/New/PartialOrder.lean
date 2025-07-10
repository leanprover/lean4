module

prelude
public import Std.Classes.Ord.New.LinearPreorder

public section

class LawfulPartialOrder (α : Type u) [PartiallyComparable α] extends LawfulPreorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
