module

prelude
public import Std.Classes.Ord.New.LinearPreorder

public section

class LawfulPartialOrder (α : Type u) [PartiallyComparable α] extends LawfulPreorder α,
    Std.Antisymm (α := α) (· ≤ ·) where
