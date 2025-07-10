module

prelude
public import Std.Classes.Ord.New.Preorder

public section

class LawfulLinearPreorder (α : Type u) [Comparable α] extends LawfulPreorder α, LawfulComparable α
