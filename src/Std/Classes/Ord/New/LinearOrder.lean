module

prelude
public import Std.Classes.Ord.New.LinearPreorder
public import Std.Classes.Ord.New.PartialOrder

public section

class LawfulLinearOrder (α : Type u) [Comparable α] extends LawfulLinearPreorder α, LawfulPartialOrder α
