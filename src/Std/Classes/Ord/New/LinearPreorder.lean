module

prelude
public import Std.Classes.Ord.Basic
public import Std.Classes.Ord.New.Preorder

public section

class LawfulLinearPreorder (α : Type u) [Comparable α] extends LawfulPreorder α,
    LawfulOrientedComparable α

instance (α : Type u) [Ord α] [Comparable α] [LawfulOrd α] [LawfulLinearPreorder α] :
    Std.TransOrd α where
  isLE_trans := by
    simp [Comparable.compare_isLE]
    apply LawfulPreorder.le_trans
