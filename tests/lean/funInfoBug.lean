import Std.Data.AssocList

def l : List (Prod Nat Nat) := [(1, 1), (2, 2)]
#eval l -- works

def Std.AssocList.ToList : AssocList α β → List (α × β)
  | AssocList.nil => []
  | AssocList.cons k v t => (k, v) :: ToList t

instance [Repr α] [Repr β] : Repr (Std.AssocList α β) where
  reprPrec f _ := repr f.ToList

#reduce (l.toAssocList)
