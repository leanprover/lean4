inductive Step (α : Type u) where
  | impossible : α → Step α
  deriving Hashable
