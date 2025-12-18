/--Ensure that `deriving Ord` works on indexed inductive types.-/
inductive Ty where
  | int
  | bool
inductive Expr : Ty → Type where
  | a : Expr .int
  | b : Expr .bool
deriving Ord

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
deriving Ord
