inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α Nat.zero
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

inductive Expr
  | val (v : Nat)
  | app2 (f : String) (args : Vec Expr 2)
  | app3 (f : String) (args : Vec Expr 3)
