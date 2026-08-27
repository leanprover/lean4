inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)

inductive Expr where
  | app2 (f : String) (args : Vec Expr 2)
  | app3 (f : String) (args : Vec Expr 3)

#print Expr.app2.sizeOf_spec
#print Expr.app3.sizeOf_spec
