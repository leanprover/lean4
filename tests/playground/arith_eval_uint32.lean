inductive Expr
| Var : UInt32 → Expr
| Val : UInt32 → Expr
| Add : Expr → Expr → Expr

open Expr

def dec (n : UInt32) : UInt32 :=
if n = 0 then 0 else n-1

def mkExpr : UInt32 → UInt32 → Expr | n, v =>
if n = 0 then Val v
else Add (mkExpr (n-1) (v+1)) (mkExpr (n-1) (dec v))

def eval : Expr → UInt32
| Var x   => 0
| Val v   => v
| Add l r   => eval l + eval r

def main : IO UInt32 :=
IO.println (toString $ eval (mkExpr 26 1)) *>
pure 0
