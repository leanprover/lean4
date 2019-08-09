inductive Expr
| Var : Nat → Expr
| Val : Nat → Expr
| Add : Expr → Expr → Expr

open Expr Nat

def mkExpr : Nat → Nat → Expr
| 0,        v => Val v
| succ n,   v => Add (mkExpr n (v+1)) (mkExpr n (v-1))

def eval : Expr → Nat
| Var x   => 0
| Val v   => v
| Add l r   => eval l + eval r

def main : IO UInt32 :=
IO.println (toString $ eval (mkExpr 26 1)) *>
pure 0
