inductive Expr
| Var : nat → Expr
| Val : nat → Expr
| Add : Expr → Expr → Expr

open Expr nat

def mk_expr : nat → nat → Expr
| 0        v := Val v
| (succ n) v := Add (mk_expr n (v+1)) (mk_expr n (v-1))

def eval : Expr → nat
| (Var x) := 0
| (Val v) := v
| (Add l r) := eval l + eval r

def main : io uint32 :=
io.println' (to_string $ eval (mk_expr 26 1)) *>
pure 0
