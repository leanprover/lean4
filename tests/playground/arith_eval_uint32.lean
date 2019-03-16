inductive Expr
| Var : uint32 → Expr
| Val : uint32 → Expr
| Add : Expr → Expr → Expr

open Expr

def dec (n : uint32) : uint32 :=
if n = 0 then 0 else n-1

def mk_expr : uint32 → uint32 → Expr | n v :=
if n = 0 then Val v
else Add (mk_expr (n-1) (v+1)) (mk_expr (n-1) (dec v))

def eval : Expr → uint32
| (Var x) := 0
| (Val v) := v
| (Add l r) := eval l + eval r

def main : io uint32 :=
io.println (to_string $ eval (mk_expr 26 1)) *>
pure 0
