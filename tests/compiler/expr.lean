import Init.Lean.Expr
open Lean

def main : IO UInt32 :=
do
let e := Expr.app (Expr.app (Expr.const `f []) (Expr.const `a [])) (Expr.const `b []);
IO.println e;
IO.println ("hash: " ++ toString e.hash);
IO.println e.getAppArgs;
pure 0
