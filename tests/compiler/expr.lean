import Init.Lean.Expr
open Lean

def main : IO UInt32 :=
do
let e := mkAppN (mkConst `f) #[mkConst `a, mkConst `b];
IO.println e;
IO.println ("hash: " ++ toString e.hash);
IO.println e.getAppArgs;
pure 0
