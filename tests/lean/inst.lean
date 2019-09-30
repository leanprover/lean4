import init.lean.expr
open Lean

def tst : IO Unit :=
do
let f := mkConst `f;
let x := Expr.bvar 0;
let y := Expr.bvar 1;
let t := Expr.app (Expr.app (Expr.app f x) y) x;
let a := mkConst `a;
let b := Expr.app f (mkConst `b);
IO.println t.dbgToString;
IO.println (t.instantiate [a, b].toArray).dbgToString;
IO.println (t.instantiateRev [a, b].toArray).dbgToString;
IO.println (t.instantiate [a].toArray).dbgToString;
IO.println (t.instantiate1 a).dbgToString;
pure ()

#eval tst
