import init.lean.expr
open Lean

def main (xs : List String) : IO Unit :=
do
let f := mkConst `f;
let x := Expr.fvar `x;
let y := Expr.fvar `y;
let t := Expr.app (Expr.app (Expr.app f x) y) (Expr.app f x);
IO.println t.dbgToString;
let p := t.abstract [x, y].toArray;
IO.println p.dbgToString;
IO.println (p.instantiateRev [x, y].toArray).dbgToString;
let a := mkConst `a;
let b := Expr.app f (mkConst `b);
IO.println (p.instantiateRev [a, b].toArray).dbgToString;
IO.println (p.instantiate [a].toArray).dbgToString;
let p := t.abstractRange 1 [x, y].toArray;
IO.println p.dbgToString;
let p := t.abstractRange 3 [x, y].toArray;
IO.println p.dbgToString;
pure ()
