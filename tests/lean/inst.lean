import Init.Lean.Expr
open Lean

def tst : IO Unit :=
do
let f := mkConst `f;
let x := Expr.bvar 0;
let y := Expr.bvar 1;
let t := Expr.app (Expr.app (Expr.app f x) y) x;
let a := mkConst `a;
let b := Expr.app f (mkConst `b);
let c := mkConst `c;
IO.println t;
IO.println (t.instantiate #[a, b]);
IO.println (t.instantiateRange 0 2 #[a, b]);
IO.println (t.instantiateRange 2 4 #[c, c, a, b, c]);
IO.println (t.instantiateRev #[a, b]);
IO.println (t.instantiate #[a]);
IO.println (t.instantiate1 a);
pure ()

#eval tst
