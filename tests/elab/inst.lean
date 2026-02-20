import Lean.Expr

open Lean

def tst : IO Unit :=
do
let f := mkConst `f;
let x := mkBVar 0;
let y := mkBVar 1;
let t := mkApp (mkApp (mkApp f x) y) x;
let a := mkConst `a;
let b := mkApp f (mkConst `b);
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
