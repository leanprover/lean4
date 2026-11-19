import Lean.Expr

open Lean

def tst : IO Unit :=
do
let f := mkConst `f;
let x := mkFVar { name := `x };
let y := mkFVar { name := `y };
let t := mkApp (mkApp (mkApp f x) y) (mkApp f x);
IO.println t;
let p := t.abstract [x, y].toArray;
IO.println p;
IO.println $ p.instantiateRev #[x, y];
let a := mkConst `a;
let b := mkApp f (mkConst `b);
IO.println $ p.instantiateRev #[a, b];
IO.println $ p.instantiate #[a];
let p := t.abstractRange 1 #[x, y];
IO.println p;
let p := t.abstractRange 3 #[x, y];
IO.println p;
pure ()

#eval tst
