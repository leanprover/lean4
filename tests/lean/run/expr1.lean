import Init.Lean.Expr
open Lean

def tst1 : IO Unit :=
do let f   := Expr.const `f [];
   let a   := Expr.const `a [];
   let b   := Expr.const `b [];
   let t   := mkApp f #[a, b, b];
   let as₁ := t.getAppArgs;
   let as₂ := t.getAppRevArgs;
   IO.println as₁;
   IO.println as₂;
   unless (as₁.reverse == as₂) $ throw "failed";
   pure ()

#eval tst1
