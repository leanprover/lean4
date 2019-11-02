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

def tst2 : IO Unit :=
do let l1 := Level.max (Level.param `a) (Level.param `b);
   let l2 := Level.max (Level.param `b) (Level.param `a);
   IO.println l1;
   IO.println l2;
   unless (Level.isEquiv l1 l2) $ throw "not equiv";
   pure ()

#eval tst2

def tst3 : IO Unit :=
do let f   := Expr.const `f [];
   let a   := Expr.const `a [];
   let b   := Expr.const `b [];
   let c   := Expr.const `c [];
   let t   := mkApp f #[a, b, c];
   IO.println $ t.getArg! 0;
   IO.println $ t.getArg! 1;
   IO.println $ t.getArg! 2;
   pure ()

#eval tst3
