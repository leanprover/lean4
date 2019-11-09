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


def tst4 : IO Unit :=
do let f   := Expr.const `f [];
   let a   := Expr.const `a [];
   let b   := Expr.const `b [];
   let x0   := Expr.bvar 0;
   let x1   := Expr.bvar 1;
   let t1   := mkApp f #[a, b];
   let t2   := mkApp f #[a, x0];
   let t3   := Expr.lam `x BinderInfo.default (Expr.sort Level.zero) (mkApp f #[a, x0]);
   let t4   := Expr.lam `x BinderInfo.default (Expr.sort Level.zero) (mkApp f #[a, x1]);
   unless (!t1.hasLooseBVar 0) $ throw "failed-1";
   unless (t2.hasLooseBVar 0) $ throw "failed-2";
   unless (!t3.hasLooseBVar 0) $ throw "failed-3";
   unless (t4.hasLooseBVar 0) $ throw "failed-4";
   unless (!t4.hasLooseBVar 1) $ throw "failed-4";
   unless (!t2.hasLooseBVar 1) $ throw "failed-5";
   pure ()

#eval tst4
