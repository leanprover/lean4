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
   unless (!t4.hasLooseBVar 1) $ throw "failed-5";
   unless (!t2.hasLooseBVar 1) $ throw "failed-6";
   pure ()

#eval tst4

def tst5 : IO Unit :=
do let f   := Expr.const `f [];
   let a   := Expr.const `a [];
   let nat := Expr.const `Nat [];
   let x0  := Expr.bvar 0;
   let x1  := Expr.bvar 1;
   let x2  := Expr.bvar 2;
   let t   := Expr.lam `x BinderInfo.default nat (Expr.app f x0);
   IO.println t.etaExpanded?;
   unless (t.etaExpanded? == some f) $ throw "failed-1";
   let t   := Expr.lam `x BinderInfo.default nat (Expr.app f x1);
   unless (t.etaExpanded? == none) $ throw "failed-2";
   let t   := Expr.lam `x BinderInfo.default nat (mkApp f #[a, x0]);
   unless (t.etaExpanded? == some (Expr.app f a)) $ throw "failed-3";
   let t   := Expr.lam `x BinderInfo.default nat (mkApp f #[x0, x0]);
   unless (t.etaExpanded? == none) $ throw "failed-4";
   let t   := Expr.lam `x BinderInfo.default nat (Expr.lam `y BinderInfo.default nat (Expr.app f x0));
   unless (t.etaExpanded? == none) $ throw "failed-5";
   let t   := Expr.lam `x BinderInfo.default nat (Expr.lam `y BinderInfo.default nat (mkApp f #[x1, x0]));
   IO.println t;
   unless (t.etaExpanded? == some f) $ throw "failed-6";
   let t   := Expr.lam `x BinderInfo.default nat (Expr.lam `y BinderInfo.default nat (Expr.lam `z BinderInfo.default nat (mkApp f #[x2, x1, x0])));
   IO.println t;
   unless (t.etaExpanded? == some f) $ throw "failed-7";
   let t   := Expr.lam `x BinderInfo.default nat (Expr.lam `y BinderInfo.default nat (Expr.lam `z BinderInfo.default nat (mkApp f #[a, x2, x1, x0])));
   IO.println t;
   unless (t.etaExpanded? == some (Expr.app f a)) $ throw "failed-8";
   IO.println t.etaExpanded?;
   pure ()

#eval tst5
