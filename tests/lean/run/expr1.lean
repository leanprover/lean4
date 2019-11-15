import Init.Lean.Expr
open Lean

def tst1 : IO Unit :=
do let f   := mkConst `f [];
   let a   := mkConst `a [];
   let b   := mkConst `b [];
   let t   := mkAppN f #[a, b, b];
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
do let f   := mkConst `f [];
   let a   := mkConst `a [];
   let b   := mkConst `b [];
   let c   := mkConst `c [];
   let t   := mkAppN f #[a, b, c];
   IO.println $ t.getArg! 0;
   IO.println $ t.getArg! 1;
   IO.println $ t.getArg! 2;
   pure ()

#eval tst3


def tst4 : IO Unit :=
do let f   := mkConst `f [];
   let a   := mkConst `a [];
   let b   := mkConst `b [];
   let x0   := mkBVar 0;
   let x1   := mkBVar 1;
   let t1   := mkAppN f #[a, b];
   let t2   := mkAppN f #[a, x0];
   let t3   := mkLambda `x BinderInfo.default (mkSort Level.zero) (mkAppN f #[a, x0]);
   let t4   := mkLambda `x BinderInfo.default (mkSort Level.zero) (mkAppN f #[a, x1]);
   unless (!t1.hasLooseBVar 0) $ throw "failed-1";
   unless (t2.hasLooseBVar 0) $ throw "failed-2";
   unless (!t3.hasLooseBVar 0) $ throw "failed-3";
   unless (t4.hasLooseBVar 0) $ throw "failed-4";
   unless (!t4.hasLooseBVar 1) $ throw "failed-5";
   unless (!t2.hasLooseBVar 1) $ throw "failed-6";
   pure ()

#eval tst4

def tst5 : IO Unit :=
do let f   := mkConst `f [];
   let a   := mkConst `a [];
   let nat := mkConst `Nat [];
   let x0  := mkBVar 0;
   let x1  := mkBVar 1;
   let x2  := mkBVar 2;
   let t   := mkLambda `x BinderInfo.default nat (mkApp f x0);
   IO.println t.etaExpanded?;
   unless (t.etaExpanded? == some f) $ throw "failed-1";
   let t   := mkLambda `x BinderInfo.default nat (mkApp f x1);
   unless (t.etaExpanded? == none) $ throw "failed-2";
   let t   := mkLambda `x BinderInfo.default nat (mkAppN f #[a, x0]);
   unless (t.etaExpanded? == some (mkApp f a)) $ throw "failed-3";
   let t   := mkLambda `x BinderInfo.default nat (mkAppN f #[x0, x0]);
   unless (t.etaExpanded? == none) $ throw "failed-4";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkApp f x0));
   unless (t.etaExpanded? == none) $ throw "failed-5";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkAppN f #[x1, x0]));
   IO.println t;
   unless (t.etaExpanded? == some f) $ throw "failed-6";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkLambda `z BinderInfo.default nat (mkAppN f #[x2, x1, x0])));
   IO.println t;
   unless (t.etaExpanded? == some f) $ throw "failed-7";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkLambda `z BinderInfo.default nat (mkAppN f #[a, x2, x1, x0])));
   IO.println t;
   unless (t.etaExpanded? == some (mkApp f a)) $ throw "failed-8";
   IO.println t.etaExpanded?;
   let t   := mkApp f a;
   unless (t.etaExpanded? == some (mkApp f a)) $ throw "failed-9";
   pure ()

#eval tst5
