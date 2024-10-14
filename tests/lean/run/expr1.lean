import Lean.Expr

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
   unless as₁.reverse == as₂ do throw $ IO.userError "failed";
   pure ()

/--
info: #[a, b, b]
#[b, b, a]
-/
#guard_msgs in
#eval tst1

def tst2 : IO Unit :=
do let l1 := mkLevelMax (mkLevelParam `a) (mkLevelParam `b);
   let l2 := mkLevelMax (mkLevelParam `b) (mkLevelParam `a);
   IO.println l1;
   IO.println l2;
   unless Level.isEquiv l1 l2 do throw $ IO.userError "not equiv";
   pure ()

/--
info: max a b
max b a
-/
#guard_msgs in
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

/--
info: a
b
c
-/
#guard_msgs in
#eval tst3


def tst4 : IO Unit :=
do let f   := mkConst `f [];
   let a   := mkConst `a [];
   let b   := mkConst `b [];
   let x0   := mkBVar 0;
   let x1   := mkBVar 1;
   let t1   := mkAppN f #[a, b];
   let t2   := mkAppN f #[a, x0];
   let t3   := mkLambda `x BinderInfo.default (mkSort levelZero) (mkAppN f #[a, x0]);
   let t4   := mkLambda `x BinderInfo.default (mkSort levelZero) (mkAppN f #[a, x1]);
   unless (!t1.hasLooseBVar 0) do throw $ IO.userError "failed-1";
   unless (t2.hasLooseBVar 0) do throw $ IO.userError "failed-2";
   unless (!t3.hasLooseBVar 0) do throw $ IO.userError "failed-3";
   unless (t4.hasLooseBVar 0) do throw $ IO.userError "failed-4";
   unless (!t4.hasLooseBVar 1) do throw $ IO.userError "failed-5";
   unless (!t2.hasLooseBVar 1) do throw $ IO.userError "failed-6";
   pure ()

#guard_msgs in
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
   unless (t.etaExpanded? == some f) do throw $ IO.userError "failed-1";
   let t   := mkLambda `x BinderInfo.default nat (mkApp f x1);
   unless (t.etaExpanded? == none) do throw $ IO.userError "failed-2";
   let t   := mkLambda `x BinderInfo.default nat (mkAppN f #[a, x0]);
   unless (t.etaExpanded? == some (mkApp f a)) do throw $ IO.userError "failed-3";
   let t   := mkLambda `x BinderInfo.default nat (mkAppN f #[x0, x0]);
   unless (t.etaExpanded? == none) do throw $ IO.userError "failed-4";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkApp f x0));
   unless (t.etaExpanded? == none) do throw $ IO.userError "failed-5";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkAppN f #[x1, x0]));
   IO.println t;
   unless (t.etaExpanded? == some f) do throw $ IO.userError "failed-6";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkLambda `z BinderInfo.default nat (mkAppN f #[x2, x1, x0])));
   IO.println t;
   unless (t.etaExpanded? == some f) do throw $ IO.userError "failed-7";
   let t   := mkLambda `x BinderInfo.default nat (mkLambda `y BinderInfo.default nat (mkLambda `z BinderInfo.default nat (mkAppN f #[a, x2, x1, x0])));
   IO.println t;
   unless (t.etaExpanded? == some (mkApp f a)) do throw $ IO.userError "failed-8";
   IO.println t.etaExpanded?;
   let t   := mkApp f a;
   unless (t.etaExpanded? == some (mkApp f a)) do throw $ IO.userError "failed-9";
   pure ()

/--
info: (some f)
fun (x : Nat) (y : Nat) => f x y
fun (x : Nat) (y : Nat) (z : Nat) => f x y z
fun (x : Nat) (y : Nat) (z : Nat) => f a x y z
(some (f a))
-/
#guard_msgs in
#eval tst5

def tst6 : IO Unit := do
let x1 := mkBVar 0;
let x2 := mkBVar 1;
let t1 := mkApp2 (mkConst `f) x1 x2;
let t2 := mkForall `x BinderInfo.default (mkConst `Nat) t1;
IO.println (t1.liftLooseBVars 0 1);
IO.println (t2.liftLooseBVars 0 1);
let t3 := (t2.liftLooseBVars 0 1).lowerLooseBVars 1 1;
IO.println $ t3;
unless (t2 == t3) do throw $ IO.userError "failed-1";
pure ()

/--
info: f #1 #2
forall (x : Nat), f x #1
forall (x : Nat), f x #0
-/
#guard_msgs in
#eval tst6

instance : Coe Name FVarId where
  coe n := { name := n }

def tst7 : IO Unit := do
let x := mkFVar `x;
let y := mkFVar `y;
let f := mkConst `f;
let t := mkAppN f #[x, y, mkNatLit 2];
let t := t.abstract #[x, y];
let t := t.instantiateRev #[mkNatLit 0, mkNatLit 1];
IO.println t

/--
info: f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-/
#guard_msgs in
#eval tst7
