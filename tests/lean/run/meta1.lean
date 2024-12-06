import Lean.Meta

open Lean
open Lean.Meta

def tstInferType (e : Expr) : CoreM Unit := do
  let env ← getEnv
  let (type, _, _) ← (inferType e : MetaM _).toIO { fileName := "", fileMap := default } { env := env } {} {};
  IO.println (toString e ++ " : " ++ toString type)

def tstWHNF (e : Expr) : CoreM Unit := do
  let env ← getEnv
  let (s, _, _) ← (whnf e : MetaM _).toIO { fileName := "", fileMap := default } { env := env };
  IO.println (toString e ++ " ==> " ++ toString s)

unsafe def tstIsProp (e : Expr) : CoreM Unit := do
  let env ← getEnv
  let (b, _, _) ← (isProp e : MetaM _).toIO { fileName := "", fileMap := default } { env := env };
  IO.println (toString e ++ ", isProp: " ++ toString b)

def t1 : Expr :=
let map  := mkConst `List.map [levelOne, levelOne];
let nat  := mkConst `Nat [];
let bool := mkConst `Bool [];
mkAppN map #[nat, bool]

/-- info: List.map.{1, 1} Nat Bool : (Nat -> Bool) -> (List.{1} Nat) -> (List.{1} Bool) -/
#guard_msgs in
#eval tstInferType t1

def t2 : Expr :=
let prop := mkSort levelZero;
mkForall `x BinderInfo.default prop prop

/-- info: Prop -> Prop : Type -/
#guard_msgs in
#eval tstInferType t2

def t3 : Expr :=
let nat   := mkConst `Nat [];
let natLe := mkConst `Nat.le [];
let zero  := mkLit (Literal.natVal 0);
let p     := mkAppN natLe #[mkBVar 0, zero];
mkForall `x BinderInfo.default nat p

/-- info: forall (x : Nat), Nat.le x 0 : Prop -/
#guard_msgs in
#eval tstInferType t3

def t4 : Expr :=
let nat   := mkConst `Nat [];
let p     := mkAppN (mkConst `Nat.succ []) #[mkBVar 0];
mkLambda `x BinderInfo.default nat p

/-- info: fun (x : Nat) => Nat.succ x : Nat -> Nat -/
#guard_msgs in
#eval tstInferType t4

def t5 : Expr :=
let add   := mkConst `Nat.add [];
mkAppN add #[mkLit (Literal.natVal 3), mkLit (Literal.natVal 5)]

/-- info: Nat.add 3 5 ==> 8 -/
#guard_msgs in
#eval tstWHNF t5

set_option pp.all true
/-- info: @List.cons.{0} Nat : Nat → List.{0} Nat → List.{0} Nat -/
#guard_msgs in
#check @List.cons Nat

def t6 : Expr :=
let map  := mkConst `List.map [levelOne, levelOne];
let nat  := mkConst `Nat [];
let add  := mkConst `Nat.add [];
let f    := mkLambda `x BinderInfo.default nat (mkAppN add #[mkBVar 0, mkLit (Literal.natVal 1)]);
let cons := mkApp (mkConst `List.cons [levelZero]) nat;
let nil  := mkApp (mkConst `List.nil [levelZero]) nat;
let one  := mkLit (Literal.natVal 1);
let four := mkLit (Literal.natVal 4);
let xs   := mkApp (mkApp cons one) (mkApp (mkApp cons four) nil);
mkAppN map #[nat, nat, f, xs]

/--
info: List.map.{1, 1} Nat Nat (fun (x : Nat) => Nat.add x 1) (List.cons.{0} Nat 1 (List.cons.{0} Nat 4 (List.nil.{0} Nat))) : List.{1} Nat
-/
#guard_msgs in
#eval tstInferType t6

/--
info: List.map.{1, 1} Nat Nat (fun (x : Nat) => Nat.add x 1) (List.cons.{0} Nat 1 (List.cons.{0} Nat 4 (List.nil.{0} Nat))) ==> List.cons.{1} Nat ((fun (x : Nat) => Nat.add x 1) 1) (List.map.{1, 1} Nat Nat (fun (x : Nat) => Nat.add x 1) (List.cons.{0} Nat 4 (List.nil.{0} Nat)))
-/
#guard_msgs in
#eval tstWHNF t6

/-- info: Prop : Type -/
#guard_msgs in
#eval tstInferType $ mkSort levelZero

/--
info: fun {a : Type} (x : a) (xs : List.{0} a) => xs : forall {a : Type}, a -> (List.{0} a) -> (List.{0} a)
-/
#guard_msgs in
#eval tstInferType $ mkLambda `a BinderInfo.implicit (mkSort levelOne) (mkLambda `x BinderInfo.default (mkBVar 0) (mkLambda `xs BinderInfo.default (mkApp (mkConst `List [levelZero]) (mkBVar 1)) (mkBVar 0)))

def t7 : Expr :=
let nat  := mkConst `Nat [];
let one  := mkLit (Literal.natVal 1);
mkLet `x nat one one

/-- info: let x : Nat := 1; 1 : Nat -/
#guard_msgs in
#eval tstInferType $ t7

/-- info: let x : Nat := 1; 1 ==> 1 -/
#guard_msgs in
#eval tstWHNF $ t7

def t8 : Expr :=
let nat  := mkConst `Nat [];
let one  := mkLit (Literal.natVal 1);
let add  := mkConst `Nat.add [];
mkLet `x nat one (mkAppN add #[one, mkBVar 0])

/-- info: let x : Nat := 1; Nat.add 1 x : Nat -/
#guard_msgs in
#eval tstInferType $ t8

/-- info: let x : Nat := 1; Nat.add 1 x ==> 2 -/
#guard_msgs in
#eval tstWHNF $ t8

def t9 : Expr :=
let nat  := mkConst `Nat [];
mkLet `a (mkSort levelOne) nat (mkForall `x BinderInfo.default (mkBVar 0) (mkBVar 1))

/-- info: let a : Type := Nat; a -> a : Type -/
#guard_msgs in
#eval tstInferType $ t9

/-- info: let a : Type := Nat; a -> a ==> Nat -> Nat -/
#guard_msgs in
#eval tstWHNF $ t9

/-- info: 10 : Nat -/
#guard_msgs in
#eval tstInferType $ mkLit (Literal.natVal 10)

/-- info: "hello" : String -/
#guard_msgs in
#eval tstInferType $ mkLit (Literal.strVal "hello")

/-- info: [mdata 10] : Nat -/
#guard_msgs in
#eval tstInferType $ mkMData {} $ mkLit (Literal.natVal 10)

def t10 : Expr :=
let nat  := mkConst `Nat [];
let refl := mkApp (mkConst `Eq.refl [levelOne]) nat;
mkLambda `a BinderInfo.default nat (mkApp refl (mkBVar 0))

/-- info: fun (a : Nat) => Eq.refl.{1} Nat a : forall (a : Nat), Eq.{1} Nat a a -/
#guard_msgs in
#eval tstInferType t10

/-- info: fun (a : Nat) => Eq.refl.{1} Nat a, isProp: false -/
#guard_msgs in
#eval tstIsProp t10

/-- info: And True True, isProp: true -/
#guard_msgs in
#eval tstIsProp (mkAppN (mkConst `And []) #[mkConst `True [], mkConst `True []])

/-- info: And, isProp: false -/
#guard_msgs in
#eval tstIsProp (mkConst `And [])

-- Example where isPropQuick fails
/-- info: id.{0} Prop (And True True), isProp: true -/
#guard_msgs in
#eval tstIsProp (mkAppN (mkConst `id [levelZero]) #[mkSort levelZero, mkAppN (mkConst `And []) #[mkConst `True [], mkConst
 `True []]])

/-- info: Eq.{1} Nat 0 1, isProp: true -/
#guard_msgs in
#eval tstIsProp (mkAppN (mkConst `Eq [levelOne]) #[mkConst `Nat [], mkLit (Literal.natVal 0), mkLit (Literal.natVal 1)])

/-- info: forall (x : Nat), Eq.{1} Nat x 1, isProp: true -/
#guard_msgs in
#eval tstIsProp $
  mkForall `x BinderInfo.default (mkConst `Nat [])
    (mkAppN (mkConst `Eq [levelOne]) #[mkConst `Nat [], mkBVar 0, mkLit (Literal.natVal 1)])

/-- info: (fun (x : Nat) => Eq.{1} Nat x 1) 0, isProp: true -/
#guard_msgs in
#eval tstIsProp $
  mkApp
    (mkLambda `x BinderInfo.default (mkConst `Nat [])
      (mkAppN (mkConst `Eq [levelOne]) #[mkConst `Nat [], mkBVar 0, mkLit (Literal.natVal 1)]))
    (mkLit (Literal.natVal 0))
