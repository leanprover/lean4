import Lean.Meta

open Lean
open Lean.Meta

partial def fact : Nat → Nat
| 0   => 1
| n+1 => (n+1)*fact n

set_option trace.Meta.debug true
set_option trace.Meta.check false

def print (msg : MessageData) : MetaM Unit := do
trace[Meta.debug] msg

def checkM (x : MetaM Bool) : MetaM Unit :=
unless (← x) do throwError "check failed"

def ex (x_1 x_2 x_3 : Nat) : Nat × Nat :=
let x  := fact (10 + x_1 + x_2 + x_3);
let ty := Nat → Nat;
let f  : ty := fun x => x;
let n  := 20;
let z  := f 10;
(let y  : { v : Nat // v = n } := ⟨20, rfl⟩; y.1 + n + f x, z + 10)

def tst1 : MetaM Unit := do
print "----- tst1 -----";
let c ← getConstInfo `ex;
lambdaTelescope c.value?.get! fun xs body =>
  withTrackingZetaDelta do
    check body;
    let ys ← getZetaDeltaFVarIds;
    let ys := ys.toList.map mkFVar;
    print ys;
    checkM $ pure $ ys.length == 2;
    let c ← mkAuxDefinitionFor `foo body;
    print c;
    check c;
    pure ()

#eval tst1

#print foo

def tst2 : MetaM Unit := do
print "----- tst2 -----";
let nat := mkConst `Nat;
let t0  := mkApp (mkConst `IO) nat;
let t   := mkForall `_ BinderInfo.default nat t0;
print t;
check t;
forallBoundedTelescope t (some 1) fun xs b => do
  print b;
  checkM $ pure $ xs.size == 1;
  checkM $ pure $ b == t0;
  pure ()

/--
info: [Meta.debug] ----- tst2 -----
[Meta.debug] Nat → IO Nat
[Meta.debug] IO Nat
-/
#guard_msgs in
#eval tst2


def tst3 : MetaM Unit := do
print "----- tst2 -----";
let nat := mkConst `Nat;
let t0  := mkApp (mkConst `IO) nat;
let t   := t0;
print t;
check t;
forallBoundedTelescope t (some 0) fun xs b => do
  print b;
  checkM $ pure $ xs.size == 0;
  checkM $ pure $ b == t0;
  pure ()

/--
info: [Meta.debug] ----- tst2 -----
[Meta.debug] IO Nat
[Meta.debug] IO Nat
-/
#guard_msgs in
#eval tst3

def tst4 : MetaM Unit := do
print "----- tst4 -----";
let nat := mkConst `Nat;
withLocalDeclD `x nat fun x =>
withLocalDeclD `y nat fun y => do
let m ← mkFreshExprMVar nat;
print (← ppGoal m.mvarId!);
let val ← mkAppM `Add.add #[mkNatLit 10, y];
let ⟨zId, nId, subst⟩ ← m.mvarId!.assertAfter x.fvarId! `z nat val;
print m;
print (← ppGoal nId);
nId.withContext do {
  print m!"{subst.apply x} {subst.apply y} {mkFVar zId}";
  nId.assign (← mkAppM `Add.add #[subst.apply x, mkFVar zId]);
  print (mkMVar nId)
};
print m;
let expected ← mkAppM `Add.add #[x, val];
checkM (isDefEq m expected);
pure ()

set_option pp.mvars false in
/--
info: [Meta.debug] ----- tst4 -----
[Meta.debug] x y : Nat
    ⊢ Nat
[Meta.debug] ?_ (Add.add 10 y) y
[Meta.debug] x z y : Nat
    ⊢ Nat
[Meta.debug] x y z
[Meta.debug] Add.add x z
[Meta.debug] Add.add x (Add.add 10 y)
-/
#guard_msgs in
#eval tst4

def tst5 : MetaM Unit := do
print "----- tst5 -----";
let prop := mkSort levelZero;
withLocalDeclD `p prop fun p =>
withLocalDeclD `q prop fun q => do
withLocalDeclD `h₁ p fun h₁ => do
let eq ← mkEq p q;
withLocalDeclD `h₂ eq fun h₂ => do
let m ← mkFreshExprMVar q;
let r ← m.mvarId!.replaceLocalDecl h₁.fvarId! q h₂;
print (← ppGoal r.mvarId);
r.mvarId.assign (mkFVar r.fvarId);
print m;
check m;
pure ()

/--
info: [Meta.debug] ----- tst5 -----
[Meta.debug] p q : Prop
    h₁ : q
    h₂ : p = q
    ⊢ q
[Meta.debug] Eq.mp h₂ h₁
-/
#guard_msgs in
#eval tst5

def tst6 : MetaM Unit := do
print "----- tst6 -----";
let nat := mkConst `Nat;
withLocalDeclD `x nat fun x =>
withLocalDeclD `y nat fun y => do
let m ← mkFreshExprMVar nat;
print (← ppGoal m.mvarId!);
let val ← mkAppM `Add.add #[mkNatLit 10, y];
let ⟨zId, nId, subst⟩ ← m.mvarId!.assertAfter y.fvarId! `z nat val;
print m;
print (← ppGoal nId);
nId.withContext do {
  print m!"{subst.apply x} {subst.apply y} {mkFVar zId}";
  nId.assign (← mkAppM `Add.add #[subst.apply x, mkFVar zId]);
  print (mkMVar nId)
};
print m;
let expected ← mkAppM `Add.add #[x, val];
checkM (isDefEq m expected);
pure ()

set_option pp.mvars false in
/--
info: [Meta.debug] ----- tst6 -----
[Meta.debug] x y : Nat
    ⊢ Nat
[Meta.debug] ?_ (Add.add 10 y)
[Meta.debug] x y z : Nat
    ⊢ Nat
[Meta.debug] x y z
[Meta.debug] Add.add x z
[Meta.debug] Add.add x (Add.add 10 y)
-/
#guard_msgs in
#eval tst6

def tst7 : MetaM Unit := do
print "----- tst7 -----";
let nat := mkConst `Nat;
withLocalDeclD `x nat fun x =>
withLocalDeclD `y nat fun y => do
let val ← mkAppM `Add.add #[x, y];
print val;
let val := val.replaceFVars #[x, y] #[mkNatLit 0, mkNatLit 1];
print val;
let expected ← mkAppM `Add.add #[mkNatLit 0, mkNatLit 1];
print expected;
checkM (pure $ val == expected);
pure ()

/--
info: [Meta.debug] ----- tst7 -----
[Meta.debug] Add.add x y
[Meta.debug] Add.add 0 1
[Meta.debug] Add.add 0 1
-/
#guard_msgs in
#eval tst7

def aux := [1, 2, 3].isEmpty

def tst8 : MetaM Unit := do
  print "----- tst8 -----"
  let t := mkConst `aux
  let some t ← unfoldDefinition? t | throwError "unexpected"
  let some t ← unfoldDefinition? t | throwError "unexpected"
  print t
  let t ← whnfCore t
  print t
  pure ()

/--
info: [Meta.debug] ----- tst8 -----
[Meta.debug] match [1, 2, 3] with
    | [] => true
    | head :: tail => false
[Meta.debug] false
-/
#guard_msgs in
#eval tst8

def tst9 : MetaM Unit := do
  print "----- tst9 -----"
  let defInsts ← getDefaultInstances `OfNat
  print (toString defInsts)
  pure ()

/--
info: [Meta.debug] ----- tst9 -----
[Meta.debug] [(instOfNatNat, 100)]
-/
#guard_msgs in
#eval tst9


mutual
inductive Foo (α : Type) where
  | mk : List (Bla α) → Foo α
  | leaf : α → Foo α
inductive Bla (α : Type) where
  | nil : Bla α
  | cons : Foo α → Bla α → Bla α
end

def tst10 : MetaM Unit := do
  assert! !(← getConstInfoInduct `List).isNested
  assert! (← getConstInfoInduct `Bla).isNested
  assert! (← getConstInfoInduct `Foo).isNested
  assert! !(← getConstInfoInduct `Prod).isNested

#guard_msgs in
#eval tst10

def tst11 : MetaM Unit := do
  print "----- tst11 -----"
  withLocalDeclD `x (mkConst ``True) fun x =>
  withLocalDeclD `y (mkConst ``True) fun y => do
    checkM (isDefEq x y)
    pure ()

/-- info: [Meta.debug] ----- tst11 ----- -/
#guard_msgs in
#eval tst11

def tst12 : MetaM Unit := do
  print "----- tst12 -----";
  let nat := mkConst `Nat
  withLocalDeclD `x nat fun x =>
  withLocalDeclD `y nat fun y => do
  let val ← mkAppM' (mkConst `Add.add [levelZero]) #[mkNatLit 10, y];
  check val; print val
  let val ← mkAppM' (mkApp (mkConst ``Add.add [levelZero]) (mkConst ``Int)) #[mkApp (mkConst ``Int.ofNat) (mkNatLit 10), mkApp (mkConst ``Int.ofNat) y];
  check val; print val
  let val ← mkAppOptM' (mkConst `Add.add [levelZero]) #[mkConst  ``Nat, none, mkNatLit 10, y];
  check val; print val
  pure ()

/--
info: [Meta.debug] ----- tst12 -----
[Meta.debug] Add.add 10 y
[Meta.debug] Add.add (Int.ofNat 10) (Int.ofNat y)
[Meta.debug] Add.add 10 y
-/
#guard_msgs in
#eval tst12

#check @Add.add
