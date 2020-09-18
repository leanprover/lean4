import Lean.Meta
new_frontend
open Lean
open Lean.Meta

partial def fact : Nat → Nat
| 0 => 1
| n+1 => (n+1)*fact n

set_option trace.Meta.debug true
set_option trace.Meta.check false

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throwError "check failed"

def ex (x_1 x_2 x_3 : Nat) : Nat × Nat :=
let x  := fact (10 + x_1 + x_2 + x_3);
let ty := Nat → Nat;
let f  : ty := fun x => x;
let n  := 20;
let z  := f 10;
(let y  : { v : Nat // v = n } := ⟨20, rfl⟩; y.1 + n + f x, z + 10)

def tst1 : MetaM Unit := do
print "----- tst1 -----";
c ← getConstInfo `ex;
lambdaTelescope c.value?.get! fun xs body =>
  withTrackingZeta do
    Meta.check body;
    ys ← getZetaFVarIds;
    let ys := ys.toList.map mkFVar;
    print ys;
    check $ pure $ ys.length == 2;
    c ← mkAuxDefinitionFor `foo body;
    print c;
    Meta.check c;
    pure ()

#eval tst1

#print foo

def tst2 : MetaM Unit := do
print "----- tst2 -----";
let nat := mkConst `Nat;
let t0  := mkApp (mkConst `IO) nat;
let t   := mkForall `_ BinderInfo.default nat t0;
print t;
Meta.check t;
forallBoundedTelescope t (some 1) fun xs b => do
  print b;
  check $ pure $ xs.size == 1;
  check $ pure $ b == t0;
  pure ()

#eval tst2


def tst3 : MetaM Unit := do
print "----- tst2 -----";
let nat := mkConst `Nat;
let t0  := mkApp (mkConst `IO) nat;
let t   := t0;
print t;
Meta.check t;
forallBoundedTelescope t (some 0) fun xs b => do
  print b;
  check $ pure $ xs.size == 0;
  check $ pure $ b == t0;
  pure ()

#eval tst3

def tst4 : MetaM Unit := do
print "----- tst4 -----";
let nat := mkConst `Nat;
withLocalDeclD `x nat fun x =>
withLocalDeclD `y nat fun y => do
m ← mkFreshExprMVar nat;
print (← ppGoal m.mvarId!);
val ← mkAppM `HasAdd.add #[mkNatLit 10, y];
⟨zId, nId, subst⟩ ← assertAfter m.mvarId! x.fvarId! `z nat val;
print m;
print (← ppGoal nId);
withMVarContext nId do {
  print (subst.apply x ++ " " ++ subst.apply y ++ " " ++ mkFVar zId);
  assignExprMVar nId (← mkAppM `HasAdd.add #[subst.apply x, mkFVar zId]);
  print (mkMVar nId)
};
print m;
expected ← mkAppM `HasAdd.add #[x, val];
check (isDefEq m expected);
pure ()

#eval tst4

def tst5 : MetaM Unit := do
print "----- tst5 -----";
let prop := mkSort levelZero;
withLocalDeclD `p prop fun p =>
withLocalDeclD `q prop fun q => do
withLocalDeclD `h₁ p fun h₁ => do
eq ← mkEq p q;
withLocalDeclD `h₂ eq fun h₂ => do
m ← mkFreshExprMVar q;
r ← replaceLocalDecl m.mvarId! h₁.fvarId! q h₂;
print (← ppGoal r.mvarId);
assignExprMVar r.mvarId (mkFVar r.fvarId);
print m;
Lean.Meta.check m;
pure ()

#eval tst5
