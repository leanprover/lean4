import Init.Lean
open Lean
open Lean.Meta

inductive Vec (α : Type) : Nat → Type
| nil      : Vec 0
| cons {n} : α → Vec n → Vec (n+1)

set_option trace.Meta.debug true

def nat  := mkConst `Nat
def succ := mkConst `Nat.succ

def tst1 : MetaM Unit :=
withLocalDecl `n nat BinderInfo.default $ fun n => do
let n1    := mkApp succ n;
let vecN1 := mkApp2 (mkConst `Vec) nat n1;
withLocalDecl `xs vecN1 BinderInfo.default $ fun xs => do
generalizeTelescope #[n1, xs] `aux $ fun ys => do
let ys := (ys.map mkFVar);
t ← mkLambda ys ys.back;
trace! `Meta.debug t;
pure ()

#eval tst1

set_option pp.all true

def tst2 : MetaM Unit :=
withLocalDecl `n nat BinderInfo.default $ fun n => do
let n1    := mkApp succ n;
let vecN1 := mkApp2 (mkConst `Vec) nat n1;
withLocalDecl `xs vecN1 BinderInfo.default $ fun xs => do
e ← mkEqRefl xs;
generalizeTelescope #[n1, xs, e] `aux $ fun ys => do
let ys := (ys.map mkFVar);
t ← mkLambda ys ys.back;
trace! `Meta.debug t;
pure ()

#eval tst2

def failIfSuccess (x : MetaM Unit) : MetaM Unit :=
whenM (catch (x *> pure true) (fun _ => pure false)) $
  throw $ Exception.other "unexpected success"

def tst3 : MetaM Unit :=
withLocalDecl `n nat BinderInfo.default $ fun n => do
let n1    := mkApp succ n;
let vecN1 := mkApp2 (mkConst `Vec) nat n1;
withLocalDecl `xs vecN1 BinderInfo.default $ fun xs => do
e ← mkEqRefl xs;
failIfSuccess $ do {
  generalizeTelescope #[n1, e] `aux $ fun ys => do
  let ys := (ys.map mkFVar);
  t ← mkLambda ys ys.back;
  trace! `Meta.debug t;
  pure ()
};
trace! `Meta.debug "failed as expected"

#eval tst3
