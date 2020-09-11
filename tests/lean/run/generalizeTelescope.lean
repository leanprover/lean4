import Lean
new_frontend
open Lean
open Lean.Meta

inductive Vec (α : Type) : Nat → Type
| nil      : Vec α 0
| cons {n} : α → Vec α n → Vec α (n+1)

set_option trace.Meta.debug true

def nat  := mkConst `Nat
def succ := mkConst `Nat.succ

def tst1 : MetaM Unit :=
withLocalDeclD `n nat $ fun n => do
let n1    := mkApp succ n;
let vecN1 := mkApp2 (mkConst `Vec) nat n1;
withLocalDeclD `xs vecN1 $ fun xs => do
generalizeTelescope #[n1, xs] `aux $ fun ys => do
t ← mkLambdaFVars ys ys.back;
trace! `Meta.debug t;
pure ()

#eval tst1

set_option pp.all true

def tst2 : MetaM Unit :=
withLocalDeclD `n nat $ fun n => do
let n1    := mkApp succ n;
let vecN1 := mkApp2 (mkConst `Vec) nat n1;
withLocalDeclD `xs vecN1 $ fun xs => do
e ← mkEqRefl xs;
generalizeTelescope #[n1, xs, e] `aux $ fun ys => do
t ← mkLambdaFVars ys ys.back;
trace! `Meta.debug t;
pure ()

#eval tst2

def failIfSuccess (x : MetaM Unit) : MetaM Unit :=
whenM (catch (x *> pure true) (fun _ => pure false)) $
  throwError "unexpected success"

def tst3 : MetaM Unit :=
withLocalDeclD `n nat $ fun n => do
let n1    := mkApp succ n;
let vecN1 := mkApp2 (mkConst `Vec) nat n1;
withLocalDeclD `xs vecN1 $ fun xs => do
e ← mkEqRefl xs;
failIfSuccess $ do {
  generalizeTelescope #[n1, e] `aux $ fun ys => do
  t ← mkLambdaFVars ys ys.back;
  trace! `Meta.debug t;
  pure ()
};
trace! `Meta.debug "failed as expected"

#eval tst3
