import Lean

open Lean
open Lean.Meta

inductive Vec (α : Type) : Nat → Type
| nil      : Vec α 0
| cons {n} : α → Vec α n → Vec α (n+1)

set_option trace.Meta.debug true

def nat  := mkConst `Nat
def succ := mkConst `Nat.succ

def tst1 : MetaM Unit :=
withLocalDeclD `n nat fun n => do
let n1    := mkApp succ n
let vecN1 := mkApp2 (mkConst `Vec) nat n1
withLocalDeclD `xs vecN1 fun xs => do
generalizeTelescope #[n1, xs] fun ys => do
let t ← mkLambdaFVars ys ys.back!
trace[Meta.debug] t
pure ()

/-- info: [Meta.debug] fun x x => x -/
#guard_msgs in
#eval tst1

set_option pp.all true

def tst2 : MetaM Unit :=
withLocalDeclD `n nat fun n => do
let n1    := mkApp succ n
let vecN1 := mkApp2 (mkConst `Vec) nat n1
withLocalDeclD `xs vecN1 $ fun xs => do
let e ← mkEqRefl xs
generalizeTelescope #[n1, xs, e] fun ys => do
let t ← mkLambdaFVars ys ys.back!
trace[Meta.debug] t
pure ()

/-- info: [Meta.debug] fun (x : Nat) (x_1 : Vec Nat x) (x : @Eq.{1} (Vec Nat x) x_1 x_1) => x -/
#guard_msgs in
#eval tst2

def failIfSuccess (x : MetaM Unit) : MetaM Unit := do
let worked ← try x; pure true catch _ => pure false
if worked then
  throwError "unexpected success"

def tst3 : MetaM Unit :=
withLocalDeclD `n nat $ fun n => do
let n1    := mkApp succ n
let vecN1 := mkApp2 (mkConst `Vec) nat n1
withLocalDeclD `xs vecN1 $ fun xs => do
let e ← mkEqRefl xs
failIfSuccess do
  generalizeTelescope #[n1, e] fun ys => do
  let t ← mkLambdaFVars ys ys.back!
  trace[Meta.debug] t
  pure ()
trace[Meta.debug] "failed as expected"

/-- info: [Meta.debug] failed as expected -/
#guard_msgs in
#eval tst3
