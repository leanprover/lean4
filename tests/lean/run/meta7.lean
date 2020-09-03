import Lean.Meta
open Lean
open Lean.Meta

set_option trace.Meta true
set_option trace.Meta.isDefEq.step false
set_option trace.Meta.isDefEq.delta false
set_option trace.Meta.isDefEq.assign false

def print (msg : MessageData) : MetaM Unit :=
trace! `Meta.debug msg

def check (x : MetaM Bool) : MetaM Unit :=
unlessM x $ throwError "check failed"

def ex : Nat × Nat :=
let x  := 10;
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
    pure ()

#eval tst1
