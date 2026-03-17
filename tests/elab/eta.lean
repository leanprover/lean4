import Lean

open Lean in
open Lean.Meta in
def tst (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  trace[Meta.debug] ">> {info.value!.eta}"

def aux1 := fun (x : Nat) y z => Nat.add y z
def aux2 := fun y z => Nat.add y z
def aux3 := (1+.)
def aux4 := fun (x : Nat) y z => Nat.add z y
def aux5 := fun y => Nat.add y y

set_option trace.Meta.debug true
#eval tst `aux1
#eval tst `aux2
#eval tst `aux3
#eval tst `aux4
#eval tst `aux5
