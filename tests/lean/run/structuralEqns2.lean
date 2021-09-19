import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getEqnsFor? declName)

def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => g i j

#eval tst ``g
#check g.eq_1
#check g.eq_2
#check g.eq_3

def h (i j : Nat) : Nat :=
  let z :=
    match j with
    | Nat.zero => 1
    | Nat.succ j => h i j
  z + z

#eval tst ``h
#check h.eq_1
#check h.eq_2
