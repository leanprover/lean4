import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => g i j

/-- info: (some g.eq_def) -/
#guard_msgs in
#eval tst ``g
#check g.eq_1
#check g.eq_2
#check g.eq_def

def h (i j : Nat) : Nat :=
  let z :=
    match j with
    | Nat.zero => 1
    | Nat.succ j => h i j
  z + z

/-- info: (some h.eq_def) -/
#guard_msgs in
#eval tst ``h
#check h.eq_1
#check h.eq_2
#check h.eq_def
