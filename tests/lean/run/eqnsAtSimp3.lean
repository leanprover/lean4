import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getEqnsFor? declName)

def f (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * f x 0
  | x+1, y => 2 * f x y

#eval tst ``f
#check f._eq_1
#check f._eq_2
#check f._eq_3
#check f._eq_4
