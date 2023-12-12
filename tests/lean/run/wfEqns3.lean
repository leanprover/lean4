import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

def f (x : Nat) : Nat :=
  if h : x = 0 then
    1
  else
   f (x - 1) * 2
decreasing_by
  apply Nat.pred_lt
  exact h

#eval tst ``f
#check f._eq_1
#check f._unfold
