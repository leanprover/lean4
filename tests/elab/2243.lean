import Lean

open Lean Elab Tactic in
elab "exact_false" : tactic =>
  closeMainGoal `exact_false (mkConst ``Bool.false)

def f (b : Bool := by exact_false) : Nat := bif b then 1 else 0

example : f false = bif false then 1 else 0 := by rw [f]
example : f true = bif true then 1 else 0 := by rw [f]
example (b : Bool) : f b = bif b then 1 else 0 := by rw [f]

def g (x : Nat) (b : Bool := by exact_false) : Nat :=
  match x with
  | 0 => bif b then 1 else 0
  | x+1 => g x b + 1

example : g (x+1) true = g x true + 1 := by rw [g]
example : g (x+1) false = g x false + 1 := by rw [g]
example : g (x+1) = g x false + 1 := by rw [g]
example : g (x+1) b = g x b + 1 := by rw [g]

def foo (x n : Nat) (b : Bool := by exact_false) : Nat :=
  if _ : x < n then
    foo (x+1) n b + 1
  else
    g x b
termination_by n - x

example : foo x n true = if _ : x < n then foo (x+1) n true + 1 else g x true := by
  rw [foo]
example : foo x n b = if _ : x < n then foo (x+1) n b + 1 else g x b := by
  rw [foo]
example : foo x n false = if _ : x < n then foo (x+1) n false + 1 else g x false := by
  rw [foo]
