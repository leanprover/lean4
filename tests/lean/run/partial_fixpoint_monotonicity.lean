-- Tests the `monotonicity` tactic

/-
Should test that the tactic syntax is scoped, but cannot use #guard_msgs to catch “tactic not known”
errors, it seems:

/--
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by monotonicity

-/

open Lean.Order

example : monotone (fun (f : Nat → Option Unit) => do {do f 1; f 2; f 3}) := by
  repeat monotonicity

example : monotone (fun (f : Option Unit) => do {do f; f; f}) := by
  repeat monotonicity

example : monotone
  (fun (f : Nat → Option Unit) => do
    for x in [1,2,3] do f x) := by
  repeat' monotonicity
