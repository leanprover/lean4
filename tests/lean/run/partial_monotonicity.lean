-- Tests the `partial_monotonicity` tactic

open Lean.Tailrec

example : monotone (fun (f : Nat → Option Unit) => do {do f 1; f 2; f 3}) := by
  partial_monotonicity

-- The tactic only handels unary functions:

/--
error: Failed to prove monotonicity of:
  fun x => x
-/
#guard_msgs in
example : monotone (fun (f : Option Unit) => do {do f; f; f}) := by
  partial_monotonicity
