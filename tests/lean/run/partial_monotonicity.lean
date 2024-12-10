-- Tests the `partial_monotonicity` tactic

-- These can move to Init after a stage0 update
attribute [partial_monotone]
  Lean.Tailrec.monotone_ite
  Lean.Tailrec.monotone_dite
  Lean.Tailrec.monotone_bind
  Lean.Tailrec.monotone_mapM
  Lean.Tailrec.monotone_mapFinIdxM

open Lean.Tailrec

example : monotone (fun (f : Nat → Option Unit) => do {do f 1; f 2; f 3}) := by
  repeat' partial_monotonicity

-- The tactic only handels unary functions:

/--
error: Failed to prove monotonicity of:
  fun x => x
---
error: Failed to prove monotonicity of:
  fun x => x
---
error: Failed to prove monotonicity of:
  fun x => x
-/
#guard_msgs in
example : monotone (fun (f : Option Unit) => do {do f; f; f}) := by
  partial_monotonicity
  · partial_monotonicity
  · partial_monotonicity
    partial_monotonicity
    · partial_monotonicity
    · partial_monotonicity
      partial_monotonicity
