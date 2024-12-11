-- Tests the `monotonicity` tactic

-- These can move to Init after a stage0 update
open Lean.Order in
attribute [partial_fixpoint_monotone]
  monotone_ite
  monotone_dite
  monotone_bind
  monotone_mapM
  monotone_mapFinIdxM


/-
Shoudl test that the tactic syntax is scoped, but cannot use #guard_msgs to catch “tactic not known”
error:

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
  monotonicity
  · monotonicity
  · monotonicity
    monotonicity
    · monotonicity
    · monotonicity
      monotonicity
