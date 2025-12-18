import Lean

open Lean Meta Elab
open Lean.Elab.Structural

/-!
Unit test for `IndGroupInst.nestedTypeFormers`
-/

inductive Tree (α : Type u) : Type u
 | node : α → (Bool → Tree α) → List (Tree α) → Tree α


/-- info: [List (Tree Bool)] -/
#guard_msgs in
run_meta
  let igi : IndGroupInst := {all := #[``Tree], levels := [0], params := #[.const ``Bool []], numNested := 1}
  logInfo m!"{← igi.nestedTypeFormers}"

inductive Vec (α : Type u) : Nat → Type u where
  | empty : Vec α 0
  | succ : α → Vec α n → Vec α (n + 1)

inductive VTree (α : Type u) : Type u
 | node : α → Vec (VTree α) 32 → VTree α

/-- info: [(a : Nat) → Vec (VTree Bool) a] -/
#guard_msgs in
run_meta
  let igi : IndGroupInst := {all := #[``VTree], levels := [0], params := #[.const ``Bool []], numNested := 1}
  logInfo m!"{← igi.nestedTypeFormers}"
