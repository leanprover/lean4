import Lean

open Lean Meta Elab Tactic Grind in
elab "grind_pre" : tactic => do
  let declName := (← Term.getDeclName?).getD `_main
  liftMetaTactic fun mvarId => do
    let result ← Meta.Grind.main mvarId declName
    return result.goals.map (·.mvarId) |>.toList

abbrev f (a : α) := a

/--
warning: declaration uses 'sorry'
---
info: a b c : Bool
h : a = true ∧ (b = true ∨ c = true)
⊢ (b && a) = true
-/
#guard_msgs in
example (h : (f a && (b || f (f c))) = true) : b && a := by
  grind_pre
  trace_state
  sorry

def g (i : Nat) (j : Nat) (_ : i > j := by omega) := i + j

example (i j : Nat) (h : i > j) : g (i+1) j = f ((fun x => x) i) + f j + 1 := by
  grind_pre
  guard_target =ₛ @g (i+1) j (_example.proof_1 i j h) = i + j + 1
  simp_arith [g]
