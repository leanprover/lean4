import Lean

def f (α : Type) [Add α] (a : α) := a + a + a

open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let nodes ← filterENodes fun e => return e.self.isAppOf ``Lean.Grind.nestedProof
    logInfo (nodes.toList.map (·.self))

/--
info: [Lean.Grind.nestedProof (i < a.toList.length) (_example.proof_1 i j a b h1 h2),
 Lean.Grind.nestedProof (j < a.toList.length) h1,
 Lean.Grind.nestedProof (j < b.toList.length) h]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → a = b → False := by
  grind_test
  sorry
