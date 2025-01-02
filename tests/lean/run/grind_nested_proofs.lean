import Lean

def f (α : Type) [Add α] (a : α) := a + a + a

open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let nodes ← filterENodes fun e => return e.self.isAppOf ``Lean.Grind.nestedProof
    logInfo (nodes.toList.map (·.self))
    let nodes ← filterENodes fun e => return e.self.isAppOf ``GetElem.getElem
    let [_, n, _] := nodes.toList | unreachable!
    logInfo (← getEqc n.self)

set_option grind.debug true
set_option grind.debug.proofs true

/-
Recall that array access terms, such as `a[i]`, have nested proofs.
The following test relies on `grind` `nestedProof` wrapper to
detect equalities between array access terms.
-/

/-
info: [Lean.Grind.nestedProof (i < a.toList.length) (_example.proof_1 i j a b h1 h2),
 Lean.Grind.nestedProof (j < a.toList.length) h1,
 Lean.Grind.nestedProof (j < b.toList.length) h]
---
info: [a[i], b[j], a[j]]
---
warning: declaration uses 'sorry'
-/
-- #guard_msgs in

set_option trace.Meta.debug true

example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → a = b → False := by
  grind_test
  sorry

#exit

/--
info: [Lean.Grind.nestedProof (i < a.toList.length) (_example.proof_1 i j a b h1 h2),
 Lean.Grind.nestedProof (j < a.toList.length) h1,
 Lean.Grind.nestedProof (j < b.toList.length) h]
---
info: [a[i], a[j]]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → False := by
  grind_test
  sorry
