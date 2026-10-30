/-!
Tests that `lia` proofs are well-scoped when the subgoals of `cases_next` are closed later by `finish`.
The cutsat constraints stored in these subgoals by `cases_next` must not be hoisted to case splits
below the ones of the proofs that use them.
-/
set_option grind.debug true
set_option linter.unusedVariables false

example (x y z w v : Int) (p4 : Prop) (h0 : 3*x + w + z ≥ 2) (h1 : -w + 3*v + z > 2)
    (h2 : z + v = -3 ∨ v + 3*x + w = 3) (h3 : p4)
    (h4 : p4 → 3*x + w + z ≤ 1 ∨ max (x + z + 2*y) z ≤ 1 ∨ -w + 3*v + z = 2)
    (h5 : p4 ∨ 2*v + -x ≥ 1) (h6 : x + z + 2*y ≥ 2) (h7 : 3*z + x + 2*v ≤ -3 ∨ x + z + v = -2) :
    False := by
  grind =>
    cases_next
    all_goals finish

example (x y z w v : Int) (p4 : Prop) (h0 : 3*x + w + z ≥ 2) (h1 : -w + 3*v + z > 2)
    (h2 : z + v = -3 ∨ v + 3*x + w = 3) (h3 : p4)
    (h4 : p4 → 3*x + w + z ≤ 1 ∨ max (x + z + 2*y) z ≤ 1 ∨ -w + 3*v + z = 2)
    (h5 : p4 ∨ 2*v + -x ≥ 1) (h6 : x + z + 2*y ≥ 2) (h7 : 3*z + x + 2*v ≤ -3 ∨ x + z + v = -2) :
    False := by
  grind =>
    cases_next
    all_goals (cases_next; all_goals finish)
