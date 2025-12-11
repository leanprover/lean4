/-!
# Interactive tests of the induction tactic
-/

/-!
On an incomplete proof, the goal is visible at least for the first alternative.
-/
example (as bs : List Nat) : (as.append bs).length = as.length + bs.length := by
  induction as with
  | nil =>
        --^ $/lean/plainGoal
  | cons b bs ih =>

example (as bs : List Nat) : (as.append bs).length = as.length + bs.length := by
  induction as with
  | nil => sorry
  | cons b bs ih => sorry
  --
--^ $/lean/plainGoal
