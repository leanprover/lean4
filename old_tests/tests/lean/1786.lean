theorem nil_subset : (true ∧ true) = true := by simp
open list

example (x : ℕ) : x = x := by simp [nil_subset]
