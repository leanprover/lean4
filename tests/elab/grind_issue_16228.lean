/-!
Regression test for #16228: `lia` creates variables inside a Cooper split (here, by eliminating an
equation without unit coefficients). The proof of the refuted case uses them, so they must survive
backtracking.
-/

example (x : Int) : x % 3 ≤ 2 * x % 3 → 4 * x % 3 ≤ 2 * x % 3 := by
  lia

example (x : Int) : x % 3 ≤ 2 * x % 3 → 4 * x % 3 ≤ 2 * x % 3 := by
  grind

set_option grind.debug true in
example (x : Int) : x % 3 ≤ 2 * x % 3 → 4 * x % 3 ≤ 2 * x % 3 := by
  lia
