/-!
`lia` creates variables during its case-split search: `EqCnstr.elimNonUnit` introduces `σ := p̄ / m`
inside Cooper cases (#16228). These goals were found by differential testing against `omega` on linear
goals with `/` and `%` by constants, and each one creates such a variable. In the goals marked `reuse`,
`σ` is needed again after backtracking or after a variable reordering.
-/

example (x : Int) : x % 3 ≤ 2 * x % 3 → 4 * x % 3 ≤ 2 * x % 3 := by
  lia

example (x : Int) : (-1 * x) % 3 ≠ (-1 * x) / 3 + -2 → (-2 * x) % 3 ≠ (2 * x) % 3 → (4 * x) % 3 = (x) % 3 := by lia

example (x : Int) : (-1 * x) % 3 = (-2 * x) / 3 → (2 * x) % 3 < (5 * x) % 3 + 1 → (2 * x) % 3 < (x) % 3 → (x) % 3 = (4 * x) % 3 := by lia

example (x : Int) : (-1 * x) / 3 < (3 * x) / 3 + 1 → (5 * x) % 3 ≠ (-1 * x) % 3 → (2 * x) % 3 = (x) % 3 := by lia

example (x : Int) : (-1 * x) % 5 ≠ (4 * x) % 5 → (3 * x) % 5 < (-2 * x) % 5 → (x) / 5 ≠ (2 * x) / 5 → (2 * x) % 5 < (-2 * x) % 5 + -2 := by lia

example (x : Int) : (-1 * x) % 6 ≤ (3 * x) % 6 → (3 * x) % 6 < (4 * x) % 6 → (5 * x) % 6 < (-1 * x) % 6 → (4 * x) / 6 ≤ (-2 * x) % 6 := by lia -- reuse

example (x : Int) : (-1 * x) / 6 ≤ (5 * x) % 6 + -2 → (x) % 6 < (3 * x) % 6 + 0 → (4 * x) % 6 = (3 * x) / 6 → (2 * x) / 6 = (-1 * x) % 6 := by lia

example (x : Int) : (-1 * x) % 6 ≠ (5 * x) % 6 → (3 * x) % 6 < (5 * x) / 6 → (3 * x) % 6 < (-2 * x) % 6 := by lia -- reuse

example (x : Int) : (-1 * x) % 6 ≠ (5 * x) % 6 → (5 * x) % 6 < (4 * x) % 6 → (5 * x) / 6 = (3 * x) % 6 := by lia

example (x : Int) : (-1 * x) % 7 ≠ (2 * x) % 7 + -1 → (5 * x) % 7 ≠ (-2 * x) % 7 → (3 * x) % 7 = (3 * x) / 7 := by lia

example (x : Int) : (-1 * x) % 7 < (3 * x) / 7 + -1 → (5 * x) % 7 = (3 * x) / 7 → (-2 * x) % 7 ≤ (5 * x) % 7 := by lia

example (x : Int) : (-1 * x) % 7 < (4 * x) % 7 → (-1 * x) / 7 < (3 * x) % 7 → (5 * x) % 7 < (-2 * x) % 7 → (-1 * x) % 7 = (4 * x) % 7 := by lia

example (x : Int) : (-2 * x) % 3 ≠ (5 * x) % 3 → (-1 * x) % 3 = (-1 * x) % 3 → (2 * x) % 3 ≠ (-1 * x) % 3 → (4 * x) % 3 < (x) % 3 := by lia

example (x : Int) : (-2 * x) % 3 < (5 * x) % 3 → (-2 * x) % 3 = (4 * x) % 3 := by lia

example (x : Int) : (-2 * x) % 5 = (2 * x) / 5 → (3 * x) % 5 ≠ (-1 * x) % 5 → (4 * x) % 5 < (-1 * x) % 5 → (2 * x) / 5 < (x) / 5 := by lia

example (x : Int) : (-2 * x) % 5 ≠ (2 * x) % 5 → (3 * x) % 5 < (2 * x) % 5 → (4 * x) % 5 < (-1 * x) % 5 + -1 → (3 * x) % 5 < (-2 * x) % 5 := by lia -- reuse

example (x : Int) : (-2 * x) % 5 < (3 * x) % 5 → (-1 * x) % 5 < (2 * x) / 5 → (-2 * x) / 5 = (4 * x) % 5 := by lia -- reuse

example (x : Int) : (-2 * x) % 5 < (3 * x) % 5 → (2 * x) % 5 ≤ (5 * x) / 5 → (4 * x) % 5 < (3 * x) / 5 + -2 → (-2 * x) % 5 = (4 * x) % 5 + -2 := by lia

example (x : Int) : (-2 * x) % 5 < (4 * x) % 5 → (5 * x) % 5 ≤ (2 * x) % 5 + 1 := by lia

example (x : Int) : (2 * x) / 5 ≤ (5 * x) % 5 + 0 → (4 * x) / 5 < (x) % 5 → (3 * x) % 5 < (2 * x) % 5 + -2 → (4 * x) % 5 = (-1 * x) % 5 := by lia

example (x : Int) : (2 * x) % 5 ≠ (x) % 5 → (4 * x) % 5 < (3 * x) % 5 → (3 * x) % 5 ≠ (-2 * x) % 5 → (3 * x) % 5 < (5 * x) % 5 := by lia

example (x : Int) : (-2 * x) / 6 = (-2 * x) % 6 → (4 * x) % 6 ≤ (x) / 6 → (3 * x) % 6 ≠ (4 * x) % 6 → (3 * x) % 6 < (3 * x) / 6 + -2 := by lia

example (x : Int) : (2 * x) % 6 ≤ (2 * x) % 6 → (5 * x) % 6 ≠ (-1 * x) % 6 → (-2 * x) % 6 < (5 * x) % 6 := by lia

example (x : Int) : (-2 * x) / 6 ≠ (3 * x) / 6 + 2 → (2 * x) % 6 < (-2 * x) % 6 + -1 → (4 * x) % 6 = (-2 * x) % 6 := by lia -- reuse

example (x : Int) : (2 * x) / 6 = (3 * x) % 6 → (5 * x) % 6 ≤ (-1 * x) % 6 + -1 → (x) % 6 ≠ (3 * x) % 6 → (-2 * x) % 6 = (5 * x) % 6 := by lia -- reuse

example (x : Int) : (2 * x) / 6 ≤ (4 * x) % 6 + 0 → (5 * x) % 6 < (-1 * x) % 6 + -1 → (5 * x) / 6 ≤ (5 * x) % 6 := by lia -- reuse

example (x : Int) : (2 * x) % 7 ≤ (4 * x) / 7 + 1 → (5 * x) % 7 ≤ (x) / 7 → (5 * x) % 7 < (-2 * x) % 7 + 2 := by lia

example (x : Int) : (-2 * x) % 7 < (4 * x) % 7 → (-2 * x) % 7 < (5 * x) % 7 → (3 * x) % 7 < (x) % 7 → (-1 * x) % 7 = (3 * x) / 7 + 1 := by lia

example (x : Int) : (-2 * x) % 7 < (4 * x) % 7 → (-2 * x) % 7 = (5 * x) % 7 := by lia -- reuse

example (x : Int) : (-2 * x) % 7 < (5 * x) % 7 → (-1 * x) % 7 ≤ (2 * x) % 7 → (-1 * x) % 7 ≠ (5 * x) % 7 → (4 * x) / 7 < (-2 * x) % 7 + 0 := by lia

example (x : Int) : (-2 * x) % 7 < (5 * x) % 7 → (-1 * x) % 7 ≠ (3 * x) / 7 → (2 * x) % 7 < (4 * x) % 7 → (5 * x) % 7 < (3 * x) / 7 + 2 := by lia

example (x : Int) : (-2 * x) / 7 ≤ (5 * x) / 7 + 2 → (2 * x) % 7 ≠ (4 * x) % 7 → (-2 * x) % 7 ≠ (-2 * x) / 7 := by lia

example (x : Int) : (-2 * x) % 7 < (5 * x) % 7 → (-2 * x) % 7 < (4 * x) % 7 → (5 * x) % 7 ≤ (3 * x) / 7 := by lia -- reuse

example (x : Int) : (-2 * x) % 7 ≠ (5 * x) % 7 → (3 * x) / 7 < (4 * x) / 7 := by lia

example (x : Int) : (-2 * x) % 7 ≠ (5 * x) % 7 → (x) % 7 ≤ (2 * x) % 7 → (3 * x) % 7 < (-1 * x) % 7 + -1 → (5 * x) % 7 < (4 * x) % 7 := by lia -- reuse

example (x : Int) : (3 * x) % 3 = (5 * x) / 3 + 0 → (-2 * x) / 3 ≤ (-2 * x) % 3 → (2 * x) % 3 = (-2 * x) % 3 := by lia

example (x : Int) : (3 * x) / 3 ≠ (5 * x) % 3 → (3 * x) % 3 ≠ (-2 * x) % 3 → (-2 * x) / 3 = (5 * x) % 3 → (-2 * x) % 3 < (x) % 3 + 2 := by lia

example (x : Int) : (3 * x) % 5 < (-2 * x) % 5 + -1 → (-1 * x) % 5 ≤ (x) % 5 → (4 * x) % 5 ≤ (2 * x) % 5 := by lia -- reuse

example (x : Int) : (3 * x) / 5 ≠ (-2 * x) % 5 → (-2 * x) % 5 = (3 * x) % 5 := by lia

example (x : Int) : (3 * x) % 5 ≠ (-2 * x) % 5 → (3 * x) % 5 = (5 * x) % 5 := by lia

example (x : Int) : (3 * x) % 5 ≤ (-2 * x) % 5 → (x) % 5 ≤ (3 * x) % 5 → (4 * x) % 5 ≤ (-1 * x) % 5 + 0 := by lia -- reuse

example (x : Int) : (3 * x) % 5 ≠ (4 * x) % 5 → (-1 * x) % 5 ≠ (4 * x) % 5 → (-2 * x) % 5 < (4 * x) % 5 := by lia

example (x : Int) : (3 * x) % 5 ≤ (4 * x) % 5 → (-2 * x) / 5 ≠ (2 * x) / 5 → (4 * x) % 5 < (5 * x) % 5 → (3 * x) / 5 = (4 * x) % 5 := by lia

example (x : Int) : (3 * x) / 5 ≠ (x) % 5 + -2 → (-2 * x) % 5 ≠ (3 * x) % 5 → (x) / 5 < (4 * x) % 5 → (3 * x) % 5 ≤ (2 * x) / 5 := by lia

example (x : Int) : (3 * x) % 6 < (2 * x) % 6 → (5 * x) % 6 ≠ (-1 * x) % 6 → (4 * x) / 6 ≤ (4 * x) % 6 := by lia

example (x : Int) : (3 * x) % 6 ≤ (-2 * x) / 6 → (x) % 6 ≤ (-1 * x) % 6 → (4 * x) % 6 ≤ (-2 * x) % 6 := by lia

example (x : Int) : (3 * x) % 6 < (5 * x) / 6 → (5 * x) % 6 ≠ (-1 * x) % 6 + 1 → (4 * x) % 6 = (-2 * x) % 6 := by lia -- reuse

example (x : Int) : (3 * x) % 7 ≠ (-2 * x) / 7 → (5 * x) % 7 = (4 * x) / 7 → (-2 * x) / 7 = (4 * x) % 7 → (-2 * x) % 7 = (2 * x) / 7 := by lia

example (x : Int) : (3 * x) % 7 < (4 * x) % 7 → (-1 * x) % 7 ≤ (2 * x) % 7 + 1 → (5 * x) % 7 < (-2 * x) % 7 → (4 * x) / 7 = (3 * x) % 7 := by lia -- reuse

example (x : Int) : (3 * x) % 7 < (4 * x) / 7 → (-2 * x) % 7 = (5 * x) % 7 + 0 := by lia -- reuse

example (x : Int) : (3 * x) % 7 < (4 * x) % 7 → (3 * x) % 7 < (4 * x) % 7 → (2 * x) / 7 ≤ (-1 * x) % 7 → (-2 * x) % 7 = (5 * x) % 7 := by lia

example (x : Int) : (4 * x) % 3 < (2 * x) % 3 → (3 * x) % 3 ≠ (-1 * x) / 3 + -1 → (5 * x) / 3 ≤ (2 * x) % 3 → (4 * x) / 3 ≤ (4 * x) % 3 := by lia

example (x : Int) : (4 * x) % 3 ≤ (3 * x) % 3 → (2 * x) % 3 ≠ (-2 * x) % 3 + 0 → (2 * x) / 3 ≤ (5 * x) % 3 := by lia

example (x : Int) : (4 * x) % 3 < (5 * x) % 3 + 0 → (4 * x) % 3 < (x) % 3 → (-2 * x) % 3 = (4 * x) % 3 := by lia

example (x : Int) : (4 * x) % 3 ≤ (5 * x) % 3 → (x) % 3 ≠ (-2 * x) % 3 → (3 * x) % 3 ≤ (x) / 3 := by lia

example (x : Int) : (4 * x) / 5 ≠ (-1 * x) % 5 + -2 → (3 * x) / 5 ≠ (2 * x) / 5 → (5 * x) % 5 < (-2 * x) % 5 + 1 := by lia

example (x : Int) : (4 * x) % 5 ≠ (3 * x) % 5 + 1 → (-1 * x) % 5 < (-2 * x) % 5 → (3 * x) / 5 < (3 * x) % 5 + 2 → (-1 * x) % 5 = (4 * x) % 5 := by lia

example (x : Int) : (4 * x) / 5 ≤ (x) % 5 → (3 * x) % 5 = (-2 * x) % 5 := by lia

example (x : Int) : (4 * x) % 6 ≠ (-2 * x) % 6 → (x) / 6 ≤ (5 * x) % 6 := by lia -- reuse

example (x : Int) : (4 * x) / 6 < (3 * x) % 6 + -2 → (-2 * x) % 6 ≤ (3 * x) % 6 + 0 → (2 * x) / 6 < (-2 * x) % 6 → (-1 * x) % 6 = (5 * x) % 6 := by lia -- reuse

example (x : Int) : (4 * x) % 6 < (5 * x) % 6 → (-2 * x) % 6 ≤ (5 * x) % 6 + 1 → (5 * x) % 6 = (-1 * x) % 6 := by lia

example (x : Int) : (4 * x) / 7 < (-2 * x) % 7 → (3 * x) % 7 ≠ (2 * x) % 7 → (-2 * x) % 7 < (5 * x) % 7 + -2 → (-1 * x) % 7 ≤ (5 * x) % 7 + 1 := by lia -- reuse

example (x : Int) : (5 * x) % 3 = (-1 * x) / 3 → (5 * x) % 3 < (3 * x) / 3 + 1 → (x) % 3 ≠ (-1 * x) % 3 → (4 * x) % 3 = (-2 * x) % 3 := by lia

example (x : Int) : (5 * x) / 3 = (2 * x) / 3 → (2 * x) % 3 ≠ (x) % 3 → (-2 * x) % 3 = (4 * x) % 3 := by lia

example (x : Int) : (5 * x) % 3 < (4 * x) % 3 → (4 * x) % 3 < (-2 * x) / 3 + -1 → (x) % 3 ≠ (x) / 3 → (3 * x) % 3 ≤ (-1 * x) / 3 := by lia

example (x : Int) : (5 * x) % 5 < (3 * x) % 5 → (-2 * x) % 5 ≤ (4 * x) % 5 → (-2 * x) % 5 ≠ (3 * x) % 5 → (-2 * x) / 5 ≤ (x) / 5 := by lia

example (x : Int) : (5 * x) % 5 < (5 * x) / 5 + 2 → (2 * x) % 5 ≤ (-2 * x) % 5 + 0 → (-2 * x) % 5 ≠ (3 * x) % 5 → (4 * x) % 5 = (3 * x) % 5 := by lia

example (x : Int) : (5 * x) % 6 ≠ (-1 * x) % 6 → (-2 * x) / 6 ≠ (-2 * x) % 6 + 2 → (5 * x) % 6 ≤ (-2 * x) / 6 + 0 → (2 * x) % 6 ≤ (-2 * x) / 6 := by lia

example (x : Int) : (5 * x) % 6 ≠ (2 * x) % 6 → (-1 * x) % 6 ≤ (-2 * x) / 6 → (3 * x) % 6 ≠ (3 * x) / 6 + 1 := by lia

example (x : Int) : (5 * x) % 6 < (3 * x) / 6 → (4 * x) % 6 ≤ (-2 * x) % 6 := by lia -- reuse

example (x : Int) : (5 * x) / 6 ≤ (3 * x) % 6 → (4 * x) / 6 ≤ (4 * x) % 6 → (3 * x) % 6 < (x) % 6 → (4 * x) % 6 ≤ (-2 * x) % 6 := by lia

example (x : Int) : (5 * x) % 6 < (4 * x) / 6 → (-1 * x) % 6 = (5 * x) % 6 := by lia

example (x : Int) : (5 * x) % 6 ≤ (5 * x) / 6 → (4 * x) % 6 ≤ (-2 * x) % 6 := by lia -- reuse

example (x : Int) : (5 * x) % 7 ≠ (-2 * x) / 7 + 0 → (-2 * x) % 7 ≠ (5 * x) % 7 → (2 * x) % 7 ≤ (-2 * x) % 7 := by lia

example (x : Int) : (5 * x) % 7 ≠ (-2 * x) % 7 → (2 * x) % 7 < (4 * x) / 7 → (3 * x) % 7 ≠ (2 * x) / 7 + 1 → (4 * x) / 7 ≤ (-1 * x) % 7 := by lia -- reuse

example (x : Int) : (5 * x) % 7 ≠ (-2 * x) % 7 → (3 * x) % 7 < (4 * x) % 7 → (5 * x) % 7 ≠ (2 * x) % 7 + 2 → (2 * x) % 7 < (2 * x) % 7 := by lia

example (x : Int) : (5 * x) % 7 < (-2 * x) % 7 → (5 * x) / 7 = (3 * x) / 7 → (5 * x) % 7 ≤ (x) % 7 := by lia -- reuse

example (x : Int) : (5 * x) % 7 ≤ (4 * x) % 7 + -2 → (5 * x) % 7 ≠ (-2 * x) % 7 → (3 * x) / 7 < (x) % 7 := by lia

example (x : Int) : (x) / 3 < (-2 * x) % 3 → (2 * x) % 3 ≠ (4 * x) % 3 → (-1 * x) % 3 = (5 * x) % 3 := by lia

example (x : Int) : (x) / 5 < (-1 * x) % 5 → (-2 * x) % 5 = (3 * x) % 5 := by lia

example (x : Int) : (x) % 5 ≤ (-2 * x) % 5 + -2 → (2 * x) % 5 ≠ (4 * x) / 5 → (2 * x) % 5 ≤ (-1 * x) / 5 → (x) / 5 ≤ (5 * x) % 5 + -1 := by lia

example (x : Int) : (x) / 5 < (4 * x) % 5 → (3 * x) % 5 ≠ (-2 * x) % 5 → (2 * x) / 5 < (-2 * x) % 5 → (-1 * x) % 5 < (3 * x) % 5 := by lia -- reuse

example (x : Int) : (x) % 6 ≠ (-2 * x) / 6 + -1 → (-1 * x) / 6 < (4 * x) % 6 → (3 * x) % 6 < (5 * x) % 6 → (5 * x) % 6 ≤ (-1 * x) % 6 := by lia

example (x : Int) : (x) % 6 ≠ (x) / 6 → (2 * x) % 6 < (-1 * x) % 6 → (5 * x) % 6 = (2 * x) / 6 → (5 * x) % 6 = (x) % 6 := by lia

example (x : Int) : (x) / 7 ≤ (-2 * x) / 7 → (-2 * x) % 7 ≠ (5 * x) % 7 → (-2 * x) % 7 ≤ (2 * x) % 7 + 1 → (-1 * x) / 7 = (5 * x) % 7 := by lia

example (x y : Int) : (-1 * x + 2 * y) % 5 ≤ (2 * x + 3 * y) % 5 → (-1 * x) % 5 ≠ (2 * y) % 5 → (3 * x + 3 * y) / 5 ≤ (2 * y) % 5 → (5 * y) % 5 ≤ (4 * x + 2 * y) % 5 + 1 := by lia

example (x y : Int) : (-1 * x + 3 * y) % 3 ≠ (3 * y + 1 * y) % 3 → (-2 * y + 3 * x) / 3 = (2 * y) % 3 → (y + 3 * y) % 3 < (-2 * y) % 3 + -1 → (5 * y) % 3 ≠ (-1 * x) % 3 + -1 := by lia

example (x y : Int) : (-1 * y) % 5 < (y + 1 * x) / 5 → (4 * y + 1 * x) % 5 < (2 * x + 2 * x) % 5 + -2 → (x) % 5 < (5 * x) % 5 → (-1 * y) % 5 ≠ (y) / 5 + 1 := by lia

example (x y : Int) : (2 * x) % 3 ≤ (2 * x) % 3 → (-1 * y + 3 * x) % 3 ≠ (2 * y) % 3 → (2 * y + 2 * x) % 3 ≠ (2 * y) % 3 + -2 → (x + 1 * y) % 3 ≠ (-2 * x) / 3 := by lia

example (x y : Int) : (2 * x) % 3 ≠ (4 * x) % 3 + -1 → (x) / 3 < (4 * y) % 3 → (3 * x) / 3 < (4 * x) % 3 + -1 → (-2 * y) % 3 ≤ (y) % 3 := by lia

example (x y : Int) : (-2 * x) % 3 ≠ (x + 2 * y) % 3 → (4 * x) % 3 ≠ (5 * x) % 3 → (5 * x) % 3 ≠ (-2 * y) % 3 → (y + 2 * y) % 3 ≠ (4 * y) / 3 := by lia -- reuse

example (x y : Int) : (-2 * x + 3 * x) % 6 = (3 * x) / 6 + 0 → (5 * y) % 6 < (4 * y) % 6 → (x) / 6 < (4 * x + 1 * y) % 6 → (-1 * x) % 6 ≤ (3 * x) % 6 := by lia

example (x y : Int) : (2 * x) % 5 = (2 * y) % 5 → (3 * y) % 5 ≠ (-2 * x) % 5 → (2 * y + 2 * x) / 5 < (y) % 5 := by lia -- reuse

example (x y : Int) : (2 * x) / 5 ≤ (3 * x) % 5 → (y + 2 * x) % 5 < (-2 * x) / 5 → (3 * y + 2 * x) / 5 ≠ (4 * y + 1 * y) % 5 → (-2 * x) % 5 = (3 * x) % 5 := by lia

example (x y : Int) : (-2 * x) % 5 ≤ (4 * y) % 5 → (y) % 5 ≤ (-2 * x) / 5 → (-2 * y) % 5 ≠ (3 * y) % 5 → (2 * y) / 5 = (x) % 5 := by lia

example (x y : Int) : (2 * x) % 5 ≤ (x) % 5 → (3 * y + 3 * x) % 5 ≠ (3 * y) % 5 → (4 * x) % 5 ≠ (4 * y) % 5 + 0 → (-2 * y) % 5 = (3 * y) % 5 := by lia

example (x y : Int) : (-2 * x) % 7 ≤ (3 * y) % 7 → (-2 * y + 2 * x) % 7 = (4 * x) % 7 → (5 * y) % 7 = (2 * x) % 7 := by lia -- reuse

example (x y : Int) : (-2 * y) % 3 ≠ (2 * y + 3 * x) % 3 + 0 → (-1 * x) % 3 = (-2 * x) / 3 → (x) / 3 ≤ (2 * y + 1 * x) % 3 → (3 * x) % 3 ≠ (4 * y) / 3 := by lia

example (x y : Int) : (2 * y) % 3 ≤ (5 * x) % 3 → (x + 1 * y) % 3 ≠ (3 * x) / 3 + -1 → (x + 3 * y) % 3 = (4 * x) % 3 := by lia

example (x y : Int) : (-2 * y) % 3 < (y + 2 * x) % 3 + 2 → (-2 * x) % 3 < (-1 * x) % 3 → (2 * x) % 3 ≤ (-2 * x) / 3 → (4 * y) % 3 < (3 * x + 1 * x) % 3 + 2 := by lia -- reuse

example (x y : Int) : (2 * y) % 5 < (4 * y) % 5 → (5 * y) % 5 = (3 * x) / 5 → (-2 * y) % 5 ≤ (3 * y) % 5 := by lia

example (x y : Int) : (3 * x) % 5 ≤ (y + 3 * x) / 5 → (2 * y) % 5 ≤ (2 * x) % 5 + 1 → (x) % 5 ≠ (4 * y) % 5 → (4 * y) % 5 ≠ (2 * x + 1 * y) % 5 := by lia -- reuse

example (x y : Int) : (3 * y + 1 * y) % 6 = (-1 * x) % 6 → (2 * x + 2 * x) % 6 ≠ (-2 * x) % 6 → (3 * x + 3 * y) / 6 ≠ (x + 2 * y) % 6 + 2 := by lia -- reuse

example (x y : Int) : (3 * y) / 3 < (2 * x) % 3 → (-2 * y) % 3 ≤ (2 * y + 1 * y) % 3 → (5 * y) % 3 ≠ (3 * y + 1 * y) % 3 → (-2 * y) % 3 ≠ (-1 * x + 1 * y) / 3 + 0 := by lia -- reuse

example (x y : Int) : (3 * y + 3 * y) / 5 = (5 * x) % 5 → (-2 * y + 2 * x) % 5 = (2 * x + 1 * y) % 5 := by lia -- reuse

example (x y : Int) : (3 * y) % 5 = (-2 * x) % 5 → (4 * x) % 5 ≠ (2 * x + 2 * y) % 5 → (-1 * y + 2 * y) % 5 ≤ (-2 * x) % 5 + -1 := by lia -- reuse

example (x y : Int) : (3 * y) / 7 = (-1 * y + 1 * y) % 7 → (-1 * x) % 7 = (5 * x + 3 * y) % 7 → (4 * y) % 7 < (5 * y) % 7 + 0 → (y) % 7 = (-2 * x) % 7 := by lia

example (x y : Int) : (4 * x + 1 * x) % 6 < (4 * y + 1 * y) % 6 + -2 → (4 * x) % 6 ≠ (-1 * y) % 6 → (y) % 6 = (4 * x) % 6 → (4 * y) / 6 ≠ (3 * y) % 6 := by lia

example (x y : Int) : (4 * x) % 5 < (3 * x + 3 * x) % 5 → (x) % 5 = (-1 * y) / 5 → (5 * y) % 5 = (5 * y + 3 * y) / 5 → (4 * y) % 5 < (y) / 5 := by lia

example (x y : Int) : (4 * x) / 7 ≠ (-1 * x + 3 * y) / 7 → (5 * y + 3 * x) % 7 < (4 * y) % 7 + -1 → (3 * x) / 7 < (-2 * x) / 7 → (-2 * x) % 7 = (5 * x) % 7 + 0 := by lia -- reuse

example (x y : Int) : (4 * y) % 3 ≠ (x + 1 * x) % 3 → (3 * x) / 3 ≤ (3 * y) % 3 → (-2 * y) % 3 ≤ (3 * x) / 3 → (y) % 3 ≤ (x + 2 * y) % 3 := by lia -- reuse

example (x y : Int) : (4 * y) % 5 < (3 * y + 3 * y) % 5 → (4 * x + 1 * x) % 5 ≤ (3 * y) % 5 := by lia

example (x y : Int) : (5 * x + 1 * y) / 3 ≠ (2 * y) % 3 → (2 * y) % 3 ≤ (2 * x) % 3 → (3 * y) % 3 ≤ (-2 * x + 1 * y) % 3 := by lia

example (x y : Int) : (5 * x + 2 * y) % 5 ≠ (4 * y + 3 * y) % 5 → (3 * x) % 5 = (-2 * x) % 5 + -1 := by lia -- reuse

example (x y : Int) : (5 * x) % 3 < (5 * y) % 3 → (3 * x + 3 * y) % 3 ≤ (4 * y + 1 * x) % 3 := by lia

example (x y : Int) : (5 * x) / 7 ≠ (2 * y) % 7 → (4 * x + 3 * y) % 7 = (-2 * x + 3 * x) / 7 + -1 → (3 * y) % 7 = (2 * x + 2 * x) % 7 → (4 * y) % 7 = (3 * x) % 7 := by lia -- reuse

example (x y : Int) : (5 * y + 2 * x) % 3 ≠ (y) % 3 → (-2 * x + 2 * y) / 3 ≤ (5 * x) % 3 + 0 → (-2 * x) % 3 = (3 * y) % 3 → (4 * y) % 3 = (y) % 3 := by lia

example (x y : Int) : (5 * y) % 7 ≠ (-2 * y) % 7 → (-1 * x) % 7 ≠ (4 * x) / 7 + -1 → (3 * x + 2 * y) % 7 < (5 * y) % 7 → (x) / 7 < (x) % 7 := by lia

example (x y : Int) : (x + 2 * y) % 6 ≤ (5 * y) % 6 → (x) % 6 < (y + 3 * y) % 6 → (3 * x) % 6 ≠ (-1 * y + 3 * x) / 6 → (2 * x) % 6 ≤ (-1 * x) % 6 := by lia

example (x y : Int) : (y + 1 * x) % 5 < (5 * x) % 5 + -1 → (2 * x) % 5 < (4 * x) % 5 + -2 → (5 * y) % 5 < (3 * x) % 5 + 2 := by lia

example (x y : Int) : (y + 3 * x) % 6 = (y + 3 * y) / 6 + 1 → (3 * x) / 6 ≠ (-1 * x + 1 * y) % 6 + 0 → (3 * y) % 6 < (y) / 6 → (-2 * x) % 6 ≤ (-1 * y) % 6 := by lia

example (x y : Int) : (y) / 7 < (-1 * x) / 7 → (2 * x) % 7 = (3 * y) % 7 → (5 * x) % 7 ≤ (-2 * x) % 7 := by lia

example (x y z : Int) : 3 * x + 2 * y ≤ (-2 * z + 2 * y) / 6 + (4 * z + -1 * x) % 4 + -3 → (3 * z) / 2 = (-3 * z) % 3 + (3 * z + 3 * y) / 2 + -1 → 2 * y ≤ (3 * x + 4 * z) % 2 + 0 → 4 * x + (-3 * z) / 3 ≤ -3 * y + (2 * y) / 2 + 1 := by lia

example (x y z : Int) : (-3 * y + 4 * x) % 6 ≤ (-1 * y + -3 * z) % 4 + (3 * z) / 5 + -3 → (4 * z + x) % 2 ≤ (3 * z) % 6 + 0 → (2 * z + 2 * y) % 6 + (3 * y) % 5 ≠ -2 * z + (z) % 5 + -3 := by lia -- reuse

example (x y z : Int) : (-3 * z + 3 * x) / 6 ≠ (-3 * y + 2 * z) / 3 + 2 * z + -3 → 3 * z ≤ (-1 * x + -2 * z) % 3 + (3 * y) % 3 + -2 → 5 * z ≤ (y) % 3 + (-2 * x) % 6 + -3 := by lia
