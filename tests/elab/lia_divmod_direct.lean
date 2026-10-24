/-!
Goals that need the linear facts cutsat derives for `a / k` and `a % k`. `lia` asserts them directly
into cutsat, while `grind` adds them to the E-graph. The kernel checks the proofs on both paths.
-/

example (x : Int) : x % 3 < 3 := by lia
example (x : Int) : 0 ≤ x % 5 := by lia
example (x : Int) : x % (-3) < 3 := by lia
example (x : Int) (h : x % 4 = 5) : False := by lia
example (x y : Int) (h : x / 2 = y) : 2 * y ≤ x := by lia
example (x : Int) : x = 7 * (x / 7) + x % 7 := by lia
example (x : Nat) : x % 3 < 3 := by lia

example (x : Int) : x % 3 < 3 := by grind
example (x y : Int) (h : x / 2 = y) : 2 * y ≤ x := by grind
example (x : Int) : x = 7 * (x / 7) + x % 7 := by grind

/-! In `lia`, only the negated goal enters the E-graph. -/

/-- trace: [grind.assert] -1 * (x % 3) + 3 ≤ 0 -/
#guard_msgs (trace) in
set_option trace.grind.assert true in
example (x : Int) : x % 3 < 3 := by lia

/-! `grind` adds the facts to the E-graph, even when cutsat is its only arithmetic solver. -/

/--
trace: [grind.assert] -1 * (x % 3) + 3 ≤ 0
[grind.assert] x % 3 + -2 ≤ 0
[grind.assert] -1 * (x % 3) ≤ 0
[grind.assert] -1 * x + 3 * (x / 3) + x % 3 = 0
-/
#guard_msgs (trace) in
set_option trace.grind.assert true in
example (x : Int) : x % 3 < 3 := by grind -ring -linarith -ac -order
