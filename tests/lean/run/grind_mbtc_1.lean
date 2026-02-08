module
example (f : Int → Int) (x : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
  grind


-- In the following example, model-based theory combination is disabled,
-- and we have an invalid counterexample where `x := 1`,
-- but `f x` and `f 1` have different assignments.
/--
trace: [grind.lia.model] x := 1
[grind.lia.model] f x := 2
[grind.lia.model] f 1 := 5
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (f : Int → Int) (x : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
  fail_if_success grind -mbtc
  sorry

/--
trace: [grind.lia.model] x := 2
[grind.lia.model] f x := 2
[grind.lia.model] f 1 := 5
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (f : Int → Int) (x : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 3 → f x = 2 → f 1 = 2 := by
  fail_if_success grind
  sorry

example (f : Int → Int → Int) (x y : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x y = 2 → f 1 y = 2 := by
  grind

example (f : Nat → Nat) (x : Nat)
    : x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
  grind

example (f : Nat → Nat → Nat) (x y : Nat)
    : x ≠ 0 → x ≤ 1 → f x y = 2 → f 1 y = 2 := by
  grind


-- `b` must not be `2`. Otherwise, `f (b+1)` and `f 3` must be equal.
/--
trace: [grind.lia.model] a := 5
[grind.lia.model] b := 3
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (f : Int → α) (a b : Int) : b > 1 → f (b + 1) = x → f 3 = y → x = y := by
  (fail_if_success grind); sorry

-- `b` must not be `2`. Otherwise, `f (b+1)` and `f 3` must be equal.
/--
trace: [grind.lia.model] x := 5
[grind.lia.model] y := 6
[grind.lia.model] a := 7
[grind.lia.model] b := 3
[grind.lia.model] f 3 := 6
[grind.lia.model] f (b + 1) := 5
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (f : Int → Int) (a b : Int) : b > 1 → f (b + 1) = x → f 3 = y → x = y := by
  (fail_if_success grind); sorry
