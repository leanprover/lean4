set_option grind.warning false

example (f : Int → Int) (x : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
  grind


-- In the following example, model-based theory combination is disabled,
-- and we have an invalid counterexample where `x := 1`,
-- but `f x` and `f 1` have different assignments.
/--
info: [grind.cutsat.model] x := 1
[grind.cutsat.model] 「f x」 := 2
[grind.cutsat.model] 「f 1」 := 5
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (f : Int → Int) (x : Int)
    : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
  fail_if_success grind -mbtc
  sorry

/--
info: [grind.cutsat.model] x := 2
[grind.cutsat.model] 「f x」 := 2
[grind.cutsat.model] 「f 1」 := 5
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
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
