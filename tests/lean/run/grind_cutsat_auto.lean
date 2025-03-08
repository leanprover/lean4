set_option grind.warning false

example : ∀ x : Int, x > 7 → 2 * x > 14 := by
  grind

example : ∀ x : Int, 4 * x = 6 → 2 * x = 3 → False := by
  grind

example (x y z : Int) (h : 2 * x + 3 * y - 4 * z = 11) :
    2 * x ≥ 11 - 3 * y + 4 * z := by
  grind

theorem ex (x y z : Int) :
    (15*x + 7*y - 11*z = 10) ∧
    (8*x + 2*y -  6*z =  4) ∧
    (6*x + 6*y - 11*z =  9) ∧
    (9*x + 3*y = 15) ∧
    (9*x + 3*y = 16)
    → False := by
  grind

abbrev problem (x y z w v : Int) : Prop :=
  (x + 2*y + 3*z - w + v = 0) ∧
  (2*x - y + 7*z + 2*w = 14) ∧
  (v - 4*w ≥ 1) ∧
  (w ≥ 0) ∧
  (z ≤ 4) ∧
  (x ≥ -10) ∧
  (y ≤ 10) ∧
  (y ≥ -10)

/--
info: [grind.cutsat.model] x := 121
[grind.cutsat.model] y := -10
[grind.cutsat.model] z := -34
[grind.cutsat.model] w := 0
[grind.cutsat.model] v := 1
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (x y z w v : Int) : problem x y z w v → False := by
  fail_if_success grind
  sorry

/-- info: true -/
#guard_msgs in
#eval decide (problem 121 (-10) (-34) 0 1)

example (x y : Int) : 4*x + 6*y = 9 → 5*x - 2*y = 1 → False := by
  grind

example (x y z : Int) :
    7*x + 2*y +  3*z = 25 → 2*x - 8*y + 11*z = 14 →
    9*x + 4*y - 10*z = -1 → False := by
  grind

example (x y z : Int) :
    x + y + z = 6 → 2*x + 4*y - z = 7 →
    x ≥ 3 → x ≤ 4 → 10*y ≥ 6 →
    10*y ≤ 10 → z ≥ 2 → z ≤ 3 → False := by
  grind

example (p r : Int) :
     2*(p - r) = 1 → False := by
  grind

example (p q : Int) :
    6*p + 9*q = 15 → 4*p - 3*q ≤ 1 →
    5*p + 2*q ≥ 8 → p ≥ 0 → q ≤ 6 → False := by
  grind

example (x y : Int) :
    6*x + 9*y = 12 → 4*x - 2*y ≥ 1 →
    5*x + 10*y ≤ 7 → x ≥ 0 → x ≤ 4 →
    8*x - 5*y ≥ -3 → False := by
 grind

-- TODO: improve kernel reduction and remove `skipKernelTC`
set_option debug.skipKernelTC true in
example (x y z : Int) :
    2 ≤ 12*x +  5*y +  7*z → 12*x +  5*y +  7*z ≤  5 →
    -5 ≤  3*x - 11*y +  2*z →  3*x - 11*y +  2*z ≤ -1 →
    10 ≤  8*x +  9*y -  4*z →  8*x +  9*y -  4*z ≤ 12 → False := by
  grind
