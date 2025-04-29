set_option grind.warning false

example (w x y z : Int) :
  2*w + 3*x - 4*y + z = 10 →
  w - x + 2*y - 3*z = 5 →
  3*w - 2*x + y + z = 7 →
  4*w + x - y - z = 3 →
  w = 2 := by
grind

abbrev test1 (a b c d e : Int) :=
  1337*a + 424242*b - 23*c + 17*d - 101*e ≤ 12345 →
  42*a - 18*b + 23*c - 107*d + 53*e ≥ -10000 →
  a ≥ 0 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0 →
  a ≤ 100

/--
info: [grind.cutsat.model] a := 101
[grind.cutsat.model] b := 0
[grind.cutsat.model] c := 5335
[grind.cutsat.model] d := 0
[grind.cutsat.model] e := 0
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (a b c d e : Int) : test1 a b c d e  := by
  (fail_if_success grind); sorry

/-- info: false -/
#guard_msgs (info) in
#eval test1 101 0 5335 0 0

example : ∀ (x y z : Int),
    2*x + 3*y ≤ 100 →
    3*y + 4*z ≤ 200 →
    4*z + 2*x ≤ 300 →
    x ≥ 0 → y ≥ 0 → z ≥ 0 →
    x + y + z ≤ 150 := by
  grind

example : ∀ (x y : Int),
    x > 0 →
    y > 0 →
    x ≤ 100 →
    2 ∣ x →
    y ≤ 100 →
    2*x + 3*y = 47 →
    x = 22 ∨ x = 16 ∨ x = 10 ∨ x = 4 := by
  grind

example : ∀ (x y : Int),
    x + y ≤ 10 →
    2*x + y ≥ 19 →
    3*x - y ≤ 30 →
    x - 2*y ≥ -15 →
    x = 9 ∨ x = 10 := by
  grind

example : ∀ (x y z : Int),
  ¬(2*x + 3*y + 4*z ≤ 100 ∧
    3*x + 4*y + 5*z ≥ 101 ∧
    x + y + z = 50 ∧ x ≠ 50 ∧
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0) := by
  grind

example : ∀ (x y : Int),
    2*x + 3*y = 100 →
    x + y = 40 → x = y := by
  grind

example : ∀ (x y z : Int),
    3 * x + 5 * y + 7 * z = 100 →
    2 * x + 3 * y + 4 * z ≥ 50 →
    x + y + z ≤ 30 →
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 →
    z ≤ 15 := by
  grind

example : ∀ (x y z : Int),
    2 * x + 3 * y + 4 * z = 100 →
    3 * x + 4 * y + 5 * z ≥ 150 →
    x + y + z ≤ 40 →
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 →
    z ≥ 10 := by
  grind

example : ∀ (x y z : Int),
    x / 4 + y / 3 = 50 →
    x % 4 = 1 →
    y % 3 = 2 →
    x + y + z = 200 →
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 →
    z ≤ 50 := by
  grind

example : ∀ (x : Int),
    x ≥ 0 →
    x % 2 = 1 →
    x % 3 = 2 →
    x % 5 = 3 →
    x ≥ 23 := by
  grind

example : ∀ (x : Int),
    x / 5 ≥ 20 →
    x % 5 = 3 →
    x ≥ 103 := by
  grind

example : ∀ (x y z : Int),
    z > 0 →
    x + y + z = 100 →
    y = 2 * x →
    x ≤ 33 := by
  grind

example : ∀ (x y : Int),
    2 * x + 3 * y ≤ 10 →
    x + y ≤ 5 →
    x ≥ 0 → y ≥ 0 →
    x + y ≤ 5 := by
  grind

example  (x : Int) : x / 1 = x := by grind
example (x : Int) : x % 1 = 0 := by grind
example  (x : Nat) : x / 1 = x := by grind
example (x : Nat) : x % 1 = 0 := by grind
example  (x : Int) : x / -1 = -x := by grind
example (x : Int) : x % -1 = 0 := by grind
