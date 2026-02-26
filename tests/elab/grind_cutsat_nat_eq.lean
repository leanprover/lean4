module
example (a b c : Nat) : a = 0 → b = 0 → c ≥ a + b := by
  grind

example (a b c : Nat) : a + b = 0 → a ≤ b + c + a → a ≤ c := by
  grind

example (a b : Nat) (_ : 2*a + 3*b = 0) (_ : 2 ∣ 3*b + 1) : False := by
  grind

example (a b c : Nat) : a + 2*b = 0 → b + c + b = 0 → a = c := by
  grind

example (a : Nat) : a ≤ 2 → a ≠ 0 → a ≠ 1 → a ≠ 2 → False := by
  grind

example (x y : Nat) : x / 2 + y = 3 → x = 5 → y = 1 := by
  grind

example (x y : Nat) : x % 2 + y = 3 → x = 5 → y = 2 := by
  grind

example (x y : Nat) : x = y / 2 → y % 2 = 0 → y = 2*x := by
  grind

example (x : Nat) : x - 0 = x := by
  grind

example (x : Nat) : x - x = 0 := by
  grind

example (x y : Nat) : x ≤ y → x - y = 0 := by
  grind

example (x y z : Nat) : x ≤ y → x - z ≤ y - z := by
  grind

example (x y : Nat) : (x + y) - y = x := by
  grind

example (x y z : Nat) : (x + y) - (y + z) = x - z := by
  grind

example (x y : Nat) : x + y - x = y := by
  grind

example (x y : Nat) : (x - y) - y = x - 2*y := by
  grind

example (x : Nat) : x / 0 = 0 := by
  grind

example (x : Nat) : x % 0 = x := by
  grind

example (x : Nat) : x % 4 - x % 8 = 0 := by
  grind

example (x : Int) : x.natAbs ≥ 0 := by
  grind

example (x : Int) : x > 0 → x.natAbs = x := by
  grind

example (x : Int) (h : x = 7) : x.natAbs = 7 := by
  grind

example (x y : Int) (_ : (x - y).natAbs < 3) (_ : x < 5) (_ : y > 15) : False := by
  grind

example (z : Int) : z.toNat = 0 ↔ z ≤ 0 := by
  grind

example (a b : Int) : (a - b).toNat = 0 ↔ a ≤ b := by
  grind

/--
trace: [grind.lia.model] x := 3
[grind.lia.model] y := 1
[grind.lia.model] z := 4
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (x y z : Nat) : x ≥ 3 → x ≠ z → x > y → z ≤ 6 → x + y = z → False := by
  fail_if_success grind
  sorry

/--
trace: [grind.lia.model] x := 13
[grind.lia.model] y := 9
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (x y : Nat) : x > 8 → y > 8 → x ≠ y → (x - y) % 4 = 1 := by
  fail_if_success grind
  sorry

-- The following example can be solved with a single case-split if Nat.sub_sub is a preprocessing rule.
-- The generated proof is also much smaller.
example (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    : x1 - x2 - x3 - x4 - x5 - x6 - x7 - x8 - x9 - x10 = 0 →
      x1 ≤ x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 := by
  grind (splits := 1)

example (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat)
    : x1 - x2 - x3 - x4 - x5 - x6 - x7 - x8 - x9 - x10 = 0 →
      x1 ≤ x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 := by
  grind

example (x y : Int) : x ^ 1 - y = 0 → y = x := by
  grind

example (x y : Nat) : x ^ 1 - y = 0 → y ≤ x → y = x := by
  grind

example (x y : Int) : x ^ 0 - y = 0 → y = 1 := by
  grind

example (x y : Nat) : x ^ 0 + y = 0 → False := by
  grind

/--
trace: [grind.lia.model] x := 4
[grind.lia.model] y := 1
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (x y : Nat) : x = y + 3 → y > 0 → False := by
  fail_if_success grind
  sorry

example (a b : Nat) : a  = a + b - b := by
  grind

example (a b : Nat) : a = a + b - b := by
  grind -ring -linarith

example (a b : Int) : a = a + b - b := by
  grind

example (a b : Nat) : a = a + 2^b - 2^b := by
  grind

example (a b : Nat) : 2^a = 2^a + b - b := by
  grind

example (a b c : Nat) : c^a = c^a + b - b := by
  grind

example (n : Nat) : 0 ≤ 2 ^ n := by
  grind

example (f : Nat → α) (a b : Nat) : a ≤ b + 1 → a > b → f a = f (b + 1) := by
  grind
