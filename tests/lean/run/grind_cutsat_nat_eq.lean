set_option grind.warning false

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

example (x : Int) (h : x = 7) : x.natAbs = 7 := by
  grind

example (x y : Int) (_ : (x - y).natAbs < 3) (_ : x < 5) (_ : y > 15) : False := by
  grind

example (z : Int) : z.toNat = 0 ↔ z ≤ 0 := by
  grind

example (a b : Int) : (a - b).toNat = 0 ↔ a ≤ b := by
  grind

/--
info: [grind.cutsat.model] x := 3
[grind.cutsat.model] y := 1
[grind.cutsat.model] z := 4
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (x y z : Nat) : x ≥ 3 → x ≠ z → x > y → z ≤ 6 → x + y = z → False := by
  fail_if_success grind
  sorry

/--
info: [grind.cutsat.model] x := 13
[grind.cutsat.model] y := 9
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
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
info: [grind.cutsat.model] x := 4
[grind.cutsat.model] y := 1
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (x y : Nat) : x = y + 3 → y > 0 → False := by
  fail_if_success grind
  sorry
