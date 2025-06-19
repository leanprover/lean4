open Lean.Grind

variable (R : Type u) [IntModule R] [NoNatZeroDivisors R] [Preorder R] [IntModule.IsOrdered R]

example (a b c : R) (h : a < b) : a + c < b + c := by grind
example (a b c : R) (h : a < b) : c + a < c + b := by grind
example (a b : R) (h : a < b) : -b < -a := by grind
example (a b : R) (h : a < b) : -a < -b := by grind

example (a b c : R) (h : a ≤ b) : a + c ≤ b + c := by grind
example (a b c : R) (h : a ≤ b) : c + a ≤ c + b := by grind
example (a b : R) (h : a ≤ b) : -b ≤ -a := by grind
example (a b : R) (h : a ≤ b) : -a ≤ -b := by grind

example (a : R) (h : 0 < a) : 0 ≤ a := by grind
example (a : R) (h : 0 < a) : -2 * a < 0 := by grind

example (a b c : R) (_ : a ≤ b) (_ : b ≤ c) : a ≤ c := by grind
example (a b c : R) (_ : a ≤ b) (_ : b < c) : a < c := by grind
example (a b c : R) (_ : a < b) (_ : b ≤ c) : a < c := by grind
example (a b c : R) (_ : a < b) (_ : b < c) : a < c := by grind

example (a : R) (h : 2 * a < 0) : a < 0 := by grind
example (a : R) (h : 2 * a < 0) : 0 ≤ -a := by grind

example (a b c e v0 v1 : R) (h1 : v0 = 5 * a) (h2 : v1 = 3 * b) (h3 : v0 + v1 + c = 10 * e) :
    v0 + 5 * e + (v1 - 3 * e) + (c - 2 * e) = 10 * e := by
  grind

example (x y z : R) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  grind

example (x y z : R) (hx : ¬ x > 3 * y) (h2 : ¬ y > 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  grind

example (x y z : R) (hx : x ≤ 3 * y) (h2 : y ≤ 2 * z) (h3 : x ≥ 6 * z) : x = 3 * y := by
  grind
