/-!
Tests for `Grind.Config.distrib` in the `Sym.simp`-based `grind` normalizer. With the default
`distrib := false`, a product of non-constant polynomials is an atom whose factors are normalized,
as in the legacy normalizer; with `+distrib` the normalizer expands it.
-/

set_option warn.sorry false

-- Both normalizers agree: these products are atoms.
#guard_msgs in
example (a b c : Int) (f : Int → Nat) : f ((a - b) * c) = 0 := by grind_norm check; sorry

#guard_msgs in
example (a b : Nat) (f : Nat → Nat) : f ((a - 1 + 1) * b) = 0 := by grind_norm check; sorry

#guard_msgs in
example (x1 x5 : Int) (f : Int → Nat) : f (x1 * (x5 + 1 + 0)) = 0 := by grind_norm check; sorry

-- A constant factor distributes, monomials multiply, and the factors of a kept product are
-- normalized (`x * (1 + y)` becomes `x * (y + 1)`).
/--
trace: x y : Int
f : Int → Nat
⊢ f (2 * (x * y ^ 2) + 2 * x + 2 * y + 3 * (x * (y + 1))) = 0
-/
#guard_msgs in
example (x y : Int) (f : Int → Nat) : f (2 * (x + y) + x * (1 + y) * 3 + (x * y) * (2 * y)) = 0 := by
  grind_norm sym; trace_state; sorry

-- A power of a sum is an atom.
/--
trace: x : Int
f : Int → Nat
⊢ f ((x + 1) ^ 2) = 0
-/
#guard_msgs in
example (x : Int) (f : Int → Nat) : f ((x + 1) ^ 2) = 0 := by grind_norm sym; trace_state; sorry

-- The inverse of a product is an atom, a numeral inverse is a scalar.
/--
trace: a : Rat
f : Rat → Nat
⊢ f (a⁻¹ + (2 * a)⁻¹) = 0
-/
#guard_msgs in
example (a : Rat) (f : Rat → Nat) : f (1 / a + 1 / (2 * a)) = 0 := by grind_norm sym; trace_state; sorry

#guard_msgs in
example (a b : Rat) : (a + b) / 4 = a / 4 + b / 4 := by grind_norm sym; trivial

-- With `+distrib`, the product is expanded.
/--
trace: x y : Int
f : Int → Nat
⊢ f (x * y + x) = 0
-/
#guard_msgs in
example (x y : Int) (f : Int → Nat) : f (x * (y + 1)) = 0 := by grind_norm +distrib sym; trace_state; sorry

-- The atoms are what cutsat and model-based theory combination see.
set_option backward.grind.normalizer false

example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by grind

example (x y z : Int) (h : y + 1 = z) : x * (y + 1) = x * z := by grind
