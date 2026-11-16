/-!
Certificates by Kronecker substitution for fields in `Sym.simp`'s arithmetic normalizer: terms and
identities with inverses of numerals are checked by evaluating both sides at one point, with the
inverses of the numerals as rational constants (`Grind.CommRing.Expr.eq_of_kronQ`,
`Grind.CommRing.eq_true_of_kronQ`). Identities whose sides have the same polynomial, with the
inverses as atoms, are ring identities (`Grind.CommRing.eq_true_of_kron`). Relations are cleared of
denominators: `(lhs - rhs) * d` and `lhs' - rhs'` are compared at the point
(`Grind.CommRing.le_of_kronQ_rel` and its variants). Linear terms over many variables use the point
`xᵢ = (2 ^ K) ^ (i + 1)` (`Grind.CommRing.Expr.eq_of_kronQLin`). Each proof is checked by the kernel.
-/

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (x y : Rat) : (x/2 + y/3)^4 = (3*x + 2*y)^4 / 1296 := by sym => simp arithSimp
example (x y z : Rat) : (x/2 - y/5 + z)^3 * 1000 = (5*x - 2*y + 10*z)^3 := by sym => simp arithSimp
example (a b : Rat) : a/6 + b/4 - (2*a + 3*b)/12 = 0 := by sym => simp arithSimp
example (a b : Rat) : (a + b)^2/2 - (a - b)^2/2 = 2*a*b := by sym => simp arithSimp
example (a b c : Rat) : ((a + b/7 - c/3)^5 * 21^5 - (21*a + 3*b - 7*c)^5) / 11 = 0 := by sym => simp arithSimp
-- The sides have the same polynomial, with the inverses as atoms.
example (a b c : Rat) : (a + b / 4) * (c - 2) = a * c - 2 * a + b * c / 4 - 2 * b / 4 := by sym => simp arithSimp
example (a b c : Rat) : (a / 3 + b / 4 - c)^6 = (c - b / 4 - a / 3)^2 * (b / 4 - c + a / 3)^4 := by sym => simp arithSimp
-- Inverses of atoms use the normalizer.
example (a b : Rat) : a⁻¹ * 2 + a⁻¹ * b / 3 = a⁻¹ * (6 + b) / 3 := by sym => simp arithSimp

-- Relations are cleared of denominators.
example (x y z : Rat) : (x / 2 + y / 3 ≤ z / 6) = (3 * x + 2 * y ≤ z) := by sym => simp arithSimp
example (x y z : Rat) : (x / 2 + y / 3 < z / 6 + x / 4) = (3 * x + 4 * y < 2 * z) := by sym => simp arithSimp
example (x y : Rat) : ((x / 3 + y / 5)^2 ≤ (x / 3 - y / 5)^2) = (4 * (x * y) ≤ 0) := by sym => simp arithSimp
example (x y : Rat) : (x / 2 = y / 3) = (3 * x = 2 * y) := by sym => simp arithSimp
/--
error: `sym` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : Rat) : (x/2 + y/3)^2 = (3*x + 2*y)^2 / 35 := by sym => simp arithSimp

-- Linear terms over many variables: the point `xᵢ = (2 ^ K) ^ (i + 1)` (`Grind.CommRing.Expr.eq_of_kronQLin`).
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Rat) : x0 / 2 + x1 / 3 + x2 / 4 + x3 / 5 + x4 / 6 + x5 / 2 + x6 / 3 + x7 / 4 + x8 / 5 + x9 / 6 + x10 / 2 + x11 / 3 + x12 / 4 + x13 / 5 + x14 / 6 + x15 / 2 + x16 / 3 + x17 / 4 + x18 / 5 + x19 / 6 + x20 / 2 + x21 / 3 + x22 / 4 + x23 / 5 + x24 / 6 + x25 / 2 + x26 / 3 + x27 / 4 + x28 / 5 + x29 / 6 + x30 / 2 + x31 / 3 + x32 / 4 + x33 / 5 + x34 / 6 + x35 / 2 + x36 / 3 + x37 / 4 + x38 / 5 + x39 / 6 = (x0 + x5 + x10 + x15 + x20 + x25 + x30 + x35) / 2 + (x1 + x6 + x11 + x16 + x21 + x26 + x31 + x36) / 3 + (x2 + x7 + x12 + x17 + x22 + x27 + x32 + x37) / 4 + (x3 + x8 + x13 + x18 + x23 + x28 + x33 + x38) / 5 + (x4 + x9 + x14 + x19 + x24 + x29 + x34 + x39) / 6 := by sym => simp arithSimp
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Rat) : x0 / 2 + x1 / 3 + x2 / 4 + x3 / 5 + x4 / 6 + x5 / 2 + x6 / 3 + x7 / 4 + x8 / 5 + x9 / 6 + x10 / 2 + x11 / 3 + x12 / 4 + x13 / 5 + x14 / 6 + x15 / 2 + x16 / 3 + x17 / 4 + x18 / 5 + x19 / 6 + x20 / 2 + x21 / 3 + x22 / 4 + x23 / 5 + x24 / 6 + x25 / 2 + x26 / 3 + x27 / 4 + x28 / 5 + x29 / 6 + x30 / 2 + x31 / 3 + x32 / 4 + x33 / 5 + x34 / 6 + x35 / 2 + x36 / 3 + x37 / 4 + x38 / 5 + x39 / 6 + 1 / 3 ≤ x39 / 6 + x38 / 5 + x37 / 4 + x36 / 3 + x35 / 2 + x34 / 6 + x33 / 5 + x32 / 4 + x31 / 3 + x30 / 2 + x29 / 6 + x28 / 5 + x27 / 4 + x26 / 3 + x25 / 2 + x24 / 6 + x23 / 5 + x22 / 4 + x21 / 3 + x20 / 2 + x19 / 6 + x18 / 5 + x17 / 4 + x16 / 3 + x15 / 2 + x14 / 6 + x13 / 5 + x12 / 4 + x11 / 3 + x10 / 2 + x9 / 6 + x8 / 5 + x7 / 4 + x6 / 3 + x5 / 2 + x4 / 6 + x3 / 5 + x2 / 4 + x1 / 3 + x0 / 2 + 1 / 2 := by sym => simp arithSimp
example (f : Rat → Rat) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Rat) : f (x0 / 2 + x1 / 3 + x2 / 4 + x3 / 5 + x4 / 6 + x5 / 2 + x6 / 3 + x7 / 4 + x8 / 5 + x9 / 6 + x10 / 2 + x11 / 3 + x12 / 4 + x13 / 5 + x14 / 6 + x15 / 2 + x16 / 3 + x17 / 4 + x18 / 5 + x19 / 6 + x20 / 2 + x21 / 3 + x22 / 4 + x23 / 5 + x24 / 6 + x25 / 2 + x26 / 3 + x27 / 4 + x28 / 5 + x29 / 6 + x30 / 2 + x31 / 3 + x32 / 4 + x33 / 5 + x34 / 6 + x35 / 2 + x36 / 3 + x37 / 4 + x38 / 5 + x39 / 6) = f ((x0 + x5 + x10 + x15 + x20 + x25 + x30 + x35) / 2 + (x1 + x6 + x11 + x16 + x21 + x26 + x31 + x36) / 3 + (x2 + x7 + x12 + x17 + x22 + x27 + x32 + x37) / 4 + (x3 + x8 + x13 + x18 + x23 + x28 + x33 + x38) / 5 + (x4 + x9 + x14 + x19 + x24 + x29 + x34 + x39) / 6) := by sym => simp arithSimp
