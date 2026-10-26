/-!
Certificates by Kronecker substitution for fields in `Sym.simp`'s arithmetic normalizer: terms and
identities with inverses of numerals are checked by evaluating both sides at one point, with the
inverses of the numerals as rational constants (`Grind.CommRing.Expr.eq_of_kronQ`,
`Grind.CommRing.eq_true_of_kronQ`). Identities whose sides have the same polynomial, with the
inverses as atoms, are ring identities (`Grind.CommRing.eq_true_of_kron`). Relations are cleared of
denominators: `(lhs - rhs) * d` and `lhs' - rhs'` are compared at the point
(`Grind.CommRing.le_of_kronQ_rel` and its variants). Each proof is checked by the kernel.
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
error: `sym` failed
case grind
x y : Rat
⊢ 0 = 9 * x ^ 2 + 12 * (x * y) + 4 * y ^ 2
use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : Rat) : (x/2 + y/3)^2 = (3*x + 2*y)^2 / 35 := by sym => simp arithSimp
