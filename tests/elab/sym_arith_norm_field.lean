/-!
# Tests for the `arith` simproc on fields

Division is eliminated (`a / b ↦ a * b⁻¹`) and inverses are pushed to the atoms
(`(a * b)⁻¹ ↦ a⁻¹ * b⁻¹`, `(-a)⁻¹ ↦ -a⁻¹`, `a⁻¹⁻¹ ↦ a`, `0⁻¹ ↦ 0`, `1⁻¹ ↦ 1`); `x⁻¹` for an
atom or a numeral `x` is then an atom of the polynomial. Two known gaps, marked `TODO` below:
`x * x⁻¹` is not simplified (side condition), and numeral inverses are not rational
coefficients yet, so `a / 2 + a / 2` does not reach its normal form `a`.
-/

set_option warn.sorry false

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b : Rat) : a / b + a / b = 2 * (a * b⁻¹) := by
  sym => simp arithSimp

example (a b : Rat) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  sym => simp arithSimp

example (a : Rat) : (-a)⁻¹ + a⁻¹ = 0 := by
  sym => simp arithSimp

example (a : Rat) : a⁻¹⁻¹ = a := by
  sym => simp arithSimp

example (a : Rat) : a / 1 = a := by
  sym => simp arithSimp

example (a : Rat) : a / 0 = 0 := by
  sym => simp arithSimp

example (a b c : Rat) : (a + b) / c = a * c⁻¹ + b * c⁻¹ := by
  sym => simp arithSimp

example (a b : Rat) : (a * b + b * a)⁻¹ = (2 * (a * b))⁻¹ := by
  sym => simp arithSimp

-- Nested: the inner term is normalized before the inverse rewrites apply.
example (a b : Rat) : (a * (b + 0))⁻¹ = a⁻¹ * b⁻¹ := by
  sym => simp arithSimp

-- Relations.
example (a b : Rat) (h : a * b⁻¹ = 1) : a / b = 1 := by
  sym =>
    simp arithSimp
    exact h

-- **TODO**: `x * x⁻¹` needs the side condition `x ≠ 0`, to be discharged by the simplifier's
-- discharger; not supported yet.
/--
trace: case grind
a : Rat
⊢ a * a⁻¹ = 1
-/
#guard_msgs in
example (a : Rat) : a / a = 1 := by
  sym =>
    simp arithSimp
    show_goals
    sorry

-- **TODO**: numeral inverses must become rational coefficients (`a / 2 + a / 2` is `a`);
-- `2⁻¹` is an atom for now, so `2 * 2⁻¹` does not cancel. This is not a normal form.
/--
trace: case grind
a : Rat
⊢ 2 * (a * 2⁻¹) = a
-/
#guard_msgs in
example (a : Rat) : a / 2 + a / 2 = a := by
  sym =>
    simp arithSimp
    show_goals
    sorry

-- A field given by a local instance.
open Lean.Grind in
example (F : Type) [Field F] (a b : F) : a / b + a / b = 2 * (a * b⁻¹) := by
  sym => simp arithSimp

-- Division on a ring that is not a field is an atom.
example (x y : Int) : x / y + 0 = x / y := by
  sym => simp arithSimp
