/-!
# Tests for the `arith` simproc on fields

Division is eliminated (`a / b ↦ a * b⁻¹`) and inverses are pushed to the atoms
(`(a * b)⁻¹ ↦ a⁻¹ * b⁻¹`, `(-a)⁻¹ ↦ -a⁻¹`, `a⁻¹⁻¹ ↦ a`, `0⁻¹ ↦ 0`, `1⁻¹ ↦ 1`); `x⁻¹` for an
atom `x` is then an atom of the polynomial. In characteristic zero, numeral inverses are
rational coefficients: a term normalizes to `p * d⁻¹` in lowest terms (`a / 2 + b / 3` is
`(3 * a + 2 * b) * 6⁻¹`) and a relation becomes denominator-free (`a / 2 = b / 3` is
`3 * a = 2 * b`). One known gap, marked `TODO` below: `x * x⁻¹` is not simplified (side
condition).
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

-- Numeral inverses are rational coefficients.
example (a : Rat) : a / 2 + a / 2 = a := by
  sym => simp arithSimp

example (a b : Rat) : a / 2 + b / 3 = (3 * a + 2 * b) * 6⁻¹ := by
  sym => simp arithSimp

example (a b : Rat) : a / 2 + b / 3 = (3 * a + 2 * b) / 6 := by
  sym => simp arithSimp

example (a : Rat) : a / 2 * 2 = a := by
  sym => simp arithSimp

example (a : Rat) : (a / 2) ^ 2 = a ^ 2 / 4 := by
  sym => simp arithSimp

example : (1 : Rat) / 2 + 1 / 3 = 5 / 6 := by
  sym => simp arithSimp

example (a : Rat) : a / (-2) = -(a / 2) := by
  sym => simp arithSimp

example (a b : Rat) : (a + b) / 2 * ((a - b) / 2) = (a ^ 2 - b ^ 2) / 4 := by
  sym => simp arithSimp

-- The normal form of a term with a denominator, and its fixpoint.
/--
trace: case grind
f : Rat → Rat
a b : Rat
⊢ f ((3 * a + 2 * b) * 6⁻¹) = 0
-/
#guard_msgs in
example (f : Rat → Rat) (a b : Rat) : f (a / 2 + b / 3) = 0 := by
  sym =>
    simp arithSimp
    show_goals
    sorry

example (f : Rat → Rat) (a b : Rat) : f (a / 2 + b / 3) = f ((3 * a + 2 * b) * 6⁻¹) := by
  sym => simp arithSimp

-- Relations become denominator-free.
example (a b : Rat) (h : 3 * a = 2 * b) : a / 2 = b / 3 := by
  sym =>
    simp arithSimp
    exact h

example (a b : Rat) (h : a ≤ 2 * b) : a / 2 ≤ b := by
  sym =>
    simp arithSimp
    exact h

example (a : Rat) (h : 0 < a) : a / 2 < a := by
  sym =>
    simp arithSimp
    exact h

example (a b : Rat) : a / 3 + b / 3 = (a + b) / 3 := by
  sym => simp arithSimp

-- A field given by a local instance, with and without characteristic zero: numeral inverses
-- stay atoms when the characteristic is unknown.
open Lean.Grind in
example (F : Type) [Field F] (a b : F) : a / b + a / b = 2 * (a * b⁻¹) := by
  sym => simp arithSimp

open Lean.Grind in
example (F : Type) [Field F] (a : F) : a / 2 + a / 2 = 2 * (a * 2⁻¹) := by
  sym => simp arithSimp

open Lean.Grind in
example (F : Type) [Field F] [IsCharP F 0] (a b : F) : a / 2 + b / 3 = (3 * a + 2 * b) * 6⁻¹ := by
  sym => simp arithSimp

open Lean.Grind in
example (F : Type) [Field F] [IsCharP F 0] (a b : F) (h : 3 * a = 2 * b) : a / 2 = b / 3 := by
  sym =>
    simp arithSimp
    exact h

-- Division on a ring that is not a field is an atom.
example (x y : Int) : x / y + 0 = x / y := by
  sym => simp arithSimp
