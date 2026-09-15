/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Nat.Gcd
public import Init.Data.Int.Basic
public import Init.Data.Int.Repr
import Init.Data.Int.Lemmas
import Init.Data.AC
import Init.TacticsExtra

/-!
# Extended Euclidean algorithm

`Nat.extendedGcd` computes a greatest common divisor together with signed Bézout coefficients in
one Euclidean pass. `Nat.extendedGcd_gcd` identifies the gcd, and `Nat.extendedGcd_bezout` certifies
the coefficients. The Lean implementation uses arbitrary-precision `Nat` and `Int` arithmetic;
compiled evaluation uses a native implementation backed by GMP when available.
-/

@[expose] public section

namespace Nat

/-- The gcd and the two Bézout coefficients returned by `Nat.extendedGcd`. -/
structure ExtendedGcdResult where
  /-- The greatest common divisor of the inputs. -/
  gcd : Nat
  /-- The signed coefficient of the first input. -/
  coeffA : Int
  /-- The signed coefficient of the second input. -/
  coeffB : Int
deriving Repr, DecidableEq, Inhabited

/--
Computes the greatest common divisor of `a` and `b` together with signed Bézout coefficients in
one pass of the extended Euclidean algorithm. The result `r` satisfies `r.gcd = Nat.gcd a b` and
`(r.gcd : Int) = a * r.coeffA + b * r.coeffB`.

For a zero first input, the result is `⟨b, 0, 1⟩`, including `⟨0, 0, 1⟩` when both inputs are zero.
For a nonzero first input and a zero second input, the result is `⟨a, 1, 0⟩`.
The coefficients are not unique; no minimality or symmetry of the returned coefficients is
specified.

Examples:
* `Nat.extendedGcd 240 46 = ⟨2, -9, 47⟩`
* `Nat.extendedGcd 0 19 = ⟨19, 0, 1⟩`
* `Nat.extendedGcd 19 0 = ⟨19, 1, 0⟩`
-/
@[extern "lean_nat_extended_gcd"]
def extendedGcd (a b : @& Nat) : ExtendedGcdResult :=
  go a 1 0 b 0 1
where
  /-- Implementation detail of `Nat.extendedGcd`: the two rows represent the remainders as
  linear combinations of the original inputs. -/
  go (r : Nat) (s t : Int) (r' : Nat) (s' t' : Int) : ExtendedGcdResult :=
    if _h : r = 0 then
      ⟨r', s', t'⟩
    else
      let q : Int := r' / r
      go (r' % r) (s' - q * s) (t' - q * t) r s t
  termination_by r
  decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

@[simp] theorem extendedGcd_zero_left (b : Nat) : extendedGcd 0 b = ⟨b, 0, 1⟩ := by
  rw [extendedGcd, extendedGcd.go]
  rfl

@[simp] theorem extendedGcd_zero_right {a : Nat} (h : a ≠ 0) :
    extendedGcd a 0 = ⟨a, 1, 0⟩ := by
  rw [extendedGcd, extendedGcd.go, dite_eq_right h]
  simp only [Nat.zero_div, Nat.zero_mod, Int.natCast_zero, Int.zero_mul, Int.sub_zero]
  rw [extendedGcd.go]
  rfl

@[simp] theorem extendedGcd_self {a : Nat} (h : a ≠ 0) : extendedGcd a a = ⟨a, 1, 0⟩ := by
  rw [extendedGcd, extendedGcd.go, dite_eq_right h]
  simp only [Nat.mod_self]
  rw [extendedGcd.go]
  rfl

private theorem extendedGcd_go_gcd (r r' : Nat) : ∀ s t s' t',
    (extendedGcd.go r s t r' s' t').gcd = Nat.gcd r r' := by
  induction r, r' using Nat.gcd.induction with
  | H0 r' =>
    intro s t s' t'
    rw [extendedGcd.go]
    simp
  | H1 r r' hr ih =>
    intro s t s' t'
    rw [extendedGcd.go, dite_eq_right (Nat.ne_of_gt hr), ih, ← Nat.gcd_rec]

private theorem extendedGcd_go_bezout (a b r r' : Nat) : ∀ s t s' t',
    (r : Int) = a * s + b * t → (r' : Int) = a * s' + b * t' →
    let out := extendedGcd.go r s t r' s' t'
    (out.gcd : Int) = a * out.coeffA + b * out.coeffB := by
  induction r, r' using Nat.gcd.induction with
  | H0 r' =>
    intro s t s' t' _ hr'
    simpa [extendedGcd.go] using hr'
  | H1 r r' h ih =>
    intro s t s' t' hr hr'
    rw [extendedGcd.go, dite_eq_right (Nat.ne_of_gt h)]
    apply ih _ _ _ _ ?_ hr
    calc
      (r' % r : Int) = (r' : Int) - (r' / r : Nat) * (r : Int) := by
        have hd := congrArg (fun n : Nat => (n : Int)) (Nat.mod_add_div r' r)
        simp only [Int.natCast_add, Int.natCast_mul] at hd
        rw [← hd, Int.mul_comm (r : Int), Int.add_sub_cancel]
      _ = a * (s' - (r' / r : Nat) * s) + b * (t' - (r' / r : Nat) * t) := by
        rw [Int.mul_sub, Int.mul_sub, hr', hr, Int.mul_add]
        simp only [Int.sub_eq_add_neg, Int.neg_add]
        ac_rfl

/-- The gcd component of `Nat.extendedGcd a b` is `Nat.gcd a b`. -/
@[simp] theorem extendedGcd_gcd (a b : Nat) : (extendedGcd a b).gcd = Nat.gcd a b :=
  extendedGcd_go_gcd a b 1 0 0 1

/-- The coefficients returned by `Nat.extendedGcd` satisfy Bézout's identity. -/
theorem extendedGcd_bezout (a b : Nat) :
    (Nat.gcd a b : Int) = a * (extendedGcd a b).coeffA + b * (extendedGcd a b).coeffB := by
  have h := extendedGcd_go_bezout a b a b 1 0 0 1 (by simp) (by simp)
  change ((extendedGcd a b).gcd : Int) =
    a * (extendedGcd a b).coeffA + b * (extendedGcd a b).coeffB at h
  simpa only [extendedGcd_gcd] using h

/-- The gcd returned by `Nat.extendedGcd a b` divides `a`. -/
theorem extendedGcd_dvd_left (a b : Nat) : (extendedGcd a b).gcd ∣ a := by
  rw [extendedGcd_gcd]
  exact Nat.gcd_dvd_left a b

/-- The gcd returned by `Nat.extendedGcd a b` divides `b`. -/
theorem extendedGcd_dvd_right (a b : Nat) : (extendedGcd a b).gcd ∣ b := by
  rw [extendedGcd_gcd]
  exact Nat.gcd_dvd_right a b

end Nat
