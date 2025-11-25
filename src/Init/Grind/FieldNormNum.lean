/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.Field
public import Init.Data.Rat.Basic
import Init.Data.Rat.Lemmas
public section
namespace Lean.Grind.Field.NormNum

attribute [local instance] Semiring.natCast Ring.intCast

abbrev ofRat {α} [Field α] (r : Rat) : α :=
  (r.num : α)/(r.den : α)

attribute [local simp]
  Field.inv_one Semiring.natCast_zero Semiring.natCast_one Ring.intCast_zero Ring.intCast_one Semiring.one_mul Semiring.mul_one
  Semiring.pow_zero Field.inv_one Field.inv_zero

private theorem dvd_helper₁ {z : Int} {n : Nat} : ↑(z.natAbs.gcd n : Int) ∣ z := sorry
private theorem dvd_helper₂ {z : Int} {n : Nat} : z.natAbs.gcd n ∣ n := sorry

private theorem nonzero_helper {α} [Field α] {z : Int} {n m : Nat} (hn : n ≠ 0) (hm : m ≠ 0) :
    (z.natAbs.gcd (n * m) : α) ≠ 0 := sorry

theorem ofRat_add {α} [Field α] (a b : Rat) : (ofRat (a + b) : α) = ofRat a + ofRat b := by
  rw [ofRat, ofRat, ofRat, Rat.num_add, Rat.den_add]
  rw [Field.intCast_div_of_dvd dvd_helper₁]
  rw [Field.natCast_div_of_dvd dvd_helper₂]
  rw [Ring.intCast_natCast, Field.div_div]
  rw [Field.div_mul_cancel _ (nonzero_helper a.den_nz b.den_nz)]
  rw [Field.add_div, Field.div_mul, Field.div_add]
  sorry
theorem ofRat_mul {α} [Field α] (a b : Rat) : (ofRat (a * b) : α) = ofRat a * ofRat b := by
  rw [ofRat, ofRat, ofRat, Rat.num_mul, Rat.den_mul]
  rw [Field.intCast_div_of_dvd dvd_helper₁]
  rw [Field.natCast_div_of_dvd dvd_helper₂]
  rw [Ring.intCast_natCast, Field.div_div]
  rw [Field.div_mul_cancel _ (nonzero_helper a.den_nz b.den_nz)]
  sorry
theorem ofRat_inv {α} [Field α] (a : Rat) : (ofRat (a⁻¹) : α) = (ofRat a)⁻¹ := by
  simp [ofRat]; split
  next h => simp [h, Field.div_eq_mul_inv]
  next =>
    simp [Field.div_eq_mul_inv, Field.inv_mul, Field.inv_inv, Ring.intCast_mul, Ring.intCast_natCast]
    generalize a.num = n
    generalize a.den = d
    conv => rhs; rw [← Int.sign_mul_natAbs n]
    simp [Ring.intCast_mul, Ring.intCast_natCast, Field.inv_mul]
    have : (Int.cast n.sign : α) = (Int.cast n.sign : α)⁻¹ := by
      cases Int.sign_trichotomy n
      next h => simp [h]
      next h => cases h <;> simp [*, Ring.intCast_neg, Field.inv_neg]
    rw [← this, Semiring.mul_assoc, Semiring.mul_assoc]
    congr 1
    rw [CommSemiring.mul_comm]
theorem ofRat_div {α} [Field α] (a b : Rat) : (ofRat (a / b) : α) = ofRat a / ofRat b := by
  simp [Rat.div_def, ofRat_mul, Field.div_eq_mul_inv (ofRat a), ofRat_inv]
theorem ofRat_neg {α} [Field α] (a : Rat) : (ofRat (-a) : α) = -ofRat a := by
  simp [ofRat, Field.div_eq_mul_inv, Ring.intCast_neg, Ring.neg_mul]
theorem ofRat_sub {α} [Field α] (a b : Rat) : (ofRat (a - b) : α) = ofRat a - ofRat b := by
  simp [Rat.sub_eq_add_neg, ofRat_add, ofRat_neg, Ring.sub_eq_add_neg]
theorem ofRat_npow {α} [Field α] (a : Rat) (n : Nat) : (ofRat (a^n) : α) = ofRat a ^ n := by
  induction n
  next => simp [Field.div_eq_mul_inv, ofRat]
  next n ih => simp [Rat.pow_succ, ofRat_mul, ih, Semiring.pow_succ]
theorem ofRat_zpow {α} [Field α] (a : Rat) (n : Int) : (ofRat (a^n) : α) = ofRat a ^ n := by
  cases n
  next => rw [Int.ofNat_eq_natCast, Rat.zpow_natCast, Field.zpow_natCast, ofRat_npow]
  next =>
    rw [Int.negSucc_eq, Rat.zpow_neg, Field.zpow_neg, ofRat_inv]
    congr 1
    have : (1 : Int) = (1 : Nat) := rfl
    rw [this, ← Int.natCast_add, Rat.zpow_natCast, Field.zpow_natCast, ofRat_npow]

theorem natCast_eq {α} [Field α] (n : Nat) : (NatCast.natCast n : α) = ofRat n := by
  simp [ofRat, Ring.intCast_natCast, Semiring.natCast_one, Field.div_eq_mul_inv,
        Field.inv_one, Semiring.mul_one]

theorem ofNat_eq {α} [Field α] (n : Nat) : (OfNat.ofNat n : α) = ofRat n := by
  rw [Semiring.ofNat_eq_natCast]
  apply natCast_eq

theorem intCast_eq {α} [Field α] (n : Int) : (IntCast.intCast n : α) = ofRat n := by
  simp [ofRat, Semiring.natCast_one, Field.div_eq_mul_inv, Field.inv_one, Semiring.mul_one]

theorem add_eq {α} [Field α] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ + v₂ → a = ofRat v₁ → b = ofRat v₂ → a + b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_add]

theorem sub_eq {α} [Field α] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ - v₂ → a = ofRat v₁ → b = ofRat v₂ → a - b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_sub]

theorem mul_eq {α} [Field α] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ * v₂ → a = ofRat v₁ → b = ofRat v₂ → a * b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_mul]

theorem div_eq {α} [Field α] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ / v₂ → a = ofRat v₁ → b = ofRat v₂ → a / b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_div]

theorem inv_eq {α} [Field α] (a : α) (v₁ v : Rat)
    : v == v₁⁻¹ → a = ofRat v₁ → a⁻¹ = ofRat v := by
  simp; intros; subst v a; rw [ofRat_inv]

theorem neg_eq {α} [Field α] (a : α) (v₁ v : Rat)
    : v == -v₁ → a = ofRat v₁ → -a = ofRat v := by
  simp; intros; subst v a; rw [ofRat_neg]

theorem npow_eq {α} [Field α] (a : α) (n : Nat) (v₁ v : Rat)
    : v == v₁^n → a = ofRat v₁ → a ^ n = ofRat v := by
  simp; intros; subst v a; rw [ofRat_npow]

theorem zpow_eq {α} [Field α] (a : α) (n : Int) (v₁ v : Rat)
    : v == v₁^n → a = ofRat v₁ → a ^ n = ofRat v := by
  simp; intros; subst v a; rw [ofRat_zpow]

theorem eq_int {α} [Field α] (a : α) (v : Rat) (n : Int)
    : n == v.num && v.den == 1 → a = ofRat v → a = IntCast.intCast n := by
  simp; cases v; simp [ofRat]
  next den _ _ =>
  intros; subst den n a
  simp [Semiring.natCast_one, Field.div_eq_mul_inv, Field.inv_one, Semiring.mul_one]

theorem eq_inv {α} [Field α] (a : α) (v : Rat) (d : Nat)
    : v.num == 1 && v.den == d → a = ofRat v → a = (NatCast.natCast d : α)⁻¹ := by
  simp; cases v; simp [ofRat]
  next num _ _ _ =>
  intros; subst num d a
  simp [Ring.intCast_one, Field.div_eq_mul_inv, Semiring.one_mul]

theorem eq_mul_inv {α} [Field α] (a : α) (v : Rat) (n : Int) (d : Nat)
    : v.num == n && v.den == d → a = ofRat v → a = (IntCast.intCast n : α) * (NatCast.natCast d : α)⁻¹ := by
  cases v; simp [ofRat]
  intros; subst d n a
  simp [Field.div_eq_mul_inv]

end Lean.Grind.Field.NormNum
