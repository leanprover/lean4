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
import Init.ByCases
import Init.Omega
public section
namespace Lean.Grind.Field.NormNum

attribute [local instance] Semiring.natCast Ring.intCast

abbrev ofRat {α} [Field α] (r : Rat) : α :=
  (r.num : α)/(r.den : α)

attribute [local simp]
  Field.inv_one Semiring.natCast_zero Semiring.natCast_one Ring.intCast_zero Ring.intCast_one Semiring.one_mul Semiring.mul_one
  Semiring.pow_zero Field.inv_one Field.inv_zero

private theorem dvd_helper₁ {z : Int} {n : Nat} : ↑(z.natAbs.gcd n : Int) ∣ z :=
  Rat.normalize.dvd_num rfl
private theorem dvd_helper₂ {z : Int} {n : Nat} : z.natAbs.gcd n ∣ n :=
  Nat.gcd_dvd_right z.natAbs n

private theorem nonzero_helper {α} [Field α] {z : Int} {n m : Nat} (hn : (n : α) ≠ 0) (hm : (m : α) ≠ 0) :
    (z.natAbs.gcd (n * m) : α) ≠ 0 := by
  intro h
  have : z.natAbs.gcd (n * m) ∣ (n * m) := Nat.gcd_dvd_right z.natAbs (n * m)
  obtain ⟨k, hk⟩ := this
  replace hk := congrArg (fun x : Nat => (x : α)) hk
  dsimp at hk
  rw [Semiring.natCast_mul, Semiring.natCast_mul, h, Semiring.zero_mul] at hk
  replace hk := Field.of_mul_eq_zero hk
  simp_all

theorem ofRat_add' {α} [Field α] {a b : Rat} (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    (ofRat (a + b) : α) = ofRat a + ofRat b := by
  rw [ofRat, ofRat, ofRat, Rat.num_add, Rat.den_add]
  rw [Field.intCast_div_of_dvd dvd_helper₁ (by simpa [Ring.intCast_natCast] using (nonzero_helper ha hb))]
  rw [Field.natCast_div_of_dvd dvd_helper₂ (nonzero_helper ha hb)]
  rw [Ring.intCast_natCast, Field.div_div_right]
  rw [Field.div_mul_cancel (nonzero_helper ha hb)]
  rw [Field.add_div hb, Field.div_mul, Field.div_add ha]
  rw [Ring.intCast_add, Ring.intCast_mul, Ring.intCast_mul, Ring.intCast_natCast,
    Ring.intCast_natCast, CommSemiring.mul_comm (a.den : α), Field.div_div_left,
    Semiring.natCast_mul]
theorem ofRat_mul' {α} [Field α] {a b : Rat} (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) : (ofRat (a * b) : α) = ofRat a * ofRat b := by
  rw [ofRat, ofRat, ofRat, Rat.num_mul, Rat.den_mul]
  rw [Field.intCast_div_of_dvd dvd_helper₁ (by simpa [Ring.intCast_natCast] using (nonzero_helper ha hb))]
  rw [Field.natCast_div_of_dvd dvd_helper₂ (nonzero_helper ha hb)]
  rw [Ring.intCast_natCast, Field.div_div_right]
  rw [Field.div_mul_cancel (nonzero_helper ha hb)]
  rw [Field.div_mul, Field.mul_div, Field.div_div_left, Ring.intCast_mul, Semiring.natCast_mul,
    CommSemiring.mul_comm (b.den : α)]

-- Note: false without `IsCharP α 0` (consider `a = b = 1/2` in `ℤ/2ℤ`):
theorem ofRat_add {α} [Field α] [IsCharP α 0] (a b : Rat) :
    (ofRat (a + b) : α) = ofRat a + ofRat b :=
  ofRat_add' (natCast_ne_zero a.den_nz) (natCast_ne_zero b.den_nz)
-- Note: false without `IsCharP α 0` (consider `a = 2/3` and `b = 1/2` in `ℤ/2ℤ`):
theorem ofRat_mul {α} [Field α] [IsCharP α 0] (a b : Rat) : (ofRat (a * b) : α) = ofRat a * ofRat b :=
  ofRat_mul' (natCast_ne_zero a.den_nz) (natCast_ne_zero b.den_nz)

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

theorem ofRat_div' {α} [Field α] {a b : Rat} (ha : (a.den : α) ≠ 0) (hb : (b.num : α) ≠ 0) :
    (ofRat (a / b) : α) = ofRat a / ofRat b := by
  replace hb : ((b⁻¹).den : α) ≠ 0 := by
    simp only [Rat.den_inv, Rat.num_eq_zero, ne_eq]
    rw [if_neg (by intro h; simp_all)]
    rw [← Ring.intCast_natCast]
    by_cases h : 0 ≤ b.num
    · have : (b.num.natAbs : Int) = b.num := Int.natAbs_of_nonneg h
      rwa [this]
    · have : (b.num.natAbs : Int) = -b.num := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [this, Ring.intCast_neg]
      rwa [AddCommGroup.neg_eq_iff, AddCommGroup.neg_zero]
  rw [Rat.div_def, ofRat_mul' ha hb, ofRat_inv, Field.div_eq_mul_inv (ofRat a)]

theorem ofRat_div {α} [Field α] [IsCharP α 0] (a b : Rat) : (ofRat (a / b) : α) = ofRat a / ofRat b := by
  rw [Rat.div_def, ofRat_mul, ofRat_inv, Field.div_eq_mul_inv (ofRat a)]

theorem ofRat_neg {α} [Field α] (a : Rat) : (ofRat (-a) : α) = -ofRat a := by
  simp [ofRat, Field.div_eq_mul_inv, Ring.intCast_neg, Ring.neg_mul]

theorem ofRat_sub' {α} [Field α] {a b : Rat} (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    (ofRat (a - b) : α) = ofRat a - ofRat b := by
  replace hb : ((-b).den : α) ≠ 0 := by simpa
  rw [Rat.sub_eq_add_neg, ofRat_add' ha hb, ofRat_neg, Ring.sub_eq_add_neg]

theorem ofRat_sub {α} [Field α] [IsCharP α 0] (a b : Rat) :
    (ofRat (a - b) : α) = ofRat a - ofRat b := by
  rw [Rat.sub_eq_add_neg, ofRat_add, ofRat_neg, Ring.sub_eq_add_neg]

theorem ofRat_npow' {α} [Field α] {a : Rat} (ha : (a.den : α) ≠ 0) (n : Nat) : (ofRat (a^n) : α) = ofRat a ^ n := by
  have h : ∀ n : Nat, ((a^n).den : α) ≠ 0 := by
    intro n
    rw [Rat.den_pow, ne_eq, Semiring.natCast_pow]
    intro h
    induction n with
    | zero =>
      rw [Semiring.pow_zero] at h
      exact Field.zero_ne_one h.symm
    | succ n ih' =>
      rw [Semiring.pow_succ] at h
      replace h := Field.of_mul_eq_zero h
      rcases h with h | h
      · exact ih' h
      · exact ha h
  induction n
  next => simp [Field.div_eq_mul_inv, ofRat]
  next n ih =>
    rw [Rat.pow_succ, ofRat_mul' (h _) ha, ih, Semiring.pow_succ]

theorem ofRat_npow {α} [Field α] [IsCharP α 0] (a : Rat) (n : Nat) : (ofRat (a^n) : α) = ofRat a ^ n := by
  induction n
  next => simp [Field.div_eq_mul_inv, ofRat]
  next n ih => rw [Rat.pow_succ, ofRat_mul, ih, Semiring.pow_succ]

theorem ofRat_zpow' {α} [Field α] {a : Rat} (ha : (a.den : α) ≠ 0) (n : Int) : (ofRat (a^n) : α) = ofRat a ^ n := by
  cases n
  next => rw [Int.ofNat_eq_natCast, Rat.zpow_natCast, Field.zpow_natCast, ofRat_npow' ha]
  next =>
    rw [Int.negSucc_eq, Rat.zpow_neg, Field.zpow_neg, ofRat_inv]
    congr 1
    have : (1 : Int) = (1 : Nat) := rfl
    rw [this, ← Int.natCast_add, Rat.zpow_natCast, Field.zpow_natCast, ofRat_npow' ha]

theorem ofRat_zpow {α} [Field α] [IsCharP α 0] (a : Rat) (n : Int) : (ofRat (a^n) : α) = ofRat a ^ n := by
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

theorem add_eq {α} [Field α] [IsCharP α 0] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ + v₂ → a = ofRat v₁ → b = ofRat v₂ → a + b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_add]

theorem sub_eq {α} [Field α] [IsCharP α 0] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ - v₂ → a = ofRat v₁ → b = ofRat v₂ → a - b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_sub]

theorem mul_eq {α} [Field α] [IsCharP α 0] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ * v₂ → a = ofRat v₁ → b = ofRat v₂ → a * b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_mul]

theorem div_eq {α} [Field α] [IsCharP α 0] (a b : α) (v₁ v₂ v : Rat)
    : v == v₁ / v₂ → a = ofRat v₁ → b = ofRat v₂ → a / b = ofRat v := by
  simp; intros; subst v a b; rw [ofRat_div]

theorem inv_eq {α} [Field α] (a : α) (v₁ v : Rat)
    : v == v₁⁻¹ → a = ofRat v₁ → a⁻¹ = ofRat v := by
  simp; intros; subst v a; rw [ofRat_inv]

theorem neg_eq {α} [Field α] (a : α) (v₁ v : Rat)
    : v == -v₁ → a = ofRat v₁ → -a = ofRat v := by
  simp; intros; subst v a; rw [ofRat_neg]

theorem npow_eq {α} [Field α] [IsCharP α 0] (a : α) (n : Nat) (v₁ v : Rat)
    : v == v₁^n → a = ofRat v₁ → a ^ n = ofRat v := by
  simp; intros; subst v a; rw [ofRat_npow]

theorem zpow_eq {α} [Field α] [IsCharP α 0] (a : α) (n : Int) (v₁ v : Rat)
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
