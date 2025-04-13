/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Markus Himmel
-/
prelude
import Init.Data.Int.Basic
import Init.Data.Nat.Gcd
import Init.Data.Nat.Lcm
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Pow

/-!
Definition and lemmas for gcd and lcm over Int

-/
namespace Int

/-! ## gcd -/

/--
Computes the greatest common divisor of two integers as a natural number. The GCD of two integers is
the largest natural number that evenly divides both. However, the GCD of a number and `0` is the
number's absolute value.

This implementation uses `Nat.gcd`, which is overridden in both the kernel and the compiler to
efficiently evaluate using arbitrary-precision arithmetic.

Examples:
* `Int.gcd 10 15 = 5`
* `Int.gcd 10 (-15) = 5`
* `Int.gcd (-6) (-9) = 3`
* `Int.gcd 0 5 = 5`
* `Int.gcd (-7) 0 = 7`
-/
def gcd (m n : Int) : Nat := m.natAbs.gcd n.natAbs

theorem gcd_eq_natAbs_gcd_natAbs (m n : Int) : gcd m n = Nat.gcd m.natAbs n.natAbs := rfl

theorem gcd_dvd_natAbs_left (a b : Int) : gcd a b ∣ a.natAbs := Nat.gcd_dvd_left ..
theorem gcd_dvd_natAbs_right (a b : Int) : gcd a b ∣ b.natAbs := Nat.gcd_dvd_right ..

theorem gcd_dvd_left (a b : Int) : (gcd a b : Int) ∣ a := by
  simp [ofNat_dvd_left, gcd_dvd_natAbs_left]

theorem gcd_dvd_right (a b : Int) : (gcd a b : Int) ∣ b := by
  simp [ofNat_dvd_left, gcd_dvd_natAbs_right]

@[simp] theorem one_gcd {a : Int} : gcd 1 a = 1 := by simp [gcd_eq_natAbs_gcd_natAbs]
@[simp] theorem gcd_one {a : Int} : gcd a 1 = 1 := by simp [gcd_eq_natAbs_gcd_natAbs]

@[simp] theorem zero_gcd {a : Int} : gcd 0 a = a.natAbs := by simp [gcd_eq_natAbs_gcd_natAbs]
@[simp] theorem gcd_zero {a : Int} : gcd a 0 = a.natAbs := by simp [gcd_eq_natAbs_gcd_natAbs]

theorem gcd_one_left (a : Int) : gcd 1 a = 1 := by simp
theorem gcd_one_right (a : Int) : gcd a 1 = 1 := by simp
theorem gcd_zero_left (a : Int) : gcd 0 a = a.natAbs := by simp
theorem gcd_zero_right (a : Int) : gcd a 0 = a.natAbs := by simp

@[simp] theorem gcd_self {a : Int} : gcd a a = a.natAbs := by simp [gcd_eq_natAbs_gcd_natAbs]

@[simp] theorem neg_gcd {a b : Int} : gcd (-a) b = gcd a b := by simp [gcd_eq_natAbs_gcd_natAbs]
@[simp] theorem gcd_neg {a b : Int} : gcd a (-b) = gcd a b := by simp [gcd_eq_natAbs_gcd_natAbs]

@[simp, norm_cast] protected theorem gcd_natCast_natCast (a b : Nat) :
    gcd (a : Int) (b : Int) = Nat.gcd a b := by
  simp [gcd_eq_natAbs_gcd_natAbs]

theorem gcd_le_natAbs_left (b : Int) (ha : a ≠ 0) : gcd a b ≤ a.natAbs :=
  Nat.gcd_le_left b.natAbs (natAbs_pos.2 ha)

theorem gcd_le_natAbs_right (a : Int) (hb : b ≠ 0) : gcd a b ≤ b.natAbs :=
  Nat.gcd_le_right a.natAbs (natAbs_pos.2 hb)

theorem gcd_le_left (b : Int) (ha : 0 < a) : (gcd a b : Int) ≤ a := by
  rw (occs := [2]) [(by omega : a = (a.natAbs : Int))]
  simp [gcd_le_natAbs_left b (by omega : a ≠ 0)]

theorem gcd_le_right (a : Int) (hb : 0 < b) : (gcd a b : Int) ≤ b := by
  rw (occs := [2]) [(by omega : b = (b.natAbs : Int))]
  simp [gcd_le_natAbs_right a (by omega : b ≠ 0)]

theorem dvd_coe_gcd {a b c : Int} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (gcd a b : Int) :=
  ofNat_dvd_right.2 (Nat.dvd_gcd (natAbs_dvd_natAbs.2 ha) (natAbs_dvd_natAbs.2 hb))

theorem dvd_gcd {a b : Int} {c : Nat} (ha : (c : Int) ∣ a) (hb : (c : Int) ∣ b) : c ∣ gcd a b :=
  ofNat_dvd.1 (dvd_coe_gcd ha hb)

theorem dvd_coe_gcd_iff {a b c : Int} : c ∣ (gcd a b : Int) ↔ c ∣ a ∧ c ∣ b :=
  ⟨fun h => ⟨Int.dvd_trans h (gcd_dvd_left _ _), Int.dvd_trans h (gcd_dvd_right _ _)⟩,
   fun ⟨ha, hb⟩ => dvd_coe_gcd ha hb⟩

theorem dvd_gcd_iff {a b : Int} {c : Nat} : c ∣ gcd a b ↔ (c : Int) ∣ a ∧ (c : Int) ∣ b := by
  rw [← ofNat_dvd, dvd_coe_gcd_iff]

theorem gcd_comm (a b : Int) : gcd a b = gcd b a := Nat.gcd_comm ..

theorem gcd_eq_natAbs_left_iff_dvd : gcd a b = a.natAbs ↔ a ∣ b := by
  simp [gcd_eq_natAbs_gcd_natAbs, Nat.gcd_eq_left_iff_dvd]

theorem gcd_eq_natAbs_right_iff_dvd : gcd a b = b.natAbs ↔ b ∣ a := by
  simp [gcd_eq_natAbs_gcd_natAbs, Nat.gcd_eq_right_iff_dvd]

theorem gcd_eq_left_iff_dvd (ha : 0 ≤ a) : gcd a b = a ↔ a ∣ b := by
  rw (occs := [2]) [eq_natAbs_of_nonneg ha]
  simp [ofNat_inj, gcd_eq_natAbs_left_iff_dvd]

theorem gcd_eq_right_iff_dvd (hb : 0 ≤ b) : gcd a b = b ↔ b ∣ a := by
  rw [gcd_comm, gcd_eq_left_iff_dvd hb]

theorem gcd_assoc (a b c : Int) : gcd (gcd a b) c = gcd a (gcd b c) := Nat.gcd_assoc ..

theorem gcd_mul_left (m n k : Int) : gcd (m * n) (m * k) = m.natAbs * gcd n k := by
  simp [gcd_eq_natAbs_gcd_natAbs, Nat.gcd_mul_left, natAbs_mul]

theorem gcd_mul_right (m n k : Int) : gcd (m * n) (k * n) = gcd m k * n.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, Nat.gcd_mul_right, natAbs_mul]

theorem gcd_pos_of_ne_zero_left {a : Int} (b : Int) (ha : a ≠ 0) : 0 < gcd a b :=
  Nat.gcd_pos_of_pos_left _ (natAbs_pos.2 ha)

theorem gcd_pos_of_ne_zero_right (a : Int) {b : Int} (hb : b ≠ 0) : 0 < gcd a b :=
  Nat.gcd_pos_of_pos_right _ (natAbs_pos.2 hb)

theorem gcd_ne_zero_left (ha : a ≠ 0) : gcd a b ≠ 0 := by
  simp [← Nat.pos_iff_ne_zero, gcd_pos_of_ne_zero_left _ ha]

theorem gcd_ne_zero_right (hb : b ≠ 0) : gcd a b ≠ 0 := by
  simp [← Nat.pos_iff_ne_zero, gcd_pos_of_ne_zero_right _ hb]

theorem natAbs_div_gcd_pos_of_ne_zero_left (b : Int) (h : a ≠ 0) : 0 < a.natAbs / gcd a b :=
  Nat.div_gcd_pos_of_pos_left _ (natAbs_pos.2 h)

theorem natAbs_div_gcd_pos_of_ne_zero_right (a : Int) (h : b ≠ 0) : 0 < b.natAbs / gcd a b :=
  Nat.div_gcd_pos_of_pos_right _ (natAbs_pos.2 h)

theorem ediv_gcd_ne_zero_of_ne_zero_left (b : Int) (h : a ≠ 0) : a / gcd a b ≠ 0 := by
  rw [← natAbs_pos, natAbs_ediv_of_dvd (gcd_dvd_left _ _), natAbs_ofNat]
  exact natAbs_div_gcd_pos_of_ne_zero_left _ h

theorem ediv_gcd_ne_zero_if_ne_zero_right (a : Int) (h : b ≠ 0) : b / gcd a b ≠ 0 := by
  simpa [gcd_comm] using ediv_gcd_ne_zero_of_ne_zero_left a h

theorem eq_zero_of_gcd_eq_zero_left (h : gcd a b = 0) : a = 0 :=
  natAbs_eq_zero.1 (Nat.eq_zero_of_gcd_eq_zero_left h)

theorem eq_zero_of_gcd_eq_zero_right (h : gcd a b = 0) : b = 0 :=
  natAbs_eq_zero.1 (Nat.eq_zero_of_gcd_eq_zero_right h)

theorem gcd_ediv {a b c : Int} (ha : c ∣ a) (hb : c ∣ b) :
    gcd (a / c) (b / c) = gcd a b / c.natAbs := by
  rw [gcd_eq_natAbs_gcd_natAbs, natAbs_ediv_of_dvd ha, natAbs_ediv_of_dvd hb,
    Nat.gcd_div (by simpa) (by simpa), gcd_eq_natAbs_gcd_natAbs]

theorem gcd_dvd_gcd_of_dvd_left {a b : Int} (c : Int) (h : a ∣ b) : gcd a c ∣ gcd b c :=
  Nat.gcd_dvd_gcd_of_dvd_left _ (by simpa)

theorem gcd_dvd_gcd_of_dvd_right {a b : Int} (c : Int) (h : a ∣ b) : gcd c a ∣ gcd c b :=
  Nat.gcd_dvd_gcd_of_dvd_right _ (by simpa)

theorem gcd_dvd_gcd_mul_left_left (a b c : Int) : gcd a b ∣ gcd (c * a) b := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_dvd_gcd_mul_left_left ..

theorem gcd_dvd_gcd_mul_right_left (a b c : Int) : gcd a b ∣ gcd (a * c) b := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_dvd_gcd_mul_right_left ..

theorem gcd_dvd_gcd_mul_left_right (a b c : Int) : gcd a b ∣ gcd a (c * b) := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_dvd_gcd_mul_left_right ..

theorem gcd_dvd_gcd_mul_right_right (a b c : Int) : gcd a b ∣ gcd a (b * c) := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_dvd_gcd_mul_right_right ..

theorem gcd_eq_natAbs_left (h : a ∣ b) : gcd a b = a.natAbs :=
  gcd_eq_natAbs_left_iff_dvd.2 h

theorem gcd_eq_natAbs_right (h : b ∣ a) : gcd a b = b.natAbs :=
  gcd_eq_natAbs_right_iff_dvd.2 h

theorem gcd_eq_left (ha : 0 ≤ a) (h : a ∣ b) : gcd a b = a :=
  (gcd_eq_left_iff_dvd ha).2 h

theorem gcd_eq_right (hb : 0 ≤ b) (h : b ∣ a) : gcd a b = b :=
  (gcd_eq_right_iff_dvd hb).2 h

theorem gcd_right_eq_iff {a b b' : Int} : gcd a b = gcd a b' ↔ ∀ c, c ∣ a → (c ∣ b ↔ c ∣ b') := by
  simp only [gcd_eq_natAbs_gcd_natAbs, Nat.gcd_right_eq_iff]
  refine ⟨fun hk c hc => ?_, fun hc k hk => ?_⟩
  · simpa using hk c.natAbs (by simpa)
  · simpa [ofNat_dvd_left] using hc k (by simpa [ofNat_dvd_left])

theorem gcd_left_eq_iff {a a' b : Int} : gcd a b = gcd a' b ↔ ∀ c, c ∣ b → (c ∣ a ↔ c ∣ a') := by
  rw [gcd_comm a b, gcd_comm a' b, gcd_right_eq_iff]

@[simp] theorem gcd_mul_left_left (a b : Int) : gcd (a * b) b = b.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, natAbs_mul]

@[simp] theorem gcd_mul_left_right (a b : Int) : gcd a (b * a) = a.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, natAbs_mul]

@[simp] theorem gcd_mul_right_left (a b : Int) : gcd (b * a) b = b.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, natAbs_mul]

@[simp] theorem gcd_mul_right_right (a b : Int) : gcd a (a * b) = a.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, natAbs_mul]

@[simp] theorem gcd_gcd_self_right_left (m n : Int) : gcd m (gcd m n) = gcd m n :=
  Nat.gcd_gcd_self_right_left ..

@[simp] theorem gcd_gcd_self_right_right (m n : Int) : gcd m (gcd n m) = gcd n m :=
  Nat.gcd_gcd_self_right_right ..

@[simp] theorem gcd_gcd_self_left_right (m n : Int) : gcd (gcd n m) m = gcd n m :=
  Nat.gcd_gcd_self_left_right ..

@[simp] theorem gcd_gcd_self_left_left (m n : Int) : gcd (gcd m n) m = gcd m n :=
  Nat.gcd_gcd_self_left_left ..

@[simp] theorem gcd_add_mul_right_right (m n k : Int) : gcd m (n + k * m) = gcd m n :=
  gcd_right_eq_iff.2 (by rintro c ⟨l, rfl⟩; rw [Int.mul_comm, Int.mul_assoc, Int.dvd_add_self_mul])

@[simp] theorem gcd_add_mul_left_right (m n k : Int) : gcd m (n + m * k) = gcd m n := by
  rw [Int.mul_comm, gcd_add_mul_right_right]

@[simp] theorem gcd_mul_right_add_right (m n k : Int) : gcd m (k * m + n) = gcd m n := by
  rw [Int.add_comm, gcd_add_mul_right_right]

@[simp] theorem gcd_mul_left_add_right (m n k : Int) : gcd m (m * k + n) = gcd m n := by
  rw [Int.add_comm, gcd_add_mul_left_right]

@[simp] theorem gcd_add_mul_right_left (m n k : Int) : gcd (n + k * m) m = gcd n m := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]

@[simp] theorem gcd_add_mul_left_left (m n k : Int) : gcd (n + m * k) m = gcd n m := by
  rw [Int.mul_comm, gcd_add_mul_right_left]

@[simp] theorem gcd_mul_right_add_left (m n k : Int) : gcd (k * m + n) m = gcd n m := by
  rw [Int.add_comm, gcd_add_mul_right_left]

@[simp] theorem gcd_mul_left_add_left (m n k : Int) : gcd (m * k + n) m = gcd n m := by
  rw [Int.add_comm, gcd_add_mul_left_left]

@[simp] theorem gcd_add_self_right (m n : Int) : gcd m (n + m) = gcd m n := by
  simpa using gcd_add_mul_right_right _ _ 1

@[simp] theorem gcd_self_add_right (m n : Int) : gcd m (m + n) = gcd m n := by
  simpa using gcd_mul_right_add_right _ _ 1

@[simp] theorem gcd_add_self_left (m n : Int) : gcd (n + m) m = gcd n m := by
  simpa using gcd_add_mul_right_left _ _ 1

@[simp] theorem gcd_self_add_left (m n : Int) : gcd (m + n) m = gcd n m := by
  simpa using gcd_mul_right_add_left _ _ 1

@[simp] theorem gcd_add_left_left_of_dvd {m k : Int} (n : Int) :
    m ∣ k → gcd (k + n) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_add_left m n l

@[simp] theorem gcd_add_right_left_of_dvd {m k : Int} (n : Int) :
    m ∣ k → gcd (n + k) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_add_mul_left_left m n l

@[simp] theorem gcd_add_left_right_of_dvd {n k : Int} (m : Int) :
    n ∣ k → gcd n (k + m) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_add_right n m l

@[simp] theorem gcd_add_right_right_of_dvd {n k : Int} (m : Int) :
    n ∣ k → gcd n (m + k) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_add_mul_left_right n m l

@[simp] theorem gcd_sub_mul_right_right (m n k : Int) : gcd m (n - k * m) = gcd m n := by
  simp [Int.sub_eq_add_neg, ← Int.neg_mul]

@[simp] theorem gcd_sub_mul_left_right (m n k : Int) : gcd m (n - m * k) = gcd m n := by
  rw [Int.mul_comm, gcd_sub_mul_right_right]

@[simp] theorem gcd_mul_right_sub_right (m n k : Int) : gcd m (k * m - n) = gcd m n := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem gcd_mul_left_sub_right (m n k : Int) : gcd m (m * k - n) = gcd m n := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem gcd_sub_mul_right_left (m n k : Int) : gcd (n - k * m) m = gcd n m := by
  rw [gcd_comm, gcd_sub_mul_right_right, gcd_comm]

@[simp] theorem gcd_sub_mul_left_left (m n k : Int) : gcd (n - m * k) m = gcd n m := by
  rw [Int.mul_comm, gcd_sub_mul_right_left]

@[simp] theorem gcd_mul_right_sub_left (m n k : Int) : gcd (k * m - n) m = gcd n m := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem gcd_mul_left_sub_left (m n k : Int) : gcd (m * k - n) m = gcd n m := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem gcd_sub_self_right (m n : Int) : gcd m (n - m) = gcd m n := by
  simpa using gcd_sub_mul_right_right _ _ 1

@[simp] theorem gcd_self_sub_right (m n : Int) : gcd m (m - n) = gcd m n := by
  simpa using gcd_mul_right_sub_right _ _ 1

@[simp] theorem gcd_sub_self_left (m n : Int) : gcd (n - m) m = gcd n m := by
  simpa using gcd_sub_mul_right_left _ _ 1

@[simp] theorem gcd_self_sub_left (m n : Int) : gcd (m - n) m = gcd n m := by
  simpa using gcd_mul_right_sub_left _ _ 1

@[simp] theorem gcd_sub_left_left_of_dvd {m k : Int} (n : Int) :
    m ∣ k → gcd (k - n) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_sub_left m n l

@[simp] theorem gcd_sub_right_left_of_dvd {m k : Int} (n : Int) :
    m ∣ k → gcd (n - k) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_sub_mul_left_left m n l

@[simp] theorem gcd_sub_left_right_of_dvd {n k : Int} (m : Int) :
    n ∣ k → gcd n (k - m) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_sub_right n m l

@[simp] theorem gcd_sub_right_right_of_dvd {n k : Int} (m : Int) :
    n ∣ k → gcd n (m - k) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_sub_mul_left_right n m l

@[simp] theorem gcd_eq_zero_iff {a b : Int} : gcd a b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [gcd_eq_natAbs_gcd_natAbs]

@[simp] theorem gcd_pos_iff {a b : Int} : 0 < gcd a b ↔ a ≠ 0 ∨ b ≠ 0 := by
  simp only [Nat.pos_iff_ne_zero, gcd_eq_zero_iff, ne_eq, Decidable.not_and_iff_not_or_not]

theorem gcd_eq_iff {a b : Int} {g : Nat} :
    gcd a b = g ↔ (g : Int) ∣ a ∧ (g : Int) ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  refine ⟨?_, fun ⟨ha, hb, hc⟩ => Nat.dvd_antisymm ?_ (dvd_gcd ha hb)⟩
  · rintro rfl
    exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ => Int.dvd_coe_gcd⟩
  · exact Int.ofNat_dvd.1 (hc _ (gcd_dvd_left _ _) (gcd_dvd_right _ _))

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def dvdProdDvdOfDvdProd {k m n : Int} (h : k ∣ m * n) :
    { d : { m' // m' ∣ m } × { n' // n' ∣ n } // k = d.1.val * d.2.val } :=
  let d₀ := Nat.dvdProdDvdOfDvdProd (natAbs_mul _ _ ▸ natAbs_dvd_natAbs.2 h)
  if hk : 0 ≤ k then
    ⟨⟨⟨d₀.val.1.val, ofNat_dvd_left.2 d₀.val.1.property⟩,
      ⟨d₀.val.2.val, ofNat_dvd_left.2 d₀.val.2.property⟩⟩,
     (eq_natAbs_of_nonneg hk).trans (by simp [d₀.property])⟩
  else
    ⟨⟨⟨-d₀.val.1.val, by simpa using ofNat_dvd_left.2 d₀.val.1.property⟩,
      ⟨d₀.val.2.val, ofNat_dvd_left.2 d₀.val.2.property⟩⟩,
     (eq_neg_natAbs_of_nonpos (Int.le_of_not_le hk)).trans (by simp [d₀.property, Int.neg_mul])⟩

protected theorem dvd_mul {a b c : Int} : c ∣ a * b ↔ ∃ c₁ c₂, c₁ ∣ a ∧ c₂ ∣ b ∧ c₁ * c₂ = c := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩, rfl⟩ := dvdProdDvdOfDvdProd h
    exact ⟨k₁, k₂, hk₁, hk₂, rfl⟩
  · rintro ⟨k₁, k₂, hk₁, hk₂, rfl⟩
    exact Int.mul_dvd_mul hk₁ hk₂

theorem gcd_mul_right_dvd_mul_gcd (k m n : Int) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  simp [gcd_eq_natAbs_gcd_natAbs, natAbs_mul, Nat.gcd_mul_right_dvd_mul_gcd]

theorem gcd_mul_left_dvd_mul_gcd (k m n : Int) : gcd (m * n) k ∣ gcd m k * gcd n k := by
  simp [gcd_eq_natAbs_gcd_natAbs, natAbs_mul, Nat.gcd_mul_left_dvd_mul_gcd]

theorem dvd_gcd_mul_iff_dvd_mul {k n m : Int} : k ∣ gcd k n * m ↔ k ∣ n * m := by
  simp [← natAbs_dvd_natAbs, natAbs_mul, Nat.dvd_gcd_mul_iff_dvd_mul, gcd_eq_natAbs_gcd_natAbs]

theorem dvd_mul_gcd_iff_dvd_mul {k n m : Int} : k ∣ n * gcd k m ↔ k ∣ n * m := by
  simp [← natAbs_dvd_natAbs, natAbs_mul, Nat.dvd_mul_gcd_iff_dvd_mul, gcd_eq_natAbs_gcd_natAbs]

theorem dvd_gcd_mul_gcd_iff_dvd_mul {k n m : Int} : k ∣ gcd k n * gcd k m ↔ k ∣ n * m := by
  simp [← natAbs_dvd_natAbs, natAbs_mul, Nat.dvd_gcd_mul_gcd_iff_dvd_mul, gcd_eq_natAbs_gcd_natAbs]

theorem gcd_eq_one_iff {m n : Int} : gcd m n = 1 ↔ ∀ c, c ∣ m → c ∣ n → c ∣ 1 := by
  simp [gcd_eq_iff]

theorem gcd_mul_right_right_of_gcd_eq_one {n m k : Int} : gcd n m = 1 → gcd n (m * k) = gcd n k := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_mul_right_right_of_gcd_eq_one

theorem gcd_mul_left_right_of_gcd_eq_one {n m k : Int} : gcd n m = 1 → gcd n (k * m) = gcd n k := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_mul_left_right_of_gcd_eq_one

theorem gcd_mul_right_left_of_gcd_eq_one {n m k : Int} : gcd n m = 1 → gcd (n * k) m = gcd k m := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_mul_right_left_of_gcd_eq_one

theorem gcd_mul_left_left_of_gcd_eq_one {n m k : Int} : gcd n m = 1 → gcd (k * n) m = gcd k m := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_mul] using Nat.gcd_mul_left_left_of_gcd_eq_one

theorem gcd_pow_left_of_gcd_eq_one {n m : Int} {k : Nat} : gcd n m = 1 → gcd (n ^ k) m = 1 := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_pow] using Nat.gcd_pow_left_of_gcd_eq_one

theorem gcd_pow_right_of_gcd_eq_one {n m : Int} {k : Nat} (h : gcd n m = 1) : gcd n (m ^ k) = 1 := by
  rw [gcd_comm, gcd_pow_left_of_gcd_eq_one (gcd_comm _ _ ▸ h)]

theorem pow_gcd_pow_of_gcd_eq_one {n m : Int} {k l : Nat} (h : gcd n m = 1) : gcd (n ^ k) (m ^ l) = 1 :=
  gcd_pow_left_of_gcd_eq_one (gcd_pow_right_of_gcd_eq_one h)

theorem gcd_ediv_gcd_ediv_gcd_of_ne_zero_left {n m : Int} (h : n ≠ 0) :
    gcd (n / gcd n m) (m / gcd n m) = 1 := by
  rw [gcd_ediv (gcd_dvd_left _ _) (gcd_dvd_right _ _), natAbs_ofNat,
    Nat.div_self (gcd_pos_of_ne_zero_left _ h)]

theorem gcd_ediv_gcd_ediv_gcd_of_ne_zero_right {n m : Int} (h : m ≠ 0) :
    gcd (n / gcd n m) (m / gcd n m) = 1 := by
  rw [gcd_ediv (gcd_dvd_left _ _) (gcd_dvd_right _ _), natAbs_ofNat,
    Nat.div_self (gcd_pos_of_ne_zero_right _ h)]

theorem gcd_ediv_gcd_ediv_gcd {i j : Int} (h : 0 < gcd i j) : gcd (i / gcd i j) (j / gcd i j) = 1 :=
  match gcd_pos_iff.1 h with
  | Or.inl h => gcd_ediv_gcd_ediv_gcd_of_ne_zero_left h
  | Or.inr h => gcd_ediv_gcd_ediv_gcd_of_ne_zero_right h

theorem pow_gcd_pow {n m : Int} {k : Nat} : gcd (n ^ k) (m ^ k) = (gcd n m) ^ k := by
  simpa [gcd_eq_natAbs_gcd_natAbs, natAbs_pow] using Nat.pow_gcd_pow

theorem pow_dvd_pow_iff {a b : Int} {n : Nat} (h : n ≠ 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  simp [← natAbs_dvd_natAbs, natAbs_pow, Nat.pow_dvd_pow_iff h]

/-! ## lcm -/

/--
Computes the least common multiple of two integers as a natural number. The LCM of two integers is
the smallest natural number that's evenly divisible by the absolute values of both.

Examples:
 * `Int.lcm 9 6 = 18`
 * `Int.lcm 9 (-6) = 18`
 * `Int.lcm 9 3 = 9`
 * `Int.lcm 9 (-3) = 9`
 * `Int.lcm 0 3 = 0`
 * `Int.lcm (-3) 0 = 0`
-/
def lcm (m n : Int) : Nat := m.natAbs.lcm n.natAbs

theorem lcm_eq_natAbs_lcm_natAbs (m n : Int) : lcm m n = Nat.lcm m.natAbs n.natAbs := rfl

theorem lcm_eq_mul_div (m n : Int) : lcm m n = m.natAbs * n.natAbs / gcd m n := by
  simp [lcm_eq_natAbs_lcm_natAbs, Nat.lcm_eq_mul_div, gcd_eq_natAbs_gcd_natAbs]

@[simp] theorem gcd_mul_lcm (m n : Int) : gcd m n * lcm m n = m.natAbs * n.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, lcm_eq_natAbs_lcm_natAbs]

@[simp] theorem lcm_mul_gcd (m n : Int) : lcm m n * gcd m n = m.natAbs * n.natAbs := by
  simp [gcd_eq_natAbs_gcd_natAbs, lcm_eq_natAbs_lcm_natAbs]

@[simp] theorem lcm_dvd_natAbs_mul (m n : Int) : lcm m n ∣ m.natAbs * n.natAbs := ⟨gcd m n, by simp⟩
@[simp] theorem gcd_dvd_natAbs_mul (m n : Int) : gcd m n ∣ m.natAbs * n.natAbs := ⟨lcm m n, by simp⟩

@[simp] theorem lcm_dvd_mul (m n : Int) : (lcm m n : Int) ∣ m * n := by
  simp [ofNat_dvd_left, natAbs_mul]

@[simp] theorem gcd_dvd_mul (m n : Int) : (gcd m n : Int) ∣ m * n := by
  simp [ofNat_dvd_left, natAbs_mul]

theorem natAbs_dvd_lcm_left (a b : Int) : a.natAbs ∣ lcm a b := Nat.dvd_lcm_left ..
theorem natAbs_dvd_lcm_right (a b : Int) : b.natAbs ∣ lcm a b := Nat.dvd_lcm_right ..

theorem dvd_lcm_left (a b : Int) : a ∣ lcm a b := by
  simp [ofNat_dvd_right, natAbs_dvd_lcm_left]

theorem dvd_lcm_right (a b : Int) : b ∣ lcm a b := by
  simp [ofNat_dvd_right, natAbs_dvd_lcm_right]

theorem lcm_le_natAbs_mul {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0) : lcm a b ≤ a.natAbs * b.natAbs :=
  Nat.lcm_le_mul (natAbs_pos.2 ha) (natAbs_pos.2 hb)

theorem gcd_le_natAbs_mul {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0) : gcd a b ≤ a.natAbs * b.natAbs :=
  Nat.gcd_le_mul (natAbs_pos.2 ha) (natAbs_pos.2 hb)

theorem lcm_comm (a b : Int) : lcm a b = lcm b a := Nat.lcm_comm ..

@[simp] theorem one_lcm {a : Int} : lcm 1 a = a.natAbs := by simp [lcm_eq_natAbs_lcm_natAbs]
@[simp] theorem lcm_one {a : Int} : lcm a 1 = a.natAbs := by simp [lcm_eq_natAbs_lcm_natAbs]

@[simp] theorem zero_lcm {a : Int} : lcm 0 a = 0 := by simp [lcm_eq_natAbs_lcm_natAbs]
@[simp] theorem lcm_zero {a : Int} : lcm a 0 = 0 := by simp [lcm_eq_natAbs_lcm_natAbs]

theorem lcm_one_left (a : Int) : lcm 1 a = a.natAbs := by simp
theorem lcm_one_right (a : Int) : lcm a 1 = a.natAbs := by simp

theorem lcm_zero_left (a : Int) : lcm 0 a = 0 := by simp
theorem lcm_zero_right (a : Int) : lcm a 0 = 0 := by simp

@[simp] theorem lcm_self {a : Int} : lcm a a = a.natAbs := Nat.lcm_self _

@[simp] theorem neg_lcm {a b : Int} : lcm (-a) b = lcm a b := by simp [lcm_eq_natAbs_lcm_natAbs]
@[simp] theorem lcm_neg {a b : Int} : lcm a (-b) = lcm a b := by simp [lcm_eq_natAbs_lcm_natAbs]

@[simp, norm_cast] protected theorem lcm_natCast_natCast (a b : Nat) :
    lcm (a : Int) (b : Int) = Nat.lcm a b := by
  simp [lcm_eq_natAbs_lcm_natAbs]

theorem natAbs_le_lcm_left (a : Int) (hb : b ≠ 0) : a.natAbs ≤ lcm a b :=
  Nat.le_lcm_left a.natAbs (natAbs_pos.2 hb)

theorem natAbs_le_lcm_right (b : Int) (ha : a ≠ 0) : b.natAbs ≤ lcm a b :=
  Nat.le_lcm_right b.natAbs (natAbs_pos.2 ha)

theorem le_lcm_left (a : Int) (hb : b ≠ 0) : a ≤ (lcm a b : Int) :=
  Int.le_trans le_natAbs (ofNat_le.2 (natAbs_le_lcm_left a hb))

theorem le_lcm_right (b : Int) (ha : a ≠ 0) : b ≤ (lcm a b : Int) :=
  Int.le_trans le_natAbs (ofNat_le.2 (natAbs_le_lcm_right b ha))

theorem coe_lcm_dvd {a b c : Int} (ha : a ∣ c) (hb : b ∣ c) : (lcm a b : Int) ∣ c :=
  ofNat_dvd_left.2 (Nat.lcm_dvd (natAbs_dvd_natAbs.2 ha) (natAbs_dvd_natAbs.2 hb))

theorem lcm_dvd {a b : Int} {c : Nat} (ha : a ∣ (c : Int)) (hb : b ∣ (c : Int)) : lcm a b ∣ c :=
  ofNat_dvd.1 (coe_lcm_dvd ha hb)

theorem coe_lcm_dvd_iff {a b c : Int} : (lcm a b : Int) ∣ c ↔ a ∣ c ∧ b ∣ c :=
  ⟨fun h => ⟨Int.dvd_trans (dvd_lcm_left _ _) h, Int.dvd_trans (dvd_lcm_right _ _ ) h⟩,
   fun ⟨ha, hb⟩ => coe_lcm_dvd ha hb⟩

theorem lcm_dvd_iff {a b : Int} {c : Nat} : lcm a b ∣ c ↔ a ∣ (c : Int) ∧ b ∣ (c : Int) := by
  rw [← ofNat_dvd, coe_lcm_dvd_iff]

theorem lcm_eq_natAbs_left_iff_dvd : lcm a b = a.natAbs ↔ b ∣ a := by
  simp [lcm_eq_natAbs_lcm_natAbs, Nat.lcm_eq_left_iff_dvd]

theorem lcm_eq_natAbs_right_iff_dvd : lcm a b = b.natAbs ↔ a ∣ b := by
  simp [lcm_eq_natAbs_lcm_natAbs, Nat.lcm_eq_right_iff_dvd]

theorem lcm_eq_left_iff_dvd (ha : 0 ≤ a) : lcm a b = a ↔ b ∣ a := by
  rw (occs := [2]) [eq_natAbs_of_nonneg ha]
  simp [ofNat_inj, lcm_eq_natAbs_left_iff_dvd]

theorem lcm_eq_right_iff_dvd (hb : 0 ≤ b) : lcm a b = b ↔ a ∣ b := by
  rw [lcm_comm, lcm_eq_left_iff_dvd hb]

theorem lcm_assoc (a b c : Int) : lcm (lcm a b) c = lcm a (lcm b c) := Nat.lcm_assoc ..

theorem lcm_mul_left (m n k : Int) : lcm (m * n) (m * k) = m.natAbs * lcm n k := by
  simp [lcm_eq_natAbs_lcm_natAbs, Nat.lcm_mul_left, natAbs_mul]

theorem lcm_mul_right (m n k : Int) : lcm (m * n) (k * n) = lcm m k * n.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, Nat.lcm_mul_right, natAbs_mul]

theorem lcm_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  apply Nat.lcm_ne_zero <;> simpa

theorem lcm_pos : m ≠ 0 → n ≠ 0 → 0 < lcm m n := by
  simpa [← Nat.pos_iff_ne_zero] using lcm_ne_zero

theorem eq_zero_of_lcm_eq_zero (h : lcm m n = 0) : m = 0 ∨ n = 0 := by
  have := lcm_ne_zero (m := m) (n := n); omega

@[simp] theorem lcm_eq_zero_iff : lcm m n = 0 ↔ m = 0 ∨ n = 0 :=
  ⟨eq_zero_of_lcm_eq_zero, by rintro (rfl|rfl) <;> simp⟩

@[simp] theorem lcm_pos_iff : 0 < lcm m n ↔ m ≠ 0 ∧ n ≠ 0 := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, lcm_eq_zero_iff, not_or]

theorem lcm_eq_iff {n m : Int} {l : Nat} :
    lcm n m = l ↔ n ∣ (l : Int) ∧ m ∣ (l : Int) ∧ (∀ c, n ∣ c → m ∣ c → (l : Int) ∣ c) := by
  refine ⟨?_, fun ⟨hn, hm, hl⟩ => Nat.dvd_antisymm (lcm_dvd hn hm) ?_⟩
  · rintro rfl
    exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _, fun _ => coe_lcm_dvd⟩
  · exact Int.ofNat_dvd.1 (hl _ (dvd_lcm_left _ _) (dvd_lcm_right _ _))

theorem lcm_ediv {a b c : Int} (ha : c ∣ a) (hb : c ∣ b) :
    lcm (a / c) (b / c) = lcm a b / c.natAbs := by
  rw [lcm_eq_natAbs_lcm_natAbs, natAbs_ediv_of_dvd ha, natAbs_ediv_of_dvd hb,
    Nat.lcm_div (by simpa) (by simpa), lcm_eq_natAbs_lcm_natAbs]

theorem lcm_dvd_lcm_of_dvd_left {a b : Int} (c : Int) (h : a ∣ b) : lcm a c ∣ lcm b c :=
  Nat.lcm_dvd_lcm_of_dvd_left _ (by simpa)

theorem lcm_dvd_lcm_of_dvd_right {a b : Int} (c : Int) (h : a ∣ b) : lcm c a ∣ lcm c b :=
  Nat.lcm_dvd_lcm_of_dvd_right _ (by simpa)

theorem lcm_dvd_lcm_mul_left_left (a b c : Int) : lcm a b ∣ lcm (c * a) b := by
  simpa [lcm_eq_natAbs_lcm_natAbs, natAbs_mul] using Nat.lcm_dvd_lcm_mul_left_left ..

theorem lcm_dvd_lcm_mul_right_left (a b c : Int) : lcm a b ∣ lcm (a * c) b := by
  simpa [lcm_eq_natAbs_lcm_natAbs, natAbs_mul] using Nat.lcm_dvd_lcm_mul_right_left ..

theorem lcm_dvd_lcm_mul_left_right (a b c : Int) : lcm a b ∣ lcm a (c * b) := by
  simpa [lcm_eq_natAbs_lcm_natAbs, natAbs_mul] using Nat.lcm_dvd_lcm_mul_left_right ..

theorem lcm_dvd_lcm_mul_right_right (a b c : Int) : lcm a b ∣ lcm a (b * c) := by
  simpa [lcm_eq_natAbs_lcm_natAbs, natAbs_mul] using Nat.lcm_dvd_lcm_mul_right_right ..

theorem lcm_eq_natAbs_left (h : b ∣ a) : lcm a b = a.natAbs :=
  lcm_eq_natAbs_left_iff_dvd.2 h

theorem lcm_eq_natAbs_right (h : a ∣ b) : lcm a b = b.natAbs :=
  lcm_eq_natAbs_right_iff_dvd.2 h

theorem lcm_eq_left (ha : 0 ≤ a) (h : b ∣ a) : lcm a b = a :=
  (lcm_eq_left_iff_dvd ha).2 h

theorem lcm_eq_right (hb : 0 ≤ b) (h : a ∣ b) : lcm a b = b :=
  (lcm_eq_right_iff_dvd hb).2 h

@[simp] theorem lcm_mul_left_left (a b : Int) : lcm (a * b) b = a.natAbs * b.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul]

@[simp] theorem lcm_mul_left_right (a b : Int) : lcm a (b * a) = b.natAbs * a.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul]

@[simp] theorem lcm_mul_right_left (a b : Int) : lcm (b * a) b = b.natAbs * a.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul]

@[simp] theorem lcm_mul_right_right (a b : Int) : lcm a (a * b) = a.natAbs * b.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul]

@[simp] theorem lcm_lcm_self_right_left (m n : Int) : lcm m (lcm m n) = lcm m n :=
  Nat.lcm_lcm_self_right_left ..

@[simp] theorem lcm_lcm_self_right_right (m n : Int) : lcm m (lcm n m) = lcm m n :=
  Nat.lcm_lcm_self_right_right ..

@[simp] theorem lcm_lcm_self_left_right (m n : Int) : lcm (lcm n m) m = lcm n m :=
  Nat.lcm_lcm_self_left_right ..

@[simp] theorem lcm_lcm_self_left_left (m n : Int) : lcm (lcm m n) m = lcm n m :=
  Nat.lcm_lcm_self_left_left ..

theorem lcm_eq_mul_iff {m n : Int} : lcm m n = m.natAbs * n.natAbs ↔ m = 0 ∨ n = 0 ∨ gcd m n = 1 := by
  simp [lcm_eq_natAbs_lcm_natAbs, Nat.lcm_eq_mul_iff, gcd_eq_natAbs_gcd_natAbs]

@[simp] theorem lcm_eq_one_iff {m n : Int} : lcm m n = 1 ↔ m ∣ 1 ∧ n ∣ 1 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨ha, hb⟩ => Nat.eq_one_of_dvd_one (lcm_dvd ha hb)⟩ <;>
    simp [← natAbs_dvd_natAbs, ← h, natAbs_dvd_lcm_left, natAbs_dvd_lcm_right]

theorem lcm_mul_right_dvd_mul_lcm (k m n : Nat) : lcm k (m * n) ∣ lcm k m * lcm k n := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul, Nat.lcm_mul_right_dvd_mul_lcm]

theorem lcm_mul_left_dvd_mul_lcm (k m n : Nat) : lcm (m * n) k ∣ lcm m k * lcm n k := by
  simpa [lcm_comm, Nat.mul_comm] using lcm_mul_right_dvd_mul_lcm _ _ _

theorem lcm_dvd_mul_self_left_iff_dvd_mul {k n m : Nat} : lcm k n ∣ k * m ↔ n ∣ k * m := by
  simp [← natAbs_dvd_natAbs, natAbs_mul, Nat.lcm_dvd_mul_self_left_iff_dvd_mul,
    lcm_eq_natAbs_lcm_natAbs]

theorem lcm_dvd_mul_self_right_iff_dvd_mul {k m n : Nat} : lcm n k ∣ m * k ↔ n ∣ m * k := by
  rw [lcm_comm, Nat.mul_comm m, lcm_dvd_mul_self_left_iff_dvd_mul]

theorem lcm_mul_right_right_eq_mul_of_lcm_eq_mul {n m k : Int} (h : lcm n m = n.natAbs * m.natAbs) :
    lcm n (m * k) = lcm n k * m.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul, Nat.lcm_mul_right_right_eq_mul_of_lcm_eq_mul h]

theorem lcm_mul_left_right_eq_mul_of_lcm_eq_mul {n m k} (h : lcm n m = n.natAbs * m.natAbs) :
    lcm n (k * m) = lcm n k * m.natAbs := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul, Nat.lcm_mul_left_right_eq_mul_of_lcm_eq_mul h]

theorem lcm_mul_right_left_eq_mul_of_lcm_eq_mul {n m k} (h : lcm n m = n.natAbs * m.natAbs) :
    lcm (n * k) m = n.natAbs * lcm k m := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul, Nat.lcm_mul_right_left_eq_mul_of_lcm_eq_mul h]

theorem lcm_mul_left_left_eq_mul_of_lcm_eq_mul {n m k} (h : lcm n m = n.natAbs * m.natAbs) :
    lcm (k * n) m = n.natAbs * lcm k m := by
  simp [lcm_eq_natAbs_lcm_natAbs, natAbs_mul, Nat.lcm_mul_left_left_eq_mul_of_lcm_eq_mul h]

theorem pow_lcm_pow {n m : Int} {k : Nat} : lcm (n ^ k) (m ^ k) = (lcm n m) ^ k := by
  simpa [lcm_eq_natAbs_lcm_natAbs, natAbs_pow] using Nat.pow_lcm_pow

end Int
