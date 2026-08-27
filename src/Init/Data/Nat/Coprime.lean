/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module
prelude

public import Init.Data.Nat.Gcd
import Init.Data.Nat.Dvd

public section

/-!
# Definitions and properties of `coprime`
-/

namespace Nat

/-!
### `coprime`
-/

/-- `m` and `n` are coprime, or relatively prime, if their `gcd` is 1. -/
@[reducible, expose] def Coprime (m n : Nat) : Prop := gcd m n = 1

-- if we don't inline this, then the compiler computes the GCD even if it already has it
@[inline] instance (m n : Nat) : Decidable (Coprime m n) := inferInstanceAs (Decidable (_ = 1))

theorem coprime_iff_gcd_eq_one : Coprime m n ↔ gcd m n = 1 := .rfl

theorem Coprime.gcd_eq_one : Coprime m n → gcd m n = 1 := id

theorem Coprime.symm : Coprime n m → Coprime m n := (gcd_comm m n).trans

theorem coprime_comm : Coprime n m ↔ Coprime m n := ⟨Coprime.symm, Coprime.symm⟩

theorem Coprime.dvd_of_dvd_mul_right (H1 : Coprime k n) (H2 : k ∣ m * n) : k ∣ m := by
  have t := dvd_gcd (Nat.dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, Nat.mul_one] at t

theorem Coprime.dvd_of_dvd_mul_left (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
  H1.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])

theorem Coprime.gcd_mul_left_cancel (m : Nat) (H : Coprime k n) : gcd (k * m) n = gcd m n :=
  have H1 : Coprime (gcd (k * m) n) k := by
    rw [Coprime, Nat.gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  Nat.dvd_antisymm
    (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
    (gcd_dvd_gcd_mul_left_left _ _ _)

theorem Coprime.gcd_mul_right_cancel (m : Nat) (H : Coprime k n) : gcd (m * k) n = gcd m n := by
  rw [Nat.mul_comm m k, H.gcd_mul_left_cancel m]

theorem Coprime.gcd_mul_left_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (k * n) = gcd m n := by
  rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem Coprime.gcd_mul_right_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (n * k) = gcd m n := by
  rw [Nat.mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd
    (H : 0 < gcd m n) : Coprime (m / gcd m n) (n / gcd m n) := by
  rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]

theorem not_coprime_of_dvd_of_dvd (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬ Coprime m n :=
  fun co => Nat.not_le_of_gt dgt1 <| Nat.le_of_dvd Nat.zero_lt_one <| by
    rw [← co.gcd_eq_one]; exact dvd_gcd Hm Hn

theorem exists_coprime (m n : Nat) :
    ∃ m' n', Coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n := by
  cases eq_zero_or_pos (gcd m n) with
  | inl h0 =>
    rw [gcd_eq_zero_iff] at h0
    refine ⟨1, 1, gcd_one_left 1, ?_⟩
    simp [h0]
  | inr hpos =>
    exact ⟨_, _, coprime_div_gcd_div_gcd hpos,
      (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
      (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' (H : 0 < gcd m n) :
    ∃ g m' n', 0 < g ∧ Coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime m n; ⟨_, m', n', H, h⟩

theorem Coprime.mul_left (H1 : Coprime m k) (H2 : Coprime n k) : Coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem Coprime.mul_right (H1 : Coprime k m) (H2 : Coprime k n) : Coprime k (m * n) :=
  (H1.symm.mul_left H2.symm).symm

theorem Coprime.coprime_dvd_left (H1 : m ∣ k) (H2 : Coprime k n) : Coprime m n := by
  apply eq_one_of_dvd_one
  rw [Coprime] at H2
  have := Nat.gcd_dvd_gcd_of_dvd_left n H1
  rwa [← H2]

theorem Coprime.coprime_dvd_right (H1 : n ∣ m) (H2 : Coprime k m) : Coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem Coprime.coprime_mul_left (H : Coprime (k * m) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right (H : Coprime (m * k) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_mul_left_right (H : Coprime m (k * n)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right_right (H : Coprime m (n * k)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_div_left (cmn : Coprime m n) (dvd : a ∣ m) : Coprime (m / a) n := by
  match eq_zero_or_pos a with
  | .inl h0 =>
    rw [h0] at dvd
    rw [Nat.eq_zero_of_zero_dvd dvd] at cmn ⊢
    simp; assumption
  | .inr hpos =>
    let ⟨k, hk⟩ := dvd
    rw [hk, Nat.mul_div_cancel_left _ hpos]
    rw [hk] at cmn
    exact cmn.coprime_mul_left

theorem Coprime.coprime_div_right (cmn : Coprime m n) (dvd : a ∣ n) : Coprime m (n / a) :=
  (cmn.symm.coprime_div_left dvd).symm

theorem coprime_mul_iff_left : Coprime (m * n) k ↔ Coprime m k ∧ Coprime n k :=
  ⟨fun h => ⟨h.coprime_mul_right, h.coprime_mul_left⟩,
   fun ⟨h, _⟩ => by rwa [coprime_iff_gcd_eq_one, h.gcd_mul_left_cancel n]⟩

theorem coprime_mul_iff_right : Coprime k (m * n) ↔ Coprime k m ∧ Coprime k n := by
  rw [@coprime_comm k, @coprime_comm k, @coprime_comm k, coprime_mul_iff_left]

theorem Coprime.gcd_left (k : Nat) (hmn : Coprime m n) : Coprime (gcd k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_right k m

theorem Coprime.gcd_right (k : Nat) (hmn : Coprime m n) : Coprime m (gcd k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_right k n

theorem Coprime.gcd_both (k l : Nat) (hmn : Coprime m n) : Coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l

theorem Coprime.mul_dvd_of_dvd_of_dvd (hmn : Coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

@[simp] theorem coprime_zero_left (n : Nat) : Coprime 0 n ↔ n = 1 := by simp [Coprime]

@[simp] theorem coprime_zero_right (n : Nat) : Coprime n 0 ↔ n = 1 := by simp [Coprime]

theorem coprime_one_left : ∀ n, Coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right

@[simp] theorem coprime_one_left_eq_true (n) : Coprime 1 n = True := eq_true (coprime_one_left _)

@[simp] theorem coprime_one_right_eq_true (n) : Coprime n 1 = True := eq_true (coprime_one_right _)

@[simp] theorem coprime_self (n : Nat) : Coprime n n ↔ n = 1 := by simp [Coprime]

theorem Coprime.pow_left (n : Nat) (H1 : Coprime m k) : Coprime (m ^ n) k := by
  induction n with
  | zero => exact coprime_one_left _
  | succ n ih => have hm := H1.mul_left ih; rwa [Nat.pow_succ, Nat.mul_comm]

theorem Coprime.pow_right (n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem Coprime.pow {k l : Nat} (m n : Nat) (H1 : Coprime k l) : Coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

theorem Coprime.eq_one_of_dvd {k m : Nat} (H : Coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]

theorem Coprime.gcd_mul (k : Nat) (h : Coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
  Nat.dvd_antisymm
    (gcd_mul_right_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd
      (gcd_dvd_gcd_mul_right_right ..)
      (gcd_dvd_gcd_mul_left_right ..))

theorem Coprime.mul_gcd (h : Coprime m n) (k : Nat) : gcd (m * n) k = gcd m k * gcd n k := by
  rw [gcd_comm, h.gcd_mul, gcd_comm k, gcd_comm k]

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul
    (cop : Coprime c d) (h : a * b = c * d) : a.gcd c * b.gcd c = c := by
  apply Nat.dvd_antisymm
  · apply ((cop.gcd_left _).mul_left (cop.gcd_left _)).dvd_of_dvd_mul_right
    rw [← h]
    apply Nat.mul_dvd_mul (gcd_dvd ..).1 (gcd_dvd ..).1
  · rw [gcd_comm a, gcd_comm b]
    refine Nat.dvd_trans ?_ (gcd_mul_right_dvd_mul_gcd ..)
    rw [h, gcd_mul_right_right d c]; apply Nat.dvd_refl
