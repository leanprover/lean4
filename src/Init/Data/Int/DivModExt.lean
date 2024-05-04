/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Joe Hendrix
-/
prelude
import Init.Data.Int.DivModLemmas
import Init.Data.Nat.Lemmas

/-
Int div and mod lemmas that omega does not depend on
-/
namespace Int

/-! ediv -/

theorem ediv_ofNat_negSucc (m n : Nat) : m / -[n+1] = -ofNat (m / Nat.succ n) := rfl
theorem ediv_negSucc_zero (m : Nat) : -[m+1] / 0 = 0 := rfl
theorem ediv_negSucc_succ (m n : Nat) : -[m+1] / (n + 1 : Nat) = -((m / (n + 1)) : Nat) + (-1) := by
  simp [HDiv.hDiv, Div.div, Int.ediv, Int.negSucc_coe', Int.sub_eq_add_neg]
theorem ediv_negSucc_negSucc (m n : Nat) : -[m+1] / -[n+1] = ((m / (n + 1) + 1) : Nat) := rfl

/-! emod -/

theorem emod_ofNat   (a : Nat) (b : Int) : Nat.cast a % b = Nat.cast (a % b.natAbs) := rfl
theorem emod_negSucc (a : Nat) (b : Int) : -[a+1] % b = (b.natAbs : Int) - (a % b.natAbs + 1) := rfl

theorem emod_neg_iff (m n : Int) : m % n < 0 ↔ (m < 0 ∧ n = 0) := by
  change Int.emod m n < 0 ↔ (m < 0 ∧ n = 0)
  match m with
  | ofNat m =>
    simp [-ofNat_emod, Int.emod, ofNat_not_neg]
  | -[m+1] =>
    simp [-ofNat_emod, -Int.natCast_add, Int.emod, Int.subNatNat_eq_coe, negSucc_lt_zero, Int.sub_lt_iff]
    apply Iff.intro
    · intro p
      replace p := Nat.le_of_succ_le_succ p
      by_cases nz : n = 0
      · exact nz
      · have q : n.natAbs > 0 := Int.natAbs_pos.mpr nz
        have r : m % n.natAbs < n.natAbs := Nat.mod_lt _ q
        exact False.elim (Nat.not_le_of_gt r p)
    · intro p
      simp [p]

theorem emod_lt (a b : Int) (h : b ≠ 0) : a % b < Int.natAbs b := by
  rw [emod_as_nat_mod]
  by_cases p : a ≥ 0
  · simp [p, -Int.ofNat_emod]
    exact Nat.mod_lt _ (by omega)
  · simp [p, -Int.ofNat_emod]
    apply Int.sub_lt_self
    apply Int.succ_ofNat_pos

@[simp] theorem sub_emod_self_left (n y : Int) : (n - y) % n = (-y) % n := by
  simp [Int.sub_eq_add_neg]

/-! dvd -/

@[simp] theorem dvd_natCast_natCast (a b : Nat) : (a : Int) ∣ (b : Int) ↔ a ∣ b := by
  simp [Int.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, mod, Int.emod_ofNat, -emod_ofNat]
  apply Int.ofNat_inj

@[simp] theorem dvd_negSucc (a : Int) (b : Nat) : a ∣ -[b +1] ↔ a ∣ (b+1 : Nat) := by
  simp only [Int.dvd_def]
  apply Iff.intro
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    simp only [Int.mul_neg, ← p]
    rfl
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    simp only [Int.mul_neg, ← p]
    rfl

@[simp] theorem negSucc_dvd (a : Nat) (b : Int) : -[a +1] ∣ b ↔ (((a+1 : Nat) : Int) ∣ b) := by
  apply Iff.intro
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    match c with
    | .ofNat 0 =>
      simp_all
    | .ofNat (.succ c) =>
      simp_all [-natCast_add, Int.mul_neg]
    | -[c+1] =>
      simp_all [-natCast_add, Int.mul_neg]
  · intro ⟨c, p⟩
    apply Exists.intro (-c)
    match c with
    | .ofNat 0 =>
      simp_all
    | .ofNat (.succ c) =>
      simp_all [-natCast_add, Int.mul_neg]
    | -[c+1] =>
      simp_all [-natCast_add, Int.mul_neg]

/-! div -/

theorem div_eq_ediv' (a b : Int) : Int.div a b = a / b + ite (a < 0 ∧ ¬(b ∣ a)) (sign b) 0  :=
  match a, b with
  | (a : Nat), ofNat b => rfl
  | (a : Nat), -[b +1] => by
    simp [Int.div, ediv_ofNat_negSucc, ofNat_not_neg]
  | -[a +1], 0 => by
    simp [Int.div, ediv_negSucc_zero]
  | -[a +1], (b+1 : Nat) => by
    have q : ¬(Nat.cast ((b + 1) : Nat) = (0 : Int)) := by
      norm_cast
    simp [-Int.natCast_add] at q
    simp [Int.div, ediv_negSucc_succ, Nat.succ_div,
          Int.negSucc_lt_zero, q, true_and,
          -Int.natCast_add]
    split <;> rename_i pg
    · simp [Int.neg_add]
    · simp [Int.neg_add, Int.neg_add_cancel_right]
  | -[m +1], -[n +1] => by
    simp [Int.div, ediv_negSucc_negSucc,
      Int.negSucc_lt_zero,
      -ofNat_ediv, -natCast_add,
      Nat.succ_div]
    split <;> rename_i h
    . simp
    · simp [Int.add_neg_cancel_right]

/-! mod -/

theorem mod_eq_emod' (a b : Int) : Int.mod a b = a % b - b * ite (a < 0 ∧ ¬(b ∣ a)) (sign b) 0 := by
  simp [emod_def, mod_def, div_eq_ediv',
        Int.mul_add, Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]


@[simp] theorem emod_mod (a b : Int) : (mod a b) % b = a % b := by
  simp [Int.mod_eq_emod', Int.sub_eq_add_neg, Int.neg_mul_eq_mul_neg]

@[simp] theorem mod_emod (m n : Int) : Int.mod (m % n) n = m % n := by
  simp_all [mod_eq_emod', emod_neg_iff]

@[simp] theorem mod_mod (m n : Int) : Int.mod (Int.mod m n) n = Int.mod m n := by
  simp only [mod_eq_emod' m n]
  split
  · rename_i mnn
    rw [mod_eq_emod']
    by_cases q : OfNat.ofNat 0 < natAbs n <;>
    simp_all [Int.sub_eq_add_neg, Int.mul_sign, add_emod_of_dvd, Int.add_lt_iff,
              Int.natAbs_pos, Int.emod_lt, Int.dvd_add_left]
  · simp [mod_emod]


/-! fdiv -/

theorem fdiv_eq_ediv' (a b : Int) : Int.fdiv a b = a / b + if b < 0 ∧ ¬(b ∣ a) then (-1) else 0 := by
  match a, b with
  | 0,       b       =>
    simp [Int.fdiv, Int.dvd_zero]
  | ofNat (Nat.succ m), ofNat n =>
    simp [Int.fdiv, Int.ofNat_not_neg]
  | ofNat (Nat.succ m), -[n+1] =>
    simp only [fdiv,Int.negSucc_lt_zero, true_and, Int.ofNat_eq_coe, ediv_ofNat_negSucc,
               Int.negSucc_dvd, Int.dvd_natCast_natCast, ite_not,
               Nat.succ_div, Nat.succ_eq_add_one]
    split <;> rename_i h
    · rw [Int.add_zero]; rfl
    · rw [← Int.neg_add]; rfl
  | -[_+1],  0       =>
    simp
  | -[m+1],  ofNat (Nat.succ n) => rfl
  | -[m+1],  -[n+1]  =>
    simp only [Int.fdiv, Int.ediv_negSucc_negSucc, Nat.succ_div, Int.negSucc_lt_zero, true_and,
      Int.dvd_negSucc, Int.negSucc_dvd, Int.dvd_natCast_natCast]
    split <;> rename_i h
    · simp only [Int.add_zero]
      rfl
    · simp only [Int.natCast_add, Int.Nat.cast_ofNat_Int, Int.add_neg_cancel_right]
      rfl

/-! fmod -/

theorem fmod_eq_emod' (a b : Int) : Int.fmod a b = a % b - b * ite (b < 0 ∧ ¬(b ∣ a)) (-1) 0 := by
  simp [fmod_def, emod_def, fdiv_eq_ediv', Int.sub_eq_add_neg, Int.mul_add, Int.neg_add,
        Int.add_assoc]

@[simp] theorem emod_fmod (a b : Int) : (fmod a b) % b = a % b := by
  simp [Int.fmod_eq_emod', Int.sub_eq_add_neg, Int.neg_mul_eq_mul_neg]

@[simp] theorem fmod_emod (m n : Int) : Int.fmod (m % n) n = Int.fmod m n := by
  simp_all [fmod_eq_emod', emod_neg_iff]

@[simp]
theorem fmod_fmod (m n : Int) : Int.fmod (Int.fmod m n) n = Int.fmod m n := by
  simp [fmod_eq_emod', Int.sub_eq_add_neg, Int.neg_mul_eq_mul_neg,
        Int.dvd_add_left, Int.dvd_mul_right]

/-! bdiv -/

@[simp] theorem zero_bdiv (n : Nat) : bdiv 0 n = 0 := by unfold bdiv; simp; omega
@[simp] theorem bdiv_zero  (n : Int) : bdiv n 0 = 0 := by rfl
@[simp] theorem bdiv_one   (n : Int) : bdiv n 1 = n := by unfold bdiv; simp

/-! bmod -/

@[simp] theorem bmod_zero (n : Int) : bmod n 0 = n := by unfold bmod; simp


end Int
