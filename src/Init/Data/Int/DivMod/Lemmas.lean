/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Kim Morrison, Markus Himmel
-/
module

prelude
import Init.Data.Int.DivMod.Bootstrap
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Div.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Lemmas
import Init.Data.Nat.Dvd
import Init.RCases

/-!
# Further lemmas about integer division, now that `omega` is available.
-/

open Nat (succ)

namespace Int

@[simp high] theorem natCast_eq_zero {n : Nat} : (n : Int) = 0 ↔ n = 0 := by omega

protected theorem exists_add_of_le {a b : Int} (h : a ≤ b) : ∃ (c : Nat), b = a + c :=
  ⟨(b - a).toNat, by omega⟩

theorem toNat_emod {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x % y).toNat = x.toNat % y.toNat :=
  match x, y, eq_ofNat_of_zero_le hx, eq_ofNat_of_zero_le hy with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

/-! ### dvd  -/

theorem dvd_antisymm {a b : Int} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b := by
  rw [← natAbs_of_nonneg H1, ← natAbs_of_nonneg H2]
  rw [ofNat_dvd, ofNat_dvd, ofNat_inj]
  apply Nat.dvd_antisymm

protected theorem dvd_add : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b + c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d + e, by rw [Int.mul_add]⟩

protected theorem dvd_sub : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b - c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d - e, by rw [Int.mul_sub]⟩

protected theorem dvd_add_left {a b c : Int} (H : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun h => by have := Int.dvd_sub h H; rwa [Int.add_sub_cancel] at this, (Int.dvd_add · H)⟩

protected theorem dvd_add_right {a b c : Int} (H : a ∣ b) : a ∣ b + c ↔ a ∣ c := by
  rw [Int.add_comm, Int.dvd_add_left H]

@[simp] protected theorem dvd_add_mul_self {a b c : Int} : a ∣ b + c * a ↔ a ∣ b := by
  rw [Int.dvd_add_left (Int.dvd_mul_left c a)]

@[simp] protected theorem dvd_add_self_mul {a b c : Int} : a ∣ b + a * c ↔ a ∣ b := by
  rw [Int.mul_comm, Int.dvd_add_mul_self]

@[simp] protected theorem dvd_mul_self_add {a b c : Int} : a ∣ b * a + c ↔ a ∣ c := by
  rw [Int.add_comm, Int.dvd_add_mul_self]

@[simp] protected theorem dvd_self_mul_add {a b c : Int} : a ∣ a * b + c ↔ a ∣ c := by
  rw [Int.mul_comm, Int.dvd_mul_self_add]
protected theorem dvd_iff_dvd_of_dvd_sub {a b c : Int} (H : a ∣ b - c) : a ∣ b ↔ a ∣ c :=
  ⟨fun h => Int.sub_sub_self b c ▸ Int.dvd_sub h H,
   fun h => Int.sub_add_cancel b c ▸ Int.dvd_add H h⟩

protected theorem dvd_iff_dvd_of_dvd_add {a b c : Int} (H : a ∣ b + c) : a ∣ b ↔ a ∣ c := by
  rw [← Int.sub_neg] at H; rw [Int.dvd_iff_dvd_of_dvd_sub H, Int.dvd_neg]

theorem le_of_dvd {a b : Int} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
  match a, b, eq_succ_of_zero_lt bpos, H with
  | ofNat _, _, ⟨n, rfl⟩, H => ofNat_le.2 <| Nat.le_of_dvd n.succ_pos <| ofNat_dvd.1 H
  | -[_+1], _, ⟨_, rfl⟩, _ => Int.le_trans (Int.le_of_lt <| negSucc_lt_zero _) (ofNat_zero_le _)

theorem natAbs_dvd {a b : Int} : (a.natAbs : Int) ∣ b ↔ a ∣ b :=
  match natAbs_eq a with
  | .inl e => by rw [← e]
  | .inr e => by rw [← Int.neg_dvd, ← e]

theorem dvd_natAbs {a b : Int} : a ∣ b.natAbs ↔ a ∣ b :=
  match natAbs_eq b with
  | .inl e => by rw [← e]
  | .inr e => by rw [← Int.dvd_neg, ← e]

theorem natAbs_dvd_self {a : Int} : (a.natAbs : Int) ∣ a := by
  rw [Int.natAbs_dvd]
  exact Int.dvd_refl a

theorem dvd_natAbs_self {a : Int} : a ∣ (a.natAbs : Int) := by
  rw [Int.dvd_natAbs]
  exact Int.dvd_refl a

theorem natAbs_eq_of_dvd_dvd (hmn : m ∣ n) (hnm : n ∣ m) : natAbs m = natAbs n :=
  Nat.dvd_antisymm (natAbs_dvd_natAbs.2 hmn) (natAbs_dvd_natAbs.2 hnm)

theorem ofNat_dvd_right {n : Nat} {z : Int} : z ∣ (↑n : Int) ↔ z.natAbs ∣ n := by
  rw [← natAbs_dvd_natAbs, natAbs_natCast]

@[simp] theorem negSucc_dvd {a : Nat} {b : Int} : -[a+1] ∣ b ↔ ((a + 1 : Nat) : Int) ∣ b := by
  rw [← natAbs_dvd]
  norm_cast

@[simp] theorem dvd_negSucc {a : Int} {b : Nat} : a ∣ -[b+1] ↔ a ∣ ((b + 1 : Nat) : Int) := by
  rw [← dvd_natAbs]
  norm_cast

theorem eq_one_of_dvd_one {a : Int} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
  match a, eq_ofNat_of_zero_le H, H' with
  | _, ⟨_, rfl⟩, H' => congrArg ofNat <| Nat.eq_one_of_dvd_one <| ofNat_dvd.1 H'

theorem eq_one_of_mul_eq_one_right {a b : Int} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : Int} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right (b := a) H <| by rw [Int.mul_comm, H']

instance decidableDvd : DecidableRel (α := Int) (· ∣ ·) := fun _ _ =>
  decidable_of_decidable_of_iff (dvd_iff_emod_eq_zero ..).symm

protected theorem mul_dvd_mul_iff_left {a b c : Int} (h : a ≠ 0) : (a * b) ∣ (a * c) ↔ b ∣ c :=
  ⟨by rintro ⟨d, h'⟩; exact ⟨d, by rw [Int.mul_assoc] at h'; exact (mul_eq_mul_left_iff h).mp h'⟩,
    by rintro ⟨d, rfl⟩; exact ⟨d, by simp [Int.mul_assoc]⟩⟩

protected theorem mul_dvd_mul_iff_right {a b c : Int} (h : a ≠ 0) : (b * a) ∣ (c * a) ↔ b ∣ c := by
  rw [Int.mul_comm b a, Int.mul_comm c a]
  exact Int.mul_dvd_mul_iff_left h

protected theorem mul_dvd_mul {a b c d : Int} : a ∣ b → c ∣ d → a * c ∣ b * d := by
  simpa [← Int.natAbs_dvd_natAbs, natAbs_mul] using Nat.mul_dvd_mul

protected theorem mul_dvd_mul_left (a : Int) (h : b ∣ c) : a * b ∣ a * c :=
  Int.mul_dvd_mul a.dvd_refl h

protected theorem mul_dvd_mul_right (a : Int) (h : b ∣ c) : b * a ∣ c * a :=
  Int.mul_dvd_mul h a.dvd_refl

theorem dvd_of_mul_dvd_mul_left {a m n : Int} (ha : a ≠ 0) (h : a * m ∣ a * n) : m ∣ n := by
  obtain ⟨b, hb⟩ := h
  rw [Int.mul_assoc, Int.mul_eq_mul_left_iff ha] at hb
  exact ⟨_, hb⟩

theorem dvd_of_mul_dvd_mul_right {a m n : Int} (ha : a ≠ 0) (h : m * a ∣ n * a) : m ∣ n :=
  dvd_of_mul_dvd_mul_left ha (by simpa [Int.mul_comm] using h)

@[norm_cast] theorem natCast_dvd_natCast {m n : Nat} : (↑m : Int) ∣ ↑n ↔ m ∣ n where
  mp := by
    rintro ⟨a, h⟩
    obtain rfl | hm := m.eq_zero_or_pos
    · simpa using h
    have ha : 0 ≤ a := Int.not_lt.1 fun ha ↦ by
      simpa [← h, Int.not_lt.2 (Int.natCast_nonneg _)]
        using Int.mul_neg_of_pos_of_neg (natCast_pos.2 hm) ha
    match a, ha with
    | (a : Nat), _ =>
      norm_cast at h
      exact ⟨a, h⟩
  mpr := by rintro ⟨a, rfl⟩; simp [Int.dvd_mul_right]

/-! ### *div zero  -/

@[simp] protected theorem zero_tdiv : ∀ b : Int, tdiv 0 b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

@[simp] protected theorem tdiv_zero : ∀ a : Int, tdiv a 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => by simp [tdiv]

@[simp] theorem zero_fdiv (b : Int) : fdiv 0 b = 0 := by cases b <;> rfl

@[simp] protected theorem fdiv_zero : ∀ a : Int, fdiv a 0 = 0
  | 0      => rfl
  | succ _ => by simp [fdiv]
  | -[_+1] => rfl

/-! ### preliminaries for div equivalences -/

theorem negSucc_emod_ofNat_succ_eq_zero_iff {a b : Nat} :
    -[a+1] % (b + 1 : Int) = 0 ↔ (a + 1) % (b + 1) = 0 := by
  rw [← Int.natCast_one, ← Int.natCast_add]
  change Int.emod _ _ = 0 ↔ _
  rw [emod, natAbs_natCast]
  simp only [Nat.succ_eq_add_one, subNat_eq_zero_iff, Nat.add_right_cancel_iff]
  rw [eq_comm]
  apply Nat.succ_mod_succ_eq_zero_iff.symm

theorem negSucc_emod_negSucc_eq_zero_iff {a b : Nat} :
    -[a+1] % -[b+1] = 0 ↔ (a + 1) % (b + 1) = 0 := by
  change Int.emod _ _ = 0 ↔ _
  rw [emod, natAbs_negSucc]
  simp only [Nat.succ_eq_add_one, subNat_eq_zero_iff, Nat.add_right_cancel_iff]
  rw [eq_comm]
  apply Nat.succ_mod_succ_eq_zero_iff.symm

/-! ### div equivalences  -/

theorem tdiv_eq_ediv_of_nonneg : ∀ {a b : Int}, 0 ≤ a → a.tdiv b = a / b
  | 0, _, _
  | _, 0, _ => by simp
  | succ _, succ _, _ => rfl
  | succ _, -[_+1], _ => rfl

@[simp] theorem natCast_tdiv_eq_ediv {a : Nat} {b : Int} : (a : Int).tdiv b = a / b :=
    tdiv_eq_ediv_of_nonneg (by simp)

theorem tdiv_eq_ediv {a b : Int} :
    a.tdiv b = a / b + if 0 ≤ a ∨ b ∣ a then 0 else sign b := by
  simp only [dvd_iff_emod_eq_zero]
  match a, b with
  | ofNat a, ofNat b => simp [tdiv_eq_ediv_of_nonneg]
  | ofNat a, -[b+1] => simp [tdiv_eq_ediv_of_nonneg]
  | -[a+1], 0 => simp
  | -[a+1], ofNat (succ b) =>
    simp only [tdiv, Nat.succ_eq_add_one, ofNat_eq_coe, Int.natCast_add, cast_ofNat_Int,
      negSucc_not_nonneg, sign_of_add_one]
    simp only [negSucc_emod_ofNat_succ_eq_zero_iff]
    norm_cast
    simp only [Nat.succ_eq_add_one, false_or]
    split <;> rename_i h
    · rw [Int.add_zero, neg_ofNat_eq_negSucc_iff]
      exact Nat.succ_div_of_mod_eq_zero h
    · rw [neg_ofNat_eq_negSucc_add_one_iff]
      exact Nat.succ_div_of_mod_ne_zero h
  | -[a+1], -[b+1] =>
    simp only [tdiv, ofNat_eq_coe, negSucc_not_nonneg, false_or, sign_negSucc]
    norm_cast
    simp only [negSucc_ediv_negSucc]
    rw [Int.natCast_add, Int.natCast_one]
    simp only [negSucc_emod_negSucc_eq_zero_iff]
    split <;> rename_i h
    · norm_cast
      exact Nat.succ_div_of_mod_eq_zero h
    · rw [Int.add_neg_eq_sub, Int.add_sub_cancel]
      norm_cast
      exact Nat.succ_div_of_mod_ne_zero h

theorem ediv_eq_tdiv {a b : Int} :
    a / b = a.tdiv b - if 0 ≤ a ∨ b ∣ a then 0 else sign b := by
  simp [tdiv_eq_ediv]

theorem divExact_eq_tdiv {a b : Int} (h : b ∣ a) : a.divExact b h = a.tdiv b := by
  simp [ediv_eq_tdiv, h]

theorem fdiv_eq_ediv_of_nonneg : ∀ (a : Int) {b : Int}, 0 ≤ b → fdiv a b = a / b
  | 0, _, _ | -[_+1], 0, _ => by simp
  | succ _, ofNat _, _ | -[_+1], succ _, _ => rfl

theorem fdiv_eq_ediv {a b : Int} :
    a.fdiv b = a / b - if 0 ≤ b ∨ b ∣ a then 0 else 1 := by
  match a, b with
  | ofNat a, ofNat b => simp [fdiv_eq_ediv_of_nonneg]
  | -[a+1], ofNat b => simp [fdiv_eq_ediv_of_nonneg]
  | 0, -[b+1] => simp
  | ofNat (a + 1), -[b+1] =>
    simp only [fdiv, ofNat_ediv_negSucc, negSucc_not_nonneg, negSucc_dvd, false_or]
    simp only [ofNat_eq_coe, ofNat_dvd]
    norm_cast
    rw [Nat.succ_div, negSucc_eq]
    split <;> rename_i h
    · simp
    · simp [Int.neg_add]
      norm_cast
  | -[a+1], -[b+1] =>
    simp only [fdiv, ofNat_eq_coe, negSucc_ediv_negSucc, negSucc_not_nonneg, dvd_negSucc, negSucc_dvd,
      false_or]
    norm_cast
    rw [Int.natCast_add, Int.natCast_one, Nat.succ_div]
    split <;> simp

theorem ediv_eq_fdiv {a b : Int} :
    a / b = a.fdiv b + if 0 ≤ b ∨ b ∣ a then 0 else 1 := by
  simp [fdiv_eq_ediv]

theorem divExact_eq_fdiv {a b : Int} (h : b ∣ a) : a.divExact b h = a.fdiv b := by
  simp [ediv_eq_fdiv, h]

theorem fdiv_eq_tdiv_of_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fdiv a b = tdiv a b :=
  tdiv_eq_ediv_of_nonneg Ha ▸ fdiv_eq_ediv_of_nonneg _ Hb

theorem fdiv_eq_tdiv {a b : Int} :
    a.fdiv b = a.tdiv b -
      if b ∣ a then 0
      else
        if 0 ≤ a then
          if 0 ≤ b then 0
          else 1
        else
          if 0 ≤ b then b.sign
          else 1 + b.sign := by
  rw [fdiv_eq_ediv, tdiv_eq_ediv]
  by_cases h : b ∣ a <;> simp [h] <;> omega

theorem tdiv_eq_fdiv {a b : Int} :
    a.tdiv b = a.fdiv b +
      if b ∣ a then 0
      else
        if 0 ≤ a then
          if 0 ≤ b then 0
          else 1
        else
          if 0 ≤ b then b.sign
          else 1 + b.sign := by
  rw [fdiv_eq_tdiv]
  omega

theorem tdiv_eq_ediv_of_dvd {a b : Int} (h : b ∣ a) : a.tdiv b = a / b := by
  simp [tdiv_eq_ediv, h]

theorem fdiv_eq_ediv_of_dvd {a b : Int} (h : b ∣ a) : a.fdiv b = a / b := by
  simp [fdiv_eq_ediv, h]

/-! ### mod zero -/

@[simp] theorem zero_tmod (b : Int) : tmod 0 b = 0 := by cases b <;> simp [tmod]

@[simp] theorem tmod_zero : ∀ a : Int, tmod a 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1] => congrArg (fun n => -ofNat n) <| Nat.mod_zero _

@[simp] theorem zero_fmod (b : Int) : fmod 0 b = 0 := by cases b <;> rfl

@[simp] theorem fmod_zero : ∀ a : Int, fmod a 0 = a
  | 0 => rfl
  | succ _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

/-! ### mod definitions -/

theorem tmod_add_tdiv : ∀ a b : Int, tmod a b + b * (a.tdiv b) = a
  | ofNat _, ofNat _ => congrArg ofNat (Nat.mod_add_div ..)
  | ofNat m, -[n+1] => by
    change (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg]; exact congrArg ofNat (Nat.mod_add_div ..)
  | -[m+1], 0 => by
    change -(↑((succ m) % 0) : Int) + 0 * -↑(succ m / 0) = -↑(succ m)
    rw [Nat.mod_zero, Int.zero_mul, Int.add_zero]
  | -[m+1], ofNat n => by
    change -(↑((succ m) % n) : Int) + ↑n * -↑(succ m / n) = -↑(succ m)
    rw [Int.mul_neg, ← Int.neg_add]
    exact congrArg (-ofNat ·) (Nat.mod_add_div ..)
  | -[m+1], -[n+1] => by
    change -(↑(succ m % succ n) : Int) + -↑(succ n) * ↑(succ m / succ n) = -↑(succ m)
    rw [Int.neg_mul, ← Int.neg_add]
    exact congrArg (-ofNat ·) (Nat.mod_add_div ..)

theorem tdiv_add_tmod (a b : Int) : b * a.tdiv b + tmod a b = a := by
  rw [Int.add_comm]; apply tmod_add_tdiv ..

/-- Variant of `tmod_add_tdiv` with the multiplication written the other way around. -/
theorem tmod_add_tdiv' (m k : Int) : tmod m k + m.tdiv k * k = m := by
  rw [Int.mul_comm]; apply tmod_add_tdiv

/-- Variant of `tdiv_add_tmod` with the multiplication written the other way around. -/
theorem tdiv_add_tmod' (m k : Int) : m.tdiv k * k + tmod m k = m := by
  rw [Int.mul_comm]; apply tdiv_add_tmod

theorem tmod_def (a b : Int) : tmod a b = a - b * a.tdiv b := by
  rw [← Int.add_sub_cancel (tmod a b), tmod_add_tdiv]

theorem fmod_add_fdiv : ∀ a b : Int, a.fmod b + b * a.fdiv b = a
  | 0, ofNat _ | 0, -[_+1] => congrArg ofNat <| by simp
  | succ _, ofNat _ => congrArg ofNat <| Nat.mod_add_div ..
  | succ m, -[n+1] => by
    change subNatNat (m % succ n) n + (↑(succ n * (m / succ n)) + n + 1) = (m + 1)
    rw [Int.add_comm _ n, ← Int.add_assoc, ← Int.add_assoc,
      Int.subNatNat_eq_coe, Int.sub_add_cancel]
    exact congrArg (ofNat · + 1) <| Nat.mod_add_div ..
  | -[_+1], 0 => by rw [fmod_zero]; rfl
  | -[m+1], succ n => by
    change subNatNat .. - (↑(succ n * (m / succ n)) + ↑(succ n)) = -↑(succ m)
    rw [Int.subNatNat_eq_coe, ← Int.sub_sub, ← Int.neg_sub, Int.sub_sub, Int.sub_sub_self]
    exact congrArg (-ofNat ·) <| Nat.succ_add .. ▸ Nat.mod_add_div .. ▸ rfl
  | -[m+1], -[n+1] => by
    change -(↑(succ m % succ n) : Int) + -↑(succ n * (succ m / succ n)) = -↑(succ m)
    rw [← Int.neg_add]; exact congrArg (-ofNat ·) <| Nat.mod_add_div ..

/-- Variant of `fmod_add_fdiv` with the multiplication written the other way around. -/
theorem fmod_add_fdiv' (a b : Int) : a.fmod b + (a.fdiv b) * b = a := by
  rw [Int.mul_comm]; exact fmod_add_fdiv ..

theorem fdiv_add_fmod (a b : Int) : b * a.fdiv b + a.fmod b = a := by
  rw [Int.add_comm]; exact fmod_add_fdiv ..

/-- Variant of `fdiv_add_fmod` with the multiplication written the other way around. -/
theorem fdiv_add_fmod' (a b : Int) : (a.fdiv b) * b + a.fmod b = a := by
  rw [Int.mul_comm]; exact fdiv_add_fmod ..

theorem fmod_def (a b : Int) : a.fmod b = a - b * a.fdiv b := by
  rw [← Int.add_sub_cancel (a.fmod b), fmod_add_fdiv]

/-! ### mod equivalences  -/

theorem fmod_eq_emod_of_nonneg (a : Int) {b : Int} (hb : 0 ≤ b) : fmod a b = a % b := by
  simp [fmod_def, emod_def, fdiv_eq_ediv_of_nonneg _ hb]

theorem fmod_eq_emod {a b : Int} :
    fmod a b = a % b + if 0 ≤ b ∨ b ∣ a then 0 else b := by
  simp [fmod_def, emod_def, fdiv_eq_ediv]
  split <;> simp [Int.mul_sub]
  omega

theorem emod_eq_fmod {a b : Int} :
    a % b = fmod a b - if 0 ≤ b ∨ b ∣ a then 0 else b := by
  simp [fmod_eq_emod]

theorem tmod_eq_emod_of_nonneg {a b : Int} (ha : 0 ≤ a) : tmod a b = a % b := by
  simp [emod_def, tmod_def, tdiv_eq_ediv_of_nonneg ha]

theorem tmod_eq_emod {a b : Int} :
    tmod a b = a % b - if 0 ≤ a ∨ b ∣ a then 0 else b.natAbs := by
  rw [tmod_def, tdiv_eq_ediv]
  simp only [dvd_iff_emod_eq_zero]
  split
  · simp [emod_def]
  · rw [Int.mul_add, ← Int.sub_sub, emod_def]
    simp

theorem emod_eq_tmod {a b : Int} :
    a % b = tmod a b + if 0 ≤ a ∨ b ∣ a then 0 else b.natAbs := by
  simp [tmod_eq_emod]

theorem fmod_eq_tmod_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : fmod a b = tmod a b :=
  tmod_eq_emod_of_nonneg ha ▸ fmod_eq_emod_of_nonneg _ hb

theorem fmod_eq_tmod {a b : Int} :
    fmod a b = tmod a b +
      if b ∣ a then 0
      else
        if 0 ≤ a then
          if 0 ≤ b then 0
          else b
        else
          if 0 ≤ b then b.natAbs
          else 2 * b.toNat := by
  simp [fmod_eq_emod, tmod_eq_emod]
  by_cases h : b ∣ a <;> simp [h]
  split <;> split <;> omega

theorem tmod_eq_fmod {a b : Int} :
    tmod a b = fmod a b -
      if b ∣ a then 0
      else
        if 0 ≤ a then
          if 0 ≤ b then 0
          else b
        else
          if 0 ≤ b then b.natAbs
          else 2 * b.toNat := by
  simp [fmod_eq_tmod]

/-! ### `/` ediv -/

theorem mul_add_ediv_right (a c : Int) {b : Int} (H : b ≠ 0) : (a * b + c) / b = a + c / b := by
  rw [Int.add_comm, add_mul_ediv_right _ _ H, Int.add_comm]

theorem mul_add_ediv_left (b : Int) {a : Int}
    (c : Int) (H : a ≠ 0) : (a * b + c) / a = b + c / a := by
  rw [Int.add_comm, add_mul_ediv_left _ _ H, Int.add_comm]

theorem sub_mul_ediv_right (a b : Int) {c : Int} (H : c ≠ 0) : (a - b * c) / c = a / c - b := by
  rw [Int.sub_eq_add_neg, ← Int.neg_mul, add_mul_ediv_right _ _ H, Int.sub_eq_add_neg]

theorem sub_mul_ediv_left (a : Int) {b : Int}
    (c : Int) (H : b ≠ 0) : (a - b * c) / b = a / b - c := by
  rw [Int.sub_eq_add_neg, ← Int.mul_neg, add_mul_ediv_left _ _ H, Int.sub_eq_add_neg]

theorem mul_sub_ediv_right (a c : Int) {b : Int} (H : b ≠ 0) : (a * b - c) / b = a + -c / b := by
  rw [Int.sub_eq_add_neg, Int.add_comm, add_mul_ediv_right _ _ H, Int.add_comm]

theorem mul_sub_ediv_left (b : Int) {a : Int}
    (c : Int) (H : a ≠ 0) : (a * b - c) / a = b + -c / a := by
  rw [Int.sub_eq_add_neg, Int.add_comm, add_mul_ediv_left _ _ H, Int.add_comm]

theorem ediv_neg_of_neg_of_pos {a b : Int} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => negSucc_lt_zero _

@[deprecated ediv_neg_of_neg_of_pos (since := "2025-03-04")]
abbrev ediv_neg' := @ediv_neg_of_neg_of_pos

theorem negSucc_ediv (m : Nat) {b : Int} (H : 0 < b) : -[m+1] / b = -(ediv m b + 1) :=
  match b, eq_succ_of_zero_lt H with
  | _, ⟨_, rfl⟩ => rfl

theorem ediv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

theorem ediv_nonneg_of_nonpos_of_nonpos {a b : Int} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a / b := by
  match a, b with
  | ofNat a, b =>
    match Int.le_antisymm Ha (ofNat_zero_le a) with
    | h1 =>
      rw [h1, zero_ediv]
      exact Int.le_refl 0
  | a, ofNat b =>
    match Int.le_antisymm Hb (ofNat_zero_le  b) with
    | h1 =>
      rw [h1, Int.ediv_zero]
      exact Int.le_refl 0
  | negSucc a, negSucc b =>
    rw [Int.div_def, ediv]
    exact le_add_one (ediv_nonneg (ofNat_zero_le a) (Int.le_trans (ofNat_zero_le b) (le.intro 1 rfl)))

theorem ediv_pos_of_neg_of_neg {a b : Int} (ha : a < 0) (hb : b < 0) : 0 < a / b := by
  rw [Int.div_def]
  match a, b, ha, hb with
  | .negSucc a, .negSucc b, _, _ => apply ofNat_succ_pos

theorem ediv_nonpos_of_nonneg_of_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.ediv_neg .. ▸ Int.ediv_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

@[deprecated ediv_nonpos_of_nonneg_of_nonpos (since := "2025-03-04")]
abbrev ediv_nonpos := @ediv_nonpos_of_nonneg_of_nonpos

theorem ediv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg Nat.cast <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

theorem ediv_eq_neg_one_of_neg_of_le {a b : Int} (H1 : a < 0) (H2 : -a ≤ b) : a / b = -1 := by
  match a, b, H1, H2 with
  | negSucc a', ofNat (b' + 1), H1, H2 =>
    rw [Int.div_def, ediv, Int.negSucc_eq, Int.neg_inj]
    norm_cast
    rw [Nat.add_eq_right, Nat.div_eq_zero_iff_lt (by omega)]
    simp [Int.negSucc_eq] at H2
    omega

theorem ediv_eq_one_of_neg_of_le {a b : Int} (H1 : a < 0) (H2 : b ≤ a) : a / b = 1 := by
  match a, b, H1, H2 with
  | negSucc a', ofNat n', H1, H2 => simp [Int.negSucc_eq] at H2; omega
  | negSucc a', negSucc b', H1, H2 =>
    rw [Int.div_def, ediv, ofNat_eq_coe]
    norm_cast
    rw [Nat.succ_eq_add_one, Nat.add_eq_right, Nat.div_eq_zero_iff_lt (by omega)]
    simp [Int.negSucc_eq] at H2
    omega

theorem one_ediv (b : Int) : 1 / b = if b.natAbs = 1 then b else 0 := by
  induction b using wlog_sign
  case inv => simp; split <;> simp
  case w b =>
    match b with
    | 0 => simp
    | 1 => simp
    | b + 2 =>
      apply ediv_eq_zero_of_lt (by decide) (by omega)

theorem neg_one_ediv (b : Int) : -1 / b = -b.sign :=
  match b with
  | ofNat 0 => by simp
  | ofNat (b + 1) =>
    ediv_eq_neg_one_of_neg_of_le (by decide) (by simp [ofNat_eq_coe]; omega)
  | negSucc b =>
    ediv_eq_one_of_neg_of_le (by decide) (by omega)

@[simp] theorem mul_ediv_mul_of_pos {a : Int}
    (b c : Int) (H : 0 < a) : (a * b) / (a * c) = b / c :=
  suffices ∀ (m k : Nat) (b : Int), (m.succ * b) / (m.succ * k) = b / k from
    match a, eq_succ_of_zero_lt H, c, Int.eq_nat_or_neg c with
    | _, ⟨m, rfl⟩, _, ⟨k, .inl rfl⟩ => this _ ..
    | _, ⟨m, rfl⟩, _, ⟨k, .inr rfl⟩ => by
      rw [Int.mul_neg, Int.ediv_neg, Int.ediv_neg]; apply congrArg Neg.neg; apply this
  fun m k b =>
  match b, k with
  | ofNat _, _ => congrArg ofNat (Nat.mul_div_mul_left _ _ m.succ_pos)
  | -[n+1], 0 => by
    rw [Int.ofNat_zero, Int.mul_zero, Int.ediv_zero, Int.ediv_zero]
  | -[n+1], succ k => congrArg negSucc <|
    show (m.succ * n + m) / (m.succ * k.succ) = n / k.succ by
      apply Nat.div_eq_of_lt_le
      · refine Nat.le_trans ?_ (Nat.le_add_right _ _)
        rw [← Nat.mul_div_mul_left _ _ m.succ_pos]
        apply Nat.div_mul_le_self
      · change m.succ * n.succ ≤ _
        rw [Nat.mul_left_comm]
        apply Nat.mul_le_mul_left
        apply (Nat.div_lt_iff_lt_mul k.succ_pos).1
        apply Nat.lt_succ_self

@[simp] theorem mul_ediv_mul_of_pos_left
    (a : Int) {b : Int} (c : Int) (H : 0 < b) : (a * b) / (c * b) = a / c := by
  rw [Int.mul_comm, Int.mul_comm c, mul_ediv_mul_of_pos _ _ H]

protected theorem ediv_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a / b = c := by rw [H2, Int.mul_ediv_cancel_left _ H1]

protected theorem eq_ediv_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c / a :=
  (Int.ediv_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem ediv_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a / b = c :=
  Int.ediv_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem eq_ediv_of_mul_eq_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a * b = c) : a = c / b :=
  (Int.ediv_eq_of_eq_mul_left H1 H2.symm).symm

@[simp] protected theorem ediv_self {a : Int} (H : a ≠ 0) : a / a = 1 := by
  have := Int.mul_ediv_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem neg_ediv_self (a : Int) (h : a ≠ 0) : (-a) / a = -1 := by
  rw [neg_ediv_of_dvd (Int.dvd_refl a), Int.ediv_self h]

theorem sign_ediv (a b : Int) : sign (a / b) = if 0 ≤ a ∧ a < b.natAbs then 0 else sign a * sign b := by
  induction b using wlog_sign
  case inv => simp; split <;> simp [Int.mul_neg]
  case w b =>
    match b with
    | 0 => simp
    | b + 1 =>
      have : ((b + 1 : Nat) : Int).natAbs = b + 1 := by omega
      rw [this]
      match a with
      | 0 => simp
      | (a + 1 : Nat) =>
        norm_cast
        simp only [Nat.le_add_left, Nat.add_lt_add_iff_right, true_and, Int.natCast_add,
          cast_ofNat_Int, sign_of_add_one, Int.mul_one]
        split
        · rw [Nat.div_eq_of_lt (by omega)]
          simp
        · have := Nat.div_pos (a := a + 1) (b := b + 1) (by omega) (by omega)
          rw [sign_eq_one_of_pos (mod_cast this)]
      | negSucc a =>
        norm_cast

/-! ### emod -/

theorem mod_def' (m n : Int) : m % n = emod m n := rfl

theorem negSucc_emod (m : Nat) {b : Int} (bpos : 0 < b) : -[m+1] % b = b - 1 - m % b := by
  rw [Int.sub_sub, Int.add_comm]
  match b, eq_succ_of_zero_lt bpos with
  | _, ⟨n, rfl⟩ => rfl

theorem emod_negSucc (m : Nat) (n : Int) :
  (Int.negSucc m) % n = Int.subNatNat (Int.natAbs n) (Nat.succ (m % Int.natAbs n)) := rfl

theorem ofNat_mod_ofNat (m n : Nat) : (m % n : Int) = ↑(m % n) := rfl

@[simp] theorem add_neg_mul_emod_self_right (a b c : Int) : (a + -(b * c)) % c = a % c := by
  rw [Int.neg_mul_eq_neg_mul, add_mul_emod_self_right]

@[deprecated add_neg_mul_emod_self_right (since := "2025-04-11")]
theorem add_neg_mul_emod_self {a b c : Int} : (a + -(b * c)) % c = a % c :=
  add_neg_mul_emod_self_right ..

@[simp] theorem add_neg_mul_emod_self_left (a b c : Int) : (a + -(b * c)) % b = a % b := by
  rw [Int.neg_mul_eq_mul_neg, add_mul_emod_self_left]

@[simp] theorem add_emod_right (a b : Int) : (a + b) % b = a % b := by
  have := add_mul_emod_self_left a b 1; rwa [Int.mul_one] at this

@[deprecated add_emod_right (since := "2025-04-11")]
theorem add_emod_self {a b : Int} : (a + b) % b = a % b := add_emod_right ..

@[simp] theorem add_emod_left (a b : Int) : (a + b) % a = b % a := by
  rw [Int.add_comm, add_emod_right]

@[deprecated add_emod_left (since := "2025-04-11")]
theorem add_emod_self_left {a b : Int} : (a + b) % a = b % a := add_emod_left ..

@[simp] theorem sub_mul_emod_self_right (a b c : Int) : (a - b * c) % c = a % c := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem sub_mul_emod_self_left (a b c : Int) : (a - b * c) % b = a % b := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem mul_sub_emod_self_right (a b c : Int) : (a * b - c) % b = -c % b := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem mul_sub_emod_self_left (a b c : Int) : (a * b - c) % a = -c % a := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem sub_emod_right (a b : Int) : (a - b) % b = a % b := by
  rw (occs := [1]) [← Int.mul_one b, sub_mul_emod_self_left]

@[simp] theorem sub_emod_left (a b : Int) : (a - b) % a = -b % a := by
  simp [Int.sub_eq_add_neg]

theorem neg_emod_eq_sub_emod {a b : Int} : -a % b = (b - a) % b := by
  rw [← add_emod_left, Int.sub_eq_add_neg]

theorem emod_eq_add_self_emod {a b : Int} : a % b = (a + b) % b :=
  (Int.add_emod_right ..).symm

@[simp] theorem emod_neg (a b : Int) : a % -b = a % b := by
  rw [emod_def, emod_def, Int.ediv_neg, Int.neg_mul_neg]

@[simp] theorem neg_emod_self (a : Int) : -a % a = 0 := by
  rw [neg_emod_eq_sub_emod, Int.sub_self, zero_emod]

@[simp] theorem emod_sub_emod (m n k : Int) : (m % n - k) % n = (m - k) % n :=
  Int.emod_add_emod m n (-k)

@[simp] theorem sub_emod_emod (m n k : Int) : (m - n % k) % k = (m - n) % k := by
  apply (emod_add_cancel_right (n % k)).mp
  rw [Int.sub_add_cancel, Int.add_emod_emod, Int.sub_add_cancel]

theorem emod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
  have b0 := Int.le_trans H1 (Int.le_of_lt H2)
  match a, b, eq_ofNat_of_zero_le H1, eq_ofNat_of_zero_le b0 with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg ofNat <| Nat.mod_eq_of_lt (Int.ofNat_lt.1 H2)

theorem emod_lt_of_neg (a : Int) {b : Int} (h : b < 0) : a % b < -b := by
  match b, h with
  | .negSucc b', h =>
    simp only [negSucc_eq, emod_neg]
    apply emod_lt_of_pos
    omega

theorem emod_lt (a : Int) {b : Int} (h : b ≠ 0) : a % b < b.natAbs :=
  match b, h with
  | (b : Nat), h => emod_lt_of_pos a (by omega)
  | negSucc b, h => emod_lt_of_neg a (by omega)

@[simp] theorem emod_self_add_one {x : Int} (h : 0 ≤ x) : x % (x + 1) = x :=
  emod_eq_of_lt h (Int.lt_succ x)

theorem sign_emod (a : Int) {b} (h : b ≠ 0) : sign (a % b) = if b ∣ a then 0 else 1 := by
  split <;> rename_i w
  · simp [emod_eq_zero_of_dvd, w]
  · obtain rfl | w := emod_pos_of_not_dvd w
    · simp at h
    · simp [sign_eq_one_of_pos w]

theorem one_emod {b : Int} : 1 % b = if b.natAbs = 1 then 0 else 1 := by
  rw [emod_def, one_ediv]
  split <;> rename_i h
  · obtain rfl | rfl := natAbs_eq_iff.mp h <;> simp
  · simp

@[simp] theorem neg_emod_two (i : Int) : -i % 2 = i % 2 := by omega

/-! ### properties of `/` and `%` -/

theorem mul_ediv_cancel_of_dvd {a b : Int} (H : b ∣ a) : b * (a / b) = a :=
  mul_ediv_cancel_of_emod_eq_zero (emod_eq_zero_of_dvd H)

theorem ediv_mul_cancel_of_dvd {a b : Int} (H : b ∣ a) : a / b * b = a :=
  ediv_mul_cancel_of_emod_eq_zero (emod_eq_zero_of_dvd H)

theorem emod_two_eq (x : Int) : x % 2 = 0 ∨ x % 2 = 1 := by omega

theorem add_emod_eq_add_emod_left {m n k : Int} (i : Int)
    (H : m % n = k % n) : (i + m) % n = (i + k) % n := by
  rw [Int.add_comm, add_emod_eq_add_emod_right _ H, Int.add_comm]

theorem emod_add_cancel_left {m n k i : Int} : (i + m) % n = (i + k) % n ↔ m % n = k % n := by
  rw [Int.add_comm, Int.add_comm i, emod_add_cancel_right]

theorem emod_sub_cancel_right {m n k : Int} (i) : (m - i) % n = (k - i) % n ↔ m % n = k % n :=
  emod_add_cancel_right _

theorem emod_eq_emod_iff_emod_sub_eq_zero {m n k : Int} : m % n = k % n ↔ (m - k) % n = 0 :=
  (emod_sub_cancel_right k).symm.trans <| by simp [Int.sub_self]

theorem emod_sub_cancel_left {m n k : Int} (i) : (i - m) % n = (i - k) % n ↔ m % n = k % n := by
  simp only [emod_eq_emod_iff_emod_sub_eq_zero, ← dvd_iff_emod_eq_zero,
    (by omega : i - m - (i - k) = -(m - k)), Int.dvd_neg]

protected theorem ediv_emod_unique {a b r q : Int} (h : 0 < b) :
    a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b := by
  constructor
  · intro ⟨rfl, rfl⟩
    exact ⟨emod_add_ediv a b, emod_nonneg _ (Int.ne_of_gt h), emod_lt_of_pos _ h⟩
  · intro ⟨rfl, hz, hb⟩
    constructor
    · rw [Int.add_mul_ediv_left r q (Int.ne_of_gt h), ediv_eq_zero_of_lt hz hb]
      simp [Int.zero_add]
    · rw [add_mul_emod_self_left, emod_eq_of_lt hz hb]

protected theorem ediv_emod_unique' {a b r q : Int} (h : b < 0) :
    a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < -b := by
  have := Int.ediv_emod_unique (a := a) (b := -b) (r := r) (q := -q) (by omega)
  simpa [Int.neg_inj, Int.neg_mul, Int.mul_neg]

@[simp] theorem mul_emod_mul_of_pos
    {a : Int} (b c : Int) (H : 0 < a) : (a * b) % (a * c) = a * (b % c) := by
  rw [emod_def, emod_def, mul_ediv_mul_of_pos _ _ H, Int.mul_sub, Int.mul_assoc]

theorem lt_ediv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a / b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.emod_def .. ▸ emod_lt_of_pos _ H

theorem neg_ediv {a b : Int} : (-a) / b = -(a / b) - if b ∣ a then 0 else b.sign := by
  if hb : b = 0 then
    simp [hb]
  else
    conv => lhs; rw [← ediv_add_emod a b]
    rw [Int.neg_add, ← Int.mul_neg, mul_add_ediv_left _ _ hb, Int.add_comm]
    split <;> rename_i h
    · rw [emod_eq_zero_of_dvd h]
      simp
    · if hb : 0 < b then
        rw [Int.sign_eq_one_of_pos hb, ediv_eq_neg_one_of_neg_of_le]
        · omega
        · have : 0 < a % b := (emod_pos_of_not_dvd h).resolve_left (by omega)
          omega
        · have := emod_lt_of_pos a hb
          omega
      else
        replace hb : b < 0 := by omega
        rw [Int.sign_eq_neg_one_of_neg hb, Int.ediv_eq_one_of_neg_of_le]
        · omega
        · have : 0 < a % b := (emod_pos_of_not_dvd h).resolve_left (by omega)
          omega
        · have := emod_lt_of_neg a hb
          omega

theorem tdiv_cases (n m : Int) : n.tdiv m =
    if 0 ≤ n then
      if 0 ≤ m then n / m else -(n / (-m))
    else
      if 0 ≤ m then -((-n) / m) else (-n) / (-m) := by
  split <;> rename_i hn
  · split <;> rename_i hm
    · rw [Int.tdiv_eq_ediv_of_nonneg hn]
    · rw [Int.tdiv_eq_ediv_of_nonneg hn]
      simp
  · split <;> rename_i hm
    · rw [Int.tdiv_eq_ediv, Int.neg_ediv]
      simp [hn, Int.neg_sub, Int.add_comm]
    · rw [Int.tdiv_eq_ediv, Int.neg_ediv, Int.ediv_neg]
      simp [hn, Int.sub_eq_add_neg, apply_ite Neg.neg]

theorem neg_emod {a b : Int} : (-a) % b = if b ∣ a then 0 else b.natAbs - (a % b) := by
  rw [emod_def, emod_def, neg_ediv, Int.mul_sub, Int.mul_neg]
  split <;> rename_i h
  · simp [mul_ediv_cancel_of_dvd h]
  · simp
    omega

theorem natAbs_ediv (a : Int) (b : Int) : natAbs (a / b) = natAbs a / natAbs b + if 0 ≤ a ∨ b = 0 ∨ b ∣ a then 0 else 1 := by
  by_cases hb : b = 0 <;> try (simp_all; done)
  simp only [hb, false_or]
  induction b using wlog_sign
  case neg.inv => simp
  case neg.w b =>
    match a with
    | 0 => simp
    | (a + 1 : Nat) => norm_cast
    | negSucc a =>
      simp only [negSucc_eq]
      norm_cast
      rw [neg_ediv]
      norm_cast
      rw [natAbs_neg, natAbs_natCast]
      have : ¬ 0 ≤ -((a + 1 : Nat) : Int) := by omega
      simp only [this]
      have : ↑b ∣ -((a + 1 : Nat) : Int)  ↔ b ∣ a + 1 := by simp; norm_cast
      simp only [this, false_or]
      split <;> rename_i h
      · simp [-natCast_ediv]
      · rw [Nat.succ_div, if_neg h, sign_eq_one_of_pos (by omega), Int.sub_eq_add_neg, ← Int.neg_add, natAbs_neg]
        norm_cast

theorem natAbs_ediv_of_nonneg {a b : Int} (ha : 0 ≤ a) : (a / b).natAbs = a.natAbs / b.natAbs := by
  rw [natAbs_ediv, if_pos (Or.inl ha), Nat.add_zero]

theorem natAbs_ediv_of_dvd {a b : Int} (hab : b ∣ a) : (a / b).natAbs = a.natAbs / b.natAbs := by
  rw [natAbs_ediv, if_pos (Or.inr (Or.inr hab)), Nat.add_zero]

theorem natAbs_emod_of_nonneg {a : Int} (h : 0 ≤ a) (b : Int) :
    natAbs (a % b) = natAbs a % natAbs b := by
  match a, b, h with
  | (a : Nat), (b : Nat), _ => norm_cast
  | (a : Nat), negSucc b, _ => simp [negSucc_eq]; norm_cast

theorem natAbs_emod (a : Int) {b : Int} (hb : b ≠ 0):
    natAbs (a % b) = if 0 ≤ a ∨ b ∣ a then natAbs a % natAbs b else natAbs b - natAbs a % natAbs b := by
  match a with
  | (a : Nat) => simp [natAbs_emod_of_nonneg]
  | negSucc a =>
    simp
    split <;> rename_i h
    · simp [negSucc_eq]
      rw [emod_eq_zero_of_dvd, Nat.mod_eq_zero_of_dvd, natAbs_zero]
      · exact ofNat_dvd_right.mp h
      · exact dvd_natAbs.mp h
    simp [negSucc_eq]
    simp [neg_emod]
    rw [if_neg h]
    norm_cast
    have := natAbs_emod_of_nonneg (a := a + 1) (by omega) b
    norm_cast at this
    rw [natAbs_sub_of_nonneg_of_le, this]
    omega
    · exact emod_nonneg _ hb
    · have := emod_lt (a + 1 : Nat) hb
      omega

theorem natAbs_ediv_le_natAbs (a b : Int) : natAbs (a / b) ≤ natAbs a :=
  match b, Int.eq_nat_or_neg b with
  | _, ⟨n, .inl rfl⟩ => aux _ _
  | _, ⟨n, .inr rfl⟩ => by rw [Int.ediv_neg, natAbs_neg]; apply aux
where
  aux : ∀ (a : Int) (n : Nat), natAbs (a / n) ≤ natAbs a
  | ofNat _, _ => Nat.div_le_self ..
  | -[_+1], 0 => Nat.zero_le _
  | -[_+1], succ _ => Nat.succ_le_succ (Nat.div_le_self _ _)

@[deprecated natAbs_ediv_le_natAbs (since := "2025-03-05")]
abbrev natAbs_div_le_natAbs := natAbs_ediv_le_natAbs

theorem ediv_le_self {a : Int} (b : Int) (Ha : 0 ≤ a) : a / b ≤ a := by
  have := Int.le_trans le_natAbs (ofNat_le.2 <| natAbs_ediv_le_natAbs a b)
  rwa [natAbs_of_nonneg Ha] at this

theorem dvd_emod_sub_self {x m : Int} : m ∣ x % m - x :=
  dvd_of_emod_eq_zero (by simp)

theorem dvd_self_sub_emod {x m : Int} : m ∣ x - x % m :=
  dvd_of_emod_eq_zero (by simp)

theorem emod_eq_iff {a b c : Int} (hb : b ≠ 0) : a % b = c ↔ 0 ≤ c ∧ c < b.natAbs ∧ b ∣ c - a := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨emod_nonneg a hb, emod_lt a hb, dvd_emod_sub_self⟩
  · rintro ⟨h₁, h₂, h₃⟩
    rw [← Int.sub_eq_zero]
    have := dvd_emod_sub_self (x := a) (m := b)
    have hdvd := Int.dvd_sub this h₃
    rw [(by omega : a % b - a - (c - a) = a % b - c)] at hdvd
    apply eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have := emod_nonneg a hb
    have := emod_lt a hb
    omega

@[simp] theorem neg_mul_emod_left (a b : Int) : -(a * b) % b = 0 := by
  rw [← dvd_iff_emod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_left a b

@[simp] theorem neg_mul_emod_right (a b : Int) : -(a * b) % a = 0 := by
  rw [← dvd_iff_emod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_right a b

@[deprecated mul_ediv_cancel (since := "2025-03-05")]
theorem neg_mul_ediv_cancel (a b : Int) (h : b ≠ 0) : -(a * b) / b = -a := by
  rw [neg_ediv_of_dvd (Int.dvd_mul_left a b), mul_ediv_cancel _ h]

@[deprecated mul_ediv_cancel (since := "2025-03-05")]
theorem neg_mul_ediv_cancel_left (a b : Int) (h : a ≠ 0) : -(a * b) / a = -b := by
  rw [neg_ediv_of_dvd (Int.dvd_mul_right a b), mul_ediv_cancel_left _ h]

@[simp] theorem ediv_one : ∀ a : Int, a / 1 = a
  | (_:Nat) => congrArg Nat.cast (Nat.div_one _)
  | -[_+1]  => congrArg negSucc (Nat.div_one _)

@[simp] theorem emod_one (a : Int) : a % 1 = 0 := by
  simp [emod_def, Int.one_mul, Int.sub_self]

@[deprecated sub_emod_right (since := "2025-04-11")]
theorem emod_sub_cancel (x y : Int) : (x - y) % y = x % y :=
  sub_emod_right ..

@[simp] theorem add_neg_emod_self (a b : Int) : (a + -b) % b = a % b := by
  rw [Int.add_neg_eq_sub, sub_emod_right]

@[simp] theorem neg_add_emod_self (a b : Int) : (-a + b) % a = b % a := by
  rw [Int.add_comm, add_neg_emod_self]

/-- If `a % b = c` then `b` divides `a - c`. -/
theorem dvd_self_sub_of_emod_eq {a b : Int} : {c : Int} → a % b = c → b ∣ a - c
  | _, rfl => dvd_self_sub_emod

@[deprecated dvd_self_sub_of_emod_eq (since := "2025-04-12")]
theorem dvd_sub_of_emod_eq {a b : Int} : {c : Int} → a % b = c → b ∣ a - c :=
  dvd_self_sub_of_emod_eq

theorem dvd_sub_self_of_emod_eq {a b : Int} : {c : Int} → a % b = c → b ∣ c - a
  | _, rfl => dvd_emod_sub_self

protected theorem eq_mul_of_ediv_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by rw [← H2, Int.mul_ediv_cancel' H1]

protected theorem ediv_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_ediv_eq_right H', Int.ediv_eq_of_eq_mul_right H⟩

protected theorem ediv_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a / b = c ↔ a = c * b := by
  rw [Int.mul_comm]; exact Int.ediv_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_ediv_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_ediv_eq_right H1 H2]

protected theorem eq_zero_of_ediv_eq_zero {d n : Int} (h : d ∣ n) (H : n / d = 0) : n = 0 := by
  rw [← Int.mul_ediv_cancel' h, H, Int.mul_zero]

theorem sub_ediv_of_dvd_sub {a b c : Int}
    (hcab : c ∣ a - b) : (a - b) / c = a / c - b / c := by
  rw [← Int.add_sub_cancel ((a - b) / c), ← Int.add_ediv_of_dvd_left hcab, Int.sub_add_cancel]

@[simp] protected theorem ediv_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (ediv · d)⟩
  rw [← Int.mul_ediv_cancel' hda, ← Int.mul_ediv_cancel' hdb, h]

theorem ediv_sign : ∀ a b, a / sign b = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

protected theorem sign_eq_ediv_natAbs (a : Int) : sign a = a / (natAbs a) :=
  if az : a = 0 then by simp [az] else
    (Int.ediv_eq_of_eq_mul_left (ofNat_ne_zero.2 <| natAbs_ne_zero.2 az)
      (sign_mul_natAbs _).symm).symm

theorem dvd_mul_of_ediv_dvd {a b c : Int} (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c := by
  obtain ⟨e, rfl⟩ := hdiv
  rw [← Int.mul_assoc, Int.mul_comm _ (a / b), Int.ediv_mul_cancel h]
  exact Int.dvd_mul_right a e

@[simp] theorem ediv_dvd_iff_dvd_mul {a b c : Int} (h : b ∣ a) (hb : b ≠ 0) : a / b ∣ c ↔ a ∣ b * c :=
  exists_congr <| fun d ↦ by
  have := Int.dvd_trans (Int.dvd_mul_left _ _) (Int.mul_dvd_mul_left d h)
  rw [eq_comm, Int.mul_comm, ← Int.mul_ediv_assoc d h, Int.ediv_eq_iff_eq_mul_right hb this,
    Int.mul_comm, eq_comm]

theorem mul_dvd_of_dvd_ediv {a b c : Int} (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have ⟨d, hd⟩ := h
  ⟨d, by simpa [Int.mul_comm, Int.mul_left_comm] using Int.eq_mul_of_ediv_eq_left hcb hd⟩

theorem dvd_ediv_of_mul_dvd {a b c : Int} (h : a * b ∣ c) : b ∣ c / a := by
  obtain rfl | ha := Decidable.em (a = 0)
  · simp
  · obtain ⟨d, rfl⟩ := h
    simp [Int.mul_assoc, ha]

@[simp] theorem dvd_ediv_iff_mul_dvd {a b c : Int} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨mul_dvd_of_dvd_ediv hbc, dvd_ediv_of_mul_dvd⟩

theorem ediv_dvd_ediv : ∀ {a b c : Int}, a ∣ b → b ∣ c → b / a ∣ c / a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ =>
    if az : a = 0 then by simp [az]
    else by
      rw [Int.mul_ediv_cancel_left _ az, Int.mul_assoc, Int.mul_ediv_cancel_left _ az]
      apply Int.dvd_mul_right

theorem ediv_dvd_of_dvd {m n : Int} (hmn : m ∣ n) : n / m ∣ n := by
  obtain rfl | hm := Decidable.em (m = 0)
  · simpa using hmn
  · obtain ⟨a, ha⟩ := hmn
    simp [ha, Int.mul_ediv_cancel_left _ hm, Int.dvd_mul_left]

theorem emod_natAbs_of_nonneg {x : Int} (h : 0 ≤ x) {n : Nat} :
    x.natAbs % n = (x % n).toNat := by
  match x, h with
  | (x : Nat), _ => rw [Int.natAbs_natCast, Int.ofNat_mod_ofNat, Int.toNat_natCast]

theorem emod_natAbs_of_neg {x : Int} (h : x < 0) {n : Nat} (w : n ≠ 0) :
    x.natAbs % n = if (n : Int) ∣ x then 0 else n - (x % n).toNat := by
  match x, h with
  | -(x + 1 : Nat), _ =>
    rw [Int.natAbs_neg]
    rw [Int.natAbs_cast]
    rw [Int.neg_emod]
    simp only [Int.dvd_neg]
    simp only [Int.natCast_dvd_natCast]
    split <;> rename_i h
    · rw [Nat.mod_eq_zero_of_dvd h]
    · rw [← Int.natCast_emod]
      simp only [Int.natAbs_natCast]
      have : (x + 1) % n < n := Nat.mod_lt (x + 1) (by omega)
      omega

/-! ### `/` and ordering -/

protected theorem ediv_mul_le (a : Int) {b : Int} (H : b ≠ 0) : a / b * b ≤ a :=
  Int.le_of_sub_nonneg <| by rw [Int.mul_comm, ← emod_def]; apply emod_nonneg _ H

theorem le_of_mul_le_mul_left {a b c : Int} (w : a * b ≤ a * c) (h : 0 < a) : b ≤ c := by
  have w := Int.sub_nonneg_of_le w
  rw [← Int.mul_sub] at w
  have w := Int.ediv_nonneg w (Int.le_of_lt h)
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_gt h)] at w
  exact Int.le_of_sub_nonneg w

theorem le_of_mul_le_mul_right {a b c : Int} (w : b * a ≤ c * a) (h : 0 < a) : b ≤ c := by
  rw [Int.mul_comm b, Int.mul_comm c] at w
  exact le_of_mul_le_mul_left w h

protected theorem mul_le_mul_iff_of_pos_right {a b c : Int} (ha : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  ⟨(le_of_mul_le_mul_right · ha), (Int.mul_le_mul_of_nonneg_right · (Int.le_of_lt ha))⟩

protected theorem mul_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a := by
  simpa using (Int.mul_le_mul_iff_of_pos_right hb : 0 * b ≤ a * b ↔ 0 ≤ a)

protected theorem ediv_le_of_le_mul {a b c : Int} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
  le_of_mul_le_mul_right (Int.le_trans (Int.ediv_mul_le _ (Int.ne_of_gt H)) H') H

protected theorem ediv_nonpos_of_nonpos_of_neg {n s : Int} (h : n ≤ 0) (h2 : 0 < s) : n / s ≤ 0 :=
  Int.ediv_le_of_le_mul h2 (by simp [h])

protected theorem mul_lt_of_lt_ediv {a b c : Int} (H : 0 < c) (H3 : a < b / c) : a * c < b :=
  Int.lt_of_not_ge <| mt (Int.ediv_le_of_le_mul H) (Int.not_le_of_gt H3)

protected theorem mul_le_of_le_ediv {a b c : Int} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right H2 (Int.le_of_lt H1))
    (Int.ediv_mul_le _ (Int.ne_of_gt H1))

protected theorem ediv_lt_of_lt_mul {a b c : Int} (H : 0 < c) (H' : a < b * c) : a / c < b :=
  Int.lt_of_not_ge <| mt (Int.mul_le_of_le_ediv H) (Int.not_le_of_gt H')

theorem lt_of_mul_lt_mul_left {a b c : Int} (w : a * b < a * c) (h : 0 ≤ a) : b < c := by
  rcases Int.lt_trichotomy b c with lt | rfl | gt
  · exact lt
  · exact False.elim (Int.lt_irrefl _ w)
  · rcases Int.lt_trichotomy a 0 with a_lt | rfl | a_gt
    · exact False.elim (Int.lt_irrefl _ (Int.lt_of_lt_of_le a_lt h))
    · exact False.elim (Int.lt_irrefl b (by simp at w))
    · have := le_of_mul_le_mul_left (Int.le_of_lt w) a_gt
      exact False.elim (Int.lt_irrefl _ (Int.lt_of_lt_of_le gt this))

theorem lt_of_mul_lt_mul_right {a b c : Int} (w : b * a < c * a) (h : 0 ≤ a) : b < c := by
  rw [Int.mul_comm b, Int.mul_comm c] at w
  exact lt_of_mul_lt_mul_left w h

protected theorem le_ediv_of_mul_le {a b c : Int} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b / c :=
  le_of_lt_add_one <|
    lt_of_mul_lt_mul_right (Int.lt_of_le_of_lt H2 (lt_ediv_add_one_mul_self _ H1)) (Int.le_of_lt H1)

protected theorem le_ediv_iff_mul_le {a b c : Int} (H : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
  ⟨Int.mul_le_of_le_ediv H, Int.le_ediv_of_mul_le H⟩

protected theorem lt_mul_of_ediv_lt {a b c : Int} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
  Int.lt_of_not_ge <| mt (Int.le_ediv_of_mul_le H1) (Int.not_le_of_gt H2)

protected theorem ediv_lt_iff_lt_mul {a b c : Int} (H : 0 < c) : a / c < b ↔ a < b * c :=
  ⟨Int.lt_mul_of_ediv_lt H, Int.ediv_lt_of_lt_mul H⟩

theorem ediv_le_iff_le_mul {k x y : Int} (h : 0 < k) : x / k ≤ y ↔ x < y * k + k := by
  rw [Int.le_iff_lt_add_one, Int.ediv_lt_iff_lt_mul h, Int.add_mul]
  omega

protected theorem le_mul_of_ediv_le {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a / b ≤ c) :
    a ≤ c * b := by
  rw [← Int.ediv_mul_cancel H2]; exact Int.mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_ediv_of_mul_lt {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) :
    a < c / b :=
  Int.lt_of_not_ge <| mt (Int.le_mul_of_ediv_le H1 H2) (Int.not_le_of_gt H3)

protected theorem lt_ediv_iff_mul_lt {a b : Int} {c : Int} (H : 0 < c) (H' : c ∣ b) :
    a < b / c ↔ a * c < b :=
  ⟨Int.mul_lt_of_lt_ediv H, Int.lt_ediv_of_mul_lt (Int.le_of_lt H) H'⟩

theorem ediv_pos_of_pos_of_dvd {a b : Int} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a / b :=
  Int.lt_ediv_of_mul_lt H2 H3 (by rwa [Int.zero_mul])

theorem ediv_eq_ediv_of_mul_eq_mul {a b c d : Int}
    (H2 : d ∣ c) (H3 : b ≠ 0) (H4 : d ≠ 0) (H5 : a * d = b * c) : a / b = c / d :=
  Int.ediv_eq_of_eq_mul_right H3 <| by
    rw [← Int.mul_ediv_assoc _ H2]; exact (Int.ediv_eq_of_eq_mul_left H4 H5.symm).symm

theorem ediv_eq_iff_of_pos {k x y : Int} (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x < y * k + k := by
  rw [Int.eq_iff_le_and_ge, and_comm, Int.le_ediv_iff_mul_le h, Int.ediv_le_iff_le_mul h]

theorem add_ediv_of_pos {a b c : Int} (h : 0 < c) :
    (a + b) / c = a / c + b / c + if c ≤ a % c + b % c then 1 else 0 := by
  have h' : c ≠ 0 := by omega
  conv => lhs; rw [← Int.ediv_add_emod a c]
  rw [Int.add_assoc, Int.mul_add_ediv_left _ _ h']
  conv => lhs; rw [← Int.ediv_add_emod b c]
  rw [Int.add_comm (a % c), Int.add_assoc, Int.mul_add_ediv_left _ _ h',
    ← Int.add_assoc, Int.add_comm (b % c)]
  congr
  rw [Int.ediv_eq_iff_of_pos h]
  have := emod_lt_of_pos a h
  have := emod_lt_of_pos b h
  constructor
  · have := emod_nonneg a h'
    have := emod_nonneg b h'
    split <;> · simp; omega
  · split <;> · simp; omega

theorem add_ediv {a b c : Int} (h : c ≠ 0) :
    (a + b) / c = a / c + b / c + if c.natAbs ≤ a % c + b % c then c.sign else 0 := by
  induction c using wlog_sign
  case inv => simp; omega
  rename_i c
  norm_cast at h
  have : 0 < (c : Int) := by omega
  simp [sign_natCast_of_ne_zero h, add_ediv_of_pos this]

protected theorem ediv_le_ediv {a b c : Int} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
  Int.le_ediv_of_mul_le H (Int.le_trans (Int.ediv_mul_le _ (Int.ne_of_gt H)) H')

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
theorem not_dvd_iff_lt_mul_succ (m : Int) (hn : 0 < n) :
    ¬n ∣ m ↔ (∃ k, n * k < m ∧ m < n * (k + 1)) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [dvd_iff_emod_eq_zero, ← Ne] at h
    rw [← emod_add_ediv m n]
    refine ⟨m / n, Int.lt_add_of_pos_left _ ?_, ?_⟩
    · have := emod_nonneg m (Int.ne_of_gt hn)
      omega
    · rw [Int.add_comm _ (1 : Int), Int.mul_add, Int.mul_one]
      exact Int.add_lt_add_right (emod_lt_of_pos _ hn) _
  · rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩
    replace h1k := lt_of_mul_lt_mul_left h1k (by omega)
    replace h2k := lt_of_mul_lt_mul_left h2k (by omega)
    rw [Int.lt_add_one_iff, ← Int.not_lt] at h2k
    exact h2k h1k

/-! ### tdiv -/

-- `tdiv` analogues of `ediv` lemmas from `Bootstrap.lean`

@[simp] protected theorem tdiv_neg : ∀ a b : Int, a.tdiv (-b) = -(a.tdiv b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero]; rfl
  | ofNat _, -[_+1] | -[_+1], succ _ => (Int.neg_neg _).symm
  | ofNat _, succ _ | -[_+1], 0 => by simp [Int.tdiv, Int.neg_zero, ← Int.negSucc_eq]
  | -[_+1], -[_+1] => by simp only [tdiv, neg_negSucc]

/-!
There are no lemmas
* `add_mul_tdiv_right : c ≠ 0 → (a + b * c).tdiv c = a.tdiv c + b`
* `add_mul_tdiv_left : b ≠ 0 → (a + b * c).tdiv b = a.tdiv b + c`
* (similarly `mul_add_tdiv_right`, `mul_add_tdiv_left`)
* `add_tdiv_of_dvd_right : c ∣ b → (a + b).tdiv c = a.tdiv c + b.tdiv c`
* `add_tdiv_of_dvd_left : c ∣ a → (a + b).tdiv c = a.tdiv c + b.tdiv c`
because these statements are all incorrect, and require awkward conditional off-by-one corrections.
-/

@[simp] theorem mul_tdiv_cancel (a : Int) {b : Int} (H : b ≠ 0) : (a * b).tdiv b = a := by
  rw [tdiv_eq_ediv_of_dvd (Int.dvd_mul_left a b), mul_ediv_cancel _ H]

@[simp] theorem mul_tdiv_cancel_left (b : Int) (H : a ≠ 0) : (a * b).tdiv a = b :=
  Int.mul_comm .. ▸ Int.mul_tdiv_cancel _ H

-- `tdiv` analogues of `ediv` lemmas given above

-- There are no lemmas `tdiv_nonneg_iff_of_pos`, `tdiv_neg_of_neg_of_pos`, or `negSucc_tdiv`
-- corresponding to `ediv_nonneg_iff_of_pos`, `ediv_neg_of_neg_of_pos`, or `negSucc_ediv` as they require awkward corrections.

protected theorem tdiv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.tdiv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

theorem tdiv_nonneg_of_nonpos_of_nonpos {a b : Int} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a.tdiv b := by
  rw [tdiv_eq_ediv]
  split <;> rename_i h
  · simpa using ediv_nonneg_of_nonpos_of_nonpos Ha Hb
  · simp at h
    by_cases h' : b = 0
    · subst h'
      simp
    · replace h' : b < 0 := by omega
      rw [sign_eq_neg_one_of_neg h']
      have : 0 < a / b := by
        by_cases h'' : a = 0
        · subst h''
          simp at h
        · replace h'' : a < 0 := by omega
          exact ediv_pos_of_neg_of_neg h'' h'
      omega

protected theorem tdiv_nonpos_of_nonneg_of_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a.tdiv b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.tdiv_neg .. ▸ Int.tdiv_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

@[deprecated Int.tdiv_nonpos_of_nonneg_of_nonpos (since := "2025-03-04")]
abbrev tdiv_nonpos := @Int.tdiv_nonpos_of_nonneg_of_nonpos

theorem tdiv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.tdiv b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg Nat.cast <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

@[simp] theorem mul_tdiv_mul_of_pos {a : Int}
    (b c : Int) (H : 0 < a) : (a * b).tdiv (a * c) = b.tdiv c := by
  rw [tdiv_eq_ediv, mul_ediv_mul_of_pos _ _ H, tdiv_eq_ediv]
  simp only [sign_mul]
  by_cases h : 0 ≤ b
  · rw [if_pos, if_pos (.inl h)]
    left
    exact Int.mul_nonneg (Int.le_of_lt H) h
  · have H' : a ≠ 0 := by omega
    simp only [Int.mul_dvd_mul_iff_left H']
    by_cases h' : c ∣ b
    · simp [h']
    · rw [if_neg, if_neg]
      · simp [sign_eq_one_of_pos H]
      · simp [h']; omega
      · simp_all only [Int.not_le, ne_eq, or_false]
        exact Int.mul_neg_of_pos_of_neg H h

@[simp] theorem mul_tdiv_mul_of_pos_left
    (a : Int) {b : Int} (c : Int) (H : 0 < b) : (a * b).tdiv (c * b) = a.tdiv c := by
  rw [Int.mul_comm, Int.mul_comm c, mul_tdiv_mul_of_pos _ _ H]

protected theorem tdiv_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a.tdiv b = c := by rw [H2, Int.mul_tdiv_cancel_left _ H1]

protected theorem eq_tdiv_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c.tdiv a :=
  (Int.tdiv_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem tdiv_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a.tdiv b = c :=
  Int.tdiv_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem eq_tdiv_of_mul_eq_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a * b = c) : a = c.tdiv b :=
  (Int.tdiv_eq_of_eq_mul_left H1 H2.symm).symm

@[simp] protected theorem tdiv_self {a : Int} (H : a ≠ 0) : a.tdiv a = 1 := by
  have := Int.mul_tdiv_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem neg_tdiv : ∀ a b : Int, (-a).tdiv b = -(a.tdiv b)
  | 0, n => by simp [Int.neg_zero]
  | succ _, (n:Nat) => by simp [tdiv, ← Int.negSucc_eq]
  | -[_+1], 0 | -[_+1], -[_+1] => by
    simp only [tdiv, neg_negSucc, Int.neg_neg]
  | succ _, -[_+1] | -[_+1], succ _ => (Int.neg_neg _).symm

protected theorem neg_tdiv_neg (a b : Int) : (-a).tdiv (-b) = a.tdiv b := by
  simp [Int.tdiv_neg, Int.neg_tdiv, Int.neg_neg]

theorem sign_tdiv (a b : Int) : sign (a.tdiv b) = if natAbs a < natAbs b then 0 else sign a * sign b := by
  induction b using wlog_sign
  case inv => simp; split <;> simp [Int.mul_neg]
  case w b =>
    induction a using wlog_sign
    case inv => simp; split <;> simp [Int.neg_mul]
    case w a =>
      rw [tdiv_eq_ediv_of_nonneg (by simp), sign_ediv]
      simp

@[simp] theorem natAbs_tdiv (a b : Int) : natAbs (a.tdiv b) = (natAbs a).div (natAbs b) :=
  match a, b, Int.eq_nat_or_neg a, Int.eq_nat_or_neg b with
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inl rfl⟩ => rfl
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.tdiv_neg, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inl rfl⟩ => by rw [Int.neg_tdiv, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.neg_tdiv_neg, natAbs_neg, natAbs_neg]; rfl

/-! ### tmod -/

-- `tmod` analogues of `emod` lemmas from `Bootstrap.lean`

theorem ofNat_tmod (m n : Nat) : (↑(m % n) : Int) = tmod m n := rfl

theorem tmod_nonneg : ∀ {a : Int} (b : Int), 0 ≤ a → 0 ≤ tmod a b
  | ofNat _, -[_+1], _ | ofNat _, ofNat _, _ => natCast_nonneg _

@[simp] theorem tmod_neg (a b : Int) : tmod a (-b) = tmod a b := by
  rw [tmod_def, tmod_def, Int.tdiv_neg, Int.neg_mul_neg]

@[simp] theorem neg_tmod (a b : Int) : tmod (-a) b = -tmod a b := by
  rw [tmod_def, Int.neg_tdiv, Int.mul_neg, tmod_def]
  omega

theorem tmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : tmod a b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨n, rfl⟩ => ofNat_lt.2 <| Nat.mod_lt _ n.succ_pos
  | -[_+1], _, ⟨n, rfl⟩ => Int.lt_of_le_of_lt
    (Int.neg_nonpos_of_nonneg <| natCast_nonneg _) (natCast_pos.2 n.succ_pos)

theorem lt_tmod_of_pos (a : Int) {b : Int} (H : 0 < b) : -b < tmod a b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨n, rfl⟩ => by rw [ofNat_eq_coe, ← Int.natCast_succ, ← ofNat_tmod]; omega
  | -[a+1], _, ⟨n, rfl⟩ => by
    rw [negSucc_eq, neg_tmod, ← Int.natCast_add_one, ← Int.natCast_add_one, ← ofNat_tmod]
    have : (a + 1) % (n + 1) < n + 1 := Nat.mod_lt _ (Nat.zero_lt_succ n)
    omega

-- The following statements for `tmod` are false:
-- `add_mul_tmod_self_right {a b c : Int} : (a + b * c).tmod c = a.tmod c`
-- `add_mul_tmod_self_left (a b c : Int) : (a + b * c).tmod b = a.tmod b`
-- `tmod_add_tmod (m n k : Int) : (m.tmod n + k).tmod n = (m + k).tmod n`
-- `add_tmod_tmod (m n k : Int) : (m + n.tmod k).tmod k = (m + n).tmod k`
-- `add_tmod (a b n : Int) : (a + b).tmod n = (a.tmod n + b.tmod n).tmod n`
-- `add_tmod_eq_add_tmod_right {m n k : Int} (i : Int) : (m.tmod n = k.tmod n) → (m + i).tmod n = (k + i).tmod n`
-- `tmod_add_cancel_right {m n k : Int} (i) : (m + i).tmod n = (k + i).tmod n ↔ m.tmod n = k.tmod n`
-- `sub_tmod (a b n : Int) : (a - b).tmod n = (a.tmod n - b.tmod n).tmod n`

@[simp] theorem mul_tmod_left (a b : Int) : (a * b).tmod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.tmod_def, Int.mul_tdiv_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_tmod_right (a b : Int) : (a * b).tmod a = 0 := by
  rw [Int.mul_comm, mul_tmod_left]

theorem mul_tmod (a b n : Int) : (a * b).tmod n = (a.tmod n * b.tmod n).tmod n := by
  induction a using wlog_sign
  case inv => simp [Int.neg_mul]
  induction b using wlog_sign
  case inv => simp [Int.mul_neg]
  induction n using wlog_sign
  case inv => simp
  simp only [← Int.natCast_mul, ← ofNat_tmod]
  rw [Nat.mul_mod]

@[simp] theorem tmod_self {a : Int} : a.tmod a = 0 := by
  have := mul_tmod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem tmod_tmod_of_dvd (n : Int) {m k : Int}
    (h : m ∣ k) : (n.tmod k).tmod m = n.tmod m := by
  induction n using wlog_sign
  case inv => simp
  induction k using wlog_sign
  case inv => simp [Int.dvd_neg]
  induction m using wlog_sign
  case inv => simp
  simp only [← ofNat_tmod]
  norm_cast at h
  rw [Nat.mod_mod_of_dvd _ h]

theorem tmod_tmod (a b : Int) : (a.tmod b).tmod b = a.tmod b := by simp

theorem tmod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → tmod b a = 0
  | _, _, ⟨_, rfl⟩ => mul_tmod_right ..

-- `tmod` analogues of `emod` lemmas from above

theorem tmod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : tmod a b = a := by
  rw [tmod_eq_emod_of_nonneg H1, emod_eq_of_lt H1 H2]

theorem sign_tmod (a b : Int) : sign (tmod a b) = if b ∣ a then 0 else sign a := by
  if hb : b = 0 then
    subst hb
    split <;> simp_all
  else
    induction a using wlog_sign
    case inv a => split <;> simp_all
    rename_i a
    match a with
    | 0 => simp
    | (a + 1) =>
      simp
      split
      · simp [tmod_eq_zero_of_dvd, *]
      · norm_cast
        rw [tmod_eq_emod_of_nonneg (by omega)]
        rw [sign_emod _ hb]
        simp_all

@[simp] theorem natAbs_tmod (a b : Int) : natAbs (tmod a b) = natAbs a % natAbs b := by
  induction a using wlog_sign
  case inv => simp
  induction b using wlog_sign
  case inv => simp
  norm_cast

/-! properties of `tdiv` and `tmod` -/

-- Analogues of statements about `ediv` and `emod` from `Bootstrap.lean`

theorem mul_tdiv_cancel_of_tmod_eq_zero {a b : Int} (H : a.tmod b = 0) : b * (a.tdiv b) = a := by
  have := tmod_add_tdiv a b; rwa [H, Int.zero_add] at this

theorem tdiv_mul_cancel_of_tmod_eq_zero {a b : Int} (H : a.tmod b = 0) : a.tdiv b * b = a := by
  rw [Int.mul_comm, mul_tdiv_cancel_of_tmod_eq_zero H]

theorem dvd_of_tmod_eq_zero {a b : Int} (H : tmod b a = 0) : a ∣ b :=
  ⟨b.tdiv a, (mul_tdiv_cancel_of_tmod_eq_zero H).symm⟩

theorem dvd_iff_tmod_eq_zero {a b : Int} : a ∣ b ↔ tmod b a = 0 :=
  ⟨tmod_eq_zero_of_dvd, dvd_of_tmod_eq_zero⟩

protected theorem tdiv_mul_cancel {a b : Int} (H : b ∣ a) : a.tdiv b * b = a :=
  tdiv_mul_cancel_of_tmod_eq_zero (tmod_eq_zero_of_dvd H)

protected theorem mul_tdiv_cancel' {a b : Int} (H : a ∣ b) : a * b.tdiv a = b := by
  rw [Int.mul_comm, Int.tdiv_mul_cancel H]

theorem neg_tmod_self (a : Int) : (-a).tmod a = 0 := by
  simp

theorem lt_tdiv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.tdiv b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.tmod_def .. ▸ tmod_lt_of_pos _ H

protected theorem mul_tdiv_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b).tdiv c = a * (b.tdiv c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_tdiv_cancel_left _ cz, Int.mul_tdiv_cancel_left _ cz]

protected theorem mul_tdiv_assoc' (b : Int) {a c : Int} (h : c ∣ a) :
    (a * b).tdiv c = a.tdiv c * b := by
  rw [Int.mul_comm, Int.mul_tdiv_assoc _ h, Int.mul_comm]

theorem neg_tdiv_of_dvd : ∀ {a b : Int}, b ∣ a → (-a).tdiv b = -(a.tdiv b)
  | _, b, ⟨c, rfl⟩ => by
    by_cases bz : b = 0
    · simp [bz]
    · rw [Int.neg_mul_eq_mul_neg, Int.mul_tdiv_cancel_left _ bz, Int.mul_tdiv_cancel_left _ bz]

-- `sub_tdiv_of_dvd (a : Int) {b c : Int} (hcb : c ∣ b) : (a - b).tdiv c = a.tdiv c - b.tdiv c` is false in general

theorem tdiv_dvd_tdiv : ∀ {a b c : Int}, a ∣ b → b ∣ c → b.tdiv a ∣ c.tdiv a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ => by
    by_cases az : a = 0
    · simp [az]
    · rw [Int.mul_tdiv_cancel_left _ az, Int.mul_assoc, Int.mul_tdiv_cancel_left _ az]
      apply Int.dvd_mul_right

-- Analogues of statements about `emod` and `ediv` from above.

theorem mul_tdiv_cancel_of_dvd {a b : Int} (H : b ∣ a) : b * (a.tdiv b) = a :=
  mul_tdiv_cancel_of_tmod_eq_zero (tmod_eq_zero_of_dvd H)

theorem tdiv_mul_cancel_of_dvd {a b : Int} (H : b ∣ a) : a.tdiv b * b = a :=
  tdiv_mul_cancel_of_tmod_eq_zero (tmod_eq_zero_of_dvd H)

theorem tmod_two_eq (x : Int) : x.tmod 2 = -1 ∨ x.tmod 2 = 0 ∨ x.tmod 2 = 1 := by
  have h₁ : -2 < x.tmod 2 := Int.lt_tmod_of_pos x (by decide)
  have h₂ : x.tmod 2 < 2 := Int.tmod_lt_of_pos x (by decide)
  match x.tmod 2, h₁, h₂ with
  | -1, _, _ => simp
  | 0, _, _ => simp
  | 1, _, _ => simp

-- The following statements about `tmod` are false:
-- `add_tmod_eq_add_tmod_left {m n k : Int} (i : Int) (H : m.tmod n = k.tmod n) : (i + m).tmod n = (i + k).tmod n`
-- `tmod_add_cancel_left {m n k i : Int} : (i + m).tmod n = (i + k).tmod n ↔ m.tmod n = k.tmod n`
-- `tmod_sub_cancel_right {m n k : Int} (i) : (m - i).tmod n = (k - i).tmod n ↔ m.tmod n = k.tmod n`
-- `tmod_eq_tmod_iff_tmod_sub_eq_zero {m n k : Int} : m.tmod n = k.tmod n ↔ (m - k).tmod n = 0`

protected theorem tdiv_tmod_unique {a b r q : Int} (ha : 0 ≤ a) (hb : b ≠ 0) :
    a.tdiv b = q ∧ a.tmod b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < natAbs b := by
  rw [tdiv_eq_ediv_of_nonneg ha, tmod_eq_emod_of_nonneg ha]
  by_cases hb' : 0 < b
  · rw [Int.ediv_emod_unique hb']
    omega
  · replace hb' : 0 < -b := by omega
    have := Int.ediv_emod_unique (a := a) (q := -q) (r := r) hb'
    simp at this
    simp [this, Int.neg_mul, Int.mul_neg]
    omega

protected theorem tdiv_tmod_unique' {a b r q : Int} (ha : a ≤ 0) (hb : b ≠ 0) :
    a.tdiv b = q ∧ a.tmod b = r ↔ r + b * q = a ∧ -natAbs b < r ∧ r ≤ 0 := by
  have := Int.tdiv_tmod_unique (a := -a) (q := -q) (r := -r) (by omega) hb
  simp at this
  simp [this, Int.mul_neg]
  omega

@[simp] theorem mul_tmod_mul_of_pos
    {a : Int} (b c : Int) (H : 0 < a) : (a * b).tmod (a * c) = a * (b.tmod c) := by
  rw [tmod_def, tmod_def, mul_tdiv_mul_of_pos _ _ H, Int.mul_sub, Int.mul_assoc]

theorem natAbs_tdiv_le_natAbs (a b : Int) : natAbs (a.tdiv b) ≤ natAbs a := by
  induction a using wlog_sign
  case inv => simp
  induction b using wlog_sign
  case inv => simp
  simpa using Nat.div_le_self _ _

theorem tdiv_le_self {a : Int} (b : Int) (Ha : 0 ≤ a) : a.tdiv b ≤ a := by
  have := Int.le_trans le_natAbs (ofNat_le.2 <| natAbs_tdiv_le_natAbs a b)
  rwa [natAbs_of_nonneg Ha] at this

theorem dvd_tmod_sub_self {x m : Int} : m ∣ x.tmod m - x := by
  rw [tmod_eq_emod]
  have := dvd_emod_sub_self (x := x) (m := m)
  split
  · simpa
  · rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub]
    exact Int.dvd_sub this dvd_natAbs_self

theorem dvd_self_sub_tmod {x m : Int} : m ∣ x - x.tmod m :=
  Int.dvd_neg.1 (by simpa only [Int.neg_sub] using dvd_tmod_sub_self)

theorem neg_mul_tmod_right (a b : Int) : (-(a * b)).tmod a = 0 := by
  simp

theorem neg_mul_tmod_left (a b : Int) : (-(a * b)).tmod b = 0 := by
  simp

@[simp] protected theorem tdiv_one : ∀ a : Int, a.tdiv 1 = a
  | (n:Nat) => congrArg ofNat (Nat.div_one _)
  | -[n+1] => by simp [Int.tdiv]; rfl

@[simp] theorem tmod_one (a : Int) : tmod a 1 = 0 := by
  simp [tmod_def, Int.tdiv_one, Int.one_mul, Int.sub_self]

-- The following statements about `tmod` are false:
-- `tmod_sub_cancel (x y : Int) : (x - y).tmod y = x.tmod y`
-- `add_neg_tmod_self (a b : Int) : (a + -b).tmod b = a.tmod b`
-- `neg_add_tmod_self (a b : Int) : (-a + b).tmod a = b.tmod a`

theorem dvd_self_sub_of_tmod_eq {a b c : Int} (h : a.tmod b = c) : b ∣ a - c :=
  h ▸ dvd_self_sub_tmod

theorem dvd_sub_self_of_tmod_eq {a b c : Int} (h : a.tmod b = c) : b ∣ c - a :=
  h ▸ dvd_tmod_sub_self

protected theorem eq_mul_of_tdiv_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a.tdiv b = c) : a = b * c := by rw [← H2, Int.mul_tdiv_cancel' H1]

protected theorem tdiv_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.tdiv b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_tdiv_eq_right H', Int.tdiv_eq_of_eq_mul_right H⟩

protected theorem tdiv_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.tdiv b = c ↔ a = c * b := by
  rw [Int.mul_comm]; exact Int.tdiv_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_tdiv_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a.tdiv b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_tdiv_eq_right H1 H2]

protected theorem eq_zero_of_tdiv_eq_zero {d n : Int} (h : d ∣ n) (H : n.tdiv d = 0) : n = 0 := by
  rw [← Int.mul_tdiv_cancel' h, H, Int.mul_zero]

-- `sub_tdiv_of_dvd_sub {a b c : Int} (hcab : c ∣ a - b) : (a - b).tdiv c = a.tdiv c - b.tdiv c` is false in general

@[simp] protected theorem tdiv_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a.tdiv d = b.tdiv d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (tdiv · d)⟩
  rw [← Int.mul_tdiv_cancel' hda, ← Int.mul_tdiv_cancel' hdb, h]

theorem tdiv_sign : ∀ a b, a.tdiv (sign b) = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

protected theorem sign_eq_tdiv_abs (a : Int) : sign a = a.tdiv (natAbs a) :=
  if az : a = 0 then by simp [az] else
    (Int.tdiv_eq_of_eq_mul_left (ofNat_ne_zero.2 <| natAbs_ne_zero.2 az)
      (sign_mul_natAbs _).symm).symm

@[simp high] protected theorem mul_le_mul_left {a b c : Int} (ha : 0 < a) : a * b ≤ a * c ↔ b ≤ c where
  mp hbc := Int.le_of_mul_le_mul_left hbc ha
  mpr hbc := Int.mul_le_mul_of_nonneg_left hbc <| Int.le_of_lt ha

@[simp high] protected theorem mul_le_mul_right {a b c : Int} (ha : 0 < a) : b * a ≤ c * a ↔ b ≤ c where
  mp hbc := Int.le_of_mul_le_mul_right hbc ha
  mpr hbc := Int.mul_le_mul_of_nonneg_right hbc <| Int.le_of_lt ha

@[simp high] protected theorem mul_lt_mul_left {a b c : Int} (ha : 0 < a) : a * b < a * c ↔ b < c where
  mp hbc := Int.lt_of_mul_lt_mul_left hbc <| Int.le_of_lt ha
  mpr hbc := Int.mul_lt_mul_of_pos_left hbc ha

@[simp high] protected theorem mul_lt_mul_right {a b c : Int} (ha : 0 < a) : b * a < c * a ↔ b < c where
  mp hbc := Int.lt_of_mul_lt_mul_right hbc <| Int.le_of_lt ha
  mpr hbc := Int.mul_lt_mul_of_pos_right hbc ha

@[simp high] protected theorem mul_le_mul_left_of_neg {a b c : Int} (ha : a < 0) :
    a * b ≤ a * c ↔ c ≤ b := by
  rw [← Int.neg_le_neg_iff, Int.neg_mul_eq_neg_mul, Int.neg_mul_eq_neg_mul,
    Int.mul_le_mul_left <| Int.neg_pos.2 ha]

@[simp high] protected theorem mul_le_mul_right_of_neg {a b c : Int} (ha : a < 0) :
    b * a ≤ c * a ↔ c ≤ b := by
  rw [← Int.neg_le_neg_iff, Int.neg_mul_eq_mul_neg, Int.neg_mul_eq_mul_neg,
    Int.mul_le_mul_right <| Int.neg_pos.2 ha]

@[simp high] protected theorem mul_lt_mul_left_of_neg {a b c : Int} (ha : a < 0) :
    a * b < a * c ↔ c < b := by
  rw [← Int.neg_lt_neg_iff, Int.neg_mul_eq_neg_mul, Int.neg_mul_eq_neg_mul,
    Int.mul_lt_mul_left <| Int.neg_pos.2 ha]

@[simp high] protected theorem mul_lt_mul_right_of_neg {a b c : Int} (ha : a < 0) :
    b * a < c * a ↔ c < b := by
  rw [← Int.neg_lt_neg_iff, Int.neg_mul_eq_mul_neg, Int.neg_mul_eq_mul_neg,
    Int.mul_lt_mul_right <| Int.neg_pos.2 ha]

theorem ediv_le_iff_of_dvd_of_pos {a b c : Int} (hb : 0 < b) (hba : b ∣ a) :
    a / b ≤ c ↔ a ≤ b * c := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_gt]

theorem ediv_le_iff_of_dvd_of_neg {a b c : Int}  (hb : b < 0) (hba : b ∣ a) :
    a / b ≤ c ↔ b * c ≤ a := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_lt]

theorem ediv_lt_iff_of_dvd_of_pos {a b c : Int} (hb : 0 < b) (hba : b ∣ a) :
    a / b < c ↔ a < b * c := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_gt]

theorem ediv_lt_iff_of_dvd_of_neg {a b c : Int} (hb : b < 0) (hba : b ∣ a) :
    a / b < c ↔ b * c < a := by
  obtain ⟨x, rfl⟩ := hba; simp [*, Int.ne_of_lt]

theorem le_ediv_iff_of_dvd_of_pos {a b c : Int} (hc : 0 < c) (hcb : c ∣ b) :
    a ≤ b / c ↔ c * a ≤ b := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_gt]

theorem le_ediv_iff_of_dvd_of_neg {a b c : Int} (hc : c < 0) (hcb : c ∣ b) :
    a ≤ b / c ↔ b ≤ c * a := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_lt]

theorem lt_ediv_iff_of_dvd_of_pos {a b c : Int} (hc : 0 < c) (hcb : c ∣ b) :
    a < b / c ↔ c * a < b := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_gt]

theorem lt_ediv_iff_of_dvd_of_neg {a b c : Int} (hc : c < 0) (hcb : c ∣ b) :
    a < b / c ↔ b < c * a := by
  obtain ⟨x, rfl⟩ := hcb; simp [*, Int.ne_of_lt]

theorem ediv_le_ediv_iff_of_dvd_of_pos_of_pos {a b c d : Int} (hb : 0 < b) (hd : 0 < d)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b ≤ c / d ↔ d * a ≤ c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

theorem ediv_le_ediv_iff_of_dvd_of_pos_of_neg {a b c d : Int} (hb : 0 < b) (hd : d < 0)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b ≤ c / d ↔ c * b ≤ d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

theorem ediv_le_ediv_iff_of_dvd_of_neg_of_pos {a b c d : Int} (hb : b < 0) (hd : 0 < d)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b ≤ c / d ↔ c * b ≤ d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

theorem ediv_le_ediv_iff_of_dvd_of_neg_of_neg {a b c d : Int} (hb : b < 0) (hd : d < 0)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b ≤ c / d ↔ d * a ≤ c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, d.mul_assoc, b.mul_comm]

theorem ediv_lt_ediv_iff_of_dvd_of_pos {a b c d : Int} (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b < c / d ↔ d * a < c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

theorem ediv_lt_ediv_iff_of_dvd_of_pos_of_neg {a b c d : Int} (hb : 0 < b) (hd : d < 0)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

theorem ediv_lt_ediv_iff_of_dvd_of_neg_of_pos {a b c d : Int} (hb : b < 0) (hd : 0 < d)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, Int.ne_of_gt, d.mul_assoc, b.mul_comm]

theorem ediv_lt_ediv_iff_of_dvd_of_neg_of_neg {a b c d : Int} (hb : b < 0) (hd : d < 0)
    (hba : b ∣ a) (hdc : d ∣ c) : a / b < c / d ↔ d * a < c * b := by
  obtain ⟨⟨x, rfl⟩, y, rfl⟩ := hba, hdc
  simp [*, Int.ne_of_lt, d.mul_assoc, b.mul_comm]

/-! ### `tdiv` and ordering -/

-- Theorems about `tdiv` and ordering, whose `ediv` analogues are in `Bootstrap.lean`.

theorem mul_tdiv_self_le {x k : Int} (h : 0 ≤ x) : k * (x.tdiv k) ≤ x := by
  by_cases w : k = 0
  · simp [w, h]
  · rw [tdiv_eq_ediv_of_nonneg h]
    apply mul_ediv_self_le w

theorem lt_mul_tdiv_self_add {x k : Int} (h : 0 < k) : x < k * (x.tdiv k) + k := by
  rw [tdiv_eq_ediv, sign_eq_one_of_pos h]
  have := lt_mul_ediv_self_add (x := x) h
  split <;> simp [Int.mul_add] <;> omega

-- Theorems about `tdiv` and ordering, whose `ediv` analogues proved above.

protected theorem tdiv_mul_le (a : Int) {b : Int} (hb : b ≠ 0) : a.tdiv b * b ≤ a + if 0 ≤ a then 0 else (b.natAbs - 1) :=
  Int.le_of_sub_nonneg <| by
    rw [Int.mul_comm, Int.add_comm, Int.add_sub_assoc, ← tmod_def]
    split
    · simp_all [tmod_nonneg]
    · match b, hb with
      | .ofNat (b + 1), _ =>
        have := lt_tmod_of_pos a (natCast_pos.2 (b.succ_pos))
        simp_all
        omega
      | .negSucc b, _ =>
        simp only [negSucc_eq, natAbs_neg, tmod_neg]
        have := lt_tmod_of_pos (b := b + 1) a (by omega)
        omega

protected theorem tdiv_le_of_le_mul {a b c : Int} (Hc : 0 < c) (H' : a ≤ b * c) : a.tdiv c ≤ b + if 0 ≤ a then 0 else 1 :=
  le_of_mul_le_mul_right (Int.le_trans (Int.tdiv_mul_le _ (by omega))
    (by
      split
      · simpa using H'
      · simp [Int.add_mul]
        omega)) Hc

-- We don't provide `tdiv` analogues of the lemmas
-- `mul_lt_of_lt_ediv`
-- `mul_le_of_le_ediv`
-- `ediv_lt_of_lt_mul`
-- `le_ediv_iff_mul_le`
-- `ediv_lt_iff_lt_mul`
-- `lt_ediv_iff_mul_lt`
-- as they would require quite awkward statements.

protected theorem le_tdiv_of_mul_le {a b c : Int} (H1 : 0 < c) (H2 : a * c ≤ b) : a ≤ b.tdiv c :=
  le_of_lt_add_one <|
    lt_of_mul_lt_mul_right (Int.lt_of_le_of_lt H2 (lt_tdiv_add_one_mul_self _ H1)) (Int.le_of_lt H1)

protected theorem lt_mul_of_tdiv_lt {a b c : Int} (H1 : 0 < c) (H2 : a.tdiv c < b) : a < b * c :=
  Int.lt_of_not_ge <| mt (Int.le_tdiv_of_mul_le H1) (Int.not_le_of_gt H2)

protected theorem le_mul_of_tdiv_le {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ a) (H3 : a.tdiv b ≤ c) :
    a ≤ c * b := by
  rw [← Int.tdiv_mul_cancel H2]; exact Int.mul_le_mul_of_nonneg_right H3 H1

protected theorem lt_tdiv_of_mul_lt {a b c : Int} (H1 : 0 ≤ b) (H2 : b ∣ c) (H3 : a * b < c) :
    a < c.tdiv b :=
  Int.lt_of_not_ge <| mt (Int.le_mul_of_tdiv_le H1 H2) (Int.not_le_of_gt H3)

theorem tdiv_pos_of_pos_of_dvd {a b : Int} (H1 : 0 < a) (H2 : 0 ≤ b) (H3 : b ∣ a) : 0 < a.tdiv b :=
  Int.lt_tdiv_of_mul_lt H2 H3 (by rwa [Int.zero_mul])

theorem tdiv_eq_tdiv_of_mul_eq_mul {a b c d : Int}
    (H2 : d ∣ c) (H3 : b ≠ 0) (H4 : d ≠ 0) (H5 : a * d = b * c) : a.tdiv b = c.tdiv d :=
  Int.tdiv_eq_of_eq_mul_right H3 <| by
    rw [← Int.mul_tdiv_assoc _ H2]; exact (Int.tdiv_eq_of_eq_mul_left H4 H5.symm).symm

theorem le_emod_self_add_one_iff {a b : Int} (h : 0 < b) : b ≤ a % b + 1 ↔ b ∣ a + 1 := by
  match b, h with
  | .ofNat 1, h => simp
  | .ofNat (b + 2), h =>
    simp only [ofNat_eq_coe, Int.natCast_add, cast_ofNat_Int] at *
    constructor
    · rw [dvd_iff_emod_eq_zero]
      intro w
      have := emod_lt_of_pos a h
      have : a % (b + 2) = b + 1 := by omega
      rw [add_emod, this, one_emod, if_neg (by omega)]
      have : (b + 1 + 1 : Int) = b + 2 := by omega
      rw [this, emod_self]
    · rintro ⟨d, w⟩
      replace w : a = (b + 2 : Int) * d - 1 := by omega
      subst w
      rw [emod_def, mul_sub_ediv_left _ _ (by omega), neg_one_ediv,
        sign_eq_one_of_pos (by omega), Int.mul_add]
      omega

@[deprecated le_emod_self_add_one_iff (since := "2025-04-12")]
theorem le_mod_self_add_one_iff {a b : Int} (h : 0 < b) : b ≤ a % b + 1 ↔ b ∣ a + 1 :=
  le_emod_self_add_one_iff h

theorem add_one_tdiv_of_pos {a b : Int} (h : 0 < b) :
    (a + 1).tdiv b = a.tdiv b + if (0 < a + 1 ∧ b ∣ a + 1) ∨ (a < 0 ∧ b ∣ a) then 1 else 0 := by
  match b, h with
  | .ofNat 1, h => simp; omega
  | .ofNat (b + 2), h =>
    simp only [ofNat_eq_coe]
    rw [tdiv_eq_ediv, add_ediv (by omega), tdiv_eq_ediv]
    simp only [Int.natCast_add, cast_ofNat_Int]
    have : 1 / (b + 2 : Int) = 0 := by rw [one_ediv]; omega
    rw [this]
    have one_mod : 1 % (b + 2 : Int) = 1 := emod_eq_of_lt (by omega) (by omega)
    rw [one_mod]
    have : ↑(b + 2 : Int).natAbs = (b + 2 : Int) := by omega
    rw [this]
    have : (b + 2 : Int).sign = 1 := sign_eq_one_of_pos (by omega)
    rw [this]
    have : (b + 2) ≤ a % (b + 2 : Int) + 1 ↔ (b + 2 : Int) ∣ a + 1 := le_emod_self_add_one_iff (by omega)
    simp only [this]
    simp only [Int.add_zero]
    split <;> rename_i h
    · simp only [h, or_true, ↓reduceIte, and_true]
      omega
    · simp only [h, or_false, and_false]
      by_cases h₂ : 0 ≤ a
      · simp only [Int.add_zero, h₂, true_or, ↓reduceIte, false_or]
        have : 0 ≤ a + 1 := by omega
        have : 0 < a + 1 := by omega
        have : ¬ a < 0 := by omega
        simp [*]
      · simp only [Int.add_zero, h₂, false_or]
        split
        · have : a = -1 := by omega
          simp_all
        · have : a < 0 := by omega
          simp only [true_and, this]
          split <;> simp

theorem add_one_tdiv {a b : Int} :
    (a + 1).tdiv b = a.tdiv b + if (0 < a + 1 ∧ b ∣ a + 1) ∨ (a < 0 ∧ b ∣ a) then b.sign else 0 := by
  if hb : b = 0 then
    simp [hb]
  else
    induction b using wlog_sign
    case inv => simp; omega
    rename_i c
    norm_cast at hb
    have : 0 < (c : Int) := by omega
    simp [sign_natCast_of_ne_zero hb, add_one_tdiv_of_pos this]

-- One could prove a general `add_tdiv` theorem giving `(a + b).tdiv c = a.tdiv c + b.tdiv c + ...`
-- but the error term would be very complicated.

protected theorem tdiv_le_tdiv {a b c : Int} (H : 0 < c) (H' : a ≤ b) : a.tdiv c ≤ b.tdiv c := by
  obtain ⟨d, rfl⟩ := Int.exists_add_of_le H'
  clear H'
  induction d with
  | zero => simp
  | succ d ih =>
    simp only [Int.natCast_add, cast_ofNat_Int, ← Int.add_assoc]
    rw [add_one_tdiv_of_pos (by omega)]
    omega

/-! ### fdiv -/

theorem add_mul_fdiv_right (a b : Int) {c : Int} (H : c ≠ 0) : (a + b * c).fdiv c = a.fdiv c + b := by
  rw [fdiv_eq_ediv, add_mul_ediv_right _ _ H, fdiv_eq_ediv]
  simp only [Int.dvd_add_left (Int.dvd_mul_left _ _)]
  split <;> omega

theorem add_mul_fdiv_left (a : Int) {b : Int}
    (c : Int) (H : b ≠ 0) : (a + b * c).fdiv b = a.fdiv b + c := by
  rw [Int.mul_comm, Int.add_mul_fdiv_right _ _ H]

theorem mul_add_fdiv_right (a c : Int) {b : Int} (H : b ≠ 0) : (a * b + c).fdiv b = c.fdiv b + a := by
  rw [Int.add_comm, add_mul_fdiv_right _ _ H]

theorem mul_add_fdiv_left (b : Int) {a : Int}
    (c : Int) (H : a ≠ 0) : (a * b + c).fdiv a = c.fdiv a + b := by
  rw [Int.add_comm, add_mul_fdiv_left _ _ H]

theorem sub_mul_fdiv_right (a b : Int) {c : Int} (H : c ≠ 0) : (a - b * c).fdiv c = a.fdiv c - b := by
  rw [Int.sub_eq_add_neg, ← Int.neg_mul, add_mul_fdiv_right _ _ H, Int.sub_eq_add_neg]

theorem sub_mul_fdiv_left (a : Int) {b : Int}
    (c : Int) (H : b ≠ 0) : (a - b * c).fdiv b = a.fdiv b - c := by
  rw [Int.sub_eq_add_neg, ← Int.mul_neg, add_mul_fdiv_left _ _ H, Int.sub_eq_add_neg]

theorem mul_sub_fdiv_right (a c : Int) {b : Int} (H : b ≠ 0) : (a * b - c).fdiv b = a + (-c).fdiv b := by
  rw [Int.sub_eq_add_neg, Int.add_comm, add_mul_fdiv_right _ _ H, Int.add_comm]

theorem mul_sub_fdiv_left (b : Int) {a : Int}
    (c : Int) (H : a ≠ 0) : (a * b - c).fdiv a = b + (-c).fdiv a := by
  rw [Int.sub_eq_add_neg, Int.add_comm, add_mul_fdiv_left _ _ H, Int.add_comm]

@[simp] theorem mul_fdiv_cancel (a : Int) {b : Int} (H : b ≠ 0) : fdiv (a * b) b = a :=
  if b0 : 0 ≤ b then by
    rw [fdiv_eq_ediv_of_nonneg _ b0, mul_ediv_cancel _ H]
  else
    match a, b, Int.not_le.1 b0 with
    | 0, _, _ => by simp [Int.zero_mul]
    | succ a, -[b+1], _ => congrArg ofNat <| Nat.mul_div_cancel (succ a) b.succ_pos
    | -[a+1], -[b+1], _ => congrArg negSucc <| Nat.div_eq_of_lt_le
      (Nat.le_of_lt_succ <| Nat.mul_lt_mul_of_pos_right a.lt_succ_self b.succ_pos)
      (Nat.lt_succ_self _)

@[simp] theorem mul_fdiv_cancel_left (b : Int) (H : a ≠ 0) : fdiv (a * b) a = b :=
  Int.mul_comm .. ▸ Int.mul_fdiv_cancel _ H

theorem add_fdiv_of_dvd_right {a b c : Int} (H : c ∣ b) : (a + b).fdiv c = a.fdiv c + b.fdiv c := by
  by_cases h : c = 0
  · simp [h]
  · obtain ⟨d, rfl⟩ := H
    rw [add_mul_fdiv_left _ _ h]
    simp [h]

theorem add_fdiv_of_dvd_left {a b c : Int} (H : c ∣ a) : (a + b).fdiv c = a.fdiv c + b.fdiv c := by
  rw [Int.add_comm, Int.add_fdiv_of_dvd_right H, Int.add_comm]

theorem fdiv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.fdiv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_fdiv .. ▸ ofNat_zero_le _

theorem fdiv_nonneg_of_nonpos_of_nonpos {a b : Int} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a.fdiv b := by
  rw [fdiv_eq_ediv]
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · simp [hb]
    · have : 0 < a / b := ediv_pos_of_neg_of_neg (by omega) (by omega)
      split <;> omega

theorem fdiv_nonpos_of_nonneg_of_nonpos : ∀ {a b : Int}, 0 ≤ a → b ≤ 0 → a.fdiv b ≤ 0
  | 0, 0, _, _ | 0, -[_+1], _, _ | succ _, 0, _, _ | succ _, -[_+1], _, _ => by
    simp [fdiv, negSucc_le_zero]

@[deprecated fdiv_nonpos_of_nonneg_of_nonpos (since := "2025-03-04")]
abbrev fdiv_nonpos := @fdiv_nonpos_of_nonneg_of_nonpos

theorem fdiv_neg_of_neg_of_pos : ∀ {a b : Int}, a < 0 → 0 < b → a.fdiv b < 0
  | -[_+1], succ _, _, _ => negSucc_lt_zero _

theorem fdiv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.fdiv b = 0 := by
  rw [fdiv_eq_ediv, if_pos, Int.sub_zero]
  · apply ediv_eq_zero_of_lt (by omega) (by omega)
  · left; omega

@[simp] theorem mul_fdiv_mul_of_pos {a : Int}
    (b c : Int) (H : 0 < a) : (a * b).fdiv (a * c) = b.fdiv c := by
  rw [fdiv_eq_ediv, mul_ediv_mul_of_pos _ _ H, fdiv_eq_ediv]
  congr 2
  simp [Int.mul_dvd_mul_iff_left (Int.ne_of_gt H)]
  constructor
  · rintro (h | h)
    · exact .inl (Int.nonneg_of_mul_nonneg_right h H)
    · exact .inr h
  · rintro (h | h)
    · exact .inl (Int.mul_nonneg (by omega) h)
    · exact .inr h

@[simp] theorem mul_fdiv_mul_of_pos_left
    (a : Int) {b : Int} (c : Int) (H : 0 < b) : (a * b).fdiv (c * b) = a.fdiv c := by
  rw [Int.mul_comm a b, Int.mul_comm c b, Int.mul_fdiv_mul_of_pos _ _ H]

@[simp] theorem fdiv_one : ∀ a : Int, a.fdiv 1 = a
  | 0 => rfl
  | succ _ => congrArg Nat.cast (Nat.div_one _)
  | -[_+1] => congrArg negSucc (Nat.div_one _)

protected theorem fdiv_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a.fdiv b = c := by rw [H2, Int.mul_fdiv_cancel_left _ H1]

protected theorem eq_fdiv_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c.tdiv a :=
  (Int.tdiv_eq_of_eq_mul_right H1 H2.symm).symm

protected theorem fdiv_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a.fdiv b = c :=
  Int.fdiv_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem eq_fdiv_of_mul_eq_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a * b = c) : a = c.fdiv b :=
  (Int.fdiv_eq_of_eq_mul_left H1 H2.symm).symm

@[simp] protected theorem fdiv_self {a : Int} (H : a ≠ 0) : a.fdiv a = 1 := by
  have := Int.mul_fdiv_cancel 1 H; rwa [Int.one_mul] at this

theorem neg_fdiv {a b : Int} : (-a).fdiv b = -(a.fdiv b) - if b = 0 ∨ b ∣ a then 0 else 1 := by
  rw [fdiv_eq_ediv, fdiv_eq_ediv, neg_ediv]
  simp
  by_cases h : b ∣ a
  · simp [h]
  · simp [h]
    by_cases h' : 0 ≤ b
    · by_cases h'' : b = 0
      · simp [h'']
      · simp only [h', ↓reduceIte, Int.sub_zero, h'']
        replace h' : 0 < b := by omega
        rw [sign_eq_one_of_pos (by omega)]
    · simp only [h', ↓reduceIte]
      rw [sign_eq_neg_one_of_neg (by omega), if_neg (by omega)]
      omega

@[simp] protected theorem neg_fdiv_neg (a b : Int) : (-a).fdiv (-b) = a.fdiv b := by
  match a, b with
  | 0, 0 => rfl
  | 0, ofNat b => simp
  | 0, -[b+1] => simp
  | ofNat (a + 1), 0 => simp
  | ofNat (a + 1), ofNat (b + 1) =>
    unfold fdiv
    simp only [ofNat_eq_coe, Int.natCast_add, cast_ofNat_Int, Nat.succ_eq_add_one]
    rw [← negSucc_eq, ← negSucc_eq]
  | ofNat (a + 1), -[b+1] =>
    unfold fdiv
    simp only [ofNat_eq_coe, Int.natCast_add, cast_ofNat_Int, Nat.succ_eq_add_one]
    rw [← negSucc_eq, neg_negSucc]
  | -[a+1], 0 => simp
  | -[a+1], ofNat (b + 1) =>
    unfold fdiv
    simp only [ofNat_eq_coe, Int.natCast_add, cast_ofNat_Int, Nat.succ_eq_add_one]
    rw [neg_negSucc, ← negSucc_eq]
  | -[a+1], -[b+1] =>
    unfold fdiv
    simp only [ofNat_eq_coe, natCast_ediv, Nat.succ_eq_add_one, Int.natCast_add, cast_ofNat_Int]
    rw [neg_negSucc, neg_negSucc]
    simp

theorem fdiv_neg {a b : Int} (h : b ≠ 0) : a.fdiv (-b) = if b ∣ a then -(a.fdiv b) else -(a.fdiv b) - 1 := by
  rw [← Int.neg_fdiv_neg, Int.neg_neg, neg_fdiv]
  simp only [h, false_or]
  split <;> omega

/-!
One could prove the following, but as the statements are quite awkward, so far it doesn't seem worthwhile.
```
theorem natAbs_fdiv {a b : Int} (h : b ≠ 0) :
    natAbs (a.fdiv b) = a.natAbs / b.natAbs + if a.sign = b.sign ∨ b ∣ a then 0 else 1 := ...

theorem sign_fdiv (a b : Int) :
    sign (a.fdiv b) = if a.sign = b.sign ∧ natAbs a < natAbs b then 0 else sign a * sign b := ...
```
-/

/-! ### fmod -/

-- `fmod` analogues of `emod` lemmas from `Bootstrap.lean`

theorem ofNat_fmod (m n : Nat) : ↑(m % n) = fmod m n := by
  cases m <;> simp [fmod, Nat.succ_eq_add_one]

theorem fmod_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a.fmod b :=
  fmod_eq_tmod_of_nonneg ha hb ▸ tmod_nonneg _ ha

theorem fmod_nonneg_of_pos (a : Int) {b : Int} (hb : 0 < b) : 0 ≤ a.fmod b :=
  fmod_eq_emod_of_nonneg _ (Int.le_of_lt hb) ▸ emod_nonneg _ (Int.ne_of_lt hb).symm

@[deprecated fmod_nonneg_of_pos (since := "2025-03-04")]
abbrev fmod_nonneg' := @fmod_nonneg_of_pos

theorem fmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a.fmod b < b :=
  fmod_eq_emod_of_nonneg _ (Int.le_of_lt H) ▸ emod_lt_of_pos a H

-- There is no `fmod_neg : ∀ {a b : Int}, a.fmod (-b) = -a.fmod b` as this is false.

@[simp] theorem add_mul_fmod_self_right (a b c : Int) : (a + b * c).fmod c = a.fmod c := by
  rw [fmod_eq_emod, add_mul_emod_self_right, fmod_eq_emod]
  simp

@[deprecated add_mul_fmod_self_right (since := "2025-04-11")]
theorem add_mul_fmod_self {a b c : Int} : (a + b * c).fmod c = a.fmod c :=
  add_mul_fmod_self_right ..

@[simp] theorem add_mul_fmod_self_left (a b c : Int) : (a + b * c).fmod b = a.fmod b := by
  rw [Int.mul_comm, Int.add_mul_fmod_self_right]

@[simp] theorem mul_add_fmod_self_right (a b c : Int) : (a * b + c).fmod b = c.fmod b := by
  rw [Int.add_comm, add_mul_fmod_self_right]

@[simp] theorem mul_add_fmod_self_left (a b c : Int) : (a * b + c).fmod a = c.fmod a := by
  rw [Int.add_comm, add_mul_fmod_self_left]

@[simp] theorem add_neg_mul_fmod_self_right (a b c : Int) : (a + -(b * c)).fmod c = a.fmod c := by
  rw [Int.neg_mul_eq_neg_mul, add_mul_fmod_self_right]

@[simp] theorem add_neg_mul_fmod_self_left (a b c : Int) : (a + -(b * c)).fmod b = a.fmod b := by
  rw [Int.neg_mul_eq_mul_neg, add_mul_fmod_self_left]

@[simp] theorem add_fmod_right (a b : Int) : (a + b).fmod b = a.fmod b := by
  have := add_mul_fmod_self_left a b 1; rwa [Int.mul_one] at this

@[simp] theorem add_fmod_left (a b : Int) : (a + b).fmod a = b.fmod a := by
  rw [Int.add_comm, add_fmod_right]

@[simp] theorem sub_mul_fmod_self_right (a b c : Int) : (a - b * c).fmod c = a.fmod c := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem sub_mul_fmod_self_left (a b c : Int) : (a - b * c).fmod b = a.fmod b := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem mul_sub_fmod_self_right (a b c : Int) : (a * b - c).fmod b = (-c).fmod b := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem mul_sub_fmod_self_left (a b c : Int) : (a * b - c).fmod a = (-c).fmod a := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem sub_fmod_right (a b : Int) : (a - b).fmod b = a.fmod b := by
  have := sub_mul_fmod_self_left a b 1; rwa [Int.mul_one] at this

@[simp] theorem sub_fmod_left (a b : Int) : (a - b).fmod a = (-b).fmod a := by
  simp [Int.sub_eq_add_neg]

@[simp] theorem fmod_add_fmod (m n k : Int) : (m.fmod n + k).fmod n = (m + k).fmod n := by
  by_cases h : n = 0
  · simp [h]
  rw [fmod_def, fmod_def]
  conv => rhs; rw [fmod_def]
  have : m - n * m.fdiv n + k = m + k + n * (- m.fdiv n) := by simp [Int.mul_neg]; omega
  rw [this, add_fdiv_of_dvd_right (Int.dvd_mul_right ..), Int.mul_add, mul_fdiv_cancel_left _ h]
  omega

@[simp] theorem add_fmod_fmod (m n k : Int) : (m + n.fmod k).fmod k = (m + n).fmod k := by
  rw [Int.add_comm, Int.fmod_add_fmod, Int.add_comm]

theorem add_fmod (a b n : Int) : (a + b).fmod n = (a.fmod n + b.fmod n).fmod n := by
  simp

theorem add_fmod_eq_add_fmod_right {m n k : Int} (i : Int)
    (H : m.fmod n = k.fmod n) : (m + i).fmod n = (k + i).fmod n := by
  rw [add_fmod]
  conv => rhs; rw [add_fmod]
  rw [H]

theorem fmod_add_cancel_right {m n k : Int} (i) : (m + i).fmod n = (k + i).fmod n ↔ m.fmod n = k.fmod n :=
  ⟨fun H => by
    have := add_fmod_eq_add_fmod_right (-i) H
    rwa [Int.add_neg_cancel_right, Int.add_neg_cancel_right] at this,
  add_fmod_eq_add_fmod_right _⟩

@[simp] theorem mul_fmod_left (a b : Int) : (a * b).fmod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.fmod_def, Int.mul_fdiv_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_fmod_right (a b : Int) : (a * b).fmod a = 0 := by
  rw [Int.mul_comm, mul_fmod_left]

theorem mul_fmod (a b n : Int) : (a * b).fmod n = (a.fmod n * b.fmod n).fmod n := by
  conv => lhs; rw [
    ← fmod_add_fdiv a n, ← fmod_add_fdiv' b n, Int.add_mul, Int.mul_add, Int.mul_add,
    Int.mul_assoc, Int.mul_assoc, ← Int.mul_add n _ _, add_mul_fmod_self_left,
    ← Int.mul_assoc, add_mul_fmod_self_right]

@[simp] theorem fmod_self {a : Int} : a.fmod a = 0 := by
  have := mul_fmod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem fmod_fmod_of_dvd (n : Int) {m k : Int}
    (h : m ∣ k) : (n.fmod k).fmod m = n.fmod m := by
  conv => rhs; rw [← fmod_add_fdiv n k]
  match k, h with
  | _, ⟨t, rfl⟩ => rw [Int.mul_assoc, add_mul_fmod_self_left]

theorem fmod_fmod (a b : Int) : (a.fmod b).fmod b = a.fmod b := by
  simp

theorem sub_fmod (a b n : Int) : (a - b).fmod n = (a.fmod n - b.fmod n).fmod n := by
  apply (fmod_add_cancel_right b).mp
  rw [Int.sub_add_cancel, ← Int.add_fmod_fmod, Int.sub_add_cancel, fmod_fmod]

theorem fmod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → b.fmod a = 0
  | _, _, ⟨_, rfl⟩ => mul_fmod_right ..

-- `fmod` analogues of `emod` lemmas from above

theorem fmod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.fmod b = a := by
  rw [fmod_eq_emod_of_nonneg _ (Int.le_trans H1 (Int.le_of_lt H2)), emod_eq_of_lt H1 H2]

@[simp] protected theorem neg_fmod_neg (a b : Int) : (-a).fmod (-b) = -a.fmod b := by
  rw [fmod_def, Int.neg_fdiv_neg, fmod_def, Int.neg_mul]
  omega

-- Are `sign_fmod`, `natAbs_fmod` useful?

/-! ### properties of `fdiv` and `fmod` -/

-- Analogues of properties of `ediv` and `emod` from `Bootstrap.lean`

theorem mul_fdiv_cancel_of_fmod_eq_zero {a b : Int} (H : a.fmod b = 0) : b * (a.fdiv b) = a := by
  have := fmod_add_fdiv a b; rwa [H, Int.zero_add] at this

theorem fdiv_mul_cancel_of_fmod_eq_zero {a b : Int} (H : a.fmod b = 0) : (a.fdiv b) * b= a := by
  rw [Int.mul_comm, mul_fdiv_cancel_of_fmod_eq_zero H]

theorem dvd_of_fmod_eq_zero {a b : Int} (H : b.fmod a = 0) : a ∣ b :=
  ⟨b.fdiv a, (mul_fdiv_cancel_of_fmod_eq_zero H).symm⟩

theorem dvd_iff_fmod_eq_zero {a b : Int} : a ∣ b ↔ b.fmod a = 0 :=
  ⟨fmod_eq_zero_of_dvd, dvd_of_fmod_eq_zero⟩

protected theorem fdiv_mul_cancel {a b : Int} (H : b ∣ a) : a.fdiv b * b = a :=
  fdiv_mul_cancel_of_fmod_eq_zero (fmod_eq_zero_of_dvd H)

protected theorem mul_fdiv_cancel' {a b : Int} (H : a ∣ b) : a * b.fdiv a = b := by
  rw [Int.mul_comm, Int.fdiv_mul_cancel H]

protected theorem eq_mul_of_fdiv_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a.fdiv b = c) : a = b * c := by rw [← H2, Int.mul_fdiv_cancel' H1]

@[simp] theorem neg_fmod_self (a : Int) : (-a).fmod a = 0 := by
  rw [← dvd_iff_fmod_eq_zero, Int.dvd_neg]
  exact Int.dvd_refl a

theorem lt_fdiv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.fdiv b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.fmod_def .. ▸ fmod_lt_of_pos _ H

protected theorem fdiv_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.fdiv b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_fdiv_eq_right H', Int.fdiv_eq_of_eq_mul_right H⟩

protected theorem fdiv_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.fdiv b = c ↔ a = c * b := by
  rw [Int.mul_comm]; exact Int.fdiv_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_fdiv_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a.fdiv b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_fdiv_eq_right H1 H2]

protected theorem eq_zero_of_fdiv_eq_zero {d n : Int} (h : d ∣ n) (H : n.fdiv d = 0) : n = 0 := by
  rw [← Int.mul_fdiv_cancel' h, H, Int.mul_zero]

@[simp] protected theorem fdiv_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a.fdiv d = b.fdiv d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (fdiv · d)⟩
  rw [← Int.mul_fdiv_cancel' hda, ← Int.mul_fdiv_cancel' hdb, h]

protected theorem mul_fdiv_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b).fdiv c = a * (b.fdiv c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_fdiv_cancel_left _ cz, Int.mul_fdiv_cancel_left _ cz]

protected theorem mul_fdiv_assoc' (b : Int) {a c : Int} (h : c ∣ a) :
    (a * b).fdiv c = a.fdiv c * b := by
  rw [Int.mul_comm, Int.mul_fdiv_assoc _ h, Int.mul_comm]

theorem neg_fdiv_of_dvd : ∀ {a b : Int}, b ∣ a → (-a).fdiv b = -(a.fdiv b)
  | _, b, ⟨c, rfl⟩ => by
    by_cases bz : b = 0
    · simp [bz]
    · rw [Int.neg_mul_eq_mul_neg, Int.mul_fdiv_cancel_left _ bz, Int.mul_fdiv_cancel_left _ bz]

theorem sub_fdiv_of_dvd (a : Int) {b c : Int}
    (hcb : c ∣ b) : (a - b).fdiv c = a.fdiv c - b.fdiv c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_fdiv_of_dvd_right (Int.dvd_neg.2 hcb)]
  congr; exact Int.neg_fdiv_of_dvd hcb

theorem fdiv_dvd_fdiv : ∀ {a b c : Int}, a ∣ b → b ∣ c → b.fdiv a ∣ c.fdiv a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ => by
    by_cases az : a = 0
    · simp [az]
    · rw [Int.mul_fdiv_cancel_left _ az, Int.mul_assoc, Int.mul_fdiv_cancel_left _ az]
      apply Int.dvd_mul_right

-- Analogues of properties about `ediv` and `emod` from above.

theorem mul_fdiv_cancel_of_dvd {a b : Int} (H : b ∣ a) : b * (a.fdiv b) = a :=
  mul_fdiv_cancel_of_fmod_eq_zero (fmod_eq_zero_of_dvd H)

theorem fdiv_mul_cancel_of_dvd {a b : Int} (H : b ∣ a) : a.fdiv b * b = a :=
  fdiv_mul_cancel_of_fmod_eq_zero (fmod_eq_zero_of_dvd H)

theorem fmod_two_eq (x : Int) : x.fmod 2 = 0 ∨ x.fmod 2 = 1 := by
  have h₁ : 0 ≤ x.fmod 2 := Int.fmod_nonneg_of_pos _ (by decide)
  have h₂ : x.fmod 2 < 2 := Int.fmod_lt_of_pos x (by decide)
  match x.fmod 2, h₁, h₂ with
  | 0, _, _ => simp
  | 1, _, _ => simp

theorem add_fmod_eq_add_fmod_left {m n k : Int} (i : Int)
    (H : m.fmod n = k.fmod n) : (i + m).fmod n = (i + k).fmod n := by
  rw [Int.add_comm, add_fmod_eq_add_fmod_right _ H, Int.add_comm]

theorem fmod_add_cancel_left {m n k i : Int} : (i + m).fmod n = (i + k).fmod n ↔ m.fmod n = k.fmod n := by
  rw [Int.add_comm, Int.add_comm i, fmod_add_cancel_right]

theorem fmod_sub_cancel_right {m n k : Int} (i) : (m - i).fmod n = (k - i).fmod n ↔ m.fmod n = k.fmod n :=
  fmod_add_cancel_right _

theorem fmod_eq_fmod_iff_fmod_sub_eq_zero {m n k : Int} : m.fmod n = k.fmod n ↔ (m - k).fmod n = 0 :=
  (fmod_sub_cancel_right k).symm.trans <| by simp [Int.sub_self]

theorem fmod_sub_cancel_left {m n k : Int} (i) : (i - m).fmod n = (i - k).fmod n ↔ m.fmod n = k.fmod n := by
  simp only [fmod_eq_fmod_iff_fmod_sub_eq_zero, ← dvd_iff_fmod_eq_zero,
    (by omega : i - m - (i - k) = -(m - k)), Int.dvd_neg]

protected theorem fdiv_fmod_unique {a b r q : Int} (h : 0 < b) :
    a.fdiv b = q ∧ a.fmod b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b := by
  rw [fdiv_eq_ediv_of_nonneg, fmod_eq_emod_of_nonneg, Int.ediv_emod_unique]
  all_goals omega

protected theorem fdiv_fmod_unique' {a b r q : Int} (h : b < 0) :
    a.fdiv b = q ∧ a.fmod b = r ↔ r + b * q = a ∧ b < r ∧ r ≤ 0 := by
  have := Int.fdiv_fmod_unique (a := -a) (b := -b) (r := -r) (q := q) (by omega)
  simp at this
  simp [this, Int.neg_mul]
  omega

@[simp] theorem mul_fmod_mul_of_pos
    {a : Int} (b c : Int) (H : 0 < a) : (a * b).fmod (a * c) = a * (b.fmod c) := by
  rw [fmod_def, fmod_def, mul_fdiv_mul_of_pos _ _ H, Int.mul_sub, Int.mul_assoc]

theorem natAbs_fdiv_le_natAbs (a b : Int) : natAbs (a.fdiv b) ≤ natAbs a := by
  rw [fdiv_eq_ediv]
  split
  · simp [natAbs_ediv_le_natAbs]
  · rename_i h
    simp at h
    match a, b, h with
    | 0, .negSucc b, h => simp at h
    | .ofNat (a + 1), .negSucc 0, h => simp at h
    | .ofNat (a + 1), .negSucc (b + 1), h =>
      rw [negSucc_eq, ofNat_eq_coe]
      norm_cast
      rw [Int.ediv_neg, Int.sub_eq_add_neg, ← Int.neg_add, natAbs_neg]
      norm_cast
      apply Nat.div_lt_self
      omega
      omega
    | .negSucc a, .negSucc b, h =>
      simp [negSucc_eq]
      norm_cast
      rw [Int.neg_ediv, if_neg (by simpa using h.2)]
      norm_cast
      rw [sign_eq_one_of_pos (by omega), Int.sub_eq_add_neg, ← Int.neg_add, natAbs_neg,
        Int.sub_add_cancel, natAbs_neg, natAbs_natCast]
      apply Nat.div_le_self

theorem fdiv_le_self {a : Int} (b : Int) (Ha : 0 ≤ a) : a.fdiv b ≤ a := by
  have := Int.le_trans le_natAbs (ofNat_le.2 <| natAbs_fdiv_le_natAbs a b)
  rwa [natAbs_of_nonneg Ha] at this

theorem dvd_fmod_sub_self {x m : Int} : m ∣ x.fmod m - x := by
  rw [fmod_eq_emod]
  have := dvd_emod_sub_self (x := x) (m := m)
  split
  · simpa
  · have w : x % ↑m + ↑m - x = x % ↑m - x + ↑m := by omega
    rw [w]
    apply Int.dvd_add this (Int.dvd_refl ↑m)

theorem dvd_self_sub_fmod {x m : Int} : m ∣ x - x.fmod m :=
  Int.dvd_neg.1 (by simpa only [Int.neg_sub] using dvd_fmod_sub_self)

theorem dvd_self_sub_of_fmod_eq {a b c : Int} (h : a.fmod b = c) :
    (b : Int) ∣ a - c :=
  h ▸ dvd_self_sub_fmod

theorem dvd_sub_self_of_fmod_eq {a b c : Int} (h : a.fmod b = c) :
    (b : Int) ∣ c - a :=
  h ▸ dvd_fmod_sub_self

@[simp] theorem neg_mul_fmod_right (a b : Int) : (-(a * b)).fmod a = 0 := by
  rw [← dvd_iff_fmod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_right a b

@[simp] theorem neg_mul_fmod_left (a b : Int) : (-(a * b)).fmod b = 0 := by
  rw [← dvd_iff_fmod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_left a b

@[simp] theorem fmod_one (a : Int) : a.fmod 1 = 0 := by
  simp [fmod_def, Int.one_mul, Int.sub_self]

@[deprecated sub_fmod_right (since := "2025-04-12")]
theorem fmod_sub_cancel (x y : Int) : (x - y).fmod y = x.fmod y :=
  sub_fmod_right _ _

@[simp] theorem add_neg_fmod_self (a b : Int) : (a + -b).fmod b = a.fmod b := by
  rw [Int.add_neg_eq_sub, sub_fmod_right]

@[simp] theorem neg_add_fmod_self (a b : Int) : (-a + b).fmod a = b.fmod a := by
  rw [Int.add_comm, add_neg_fmod_self]

@[deprecated dvd_self_sub_of_fmod_eq (since := "2025-04-12")]
theorem dvd_sub_of_fmod_eq {a b c : Int} (h : a.fmod b = c) : b ∣ a - c :=
  dvd_self_sub_of_fmod_eq h

theorem fdiv_sign {a b : Int} : a.fdiv (sign b) = a * sign b := by
  rw [fdiv_eq_ediv]
  rcases sign_trichotomy b with h | h | h <;> simp [h]

protected theorem sign_eq_fdiv_abs (a : Int) : sign a = a.fdiv (natAbs a) :=
  if az : a = 0 then by simp [az] else
    (Int.fdiv_eq_of_eq_mul_left (ofNat_ne_zero.2 <| natAbs_ne_zero.2 az)
      (sign_mul_natAbs _).symm).symm


/-! ### `fdiv` and ordering -/

-- Theorems about `fdiv` and ordering, whose `ediv` analogues are in `Bootstrap.lean`.

theorem mul_fdiv_self_le {x k : Int} (h : 0 < k) : k * (x.fdiv k) ≤ x := by
  rw [fdiv_eq_ediv]
  have := mul_ediv_self_le (x := x) (k := k)
  split <;> simp <;> omega

theorem lt_mul_fdiv_self_add {x k : Int} (h : 0 < k) : x < k * (x.fdiv k) + k := by
  rw [fdiv_eq_ediv]
  have := lt_mul_ediv_self_add (x := x) h
  split <;> simp <;> omega

-- We do not currently prove the theorems about `fdiv` and ordering,
-- whose `ediv` analogues are proved above.

/-! ### bmod -/

@[simp]
theorem emod_bmod (x : Int) (n : Nat) : Int.bmod (x%n) n = Int.bmod x n := by
  simp [bmod]

@[deprecated emod_bmod (since := "2025-04-11")]
theorem emod_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n) n = Int.bmod x n :=
  emod_bmod ..

theorem bdiv_add_bmod (x : Int) (m : Nat) : m * bdiv x m + bmod x m = x := by
  unfold bdiv bmod
  split
  · simp_all only [cast_ofNat_Int, Int.mul_zero, emod_zero, Int.zero_add, Int.sub_zero,
      ite_self]
  · dsimp only
    split
    · exact ediv_add_emod x m
    · rw [Int.mul_add, Int.mul_one, Int.add_assoc, Int.add_comm m, Int.sub_add_cancel]
      exact ediv_add_emod x m

theorem bmod_add_bdiv (x : Int) (m : Nat) : bmod x m + m * bdiv x m = x := by
  rw [Int.add_comm]; exact bdiv_add_bmod x m

theorem bdiv_add_bmod' (x : Int) (m : Nat) : bdiv x m * m + bmod x m = x := by
  rw [Int.mul_comm]; exact bdiv_add_bmod x m

theorem bmod_add_bdiv' (x : Int) (m : Nat) : bmod x m + bdiv x m * m = x := by
  rw [Int.add_comm]; exact bdiv_add_bmod' x m

theorem bmod_eq_self_sub_mul_bdiv (x : Int) (m : Nat) : bmod x m = x - m * bdiv x m := by
  rw [← Int.add_sub_cancel (bmod x m), bmod_add_bdiv]

theorem bmod_eq_self_sub_bdiv_mul (x : Int) (m : Nat) : bmod x m = x - bdiv x m * m := by
  rw [← Int.add_sub_cancel (bmod x m), bmod_add_bdiv']

theorem bmod_pos (x : Int) (m : Nat) (p : x % m < (m + 1) / 2) : bmod x m = x % m := by
  simp [bmod_def, p]

theorem bmod_neg (x : Int) (m : Nat) (p : x % m ≥ (m + 1) / 2) : bmod x m = (x % m) - m := by
  simp [bmod_def, Int.not_lt.mpr p]

theorem bmod_eq_emod (x : Int) (m : Nat) : bmod x m = x % m - if x % m ≥ (m + 1) / 2 then m else 0 := by
  split
  · rwa [bmod_neg]
  · rw [bmod_pos] <;> simp_all

@[simp]
theorem bmod_one (x : Int) : Int.bmod x 1 = 0 := by
  simp [Int.bmod]

@[deprecated bmod_one (since := "2025-04-10")]
abbrev bmod_one_is_zero := @bmod_one

@[simp] theorem add_bmod_right (a : Int) (b : Nat) : (a + b).bmod b = a.bmod b := by
  simp [bmod_def]

@[simp] theorem add_bmod_left (a : Nat) (b : Int) : (a + b).bmod a = b.bmod a := by
  simp [bmod_def]

@[simp] theorem add_mul_bmod_self_right (a b : Int) (c : Nat)  : (a + b * c).bmod c = a.bmod c := by
  simp [bmod_def]

@[simp] theorem add_mul_bmod_self_left (a : Int) (b : Nat) (c : Int) : (a + b * c).bmod b = a.bmod b := by
  simp [bmod_def]

@[simp] theorem mul_add_bmod_self_right (a : Int) (b : Nat) (c : Int) : (a * b + c).bmod b = c.bmod b := by
  simp [bmod_def]

@[simp] theorem mul_add_bmod_self_left (a : Nat) (b c : Int) : (a * b + c).bmod a = c.bmod a := by
  simp [bmod_def]

@[simp] theorem sub_bmod_right (a : Int) (b : Nat) : (a - b).bmod b = a.bmod b := by
  simp [bmod_def]

@[simp] theorem sub_bmod_left (a : Nat) (b : Int) : (a - b).bmod a = (-b).bmod a := by
  simp [bmod_def]

@[simp] theorem sub_mul_bmod_self_right (a b : Int) (c : Nat)  : (a - b * c).bmod c = a.bmod c := by
  simp [bmod_def]

@[simp] theorem sub_mul_bmod_self_left (a : Int) (b : Nat) (c : Int) : (a - b * c).bmod b = a.bmod b := by
  simp [bmod_def]

@[simp] theorem mul_sub_bmod_self_right (a : Int) (b : Nat) (c : Int) : (a * b - c).bmod b = (-c).bmod b := by
  simp [bmod_def]

@[simp] theorem mul_sub_bmod_self_left (a : Nat) (b c : Int) : (a * b - c).bmod a = (-c).bmod a := by
  simp [bmod_def]

@[simp] theorem add_neg_mul_bmod_self_right (a b : Int) (c : Nat) : (a + -(b * c)).bmod c = a.bmod c := by
  simp [bmod_def]

@[simp] theorem add_neg_mul_bmod_self_left (a : Int) (b : Nat) (c : Int) : (a + -(b * c)).bmod b = a.bmod b := by
  simp [bmod_def]

@[deprecated add_bmod_right (since := "2025-04-10")]
theorem bmod_add_cancel {x : Int} {n : Nat} : Int.bmod (x + n) n = Int.bmod x n :=
  add_bmod_right ..

@[deprecated add_mul_bmod_self_left (since := "2025-04-10")]
theorem bmod_add_mul_cancel (x : Int) (n : Nat) (k : Int) : Int.bmod (x + n * k) n = Int.bmod x n :=
  add_mul_bmod_self_left ..

@[deprecated sub_bmod_right (since := "2025-04-10")]
theorem bmod_sub_cancel (x : Int) (n : Nat) : Int.bmod (x - n) n = Int.bmod x n :=
  sub_bmod_right ..

@[deprecated sub_mul_bmod_self_left (since := "2025-04-10")]
theorem Int.bmod_sub_mul_cancel (x : Int) (n : Nat) (k : Int) : (x - n * k).bmod n = x.bmod n :=
  sub_mul_bmod_self_left ..

@[simp]
theorem emod_add_bmod (x : Int) (n : Nat) : Int.bmod (x % n + y) n = Int.bmod (x + y) n := by
  simp [Int.emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_right_comm,  Int.add_mul_bmod_self_left]

@[deprecated emod_add_bmod (since := "2025-04-11")]
theorem emod_add_bmod_congr (x : Int) (n : Nat) : Int.bmod (x % n + y) n = Int.bmod (x + y) n :=
  emod_add_bmod ..

@[simp]
theorem emod_sub_bmod (x : Int) (n : Nat) : Int.bmod (x % n - y) n = Int.bmod (x - y) n := by
  simp only [emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_right_comm,  Int.add_mul_bmod_self_left]

@[deprecated emod_sub_bmod (since := "2025-04-11")]
theorem emod_sub_bmod_congr (x : Int) (n : Nat) : Int.bmod (x % n - y) n = Int.bmod (x - y) n :=
  emod_sub_bmod ..

@[simp]
theorem sub_emod_bmod (x : Int) (n : Nat) : Int.bmod (x - y % n) n = Int.bmod (x - y) n := by
  simp only [emod_def]
  rw [Int.sub_eq_add_neg, Int.neg_sub, Int.sub_eq_add_neg, ← Int.add_assoc, Int.add_right_comm,
    Int.add_mul_bmod_self_left, Int.sub_eq_add_neg]

@[deprecated sub_emod_bmod (since := "2025-04-11")]
theorem sub_emod_bmod_congr (x : Int) (n : Nat) : Int.bmod (x - y % n) n = Int.bmod (x - y) n :=
  sub_emod_bmod ..

@[simp]
theorem emod_mul_bmod (x : Int) (n : Nat) : Int.bmod (x % n * y) n = Int.bmod (x * y) n := by
  simp [Int.emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_mul, Int.mul_assoc, Int.add_mul_bmod_self_left]

@[deprecated emod_mul_bmod (since := "2025-04-11")]
theorem emod_mul_bmod_congr (x : Int) (n : Nat) : Int.bmod (x % n * y) n = Int.bmod (x * y) n :=
  emod_mul_bmod ..

@[simp]
theorem bmod_add_bmod : Int.bmod (Int.bmod x n + y) n = Int.bmod (x + y) n := by
  have := (@add_mul_bmod_self_left (Int.bmod x n + y) n (bdiv x n)).symm
  rwa [Int.add_right_comm, bmod_add_bdiv] at this

@[deprecated bmod_add_bmod (since := "2025-04-11")]
theorem bmod_add_bmod_congr : Int.bmod (Int.bmod x n + y) n = Int.bmod (x + y) n :=
  bmod_add_bmod ..

@[simp]
theorem bmod_sub_bmod : Int.bmod (Int.bmod x n - y) n = Int.bmod (x - y) n :=
  @bmod_add_bmod x n (-y)

@[deprecated bmod_sub_bmod (since := "2025-04-11")]
theorem bmod_sub_bmod_congr : Int.bmod (Int.bmod x n - y) n = Int.bmod (x - y) n :=
  bmod_sub_bmod ..

theorem add_bmod_eq_add_bmod_right (i : Int)
    (H : bmod x n = bmod y n) : bmod (x + i) n = bmod (y + i) n := by
  rw [← bmod_add_bmod, ← @bmod_add_bmod y, H]

theorem bmod_add_cancel_right (i : Int) : bmod (x + i) n = bmod (y + i) n ↔ bmod x n = bmod y n :=
  ⟨fun H => by
    have := add_bmod_eq_add_bmod_right (-i) H
    rwa [Int.add_neg_cancel_right, Int.add_neg_cancel_right] at this,
  fun H => by rw [← bmod_add_bmod, H, bmod_add_bmod]⟩

theorem bmod_add_cancel_left (i : Int) : bmod (i + x) n = bmod (i + y) n ↔ bmod x n = bmod y n := by
  rw [Int.add_comm i, Int.add_comm i, bmod_add_cancel_right]

theorem add_bmod_eq_add_bmod_left (i : Int) (h : bmod x n = bmod y n) :
    bmod (i + x) n = bmod (i + y) n := by
  simpa [bmod_add_cancel_left]

@[simp] theorem add_bmod_bmod : Int.bmod (x + Int.bmod y n) n = Int.bmod (x + y) n := by
  rw [Int.add_comm x, Int.bmod_add_bmod, Int.add_comm y]

@[simp] theorem sub_bmod_bmod : Int.bmod (x - Int.bmod y n) n = Int.bmod (x - y) n := by
  apply (bmod_add_cancel_right (bmod y n)).mp
  rw [Int.sub_add_cancel, add_bmod_bmod, Int.sub_add_cancel]

@[simp]
theorem bmod_mul_bmod : Int.bmod (Int.bmod x n * y) n = Int.bmod (x * y) n := by
  rw [bmod_def x n]
  split
  next p =>
    simp
  next p =>
    rw [Int.sub_mul, Int.sub_eq_add_neg, ← Int.mul_neg, add_mul_bmod_self_left, emod_mul_bmod]

@[simp] theorem mul_bmod_bmod : Int.bmod (x * Int.bmod y n) n = Int.bmod (x * y) n := by
  rw [Int.mul_comm x, bmod_mul_bmod, Int.mul_comm x]

@[simp] theorem add_emod_bmod (x : Int) (n : Nat) : (y + x % n).bmod n = (y + x).bmod n := by
  rw [Int.add_comm, emod_add_bmod, Int.add_comm]

@[simp] theorem mul_emod_bmod (x : Int) (n : Nat) : (y * (x % n)).bmod n = (y * x).bmod n := by
  rw [Int.mul_comm, emod_mul_bmod, Int.mul_comm]

@[simp] theorem mul_bmod_left (a : Int) (b : Nat) : (a * b).bmod b = 0 := by
  simp [bmod_def]; omega

@[simp] theorem mul_bmod_right (a : Nat) (b : Int) : (a * b).bmod a = 0 := by
  simp [bmod_def]; omega

theorem mul_bmod (a b : Int) (n : Nat) : (a * b).bmod n = (a.bmod n * b.bmod n).bmod n := by
  simp

theorem add_bmod (a b : Int) (n : Nat) : (a + b).bmod n = (a.bmod n + b.bmod n).bmod n := by
  simp

theorem sub_bmod (a b : Int) (n : Nat) : (a - b).bmod n = (a.bmod n - b.bmod n).bmod n := by
  simp

@[simp] theorem bmod_bmod : bmod (bmod x m) m = bmod x m := by
  rw [bmod, bmod_emod, bmod]

@[simp] theorem zero_bmod : Int.bmod 0 m = 0 := by
  simp [bmod_def]; omega

@[simp] theorem bmod_zero : Int.bmod m 0 = m := by
  simp [bmod_def]

@[simp] theorem bmod_self {a : Nat} : Int.bmod a a = 0 := by
  simp [bmod_def]; omega

@[simp] theorem neg_bmod_self {a : Nat} : Int.bmod (-a) a = 0 := by
  simp [← Int.zero_sub]

theorem dvd_bmod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ bmod x m - x := by
  dsimp [bmod]
  split
  · exact dvd_emod_sub_self
  · rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub]
    exact Int.dvd_sub dvd_emod_sub_self (Int.dvd_refl _)

theorem dvd_self_sub_bmod {x : Int} {m : Nat} : (m : Int) ∣ x - bmod x m :=
  Int.dvd_neg.1 (by simpa only [Int.neg_sub] using dvd_bmod_sub_self)

theorem dvd_of_bmod_eq_zero {a : Nat} {b : Int} (h : b.bmod a = 0) : (a : Int) ∣ b := by
  simpa [h] using dvd_bmod_sub_self (x := b) (m := a)

theorem bmod_eq_zero_of_dvd : {a : Nat} → {b : Int} → (h : (a : Int) ∣ b) → b.bmod a = 0
  | _, _, ⟨_, rfl⟩ => by simp

theorem dvd_iff_bmod_eq_zero {a : Nat} {b : Int} : (a : Int) ∣ b ↔ b.bmod a = 0 :=
  ⟨bmod_eq_zero_of_dvd, dvd_of_bmod_eq_zero⟩

theorem divExact_eq_bdiv {a : Int} {b : Nat} (h : (b : Int) ∣ a) : a.divExact b h = a.bdiv b := by
  have := bdiv_add_bmod a b
  rw [bmod_eq_zero_of_dvd h, Int.add_zero] at this
  rw [divExact_eq_ediv]
  conv => lhs; rw [← this]
  by_cases h' : (b : Int) = 0
  · cases h'
    simp_all
  · rw [mul_ediv_cancel_left _ h']

theorem le_bmod {x : Int} {m : Nat} (h : 0 < m) : - (m/2) ≤ Int.bmod x m := by
  dsimp [bmod]
  have v : (m : Int) % 2 = 0 ∨ (m : Int) % 2 = 1 := emod_two_eq _
  split <;> rename_i w
  · refine Int.le_trans ?_ (Int.emod_nonneg _ ?_)
    · exact Int.neg_nonpos_of_nonneg (Int.ediv_nonneg (natCast_nonneg _) (by decide))
    · exact Int.ne_of_gt (natCast_pos.mpr h)
  · simp [Int.not_lt] at w
    refine Int.le_trans ?_ (Int.sub_le_sub_right w _)
    rw [← ediv_add_emod m 2]
    generalize (m : Int) / 2 = q
    generalize h : (m : Int) % 2 = r at *
    rcases v with rfl | rfl
    · rw [Int.add_zero, Int.mul_ediv_cancel_left, Int.add_ediv_of_dvd_left,
        Int.mul_ediv_cancel_left, show (1 / 2 : Int) = 0 by decide, Int.add_zero,
        Int.neg_eq_neg_one_mul]
      conv => rhs; congr; rw [← Int.one_mul q]
      rw [← Int.sub_mul, show (1 - 2 : Int) = -1 by decide]
      apply Int.le_refl
      all_goals try decide
      all_goals apply Int.dvd_mul_right
    · rw [Int.add_ediv_of_dvd_left, Int.mul_ediv_cancel_left,
        show (1 / 2 : Int) = 0 by decide, Int.add_assoc, Int.add_ediv_of_dvd_left,
        Int.mul_ediv_cancel_left, show ((1 + 1) / 2 : Int) = 1 by decide, ← Int.sub_sub,
        Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_right_comm, Int.add_assoc q,
        show (1 + -1 : Int) = 0 by decide, Int.add_zero, ← Int.neg_mul]
      rw [Int.neg_eq_neg_one_mul]
      conv => rhs; congr; rw [← Int.one_mul q]
      rw [← Int.add_mul, show (1 + -2 : Int) = -1 by decide]
      apply Int.le_refl
      all_goals try decide
      all_goals try apply Int.dvd_mul_right

theorem bmod_lt {x : Int} {m : Nat} (h : 0 < m) : bmod x m < (m + 1) / 2 := by
  dsimp [bmod]
  split
  · assumption
  · apply Int.lt_of_lt_of_le
    · change _ < 0
      have : x % m < m := emod_lt_of_pos x (natCast_pos.mpr h)
      exact Int.sub_neg_of_lt this
    · exact Int.le.intro_sub _ rfl

theorem bmod_eq_iff {a : Int} {b : Nat} {c : Int} (hb : 0 < b) :
    a.bmod b = c ↔ -(b / 2) ≤ c ∧ c < (b + 1) / 2 ∧ (b : Int) ∣ (c - a) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨le_bmod hb, bmod_lt hb, dvd_bmod_sub_self⟩
  · rintro ⟨h₁, h₂, h₃⟩
    rw [← Int.sub_eq_zero]
    have := dvd_bmod_sub_self (x := a) (m := b)
    have hdvd := Int.dvd_sub this h₃
    rw [(by omega : a.bmod b - a - (c - a) = a.bmod b - c)] at hdvd
    apply eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have := le_bmod (x := a) (m := b) hb
    have := bmod_lt (x := a) (m := b) hb
    omega

theorem bmod_eq_emod_of_lt {x : Int} {m : Nat} (hx : x % m < (m + 1) / 2) : bmod x m = x % m := by
  simp [bmod, hx]

theorem bmod_eq_neg {n : Nat} {m : Int} (hm : 0 ≤ m) (hn : n = 2 * m) : m.bmod n = -m := by
  by_cases h : m = 0
  · subst h; simp
  · rw [Int.bmod_def, hn, if_neg]
    · rw [Int.emod_eq_of_lt hm] <;> omega
    · simp only [Int.not_lt]
      rw [Int.emod_eq_of_lt hm] <;> omega

theorem bmod_le {x : Int} {m : Nat} (h : 0 < m) : bmod x m ≤ (m - 1) / 2 := by
  refine lt_add_one_iff.mp ?_
  calc
    bmod x m < (m + 1) / 2  := bmod_lt h
    _ = ((m + 1 - 2) + 2)/2 := by simp
    _ = (m - 1) / 2 + 1     := by
      rw [add_ediv_of_dvd_right]
      · simp +decide only [Int.ediv_self]
        congr 2
        rw [Int.add_sub_assoc, ← Int.sub_neg]
        congr
      · trivial

theorem bmod_natAbs_add_one (x : Int) (w : x ≠ -1) : x.bmod (x.natAbs + 1) = -x.sign := by
  rw [bmod_eq_iff (by omega)]
  obtain (hx|rfl|hx) := Int.lt_trichotomy x 0
  · rw [sign_eq_neg_one_iff_neg.2 hx]
    exact ⟨by omega, by omega, ⟨1, by omega⟩⟩
  · simp
  · rw [sign_eq_one_iff_pos.2 hx]
    exact ⟨by omega, by omega, ⟨-1, by omega⟩⟩

@[deprecated bmod_natAbs_add_one (since := "2025-04-04")]
abbrev bmod_natAbs_plus_one := @bmod_natAbs_add_one

theorem bmod_self_add_one {x : Nat} : (x : Int).bmod (x + 1) = if x = 0 then 0 else -1 := by
  have := bmod_natAbs_add_one x (by omega)
  simp only [natAbs_natCast] at this
  rw [this]
  split <;> simp_all <;> omega

theorem one_bmod_two : Int.bmod 1 2 = -1 := by simp

theorem one_bmod {b : Nat} (h : 3 ≤ b) : Int.bmod 1 b = 1 := by
  have hb : 1 % (b : Int) = 1 := by rw [one_emod]; omega
  rw [bmod_pos _ _ (by omega), hb]

theorem bmod_two_eq (x : Int) : x.bmod 2 = -1 ∨ x.bmod 2 = 0 := by
  have := le_bmod (x := x) (m := 2) (by omega)
  have := bmod_lt (x := x) (m := 2) (by omega)
  omega

theorem bmod_sub_cancel_right (i : Int) : bmod (x - i) n = bmod (y - i) n ↔ bmod x n = bmod y n := by
  simp only [Int.sub_eq_add_neg, bmod_add_cancel_right]

theorem bmod_eq_bmod_iff_bmod_sub_eq_zero {m : Int} {n : Nat} {k : Int} : m.bmod n = k.bmod n ↔ (m - k).bmod n = 0 :=
  (bmod_sub_cancel_right k).symm.trans <| by simp [Int.sub_self]

theorem bmod_sub_cancel_left (i : Int) : bmod (i - x) n = bmod (i - y) n ↔ bmod x n = bmod y n := by
  simp only [bmod_eq_bmod_iff_bmod_sub_eq_zero, ← dvd_iff_bmod_eq_zero,
    (by omega : i - x - (i - y) = -(x - y)), Int.dvd_neg]

theorem mod_bmod_mul_of_pos {a : Nat} (b : Int) (c : Nat) (h : 0 < a) (hce : 2 ∣ c) :
    (a * b).bmod (a * c) = a * (b.bmod c) := by
  refine (Nat.eq_zero_or_pos c).elim (by rintro rfl; simp) (fun hc => ?_)
  rw [bmod_eq_iff (Nat.mul_pos h hc)]
  refine ⟨?_, ?_, ?_⟩
  · refine Int.le_trans ?_ (Int.mul_le_mul_of_nonneg_left (le_bmod hc) (by omega : 0 ≤ (a : Int)))
    simp only [Int.natCast_mul, Int.mul_neg, Int.neg_le_neg_iff]
    rw [Int.le_ediv_iff_mul_le (by omega), Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  · refine Int.lt_of_lt_of_le (Int.mul_lt_mul_of_pos_left (bmod_lt hc) (by omega)) ?_
    rw [Int.natCast_mul, Int.le_ediv_iff_mul_le (by omega)]
    obtain ⟨t, rfl⟩ := hce
    simp only [Int.natCast_mul, cast_ofNat_Int]
    rw [mul_add_ediv_left _ _ (by omega), ediv_eq_zero_of_lt (by omega) (by omega),
      Int.add_zero, Int.mul_comm 2, Int.mul_assoc]
    exact le.intro 1 rfl
  · rw [Int.natCast_mul, ← Int.mul_sub, Int.mul_dvd_mul_iff_left (by omega)]
    exact dvd_bmod_sub_self

@[simp]
theorem bmod_neg_bmod : bmod (-(bmod x n)) n = bmod (-x) n := by
  apply (bmod_add_cancel_right x).mp
  rw [Int.add_left_neg, ← add_bmod_bmod, Int.add_left_neg]

theorem neg_bmod {a : Int} {b : Nat} :
    (-a).bmod b = if (b : Int) ∣ 2 * a then a.bmod b else -(a.bmod b) := by
  refine (Nat.eq_zero_or_pos b).elim (by rintro rfl; split <;> simp_all <;> omega) (fun hb => ?_)
  split <;> rename_i h
  · rw [bmod_eq_bmod_iff_bmod_sub_eq_zero, ← dvd_iff_bmod_eq_zero]
    simpa [(by omega : -a - a = -2 * a), Int.neg_mul] using h
  · refine (bmod_eq_iff hb).2 ⟨?_, ?_, ?_⟩
    · simp only [Int.neg_le_neg_iff]
      have := bmod_le (x := a) hb
      omega
    · apply Int.neg_lt_of_neg_lt
      rw [bmod_def]
      split <;> rename_i h'
      · exact Int.lt_of_lt_of_le (by omega) (Int.emod_nonneg _ (by omega))
      · simp only [Int.not_lt] at h'
        apply Int.lt_sub_left_of_add_lt
        obtain ⟨c, (rfl|rfl)⟩ : ∃ c, b = 2 * c ∨ b = 2 * c + 1 := ⟨b / 2, by omega⟩
        · simp only [Int.natCast_mul, cast_ofNat_Int]
          rw [Int.mul_add_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega)]
          simp only [Int.add_zero, ← Int.sub_eq_add_neg]
          rw [(by omega : ∀ (i : Int), 2 * i - i = i)]
          refine Decidable.by_contra  (fun hc => h ?_)
          simp only [gt_iff_lt, Nat.zero_lt_succ, Nat.mul_pos_iff_of_pos_left, Int.natCast_mul,
            cast_ofNat_Int, Int.not_lt] at *
          rw [Int.mul_dvd_mul_iff_left (by omega)]
          have := ediv_add_emod a (2 * c)
          rw [(by omega : a % (2 * c) = c)] at this
          rw [← this]
          apply Int.dvd_add _ (by simp)
          rw [Int.mul_comm 2, Int.mul_assoc]
          apply Int.dvd_mul_right
        · omega
    · simp only [Int.sub_neg, Int.add_comm, ← Int.sub_eq_add_neg]
      rw [dvd_iff_bmod_eq_zero]
      simp

-- There seems to be no good statement for `natAbs_bmod`.

@[simp] theorem neg_mul_bmod_left (a : Int) (b : Nat) : (-(a * b)).bmod b = 0 := by
  simp [← Int.neg_mul]

@[simp] theorem neg_mul_bmod_right (a : Nat) (b : Int) : (-(a * b)).bmod a = 0 := by
  simp [← Int.mul_neg]

@[simp] theorem add_neg_bmod_self (a : Int) (b : Nat) : (a + -b).bmod b = a.bmod b := by
  simp [← Int.sub_eq_add_neg]

@[simp] theorem neg_add_bmod_self (a : Nat) (b : Int) : (-a + b).bmod a = b.bmod a := by
  simp [Int.add_comm]

theorem dvd_self_sub_of_bmod_eq {a : Int} {b : Nat} {c : Int} (h : a.bmod b = c) :
    (b : Int) ∣ a - c :=
  h ▸ dvd_self_sub_bmod

theorem dvd_sub_self_of_bmod_eq {a : Int} {b : Nat} {c : Int} (h : a.bmod b = c) :
    (b : Int) ∣ c - a :=
  h ▸ dvd_bmod_sub_self

theorem bmod_neg_iff {m : Nat} {x : Int} (h2 : -m ≤ x) (h1 : x < m) :
    (x.bmod m) < 0 ↔ (-(m / 2) ≤ x ∧ x < 0) ∨ ((m + 1) / 2 ≤ x) := by
  simp only [Int.bmod_def]
  by_cases xpos : 0 ≤ x
  · rw [Int.emod_eq_of_lt xpos (by omega)]; omega
  · rw [(Int.add_emod_right ..).symm, Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem bmod_eq_of_le {n : Int} {m : Nat} (hn' : -(m / 2) ≤ n) (hn : n < (m + 1) / 2) :
    n.bmod m = n :=
  (Nat.eq_zero_or_pos m).elim (by rintro rfl; simp) (fun hm => by simp_all [bmod_eq_iff])

@[deprecated bmod_eq_of_le (since := "2025-04-11")]
theorem bmod_eq_self_of_le {n : Int} {m : Nat} (hn' : -(m / 2) ≤ n) (hn : n < (m + 1) / 2) :
    n.bmod m = n :=
  bmod_eq_of_le hn' hn

theorem bmod_bmod_of_dvd {a : Int} {n m : Nat} (hnm : n ∣ m) :
    (a.bmod m).bmod n = a.bmod n := by
  rw [← Int.sub_eq_iff_eq_add.2 (bmod_add_bdiv a m).symm]
  obtain ⟨k, rfl⟩ := hnm
  simp [Int.mul_assoc]

theorem bmod_eq_of_le_mul_two {x : Int} {y : Nat} (hle : -y ≤ x * 2) (hlt : x * 2 < y) :
    x.bmod y = x := by
  apply bmod_eq_of_le (by omega) (by omega)

@[deprecated bmod_eq_of_le_mul_two (since := "2025-04-11")]
theorem bmod_eq_self_of_le_mul_two {x : Int} {y : Nat} (hle : -y ≤ x * 2) (hlt : x * 2 < y) :
    x.bmod y = x :=
  bmod_eq_of_le_mul_two hle hlt

/- ### ediv -/

theorem ediv_lt_self_of_pos_of_ne_one {x y : Int} (hx : 0 < x) (hy : y ≠ 1) :
    x / y < x := by
  by_cases hy' : 1 < y
  · obtain ⟨xn, rfl⟩ := Int.eq_ofNat_of_zero_le (a := x) (by omega)
    obtain ⟨yn, rfl⟩ := Int.eq_ofNat_of_zero_le (a := y) (by omega)
    rw [← Int.natCast_ediv]
    norm_cast
    apply Nat.div_lt_self (by omega) (by omega)
  · have := @Int.ediv_nonpos_of_nonneg_of_nonpos x y (by omega) (by omega)
    omega

theorem ediv_nonneg_of_nonneg_of_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x / y := by
  obtain ⟨xn, rfl⟩ := Int.eq_ofNat_of_zero_le (a := x) (by omega)
  obtain ⟨yn, rfl⟩ := Int.eq_ofNat_of_zero_le (a := y) (by omega)
  rw [← Int.natCast_ediv]
  exact Int.ofNat_zero_le (xn / yn)

/--  When both x and y are negative we need stricter bounds on x and y
  to establish the upper bound of x/y, i.e., x / y < x.natAbs.
  In particular, consider the following counter examples:
  · (-1) / (-2) = 1 and ¬ 1 < (-1).natAbs
    (note that Int.neg_one_ediv already handles `ediv` where the numerator is -1)
  · (-2) / (-1) = 2 and ¬ 1 < (-2).natAbs
  To exclude these cases, we enforce stricter bounds on the values of x and y.
-/
theorem ediv_lt_natAbs_self_of_lt_neg_one_of_lt_neg_one {x y : Int} (hx : x < -1) (hy : y < -1) :
    x / y < x.natAbs := by
  obtain ⟨xn, rfl⟩ := Int.eq_negSucc_of_lt_zero (a := x) (by omega)
  obtain ⟨yn, rfl⟩ := Int.eq_negSucc_of_lt_zero (a := y) (by omega)
  simp only [negSucc_ediv_negSucc, Int.natCast_add, natCast_ediv, cast_ofNat_Int, natAbs_negSucc,
    Nat.succ_eq_add_one, Int.add_lt_add_iff_right]
  rw_mod_cast [Nat.div_lt_iff_lt_mul (x := xn) (k := yn + 1) (y := xn) (by omega),
    show (xn < xn * (yn + 1)) = (1 * xn < (yn + 1) * xn) by rw [Nat.one_mul, Nat.mul_comm]]
  apply Nat.mul_lt_mul_of_lt_of_le (a := 1) (b := xn) (c := yn + 1) (d := xn) (by omega) (by omega) (by omega)

theorem self_le_ediv_of_nonpos_of_nonneg {x y : Int} (hx : x ≤ 0) (hy : 0 ≤ y) :
    x ≤ x / y := by
  by_cases hx' : x = 0
  · simp [hx', zero_ediv]
  · by_cases hy : y = 0
    · simp [hy]; omega
    · simp only [Int.le_ediv_iff_mul_le (c := y) (a := x) (b := x) (by omega),
        show (x * y ≤ x) = (x * y ≤ x * 1) by rw [Int.mul_one], Int.mul_one]
      apply Int.mul_le_mul_of_nonpos_left (a := x) (b := y) (c  := (1 : Int)) (by omega) (by omega)

theorem neg_self_le_ediv_of_nonneg_of_nonpos (x y : Int) (hx : 0 ≤ x) (hy : y ≤ 0) :
    -x ≤ x / y := by
  by_cases hy' : y = 0
  · simp [hy']; omega
  · obtain ⟨xn, rfl⟩ := Int.eq_ofNat_of_zero_le (a := x) (by omega)
    obtain ⟨yn, rfl⟩ := Int.eq_negSucc_of_lt_zero (a := y) (by omega)
    rw [show xn = ofNat xn by norm_cast, Int.ofNat_ediv_negSucc (a := xn)]
    simp only [ofNat_eq_coe, natCast_ediv, Int.natCast_add, cast_ofNat_Int, Int.neg_le_neg_iff]
    norm_cast
    apply Nat.le_trans (m := xn) (by exact Nat.div_le_self xn (yn + 1)) (by omega)

/-! Helper theorems for `dvd` simproc -/

protected theorem dvd_eq_true_of_mod_eq_zero {a b : Int} (h : b % a == 0) : (a ∣ b) = True := by
  simp [Int.dvd_of_emod_eq_zero, eq_of_beq h]

protected theorem dvd_eq_false_of_mod_ne_zero {a b : Int} (h : b % a != 0) : (a ∣ b) = False := by
  simp [eq_of_beq] at h
  simp [Int.dvd_iff_emod_eq_zero, h]

end Int
