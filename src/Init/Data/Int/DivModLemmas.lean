/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/

prelude
import Init.Data.Int.DivMod
import Init.Data.Int.Order
import Init.Data.Nat.Dvd
import Init.RCases

/-!
# Lemmas about integer division needed to bootstrap `omega`.
-/

open Nat (succ)

namespace Int

/-! ### dvd  -/

protected theorem dvd_def (a b : Int) : (a ∣ b) = Exists (fun c => b = a * c) := rfl

@[simp] protected theorem dvd_zero (n : Int) : n ∣ 0 := ⟨0, (Int.mul_zero _).symm⟩

@[simp] protected theorem dvd_refl (n : Int) : n ∣ n := ⟨1, (Int.mul_one _).symm⟩

@[simp] protected theorem one_dvd (n : Int) : 1 ∣ n := ⟨n, (Int.one_mul n).symm⟩

protected theorem dvd_trans : ∀ {a b c : Int}, a ∣ b → b ∣ c → a ∣ c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => Exists.intro (d * e) (by rw [Int.mul_assoc])

@[norm_cast] theorem ofNat_dvd {m n : Nat} : (↑m : Int) ∣ ↑n ↔ m ∣ n := by
  refine ⟨fun ⟨a, ae⟩ => ?_, fun ⟨k, e⟩ => ⟨k, by rw [e, Int.ofNat_mul]⟩⟩
  match Int.le_total a 0 with
  | .inl h =>
    have := ae.symm ▸ Int.mul_nonpos_of_nonneg_of_nonpos (ofNat_zero_le _) h
    rw [Nat.le_antisymm (ofNat_le.1 this) (Nat.zero_le _)]
    apply Nat.dvd_zero
  | .inr h => match a, eq_ofNat_of_zero_le h with
    | _, ⟨k, rfl⟩ => exact ⟨k, Int.ofNat.inj ae⟩

theorem dvd_antisymm {a b : Int} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b := by
  rw [← natAbs_of_nonneg H1, ← natAbs_of_nonneg H2]
  rw [ofNat_dvd, ofNat_dvd, ofNat_inj]
  apply Nat.dvd_antisymm

@[simp] protected theorem zero_dvd {n : Int} : 0 ∣ n ↔ n = 0 :=
  Iff.intro (fun ⟨k, e⟩ => by rw [e, Int.zero_mul])
            (fun h => h.symm ▸ Int.dvd_refl _)

protected theorem dvd_mul_right (a b : Int) : a ∣ a * b := ⟨_, rfl⟩

protected theorem dvd_mul_left (a b : Int) : b ∣ a * b := ⟨_, Int.mul_comm ..⟩

@[simp] protected theorem neg_dvd {a b : Int} : -a ∣ b ↔ a ∣ b := by
  constructor <;> exact fun ⟨k, e⟩ =>
    ⟨-k, by simp [e, Int.neg_mul, Int.mul_neg, Int.neg_neg]⟩

protected theorem dvd_neg {a b : Int} : a ∣ -b ↔ a ∣ b := by
  constructor <;> exact fun ⟨k, e⟩ =>
    ⟨-k, by simp [← e, Int.neg_mul, Int.mul_neg, Int.neg_neg]⟩

@[simp] theorem natAbs_dvd_natAbs {a b : Int} : natAbs a ∣ natAbs b ↔ a ∣ b := by
  refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ⟨natAbs k, hk.symm ▸ natAbs_mul a k⟩⟩
  rw [← natAbs_ofNat k, ← natAbs_mul, natAbs_eq_natAbs_iff] at hk
  cases hk <;> subst b
  · apply Int.dvd_mul_right
  · rw [← Int.mul_neg]; apply Int.dvd_mul_right

theorem ofNat_dvd_left {n : Nat} {z : Int} : (↑n : Int) ∣ z ↔ n ∣ z.natAbs := by
  rw [← natAbs_dvd_natAbs, natAbs_ofNat]

protected theorem dvd_add : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b + c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d + e, by rw [Int.mul_add]⟩

protected theorem dvd_sub : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b - c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d - e, by rw [Int.mul_sub]⟩

protected theorem dvd_add_left {a b c : Int} (H : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun h => by have := Int.dvd_sub h H; rwa [Int.add_sub_cancel] at this, (Int.dvd_add · H)⟩

protected theorem dvd_add_right {a b c : Int} (H : a ∣ b) : a ∣ b + c ↔ a ∣ c := by
  rw [Int.add_comm, Int.dvd_add_left H]

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

theorem ofNat_dvd_right {n : Nat} {z : Int} : z ∣ (↑n : Int) ↔ z.natAbs ∣ n := by
  rw [← natAbs_dvd_natAbs, natAbs_ofNat]

theorem eq_one_of_dvd_one {a : Int} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
  match a, eq_ofNat_of_zero_le H, H' with
  | _, ⟨_, rfl⟩, H' => congrArg ofNat <| Nat.eq_one_of_dvd_one <| ofNat_dvd.1 H'

theorem eq_one_of_mul_eq_one_right {a b : Int} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : Int} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right (b := a) H <| by rw [Int.mul_comm, H']

/-! ### *div zero  -/

@[simp] theorem zero_ediv : ∀ b : Int, 0 / b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

@[simp] protected theorem ediv_zero : ∀ a : Int, a / 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => rfl

@[simp] protected theorem zero_tdiv : ∀ b : Int, tdiv 0 b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

unseal Nat.div in
@[simp] protected theorem tdiv_zero : ∀ a : Int, tdiv a 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => rfl

@[simp] theorem zero_fdiv (b : Int) : fdiv 0 b = 0 := by cases b <;> rfl

unseal Nat.div in
@[simp] protected theorem fdiv_zero : ∀ a : Int, fdiv a 0 = 0
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

/-! ### div equivalences  -/

theorem tdiv_eq_ediv : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → a.tdiv b = a / b
  | 0, _, _, _ | _, 0, _, _ => by simp
  | succ _, succ _, _, _ => rfl


theorem fdiv_eq_ediv : ∀ (a : Int) {b : Int}, 0 ≤ b → fdiv a b = a / b
  | 0, _, _ | -[_+1], 0, _ => by simp
  | succ _, ofNat _, _ | -[_+1], succ _, _ => rfl

theorem fdiv_eq_tdiv {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fdiv a b = tdiv a b :=
  tdiv_eq_ediv Ha Hb ▸ fdiv_eq_ediv _ Hb

/-! ### mod zero -/

@[simp] theorem zero_emod (b : Int) : 0 % b = 0 := rfl

@[simp] theorem emod_zero : ∀ a : Int, a % 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

@[simp] theorem zero_tmod (b : Int) : tmod 0 b = 0 := by cases b <;> simp [tmod]

@[simp] theorem tmod_zero : ∀ a : Int, tmod a 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1] => congrArg (fun n => -ofNat n) <| Nat.mod_zero _

@[simp] theorem zero_fmod (b : Int) : fmod 0 b = 0 := by cases b <;> rfl

@[simp] theorem fmod_zero : ∀ a : Int, fmod a 0 = a
  | 0 => rfl
  | succ _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

/-! ### ofNat mod -/

@[simp, norm_cast] theorem ofNat_emod (m n : Nat) : (↑(m % n) : Int) = m % n := rfl


/-! ### mod definitions -/

theorem emod_add_ediv : ∀ a b : Int, a % b + b * (a / b) = a
  | ofNat _, ofNat _ => congrArg ofNat <| Nat.mod_add_div ..
  | ofNat m, -[n+1] => by
    show (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg]; exact congrArg ofNat <| Nat.mod_add_div ..
  | -[_+1], 0 => by rw [emod_zero]; rfl
  | -[m+1], succ n => aux m n.succ
  | -[m+1], -[n+1] => aux m n.succ
where
  aux (m n : Nat) : n - (m % n + 1) - (n * (m / n) + n) = -[m+1] := by
    rw [← ofNat_emod, ← ofNat_ediv, ← Int.sub_sub, negSucc_eq, Int.sub_sub n,
      ← Int.neg_neg (_-_), Int.neg_sub, Int.sub_sub_self, Int.add_right_comm]
    exact congrArg (fun x => -(ofNat x + 1)) (Nat.mod_add_div ..)

theorem emod_add_ediv' (a b : Int) : a % b + a / b * b = a := by
  rw [Int.mul_comm]; exact emod_add_ediv ..

theorem ediv_add_emod (a b : Int) : b * (a / b) + a % b = a := by
  rw [Int.add_comm]; exact emod_add_ediv ..

theorem ediv_add_emod' (a b : Int) : a / b * b + a % b = a := by
  rw [Int.mul_comm]; exact ediv_add_emod ..

theorem emod_def (a b : Int) : a % b = a - b * (a / b) := by
  rw [← Int.add_sub_cancel (a % b), emod_add_ediv]

theorem tmod_add_tdiv : ∀ a b : Int, tmod a b + b * (a.tdiv b) = a
  | ofNat _, ofNat _ => congrArg ofNat (Nat.mod_add_div ..)
  | ofNat m, -[n+1] => by
    show (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg]; exact congrArg ofNat (Nat.mod_add_div ..)
  | -[m+1], 0 => by
    show -(↑((succ m) % 0) : Int) + 0 * -↑(succ m / 0) = -↑(succ m)
    rw [Nat.mod_zero, Int.zero_mul, Int.add_zero]
  | -[m+1], ofNat n => by
    show -(↑((succ m) % n) : Int) + ↑n * -↑(succ m / n) = -↑(succ m)
    rw [Int.mul_neg, ← Int.neg_add]
    exact congrArg (-ofNat ·) (Nat.mod_add_div ..)
  | -[m+1], -[n+1] => by
    show -(↑(succ m % succ n) : Int) + -↑(succ n) * ↑(succ m / succ n) = -↑(succ m)
    rw [Int.neg_mul, ← Int.neg_add]
    exact congrArg (-ofNat ·) (Nat.mod_add_div ..)

theorem tdiv_add_tmod (a b : Int) : b * a.tdiv b + tmod a b = a := by
  rw [Int.add_comm]; apply tmod_add_tdiv ..

theorem tmod_add_tdiv' (m k : Int) : tmod m k + m.tdiv k * k = m := by
  rw [Int.mul_comm]; apply tmod_add_tdiv

theorem tdiv_add_tmod' (m k : Int) : m.tdiv k * k + tmod m k = m := by
  rw [Int.mul_comm]; apply tdiv_add_tmod

theorem tmod_def (a b : Int) : tmod a b = a - b * a.tdiv b := by
  rw [← Int.add_sub_cancel (tmod a b), tmod_add_tdiv]

theorem fmod_add_fdiv : ∀ a b : Int, a.fmod b + b * a.fdiv b = a
  | 0, ofNat _ | 0, -[_+1] => congrArg ofNat <| by simp
  | succ _, ofNat _ => congrArg ofNat <| Nat.mod_add_div ..
  | succ m, -[n+1] => by
    show subNatNat (m % succ n) n + (↑(succ n * (m / succ n)) + n + 1) = (m + 1)
    rw [Int.add_comm _ n, ← Int.add_assoc, ← Int.add_assoc,
      Int.subNatNat_eq_coe, Int.sub_add_cancel]
    exact congrArg (ofNat · + 1) <| Nat.mod_add_div ..
  | -[_+1], 0 => by rw [fmod_zero]; rfl
  | -[m+1], succ n => by
    show subNatNat .. - (↑(succ n * (m / succ n)) + ↑(succ n)) = -↑(succ m)
    rw [Int.subNatNat_eq_coe, ← Int.sub_sub, ← Int.neg_sub, Int.sub_sub, Int.sub_sub_self]
    exact congrArg (-ofNat ·) <| Nat.succ_add .. ▸ Nat.mod_add_div .. ▸ rfl
  | -[m+1], -[n+1] => by
    show -(↑(succ m % succ n) : Int) + -↑(succ n * (succ m / succ n)) = -↑(succ m)
    rw [← Int.neg_add]; exact congrArg (-ofNat ·) <| Nat.mod_add_div ..

theorem fdiv_add_fmod (a b : Int) : b * a.fdiv b + a.fmod b = a := by
  rw [Int.add_comm]; exact fmod_add_fdiv ..

theorem fmod_def (a b : Int) : a.fmod b = a - b * a.fdiv b := by
  rw [← Int.add_sub_cancel (a.fmod b), fmod_add_fdiv]

/-! ### mod equivalences  -/

theorem fmod_eq_emod (a : Int) {b : Int} (hb : 0 ≤ b) : fmod a b = a % b := by
  simp [fmod_def, emod_def, fdiv_eq_ediv _ hb]

theorem tmod_eq_emod {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : tmod a b = a % b := by
  simp [emod_def, tmod_def, tdiv_eq_ediv ha hb]

theorem fmod_eq_tmod {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : fmod a b = tmod a b :=
  tmod_eq_emod Ha Hb ▸ fmod_eq_emod _ Hb

/-! ### `/` ediv -/

@[simp] protected theorem ediv_neg : ∀ a b : Int, a / (-b) = -(a / b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero]; rfl
  | ofNat _, -[_+1] => (Int.neg_neg _).symm
  | ofNat _, succ _ | -[_+1], 0 | -[_+1], succ _ | -[_+1], -[_+1] => rfl

theorem ediv_neg' {a b : Int} (Ha : a < 0) (Hb : 0 < b) : a / b < 0 :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => negSucc_lt_zero _

protected theorem div_def (a b : Int) : a / b = Int.ediv a b := rfl

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

theorem ediv_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a / b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.ediv_neg .. ▸ Int.ediv_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

theorem add_mul_ediv_right (a b : Int) {c : Int} (H : c ≠ 0) : (a + b * c) / c = a / c + b :=
  suffices ∀ {{a b c : Int}}, 0 < c → (a + b * c).ediv c = a.ediv c + b from
    match Int.lt_trichotomy c 0 with
    | Or.inl hlt => by
      rw [← Int.neg_inj, ← Int.ediv_neg, Int.neg_add, ← Int.ediv_neg, ← Int.neg_mul_neg]
      exact this (Int.neg_pos_of_neg hlt)
    | Or.inr (Or.inl HEq) => absurd HEq H
    | Or.inr (Or.inr hgt) => this hgt
  suffices ∀ {k n : Nat} {a : Int}, (a + n * k.succ).ediv k.succ = a.ediv k.succ + n from
    fun a b c H => match c, eq_succ_of_zero_lt H, b with
      | _, ⟨_, rfl⟩, ofNat _ => this
      | _, ⟨k, rfl⟩, -[n+1] => show (a - n.succ * k.succ).ediv k.succ = a.ediv k.succ - n.succ by
        rw [← Int.add_sub_cancel (ediv ..), ← this, Int.sub_add_cancel]
  fun {k n} => @fun
  | ofNat _ => congrArg ofNat <| Nat.add_mul_div_right _ _ k.succ_pos
  | -[m+1] => by
    show ((n * k.succ : Nat) - m.succ : Int).ediv k.succ = n - (m / k.succ + 1 : Nat)
    by_cases h : m < n * k.succ
    · rw [← Int.ofNat_sub h, ← Int.ofNat_sub ((Nat.div_lt_iff_lt_mul k.succ_pos).2 h)]
      apply congrArg ofNat
      rw [Nat.mul_comm, Nat.mul_sub_div]; rwa [Nat.mul_comm]
    · have h := Nat.not_lt.1 h
      have H {a b : Nat} (h : a ≤ b) : (a : Int) + -((b : Int) + 1) = -[b - a +1] := by
        rw [negSucc_eq, Int.ofNat_sub h]
        simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_left_comm, Int.add_assoc]
      show ediv (↑(n * succ k) + -((m : Int) + 1)) (succ k) = n + -(↑(m / succ k) + 1 : Int)
      rw [H h, H ((Nat.le_div_iff_mul_le k.succ_pos).2 h)]
      apply congrArg negSucc
      rw [Nat.mul_comm, Nat.sub_mul_div]; rwa [Nat.mul_comm]

theorem add_ediv_of_dvd_right {a b c : Int} (H : c ∣ b) : (a + b) / c = a / c + b / c :=
  if h : c = 0 then by simp [h] else by
    let ⟨k, hk⟩ := H
    rw [hk, Int.mul_comm c k, Int.add_mul_ediv_right _ _ h,
      ← Int.zero_add (k * c), Int.add_mul_ediv_right _ _ h, Int.zero_ediv, Int.zero_add]

theorem add_ediv_of_dvd_left {a b c : Int} (H : c ∣ a) : (a + b) / c = a / c + b / c := by
  rw [Int.add_comm, Int.add_ediv_of_dvd_right H, Int.add_comm]

@[simp] theorem mul_ediv_cancel (a : Int) {b : Int} (H : b ≠ 0) : (a * b) / b = a := by
  have := Int.add_mul_ediv_right 0 a H
  rwa [Int.zero_add, Int.zero_ediv, Int.zero_add] at this

@[simp] theorem mul_ediv_cancel_left (b : Int) (H : a ≠ 0) : (a * b) / a = b :=
  Int.mul_comm .. ▸ Int.mul_ediv_cancel _ H


theorem div_nonneg_iff_of_pos {a b : Int} (h : 0 < b) : a / b ≥ 0 ↔ a ≥ 0 := by
  rw [Int.div_def]
  match b, h with
  | Int.ofNat (b+1), _ =>
    rcases a with ⟨a⟩ <;> simp [Int.ediv]
    exact decide_eq_decide.mp rfl

theorem ediv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg Nat.cast <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

theorem add_mul_ediv_left (a : Int) {b : Int}
    (c : Int) (H : b ≠ 0) : (a + b * c) / b = a / b + c :=
  Int.mul_comm .. ▸ Int.add_mul_ediv_right _ _ H

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
      · show m.succ * n.succ ≤ _
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

/-! ### emod -/

theorem mod_def' (m n : Int) : m % n = emod m n := rfl

theorem negSucc_emod (m : Nat) {b : Int} (bpos : 0 < b) : -[m+1] % b = b - 1 - m % b := by
  rw [Int.sub_sub, Int.add_comm]
  match b, eq_succ_of_zero_lt bpos with
  | _, ⟨n, rfl⟩ => rfl

theorem emod_negSucc (m : Nat) (n : Int) :
  (Int.negSucc m) % n = Int.subNatNat (Int.natAbs n) (Nat.succ (m % Int.natAbs n)) := rfl

theorem ofNat_mod_ofNat (m n : Nat) : (m % n : Int) = ↑(m % n) := rfl

theorem emod_nonneg : ∀ (a : Int) {b : Int}, b ≠ 0 → 0 ≤ a % b
  | ofNat _, _, _ => ofNat_zero_le _
  | -[_+1], _, H => Int.sub_nonneg_of_le <| ofNat_le.2 <| Nat.mod_lt _ (natAbs_pos.2 H)

theorem emod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a % b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨_, rfl⟩ => ofNat_lt.2 (Nat.mod_lt _ (Nat.succ_pos _))
  | -[_+1], _, ⟨_, rfl⟩ => Int.sub_lt_self _ (ofNat_lt.2 <| Nat.succ_pos _)

theorem mul_ediv_self_le {x k : Int} (h : k ≠ 0) : k * (x / k) ≤ x :=
  calc k * (x / k)
    _ ≤ k * (x / k) + x % k := Int.le_add_of_nonneg_right (emod_nonneg x h)
    _ = x                   := ediv_add_emod _ _

theorem lt_mul_ediv_self_add {x k : Int} (h : 0 < k) : x < k * (x / k) + k :=
  calc x
    _ = k * (x / k) + x % k := (ediv_add_emod _ _).symm
    _ < k * (x / k) + k     := Int.add_lt_add_left (emod_lt_of_pos x h) _

@[simp] theorem add_mul_emod_self {a b c : Int} : (a + b * c) % c = a % c :=
  if cz : c = 0 then by
    rw [cz, Int.mul_zero, Int.add_zero]
  else by
    rw [Int.emod_def, Int.emod_def, Int.add_mul_ediv_right _ _ cz, Int.add_comm _ b,
      Int.mul_add, Int.mul_comm, ← Int.sub_sub, Int.add_sub_cancel]

@[simp] theorem add_mul_emod_self_left (a b c : Int) : (a + b * c) % b = a % b := by
  rw [Int.mul_comm, Int.add_mul_emod_self]

@[simp] theorem add_neg_mul_emod_self {a b c : Int} : (a + -(b * c)) % c = a % c := by
  rw [Int.neg_mul_eq_neg_mul, add_mul_emod_self]

@[simp] theorem add_neg_mul_emod_self_left {a b c : Int} : (a + -(b * c)) % b = a % b := by
  rw [Int.neg_mul_eq_mul_neg, add_mul_emod_self_left]

@[simp] theorem add_emod_self {a b : Int} : (a + b) % b = a % b := by
  have := add_mul_emod_self_left a b 1; rwa [Int.mul_one] at this

@[simp] theorem add_emod_self_left {a b : Int} : (a + b) % a = b % a := by
  rw [Int.add_comm, Int.add_emod_self]

theorem neg_emod {a b : Int} : -a % b = (b - a) % b := by
  rw [← add_emod_self_left]; rfl

@[simp] theorem emod_neg (a b : Int) : a % -b = a % b := by
  rw [emod_def, emod_def, Int.ediv_neg, Int.neg_mul_neg]

@[simp] theorem emod_add_emod (m n k : Int) : (m % n + k) % n = (m + k) % n := by
  have := (add_mul_emod_self_left (m % n + k) n (m / n)).symm
  rwa [Int.add_right_comm, emod_add_ediv] at this

@[simp] theorem add_emod_emod (m n k : Int) : (m + n % k) % k = (m + n) % k := by
  rw [Int.add_comm, emod_add_emod, Int.add_comm]

theorem add_emod (a b n : Int) : (a + b) % n = (a % n + b % n) % n := by
  rw [add_emod_emod, emod_add_emod]

theorem add_emod_eq_add_emod_right {m n k : Int} (i : Int)
    (H : m % n = k % n) : (m + i) % n = (k + i) % n := by
  rw [← emod_add_emod, ← emod_add_emod k, H]

theorem emod_add_cancel_right {m n k : Int} (i) : (m + i) % n = (k + i) % n ↔ m % n = k % n :=
  ⟨fun H => by
    have := add_emod_eq_add_emod_right (-i) H
    rwa [Int.add_neg_cancel_right, Int.add_neg_cancel_right] at this,
  add_emod_eq_add_emod_right _⟩

@[simp] theorem mul_emod_left (a b : Int) : (a * b) % b = 0 := by
  rw [← Int.zero_add (a * b), Int.add_mul_emod_self, Int.zero_emod]

@[simp] theorem mul_emod_right (a b : Int) : (a * b) % a = 0 := by
  rw [Int.mul_comm, mul_emod_left]

theorem mul_emod (a b n : Int) : (a * b) % n = (a % n) * (b % n) % n := by
  conv => lhs; rw [
    ← emod_add_ediv a n, ← emod_add_ediv' b n, Int.add_mul, Int.mul_add, Int.mul_add,
    Int.mul_assoc, Int.mul_assoc, ← Int.mul_add n _ _, add_mul_emod_self_left,
    ← Int.mul_assoc, add_mul_emod_self]

@[simp] theorem emod_self {a : Int} : a % a = 0 := by
  have := mul_emod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem neg_emod_self (a : Int) : -a % a = 0 := by
  rw [neg_emod, Int.sub_self, zero_emod]

@[simp] theorem emod_emod_of_dvd (n : Int) {m k : Int}
    (h : m ∣ k) : (n % k) % m = n % m := by
  conv => rhs; rw [← emod_add_ediv n k]
  match k, h with
  | _, ⟨t, rfl⟩ => rw [Int.mul_assoc, add_mul_emod_self_left]

@[simp] theorem emod_emod (a b : Int) : (a % b) % b = a % b := by
  conv => rhs; rw [← emod_add_ediv a b, add_mul_emod_self_left]

@[simp] theorem emod_sub_emod (m n k : Int) : (m % n - k) % n = (m - k) % n :=
  Int.emod_add_emod m n (-k)

@[simp] theorem sub_emod_emod (m n k : Int) : (m - n % k) % k = (m - n) % k := by
  apply (emod_add_cancel_right (n % k)).mp
  rw [Int.sub_add_cancel, Int.add_emod_emod, Int.sub_add_cancel]

theorem sub_emod (a b n : Int) : (a - b) % n = (a % n - b % n) % n := by
  apply (emod_add_cancel_right b).mp
  rw [Int.sub_add_cancel, ← Int.add_emod_emod, Int.sub_add_cancel, emod_emod]

theorem emod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
  have b0 := Int.le_trans H1 (Int.le_of_lt H2)
  match a, b, eq_ofNat_of_zero_le H1, eq_ofNat_of_zero_le b0 with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg ofNat <| Nat.mod_eq_of_lt (Int.ofNat_lt.1 H2)

@[simp] theorem emod_self_add_one {x : Int} (h : 0 ≤ x) : x % (x + 1) = x :=
  emod_eq_of_lt h (Int.lt_succ x)

/-! ### properties of `/` and `%` -/

theorem mul_ediv_cancel_of_emod_eq_zero {a b : Int} (H : a % b = 0) : b * (a / b) = a := by
  have := emod_add_ediv a b; rwa [H, Int.zero_add] at this

theorem ediv_mul_cancel_of_emod_eq_zero {a b : Int} (H : a % b = 0) : a / b * b = a := by
  rw [Int.mul_comm, mul_ediv_cancel_of_emod_eq_zero H]

theorem emod_two_eq (x : Int) : x % 2 = 0 ∨ x % 2 = 1 := by
  have h₁ : 0 ≤ x % 2 := Int.emod_nonneg x (by decide)
  have h₂ : x % 2 < 2 := Int.emod_lt_of_pos x (by decide)
  match x % 2, h₁, h₂ with
  | 0, _, _ => simp
  | 1, _, _ => simp

theorem add_emod_eq_add_emod_left {m n k : Int} (i : Int)
    (H : m % n = k % n) : (i + m) % n = (i + k) % n := by
  rw [Int.add_comm, add_emod_eq_add_emod_right _ H, Int.add_comm]

theorem emod_add_cancel_left {m n k i : Int} : (i + m) % n = (i + k) % n ↔ m % n = k % n := by
  rw [Int.add_comm, Int.add_comm i, emod_add_cancel_right]

theorem emod_sub_cancel_right {m n k : Int} (i) : (m - i) % n = (k - i) % n ↔ m % n = k % n :=
  emod_add_cancel_right _

theorem emod_eq_emod_iff_emod_sub_eq_zero {m n k : Int} : m % n = k % n ↔ (m - k) % n = 0 :=
  (emod_sub_cancel_right k).symm.trans <| by simp [Int.sub_self]

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

@[simp] theorem mul_emod_mul_of_pos
    {a : Int} (b c : Int) (H : 0 < a) : (a * b) % (a * c) = a * (b % c) := by
  rw [emod_def, emod_def, mul_ediv_mul_of_pos _ _ H, Int.mul_sub, Int.mul_assoc]

theorem lt_ediv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a / b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.emod_def .. ▸ emod_lt_of_pos _ H

theorem natAbs_div_le_natAbs (a b : Int) : natAbs (a / b) ≤ natAbs a :=
  match b, eq_nat_or_neg b with
  | _, ⟨n, .inl rfl⟩ => aux _ _
  | _, ⟨n, .inr rfl⟩ => by rw [Int.ediv_neg, natAbs_neg]; apply aux
where
  aux : ∀ (a : Int) (n : Nat), natAbs (a / n) ≤ natAbs a
  | ofNat _, _ => Nat.div_le_self ..
  | -[_+1], 0 => Nat.zero_le _
  | -[_+1], succ _ => Nat.succ_le_succ (Nat.div_le_self _ _)

theorem ediv_le_self {a : Int} (b : Int) (Ha : 0 ≤ a) : a / b ≤ a := by
  have := Int.le_trans le_natAbs (ofNat_le.2 <| natAbs_div_le_natAbs a b)
  rwa [natAbs_of_nonneg Ha] at this

theorem dvd_of_emod_eq_zero {a b : Int} (H : b % a = 0) : a ∣ b :=
  ⟨b / a, (mul_ediv_cancel_of_emod_eq_zero H).symm⟩

theorem dvd_emod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ x % m - x := by
  apply dvd_of_emod_eq_zero
  simp [sub_emod]

theorem emod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → b % a = 0
  | _, _, ⟨_, rfl⟩ => mul_emod_right ..

theorem dvd_iff_emod_eq_zero {a b : Int} : a ∣ b ↔ b % a = 0 :=
  ⟨emod_eq_zero_of_dvd, dvd_of_emod_eq_zero⟩

@[simp] theorem neg_mul_emod_left (a b : Int) : -(a * b) % b = 0 := by
  rw [← dvd_iff_emod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_left a b

@[simp] theorem neg_mul_emod_right (a b : Int) : -(a * b) % a = 0 := by
  rw [← dvd_iff_emod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_right a b

instance decidableDvd : DecidableRel (α := Int) (· ∣ ·) := fun _ _ =>
  decidable_of_decidable_of_iff (dvd_iff_emod_eq_zero ..).symm

theorem emod_pos_of_not_dvd {a b : Int} (h : ¬ a ∣ b) : a = 0 ∨ 0 < b % a := by
  rw [dvd_iff_emod_eq_zero] at h
  by_cases w : a = 0
  · simp_all
  · exact Or.inr (Int.lt_iff_le_and_ne.mpr ⟨emod_nonneg b w, Ne.symm h⟩)

protected theorem mul_ediv_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b) / c = a * (b / c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_ediv_cancel_left _ cz, Int.mul_ediv_cancel_left _ cz]

protected theorem mul_ediv_assoc' (b : Int) {a c : Int}
    (h : c ∣ a) : (a * b) / c = a / c * b := by
  rw [Int.mul_comm, Int.mul_ediv_assoc _ h, Int.mul_comm]

theorem neg_ediv_of_dvd : ∀ {a b : Int}, b ∣ a → (-a) / b = -(a / b)
  | _, b, ⟨c, rfl⟩ => by
    by_cases bz : b = 0
    · simp [bz]
    · rw [Int.neg_mul_eq_mul_neg, Int.mul_ediv_cancel_left _ bz, Int.mul_ediv_cancel_left _ bz]

@[simp] theorem neg_mul_ediv_cancel (a b : Int) (h : b ≠ 0) : -(a * b) / b = -a := by
  rw [neg_ediv_of_dvd (Int.dvd_mul_left a b), mul_ediv_cancel _ h]

@[simp] theorem neg_mul_ediv_cancel_left (a b : Int) (h : a ≠ 0) : -(a * b) / a = -b := by
  rw [neg_ediv_of_dvd (Int.dvd_mul_right a b), mul_ediv_cancel_left _ h]

theorem sub_ediv_of_dvd (a : Int) {b c : Int}
    (hcb : c ∣ b) : (a - b) / c = a / c - b / c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_ediv_of_dvd_right (Int.dvd_neg.2 hcb)]
  congr; exact Int.neg_ediv_of_dvd hcb

@[simp] theorem ediv_one : ∀ a : Int, a / 1 = a
  | (_:Nat) => congrArg Nat.cast (Nat.div_one _)
  | -[_+1]  => congrArg negSucc (Nat.div_one _)

@[simp] theorem emod_one (a : Int) : a % 1 = 0 := by
  simp [emod_def, Int.one_mul, Int.sub_self]

@[simp] protected theorem ediv_self {a : Int} (H : a ≠ 0) : a / a = 1 := by
  have := Int.mul_ediv_cancel 1 H; rwa [Int.one_mul] at this

@[simp] protected theorem neg_ediv_self (a : Int) (h : a ≠ 0) : (-a) / a = -1 := by
  rw [neg_ediv_of_dvd (Int.dvd_refl a), Int.ediv_self h]

@[simp]
theorem emod_sub_cancel (x y : Int): (x - y) % y = x % y := by
  by_cases h : y = 0
  · simp [h]
  · simp only [Int.emod_def, Int.sub_ediv_of_dvd, Int.dvd_refl, Int.ediv_self h, Int.mul_sub]
    simp [Int.mul_one, Int.sub_sub, Int.add_comm y]

@[simp] theorem add_neg_emod_self (a b : Int) : (a + -b) % b = a % b := by
  rw [← Int.sub_eq_add_neg, emod_sub_cancel]

@[simp] theorem neg_add_emod_self (a b : Int) : (-a + b) % a = b % a := by
  rw [Int.add_comm, add_neg_emod_self]

/-- If `a % b = c` then `b` divides `a - c`. -/
theorem dvd_sub_of_emod_eq {a b c : Int} (h : a % b = c) : b ∣ a - c := by
  have hx : (a % b) % b = c % b := by
    rw [h]
  rw [Int.emod_emod, ← emod_sub_cancel_right c, Int.sub_self, zero_emod] at hx
  exact dvd_of_emod_eq_zero hx

protected theorem ediv_mul_cancel {a b : Int} (H : b ∣ a) : a / b * b = a :=
  ediv_mul_cancel_of_emod_eq_zero (emod_eq_zero_of_dvd H)

protected theorem mul_ediv_cancel' {a b : Int} (H : a ∣ b) : a * (b / a) = b := by
  rw [Int.mul_comm, Int.ediv_mul_cancel H]

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
  rw [← Int.add_sub_cancel ((a-b) / c), ← Int.add_ediv_of_dvd_left hcab, Int.sub_add_cancel]

@[simp] protected theorem ediv_left_inj {a b d : Int}
    (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h => ?_, congrArg (ediv · d)⟩
  rw [← Int.mul_ediv_cancel' hda, ← Int.mul_ediv_cancel' hdb, h]

theorem ediv_sign : ∀ a b, a / sign b = a * sign b
  | _, succ _ => by simp [sign, Int.mul_one]
  | _, 0 => by simp [sign, Int.mul_zero]
  | _, -[_+1] => by simp [sign, Int.mul_neg, Int.mul_one]

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

protected theorem ediv_le_of_le_mul {a b c : Int} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b :=
  le_of_mul_le_mul_right (Int.le_trans (Int.ediv_mul_le _ (Int.ne_of_gt H)) H') H

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

protected theorem ediv_le_ediv {a b c : Int} (H : 0 < c) (H' : a ≤ b) : a / c ≤ b / c :=
  Int.le_ediv_of_mul_le H (Int.le_trans (Int.ediv_mul_le _ (Int.ne_of_gt H)) H')

protected theorem lt_mul_of_ediv_lt {a b c : Int} (H1 : 0 < c) (H2 : a / c < b) : a < b * c :=
  Int.lt_of_not_ge <| mt (Int.le_ediv_of_mul_le H1) (Int.not_le_of_gt H2)

protected theorem ediv_lt_iff_lt_mul {a b c : Int} (H : 0 < c) : a / c < b ↔ a < b * c :=
  ⟨Int.lt_mul_of_ediv_lt H, Int.ediv_lt_of_lt_mul H⟩

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

/-! ### tdiv -/

@[simp] protected theorem tdiv_one : ∀ a : Int, a.tdiv 1 = a
  | (n:Nat) => congrArg ofNat (Nat.div_one _)
  | -[n+1] => by simp [Int.tdiv, neg_ofNat_succ]; rfl

unseal Nat.div in
@[simp] protected theorem tdiv_neg : ∀ a b : Int, a.tdiv (-b) = -(a.tdiv b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero]; rfl
  | ofNat _, -[_+1] | -[_+1], succ _ => (Int.neg_neg _).symm
  | ofNat _, succ _ | -[_+1], 0 | -[_+1], -[_+1] => rfl

unseal Nat.div in
@[simp] protected theorem neg_tdiv : ∀ a b : Int, (-a).tdiv b = -(a.tdiv b)
  | 0, n => by simp [Int.neg_zero]
  | succ _, (n:Nat) | -[_+1], 0 | -[_+1], -[_+1] => rfl
  | succ _, -[_+1] | -[_+1], succ _ => (Int.neg_neg _).symm

protected theorem neg_tdiv_neg (a b : Int) : (-a).tdiv (-b) = a.tdiv b := by
  simp [Int.tdiv_neg, Int.neg_tdiv, Int.neg_neg]

protected theorem tdiv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.tdiv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_zero_le _

protected theorem tdiv_nonpos {a b : Int} (Ha : 0 ≤ a) (Hb : b ≤ 0) : a.tdiv b ≤ 0 :=
  Int.nonpos_of_neg_nonneg <| Int.tdiv_neg .. ▸ Int.tdiv_nonneg Ha (Int.neg_nonneg_of_nonpos Hb)

theorem tdiv_eq_zero_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.tdiv b = 0 :=
  match a, b, eq_ofNat_of_zero_le H1, eq_succ_of_zero_lt (Int.lt_of_le_of_lt H1 H2) with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => congrArg Nat.cast <| Nat.div_eq_of_lt <| ofNat_lt.1 H2

@[simp] protected theorem mul_tdiv_cancel (a : Int) {b : Int} (H : b ≠ 0) : (a * b).tdiv b = a :=
  have : ∀ {a b : Nat}, (b : Int) ≠ 0 → (tdiv (a * b) b : Int) = a := fun H => by
    rw [← ofNat_mul, ← ofNat_tdiv,
      Nat.mul_div_cancel _ <| Nat.pos_of_ne_zero <| Int.ofNat_ne_zero.1 H]
  match a, b, a.eq_nat_or_neg, b.eq_nat_or_neg with
  | _, _, ⟨a, .inl rfl⟩, ⟨b, .inl rfl⟩ => this H
  | _, _, ⟨a, .inl rfl⟩, ⟨b, .inr rfl⟩ => by
    rw [Int.mul_neg, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg,
      this (Int.neg_ne_zero.1 H)]
  | _, _, ⟨a, .inr rfl⟩, ⟨b, .inl rfl⟩ => by rw [Int.neg_mul, Int.neg_tdiv, this H]
  | _, _, ⟨a, .inr rfl⟩, ⟨b, .inr rfl⟩ => by
    rw [Int.neg_mul_neg, Int.tdiv_neg, this (Int.neg_ne_zero.1 H)]

@[simp] protected theorem mul_tdiv_cancel_left (b : Int) (H : a ≠ 0) : (a * b).tdiv a = b :=
  Int.mul_comm .. ▸ Int.mul_tdiv_cancel _ H

@[simp] protected theorem tdiv_self {a : Int} (H : a ≠ 0) : a.tdiv a = 1 := by
  have := Int.mul_tdiv_cancel 1 H; rwa [Int.one_mul] at this

theorem mul_tdiv_cancel_of_tmod_eq_zero {a b : Int} (H : a.tmod b = 0) : b * (a.tdiv b) = a := by
  have := tmod_add_tdiv a b; rwa [H, Int.zero_add] at this

theorem tdiv_mul_cancel_of_tmod_eq_zero {a b : Int} (H : a.tmod b = 0) : a.tdiv b * b = a := by
  rw [Int.mul_comm, mul_tdiv_cancel_of_tmod_eq_zero H]

theorem dvd_of_tmod_eq_zero {a b : Int} (H : tmod b a = 0) : a ∣ b :=
  ⟨b.tdiv a, (mul_tdiv_cancel_of_tmod_eq_zero H).symm⟩

protected theorem mul_tdiv_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b).tdiv c = a * (b.tdiv c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_tdiv_cancel_left _ cz, Int.mul_tdiv_cancel_left _ cz]

protected theorem mul_tdiv_assoc' (b : Int) {a c : Int} (h : c ∣ a) :
    (a * b).tdiv c = a.tdiv c * b := by
  rw [Int.mul_comm, Int.mul_tdiv_assoc _ h, Int.mul_comm]

theorem tdiv_dvd_tdiv : ∀ {a b c : Int}, a ∣ b → b ∣ c → b.tdiv a ∣ c.tdiv a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ => by
    by_cases az : a = 0
    · simp [az]
    · rw [Int.mul_tdiv_cancel_left _ az, Int.mul_assoc, Int.mul_tdiv_cancel_left _ az]
      apply Int.dvd_mul_right

@[simp] theorem natAbs_tdiv (a b : Int) : natAbs (a.tdiv b) = (natAbs a).div (natAbs b) :=
  match a, b, eq_nat_or_neg a, eq_nat_or_neg b with
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inl rfl⟩ => rfl
  | _, _, ⟨_, .inl rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.tdiv_neg, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inl rfl⟩ => by rw [Int.neg_tdiv, natAbs_neg, natAbs_neg]; rfl
  | _, _, ⟨_, .inr rfl⟩, ⟨_, .inr rfl⟩ => by rw [Int.neg_tdiv_neg, natAbs_neg, natAbs_neg]; rfl

protected theorem tdiv_eq_of_eq_mul_right {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = b * c) : a.tdiv b = c := by rw [H2, Int.mul_tdiv_cancel_left _ H1]

protected theorem eq_tdiv_of_mul_eq_right {a b c : Int}
    (H1 : a ≠ 0) (H2 : a * b = c) : b = c.tdiv a :=
  (Int.tdiv_eq_of_eq_mul_right H1 H2.symm).symm

/-! ### (t-)mod -/

theorem ofNat_tmod (m n : Nat) : (↑(m % n) : Int) = tmod m n := rfl

@[simp] theorem tmod_one (a : Int) : tmod a 1 = 0 := by
  simp [tmod_def, Int.tdiv_one, Int.one_mul, Int.sub_self]

theorem tmod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : tmod a b = a := by
  rw [tmod_eq_emod H1 (Int.le_trans H1 (Int.le_of_lt H2)), emod_eq_of_lt H1 H2]

theorem tmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : tmod a b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨n, rfl⟩ => ofNat_lt.2 <| Nat.mod_lt _ n.succ_pos
  | -[_+1], _, ⟨n, rfl⟩ => Int.lt_of_le_of_lt
    (Int.neg_nonpos_of_nonneg <| Int.ofNat_nonneg _) (ofNat_pos.2 n.succ_pos)

theorem tmod_nonneg : ∀ {a : Int} (b : Int), 0 ≤ a → 0 ≤ tmod a b
  | ofNat _, -[_+1], _ | ofNat _, ofNat _, _ => ofNat_nonneg _

@[simp] theorem tmod_neg (a b : Int) : tmod a (-b) = tmod a b := by
  rw [tmod_def, tmod_def, Int.tdiv_neg, Int.neg_mul_neg]

@[simp] theorem mul_tmod_left (a b : Int) : (a * b).tmod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.tmod_def, Int.mul_tdiv_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_tmod_right (a b : Int) : (a * b).tmod a = 0 := by
  rw [Int.mul_comm, mul_tmod_left]

theorem tmod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → tmod b a = 0
  | _, _, ⟨_, rfl⟩ => mul_tmod_right ..

theorem dvd_iff_tmod_eq_zero {a b : Int} : a ∣ b ↔ tmod b a = 0 :=
  ⟨tmod_eq_zero_of_dvd, dvd_of_tmod_eq_zero⟩

@[simp] theorem neg_mul_tmod_right (a b : Int) : (-(a * b)).tmod a = 0 := by
  rw [← dvd_iff_tmod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_right a b

@[simp] theorem neg_mul_tmod_left (a b : Int) : (-(a * b)).tmod b = 0 := by
  rw [← dvd_iff_tmod_eq_zero, Int.dvd_neg]
  exact Int.dvd_mul_left a b

protected theorem tdiv_mul_cancel {a b : Int} (H : b ∣ a) : a.tdiv b * b = a :=
  tdiv_mul_cancel_of_tmod_eq_zero (tmod_eq_zero_of_dvd H)

protected theorem mul_tdiv_cancel' {a b : Int} (H : a ∣ b) : a * b.tdiv a = b := by
  rw [Int.mul_comm, Int.tdiv_mul_cancel H]

protected theorem eq_mul_of_tdiv_eq_right {a b c : Int}
    (H1 : b ∣ a) (H2 : a.tdiv b = c) : a = b * c := by rw [← H2, Int.mul_tdiv_cancel' H1]

@[simp] theorem tmod_self {a : Int} : a.tmod a = 0 := by
  have := mul_tmod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem neg_tmod_self (a : Int) : (-a).tmod a = 0 := by
  rw [← dvd_iff_tmod_eq_zero, Int.dvd_neg]
  exact Int.dvd_refl a

theorem lt_tdiv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.tdiv b + 1) * b := by
  rw [Int.add_mul, Int.one_mul, Int.mul_comm]
  exact Int.lt_add_of_sub_left_lt <| Int.tmod_def .. ▸ tmod_lt_of_pos _ H

protected theorem tdiv_eq_iff_eq_mul_right {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.tdiv b = c ↔ a = b * c :=
  ⟨Int.eq_mul_of_tdiv_eq_right H', Int.tdiv_eq_of_eq_mul_right H⟩

protected theorem tdiv_eq_iff_eq_mul_left {a b c : Int}
    (H : b ≠ 0) (H' : b ∣ a) : a.tdiv b = c ↔ a = c * b := by
  rw [Int.mul_comm]; exact Int.tdiv_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_tdiv_eq_left {a b c : Int}
    (H1 : b ∣ a) (H2 : a.tdiv b = c) : a = c * b := by
  rw [Int.mul_comm, Int.eq_mul_of_tdiv_eq_right H1 H2]

protected theorem tdiv_eq_of_eq_mul_left {a b c : Int}
    (H1 : b ≠ 0) (H2 : a = c * b) : a.tdiv b = c :=
  Int.tdiv_eq_of_eq_mul_right H1 (by rw [Int.mul_comm, H2])

protected theorem eq_zero_of_tdiv_eq_zero {d n : Int} (h : d ∣ n) (H : n.tdiv d = 0) : n = 0 := by
  rw [← Int.mul_tdiv_cancel' h, H, Int.mul_zero]

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

/-! ### fdiv -/

theorem fdiv_nonneg {a b : Int} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a.fdiv b :=
  match a, b, eq_ofNat_of_zero_le Ha, eq_ofNat_of_zero_le Hb with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => ofNat_fdiv .. ▸ ofNat_zero_le _

unseal Nat.div in
theorem fdiv_nonpos : ∀ {a b : Int}, 0 ≤ a → b ≤ 0 → a.fdiv b ≤ 0
  | 0, 0, _, _ | 0, -[_+1], _, _ | succ _, 0, _, _ | succ _, -[_+1], _, _ => ⟨_⟩

theorem fdiv_neg' : ∀ {a b : Int}, a < 0 → 0 < b → a.fdiv b < 0
  | -[_+1], succ _, _, _ => negSucc_lt_zero _

@[simp] theorem fdiv_one : ∀ a : Int, a.fdiv 1 = a
  | 0 => rfl
  | succ _ => congrArg Nat.cast (Nat.div_one _)
  | -[_+1] => congrArg negSucc (Nat.div_one _)

@[simp] theorem mul_fdiv_cancel (a : Int) {b : Int} (H : b ≠ 0) : fdiv (a * b) b = a :=
  if b0 : 0 ≤ b then by
    rw [fdiv_eq_ediv _ b0, mul_ediv_cancel _ H]
  else
    match a, b, Int.not_le.1 b0 with
    | 0, _, _ => by simp [Int.zero_mul]
    | succ a, -[b+1], _ => congrArg ofNat <| Nat.mul_div_cancel (succ a) b.succ_pos
    | -[a+1], -[b+1], _ => congrArg negSucc <| Nat.div_eq_of_lt_le
      (Nat.le_of_lt_succ <| Nat.mul_lt_mul_of_pos_right a.lt_succ_self b.succ_pos)
      (Nat.lt_succ_self _)

@[simp] theorem mul_fdiv_cancel_left (b : Int) (H : a ≠ 0) : fdiv (a * b) a = b :=
  Int.mul_comm .. ▸ Int.mul_fdiv_cancel _ H

@[simp] protected theorem fdiv_self {a : Int} (H : a ≠ 0) : a.fdiv a = 1 := by
  have := Int.mul_fdiv_cancel 1 H; rwa [Int.one_mul] at this

theorem lt_fdiv_add_one_mul_self (a : Int) {b : Int} (H : 0 < b) : a < (a.fdiv b + 1) * b :=
  Int.fdiv_eq_ediv _ (Int.le_of_lt H) ▸ lt_ediv_add_one_mul_self a H

/-! ### fmod -/

theorem ofNat_fmod (m n : Nat) : ↑(m % n) = fmod m n := by
  cases m <;> simp [fmod, Nat.succ_eq_add_one]

@[simp] theorem fmod_one (a : Int) : a.fmod 1 = 0 := by
  simp [fmod_def, Int.one_mul, Int.sub_self]

theorem fmod_eq_of_lt {a b : Int} (H1 : 0 ≤ a) (H2 : a < b) : a.fmod b = a := by
  rw [fmod_eq_emod _ (Int.le_trans H1 (Int.le_of_lt H2)), emod_eq_of_lt H1 H2]

theorem fmod_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a.fmod b :=
  fmod_eq_tmod ha hb ▸ tmod_nonneg _ ha

theorem fmod_nonneg' (a : Int) {b : Int} (hb : 0 < b) : 0 ≤ a.fmod b :=
  fmod_eq_emod _ (Int.le_of_lt hb) ▸ emod_nonneg _ (Int.ne_of_lt hb).symm

theorem fmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a.fmod b < b :=
  fmod_eq_emod _ (Int.le_of_lt H) ▸ emod_lt_of_pos a H

@[simp] theorem mul_fmod_left (a b : Int) : (a * b).fmod b = 0 :=
  if h : b = 0 then by simp [h, Int.mul_zero] else by
    rw [Int.fmod_def, Int.mul_fdiv_cancel _ h, Int.mul_comm, Int.sub_self]

@[simp] theorem mul_fmod_right (a b : Int) : (a * b).fmod a = 0 := by
  rw [Int.mul_comm, mul_fmod_left]

@[simp] theorem fmod_self {a : Int} : a.fmod a = 0 := by
  have := mul_fmod_left 1 a; rwa [Int.one_mul] at this

/-! ### Theorems crossing div/mod versions -/

theorem tdiv_eq_ediv_of_dvd {a b : Int} (h : b ∣ a) : a.tdiv b = a / b := by
  by_cases b0 : b = 0
  · simp [b0]
  · rw [Int.tdiv_eq_iff_eq_mul_left b0 h, ← Int.ediv_eq_iff_eq_mul_left b0 h]

theorem fdiv_eq_ediv_of_dvd : ∀ {a b : Int}, b ∣ a → a.fdiv b = a / b
  | _, b, ⟨c, rfl⟩ => by
    by_cases bz : b = 0
    · simp [bz]
    · rw [mul_fdiv_cancel_left _ bz, mul_ediv_cancel_left _ bz]

/-! ### bmod -/

@[simp] theorem bmod_emod : bmod x m % m = x % m := by
  dsimp [bmod]
  split <;> simp [Int.sub_emod]

@[simp]
theorem emod_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n) n = Int.bmod x n := by
  simp [bmod, Int.emod_emod]

theorem bmod_def (x : Int) (m : Nat) : bmod x m =
  if (x % m) < (m + 1) / 2 then
    x % m
  else
    (x % m) - m :=
  rfl

theorem bdiv_add_bmod (x : Int) (m : Nat) : m * bdiv x m + bmod x m = x := by
  unfold bdiv bmod
  split
  · simp_all only [Nat.cast_ofNat_Int, Int.mul_zero, emod_zero, Int.zero_add, Int.sub_zero,
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

@[simp]
theorem bmod_one_is_zero (x : Int) : Int.bmod x 1 = 0 := by
  simp [Int.bmod]

@[simp]
theorem bmod_add_cancel (x : Int) (n : Nat) : Int.bmod (x + n) n = Int.bmod x n := by
  simp [bmod_def]

@[simp]
theorem bmod_add_mul_cancel (x : Int) (n : Nat) (k : Int) : Int.bmod (x + n * k) n = Int.bmod x n := by
  simp [bmod_def]

@[simp]
theorem bmod_sub_cancel (x : Int) (n : Nat) : Int.bmod (x - n) n = Int.bmod x n := by
  simp [bmod_def]

@[simp]
theorem emod_add_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n + y) n = Int.bmod (x + y) n := by
  simp [Int.emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_right_comm,  Int.bmod_add_mul_cancel]

@[simp]
theorem emod_sub_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n - y) n = Int.bmod (x - y) n := by
  simp only [emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_right_comm,  Int.bmod_add_mul_cancel]

@[simp]
theorem sub_emod_bmod_congr (x : Int) (n : Nat) : Int.bmod (x - y%n) n = Int.bmod (x - y) n := by
  simp only [emod_def]
  rw [Int.sub_eq_add_neg, Int.neg_sub, Int.sub_eq_add_neg, ← Int.add_assoc, Int.add_right_comm,
    Int.bmod_add_mul_cancel, Int.sub_eq_add_neg]

@[simp]
theorem emod_mul_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n * y) n = Int.bmod (x * y) n := by
  simp [Int.emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_mul, Int.mul_assoc, Int.bmod_add_mul_cancel]

@[simp]
theorem bmod_add_bmod_congr : Int.bmod (Int.bmod x n + y) n = Int.bmod (x + y) n := by
  have := (@bmod_add_mul_cancel (Int.bmod x n + y) n (bdiv x n)).symm
  rwa [Int.add_right_comm, bmod_add_bdiv] at this

@[simp]
theorem bmod_sub_bmod_congr : Int.bmod (Int.bmod x n - y) n = Int.bmod (x - y) n :=
  @bmod_add_bmod_congr x n (-y)

theorem add_bmod_eq_add_bmod_right (i : Int)
    (H : bmod x n = bmod y n) : bmod (x + i) n = bmod (y + i) n := by
  rw [← bmod_add_bmod_congr, ← @bmod_add_bmod_congr y, H]

theorem bmod_add_cancel_right (i : Int) : bmod (x + i) n = bmod (y + i) n ↔ bmod x n = bmod y n :=
  ⟨fun H => by
    have := add_bmod_eq_add_bmod_right (-i) H
    rwa [Int.add_neg_cancel_right, Int.add_neg_cancel_right] at this,
  fun H => by rw [← bmod_add_bmod_congr, H, bmod_add_bmod_congr]⟩

@[simp] theorem add_bmod_bmod : Int.bmod (x + Int.bmod y n) n = Int.bmod (x + y) n := by
  rw [Int.add_comm x, Int.bmod_add_bmod_congr, Int.add_comm y]

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
    rw [Int.sub_mul, Int.sub_eq_add_neg, ← Int.mul_neg, bmod_add_mul_cancel, emod_mul_bmod_congr]

@[simp] theorem mul_bmod_bmod : Int.bmod (x * Int.bmod y n) n = Int.bmod (x * y) n := by
  rw [Int.mul_comm x, bmod_mul_bmod, Int.mul_comm x]

theorem add_bmod (a b : Int) (n : Nat) : (a + b).bmod n = (a.bmod n + b.bmod n).bmod n := by
  simp

theorem emod_bmod {x : Int} {m : Nat} : bmod (x % m) m = bmod x m := by
  simp [bmod]

@[simp] theorem bmod_bmod : bmod (bmod x m) m = bmod x m := by
  rw [bmod, bmod_emod]
  rfl

@[simp] theorem bmod_zero : Int.bmod 0 m = 0 := by
  dsimp [bmod]
  simp only [Int.zero_sub, ite_eq_left_iff, Int.neg_eq_zero]
  intro h
  rw [@Int.not_lt] at h
  match m with
  | 0 => rfl
  | (m+1) =>
    exfalso
    rw [natCast_add, ofNat_one, Int.add_assoc, add_ediv_of_dvd_right] at h
    change _ + 2 / 2 ≤ 0 at h
    rw [Int.ediv_self, ← ofNat_two, ← ofNat_ediv, add_one_le_iff, ← @Int.not_le] at h
    exact h (ofNat_nonneg _)
    all_goals decide

theorem dvd_bmod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ bmod x m - x := by
  dsimp [bmod]
  split
  · exact dvd_emod_sub_self
  · rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub]
    exact Int.dvd_sub dvd_emod_sub_self (Int.dvd_refl _)

theorem le_bmod {x : Int} {m : Nat} (h : 0 < m) : - (m/2) ≤ Int.bmod x m := by
  dsimp [bmod]
  have v : (m : Int) % 2 = 0 ∨ (m : Int) % 2 = 1 := emod_two_eq _
  split <;> rename_i w
  · refine Int.le_trans ?_ (Int.emod_nonneg _ ?_)
    · exact Int.neg_nonpos_of_nonneg (Int.ediv_nonneg (Int.ofNat_nonneg _) (by decide))
    · exact Int.ne_of_gt (ofNat_pos.mpr h)
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
    · show _ < 0
      have : x % m < m := emod_lt_of_pos x (ofNat_pos.mpr h)
      exact Int.sub_neg_of_lt this
    · exact Int.le.intro_sub _ rfl

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

-- This could be strengthed by changing to `w : x ≠ -1` if needed.
theorem bmod_natAbs_plus_one (x : Int) (w : 1 < x.natAbs) : bmod x (x.natAbs + 1) = - x.sign := by
  have t₁ : ∀ (x : Nat), x % (x + 2) = x :=
    fun x => Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (Nat.lt.base x))
  have t₂ : ∀ (x : Int), 0 ≤ x → x % (x + 2) = x := fun x h => by
    match x, h with
    | Int.ofNat x, _ => erw [← Int.ofNat_two, ← ofNat_add, ← ofNat_emod, t₁]; rfl
  cases x with
  | ofNat x =>
    simp only [bmod, ofNat_eq_coe, natAbs_ofNat, natCast_add, ofNat_one,
      emod_self_add_one (ofNat_nonneg x)]
    match x with
    | 0 => rw [if_pos] <;> simp +decide
    | (x+1) =>
      rw [if_neg]
      · simp [← Int.sub_sub]
      · refine Int.not_lt.mpr ?_
        simp only [← natCast_add, ← ofNat_one, ← ofNat_two, ← ofNat_ediv]
        match x with
        | 0 => apply Int.le_refl
        | (x+1) =>
          refine Int.ofNat_le.mpr ?_
          apply Nat.div_le_of_le_mul
          simp only [Nat.two_mul, Nat.add_assoc]
          apply Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_left
            _ _) _) _)
  | negSucc x =>
    rw [bmod, natAbs_negSucc, natCast_add, ofNat_one, sign_negSucc, Int.neg_neg,
      Nat.succ_eq_add_one, negSucc_emod]
    erw [t₂]
    · rw [natCast_add, ofNat_one, Int.add_sub_cancel, Int.add_comm, Int.add_sub_cancel, if_pos]
      · match x, w with
        | (x+1), _ =>
          rw [Int.add_assoc, add_ediv_of_dvd_right, show (1 + 1 : Int) = 2 by decide, Int.ediv_self]
          apply Int.lt_add_one_of_le
          rw [Int.add_comm, ofNat_add, Int.add_assoc, add_ediv_of_dvd_right,
            show ((1 : Nat) + 1 : Int) = 2 by decide, Int.ediv_self]
          apply Int.le_add_of_nonneg_left
          exact Int.le.intro_sub _ rfl
          all_goals decide
    · exact ofNat_nonneg x
    · exact succ_ofNat_pos (x + 1)

@[simp]
theorem bmod_neg_bmod : bmod (-(bmod x n)) n = bmod (-x) n := by
  apply (bmod_add_cancel_right x).mp
  rw [Int.add_left_neg, ← add_bmod_bmod, Int.add_left_neg]

/-! Helper theorems for `dvd` simproc -/

protected theorem dvd_eq_true_of_mod_eq_zero {a b : Int} (h : b % a == 0) : (a ∣ b) = True := by
  simp [Int.dvd_of_emod_eq_zero, eq_of_beq h]

protected theorem dvd_eq_false_of_mod_ne_zero {a b : Int} (h : b % a != 0) : (a ∣ b) = False := by
  simp [eq_of_beq] at h
  simp [Int.dvd_iff_emod_eq_zero, h]

end Int
