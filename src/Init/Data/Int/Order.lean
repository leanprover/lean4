/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.Int.Lemmas
import Init.ByCases

/-!
# Results about the order properties of the integers, and the integers as an ordered ring.
-/

open Nat

namespace Int

/-! ## Order properties of the integers -/

theorem nonneg_def {a : Int} : NonNeg a ↔ ∃ n : Nat, a = n :=
  ⟨fun ⟨n⟩ => ⟨n, rfl⟩, fun h => match a, h with | _, ⟨n, rfl⟩ => ⟨n⟩⟩

theorem NonNeg.elim {a : Int} : NonNeg a → ∃ n : Nat, a = n := nonneg_def.1

theorem nonneg_or_nonneg_neg : ∀ (a : Int), NonNeg a ∨ NonNeg (-a)
  | (_:Nat) => .inl ⟨_⟩
  | -[_+1]  => .inr ⟨_⟩

theorem le_def (a b : Int) : a ≤ b ↔ NonNeg (b - a) := .rfl

theorem lt_iff_add_one_le (a b : Int) : a < b ↔ a + 1 ≤ b := .rfl

theorem le.intro_sub {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  simp [le_def, h]; constructor

attribute [local simp] Int.add_left_neg Int.add_right_neg Int.neg_add

theorem le.intro {a b : Int} (n : Nat) (h : a + n = b) : a ≤ b :=
  le.intro_sub n <| by rw [← h, Int.add_comm]; simp [Int.sub_eq_add_neg, Int.add_assoc]

theorem le.dest_sub {a b : Int} (h : a ≤ b) : ∃ n : Nat, b - a = n := nonneg_def.1 h

theorem le.dest {a b : Int} (h : a ≤ b) : ∃ n : Nat, a + n = b :=
  let ⟨n, h₁⟩ := le.dest_sub h
  ⟨n, by rw [← h₁, Int.add_comm]; simp [Int.sub_eq_add_neg, Int.add_assoc]⟩

protected theorem le_total (a b : Int) : a ≤ b ∨ b ≤ a :=
  (nonneg_or_nonneg_neg (b - a)).imp_right fun H => by
    rwa [show -(b - a) = a - b by simp [Int.add_comm, Int.sub_eq_add_neg]] at H

@[simp] theorem ofNat_le {m n : Nat} : (↑m : Int) ≤ ↑n ↔ m ≤ n :=
  ⟨fun h =>
    let ⟨k, hk⟩ := le.dest h
    Nat.le.intro <| Int.ofNat.inj <| (Int.ofNat_add m k).trans hk,
  fun h =>
    let ⟨k, (hk : m + k = n)⟩ := Nat.le.dest h
    le.intro k (by rw [← hk]; rfl)⟩

theorem ofNat_zero_le (n : Nat) : 0 ≤ (↑n : Int) := ofNat_le.2 n.zero_le

theorem eq_ofNat_of_zero_le {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  have t := le.dest_sub h; rwa [Int.sub_zero] at t

theorem eq_succ_of_zero_lt {a : Int} (h : 0 < a) : ∃ n : Nat, a = n.succ :=
  let ⟨n, (h : ↑(1 + n) = a)⟩ := le.dest h
  ⟨n, by rw [Nat.add_comm] at h; exact h.symm⟩

theorem lt_add_succ (a : Int) (n : Nat) : a < a + Nat.succ n :=
  le.intro n <| by rw [Int.add_comm, Int.add_left_comm]; rfl

theorem lt.intro {a b : Int} {n : Nat} (h : a + Nat.succ n = b) : a < b :=
  h ▸ lt_add_succ a n

theorem lt.dest {a b : Int} (h : a < b) : ∃ n : Nat, a + Nat.succ n = b :=
  let ⟨n, h⟩ := le.dest h; ⟨n, by rwa [Int.add_comm, Int.add_left_comm] at h⟩

@[simp] theorem ofNat_lt {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← ofNat_succ, ofNat_le]; rfl

@[simp] theorem ofNat_pos {n : Nat} : 0 < (↑n : Int) ↔ 0 < n := ofNat_lt

theorem ofNat_nonneg (n : Nat) : 0 ≤ (n : Int) := ⟨_⟩

theorem ofNat_succ_pos (n : Nat) : 0 < (succ n : Int) := ofNat_lt.2 <| Nat.succ_pos _

@[simp] protected theorem le_refl (a : Int) : a ≤ a :=
  le.intro _ (Int.add_zero a)

protected theorem le_trans {a b c : Int} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  le.intro (n + m) <| by rw [← hm, ← hn, Int.add_assoc, ofNat_add]

protected theorem le_antisymm {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  have := hn; rw [← hm, Int.add_assoc, ← ofNat_add] at this
  have := Int.ofNat.inj <| Int.add_left_cancel <| this.trans (Int.add_zero _).symm
  rw [← hn, Nat.eq_zero_of_add_eq_zero_left this, ofNat_zero, Int.add_zero a]

protected theorem lt_irrefl (a : Int) : ¬a < a := fun H =>
  let ⟨n, hn⟩ := lt.dest H
  have : (a+Nat.succ n) = a+0 := by
    rw [hn, Int.add_zero]
  have : Nat.succ n = 0 := Int.ofNat.inj (Int.add_left_cancel this)
  show False from Nat.succ_ne_zero _ this

protected theorem ne_of_lt {a b : Int} (h : a < b) : a ≠ b := fun e => by
  cases e; exact Int.lt_irrefl _ h

protected theorem ne_of_gt {a b : Int} (h : b < a) : a ≠ b := (Int.ne_of_lt h).symm

protected theorem le_of_lt {a b : Int} (h : a < b) : a ≤ b :=
  let ⟨_, hn⟩ := lt.dest h; le.intro _ hn

protected theorem lt_iff_le_and_ne {a b : Int} : a < b ↔ a ≤ b ∧ a ≠ b := by
  refine ⟨fun h => ⟨Int.le_of_lt h, Int.ne_of_lt h⟩, fun ⟨aleb, aneb⟩ => ?_⟩
  let ⟨n, hn⟩ := le.dest aleb
  have : n ≠ 0 := aneb.imp fun eq => by rw [← hn, eq, ofNat_zero, Int.add_zero]
  apply lt.intro; rwa [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this)] at hn

theorem lt_succ (a : Int) : a < a + 1 := Int.le_refl _

protected theorem zero_lt_one : (0 : Int) < 1 := ⟨_⟩

protected theorem lt_iff_le_not_le {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [Int.lt_iff_le_and_ne]
  constructor <;> refine fun ⟨h, h'⟩ => ⟨h, h'.imp fun h' => ?_⟩
  · exact Int.le_antisymm h h'
  · subst h'; apply Int.le_refl

protected theorem not_le {a b : Int} : ¬a ≤ b ↔ b < a :=
  ⟨fun h => Int.lt_iff_le_not_le.2 ⟨(Int.le_total ..).resolve_right h, h⟩,
   fun h => (Int.lt_iff_le_not_le.1 h).2⟩

protected theorem not_lt {a b : Int} : ¬a < b ↔ b ≤ a :=
  by rw [← Int.not_le, Decidable.not_not]

protected theorem lt_trichotomy (a b : Int) : a < b ∨ a = b ∨ b < a :=
  if eq : a = b then .inr <| .inl eq else
  if le : a ≤ b then .inl <| Int.lt_iff_le_and_ne.2 ⟨le, eq⟩ else
  .inr <| .inr <| Int.not_le.1 le

protected theorem ne_iff_lt_or_gt {a b : Int} : a ≠ b ↔ a < b ∨ b < a := by
  constructor
  · intro h
    cases Int.lt_trichotomy a b
    case inl lt => exact Or.inl lt
    case inr h =>
      cases h
      case inl =>simp_all
      case inr gt => exact Or.inr gt
  · intro h
    cases h
    case inl lt => exact Int.ne_of_lt lt
    case inr gt => exact Int.ne_of_gt gt

protected theorem lt_or_gt_of_ne {a b : Int} : a ≠ b →  a < b ∨ b < a:= Int.ne_iff_lt_or_gt.mp

protected theorem eq_iff_le_and_ge {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · intro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂

protected theorem lt_of_le_of_lt {a b c : Int} (h₁ : a ≤ b) (h₂ : b < c) : a < c :=
  Int.not_le.1 fun h => Int.not_le.2 h₂ (Int.le_trans h h₁)

protected theorem lt_of_lt_of_le {a b c : Int} (h₁ : a < b) (h₂ : b ≤ c) : a < c :=
  Int.not_le.1 fun h => Int.not_le.2 h₁ (Int.le_trans h₂ h)

protected theorem lt_trans {a b c : Int} (h₁ : a < b) (h₂ : b < c) : a < c :=
  Int.lt_of_le_of_lt (Int.le_of_lt h₁) h₂

instance : Trans (α := Int) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Int.le_trans⟩

instance : Trans (α := Int) (· < ·) (· ≤ ·) (· < ·) := ⟨Int.lt_of_lt_of_le⟩

instance : Trans (α := Int) (· ≤ ·) (· < ·) (· < ·) := ⟨Int.lt_of_le_of_lt⟩

instance : Trans (α := Int) (· < ·) (· < ·) (· < ·) := ⟨Int.lt_trans⟩

protected theorem min_def (n m : Int) : min n m = if n ≤ m then n else m := rfl

protected theorem max_def (n m : Int) : max n m = if n ≤ m then m else n := rfl

protected theorem min_comm (a b : Int) : min a b = min b a := by
  simp [Int.min_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Int.le_total ..

protected theorem min_le_right (a b : Int) : min a b ≤ b := by rw [Int.min_def]; split <;> simp [*]

protected theorem min_le_left (a b : Int) : min a b ≤ a := Int.min_comm .. ▸ Int.min_le_right ..

protected theorem le_min {a b c : Int} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨Int.le_trans h (Int.min_le_left ..), Int.le_trans h (Int.min_le_right ..)⟩,
   fun ⟨h₁, h₂⟩ => by rw [Int.min_def]; split <;> assumption⟩

protected theorem max_comm (a b : Int) : max a b = max b a := by
  simp only [Int.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Int.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Int.le_total ..

protected theorem le_max_left (a b : Int) : a ≤ max a b := by rw [Int.max_def]; split <;> simp [*]

protected theorem le_max_right (a b : Int) : b ≤ max a b := Int.max_comm .. ▸ Int.le_max_left ..

protected theorem max_le {a b c : Int} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨Int.le_trans (Int.le_max_left ..) h, Int.le_trans (Int.le_max_right ..) h⟩,
   fun ⟨h₁, h₂⟩ => by rw [Int.max_def]; split <;> assumption⟩

theorem eq_natAbs_of_zero_le {a : Int} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_ofNat_of_zero_le h
  rw [e]; rfl

theorem le_natAbs {a : Int} : a ≤ natAbs a :=
  match Int.le_total 0 a with
  | .inl h => by rw [eq_natAbs_of_zero_le h]; apply Int.le_refl
  | .inr h => Int.le_trans h (ofNat_zero_le _)

theorem negSucc_lt_zero (n : Nat) : -[n+1] < 0 :=
  Int.not_le.1 fun h => let ⟨_, h⟩ := eq_ofNat_of_zero_le h; nomatch h

@[simp] theorem negSucc_not_nonneg (n : Nat) : 0 ≤ -[n+1] ↔ False := by
  simp only [Int.not_le, iff_false]; exact Int.negSucc_lt_zero n

protected theorem add_le_add_left {a b : Int} (h : a ≤ b) (c : Int) : c + a ≤ c + b :=
  let ⟨n, hn⟩ := le.dest h; le.intro n <| by rw [Int.add_assoc, hn]

protected theorem add_lt_add_left {a b : Int} (h : a < b) (c : Int) : c + a < c + b :=
  Int.lt_iff_le_and_ne.2 ⟨Int.add_le_add_left (Int.le_of_lt h) _, fun heq =>
    b.lt_irrefl <| by rwa [Int.add_left_cancel heq] at h⟩

protected theorem add_le_add_right {a b : Int} (h : a ≤ b) (c : Int) : a + c ≤ b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_le_add_left h c

protected theorem add_lt_add_right {a b : Int} (h : a < b) (c : Int) : a + c < b + c :=
  Int.add_comm c a ▸ Int.add_comm c b ▸ Int.add_lt_add_left h c

protected theorem le_of_add_le_add_left {a b c : Int} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption

protected theorem le_of_add_le_add_right {a b c : Int} (h : a + b ≤ c + b) : a ≤ c :=
  Int.le_of_add_le_add_left (a := b) <| by rwa [Int.add_comm b a, Int.add_comm b c]

protected theorem add_le_add_iff_left (a : Int) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨Int.le_of_add_le_add_left, (Int.add_le_add_left · _)⟩

protected theorem add_le_add_iff_right (c : Int) : a + c ≤ b + c ↔ a ≤ b :=
  ⟨Int.le_of_add_le_add_right, (Int.add_le_add_right · _)⟩

protected theorem add_le_add {a b c d : Int} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  Int.le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem le_add_of_nonneg_right {a b : Int} (h : 0 ≤ b) : a ≤ a + b := by
  have : a + b ≥ a + 0 := Int.add_le_add_left h a
  rwa [Int.add_zero] at this

protected theorem le_add_of_nonneg_left {a b : Int} (h : 0 ≤ b) : a ≤ b + a := by
  have : 0 + a ≤ b + a := Int.add_le_add_right h a
  rwa [Int.zero_add] at this

protected theorem neg_le_neg {a b : Int} (h : a ≤ b) : -b ≤ -a := by
  have : 0 ≤ -a + b := Int.add_left_neg a ▸ Int.add_le_add_left h (-a)
  have : 0 + -b ≤ -a + b + -b := Int.add_le_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem le_of_neg_le_neg {a b : Int} (h : -b ≤ -a) : a ≤ b :=
  suffices - -a ≤ - -b by simp [Int.neg_neg] at this; assumption
  Int.neg_le_neg h

protected theorem neg_nonpos_of_nonneg {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_nonneg_of_nonpos {a : Int} (h : a ≤ 0) : 0 ≤ -a := by
  have : -0 ≤ -a := Int.neg_le_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_lt_neg {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this

protected theorem neg_neg_of_pos {a : Int} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem neg_pos_of_neg {a : Int} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this

protected theorem sub_nonneg_of_le {a b : Int} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem le_of_sub_nonneg {a b : Int} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_pos_of_lt {a b : Int} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h

protected theorem lt_of_sub_pos {a b : Int} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h

protected theorem sub_left_le_of_le_add {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h

protected theorem sub_le_self (a : Int) {b : Int} (h : 0 ≤ b) : a - b ≤ a :=
  calc  a + -b
    _ ≤ a + 0 := Int.add_le_add_left (Int.neg_nonpos_of_nonneg h) _
    _ = a     := by rw [Int.add_zero]

protected theorem sub_lt_self (a : Int) {b : Int} (h : 0 < b) : a - b < a :=
  calc  a + -b
    _ < a + 0 := Int.add_lt_add_left (Int.neg_neg_of_pos h) _
    _ = a     := by rw [Int.add_zero]

theorem add_one_le_of_lt {a b : Int} (H : a < b) : a + 1 ≤ b := H

/- ### Order properties and multiplication -/


protected theorem mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  let ⟨n, hn⟩ := eq_ofNat_of_zero_le ha
  let ⟨m, hm⟩ := eq_ofNat_of_zero_le hb
  rw [hn, hm, ← ofNat_mul]; apply ofNat_nonneg

protected theorem mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  let ⟨n, hn⟩ := eq_succ_of_zero_lt ha
  let ⟨m, hm⟩ := eq_succ_of_zero_lt hb
  rw [hn, hm, ← ofNat_mul]; apply ofNat_succ_pos

protected theorem mul_lt_mul_of_pos_left {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have : 0 < c * (b - a) := Int.mul_pos h₂ (Int.sub_pos_of_lt h₁)
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_lt_mul_of_pos_right {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < (b - a) * c := Int.mul_pos this h₂
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_pos this

protected theorem mul_le_mul_of_nonneg_left {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
  if hba : b ≤ a then by
    rw [Int.le_antisymm hba h₁]; apply Int.le_refl
  else if hc0 : c ≤ 0 then by
    simp [Int.le_antisymm hc0 h₂, Int.zero_mul]
  else by
    exact Int.le_of_lt <| Int.mul_lt_mul_of_pos_left
      (Int.lt_iff_le_not_le.2 ⟨h₁, hba⟩) (Int.lt_iff_le_not_le.2 ⟨h₂, hc0⟩)

protected theorem mul_le_mul_of_nonneg_right {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  rw [Int.mul_comm, Int.mul_comm b]; exact Int.mul_le_mul_of_nonneg_left h₁ h₂

protected theorem mul_le_mul {a b c d : Int}
    (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right hac nn_b) (Int.mul_le_mul_of_nonneg_left hbd nn_c)

protected theorem mul_nonpos_of_nonneg_of_nonpos {a b : Int}
  (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at h

protected theorem mul_nonpos_of_nonpos_of_nonneg {a b : Int}
  (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right ha hb
  rwa [Int.zero_mul] at h

protected theorem mul_le_mul_of_nonpos_right {a b c : Int}
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
  have : -c ≥ 0 := Int.neg_nonneg_of_nonpos hc
  have : b * -c ≤ a * -c := Int.mul_le_mul_of_nonneg_right h this
  Int.le_of_neg_le_neg <| by rwa [← Int.neg_mul_eq_mul_neg, ← Int.neg_mul_eq_mul_neg] at this

protected theorem mul_le_mul_of_nonpos_left {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
  rw [Int.mul_comm a b, Int.mul_comm a c]
  apply Int.mul_le_mul_of_nonpos_right h ha

/- ## natAbs -/

@[simp] theorem natAbs_ofNat (n : Nat) : natAbs ↑n = n := rfl
@[simp] theorem natAbs_negSucc (n : Nat) : natAbs -[n+1] = n.succ := rfl
@[simp] theorem natAbs_zero : natAbs (0 : Int) = (0 : Nat) := rfl
@[simp] theorem natAbs_one : natAbs (1 : Int) = (1 : Nat) := rfl

@[simp] theorem natAbs_eq_zero : natAbs a = 0 ↔ a = 0 :=
  ⟨fun H => match a with
    | ofNat _ => congrArg ofNat H
    | -[_+1]  => absurd H (succ_ne_zero _),
  fun e => e ▸ rfl⟩

theorem natAbs_pos : 0 < natAbs a ↔ a ≠ 0 := by rw [Nat.pos_iff_ne_zero, Ne, natAbs_eq_zero]

@[simp] theorem natAbs_neg : ∀ (a : Int), natAbs (-a) = natAbs a
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

theorem natAbs_eq : ∀ (a : Int), a = natAbs a ∨ a = -↑(natAbs a)
  | ofNat _ => Or.inl rfl
  | -[_+1]  => Or.inr rfl

theorem natAbs_negOfNat (n : Nat) : natAbs (negOfNat n) = n := by
  cases n <;> rfl

theorem natAbs_mul (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]

theorem natAbs_eq_natAbs_iff {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases Int.natAbs_eq a with
    | inl h₁ | inr h₁ =>
      cases Int.natAbs_eq b with
      | inl h₂ | inr h₂ => rw [h₁, h₂]; simp [h]
  · cases h with (subst a; try rfl)
    | inr h => rw [Int.natAbs_neg]

theorem natAbs_of_nonneg {a : Int} (H : 0 ≤ a) : (natAbs a : Int) = a :=
  match a, eq_ofNat_of_zero_le H with
  | _, ⟨_, rfl⟩ => rfl

theorem ofNat_natAbs_of_nonpos {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  rw [← natAbs_neg, natAbs_of_nonneg (Int.neg_nonneg_of_nonpos H)]
