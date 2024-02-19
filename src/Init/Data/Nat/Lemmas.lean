/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Data.Nat.Dvd
import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2

/-! # Basic lemmas about natural numbers

The primary purpose of the lemmas in this file is to assist with reasoning
about sizes of objects, array indices and such.

This file was upstreamed from Std,
and later these lemmas should be organised into other files more systematically.
-/

namespace Nat

/-! ### le/lt -/

protected theorem lt_asymm {a b : Nat} (h : a < b) : ¬ b < a := Nat.not_lt.2 (Nat.le_of_lt h)
protected abbrev not_lt_of_gt := @Nat.lt_asymm
protected abbrev not_lt_of_lt := @Nat.lt_asymm

protected theorem lt_iff_le_not_le {m n : Nat} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun ⟨_, h⟩ => Nat.lt_of_not_ge h⟩
protected abbrev lt_iff_le_and_not_ge := @Nat.lt_iff_le_not_le

protected theorem lt_iff_le_and_ne {m n : Nat} : m < n ↔ m ≤ n ∧ m ≠ n :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.ne_of_lt h⟩, fun h => Nat.lt_of_le_of_ne h.1 h.2⟩

protected theorem ne_iff_lt_or_gt {a b : Nat} : a ≠ b ↔ a < b ∨ b < a :=
  ⟨Nat.lt_or_gt_of_ne, fun | .inl h => Nat.ne_of_lt h | .inr h => Nat.ne_of_gt h⟩
protected abbrev lt_or_gt := @Nat.ne_iff_lt_or_gt

protected abbrev le_or_ge := @Nat.le_total
protected abbrev le_or_le := @Nat.le_total

protected theorem eq_or_lt_of_not_lt {a b : Nat} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  (Nat.lt_trichotomy ..).resolve_left hnlt

protected theorem lt_or_eq_of_le {n m : Nat} (h : n ≤ m) : n < m ∨ n = m :=
  (Nat.lt_or_ge ..).imp_right (Nat.le_antisymm h)

protected theorem le_iff_lt_or_eq {n m : Nat} : n ≤ m ↔ n < m ∨ n = m :=
  ⟨Nat.lt_or_eq_of_le, fun | .inl h => Nat.le_of_lt h | .inr rfl => Nat.le_refl _⟩

protected theorem lt_succ_iff : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

protected theorem lt_succ_iff_lt_or_eq : m < succ n ↔ m < n ∨ m = n :=
  Nat.lt_succ_iff.trans Nat.le_iff_lt_or_eq

protected theorem eq_of_lt_succ_of_not_lt (hmn : m < n + 1) (h : ¬ m < n) : m = n :=
  (Nat.lt_succ_iff_lt_or_eq.1 hmn).resolve_left h

protected theorem eq_of_le_of_lt_succ (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (le_of_succ_le_succ h₂) h₁


/-! ## zero/one/two -/

theorem le_zero : i ≤ 0 ↔ i = 0 := ⟨Nat.eq_zero_of_le_zero, fun | rfl => Nat.le_refl _⟩

protected abbrev one_pos := @Nat.zero_lt_one

protected theorem two_pos : 0 < 2 := Nat.zero_lt_succ _

theorem add_one_ne_zero (n) : n + 1 ≠ 0 := succ_ne_zero _

protected theorem ne_zero_iff_zero_lt : n ≠ 0 ↔ 0 < n := Nat.pos_iff_ne_zero.symm

protected theorem zero_lt_two : 0 < 2 := Nat.zero_lt_succ _

protected theorem one_lt_two : 1 < 2 := Nat.succ_lt_succ Nat.zero_lt_one

protected theorem eq_zero_of_not_pos (h : ¬0 < n) : n = 0 :=
  Nat.eq_zero_of_le_zero (Nat.not_lt.1 h)

/-! ## succ/pred -/

attribute [simp] succ_ne_zero zero_lt_succ lt_succ_self Nat.pred_zero Nat.pred_succ Nat.pred_le

theorem succ_ne_self (n) : succ n ≠ n := Nat.ne_of_gt (lt_succ_self n)

theorem succ_le : succ n ≤ m ↔ n < m := .rfl

theorem lt_succ : m < succ n ↔ m ≤ n := ⟨le_of_lt_succ, lt_succ_of_le⟩

theorem lt_succ_of_lt (h : a < b) : a < succ b := le_succ_of_le h

theorem succ_pred_eq_of_ne_zero : ∀ {n}, n ≠ 0 → succ (pred n) = n
  | _+1, _ => rfl

theorem eq_zero_or_eq_succ_pred : ∀ n, n = 0 ∨ n = succ (pred n)
  | 0 => .inl rfl
  | _+1 => .inr rfl

theorem succ_inj' : succ a = succ b ↔ a = b := ⟨succ.inj, congrArg _⟩

theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := ⟨le_of_succ_le_succ, succ_le_succ⟩

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := ⟨lt_of_succ_lt_succ, succ_lt_succ⟩

theorem pred_inj : ∀ {a b}, 0 < a → 0 < b → pred a = pred b → a = b
  | _+1, _+1, _, _ => congrArg _

theorem pred_ne_self : ∀ {a}, a ≠ 0 → pred a ≠ a
  | _+1, _ => (succ_ne_self _).symm

theorem pred_lt_self : ∀ {a}, 0 < a → pred a < a
  | _+1, _ => lt_succ_self _

theorem pred_lt_pred : ∀ {n m}, n ≠ 0 → n < m → pred n < pred m
  | _+1, _+1, _, h => lt_of_succ_lt_succ h

theorem pred_le_iff_le_succ : ∀ {n m}, pred n ≤ m ↔ n ≤ succ m
  | 0, _ => ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  | _+1, _ => Nat.succ_le_succ_iff.symm

theorem le_succ_of_pred_le : pred n ≤ m → n ≤ succ m := pred_le_iff_le_succ.1

theorem pred_le_of_le_succ : n ≤ succ m → pred n ≤ m := pred_le_iff_le_succ.2

theorem lt_pred_iff_succ_lt : ∀ {n m}, n < pred m ↔ succ n < m
  | _, 0 => ⟨nofun, nofun⟩
  | _, _+1 => Nat.succ_lt_succ_iff.symm

theorem succ_lt_of_lt_pred : n < pred m → succ n < m := lt_pred_iff_succ_lt.1

theorem lt_pred_of_succ_lt : succ n < m → n < pred m := lt_pred_iff_succ_lt.2

theorem le_pred_iff_lt : ∀ {n m}, 0 < m → (n ≤ pred m ↔ n < m)
  | 0, _+1, _ => ⟨fun _ => Nat.zero_lt_succ _, fun _ => Nat.zero_le _⟩
  | _+1, _+1, _ => Nat.lt_pred_iff_succ_lt

theorem lt_of_le_pred (h : 0 < m) : n ≤ pred m → n < m := (le_pred_iff_lt h).1

theorem le_pred_of_lt (h : n < m) : n ≤ pred m := (le_pred_iff_lt (Nat.zero_lt_of_lt h)).2 h

theorem exists_eq_succ_of_ne_zero : ∀ {n}, n ≠ 0 → ∃ k, n = succ k
  | _+1, _ => ⟨_, rfl⟩

/-! ## add -/

protected theorem add_add_add_comm (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm b]

theorem one_add (n) : 1 + n = succ n := Nat.add_comm ..

theorem succ_eq_one_add (n) : succ n = 1 + n := (one_add _).symm

theorem succ_add_eq_add_succ (a b) : succ a + b = a + succ b := Nat.succ_add ..

protected theorem eq_zero_of_add_eq_zero_right (h : n + m = 0) : n = 0 :=
  (Nat.eq_zero_of_add_eq_zero h).1

protected theorem add_eq_zero_iff : n + m = 0 ↔ n = 0 ∧ m = 0 :=
  ⟨Nat.eq_zero_of_add_eq_zero, fun ⟨h₁, h₂⟩ => h₂.symm ▸ h₁⟩

protected theorem add_left_cancel_iff {n : Nat} : n + m = n + k ↔ m = k :=
  ⟨Nat.add_left_cancel, fun | rfl => rfl⟩

protected theorem add_right_cancel_iff {n : Nat} : m + n = k + n ↔ m = k :=
  ⟨Nat.add_right_cancel, fun | rfl => rfl⟩

protected theorem add_le_add_iff_left {n : Nat} : n + m ≤ n + k ↔ m ≤ k :=
  ⟨Nat.le_of_add_le_add_left, fun h => Nat.add_le_add_left h _⟩

protected theorem lt_of_add_lt_add_right : ∀ {n : Nat}, k + n < m + n → k < m
  | 0, h => h
  | _+1, h => Nat.lt_of_add_lt_add_right (Nat.lt_of_succ_lt_succ h)

protected theorem lt_of_add_lt_add_left {n : Nat} : n + k < n + m → k < m := by
  rw [Nat.add_comm n, Nat.add_comm n]; exact Nat.lt_of_add_lt_add_right

protected theorem add_lt_add_iff_left {k n m : Nat} : k + n < k + m ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_left, fun h => Nat.add_lt_add_left h _⟩

protected theorem add_lt_add_iff_right {k n m : Nat} : n + k < m + k ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_right, fun h => Nat.add_lt_add_right h _⟩

protected theorem add_lt_add_of_le_of_lt {a b c d : Nat} (hle : a ≤ b) (hlt : c < d) :
    a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right hle _) (Nat.add_lt_add_left hlt _)

protected theorem add_lt_add_of_lt_of_le {a b c d : Nat} (hlt : a < b) (hle : c ≤ d) :
    a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left hle _) (Nat.add_lt_add_right hlt _)

protected theorem lt_add_left (c : Nat) (h : a < b) : a < c + b :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

protected theorem lt_add_right (c : Nat) (h : a < b) : a < b + c :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

protected theorem lt_add_of_pos_right (h : 0 < k) : n < n + k :=
  Nat.add_lt_add_left h n

protected theorem lt_add_of_pos_left : 0 < k → n < k + n := by
  rw [Nat.add_comm]; exact Nat.lt_add_of_pos_right

protected theorem pos_of_lt_add_right (h : n < n + k) : 0 < k :=
  Nat.lt_of_add_lt_add_left h

protected theorem pos_of_lt_add_left : n < k + n → 0 < k := by
  rw [Nat.add_comm]; exact Nat.pos_of_lt_add_right

protected theorem lt_add_right_iff_pos : n < n + k ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_right, Nat.lt_add_of_pos_right⟩

protected theorem lt_add_left_iff_pos : n < k + n ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_left, Nat.lt_add_of_pos_left⟩

protected theorem add_pos_left (h : 0 < m) (n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

protected theorem add_pos_right (m) (h : 0 < n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

protected theorem add_self_ne_one : ∀ n, n + n ≠ 1
  | n+1, h => by rw [Nat.succ_add, Nat.succ_inj'] at h; contradiction

/-! ## sub -/

protected theorem sub_one (n) : n - 1 = pred n := rfl

protected theorem one_sub : ∀ n, 1 - n = if n = 0 then 1 else 0
  | 0 => rfl
  | _+1 => by rw [if_neg (Nat.succ_ne_zero _), Nat.succ_sub_succ, Nat.zero_sub]

theorem succ_sub_sub_succ (n m k) : succ n - m - succ k = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]

protected theorem sub_right_comm (m n k : Nat) : m - n - k = m - k - n := by
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

protected theorem add_sub_cancel_right (n m : Nat) : (n + m) - m = n := Nat.add_sub_cancel ..

@[simp] protected theorem add_sub_cancel' {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm, Nat.sub_add_cancel h]

theorem succ_sub_one (n) : succ n - 1 = n := rfl

protected theorem add_one_sub_one (n : Nat) : (n + 1) - 1 = n := rfl

protected theorem one_add_sub_one (n : Nat) : (1 + n) - 1 = n := Nat.add_sub_cancel_left 1 _

protected theorem sub_sub_self {n m : Nat} (h : m ≤ n) : n - (n - m) = m :=
  (Nat.sub_eq_iff_eq_add (Nat.sub_le ..)).2 (Nat.add_sub_of_le h).symm

protected theorem sub_add_comm {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  rw [Nat.sub_eq_iff_eq_add (Nat.le_trans h (Nat.le_add_right ..))]
  rwa [Nat.add_right_comm, Nat.sub_add_cancel]

protected theorem sub_eq_zero_iff_le : n - m = 0 ↔ n ≤ m :=
  ⟨Nat.le_of_sub_eq_zero, Nat.sub_eq_zero_of_le⟩

protected theorem sub_pos_iff_lt : 0 < n - m ↔ m < n :=
  ⟨Nat.lt_of_sub_pos, Nat.sub_pos_of_lt⟩

protected theorem sub_le_iff_le_add {a b c : Nat} : a - b ≤ c ↔ a ≤ c + b :=
  ⟨Nat.le_add_of_sub_le, sub_le_of_le_add⟩

protected theorem sub_le_iff_le_add' {a b c : Nat} : a - b ≤ c ↔ a ≤ b + c := by
  rw [Nat.add_comm, Nat.sub_le_iff_le_add]

protected theorem le_sub_iff_add_le {n : Nat} (h : k ≤ m) : n ≤ m - k ↔ n + k ≤ m :=
  ⟨Nat.add_le_of_le_sub h, Nat.le_sub_of_add_le⟩

@[deprecated Nat.le_sub_iff_add_le]
protected theorem add_le_to_le_sub (n : Nat) (h : m ≤ k) : n + m ≤ k ↔ n ≤ k - m :=
  (Nat.le_sub_iff_add_le h).symm

protected theorem add_le_of_le_sub' {n k m : Nat} (h : m ≤ k) : n ≤ k - m → m + n ≤ k :=
  Nat.add_comm .. ▸ Nat.add_le_of_le_sub h

@[deprecated Nat.add_le_of_le_sub']
protected theorem add_le_of_le_sub_left {n k m : Nat} (h : m ≤ k) : n ≤ k - m → m + n ≤ k :=
  Nat.add_le_of_le_sub' h

protected theorem le_sub_of_add_le' {n k m : Nat} : m + n ≤ k → n ≤ k - m :=
  Nat.add_comm .. ▸ Nat.le_sub_of_add_le

protected theorem le_sub_iff_add_le' {n : Nat} (h : k ≤ m) : n ≤ m - k ↔ k + n ≤ m :=
  ⟨Nat.add_le_of_le_sub' h, Nat.le_sub_of_add_le'⟩

protected theorem le_of_sub_le_sub_left : ∀ {n k m : Nat}, n ≤ k → k - m ≤ k - n → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le ..
  | _+1, _, 0, h₀, h₁ =>
    absurd (Nat.sub_lt (Nat.zero_lt_of_lt h₀) (Nat.zero_lt_succ _)) (Nat.not_lt.2 h₁)
  | _+1, _+1, _+1, h₀, h₁ => by
    simp only [Nat.succ_sub_succ] at h₁
    exact succ_le_succ <| Nat.le_of_sub_le_sub_left (Nat.le_of_succ_le_succ h₀) h₁

protected theorem sub_le_sub_iff_left {n m k : Nat} (h : n ≤ k) : k - m ≤ k - n ↔ n ≤ m :=
  ⟨Nat.le_of_sub_le_sub_left h, fun h => Nat.sub_le_sub_left h _⟩

protected theorem sub_lt_of_pos_le (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b :=
  Nat.sub_lt (Nat.lt_of_lt_of_le h₀ h₁) h₀
protected abbrev sub_lt_self := @Nat.sub_lt_of_pos_le

theorem add_lt_of_lt_sub' {a b c : Nat} : b < c - a → a + b < c := by
  rw [Nat.add_comm]; exact Nat.add_lt_of_lt_sub

protected theorem sub_add_lt_sub (h₁ : m + k ≤ n) (h₂ : 0 < k) : n - (m + k) < n - m := by
  rw [← Nat.sub_sub]; exact Nat.sub_lt_of_pos_le h₂ (Nat.le_sub_of_add_le' h₁)

theorem le_sub_one_of_lt : a < b → a ≤ b - 1 := Nat.le_pred_of_lt

theorem sub_one_lt_of_le (h₀ : 0 < a) (h₁ : a ≤ b) : a - 1 < b :=
  Nat.lt_of_lt_of_le (Nat.pred_lt' h₀) h₁

theorem sub_lt_succ (a b) : a - b < succ a := lt_succ_of_le (sub_le a b)

theorem sub_one_sub_lt (h : i < n) : n - 1 - i < n := by
  rw [Nat.sub_right_comm]; exact Nat.sub_one_lt_of_le (Nat.sub_pos_of_lt h) (Nat.sub_le ..)

protected theorem exists_eq_add_of_le (h : m ≤ n) : ∃ k : Nat, n = m + k :=
  ⟨n - m, (add_sub_of_le h).symm⟩

protected theorem exists_eq_add_of_le' (h : m ≤ n) : ∃ k : Nat, n = k + m :=
  ⟨n - m, (Nat.sub_add_cancel h).symm⟩

protected theorem exists_eq_add_of_lt (h : m < n) : ∃ k : Nat, n = m + k + 1 :=
  ⟨n - (m + 1), by rw [Nat.add_right_comm, add_sub_of_le h]⟩

/-! ### min/max -/

theorem succ_min_succ (x y) : min (succ x) (succ y) = succ (min x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.succ_le_succ h)]
  | inr h => rw [Nat.min_eq_right h, Nat.min_eq_right (Nat.succ_le_succ h)]

@[simp] protected theorem min_self (a : Nat) : min a a = a := Nat.min_eq_left (Nat.le_refl _)

@[simp] protected theorem zero_min (a) : min 0 a = 0 := Nat.min_eq_left (Nat.zero_le _)

@[simp] protected theorem min_zero (a) : min a 0 = 0 := Nat.min_eq_right (Nat.zero_le _)

protected theorem min_assoc : ∀ (a b c : Nat), min (min a b) c = min a (min b c)
  | 0, _, _ => by rw [Nat.zero_min, Nat.zero_min, Nat.zero_min]
  | _, 0, _ => by rw [Nat.zero_min, Nat.min_zero, Nat.zero_min]
  | _, _, 0 => by rw [Nat.min_zero, Nat.min_zero, Nat.min_zero]
  | _+1, _+1, _+1 => by simp only [Nat.succ_min_succ]; exact congrArg succ <| Nat.min_assoc ..

protected theorem sub_sub_eq_min : ∀ (a b : Nat), a - (a - b) = min a b
  | 0, _ => by rw [Nat.zero_sub, Nat.zero_min]
  | _, 0 => by rw [Nat.sub_zero, Nat.sub_self, Nat.min_zero]
  | _+1, _+1 => by
    rw [Nat.succ_sub_succ, Nat.succ_min_succ, Nat.succ_sub (Nat.sub_le ..)]
    exact congrArg succ <| Nat.sub_sub_eq_min ..

protected theorem sub_eq_sub_min (n m : Nat) : n - m = n - min n m := by
  cases Nat.le_total n m with
  | inl h => rw [Nat.min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.sub_self]
  | inr h => rw [Nat.min_eq_right h]

@[simp] protected theorem sub_add_min_cancel (n m : Nat) : n - m + min n m = n := by
  rw [Nat.sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left ..)]

protected theorem max_eq_right {a b : Nat} (h : a ≤ b) : max a b = b := if_pos h

protected theorem max_eq_left {a b : Nat} (h : b ≤ a) : max a b = a := by
  rw [Nat.max_comm]; exact Nat.max_eq_right h

protected theorem succ_max_succ (x y) : max (succ x) (succ y) = succ (max x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.succ_le_succ h)]
  | inr h => rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.succ_le_succ h)]

protected theorem max_le_of_le_of_le {a b c : Nat} : a ≤ c → b ≤ c → max a b ≤ c := by
  intros; cases Nat.le_total a b with
  | inl h => rw [Nat.max_eq_right h]; assumption
  | inr h => rw [Nat.max_eq_left h]; assumption

protected theorem max_le {a b c : Nat} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨Nat.le_trans (Nat.le_max_left ..) h, Nat.le_trans (Nat.le_max_right ..) h⟩,
   fun ⟨h₁, h₂⟩ => Nat.max_le_of_le_of_le h₁ h₂⟩

protected theorem max_lt {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.succ_le, ← Nat.succ_max_succ a b]; exact Nat.max_le

@[simp] protected theorem max_self (a : Nat) : max a a = a := Nat.max_eq_right (Nat.le_refl _)

@[simp] protected theorem zero_max (a) : max 0 a = a := Nat.max_eq_right (Nat.zero_le _)

@[simp] protected theorem max_zero (a) : max a 0 = a := Nat.max_eq_left (Nat.zero_le _)

protected theorem max_assoc : ∀ (a b c : Nat), max (max a b) c = max a (max b c)
  | 0, _, _ => by rw [Nat.zero_max, Nat.zero_max]
  | _, 0, _ => by rw [Nat.zero_max, Nat.max_zero]
  | _, _, 0 => by rw [Nat.max_zero, Nat.max_zero]
  | _+1, _+1, _+1 => by simp only [Nat.succ_max_succ]; exact congrArg succ <| Nat.max_assoc ..

protected theorem sub_add_eq_max (a b : Nat) : a - b + b = max a b := by
  match Nat.le_total a b with
  | .inl hl => rw [Nat.max_eq_right hl, Nat.sub_eq_zero_iff_le.mpr hl, Nat.zero_add]
  | .inr hr => rw [Nat.max_eq_left hr, Nat.sub_add_cancel hr]

protected theorem sub_eq_max_sub (n m : Nat) : n - m = max n m - m := by
  cases Nat.le_total m n with
  | inl h => rw [Nat.max_eq_left h]
  | inr h => rw [Nat.max_eq_right h, Nat.sub_eq_zero_of_le h, Nat.sub_self]

protected theorem max_min_distrib_left : ∀ (a b c : Nat), max a (min b c) = min (max a b) (max a c)
  | 0, _, _ => by simp only [Nat.zero_max]
  | _, 0, _ => by
    rw [Nat.zero_min, Nat.max_zero]
    exact Nat.min_eq_left (Nat.le_max_left ..) |>.symm
  | _, _, 0 => by
    rw [Nat.min_zero, Nat.max_zero]
    exact Nat.min_eq_right (Nat.le_max_left ..) |>.symm
  | _+1, _+1, _+1 => by
    simp only [Nat.succ_max_succ, Nat.succ_min_succ]
    exact congrArg succ <| Nat.max_min_distrib_left ..

protected theorem min_max_distrib_left : ∀ (a b c : Nat), min a (max b c) = max (min a b) (min a c)
  | 0, _, _ => by simp only [Nat.zero_min, Nat.max_self]
  | _, 0, _ => by simp only [Nat.min_zero, Nat.zero_max]
  | _, _, 0 => by simp only [Nat.min_zero, Nat.max_zero]
  | _+1, _+1, _+1 => by
    simp only [Nat.succ_max_succ, Nat.succ_min_succ]
    exact congrArg succ <| Nat.min_max_distrib_left ..

protected theorem max_min_distrib_right (a b c : Nat) :
    max (min a b) c = min (max a c) (max b c) := by
  repeat rw [Nat.max_comm _ c]
  exact Nat.max_min_distrib_left ..

protected theorem min_max_distrib_right (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  repeat rw [Nat.min_comm _ c]
  exact Nat.min_max_distrib_left ..

protected theorem add_max_add_right : ∀ (a b c : Nat), max (a + c) (b + c) = max a b + c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.succ_max_succ ..) <| congrArg _ (Nat.add_max_add_right ..)

protected theorem add_min_add_right : ∀ (a b c : Nat), min (a + c) (b + c) = min a b + c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.succ_min_succ ..) <| congrArg _ (Nat.add_min_add_right ..)

protected theorem add_max_add_left (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.add_max_add_right ..

protected theorem add_min_add_left (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.add_min_add_right ..

protected theorem pred_min_pred : ∀ (x y), min (pred x) (pred y) = pred (min x y)
  | 0, _ => by simp only [Nat.pred_zero, Nat.zero_min]
  | _, 0 => by simp only [Nat.pred_zero, Nat.min_zero]
  | _+1, _+1 => by simp only [Nat.pred_succ, Nat.succ_min_succ]

protected theorem pred_max_pred : ∀ (x y), max (pred x) (pred y) = pred (max x y)
  | 0, _ => by simp only [Nat.pred_zero, Nat.zero_max]
  | _, 0 => by simp only [Nat.pred_zero, Nat.max_zero]
  | _+1, _+1 => by simp only [Nat.pred_succ, Nat.succ_max_succ]

protected theorem sub_min_sub_right : ∀ (a b c : Nat), min (a - c) (b - c) = min a b - c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.pred_min_pred ..) <| congrArg _ (Nat.sub_min_sub_right ..)

protected theorem sub_max_sub_right : ∀ (a b c : Nat), max (a - c) (b - c) = max a b - c
  | _, _, 0 => rfl
  | _, _, _+1 => Eq.trans (Nat.pred_max_pred ..) <| congrArg _ (Nat.sub_max_sub_right ..)

-- protected theorem sub_min_sub_left (a b c : Nat) : min (a - b) (a - c) = a - max b c := by
--   induction b, c using Nat.recDiagAux with
--   | zero_left => rw [Nat.sub_zero, Nat.zero_max]; exact Nat.min_eq_right (Nat.sub_le ..)
--   | zero_right => rw [Nat.sub_zero, Nat.max_zero]; exact Nat.min_eq_left (Nat.sub_le ..)
--   | succ_succ _ _ ih => simp only [Nat.sub_succ, Nat.succ_max_succ, Nat.pred_min_pred, ih]

-- protected theorem sub_max_sub_left (a b c : Nat) : max (a - b) (a - c) = a - min b c := by
--   induction b, c using Nat.recDiagAux with
--   | zero_left => rw [Nat.sub_zero, Nat.zero_min]; exact Nat.max_eq_left (Nat.sub_le ..)
--   | zero_right => rw [Nat.sub_zero, Nat.min_zero]; exact Nat.max_eq_right (Nat.sub_le ..)
--   | succ_succ _ _ ih => simp only [Nat.sub_succ, Nat.succ_min_succ, Nat.pred_max_pred, ih]

-- protected theorem mul_max_mul_right (a b c : Nat) : max (a * c) (b * c) = max a b * c := by
--   induction a, b using Nat.recDiagAux with
--   | zero_left => simp only [Nat.zero_mul, Nat.zero_max]
--   | zero_right => simp only [Nat.zero_mul, Nat.max_zero]
--   | succ_succ _ _ ih => simp only [Nat.succ_mul, Nat.add_max_add_right, ih]

-- protected theorem mul_min_mul_right (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
--   induction a, b using Nat.recDiagAux with
--   | zero_left => simp only [Nat.zero_mul, Nat.zero_min]
--   | zero_right => simp only [Nat.zero_mul, Nat.min_zero]
--   | succ_succ _ _ ih => simp only [Nat.succ_mul, Nat.add_min_add_right, ih]

-- protected theorem mul_max_mul_left (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
--   repeat rw [Nat.mul_comm a]
--   exact Nat.mul_max_mul_right ..

-- protected theorem mul_min_mul_left (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
--   repeat rw [Nat.mul_comm a]
--   exact Nat.mul_min_mul_right ..

/-! ### mul -/

@[deprecated Nat.mul_le_mul_left]
protected theorem mul_le_mul_of_nonneg_left {a b c : Nat} : a ≤ b → c * a ≤ c * b :=
  Nat.mul_le_mul_left c

@[deprecated Nat.mul_le_mul_right]
protected theorem mul_le_mul_of_nonneg_right {a b c : Nat} : a ≤ b → a * c ≤ b * c :=
  Nat.mul_le_mul_right c

protected theorem mul_right_comm (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]

protected theorem mul_mul_mul_comm (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm b]

protected theorem mul_two (n) : n * 2 = n + n := by rw [Nat.mul_succ, Nat.mul_one]

protected theorem two_mul (n) : 2 * n = n + n := by rw [Nat.succ_mul, Nat.one_mul]

theorem mul_eq_zero : ∀ {m n}, n * m = 0 ↔ n = 0 ∨ m = 0
  | 0, _ => ⟨fun _ => .inr rfl, fun _ => rfl⟩
  | _, 0 => ⟨fun _ => .inl rfl, fun _ => Nat.zero_mul ..⟩
  | _+1, _+1 => ⟨nofun, nofun⟩

protected theorem mul_ne_zero_iff : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by rw [ne_eq, mul_eq_zero, not_or]

protected theorem mul_ne_zero : n ≠ 0 → m ≠ 0 → n * m ≠ 0 := (Nat.mul_ne_zero_iff.2 ⟨·,·⟩)

protected theorem ne_zero_of_mul_ne_zero_left (h : n * m ≠ 0) : n ≠ 0 :=
  (Nat.mul_ne_zero_iff.1 h).1

protected theorem mul_left_cancel {n m k : Nat} (np : 0 < n) (h : n * m = n * k) : m = k := by
  match Nat.lt_trichotomy m k with
  | Or.inl p =>
    have r : n * m < n * k := Nat.mul_lt_mul_of_pos_left p np
    simp [h] at r
  | Or.inr (Or.inl p) => exact p
  | Or.inr (Or.inr p) =>
    have r : n * k < n * m := Nat.mul_lt_mul_of_pos_left p np
    simp [h] at r

protected theorem mul_right_cancel {n m k : Nat} (mp : 0 < m) (h : n * m = k * m) : n = k := by
  simp [Nat.mul_comm _ m] at h
  apply Nat.mul_left_cancel mp h

protected theorem mul_left_cancel_iff {n: Nat} (p : 0 < n) (m k : Nat) : n * m = n * k ↔ m = k :=
  ⟨Nat.mul_left_cancel p, fun | rfl => rfl⟩

protected theorem mul_right_cancel_iff {m : Nat} (p : 0 < m) (n k : Nat) : n * m = k * m ↔ n = k :=
  ⟨Nat.mul_right_cancel p, fun | rfl => rfl⟩

protected theorem ne_zero_of_mul_ne_zero_right (h : n * m ≠ 0) : m ≠ 0 :=
  (Nat.mul_ne_zero_iff.1 h).2

protected theorem le_mul_of_pos_left (m) (h : 0 < n) : m ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.one_mul _).symm) (Nat.mul_le_mul_right _ h)

protected theorem le_mul_of_pos_right (n) (h : 0 < m) : n ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ h)

protected theorem mul_lt_mul_of_lt_of_le (hac : a < c) (hbd : b ≤ d) (hd : 0 < d) :
    a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hbd) (Nat.mul_lt_mul_of_pos_right hac hd)

protected theorem mul_lt_mul_of_lt_of_le' (hac : a < c) (hbd : b ≤ d) (hb : 0 < b) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_le hac hbd (Nat.lt_of_lt_of_le hb hbd)

protected theorem mul_lt_mul_of_le_of_lt (hac : a ≤ c) (hbd : b < d) (hc : 0 < c) :
    a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hac) (Nat.mul_lt_mul_of_pos_left hbd hc)

protected theorem mul_lt_mul_of_le_of_lt' (hac : a ≤ c) (hbd : b < d) (ha : 0 < a) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt hac hbd (Nat.lt_of_lt_of_le ha hac)

protected theorem mul_lt_mul_of_lt_of_lt {a b c d : Nat} (hac : a < c) (hbd : b < d) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hac) hbd (Nat.zero_lt_of_lt hac)

theorem succ_mul_succ (a b) : succ a * succ b = a * b + a + b + 1 := by
  rw [succ_mul, mul_succ]; rfl
theorem mul_le_add_right (m k n : Nat) : k * m ≤ m + n ↔ (k-1) * m ≤ n := by
  match k with
  | 0 =>
    simp
  | succ k =>
    simp [succ_mul, Nat.add_comm _ m, Nat.add_le_add_iff_left]

theorem succ_mul_succ_eq (a b : Nat) : succ a * succ b = a * b + a + b + 1 := by
  rw [mul_succ, succ_mul, Nat.add_right_comm _ a]; rfl

protected theorem mul_self_sub_mul_self_eq (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a,
    Nat.sub_add_eq, Nat.add_sub_cancel]

protected theorem pos_of_mul_pos_left {a b : Nat} (h : 0 < a * b) : 0 < b := by
  apply Decidable.by_contra
  intros
  simp_all

protected theorem pos_of_mul_pos_right {a b : Nat} (h : 0 < a * b) : 0 < a := by
  apply Decidable.by_contra
  intros
  simp_all

@[simp] protected theorem mul_pos_iff_of_pos_left {a b : Nat} (h : 0 < a) :
    0 < a * b ↔ 0 < b :=
  ⟨Nat.pos_of_mul_pos_left, Nat.mul_pos h⟩

@[simp] protected theorem mul_pos_iff_of_pos_right {a b : Nat} (h : 0 < b) :
    0 < a * b ↔ 0 < a :=
  ⟨Nat.pos_of_mul_pos_right, fun w => Nat.mul_pos w h⟩

/-! ### div/mod -/

protected theorem div_le_of_le_mul {m n : Nat} : ∀ {k}, m ≤ k * n → m / k ≤ n
  | 0, _ => by simp [Nat.div_zero, n.zero_le]
  | succ k, h => by
    suffices succ k * (m / succ k) ≤ succ k * n from
      Nat.le_of_mul_le_mul_left this (zero_lt_succ _)
    have h1 : succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) := Nat.le_add_left _ _
    have h2 : m % succ k + succ k * (m / succ k) = m := by rw [mod_add_div]
    have h3 : m ≤ succ k * n := h
    rw [← h2] at h3
    exact Nat.le_trans h1 h3

@[simp] theorem mul_div_right (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]

@[simp] theorem mul_div_left (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [Nat.mul_comm, mul_div_right _ H]

protected theorem div_self (H : 0 < n) : n / n = 1 := by
  let t := add_div_right 0 H
  rwa [Nat.zero_add, Nat.zero_div] at t

protected theorem mul_div_cancel (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  let t := add_mul_div_right 0 m H
  rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t

protected theorem mul_div_cancel_left (m : Nat) {n : Nat} (H : 0 < n) : n * m / n = m :=
by rw [Nat.mul_comm, Nat.mul_div_cancel _ H]

protected theorem div_eq_of_eq_mul_left (H1 : 0 < n) (H2 : m = k * n) : m / n = k :=
by rw [H2, Nat.mul_div_cancel _ H1]

protected theorem div_eq_of_eq_mul_right (H1 : 0 < n) (H2 : m = n * k) : m / n = k :=
by rw [H2, Nat.mul_div_cancel_left _ H1]

protected theorem div_div_eq_div_mul (m n k : Nat) : m / n / k = m / (n * k) := by
  cases eq_zero_or_pos k with
  | inl k0 => rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero] | inr kpos => ?_
  cases eq_zero_or_pos n with
  | inl n0 => rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div] | inr npos => ?_
  apply Nat.le_antisymm
  · apply (le_div_iff_mul_le (Nat.mul_pos npos kpos)).2
    rw [Nat.mul_comm n k, ← Nat.mul_assoc]
    apply (le_div_iff_mul_le npos).1
    apply (le_div_iff_mul_le kpos).1
    (apply Nat.le_refl)
  · apply (le_div_iff_mul_le kpos).2
    apply (le_div_iff_mul_le npos).2
    rw [Nat.mul_assoc, Nat.mul_comm n k]
    apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
    apply Nat.le_refl

protected theorem mul_div_mul_left {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]

protected theorem mul_div_mul_right {m : Nat} (n k : Nat) (H : 0 < m) :
    n * m / (k * m) = n / k := by rw [Nat.mul_comm, Nat.mul_comm k, Nat.mul_div_mul_left _ _ H]

theorem mul_div_le (m n : Nat) : n * (m / n) ≤ m := by
  match n, Nat.eq_zero_or_pos n with
  | _, Or.inl rfl => rw [Nat.zero_mul]; exact m.zero_le
  | n, Or.inr h => rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le h]; exact Nat.le_refl _

theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by decide) with
  | 0, _ => .inl rfl
  | 1, _ => .inr rfl

theorem le_of_mod_lt {a b : Nat} (h : a % b < a) : b ≤ a :=
  Nat.not_lt.1 fun hf => (ne_of_lt h).elim (Nat.mod_eq_of_lt hf)

theorem mul_mod_mul_right (z x y : Nat) : (x * z) % (y * z) = (x % y) * z := by
  rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z]; apply mul_mod_mul_left

@[simp] theorem mod_mod_of_dvd (a : Nat) (h : c ∣ b) : a % b % c = a % c := by
  rw (config := {occs := .pos [2]}) [← mod_add_div a b]
  have ⟨x, h⟩ := h
  subst h
  rw [Nat.mul_assoc, add_mul_mod_self_left]

theorem sub_mul_mod {x k n : Nat} (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  match k with
  | 0 => rw [Nat.mul_zero, Nat.sub_zero]
  | succ k =>
    have h₂ : n * k ≤ x := Nat.le_trans (le_add_right _ n) h₁
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_add_right (b := n * k)
      rw [Nat.sub_add_cancel h₂]
      simp [mul_succ, Nat.add_comm] at h₁; simp [h₁]
    rw [mul_succ, ← Nat.sub_sub, ← mod_eq_sub_mod h₄, sub_mul_mod h₂]

@[simp] theorem mod_mod (a n : Nat) : (a % n) % n = a % n :=
  match eq_zero_or_pos n with
  | .inl n0 => by simp [n0, mod_zero]
  | .inr npos => Nat.mod_eq_of_lt (mod_lt _ npos)

theorem mul_mod (a b n : Nat) : a * b % n = (a % n) * (b % n) % n := by
  rw (config := {occs := .pos [1]}) [← mod_add_div a n]
  rw (config := {occs := .pos [1]}) [← mod_add_div b n]
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add n, add_mul_mod_self_left,
    Nat.mul_comm _ (n * (b / n)), Nat.mul_assoc, add_mul_mod_self_left]

@[simp] theorem mod_add_mod (m n k : Nat) : (m % n + k) % n = (m + k) % n := by
  have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm
  rwa [Nat.add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : Nat) : (m + n % k) % k = (m + n) % k := by
  rw [Nat.add_comm, mod_add_mod, Nat.add_comm]

theorem add_mod (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  rw [add_mod_mod, mod_add_mod]

/-! ### pow -/

theorem pow_succ' {m n : Nat} : m ^ n.succ = m * m ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

@[simp] theorem pow_eq {m n : Nat} : m.pow n = m ^ n := rfl

theorem shiftLeft_eq (a b : Nat) : a <<< b = a * 2 ^ b :=
  match b with
  | 0 => (Nat.mul_one _).symm
  | b+1 => (shiftLeft_eq _ b).trans <| by
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem one_shiftLeft (n : Nat) : 1 <<< n = 2 ^ n := by rw [shiftLeft_eq, Nat.one_mul]

attribute [simp] Nat.pow_zero

protected theorem zero_pow {n : Nat} (H : 0 < n) : 0 ^ n = 0 := by
  match n with
  | 0 => contradiction
  | n+1 => rw [Nat.pow_succ, Nat.mul_zero]

@[simp] protected theorem one_pow (n : Nat) : 1 ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.pow_succ, Nat.mul_one, ih]

@[simp] protected theorem pow_one (a : Nat) : a ^ 1 = a := by
  rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

protected theorem pow_two (a : Nat) : a ^ 2 = a * a := by rw [Nat.pow_succ, Nat.pow_one]

protected theorem pow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

protected theorem pow_add' (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← Nat.pow_add, Nat.add_comm]

protected theorem pow_mul (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ _ ih => rw [Nat.mul_succ, Nat.pow_add, Nat.pow_succ, ih]

protected theorem pow_mul' (a m n : Nat) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [← Nat.pow_mul, Nat.mul_comm]

protected theorem pow_right_comm (a m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← Nat.pow_mul, Nat.pow_mul']

protected theorem mul_pow (a b n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.mul_mul_mul_comm, ih]

protected abbrev pow_le_pow_left := @pow_le_pow_of_le_left
protected abbrev pow_le_pow_right := @pow_le_pow_of_le_right

protected theorem one_lt_two_pow (h : n ≠ 0) : 1 < 2 ^ n :=
  match n, h with
  | n+1, _ => by
    rw [Nat.pow_succ', ← Nat.one_mul 1]
    exact Nat.mul_lt_mul_of_lt_of_le' (by decide) (Nat.two_pow_pos n) (by decide)

@[simp] protected theorem one_lt_two_pow_iff : 1 < 2 ^ n ↔ n ≠ 0 :=
  ⟨(by intro h p; subst p; simp at h), Nat.one_lt_two_pow⟩

protected theorem one_le_two_pow : 1 ≤ 2 ^ n :=
  if h : n = 0 then
    by subst h; simp
  else
    Nat.le_of_lt (Nat.one_lt_two_pow h)

protected theorem pow_pos (h : 0 < a) : 0 < a^n :=
  match n with
  | 0 => Nat.zero_lt_one
  | _ + 1 => Nat.mul_pos (Nat.pow_pos h) h

protected theorem pow_lt_pow_succ (h : 1 < a) : a ^ n < a ^ (n + 1) := by
  rw [← Nat.mul_one (a^n), Nat.pow_succ]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) h (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h))

protected theorem pow_lt_pow_of_lt {a n m : Nat} (h : 1 < a) (w : n < m) : a ^ n < a ^ m := by
  have := Nat.exists_eq_add_of_lt w
  cases this
  case intro k p =>
  rw [Nat.add_right_comm] at p
  subst p
  rw [Nat.pow_add, ← Nat.mul_one (a^n)]
  have t : 0 < a ^ k := Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h)
  exact Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_succ h) t t

protected theorem pow_le_pow_of_le {a n m : Nat} (h : 1 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  cases Nat.lt_or_eq_of_le w
  case inl lt =>
    exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)
  case inr eq =>
    subst eq
    exact Nat.le_refl _

protected theorem pow_le_pow_iff_right {a n m : Nat} (h : 1 < a) :
    a ^ n ≤ a ^ m ↔ n ≤ m := by
  constructor
  · apply Decidable.by_contra
    intros w
    simp [Decidable.not_imp_iff_and_not] at w
    apply Nat.lt_irrefl (a ^ n)
    exact Nat.lt_of_le_of_lt w.1 (Nat.pow_lt_pow_of_lt h w.2)
  · intro w
    cases Nat.eq_or_lt_of_le w
    case inl eq => subst eq; apply Nat.le_refl
    case inr lt => exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)

protected theorem pow_lt_pow_iff_right {a n m : Nat} (h : 1 < a) :
    a ^ n < a ^ m ↔ n < m := by
  constructor
  · apply Decidable.by_contra
    intros w
    simp at w
    apply Nat.lt_irrefl (a ^ n)
    exact Nat.lt_of_lt_of_le w.1 (Nat.pow_le_pow_of_le h w.2)
  · intro w
    exact Nat.pow_lt_pow_of_lt h w

/-! ### log2 -/

theorem le_log2 (h : n ≠ 0) : k ≤ n.log2 ↔ 2 ^ k ≤ n := by
  match k with
  | 0 => simp [show 1 ≤ n from Nat.pos_of_ne_zero h]
  | k+1 =>
    rw [log2]; split
    · have n0 : 0 < n / 2 := (Nat.le_div_iff_mul_le (by decide)).2 ‹_›
      simp only [Nat.add_le_add_iff_right, le_log2 (Nat.ne_of_gt n0), le_div_iff_mul_le,
        Nat.pow_succ]
      exact Nat.le_div_iff_mul_le (by decide)
    · simp only [le_zero_eq, succ_ne_zero, false_iff]
      refine mt (Nat.le_trans ?_) ‹_›
      exact Nat.pow_le_pow_of_le_right Nat.zero_lt_two (Nat.le_add_left 1 k)

theorem log2_lt (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
  rw [← Nat.not_le, ← Nat.not_le, le_log2 h]

theorem log2_self_le (h : n ≠ 0) : 2 ^ n.log2 ≤ n := (le_log2 h).1 (Nat.le_refl _)

theorem lt_log2_self : n < 2 ^ (n.log2 + 1) :=
  match n with
  | 0 => Nat.zero_lt_two
  | n+1 => (log2_lt n.succ_ne_zero).1 (Nat.le_refl _)

/-! ### dvd -/

theorem dvd_sub {k m n : Nat} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
  (Nat.dvd_add_iff_left h₂).2 <| by rwa [Nat.sub_add_cancel H]

protected theorem mul_dvd_mul {a b c d : Nat} : a ∣ b → c ∣ d → a * c ∣ b * d
  | ⟨e, he⟩, ⟨f, hf⟩ =>
    ⟨e * f, by simp [he, hf, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩

protected theorem mul_dvd_mul_left (a : Nat) (h : b ∣ c) : a * b ∣ a * c :=
  Nat.mul_dvd_mul (Nat.dvd_refl a) h

protected theorem mul_dvd_mul_right (h: a ∣ b) (c : Nat) : a * c ∣ b * c :=
  Nat.mul_dvd_mul h (Nat.dvd_refl c)

@[simp] theorem dvd_one {n : Nat} : n ∣ 1 ↔ n = 1 :=
  ⟨eq_one_of_dvd_one, fun h => h.symm ▸ Nat.dvd_refl _⟩

protected theorem mul_div_assoc (m : Nat) (H : k ∣ n) : m * n / k = m * (n / k) := by
  match Nat.eq_zero_or_pos k with
  | .inl h0 => rw [h0, Nat.div_zero, Nat.div_zero, Nat.mul_zero]
  | .inr hpos =>
    have h1 : m * n / k = m * (n / k * k) / k := by rw [Nat.div_mul_cancel H]
    rw [h1, ← Nat.mul_assoc, Nat.mul_div_cancel _ hpos]

protected theorem dvd_of_mul_dvd_mul_left
    (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n := by
  let ⟨l, H⟩ := H
  rw [Nat.mul_assoc] at H
  exact ⟨_, Nat.eq_of_mul_eq_mul_left kpos H⟩

protected theorem dvd_of_mul_dvd_mul_right (kpos : 0 < k) (H : m * k ∣ n * k) : m ∣ n := by
  rw [Nat.mul_comm m k, Nat.mul_comm n k] at H; exact Nat.dvd_of_mul_dvd_mul_left kpos H

theorem pow_dvd_pow_iff_pow_le_pow {k l : Nat} :
    ∀ {x : Nat}, 0 < x → (x ^ k ∣ x ^ l ↔ x ^ k ≤ x ^ l)
  | x + 1, w => by
    constructor
    · intro a
      exact le_of_dvd (Nat.pow_pos (succ_pos x)) a
    · intro a
      cases x
      case zero => simp
      case succ x =>
        have le :=
          (Nat.pow_le_pow_iff_right (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))).mp a
        refine ⟨(x + 2) ^ (l - k), ?_⟩
        rw [← Nat.pow_add, Nat.add_comm k, Nat.sub_add_cancel le]

/-- If `1 < x`, then `x^k` divides `x^l` if and only if `k` is at most `l`. -/
theorem pow_dvd_pow_iff_le_right {x k l : Nat} (w : 1 < x) : x ^ k ∣ x ^ l ↔ k ≤ l := by
  rw [pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w), Nat.pow_le_pow_iff_right w]

theorem pow_dvd_pow_iff_le_right' {b k l : Nat} : (b + 2) ^ k ∣ (b + 2) ^ l ↔ k ≤ l :=
  pow_dvd_pow_iff_le_right (Nat.lt_of_sub_eq_succ rfl)

protected theorem eq_mul_of_div_eq_right {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) :
    a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]

protected theorem div_eq_iff_eq_mul_right {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = b * c :=
  ⟨Nat.eq_mul_of_div_eq_right H', Nat.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = c * b := by
  rw [Nat.mul_comm]; exact Nat.div_eq_iff_eq_mul_right H H'

protected theorem pow_dvd_pow {m n : Nat} (a : Nat) (h : m ≤ n) : a ^ m ∣ a ^ n := by
  cases Nat.exists_eq_add_of_le h
  case intro k p =>
    subst p
    rw [Nat.pow_add]
    apply Nat.dvd_mul_right

protected theorem pow_sub_mul_pow (a : Nat) {m n : Nat} (h : m ≤ n) :
    a ^ (n - m) * a ^ m = a ^ n := by
  rw [← Nat.pow_add, Nat.sub_add_cancel h]

theorem pow_dvd_of_le_of_pow_dvd {p m n k : Nat} (hmn : m ≤ n) (hdiv : p ^ n ∣ k) : p ^ m ∣ k :=
  Nat.dvd_trans (Nat.pow_dvd_pow _ hmn) hdiv

theorem dvd_of_pow_dvd {p k m : Nat} (hk : 1 ≤ k) (hpk : p ^ k ∣ m) : p ∣ m := by
  rw [← Nat.pow_one p]; exact pow_dvd_of_le_of_pow_dvd hk hpk

protected theorem pow_div {x m n : Nat} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) := by
  rw [Nat.div_eq_iff_eq_mul_left (Nat.pow_pos hx) (Nat.pow_dvd_pow _ h), Nat.pow_sub_mul_pow _ h]

/-! ### shiftLeft and shiftRight -/

@[simp] theorem shiftLeft_zero : n <<< 0 = n := rfl

/-- Shiftleft on successor with multiple moved inside. -/
theorem shiftLeft_succ_inside (m n : Nat) : m <<< (n+1) = (2*m) <<< n := rfl

/-- Shiftleft on successor with multiple moved to outside. -/
theorem shiftLeft_succ : ∀(m n), m <<< (n + 1) = 2 * (m <<< n)
| m, 0 => rfl
| m, k + 1 => by
  rw [shiftLeft_succ_inside _ (k+1)]
  rw [shiftLeft_succ _ k, shiftLeft_succ_inside]

@[simp] theorem shiftRight_zero : n >>> 0 = n := rfl

theorem shiftRight_succ (m n) : m >>> (n + 1) = (m >>> n) / 2 := rfl

/-- Shiftright on successor with division moved inside. -/
theorem shiftRight_succ_inside : ∀m n, m >>> (n+1) = (m/2) >>> n
| m, 0 => rfl
| m, k + 1 => by
  rw [shiftRight_succ _ (k+1)]
  rw [shiftRight_succ_inside _ k, shiftRight_succ]

@[simp] theorem zero_shiftLeft : ∀ n, 0 <<< n = 0
  | 0 => by simp [shiftLeft]
  | n + 1 => by simp [shiftLeft, zero_shiftLeft n, shiftLeft_succ]

@[simp] theorem zero_shiftRight : ∀ n, 0 >>> n = 0
  | 0 => by simp [shiftRight]
  | n + 1 => by simp [shiftRight, zero_shiftRight n, shiftRight_succ]

theorem shiftRight_add (m n : Nat) : ∀ k, m >>> (n + k) = (m >>> n) >>> k
  | 0 => rfl
  | k + 1 => by simp [add_succ, shiftRight_add, shiftRight_succ]

theorem shiftLeft_shiftLeft (m n : Nat) : ∀ k, (m <<< n) <<< k = m <<< (n + k)
  | 0 => rfl
  | k + 1 => by simp [add_succ, shiftLeft_shiftLeft _ _ k, shiftLeft_succ]

theorem shiftRight_eq_div_pow (m : Nat) : ∀ n, m >>> n = m / 2 ^ n
  | 0 => (Nat.div_one _).symm
  | k + 1 => by
    rw [shiftRight_add, shiftRight_eq_div_pow m k]
    simp [Nat.div_div_eq_div_mul, ← Nat.pow_succ, shiftRight_succ]

theorem mul_add_div {m : Nat} (m_pos : m > 0) (x y : Nat) : (m * x + y) / m = x + y / m := by
  match x with
  | 0 => simp
  | x + 1 =>
    rw [Nat.mul_succ, Nat.add_assoc _ m, mul_add_div m_pos x (m+y), div_eq]
    simp_arith [m_pos]; rw [Nat.add_comm, Nat.add_sub_cancel]

theorem mul_add_mod (m x y : Nat) : (m * x + y) % m = y % m := by
  match x with
  | 0 => simp
  | x + 1 =>
    simp [Nat.mul_succ, Nat.add_assoc _ m, mul_add_mod _ x]

@[simp] theorem mod_div_self (m n : Nat) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
  · case succ n => exact Nat.div_eq_of_lt (m.mod_lt n.succ_pos)

/-! ### Decidability of predicates -/

instance decidableBallLT :
  ∀ (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h)
| 0, _, _ => isTrue fun _ => (by cases ·)
| n + 1, P, H =>
  match decidableBallLT n (P · <| lt_succ_of_lt ·) with
  | isFalse h => isFalse (h fun _ _ => · _ _)
  | isTrue h =>
    match H n Nat.le.refl with
    | isFalse p => isFalse (p <| · _ _)
    | isTrue p => isTrue fun _ h' => (Nat.lt_succ_iff_lt_or_eq.1 h').elim (h _) fun hn => hn ▸ p

instance decidableForallFin (P : Fin n → Prop) [DecidablePred P] : Decidable (∀ i, P i) :=
  decidable_of_iff (∀ k h, P ⟨k, h⟩) ⟨fun m ⟨k, h⟩ => m k h, fun m k h => m ⟨k, h⟩⟩

instance decidableBallLE (n : Nat) (P : ∀ k, k ≤ n → Prop) [∀ n h, Decidable (P n h)] :
    Decidable (∀ n h, P n h) :=
  decidable_of_iff (∀ (k) (h : k < succ n), P k (le_of_lt_succ h))
    ⟨fun m k h => m k (lt_succ_of_le h), fun m k _ => m k _⟩

instance decidableExistsLT [h : DecidablePred p] : DecidablePred fun n => ∃ m : Nat, m < n ∧ p m
  | 0 => isFalse (by simp only [not_lt_zero, false_and, exists_const, not_false_eq_true])
  | n + 1 =>
    @decidable_of_decidable_of_iff _ _ (@instDecidableOr _ _ (decidableExistsLT (p := p) n) (h n))
      (by simp only [Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or, exists_eq_left])

instance decidableExistsLE [DecidablePred p] : DecidablePred fun n => ∃ m : Nat, m ≤ n ∧ p m :=
  fun n => decidable_of_iff (∃ m, m < n + 1 ∧ p m)
    (exists_congr fun _ => and_congr_left' Nat.lt_succ_iff)
