/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega

/-! # Basic lemmas about natural numbers

The primary purpose of the lemmas in this file is to assist with reasoning
about sizes of objects, array indices and such.

This file was upstreamed from Std,
and later these lemmas should be organised into other files more systematically.
-/

namespace Nat

@[deprecated and_forall_add_one (since := "2024-07-30")] abbrev and_forall_succ := @and_forall_add_one
@[deprecated or_exists_add_one (since := "2024-07-30")] abbrev or_exists_succ := @or_exists_add_one

@[simp] theorem exists_ne_zero {P : Nat → Prop} : (∃ n, ¬ n = 0 ∧ P n) ↔ ∃ n, P (n + 1) :=
  ⟨fun ⟨n, h, w⟩ => by cases n with | zero => simp at h | succ n => exact ⟨n, w⟩,
    fun ⟨n, w⟩ => ⟨n + 1, by simp, w⟩⟩

@[simp] theorem exists_eq_add_one : (∃ n, a = n + 1) ↔ 0 < a :=
  ⟨fun ⟨n, h⟩ => by omega, fun h => ⟨a - 1, by omega⟩⟩
@[simp] theorem exists_add_one_eq : (∃ n, n + 1 = a) ↔ 0 < a :=
  ⟨fun ⟨n, h⟩ => by omega, fun h => ⟨a - 1, by omega⟩⟩

/-- Dependent variant of `forall_lt_succ_right`. -/
theorem forall_lt_succ_right' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∀ m (h : m < n + 1), p m h) ↔ (∀ m (h : m < n), p m (by omega)) ∧ p n (by omega) := by
  simp only [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq]
  constructor
  · intro w
    constructor
    · intro m h
      exact w _ (.inl h)
    · exact w _ (.inr rfl)
  · rintro w m (h|rfl)
    · exact w.1 _ h
    · exact w.2

/-- See `forall_lt_succ_right'` for a variant where `p` takes the bound as an argument. -/
theorem forall_lt_succ_right {p : Nat → Prop} :
    (∀ m, m < n + 1 → p m) ↔ (∀ m, m < n → p m) ∧ p n := by
  simpa using forall_lt_succ_right' (p := fun m _ => p m)

/-- Dependent variant of `forall_lt_succ_left`. -/
theorem forall_lt_succ_left' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∀ m (h : m < n + 1), p m h) ↔ p 0 (by omega) ∧ (∀ m (h : m < n), p (m + 1) (by omega)) := by
  constructor
  · intro w
    constructor
    · exact w 0 (by omega)
    · intro m h
      exact w (m + 1) (by omega)
  · rintro ⟨h₀, h₁⟩ m h
    cases m with
    | zero => exact h₀
    | succ m => exact h₁ m (by omega)

/-- See `forall_lt_succ_left'` for a variant where `p` takes the bound as an argument. -/
theorem forall_lt_succ_left {p : Nat → Prop} :
    (∀ m, m < n + 1 → p m) ↔ p 0 ∧ (∀ m, m < n → p (m + 1)) := by
  simpa using forall_lt_succ_left' (p := fun m _ => p m)

/-- Dependent variant of `exists_lt_succ_right`. -/
theorem exists_lt_succ_right' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∃ m, ∃ (h : m < n + 1), p m h) ↔ (∃ m, ∃ (h : m < n), p m (by omega)) ∨ p n (by omega) := by
  simp only [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq]
  constructor
  · rintro ⟨m, (h|rfl), w⟩
    · exact .inl ⟨m, h, w⟩
    · exact .inr w
  · rintro (⟨m, h, w⟩ | w)
    · exact ⟨m, by omega, w⟩
    · exact ⟨n, by omega, w⟩

/-- See `exists_lt_succ_right'` for a variant where `p` takes the bound as an argument. -/
theorem exists_lt_succ_right {p : Nat → Prop} :
    (∃ m, m < n + 1 ∧ p m) ↔ (∃ m, m < n ∧ p m) ∨ p n := by
  simpa using exists_lt_succ_right' (p := fun m _ => p m)

/-- Dependent variant of `exists_lt_succ_left`. -/
theorem exists_lt_succ_left' {p : (m : Nat) → (m < n + 1) → Prop} :
    (∃ m, ∃ (h : m < n + 1), p m h) ↔ p 0 (by omega) ∨ (∃ m, ∃ (h : m < n), p (m + 1) (by omega)) := by
  constructor
  · rintro ⟨_|m, h, w⟩
    · exact .inl w
    · exact .inr ⟨m, by omega, w⟩
  · rintro (w|⟨m, h, w⟩)
    · exact ⟨0, by omega, w⟩
    · exact ⟨m + 1, by omega, w⟩

/-- See `exists_lt_succ_left'` for a variant where `p` takes the bound as an argument. -/
theorem exists_lt_succ_left {p : Nat → Prop} :
    (∃ m, m < n + 1 ∧ p m) ↔ p 0 ∨ (∃ m, m < n ∧ p (m + 1)) := by
  simpa using exists_lt_succ_left' (p := fun m _ => p m)

/-! ## add -/

protected theorem add_add_add_comm (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm b]

theorem one_add (n) : 1 + n = succ n := Nat.add_comm ..

theorem succ_eq_one_add (n) : succ n = 1 + n := (one_add _).symm

theorem succ_add_eq_add_succ (a b) : succ a + b = a + succ b := Nat.succ_add ..

protected theorem eq_zero_of_add_eq_zero_right (h : n + m = 0) : n = 0 :=
  (Nat.eq_zero_of_add_eq_zero h).1

@[simp] protected theorem add_eq_zero_iff : n + m = 0 ↔ n = 0 ∧ m = 0 :=
  ⟨Nat.eq_zero_of_add_eq_zero, fun ⟨h₁, h₂⟩ => h₂.symm ▸ h₁⟩

@[simp] protected theorem add_left_cancel_iff {n : Nat} : n + m = n + k ↔ m = k :=
  ⟨Nat.add_left_cancel, fun | rfl => rfl⟩

@[simp] protected theorem add_right_cancel_iff {n : Nat} : m + n = k + n ↔ m = k :=
  ⟨Nat.add_right_cancel, fun | rfl => rfl⟩

@[simp] protected theorem add_left_eq_self  {a b : Nat} : a + b = b ↔ a = 0 := by omega
@[simp] protected theorem add_right_eq_self {a b : Nat} : a + b = a ↔ b = 0 := by omega
@[simp] protected theorem self_eq_add_right {a b : Nat} : a = a + b ↔ b = 0 := by omega
@[simp] protected theorem self_eq_add_left  {a b : Nat} : a = b + a ↔ b = 0 := by omega

@[simp] protected theorem add_le_add_iff_left {n : Nat} : n + m ≤ n + k ↔ m ≤ k :=
  ⟨Nat.le_of_add_le_add_left, fun h => Nat.add_le_add_left h _⟩

protected theorem lt_of_add_lt_add_right : ∀ {n : Nat}, k + n < m + n → k < m
  | 0, h => h
  | _+1, h => Nat.lt_of_add_lt_add_right (Nat.lt_of_succ_lt_succ h)

protected theorem lt_of_add_lt_add_left {n : Nat} : n + k < n + m → k < m := by
  rw [Nat.add_comm n, Nat.add_comm n]; exact Nat.lt_of_add_lt_add_right

@[simp] protected theorem add_lt_add_iff_left {k n m : Nat} : k + n < k + m ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_left, fun h => Nat.add_lt_add_left h _⟩

@[simp] protected theorem add_lt_add_iff_right {k n m : Nat} : n + k < m + k ↔ n < m :=
  ⟨Nat.lt_of_add_lt_add_right, fun h => Nat.add_lt_add_right h _⟩

protected theorem add_lt_add_of_le_of_lt {a b c d : Nat} (hle : a ≤ b) (hlt : c < d) :
    a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right hle _) (Nat.add_lt_add_left hlt _)

protected theorem add_lt_add_of_lt_of_le {a b c d : Nat} (hlt : a < b) (hle : c ≤ d) :
    a + c < b + d :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left hle _) (Nat.add_lt_add_right hlt _)

protected theorem pos_of_lt_add_right (h : n < n + k) : 0 < k :=
  Nat.lt_of_add_lt_add_left h

protected theorem pos_of_lt_add_left : n < k + n → 0 < k := by
  rw [Nat.add_comm]; exact Nat.pos_of_lt_add_right

@[simp] protected theorem lt_add_right_iff_pos : n < n + k ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_right, Nat.lt_add_of_pos_right⟩

@[simp] protected theorem lt_add_left_iff_pos : n < k + n ↔ 0 < k :=
  ⟨Nat.pos_of_lt_add_left, Nat.lt_add_of_pos_left⟩

protected theorem add_pos_left (h : 0 < m) (n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

protected theorem add_pos_right (m) (h : 0 < n) : 0 < m + n :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left ..)

protected theorem add_self_ne_one : ∀ n, n + n ≠ 1
  | n+1, h => by rw [Nat.succ_add, Nat.succ.injEq] at h; contradiction

theorem le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega

/-! ## sub -/

protected theorem sub_one (n) : n - 1 = pred n := rfl

protected theorem one_sub : ∀ n, 1 - n = if n = 0 then 1 else 0
  | 0 => rfl
  | _+1 => by rw [if_neg (Nat.succ_ne_zero _), Nat.succ_sub_succ, Nat.zero_sub]

theorem succ_sub_sub_succ (n m k) : succ n - m - succ k = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]

theorem add_sub_sub_add_right (n m k l : Nat) :
    (n + l) - m - (k + l) = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, ←Nat.add_assoc, Nat.add_sub_add_right]

protected theorem sub_right_comm (m n k : Nat) : m - n - k = m - k - n := by
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

protected theorem add_sub_cancel_right (n m : Nat) : (n + m) - m = n := Nat.add_sub_cancel ..

@[simp] protected theorem add_sub_cancel' {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm, Nat.sub_add_cancel h]

theorem succ_sub_one (n) : succ n - 1 = n := rfl

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

theorem add_lt_iff_lt_sub_right {a b c : Nat} : a + b < c ↔ a < c - b := by
  omega

protected theorem add_le_of_le_sub' {n k m : Nat} (h : m ≤ k) : n ≤ k - m → m + n ≤ k :=
  Nat.add_comm .. ▸ Nat.add_le_of_le_sub h

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

theorem sub_one_lt_of_le (h₀ : 0 < a) (h₁ : a ≤ b) : a - 1 < b :=
  Nat.lt_of_lt_of_le (Nat.pred_lt_of_lt h₀) h₁

theorem sub_lt_succ (a b) : a - b < succ a := lt_succ_of_le (sub_le a b)

theorem sub_lt_add_one (a b) : a - b < a + 1 := lt_add_one_of_le (sub_le a b)

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
instance : Std.IdempotentOp (α := Nat) min := ⟨Nat.min_self⟩

@[simp] protected theorem zero_min (a) : min 0 a = 0 := Nat.min_eq_left (Nat.zero_le _)

@[simp] protected theorem min_zero (a) : min a 0 = 0 := Nat.min_eq_right (Nat.zero_le _)

@[simp] protected theorem min_assoc : ∀ (a b c : Nat), min (min a b) c = min a (min b c)
  | 0, _, _ => by rw [Nat.zero_min, Nat.zero_min, Nat.zero_min]
  | _, 0, _ => by rw [Nat.zero_min, Nat.min_zero, Nat.zero_min]
  | _, _, 0 => by rw [Nat.min_zero, Nat.min_zero, Nat.min_zero]
  | _+1, _+1, _+1 => by simp only [Nat.succ_min_succ]; exact congrArg succ <| Nat.min_assoc ..
instance : Std.Associative (α := Nat) min := ⟨Nat.min_assoc⟩

@[simp] protected theorem min_self_assoc {m n : Nat} : min m (min m n) = min m n := by
  rw [← Nat.min_assoc, Nat.min_self]

@[simp] protected theorem min_self_assoc' {m n : Nat} : min n (min m n) = min n m := by
  rw [Nat.min_comm m n, ← Nat.min_assoc, Nat.min_self]

@[simp] theorem min_add_left {a b : Nat} : min a (b + a) = a := by
  rw [Nat.min_def]
  simp
@[simp] theorem min_add_right {a b : Nat} : min a (a + b) = a := by
  rw [Nat.min_def]
  simp
@[simp] theorem add_left_min {a b : Nat} : min (b + a) a = a := by
  rw [Nat.min_comm, min_add_left]
@[simp] theorem add_right_min {a b : Nat} : min (a + b) a = a := by
  rw [Nat.min_comm, min_add_right]

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
instance : Std.IdempotentOp (α := Nat) max := ⟨Nat.max_self⟩

@[simp] protected theorem zero_max (a) : max 0 a = a := Nat.max_eq_right (Nat.zero_le _)

@[simp] protected theorem max_zero (a) : max a 0 = a := Nat.max_eq_left (Nat.zero_le _)
instance : Std.LawfulIdentity (α := Nat) max 0 where
  left_id := Nat.zero_max
  right_id := Nat.max_zero

protected theorem max_assoc : ∀ (a b c : Nat), max (max a b) c = max a (max b c)
  | 0, _, _ => by rw [Nat.zero_max, Nat.zero_max]
  | _, 0, _ => by rw [Nat.zero_max, Nat.max_zero]
  | _, _, 0 => by rw [Nat.max_zero, Nat.max_zero]
  | _+1, _+1, _+1 => by simp only [Nat.succ_max_succ]; exact congrArg succ <| Nat.max_assoc ..
instance : Std.Associative (α := Nat) max := ⟨Nat.max_assoc⟩

@[simp] theorem max_add_left {a b : Nat} : max a (b + a) = b + a := by
  rw [Nat.max_def]
  simp
@[simp] theorem max_add_right {a b : Nat} : max a (a + b) = a + b := by
  rw [Nat.max_def]
  simp
@[simp] theorem add_left_max {a b : Nat} : max (b + a) a = b + a := by
  rw [Nat.max_comm, max_add_left]
@[simp] theorem add_right_max {a b : Nat} : max (a + b) a = a + b := by
  rw [Nat.max_comm, max_add_right]

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

protected theorem sub_min_sub_left (a b c : Nat) : min (a - b) (a - c) = a - max b c := by
  omega

protected theorem sub_max_sub_left (a b c : Nat) : max (a - b) (a - c) = a - min b c := by
  omega

protected theorem mul_max_mul_right (a b c : Nat) : max (a * c) (b * c) = max a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_max_add_right, ind]

protected theorem mul_min_mul_right (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_min_add_right, ind]

protected theorem mul_max_mul_left (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_max_mul_right ..

protected theorem mul_min_mul_left (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_min_mul_right ..

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

protected theorem mul_right_comm (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]

protected theorem mul_mul_mul_comm (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm b]

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

protected theorem mul_left_cancel_iff {n : Nat} (p : 0 < n) {m k : Nat} : n * m = n * k ↔ m = k :=
  ⟨Nat.mul_left_cancel p, fun | rfl => rfl⟩

protected theorem mul_right_cancel_iff {m : Nat} (p : 0 < m) {n k : Nat} : n * m = k * m ↔ n = k :=
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

theorem add_one_mul_add_one (a b : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 := by
  rw [add_one_mul, mul_add_one]; rfl

theorem mul_le_add_right {m k n : Nat} : k * m ≤ m + n ↔ (k-1) * m ≤ n := by
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

protected theorem pos_of_lt_mul_left {a b c : Nat} (h : a < b * c) : 0 < c := by
  replace h : 0 < b * c := by omega
  exact Nat.pos_of_mul_pos_left h

protected theorem pos_of_lt_mul_right {a b c : Nat} (h : a < b * c) : 0 < b := by
  replace h : 0 < b * c := by omega
  exact Nat.pos_of_mul_pos_right h

/-! ### div/mod -/

theorem mod_two_eq_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  match n % 2, @Nat.mod_lt n 2 (by decide) with
  | 0, _ => .inl rfl
  | 1, _ => .inr rfl

@[simp] theorem mod_two_bne_zero : ((a % 2) != 0) = (a % 2 == 1) := by
  cases mod_two_eq_zero_or_one a <;> simp_all
@[simp] theorem mod_two_bne_one : ((a % 2) != 1) = (a % 2 == 0) := by
  cases mod_two_eq_zero_or_one a <;> simp_all

theorem le_of_mod_lt {a b : Nat} (h : a % b < a) : b ≤ a :=
  Nat.not_lt.1 fun hf => (ne_of_lt h).elim (Nat.mod_eq_of_lt hf)

theorem mul_mod_mul_right (z x y : Nat) : (x * z) % (y * z) = (x % y) * z := by
  rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z]; apply mul_mod_mul_left

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
  rw (occs := [1]) [← mod_add_div a n]
  rw (occs := [1]) [← mod_add_div b n]
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

@[simp] theorem self_sub_mod (n k : Nat) [NeZero k] : (n - k) % n = n - k := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mod_eq_of_lt]
    cases k with
    | zero => simp_all
    | succ k => omega

@[simp] theorem mod_mul_mod {a b c : Nat} : (a % c * b) % c = a * b % c := by
  rw [mul_mod, mod_mod, ← mul_mod]

theorem mod_eq_sub (x w : Nat) : x % w = x - w * (x / w) := by
  conv => rhs; congr; rw [← mod_add_div x w]
  simp

/-! ### pow -/

theorem pow_succ' {m n : Nat} : m ^ n.succ = m * m ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem pow_add_one' {m n : Nat} : m ^ (n + 1) = m * m ^ n := by
  rw [Nat.pow_add_one, Nat.mul_comm]

@[simp] theorem pow_eq {m n : Nat} : m.pow n = m ^ n := rfl

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

@[simp] theorem one_mod_two_pow_eq_one : 1 % 2 ^ n = 1 ↔ 0 < n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mod_eq_of_lt (a := 1) (Nat.one_lt_two_pow (by omega))]
    simp

@[simp] theorem one_mod_two_pow (h : 0 < n) : 1 % 2 ^ n = 1 :=
  one_mod_two_pow_eq_one.mpr h

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

@[simp]
protected theorem pow_pred_mul {x w : Nat} (h : 0 < w) :
    x ^ (w - 1) * x = x ^ w := by
  simp [← Nat.pow_succ, succ_eq_add_one, Nat.sub_add_cancel h]

protected theorem pow_pred_lt_pow {x w : Nat} (h₁ : 1 < x) (h₂ : 0 < w) :
    x ^ (w - 1) < x ^ w :=
  Nat.pow_lt_pow_of_lt h₁ (by omega)

protected theorem two_pow_pred_lt_two_pow {w : Nat} (h : 0 < w) :
    2 ^ (w - 1) < 2 ^ w :=
  Nat.pow_pred_lt_pow (by omega) h

@[simp]
protected theorem two_pow_pred_add_two_pow_pred (h : 0 < w) :
    2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
  rw [← Nat.pow_pred_mul h]
  omega

@[simp]
protected theorem two_pow_sub_two_pow_pred (h : 0 < w) :
    2 ^ w - 2 ^ (w - 1) = 2 ^ (w - 1) := by
  simp [← Nat.two_pow_pred_add_two_pow_pred h]

@[simp]
protected theorem two_pow_pred_mod_two_pow (h : 0 < w) :
    2 ^ (w - 1) % 2 ^ w = 2 ^ (w - 1) := by
  rw [mod_eq_of_lt]
  apply Nat.pow_pred_lt_pow (by omega) h

protected theorem pow_lt_pow_iff_pow_mul_le_pow {a n m : Nat} (h : 1 < a) :
    a ^ n < a ^ m ↔ a ^ n * a ≤ a ^ m := by
  rw [←Nat.pow_add_one, Nat.pow_le_pow_iff_right (by omega), Nat.pow_lt_pow_iff_right (by omega)]
  omega

protected theorem lt_pow_self {n a : Nat} (h : 1 < a) : n < a ^ n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ _ ih => exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right ih 1) (Nat.pow_lt_pow_succ h)

protected theorem lt_two_pow_self : n < 2 ^ n :=
  Nat.lt_pow_self Nat.one_lt_two

@[simp]
protected theorem mod_two_pow_self : n % 2 ^ n = n :=
  Nat.mod_eq_of_lt Nat.lt_two_pow_self

@[simp]
theorem two_pow_pred_mul_two (h : 0 < w) :
    2 ^ (w - 1) * 2 = 2 ^ w := by
  simp [← Nat.pow_succ, Nat.sub_add_cancel h]

/-! ### log2 -/

@[simp]
theorem log2_zero : Nat.log2 0 = 0 := by
  simp [Nat.log2]

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
      exact Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_add_left 1 k)

theorem log2_lt (h : n ≠ 0) : n.log2 < k ↔ n < 2 ^ k := by
  rw [← Nat.not_le, ← Nat.not_le, le_log2 h]

@[simp]
theorem log2_two_pow : (2 ^ n).log2 = n := by
  apply Nat.eq_of_le_of_lt_succ <;> simp [le_log2, log2_lt, NeZero.ne, Nat.pow_lt_pow_iff_right]

theorem log2_self_le (h : n ≠ 0) : 2 ^ n.log2 ≤ n := (le_log2 h).1 (Nat.le_refl _)

theorem lt_log2_self : n < 2 ^ (n.log2 + 1) :=
  match n with
  | 0 => by simp
  | n+1 => (log2_lt n.succ_ne_zero).1 (Nat.le_refl _)

/-! ### dvd -/

protected theorem eq_mul_of_div_eq_right {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) :
    a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]

protected theorem div_eq_iff_eq_mul_right {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = b * c :=
  ⟨Nat.eq_mul_of_div_eq_right H', Nat.div_eq_of_eq_mul_right H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = c * b := by
  rw [Nat.mul_comm]; exact Nat.div_eq_iff_eq_mul_right H H'

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
| _, 0 => rfl
| _, k + 1 => by
  rw [shiftLeft_succ_inside _ (k+1)]
  rw [shiftLeft_succ _ k, shiftLeft_succ_inside]

/-- Shiftright on successor with division moved inside. -/
theorem shiftRight_succ_inside : ∀m n, m >>> (n+1) = (m/2) >>> n
| _, 0 => rfl
| _, k + 1 => by
  rw [shiftRight_succ _ (k+1)]
  rw [shiftRight_succ_inside _ k, shiftRight_succ]

@[simp] theorem zero_shiftLeft : ∀ n, 0 <<< n = 0
  | 0 => by simp [shiftLeft]
  | n + 1 => by simp [shiftLeft, zero_shiftLeft n, shiftLeft_succ]

@[simp] theorem zero_shiftRight : ∀ n, 0 >>> n = 0
  | 0 => by simp [shiftRight]
  | n + 1 => by simp [shiftRight, zero_shiftRight n, shiftRight_succ]

theorem shiftLeft_add (m n : Nat) : ∀ k, m <<< (n + k) = (m <<< n) <<< k
  | 0 => rfl
  | k + 1 => by simp [← Nat.add_assoc, shiftLeft_add _ _ k, shiftLeft_succ]

@[simp] theorem shiftLeft_shiftRight (x n : Nat) : x <<< n >>> n = x := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem mul_add_div {m : Nat} (m_pos : m > 0) (x y : Nat) : (m * x + y) / m = x + y / m := by
  match x with
  | 0 => simp
  | x + 1 =>
    rw [Nat.mul_succ, Nat.add_assoc _ m, mul_add_div m_pos x (m+y), div_eq]
    simp +arith [m_pos]; rw [Nat.add_comm, Nat.add_sub_cancel]

theorem mul_add_mod (m x y : Nat) : (m * x + y) % m = y % m := by
  match x with
  | 0 => simp
  | x + 1 =>
    simp [Nat.mul_succ, Nat.add_assoc _ m, mul_add_mod _ x]

@[simp] theorem mod_div_self (m n : Nat) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
  · case succ n => exact Nat.div_eq_of_lt (m.mod_lt n.succ_pos)

theorem mod_eq_iff {a b c : Nat} :
    a % b = c ↔ (b = 0 ∧ a = c) ∨ (c < b ∧ Exists fun k => a = b * k + c) :=
  ⟨fun h =>
    if w : b = 0 then
      .inl ⟨w, by simpa [w] using h⟩
    else
      .inr ⟨by subst h; exact Nat.mod_lt a (zero_lt_of_ne_zero w),
        a / b, by subst h; exact (div_add_mod a b).symm⟩,
   by
     rintro (⟨rfl, rfl⟩ | ⟨w, h, rfl⟩)
     · simp_all
     · rw [mul_add_mod, mod_eq_of_lt w]⟩

theorem succ_mod_succ_eq_zero_iff {a b : Nat} :
    (a + 1) % (b + 1) = 0 ↔ a % (b + 1) = b := by
  symm
  rw [mod_eq_iff, mod_eq_iff]
  simp only [add_one_ne_zero, false_and, Nat.lt_add_one, true_and, false_or, and_self, zero_lt_succ,
    Nat.add_zero]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k + 1, ?_⟩
    simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc]
  · rintro ⟨k, h⟩
    cases k with
    | zero => simp at h
    | succ k =>
      refine ⟨k, ?_⟩
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc,
        Nat.add_right_cancel_iff] at h
      subst h
      simp [Nat.add_mul]

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

/-- Dependent version of `decidableExistsLT`. -/
instance decidableExistsLT' {p : (m : Nat) → m < k → Prop} [I : ∀ m h, Decidable (p m h)] :
    Decidable (∃ m : Nat, ∃ h : m < k, p m h) :=
  match k, p, I with
  | 0, _, _ => isFalse (by simp)
  | (k + 1), p, I => @decidable_of_iff _ ((∃ m, ∃ h : m < k, p m (by omega)) ∨ p k (by omega))
      ⟨by rintro (⟨m, h, w⟩ | w); exact ⟨m, by omega, w⟩; exact ⟨k, by omega, w⟩,
        fun ⟨m, h, w⟩ => if h' : m < k then .inl ⟨m, h', w⟩ else
          by obtain rfl := (by omega : m = k); exact .inr w⟩
      (@instDecidableOr _ _
        (decidableExistsLT' (p := fun m h => p m (by omega)) (I := fun m h => I m (by omega)))
        inferInstance)

/-- Dependent version of `decidableExistsLE`. -/
instance decidableExistsLE' {p : (m : Nat) → m ≤ k → Prop} [I : ∀ m h, Decidable (p m h)] :
    Decidable (∃ m : Nat, ∃ h : m ≤ k, p m h) :=
  decidable_of_iff (∃ m, ∃ h : m < k + 1, p m (by omega)) (exists_congr fun _ =>
    ⟨fun ⟨h, w⟩ => ⟨le_of_lt_succ h, w⟩, fun ⟨h, w⟩ => ⟨lt_add_one_of_le h, w⟩⟩)

/-! ### Results about `List.sum` specialized to `Nat` -/

protected theorem sum_pos_iff_exists_pos {l : List Nat} : 0 < l.sum ↔ ∃ x ∈ l, 0 < x := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [← ih]
    omega
