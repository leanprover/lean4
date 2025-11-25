/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

prelude
public import Init.ByCases

public section

namespace Nat

/-! # min lemmas -/

protected theorem min_eq_min (a : Nat) : Nat.min a b = min a b := rfl

@[simp] protected theorem zero_min (a : Nat) : min 0 a = 0 := by
  simp [Nat.min_def]

@[simp] protected theorem min_zero (a : Nat) : min a 0 = 0 := by
  simp [Nat.min_def]

@[simp] protected theorem add_min_add_right (a b c : Nat) : min (a + c) (b + c) = min a b + c := by
  rw [Nat.min_def, Nat.min_def]
  simp only [Nat.add_le_add_iff_right]
  split <;> simp

@[simp] protected theorem add_min_add_left (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  rw [Nat.min_def, Nat.min_def]
  simp only [Nat.add_le_add_iff_left]
  split <;> simp

@[simp] protected theorem mul_min_mul_right (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  by_cases h : 0 < c
  · rw [Nat.min_def, Nat.min_def]
    simp only [Nat.mul_le_mul_right_iff h]
    split <;> simp
  · replace h : c = 0 := by exact Nat.eq_zero_of_not_pos h
    subst h
    simp

@[simp] protected theorem mul_min_mul_left (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  rw [Nat.mul_comm a, Nat.mul_comm a, Nat.mul_min_mul_right, Nat.mul_comm]

protected theorem min_comm (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
instance : Std.Commutative (α := Nat) min := ⟨Nat.min_comm⟩

protected theorem min_le_right (a b : Nat) : min a b ≤ b := by
  by_cases (a ≤ b) <;> simp [Nat.min_def, *]
protected theorem min_le_left (a b : Nat) : min a b ≤ a :=
  Nat.min_comm .. ▸ Nat.min_le_right ..

@[simp] protected theorem min_eq_left {a b : Nat} (h : a ≤ b) : min a b = a := if_pos h
@[simp] protected theorem min_eq_right {a b : Nat} (h : b ≤ a) : min a b = b :=
  Nat.min_comm .. ▸ Nat.min_eq_left h

protected theorem le_min_of_le_of_le {a b c : Nat} : a ≤ b → a ≤ c → a ≤ min b c := by
  intros; cases Nat.le_total b c with
  | inl h => rw [Nat.min_eq_left h]; assumption
  | inr h => rw [Nat.min_eq_right h]; assumption

protected theorem le_min {a b c : Nat} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c :=
  ⟨fun h => ⟨Nat.le_trans h (Nat.min_le_left ..), Nat.le_trans h (Nat.min_le_right ..)⟩,
   fun ⟨h₁, h₂⟩ => Nat.le_min_of_le_of_le h₁ h₂⟩

protected theorem lt_min {a b c : Nat} : a < min b c ↔ a < b ∧ a < c := Nat.le_min

/-! # max lemmas -/

protected theorem max_eq_max (a : Nat) : Nat.max a b = max a b := rfl

@[simp] protected theorem zero_max (a : Nat) : max 0 a = a := by
  simp [Nat.max_def]

@[simp] protected theorem max_zero (a : Nat) : max a 0 = a := by
  simp +contextual [Nat.max_def]

@[simp] protected theorem add_max_add_right (a b c : Nat) : max (a + c) (b + c) = max a b + c := by
  rw [Nat.max_def, Nat.max_def]
  simp only [Nat.add_le_add_iff_right]
  split <;> simp

@[simp] protected theorem add_max_add_left (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  rw [Nat.max_def, Nat.max_def]
  simp only [Nat.add_le_add_iff_left]
  split <;> simp

@[simp] protected theorem mul_max_mul_right (a b c : Nat) : max (a * c) (b * c) = max a b * c := by
  by_cases h : 0 < c
  · rw [Nat.max_def, Nat.max_def]
    simp only [Nat.mul_le_mul_right_iff h]
    split <;> simp
  · replace h : c = 0 := by exact Nat.eq_zero_of_not_pos h
    subst h
    simp

@[simp] protected theorem mul_max_mul_left (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  rw [Nat.mul_comm a, Nat.mul_comm a, Nat.mul_max_mul_right, Nat.mul_comm]

protected theorem max_comm (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..
instance : Std.Commutative (α := Nat) max := ⟨Nat.max_comm⟩

protected theorem le_max_left (a b : Nat) : a ≤ max a b := by
  by_cases (a ≤ b) <;> simp [Nat.max_def, *]
protected theorem le_max_right (a b : Nat) : b ≤ max a b :=
   Nat.max_comm .. ▸ Nat.le_max_left ..

@[simp] protected theorem max_eq_right {a b : Nat} (h : a ≤ b) : max a b = b := if_pos h

@[simp] protected theorem max_eq_left {a b : Nat} (h : b ≤ a) : max a b = a :=
  Nat.max_comm .. ▸ Nat.max_eq_right h

protected theorem max_le_of_le_of_le {a b c : Nat} : a ≤ c → b ≤ c → max a b ≤ c := by
  intros; cases Nat.le_total a b with
  | inl h => rw [Nat.max_eq_right h]; assumption
  | inr h => rw [Nat.max_eq_left h]; assumption

protected theorem max_le {a b c : Nat} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨Nat.le_trans (Nat.le_max_left ..) h, Nat.le_trans (Nat.le_max_right ..) h⟩,
   fun ⟨h₁, h₂⟩ => Nat.max_le_of_le_of_le h₁ h₂⟩

protected theorem max_lt {a b c : Nat} : max a b < c ↔ a < c ∧ b < c :=
  match c with
  | 0 => by simp
  | c + 1 => by simpa [Nat.lt_add_one_iff] using Nat.max_le

end Nat
