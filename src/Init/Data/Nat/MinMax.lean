/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.ByCases

namespace Nat

/-! # min lemmas -/

protected theorem min_eq_min (a : Nat) : Nat.min a b = min a b := rfl

protected theorem min_comm (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
instance : Std.Commutative (α := Nat) min := ⟨Nat.min_comm⟩

protected theorem min_le_right (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]
protected theorem min_le_left (a b : Nat) : min a b ≤ a :=
  Nat.min_comm .. ▸ Nat.min_le_right ..

protected theorem min_eq_left {a b : Nat} (h : a ≤ b) : min a b = a := if_pos h
protected theorem min_eq_right {a b : Nat} (h : b ≤ a) : min a b = b :=
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

protected theorem max_comm (a b : Nat) : max a b = max b a := by
  simp only [Nat.max_def]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₂ h₁
  · cases not_or_intro h₁ h₂ <| Nat.le_total ..
instance : Std.Commutative (α := Nat) max := ⟨Nat.max_comm⟩

protected theorem le_max_left ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]
protected theorem le_max_right (a b : Nat) : b ≤ max a b :=
   Nat.max_comm .. ▸ Nat.le_max_left ..

end Nat
