/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Nat
import Init.Data.Int
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

theorem Int.emod_add_div (m k : Int) : m % k + k * (m / k) = m := by
  simp [Int.emod_def]

-- The following two somewhat obscure facts could probably be included as theorems.
-- However as a simp lemma it does not improve confluence:
-- it just creates more goals with iterated `%`.
theorem Nat.mod_self_mod_eq_zero_of_mod_dvd_right (a b : Nat) (h : a % b ∣ b) : a % (a % b) = 0 := by
  obtain ⟨k, h⟩ := h
  rw [Nat.mod_eq_zero_of_dvd]
  have p : a = a % b + b * (a / b) := (Nat.mod_add_div a b).symm
  replace p : a = a % b + (a % b * k) * (a / b) := by
    conv at p => rhs; rhs; lhs; rw [h]
    exact p
  replace p : a = (a % b) * (1 + k * (a / b)) := by
    conv at p => rhs; lhs; rw [← Nat.mul_one (a % b)]
    rwa [Nat.mul_assoc, ← Nat.mul_add] at p
  conv => rhs; rw [p]
  exact Nat.dvd_mul_right _ _

theorem Int.mod_self_mod_eq_zero_of_mod_dvd_right (a b : Int) (h : a % b ∣ b) : a % (a % b) = 0 := by
  obtain ⟨k, h⟩ := h
  rw [Int.emod_eq_zero_of_dvd]
  have p : a = a % b + b * (a / b) := (Int.emod_add_div a b).symm
  replace p : a = a % b + (a % b * k) * (a / b) := by
    conv at p => rhs; rhs; lhs; rw [h]
    exact p
  replace p : a = (a % b) * (1 + k * (a / b)) := by
    conv at p => rhs; lhs; rw [← Int.mul_one (a % b)]
    rwa [Int.mul_assoc, ← Int.mul_add] at p
  conv => rhs; rw [p]
  exact Int.dvd_mul_right _ _

simp_lc allow Nat.mod_self Nat.mod_mod_of_dvd
simp_lc allow Int.emod_self Int.emod_emod_of_dvd

-- Ugly corner case, let's just allow it.
example (n k : Int) : Prop := ∀ (_ : n % k + 1 ∣ k) (_ : 0 ≤ n % k), n % (n % k + 1) = n % k
simp_lc allow Int.emod_emod_of_dvd Int.emod_self_add_one

-- These could be added as simp lemmas, resolving the non-confluence between
-- `Int.mul_ediv_mul_of_pos_left` and `Int.mul_ediv_mul_of_pos`,
-- but they themselves cause further non-confluence.
theorem Int.ediv_self_of_pos (a : Int) (_ : 0 < a) : a / a = 1 := Int.ediv_self (by omega)
theorem Int.ediv_self_of_lt_zero (a : Int) (_ : a < 0) : a / a = 1 := Int.ediv_self (by omega)
simp_lc allow Int.mul_ediv_mul_of_pos_left Int.mul_ediv_mul_of_pos

/-!
The following theorems could be added a simp lemmas,
improving confluence and avoiding needing the three `allow` statements below,
however they have bad discrimination tree keys (`@Exists Nat <other>`) so we just allow it.
-/
theorem Nat.exists_ne {y : Nat} : ∃ x, x ≠ y := ⟨y + 1, by simp⟩

theorem Nat.exists_succ_eq_right (q : Nat → Prop) (a : Nat) :
    (∃ n, q (n + 1) ∧ n + 1 = a) ↔ a ≠ 0 ∧ q a :=
  ⟨by rintro ⟨n, h, rfl⟩; exact ⟨by simp, h⟩, by rintro ⟨h₁, h₂⟩; match a, h₁ with | a + 1, _ => exact ⟨a, h₂, rfl⟩⟩
theorem Nat.exists_eq_succ_right (q : Nat → Prop) (a : Nat) :
    (∃ n, q (n + 1) ∧ a = n + 1) ↔ a ≠ 0 ∧ q a := by
  simp [eq_comm (a := a), exists_succ_eq_right]
theorem Nat.exists_succ_eq_left (q : Nat → Prop) (a : Nat) :
    (∃ n, n + 1 = a ∧ q (n + 1)) ↔ a ≠ 0 ∧ q a := by
  simp [and_comm, exists_succ_eq_right]
theorem Nat.exists_eq_succ_left (q : Nat → Prop) (a : Nat) :
    (∃ n, n + 1 = a ∧ q (n + 1)) ↔ a ≠ 0 ∧ q a := by
  simp [and_comm, exists_succ_eq_right]

simp_lc allow exists_and_right Nat.exists_ne_zero
simp_lc allow exists_eq_right_right Nat.exists_ne_zero
simp_lc allow exists_eq_right_right' Nat.exists_ne_zero

-- An obscure interaction?
example (a b : Nat) (h : 2 ^ (a % b) ∣ b) : a % 2 ^ (a % b) = a % b := by
  have : a % b % 2 ^ (a % b) = a % b % 2 ^ (a % b) := rfl
  conv at this => lhs; rw [Nat.mod_mod_of_dvd _ h]
  conv at this => rhs; rw [Nat.mod_two_pow_self]
  exact this
simp_lc allow Nat.mod_mod_of_dvd Nat.mod_two_pow_self

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in _root_ Nat Int
