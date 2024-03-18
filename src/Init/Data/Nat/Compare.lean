/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Classical
import Init.Data.Ord

/-! # Basic lemmas about comparing natural numbers

This file introduce some basic lemmas about compare as applied to natural
numbers.
-/
namespace Nat

theorem compare_def_lt (a b : Nat) :
    compare a b = if a < b then .lt else if b < a then .gt else .eq := by
  simp only [compare, compareOfLessAndEq]
  split
  · rfl
  · next h =>
    match Nat.lt_or_eq_of_le (Nat.not_lt.1 h) with
    | .inl h => simp [h, Nat.ne_of_gt h]
    | .inr rfl => simp

theorem compare_def_le (a b : Nat) :
    compare a b = if a ≤ b then if b ≤ a then .eq else .lt else .gt := by
  rw [compare_def_lt]
  split
  · next hlt => simp [Nat.le_of_lt hlt, Nat.not_le.2 hlt]
  · next hge =>
    split
    · next hgt => simp [Nat.le_of_lt hgt, Nat.not_le.2 hgt]
    · next hle => simp [Nat.not_lt.1 hge, Nat.not_lt.1 hle]

protected theorem compare_swap (a b : Nat) : (compare a b).swap = compare b a := by
  simp only [compare_def_le]; (repeat' split) <;> try rfl
  next h1 h2 => cases h1 (Nat.le_of_not_le h2)

protected theorem compare_eq_eq {a b : Nat} : compare a b = .eq ↔ a = b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.ne_of_lt, Nat.ne_of_gt, *]
  next hlt hgt => exact Nat.le_antisymm (Nat.not_lt.1 hgt) (Nat.not_lt.1 hlt)

protected theorem compare_eq_lt {a b : Nat} : compare a b = .lt ↔ a < b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [*]

protected theorem compare_eq_gt {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]

protected theorem compare_ne_gt {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  rw [compare_def_le]; (repeat' split) <;> simp [*]

protected theorem compare_ne_lt {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  rw [compare_def_le]; (repeat' split) <;> simp [Nat.le_of_not_le, *]

end Nat
