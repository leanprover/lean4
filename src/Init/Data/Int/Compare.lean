/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Ord
import Init.Data.Int.Order

/-! # Basic lemmas about comparing integers

This file introduces some basic lemmas about `compare` as applied to integers.
-/
namespace Int

protected theorem lt_or_eq_of_le {n m : Int} (h : n ≤ m) : n < m ∨ n = m := by
  omega

protected theorem le_iff_lt_or_eq {n m : Int} : n ≤ m ↔ n < m ∨ n = m :=
  ⟨Int.lt_or_eq_of_le, fun | .inl h => Int.le_of_lt h | .inr rfl => Int.le_refl _⟩

theorem compare_def_lt (a b : Int) :
    compare a b = if a < b then .lt else if b < a then .gt else .eq := by
  simp only [compare, compareOfLessAndEq]
  split
  · rfl
  · next h =>
    match Int.lt_or_eq_of_le (Int.not_lt.1 h) with
    | .inl h => simp [h, Int.ne_of_gt h]
    | .inr rfl => simp

theorem compare_def_le (a b : Int) :
    compare a b = if a ≤ b then if b ≤ a then .eq else .lt else .gt := by
  rw [compare_def_lt]
  split
  · next hlt => simp [Int.le_of_lt hlt, Int.not_le.2 hlt]
  · next hge =>
    split
    · next hgt => simp [Int.le_of_lt hgt, Int.not_le.2 hgt]
    · next hle => simp [Int.not_lt.1 hge, Int.not_lt.1 hle]

protected theorem compare_swap (a b : Int) : (compare a b).swap = compare b a := by
  simp only [compare_def_le]; (repeat' split) <;> try rfl
  next h1 h2 => cases h1 (Int.le_of_not_le h2)

protected theorem compare_eq_eq {a b : Int} : compare a b = .eq ↔ a = b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Int.ne_of_lt, Int.ne_of_gt, *]
  next hlt hgt => exact Int.le_antisymm (Int.not_lt.1 hgt) (Int.not_lt.1 hlt)

-- protected theorem compare_eq_lt {a b : Nat} : compare a b = .lt ↔ a < b := by
--   rw [compare_def_lt]; (repeat' split) <;> simp [*]

-- protected theorem compare_eq_gt {a b : Nat} : compare a b = .gt ↔ b < a := by
--   rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]

-- protected theorem compare_ne_gt {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
--   rw [compare_def_le]; (repeat' split) <;> simp [*]

-- protected theorem compare_ne_lt {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
--   rw [compare_def_le]; (repeat' split) <;> simp [Nat.le_of_not_le, *]

protected theorem isLE_compare {a b : Int} :
    (compare a b).isLE ↔ a ≤ b := by
  simp only [Int.compare_def_le]
  repeat' split <;> simp_all

-- protected theorem isGE_compare {a b : Nat} :
--     (compare a b).isLE ↔ a ≤ b := by
--   simp only [Nat.compare_def_le]
--   repeat' split <;> simp_all

end Int
