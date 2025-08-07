/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Order.Lemmas
public import Init.Data.Order.FactoriesExtra
public import Init.Data.Order.Ord

namespace Std

/-
* Factories
-/

-- theorem LawfulOrderOrd.compare_eq_lt_iff_lt_and_not_gt {α : Type u} [LE α] [Ord α] [LawfulOrderOrd α]
--     {a b : α} : compare a b = .lt ↔ a ≤ b ∧ ¬ b ≤ a := by
--   rw [← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
--   cases compare a b <;> simp

-- theorem LawfulOrderOrd.compare_eq_gt {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α]
--     {a b : α} : compare a b = .gt ↔ ¬ OrderData.IsLE a b ∧ OrderData.IsLE b a := by
--   rw [← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
--   cases compare a b <;> simp

-- theorem LawfulOrderOrd.compare_eq_eq {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α]
--     {a b : α} : compare a b = .eq ↔ OrderData.IsLE a b ∧ OrderData.IsLE b a := by
--   rw [← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
--   cases compare a b <;> simp

theorem compare_isLE {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α]
    {a b : α} : (compare a b).isLE ↔ a ≤ b := by
  simp [← LawfulOrderOrd.compare_isLE]

theorem compare_isGE {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α]
    {a b : α} : (compare a b).isGE ↔ b ≤ a := by
  simp [← LawfulOrderOrd.compare_isGE]

theorem compare_eq_lt {α : Type u} [Ord α] [LT α] [LE α] [LawfulOrderOrd α] [LawfulOrderLT α]
    {a b : α} : compare a b = .lt ↔ a < b := by
  rw [LawfulOrderLT.lt_iff, ← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
  cases compare a b <;> simp

theorem compare_eq_gt {α : Type u} [Ord α] [LT α] [LE α] [LawfulOrderOrd α] [LawfulOrderLT α]
    {a b : α} : compare a b = .gt ↔ b < a := by
  rw [LawfulOrderLT.lt_iff, ← LawfulOrderOrd.compare_isGE, ← LawfulOrderOrd.compare_isLE]
  cases compare a b <;> simp

theorem compare_eq_eq {α : Type u} [Ord α] [BEq α] [LE α] [LawfulOrderOrd α] [LawfulOrderBEq α]
    {a b : α} : compare a b = .eq ↔ a == b := by
  open Classical.Order in
  rw [LawfulOrderBEq.beq_iff_isLE_and_isLE, ← compare_isLE, ← compare_isGE]
  cases compare a b <;> simp

public instance {α : Type u} [LE α] [Ord α] [LawfulOrderOrd α] : OrientedOrd α where
  eq_swap := by
    open Classical.Order in
    intro a b
    apply Eq.symm
    cases h : compare a b
    · rw [compare_eq_lt] at h
      simpa [Ordering.swap_eq_lt, compare_eq_gt] using h
    · rw [compare_eq_eq] at h
      simpa [Ordering.swap_eq_eq, compare_eq_eq] using BEq.symm h
    · rw [compare_eq_gt] at h
      simpa [Ordering.swap_eq_gt, compare_eq_lt] using h

public instance {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] [IsPreorder α] : TransOrd α where
  isLE_trans := by
    simp only [compare_isLE]
    apply le_trans

public instance {α : Type u} [Ord α] [BEq α] [LE α] [LawfulOrderOrd α] [LawfulOrderBEq α] :
    LawfulBEqOrd α where
  compare_eq_iff_beq := by
    simp [Ordering.eq_eq_iff_isLE_and_isGE, compare_isLE, compare_isGE, beq_iff_le_and_ge]

public instance {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] [IsPartialOrder α] : LawfulEqOrd α where
  eq_of_compare {a b} := by
    intro h
    apply le_antisymm
    · simp [← compare_isLE, h]
    · simp [← compare_isGE, h]

public instance [Ord α] [LE α] [LawfulOrderOrd α] :
    Total (α := α) (· ≤ ·) where
  total a b := by
    rw [← compare_isLE, ← compare_isGE]
    cases compare a b <;> simp

public theorem IsLinearPreorder.of_ord {α : Type u} [LE α] [Ord α] [LawfulOrderOrd α]
    [TransOrd α] : IsLinearPreorder α where
  le_refl a := by simp [← compare_isLE]
  le_trans a b c := by simpa [← compare_isLE] using TransOrd.isLE_trans
  le_total a b := Total.total a b

public theorem IsLinearOrder.of_ord {α : Type u} [LE α] [Ord α] [LawfulOrderOrd α]
    [TransOrd α] [LawfulEqOrd α] : IsLinearOrder α where
  toIsLinearPreorder := .of_ord
  le_antisymm a b hab hba := by
    apply LawfulEqOrd.eq_of_compare
    rw [← compare_isLE] at hab
    rw [← compare_isGE] at hba
    rw [Ordering.eq_eq_iff_isLE_and_isGE, hab, hba, and_self]

end Std

namespace Classical.Order
open Std

/--
Derives an `Ord α` instance from an `OrderData α`. Because in `Ord α`, all elements are comparable,
the resulting `Ord α` instance only makes sens if the `OrderData α`-defined order structure is total
-/
public noncomputable scoped instance instOrd {α : Type u} [LE α] :
    Ord α where
  compare a b := if a ≤ b then if b ≤ a then .eq else .lt else .gt

public instance instLawfulOrderOrd {α : Type u} [LE α]
    [Total (α := α) (· ≤ ·)] :
    LawfulOrderOrd α where
  compare_isLE a b := by
    simp only [compare]
    by_cases a ≤ b <;> rename_i h
    · simp only [h, ↓reduceIte, iff_true]
      split <;> simp
    · simp [h]
  compare_isGE a b := by
    simp only [compare]
    cases Total.total (r := (· ≤ ·)) a b <;> rename_i h
    · simp only [h, ↓reduceIte]
      split <;> simp [*]
    · simp only [h, ↓reduceIte, iff_true]
      split <;> simp

end Classical.Order
