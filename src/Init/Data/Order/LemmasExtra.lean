module

prelude
import Init.Data.Order.Lemmas
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.Ord

namespace Std

/-
* LawfulOrderOrd implies OrientedOrd, Total (· ≤ ·)
* Factories
* other LawfulOrder* instances
-/

theorem LawfulOrderOrd.compare_eq_lt {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α]
    {a b : α} : compare a b = .lt ↔ OrderData.IsLE a b ∧ ¬ OrderData.IsLE b a := by
  rw [← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
  cases compare a b <;> simp

theorem LawfulOrderOrd.compare_eq_gt {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α]
    {a b : α} : compare a b = .gt ↔ ¬ OrderData.IsLE a b ∧ OrderData.IsLE b a := by
  rw [← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
  cases compare a b <;> simp

theorem LawfulOrderOrd.compare_eq_eq {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α]
    {a b : α} : compare a b = .eq ↔ OrderData.IsLE a b ∧ OrderData.IsLE b a := by
  rw [← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
  cases compare a b <;> simp

theorem compare_isLE {α : Type u} [Ord α] [LE α] [OrderData α] [LawfulOrderOrd α] [LawfulOrderLE α]
    {a b : α} : (compare a b).isLE ↔ a ≤ b := by
  simp [LawfulOrderLE.le_iff, ← LawfulOrderOrd.compare_isLE]

theorem compare_isGE {α : Type u} [Ord α] [LE α] [OrderData α] [LawfulOrderOrd α] [LawfulOrderLE α]
    {a b : α} : (compare a b).isGE ↔ b ≤ a := by
  simp [LawfulOrderLE.le_iff, ← LawfulOrderOrd.compare_isGE]

theorem compare_eq_lt {α : Type u} [Ord α] [LT α] [OrderData α] [LawfulOrderOrd α] [LawfulOrderLT α]
    {a b : α} : compare a b = .lt ↔ a < b := by
  rw [LawfulOrderLT.lt_iff, ← LawfulOrderOrd.compare_isLE, ← LawfulOrderOrd.compare_isGE]
  cases compare a b <;> simp

theorem compare_eq_gt {α : Type u} [Ord α] [LT α] [OrderData α] [LawfulOrderOrd α] [LawfulOrderLT α]
    {a b : α} : compare a b = .gt ↔ b < a := by
  rw [LawfulOrderLT.lt_iff, ← LawfulOrderOrd.compare_isGE, ← LawfulOrderOrd.compare_isLE]
  cases compare a b <;> simp

theorem compare_eq_eq {α : Type u} [Ord α] [BEq α] [OrderData α] [LawfulOrderOrd α] [LawfulOrderBEq α]
    {a b : α} : compare a b = .eq ↔ a == b := by
  open Classical.Order in
  rw [LawfulOrderBEq.beq_iff_isLE_and_isLE, ← LawfulOrderLE.le_iff, ← LawfulOrderLE.le_iff,
    ← compare_isLE, ← compare_isGE]
  cases compare a b <;> simp

public instance {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α] : OrientedOrd α where
  eq_swap := by
    open Classical.Order in
    intro a b
    apply Eq.symm
    cases h : compare a b
    · rw [compare_eq_lt] at h
      simpa [Ordering.swap_eq_lt, compare_eq_gt] using h
    · rw [compare_eq_eq] at h
      simpa [Ordering.swap_eq_eq, compare_eq_eq] using BEq.symm h
    · rw [LawfulOrderOrd.compare_eq_gt, and_comm] at h
      simpa [Ordering.swap_eq_gt, compare_eq_lt] using h

public instance {α : Type u} [Ord α] [OrderData α] [LawfulOrderOrd α] [IsPreorder α] : TransOrd α where
  isLE_trans := by
    open scoped Classical.Order in
    simp only [compare_isLE]
    apply le_trans

public instance {α : Type u} [Ord α] [BEq α] [OrderData α] [LawfulOrderOrd α] [LawfulOrderBEq α] :
    LawfulBEqOrd α where
  compare_eq_iff_beq := by
    open scoped Classical.Order in
    simp [Ordering.eq_eq_iff_isLE_and_isGE, compare_isLE, compare_isGE, beq_iff_le_and_ge]

public instance {α : Type u} [Ord α] [OrderData α] [LawfulOrderOrd α] [IsPartialOrder α] : LawfulEqOrd α where
  eq_of_compare {a b} := by
    open Classical.Order in
    intro h
    apply le_antisymm
    · simp [← compare_isLE, h]
    · simp [← compare_isGE, h]

end Std

namespace Classical.Order
open Std

open scoped Classical in
public noncomputable scoped instance instOrd {α : Type u} [OrderData α] :
    Ord α where
  compare a b := if OrderData.IsLE a b then if OrderData.IsLE b a then .eq else .lt else .gt

public instance instLawfulOrderOrd {α : Type u} [OrderData α]
    [Total (α := α) OrderData.IsLE] :
    LawfulOrderOrd α where
  compare_isLE a b := by
    simp only [compare]
    by_cases OrderData.IsLE a b <;> rename_i h
    · simp only [h, ↓reduceIte, iff_true]
      split <;> simp
    · simp [h]
  compare_isGE a b := by
    simp only [compare]
    cases Total.total (r := OrderData.IsLE) a b <;> rename_i h
    · simp only [h, ↓reduceIte]
      split <;> simp [*]
    · simp only [h, ↓reduceIte, iff_true]
      split <;> simp

end Classical.Order
