module

prelude
import Init.Data.Order.Lemmas
public import Init.Data.Order.ClassesExtra
public import Std.Classes.Ord -- TODO: move to Init?

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

public instance {α : Type u} [OrderData α] [Ord α] [LawfulOrderOrd α] : OrientedOrd α where
  eq_swap := by
    intro a b
    apply Eq.symm
    cases h : compare a b
    · rw [LawfulOrderOrd.compare_eq_lt] at h
      simp only [Ordering.swap_eq_lt, LawfulOrderOrd.compare_eq_gt]
      exact h.symm
    · rw [LawfulOrderOrd.compare_eq_eq] at h
      simp only [Ordering.swap_eq_eq, LawfulOrderOrd.compare_eq_eq]
      exact h.symm
    · rw [LawfulOrderOrd.compare_eq_gt] at h
      simp only [Ordering.swap_eq_gt, LawfulOrderOrd.compare_eq_lt]
      exact h.symm

public instance {α : Type u} [OrderData α] [Ord α] [BEq α] [LawfulOrderOrd α] [LawfulOrderBEq α] :
    sorry := sorry

open scoped _root_.Classical in
public noncomputable scoped instance _root_.Classical.Order.instOrd {α : Type u} [OrderData α] :
    Ord α where
  compare a b :=
    if OrderData.IsLE a b then if OrderData.IsLE b a then .eq else .lt else .gt

open scoped _root_.Classical in
open scoped _root_.Classical.Order in
public scoped instance _root_.Classical.Order.instLawfulOrderOrd {α : Type u} [OrderData α]
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

end Std
