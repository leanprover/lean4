/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Classes.Ord.Basic
import Std.Classes.Ord.New.LinearPreorder

set_option autoImplicit false

universe u

namespace Std.Internal

class IsCut {α : Type u} [Comparable α] (cut : α → Ordering) where
  lt {k k'} : cut k' = .lt → k' < k → cut k = .lt
  gt {k k'} : cut k' = .gt → k < k' → cut k = .gt

-- TODO: It is not nice that we need an `Ord` instance here
class IsStrictCut {α : Type u} [Ord α] [Comparable α] (cut : α → Ordering) extends IsCut cut where
  eq (k) {k'} : cut k' = .eq → cut k = compare k' k

variable {α : Type u} {cmp : α → α → Ordering} {cut : α → Ordering}

theorem IsStrictCut.gt_of_isGE_of_gt [Ord α] [Comparable α] [LawfulOrd α]
    [LawfulOrientedComparable α] [IsStrictCut cut] {k k' : α} :
    (cut k').isGE → k < k' → cut k = .gt := by
  cases h₁ : cut k' with
  | lt => rintro ⟨⟩
  | gt => exact fun _ => IsCut.gt h₁
  | eq => exact fun h₂ h₃ => by simp [IsStrictCut.eq k h₁, Comparable.compare_eq_gt_iff_gt, h₃]

theorem IsStrictCut.lt_of_isLE_of_lt [Ord α] [Comparable α] [LawfulOrd α] [LawfulComparable α]
    [IsStrictCut cut] {k k' : α} :
    (cut k').isLE → k' < k → cut k = .lt := by
  cases h₁ : cut k' with
  | gt => rintro ⟨⟩
  | lt => exact fun _ => IsCut.lt h₁
  | eq => exact fun h₂ h₃ => by simp [IsStrictCut.eq k h₁, Comparable.compare_eq_lt_iff_lt, h₃]

instance {_ : Ord α} [Comparable α] [LawfulLinearPreorder α] [LawfulOrd α] {k : α} :
    IsStrictCut (compare k) where
  lt h₁ h₂ := by
    simp only [Comparable.compare_eq_lt_iff_lt] at ⊢ h₁
    exact Trans.trans h₁ h₂
  gt h₁ h₂ := by
    simp only [Comparable.compare_eq_gt_iff_gt] at ⊢ h₁
    exact Trans.trans h₂ h₁
  eq _ _ := TransCmp.congr_left

instance [Ord α] [Comparable α] : IsStrictCut (fun _ : α => .lt) where
  lt := by simp
  gt := by simp
  eq := by simp

instance [Ord α] [Comparable α] [LawfulOrd α] [LawfulLinearPreorder α] {k : α} :
    IsStrictCut fun k' => (compare k k').then .gt where
  lt {_ _} := by simpa [Ordering.then_eq_lt, Comparable.compare_eq_lt_iff_lt] using Trans.trans
  eq {_ _} := by simp [Ordering.then_eq_eq]
  gt {_ _} := by
    simp [Ordering.then_eq_gt, ← Ordering.isGE_iff_eq_gt_or_eq_eq, ← Comparable.compare_eq_gt_iff_gt]
    intro h₁ h₂
    exact TransOrd.isGE_trans h₁ (Ordering.isGE_of_eq_gt h₂)

end Std.Internal
