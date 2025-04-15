/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Ord

set_option autoImplicit false

universe u

namespace Std.Internal

class IsCut {α : Type u} (cmp : α → α → Ordering) (cut : α → Ordering) where
  lt {k k'} : cut k' = .lt → cmp k' k = .lt → cut k = .lt
  gt {k k'} : cut k' = .gt → cmp k' k = .gt → cut k = .gt

class IsStrictCut {α : Type u} (cmp : α → α → Ordering) (cut : α → Ordering) extends IsCut cmp cut where
  eq (k) {k'} : cut k' = .eq → cut k = cmp k' k

variable {α : Type u} {cmp : α → α → Ordering} {cut : α → Ordering}

theorem IsStrictCut.gt_of_isGE_of_gt [IsStrictCut cmp cut] {k k' : α} :
    (cut k').isGE → cmp k' k = .gt → cut k = .gt := by
  cases h₁ : cut k' with
  | lt => rintro ⟨⟩
  | gt => exact fun _ => IsCut.gt h₁
  | eq => exact fun h₂ h₃ => by rw [← h₃, IsStrictCut.eq (cmp := cmp) k h₁]

theorem IsStrictCut.lt_of_isLE_of_lt [IsStrictCut cmp cut] {k k' : α} :
    (cut k').isLE → cmp k' k = .lt → cut k = .lt := by
  cases h₁ : cut k' with
  | gt => rintro ⟨⟩
  | lt => exact fun _ => IsCut.lt h₁
  | eq => exact fun h₂ h₃ => by rw [← h₃, IsStrictCut.eq (cmp := cmp) k h₁]

end Std.Internal
