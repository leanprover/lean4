-- This file produces:
-- PANIC at Lean.MetavarContext.getLevelDepth Lean.MetavarContext:839:14: unknown metavariable

-- from Mathlib.CategoryTheory.Category.Basic
class Category.{v, u} (obj : Type u) : Type max u (v + 1) where

-- from Mathlib.CategoryTheory.Functor.Basic
structure Functor' (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type max v₁ v₂ u₁ u₂ where

-- from Mathlib.CategoryTheory.Types
instance : Category (Type u) := sorry

-- from Mathlib.CategoryTheory.Limits.HasLimits
section

variable {J : Type u₁} [Category.{v₁} J] {C : Type u} [Category.{v} C]

class HasLimit (F : Functor' J C) : Prop where
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  has_limit : ∀ (J : Type u₁) [Category.{v₁} J] (F : Functor' J C), HasLimit F

instance {J : Type u₁} [Category.{v₁} J] [HasLimitsOfSize.{v₁, u₁} C] (F : Functor' J C) : HasLimit F :=
  sorry

def limit (F : Functor' J C) [HasLimit F] : C := sorry
def limit.π (F : Functor' J C) [HasLimit F] (j : J) : sorry := sorry

end

-- from Mathlib.CategoryTheory.Limits.Types
instance hasLimitsOfSize : HasLimitsOfSize.{v} (Type max v u) := sorry

set_option pp.mvars false
/--
error: type mismatch
  limit.π sorry sorry
has type
  sorry : Sort _
but is expected to have type
  limit f → sorry : Sort (imax (max (u + 1) (v + 1)) _)
-/
#guard_msgs in
theorem pi_lift_π_apply {C : Type v} [Category.{v} C] (f : Functor' C (Type max v u)) :
    (limit.π sorry sorry : limit f → sorry) sorry = sorry :=
  sorry
