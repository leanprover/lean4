/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.Data.List.Control
import Init.Data.Array.Basic
import Init.Internal.Order.Basic

namespace Lean.Order

section monad

variable {m : Type u → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m]
variable {α β : Type u}
variable {γ : Type w} [PartialOrder γ]

theorem monotone_option_bindM (f : γ → α → m (Option β)) (xs : Option α) (hmono : monotone f) :
    monotone (fun x => xs.bindM (f x)) := by
  cases xs with
  | none => apply monotone_const
  | some x =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const

theorem monotone_option_mapM (f : γ → α → m β) (xs : Option α) (hmono : monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  cases xs with
  | none => apply monotone_const
  | some x =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const

theorem monotone_option_elimM (a : γ → m (Option α)) (n : γ → m β) (s : γ → α → m β)
    (hmono₁ : monotone a) (hmono₂ : monotone n) (hmono₃ : monotone s) :
    monotone (fun x => Option.elimM (a x) (n x) (s x)) := by
  apply monotone_bind
  · apply hmono₁
  · apply monotone_of_monotone_apply
    intro o
    cases o
    case none => apply hmono₂
    case some y =>
      dsimp only [Option.elim]
      apply monotone_apply
      apply hmono₃

omit [MonoBind m] in
theorem monotone_option_getDM (o : Option α) (y : γ → m α) (hmono : monotone y) :
    monotone (fun x => o.getDM (y x)) := by
  cases o
  · apply hmono
  · apply monotone_const

theorem monotone_list_mapM (f : γ → α → m β) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  cases xs with
  | nil => apply monotone_const
  | cons _ xs =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      dsimp
      generalize [y] = ys
      induction xs generalizing ys with
      | nil => apply monotone_const
      | cons _ _ ih =>
        apply monotone_bind
        · apply monotone_apply
          apply hmono
        · apply monotone_of_monotone_apply
          intro y
          apply ih

theorem monotone_array_mapFinIdxM (xs : Array α) (f : γ → Fin xs.size → α → m β) (hmono : monotone f) :
    monotone (fun x => xs.mapFinIdxM (f x)) := by
  suffices
    ∀ i j (h : i + j = xs.size) r, monotone (fun x => Array.mapFinIdxM.map xs (f x) i j h r) by
    apply this
  intros i j h r
  induction i, j, h, r using Array.mapFinIdxM.map.induct xs
  case case1 =>
    apply monotone_const
  case case2 ih =>
    apply monotone_bind
    · dsimp
      apply monotone_apply
      apply monotone_apply
      apply hmono
    · intro y
      apply monotone_of_monotone_apply
      apply ih

end monad

end Lean.Order
