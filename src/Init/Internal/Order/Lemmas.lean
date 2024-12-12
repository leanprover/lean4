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

theorem monotone_mapM
    (m : Type u → Type v) [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Type w} [PartialOrder γ]
    (f : γ → α → m β)
    (xs : List α)
    (hmono : forall_arg monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  cases xs with
  | nil => apply monotone_const
  | cons _ xs =>
    apply monotone_bind
    · apply hmono
    · intro y
      dsimp
      generalize [y] = ys
      induction xs generalizing ys with
      | nil => apply monotone_const
      | cons _ _ ih =>
        apply monotone_bind
        · apply hmono
        · intro z
          apply ih

theorem monotone_mapFinIdxM
    (m : Type u → Type v) [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Type w} [PartialOrder γ]
    (xs : Array α)
    (f : γ → Fin xs.size → α → m β)
    (hmono : forall_arg (forall_arg monotone) f) :
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
      apply hmono
    · intro y
      apply ih

end Lean.Order
