/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.Tailrec.Basic
import Init.Data.List.Control
import Init.Data.Array.Basic

namespace Lean.Tailrec

theorem monotone_mapM
    (m : Type u → Type v) [Monad m] [∀ α, Order (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Type w} [Order γ]
    (f : γ → α → m β)
    (xs : List α)
    (hmono : forall_arg monotone f) :
    monotone (fun x => xs.mapM (fun y => f x y)) := by
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
    (m : Type u → Type v) [Monad m] [∀ α, Order (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Type w} [Order γ]
    (xs : Array α)
    (f : γ → Fin xs.size → α → m β)
    (hmono : forall_arg (forall_arg monotone) f) :
    monotone (fun x => xs.mapFinIdxM (fun i y => f x i y)) := by
  -- This shows a limitation of the induction principles:
  -- the parameter `f` isn't strictly needed, and cannot actually be instantiated here
  suffices
    ∀ i j (h : i + j = xs.size) r, monotone (fun x => Array.mapFinIdxM.map xs (fun i y => f x i y) i j h r) by
    apply this
  intros i j h r
  induction i, j, h, r using Array.mapFinIdxM.map.induct (m := m) xs
  case case1 =>
    apply monotone_const
  case case2 ih =>
    apply monotone_bind
    · dsimp
      apply hmono
    · intro y
      apply ih
  case f i y => exact f sorry i y


end Lean.Tailrec
