/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.Tailrec.Basic
import Init.Data.List.Control

namespace Lean.Tailrec

theorem monotone_mapM
    (m : Type u → Type v) [Monad m] [∀ α, Order (m α)] [MonoBind m]
    {α β : Type u}
    {γ : Type w} [Order γ]
    (f : γ → α → m β)
    (xs : List α)
    (hmono : monotone_fun f) :
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

end Lean.Tailrec
