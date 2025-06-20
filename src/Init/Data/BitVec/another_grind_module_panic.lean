/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Data.BitVec.Basic
import Init.Grind

namespace BitVec

theorem getElem_of_getLsbD_eq_true' {x : BitVec w} {i : Nat} (h : x.getLsbD i = true) :
    (x[i]'sorry = true) = True := by
  sorry

theorem getLsbD_eq_getMsbD' (x : BitVec w) (i : Nat) : x.getLsbD i = (decide (i < w) && x.getMsbD (w - 1 - i)) := by
  rw [getMsbD]
  by_cases h₁ : i < w <;> by_cases h₂ : w - 1 - i < w <;> simp only [h₁, h₂]
  · -- FIXME `grind` panics here
    grind only [= getLsbD_eq_getElem, cases Or]
  all_goals sorry
