/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Notation
import Init.Tactics
import Init.SimpLemmas

theorem apply_bif (f : α → β) {b : Bool} {a a' : α} :
    f (bif b then a else a') = bif b then f a else f a' := by
  cases b <;> simp

@[simp]
theorem bif_const {b : Bool} {a : α} : (bif b then a else a) = a := by
  cases b <;> simp

theorem bif_pos {b : Bool} {a a' : α} (h : b = true) : (bif b then a else a') = a := by
  rw [h, cond_true]

theorem bif_neg {b : Bool} {a a' : α} (h : b = false) : (bif b then a else a') = a' := by
  rw [h, cond_false]
