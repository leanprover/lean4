/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
import Init.Data.List.Lex

open Std

namespace List

variable [LE α] [LT α] [Ord α] [h : BEq α] [DecidableEq α] [DecidableLT α] [IsLinearOrder α]
  [LawfulOrderLT α] [LawfulOrderOrd α] [LawfulOrderBEq α]

public instance : LawfulOrderOrd (List α) where
  isLE_compare xs ys := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp
    | cons x xs ih =>
      rcases ys with (_|⟨y, ys⟩)
      · simp
      · simp [Ordering.isLE_then_iff_or, ih ys, List.cons_le_cons_iff, Std.compare_eq_lt]
  isGE_compare xs ys := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp
    | cons x xs ih =>
      rcases ys with (_|⟨y, ys⟩)
      · simp
      · simp [Ordering.isGE_then_iff_or, ih ys, List.cons_le_cons_iff, Std.compare_eq_gt,
          eq_comm (a := x)]

public instance : LinearOrderPackage (List α) := .ofLE _ { }

-- Make sure we're not accidentally baking in `instBEqOfDecidableEq`.
example : (instLinearOrderPackage (α := α)).toBEq = @List.instBEq _ h := by
  with_reducible_and_instances rfl

end List
