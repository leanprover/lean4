/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
public import Init.Data.Array.Lex.Lemmas
import Init.Data.List.Package

open Std

namespace Array

variable [LE α] [LT α] [Ord α] [h : BEq α] [DecidableEq α] [DecidableLT α] [IsLinearOrder α]
  [LawfulOrderLT α] [LawfulOrderOrd α] [LawfulOrderBEq α]

public instance : LawfulOrderOrd (Array α) where
  isLE_compare xs ys := by rw [Array.compare_eq_compare_toList, Std.isLE_compare, le_toList]
  isGE_compare xs ys := by rw [Array.compare_eq_compare_toList, Std.isGE_compare, le_toList]

public instance : LinearOrderPackage (Array α) := .ofLE _ { }

-- Make sure we're not accidentally baking in `instBEqOfDecidableEq`.
example : (instLinearOrderPackage (α := α)).toBEq = @Array.instBEq _ h := by
  with_reducible_and_instances rfl

end Array
