/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
public import Init.Data.Vector.Lex
public import Init.Data.Ord.Vector
import Init.Data.List.Package

open Std

namespace Vector

variable [LE α] [LT α] [Ord α] [h : BEq α] [DecidableEq α] [DecidableLT α] [IsLinearOrder α]
  [LawfulOrderLT α] [LawfulOrderOrd α] [LawfulOrderBEq α]

public instance : LawfulOrderOrd (Vector α n) where
  isLE_compare xs ys := by rw [Vector.compare_eq_compare_toList, Std.isLE_compare, le_toList]
  isGE_compare xs ys := by rw [Vector.compare_eq_compare_toList, Std.isGE_compare, le_toList]

public instance : LinearOrderPackage (Vector α n) := .ofLE _ { }

-- Make sure we're not accidentally baking in `instBEqOfDecidableEq`.
example : (instLinearOrderPackage (α := α) (n := n)).toBEq = @Vector.instBEq _ _ h := by
  with_reducible_and_instances rfl

end Vector
