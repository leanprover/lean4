/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.BitVec.Basic
public import Init.Data.Order.PackageFactories
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Compare
import Init.Data.Nat.Order

open Std

namespace BitVec

public instance : LinearOrderPackage (BitVec w) := .ofLE _ { }

@[simp]
public theorem compare_toNat {w : Nat} {x y : BitVec w} :
    compare x.toNat y.toNat = compare x y := by
  apply Std.compare_eq_of_lt_iff
  · simp [Std.compare_eq_lt, lt_def]
  · simp [Std.compare_eq_gt, lt_def]

-- We need the `no_index` here because otherwise the `simp` discrimination key will contain
-- `BitVec (HAdd.hAdd ..)`, but if `w` and `v` are concrete numbers, then the RHS will have
-- a type like `BitVec 16` rather than `BitVec (8 + 8)`, which would cause `simp` to fail to
-- apply this lemma.
public theorem compare_append_append {w v : Nat} {x₁ x₂ : BitVec w} {y₁ y₂ : BitVec v} :
    @compare (no_index _) _ (@HAppend.hAppend _ _ (no_index _) _ x₁ y₁)
      (@HAppend.hAppend _ _ (no_index _) _ x₂ y₂) =
      (compare x₁ x₂).then (compare y₁ y₂) := by
  apply Std.compare_eq_of_lt_iff
  · simp [Ordering.then_eq_lt, Std.compare_eq_lt, append_lt_append_iff]
  · simp [Ordering.then_eq_gt, Std.compare_eq_gt, append_lt_append_iff, eq_comm (a := x₂)]

public theorem compare_setWidth_setWidth_of_le {w w' : Nat} {x y : BitVec w} (h : w ≤ w') :
    compare (x.setWidth w') (y.setWidth w') = compare x y := by
  apply Std.compare_eq_of_lt_iff <;>
    simp_all [setWidth_lt_setWidth_iff_of_le, Std.compare_eq_lt, Std.compare_eq_gt]

end BitVec
