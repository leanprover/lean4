/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.String.Slice.Basic
public import Init.Data.Order.PackageFactories
import all Init.Data.String.Slice.Basic
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Slice

open Std

namespace String.Slice

theorem blt_eq_true_iff {s t : Slice} : s.blt t = true ↔ s.copy < t.copy := by
  rw [blt, ← String.toByteArray_lt_toByteArray_iff]
  simp only [utf8ByteSize_eq_size_toByteArray_copy]
  split <;> rename_i h
  · rw [Bool.not_eq_true', ← Bool.not_eq_true, Pattern.Internal.memcmpSliceLt_eq_true_iff,
      ByteArray.lt_iff_not_extract_lt_of_size_lt h]
    simp only [offset_startPos, Pos.Raw.byteIdx_zero, Nat.zero_add, ByteArray.extract_zero_size]
  · rw [Pattern.Internal.memcmpSliceLt_eq_true_iff,
      ByteArray.lt_iff_extract_lt_of_size_le (Nat.not_lt.1 h)]
    simp only [offset_startPos, Pos.Raw.byteIdx_zero, Nat.zero_add, ByteArray.extract_zero_size]

@[simp]
public theorem blt_eq_decide_lt {s t : Slice} : s.blt t = decide (s < t) := rfl

theorem lt_iff_blt_eq_true {s t : Slice} : s < t ↔ s.blt t = true := by
  simp

theorem not_lt {s t : Slice} : ¬s < t ↔ t ≤ s := Iff.rfl

@[simp]
public theorem lt_iff_copy_lt_copy {s t : Slice} : s < t ↔ s.copy < t.copy := by
  rw [lt_iff_blt_eq_true, blt_eq_true_iff]

@[simp]
public theorem le_iff_copy_le_copy {s t : Slice} : s ≤ t ↔ s.copy ≤ t.copy := by
  rw [← not_lt, lt_iff_copy_lt_copy, Std.not_lt]

@[simp]
public theorem compare_eq {s t : Slice} : Slice.compare s t = compare s t := rfl

@[simp]
public theorem compare_eq_compare_copy_copy {s t : Slice} :
    compare s t = compare s.copy t.copy := by
  rw [← compare_eq, Slice.compare,
    Pattern.Internal.memcmpSliceCompare_eq_compare, ← String.compare_toByteArray_toByteArray,
    ByteArray.compare_eq_compare_extract_min_then (a := s.copy.toByteArray)]
  simp only [offset_startPos, Pos.Raw.byteIdx_zero, Nat.zero_add,
    utf8ByteSize_eq_size_toByteArray_copy]

instance : LawfulOrderLT Slice where
  lt_iff a b := by simp [Std.lt_iff_le_and_not_ge]

instance : LawfulOrderOrd Slice where
  isLE_compare a b := by simp [Std.isLE_compare]
  isGE_compare a b := by simp [Std.isGE_compare]

instance : LawfulOrderBEq Slice where
  beq_iff_le_and_ge a b := by simp [Std.le_antisymm_iff]

instance : TransOrd Slice where
  isLE_trans {a b c} := by
    simpa using TransOrd.isLE_trans (a := a.copy) (b := b.copy) (c := c.copy)

public instance : LinearPreorderPackage Slice := .ofOrd _


end String.Slice
