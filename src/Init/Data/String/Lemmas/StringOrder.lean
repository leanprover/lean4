/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.String.Compare
public import Init.Data.String.Basic
import Init.Data.String.Lemmas.Decode

public section

open Std

namespace String

@[deprecated Std.not_le +typeChanged (since := "2026-10-09")]
protected theorem not_le {a b : String} : ¬ a ≤ b ↔ b < a := Std.not_le
@[deprecated Std.not_lt +typeChanged (since := "2026-10-09")]
protected theorem not_lt {a b : String} : ¬ a < b ↔ b ≤ a := Std.not_lt
@[deprecated Std.le_refl +typeChanged (since := "2026-10-09")]
protected theorem le_refl (a : String) : a ≤ a := Std.le_refl _
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem lt_irrefl (a : String) : ¬ a < a := Std.lt_irrefl
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem le_trans {a b c : String} : a ≤ b → b ≤ c → a ≤ c := Std.le_trans
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem lt_trans {a b c : String} : a < b → b < c → a < c := Std.lt_trans
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem le_total (a b : String) : a ≤ b ∨ b ≤ a := Std.le_total
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem le_antisymm {a b : String} : a ≤ b → b ≤ a → a = b := Std.le_antisymm
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem lt_asymm {a b : String} (h : a < b) : ¬ b < a := Std.not_gt_of_lt h
@[deprecated Std.lt_irrefl +typeChanged (since := "2026-10-09")]
protected theorem ne_of_lt {a b : String} (h : a < b) : a ≠ b := Std.ne_of_lt h

@[simp]
theorem toList_lt_toList_iff {s t : String} : s.toList < t.toList ↔ s < t := by
  simp [← toByteArray_lt_toByteArray_iff, toList_lt_toList_iff_toByteArray_lt_toByteArray]

@[deprecated toList_lt_toList_iff +typeChanged (since := "2026-10-09")]
theorem lt_iff {s t : String} : s < t ↔ s.toList < t.toList :=
  toList_lt_toList_iff.symm

@[simp]
theorem toList_le_toList_iff {s t : String} : s.toList ≤ t.toList ↔ s ≤ t := by
  simp [← toByteArray_le_toByteArray_iff, toList_le_toList_iff_toByteArray_le_toByteArray]

@[simp]
theorem compare_toList_toList {s t : String} : compare s.toList t.toList = compare s t := by
  simp [← compare_toByteArray_toByteArray, compare_toList_toList_eq_compare_toByteArray_toByteArray]

end String
