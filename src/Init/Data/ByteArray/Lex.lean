/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
public import Init.Data.Order.Factories
public import Init.Data.ByteArray.Lemmas
public import Init.Data.Array.Lex.Lemmas
public import Init.Data.Ord.Array
public import Init.Data.Ord.UInt
public import Init.Data.UInt.Package
public import Init.Data.Array.Package
public import Init.Data.Order.LemmasExtra
import Init.Omega
import Init.Data.Nat.Compare
import Init.Data.Nat.MinMax

open Std

namespace ByteArray

public instance : LT ByteArray where
  lt a b := a.data < b.data

public instance : LE ByteArray :=
  LE.ofLT _

@[simp]
public theorem data_lt_data {a b : ByteArray} : a.data < b.data ↔ a < b :=
  Iff.rfl

@[extern "lean_byte_array_dec_lt"]
public protected def decidableLT (a b : @& ByteArray) : Decidable (a < b) :=
  decidable_of_iff _ data_lt_data

public instance : DecidableLT ByteArray :=
  ByteArray.decidableLT

-- Work around #15328
public instance : DecidableLE ByteArray :=
  fun a b => inferInstanceAs (Decidable (¬ b < a))

@[extern "lean_byte_array_compare", expose]
public protected def compare (a b : @& ByteArray) : Ordering :=
  compare a.data b.data

public instance : Ord ByteArray where
  compare := ByteArray.compare

@[simp]
public theorem compare_data_data {a b : ByteArray} : Ord.compare a.data b.data = Ord.compare a b :=
  (rfl)

instance : Std.Asymm (α := ByteArray) (· < ·) where
  asymm a b := by simpa only [← data_lt_data] using Std.not_gt_of_lt

@[simp]
public theorem data_le_data {a b : ByteArray} : a.data ≤ b.data ↔ a ≤ b :=
  Iff.rfl

instance : LawfulOrderOrd ByteArray where
  isLE_compare a b := by simp [← compare_data_data, isLE_compare]
  isGE_compare := by simp [← compare_data_data, isGE_compare]

theorem beq_eq {a b : ByteArray} : (a == b) = (a.data == b.data) := rfl

instance : LawfulBEq ByteArray where
  rfl := by simp [beq_eq]
  eq_of_beq := by simp [beq_eq, ByteArray.ext_iff]

instance : Trans (α := ByteArray) (¬ · < ·) (¬ · < ·) (¬ · < ·) where
  trans {_ _ _} := by simpa [← data_lt_data, -data_le_data] using flip le_trans

instance : Trichotomous (α := ByteArray) (· < ·) where
  trichotomous a b := by simpa [← data_lt_data, -data_le_data, ByteArray.ext_iff] using flip le_antisymm

public instance : LinearOrderPackage ByteArray := .ofLE _ { }

public theorem compare_extract_extract_of_lt {a b : ByteArray} {i j i' j' : Nat}
    (hi : i < j) (hj : j ≤ a.size) (hi' : i' < j') (hj' : j' ≤ b.size) :
    compare (a.extract i j) (b.extract i' j') =
      (compare a[i] b[i']).then (compare (a.extract (i + 1) j) (b.extract (i' + 1) j')) := by
  rw [extract_eq_extract_append_extract (i + 1) (by omega) (by omega),
    extract_eq_extract_append_extract (a := b) (i' + 1) (by omega) (by omega),
    extract_add_one (by omega), extract_add_one (by omega)]
  simp only [← compare_data_data, Array.compare_eq_compare_toList, toList_data_append,
    List.toList_data_toByteArray, List.singleton_append, List.compare_cons_cons]

public theorem compare_eq_compare_extract_min_then {a b : ByteArray} :
    compare a b =
      (compare (a.extract 0 (min a.size b.size)) (b.extract 0 (min a.size b.size))).then
        (compare a.size b.size) := by
  simp only [← compare_data_data, data_extract]
  exact Array.compare_eq_compare_extract_min_then

public theorem lt_iff_extract_lt_of_size_le {a b : ByteArray} (h : b.size ≤ a.size) :
    a < b ↔ a.extract 0 b.size < b := by
  rw [← Std.compare_eq_lt, compare_eq_compare_extract_min_then, Nat.min_eq_right h,
    extract_zero_size, Ordering.then_eq_lt, Std.compare_eq_lt, Nat.compare_eq_lt]
  simp [Nat.not_lt.2 h]

public theorem lt_iff_not_extract_lt_of_size_lt {a b : ByteArray} (h : a.size < b.size) :
    a < b ↔ ¬ b.extract 0 a.size < a := by
  rw [← Std.compare_eq_lt, compare_eq_compare_extract_min_then,
    Nat.min_eq_left (Nat.le_of_lt h), extract_zero_size, ← Std.compare_eq_gt, Ordering.then_eq_lt,
    Nat.compare_eq_lt.2 h]
  cases compare a (b.extract 0 a.size) <;> simp

end ByteArray

@[simp]
public theorem List.toByteArray_lt_toByteArray {l₁ l₂ : List UInt8} :
    l₁.toByteArray < l₂.toByteArray ↔ l₁ < l₂ := by
  conv => rhs; rw [← List.toList_data_toByteArray (l := l₁),
    ← List.toList_data_toByteArray (l := l₂)]
  rw [Array.lt_toList, ByteArray.data_lt_data]

@[simp]
public theorem List.toByteArray_le_toByteArray {l₁ l₂ : List UInt8} :
    l₁.toByteArray ≤ l₂.toByteArray ↔ l₁ ≤ l₂ :=
  not_congr List.toByteArray_lt_toByteArray

@[simp]
public theorem List.compare_toByteArray_toByteArray {l₁ l₂ : List UInt8} :
    compare l₁.toByteArray l₂.toByteArray = compare l₁ l₂ := by
  rw [← ByteArray.compare_data_data, Array.compare_eq_compare_toList,
    List.toList_data_toByteArray, List.toList_data_toByteArray]
