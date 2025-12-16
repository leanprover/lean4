/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Lemmas

set_option doc.verso true

public section

namespace Std.PRange.Nat

@[simp]
theorem succ?_eq {n : Nat} : succ? n = some (n + 1) :=
  rfl

@[simp]
theorem succMany?_eq {n : Nat} : succMany? n m = some (m + n) :=
  rfl

@[simp]
theorem succ_eq {n : Nat} : succ n = n + 1 :=
  rfl

@[simp]
theorem succMany_eq {n : Nat} : succMany n m = m + n := by
  rfl

end Std.PRange.Nat

namespace Nat
open Std Std.PRange Std.PRange.Nat

@[simp]
theorem size_rcc {a b : Nat} :
    (a...=b).size = b + 1 - a := by
  simp [Rcc.size, Rxc.HasSize.size]

@[deprecated size_rcc (since := "2025-10-30")]
def _root_.Std.PRange.Nat.size_Rcc := @_root_.Nat.size_rcc

@[deprecated size_rcc (since := "2025-12-01")]
def _root_.Std.PRange.Nat.size_rcc := @_root_.Nat.size_rcc

@[simp]
theorem length_toList_rcc {a b : Nat} :
    (a...=b).toList.length = b + 1 - a := by
  simp only [Rcc.length_toList, size_rcc]

@[simp]
theorem size_toArray_rcc {a b : Nat} :
    (a...=b).toArray.size = b + 1 - a := by
  simp only [Rcc.size_toArray, size_rcc]

@[simp]
theorem size_rco {a b : Nat} :
    (a...b).size = b - a := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[deprecated size_rco (since := "2025-10-30")]
def _root_.Std.PRange.Nat.size_Rco := @_root_.Nat.size_rco

@[deprecated size_rco (since := "2025-12-01")]
def _root_.Std.PRange.Nat.size_rco := @_root_.Nat.size_rco

@[simp]
theorem length_toList_rco {a b : Nat} :
    (a...b).toList.length = b - a := by
  simp only [Rco.length_toList, size_rco]

@[simp]
theorem size_toArray_rco {a b : Nat} :
    (a...b).toArray.size = b - a := by
  simp only [Rco.size_toArray, size_rco]

@[simp]
theorem size_roc {a b : Nat} :
    (a<...=b).size = b - a := by
  simp [Roc.size, Rxc.HasSize.size]

@[deprecated size_roc (since := "2025-10-30")]
def _root_.Std.PRange.Nat.size_Roc := @_root_.Nat.size_roc

@[deprecated size_roc (since := "2025-12-01")]
def _root_.Std.PRange.Nat.size_roc := @_root_.Nat.size_roc

@[simp]
theorem length_toList_roc {a b : Nat} :
    (a<...=b).toList.length = b - a := by
  simp only [Roc.length_toList, size_roc]

@[simp]
theorem size_toArray_roc {a b : Nat} :
    (a<...=b).toArray.size = b - a := by
  simp only [Roc.size_toArray, size_roc]

@[simp]
theorem size_roo {a b : Nat} :
    (a<...b).size = b - a - 1 := by
  simp [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[deprecated size_roo (since := "2025-10-30")]
def _root_.Std.PRange.Nat.size_Roo := @_root_.Nat.size_roo

@[deprecated size_roo (since := "2025-12-01")]
def _root_.Std.PRange.Nat.size_roo := @_root_.Nat.size_roo

@[simp]
theorem length_toList_roo {a b : Nat} :
    (a<...b).toList.length = b - a - 1 := by
  simp only [Roo.length_toList, size_roo]

@[simp]
theorem size_toArray_roo {a b : Nat} :
    (a<...b).toArray.size = b - a - 1 := by
  simp only [Roo.size_toArray, size_roo]

@[simp]
theorem size_ric {b : Nat} :
    (*...=b).size = b + 1 := by
  simp [Ric.size, Rxc.HasSize.size]

@[deprecated size_ric (since := "2025-10-30")]
def _root_.Std.PRange.Nat.size_Ric := @_root_.Nat.size_ric

@[deprecated size_ric (since := "2025-12-01")]
def _root_.Std.PRange.Nat.size_ric := @_root_.Nat.size_ric

@[simp]
theorem length_toList_ric {b : Nat} :
    (*...=b).toList.length = b + 1 := by
  simp only [Ric.length_toList, size_ric]

@[simp]
theorem size_toArray_ric {b : Nat} :
    (*...=b).toArray.size = b + 1 := by
  simp only [Ric.size_toArray, size_ric]

@[simp]
theorem size_rio {b : Nat} :
    (*...b).size = b := by
  simp [Rio.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[deprecated size_rio (since := "2025-10-30")]
def _root_.Std.PRange.Nat.size_Rio := @_root_.Nat.size_rio

@[deprecated size_rio (since := "2025-12-01")]
def _root_.Std.PRange.Nat.size_rio := @_root_.Nat.size_rio

@[simp]
theorem length_toList_rio {b : Nat} :
    (*...b).toList.length = b := by
  simp only [Rio.length_toList, size_rio]

@[simp]
theorem size_toArray_rio {b : Nat} :
    (*...b).toArray.size = b := by
  simp only [Rio.size_toArray, size_rio]

@[simp]
theorem toList_toArray_rco {m n : Nat} :
    (m...n).toArray.toList = (m...n).toList := by
  simp

@[simp]
theorem toArray_toList_rco {m n : Nat} :
    (m...n).toList.toArray = (m...n).toArray := by
  simp

theorem toList_rco_eq_if {m n : Nat} :
    (m...n).toList = if m < n then m :: ((m + 1)...n).toList else [] := by
  rw [Rco.toList_eq_if_roo]
  simp [Roo.toList_eq_match_rco]

theorem toList_rco_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := by
  simp [← succ_eq, Rco.toList_succ_succ_eq_map]

@[deprecated _root_.Nat.toList_rco_succ_succ (since := "2025-10-30")]
def _root_.Std.PRange.Nat.toList_Rco_succ_succ := @_root_.Nat.toList_rco_succ_succ

@[deprecated _root_.Nat.toList_rco_succ_succ (since := "2025-12-01")]
def _root_.Std.PRange.Nat.toList_rco_succ_succ := @_root_.Nat.toList_rco_succ_succ

theorem toList_rco_succ_right_eq_cons_map {m n : Nat} (h : m ≤ n) :
    (m...(n + 1)).toList = m :: (m...n).toList.map (· + 1) := by
  rw [Rco.toList_eq_if_roo, if_pos (Nat.lt_succ_iff.mpr h), Roo.toList_eq_match_rco]
  simp [toList_rco_succ_succ]

@[simp]
theorem toList_rco_eq_nil_iff {m n : Nat} :
    (m...n).toList = [] ↔ n ≤ m := by
  simp [Rco.toList_eq_if_roo]

theorem toList_rco_ne_nil_iff {m n : Nat} :
    (m...n).toList ≠ [] ↔ m < n := by
  simp

@[simp]
theorem toList_rco_eq_nil {m n : Nat} (h : n ≤ m) :
    (m...n).toList = [] := by
  simp [h]

@[simp]
theorem toList_rco_eq_singleton_iff {m n : Nat} :
    (m...n).toList = [k] ↔ n = m + 1 ∧ m = k := by
  rw [toList_rco_eq_if]
  split <;> (simp; omega)

@[simp 1001]
theorem toList_rco_eq_singleton {m n : Nat} (h : n = m + 1) :
    (m...n).toList = [m] := by
  simp [h]

@[simp]
theorem toList_rco_eq_cons_iff {m n a : Nat} :
    (m...n).toList = a :: xs ↔ m = a ∧ m < n ∧ ((m + 1)...n).toList = xs := by
  rw [Rco.toList_eq_if_roo]
  split <;> simp +contextual [*, Roo.toList_eq_match_rco, eq_comm]

theorem toList_rco_eq_cons {m n : Nat} (h : m < n) :
    (m...n).toList = m :: ((m + 1)...n).toList := by
  simp [h]

@[simp]
theorem toList_rco_zero_right_eq_nil {m : Nat} :
    (m...0).toList = [] := by
  simp

theorem map_add_toList_rco {m n k : Nat} :
    (m...n).toList.map (· + k) = ((m + k)...(n + k)).toList := by
  induction k
  · simp
  · rename_i k ih
    simp [← Nat.add_assoc, toList_rco_succ_succ, ← ih]

theorem map_add_toList_rco' {m n k : Nat} :
    (m...n).toList.map (k + ·) = ((k + m)...(k + n)).toList := by
  simp [Nat.add_comm, ← map_add_toList_rco]

theorem toList_rco_add_right_eq_map {m n : Nat} :
    (m...(m + n)).toList = (0...n).toList.map (· + m) := by
  rw (occs := [1]) [← Nat.zero_add m]
  simp [map_add_toList_rco', Nat.add_comm _ m]

theorem toList_rco_add_succ_right_eq_append {m n : Nat} :
    (m...(m + n + 1)).toList = (m...(m + n)).toList ++ [m + n] := by
  induction n generalizing m
  · simp
  · rename_i n ih
    rw [toList_rco_eq_cons (by omega), toList_rco_eq_cons (m := m) (by omega),
      show m + (n + 1) + 1 = (m + 1) + n + 1 by omega, ih]
    simp [show m + 1 + n = m + (n + 1) by omega]

theorem toList_rco_succ_right_eq_append {m n : Nat} (h : m ≤ n) :
    (m...(n + 1)).toList = (m...n).toList ++ [n] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [toList_rco_add_succ_right_eq_append]

theorem toList_rco_add_succ_right_eq_append' {m n : Nat} :
    (m...(m + (n + 1))).toList = (m...(m + n)).toList ++ [m + n] := by
  simp [toList_rco_add_succ_right_eq_append, ← Nat.add_assoc]

theorem toList_rco_eq_append {m n : Nat} (h : m < n) :
    (m...n).toList = (m...(n - 1)).toList ++ [n - 1] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  simp [toList_rco_add_succ_right_eq_append]

theorem toList_rco_eq_if_append {m n : Nat} :
    (m...n).toList = if m < n then (m...(n - 1)).toList ++ [n - 1] else [] := by
  split
  · simp only [toList_rco_eq_append, *]
  · simp; omega

theorem toList_rco_add_add_eq_append {m n k : Nat} :
    (m...(m + n + k)).toList = (m...(m + n)).toList ++ ((m + n)...(m + n + k)).toList := by
  induction k
  · simp
  · rename_i k ih
    rw [toList_rco_add_succ_right_eq_append', ← List.append_assoc, ← ih, toList_rco_eq_append]
    · simp
    · omega

theorem toList_rco_append_toList_rco {l m n : Nat} (h : l ≤ m) (h' : m ≤ n) :
    (l...m).toList ++ (m...n).toList = (l...n).toList := by
  obtain ⟨_, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨_, rfl⟩ := Nat.exists_eq_add_of_le h'
  simp [toList_rco_add_add_eq_append]

@[simp]
theorem getElem_toList_rco {m n i : Nat} (_h : i < (m...n).toList.length) :
    (m...n).toList[i]'_h = m + i := by
  simp [Rco.getElem_toList_eq]

theorem getElem?_toList_rco {m n i : Nat} :
    (m...n).toList[i]? = if i < n - m then some (m + i) else none := by
  simp [Rco.getElem?_toList_eq, Option.filter_some, ← Nat.lt_sub_iff_add_lt']

@[simp]
theorem getElem?_toList_rco_eq_some_iff {m n i : Nat} :
    (m...n).toList[i]? = some k ↔ i < n - m ∧ m + i = k := by
  simp [getElem?_toList_rco, eq_comm]

@[simp]
theorem getElem?_toList_rco_eq_none_iff {m n i : Nat} :
    (m...n).toList[i]? = none ↔ n ≤ i + m := by
  simp [getElem?_toList_rco]

@[simp]
theorem isSome_getElem?_toList_rco_eq {m n i : Nat} :
    (m...n).toList[i]?.isSome = (i < n - m) := by
  simp

@[simp]
theorem isNone_getElem?_toList_rco_eq {m n i : Nat} :
    (m...n).toList[i]?.isNone = (n ≤ i + m) := by
  simp

@[simp 1001]
theorem getElem?_toList_rco_eq_some {m n i : Nat} (h : i < n - m) :
    (m...n).toList[i]? = some (m + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toList_rco_eq_none {m n i : Nat} (h : n ≤ i + m) :
    (m...n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_rco {m n i : Nat} :
    (m...n).toList[i]! = if i < n - m then (m + i) else 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Nat.default_eq_zero]
  split <;> simp

@[simp 1001]
theorem getElem!_toList_rco_eq_add {m n i : Nat} (h : i < n - m) :
    (m...n).toList[i]! = m + i := by
  simp [h]

@[simp 1001]
theorem getElem!_toList_rco_eq_zero {m n i : Nat} (h : n ≤ i + m) :
    (m...n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_rco_eq_zero_iff {m n i : Nat} :
    (m...n).toList[i]! = 0 ↔ n ≤ i + m ∨ (m = 0 ∧ i = 0) := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Nat.default_eq_zero]
  split <;> (simp; omega)

theorem zero_lt_getElem!_toList_rco_iff {m n i : Nat} :
    0 < (m...n).toList[i]! ↔ i < n - m ∧ 0 < i + m := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Nat.default_eq_zero]
  split <;> (simp; omega)

theorem getD_toList_rco {m n i fallback : Nat} :
    (m...n).toList.getD i fallback = if i < n - m then (m + i) else fallback := by
  by_cases h : i < n - m <;> simp [h]

@[simp]
theorem getD_toList_rco_eq_add {m n i fallback : Nat} (h : i < n - m) :
    (m...n).toList.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toList_rco_eq_fallback {m n i fallback : Nat} (h : n ≤ i + m) :
    (m...n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_rco_eq_if {m n : Nat} :
    (m...n).toArray = if m < n then #[m] ++ ((m + 1)...n).toArray else #[] := by
  rw [Rco.toArray_eq_if_roo]
  simp [Roo.toArray_eq_match_rco]

theorem toArray_rco_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toArray = (m...n).toArray.map (· + 1) := by
  simp [← succ_eq, Rco.toArray_succ_succ_eq_map]

theorem toArray_rco_succ_right_eq_append_map {m n : Nat} (h : m ≤ n) :
    (m...(n + 1)).toArray = #[m] ++ (m...n).toArray.map (· + 1) := by
  rw [Rco.toArray_eq_if_roo, if_pos (Nat.lt_succ_iff.mpr h), Roo.toArray_eq_match_rco]
  simp [toArray_rco_succ_succ]

@[simp]
theorem toArray_rco_eq_empty_iff {m n : Nat} :
    (m...n).toArray = #[] ↔ n ≤ m := by
  simp [Rco.toArray_eq_if_roo]

theorem toArray_rco_ne_empty_iff {m n : Nat} :
    (m...n).toArray ≠ #[] ↔ m < n := by
  simp

@[simp]
theorem toArray_rco_eq_empty {m n : Nat} (h : n ≤ m) :
    (m...n).toArray = #[] := by
  simp [h]

@[simp]
theorem toArray_rco_eq_singleton_iff {m n : Nat} :
    (m...n).toArray = #[k] ↔ n = m + 1 ∧ m = k := by
  rw [toArray_rco_eq_if]
  split <;> (simp; omega)

@[simp 1001]
theorem toArray_rco_eq_singleton {m n : Nat} (h : n = m + 1) :
    (m...n).toArray = #[m] := by
  simp [h]

@[simp]
theorem toArray_rco_eq_singleton_append_iff {m n a : Nat} :
    (m...n).toArray = #[a] ++ xs ↔ m = a ∧ m < n ∧ ((m + 1)...n).toArray = xs := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff]
  simp

theorem toArray_rco_eq_singleton_append {m n : Nat} (h : m < n) :
    (m...n).toArray = #[m] ++ ((m + 1)...n).toArray := by
  simp [h]

@[simp]
theorem toArray_rco_zero_right_eq_empty {m : Nat} :
    (m...0).toArray = #[] := by
  simp

theorem map_add_toArray_rco {m n k : Nat} :
    (m...n).toArray.map (· + k) = ((m + k)...(n + k)).toArray := by
  simp only [← toArray_toList_rco, List.map_toArray, map_add_toList_rco]

theorem map_add_toArray_rco' {m n k : Nat} :
    (m...n).toArray.map (k + ·) = ((k + m)...(k + n)).toArray := by
  simp [Nat.add_comm, ← map_add_toArray_rco]

theorem toArray_rco_add_right_eq_map {m n : Nat} :
    (m...(m + n)).toArray = (0...n).toArray.map (· + m) := by
  rw (occs := [1]) [← Nat.zero_add m]
  simp [map_add_toArray_rco', Nat.add_comm _ m]

theorem toArray_rco_add_succ_right_eq_push {m n : Nat} :
    (m...(m + n + 1)).toArray = (m...(m + n)).toArray.push (m + n) := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff, toList_rco_add_succ_right_eq_append]
  simp

theorem toArray_rco_succ_right_eq_push {m n : Nat} (h : m ≤ n) :
    (m...(n + 1)).toArray = (m...n).toArray.push n := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff, toList_rco_succ_right_eq_append h]
  simp

theorem toArray_rco_add_succ_right_eq_push' {m n : Nat} :
    (m...(m + (n + 1))).toArray = (m...(m + n)).toArray.push (m + n) := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff, toList_rco_add_succ_right_eq_append']
  simp

theorem toArray_rco_eq_push {m n : Nat} (h : m < n) :
    (m...n).toArray = (m...(n - 1)).toArray.push (n - 1) := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff, toList_rco_eq_append h]
  simp

theorem toArray_rco_eq_if_push {m n : Nat} :
    (m...n).toArray = if m < n then (m...(n - 1)).toArray.push (n - 1) else #[] := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff]
  rw [toList_rco_eq_if_append, List.push_toArray]
  split <;> simp

theorem toArray_rco_add_add_eq_append {m n k : Nat} :
    (m...(m + n + k)).toArray = (m...(m + n)).toArray ++ ((m + n)...(m + n + k)).toArray := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff]
  simp [toList_rco_add_add_eq_append]

theorem toArray_rco_append_toArray_rco {l m n : Nat} (h : l ≤ m) (h' : m ≤ n) :
    (l...m).toArray ++ (m...n).toArray = (l...n).toArray := by
  simp only [← toArray_toList_rco, List.eq_toArray_iff]
  simp [toList_rco_append_toList_rco h h']

@[simp]
theorem getElem_toArray_rco {m n i : Nat} (_h : i < (m...n).toArray.size) :
    (m...n).toArray[i]'_h = m + i := by
  simp [Rco.getElem_toArray_eq]

theorem getElem?_toArray_rco {m n i : Nat} :
    (m...n).toArray[i]? = if i < n - m then some (m + i) else none := by
  simp [Rco.getElem?_toArray_eq, Option.filter_some, ← Nat.lt_sub_iff_add_lt']

@[simp]
theorem getElem?_toArray_rco_eq_some_iff {m n i : Nat} :
    (m...n).toArray[i]? = some k ↔ i < n - m ∧ m + i = k := by
  simp [getElem?_toArray_rco, eq_comm]

@[simp]
theorem getElem?_toArray_rco_eq_none_iff {m n i : Nat} :
    (m...n).toArray[i]? = none ↔ n ≤ i + m := by
  simp [getElem?_toArray_rco]

@[simp]
theorem isSome_getElem?_toArray_rco_eq {m n i : Nat} :
    (m...n).toArray[i]?.isSome = (i < n - m) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_rco_eq {m n i : Nat} :
    (m...n).toArray[i]?.isNone = (n ≤ i + m) := by
  simp

@[simp 1001]
theorem getElem?_toArray_rco_eq_some {m n i : Nat} (h : i < n - m) :
    (m...n).toArray[i]? = some (m + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toArray_rco_eq_none {m n i : Nat} (h : n ≤ i + m) :
    (m...n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_rco {m n i : Nat} :
    (m...n).toArray[i]! = if i < n - m then (m + i) else 0 := by
  simp only [← toArray_toList_rco, List.getElem!_toArray, getElem!_toList_rco]

@[simp 1001]
theorem getElem!_toArray_rco_eq_add {m n i : Nat} (h : i < n - m) :
    (m...n).toArray[i]! = m + i := by
  simp [h]

@[simp 1001]
theorem getElem!_toArray_rco_eq_zero {m n i : Nat} (h : n ≤ i + m) :
    (m...n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_rco_eq_zero_iff {m n i : Nat} :
    (m...n).toArray[i]! = 0 ↔ n ≤ i + m ∨ (m = 0 ∧ i = 0) := by
  simp only [← toArray_toList_rco, List.getElem!_toArray, getElem!_toList_rco_eq_zero_iff]

theorem zero_lt_getElem!_toArray_rco_iff {m n i : Nat} :
    0 < (m...n).toArray[i]! ↔ i < n - m ∧ 0 < i + m := by
  simp only [← toArray_toList_rco, List.getElem!_toArray, zero_lt_getElem!_toList_rco_iff]

theorem getD_toArray_rco {m n i fallback : Nat} :
    (m...n).toArray.getD i fallback = if i < n - m then (m + i) else fallback := by
  by_cases h : i < n - m <;> simp [h]

@[simp]
theorem getD_toArray_rco_eq_add {m n i fallback : Nat} (h : i < n - m) :
    (m...n).toArray.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toArray_rco_eq_fallback {m n i fallback : Nat} (h : n ≤ i + m) :
    (m...n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a...b` by
varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a...b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, the
statement holds for nonempty ranges {lean}`a...b` if it holds for the smaller range
{lean}`(a + 1)...b`.

The following is an example reproving {name}`length_toList_rco`.

```lean
example (a b : Nat) : (a...b).toList.length = b - a := by
  induction a, b using Nat.induct_rco_left
  case base =>
    simp only [Nat.toList_rco_eq_nil, List.length_nil, Nat.sub_eq_zero_of_le, *]
  case step =>
    simp only [Nat.toList_rco_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_rco_left (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a < b → motive (a + 1) b → motive a b)
    (a b : Nat) : motive a b := by
  induction h : b - a generalizing a b
  · apply base; omega
  · rename_i d ih
    apply step
    · omega
    · apply ih; omega

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a...b` by
varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a...b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, if the
statement holds for {lean}`a...b`, it also holds for the larger range {lean}`a...(b + 1)`.

The following is an example reproving {name}`length_toList_rco`.

```lean
example (a b : Nat) : (a...b).toList.length = b - a := by
  induction a, b using Nat.induct_rco_right
  case base =>
    simp only [Nat.toList_rco_eq_nil, List.length_nil, Nat.sub_eq_zero_of_le, *]
  case step a b hle ih =>
    rw [Nat.toList_rco_eq_append (by omega),
      List.length_append, List.length_singleton, Nat.add_sub_cancel, ih]
    omega
```
-/
theorem induct_rco_right (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Nat) : motive a b := by
  induction h : b - a generalizing a b
  · apply base; omega
  · rename_i d ih
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
    apply step
    · omega
    · apply ih
      omega

theorem toList_rcc_eq_toList_rco {m n : Nat} :
    (m...=n).toList = (m...(n + 1)).toList := by
  simp [Rcc.toList_eq_toList_rco]

@[simp]
theorem toList_toArray_rcc {m n : Nat} :
    (m...=n).toArray.toList = (m...=n).toList :=
  Rcc.toList_toArray

@[simp]
theorem toArray_toList_rcc {m n : Nat} :
    (m...=n).toList.toArray = (m...=n).toArray :=
  Rcc.toArray_toList

theorem toList_rcc_eq_if {m n : Nat} :
    (m...=n).toList = if m ≤ n then m :: ((m + 1)...=n).toList else [] := by
  rw [toList_rcc_eq_toList_rco, toList_rcc_eq_toList_rco, toList_rco_eq_if]
  split <;> (simp; omega)

theorem toList_rcc_succ_succ {m n : Nat} :
    ((m+1)...=(n+1)).toList = (m...=n).toList.map (· + 1) := by
  simp [← succ_eq, toList_rcc_eq_toList_rco, Rco.toList_succ_succ_eq_map]

theorem toList_rcc_succ_right_eq_cons_map {m n : Nat} (h : m ≤ n + 1) :
    (m...=(n + 1)).toList = m :: (m...=n).toList.map (· + 1) := by
  simp [toList_rcc_eq_toList_rco, toList_rco_succ_succ]; omega

@[simp]
theorem toList_rcc_eq_nil_iff {m n : Nat} :
    (m...=n).toList = [] ↔ n < m := by
  simp [toList_rcc_eq_toList_rco]; omega

theorem toList_rcc_ne_nil_iff {m n : Nat} :
    (m...=n).toList ≠ [] ↔ m ≤ n := by
  simp [toList_rcc_eq_toList_rco]; omega

@[simp 1001]
theorem toList_rcc_eq_nil {m n : Nat} (h : n < m) :
    (m...=n).toList = [] := by
  simp; omega

@[simp]
theorem toList_rcc_eq_singleton_iff {m n : Nat} :
    (m...=n).toList = [k] ↔ n = m ∧ m = k := by
  simp [toList_rcc_eq_toList_rco]; omega

@[simp 1001]
theorem toList_rcc_eq_singleton {m n : Nat} (h : n = m) :
    (m...=n).toList = [m] := by
  simp [h]

@[simp]
theorem toList_rcc_eq_cons_iff {m n a : Nat} :
    (m...=n).toList = a :: xs ↔ m = a ∧ m ≤ n ∧ ((m + 1)...=n).toList = xs := by
  simp [toList_rcc_eq_toList_rco]; omega

theorem toList_rcc_eq_cons {m n : Nat} (h : m ≤ n) :
    (m...=n).toList = m :: ((m + 1)...=n).toList := by
  simp; omega

theorem map_add_toList_rcc {m n k : Nat} :
    (m...=n).toList.map (· + k) = ((m + k)...=(n + k)).toList := by
  simp [toList_rcc_eq_toList_rco, map_add_toList_rco, show n + 1 + k = n + k + 1 by omega]

theorem map_add_toList_rcc' {m n k : Nat} :
    (m...=n).toList.map (k + ·) = ((k + m)...=(k + n)).toList := by
  simp [toList_rcc_eq_toList_rco, map_add_toList_rco', ← Nat.add_assoc]

theorem toList_rcc_add_right_eq_map {m n : Nat} :
    (m...=(m + n)).toList = (0...=n).toList.map (· + m) := by
  simp [toList_rcc_eq_toList_rco, show m + n + 1 = m + (n + 1) by omega,
    toList_rco_add_right_eq_map]

theorem toList_rcc_add_succ_right_eq_append {m n : Nat} :
    (m...=(m + n + 1)).toList = (m...=(m + n)).toList ++ [m + n + 1] := by
  simp only [Rcc.toList_eq_toList_rco, succ_eq]
  rw [toList_rco_eq_append (by omega)]
  simp

@[simp]
theorem toList_rcc_eq_append {m n : Nat} (h : m ≤ n) :
    (m...=n).toList = (m...n).toList ++ [n] := by
  simp [toList_rcc_eq_toList_rco, toList_rco_eq_append (Nat.lt_succ_of_le h)]

theorem toList_rcc_succ_right_eq_append {m n : Nat} (h : m ≤ n + 1) :
    (m...=(n + 1)).toList = (m...=n).toList ++ [n + 1] := by
  rw [toList_rcc_eq_append (by omega)]
  simp [toList_rcc_eq_toList_rco]

theorem toList_rcc_add_succ_right_eq_append' {m n : Nat} :
    (m...=(m + (n + 1))).toList = (m...=(m + n)).toList ++ [m + n + 1] := by
  rw [toList_rcc_eq_append (by omega), toList_rcc_eq_append (by omega)]
  simp [toList_rco_eq_append]; omega

@[simp]
theorem getElem_toList_rcc {m n i : Nat} (_h : i < (m...=n).toList.length) :
    (m...=n).toList[i]'_h = m + i := by
  simp [toList_rcc_eq_toList_rco]

theorem getElem?_toList_rcc {m n i : Nat} :
    (m...=n).toList[i]? = if i < n + 1 - m then some (m + i) else none := by
  simp [toList_rcc_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem getElem?_toList_rcc_eq_some_iff {m n i : Nat} :
    (m...=n).toList[i]? = some k ↔ i < n + 1 - m ∧ m + i = k := by
  simp [toList_rcc_eq_toList_rco, getElem?_toList_rco, eq_comm]

@[simp]
theorem getElem?_toList_rcc_eq_none_iff {m n i : Nat} :
    (m...=n).toList[i]? = none ↔ n + 1 ≤ i + m := by
  simp [toList_rcc_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem isSome_getElem?_toList_rcc_eq {m n i : Nat} :
    (m...=n).toList[i]?.isSome = (i < n + 1 - m) := by
  simp

@[simp]
theorem isNone_getElem?_toList_rcc_eq {m n i : Nat} :
    (m...=n).toList[i]?.isNone = (n + 1 ≤ i + m) := by
  simp

@[simp]
theorem getElem?_toList_rcc_eq_some {m n i : Nat} (h : i < n + 1 - m) :
    (m...=n).toList[i]? = some (m + i) := by
  simp [h]

@[simp]
theorem getElem?_toList_rcc_eq_none {m n i : Nat} (h : n + 1 ≤ i + m) :
    (m...=n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_rcc {m n i : Nat} :
    (m...=n).toList[i]! = if i < n + 1 - m then (m + i) else 0 := by
  simp only [toList_rcc_eq_toList_rco, getElem!_toList_rco]

@[simp]
theorem getElem!_toList_rcc_eq_add {m n i : Nat} (h : i < n + 1 - m) :
    (m...=n).toList[i]! = m + i := by
  simp [h]

@[simp]
theorem getElem!_toList_rcc_eq_zero {m n i : Nat} (h : n + 1 ≤ i + m) :
    (m...=n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_rcc_eq_zero_iff {m n i : Nat} :
    (m...=n).toList[i]! = 0 ↔ n + 1 ≤ i + m ∨ (m = 0 ∧ i = 0) := by
  simp only [toList_rcc_eq_toList_rco, getElem!_toList_rco_eq_zero_iff]

theorem zero_lt_getElem!_toList_rcc_iff {m n i : Nat} :
    0 < (m...=n).toList[i]! ↔ i < n + 1 - m ∧ 0 < i + m := by
  simp only [toList_rcc_eq_toList_rco, zero_lt_getElem!_toList_rco_iff]

theorem getD_toList_rcc {m n i fallback : Nat} :
    (m...=n).toList.getD i fallback = if i < n + 1 - m then (m + i) else fallback := by
  by_cases h : i < n + 1 - m <;> simp [h]

@[simp]
theorem getD_toList_rcc_eq_add {m n i fallback : Nat} (h : i < n + 1 - m) :
    (m...=n).toList.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toList_rcc_eq_fallback {m n i fallback : Nat} (h : n + 1 ≤ i + m) :
    (m...=n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_rcc_eq_toArray_rco {m n : Nat} :
    (m...=n).toArray = (m...(n + 1)).toArray := by
  simp [toList_rcc_eq_toList_rco, ← toArray_toList_rcc]

theorem toArray_rcc_eq_if {m n : Nat} :
    (m...=n).toArray = if m ≤ n then #[m] ++ ((m + 1)...=n).toArray else #[] := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff]
  rw [toList_rcc_eq_if]
  split <;> simp [toList_rcc_eq_toList_rco]

theorem toArray_rcc_succ_succ {m n : Nat} :
    ((m+1)...=(n+1)).toArray = (m...=n).toArray.map (· + 1) := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff, toList_rcc_succ_succ]
  simp [toList_rcc_eq_toList_rco]

theorem toArray_rcc_succ_right_eq_append_map {m n : Nat} (h : m ≤ n + 1) :
    (m...=(n + 1)).toArray = #[m] ++ (m...=n).toArray.map (· + 1) := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff, toList_rcc_succ_right_eq_cons_map h]
  simp [toList_rcc_eq_toList_rco]

@[simp]
theorem toArray_rcc_eq_empty_iff {m n : Nat} :
    (m...=n).toArray = #[] ↔ n < m := by
  simp [toArray_rcc_eq_toArray_rco, Nat.succ_le_iff]

theorem toArray_rcc_ne_empty_iff {m n : Nat} :
    (m...=n).toArray ≠ #[] ↔ m ≤ n := by
  simp [toArray_rcc_eq_toArray_rco, Nat.succ_le_iff]

@[simp 1001]
theorem toArray_rcc_eq_empty {m n : Nat} (h : n < m) :
    (m...=n).toArray = #[] := by
  simp; omega

@[simp]
theorem toArray_rcc_eq_singleton_iff {m n : Nat} :
    (m...=n).toArray = #[k] ↔ n = m ∧ m = k := by
  simp [toArray_rcc_eq_toArray_rco]

@[simp 1001]
theorem toArray_rcc_eq_singleton {m n : Nat} (h : n = m) :
    (m...=n).toArray = #[m] := by
  simp [h]

@[simp]
theorem toArray_rcc_eq_singleton_append_iff {m n a : Nat} :
    (m...=n).toArray = #[a] ++ xs ↔ m = a ∧ m ≤ n ∧ ((m + 1)...=n).toArray = xs := by
  simp [toArray_rcc_eq_toArray_rco]; omega

theorem toArray_rcc_eq_singleton_append {m n : Nat} (h : m ≤ n) :
    (m...=n).toArray = #[m] ++ ((m + 1)...=n).toArray := by
  simp; omega

theorem map_add_toArray_rcc {m n k : Nat} :
    (m...=n).toArray.map (· + k) = ((m + k)...=(n + k)).toArray := by
  simp [toArray_rcc_eq_toArray_rco, map_add_toArray_rco, show n + 1 + k = n + k + 1 by omega]

theorem map_add_toArray_rcc' {m n k : Nat} :
    (m...=n).toArray.map (k + ·) = ((k + m)...=(k + n)).toArray := by
  simp [toArray_rcc_eq_toArray_rco, map_add_toArray_rco', ← Nat.add_assoc]

theorem toArray_rcc_add_right_eq_map {m n : Nat} :
    (m...=(m + n)).toArray = (0...=n).toArray.map (· + m) := by
  simp [toArray_rcc_eq_toArray_rco, show m + n + 1 = m + (n + 1) by omega,
    toArray_rco_add_right_eq_map]

theorem toArray_rcc_add_succ_right_eq_push {m n : Nat} :
    (m...=(m + n + 1)).toArray = (m...=(m + n)).toArray.push (m + n + 1) := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff, toList_rcc_add_succ_right_eq_append]
  simp

@[simp]
theorem toArray_rcc_eq_push {m n : Nat} (h : m ≤ n) :
    (m...=n).toArray = (m...n).toArray.push n := by
  simp [toArray_rcc_eq_toArray_rco, toArray_rco_eq_push (Nat.lt_succ_of_le h)]

theorem toArray_rcc_succ_right_eq_push {m n : Nat} (h : m ≤ n + 1) :
    (m...=(n + 1)).toArray = (m...=n).toArray.push (n + 1) := by
  rw [toArray_rcc_eq_push (by omega)]
  simp [toArray_rcc_eq_toArray_rco]

theorem toArray_rcc_add_succ_right_eq_push' {m n : Nat} :
    (m...=(m + (n + 1))).toArray = (m...=(m + n)).toArray.push (m + n + 1) := by
  rw [toArray_rcc_eq_push (by omega), toArray_rcc_eq_push (by omega)]
  simp [toArray_rco_eq_push, Nat.add_assoc]

@[simp]
theorem getElem_toArray_rcc {m n i : Nat} (_h : i < (m...=n).toArray.size) :
    (m...=n).toArray[i]'_h = m + i := by
  simp [toArray_rcc_eq_toArray_rco]

theorem getElem?_toArray_rcc {m n i : Nat} :
    (m...=n).toArray[i]? = if i < n + 1 - m then some (m + i) else none := by
  simp [toArray_rcc_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem getElem?_toArray_rcc_eq_some_iff {m n i : Nat} :
    (m...=n).toArray[i]? = some k ↔ i < n + 1 - m ∧ m + i = k := by
  simp [toArray_rcc_eq_toArray_rco, getElem?_toArray_rco, eq_comm]

@[simp]
theorem getElem?_toArray_rcc_eq_none_iff {m n i : Nat} :
    (m...=n).toArray[i]? = none ↔ n + 1 ≤ i + m := by
  simp [toArray_rcc_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem isSome_getElem?_toArray_rcc_eq {m n i : Nat} :
    (m...=n).toArray[i]?.isSome = (i < n + 1 - m) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_rcc_eq {m n i : Nat} :
    (m...=n).toArray[i]?.isNone = (n + 1 ≤ i + m) := by
  simp

@[simp]
theorem getElem?_toArray_rcc_eq_some {m n i : Nat} (h : i < n + 1 - m) :
    (m...=n).toArray[i]? = some (m + i) := by
  simp [h]

@[simp]
theorem getElem?_toArray_rcc_eq_none {m n i : Nat} (h : n + 1 ≤ i + m) :
    (m...=n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_rcc {m n i : Nat} :
    (m...=n).toArray[i]! = if i < n + 1 - m then (m + i) else 0 := by
  simp only [toArray_rcc_eq_toArray_rco, getElem!_toArray_rco]

@[simp]
theorem getElem!_toArray_rcc_eq_add {m n i : Nat} (h : i < n + 1 - m) :
    (m...=n).toArray[i]! = m + i := by
  simp [h]

@[simp]
theorem getElem!_toArray_rcc_eq_zero {m n i : Nat} (h : n + 1 ≤ i + m) :
    (m...=n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_rcc_eq_zero_iff {m n i : Nat} :
    (m...=n).toArray[i]! = 0 ↔ n + 1 ≤ i + m ∨ (m = 0 ∧ i = 0) := by
  simp only [toArray_rcc_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff]

theorem zero_lt_getElem!_toArray_rcc_iff {m n i : Nat} :
    0 < (m...=n).toArray[i]! ↔ i < n + 1 - m ∧ 0 < i + m := by
  simp only [toArray_rcc_eq_toArray_rco, zero_lt_getElem!_toArray_rco_iff]

theorem getD_toArray_rcc {m n i fallback : Nat} :
    (m...=n).toArray.getD i fallback = if i < n + 1 - m then (m + i) else fallback := by
  by_cases h : i < n + 1 - m <;> simp [h]

@[simp]
theorem getD_toArray_rcc_eq_add {m n i fallback : Nat} (h : i < n + 1 - m) :
    (m...=n).toArray.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toArray_rcc_eq_fallback {m n i fallback : Nat} (h : n + 1 ≤ i + m) :
    (m...=n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a...=b` by
varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b < a`, the statement holds for the empty range {lean}`a...=b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, the
statement holds for nonempty ranges {lean}`a...b` if it holds for the smaller range
{lean}`(a + 1)...=b`.

The following is an example reproving {name}`length_toList_rcc`.

```lean
example (a b : Nat) : (a...=b).toList.length = b + 1 - a := by
  induction a, b using Nat.induct_rcc_left
  case base =>
    simp only [Nat.toList_rcc_eq_nil, List.length_nil, *]; omega
  case step =>
    simp only [Nat.toList_rcc_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_rcc_left (motive : Nat → Nat → Prop)
    (base : ∀ a b, b < a → motive a b)
    (step : ∀ a b, a ≤ b → motive (a + 1) b → motive a b)
    (a b : Nat) : motive a b := by
  induction h : b + 1 - a generalizing a b
  · apply base; omega
  · rename_i d ih
    apply step
    · omega
    · apply ih; omega

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a...=b` by
varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a`, the statement holds for the subsingleton range {lean}`a...=b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, if the
statement holds for {lean}`a...=b`, it also holds for the larger range {lean}`a...=(b + 1)`.

The following is an example reproving {name}`length_toList_rcc`.

```lean
example (a b : Nat) : (a...=b).toList.length = b + 1 - a := by
  induction a, b using Nat.induct_rcc_right
  case base a b hge =>
    by_cases h : b < a
    · simp only [Nat.toList_rcc_eq_nil, List.length_nil, *]
      omega
    · have : b = a := by omega
      simp only [Nat.toList_rcc_eq_singleton, List.length_singleton,
        Nat.add_sub_cancel_left, *]
  case step a b hle ih =>
    rw [Nat.toList_rcc_succ_right_eq_append (by omega), List.length_append,
      List.length_singleton, ih] <;> omega
```
-/
theorem induct_rcc_right (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Nat) : motive a b := by
  induction h : b - a generalizing a b
  · apply base; omega
  · rename_i d ih
    match b with
    | 0 => apply base; omega
    | n + 1 =>
      apply step
      · omega
      · apply ih
        omega

theorem toList_roo_eq_toList_rco {m n : Nat} :
    (m<...n).toList = ((m + 1)...n).toList := by
  simp [Roo.toList_eq_match_rco]

@[simp]
theorem toList_toArray_roo {m n : Nat} :
    (m<...n).toArray.toList = (m<...n).toList :=
  Roo.toList_toArray

@[simp]
theorem toArray_toList_roo {m n : Nat} :
    (m<...n).toList.toArray = (m<...n).toArray :=
  Roo.toArray_toList

theorem toList_roo_eq_if {m n : Nat} :
    (m<...n).toList = if m + 1 < n then (m + 1) :: ((m + 1)<...n).toList else [] := by
  simp only [toList_roo_eq_toList_rco]
  rw [toList_rco_eq_if]

theorem toList_roo_succ_succ {m n : Nat} :
    ((m+1)<...(n+1)).toList = (m<...n).toList.map (· + 1) := by
  simp [toList_roo_eq_toList_rco, toList_rco_succ_succ]

theorem toList_roo_succ_right_eq_cons_map {m n : Nat} (h : m < n) :
    (m<...(n + 1)).toList = (m + 1) :: (m<...n).toList.map (· + 1) := by
  simp [toList_roo_eq_toList_rco, toList_rco_succ_right_eq_cons_map h]

@[simp]
theorem toList_roo_eq_nil_iff {m n : Nat} :
    (m<...n).toList = [] ↔ n ≤ m + 1 := by
  simp [toList_roo_eq_toList_rco]

theorem toList_roo_ne_nil_iff {m n : Nat} :
    (m<...n).toList ≠ [] ↔ m + 1 < n := by
  simp

@[simp 1001]
theorem toList_roo_eq_nil {m n : Nat} (h : n ≤ m + 1) :
    (m<...n).toList = [] := by
  simp [h]

@[simp]
theorem toList_roo_eq_singleton_iff {m n : Nat} :
    (m<...n).toList = [k] ↔ n = m + 2 ∧ m + 1 = k := by
  simp [toList_roo_eq_toList_rco]; omega

@[simp 1001]
theorem toList_roo_eq_singleton {m n : Nat} (h : n = m + 2) :
    (m<...n).toList = [m + 1] := by
  simp [h]

@[simp]
theorem toList_roo_eq_cons_iff {m n a : Nat} :
    (m<...n).toList = a :: xs ↔ m + 1 = a ∧ m + 1 < n ∧ ((m + 1)<...n).toList = xs := by
  simp [toList_roo_eq_toList_rco]

theorem toList_roo_eq_cons {m n : Nat} (h : m + 1 < n) :
    (m<...n).toList = (m + 1) :: ((m + 1)<...n).toList := by
  simp; omega

@[simp 1001]
theorem toList_roo_zero_right_eq_nil {m : Nat} :
    (m<...0).toList = [] := by
  simp

@[simp 1001]
theorem toList_roo_one_right_eq_nil {m : Nat} :
    (m<...1).toList = [] := by
  simp

theorem map_add_toList_roo {m n k : Nat} :
    (m<...n).toList.map (· + k) = ((m + k)<...(n + k)).toList := by
  simp [toList_roo_eq_toList_rco, map_add_toList_rco, show m + 1 + k = m + k + 1 by omega]

theorem map_add_toList_roo' {m n k : Nat} :
    (m<...n).toList.map (k + ·) = ((k + m)<...(k + n)).toList := by
  simp [toList_roo_eq_toList_rco, map_add_toList_rco', show k + (m + 1) = k + m + 1 by omega]

theorem toList_roo_add_right_eq_map {m n : Nat} :
    (m<...(m + 1 + n)).toList = (0...n).toList.map (· + m + 1) := by
  simp [toList_roo_eq_toList_rco, toList_rco_add_right_eq_map,
    show ∀ a, a + (m + 1) = (a + m) + 1 by omega]

theorem toList_roo_succ_right_eq_append {m n : Nat} (h : m < n) :
    (m<...(n + 1)).toList = (m<...n).toList ++ [n] := by
  simp [toList_roo_eq_toList_rco, toList_rco_succ_right_eq_append h]

@[simp]
theorem toList_roo_eq_append {m n : Nat} (h : m + 1 < n) :
    (m<...n).toList = (m<...(n - 1)).toList ++ [n - 1] := by
  simp [toList_roo_eq_toList_rco, toList_rco_eq_append h]

@[simp]
theorem getElem_toList_roo {m n i : Nat} (_h : i < (m<...n).toList.length) :
    (m<...n).toList[i]'_h = m + 1 + i := by
  simp [toList_roo_eq_toList_rco]

theorem getElem?_toList_roo {m n i : Nat} :
    (m<...n).toList[i]? = if i < n - (m + 1) then some (m + 1 + i) else none := by
  simp [toList_roo_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem getElem?_toList_roo_eq_some_iff {m n i : Nat} :
    (m<...n).toList[i]? = some k ↔ i < n - (m + 1) ∧ m + 1 + i = k := by
  simp [toList_roo_eq_toList_rco]

@[simp]
theorem getElem?_toList_roo_eq_none_iff {m n i : Nat} :
    (m<...n).toList[i]? = none ↔ n ≤ i + (m + 1) := by
  simp [toList_roo_eq_toList_rco]

@[simp]
theorem isSome_getElem?_toList_roo_eq {m n i : Nat} :
    (m<...n).toList[i]?.isSome = (i < n - (m + 1)) := by
  simp [toList_roo_eq_toList_rco]

@[simp]
theorem isNone_getElem?_toList_roo_eq {m n i : Nat} :
    (m<...n).toList[i]?.isNone = (n ≤ i + (m + 1)) := by
  simp [toList_roo_eq_toList_rco]

@[simp 1001]
theorem getElem?_toList_roo_eq_some {m n i : Nat} (h : i < n - (m + 1)) :
    (m<...n).toList[i]? = some (m + 1 + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toList_roo_eq_none {m n i : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toList[i]? = none := by
  simp [h, toList_roo_eq_toList_rco]

theorem getElem!_toList_roo {m n i : Nat} :
    (m<...n).toList[i]! = if i < n - (m + 1) then (m + 1 + i) else 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_roo, Nat.default_eq_zero]
  split <;> simp

@[simp 1001]
theorem getElem!_toList_roo_eq_add {m n i : Nat} (h : i < n - (m + 1)) :
    (m<...n).toList[i]! = m + 1 + i := by
  simp [h]

@[simp 1001]
theorem getElem!_toList_roo_eq_zero {m n i : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_roo_eq_zero_iff {m n i : Nat} :
    (m<...n).toList[i]! = 0 ↔ n ≤ i + (m + 1) := by
  rw [toList_roo_eq_toList_rco, getElem!_toList_rco_eq_zero_iff]
  omega

theorem zero_lt_getElem!_toList_roo_iff {m n i : Nat} :
    0 < (m<...n).toList[i]! ↔ i < n - (m + 1) := by
  rw [toList_roo_eq_toList_rco, zero_lt_getElem!_toList_rco_iff]
  omega

theorem getD_toList_roo {m n i fallback : Nat} :
    (m<...n).toList.getD i fallback = if i < n - (m + 1) then (m + 1 + i) else fallback := by
  by_cases h : i < n - (m + 1) <;> simp [h, toList_roo_eq_toList_rco]

@[simp]
theorem getD_toList_roo_eq_add {m n i fallback : Nat} (h : i < n - (m + 1)) :
    (m<...n).toList.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toList_roo_eq_fallback {m n i fallback : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_roo_eq_toArray_rco {m n : Nat} :
    (m<...n).toArray = ((m + 1)...n).toArray := by
  simp [Roo.toArray_eq_match_rco]

theorem toArray_roo_eq_if {m n : Nat} :
    (m<...n).toArray = if m + 1 < n then #[m + 1] ++ ((m + 1)<...n).toArray else #[] := by
  simp only [toArray_roo_eq_toArray_rco]
  rw [toArray_rco_eq_if]

theorem toArray_roo_succ_succ {m n : Nat} :
    ((m+1)<...(n+1)).toArray = (m<...n).toArray.map (· + 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_succ_succ]

theorem toArray_roo_succ_right_eq_append_map {m n : Nat} (h : m < n) :
    (m<...(n + 1)).toArray = #[m + 1] ++ (m<...n).toArray.map (· + 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_succ_right_eq_append_map h]

@[simp]
theorem toArray_roo_eq_nil_iff {m n : Nat} :
    (m<...n).toArray = #[] ↔ n ≤ m + 1 := by
  simp [toArray_roo_eq_toArray_rco]

theorem toArray_roo_ne_nil_iff {m n : Nat} :
    (m<...n).toArray ≠ #[] ↔ m + 1 < n := by
  simp

@[simp 1001]
theorem toArray_roo_eq_nil {m n : Nat} (h : n ≤ m + 1) :
    (m<...n).toArray = #[] := by
  simp [h]

@[simp]
theorem toArray_roo_eq_singleton_iff {m n : Nat} :
    (m<...n).toArray = #[k] ↔ n = m + 2 ∧ m + 1 = k := by
  simp [toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem toArray_roo_eq_singleton {m n : Nat} (h : n = m + 2) :
    (m<...n).toArray = #[m + 1] := by
  simp [h]

@[simp]
theorem toArray_roo_eq_singleton_append_iff {m n a : Nat} :
    (m<...n).toArray = #[a] ++ xs ↔ m + 1 = a ∧ m + 1 < n ∧ ((m + 1)<...n).toArray = xs := by
  simp [toArray_roo_eq_toArray_rco]

theorem toArray_roo_eq_singleton_append {m n : Nat} (h : m + 1 < n) :
    (m<...n).toArray = #[m + 1] ++ ((m + 1)<...n).toArray := by
  simp; omega

@[simp 1001]
theorem toArray_roo_zero_right_eq_nil {m : Nat} :
    (m<...0).toArray = #[] := by
  simp

@[simp 1001]
theorem toArray_roo_one_right_eq_nil {m : Nat} :
    (m<...1).toArray = #[] := by
  simp

theorem map_add_toArray_roo {m n k : Nat} :
    (m<...n).toArray.map (· + k) = ((m + k)<...(n + k)).toArray := by
  simp [toArray_roo_eq_toArray_rco, map_add_toArray_rco, show m + 1 + k = m + k + 1 by omega]

theorem map_add_toArray_roo' {m n k : Nat} :
    (m<...n).toArray.map (k + ·) = ((k + m)<...(k + n)).toArray := by
  simp [toArray_roo_eq_toArray_rco, map_add_toArray_rco', show k + (m + 1) = k + m + 1 by omega]

theorem toArray_roo_add_right_eq_map {m n : Nat} :
    (m<...(m + 1 + n)).toArray = (0...n).toArray.map (· + m + 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_add_right_eq_map,
    show ∀ a, a + (m + 1) = (a + m) + 1 by omega]

theorem toArray_roo_succ_right_eq_push {m n : Nat} (h : m < n) :
    (m<...(n + 1)).toArray = (m<...n).toArray.push n := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_succ_right_eq_push h]

@[simp]
theorem toArray_roo_eq_push {m n : Nat} (h : m + 1 < n) :
    (m<...n).toArray = (m<...(n - 1)).toArray.push (n - 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_eq_push h]

@[simp]
theorem getElem_toArray_roo {m n i : Nat} (_h : i < (m<...n).toArray.size) :
    (m<...n).toArray[i]'_h = m + 1 + i := by
  simp [toArray_roo_eq_toArray_rco]

theorem getElem?_toArray_roo {m n i : Nat} :
    (m<...n).toArray[i]? = if i < n - (m + 1) then some (m + 1 + i) else none := by
  simp [toArray_roo_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem getElem?_toArray_roo_eq_some_iff {m n i : Nat} :
    (m<...n).toArray[i]? = some k ↔ i < n - (m + 1) ∧ m + 1 + i = k := by
  simp [toArray_roo_eq_toArray_rco]

@[simp]
theorem getElem?_toArray_roo_eq_none_iff {m n i : Nat} :
    (m<...n).toArray[i]? = none ↔ n ≤ i + (m + 1) := by
  simp [toArray_roo_eq_toArray_rco]

@[simp]
theorem isSome_getElem?_toArray_roo_eq {m n i : Nat} :
    (m<...n).toArray[i]?.isSome = (i < n - (m + 1)) := by
  simp [toArray_roo_eq_toArray_rco]

@[simp]
theorem isNone_getElem?_toArray_roo_eq {m n i : Nat} :
    (m<...n).toArray[i]?.isNone = (n ≤ i + (m + 1)) := by
  simp [toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem getElem?_toArray_roo_eq_some {m n i : Nat} (h : i < n - (m + 1)) :
    (m<...n).toArray[i]? = some (m + 1 + i) := by
  simp [h, toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem getElem?_toArray_roo_eq_none {m n i : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toArray[i]? = none := by
  simp [h, toArray_roo_eq_toArray_rco]

theorem getElem!_toArray_roo {m n i : Nat} :
    (m<...n).toArray[i]! = if i < n - (m + 1) then (m + 1 + i) else 0 := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, getElem?_toArray_roo,
    Nat.default_eq_zero]
  split <;> simp

@[simp 1001]
theorem getElem!_toArray_roo_eq_add {m n i : Nat} (h : i < n - (m + 1)) :
    (m<...n).toArray[i]! = m + 1 + i := by
  simp [h, toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem getElem!_toArray_roo_eq_zero {m n i : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toArray[i]! = 0 := by
  simp [h, toArray_roo_eq_toArray_rco]

theorem getElem!_toArray_roo_eq_zero_iff {m n i : Nat} :
    (m<...n).toArray[i]! = 0 ↔ n ≤ i + (m + 1) := by
  rw [toArray_roo_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff]
  omega

theorem zero_lt_getElem!_toArray_roo_iff {m n i : Nat} :
    0 < (m<...n).toArray[i]! ↔ i < n - (m + 1) := by
  rw [toArray_roo_eq_toArray_rco, zero_lt_getElem!_toArray_rco_iff]
  omega

theorem getD_toArray_roo {m n i fallback : Nat} :
    (m<...n).toArray.getD i fallback = if i < n - (m + 1) then (m + 1 + i) else fallback := by
  by_cases h : i < n - (m + 1) <;> simp [h, toArray_roo_eq_toArray_rco]

@[simp]
theorem getD_toArray_roo_eq_add {m n i fallback : Nat} (h : i < n - (m + 1)) :
    (m<...n).toArray.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toArray_roo_eq_fallback {m n i fallback : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a<...b` by
varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a + 1`, the statement holds for the empty range {lean}`a<...b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, the
statement holds for nonempty ranges {lean}`a<...b` if it holds for the smaller range
{lean}`(a + 1)<...b`.

The following is an example reproving {name}`length_toList_roo`.

```lean
example (a b : Nat) : (a<...b).toList.length = b - a - 1 := by
  induction a, b using Nat.induct_roo_left
  case base =>
    simp only [Nat.toList_roo_eq_nil, List.length_nil, *]; omega
  case step =>
    simp only [Nat.toList_roo_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_roo_left (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a + 1 → motive a b)
    (step : ∀ a b, a + 1 < b → motive (a + 1) b → motive a b)
    (a b : Nat) : motive a b := by
  induction h : b - a - 1 generalizing a b
  · apply base; omega
  · rename_i d ih
    apply step
    · omega
    · apply ih; omega

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a<...b` by
varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a + 1`, the statement holds for the empty range {lean}`a<...b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, if the
statement holds for {lean}`a<...b`, it also holds for the larger range {lean}`a<...(b + 1)`.

The following is an example reproving {name}`length_toList_roo`.

```lean
example (a b : Nat) : (a<...b).toList.length = b - a - 1 := by
  induction a, b using Nat.induct_roo_right
  case base =>
    simp only [Nat.toList_roo_eq_nil, List.length_nil, *]; omega
  case step a b hle ih =>
    rw [Nat.toList_roo_eq_append (by omega),
      List.length_append, List.length_singleton, Nat.add_sub_cancel, ih]
    omega
```
-/
theorem induct_roo_right (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a + 1 → motive a b)
    (step : ∀ a b, a + 1 ≤ b → motive a b → motive a (b + 1))
    (a b : Nat) : motive a b := by
  induction h : b - a - 1 generalizing a b
  · apply base; omega
  · rename_i d ih
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
    apply step
    · omega
    · apply ih
      omega

theorem toList_roc_eq_toList_roo {m n : Nat} :
    (m<...=n).toList = (m<...(n + 1)).toList := by
  simp [Roc.toList_eq_toList_roo]

theorem toList_roc_eq_toList_rco {m n : Nat} :
    (m<...=n).toList = ((m + 1)...(n + 1)).toList := by
  simp [toList_roc_eq_toList_roo, toList_roo_eq_toList_rco]

theorem toList_roc_eq_toList_rcc {m n : Nat} :
    (m<...=n).toList = ((m + 1)...=n).toList := by
  simp [toList_roc_eq_toList_rco, toList_rcc_eq_toList_rco]

@[simp]
theorem toList_toArray_roc {m n : Nat} :
    (m<...=n).toArray.toList = (m<...=n).toList :=
  Roc.toList_toArray

@[simp]
theorem toArray_toList_roc {m n : Nat} :
    (m<...=n).toList.toArray = (m<...=n).toArray :=
  Roc.toArray_toList

theorem toList_roc_eq_if {m n : Nat} :
    (m<...=n).toList = if m + 1 ≤ n then (m + 1) :: ((m + 1)<...=n).toList else [] := by
  rw [toList_roc_eq_toList_rco, toList_roc_eq_toList_rco, toList_rco_eq_if]
  split <;> (simp; omega)

theorem toList_roc_succ_succ {m n : Nat} :
    ((m+1)<...=(n+1)).toList = (m<...=n).toList.map (· + 1) := by
  simp [← succ_eq, toList_roc_eq_toList_rco, Rco.toList_succ_succ_eq_map]

theorem toList_roc_succ_right_eq_cons_map {m n : Nat} (h : m ≤ n) :
    (m<...=(n + 1)).toList = (m + 1) :: (m<...=n).toList.map (· + 1) := by
  simp [toList_roc_eq_toList_rco, toList_rco_succ_right_eq_cons_map, h]

@[simp]
theorem toList_roc_eq_nil_iff {m n : Nat} :
    (m<...=n).toList = [] ↔ n ≤ m := by
  simp [toList_roc_eq_toList_rco]

theorem toList_roc_ne_nil_iff {m n : Nat} :
    (m<...=n).toList ≠ [] ↔ m < n := by
  simp

@[simp 1001]
theorem toList_roc_eq_nil {m n : Nat} (h : n ≤ m) :
    (m<...=n).toList = [] := by
  simp; omega

@[simp]
theorem toList_roc_eq_singleton_iff {m n : Nat} :
    (m<...=n).toList = [k] ↔ n = m + 1 ∧ m + 1 = k := by
  simp [toList_roc_eq_toList_rco]; omega

@[simp 1001]
theorem toList_roc_eq_singleton {m n : Nat} (h : n = m + 1) :
    (m<...=n).toList = [m + 1] := by
  simp [h]

@[simp]
theorem toList_roc_eq_cons_iff {m n a : Nat} :
    (m<...=n).toList = a :: xs ↔ m + 1 = a ∧ m < n ∧ ((m + 1)<...=n).toList = xs := by
  simp [toList_roc_eq_toList_rco]

theorem toList_roc_eq_cons {m n : Nat} (h : m < n) :
    (m<...=n).toList = (m + 1) :: ((m + 1)<...=n).toList := by
  simp; omega

theorem map_add_toList_roc {m n k : Nat} :
    (m<...=n).toList.map (· + k) = ((m + k)<...=(n + k)).toList := by
  simp [toList_roc_eq_toList_rco, map_add_toList_rco, show ∀ l, l + 1 + k = l + k + 1 by omega]

theorem map_add_toList_roc' {m n k : Nat} :
    (m<...=n).toList.map (k + ·) = ((k + m)<...=(k + n)).toList := by
  simp [toList_roc_eq_toList_rco, map_add_toList_rco', ← Nat.add_assoc]

theorem toList_roc_add_right_eq_map {m n : Nat} :
    (m<...=(m + n)).toList = (0...n).toList.map (· + m + 1) := by
  simp [toList_roc_eq_toList_rco, show m + n + 1 = m + 1 + n by omega, toList_rco_add_right_eq_map,
    ← Nat.add_assoc]

theorem toList_roc_succ_right_eq_append {m n : Nat} (h : m ≤ n) :
    (m<...=(n + 1)).toList = (m<...=n).toList ++ [n + 1] := by
  simp [toList_roc_eq_toList_rco, toList_rco_succ_right_eq_append, h]

theorem toList_roc_add_succ_right_eq_append {m n : Nat} :
    (m<...=(m + n + 1)).toList = (m<...=(m + n)).toList ++ [m + n + 1] := by
  rw [toList_roc_succ_right_eq_append (by omega)]

theorem toList_roc_add_succ_right_eq_append' {m n : Nat} :
    (m<...=(m + (n + 1))).toList = (m<...=(m + n)).toList ++ [m + n + 1] := by
  rw [← Nat.add_assoc, toList_roc_add_succ_right_eq_append]

theorem toList_roc_eq_append {m n : Nat} (h : m < n) :
    (m<...=n).toList = (m<...=(n - 1)).toList ++ [n] := by
  simp [toList_roc_eq_toList_rco, toList_rco_eq_append (Nat.succ_le_succ h),
    Nat.sub_add_cancel (n := n) (m := 1) (by omega)]

theorem toList_roc_add_add_eq_append {m n k : Nat} :
    (m<...=(m + n + k)).toList = (m<...=(m + n)).toList ++ ((m + n)<...=(m + n + k)).toList := by
  simp only [toList_roc_eq_toList_rco]
  rw [← toList_rco_append_toList_rco] <;> omega

theorem toList_roc_append_toList_roc {l m n : Nat} (h : l ≤ m) (h' : m ≤ n) :
    (l<...=m).toList ++ (m<...=n).toList = (l<...=n).toList := by
  simp [toList_roc_eq_toList_rco,
    toList_rco_append_toList_rco (Nat.succ_le_succ h) (Nat.succ_le_succ h')]

@[simp]
theorem getElem_toList_roc {m n i : Nat} (_h : i < (m<...=n).toList.length) :
    (m<...=n).toList[i]'_h = m + 1 + i := by
  simp [toList_roc_eq_toList_rco]

theorem getElem?_toList_roc {m n i : Nat} :
    (m<...=n).toList[i]? = if i < n - m then some (m + 1 + i) else none := by
  simp [toList_roc_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem getElem?_toList_roc_eq_some_iff {m n i : Nat} :
    (m<...=n).toList[i]? = some k ↔ i < n - m ∧ m + 1 + i = k := by
  simp [toList_roc_eq_toList_rco]

@[simp]
theorem getElem?_toList_roc_eq_none_iff {m n i : Nat} :
    (m<...=n).toList[i]? = none ↔ n ≤ i + m := by
  simp

@[simp]
theorem isSome_getElem?_toList_roc_eq {m n i : Nat} :
    (m<...=n).toList[i]?.isSome = (i < n - m) := by
  simp

@[simp]
theorem isNone_getElem?_toList_roc_eq {m n i : Nat} :
    (m<...=n).toList[i]?.isNone = (n ≤ i + m) := by
  simp

@[simp]
theorem getElem?_toList_roc_eq_some {m n i : Nat} (h : i < n - m) :
    (m<...=n).toList[i]? = some (m + 1 + i) := by
  simp [h]

@[simp]
theorem getElem?_toList_roc_eq_none {m n i : Nat} (h : n ≤ i + m) :
    (m<...=n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_roc {m n i : Nat} :
    (m<...=n).toList[i]! = if i < n - m then (m + 1 + i) else 0 := by
  rw [toList_roc_eq_toList_rco, getElem!_toList_rco]
  simp

@[simp]
theorem getElem!_toList_roc_eq_add {m n i : Nat} (h : i < n - m) :
    (m<...=n).toList[i]! = m + 1 + i := by
  simp [h]

@[simp]
theorem getElem!_toList_roc_eq_zero {m n i : Nat} (h : n ≤ i + m) :
    (m<...=n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_roc_eq_zero_iff {m n i : Nat} :
    (m<...=n).toList[i]! = 0 ↔ n ≤ i + m := by
  simp only [toList_roc_eq_toList_rco, getElem!_toList_rco_eq_zero_iff]
  omega

theorem zero_lt_getElem!_toList_roc_iff {m n i : Nat} :
    0 < (m<...=n).toList[i]! ↔ i < n - m := by
  simp only [toList_roc_eq_toList_rco, zero_lt_getElem!_toList_rco_iff]
  omega

theorem getD_toList_roc {m n i fallback : Nat} :
    (m<...=n).toList.getD i fallback = if i < n - m then (m + 1 + i) else fallback := by
  by_cases h : i < n - m <;> simp [h]

@[simp]
theorem getD_toList_roc_eq_add {m n i fallback : Nat} (h : i < n - m) :
    (m<...=n).toList.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toList_roc_eq_fallback {m n i fallback : Nat} (h : n ≤ i + m) :
    (m<...=n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_roc_eq_toArray_rcc {m n : Nat} :
    (m<...=n).toArray = ((m + 1)...=n).toArray := by
  rw [← toArray_toList_roc, toList_roc_eq_toList_rcc, toArray_toList_rcc]

theorem toArray_roc_eq_toArray_roo {m n : Nat} :
    (m<...=n).toArray = (m<...(n + 1)).toArray := by
  rw [← toArray_toList_roc, toList_roc_eq_toList_roo, toArray_toList_roo]

theorem toArray_roc_eq_toArray_rco {m n : Nat} :
    (m<...=n).toArray = ((m + 1)...(n + 1)).toArray := by
  rw [← toArray_toList_roc, toList_roc_eq_toList_rco, toArray_toList_rco]

theorem toArray_roc_eq_if {m n : Nat} :
    (m<...=n).toArray = if m + 1 ≤ n then #[m + 1] ++ ((m + 1)<...=n).toArray else #[] := by
  rw [toArray_roc_eq_toArray_rco, toArray_roc_eq_toArray_rco, toArray_rco_eq_if]
  split <;> (simp; omega)

theorem toArray_roc_succ_succ {m n : Nat} :
    ((m+1)<...=(n+1)).toArray = (m<...=n).toArray.map (· + 1) := by
  simp only [← toArray_toList_roc, toList_roc_succ_succ, List.map_toArray]

theorem toArray_roc_succ_right_eq_append_map {m n : Nat} (h : m ≤ n) :
    (m<...=(n + 1)).toArray = #[m + 1] ++ (m<...=n).toArray.map (· + 1) := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_succ_right_eq_append_map, h]

@[simp]
theorem toArray_roc_eq_nil_iff {m n : Nat} :
    (m<...=n).toArray = #[] ↔ n ≤ m := by
  simp [toArray_roc_eq_toArray_rco]

theorem toArray_roc_ne_nil_iff {m n : Nat} :
    (m<...=n).toArray ≠ #[] ↔ m < n := by
  simp

@[simp 1001]
theorem toArray_roc_eq_nil {m n : Nat} (h : n ≤ m) :
    (m<...=n).toArray = #[] := by
  simp; omega

@[simp]
theorem toArray_roc_eq_singleton_iff {m n : Nat} :
    (m<...=n).toArray = #[k] ↔ n = m + 1 ∧ m + 1 = k := by
  simp [toArray_roc_eq_toArray_rco]

@[simp 1001]
theorem toArray_roc_eq_singleton {m n : Nat} (h : n = m + 1) :
    (m<...=n).toArray = #[m + 1] := by
  simp [h]

@[simp]
theorem toArray_roc_eq_singleton_append_iff {m n a : Nat} :
    (m<...=n).toArray = #[a] ++ xs ↔ m + 1 = a ∧ m < n ∧ ((m + 1)<...=n).toArray = xs := by
  simp [toArray_roc_eq_toArray_rco]

theorem toArray_roc_eq_singleton_append {m n : Nat} (h : m < n) :
    (m<...=n).toArray = #[m + 1] ++ ((m + 1)<...=n).toArray := by
  simp; omega

theorem map_add_toArray_roc {m n k : Nat} :
    (m<...=n).toArray.map (· + k) = ((m + k)<...=(n + k)).toArray := by
  simp [toArray_roc_eq_toArray_rco, map_add_toArray_rco, show ∀ l, l + 1 + k = l + k + 1 by omega]

theorem map_add_toArray_roc' {m n k : Nat} :
    (m<...=n).toArray.map (k + ·) = ((k + m)<...=(k + n)).toArray := by
  simp [toArray_roc_eq_toArray_rco, map_add_toArray_rco', ← Nat.add_assoc]

theorem toArray_roc_add_right_eq_map {m n : Nat} :
    (m<...=(m + n)).toArray = (0...n).toArray.map (· + m + 1) := by
  simp [toArray_roc_eq_toArray_rco, show m + n + 1 = m + 1 + n by omega,
    toArray_rco_add_right_eq_map, ← Nat.add_assoc]

theorem toArray_roc_succ_right_eq_push {m n : Nat} (h : m ≤ n) :
    (m<...=(n + 1)).toArray = (m<...=n).toArray.push (n + 1) := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_succ_right_eq_push, h]

theorem toArray_roc_add_succ_right_eq_push {m n : Nat} :
    (m<...=(m + n + 1)).toArray = (m<...=(m + n)).toArray.push (m + n + 1) := by
  rw [toArray_roc_succ_right_eq_push (by omega)]

theorem toArray_roc_add_succ_right_eq_push' {m n : Nat} :
    (m<...=(m + (n + 1))).toArray = (m<...=(m + n)).toArray.push (m + n + 1) := by
  rw [← Nat.add_assoc, toArray_roc_add_succ_right_eq_push]

theorem toArray_roc_eq_push {m n : Nat} (h : m < n) :
    (m<...=n).toArray = (m<...=(n - 1)).toArray.push n := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_eq_push (Nat.succ_le_succ h),
    Nat.sub_add_cancel (n := n) (m := 1) (by omega)]

theorem toArray_roc_add_add_eq_append {m n k : Nat} :
    (m<...=(m + n + k)).toArray = (m<...=(m + n)).toArray ++ ((m + n)<...=(m + n + k)).toArray := by
  simp only [toArray_roc_eq_toArray_rco]
  rw [← toArray_rco_append_toArray_rco] <;> omega

theorem toArray_roc_append_toArray_roc {l m n : Nat} (h : l ≤ m) (h' : m ≤ n) :
    (l<...=m).toArray ++ (m<...=n).toArray = (l<...=n).toArray := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_append_toArray_rco (Nat.succ_le_succ h) (Nat.succ_le_succ h')]

@[simp]
theorem getElem_toArray_roc {m n i : Nat} (_h : i < (m<...=n).toArray.size) :
    (m<...=n).toArray[i]'_h = m + 1 + i := by
simp [toArray_roc_eq_toArray_rco]

theorem getElem?_toArray_roc {m n i : Nat} :
    (m<...=n).toArray[i]? = if i < n - m then some (m + 1 + i) else none := by
  simp [toArray_roc_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem getElem?_toArray_roc_eq_some_iff {m n i : Nat} :
    (m<...=n).toArray[i]? = some k ↔ i < n - m ∧ m + 1 + i = k := by
  simp [toArray_roc_eq_toArray_rco]

@[simp]
theorem getElem?_toArray_roc_eq_none_iff {m n i : Nat} :
    (m<...=n).toArray[i]? = none ↔ n ≤ i + m := by
  simp

@[simp]
theorem isSome_getElem?_toArray_roc_eq {m n i : Nat} :
    (m<...=n).toArray[i]?.isSome = (i < n - m) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_roc_eq {m n i : Nat} :
    (m<...=n).toArray[i]?.isNone = (n ≤ i + m) := by
  simp

@[simp]
theorem getElem?_toArray_roc_eq_some {m n i : Nat} (h : i < n - m) :
    (m<...=n).toArray[i]? = some (m + 1 + i) := by
  simp [h]

@[simp]
theorem getElem?_toArray_roc_eq_none {m n i : Nat} (h : n ≤ i + m) :
    (m<...=n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_roc {m n i : Nat} :
    (m<...=n).toArray[i]! = if i < n - m then (m + 1 + i) else 0 := by
  rw [toArray_roc_eq_toArray_rco, getElem!_toArray_rco]
  simp

@[simp]
theorem getElem!_toArray_roc_eq_add {m n i : Nat} (h : i < n - m) :
    (m<...=n).toArray[i]! = m + 1 + i := by
  simp [h]

@[simp]
theorem getElem!_toArray_roc_eq_zero {m n i : Nat} (h : n ≤ i + m) :
    (m<...=n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_roc_eq_zero_iff {m n i : Nat} :
    (m<...=n).toArray[i]! = 0 ↔ n ≤ i + m := by
  simp only [toArray_roc_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff]
  omega

theorem zero_lt_getElem!_toArray_roc_iff {m n i : Nat} :
    0 < (m<...=n).toArray[i]! ↔ i < n - m := by
  simp only [toArray_roc_eq_toArray_rco, zero_lt_getElem!_toArray_rco_iff]
  omega

theorem getD_toArray_roc {m n i fallback : Nat} :
    (m<...=n).toArray.getD i fallback = if i < n - m then (m + 1 + i) else fallback := by
  by_cases h : i < n - m <;> simp [h]

@[simp]
theorem getD_toArray_roc_eq_add {m n i fallback : Nat} (h : i < n - m) :
    (m<...=n).toArray.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toArray_roc_eq_fallback {m n i fallback : Nat} (h : n ≤ i + m) :
    (m<...=n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a<...=b`
by varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a<...=b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, the
statement holds for nonempty ranges {lean}`a<...=b` if it holds for the smaller range
{lean}`(a + 1)<...=b`.

The following is an example reproving {name}`length_toList_roc`.

```lean
example (a b : Nat) : (a<...=b).toList.length = b - a := by
  induction a, b using Nat.induct_roc_left
  case base =>
    simp only [Nat.toList_roc_eq_nil, List.length_nil, *]; omega
  case step =>
    simp only [Nat.toList_roc_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_roc_left (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a < b → motive (a + 1) b → motive a b)
    (a b : Nat) : motive a b :=
  induct_rco_left motive base step a b

/--
Induction principle for proving properties of {name}`Nat`-based ranges of the form {lean}`a<...=b`
by varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Nat` and {given}`b : Nat` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a<...=b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, if the
statement holds for {lean}`a<...=b`, it also holds for the larger range {lean}`a<...=(b + 1)`.

The following is an example reproving {name}`length_toList_roc`.

```lean
example (a b : Nat) : (a<...=b).toList.length = b - a := by
  induction a, b using Nat.induct_roc_right
  case base =>
    simp only [Nat.toList_roc_eq_nil, List.length_nil, *]; omega
  case step a b hle ih =>
    rw [Nat.toList_roc_eq_append (by omega),
      List.length_append, List.length_singleton, Nat.add_sub_cancel, ih]
    omega
```
-/
theorem induct_roc_right (motive : Nat → Nat → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Nat) : motive a b :=
  induct_rco_right motive base step a b

theorem toList_rio_eq_toList_rco {n : Nat} :
    (*...n).toList = (0...n).toList := by
  simp [Rio.toList_eq_match_rco]

@[simp]
theorem toList_toArray_rio {n : Nat} :
    (*...n).toArray.toList = (*...n).toList :=
  Rio.toList_toArray

@[simp]
theorem toArray_toList_rio {n : Nat} :
    (*...n).toList.toArray = (*...n).toArray :=
  Rio.toArray_toList

theorem toList_rio_eq_if {n : Nat} :
    (*...n).toList = if 0 < n then (*...(n - 1)).toList ++ [n - 1] else [] := by
  simp only [toList_rio_eq_toList_rco]
  by_cases h : 0 < n
  · rw [toList_rco_eq_append h, if_pos h]
  · simp [*]; omega

theorem toList_rio_succ {n : Nat} :
    (*...(n+1)).toList = (*...n).toList ++ [n] := by
  rw [toList_rio_eq_if, if_pos (by omega)]
  simp

@[simp]
theorem toList_rio_eq_nil_iff {n : Nat} :
    (*...n).toList = [] ↔ n = 0 := by
  simp [toList_rio_eq_toList_rco]

theorem toList_rio_ne_nil_iff {n : Nat} :
    (*...n).toList ≠ [] ↔ 0 < n := by
  simp [Nat.pos_iff_ne_zero]

@[simp]
theorem toList_rio_eq_nil {n : Nat} (h : n = 0) :
    (*...n).toList = [] := by
  simp [h]

@[simp]
theorem toList_rio_eq_singleton_iff {n : Nat} :
    (*...n).toList = [k] ↔ n = 1 ∧ 0 = k := by
  simp [toList_rio_eq_toList_rco]; omega

@[simp]
theorem toList_rio_one_eq_singleton :
    (*...1).toList = [0] := by
  simp

@[simp]
theorem toList_rio_eq_cons_iff {n a : Nat} :
    (*...n).toList = a :: xs ↔ 0 = a ∧ 0 < n ∧ (1...n).toList = xs := by
  simp [toList_rio_eq_toList_rco]

theorem toList_rio_eq_cons {n : Nat} (h : 0 < n) :
    (*...n).toList = 0 :: (1...n).toList := by
  simp [h]

@[simp]
theorem toList_rio_zero_right_eq_nil {m : Nat} :
    (m...0).toList = [] := by
  simp

theorem map_add_toList_rio {n k : Nat} :
    (*...n).toList.map (· + k) = (k...(n + k)).toList := by
  simp [toList_rio_eq_toList_rco, map_add_toList_rco]

theorem map_add_toList_rio' {n k : Nat} :
    (*...n).toList.map (k + ·) = (k...(k + n)).toList := by
  simp [toList_rio_eq_toList_rco, map_add_toList_rco']

theorem toList_rio_succ_eq_append {n : Nat} :
    (*...(n + 1)).toList = (*...n).toList ++ [n] := by
  simp [toList_rio_eq_toList_rco, toList_rco_succ_right_eq_append]

theorem toList_rio_eq_append {n : Nat} (h : 0 < n) :
    (*...n).toList = (*...(n - 1)).toList ++ [n - 1] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  simp [toList_rio_eq_toList_rco, toList_rco_succ_right_eq_append]

theorem toList_rio_add_add_eq_append {m n : Nat} :
    (*...(m + n)).toList = (*...m).toList ++ (m...(m + n)).toList := by
  simp only [toList_rio_eq_toList_rco]
  rw [toList_rco_append_toList_rco (by omega) (by omega)]

@[simp]
theorem getElem_toList_rio {n i : Nat} (_h : i < (*...n).toList.length) :
    (*...n).toList[i]'_h = i := by
  simp [toList_rio_eq_toList_rco]

theorem getElem?_toList_rio {n i : Nat} :
    (*...n).toList[i]? = if i < n then some i else none := by
  simp [toList_rio_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem getElem?_toList_rio_eq_some_iff {n i : Nat} :
    (*...n).toList[i]? = some k ↔ i < n ∧ i = k := by
  simp [toList_rio_eq_toList_rco]

@[simp]
theorem getElem?_toList_rio_eq_none_iff {n i : Nat} :
    (*...n).toList[i]? = none ↔ n ≤ i := by
  simp

@[simp]
theorem isSome_getElem?_toList_rio_eq {n i : Nat} :
    (*...n).toList[i]?.isSome = (i < n) := by
  simp

@[simp]
theorem isNone_getElem?_toList_rio_eq {n i : Nat} :
    (*...n).toList[i]?.isNone = (n ≤ i) := by
  simp

@[simp]
theorem getElem?_toList_rio_eq_some {n i : Nat} (h : i < n) :
    (*...n).toList[i]? = some i := by
  simp [h]

@[simp]
theorem getElem?_toList_rio_eq_none {n i : Nat} (h : n ≤ i) :
    (*...n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_rio {n i : Nat} :
    (*...n).toList[i]! = if i < n then i else 0 := by
  simp only [toList_rio_eq_toList_rco, getElem!_toList_rco, Nat.sub_zero, Nat.zero_add]

@[simp]
theorem getElem!_toList_rio_eq_self {n i : Nat} (h : i < n) :
    (*...n).toList[i]! = i := by
  simp [h]

@[simp]
theorem getElem!_toList_rio_eq_zero {n i : Nat} (h : n ≤ i) :
    (*...n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_rio_eq_zero_iff {n i : Nat} :
    (*...n).toList[i]! = 0 ↔ n ≤ i ∨ i = 0 := by
  simp only [toList_rio_eq_toList_rco, getElem!_toList_rco_eq_zero_iff, Nat.add_zero, true_and]

theorem zero_lt_getElem!_toList_rio_iff {n i : Nat} :
    0 < (*...n).toList[i]! ↔ i < n ∧ 0 < i := by
  simp only [toList_rio_eq_toList_rco, zero_lt_getElem!_toList_rco_iff, Nat.sub_zero, Nat.add_zero]

theorem getD_toList_rio {n i fallback : Nat} :
    (*...n).toList.getD i fallback = if i < n then i else fallback := by
  simp only [toList_rio_eq_toList_rco, getD_toList_rco]
  simp

@[simp]
theorem getD_toList_rio_eq_self {n i fallback : Nat} (h : i < n) :
    (*...n).toList.getD i fallback = i := by
  simp [h]

@[simp]
theorem getD_toList_rio_eq_fallback {n i fallback : Nat} (h : n ≤ i) :
    (*...n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_rio_eq_toArray_rco {n : Nat} :
    (*...n).toArray = (0...n).toArray := by
  simp [Rio.toArray_eq_match_rco]

theorem toArray_rio_eq_if {n : Nat} :
    (*...n).toArray = if 0 < n then (*...(n - 1)).toArray.push (n - 1) else #[] := by
  simp only [toArray_rio_eq_toArray_rco]
  by_cases h : 0 < n
  · rw [toArray_rco_eq_push h, if_pos h]
  · simp [*]; omega

theorem toArray_rio_succ {n : Nat} :
    (*...(n+1)).toArray = (*...n).toArray ++ [n] := by
  rw [toArray_rio_eq_if, if_pos (by omega)]
  simp

@[simp]
theorem toArray_rio_eq_nil_iff {n : Nat} :
    (*...n).toArray = #[] ↔ n = 0 := by
  simp [toArray_rio_eq_toArray_rco]

theorem toArray_rio_ne_nil_iff {n : Nat} :
    (*...n).toArray ≠ #[] ↔ 0 < n := by
  simp [Nat.pos_iff_ne_zero]

@[simp]
theorem toArray_rio_eq_nil {n : Nat} (h : n = 0) :
    (*...n).toArray = #[] := by
  simp [h]

@[simp]
theorem toArray_rio_eq_singleton_iff {n : Nat} :
    (*...n).toArray = #[k] ↔ n = 1 ∧ 0 = k := by
  simp [toArray_rio_eq_toArray_rco]

@[simp]
theorem toArray_rio_one_eq_singleton :
    (*...1).toArray = #[0] := by
  simp

@[simp]
theorem toArray_rio_eq_singleton_append_iff {n a : Nat} :
    (*...n).toArray = #[a] ++ xs ↔ 0 = a ∧ 0 < n ∧ (1...n).toArray = xs := by
  simp [toArray_rio_eq_toArray_rco]

theorem toArray_rio_eq_singleton_append {n : Nat} (h : 0 < n) :
    (*...n).toArray = #[0] ++ (1...n).toArray := by
  simp [h]

@[simp]
theorem toArray_rio_zero_right_eq_nil {m : Nat} :
    (m...0).toArray = #[] := by
  simp

theorem map_add_toArray_rio {n k : Nat} :
    (*...n).toArray.map (· + k) = (k...(n + k)).toArray := by
  simp [toArray_rio_eq_toArray_rco, map_add_toArray_rco]

theorem map_add_toArray_rio' {n k : Nat} :
    (*...n).toArray.map (k + ·) = (k...(k + n)).toArray := by
  simp [toArray_rio_eq_toArray_rco, map_add_toArray_rco']

theorem toArray_rio_succ_eq_push {n : Nat} :
    (*...(n + 1)).toArray = (*...n).toArray.push n := by
  simp [toArray_rio_eq_toArray_rco, toArray_rco_succ_right_eq_push]

theorem toArray_rio_eq_push {n : Nat} (h : 0 < n) :
    (*...n).toArray = (*...(n - 1)).toArray.push (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  simp [toArray_rio_eq_toArray_rco, toArray_rco_succ_right_eq_push]

theorem toArray_rio_add_add_eq_append {m n : Nat} :
    (*...(m + n)).toArray = (*...m).toArray ++ (m...(m + n)).toArray := by
  simp only [toArray_rio_eq_toArray_rco]
  rw [toArray_rco_append_toArray_rco (by omega) (by omega)]

@[simp]
theorem getElem_toArray_rio {n i : Nat} (_h : i < (*...n).toArray.size) :
    (*...n).toArray[i]'_h = i := by
  simp [toArray_rio_eq_toArray_rco]

theorem getElem?_toArray_rio {n i : Nat} :
    (*...n).toArray[i]? = if i < n then some i else none := by
  simp [toArray_rio_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem getElem?_toArray_rio_eq_some_iff {n i : Nat} :
    (*...n).toArray[i]? = some k ↔ i < n ∧ i = k := by
  simp [toArray_rio_eq_toArray_rco]

@[simp]
theorem getElem?_toArray_rio_eq_none_iff {n i : Nat} :
    (*...n).toArray[i]? = none ↔ n ≤ i := by
  simp

@[simp]
theorem isSome_getElem?_toArray_rio_eq {n i : Nat} :
    (*...n).toArray[i]?.isSome = (i < n) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_rio_eq {n i : Nat} :
    (*...n).toArray[i]?.isNone = (n ≤ i) := by
  simp

@[simp]
theorem getElem?_toArray_rio_eq_some {n i : Nat} (h : i < n) :
    (*...n).toArray[i]? = some i := by
  simp [h]

@[simp]
theorem getElem?_toArray_rio_eq_none {n i : Nat} (h : n ≤ i) :
    (*...n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_rio {n i : Nat} :
    (*...n).toArray[i]! = if i < n then i else 0 := by
  simp only [toArray_rio_eq_toArray_rco, getElem!_toArray_rco, Nat.sub_zero, Nat.zero_add]

@[simp]
theorem getElem!_toArray_rio_eq_self {n i : Nat} (h : i < n) :
    (*...n).toArray[i]! = i := by
  simp [h]

@[simp]
theorem getElem!_toArray_rio_eq_zero {n i : Nat} (h : n ≤ i) :
    (*...n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_rio_eq_zero_iff {n i : Nat} :
    (*...n).toArray[i]! = 0 ↔ n ≤ i ∨ i = 0 := by
  simp only [toArray_rio_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff, Nat.add_zero, true_and]

theorem zero_lt_getElem!_toArray_rio_iff {n i : Nat} :
    0 < (*...n).toArray[i]! ↔ i < n ∧ 0 < i := by
  simp only [toArray_rio_eq_toArray_rco, zero_lt_getElem!_toArray_rco_iff, Nat.sub_zero, Nat.add_zero]

theorem getD_toArray_rio {n i fallback : Nat} :
    (*...n).toArray.getD i fallback = if i < n then i else fallback := by
  simp only [toArray_rio_eq_toArray_rco, getD_toArray_rco]
  simp

@[simp]
theorem getD_toArray_rio_eq_self {n i fallback : Nat} (h : i < n) :
    (*...n).toArray.getD i fallback = i := by
  simp [h]

@[simp]
theorem getD_toArray_rio_eq_fallback {n i fallback : Nat} (h : n ≤ i) :
    (*...n).toArray.getD i fallback = fallback := by
  simp [h]

theorem toList_ric_eq_toList_rio {n : Nat} :
    (*...=n).toList = (*...(n + 1)).toList := by
  simp [Ric.toList_eq_match_rcc, toList_rio_succ_eq_append, toList_rio_eq_toList_rco]

theorem toList_ric_eq_toList_rcc {n : Nat} :
    (*...=n).toList = (0...=n).toList := by
  simp [toList_ric_eq_toList_rio, toList_rio_eq_toList_rco, toList_rcc_eq_toList_rco,
    - toList_rcc_eq_append]

theorem toList_ric_eq_toList_rco {n : Nat} :
    (*...=n).toList = (0...(n + 1)).toList := by
  simp [toList_ric_eq_toList_rio, toList_rio_eq_toList_rco]

@[simp]
theorem toList_toArray_ric {n : Nat} :
    (*...=n).toArray.toList = (*...=n).toList :=
  Ric.toList_toArray

@[simp]
theorem toArray_toList_ric {n : Nat} :
    (*...=n).toList.toArray = (*...=n).toArray :=
  Ric.toArray_toList

theorem toList_ric_eq_toList_rio_append {n : Nat} :
    (*...=n).toList = (*...n).toList ++ [n] := by
  rw [toList_ric_eq_toList_rco, toList_rio_eq_toList_rco, toList_rco_eq_if_append]
  simp

theorem toList_ric_succ {n : Nat} :
    (*...=(n + 1)).toList = (*...=n).toList ++ [n + 1] := by
  rw [toList_ric_eq_toList_rco, toList_rco_succ_right_eq_append (by omega), toList_ric_eq_toList_rco]

@[simp]
theorem toList_ric_ne_nil {n : Nat} :
    (*...=n).toList ≠ [] := by
  simp [toList_ric_eq_toList_rco]

@[simp]
theorem toList_ric_eq_singleton_iff {n : Nat} :
    (*...=n).toList = [k] ↔ n = 0 ∧ 0 = k := by
  simp [toList_ric_eq_toList_rco]; omega

@[simp]
theorem toList_ric_zero_eq_singleton :
    (*...=0).toList = [0] := by
  simp

@[simp]
theorem toList_ric_eq_cons_iff {n a : Nat} :
    (*...=n).toList = a :: xs ↔ 0 = a ∧ (1...=n).toList = xs := by
  simp [toList_ric_eq_toList_rco, toList_rcc_eq_toList_rco]

theorem toList_ric_eq_cons {n : Nat} :
    (*...=n).toList = 0 :: (1...=n).toList := by
  simp

theorem map_add_toList_ric {n k : Nat} :
    (*...=n).toList.map (· + k) = (k...=(n + k)).toList := by
  simp [toList_ric_eq_toList_rco, toList_rcc_eq_toList_rco, map_add_toList_rco,
    show n + 1 + k = n + k + 1 by omega, - toList_rcc_eq_append]

theorem map_add_toList_ric' {n k : Nat} :
    (*...=n).toList.map (k + ·) = (k...=(k + n)).toList := by
  simp [toList_ric_eq_toList_rco, map_add_toList_rco', Nat.add_assoc,
    toList_rcc_eq_toList_rco, - toList_rcc_eq_append]

theorem toList_ric_succ_eq_append {n : Nat} :
    (*...=(n + 1)).toList = (*...=n).toList ++ [n + 1] := by
  simp [toList_ric_eq_toList_rco, toList_rco_succ_right_eq_append]

theorem toList_ric_eq_append {n : Nat} (h : 0 < n) :
    (*...=n).toList = (*...=(n - 1)).toList ++ [n] := by
  simp [toList_ric_eq_toList_rco, Nat.sub_add_cancel h, toList_rco_succ_right_eq_append]

theorem toList_ric_add_add_eq_append {m n : Nat} :
    (*...=(m + n)).toList = (*...m).toList ++ (m...=(m + n)).toList := by
  simp only [toList_ric_eq_toList_rio, toList_rio_add_add_eq_append]
  simp

@[simp]
theorem getElem_toList_ric {n i : Nat} (_h : i < (*...=n).toList.length) :
    (*...=n).toList[i]'_h = i := by
  simp [toList_ric_eq_toList_rco]

theorem getElem?_toList_ric {n i : Nat} :
    (*...=n).toList[i]? = if i ≤ n then some i else none := by
  simp [toList_ric_eq_toList_rco, getElem?_toList_rco, Nat.lt_succ_iff]

@[simp]
theorem getElem?_toList_ric_eq_some_iff {n i : Nat} :
    (*...=n).toList[i]? = some k ↔ i ≤ n ∧ i = k := by
  simp [toList_ric_eq_toList_rco, Nat.lt_succ_iff]

@[simp]
theorem getElem?_toList_ric_eq_none_iff {n i : Nat} :
    (*...=n).toList[i]? = none ↔ n < i := by
  simp [Nat.succ_le_iff]

@[simp]
theorem isSome_getElem?_toList_ric_eq {n i : Nat} :
    (*...=n).toList[i]?.isSome = (i ≤ n) := by
  simp [Nat.lt_succ_iff]

@[simp]
theorem isNone_getElem?_toList_ric_eq {n i : Nat} :
    (*...=n).toList[i]?.isNone = (n < i) := by
  simp [Nat.succ_le_iff]

@[simp]
theorem getElem?_toList_ric_eq_some {n i : Nat} (h : i ≤ n) :
    (*...=n).toList[i]? = some i := by
  simp [Nat.lt_succ_iff, h]

@[simp]
theorem getElem?_toList_ric_eq_none {n i : Nat} (h : n < i) :
    (*...=n).toList[i]? = none := by
  simp [Nat.succ_le_iff, h]

theorem getElem!_toList_ric {n i : Nat} :
    (*...=n).toList[i]! = if i ≤ n then i else 0 := by
  simp only [toList_ric_eq_toList_rco, getElem!_toList_rco, Nat.sub_zero, Nat.zero_add,
    Nat.lt_succ_iff]

@[simp]
theorem getElem!_toList_ric_eq_self {n i : Nat} (h : i ≤ n) :
    (*...=n).toList[i]! = i := by
  simp only [toList_ric_eq_toList_rco, getElem!_toList_rco]
  simp; omega

@[simp]
theorem getElem!_toList_ric_eq_zero {n i : Nat} (h : n < i) :
    (*...=n).toList[i]! = 0 := by
  simp only [getElem!_toList_ric]
  simp; omega

theorem getElem!_toList_ric_eq_zero_iff {n i : Nat} :
    (*...=n).toList[i]! = 0 ↔ n < i ∨ i = 0 := by
  simp only [toList_ric_eq_toList_rco, getElem!_toList_rco_eq_zero_iff, Nat.add_zero, true_and,
    Nat.succ_le_iff]

theorem zero_lt_getElem!_toList_ric_iff {n i : Nat} :
    0 < (*...=n).toList[i]! ↔ i ≤ n ∧ 0 < i := by
  simp only [toList_ric_eq_toList_rco, zero_lt_getElem!_toList_rco_iff, Nat.sub_zero, Nat.add_zero,
    Nat.lt_succ_iff]

theorem getD_toList_ric {n i fallback : Nat} :
    (*...=n).toList.getD i fallback = if i ≤ n then i else fallback := by
  simp only [toList_ric_eq_toList_rco, getD_toList_rco]
  simp [Nat.lt_succ_iff]

@[simp]
theorem getD_toList_ric_eq_self {n i fallback : Nat} (h : i ≤ n) :
    (*...=n).toList.getD i fallback = i := by
  rw [toList_ric_eq_toList_rio, getD_toList_rio_eq_self]; omega

@[simp]
theorem getD_toList_ric_eq_fallback {n i fallback : Nat} (h : n < i) :
    (*...=n).toList.getD i fallback = fallback := by
  rw [toList_ric_eq_toList_rio, getD_toList_rio_eq_fallback]; omega

theorem toArray_ric_eq_toArray_rio {n : Nat} :
    (*...=n).toArray = (*...(n + 1)).toArray := by
  simp only [← toArray_toList_ric, toList_ric_eq_toList_rio, toArray_toList_rio]

theorem toArray_ric_eq_toArray_rcc {n : Nat} :
    (*...=n).toArray = (0...=n).toArray := by
  simp [toArray_ric_eq_toArray_rio, toArray_rio_eq_toArray_rco, toArray_rcc_eq_toArray_rco,
    - toArray_rcc_eq_push]

theorem toArray_ric_eq_toArray_rco {n : Nat} :
    (*...=n).toArray = (0...(n + 1)).toArray := by
  simp [toArray_ric_eq_toArray_rio, toArray_rio_eq_toArray_rco]

theorem toArray_ric_eq_toArray_rio_push {n : Nat} :
    (*...=n).toArray = (*...n).toArray.push n := by
  rw [toArray_ric_eq_toArray_rco, toArray_rio_eq_toArray_rco, toArray_rco_eq_if_push]
  simp

theorem toArray_ric_succ {n : Nat} :
    (*...=(n + 1)).toArray = (*...=n).toArray.push (n + 1) := by
  rw [toArray_ric_eq_toArray_rco, toArray_rco_succ_right_eq_push (by omega), toArray_ric_eq_toArray_rco]

@[simp]
theorem toArray_ric_ne_nil {n : Nat} :
    (*...=n).toArray ≠ #[] := by
  simp [toArray_ric_eq_toArray_rco]

@[simp]
theorem toArray_ric_eq_singleton_iff {n : Nat} :
    (*...=n).toArray = #[k] ↔ n = 0 ∧ 0 = k := by
  simp [toArray_ric_eq_toArray_rco]

@[simp]
theorem toArray_ric_zero_eq_singleton :
    (*...=0).toArray = #[0] := by
  simp

@[simp]
theorem toArray_ric_eq_singleton_append_iff {n a : Nat} :
    (*...=n).toArray = #[a] ++ xs ↔ 0 = a ∧ (1...=n).toArray = xs := by
  simp [toArray_ric_eq_toArray_rco, toArray_rcc_eq_toArray_rco]

theorem toArray_ric_eq_cons {n : Nat} :
    (*...=n).toArray = #[0] ++ (1...=n).toArray := by
  simp

theorem map_add_toArray_ric {n k : Nat} :
    (*...=n).toArray.map (· + k) = (k...=(n + k)).toArray := by
  simp [toArray_ric_eq_toArray_rco, map_add_toArray_rco, show n + 1 + k = n + k + 1 by omega,
    toArray_rcc_eq_toArray_rco, - toArray_rcc_eq_push]

theorem map_add_toArray_ric' {n k : Nat} :
    (*...=n).toArray.map (k + ·) = (k...=(k + n)).toArray := by
  simp [toArray_ric_eq_toArray_rco, map_add_toArray_rco', Nat.add_assoc,
    toArray_rcc_eq_toArray_rco, - toArray_rcc_eq_push]

theorem toArray_ric_succ_eq_push {n : Nat} :
    (*...=(n + 1)).toArray = (*...=n).toArray.push (n + 1) := by
  simp [toArray_ric_eq_toArray_rco, toArray_rco_succ_right_eq_push]

theorem toArray_ric_eq_push {n : Nat} (h : 0 < n) :
    (*...=n).toArray = (*...=(n - 1)).toArray.push n:= by
  simp [toArray_ric_eq_toArray_rco, Nat.sub_add_cancel h, toArray_rco_succ_right_eq_push]

theorem toArray_ric_add_add_eq_append {m n : Nat} :
    (*...=(m + n)).toArray = (*...m).toArray ++ (m...=(m + n)).toArray := by
  simp only [toArray_ric_eq_toArray_rio, toArray_rio_add_add_eq_append]
  simp

@[simp]
theorem getElem_toArray_ric {n i : Nat} (_h : i < (*...=n).toArray.size) :
    (*...=n).toArray[i]'_h = i := by
  simp [toArray_ric_eq_toArray_rco]

theorem getElem?_toArray_ric {n i : Nat} :
    (*...=n).toArray[i]? = if i ≤ n then some i else none := by
  simp [toArray_ric_eq_toArray_rco, getElem?_toArray_rco, Nat.lt_succ_iff]

@[simp]
theorem getElem?_toArray_ric_eq_some_iff {n i : Nat} :
    (*...=n).toArray[i]? = some k ↔ i ≤ n ∧ i = k := by
  simp [toArray_ric_eq_toArray_rco, Nat.lt_succ_iff]

@[simp]
theorem getElem?_toArray_ric_eq_none_iff {n i : Nat} :
    (*...=n).toArray[i]? = none ↔ n < i := by
  simp [Nat.succ_le_iff]

@[simp]
theorem isSome_getElem?_toArray_ric_eq {n i : Nat} :
    (*...=n).toArray[i]?.isSome = (i ≤ n) := by
  simp [Nat.lt_succ_iff]

@[simp]
theorem isNone_getElem?_toArray_ric_eq {n i : Nat} :
    (*...=n).toArray[i]?.isNone = (n < i) := by
  simp [Nat.succ_le_iff]

@[simp]
theorem getElem?_toArray_ric_eq_some {n i : Nat} (h : i ≤ n) :
    (*...=n).toArray[i]? = some i := by
  simp [Nat.lt_succ_iff, h]

@[simp]
theorem getElem?_toArray_ric_eq_none {n i : Nat} (h : n < i) :
    (*...=n).toArray[i]? = none := by
  simp [Nat.succ_le_iff, h]

theorem getElem!_toArray_ric {n i : Nat} :
    (*...=n).toArray[i]! = if i ≤ n then i else 0 := by
  simp only [toArray_ric_eq_toArray_rco, getElem!_toArray_rco, Nat.sub_zero, Nat.zero_add,
    Nat.lt_succ_iff]

@[simp]
theorem getElem!_toArray_ric_eq_self {n i : Nat} (h : i ≤ n) :
    (*...=n).toArray[i]! = i := by
  simp only [toArray_ric_eq_toArray_rco, getElem!_toArray_rco]
  simp; omega

@[simp]
theorem getElem!_toArray_ric_eq_zero {n i : Nat} (h : n < i) :
    (*...=n).toArray[i]! = 0 := by
  simp only [getElem!_toArray_ric]
  simp; omega

theorem getElem!_toArray_ric_eq_zero_iff {n i : Nat} :
    (*...=n).toArray[i]! = 0 ↔ n < i ∨ i = 0 := by
  simp only [toArray_ric_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff, Nat.add_zero, true_and,
    Nat.succ_le_iff]

theorem zero_lt_getElem!_toArray_ric_iff {n i : Nat} :
    0 < (*...=n).toArray[i]! ↔ i ≤ n ∧ 0 < i := by
  simp only [toArray_ric_eq_toArray_rco, zero_lt_getElem!_toArray_rco_iff, Nat.sub_zero, Nat.add_zero,
    Nat.lt_succ_iff]

theorem getD_toArray_ric {n i fallback : Nat} :
    (*...=n).toArray.getD i fallback = if i ≤ n then i else fallback := by
  simp only [toArray_ric_eq_toArray_rco, getD_toArray_rco]
  simp [Nat.lt_succ_iff]

@[simp]
theorem getD_toArray_ric_eq_self {n i fallback : Nat} (h : i ≤ n) :
    (*...=n).toArray.getD i fallback = i := by
  rw [toArray_ric_eq_toArray_rio, getD_toArray_rio_eq_self]; omega

@[simp]
theorem getD_toArray_ric_eq_fallback {n i fallback : Nat} (h : n < i) :
    (*...=n).toArray.getD i fallback = fallback := by
  rw [toArray_ric_eq_toArray_rio, getD_toArray_rio_eq_fallback]; omega

end Nat

theorem List.range_eq_toList_rco {n : Nat} :
    List.range n = (0...n).toList := by
  simp [List.ext_getElem_iff, Std.Rco.getElem_toList_eq]

theorem List.range'_eq_toList_rco {m n : Nat} :
    List.range' m n = (m...(m + n)).toList := by
  simp [List.ext_getElem_iff, Std.Rco.getElem_toList_eq]

theorem Array.range_eq_toArray_rco {n : Nat} :
    Array.range n = (0...n).toArray := by
  apply Array.ext_getElem?; intro n
  simp [Std.Rco.getElem?_toArray_eq, Array.getElem?_range, Option.filter]

theorem Array.range'_eq_toArray_rco {m n : Nat} :
    Array.range' m n = (m...(m + n)).toArray := by
  apply Array.ext_getElem?; intro n
  simp [Std.Rco.getElem?_toArray_eq, Array.getElem?_range', Option.filter]
