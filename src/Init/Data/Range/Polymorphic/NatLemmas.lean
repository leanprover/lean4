/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Lemmas

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

@[simp]
theorem size_rcc {a b : Nat} :
    (a...=b).size = b + 1 - a := by
  simp [Rcc.size, Rxc.HasSize.size]

@[deprecated size_rcc (since := "2025-10-30")]
def size_Rcc := @size_rcc

@[simp]
theorem size_rco {a b : Nat} :
    (a...b).size = b - a := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[deprecated size_rco (since := "2025-10-30")]
def size_Rco := @size_rco

@[simp]
theorem size_roc {a b : Nat} :
    (a<...=b).size = b - a := by
  simp [Roc.size, Rxc.HasSize.size]

@[deprecated size_roc (since := "2025-10-30")]
def size_Roc := @size_roc

@[simp]
theorem size_roo {a b : Nat} :
    (a<...b).size = b - a - 1 := by
  simp [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[deprecated size_roo (since := "2025-10-30")]
def size_Roo := @size_roo

@[simp]
theorem size_ric {b : Nat} :
    (*...=b).size = b + 1 := by
  simp [Ric.size, Rxc.HasSize.size]

@[deprecated size_ric (since := "2025-10-30")]
def size_Ric := @size_ric

@[simp]
theorem size_rio {b : Nat} :
    (*...b).size = b := by
  simp [Rio.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[deprecated size_rio (since := "2025-10-30")]
def size_Rio := @size_rio

theorem toList_rco_eq_if {m n : Nat} :
    (m...n).toList = if m < n then m :: ((m + 1)...n).toList else [] := by
  rw [Rco.toList_eq_if_roo]
  simp [Roo.toList_eq_match_rco]

theorem toList_rco_succ_succ {m n : Nat} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := by
  simp [← succ_eq, Rco.toList_succ_succ_eq_map]

@[deprecated toList_rco_succ_succ (since := "2025-10-30")]
def toList_Rco_succ_succ := @toList_rco_succ_succ

@[deprecated toList_rco_succ_succ (since := "2025-08-22")]
def ClosedOpen.toList_succ_succ := @toList_rco_succ_succ

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
theorem toList_rco_eq_cons_iff {m n a : Nat} :
    (m...n).toList = a :: xs ↔ m = a ∧ m < n ∧ xs = ((m + 1)...n).toList := by
  rw [Rco.toList_eq_if_roo]
  split <;> simp +contextual [*, Roo.toList_eq_match_rco, eq_comm]

@[simp]
theorem toList_rco_eq_cons {m n : Nat} (h : m < n) :
    (m...n).toList = m :: ((m + 1)...n).toList := by
  simp [h]

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

theorem toList_rco_add_succ_right_eq_append' {m n : Nat} :
    (m...(m + (n + 1))).toList = (m...(m + n)).toList ++ [m + n] := by
  simp [toList_rco_add_succ_right_eq_append, ← Nat.add_assoc]

theorem toList_rco_eq_append {m n : Nat} (h : m < n) :
    (m...n).toList = (m...(n - 1)).toList ++ [n - 1] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  simp [toList_rco_add_succ_right_eq_append]

theorem toList_rco_add_add_eq_append {m n k : Nat} :
    (m...(m + n + k)).toList = (m...(m + n)).toList ++ ((m + n)...(m + n + k)).toList := by
  induction k
  · simp
  · rename_i k ih
    rw [toList_rco_add_succ_right_eq_append', ← List.append_assoc, ← ih, toList_rco_eq_append]
    · simp
    · omega

theorem getElem?_toList_rco {m n i : Nat} :
    (m...n).toList[i]? = if m + i < n then some (m + i) else none := by
  simp [Rco.getElem?_toList_eq, Option.filter_some]

@[simp]
theorem getElem?_toList_rco_eq_none_iff {m n i : Nat} :
    (m...n).toList[i]? = none ↔ n ≤ m + i := by
  simp [getElem?_toList_rco]

@[simp]
theorem getElem?_toList_rco_eq_some_iff {m n i : Nat} :
    (m...n).toList[i]? = some k ↔ m + i < n ∧ k = m + i := by
  simp [getElem?_toList_rco, eq_comm]

@[simp]
theorem isSome_getElem?_toList_rco_eq {m n i : Nat} :
    (m...n).toList[i]?.isSome = (m + i < n) := by
  simp
  simp [Nat.lt_sub_iff_add_lt, Nat.add_comm]

@[simp]
theorem isNone_getElem?_toList_rco_eq {m n i : Nat} :
    (m...n).toList[i]?.isNone = (m + i < n) := by
  simp [Nat.lt_sub_iff_add_lt, Nat.add_comm]

theorem getElem?_toList_rco_eq_some {m n i : Nat} (h : m + i < n) :
    (m...n).toList[i]? = some (m + i) := by
  simp [getElem?_toList_rco, h]

theorem getElem?_toList_rco_eq_none {m n i : Nat} (h : n ≤ m + i) :
    (m...n).toList[i]? = none := by
  simp [getElem?_toList_rco, h]

end Std.PRange.Nat

theorem List.range_eq_toList_rco {n : Nat} :
    List.range n = (0...n).toList := by
  simp [List.ext_getElem_iff, Std.Rco.getElem_toList_eq]

theorem List.range'_eq_toList_rco {m n : Nat} :
    List.range' m n = (m...(m + n)).toList := by
  simp [List.ext_getElem_iff, Std.Rco.getElem_toList_eq]
