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

@[simp]
theorem size_rcc {a b : Nat} :
    (a...=b).size = b + 1 - a := by
  simp [Rcc.size, Rxc.HasSize.size]

@[simp]
theorem length_toList_rcc {a b : Nat} :
    (a...=b).toList.length = b + 1 - a := by
  simp only [Rcc.length_toList, size_rcc]

@[deprecated size_rcc (since := "2025-10-30")]
def size_Rcc := @size_rcc

@[simp]
theorem size_rco {a b : Nat} :
    (a...b).size = b - a := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[simp]
theorem length_toList_rco {a b : Nat} :
    (a...b).toList.length = b - a := by
  simp only [Rco.length_toList, size_rco]

@[deprecated size_rco (since := "2025-10-30")]
def size_Rco := @size_rco

@[simp]
theorem size_roc {a b : Nat} :
    (a<...=b).size = b - a := by
  simp [Roc.size, Rxc.HasSize.size]

@[simp]
theorem length_toList_roc {a b : Nat} :
    (a<...=b).toList.length = b - a := by
  simp only [Roc.length_toList, size_roc]

@[deprecated size_roc (since := "2025-10-30")]
def size_Roc := @size_roc

@[simp]
theorem size_roo {a b : Nat} :
    (a<...b).size = b - a - 1 := by
  simp [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[simp]
theorem length_toList_roo {a b : Nat} :
    (a<...b).toList.length = b - a - 1 := by
  simp only [Roo.length_toList, size_roo]

@[deprecated size_roo (since := "2025-10-30")]
def size_Roo := @size_roo

@[simp]
theorem size_ric {b : Nat} :
    (*...=b).size = b + 1 := by
  simp [Ric.size, Rxc.HasSize.size]

@[simp]
theorem length_toList_ric {b : Nat} :
    (*...=b).toList.length = b + 1 := by
  simp only [Ric.length_toList, size_ric]

@[deprecated size_ric (since := "2025-10-30")]
def size_Ric := @size_ric

@[simp]
theorem size_rio {b : Nat} :
    (*...b).size = b := by
  simp [Rio.size, Rxo.HasSize.size, Rxc.HasSize.size]

@[simp]
theorem length_toList_rio {b : Nat} :
    (*...b).toList.length = b := by
  simp only [Rio.length_toList, size_rio]

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
    (m...n).toList[i]? = some k ↔ i < n - m ∧ k = m + i := by
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

@[simp]
theorem getElem?_toList_rco_eq_some {m n i : Nat} (h : i < n - m) :
    (m...n).toList[i]? = some (m + i) := by
  simp [h]

@[simp]
theorem getElem?_toList_rco_eq_none {m n i : Nat} (h : n ≤ i + m) :
    (m...n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_rco {m n i : Nat} :
    (m...n).toList[i]! = if i < n - m then (m + i) else 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Nat.default_eq_zero]
  split <;> simp

@[simp]
theorem getElem!_toList_rco_eq_add {m n i : Nat} (h : i < n - m) :
    (m...n).toList[i]! = m + i := by
  simp [h]

@[simp]
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
  induction a, b using Std.PRange.Nat.induct_rco_left
  case base =>
    simp only [Std.PRange.Nat.toList_rco_eq_nil, List.length_nil, Nat.sub_eq_zero_of_le, *]
  case step =>
    simp only [Std.PRange.Nat.toList_rco_eq_cons, List.length_cons, *]; omega
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
  induction a, b using Std.PRange.Nat.induct_rco_right
  case base =>
    simp only [Std.PRange.Nat.toList_rco_eq_nil, List.length_nil, Nat.sub_eq_zero_of_le, *]
  case step a b hle ih =>
    rw [Std.PRange.Nat.toList_rco_eq_append (by omega),
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

@[simp]
theorem toList_rcc_eq_toList_rco {m n : Nat} :
    (m...=n).toList = (m...(n + 1)).toList := by
  simp

theorem toList_rcc_eq_if {m n : Nat} :
    (m...=n).toList = if m ≤ n then m :: ((m + 1)...=n).toList else [] := by
  rw [toList_rcc_eq_toList_rco, toList_rcc_eq_toList_rco, toList_rco_eq_if]
  split <;> (simp; omega)

theorem toList_rcc_succ_succ {m n : Nat} :
    ((m+1)...=(n+1)).toList = (m...=n).toList.map (· + 1) := by
  simp [← succ_eq, Rco.toList_succ_succ_eq_map]

theorem toList_rcc_succ_right_eq_cons_map {m n : Nat} (h : m ≤ n + 1) :
    (m...=(n + 1)).toList = m :: (m...=n).toList.map (· + 1) := by
  simp [toList_rco_succ_succ]; omega

@[simp]
theorem toList_rcc_eq_nil_iff {m n : Nat} :
    (m...=n).toList = [] ↔ n < m := by
  simp; omega

theorem toList_rcc_ne_nil_iff {m n : Nat} :
    (m...=n).toList ≠ [] ↔ m ≤ n := by
  simp; omega

@[simp]
theorem toList_rcc_eq_nil {m n : Nat} (h : n < m) :
    (m...=n).toList = [] := by
  simp; omega

@[simp]
theorem toList_rcc_eq_cons_iff {m n a : Nat} :
    (m...=n).toList = a :: xs ↔ m = a ∧ m ≤ n ∧ xs = ((m + 1)...=n).toList := by
  simp; omega

@[simp]
theorem toList_rcc_eq_cons {m n : Nat} (h : m ≤ n) :
    (m...=n).toList = m :: ((m + 1)...=n).toList := by
  simp; omega

theorem map_add_toList_rcc {m n k : Nat} :
    (m...=n).toList.map (· + k) = ((m + k)...=(n + k)).toList := by
  simp [map_add_toList_rco, show n + 1 + k = n + k + 1 by omega]

theorem map_add_toList_rcc' {m n k : Nat} :
    (m...=n).toList.map (k + ·) = ((k + m)...=(k + n)).toList := by
  simp [map_add_toList_rco', ← Nat.add_assoc]

theorem toList_rcc_add_right_eq_map {m n : Nat} :
    (m...=(m + n)).toList = (0...=n).toList.map (· + m) := by
  simp [show m + n + 1 = (m + 1) + n by omega, toList_rco_add_right_eq_map, toList_rco_succ_succ,
    show ∀ a, a + 1 + m = a + (m + 1) by omega]
  omega

theorem toList_rcc_add_succ_right_eq_append {m n : Nat} :
    (m...=(m + n + 1)).toList = (m...=(m + n)).toList ++ [m + n + 1] := by
  simp only [Rcc.toList_eq_toList_rco, succ_eq]
  rw [toList_rco_eq_append (by omega)]
  simp

theorem toList_rcc_eq_append {m n : Nat} (h : m ≤ n) (h' : 0 < n) :
    (m...=n).toList = (m...=(n - 1)).toList ++ [n] := by
  simp only [toList_rcc_eq_toList_rco]
  rw [toList_rco_eq_append (by omega), Nat.sub_add_cancel (by omega)]
  simp

theorem toList_rcc_succ_right_eq_append {m n : Nat} (h : m ≤ n + 1) :
    (m...=(n + 1)).toList = (m...=n).toList ++ [n + 1] := by
  rw [toList_rcc_eq_append (by omega) (by omega)]
  simp

theorem toList_rcc_add_succ_right_eq_append' {m n : Nat} :
    (m...=(m + (n + 1))).toList = (m...=(m + n)).toList ++ [m + n + 1] := by
  rw [toList_rcc_eq_append (by omega) (by omega)]
  simp; omega

@[simp]
theorem getElem_toList_rcc {m n i : Nat} (_h : i < (m...=n).toList.length) :
    (m...=n).toList[i]'_h = m + i := by
  simp

theorem getElem?_toList_rcc {m n i : Nat} :
    (m...=n).toList[i]? = if i < n + 1 - m then some (m + i) else none := by
  simp [getElem?_toList_rco]

@[simp]
theorem getElem?_toList_rcc_eq_some_iff {m n i : Nat} :
    (m...=n).toList[i]? = some k ↔ i < n + 1 - m ∧ k = m + i := by
  simp [getElem?_toList_rco, eq_comm]

@[simp]
theorem getElem?_toList_rcc_eq_none_iff {m n i : Nat} :
    (m...=n).toList[i]? = none ↔ n + 1 ≤ i + m := by
  simp [getElem?_toList_rco]

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
  induction a, b using Std.PRange.Nat.induct_rcc_left
  case base =>
    simp only [Std.PRange.Nat.toList_rcc_eq_nil, List.length_nil, *]; omega
  case step =>
    simp only [Std.PRange.Nat.toList_rcc_eq_cons, List.length_cons, *]; omega
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
{lean}`b < a`, the statement holds for the empty range {lean}`a...=b`.

In the {name}`step` case, one proves that for any {given}`a : Nat` and {given}`b : Nat`, if the
statement holds for {lean}`a...=b`, it also holds for the larger range {lean}`a...=(b + 1)`.

The following is an example reproving {name}`length_toList_rcc`.

```lean
example (a b : Nat) : (a...=b).toList.length = b + 1 - a := by
  induction a, b using Std.PRange.Nat.induct_rcc_right
  case base =>
    simp only [Std.PRange.Nat.toList_rcc_eq_nil, List.length_nil, *]
    omega
  case step a b hle ih =>
    rw [Std.PRange.Nat.toList_rcc_eq_append (by omega),
      List.length_append, List.length_singleton, Nat.add_sub_cancel, ih] <;> omega
```
-/
theorem induct_rcc_right (motive : Nat → Nat → Prop)
    (base : ∀ a b, b < a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Nat) : motive a b := by
  apply induct_rco_right (fun a b => motive a (b + 1))
  induction h : b + 1 - a generalizing a b
  · apply base; omega
  · rename_i d ih

    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
    apply step
    · omega
    · apply ih
      omega

@[simp]
theorem toList_roo_eq_toList_rco {m n : Nat} :
    (m<...n).toList = ((m + 1)...n).toList := by
  simp [Roo.toList_eq_match_rco]

theorem toList_roo_eq_if {m n : Nat} :
    (m<...n).toList = if m + 1 < n then (m + 1) :: ((m + 1)<...n).toList else [] := by
  simp only [toList_roo_eq_toList_rco]
  rw [toList_rco_eq_if]

theorem toList_roo_succ_succ {m n : Nat} :
    ((m+1)<...(n+1)).toList = (m<...n).toList.map (· + 1) := by
  simp [toList_rco_succ_succ]

theorem toList_roo_succ_right_eq_cons_map {m n : Nat} (h : m < n) :
    (m<...(n + 1)).toList = (m + 1) :: (m<...n).toList.map (· + 1) := by
  simp [toList_rco_succ_right_eq_cons_map h]

@[simp]
theorem toList_roo_eq_nil_iff {m n : Nat} :
    (m<...n).toList = [] ↔ n ≤ m + 1 := by
  simp

theorem toList_roo_ne_nil_iff {m n : Nat} :
    (m<...n).toList ≠ [] ↔ m + 1 < n := by
  simp

@[simp]
theorem toList_roo_eq_nil {m n : Nat} (h : n ≤ m + 1) :
    (m<...n).toList = [] := by
  simp [h]

@[simp]
theorem toList_roo_eq_cons_iff {m n a : Nat} :
    (m<...n).toList = a :: xs ↔ m + 1 = a ∧ m + 1 < n ∧ xs = ((m + 1)<...n).toList := by
  simp

@[simp]
theorem toList_roo_eq_cons {m n : Nat} (h : m + 1 < n) :
    (m<...n).toList = (m + 1) :: ((m + 1)<...n).toList := by
  simp [h]

theorem toList_roo_zero_right_eq_nil {m : Nat} :
    (m<...0).toList = [] := by
  simp

theorem toList_roo_one_right_eq_nil {m : Nat} :
    (m<...1).toList = [] := by
  simp

theorem map_add_toList_roo {m n k : Nat} :
    (m<...n).toList.map (· + k) = ((m + k)<...(n + k)).toList := by
  simp [map_add_toList_rco, show m + 1 + k = m + k + 1 by omega]

theorem map_add_toList_roo' {m n k : Nat} :
    (m<...n).toList.map (k + ·) = ((k + m)<...(k + n)).toList := by
  simp [map_add_toList_rco', show k + (m + 1) = k + m + 1 by omega]

theorem toList_roo_add_right_eq_map {m n : Nat} :
    (m<...(m + 1 + n)).toList = (0...n).toList.map (· + m + 1) := by
  simp [toList_rco_add_right_eq_map, show ∀ a, a + (m + 1) = (a + m) + 1 by omega]

@[simp]
theorem getElem_toList_roo {m n i : Nat} (_h : i < (m<...n).toList.length) :
    (m<...n).toList[i]'_h = m + 1 + i := by
  simp

theorem getElem?_toList_roo {m n i : Nat} :
    (m<...n).toList[i]? = if i < n - (m + 1) then some (m + 1 + i) else none := by
  simp [getElem?_toList_rco]

@[simp]
theorem getElem?_toList_roo_eq_some_iff {m n i : Nat} :
    (m<...n).toList[i]? = some k ↔ i < n - (m + 1) ∧ k = m + 1 + i := by
  simp

@[simp]
theorem getElem?_toList_roo_eq_none_iff {m n i : Nat} :
    (m<...n).toList[i]? = none ↔ n ≤ i + (m + 1) := by
  simp

@[simp]
theorem isSome_getElem?_toList_roo_eq {m n i : Nat} :
    (m<...n).toList[i]?.isSome = (i < n - (m + 1)) := by
  simp

@[simp]
theorem isNone_getElem?_toList_roo_eq {m n i : Nat} :
    (m<...n).toList[i]?.isNone = (n ≤ i + (m + 1)) := by
  simp

@[simp]
theorem getElem?_toList_roo_eq_some {m n i : Nat} (h : i < n - (m + 1)) :
    (m<...n).toList[i]? = some (m + 1 + i) := by
  simp [h]

@[simp]
theorem getElem?_toList_roo_eq_none {m n i : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_roo {m n i : Nat} :
    (m<...n).toList[i]! = if i < n - (m + 1) then (m + 1 + i) else 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_roo, Nat.default_eq_zero]
  split <;> simp

@[simp]
theorem getElem!_toList_roo_eq_add {m n i : Nat} (h : i < n - (m + 1)) :
    (m<...n).toList[i]! = m + 1 + i := by
  simp [h]

@[simp]
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
  by_cases h : i < n - (m + 1) <;> simp [h]

@[simp]
theorem getD_toList_roo_eq_add {m n i fallback : Nat} (h : i < n - (m + 1)) :
    (m<...n).toList.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toList_roo_eq_fallback {m n i fallback : Nat} (h : n ≤ i + (m + 1)) :
    (m<...n).toList.getD i fallback = fallback := by
  simp [h]

theorem toList_roc_eq_toList_rcc {m n : Nat} :
    (m<...=n).toList = ((m + 1)...=n).toList := by
  simp

theorem toList_roc_eq_toList_roo {m n : Nat} :
    (m<...=n).toList = (m<...(n + 1)).toList := by
  simp

theorem toList_roc_eq_toList_rco {m n : Nat} :
    (m<...=n).toList = ((m + 1)...(n + 1)).toList := by
  simp

theorem toList_roc_eq_if {m n : Nat} :
    (m<...=n).toList = if m + 1 ≤ n then (m + 1) :: ((m + 1)<...=n).toList else [] := by
  rw [toList_roc_eq_toList_rco, toList_roc_eq_toList_rco, toList_rco_eq_if]
  split <;> (simp; omega)

theorem toList_roc_succ_succ {m n : Nat} :
    ((m+1)<...=(n+1)).toList = (m<...=n).toList.map (· + 1) := by
  simp [← succ_eq, Rco.toList_succ_succ_eq_map]

theorem toList_roc_succ_right_eq_cons_map {m n : Nat} (h : m ≤ n) :
    (m<...=(n + 1)).toList = (m + 1) :: (m<...=n).toList.map (· + 1) := by
  simp [toList_rco_succ_right_eq_cons_map, h]

@[simp]
theorem toList_roc_eq_nil_iff {m n : Nat} :
    (m<...=n).toList = [] ↔ n ≤ m := by
  simp

theorem toList_roc_ne_nil_iff {m n : Nat} :
    (m<...=n).toList ≠ [] ↔ m < n := by
  simp

@[simp]
theorem toList_roc_eq_nil {m n : Nat} (h : n ≤ m) :
    (m<...=n).toList = [] := by
  simp; omega

@[simp]
theorem toList_roc_eq_cons_iff {m n a : Nat} :
    (m<...=n).toList = a :: xs ↔ m + 1 = a ∧ m < n ∧ xs = ((m + 1)<...=n).toList := by
  simp

@[simp]
theorem toList_roc_eq_cons {m n : Nat} (h : m < n) :
    (m<...=n).toList = (m + 1) :: ((m + 1)<...=n).toList := by
  simp; omega

theorem map_add_toList_roc {m n k : Nat} :
    (m<...=n).toList.map (· + k) = ((m + k)<...=(n + k)).toList := by
  simp [map_add_toList_rco, show ∀ l, l + 1 + k = l + k + 1 by omega]

theorem map_add_toList_roc' {m n k : Nat} :
    (m<...=n).toList.map (k + ·) = ((k + m)<...=(k + n)).toList := by
  simp [map_add_toList_rco', ← Nat.add_assoc]

theorem toList_roc_add_right_eq_map {m n : Nat} :
    (m<...=(m + n)).toList = (0...n).toList.map (· + m + 1) := by
  simp [show m + n + 1 = m + 1 + n by omega, toList_rco_add_right_eq_map, ← Nat.add_assoc]

theorem toList_roc_succ_right_eq_append {m n : Nat} (h : m ≤ n) :
    (m<...=(n + 1)).toList = (m<...=n).toList ++ [n + 1] := by
  simp [toList_rco_succ_right_eq_append, h]

theorem toList_roc_add_succ_right_eq_append {m n : Nat} :
    (m<...=(m + n + 1)).toList = (m<...=(m + n)).toList ++ [m + n + 1] := by
  rw [toList_roc_succ_right_eq_append (by omega)]

theorem toList_roc_add_succ_right_eq_append' {m n : Nat} :
    (m<...=(m + (n + 1))).toList = (m<...=(m + n)).toList ++ [m + n + 1] := by
  rw [← Nat.add_assoc, toList_roc_add_succ_right_eq_append]

theorem toList_roc_eq_append {m n : Nat} (h : m < n) :
    (m<...=n).toList = (m<...=(n - 1)).toList ++ [n] := by
  simp [toList_rco_eq_append (Nat.succ_le_succ h), Nat.sub_add_cancel (n := n) (m := 1) (by omega)]

theorem toList_roc_add_add_eq_append {m n k : Nat} :
    (m<...=(m + n + k)).toList = (m<...=(m + n)).toList ++ ((m + n)<...=(m + n + k)).toList := by
  simp only [toList_roc_eq_toList_rco]
  rw [← toList_rco_append_toList_rco] <;> omega

theorem toList_roc_append_toList_roc {l m n : Nat} (h : l ≤ m) (h' : m ≤ n) :
    (l<...=m).toList ++ (m<...=n).toList = (l<...=n).toList := by
  simp [toList_rco_append_toList_rco (Nat.succ_le_succ h) (Nat.succ_le_succ h')]

@[simp]
theorem getElem_toList_roc {m n i : Nat} (_h : i < (m<...=n).toList.length) :
    (m<...=n).toList[i]'_h = m + 1 + i := by
  simp

theorem getElem?_toList_roc {m n i : Nat} :
    (m<...=n).toList[i]? = if i < n - m then some (m + 1 + i) else none := by
  simp [getElem?_toList_rco]

@[simp]
-- TODO: flip the `k = ...` in these lemmas?
theorem getElem?_toList_roc_eq_some_iff {m n i : Nat} :
    (m<...=n).toList[i]? = some k ↔ i < n - m ∧ k = m + 1 + i := by
  simp

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

/-
TODO:

* induction principles
* `List.*` lemmas
-/

end Std.PRange.Nat

theorem List.range_eq_toList_rco {n : Nat} :
    List.range n = (0...n).toList := by
  simp [List.ext_getElem_iff, Std.Rco.getElem_toList_eq]

theorem List.range'_eq_toList_rco {m n : Nat} :
    List.range' m n = (m...(m + n)).toList := by
  simp [List.ext_getElem_iff, Std.Rco.getElem_toList_eq]
