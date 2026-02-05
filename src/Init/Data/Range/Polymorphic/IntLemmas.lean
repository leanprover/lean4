/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

prelude
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Lemmas

public section

set_option doc.verso true

namespace Std.PRange.Int

@[simp]
theorem succ?_eq {n : Int} : succ? n = some (n + 1) :=
  rfl

@[simp]
theorem succMany?_eq {n : Nat} {m : Int} : succMany? n m = some (m + n) :=
  rfl

@[simp]
theorem succ_eq {n : Int} : succ n = n + 1 :=
  rfl

@[simp]
theorem succMany_eq {n : Nat} {m : Int} : succMany n m = m + n := by
  rfl

end Std.PRange.Int

namespace Int
open Std Std.PRange Std.PRange.Int

@[simp]
theorem size_rcc {a b : Int} :
    (a...=b).size = (b + 1 - a).toNat := by
  simp [Rcc.size, Rxc.HasSize.size]

@[simp]
theorem length_toList_rcc {a b : Int} :
    (a...=b).toList.length = (b + 1 - a).toNat := by
  simp only [Rcc.length_toList, size_rcc]

@[simp]
theorem size_rco {a b : Int} :
    (a...b).size = (b - a).toNat := by
  simp only [Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
  omega

@[simp]
theorem length_toList_rco {a b : Int} :
    (a...b).toList.length = (b - a).toNat := by
  simp only [Rco.length_toList, size_rco]

@[simp]
theorem size_toArray_rco {a b : Int} :
    (a...b).toArray.size = (b - a).toNat := by
  simp only [Rco.size_toArray, size_rco]

@[simp]
theorem size_roc {a b : Int} :
    (a<...=b).size = (b - a).toNat := by
  simp only [Roc.size, Rxc.HasSize.size]
  omega

@[simp]
theorem length_toList_roc {a b : Int} :
    (a<...=b).toList.length = (b - a).toNat := by
  simp only [Roc.length_toList, size_roc]

@[simp]
theorem size_toArray_roc {a b : Int} :
    (a<...=b).toArray.size = (b - a).toNat := by
  simp only [Roc.size_toArray, size_roc]

@[simp]
theorem size_roo {a b : Int} :
    (a<...b).size = (b - a - 1).toNat := by
  simp only [Roo.size, Rxo.HasSize.size, Rxc.HasSize.size, Int.pred_toNat]
  omega

@[simp]
theorem length_toList_roo {a b : Int} :
    (a<...b).toList.length = (b - a - 1).toNat := by
  simp only [Roo.length_toList, size_roo]

@[simp]
theorem size_toArray_roo {a b : Int} :
    (a<...b).toArray.size = (b - a - 1).toNat := by
  simp only [Roo.size_toArray, size_roo]

@[simp]
theorem toList_toArray_rco {m n : Int} :
    (m...n).toArray.toList = (m...n).toList := by
  simp

@[simp]
theorem toArray_toList_rco {m n : Int} :
    (m...n).toList.toArray = (m...n).toArray := by
  simp

theorem toList_rco_eq_if {m n : Int} :
    (m...n).toList = if m < n then m :: ((m + 1)...n).toList else [] := by
  rw [Rco.toList_eq_if_roo]
  simp [Roo.toList_eq_match_rco]

theorem toList_rco_succ_succ {m n : Int} :
    ((m+1)...(n+1)).toList = (m...n).toList.map (· + 1) := by
  simp [← succ_eq, Rco.toList_succ_succ_eq_map]

theorem toList_rco_succ_right_eq_cons_map {m n : Int} (h : m ≤ n) :
    (m...(n + 1)).toList = m :: (m...n).toList.map (· + 1) := by
  rw [Rco.toList_eq_if_roo, if_pos (Int.le_iff_lt_add_one.mp h), Roo.toList_eq_match_rco]
  simp [toList_rco_succ_succ]

@[simp]
theorem toList_rco_eq_nil_iff {m n : Int} :
    (m...n).toList = [] ↔ n ≤ m := by
  simp [Rco.toList_eq_if_roo]

theorem toList_rco_ne_nil_iff {m n : Int} :
    (m...n).toList ≠ [] ↔ m < n := by
  simp

@[simp]
theorem toList_rco_eq_nil {m n : Int} (h : n ≤ m) :
    (m...n).toList = [] := by
  simp [h]

@[simp]
theorem toList_rco_eq_singleton_iff {m n : Int} :
    (m...n).toList = [k] ↔ n = m + 1 ∧ m = k := by
  rw [toList_rco_eq_if]
  split <;> (simp; omega)

@[simp 1001]
theorem toList_rco_eq_singleton {m n : Int} (h : n = m + 1) :
    (m...n).toList = [m] := by
  simp [h]

@[simp]
theorem toList_rco_eq_cons_iff {m n a : Int} :
    (m...n).toList = a :: xs ↔ m = a ∧ m < n ∧ ((m + 1)...n).toList = xs := by
  rw [Rco.toList_eq_if_roo]
  split <;> simp +contextual [*, Roo.toList_eq_match_rco, eq_comm]

theorem toList_rco_eq_cons {m n : Int} (h : m < n) :
    (m...n).toList = m :: ((m + 1)...n).toList := by
  simp [h]

theorem map_add_toList_rco {m n k : Int} :
    (m...n).toList.map (· + k) = ((m + k)...(n + k)).toList := by
  apply List.ext_getElem
  · simp only [List.length_map, Int.length_toList_rco]
    omega
  · simp only [List.getElem_map, Rco.getElem_toList_eq, succMany?_eq, Option.get_some]
    omega

theorem map_add_toList_rco' {m n k : Int} :
    (m...n).toList.map (k + ·) = ((k + m)...(k + n)).toList := by
  simp [Int.add_comm, ← map_add_toList_rco]

theorem toList_rco_add_right_eq_map {m n : Int} :
    (m...(m + n)).toList = (0...n).toList.map (· + m) := by
  rw (occs := [1]) [← Int.zero_add m]
  simp [map_add_toList_rco', Int.add_comm _ m]

theorem toList_rco_succ_right_eq_append {m n : Int} (h : m ≤ n) :
    (m...(n + 1)).toList = (m...n).toList ++ [n] := by
  apply List.ext_getElem
  · simp; omega
  · simp [Rco.getElem_toList_eq, List.getElem_append]; omega

theorem toList_rco_eq_append {m n : Int} (h : m < n) :
    (m...n).toList = (m...(n - 1)).toList ++ [n - 1] := by
  rw [show n = n - 1 + 1 by omega, toList_rco_succ_right_eq_append (by omega)]
  simp

theorem toList_rco_eq_if_append {m n : Int} :
    (m...n).toList = if m < n then (m...(n - 1)).toList ++ [n - 1] else [] := by
  split
  · simp only [toList_rco_eq_append, *]
  · simp; omega

theorem toList_rco_add_add_eq_append {m : Int} {n k : Nat} :
    (m...(m + n + k)).toList = (m...(m + n)).toList ++ ((m + n)...(m + n + k)).toList := by
  apply List.ext_getElem
  · simp; omega
  · simp [Rco.getElem_toList_eq, List.getElem_append]; omega

theorem toList_rco_append_toList_rco {l m n : Int} (h : l ≤ m) (h' : m ≤ n) :
    (l...m).toList ++ (m...n).toList = (l...n).toList := by
  apply List.ext_getElem
  · simp; omega
  · simp [Rco.getElem_toList_eq, List.getElem_append]; omega

@[simp]
theorem getElem_toList_rco {m n : Int} {i : Nat} (_h : i < (m...n).toList.length) :
    (m...n).toList[i]'_h = m + i := by
  simp [Rco.getElem_toList_eq]

theorem getElem?_toList_rco {m n : Int} {i : Nat} :
    (m...n).toList[i]? = if i < (n - m).toNat then some (m + i) else none := by
  simp [Rco.getElem?_toList_eq, Option.filter_some,
    show m + ↑i < n ↔ i < (n - m).toNat by omega]

@[simp]
theorem getElem?_toList_rco_eq_some_iff {m n : Int} {i : Nat} :
    (m...n).toList[i]? = some k ↔ i < (n - m).toNat ∧ m + i = k := by
  simp [getElem?_toList_rco, eq_comm]

@[simp]
theorem getElem?_toList_rco_eq_none_iff {m n : Int} {i : Nat} :
    (m...n).toList[i]? = none ↔ (n - m).toNat ≤ i := by
  simp [getElem?_toList_rco]

@[simp]
theorem isSome_getElem?_toList_rco_eq {m n : Int} {i : Nat} :
    (m...n).toList[i]?.isSome = (i < (n - m).toNat) := by
  simp

@[simp]
theorem isNone_getElem?_toList_rco_eq {m n : Int} {i : Nat} :
    (m...n).toList[i]?.isNone = ((n - m).toNat ≤ i) := by
  simp

@[simp 1001]
theorem getElem?_toList_rco_eq_some {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m...n).toList[i]? = some (m + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toList_rco_eq_none {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m...n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_rco {m n : Int} {i : Nat} :
    (m...n).toList[i]! = if i < (n - m).toNat then (m + i) else 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Int.default_eq_zero]
  split <;> simp

@[simp 1001]
theorem getElem!_toList_rco_eq_add {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m...n).toList[i]! = m + i := by
  simp [h]

@[simp 1001]
theorem getElem!_toList_rco_eq_zero {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m...n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_rco_eq_zero_iff {m n : Int} {i : Nat} :
    (m...n).toList[i]! = 0 ↔ (n - m).toNat ≤ i ∨ (m + i = 0) := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Int.default_eq_zero]
  split <;> (simp; omega)

theorem getElem!_toList_rco_ne_zero_iff {m n : Int} {i : Nat} :
    (m...n).toList[i]! ≠ 0 ↔ i < (n - m).toNat ∧ m + i ≠ 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_rco, Int.default_eq_zero]
  split <;> (simp; omega)

theorem getD_toList_rco {m n fallback : Int} {i : Nat} :
    (m...n).toList.getD i fallback = if i < (n - m).toNat then m + i else fallback := by
  by_cases h : i < (n - m).toNat <;> simp [h]

@[simp]
theorem getD_toList_rco_eq_add {m n fallback : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m...n).toList.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toList_rco_eq_fallback {m n fallback : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m...n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_rco_eq_if {m n : Int} :
    (m...n).toArray = if m < n then #[m] ++ ((m + 1)...n).toArray else #[] := by
  rw [Rco.toArray_eq_if_roo]
  simp [Roo.toArray_eq_match_rco]

theorem toArray_rco_succ_succ {m n : Int} :
    ((m+1)...(n+1)).toArray = (m...n).toArray.map (· + 1) := by
  simp [← succ_eq, Rco.toArray_succ_succ_eq_map]

theorem toArray_rco_succ_right_eq_append_map {m n : Int} (h : m ≤ n) :
    (m...(n + 1)).toArray = #[m] ++ (m...n).toArray.map (· + 1) := by
  rw [Rco.toArray_eq_if_roo, if_pos (Int.le_iff_lt_add_one.mp h), Roo.toArray_eq_match_rco]
  simp [toArray_rco_succ_succ]

@[simp]
theorem toArray_rco_eq_empty_iff {m n : Int} :
    (m...n).toArray = #[] ↔ n ≤ m := by
  simp [Rco.toArray_eq_if_roo]

theorem toArray_rco_ne_empty_iff {m n : Int} :
    (m...n).toArray ≠ #[] ↔ m < n := by
  simp

@[simp]
theorem toArray_rco_eq_empty {m n : Int} (h : n ≤ m) :
    (m...n).toArray = #[] := by
  simp [h]

@[simp]
theorem toArray_rco_eq_singleton_iff {m n : Int} :
    (m...n).toArray = #[k] ↔ n = m + 1 ∧ m = k := by
  rw [toArray_rco_eq_if]
  split <;> (simp; omega)

@[simp 1001]
theorem toArray_rco_eq_singleton {m n : Int} (h : n = m + 1) :
    (m...n).toArray = #[m] := by
  simp [h]

@[simp]
theorem toArray_rco_eq_singleton_append_iff {m n a : Int} :
    (m...n).toArray = #[a] ++ xs ↔ m = a ∧ m < n ∧ ((m + 1)...n).toArray = xs := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff]
  simp

theorem toArray_rco_eq_singleton_append {m n : Int} (h : m < n) :
    (m...n).toArray = #[m] ++ ((m + 1)...n).toArray := by
  simp [h]

theorem map_add_toArray_rco {m n k : Int} :
    (m...n).toArray.map (· + k) = ((m + k)...(n + k)).toArray := by
  simp only [← toArray_toList_rco, List.map_toArray, map_add_toList_rco]

theorem map_add_toArray_rco' {m n k : Int} :
    (m...n).toArray.map (k + ·) = ((k + m)...(k + n)).toArray := by
  simp [Int.add_comm, ← map_add_toArray_rco]

theorem toArray_rco_add_right_eq_map {m n : Int} :
    (m...(m + n)).toArray = (0...n).toArray.map (· + m) := by
  rw (occs := [1]) [← Int.zero_add m]
  simp [map_add_toArray_rco', Int.add_comm _ m]

theorem toArray_rco_succ_right_eq_push {m n : Int} (h : m ≤ n) :
    (m...(n + 1)).toArray = (m...n).toArray.push n := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff, toList_rco_succ_right_eq_append h]
  simp

theorem toArray_rco_eq_push {m n : Int} (h : m < n) :
    (m...n).toArray = (m...(n - 1)).toArray.push (n - 1) := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff, toList_rco_eq_append h]
  simp

theorem toArray_rco_eq_if_push {m n : Int} :
    (m...n).toArray = if m < n then (m...(n - 1)).toArray.push (n - 1) else #[] := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff]
  rw [toList_rco_eq_if_append, List.push_toArray]
  split <;> simp

theorem toArray_rco_add_add_eq_append {m : Int} {n k : Nat} :
    (m...(m + n + k)).toArray = (m...(m + n)).toArray ++ ((m + n)...(m + n + k)).toArray := by
  simp only [← toArray_toList_rco, List.toArray_eq_iff]
  simp [toList_rco_add_add_eq_append]

theorem toArray_rco_append_toArray_rco {l m n : Int} (h : l ≤ m) (h' : m ≤ n) :
    (l...m).toArray ++ (m...n).toArray = (l...n).toArray := by
  simp only [← toArray_toList_rco, List.eq_toArray_iff]
  simp [toList_rco_append_toList_rco h h']

@[simp]
theorem getElem_toArray_rco {m n : Int} {i : Nat} (_h : i < (m...n).toArray.size) :
    (m...n).toArray[i]'_h = m + i := by
  simp [Rco.getElem_toArray_eq]

theorem getElem?_toArray_rco {m n : Int} {i : Nat} :
    (m...n).toArray[i]? = if i < (n - m).toNat then some (m + i) else none := by
  rw [← toArray_toList_rco, List.getElem?_toArray, getElem?_toList_rco]

@[simp]
theorem getElem?_toArray_rco_eq_some_iff {m n : Int} {i : Nat} :
    (m...n).toArray[i]? = some k ↔ i < (n - m).toNat ∧ m + i = k := by
  simp [getElem?_toArray_rco, eq_comm]

@[simp]
theorem getElem?_toArray_rco_eq_none_iff {m n : Int} {i : Nat} :
    (m...n).toArray[i]? = none ↔ (n - m).toNat ≤ i := by
  simp [getElem?_toArray_rco]

@[simp]
theorem isSome_getElem?_toArray_rco_eq {m n : Int} {i : Nat} :
    (m...n).toArray[i]?.isSome = (i < (n - m).toNat) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_rco_eq {m n : Int} {i : Nat} :
    (m...n).toArray[i]?.isNone = ((n - m).toNat ≤ i) := by
  simp

@[simp 1001]
theorem getElem?_toArray_rco_eq_some {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m...n).toArray[i]? = some (m + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toArray_rco_eq_none {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m...n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_rco {m n : Int} {i : Nat} :
    (m...n).toArray[i]! = if i < (n - m).toNat then (m + i) else 0 := by
  simp only [← toArray_toList_rco, List.getElem!_toArray, getElem!_toList_rco]

@[simp 1001]
theorem getElem!_toArray_rco_eq_add {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m...n).toArray[i]! = m + i := by
  simp [h]

@[simp 1001]
theorem getElem!_toArray_rco_eq_zero {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m...n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_rco_eq_zero_iff {m n : Int} {i : Nat} :
    (m...n).toArray[i]! = 0 ↔ (n - m).toNat ≤ i ∨ m + i = 0 := by
  simp only [← toArray_toList_rco, List.getElem!_toArray, getElem!_toList_rco_eq_zero_iff]

theorem getElem!_toArray_rco_ne_zero_iff {m n : Int} {i : Nat} :
    (m...n).toArray[i]! ≠ 0 ↔ i < (n - m).toNat ∧ m + i ≠ 0 := by
  simp only [← toArray_toList_rco, List.getElem!_toArray, getElem!_toList_rco_ne_zero_iff]

theorem getD_toArray_rco {m n fallback : Int} {i : Nat} :
    (m...n).toArray.getD i fallback = if i < (n - m).toNat then m + i else fallback := by
  by_cases h : i < (n - m).toNat <;> simp [h]

@[simp]
theorem getD_toArray_rco_eq_add {m n fallback : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m...n).toArray.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toArray_rco_eq_fallback {m n fallback : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m...n).toArray.getD i fallback = fallback := by
  simp [h]

example {a b : Int} (h : 0 = (a - b).toNat) : a ≤ b := by
  simpa [Int.zero_eq_toNat_sub_iff] using h

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a...b` by
varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a...b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, the
statement holds for nonempty ranges {lean}`a...b` if it holds for the smaller range
{lean}`(a + 1)...b`.

The following is an example reproving {name}`length_toList_rco`.

```lean
example (a b : Int) : (a...b).toList.length = (b - a).toNat := by
  induction a, b using Int.induct_rco_left
  case base =>
    simp [Int.toList_rco_eq_nil, List.length_nil, Int.zero_eq_toNat_sub_iff, *]
  case step =>
    simp only [Int.toList_rco_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_rco_left (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a < b → motive (a + 1) b → motive a b)
    (a b : Int) : motive a b := by
  induction h : (b - a).toNat generalizing a b
  · apply base; omega
  · rename_i d ih
    apply step
    · omega
    · apply ih; omega

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a...b` by
varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a...b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, if the
statement holds for {lean}`a...b`, it also holds for the larger range {lean}`a...(b + 1)`.

The following is an example reproving {name}`length_toList_rco`.

```lean
example (a b : Int) : (a...b).toList.length = (b - a).toNat := by
  induction a, b using Int.induct_rco_right
  case base =>
    simp only [Int.toList_rco_eq_nil, List.length_nil, Int.zero_eq_toNat_sub_iff, *]
  case step a b hle ih =>
    rw [Int.toList_rco_eq_append (by omega),
      List.length_append, List.length_singleton, Int.add_sub_cancel, ih]
    omega
```
-/
theorem induct_rco_right (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Int) : motive a b := by
  induction h : (b - a).toNat generalizing a b
  · apply base; omega
  · rename_i d ih
    rw [show b = b - 1 + 1 by omega]
    apply step
    · omega
    · apply ih
      omega

theorem toList_rcc_eq_toList_rco {m n : Int} :
    (m...=n).toList = (m...(n + 1)).toList :=
  Rcc.toList_eq_toList_rco

@[simp]
theorem toList_toArray_rcc {m n : Int} :
    (m...=n).toArray.toList = (m...=n).toList :=
  Rcc.toList_toArray

@[simp]
theorem toArray_toList_rcc {m n : Int} :
    (m...=n).toList.toArray = (m...=n).toArray :=
  Rcc.toArray_toList

theorem toList_rcc_eq_if {m n : Int} :
    (m...=n).toList = if m ≤ n then m :: ((m + 1)...=n).toList else [] := by
  rw [toList_rcc_eq_toList_rco, toList_rcc_eq_toList_rco, toList_rco_eq_if]
  split <;> (simp; omega)

theorem toList_rcc_succ_succ {m n : Int} :
    ((m+1)...=(n+1)).toList = (m...=n).toList.map (· + 1) := by
  simp [← succ_eq, toList_rcc_eq_toList_rco, Rco.toList_succ_succ_eq_map]

theorem toList_rcc_succ_right_eq_cons_map {m n : Int} (h : m ≤ n + 1) :
    (m...=(n + 1)).toList = m :: (m...=n).toList.map (· + 1) := by
  simp [toList_rcc_eq_toList_rco, toList_rco_succ_succ]; omega

@[simp]
theorem toList_rcc_eq_nil_iff {m n : Int} :
    (m...=n).toList = [] ↔ n < m := by
  simp [toList_rcc_eq_toList_rco]; omega

theorem toList_rcc_ne_nil_iff {m n : Int} :
    (m...=n).toList ≠ [] ↔ m ≤ n := by
  simp [toList_rcc_eq_toList_rco]; omega

@[simp 1001]
theorem toList_rcc_eq_nil {m n : Int} (h : n < m) :
    (m...=n).toList = [] := by
  simp; omega

@[simp]
theorem toList_rcc_eq_singleton_iff {m n : Int} :
    (m...=n).toList = [k] ↔ n = m ∧ m = k := by
  simp [toList_rcc_eq_toList_rco]; omega

@[simp 1001]
theorem toList_rcc_eq_singleton {m n : Int} (h : n = m) :
    (m...=n).toList = [m] := by
  simp [h]

@[simp]
theorem toList_rcc_eq_cons_iff {m n a : Int} :
    (m...=n).toList = a :: xs ↔ m = a ∧ m ≤ n ∧ ((m + 1)...=n).toList = xs := by
  simp [toList_rcc_eq_toList_rco]; omega

theorem toList_rcc_eq_cons {m n : Int} (h : m ≤ n) :
    (m...=n).toList = m :: ((m + 1)...=n).toList := by
  simp; omega

theorem map_add_toList_rcc {m n k : Int} :
    (m...=n).toList.map (· + k) = ((m + k)...=(n + k)).toList := by
  simp [toList_rcc_eq_toList_rco, map_add_toList_rco, show n + 1 + k = n + k + 1 by omega]

theorem map_add_toList_rcc' {m n k : Int} :
    (m...=n).toList.map (k + ·) = ((k + m)...=(k + n)).toList := by
  simp [toList_rcc_eq_toList_rco, map_add_toList_rco', ← Int.add_assoc]

theorem toList_rcc_add_right_eq_map {m n : Int} :
    (m...=(m + n)).toList = (0...=n).toList.map (· + m) := by
  simp [toList_rcc_eq_toList_rco, show m + n + 1 = m + (n + 1) by omega, toList_rco_add_right_eq_map]

@[simp]
theorem toList_rcc_eq_append {m n : Int} (h : m ≤ n) :
    (m...=n).toList = (m...n).toList ++ [n] := by
  simp [toList_rcc_eq_toList_rco, toList_rco_eq_append (Int.le_iff_lt_add_one.mp h)]

theorem toList_rcc_succ_right_eq_append {m n : Int} (h : m ≤ n + 1) :
    (m...=(n + 1)).toList = (m...=n).toList ++ [n + 1] := by
  rw [toList_rcc_eq_append (by omega)]
  simp [toList_rcc_eq_toList_rco]

@[simp]
theorem getElem_toList_rcc {m n : Int} {i : Nat} (_h : i < (m...=n).toList.length) :
    (m...=n).toList[i]'_h = m + i := by
  simp [toList_rcc_eq_toList_rco]

theorem getElem?_toList_rcc {m n : Int} {i : Nat} :
    (m...=n).toList[i]? = if i < (n + 1 - m).toNat then some (m + i) else none := by
  simp [toList_rcc_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem getElem?_toList_rcc_eq_some_iff {m n : Int} {i : Nat} :
    (m...=n).toList[i]? = some k ↔ i < (n + 1 - m).toNat ∧ m + i = k := by
  simp [toList_rcc_eq_toList_rco, getElem?_toList_rco, eq_comm]

@[simp]
theorem getElem?_toList_rcc_eq_none_iff {m n : Int} {i : Nat} :
    (m...=n).toList[i]? = none ↔ (n + 1 - m).toNat ≤ i := by
  simp [toList_rcc_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem isSome_getElem?_toList_rcc_eq {m n : Int} {i : Nat} :
    (m...=n).toList[i]?.isSome = (i < (n + 1 - m).toNat) := by
  simp

@[simp]
theorem isNone_getElem?_toList_rcc_eq {m n : Int} {i : Nat} :
    (m...=n).toList[i]?.isNone = ((n + 1 - m).toNat ≤ i) := by
  simp

@[simp]
theorem getElem?_toList_rcc_eq_some {m n : Int} {i : Nat} (h : i < (n + 1 - m).toNat) :
    (m...=n).toList[i]? = some (m + i) := by
  simp [h]

@[simp]
theorem getElem?_toList_rcc_eq_none {m n : Int} {i : Nat} (h : (n + 1 - m).toNat ≤ i) :
    (m...=n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_rcc {m n : Int} {i : Nat} :
    (m...=n).toList[i]! = if i < (n + 1 - m).toNat then m + i else 0 := by
  simp only [toList_rcc_eq_toList_rco, getElem!_toList_rco]

@[simp]
theorem getElem!_toList_rcc_eq_add {m n : Int} {i : Nat} (h : i < (n + 1 - m).toNat) :
    (m...=n).toList[i]! = m + i := by
  simp [h]

@[simp]
theorem getElem!_toList_rcc_eq_zero {m n : Int} {i : Nat} (h : (n + 1 - m).toNat ≤ i) :
    (m...=n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_rcc_eq_zero_iff {m n : Int} {i : Nat} :
    (m...=n).toList[i]! = 0 ↔ (n + 1 - m).toNat ≤ i ∨ (m + i = 0) := by
  simp only [toList_rcc_eq_toList_rco, getElem!_toList_rco_eq_zero_iff]

theorem getElem!_toList_rcc_ne_zero_iff {m n : Int} {i : Nat} :
    (m...=n).toList[i]! ≠ 0 ↔ i < (n + 1 - m).toNat ∧ m + i ≠ 0 := by
  simp only [toList_rcc_eq_toList_rco, getElem!_toList_rco_ne_zero_iff]

theorem getD_toList_rcc {m n fallback : Int} {i : Nat} :
    (m...=n).toList.getD i fallback = if i < (n + 1 - m).toNat then (m + i) else fallback := by
  by_cases h : i < (n + 1 - m).toNat <;> simp [h]

@[simp]
theorem getD_toList_rcc_eq_add {m n fallback : Int} {i : Nat} (h : i < (n + 1 - m).toNat) :
    (m...=n).toList.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toList_rcc_eq_fallback {m n fallback : Int} {i : Nat} (h : (n + 1 - m).toNat ≤ i) :
    (m...=n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_rcc_eq_toArray_rco {m n : Int} :
    (m...=n).toArray = (m...(n + 1)).toArray := by
  simp [← toArray_toList_rcc, toList_rcc_eq_toList_rco]

theorem toArray_rcc_eq_if {m n : Int} :
    (m...=n).toArray = if m ≤ n then #[m] ++ ((m + 1)...=n).toArray else #[] := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff]
  rw [toList_rcc_eq_if]
  split <;> simp

theorem toArray_rcc_succ_succ {m n : Int} :
    ((m+1)...=(n+1)).toArray = (m...=n).toArray.map (· + 1) := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff, toList_rcc_succ_succ]
  simp

theorem toArray_rcc_succ_right_eq_append_map {m n : Int} (h : m ≤ n + 1) :
    (m...=(n + 1)).toArray = #[m] ++ (m...=n).toArray.map (· + 1) := by
  simp only [← toArray_toList_rcc, List.toArray_eq_iff, toList_rcc_succ_right_eq_cons_map h]
  simp

@[simp]
theorem toArray_rcc_eq_empty_iff {m n : Int} :
    (m...=n).toArray = #[] ↔ n < m := by
  simp [toArray_rcc_eq_toArray_rco, Int.add_one_le_iff]

theorem toArray_rcc_ne_empty_iff {m n : Int} :
    (m...=n).toArray ≠ #[] ↔ m ≤ n := by
  simp [toArray_rcc_eq_toArray_rco, Int.add_one_le_iff]

@[simp 1001]
theorem toArray_rcc_eq_empty {m n : Int} (h : n < m) :
    (m...=n).toArray = #[] := by
  simp; omega

@[simp]
theorem toArray_rcc_eq_singleton_iff {m n : Int} :
    (m...=n).toArray = #[k] ↔ n = m ∧ m = k := by
  simp [toArray_rcc_eq_toArray_rco]

@[simp 1001]
theorem toArray_rcc_eq_singleton {m n : Int} (h : n = m) :
    (m...=n).toArray = #[m] := by
  simp [h]

@[simp]
theorem toArray_rcc_eq_singleton_append_iff {m n a : Int} :
    (m...=n).toArray = #[a] ++ xs ↔ m = a ∧ m ≤ n ∧ ((m + 1)...=n).toArray = xs := by
  simp [toArray_rcc_eq_toArray_rco]; omega

theorem toArray_rcc_eq_singleton_append {m n : Int} (h : m ≤ n) :
    (m...=n).toArray = #[m] ++ ((m + 1)...=n).toArray := by
  simp; omega

theorem map_add_toArray_rcc {m n k : Int} :
    (m...=n).toArray.map (· + k) = ((m + k)...=(n + k)).toArray := by
  simp [toArray_rcc_eq_toArray_rco, map_add_toArray_rco, show n + 1 + k = n + k + 1 by omega]

theorem map_add_toArray_rcc' {m n k : Int} :
    (m...=n).toArray.map (k + ·) = ((k + m)...=(k + n)).toArray := by
  simp [toArray_rcc_eq_toArray_rco, map_add_toArray_rco', ← Int.add_assoc]

theorem toArray_rcc_add_right_eq_map {m n : Int} :
    (m...=(m + n)).toArray = (0...=n).toArray.map (· + m) := by
  simp [toArray_rcc_eq_toArray_rco, show m + n + 1 = m + (n + 1) by omega, toArray_rco_add_right_eq_map]

@[simp]
theorem toArray_rcc_eq_push {m n : Int} (h : m ≤ n) :
    (m...=n).toArray = (m...n).toArray.push n := by
  simp [toArray_rcc_eq_toArray_rco, toArray_rco_eq_push (Int.lt_add_one_of_le h)]

theorem toArray_rcc_succ_right_eq_push {m n : Int} (h : m ≤ n + 1) :
    (m...=(n + 1)).toArray = (m...=n).toArray.push (n + 1) := by
  rw [toArray_rcc_eq_push (by omega)]
  simp [toArray_rcc_eq_toArray_rco]

@[simp]
theorem getElem_toArray_rcc {m n : Int} {i : Nat} (_h : i < (m...=n).toArray.size) :
    (m...=n).toArray[i]'_h = m + i := by
  simp [toArray_rcc_eq_toArray_rco]

theorem getElem?_toArray_rcc {m n : Int} {i : Nat} :
    (m...=n).toArray[i]? = if i < (n + 1 - m).toNat then some (m + i) else none := by
  simp [toArray_rcc_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem getElem?_toArray_rcc_eq_some_iff {m n : Int} {i : Nat} :
    (m...=n).toArray[i]? = some k ↔ i < (n + 1 - m).toNat ∧ m + i = k := by
  simp [toArray_rcc_eq_toArray_rco, getElem?_toArray_rco, eq_comm]

@[simp]
theorem getElem?_toArray_rcc_eq_none_iff {m n : Int} {i : Nat} :
    (m...=n).toArray[i]? = none ↔ (n + 1 - m).toNat ≤ i := by
  simp [toArray_rcc_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem isSome_getElem?_toArray_rcc_eq {m n : Int} {i : Nat} :
    (m...=n).toArray[i]?.isSome = (i < (n + 1 - m).toNat) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_rcc_eq {m n : Int} {i : Nat} :
    (m...=n).toArray[i]?.isNone = ((n + 1 - m).toNat ≤ i) := by
  simp

@[simp]
theorem getElem?_toArray_rcc_eq_some {m n : Int} {i : Nat} (h : i < (n + 1 - m).toNat) :
    (m...=n).toArray[i]? = some (m + i) := by
  simp [h]

@[simp]
theorem getElem?_toArray_rcc_eq_none {m n : Int} {i : Nat} (h : (n + 1 - m).toNat ≤ i) :
    (m...=n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_rcc {m n : Int} {i : Nat} :
    (m...=n).toArray[i]! = if i < (n + 1 - m).toNat then m + i else 0 := by
  simp only [toArray_rcc_eq_toArray_rco, getElem!_toArray_rco]

@[simp]
theorem getElem!_toArray_rcc_eq_add {m n : Int} {i : Nat} (h : i < (n + 1 - m).toNat) :
    (m...=n).toArray[i]! = m + i := by
  simp [h]

@[simp]
theorem getElem!_toArray_rcc_eq_zero {m n : Int} {i : Nat} (h : (n + 1 - m).toNat ≤ i) :
    (m...=n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_rcc_eq_zero_iff {m n : Int} {i : Nat} :
    (m...=n).toArray[i]! = 0 ↔ (n + 1 - m).toNat ≤ i ∨ (m + i = 0) := by
  simp only [toArray_rcc_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff]

theorem getElem!_toArray_rcc_ne_zero_iff {m n : Int} {i : Nat} :
    (m...=n).toArray[i]! ≠ 0 ↔ i < (n + 1 - m).toNat ∧ m + i ≠ 0 := by
  simp only [toArray_rcc_eq_toArray_rco, getElem!_toArray_rco_ne_zero_iff]

theorem getD_toArray_rcc {m n fallback : Int} {i : Nat} :
    (m...=n).toArray.getD i fallback = if i < (n + 1 - m).toNat then (m + i) else fallback := by
  by_cases h : i < (n + 1 - m).toNat <;> simp [h]

@[simp]
theorem getD_toArray_rcc_eq_add {m n fallback : Int} {i : Nat} (h : i < (n + 1 - m).toNat) :
    (m...=n).toArray.getD i fallback = m + i := by
  simp [h]

@[simp]
theorem getD_toArray_rcc_eq_fallback {m n fallback : Int} {i : Nat} (h : (n + 1 - m).toNat ≤ i) :
    (m...=n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a...=b` by
varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b < a`, the statement holds for the empty range {lean}`a...=b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, the
statement holds for nonempty ranges {lean}`a...b` if it holds for the smaller range
{lean}`(a + 1)...=b`.

The following is an example reproving {name}`length_toList_rcc`.

```lean
example (a b : Int) : (a...=b).toList.length = (b + 1 - a).toNat := by
  induction a, b using Int.induct_rcc_left
  case base =>
    simp only [Int.toList_rcc_eq_nil, List.length_nil, Int.zero_eq_toNat_sub_iff, *]; omega
  case step =>
    simp only [Int.toList_rcc_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_rcc_left (motive : Int → Int → Prop)
    (base : ∀ a b, b < a → motive a b)
    (step : ∀ a b, a ≤ b → motive (a + 1) b → motive a b)
    (a b : Int) : motive a b := by
  induction h : (b + 1 - a).toNat generalizing a b
  · apply base; omega
  · rename_i d ih
    apply step
    · omega
    · apply ih; omega

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a...=b` by
varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a`, the statement holds for the subsingleton range {lean}`a...=b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, if the
statement holds for {lean}`a...=b`, it also holds for the larger range {lean}`a...=(b + 1)`.

The following is an example reproving {name}`length_toList_rcc`.

```lean
example (a b : Int) : (a...=b).toList.length = (b + 1 - a).toNat := by
  induction a, b using Int.induct_rcc_right
  case base a b hge =>
    by_cases h : b < a
    · simp only [Int.toList_rcc_eq_nil, List.length_nil, *]
      omega
    · have : b = a := by omega
      simp only [Int.toList_rcc_eq_singleton, List.length_singleton,
        Int.sub_eq_iff_eq_add'.mpr rfl, Int.toNat_one, *]
  case step a b hle ih =>
    rw [Int.toList_rcc_succ_right_eq_append (by omega), List.length_append,
      List.length_singleton, ih] <;> omega
```
-/
theorem induct_rcc_right (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Int) : motive a b := by
  induction h : (b - a).toNat generalizing a b
  · apply base; omega
  · rename_i d ih
    rw [show b = b - 1 + 1 by omega]
    apply step
    · omega
    · apply ih
      omega

theorem toList_roo_eq_toList_rco {m n : Int} :
    (m<...n).toList = ((m + 1)...n).toList :=
  Roo.toList_eq_match_rco

@[simp]
theorem toList_toArray_roo {m n : Int} :
    (m<...n).toArray.toList = (m<...n).toList :=
  Roo.toList_toArray

@[simp]
theorem toArray_toList_roo {m n : Int} :
    (m<...n).toList.toArray = (m<...n).toArray :=
  Roo.toArray_toList

theorem toList_roo_eq_if {m n : Int} :
    (m<...n).toList = if m + 1 < n then (m + 1) :: ((m + 1)<...n).toList else [] := by
  simp only [toList_roo_eq_toList_rco]
  rw [toList_rco_eq_if]

theorem toList_roo_succ_succ {m n : Int} :
    ((m+1)<...(n+1)).toList = (m<...n).toList.map (· + 1) := by
  simp [toList_roo_eq_toList_rco, toList_rco_succ_succ]

theorem toList_roo_succ_right_eq_cons_map {m n : Int} (h : m < n) :
    (m<...(n + 1)).toList = (m + 1) :: (m<...n).toList.map (· + 1) := by
  simp [toList_roo_eq_toList_rco, toList_rco_succ_right_eq_cons_map h]

@[simp]
theorem toList_roo_eq_nil_iff {m n : Int} :
    (m<...n).toList = [] ↔ n ≤ m + 1 := by
  simp [toList_roo_eq_toList_rco]

theorem toList_roo_ne_nil_iff {m n : Int} :
    (m<...n).toList ≠ [] ↔ m + 1 < n := by
  simp

@[simp 1001]
theorem toList_roo_eq_nil {m n : Int} (h : n ≤ m + 1) :
    (m<...n).toList = [] := by
  simp [h]

@[simp]
theorem toList_roo_eq_singleton_iff {m n : Int} :
    (m<...n).toList = [k] ↔ n = m + 2 ∧ m + 1 = k := by
  simp [toList_roo_eq_toList_rco]; omega

@[simp 1001]
theorem toList_roo_eq_singleton {m n : Int} (h : n = m + 2) :
    (m<...n).toList = [m + 1] := by
  simp [h, toList_roo_eq_toList_rco]; omega

@[simp]
theorem toList_roo_eq_cons_iff {m n a : Int} :
    (m<...n).toList = a :: xs ↔ m + 1 = a ∧ m + 1 < n ∧ ((m + 1)<...n).toList = xs := by
  simp [toList_roo_eq_toList_rco]

theorem toList_roo_eq_cons {m n : Int} (h : m + 1 < n) :
    (m<...n).toList = (m + 1) :: ((m + 1)<...n).toList := by
  simp; omega

theorem map_add_toList_roo {m n k : Int} :
    (m<...n).toList.map (· + k) = ((m + k)<...(n + k)).toList := by
  simp [toList_roo_eq_toList_rco, map_add_toList_rco, show m + 1 + k = m + k + 1 by omega]

theorem map_add_toList_roo' {m n k : Int} :
    (m<...n).toList.map (k + ·) = ((k + m)<...(k + n)).toList := by
  simp [toList_roo_eq_toList_rco, map_add_toList_rco', show k + (m + 1) = k + m + 1 by omega]

theorem toList_roo_add_right_eq_map {m n : Int} :
    (m<...(m + 1 + n)).toList = (0...n).toList.map (· + m + 1) := by
  simp [toList_roo_eq_toList_rco, toList_rco_add_right_eq_map, show ∀ a, a + (m + 1) = (a + m) + 1 by omega]

theorem toList_roo_succ_right_eq_append {m n : Int} (h : m < n) :
    (m<...(n + 1)).toList = (m<...n).toList ++ [n] := by
  simp [toList_roo_eq_toList_rco, toList_rco_succ_right_eq_append h]

@[simp]
theorem toList_roo_eq_append {m n : Int} (h : m + 1 < n) :
    (m<...n).toList = (m<...(n - 1)).toList ++ [n - 1] := by
  simp [toList_roo_eq_toList_rco, toList_rco_eq_append h]

@[simp]
theorem getElem_toList_roo {m n : Int} {i : Nat} (_h : i < (m<...n).toList.length) :
    (m<...n).toList[i]'_h = m + 1 + i := by
  simp [toList_roo_eq_toList_rco]

theorem getElem?_toList_roo {m n : Int} {i : Nat} :
    (m<...n).toList[i]? = if i < (n - (m + 1)).toNat then some (m + 1 + i) else none := by
  simp [toList_roo_eq_toList_rco, getElem?_toList_rco]

@[simp]
theorem getElem?_toList_roo_eq_some_iff {m n : Int} {i : Nat} :
    (m<...n).toList[i]? = some k ↔ i < (n - (m + 1)).toNat ∧ m + 1 + i = k := by
  simp [toList_roo_eq_toList_rco]

@[simp]
theorem getElem?_toList_roo_eq_none_iff {m n : Int} {i : Nat} :
    (m<...n).toList[i]? = none ↔ (n - (m + 1)).toNat ≤ i := by
  simp [toList_roo_eq_toList_rco]

@[simp]
theorem isSome_getElem?_toList_roo_eq {m n : Int} {i : Nat} :
    (m<...n).toList[i]?.isSome = (i < (n - (m + 1)).toNat) := by
  simp [toList_roo_eq_toList_rco]

@[simp]
theorem isNone_getElem?_toList_roo_eq {m n : Int} {i : Nat} :
    (m<...n).toList[i]?.isNone = ((n - (m + 1)).toNat ≤ i) := by
  simp [toList_roo_eq_toList_rco]

@[simp 1001]
theorem getElem?_toList_roo_eq_some {m n : Int} {i : Nat} (h : i < (n - (m + 1)).toNat) :
    (m<...n).toList[i]? = some (m + 1 + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toList_roo_eq_none {m n : Int} (h : (n - (m + 1)).toNat ≤ i) :
    (m<...n).toList[i]? = none := by
  simp [h, toList_roo_eq_toList_rco]

theorem getElem!_toList_roo {m n : Int} {i : Nat} :
    (m<...n).toList[i]! = if i < (n - (m + 1)).toNat then (m + 1 + i) else 0 := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_toList_roo, Int.default_eq_zero]
  split <;> simp

@[simp 1001]
theorem getElem!_toList_roo_eq_add {m n : Int} {i : Nat} (h : i < (n - (m + 1)).toNat) :
    (m<...n).toList[i]! = m + 1 + i := by
  simp [h]

@[simp 1001]
theorem getElem!_toList_roo_eq_zero {m n : Int} {i : Nat} (h : (n - (m + 1)).toNat ≤ i) :
    (m<...n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_roo_eq_zero_iff {m n : Int} {i : Nat} :
    (m<...n).toList[i]! = 0 ↔ (n - (m + 1)).toNat ≤ i ∨ m + i = -1 := by
  rw [toList_roo_eq_toList_rco, getElem!_toList_rco_eq_zero_iff]
  omega

theorem zero_ne_getElem!_toList_roo_iff {m n : Int} {i : Nat} :
    (m<...n).toList[i]! ≠ 0 ↔ i < (n - (m + 1)).toNat ∧ m + i ≠ -1 := by
  rw [toList_roo_eq_toList_rco, getElem!_toList_rco_ne_zero_iff]
  omega

theorem getD_toList_roo {m n fallback : Int} {i : Nat} :
    (m<...n).toList.getD i fallback = if i < (n - (m + 1)).toNat then (m + 1 + i) else fallback := by
  by_cases h : i < (n - (m + 1)).toNat <;> simp [h, toList_roo_eq_toList_rco]

@[simp]
theorem getD_toList_roo_eq_add {m n fallback : Int} {i : Nat} (h : i < (n - (m + 1)).toNat) :
    (m<...n).toList.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toList_roo_eq_fallback {m n fallback : Int} {i : Nat} (h : (n - (m + 1)).toNat ≤ i) :
    (m<...n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_roo_eq_toArray_rco {m n : Int} :
    (m<...n).toArray = ((m + 1)...n).toArray := by
  simp [Roo.toArray_eq_match_rco]

theorem toArray_roo_eq_if {m n : Int} :
    (m<...n).toArray = if m + 1 < n then #[m + 1] ++ ((m + 1)<...n).toArray else #[] := by
  simp only [toArray_roo_eq_toArray_rco]
  rw [toArray_rco_eq_if]

theorem toArray_roo_succ_succ {m n : Int} :
    ((m+1)<...(n+1)).toArray = (m<...n).toArray.map (· + 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_succ_succ, ]

theorem toArray_roo_succ_right_eq_append_map {m n : Int} (h : m < n) :
    (m<...(n + 1)).toArray = #[m + 1] ++ (m<...n).toArray.map (· + 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_succ_right_eq_append_map h]

@[simp]
theorem toArray_roo_eq_nil_iff {m n : Int} :
    (m<...n).toArray = #[] ↔ n ≤ m + 1 := by
  simp [toArray_roo_eq_toArray_rco]

theorem toArray_roo_ne_nil_iff {m n : Int} :
    (m<...n).toArray ≠ #[] ↔ m + 1 < n := by
  simp [toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem toArray_roo_eq_nil {m n : Int} (h : n ≤ m + 1) :
    (m<...n).toArray = #[] := by
  simp [h]

@[simp]
theorem toArray_roo_eq_singleton_iff {m n : Int} :
    (m<...n).toArray = #[k] ↔ n = m + 2 ∧ m + 1 = k := by
  simp [toArray_roo_eq_toArray_rco]; omega

@[simp 1001]
theorem toArray_roo_eq_singleton {m n : Int} (h : n = m + 2) :
    (m<...n).toArray = #[m + 1] := by
  simp [h]

@[simp]
theorem toArray_roo_eq_singleton_append_iff {m n a : Int} :
    (m<...n).toArray = #[a] ++ xs ↔ m + 1 = a ∧ m + 1 < n ∧ ((m + 1)<...n).toArray = xs := by
  simp [toArray_roo_eq_toArray_rco]

theorem toArray_roo_eq_singleton_append {m n : Int} (h : m + 1 < n) :
    (m<...n).toArray = #[m + 1] ++ ((m + 1)<...n).toArray := by
  simp [h]

theorem map_add_toArray_roo {m n k : Int} :
    (m<...n).toArray.map (· + k) = ((m + k)<...(n + k)).toArray := by
  simp [toArray_roo_eq_toArray_rco, map_add_toArray_rco, show m + 1 + k = m + k + 1 by omega]

theorem map_add_toArray_roo' {m n k : Int} :
    (m<...n).toArray.map (k + ·) = ((k + m)<...(k + n)).toArray := by
  simp [toArray_roo_eq_toArray_rco, map_add_toArray_rco', show k + (m + 1) = k + m + 1 by omega]

theorem toArray_roo_add_right_eq_map {m n : Int} :
    (m<...(m + 1 + n)).toArray = (0...n).toArray.map (· + m + 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_add_right_eq_map,
    show ∀ a, a + (m + 1) = (a + m) + 1 by omega]

theorem toArray_roo_succ_right_eq_push {m n : Int} (h : m < n) :
    (m<...(n + 1)).toArray = (m<...n).toArray.push n := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_succ_right_eq_push h]

@[simp]
theorem toArray_roo_eq_push {m n : Int} (h : m + 1 < n) :
    (m<...n).toArray = (m<...(n - 1)).toArray.push (n - 1) := by
  simp [toArray_roo_eq_toArray_rco, toArray_rco_eq_push h]

@[simp]
theorem getElem_toArray_roo {m n : Int} {i : Nat} (_h : i < (m<...n).toArray.size) :
    (m<...n).toArray[i]'_h = m + 1 + i := by
  simp [toArray_roo_eq_toArray_rco]

theorem getElem?_toArray_roo {m n : Int} {i : Nat} :
    (m<...n).toArray[i]? = if i < (n - (m + 1)).toNat then some (m + 1 + i) else none := by
  simp [toArray_roo_eq_toArray_rco, getElem?_toArray_rco]

@[simp]
theorem getElem?_toArray_roo_eq_some_iff {m n : Int} {i : Nat} :
    (m<...n).toArray[i]? = some k ↔ i < (n - (m + 1)).toNat ∧ m + 1 + i = k := by
  simp [toArray_roo_eq_toArray_rco]

@[simp]
theorem getElem?_toArray_roo_eq_none_iff {m n : Int} {i : Nat} :
    (m<...n).toArray[i]? = none ↔ (n - (m + 1)).toNat ≤ i := by
  simp [toArray_roo_eq_toArray_rco]

@[simp]
theorem isSome_getElem?_toArray_roo_eq {m n : Int} {i : Nat} :
    (m<...n).toArray[i]?.isSome = (i < (n - (m + 1)).toNat) := by
  simp [toArray_roo_eq_toArray_rco]

@[simp]
theorem isNone_getElem?_toArray_roo_eq {m n : Int} {i : Nat} :
    (m<...n).toArray[i]?.isNone = ((n - (m + 1)).toNat ≤ i) := by
  simp [toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem getElem?_toArray_roo_eq_some {m n : Int} {i : Nat} (h : i < (n - (m + 1)).toNat) :
    (m<...n).toArray[i]? = some (m + 1 + i) := by
  simp [h]

@[simp 1001]
theorem getElem?_toArray_roo_eq_none {m n : Int} {i : Nat} (h : (n - (m + 1)).toNat ≤ i) :
    (m<...n).toArray[i]? = none := by
  simp [h, toArray_roo_eq_toArray_rco]

theorem getElem!_toArray_roo {m n : Int} {i : Nat} :
    (m<...n).toArray[i]! = if i < (n - (m + 1)).toNat then (m + 1 + i) else 0 := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, getElem?_toArray_roo,
    Int.default_eq_zero]
  split <;> simp

@[simp 1001]
theorem getElem!_toArray_roo_eq_add {m n : Int} {i : Nat} (h : i < (n - (m + 1)).toNat) :
    (m<...n).toArray[i]! = m + 1 + i := by
  simp [h, toArray_roo_eq_toArray_rco]

@[simp 1001]
theorem getElem!_toArray_roo_eq_zero {m n : Int} {i : Nat} (h : (n - (m + 1)).toNat ≤ i) :
    (m<...n).toArray[i]! = 0 := by
  simp [h, toArray_roo_eq_toArray_rco]

theorem getElem!_toArray_roo_eq_zero_iff {m n : Int} {i : Nat} :
    (m<...n).toArray[i]! = 0 ↔ (n - (m + 1)).toNat ≤ i ∨ m + i = -1 := by
  rw [toArray_roo_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff]
  omega

theorem getElem!_toArray_roo_ne_zero_iff {m n : Int} {i : Nat} :
    (m<...n).toArray[i]! ≠ 0 ↔ i < (n - (m + 1)).toNat ∧ m + i ≠ -1 := by
  rw [toArray_roo_eq_toArray_rco, getElem!_toArray_rco_ne_zero_iff]
  omega

theorem getD_toArray_roo {m n fallback : Int} {i : Nat} :
    (m<...n).toArray.getD i fallback = if i < (n - (m + 1)).toNat then (m + 1 + i) else fallback := by
  by_cases h : i < (n - (m + 1)).toNat <;> simp [h, toArray_roo_eq_toArray_rco]

@[simp]
theorem getD_toArray_roo_eq_add {m n fallback : Int} {i : Nat} (h : i < (n - (m + 1)).toNat) :
    (m<...n).toArray.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toArray_roo_eq_fallback {m n fallback : Int} {i : Nat} (h : (n - (m + 1)).toNat ≤ i) :
    (m<...n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a<...b` by
varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a + 1`, the statement holds for the empty range {lean}`a<...b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, the
statement holds for nonempty ranges {lean}`a<...b` if it holds for the smaller range
{lean}`(a + 1)<...b`.

The following is an example reproving {name}`length_toList_roo`.

```lean
example (a b : Int) : (a<...b).toList.length = (b - a - 1).toNat := by
  induction a, b using Int.induct_roo_left
  case base =>
    simp only [Int.toList_roo_eq_nil, List.length_nil, Int.zero_eq_toNat_sub_iff, *]; omega
  case step =>
    simp only [Int.toList_roo_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_roo_left (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a + 1 → motive a b)
    (step : ∀ a b, a + 1 < b → motive (a + 1) b → motive a b)
    (a b : Int) : motive a b := by
  induction h : (b - a - 1).toNat generalizing a b
  · apply base; omega
  · rename_i d ih
    apply step
    · omega
    · apply ih; omega

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a<...b` by
varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a + 1`, the statement holds for the empty range {lean}`a<...b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, if the
statement holds for {lean}`a<...b`, it also holds for the larger range {lean}`a<...(b + 1)`.

The following is an example reproving {name}`length_toList_roo`.

```lean
example (a b : Int) : (a<...b).toList.length = (b - a - 1).toNat := by
  induction a, b using Int.induct_roo_right
  case base =>
    simp only [Int.toList_roo_eq_nil, List.length_nil, *]; omega
  case step a b hle ih =>
    rw [Int.toList_roo_eq_append (by omega),
      List.length_append, List.length_singleton, Int.add_sub_cancel, ih]
    omega
```
-/
theorem induct_roo_right (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a + 1 → motive a b)
    (step : ∀ a b, a + 1 ≤ b → motive a b → motive a (b + 1))
    (a b : Int) : motive a b := by
  induction h : (b - a - 1).toNat generalizing a b
  · apply base; omega
  · rename_i d ih
    rw [show b = b - 1 + 1 by omega]
    apply step
    · omega
    · apply ih
      omega

theorem toList_roc_eq_toList_roo {m n : Int} :
    (m<...=n).toList = (m<...(n + 1)).toList :=
  Roc.toList_eq_toList_roo

theorem toList_roc_eq_toList_rco {m n : Int} :
    (m<...=n).toList = ((m + 1)...(n + 1)).toList := by
  simp [toList_roc_eq_toList_roo, toList_roo_eq_toList_rco]

theorem toList_roc_eq_toList_rcc {m n : Int} :
    (m<...=n).toList = ((m + 1)...=n).toList := by
  simp [toList_roc_eq_toList_rco, toList_rcc_eq_toList_rco]

@[simp]
theorem toList_toArray_roc {m n : Int} :
    (m<...=n).toArray.toList = (m<...=n).toList :=
  Roc.toList_toArray

@[simp]
theorem toArray_toList_roc {m n : Int} :
    (m<...=n).toList.toArray = (m<...=n).toArray :=
  Roc.toArray_toList

theorem toList_roc_eq_if {m n : Int} :
    (m<...=n).toList = if m + 1 ≤ n then (m + 1) :: ((m + 1)<...=n).toList else [] := by
  rw [toList_roc_eq_toList_rco, toList_roc_eq_toList_rco, toList_rco_eq_if]
  split <;> (simp; omega)

theorem toList_roc_succ_succ {m n : Int} :
    ((m+1)<...=(n+1)).toList = (m<...=n).toList.map (· + 1) := by
  simp [← succ_eq, toList_roc_eq_toList_rco, Rco.toList_succ_succ_eq_map]

theorem toList_roc_succ_right_eq_cons_map {m n : Int} (h : m ≤ n) :
    (m<...=(n + 1)).toList = (m + 1) :: (m<...=n).toList.map (· + 1) := by
  simp only [toList_roc_eq_toList_rcc]
  rw [toList_rcc_succ_right_eq_cons_map (by omega)]

@[simp]
theorem toList_roc_eq_nil_iff {m n : Int} :
    (m<...=n).toList = [] ↔ n ≤ m := by
  simp [toList_roc_eq_toList_rco]

theorem toList_roc_ne_nil_iff {m n : Int} :
    (m<...=n).toList ≠ [] ↔ m < n := by
  simp

@[simp 1001]
theorem toList_roc_eq_nil {m n : Int} (h : n ≤ m) :
    (m<...=n).toList = [] := by
  simp; omega

@[simp]
theorem toList_roc_eq_singleton_iff {m n : Int} :
    (m<...=n).toList = [k] ↔ n = m + 1 ∧ m + 1 = k := by
  simp [toList_roc_eq_toList_rco]; omega

@[simp 1001]
theorem toList_roc_eq_singleton {m n : Int} (h : n = m + 1) :
    (m<...=n).toList = [m + 1] := by
  simp [h]

@[simp]
theorem toList_roc_eq_cons_iff {m n a : Int} :
    (m<...=n).toList = a :: xs ↔ m + 1 = a ∧ m < n ∧ ((m + 1)<...=n).toList = xs := by
  simp [toList_roc_eq_toList_rco]

theorem toList_roc_eq_cons {m n : Int} (h : m < n) :
    (m<...=n).toList = (m + 1) :: ((m + 1)<...=n).toList := by
  simp; omega

theorem map_add_toList_roc {m n k : Int} :
    (m<...=n).toList.map (· + k) = ((m + k)<...=(n + k)).toList := by
  simp [toList_roc_eq_toList_rco, map_add_toList_rco, show ∀ l, l + 1 + k = l + k + 1 by omega]

theorem map_add_toList_roc' {m n k : Int} :
    (m<...=n).toList.map (k + ·) = ((k + m)<...=(k + n)).toList := by
  simp [toList_roc_eq_toList_rco, map_add_toList_rco', ← Int.add_assoc]

theorem toList_roc_add_right_eq_map {m n : Int} :
    (m<...=(m + n)).toList = (0...n).toList.map (· + m + 1) := by
  simp [toList_roc_eq_toList_rco, show m + n + 1 = m + 1 + n by omega, toList_rco_add_right_eq_map,
    ← Int.add_assoc]

theorem toList_roc_succ_right_eq_append {m n : Int} (h : m ≤ n) :
    (m<...=(n + 1)).toList = (m<...=n).toList ++ [n + 1] := by
  simp [toList_roc_eq_toList_rco, toList_rco_succ_right_eq_append, h]

theorem toList_roc_eq_append {m n : Int} (h : m < n) :
    (m<...=n).toList = (m<...=(n - 1)).toList ++ [n] := by
  simp [toList_roc_eq_toList_rco, toList_rco_eq_append (Int.add_lt_add_right h 1),
    Int.sub_add_cancel (a := n) (b := 1)]

theorem toList_roc_append_toList_roc {l m n : Int} (h : l ≤ m) (h' : m ≤ n) :
    (l<...=m).toList ++ (m<...=n).toList = (l<...=n).toList := by
  simp [toList_roc_eq_toList_rco, toList_rco_append_toList_rco (Int.add_le_add_right h 1) (Int.add_le_add_right h' 1)]

@[simp]
theorem getElem_toList_roc {m n : Int} {i : Nat} (_h : i < (m<...=n).toList.length) :
    (m<...=n).toList[i]'_h = m + 1 + i := by
  simp [toList_roc_eq_toList_rco]

theorem getElem?_toList_roc {m n : Int} {i : Nat} :
    (m<...=n).toList[i]? = if i < (n - m).toNat then some (m + 1 + i) else none := by
  simp [toList_roc_eq_toList_rco, getElem?_toList_rco, Int.add_sub_add_right]

@[simp]
theorem getElem?_toList_roc_eq_some_iff {m n : Int} {i : Nat} :
    (m<...=n).toList[i]? = some k ↔ i < (n - m).toNat ∧ m + 1 + i = k := by
  simp [toList_roc_eq_toList_rco, Int.add_sub_add_right]

@[simp]
theorem getElem?_toList_roc_eq_none_iff {m n : Int} {i : Nat} :
    (m<...=n).toList[i]? = none ↔ (n - m).toNat ≤ i := by
  simp [toList_roc_eq_toList_rco, Int.add_sub_add_right]

@[simp]
theorem isSome_getElem?_toList_roc_eq {m n : Int} {i : Nat} :
    (m<...=n).toList[i]?.isSome = (i < (n - m).toNat) := by
  simp

@[simp]
theorem isNone_getElem?_toList_roc_eq {m n : Int} {i : Nat} :
    (m<...=n).toList[i]?.isNone = ((n - m).toNat ≤ i) := by
  simp [toList_roc_eq_toList_rco, Int.add_sub_add_right]

@[simp]
theorem getElem?_toList_roc_eq_some {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m<...=n).toList[i]? = some (m + 1 + i) := by
  simp [h]

@[simp]
theorem getElem?_toList_roc_eq_none {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m<...=n).toList[i]? = none := by
  simp [h]

theorem getElem!_toList_roc {m n : Int} {i : Nat} :
    (m<...=n).toList[i]! = if i < (n - m).toNat then (m + 1 + i) else 0 := by
  rw [toList_roc_eq_toList_rco, getElem!_toList_rco]
  simp [Int.add_sub_add_right]

@[simp]
theorem getElem!_toList_roc_eq_add {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m<...=n).toList[i]! = m + 1 + i := by
  simp [h]

@[simp]
theorem getElem!_toList_roc_eq_zero {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m<...=n).toList[i]! = 0 := by
  simp [h]

theorem getElem!_toList_roc_eq_zero_iff {m n : Int} {i : Nat} :
    (m<...=n).toList[i]! = 0 ↔ (n - m).toNat ≤ i ∨ m + i = -1 := by
  simp only [toList_roc_eq_toList_rco, getElem!_toList_rco_eq_zero_iff, Int.add_sub_add_right]
  omega

theorem getElem!_toList_roc_ne_zero_iff {m n : Int} {i : Nat} :
    (m<...=n).toList[i]! ≠ 0 ↔ i < (n - m).toNat ∧ m + i ≠ -1 := by
  simp only [toList_roc_eq_toList_rco, getElem!_toList_rco_ne_zero_iff,
    Int.add_sub_add_right]
  omega

theorem getD_toList_roc {m n fallback : Int} {i : Nat} :
    (m<...=n).toList.getD i fallback = if i < (n - m).toNat then (m + 1 + i) else fallback := by
  by_cases h : i < (n - m).toNat <;> simp [h]

@[simp]
theorem getD_toList_roc_eq_add {m n fallback : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m<...=n).toList.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toList_roc_eq_fallback {m n fallback : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m<...=n).toList.getD i fallback = fallback := by
  simp [h]

theorem toArray_roc_eq_toArray_rcc {m n : Int} :
    (m<...=n).toArray = ((m + 1)...=n).toArray := by
  rw [← toArray_toList_roc, toList_roc_eq_toList_rcc, toArray_toList_rcc]

theorem toArray_roc_eq_toArray_roo {m n : Int} :
    (m<...=n).toArray = (m<...(n + 1)).toArray := by
  rw [← toArray_toList_roc, toList_roc_eq_toList_roo, toArray_toList_roo]

theorem toArray_roc_eq_toArray_rco {m n : Int} :
    (m<...=n).toArray = ((m + 1)...(n + 1)).toArray := by
  rw [← toArray_toList_roc, toList_roc_eq_toList_rco, toArray_toList_rco]

theorem toArray_roc_eq_if {m n : Int} :
    (m<...=n).toArray = if m + 1 ≤ n then #[m + 1] ++ ((m + 1)<...=n).toArray else #[] := by
  rw [toArray_roc_eq_toArray_rco, toArray_roc_eq_toArray_rco, toArray_rco_eq_if]
  split <;> (simp; omega)

theorem toArray_roc_succ_succ {m n : Int} :
    ((m+1)<...=(n+1)).toArray = (m<...=n).toArray.map (· + 1) := by
  simp only [← toArray_toList_roc, toList_roc_succ_succ, List.map_toArray]

theorem toArray_roc_succ_right_eq_append_map {m n : Int} (h : m ≤ n) :
    (m<...=(n + 1)).toArray = #[m + 1] ++ (m<...=n).toArray.map (· + 1) := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_succ_right_eq_append_map, h]

@[simp]
theorem toArray_roc_eq_nil_iff {m n : Int} :
    (m<...=n).toArray = #[] ↔ n ≤ m := by
  simp [toArray_roc_eq_toArray_rco]

theorem toArray_roc_ne_nil_iff {m n : Int} :
    (m<...=n).toArray ≠ #[] ↔ m < n := by
  simp [toArray_roc_eq_toArray_rco]

@[simp 1001]
theorem toArray_roc_eq_nil {m n : Int} (h : n ≤ m) :
    (m<...=n).toArray = #[] := by
  simp; omega

@[simp]
theorem toArray_roc_eq_singleton_iff {m n : Int} :
    (m<...=n).toArray = #[k] ↔ n = m + 1 ∧ m + 1 = k := by
  simp [toArray_roc_eq_toArray_rco]

@[simp 1001]
theorem toArray_roc_eq_singleton {m n : Int} (h : n = m + 1) :
    (m<...=n).toArray = #[m + 1] := by
  simp [h]

@[simp]
theorem toArray_roc_eq_singleton_append_iff {m n a : Int} :
    (m<...=n).toArray = #[a] ++ xs ↔ m + 1 = a ∧ m < n ∧ ((m + 1)<...=n).toArray = xs := by
  simp [toArray_roc_eq_toArray_rco]

theorem toArray_roc_eq_singleton_append {m n : Int} (h : m < n) :
    (m<...=n).toArray = #[m + 1] ++ ((m + 1)<...=n).toArray := by
  simp; omega

theorem map_add_toArray_roc {m n k : Int} :
    (m<...=n).toArray.map (· + k) = ((m + k)<...=(n + k)).toArray := by
  simp [toArray_roc_eq_toArray_rco, map_add_toArray_rco, show ∀ l, l + 1 + k = l + k + 1 by omega]

theorem map_add_toArray_roc' {m n k : Int} :
    (m<...=n).toArray.map (k + ·) = ((k + m)<...=(k + n)).toArray := by
  simp [toArray_roc_eq_toArray_rco, map_add_toArray_rco', ← Int.add_assoc]

theorem toArray_roc_add_right_eq_map {m n : Int} :
    (m<...=(m + n)).toArray = (0...n).toArray.map (· + m + 1) := by
  simp [toArray_roc_eq_toArray_rco, show m + n + 1 = m + 1 + n by omega,
    toArray_rco_add_right_eq_map, ← Int.add_assoc]

theorem toArray_roc_succ_right_eq_push {m n : Int} (h : m ≤ n) :
    (m<...=(n + 1)).toArray = (m<...=n).toArray.push (n + 1) := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_succ_right_eq_push, h]

theorem toArray_roc_eq_push {m n : Int} (h : m < n) :
    (m<...=n).toArray = (m<...=(n - 1)).toArray.push n := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_eq_push (Int.add_le_add_right h 1),
    Int.sub_add_cancel n 1]

theorem toArray_roc_append_toArray_roc {l m n : Int} (h : l ≤ m) (h' : m ≤ n) :
    (l<...=m).toArray ++ (m<...=n).toArray = (l<...=n).toArray := by
  simp [toArray_roc_eq_toArray_rco, toArray_rco_append_toArray_rco (Int.add_le_add_right h 1) (Int.add_le_add_right h' 1)]

@[simp]
theorem getElem_toArray_roc {m n : Int} {i : Nat} (_h : i < (m<...=n).toArray.size) :
    (m<...=n).toArray[i]'_h = m + 1 + i := by
  simp [toArray_roc_eq_toArray_rco]

theorem getElem?_toArray_roc {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]? = if i < (n - m).toNat then some (m + 1 + i) else none := by
  simp [toArray_roc_eq_toArray_rco, getElem?_toArray_rco, Int.add_sub_add_right]

@[simp]
theorem getElem?_toArray_roc_eq_some_iff {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]? = some k ↔ i < (n - m).toNat ∧ m + 1 + i = k := by
  simp [toArray_roc_eq_toArray_rco, Int.add_sub_add_right]

@[simp]
theorem getElem?_toArray_roc_eq_none_iff {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]? = none ↔ (n - m).toNat ≤ i := by
  simp

@[simp]
theorem isSome_getElem?_toArray_roc_eq {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]?.isSome = (i < (n - m).toNat) := by
  simp

@[simp]
theorem isNone_getElem?_toArray_roc_eq {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]?.isNone = ((n - m).toNat ≤ i) := by
  simp

@[simp]
theorem getElem?_toArray_roc_eq_some {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m<...=n).toArray[i]? = some (m + 1 + i) := by
  simp [h]

@[simp]
theorem getElem?_toArray_roc_eq_none {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m<...=n).toArray[i]? = none := by
  simp [h]

theorem getElem!_toArray_roc {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]! = if i < (n - m).toNat then (m + 1 + i) else 0 := by
  rw [toArray_roc_eq_toArray_rco, getElem!_toArray_rco, Int.add_sub_add_right]

@[simp]
theorem getElem!_toArray_roc_eq_add {m n : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m<...=n).toArray[i]! = m + 1 + i := by
  simp [h]

@[simp]
theorem getElem!_toArray_roc_eq_zero {m n : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m<...=n).toArray[i]! = 0 := by
  simp [h]

theorem getElem!_toArray_roc_eq_zero_iff {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]! = 0 ↔ (n - m).toNat ≤ i ∨ m + i = -1 := by
  simp only [toArray_roc_eq_toArray_rco, getElem!_toArray_rco_eq_zero_iff]
  omega

theorem zero_lt_getElem!_toArray_roc_iff {m n : Int} {i : Nat} :
    (m<...=n).toArray[i]! ≠ 0 ↔ i < (n - m).toNat ∧ m + i ≠ -1 := by
  simp only [toArray_roc_eq_toArray_rco, getElem!_toArray_rco_ne_zero_iff]
  omega

theorem getD_toArray_roc {m n fallback : Int} {i : Nat} :
    (m<...=n).toArray.getD i fallback = if i < (n - m).toNat then (m + 1 + i) else fallback := by
  by_cases h : i < (n - m).toNat <;> simp [h]

@[simp]
theorem getD_toArray_roc_eq_add {m n fallback : Int} {i : Nat} (h : i < (n - m).toNat) :
    (m<...=n).toArray.getD i fallback = m + 1 + i := by
  simp [h]

@[simp]
theorem getD_toArray_roc_eq_fallback {m n fallback : Int} {i : Nat} (h : (n - m).toNat ≤ i) :
    (m<...=n).toArray.getD i fallback = fallback := by
  simp [h]

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a<...=b`
by varying the lower bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a<...=b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, the
statement holds for nonempty ranges {lean}`a<...=b` if it holds for the smaller range
{lean}`(a + 1)<...=b`.

The following is an example reproving {name}`length_toList_roc`.

```lean
example (a b : Int) : (a<...=b).toList.length = (b - a).toNat := by
  induction a, b using Int.induct_roc_left
  case base =>
    simp only [Int.toList_roc_eq_nil, List.length_nil, Int.zero_eq_toNat_sub_iff, *]
  case step =>
    simp only [Int.toList_roc_eq_cons, List.length_cons, *]; omega
```
-/
theorem induct_roc_left (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a < b → motive (a + 1) b → motive a b)
    (a b : Int) : motive a b :=
  induct_rco_left motive base step a b

/--
Induction principle for proving properties of {name}`Int`-based ranges of the form {lean}`a<...=b`
by varying the upper bound.

In the {name}`base` case, one proves that for any {given}`a : Int` and {given}`b : Int` with
{lean}`b ≤ a`, the statement holds for the empty range {lean}`a<...=b`.

In the {name}`step` case, one proves that for any {given}`a : Int` and {given}`b : Int`, if the
statement holds for {lean}`a<...=b`, it also holds for the larger range {lean}`a<...=(b + 1)`.

The following is an example reproving {name}`length_toList_roc`.

```lean
example (a b : Int) : (a<...=b).toList.length = (b - a).toNat := by
  induction a, b using Int.induct_roc_right
  case base =>
    simp only [Int.toList_roc_eq_nil, List.length_nil, Int.zero_eq_toNat_sub_iff, *]
  case step a b hle ih =>
    rw [Int.toList_roc_eq_append (by omega),
      List.length_append, List.length_singleton, Int.add_sub_cancel, ih]
    omega
```
-/
theorem induct_roc_right (motive : Int → Int → Prop)
    (base : ∀ a b, b ≤ a → motive a b)
    (step : ∀ a b, a ≤ b → motive a b → motive a (b + 1))
    (a b : Int) : motive a b :=
  induct_rco_right motive base step a b

end Int
