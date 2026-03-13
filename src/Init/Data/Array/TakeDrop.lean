/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
import all Init.Data.Array.Basic
import Init.Data.Array.Bootstrap
public import Init.Data.Array.Basic
public import Init.NotationExtra
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.TakeDrop
public import Init.Data.Nat.MinMax
import Init.Omega
import Init.Data.Option.Array

public section

namespace Array

@[simp, grind =] theorem take_empty {i : Nat} :
    (#[] : Array α).take i = #[] := by cases i <;> rfl

@[simp, grind =] theorem take_zero {xs : Array α} :
    xs.take 0 = #[] := by
  simp [Array.take_eq_extract]

@[simp, grind =] theorem drop_empty : (#[] : Array α).drop i = #[] := by
  simp [Array.drop_eq_extract]

@[simp, grind =] theorem drop_zero {xs : Array α} : xs.drop 0 = xs := by
  simp [Array.drop_eq_extract]

theorem drop_eq_empty_of_le {xs : Array α} {i : Nat} (h : xs.size ≤ i) : xs.drop i = #[] := by
  simp [Array.drop_eq_extract, Array.extract_empty_of_size_le_start h]

@[simp, grind =] theorem size_take {xs : Array α} {i : Nat} : (xs.take i).size = min i xs.size := by
  simp [take_eq_extract]

theorem size_take_le (i : Nat) (xs : Array α) : (xs.take i).size ≤ i := by
  simp [Nat.min_le_left]

theorem size_take_le' (i : Nat) (xs : Array α) : (xs.take i).size ≤ xs.size := by
  simp [Nat.min_le_right]

theorem size_take_of_le {xs : Array α} (h : i ≤ xs.size) : (xs.take i).size = i := by
  simp [Nat.min_eq_left h]

@[simp, grind =] theorem size_drop {xs : Array α} {i : Nat} : (xs.drop i).size = xs.size - i := by
  simp [drop_eq_extract]

@[simp] theorem take_append_drop (i : Nat) (xs : Array α) : xs.take i ++ xs.drop i = xs := by
  apply ext'
  simp

theorem take_of_size_le {xs : Array α} (h : xs.size ≤ i) : xs.take i = xs := by
  apply ext'
  simp [List.take_of_length_le (by simpa)]

theorem drop_of_size_le {xs : Array α} (h : xs.size ≤ i) : xs.drop i = #[] := by
  apply ext'
  simp [List.drop_of_length_le (by simpa)]

@[simp, grind =] theorem take_size {xs : Array α} : xs.take xs.size = xs :=
  take_of_size_le (Nat.le_refl _)

@[simp, grind =] theorem drop_size {xs : Array α} : xs.drop xs.size = #[] :=
  drop_of_size_le (Nat.le_refl _)

theorem lt_size_of_take_ne_self {xs : Array α} {i : Nat} (h : xs.take i ≠ xs) : i < xs.size :=
  Nat.gt_of_not_le (mt take_of_size_le h)

theorem size_lt_of_drop_ne_empty {xs : Array α} {i : Nat} (h : xs.drop i ≠ #[]) : i < xs.size :=
  Nat.gt_of_not_le (mt drop_of_size_le h)

@[simp] theorem drop_eq_empty_iff {xs : Array α} {i : Nat} : xs.drop i = #[] ↔ xs.size ≤ i := by
  constructor
  · intro h
    have := congrArg size h
    simpa [Nat.sub_eq_zero_iff_le] using this
  · exact drop_of_size_le

@[simp] theorem take_eq_empty_iff {xs : Array α} {k : Nat} :
    xs.take k = #[] ↔ k = 0 ∨ xs = #[] := by
  rw [← toList_inj, toList_take, ← toList_inj]
  simp [List.take_eq_nil_iff]

theorem getElem_take' {xs : Array α} {i j : Nat} (hi : i < xs.size) (hj : i < j) :
    xs[i] = (xs.take j)[i]'(size_take .. ▸ Nat.lt_min.mpr ⟨hj, hi⟩) := by
  simp [take_eq_extract]

@[simp, grind =] theorem getElem_take {xs : Array α} {j i : Nat}
    {h : i < (xs.take j).size} :
    (xs.take j)[i] = xs[i]'(Nat.lt_of_lt_of_le h (size_take_le' _ _)) := by
  simp [take_eq_extract]

@[simp] theorem getElem?_take_of_lt {xs : Array α} {i j : Nat} (h : i < j) :
    (xs.take j)[i]? = xs[i]? := by
  simp [getElem?_def, take_eq_extract, Nat.lt_min, h]

theorem getElem?_take_eq_none {xs : Array α} {i j : Nat} (h : i ≤ j) :
    (xs.take i)[j]? = none :=
  getElem?_eq_none <| Nat.le_trans (size_take_le _ _) h

@[grind =] theorem getElem?_take {xs : Array α} {i j : Nat} :
    (xs.take i)[j]? = if j < i then xs[j]? else none := by
  simp [← getElem?_toList, List.getElem?_take]

theorem back?_take {xs : Array α} {i : Nat} :
    (xs.take i).back? = if i = 0 then none else xs[i - 1]?.or xs.back? := by
  simp [← getLast?_toList, List.getLast?_take]

theorem lt_size_drop {xs : Array α} {i j : Nat} (h : i + j < xs.size) :
    j < (xs.drop i).size := by
  simpa [← length_toList] using xs.toList.lt_length_drop (length_toList ▸ h)

theorem getElem_drop' {xs : Array α} {i j : Nat} (h : i + j < xs.size) :
    xs[i + j] = (xs.drop i)[j]'(lt_size_drop h) := by
  simp [drop_eq_extract]

@[simp, grind =] theorem getElem_drop {xs : Array α} {i j : Nat}
    {h : j < (xs.drop i).size} :
    (xs.drop i)[j] = xs[i + j]'(by
      rw [Nat.add_comm]
      exact Nat.add_lt_of_lt_sub (List.length_drop ▸ (by simpa using h))) := by
  simp [drop_eq_extract]

@[simp, grind =] theorem getElem?_drop {xs : Array α} {i j : Nat} :
    (xs.drop i)[j]? = xs[i + j]? := by
  simp [← getElem?_toList]

theorem back?_drop {xs : Array α} {i : Nat} :
    (xs.drop i).back? = if xs.size ≤ i then none else xs.back? := by
  simp [← getLast?_toList, List.getLast?_drop]

@[simp, grind =] theorem back_drop {xs : Array α} {i : Nat} (h : xs.drop i ≠ #[]) :
    (xs.drop i).back (by simpa [Nat.lt_sub_iff_add_lt] using h) = xs.back (by simp at h; omega) := by
  simp only [← getLast_toList _ (by simpa), toList_drop, List.getLast_drop]
  simp

theorem mem_take_iff_getElem {xs : Array α} {a : α} :
    a ∈ xs.take i ↔ ∃ (j : Nat) (hm : j < min i xs.size), xs[j] = a := by
  simp [← mem_toList_iff, List.mem_take_iff_getElem]

theorem mem_drop_iff_getElem {xs : Array α} {a : α} :
    a ∈ xs.drop i ↔ ∃ (j : Nat) (hm : j + i < xs.size), xs[i + j] = a := by
  simp [← mem_toList_iff, List.mem_drop_iff_getElem]

@[grind =] theorem take_take {xs : Array α} {i j : Nat} :
    (xs.take j).take i = xs.take (min i j) := by
  apply ext'; simp [List.take_take]

@[simp] theorem drop_drop {xs : Array α} {i j : Nat} :
    (xs.drop j).drop i = xs.drop (j + i) := by
  apply ext'; simp [List.drop_drop]

theorem take_drop {xs : Array α} {i j : Nat} :
    (xs.drop j).take i = (xs.take (j + i)).drop j := by
  apply ext'; simp [List.take_drop]

theorem drop_take {xs : Array α} {i j : Nat} :
    (xs.take j).drop i = (xs.drop i).take (j - i) := by
  apply ext'; simp [List.drop_take]

@[simp, grind =] theorem drop_take_self {xs : Array α} {i : Nat} :
    (xs.take i).drop i = #[] := by
  apply ext'; simp

/-
TODO: not marked as `@[grind]` because it causes trouble by creating many large terms.
For example, `set_getElem_succ_eraseIdx_succ` in `grind_list_erase.lean` would fail with it.
-/
theorem take_add {xs : Array α} {i j : Nat} :
    xs.take (i + j) = xs.take i ++ (xs.drop i).take j := by
  apply ext'; simp [List.take_add]

theorem take_add_one {xs : Array α} {i : Nat} :
    xs.take (i + 1) = xs.take i ++ xs[i]?.toArray := by
  apply ext'; simp [List.take_add_one]

theorem take_append {xs ys : Array α} {i : Nat} :
    (xs ++ ys).take i = xs.take i ++ ys.take (i - xs.size) := by
  apply ext'; simp [List.take_append]

@[grind =] theorem take_append_of_le_size {xs ys : Array α} {i : Nat} (h : i ≤ xs.size) :
    (xs ++ ys).take i = xs.take i := by
  apply ext'; simp [List.take_append_of_le_length (by simpa)]

@[grind =] theorem take_append_size {xs ys : Array α} : (xs ++ ys).take xs.size = xs := by
  apply ext'; simp

theorem take_size_add_append {xs ys : Array α} (i : Nat) :
    (xs ++ ys).take (xs.size + i) = xs ++ ys.take i := by
  apply ext'; simp [List.take_length_add_append, ← length_toList]

theorem drop_append {xs ys : Array α} {i : Nat} :
    (xs ++ ys).drop i = xs.drop i ++ ys.drop (i - xs.size) := by
  apply ext'; simp [List.drop_append]

@[grind =] theorem drop_append_of_le_size {xs ys : Array α} {i : Nat} (h : i ≤ xs.size) :
    (xs ++ ys).drop i = xs.drop i ++ ys := by
  apply ext'; simp [List.drop_append_of_le_length (by simpa)]

@[grind =] theorem drop_append_size {xs ys : Array α} : (xs ++ ys).drop xs.size = ys := by
  apply ext'; simp

@[simp] theorem drop_size_add_append {xs ys : Array α} (i : Nat) :
    (xs ++ ys).drop (xs.size + i) = ys.drop i := by
  apply ext'; simp [List.drop_length_add_append, ← length_toList]

theorem take_setIfInBounds {xs : Array α} {i j : Nat} {a : α} :
    (xs.setIfInBounds j a).take i = (xs.take i).setIfInBounds j a := by
  apply ext'; simp [List.take_set]

theorem take_setIfInBounds_of_le {xs : Array α} {a : α} {i j : Nat} (h : j ≤ i) :
    (xs.setIfInBounds i a).take j = xs.take j := by
  apply ext'; simp [List.take_set_of_le h]

theorem drop_setIfInBounds {xs : Array α} {i j : Nat} {a : α} :
    (xs.setIfInBounds j a).drop i = if j < i then xs.drop i else (xs.drop i).setIfInBounds (j - i) a := by
  apply ext'
  simp only [toList_drop, toList_setIfInBounds, List.drop_set]
  split <;> simp_all

theorem setIfInBounds_drop {xs : Array α} {i j : Nat} {a : α} :
    (xs.drop i).setIfInBounds j a = (xs.setIfInBounds (i + j) a).drop i := by
  rw [drop_setIfInBounds, if_neg, Nat.add_sub_cancel_left]
  exact Nat.not_lt.2 (Nat.le_add_right ..)

theorem drop_setIfInBounds_of_lt {xs : Array α} {a : α} {i j : Nat} (h : i < j) :
    (xs.setIfInBounds i a).drop j = xs.drop j := by
  apply ext'; simp [List.drop_set_of_lt h]

@[simp] theorem take_push_getElem {xs : Array α} {i : Nat} (h : i < xs.size) :
    (xs.take i).push xs[i] = xs.take (i + 1) := by
  apply ext'; simp [List.take_succ_eq_append_getElem h]

theorem take_succ_eq_push_getElem {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs.take (i + 1) = (xs.take i).push xs[i] :=
  (take_push_getElem h).symm

@[simp] theorem take_push_back (xs : Array α) (h : 0 < xs.size) :
    (xs.take (xs.size - 1)).push (xs.back h) = xs := by
  apply ext'
  simp only [← length_toList, toList_push, toList_take, ← getLast_toList _ (by simpa [Nat.pos_iff_ne_zero] using h)]
  rw [List.take_append_getLast]

@[simp] theorem map_take {f : α → β} {xs : Array α} {i : Nat} :
    (xs.take i).map f = (xs.map f).take i := by
  apply ext'; simp [List.map_take]

@[simp] theorem map_drop {f : α → β} {xs : Array α} {i : Nat} :
    (xs.drop i).map f = (xs.map f).drop i := by
  apply ext'; simp [List.map_drop]

@[simp, grind =] theorem take_replicate {a : α} {i n : Nat} :
    (replicate n a).take i = replicate (min i n) a := by
  apply ext'; simp

@[simp, grind =] theorem drop_replicate {a : α} {i n : Nat} :
    (replicate n a).drop i = replicate (n - i) a := by
  apply ext'; simp

@[simp] theorem take_eq_take_iff {xs : Array α} {i j : Nat} :
    xs.take i = xs.take j ↔ min i xs.size = min j xs.size := by
  rw [← toList_inj, toList_take, toList_take, List.take_eq_take_iff]
  simp

theorem take_eq_take_min {xs : Array α} {i : Nat} :
    xs.take i = xs.take (min i xs.size) := by
  simp

@[simp] theorem drop_eq_drop_iff {xs : Array α} {i j : Nat} :
    xs.drop i = xs.drop j ↔ min i xs.size = min j xs.size := by
  rw [← toList_inj, toList_drop, toList_drop, List.drop_eq_drop_iff]
  simp

theorem drop_eq_drop_min {xs : Array α} {i : Nat} :
    xs.drop i = xs.drop (min i xs.size) := by
  simp

theorem take_reverse {xs : Array α} {i : Nat} :
    xs.reverse.take i = (xs.drop (xs.size - i)).reverse := by
  apply ext'; simp [List.take_reverse]

theorem drop_reverse {xs : Array α} {i : Nat} :
    xs.reverse.drop i = (xs.take (xs.size - i)).reverse := by
  apply ext'; simp [List.drop_reverse]

theorem reverse_take {xs : Array α} {i : Nat} :
    (xs.take i).reverse = xs.reverse.drop (xs.size - i) := by
  apply ext'; simp [List.reverse_take]

theorem reverse_drop {xs : Array α} {i : Nat} :
    (xs.drop i).reverse = xs.reverse.take (xs.size - i) := by
  apply ext'; simp [List.reverse_drop]

theorem pop_eq_take {xs : Array α} : xs.pop = xs.take (xs.size - 1) := by
  apply ext'; simp [List.dropLast_eq_take]

theorem pop_take {xs : Array α} {i : Nat} (h : i < xs.size) :
    (xs.take i).pop = xs.take (i - 1) := by
  simp only [pop_eq_take, size_take, take_take]
  rw [Nat.min_eq_left, Nat.min_eq_left] <;> omega

theorem extract_eq_drop_take {xs : Array α} {start stop : Nat} :
    xs.extract start stop = (xs.take stop).drop start := by
  apply ext'; simp [List.extract_eq_drop_take']

theorem extract_eq_take_drop {xs : Array α} {start stop : Nat} :
    xs.extract start stop = (xs.drop start).take (stop - start) := by
  apply ext'; simp [List.extract_eq_take_drop]

theorem drop_eq_toArray_getElem?_append {xs : Array α} {i : Nat} :
    xs.drop i = xs[i]?.toArray ++ xs.drop (i + 1) := by
  apply ext'
  simp only [toList_drop, toList_append, Option.toList_toArray]
  rw [List.drop_eq_getElem?_toList_append, getElem?_toList]

end Array

/-!
These lemmas are used in the internals of HashMap.
They should find a new home and/or be reformulated.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

theorem exists_of_set {i : Nat} {a' : α} {l : List α} (h : i < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l[i] :: l₂ ∧ l₁.length = i ∧ l.set i a' = l₁ ++ a' :: l₂ := by
  refine ⟨l.take i, l.drop (i + 1), ⟨by simp, ⟨length_take_of_le (Nat.le_of_lt h), ?_⟩⟩⟩
  simp [set_eq_take_append_cons_drop, h]

end List

namespace Array

theorem exists_of_uset {xs : Array α} {i d} (h) :
    ∃ l₁ l₂, xs.toList = l₁ ++ xs[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (xs.uset i d h).toList = l₁ ++ d :: l₂ := by
  simpa only [ugetElem_eq_getElem, ← getElem_toList, uset, toList_set] using
    List.exists_of_set _

end Array
