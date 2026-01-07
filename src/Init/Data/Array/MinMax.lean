/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.List.MinMax
import Init.Data.List.ToArray

namespace Array

/-! ## Minima and maxima -/

/-! ### min -/

/--
Returns the smallest element of a non-empty array.

Examples:
* `#[4].min (by decide) = 4`
* `#[1, 4, 2, 10, 6].min (by decide) = 1`
-/
def min [Min α] (arr : Array α) (h : arr.size > 0) : α :=
  arr.foldl Min.min arr[0] (start := 1)

/-! ### min? -/

/--
Returns the smallest element of the array if it is not empty, or `none` if it is empty.

Examples:
* `#[].min? = none`
* `#[4].min? = some 4`
* `#[1, 4, 2, 10, 6].min? = some 1`
-/
def min? [Min α] (arr : Array α) : Option α :=
  if h : arr.size > 0 then
    some (arr.min h)
  else
    none

/-! ### max -/

/--
Returns the largest element of a non-empty array.

Examples:
* `#[4].max (by decide) = 4`
* `#[1, 4, 2, 10, 6].max (by decide) = 10`
-/
def max [Max α] (arr : Array α) (h : arr.size > 0) : α :=
  arr.foldl Max.max arr[0] (start := 1)

/-! ### max? -/

/--
Returns the largest element of the array if it is not empty, or `none` if it is empty.

Examples:
* `#[].max? = none`
* `#[4].max? = some 4`
* `#[1, 4, 2, 10, 6].max? = some 10`
-/
def max? [Max α] (arr : Array α) : Option α :=
  if h : arr.size > 0 then
    some (arr.max h)
  else
    none

/-! ### Compatibility with `List` -/

theorem foldlM_eq_foldlM_extract.aux₀ [Monad m] {f : β → α → m β} {xs : Array α} {s hs i j b} :
    foldlM.loop f xs s hs i j b = foldlM.loop f xs xs.size (Nat.le_refl _) (Min.min i (s - j)) j b := by
  induction i generalizing j b
  · simp [foldlM.loop]
  · rename_i i ih
    simp +singlePass only [foldlM.loop.eq_def (i := i + 1)]
    split
    · have : Min.min (i + 1) (s - j) = Min.min i (s - j - 1) + 1 := by omega
      rw [this]
      rw [foldlM.loop, dif_pos (by omega)]
      simp
      apply bind_congr; intro
      rw [ih]
      rfl
    · rw [foldlM.loop]
      split
      · have : Min.min (i + 1) (s - j) = 0 := by omega
        rw [this]
      · rfl

theorem foldlM_eq_foldlM_extract.aux [Monad m]
    {f : β → α → m β} {xs : Array α} {i j} {b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i (j + 1) b = foldlM.loop f (xs.toList.drop 1).toArray (xs.size - 1) (by simp) i j b := by
  induction i generalizing j b
  · simp [foldlM.loop]
  · rename_i i ih
    simp +singlePass only [foldlM.loop.eq_def (i := i + 1)]
    split <;> rename_i h
    · rw [dif_pos (by omega)]
      simp
      apply bind_congr; intro
      simp [ih]
    · rw [dif_neg (by omega)]

theorem foldlM_eq_foldlM_extract.aux₂ [Monad m]
    {f : β → α → m β} {xs : Array α} {i j} {b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i j b = foldlM.loop f (xs.toList.drop j).toArray (xs.size - j) (by simp) i 0 b := by
  induction j generalizing xs
  · simp
  · rename_i j ih
    rw [foldlM_eq_foldlM_extract.aux]
    specialize ih (xs := (xs.toList.drop 1).toArray)
    simp only [List.drop_drop, Nat.add_comm 1, List.size_toArray, List.length_drop, Array.length_toList] at ih
    rw [ih]
    congr 1; omega

theorem foldlM_eq_foldlM_extract.aux₃ [Monad m]
    {f : β → α → m β} {xs : Array α} {i} {b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i 0 b = (xs.toList.take i).foldlM (init := b) f := by
  conv => lhs; rw [← Array.toArray_toList (xs := xs)]
  generalize xs.toList = xs
  induction i generalizing xs b
  · simp [foldlM.loop]
  · rename_i i ih
    simp +singlePass only [foldlM.loop.eq_def (i := i + 1)]
    split
    · simp only [Nat.zero_add]
      match xs with
      | x :: xs =>
        simp
        apply bind_congr; intro b'
        simp at ih
        rw [← ih]
        clear ih
        simpa using aux (xs := (x :: xs).toArray) (f := f) (b := b') (i := i) (j := 0)
    · simp_all

theorem foldlM_eq_foldlM_extract.aux₄ [Monad m] {f : β → α → m β} {xs : Array α} {i b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i j b = (xs.extract j (i + j)).foldlM (init := b) f := by
  rw [aux₂]
  have := aux₃ (xs := (xs.toList.drop j).toArray) (f := f) (b := b) (i := i)
  simp only [List.size_toArray, List.length_drop, length_toList] at this
  simp only [this, List.take_drop, Nat.add_comm j, ← Array.foldlM_toList, Array.toList_extract]
  simp

theorem foldlM_eq_foldlM_extract [Monad m] {f : β → α → m β} {xs : Array α} {b} :
    xs.foldlM (init := b) f (start := start) (stop := stop) =
      (xs.extract start stop).foldlM (init := b) f := by
  simp only [foldlM]
  split
  · rw [dif_pos (by omega)]
    rw [foldlM_eq_foldlM_extract.aux₀]
    rw [foldlM_eq_foldlM_extract.aux₄]
    rw [foldlM_eq_foldlM_extract.aux₄]
    simp
    congr 1
    · rw [← Array.toArray_toList (xs := xs)]
      simp only [List.extract_toArray, List.extract_eq_drop_take]
      simp [List.take_take]
      omega
    · omega
  · simp only [size_extract, Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
    rw [foldlM_eq_foldlM_extract.aux₄]
    rw [foldlM_eq_foldlM_extract.aux₀]
    rw [foldlM_eq_foldlM_extract.aux₄]
    simp
    congr 1
    · rw [← Array.toArray_toList (xs := xs)]
      simp only [List.extract_toArray, List.extract_eq_drop_take]
      simp [List.take_take]
      omega
    · omega

theorem foldl_eq_foldl_extract {xs : Array α} {f : β → α → β} {init : β} :
    xs.foldl (init := init) (start := start) (stop := stop) f = (xs.extract start stop).foldl (init := init) f := by
  simp only [foldl_eq_foldlM]
  rw [foldlM_eq_foldlM_extract]

@[simp, grind =]
theorem _root_.List.min_toArray [Min α] {l : List α} {h} :
    l.toArray.min h = l.min (by simpa [List.ne_nil_iff_length_pos] using h) := by
  let h' : l ≠ [] := by simpa [List.ne_nil_iff_length_pos] using h
  change l.toArray.min h = l.min h'
  rw [Array.min]
  · induction l
    · contradiction
    · rename_i x xs
      simp
      rw [List.toArray_cons, foldl_eq_foldl_extract]
      rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take]
      simp [List.min]

@[simp, grind =]
theorem _root_.List.min?_toArray [Min α] {l : List α} :
    l.toArray.min? = l.min? := by
  rw [Array.min?]
  split
  · simp [List.min_toArray, List.min_eq_get_min?]
  · simp_all

@[simp, grind =]
theorem min?_toList [Min α] {xs : Array α} :
    xs.toList.min? = xs.min? := by
  rcases xs with ⟨l⟩
  simp

@[simp, grind =]
theorem _root_.List.max_toArray [Max α] {l : List α} {h} :
    l.toArray.max h = l.max (by simpa [List.ne_nil_iff_length_pos] using h) := by
  let h' : l ≠ [] := by simpa [List.ne_nil_iff_length_pos] using h
  change l.toArray.max h = l.max h'
  rw [Array.max]
  · induction l
    · contradiction
    · rename_i x xs
      simp
      rw [List.toArray_cons, foldl_eq_foldl_extract]
      rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take]
      simp [List.max]

@[simp, grind =]
theorem _root_.List.max?_toArray [Max α] {l : List α} :
    l.toArray.max? = l.max? := by
  rw [Array.max?]
  split
  · simp [List.max_toArray, List.max_eq_get_max?]
  · simp_all

@[simp, grind =]
theorem max?_toList [Max α] {xs : Array α} :
    xs.toList.max? = xs.max? := by
  rcases xs with ⟨l⟩
  simp

end Array
