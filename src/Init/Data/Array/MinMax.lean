/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Array.Lemmas
import Init.Data.List.MinMax
public import Init.Data.Order.Classes
import Init.Data.Array.Bootstrap
import Init.Data.Array.DecidableEq
import Init.Data.List.TakeDrop
import Init.Data.Order.Lemmas

namespace Array

/-! ## Minima and maxima -/

/-! ### min -/

/--
Returns the smallest element of a non-empty array.

Examples:
* `#[4].min (by decide) = 4`
* `#[1, 4, 2, 10, 6].min (by decide) = 1`
-/
public protected def min [Min α] (arr : Array α) (h : arr ≠ #[]) : α :=
  haveI : arr.size > 0 := by simp [Array.size_pos_iff, h]
  arr.foldl min arr[0] (start := 1)

/-! ### min? -/

/--
Returns the smallest element of the array if it is not empty, or `none` if it is empty.

Examples:
* `#[].min? = none`
* `#[4].min? = some 4`
* `#[1, 4, 2, 10, 6].min? = some 1`
-/
public protected def min? [Min α] (arr : Array α) : Option α :=
  if h : arr ≠ #[] then
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
public protected def max [Max α] (arr : Array α) (h : arr ≠ #[]) : α :=
  haveI : arr.size > 0 := by simp [Array.size_pos_iff, h]
  arr.foldl max arr[0] (start := 1)

/-! ### max? -/

/--
Returns the largest element of the array if it is not empty, or `none` if it is empty.

Examples:
* `#[].max? = none`
* `#[4].max? = some 4`
* `#[1, 4, 2, 10, 6].max? = some 10`
-/
public protected def max? [Max α] (arr : Array α) : Option α :=
  if h : arr ≠ #[] then
    some (arr.max h)
  else
    none

/-! ### Compatibility with `List` -/

@[simp, grind =]
public theorem _root_.List.min_toArray [Min α] {l : List α} {h} :
    l.toArray.min h = l.min (by simpa [List.ne_nil_iff_length_pos] using h) := by
  let h' : l ≠ [] := by simpa [List.ne_nil_iff_length_pos] using h
  change l.toArray.min h = l.min h'
  rw [Array.min]
  · induction l
    · contradiction
    · rename_i x xs
      simp only [List.getElem_toArray, List.getElem_cons_zero, List.size_toArray, List.length_cons]
      rw [List.toArray_cons, foldl_eq_foldl_extract]
      rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_take_drop]
      simp [List.min]

public theorem _root_.List.min_eq_min_toArray [Min α] {l : List α} {h} :
    l.min h = l.toArray.min (by simpa [List.ne_nil_iff_length_pos] using h) := by
  simp

@[simp, grind =]
public theorem min_toList [Min α] {xs : Array α} {h} :
    xs.toList.min h = xs.min (by simpa [List.ne_nil_iff_length_pos] using h) := by
  cases xs; simp

public theorem min_eq_min_toList [Min α] {xs : Array α} {h} :
    xs.min h = xs.toList.min (by simpa [List.ne_nil_iff_length_pos] using h) := by
  simp

@[simp, grind =]
public theorem _root_.List.min?_toArray [Min α] {l : List α} :
    l.toArray.min? = l.min? := by
  rw [Array.min?]
  split
  · simp [List.min_toArray, List.min_eq_get_min?, - List.get_min?]
  · simp_all

@[simp, grind =]
public theorem min?_toList [Min α] {xs : Array α} :
    xs.toList.min? = xs.min? := by
  cases xs; simp

@[simp, grind =]
public theorem _root_.List.max_toArray [Max α] {l : List α} {h} :
    l.toArray.max h = l.max (by simpa [List.ne_nil_iff_length_pos] using h) := by
  let h' : l ≠ [] := by simpa [List.ne_nil_iff_length_pos] using h
  change l.toArray.max h = l.max h'
  rw [Array.max]
  · induction l
    · contradiction
    · rename_i x xs
      simp only [List.getElem_toArray, List.getElem_cons_zero, List.size_toArray, List.length_cons]
      rw [List.toArray_cons, foldl_eq_foldl_extract]
      rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_take_drop]
      simp [List.max]

public theorem _root_.List.max_eq_max_toArray [Max α] {l : List α} {h} :
    l.max h = l.toArray.max (by simpa [List.ne_nil_iff_length_pos] using h) := by
  simp

@[simp, grind =]
public theorem max_toList [Max α] {xs : Array α} {h} :
    xs.toList.max h = xs.max (by simpa [List.ne_nil_iff_length_pos] using h) := by
  cases xs; simp

public theorem max_eq_max_toList [Max α] {xs : Array α} {h} :
    xs.max h = xs.toList.max (by simpa [List.ne_nil_iff_length_pos] using h) := by
  simp

@[simp, grind =]
public theorem _root_.List.max?_toArray [Max α] {l : List α} :
    l.toArray.max? = l.max? := by
  rw [Array.max?]
  split
  · simp [List.max_toArray, List.max_eq_get_max?, - List.get_max?]
  · simp_all

@[simp, grind =]
public theorem max?_toList [Max α] {xs : Array α} :
    xs.toList.max? = xs.max? := by
  cases xs; simp

/-! ### Lemmas about `min?` -/

@[simp, grind =]
public theorem min?_empty [Min α] : (#[] : Array α).min? = none :=
  (rfl)

@[simp, grind =]
public theorem min?_singleton [Min α] {x : α} : #[x].min? = some x :=
  (rfl)

-- We don't put `@[simp]` on `min?_singleton_append'`,
-- because the definition in terms of `foldl` is not useful for proofs.
public theorem min?_singleton_append' [Min α] {xs : Array α} :
    (#[x] ++ xs).min? = some (xs.foldl min x) := by
  simp [← min?_toList, toList_append, List.min?]

@[simp]
public theorem min?_singleton_append [Min α] [Std.Associative (min : α → α → α)] {xs : Array α} :
    (#[x] ++ xs).min? = some (xs.min?.elim x (min x)) := by
  simp [← min?_toList, toList_append, List.min?_cons]

@[simp, grind =]
public theorem min?_eq_none_iff {xs : Array α} [Min α] : xs.min? = none ↔ xs = #[] := by
  rcases xs with ⟨l⟩
  simp

@[simp, grind =]
public theorem isSome_min?_iff {xs : Array α} [Min α] : xs.min?.isSome ↔ xs ≠ #[] := by
  rcases xs with ⟨l⟩
  simp

@[grind .]
public theorem isSome_min?_of_mem {xs : Array α} [Min α] {a : α} (h : a ∈ xs) :
    xs.min?.isSome := by
  rw [← min?_toList]
  apply List.isSome_min?_of_mem (a := a)
  simpa

public theorem isSome_min?_of_ne_empty [Min α] (xs : Array α) (h : xs ≠ #[]) : xs.min?.isSome := by
  rw [← min?_toList]
  apply List.isSome_min?_of_ne_nil
  simpa

public theorem min?_mem [Min α] [Std.MinEqOr α] (xs : Array α) (h : xs.min? = some a) : a ∈ xs := by
  rw [← min?_toList] at h
  simpa using List.min?_mem h

public theorem le_min?_iff [Min α] [LE α] [Std.LawfulOrderInf α] :
    {xs : Array α} → xs.min? = some a → ∀ {x}, x ≤ a ↔ ∀ b, b ∈ xs → x ≤ b := by
  intro xs h x
  simp only [← min?_toList] at h
  simpa using List.le_min?_iff h

public theorem min?_eq_some_iff [Min α] [LE α] {xs : Array α} [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] : xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  rcases xs with ⟨l⟩
  simpa using List.min?_eq_some_iff

public theorem min?_replicate [Min α] [Std.IdempotentOp (min : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).min? = if n = 0 then none else some a := by
  rw [← List.toArray_replicate, List.min?_toArray, List.min?_replicate]

@[simp, grind =]
public theorem min?_replicate_of_pos [Min α] [Std.MinEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).min? = some a := by
  simp [min?_replicate, Nat.ne_of_gt h]

public theorem foldl_min [Min α] [Std.IdempotentOp (min : α → α → α)]
    [Std.Associative (min : α → α → α)] {xs : Array α} {a : α} :
    xs.foldl (init := a) min = min a (xs.min?.getD a) := by
  rcases xs with ⟨l⟩
  simp [List.foldl_min]

/-! ### Lemmas about `max?` -/

@[simp, grind =]
public theorem max?_empty [Max α] : (#[] : Array α).max? = none :=
  (rfl)

@[simp, grind =]
public theorem max?_singleton [Max α] {x : α} : #[x].max? = some x :=
  (rfl)

-- We don't put `@[simp]` on `max?_singleton_append'`,
-- because the definition in terms of `foldl` is not useful for proofs.
public theorem max?_singleton_append' [Max α] {xs : Array α} : (#[x] ++ xs).max? = some (xs.foldl max x) := by
  simp [← max?_toList, toList_append, List.max?]

@[simp]
public theorem max?_singleton_append [Max α] [Std.Associative (max : α → α → α)] {xs : Array α} :
    (#[x] ++ xs).max? = some (xs.max?.elim x (max x)) := by
  simp [← max?_toList, toList_append, List.max?_cons]

@[simp, grind =]
public theorem max?_eq_none_iff {xs : Array α} [Max α] : xs.max? = none ↔ xs = #[] := by
  rcases xs with ⟨l⟩
  simp

@[simp, grind =]
public theorem isSome_max?_iff {xs : Array α} [Max α] : xs.max?.isSome ↔ xs ≠ #[] := by
  rcases xs with ⟨l⟩
  simp

@[grind .]
public theorem isSome_max?_of_mem {xs : Array α} [Max α] {a : α} (h : a ∈ xs) :
    xs.max?.isSome := by
  rw [← max?_toList]
  apply List.isSome_max?_of_mem (a := a)
  simpa

public theorem isSome_max?_of_ne_empty [Max α] (xs : Array α) (h : xs ≠ #[]) : xs.max?.isSome := by
  rw [← max?_toList]
  apply List.isSome_max?_of_ne_nil
  simpa

public theorem max?_mem [Max α] [Std.MaxEqOr α] (xs : Array α) (h : xs.max? = some a) : a ∈ xs := by
  rw [← max?_toList] at h
  simpa using List.max?_mem h

public theorem max?_le_iff [Max α] [LE α] [Std.LawfulOrderSup α] :
    {xs : Array α} → xs.max? = some a → ∀ {x}, a ≤ x ↔ ∀ b, b ∈ xs → b ≤ x := by
  intro xs h x
  simp only [← max?_toList] at h
  simpa using List.max?_le_iff h

public theorem max?_eq_some_iff [Max α] [LE α] {xs : Array α} [Std.IsLinearOrder α]
    [Std.LawfulOrderMax α] : xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  rcases xs with ⟨l⟩
  simpa using List.max?_eq_some_iff

public theorem max?_replicate [Max α] [Std.IdempotentOp (max : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).max? = if n = 0 then none else some a := by
  rw [← List.toArray_replicate, List.max?_toArray, List.max?_replicate]

@[simp, grind =]
public theorem max?_replicate_of_pos [Max α] [Std.MaxEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).max? = some a := by
  simp [max?_replicate, Nat.ne_of_gt h]

public theorem foldl_max [Max α] [Std.IdempotentOp (max : α → α → α)] [Std.Associative (max : α → α → α)]
    {xs : Array α} {a : α} : xs.foldl (init := a) max = max a (xs.max?.getD a) := by
  rcases xs with ⟨l⟩
  simp [List.foldl_max]

/-! ### Lemmas about `min` -/

@[simp, grind =]
theorem min_singleton [Min α] {x : α} :
    #[x].min (ne_empty_of_size_eq_add_one rfl) = x := by
  (rfl)

public theorem min?_eq_some_min [Min α] : {xs : Array α} → (h : xs ≠ #[]) →
    xs.min? = some (xs.min h)
  | ⟨a::as⟩, _ => by simp [Array.min, Array.min?]

public theorem min_eq_get_min? [Min α] : (xs : Array α) → (h : xs ≠ #[]) →
    xs.min h = xs.min?.get (xs.isSome_min?_of_ne_empty h)
  | ⟨a::as⟩, _ => by simp [Array.min, Array.min?]

@[simp, grind =]
public theorem get_min? [Min α] {xs : Array α} {h : xs.min?.isSome} :
    xs.min?.get h = xs.min (isSome_min?_iff.mp h) := by
  simp [min?_eq_some_min (isSome_min?_iff.mp h)]

@[grind .]
public theorem min_mem [Min α] [Std.MinEqOr α] {xs : Array α} (h : xs ≠ #[]) : xs.min h ∈ xs :=
  xs.min?_mem (min?_eq_some_min h)

@[grind .]
public theorem min_le_of_mem [Min α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMin α]
    {xs : Array α} {a : α} (ha : a ∈ xs) :
    xs.min (ne_empty_of_mem ha) ≤ a :=
  (Array.min?_eq_some_iff.mp (min?_eq_some_min (ne_empty_of_mem ha))).right a ha

public protected theorem le_min_iff [Min α] [LE α] [Std.LawfulOrderInf α]
    {xs : Array α} (h : xs ≠ #[]) : ∀ {x}, x ≤ xs.min h ↔ ∀ b, b ∈ xs → x ≤ b :=
  le_min?_iff (min?_eq_some_min h)

public theorem min_eq_iff [Min α] [LE α] {xs : Array α} [Std.IsLinearOrder α] [Std.LawfulOrderMin α]
    (h : xs ≠ #[]) : xs.min h = a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  simpa [min?_eq_some_min h] using (min?_eq_some_iff (xs := xs))

@[simp, grind =]
public theorem min_replicate [Min α] [Std.MinEqOr α] {n : Nat} {a : α} (h : (replicate n a) ≠ #[]) :
    (replicate n a).min h = a := by
  have n_pos : 0 < n := by simpa [Nat.ne_zero_iff_zero_lt] using h
  simpa [min?_eq_some_min h] using (min?_replicate_of_pos (a := a) n_pos)

public theorem foldl_min_eq_min [Min α] [Std.IdempotentOp (min : α → α → α)]
    [Std.Associative (min : α → α → α)] {xs : Array α} (h : xs ≠ #[]) {a : α} :
    xs.foldl min a = min a (xs.min h) := by
  simpa [min?_eq_some_min h] using foldl_min (xs := xs)

/-! ### Lemmas about `max` -/

@[simp, grind =]
theorem max_singleton [Max α] {x : α} :
    #[x].max (ne_empty_of_size_eq_add_one rfl) = x := by
  (rfl)

public theorem max?_eq_some_max [Max α] : {xs : Array α} → (h : xs ≠ #[]) →
    xs.max? = some (xs.max h)
  | ⟨a::as⟩, _ => by simp [Array.max, Array.max?]

public theorem max_eq_get_max? [Max α] : (xs : Array α) → (h : xs ≠ #[]) →
    xs.max h = xs.max?.get (xs.isSome_max?_of_ne_empty h)
  | ⟨a::as⟩, _ => by simp [Array.max, Array.max?]

@[simp, grind =]
public theorem get_max? [Max α] {xs : Array α} {h : xs.max?.isSome} :
    xs.max?.get h = xs.max (isSome_max?_iff.mp h) := by
  simp [max?_eq_some_max (isSome_max?_iff.mp h)]

@[grind .]
public theorem max_mem [Max α] [Std.MaxEqOr α] {xs : Array α} (h : xs ≠ #[]) : xs.max h ∈ xs :=
  xs.max?_mem (max?_eq_some_max h)

public protected theorem max_le_iff [Max α] [LE α] [Std.LawfulOrderSup α]
    {xs : Array α} (h : xs ≠ #[]) : ∀ {x}, xs.max h ≤ x ↔ ∀ b, b ∈ xs → b ≤ x :=
  max?_le_iff (max?_eq_some_max h)

public theorem max_eq_iff [Max α] [LE α] {xs : Array α} [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    (h : xs ≠ #[]) : xs.max h = a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  simpa [max?_eq_some_max h] using (max?_eq_some_iff (xs := xs))

@[grind .]
public theorem le_max_of_mem [Max α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {xs : Array α} {a : α} (ha : a ∈ xs) :
    a ≤ xs.max (ne_empty_of_mem ha) :=
  (Array.max?_eq_some_iff.mp (max?_eq_some_max (ne_empty_of_mem ha))).right a ha

@[simp, grind =]
public theorem max_replicate [Max α] [Std.MaxEqOr α] {n : Nat} {a : α} (h : (replicate n a) ≠ #[]) :
    (replicate n a).max h = a := by
  have n_pos : 0 < n := by simpa [Nat.ne_zero_iff_zero_lt] using h
  simpa [max?_eq_some_max h] using (max?_replicate_of_pos (a := a) n_pos)

public theorem foldl_max_eq_max [Max α] [Std.IdempotentOp (max : α → α → α)]
    [Std.Associative (max : α → α → α)] {xs : Array α} (h : xs ≠ #[]) {a : α} :
    xs.foldl max a = max a (xs.max h) := by
  simpa [max?_eq_some_max h] using foldl_max (xs := xs)

end Array
