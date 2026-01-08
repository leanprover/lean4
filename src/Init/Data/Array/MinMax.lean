/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Paul Reichert
-/
module

prelude
public import Init.Data.Array.Bootstrap
public import Init.Data.Array.Lemmas
public import Init.Data.Array.DecidableEq
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
public def min [Min α] (arr : Array α) (h : arr ≠ #[]) : α :=
  haveI : arr.size > 0 := by simp [Array.size_pos_iff, h]
  arr.foldl Min.min arr[0] (start := 1)

/-! ### min? -/

/--
Returns the smallest element of the array if it is not empty, or `none` if it is empty.

Examples:
* `#[].min? = none`
* `#[4].min? = some 4`
* `#[1, 4, 2, 10, 6].min? = some 1`
-/
public def min? [Min α] (arr : Array α) : Option α :=
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
public def max [Max α] (arr : Array α) (h : arr ≠ #[]) : α :=
  haveI : arr.size > 0 := by simp [Array.size_pos_iff, h]
  arr.foldl Max.max arr[0] (start := 1)

/-! ### max? -/

/--
Returns the largest element of the array if it is not empty, or `none` if it is empty.

Examples:
* `#[].max? = none`
* `#[4].max? = some 4`
* `#[1, 4, 2, 10, 6].max? = some 10`
-/
public def max? [Max α] (arr : Array α) : Option α :=
  if h : arr ≠ #[] then
    some (arr.max h)
  else
    none

/-! ### Prerequisite lemmas -/

theorem foldlM.loop.normalize_stop [Monad m] {f : β → α → m β} {xs : Array α} {s hs i j b} :
    foldlM.loop f xs s hs i j b = foldlM.loop f xs xs.size (Nat.le_refl _) (Min.min i (s - j)) j b := by
  induction i generalizing j b
  · simp [foldlM.loop]
  · rename_i i ih
    simp +singlePass only [foldlM.loop.eq_def (i := i + 1)]
    split
    · have : Min.min (i + 1) (s - j) = Min.min i (s - j - 1) + 1 := by omega
      rw [this]
      rw [foldlM.loop, dif_pos (by omega)]
      apply bind_congr; intro
      rw [ih]
      rfl
    · rw [foldlM.loop]
      split
      · have : Min.min (i + 1) (s - j) = 0 := by omega
        rw [this]
      · rfl

theorem foldlM.loop.shift_one [Monad m]
    {f : β → α → m β} {xs : Array α} {i j} {b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i (j + 1) b = foldlM.loop f (xs.toList.drop 1).toArray (xs.size - 1) (by simp) i j b := by
  induction i generalizing j b
  · simp only [loop, dite_eq_ite, ite_self]
  · rename_i i ih
    simp +singlePass only [foldlM.loop.eq_def (i := i + 1)]
    split <;> rename_i h
    · rw [dif_pos (by omega)]
      simp only [List.drop_one, List.getElem_toArray, List.getElem_tail, getElem_toList]
      apply bind_congr; intro
      simp [ih]
    · rw [dif_neg (by omega)]

theorem foldlM.loop.shift [Monad m]
    {f : β → α → m β} {xs : Array α} {i j} {b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i j b = foldlM.loop f (xs.toList.drop j).toArray (xs.size - j) (by simp) i 0 b := by
  induction j generalizing xs
  · simp
  · rename_i j ih
    rw [shift_one]
    specialize ih (xs := (xs.toList.drop 1).toArray)
    simp only [List.drop_drop, Nat.add_comm 1, List.size_toArray, List.length_drop, Array.length_toList] at ih
    rw [ih]
    congr 1; omega

theorem foldlM.loop_eq_foldlM_take [Monad m]
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
        simp only [List.getElem_toArray, List.getElem_cons_zero, List.size_toArray,
          List.length_cons, List.take_succ_cons, List.foldlM_cons]
        apply bind_congr; intro b'
        simp only [List.size_toArray] at ih
        rw [← ih]
        clear ih
        simpa using loop.shift_one (xs := (x :: xs).toArray) (f := f) (b := b') (i := i) (j := 0)
    · simp_all

theorem foldlM.loop_eq_foldlM_extract [Monad m] {f : β → α → m β} {xs : Array α} {i b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i j b = (xs.extract j (i + j)).foldlM (init := b) f := by
  rw [loop.shift]
  have := loop_eq_foldlM_take (xs := (xs.toList.drop j).toArray) (f := f) (b := b) (i := i)
  simp only [List.size_toArray, List.length_drop, length_toList] at this
  simp only [this, List.take_drop, Nat.add_comm j, ← Array.foldlM_toList, Array.toList_extract]
  simp

public theorem foldlM_eq_foldlM_extract [Monad m] {f : β → α → m β} {xs : Array α} {b} :
    xs.foldlM (init := b) f (start := start) (stop := stop) =
      (xs.extract start stop).foldlM (init := b) f := by
  simp only [foldlM]
  split
  · rw [dif_pos (by omega)]
    rw [foldlM.loop.normalize_stop, foldlM.loop_eq_foldlM_extract, foldlM.loop_eq_foldlM_extract]
    simp only [Nat.le_refl, Nat.min_eq_left, size_extract, Nat.sub_zero, Nat.add_zero]
    congr 1
    · rw [← Array.toArray_toList (xs := xs)]
      simp only [List.extract_toArray, List.extract_eq_drop_take]
      simp only [toArray_toList, List.drop_zero, List.take_take, mk.injEq, List.take_eq_take_iff]
      omega
    · omega
  · simp only [size_extract, Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
    rw [foldlM.loop_eq_foldlM_extract, foldlM.loop.normalize_stop,  foldlM.loop_eq_foldlM_extract]
    simp only [size_extract, Nat.sub_zero, Nat.le_refl, Nat.min_eq_left, Nat.add_zero]
    congr 1
    · rw [← Array.toArray_toList (xs := xs)]
      simp only [List.extract_toArray, List.extract_eq_drop_take]
      simp only [toArray_toList, List.drop_zero, List.take_take, mk.injEq, List.take_eq_take_iff]
      omega
    · omega

/-! ### Compatibility with `List` -/

public theorem foldl_eq_foldl_extract {xs : Array α} {f : β → α → β} {init : β} :
    xs.foldl (init := init) (start := start) (stop := stop) f = (xs.extract start stop).foldl (init := init) f := by
  simp only [foldl_eq_foldlM]
  rw [foldlM_eq_foldlM_extract]

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
      rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take]
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
  · simp [List.min_toArray, List.min_eq_get_min?]
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
      rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take]
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
  · simp [List.max_toArray, List.max_eq_get_max?]
  · simp_all

@[simp, grind =]
public theorem max?_toList [Max α] {xs : Array α} :
    xs.toList.max? = xs.max? := by
  cases xs; simp

/-! ### Lemmas about `min?` -/

@[simp]
public theorem min?_empty [Min α] : (#[] : Array α).min? = none :=
  (rfl)

@[simp]
public theorem min?_singleton [Min α] {x : α} : #[x].min? = some x :=
  (rfl)

-- We don't put `@[simp]` on `min?_singleton_append'`,
-- because the definition in terms of `foldl` is not useful for proofs.
public theorem min?_singleton_append' [Min α] {xs : Array α} :
    (#[x] ++ xs).min? = some (xs.foldl Min.min x) := by
  simp [← min?_toList, toList_append, List.min?]

@[simp]
public theorem min?_singleton_append [Min α] [Std.Associative (Min.min : α → α → α)] {xs : Array α} :
    (#[x] ++ xs).min? = some (xs.min?.elim x (Min.min x)) := by
  simp [← min?_toList, toList_append, List.min?_cons]

@[simp]
public theorem min?_eq_none_iff {xs : Array α} [Min α] : xs.min? = none ↔ xs.isEmpty := by
  rcases xs with ⟨l⟩
  simp

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

public theorem min?_replicate [Min α] [Std.IdempotentOp (Min.min : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).min? = if n = 0 then none else some a := by
  rw [← List.toArray_replicate, List.min?_toArray, List.min?_replicate]

@[simp]
public theorem min?_replicate_of_pos [Min α] [Std.MinEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).min? = some a := by
  simp [min?_replicate, Nat.ne_of_gt h]

public theorem foldl_min [Min α] [Std.IdempotentOp (Min.min : α → α → α)] [Std.Associative (Min.min : α → α → α)]
    {xs : Array α} {a : α} : xs.foldl (init := a) Min.min = Min.min a (xs.min?.getD a) := by
  rcases xs with ⟨l⟩
  simp [List.foldl_min]

/-! ### Lemmas about `max?` -/

@[simp]
public theorem max?_empty [Max α] : (#[] : Array α).max? = none :=
  (rfl)

@[simp]
public theorem max?_singleton [Max α] {x : α} : #[x].max? = some x :=
  (rfl)

-- We don't put `@[simp]` on `max?_singleton_append'`,
-- because the definition in terms of `foldl` is not useful for proofs.
public theorem max?_singleton_append' [Max α] {xs : Array α} : (#[x] ++ xs).max? = some (xs.foldl Max.max x) := by
  simp [← max?_toList, toList_append, List.max?]

@[simp]
public theorem max?_singleton_append [Max α] [Std.Associative (Max.max : α → α → α)] {xs : Array α} :
    (#[x] ++ xs).max? = some (xs.max?.elim x (Max.max x)) := by
  simp [← max?_toList, toList_append, List.max?_cons]

@[simp]
public theorem max?_eq_none_iff {xs : Array α} [Max α] : xs.max? = none ↔ xs.isEmpty := by
  rcases xs with ⟨l⟩
  simp

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

public theorem max?_replicate [Max α] [Std.IdempotentOp (Max.max : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).max? = if n = 0 then none else some a := by
  rw [← List.toArray_replicate, List.max?_toArray, List.max?_replicate]

@[simp] public theorem max?_replicate_of_pos [Max α] [Std.MaxEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).max? = some a := by
  simp [max?_replicate, Nat.ne_of_gt h]

public theorem foldl_max [Max α] [Std.IdempotentOp (Max.max : α → α → α)] [Std.Associative (Max.max : α → α → α)]
    {xs : Array α} {a : α} : xs.foldl (init := a) Max.max = Max.max a (xs.max?.getD a) := by
  rcases xs with ⟨l⟩
  simp [List.foldl_max]

/-! ### Lemmas about `min` -/

public theorem min?_eq_some_min [Min α] : {xs : Array α} → (h : xs ≠ #[]) →
    xs.min? = some (xs.min h)
  | ⟨a::as⟩, _ => by simp [Array.min, Array.min?]

public theorem min_eq_get_min? [Min α] : (xs : Array α) → (h : xs ≠ #[]) →
    xs.min h = xs.min?.get (xs.isSome_min?_of_ne_empty h)
  | ⟨a::as⟩, _ => by simp [Array.min, Array.min?]

public theorem min_mem [Min α] [Std.MinEqOr α] {xs : Array α} (h : xs ≠ #[]) : xs.min h ∈ xs :=
  xs.min?_mem (min?_eq_some_min h)

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

@[simp]
public theorem min_replicate [Min α] [Std.MinEqOr α] {n : Nat} {a : α} (h : (replicate n a) ≠ #[]) :
    (replicate n a).min h = a := by
  have n_pos : 0 < n := by simpa [Nat.ne_zero_iff_zero_lt] using h
  simpa [min?_eq_some_min h] using (min?_replicate_of_pos (a := a) n_pos)

public theorem foldl_min_eq_min [Min α] [Std.IdempotentOp (Min.min : α → α → α)]
    [Std.Associative (Min.min : α → α → α)] {xs : Array α} (h : xs ≠ #[]) {a : α} :
    xs.foldl Min.min a = Min.min a (xs.min h) := by
  simpa [min?_eq_some_min h] using foldl_min (xs := xs)

/-! ### Lemmas about `max` -/

public theorem max?_eq_some_max [Max α] : {xs : Array α} → (h : xs ≠ #[]) →
    xs.max? = some (xs.max h)
  | ⟨a::as⟩, _ => by simp [Array.max, Array.max?]

public theorem max_eq_get_max? [Max α] : (xs : Array α) → (h : xs ≠ #[]) →
    xs.max h = xs.max?.get (xs.isSome_max?_of_ne_empty h)
  | ⟨a::as⟩, _ => by simp [Array.max, Array.max?]

public theorem max_mem [Max α] [Std.MaxEqOr α] {xs : Array α} (h : xs ≠ #[]) : xs.max h ∈ xs :=
  xs.max?_mem (max?_eq_some_max h)

public protected theorem max_le_iff [Max α] [LE α] [Std.LawfulOrderSup α]
    {xs : Array α} (h : xs ≠ #[]) : ∀ {x}, xs.max h ≤ x ↔ ∀ b, b ∈ xs → b ≤ x :=
  max?_le_iff (max?_eq_some_max h)

public theorem max_eq_iff [Max α] [LE α] {xs : Array α} [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    (h : xs ≠ #[]) : xs.max h = a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  simpa [max?_eq_some_max h] using (max?_eq_some_iff (xs := xs))

public theorem le_max_of_mem [Max α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {xs : Array α} {a : α} (ha : a ∈ xs) :
    a ≤ xs.max (ne_empty_of_mem ha) :=
  (Array.max?_eq_some_iff.mp (max?_eq_some_max (ne_empty_of_mem ha))).right a ha

@[simp]
public theorem max_replicate [Max α] [Std.MaxEqOr α] {n : Nat} {a : α} (h : (replicate n a) ≠ #[]) :
    (replicate n a).max h = a := by
  have n_pos : 0 < n := by simpa [Nat.ne_zero_iff_zero_lt] using h
  simpa [max?_eq_some_max h] using (max?_replicate_of_pos (a := a) n_pos)

public theorem foldl_max_eq_max [Max α] [Std.IdempotentOp (Max.max : α → α → α)]
    [Std.Associative (Max.max : α → α → α)] {xs : Array α} (h : xs ≠ #[]) {a : α} :
    xs.foldl Max.max a = Max.max a (xs.max h) := by
  simpa [max?_eq_some_max h] using foldl_max (xs := xs)

end Array
