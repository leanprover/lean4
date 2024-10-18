/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Mario Carneiro
-/

prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Range

namespace List

/-! ## Operations using indexes -/

/-! ### mapIdx -/

/--
Given a function `f : Nat → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`.
-/
@[inline] def mapIdx (f : Nat → α → β) (as : List α) : List β := go as #[] where
  /-- Auxiliary for `mapIdx`:
  `mapIdx.go [a₀, a₁, ...] acc = acc.toList ++ [f acc.size a₀, f (acc.size + 1) a₁, ...]` -/
  @[specialize] go : List α → Array β → List β
  | [], acc => acc.toList
  | a :: as, acc => go as (acc.push (f acc.size a))

@[simp]
theorem mapIdx_nil {f : Nat → α → β} : mapIdx f [] = [] :=
  rfl

theorem mapIdx_go_append  {l₁ l₂ : List α} {arr : Array β} :
    mapIdx.go f (l₁ ++ l₂) arr = mapIdx.go f l₂ (List.toArray (mapIdx.go f l₁ arr)) := by
  generalize h : (l₁ ++ l₂).length = len
  induction len generalizing l₁ arr with
  | zero =>
    have l₁_nil : l₁ = [] := by
      cases l₁
      · rfl
      · contradiction
    have l₂_nil : l₂ = [] := by
      cases l₂
      · rfl
      · rw [List.length_append] at h; contradiction
    rw [l₁_nil, l₂_nil]; simp only [mapIdx.go, List.toArray_toList]
  | succ len ih =>
    cases l₁ with
    | nil =>
      simp only [mapIdx.go, nil_append, List.toArray_toList]
    | cons head tail =>
      simp only [mapIdx.go, List.append_eq]
      rw [ih]
      · simp only [cons_append, length_cons, length_append, Nat.succ.injEq] at h
        simp only [length_append, h]

theorem mapIdx_go_length {arr : Array β} :
    length (mapIdx.go f l arr) = length l + arr.size := by
  induction l generalizing arr with
  | nil => simp only [mapIdx.go, length_nil, Nat.zero_add]
  | cons _ _ ih =>
    simp only [mapIdx.go, ih, Array.size_push, Nat.add_succ, length_cons, Nat.add_comm]

@[simp] theorem mapIdx_concat {l : List α} {e : α} :
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] := by
  unfold mapIdx
  rw [mapIdx_go_append]
  simp only [mapIdx.go, Array.size_toArray, mapIdx_go_length, length_nil, Nat.add_zero,
    Array.push_toList]

@[simp] theorem mapIdx_singleton {a : α} : mapIdx f [a] = [f 0 a] := by
  simpa using mapIdx_concat (l := [])

theorem length_mapIdx_go : ∀ {l : List α} {arr : Array β},
    (mapIdx.go f l arr).length = l.length + arr.size
  | [], _ => by simp [mapIdx.go]
  | a :: l, _ => by
    simp only [mapIdx.go, length_cons]
    rw [length_mapIdx_go]
    simp
    omega

@[simp] theorem length_mapIdx {l : List α} : (l.mapIdx f).length = l.length := by
  simp [mapIdx, length_mapIdx_go]

theorem getElem?_mapIdx_go : ∀ {l : List α} {arr : Array β} {i : Nat},
    (mapIdx.go f l arr)[i]? =
      if h : i < arr.size then some arr[i] else Option.map (f i) l[i - arr.size]?
  | [], arr, i => by
    simp only [mapIdx.go, Array.toListImpl_eq, getElem?_eq, Array.length_toList,
      Array.getElem_eq_getElem_toList, length_nil, Nat.not_lt_zero, ↓reduceDIte, Option.map_none']
  | a :: l, arr, i => by
    rw [mapIdx.go, getElem?_mapIdx_go]
    simp only [Array.size_push]
    split <;> split
    · simp only [Option.some.injEq]
      rw [Array.getElem_eq_getElem_toList]
      simp only [Array.push_toList]
      rw [getElem_append_left, Array.getElem_eq_getElem_toList]
    · have : i = arr.size := by omega
      simp_all
    · omega
    · have : i - arr.size = i - (arr.size + 1) + 1 := by omega
      simp_all

@[simp] theorem getElem?_mapIdx {l : List α} {i : Nat} :
    (l.mapIdx f)[i]? = Option.map (f i) l[i]? := by
  simp [mapIdx, getElem?_mapIdx_go]

@[simp] theorem getElem_mapIdx {l : List α} {f : Nat → α → β} {i : Nat} {h : i < (l.mapIdx f).length} :
    (l.mapIdx f)[i] = f i (l[i]'(by simpa using h)) := by
  apply Option.some_inj.mp
  rw [← getElem?_eq_getElem, getElem?_mapIdx, getElem?_eq_getElem (by simpa using h)]
  simp

theorem mapIdx_eq_enum_map {l : List α} :
    l.mapIdx f = l.enum.map (Function.uncurry f) := by
  ext1 i
  simp only [getElem?_mapIdx, Option.map, getElem?_map, getElem?_enum]
  split <;> simp

@[simp]
theorem mapIdx_cons {l : List α} {a : α} :
    mapIdx f (a :: l) = f 0 a :: mapIdx (fun i => f (i + 1)) l := by
  simp [mapIdx_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zipWith,
    range_succ_eq_map, zipWith_map_left]

theorem mapIdx_append {K L : List α} :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i => f (i + K.length) := by
  induction K generalizing f with
  | nil => rfl
  | cons _ _ ih => simp [ih (f := fun i => f (i + 1)), Nat.add_assoc]

@[simp]
theorem mapIdx_eq_nil_iff {l : List α} : List.mapIdx f l = [] ↔ l = [] := by
  rw [List.mapIdx_eq_enum_map, List.map_eq_nil_iff, List.enum_eq_nil]

theorem mapIdx_ne_nil_iff {l : List α} :
    List.mapIdx f l ≠ [] ↔ l ≠ [] := by
  simp

theorem exists_of_mem_mapIdx {b : β} {l : List α}
    (h : b ∈ mapIdx f l) : ∃ (i : Nat) (h : i < l.length), f i l[i] = b := by
  rw [mapIdx_eq_enum_map] at h
  replace h := exists_of_mem_map h
  simp only [Prod.exists, mk_mem_enum_iff_getElem?, Function.uncurry_apply_pair] at h
  obtain ⟨i, b, h, rfl⟩ := h
  rw [getElem?_eq_some_iff] at h
  obtain ⟨h, rfl⟩ := h
  exact ⟨i, h, rfl⟩

@[simp] theorem mem_mapIdx {b : β} {l : List α} :
    b ∈ mapIdx f l ↔ ∃ (i : Nat) (h : i < l.length), f i l[i] = b := by
  constructor
  · intro h
    exact exists_of_mem_mapIdx h
  · rintro ⟨i, h, rfl⟩
    rw [mem_iff_getElem]
    exact ⟨i, by simpa using h, by simp⟩

theorem mapIdx_eq_cons_iff {l : List α} {b : β} :
    mapIdx f l = b :: l₂ ↔
      ∃ (a : α) (l₁ : List α), l = a :: l₁ ∧ f 0 a = b ∧ mapIdx (fun i => f (i + 1)) l₁ = l₂ := by
  cases l <;> simp [and_assoc]

theorem mapIdx_eq_cons_iff' {l : List α} {b : β} :
    mapIdx f l = b :: l₂ ↔
      l.head?.map (f 0) = some b ∧ l.tail?.map (mapIdx fun i => f (i + 1)) = some l₂ := by
  cases l <;> simp

theorem mapIdx_eq_iff {l : List α} : mapIdx f l = l' ↔ ∀ i : Nat, l'[i]? = l[i]?.map (f i) := by
  constructor
  · intro w i
    simpa using congrArg (fun l => l[i]?) w.symm
  · intro w
    ext1 i
    simp [w]

theorem mapIdx_eq_mapIdx_iff {l : List α} :
    mapIdx f l = mapIdx g l ↔ ∀ i : Nat, (h : i < l.length) → f i l[i] = g i l[i] := by
  constructor
  · intro w i h
    simpa [h] using congrArg (fun l => l[i]?) w
  · intro w
    apply ext_getElem
    · simp
    · intro i h₁ h₂
      simp [w]

@[simp] theorem mapIdx_set {l : List α} {i : Nat} {a : α} :
    (l.set i a).mapIdx f = (l.mapIdx f).set i (f i a) := by
  simp only [mapIdx_eq_iff, getElem?_set, length_mapIdx, getElem?_mapIdx]
  intro i
  split
  · split <;> simp_all
  · rfl

@[simp] theorem head_mapIdx {l : List α} {f : Nat → α → β} {w : mapIdx f l ≠ []} :
    (mapIdx f l).head w = f 0 (l.head (by simpa using w)) := by
  cases l with
  | nil => simp at w
  | cons _ _ => simp

@[simp] theorem head?_mapIdx {l : List α} {f : Nat → α → β} : (mapIdx f l).head? = l.head?.map (f 0) := by
  cases l <;> simp

@[simp] theorem getLast_mapIdx {l : List α} {f : Nat → α → β} {h} :
    (mapIdx f l).getLast h = f (l.length - 1) (l.getLast (by simpa using h)) := by
  cases l with
  | nil => simp at h
  | cons _ _ =>
    simp only [← getElem_cons_length _ _ _ rfl]
    simp only [mapIdx_cons]
    simp only [← getElem_cons_length _ _ _ rfl]
    simp only [← mapIdx_cons, getElem_mapIdx]
    simp

@[simp] theorem getLast?_mapIdx {l : List α} {f : Nat → α → β} :
    (mapIdx f l).getLast? = (getLast? l).map (f (l.length - 1)) := by
  cases l
  · simp
  · rw [getLast?_eq_getLast, getLast?_eq_getLast, getLast_mapIdx] <;> simp

@[simp] theorem mapIdx_mapIdx {l : List α} {f : Nat → α → β} {g : Nat → β → γ} :
    (l.mapIdx f).mapIdx g = l.mapIdx (fun i => g i ∘ f i) := by
  simp [mapIdx_eq_iff]

theorem mapIdx_eq_replicate_iff {l : List α} {f : Nat → α → β} {b : β} :
    mapIdx f l = replicate l.length b ↔ ∀ (i : Nat) (h : i < l.length), f i l[i] = b := by
  simp only [eq_replicate_iff, length_mapIdx, mem_mapIdx, forall_exists_index, true_and]
  constructor
  · intro w i h
    apply w _ _ _ rfl
  · rintro w _ i h rfl
    exact w i h

@[simp] theorem mapIdx_reverse {l : List α} {f : Nat → α → β} :
    l.reverse.mapIdx f = (mapIdx (fun i => f (l.length - 1 - i)) l).reverse := by
  simp [mapIdx_eq_iff]
  intro i
  by_cases h : i < l.length
  · simp [getElem?_reverse, h]
    congr
    omega
  · simp at h
    rw [getElem?_eq_none (by simp [h]), getElem?_eq_none (by simp [h])]
    simp

end List
