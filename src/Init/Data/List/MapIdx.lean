/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Mario Carneiro
-/

prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Range
import Init.Data.List.OfFn
import Init.Data.Fin.Lemmas
import Init.Data.Option.Attach

namespace List

/-! ## Operations using indexes -/

/-! ### mapIdx -/


/--
Given a list `as = [a₀, a₁, ...]` function `f : Fin as.length → α → β`, returns the list
`[f 0 a₀, f 1 a₁, ...]`.
-/
@[inline] def mapFinIdx (as : List α) (f : Fin as.length → α → β) : List β := go as #[] (by simp) where
  /-- Auxiliary for `mapFinIdx`:
  `mapFinIdx.go [a₀, a₁, ...] acc = acc.toList ++ [f 0 a₀, f 1 a₁, ...]` -/
  @[specialize] go : (bs : List α) → (acc : Array β) → bs.length + acc.size = as.length → List β
  | [], acc, h => acc.toList
  | a :: as, acc, h =>
    go as (acc.push (f ⟨acc.size, by simp at h; omega⟩ a)) (by simp at h ⊢; omega)

/--
Given a function `f : Nat → α → β` and `as : List α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`.
-/
@[inline] def mapIdx (f : Nat → α → β) (as : List α) : List β := go as #[] where
  /-- Auxiliary for `mapIdx`:
  `mapIdx.go [a₀, a₁, ...] acc = acc.toList ++ [f acc.size a₀, f (acc.size + 1) a₁, ...]` -/
  @[specialize] go : List α → Array β → List β
  | [], acc => acc.toList
  | a :: as, acc => go as (acc.push (f acc.size a))

/-! ### mapFinIdx -/

@[simp]
theorem mapFinIdx_nil {f : Fin 0 → α → β} : mapFinIdx [] f = [] :=
  rfl

@[simp] theorem length_mapFinIdx_go :
    (mapFinIdx.go as f bs acc h).length = as.length := by
  induction bs generalizing acc with
  | nil => simpa using h
  | cons _ _ ih => simp [mapFinIdx.go, ih]

@[simp] theorem length_mapFinIdx {as : List α} {f : Fin as.length → α → β} :
    (as.mapFinIdx f).length = as.length := by
  simp [mapFinIdx, length_mapFinIdx_go]

theorem getElem_mapFinIdx_go {as : List α} {f : Fin as.length → α → β} {i : Nat} {h} {w} :
    (mapFinIdx.go as f bs acc h)[i] =
      if w' : i < acc.size then acc[i] else f ⟨i, by simp at w; omega⟩ (bs[i - acc.size]'(by simp at w; omega)) := by
  induction bs generalizing acc with
  | nil =>
    simp only [length_mapFinIdx_go, length_nil, Nat.zero_add] at w h
    simp only [mapFinIdx.go, Array.getElem_toList]
    rw [dif_pos]
  | cons _ _ ih =>
    simp [mapFinIdx.go]
    rw [ih]
    simp
    split <;> rename_i h₁ <;> split <;> rename_i h₂
    · rw [Array.getElem_push_lt]
    · have h₃ : i = acc.size := by omega
      subst h₃
      simp
    · omega
    · have h₃ : i - acc.size = (i - (acc.size + 1)) + 1 := by omega
      simp [h₃]

@[simp] theorem getElem_mapFinIdx {as : List α} {f : Fin as.length → α → β} {i : Nat} {h} :
    (as.mapFinIdx f)[i] = f ⟨i, by simp at h; omega⟩ (as[i]'(by simp at h; omega)) := by
  simp [mapFinIdx, getElem_mapFinIdx_go]

theorem mapFinIdx_eq_ofFn {as : List α} {f : Fin as.length → α → β} :
    as.mapFinIdx f = List.ofFn fun i : Fin as.length => f i as[i] := by
  apply ext_getElem <;> simp

@[simp] theorem getElem?_mapFinIdx {l : List α} {f : Fin l.length → α → β} {i : Nat} :
    (l.mapFinIdx f)[i]? = l[i]?.pbind fun x m => f ⟨i, by simp [getElem?_eq_some_iff] at m; exact m.1⟩ x := by
  simp only [getElem?_def, length_mapFinIdx, getElem_mapFinIdx]
  split <;> simp

@[simp]
theorem mapFinIdx_cons {l : List α} {a : α} {f : Fin (l.length + 1) → α → β} :
    mapFinIdx (a :: l) f = f 0 a :: mapFinIdx l (fun i => f i.succ) := by
  apply ext_getElem
  · simp
  · rintro (_|i) h₁ h₂ <;> simp

theorem mapFinIdx_append {K L : List α} {f : Fin (K ++ L).length → α → β} :
    (K ++ L).mapFinIdx f =
      K.mapFinIdx (fun i => f (i.castLE (by simp))) ++ L.mapFinIdx (fun i => f ((i.natAdd K.length).cast (by simp))) := by
  apply ext_getElem
  · simp
  · intro i h₁ h₂
    rw [getElem_append]
    simp only [getElem_mapFinIdx, length_mapFinIdx]
    split <;> rename_i h
    · rw [getElem_append_left]
      congr
    · simp only [Nat.not_lt] at h
      rw [getElem_append_right h]
      congr
      simp
      omega

@[simp] theorem mapFinIdx_concat {l : List α} {e : α} {f : Fin (l ++ [e]).length → α → β}:
    (l ++ [e]).mapFinIdx f = l.mapFinIdx (fun i => f (i.castLE (by simp))) ++ [f ⟨l.length, by simp⟩ e] := by
  simp [mapFinIdx_append]
  congr

theorem mapFinIdx_singleton {a : α} {f : Fin 1 → α → β} :
    [a].mapFinIdx f = [f ⟨0, by simp⟩ a] := by
  simp

theorem mapFinIdx_eq_enum_map {l : List α} {f : Fin l.length → α → β} :
    l.mapFinIdx f = l.enum.attach.map
      fun ⟨⟨i, x⟩, m⟩ =>
        f ⟨i, by rw [mk_mem_enum_iff_getElem?, getElem?_eq_some_iff] at m; exact m.1⟩ x := by
  apply ext_getElem <;> simp

@[simp]
theorem mapFinIdx_eq_nil_iff {l : List α} {f : Fin l.length → α → β} :
    l.mapFinIdx f = [] ↔ l = [] := by
  rw [mapFinIdx_eq_enum_map, map_eq_nil_iff, attach_eq_nil_iff, enum_eq_nil_iff]

theorem mapFinIdx_ne_nil_iff {l : List α} {f : Fin l.length → α → β} :
    l.mapFinIdx f ≠ [] ↔ l ≠ [] := by
  simp

theorem exists_of_mem_mapFinIdx {b : β} {l : List α} {f : Fin l.length → α → β}
    (h : b ∈ l.mapFinIdx f) : ∃ (i : Fin l.length), f i l[i] = b := by
  rw [mapFinIdx_eq_enum_map] at h
  replace h := exists_of_mem_map h
  simp only [mem_attach, true_and, Subtype.exists, Prod.exists, mk_mem_enum_iff_getElem?] at h
  obtain ⟨i, b, h, rfl⟩ := h
  rw [getElem?_eq_some_iff] at h
  obtain ⟨h', rfl⟩ := h
  exact ⟨⟨i, h'⟩, rfl⟩

@[simp] theorem mem_mapFinIdx {b : β} {l : List α} {f : Fin l.length → α → β} :
    b ∈ l.mapFinIdx f ↔ ∃ (i : Fin l.length), f i l[i] = b := by
  constructor
  · intro h
    exact exists_of_mem_mapFinIdx h
  · rintro ⟨i, h, rfl⟩
    rw [mem_iff_getElem]
    exact ⟨i, by simp⟩

theorem mapFinIdx_eq_cons_iff {l : List α} {b : β} {f : Fin l.length → α → β} :
    l.mapFinIdx f = b :: l₂ ↔
      ∃ (a : α) (l₁ : List α) (h : l = a :: l₁),
        f ⟨0, by simp [h]⟩ a = b ∧ l₁.mapFinIdx (fun i => f (i.succ.cast (by simp [h]))) = l₂ := by
  cases l with
  | nil => simp
  | cons x l' =>
    simp only [mapFinIdx_cons, cons.injEq, length_cons, Fin.zero_eta, Fin.cast_succ_eq,
      exists_and_left]
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨x, rfl, l', by simp⟩
    · rintro ⟨a, ⟨rfl, h⟩, ⟨_, ⟨rfl, rfl⟩, h⟩⟩
      exact ⟨rfl, h⟩

theorem mapFinIdx_eq_cons_iff' {l : List α} {b : β} {f : Fin l.length → α → β} :
    l.mapFinIdx f = b :: l₂ ↔
      l.head?.pbind (fun x m => (f ⟨0, by cases l <;> simp_all⟩ x)) = some b ∧
        l.tail?.attach.map (fun ⟨t, m⟩ => t.mapFinIdx fun i => f (i.succ.cast (by cases l <;> simp_all))) = some l₂ := by
  cases l <;> simp

theorem mapFinIdx_eq_iff {l : List α} {f : Fin l.length → α → β} :
    l.mapFinIdx f = l' ↔ ∃ h : l'.length = l.length, ∀ (i : Nat) (h : i < l.length), l'[i] = f ⟨i, h⟩ l[i] := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h, w⟩
    apply ext_getElem <;> simp_all

theorem mapFinIdx_eq_mapFinIdx_iff {l : List α} {f g : Fin l.length → α → β} :
    l.mapFinIdx f = l.mapFinIdx g ↔ ∀ (i : Fin l.length), f i l[i] = g i l[i] := by
  rw [eq_comm, mapFinIdx_eq_iff]
  simp [Fin.forall_iff]

@[simp] theorem mapFinIdx_mapFinIdx {l : List α} {f : Fin l.length → α → β} {g : Fin _ → β → γ} :
    (l.mapFinIdx f).mapFinIdx g = l.mapFinIdx (fun i => g (i.cast (by simp)) ∘ f i) := by
  simp [mapFinIdx_eq_iff]

theorem mapFinIdx_eq_replicate_iff {l : List α} {f : Fin l.length → α → β} {b : β} :
    l.mapFinIdx f = replicate l.length b ↔ ∀ (i : Fin l.length), f i l[i] = b := by
  simp [eq_replicate_iff, length_mapFinIdx, mem_mapFinIdx, forall_exists_index, true_and]

@[simp] theorem mapFinIdx_reverse {l : List α} {f : Fin l.reverse.length → α → β} :
    l.reverse.mapFinIdx f = (l.mapFinIdx (fun i => f ⟨l.length - 1 - i, by simp; omega⟩)).reverse := by
  simp [mapFinIdx_eq_iff]
  intro i h
  congr
  omega

/-! ### mapIdx -/

@[simp]
theorem mapIdx_nil {f : Nat → α → β} : mapIdx f [] = [] :=
  rfl

theorem mapIdx_go_length {arr : Array β} :
    length (mapIdx.go f l arr) = length l + arr.size := by
  induction l generalizing arr with
  | nil => simp only [mapIdx.go, length_nil, Nat.zero_add]
  | cons _ _ ih =>
    simp only [mapIdx.go, ih, Array.size_push, Nat.add_succ, length_cons, Nat.add_comm]

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
    simp only [mapIdx.go, Array.toListImpl_eq, getElem?_def, Array.length_toList,
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

@[simp] theorem mapFinIdx_eq_mapIdx {l : List α} {f : Fin l.length → α → β} {g : Nat → α → β}
    (h : ∀ (i : Fin l.length), f i l[i] = g i l[i]) :
    l.mapFinIdx f = l.mapIdx g := by
  simp_all [mapFinIdx_eq_iff]

theorem mapIdx_eq_mapFinIdx {l : List α} {f : Nat → α → β} :
    l.mapIdx f = l.mapFinIdx (fun i => f i) := by
  simp [mapFinIdx_eq_mapIdx]

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

@[simp] theorem mapIdx_concat {l : List α} {e : α} :
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] := by
  simp [mapIdx_append]

theorem mapIdx_singleton {a : α} : mapIdx f [a] = [f 0 a] := by
  simp

@[simp]
theorem mapIdx_eq_nil_iff {l : List α} : List.mapIdx f l = [] ↔ l = [] := by
  rw [List.mapIdx_eq_enum_map, List.map_eq_nil_iff, List.enum_eq_nil_iff]

theorem mapIdx_ne_nil_iff {l : List α} :
    List.mapIdx f l ≠ [] ↔ l ≠ [] := by
  simp

theorem exists_of_mem_mapIdx {b : β} {l : List α}
    (h : b ∈ mapIdx f l) : ∃ (i : Nat) (h : i < l.length), f i l[i] = b := by
  rw [mapIdx_eq_mapFinIdx] at h
  simpa [Fin.exists_iff] using exists_of_mem_mapFinIdx h

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
