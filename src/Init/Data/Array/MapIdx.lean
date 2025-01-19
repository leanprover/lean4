/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.Array.Attach
import Init.Data.List.MapIdx

namespace Array

/-! ### mapFinIdx -/

-- This could also be proved from `SatisfiesM_mapIdxM` in Batteries.
theorem mapFinIdx_induction (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : (i : Nat) → β → (h : i < as.size) → Prop)
    (hs : ∀ i h, motive i → p i (f i as[i] h) h ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (Array.mapFinIdx as f).size = as.size,
      ∀ i h, p i ((Array.mapFinIdx as f)[i]) h := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p i bs[i] h) (hm : motive j) :
    let arr : Array β := Array.mapFinIdxM.map (m := Id) as f i j h bs
    motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p i arr[i] h := by
    induction i generalizing j bs with simp [mapFinIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      apply @ih (bs.push (f j as[j] (by omega))) (j + 1) (by omega) (by simp; omega)
      · intro i i_lt h'
        rw [getElem_push]
        split
        · apply h₂
        · simp only [size_push] at h'
          obtain rfl : i = j := by omega
          apply (hs i (by omega) hm).1
      · exact (hs j (by omega) hm).2
  simp [mapFinIdx, mapFinIdxM]; exact go rfl nofun h0

theorem mapFinIdx_spec (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → β)
    (p : (i : Nat) → β → (h : i < as.size) → Prop) (hs : ∀ i h, p i (f i as[i] h) h) :
    ∃ eq : (Array.mapFinIdx as f).size = as.size,
      ∀ i h, p i ((Array.mapFinIdx as f)[i]) h :=
  (mapFinIdx_induction _ _ (fun _ => True) trivial p fun _ _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapFinIdx (a : Array α) (f : (i : Nat) → α → (h : i < a.size) → β) :
    (a.mapFinIdx f).size = a.size :=
  (mapFinIdx_spec (p := fun _ _ _ => True) (hs := fun _ _ => trivial)).1

@[simp] theorem size_zipWithIndex (as : Array α) : as.zipWithIndex.size = as.size :=
  Array.size_mapFinIdx _ _

@[simp] theorem getElem_mapFinIdx (a : Array α) (f : (i : Nat) → α → (h : i < a.size) → β) (i : Nat)
    (h : i < (mapFinIdx a f).size) :
    (a.mapFinIdx f)[i] = f i (a[i]'(by simp_all))  (by simp_all) :=
  (mapFinIdx_spec _ _ (fun i b h => b = f i a[i] h) fun _ _ => rfl).2 i _

@[simp] theorem getElem?_mapFinIdx (a : Array α) (f : (i : Nat) → α → (h : i < a.size) → β) (i : Nat) :
    (a.mapFinIdx f)[i]? =
      a[i]?.pbind fun b h => f i b (getElem?_eq_some_iff.1 h).1 := by
  simp only [getElem?_def, size_mapFinIdx, getElem_mapFinIdx]
  split <;> simp_all

@[simp] theorem toList_mapFinIdx (a : Array α) (f : (i : Nat) → α → (h : i < a.size) → β) :
    (a.mapFinIdx f).toList = a.toList.mapFinIdx (fun i a h => f i a (by simpa)) := by
  apply List.ext_getElem <;> simp

/-! ### mapIdx -/

theorem mapIdx_induction (f : Nat → α → β) (as : Array α)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : (i : Nat) → β → (h : i < as.size) → Prop)
    (hs : ∀ i h, motive i → p i (f i as[i]) h ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (as.mapIdx f).size = as.size,
      ∀ i h, p i ((as.mapIdx f)[i]) h :=
  mapFinIdx_induction as (fun i a _ => f i a) motive h0 p hs

theorem mapIdx_spec (f : Nat → α → β) (as : Array α)
    (p : (i : Nat) → β → (h : i < as.size) → Prop) (hs : ∀ i h, p i (f i as[i]) h) :
    ∃ eq : (as.mapIdx f).size = as.size,
      ∀ i h, p i ((as.mapIdx f)[i]) h :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (f : Nat → α → β) (as : Array α) : (as.mapIdx f).size = as.size :=
  (mapIdx_spec (p := fun _ _ _ => True) (hs := fun _ _ => trivial)).1

@[simp] theorem getElem_mapIdx (f : Nat → α → β) (as : Array α) (i : Nat)
    (h : i < (as.mapIdx f).size) :
    (as.mapIdx f)[i] = f i (as[i]'(by simp_all)) :=
  (mapIdx_spec _ _ (fun i b h => b = f i as[i]) fun _ _ => rfl).2 i (by simp_all)

@[simp] theorem getElem?_mapIdx (f : Nat → α → β) (as : Array α) (i : Nat) :
    (as.mapIdx f)[i]? =
      as[i]?.map (f i) := by
  simp [getElem?_def, size_mapIdx, getElem_mapIdx]

@[simp] theorem toList_mapIdx (f : Nat → α → β) (as : Array α) :
    (as.mapIdx f).toList = as.toList.mapIdx (fun i a => f i a) := by
  apply List.ext_getElem <;> simp

end Array

namespace List

@[simp] theorem mapFinIdx_toArray (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) :
    l.toArray.mapFinIdx f = (l.mapFinIdx f).toArray := by
  ext <;> simp

@[simp] theorem mapIdx_toArray (f : Nat → α → β) (l : List α) :
    l.toArray.mapIdx f = (l.mapIdx f).toArray := by
  ext <;> simp

end List

namespace Array

/-! ### mapFinIdx -/

@[simp]
theorem mapFinIdx_nil {f : Fin 0 → α → β} : mapFinIdx #[] f = #[] :=
  rfl

theorem mapFinIdx_eq_ofFn {as : Array α} {f : Fin as.size → α → β} :
    as.mapFinIdx f = Array.ofFn fun i : Fin as.size => f i as[i] := by
  cases as
  simp [List.mapFinIdx_eq_ofFn]

@[simp]
theorem mapFinIdx_push {l : Array α} {a : α} {f : Fin (l.push a).size → α → β} :
    mapFinIdx (l.push a) f =
      (mapFinIdx l (fun i => f (i.castLE (by simp)))).push (f ⟨l.size, by simp⟩ a) := by
  sorry

theorem mapFinIdx_append {K L : Array α} {f : Fin (K ++ L).size → α → β} :
    (K ++ L).mapFinIdx f =
      K.mapFinIdx (fun i => f (i.castLE (by simp))) ++
        L.mapFinIdx (fun i => f ((i.natAdd K.size).cast (by simp))) := by
  cases K
  cases L
  simp [List.mapFinIdx_append]
  sorry

theorem mapFinIdx_singleton {a : α} {f : Fin 1 → α → β} :
    #[a].mapFinIdx f = #[f ⟨0, by simp⟩ a] := by
  simp

theorem mapFinIdx_eq_zipWithIndex_map {l : Array α} {f : Fin l.size → α → β} :
    l.mapFinIdx f = l.zipWithIndex.attach.map
      fun ⟨⟨x, i⟩, m⟩ =>
        f ⟨i, by simp at m; exact m.1⟩ x := by
  sorry

@[simp]
theorem mapFinIdx_eq_empty_iff {l : Array α} {f : Fin l.size → α → β} :
    l.mapFinIdx f = #[] ↔ l = #[] := by
  cases l
  simp

theorem mapFinIdx_ne_empty_iff {l : Array α} {f : Fin l.size → α → β} :
    l.mapFinIdx f ≠ #[] ↔ l ≠ #[] := by
  simp

theorem exists_of_mem_mapFinIdx {b : β} {l : Array α} {f : Fin l.size → α → β}
    (h : b ∈ l.mapFinIdx f) : ∃ (i : Fin l.size), f i l[i] = b := by
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
      ← Array.getElem_toList, length_nil, Nat.not_lt_zero, ↓reduceDIte, Option.map_none']
  | a :: l, arr, i => by
    rw [mapIdx.go, getElem?_mapIdx_go]
    simp only [Array.size_push]
    split <;> split
    · simp only [Option.some.injEq]
      rw [← Array.getElem_toList]
      simp only [Array.push_toList]
      rw [getElem_append_left, ← Array.getElem_toList]
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
