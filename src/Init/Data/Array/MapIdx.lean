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

@[congr] theorem mapFinIdx_congr {xs ys : Array α} (w : xs = ys)
    (f : (i : Nat) → α → (h : i < xs.size) → β) :
    mapFinIdx xs f = mapFinIdx ys (fun i a h => f i a (by simp [w]; omega)) := by
  subst w
  rfl

@[simp]
theorem mapFinIdx_nil {f : (i : Nat) → α → (h : i < 0) → β} : mapFinIdx #[] f = #[] :=
  rfl

theorem mapFinIdx_eq_ofFn {as : Array α} {f : (i : Nat) → α → (h : i < as.size) → β} :
    as.mapFinIdx f = Array.ofFn fun i : Fin as.size => f i as[i] i.2 := by
  cases as
  simp [List.mapFinIdx_eq_ofFn]

theorem mapFinIdx_append {K L : Array α} {f : (i : Nat) → α → (h : i < (K ++ L).size) → β} :
    (K ++ L).mapFinIdx f =
      K.mapFinIdx (fun i a h => f i a (by simp; omega)) ++
        L.mapFinIdx (fun i a h => f (i + K.size) a (by simp; omega)) := by
  cases K
  cases L
  simp [List.mapFinIdx_append]

@[simp]
theorem mapFinIdx_push {l : Array α} {a : α} {f : (i : Nat) → α → (h : i < (l.push a).size) → β} :
    mapFinIdx (l.push a) f =
      (mapFinIdx l (fun i a h => f i a (by simp; omega))).push (f l.size a (by simp)) := by
  simp [← append_singleton, mapFinIdx_append]

theorem mapFinIdx_singleton {a : α} {f : (i : Nat) → α → (h : i < 1) → β} :
    #[a].mapFinIdx f = #[f 0 a (by simp)] := by
  simp

theorem mapFinIdx_eq_zipWithIndex_map {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = l.zipWithIndex.attach.map
      fun ⟨⟨x, i⟩, m⟩ =>
        f i x (by simp at m; exact m.1) := by
  sorry

@[simp]
theorem mapFinIdx_eq_empty_iff {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = #[] ↔ l = #[] := by
  cases l
  simp

theorem mapFinIdx_ne_empty_iff {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f ≠ #[] ↔ l ≠ #[] := by
  simp

theorem exists_of_mem_mapFinIdx {b : β} {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β}
    (h : b ∈ l.mapFinIdx f) : ∃ (i : Nat) (h : i < l.size), f i l[i] h = b := by
  rcases l with ⟨l⟩
  exact List.exists_of_mem_mapFinIdx (by simpa using h)

@[simp] theorem mem_mapFinIdx {b : β} {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} :
    b ∈ l.mapFinIdx f ↔ ∃ (i : Nat) (h : i < l.size), f i l[i] h = b := by
  rcases l with ⟨l⟩
  simp

theorem mapFinIdx_eq_iff {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = l' ↔ ∃ h : l'.size = l.size, ∀ (i : Nat) (h : i < l.size), l'[i] = f i l[i] h := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simpa using List.mapFinIdx_eq_iff

theorem mapFinIdx_eq_push_iff {l : Array α} {b : β} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = l₂.push b ↔
      ∃ (a : α) (l₁ : Array α) (w : l = l₁.push a),
        l₁.mapFinIdx (fun i a h => f i a (by simp [w]; omega)) = l₂ ∧ b = f (l.size - 1) a (by simp [w]) := by
  rw [mapFinIdx_eq_iff]
  constructor
  · rintro ⟨h, w⟩
    sorry
  · sorry


theorem mapFinIdx_eq_mapFinIdx_iff {l : Array α} {f g : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = l.mapFinIdx g ↔ ∀ (i : Nat) (h : i < l.size), f i l[i] h = g i l[i] h := by
  rw [eq_comm, mapFinIdx_eq_iff]
  simp

@[simp] theorem mapFinIdx_mapFinIdx {l : Array α}
    {f : (i : Nat) → α → (h : i < l.size) → β}
    {g : (i : Nat) → β → (h : i < (l.mapFinIdx f).size) → γ} :
    (l.mapFinIdx f).mapFinIdx g = l.mapFinIdx (fun i a h => g i (f i a h) (by simpa using h)) := by
  simp [mapFinIdx_eq_iff]

theorem mapFinIdx_eq_mkArray_iff {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} {b : β} :
    l.mapFinIdx f = mkArray l.size b ↔ ∀ (i : Nat) (h : i < l.size), f i l[i] h = b := by
  rcases l with ⟨l⟩
  rw [← toList_inj]
  simp [List.mapFinIdx_eq_replicate_iff]

@[simp] theorem mapFinIdx_reverse {l : Array α} {f : (i : Nat) → α → (h : i < l.reverse.size) → β} :
    l.reverse.mapFinIdx f = (l.mapFinIdx (fun i a h => f (l.size - 1 - i) a (by simp; omega))).reverse := by
  rcases l with ⟨l⟩
  simp [List.mapFinIdx_reverse]

/-! ### mapIdx -/

@[simp]
theorem mapIdx_nil {f : Nat → α → β} : mapIdx f #[] = #[] :=
  rfl

@[simp] theorem mapFinIdx_eq_mapIdx {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} {g : Nat → α → β}
    (h : ∀ (i : Nat) (h : i < l.size), f i l[i] h = g i l[i]) :
    l.mapFinIdx f = l.mapIdx g := by
  simp_all [mapFinIdx_eq_iff]

theorem mapIdx_eq_mapFinIdx {l : Array α} {f : Nat → α → β} :
    l.mapIdx f = l.mapFinIdx (fun i a _ => f i a) := by
  simp [mapFinIdx_eq_mapIdx]

theorem mapIdx_eq_enum_map {l : Array α} {f : Nat → α → β} :
    l.mapIdx f = l.zipWithIndex.map fun ⟨a, i⟩ => f i a := by
  sorry

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
