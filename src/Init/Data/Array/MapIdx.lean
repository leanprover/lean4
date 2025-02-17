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

@[simp] theorem size_zipIdx (as : Array α) (k : Nat) : (as.zipIdx k).size = as.size :=
  Array.size_mapFinIdx _ _

@[deprecated size_zipIdx (since := "2025-01-21")] abbrev size_zipWithIndex := @size_zipIdx

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

/-! ### zipIdx -/

@[simp] theorem getElem_zipIdx (a : Array α) (k : Nat) (i : Nat) (h : i < (a.zipIdx k).size) :
    (a.zipIdx k)[i] = (a[i]'(by simp_all), k + i) := by
  simp [zipIdx]

@[deprecated getElem_zipIdx (since := "2025-01-21")]
abbrev getElem_zipWithIndex := @getElem_zipIdx

@[simp] theorem zipIdx_toArray {l : List α} {k : Nat} :
    l.toArray.zipIdx k = (l.zipIdx k).toArray := by
  ext i hi₁ hi₂ <;> simp [Nat.add_comm]

@[deprecated zipIdx_toArray (since := "2025-01-21")]
abbrev zipWithIndex_toArray := @zipIdx_toArray

@[simp] theorem toList_zipIdx (a : Array α) (k : Nat) :
    (a.zipIdx k).toList = a.toList.zipIdx k := by
  rcases a with ⟨a⟩
  simp

@[deprecated toList_zipIdx (since := "2025-01-21")]
abbrev toList_zipWithIndex := @toList_zipIdx

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {k i : Nat} {x : α} {l : Array α} :
    (x, i) ∈ zipIdx l k ↔ k ≤ i ∧ l[i - k]? = some x := by
  rcases l with ⟨l⟩
  simp [List.mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mk_mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mk_mem_zipIdx_iff_getElem? {x : α} {i : Nat} {l : Array α} :
    (x, i) ∈ l.zipIdx ↔ l[i]? = x := by
  rw [mk_mem_zipIdx_iff_le_and_getElem?_sub]
  simp

theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {l : Array α} {k : Nat} :
    x ∈ zipIdx l k ↔ k ≤ x.2 ∧ l[x.2 - k]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mem_zipIdx_iff_getElem? {x : α × Nat} {l : Array α} :
    x ∈ l.zipIdx ↔ l[x.2]? = some x.1 := by
  rw [mk_mem_zipIdx_iff_getElem?]

@[deprecated mk_mem_zipIdx_iff_getElem? (since := "2025-01-21")]
abbrev mk_mem_zipWithIndex_iff_getElem? := @mk_mem_zipIdx_iff_getElem?

@[deprecated mem_zipIdx_iff_getElem? (since := "2025-01-21")]
abbrev mem_zipWithIndex_iff_getElem? := @mem_zipIdx_iff_getElem?

/-! ### mapFinIdx -/

@[congr] theorem mapFinIdx_congr {xs ys : Array α} (w : xs = ys)
    (f : (i : Nat) → α → (h : i < xs.size) → β) :
    mapFinIdx xs f = mapFinIdx ys (fun i a h => f i a (by simp [w]; omega)) := by
  subst w
  rfl

@[simp]
theorem mapFinIdx_empty {f : (i : Nat) → α → (h : i < 0) → β} : mapFinIdx #[] f = #[] :=
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

theorem mapFinIdx_eq_zipIdx_map {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = l.zipIdx.attach.map
      fun ⟨⟨x, i⟩, m⟩ =>
        f i x (by simp [mk_mem_zipIdx_iff_getElem?, getElem?_eq_some_iff] at m; exact m.1) := by
  ext <;> simp

@[deprecated mapFinIdx_eq_zipIdx_map (since := "2025-01-21")]
abbrev mapFinIdx_eq_zipWithIndex_map := @mapFinIdx_eq_zipIdx_map

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

@[simp] theorem mapFinIdx_eq_singleton_iff {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} {b : β} :
    l.mapFinIdx f = #[b] ↔ ∃ (a : α) (w : l = #[a]), f 0 a (by simp [w]) = b := by
  rcases l with ⟨l⟩
  simp

theorem mapFinIdx_eq_append_iff {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} {l₁ l₂ : Array β} :
    l.mapFinIdx f = l₁ ++ l₂ ↔
      ∃ (l₁' : Array α) (l₂' : Array α) (w : l = l₁' ++ l₂'),
        l₁'.mapFinIdx (fun i a h => f i a (by simp [w]; omega)) = l₁ ∧
        l₂'.mapFinIdx (fun i a h => f (i + l₁'.size) a (by simp [w]; omega)) = l₂ := by
  rcases l with ⟨l⟩
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp only [List.mapFinIdx_toArray, List.append_toArray, mk.injEq, List.mapFinIdx_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    refine ⟨l₁.toArray, l₂.toArray, by simp_all⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, rfl, h₁, h₂⟩
    simp [← toList_inj] at h₁ h₂
    obtain rfl := h₁
    obtain rfl := h₂
    refine ⟨l₁, l₂, by simp_all⟩

theorem mapFinIdx_eq_push_iff {l : Array α} {b : β} {f : (i : Nat) → α → (h : i < l.size) → β} :
    l.mapFinIdx f = l₂.push b ↔
      ∃ (l₁ : Array α) (a : α) (w : l = l₁.push a),
        l₁.mapFinIdx (fun i a h => f i a (by simp [w]; omega)) = l₂ ∧ b = f (l.size - 1) a (by simp [w]) := by
  rw [push_eq_append, mapFinIdx_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, h₂⟩
    simp only [mapFinIdx_eq_singleton_iff, Nat.zero_add] at h₂
    obtain ⟨a, rfl, rfl⟩ := h₂
    exact ⟨l₁, a, by simp⟩
  · rintro ⟨l₁, a, rfl, rfl, rfl⟩
    exact ⟨l₁, #[a], by simp⟩

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
theorem mapIdx_empty {f : Nat → α → β} : mapIdx f #[] = #[] :=
  rfl

@[simp] theorem mapFinIdx_eq_mapIdx {l : Array α} {f : (i : Nat) → α → (h : i < l.size) → β} {g : Nat → α → β}
    (h : ∀ (i : Nat) (h : i < l.size), f i l[i] h = g i l[i]) :
    l.mapFinIdx f = l.mapIdx g := by
  simp_all [mapFinIdx_eq_iff]

theorem mapIdx_eq_mapFinIdx {l : Array α} {f : Nat → α → β} :
    l.mapIdx f = l.mapFinIdx (fun i a _ => f i a) := by
  simp [mapFinIdx_eq_mapIdx]

theorem mapIdx_eq_zipIdx_map {l : Array α} {f : Nat → α → β} :
    l.mapIdx f = l.zipIdx.map fun ⟨a, i⟩ => f i a := by
  ext <;> simp

@[deprecated mapIdx_eq_zipIdx_map (since := "2025-01-21")]
abbrev mapIdx_eq_zipWithIndex_map := @mapIdx_eq_zipIdx_map

theorem mapIdx_append {K L : Array α} :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i => f (i + K.size) := by
  rcases K with ⟨K⟩
  rcases L with ⟨L⟩
  simp [List.mapIdx_append]

@[simp]
theorem mapIdx_push {l : Array α} {a : α} :
    mapIdx f (l.push a) = (mapIdx f l).push (f l.size a) := by
  simp [← append_singleton, mapIdx_append]

theorem mapIdx_singleton {a : α} : mapIdx f #[a] = #[f 0 a] := by
  simp

@[simp]
theorem mapIdx_eq_empty_iff {l : Array α} : mapIdx f l = #[] ↔ l = #[] := by
  rcases l with ⟨l⟩
  simp

theorem mapIdx_ne_empty_iff {l : Array α} :
    mapIdx f l ≠ #[] ↔ l ≠ #[] := by
  simp

theorem exists_of_mem_mapIdx {b : β} {l : Array α}
    (h : b ∈ mapIdx f l) : ∃ (i : Nat) (h : i < l.size), f i l[i] = b := by
  rw [mapIdx_eq_mapFinIdx] at h
  simpa [Fin.exists_iff] using exists_of_mem_mapFinIdx h

@[simp] theorem mem_mapIdx {b : β} {l : Array α} :
    b ∈ mapIdx f l ↔ ∃ (i : Nat) (h : i < l.size), f i l[i] = b := by
  constructor
  · intro h
    exact exists_of_mem_mapIdx h
  · rintro ⟨i, h, rfl⟩
    rw [mem_iff_getElem]
    exact ⟨i, by simpa using h, by simp⟩

theorem mapIdx_eq_push_iff {l : Array α} {b : β} :
    mapIdx f l = l₂.push b ↔
      ∃ (a : α) (l₁ : Array α), l = l₁.push a ∧ mapIdx f l₁ = l₂ ∧ f l₁.size a = b := by
  rw [mapIdx_eq_mapFinIdx, mapFinIdx_eq_push_iff]
  simp only [mapFinIdx_eq_mapIdx, exists_and_left, exists_prop]
  constructor
  · rintro ⟨l₁, rfl, a, rfl, rfl⟩
    exact ⟨a, l₁, by simp⟩
  · rintro ⟨a, l₁, rfl, rfl, rfl⟩
    exact ⟨l₁, rfl, a, by simp⟩

@[simp] theorem mapIdx_eq_singleton_iff {l : Array α} {f : Nat → α → β} {b : β} :
    mapIdx f l = #[b] ↔ ∃ (a : α), l = #[a] ∧ f 0 a = b := by
  rcases l with ⟨l⟩
  simp [List.mapIdx_eq_singleton_iff]

theorem mapIdx_eq_append_iff {l : Array α} {f : Nat → α → β} {l₁ l₂ : Array β} :
    mapIdx f l = l₁ ++ l₂ ↔
      ∃ (l₁' : Array α) (l₂' : Array α), l = l₁' ++ l₂' ∧
        l₁'.mapIdx f = l₁ ∧
        l₂'.mapIdx (fun i => f (i + l₁'.size)) = l₂ := by
  rcases l with ⟨l⟩
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp only [List.mapIdx_toArray, List.append_toArray, mk.injEq, List.mapIdx_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₁.toArray, l₂.toArray, by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, rfl, h₁, h₂⟩
    simp only [List.mapIdx_toArray, mk.injEq, size_toArray] at h₁ h₂
    obtain rfl := h₁
    obtain rfl := h₂
    exact ⟨l₁, l₂, by simp⟩

theorem mapIdx_eq_iff {l : Array α} : mapIdx f l = l' ↔ ∀ i : Nat, l'[i]? = l[i]?.map (f i) := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp [List.mapIdx_eq_iff]

theorem mapIdx_eq_mapIdx_iff {l : Array α} :
    mapIdx f l = mapIdx g l ↔ ∀ i : Nat, (h : i < l.size) → f i l[i] = g i l[i] := by
  rcases l with ⟨l⟩
  simp [List.mapIdx_eq_mapIdx_iff]

@[simp] theorem mapIdx_set {l : Array α} {i : Nat} {h : i < l.size} {a : α} :
    (l.set i a).mapIdx f = (l.mapIdx f).set i (f i a) (by simpa) := by
  rcases l with ⟨l⟩
  simp [List.mapIdx_set]

@[simp] theorem mapIdx_setIfInBounds {l : Array α} {i : Nat} {a : α} :
    (l.setIfInBounds i a).mapIdx f = (l.mapIdx f).setIfInBounds i (f i a) := by
  rcases l with ⟨l⟩
  simp [List.mapIdx_set]

@[simp] theorem back?_mapIdx {l : Array α} {f : Nat → α → β} :
    (mapIdx f l).back? = (l.back?).map (f (l.size - 1)) := by
  rcases l with ⟨l⟩
  simp [List.getLast?_mapIdx]

@[simp] theorem back_mapIdx {l : Array α} {f : Nat → α → β} (h) :
    (l.mapIdx f).back h = f (l.size - 1) (l.back (by simpa using h)) := by
  rcases l with ⟨l⟩
  simp [List.getLast_mapIdx]

@[simp] theorem mapIdx_mapIdx {l : Array α} {f : Nat → α → β} {g : Nat → β → γ} :
    (l.mapIdx f).mapIdx g = l.mapIdx (fun i => g i ∘ f i) := by
  simp [mapIdx_eq_iff]

theorem mapIdx_eq_mkArray_iff {l : Array α} {f : Nat → α → β} {b : β} :
    mapIdx f l = mkArray l.size b ↔ ∀ (i : Nat) (h : i < l.size), f i l[i] = b := by
  rcases l with ⟨l⟩
  rw [← toList_inj]
  simp [List.mapIdx_eq_replicate_iff]

@[simp] theorem mapIdx_reverse {l : Array α} {f : Nat → α → β} :
    l.reverse.mapIdx f = (mapIdx (fun i => f (l.size - 1 - i)) l).reverse := by
  rcases l with ⟨l⟩
  simp [List.mapIdx_reverse]

end Array

namespace List

theorem mapFinIdxM_toArray [Monad m] [LawfulMonad m] (l : List α)
    (f : (i : Nat) → α → (h : i < l.length) → m β) :
    l.toArray.mapFinIdxM f = toArray <$> l.mapFinIdxM f := by
  let rec go (i : Nat) (acc : Array β) (inv : i + acc.size = l.length) :
      Array.mapFinIdxM.map l.toArray f i acc.size inv acc
      = toArray <$> mapFinIdxM.go l f (l.drop acc.size) acc
        (by simp [Nat.sub_add_cancel (Nat.le.intro (Nat.add_comm _ _ ▸ inv))]) := by
    match i with
    | 0 =>
      rw [Nat.zero_add] at inv
      simp only [Array.mapFinIdxM.map, inv, drop_length, mapFinIdxM.go, map_pure]
    | k + 1 =>
      conv => enter [2, 2, 3]; rw [← getElem_cons_drop l acc.size (by omega)]
      simp only [Array.mapFinIdxM.map, mapFinIdxM.go, _root_.map_bind]
      congr; funext x
      conv => enter [1, 4]; rw [← Array.size_push _ x]
      conv => enter [2, 2, 3]; rw [← Array.size_push _ x]
      refine go k (acc.push x) _
  simp only [Array.mapFinIdxM, mapFinIdxM]
  exact go _ #[] _

theorem mapIdxM_toArray [Monad m] [LawfulMonad m] (l : List α)
    (f : Nat → α → m β) :
    l.toArray.mapIdxM f = toArray <$> l.mapIdxM f := by
  let rec go (bs : List α) (acc : Array β) (inv : bs.length + acc.size = l.length) :
      mapFinIdxM.go l (fun i a h => f i a) bs acc inv = mapIdxM.go f bs acc := by
    match bs with
    | [] => simp only [mapFinIdxM.go, mapIdxM.go]
    | x :: xs => simp only [mapFinIdxM.go, mapIdxM.go, go]
  unfold Array.mapIdxM
  rw [mapFinIdxM_toArray]
  simp only [mapFinIdxM, mapIdxM]
  rw [go]

end List

namespace Array

theorem toList_mapFinIdxM [Monad m] [LawfulMonad m] (l : Array α)
    (f : (i : Nat) → α → (h : i < l.size) → m β) :
    toList <$> l.mapFinIdxM f = l.toList.mapFinIdxM f := by
  rw [List.mapFinIdxM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_mapIdxM [Monad m] [LawfulMonad m] (l : Array α)
    (f : Nat → α → m β) :
    toList <$> l.mapIdxM f = l.toList.mapIdxM f := by
  rw [List.mapIdxM_toArray]
  simp only [Functor.map_map, id_map']

end Array
