/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.Array.Attach
import Init.Data.List.MapIdx

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/-! ### mapFinIdx -/

-- This could also be proved from `SatisfiesM_mapIdxM` in Batteries.
theorem mapFinIdx_induction (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : (i : Nat) → β → (h : i < xs.size) → Prop)
    (hs : ∀ i h, motive i → p i (f i xs[i] h) h ∧ motive (i + 1)) :
    motive xs.size ∧ ∃ eq : (Array.mapFinIdx xs f).size = xs.size,
      ∀ i h, p i ((Array.mapFinIdx xs f)[i]) h := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p i bs[i] h) (hm : motive j) :
    let as : Array β := Array.mapFinIdxM.map (m := Id) xs f i j h bs
    motive xs.size ∧ ∃ eq : as.size = xs.size, ∀ i h, p i as[i] h := by
    induction i generalizing j bs with simp [mapFinIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      apply @ih (bs.push (f j xs[j] (by omega))) (j + 1) (by omega) (by simp; omega)
      · intro i i_lt h'
        rw [getElem_push]
        split
        · apply h₂
        · simp only [size_push] at h'
          obtain rfl : i = j := by omega
          apply (hs i (by omega) hm).1
      · exact (hs j (by omega) hm).2
  simp [mapFinIdx, mapFinIdxM]; exact go rfl nofun h0

theorem mapFinIdx_spec (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β)
    (p : (i : Nat) → β → (h : i < xs.size) → Prop) (hs : ∀ i h, p i (f i xs[i] h) h) :
    ∃ eq : (Array.mapFinIdx xs f).size = xs.size,
      ∀ i h, p i ((Array.mapFinIdx xs f)[i]) h :=
  (mapFinIdx_induction _ _ (fun _ => True) trivial p fun _ _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapFinIdx (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β) :
    (xs.mapFinIdx f).size = xs.size :=
  (mapFinIdx_spec (p := fun _ _ _ => True) (hs := fun _ _ => trivial)).1

@[simp] theorem size_zipIdx (xs : Array α) (k : Nat) : (xs.zipIdx k).size = xs.size :=
  Array.size_mapFinIdx _ _

@[deprecated size_zipIdx (since := "2025-01-21")] abbrev size_zipWithIndex := @size_zipIdx

@[simp] theorem getElem_mapFinIdx (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β) (i : Nat)
    (h : i < (xs.mapFinIdx f).size) :
    (xs.mapFinIdx f)[i] = f i (xs[i]'(by simp_all)) (by simp_all) :=
  (mapFinIdx_spec _ _ (fun i b h => b = f i xs[i] h) fun _ _ => rfl).2 i _

@[simp] theorem getElem?_mapFinIdx (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β) (i : Nat) :
    (xs.mapFinIdx f)[i]? =
      xs[i]?.pbind fun b h => f i b (getElem?_eq_some_iff.1 h).1 := by
  simp only [getElem?_def, size_mapFinIdx, getElem_mapFinIdx]
  split <;> simp_all

@[simp] theorem toList_mapFinIdx (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β) :
    (xs.mapFinIdx f).toList = xs.toList.mapFinIdx (fun i a h => f i a (by simpa)) := by
  apply List.ext_getElem <;> simp

/-! ### mapIdx -/

theorem mapIdx_induction (f : Nat → α → β) (xs : Array α)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : (i : Nat) → β → (h : i < xs.size) → Prop)
    (hs : ∀ i h, motive i → p i (f i xs[i]) h ∧ motive (i + 1)) :
    motive xs.size ∧ ∃ eq : (xs.mapIdx f).size = xs.size,
      ∀ i h, p i ((xs.mapIdx f)[i]) h :=
  mapFinIdx_induction xs (fun i a _ => f i a) motive h0 p hs

theorem mapIdx_spec (f : Nat → α → β) (xs : Array α)
    (p : (i : Nat) → β → (h : i < xs.size) → Prop) (hs : ∀ i h, p i (f i xs[i]) h) :
    ∃ eq : (xs.mapIdx f).size = xs.size,
      ∀ i h, p i ((xs.mapIdx f)[i]) h :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (f : Nat → α → β) (xs : Array α) : (xs.mapIdx f).size = xs.size :=
  (mapIdx_spec (p := fun _ _ _ => True) (hs := fun _ _ => trivial)).1

@[simp] theorem getElem_mapIdx (f : Nat → α → β) (xs : Array α) (i : Nat)
    (h : i < (xs.mapIdx f).size) :
    (xs.mapIdx f)[i] = f i (xs[i]'(by simp_all)) :=
  (mapIdx_spec _ _ (fun i b h => b = f i xs[i]) fun _ _ => rfl).2 i (by simp_all)

@[simp] theorem getElem?_mapIdx (f : Nat → α → β) (xs : Array α) (i : Nat) :
    (xs.mapIdx f)[i]? =
      xs[i]?.map (f i) := by
  simp [getElem?_def, size_mapIdx, getElem_mapIdx]

@[simp] theorem toList_mapIdx (f : Nat → α → β) (xs : Array α) :
    (xs.mapIdx f).toList = xs.toList.mapIdx (fun i a => f i a) := by
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

@[simp] theorem getElem_zipIdx (xs : Array α) (k : Nat) (i : Nat) (h : i < (xs.zipIdx k).size) :
    (xs.zipIdx k)[i] = (xs[i]'(by simp_all), k + i) := by
  simp [zipIdx]

@[deprecated getElem_zipIdx (since := "2025-01-21")]
abbrev getElem_zipWithIndex := @getElem_zipIdx

@[simp] theorem zipIdx_toArray {l : List α} {k : Nat} :
    l.toArray.zipIdx k = (l.zipIdx k).toArray := by
  ext i hi₁ hi₂ <;> simp [Nat.add_comm]

@[deprecated zipIdx_toArray (since := "2025-01-21")]
abbrev zipWithIndex_toArray := @zipIdx_toArray

@[simp] theorem toList_zipIdx (xs : Array α) (k : Nat) :
    (xs.zipIdx k).toList = xs.toList.zipIdx k := by
  rcases xs with ⟨xs⟩
  simp

@[deprecated toList_zipIdx (since := "2025-01-21")]
abbrev toList_zipWithIndex := @toList_zipIdx

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {k i : Nat} {x : α} {xs : Array α} :
    (x, i) ∈ xs.zipIdx k ↔ k ≤ i ∧ xs[i - k]? = some x := by
  rcases xs with ⟨xs⟩
  simp [List.mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mk_mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mk_mem_zipIdx_iff_getElem? {x : α} {i : Nat} {xs : Array α} :
    (x, i) ∈ xs.zipIdx ↔ xs[i]? = x := by
  rw [mk_mem_zipIdx_iff_le_and_getElem?_sub]
  simp

theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {xs : Array α} {k : Nat} :
    x ∈ xs.zipIdx k ↔ k ≤ x.2 ∧ xs[x.2 - k]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mem_zipIdx_iff_getElem? {x : α × Nat} {xs : Array α} :
    x ∈ xs.zipIdx ↔ xs[x.2]? = some x.1 := by
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

theorem mapFinIdx_eq_ofFn {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = Array.ofFn fun i : Fin xs.size => f i xs[i] i.2 := by
  cases xs
  simp [List.mapFinIdx_eq_ofFn]

theorem mapFinIdx_append {xs ys : Array α} {f : (i : Nat) → α → (h : i < (xs ++ ys).size) → β} :
    (xs ++ ys).mapFinIdx f =
      xs.mapFinIdx (fun i a h => f i a (by simp; omega)) ++
        ys.mapFinIdx (fun i a h => f (i + xs.size) a (by simp; omega)) := by
  cases xs
  cases ys
  simp [List.mapFinIdx_append]

@[simp]
theorem mapFinIdx_push {xs : Array α} {a : α} {f : (i : Nat) → α → (h : i < (xs.push a).size) → β} :
    mapFinIdx (xs.push a) f =
      (mapFinIdx xs (fun i a h => f i a (by simp; omega))).push (f xs.size a (by simp)) := by
  simp [← append_singleton, mapFinIdx_append]

theorem mapFinIdx_singleton {a : α} {f : (i : Nat) → α → (h : i < 1) → β} :
    #[a].mapFinIdx f = #[f 0 a (by simp)] := by
  simp

theorem mapFinIdx_eq_zipIdx_map {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = xs.zipIdx.attach.map
      fun ⟨⟨x, i⟩, m⟩ =>
        f i x (by simp [mk_mem_zipIdx_iff_getElem?, getElem?_eq_some_iff] at m; exact m.1) := by
  ext <;> simp

@[deprecated mapFinIdx_eq_zipIdx_map (since := "2025-01-21")]
abbrev mapFinIdx_eq_zipWithIndex_map := @mapFinIdx_eq_zipIdx_map

@[simp]
theorem mapFinIdx_eq_empty_iff {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = #[] ↔ xs = #[] := by
  cases xs
  simp

theorem mapFinIdx_ne_empty_iff {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f ≠ #[] ↔ xs ≠ #[] := by
  simp

theorem exists_of_mem_mapFinIdx {b : β} {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β}
    (h : b ∈ xs.mapFinIdx f) : ∃ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  rcases xs with ⟨xs⟩
  exact List.exists_of_mem_mapFinIdx (by simpa using h)

@[simp] theorem mem_mapFinIdx {b : β} {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    b ∈ xs.mapFinIdx f ↔ ∃ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  rcases xs with ⟨xs⟩
  simp

theorem mapFinIdx_eq_iff {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys : Array β} :
    xs.mapFinIdx f = ys ↔ ∃ h : ys.size = xs.size, ∀ (i : Nat) (h : i < xs.size), ys[i] = f i xs[i] h := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simpa using List.mapFinIdx_eq_iff

@[simp] theorem mapFinIdx_eq_singleton_iff {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} {b : β} :
    xs.mapFinIdx f = #[b] ↔ ∃ (a : α) (w : xs = #[a]), f 0 a (by simp [w]) = b := by
  rcases xs with ⟨xs⟩
  simp

theorem mapFinIdx_eq_append_iff {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} {ys zs : Array β} :
    xs.mapFinIdx f = ys ++ zs ↔
      ∃ (ys' : Array α) (zs' : Array α) (w : xs = ys' ++ zs'),
        ys'.mapFinIdx (fun i a h => f i a (by simp [w]; omega)) = ys ∧
        zs'.mapFinIdx (fun i a h => f (i + ys'.size) a (by simp [w]; omega)) = zs := by
  rcases xs with ⟨l⟩
  rcases ys with ⟨l₁⟩
  rcases zs with ⟨l₂⟩
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

theorem mapFinIdx_eq_push_iff {xs : Array α} {b : β} {f : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = ys.push b ↔
      ∃ (zs : Array α) (a : α) (w : xs = zs.push a),
        zs.mapFinIdx (fun i a h => f i a (by simp [w]; omega)) = ys ∧ b = f (xs.size - 1) a (by simp [w]) := by
  rw [push_eq_append, mapFinIdx_eq_append_iff]
  constructor
  · rintro ⟨ys', zs', rfl, rfl, h₂⟩
    simp only [mapFinIdx_eq_singleton_iff, Nat.zero_add] at h₂
    obtain ⟨a, rfl, rfl⟩ := h₂
    exact ⟨ys', a, by simp⟩
  · rintro ⟨zs, a, rfl, rfl, rfl⟩
    exact ⟨zs, #[a], by simp⟩

theorem mapFinIdx_eq_mapFinIdx_iff {xs : Array α} {f g : (i : Nat) → α → (h : i < xs.size) → β} :
    xs.mapFinIdx f = xs.mapFinIdx g ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = g i xs[i] h := by
  rw [eq_comm, mapFinIdx_eq_iff]
  simp

@[simp] theorem mapFinIdx_mapFinIdx {xs : Array α}
    {f : (i : Nat) → α → (h : i < xs.size) → β}
    {g : (i : Nat) → β → (h : i < (xs.mapFinIdx f).size) → γ} :
    (xs.mapFinIdx f).mapFinIdx g = xs.mapFinIdx (fun i a h => g i (f i a h) (by simpa using h)) := by
  simp [mapFinIdx_eq_iff]

theorem mapFinIdx_eq_mkArray_iff {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} {b : β} :
    xs.mapFinIdx f = mkArray xs.size b ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = b := by
  rcases xs with ⟨l⟩
  rw [← toList_inj]
  simp [List.mapFinIdx_eq_replicate_iff]

@[simp] theorem mapFinIdx_reverse {xs : Array α} {f : (i : Nat) → α → (h : i < xs.reverse.size) → β} :
    xs.reverse.mapFinIdx f = (xs.mapFinIdx (fun i a h => f (xs.size - 1 - i) a (by simp; omega))).reverse := by
  rcases xs with ⟨l⟩
  simp [List.mapFinIdx_reverse]

/-! ### mapIdx -/

@[simp]
theorem mapIdx_empty {f : Nat → α → β} : mapIdx f #[] = #[] :=
  rfl

@[simp] theorem mapFinIdx_eq_mapIdx {xs : Array α} {f : (i : Nat) → α → (h : i < xs.size) → β} {g : Nat → α → β}
    (h : ∀ (i : Nat) (h : i < xs.size), f i xs[i] h = g i xs[i]) :
    xs.mapFinIdx f = xs.mapIdx g := by
  simp_all [mapFinIdx_eq_iff]

theorem mapIdx_eq_mapFinIdx {xs : Array α} {f : Nat → α → β} :
    xs.mapIdx f = xs.mapFinIdx (fun i a _ => f i a) := by
  simp [mapFinIdx_eq_mapIdx]

theorem mapIdx_eq_zipIdx_map {xs : Array α} {f : Nat → α → β} :
    xs.mapIdx f = xs.zipIdx.map fun ⟨a, i⟩ => f i a := by
  ext <;> simp

@[deprecated mapIdx_eq_zipIdx_map (since := "2025-01-21")]
abbrev mapIdx_eq_zipWithIndex_map := @mapIdx_eq_zipIdx_map

theorem mapIdx_append {xs ys : Array α} :
    (xs ++ ys).mapIdx f = xs.mapIdx f ++ ys.mapIdx (fun i => f (i + xs.size)) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp [List.mapIdx_append]

@[simp]
theorem mapIdx_push {xs : Array α} {a : α} :
    mapIdx f (xs.push a) = (mapIdx f xs).push (f xs.size a) := by
  simp [← append_singleton, mapIdx_append]

theorem mapIdx_singleton {a : α} : mapIdx f #[a] = #[f 0 a] := by
  simp

@[simp]
theorem mapIdx_eq_empty_iff {xs : Array α} : mapIdx f xs = #[] ↔ xs = #[] := by
  rcases xs with ⟨xs⟩
  simp

theorem mapIdx_ne_empty_iff {xs : Array α} :
    mapIdx f xs ≠ #[] ↔ xs ≠ #[] := by
  simp

theorem exists_of_mem_mapIdx {b : β} {xs : Array α}
    (h : b ∈ mapIdx f xs) : ∃ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
  rw [mapIdx_eq_mapFinIdx] at h
  simpa [Fin.exists_iff] using exists_of_mem_mapFinIdx h

@[simp] theorem mem_mapIdx {b : β} {xs : Array α} :
    b ∈ mapIdx f xs ↔ ∃ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
  constructor
  · intro h
    exact exists_of_mem_mapIdx h
  · rintro ⟨i, h, rfl⟩
    rw [mem_iff_getElem]
    exact ⟨i, by simpa using h, by simp⟩

theorem mapIdx_eq_push_iff {xs : Array α} {b : β} :
    mapIdx f xs = ys.push b ↔
      ∃ (a : α) (zs : Array α), xs = zs.push a ∧ mapIdx f zs = ys ∧ f zs.size a = b := by
  rw [mapIdx_eq_mapFinIdx, mapFinIdx_eq_push_iff]
  simp only [mapFinIdx_eq_mapIdx, exists_and_left, exists_prop]
  constructor
  · rintro ⟨zs, rfl, a, rfl, rfl⟩
    exact ⟨a, zs, by simp⟩
  · rintro ⟨a, zs, rfl, rfl, rfl⟩
    exact ⟨zs, rfl, a, by simp⟩

@[simp] theorem mapIdx_eq_singleton_iff {xs : Array α} {f : Nat → α → β} {b : β} :
    mapIdx f xs = #[b] ↔ ∃ (a : α), xs = #[a] ∧ f 0 a = b := by
  rcases xs with ⟨xs⟩
  simp [List.mapIdx_eq_singleton_iff]

theorem mapIdx_eq_append_iff {xs : Array α} {f : Nat → α → β} {ys zs : Array β} :
    mapIdx f xs = ys ++ zs ↔
      ∃ (xs' : Array α) (zs' : Array α), xs = xs' ++ zs' ∧
        xs'.mapIdx f = ys ∧
        zs'.mapIdx (fun i => f (i + xs'.size)) = zs := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  rcases zs with ⟨zs⟩
  simp only [List.mapIdx_toArray, List.append_toArray, mk.injEq, List.mapIdx_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₁.toArray, l₂.toArray, by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, rfl, h₁, h₂⟩
    simp only [List.mapIdx_toArray, mk.injEq, List.size_toArray] at h₁ h₂
    obtain rfl := h₁
    obtain rfl := h₂
    exact ⟨l₁, l₂, by simp⟩

theorem mapIdx_eq_iff {xs : Array α} : mapIdx f xs = ys ↔ ∀ i : Nat, ys[i]? = xs[i]?.map (f i) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp [List.mapIdx_eq_iff]

theorem mapIdx_eq_mapIdx_iff {xs : Array α} :
    mapIdx f xs = mapIdx g xs ↔ ∀ i : Nat, (h : i < xs.size) → f i xs[i] = g i xs[i] := by
  rcases xs with ⟨xs⟩
  simp [List.mapIdx_eq_mapIdx_iff]

@[simp] theorem mapIdx_set {xs : Array α} {i : Nat} {h : i < xs.size} {a : α} :
    (xs.set i a).mapIdx f = (xs.mapIdx f).set i (f i a) (by simpa) := by
  rcases xs with ⟨xs⟩
  simp [List.mapIdx_set]

@[simp] theorem mapIdx_setIfInBounds {xs : Array α} {i : Nat} {a : α} :
    (xs.setIfInBounds i a).mapIdx f = (xs.mapIdx f).setIfInBounds i (f i a) := by
  rcases xs with ⟨xs⟩
  simp [List.mapIdx_set]

@[simp] theorem back?_mapIdx {xs : Array α} {f : Nat → α → β} :
    (mapIdx f xs).back? = (xs.back?).map (f (xs.size - 1)) := by
  rcases xs with ⟨xs⟩
  simp [List.getLast?_mapIdx]

@[simp] theorem back_mapIdx {xs : Array α} {f : Nat → α → β} (h) :
    (xs.mapIdx f).back h = f (xs.size - 1) (xs.back (by simpa using h)) := by
  rcases xs with ⟨xs⟩
  simp [List.getLast_mapIdx]

@[simp] theorem mapIdx_mapIdx {xs : Array α} {f : Nat → α → β} {g : Nat → β → γ} :
    (xs.mapIdx f).mapIdx g = xs.mapIdx (fun i => g i ∘ f i) := by
  simp [mapIdx_eq_iff]

theorem mapIdx_eq_mkArray_iff {xs : Array α} {f : Nat → α → β} {b : β} :
    mapIdx f xs = mkArray xs.size b ↔ ∀ (i : Nat) (h : i < xs.size), f i xs[i] = b := by
  rcases xs with ⟨xs⟩
  rw [← toList_inj]
  simp [List.mapIdx_eq_replicate_iff]

@[simp] theorem mapIdx_reverse {xs : Array α} {f : Nat → α → β} :
    xs.reverse.mapIdx f = (mapIdx (fun i => f (xs.size - 1 - i)) xs).reverse := by
  rcases xs with ⟨xs⟩
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

theorem toList_mapFinIdxM [Monad m] [LawfulMonad m] (xs : Array α)
    (f : (i : Nat) → α → (h : i < xs.size) → m β) :
    toList <$> xs.mapFinIdxM f = xs.toList.mapFinIdxM f := by
  rw [List.mapFinIdxM_toArray]
  simp only [Functor.map_map, id_map']

theorem toList_mapIdxM [Monad m] [LawfulMonad m] (xs : Array α)
    (f : Nat → α → m β) :
    toList <$> xs.mapIdxM f = xs.toList.mapIdxM f := by
  rw [List.mapIdxM_toArray]
  simp only [Functor.map_map, id_map']

end Array
