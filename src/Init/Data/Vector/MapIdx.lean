/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.MapIdx
import Init.Data.Vector.Lemmas

namespace Vector

/-! ### mapFinIdx -/

@[simp] theorem getElem_mapFinIdx (a : Vector α n) (f : (i : Nat) → α → (h : i < n) → β) (i : Nat)
    (h : i < n) :
    (a.mapFinIdx f)[i] = f i a[i] h := by
  rcases a with ⟨a, rfl⟩
  simp

@[simp] theorem getElem?_mapFinIdx (a : Vector α n) (f : (i : Nat) → α → (h : i < n) → β) (i : Nat) :
    (a.mapFinIdx f)[i]? =
      a[i]?.pbind fun b h => f i b (getElem?_eq_some_iff.1 h).1 := by
  simp only [getElem?_def, getElem_mapFinIdx]
  split <;> simp_all

/-! ### mapIdx -/

@[simp] theorem getElem_mapIdx (f : Nat → α → β) (a : Vector α n) (i : Nat) (h : i < n) :
    (a.mapIdx f)[i] = f i (a[i]'(by simp_all)) := by
  rcases a with ⟨a, rfl⟩
  simp

@[simp] theorem getElem?_mapIdx (f : Nat → α → β) (a : Vector α n) (i : Nat) :
    (a.mapIdx f)[i]? = a[i]?.map (f i) := by
  rcases a with ⟨a, rfl⟩
  simp

end Vector

namespace Array

@[simp] theorem mapFinIdx_toVector (l : Array α) (f : (i : Nat) → α → (h : i < l.size) → β) :
    l.toVector.mapFinIdx f = (l.mapFinIdx f).toVector.cast (by simp) := by
  ext <;> simp

@[simp] theorem mapIdx_toVector (f : Nat → α → β) (l : Array α) :
    l.toVector.mapIdx f = (l.mapIdx f).toVector.cast (by simp) := by
  ext <;> simp

end Array

namespace Vector

/-! ### zipIdx -/

@[simp] theorem toList_zipIdx (a : Vector α n) (k : Nat := 0) :
    (a.zipIdx k).toList = a.toList.zipIdx k := by
  rcases a with ⟨a, rfl⟩
  simp

@[simp] theorem getElem_zipIdx (a : Vector α n) (i : Nat) (h : i < n) :
    (a.zipIdx k)[i] = (a[i]'(by simp_all), k + i) := by
  rcases a with ⟨a, rfl⟩
  simp

@[simp] theorem zipIdx_toVector {l : Array α} {k : Nat} :
    l.toVector.zipIdx k = (l.zipIdx k).toVector.cast (by simp) := by
  ext <;> simp

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {x : α} {i : Nat} {l : Vector α n} {k : Nat} :
    (x, i) ∈ l.zipIdx k ↔ k ≤ i ∧ l[i - k]? = x := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mk_mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mk_mem_zipIdx_iff_getElem? {x : α} {i : Nat} {l : Vector α n} :
    (x, i) ∈ l.zipIdx ↔ l[i]? = x := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mk_mem_zipIdx_iff_le_and_getElem?_sub]

theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {l : Vector α n} {k : Nat} :
    x ∈ zipIdx l k ↔ k ≤ x.2 ∧ l[x.2 - k]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mem_zipIdx_iff_getElem? {x : α × Nat} {l : Vector α n} :
    x ∈ l.zipIdx ↔ l[x.2]? = some x.1 := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mem_zipIdx_iff_getElem?]

@[deprecated toList_zipIdx (since := "2025-01-27")]
abbrev toList_zipWithIndex := @toList_zipIdx
@[deprecated getElem_zipIdx (since := "2025-01-27")]
abbrev getElem_zipWithIndex := @getElem_zipIdx
@[deprecated zipIdx_toVector (since := "2025-01-27")]
abbrev zipWithIndex_toVector := @zipIdx_toVector
@[deprecated mk_mem_zipIdx_iff_le_and_getElem?_sub (since := "2025-01-27")]
abbrev mk_mem_zipWithIndex_iff_le_and_getElem?_sub := @mk_mem_zipIdx_iff_le_and_getElem?_sub
@[deprecated mk_mem_zipIdx_iff_getElem? (since := "2025-01-27")]
abbrev mk_mem_zipWithIndex_iff_getElem? := @mk_mem_zipIdx_iff_getElem?
@[deprecated mem_zipIdx_iff_le_and_getElem?_sub (since := "2025-01-27")]
abbrev mem_zipWithIndex_iff_le_and_getElem?_sub := @mem_zipIdx_iff_le_and_getElem?_sub
@[deprecated mem_zipIdx_iff_getElem? (since := "2025-01-27")]
abbrev mem_zipWithIndex_iff_getElem? := @mem_zipIdx_iff_getElem?

/-! ### mapFinIdx -/

@[congr] theorem mapFinIdx_congr {xs ys : Vector α n} (w : xs = ys)
    (f : (i : Nat) → α → (h : i < n) → β) :
    mapFinIdx xs f = mapFinIdx ys f := by
  subst w
  rfl

@[simp]
theorem mapFinIdx_empty {f : (i : Nat) → α → (h : i < 0) → β} : mapFinIdx #v[] f = #v[] :=
  rfl

theorem mapFinIdx_eq_ofFn {as : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    as.mapFinIdx f = Vector.ofFn fun i : Fin n => f i as[i] i.2 := by
  rcases as with ⟨as, rfl⟩
  simp [Array.mapFinIdx_eq_ofFn]

theorem mapFinIdx_append {K : Vector α n} {L : Vector α m} {f : (i : Nat) → α → (h : i < n + m) → β} :
    (K ++ L).mapFinIdx f =
      K.mapFinIdx (fun i a h => f i a (by omega)) ++
        L.mapFinIdx (fun i a h => f (i + n) a (by omega)) := by
  rcases K with ⟨K, rfl⟩
  rcases L with ⟨L, rfl⟩
  simp [Array.mapFinIdx_append]

@[simp]
theorem mapFinIdx_push {l : Vector α n} {a : α} {f : (i : Nat) → α → (h : i < n + 1) → β} :
    mapFinIdx (l.push a) f =
      (mapFinIdx l (fun i a h => f i a (by omega))).push (f l.size a (by simp)) := by
  simp [← append_singleton, mapFinIdx_append]

theorem mapFinIdx_singleton {a : α} {f : (i : Nat) → α → (h : i < 1) → β} :
    #v[a].mapFinIdx f = #v[f 0 a (by simp)] := by
  simp

-- FIXME this lemma can't be stated until we've aligned `List/Array/Vector.attach`:
-- theorem mapFinIdx_eq_zipWithIndex_map {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
--     l.mapFinIdx f = l.zipWithIndex.attach.map
--       fun ⟨⟨x, i⟩, m⟩ =>
--         f i x (by simp [mk_mem_zipWithIndex_iff_getElem?, getElem?_eq_some_iff] at m; exact m.1) := by
--   ext <;> simp

theorem exists_of_mem_mapFinIdx {b : β} {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β}
    (h : b ∈ l.mapFinIdx f) : ∃ (i : Nat) (h : i < n), f i l[i] h = b := by
  rcases l with ⟨l, rfl⟩
  exact List.exists_of_mem_mapFinIdx (by simpa using h)

@[simp] theorem mem_mapFinIdx {b : β} {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    b ∈ l.mapFinIdx f ↔ ∃ (i : Nat) (h : i < n), f i l[i] h = b := by
  rcases l with ⟨l, rfl⟩
  simp

theorem mapFinIdx_eq_iff {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    l.mapFinIdx f = l' ↔ ∀ (i : Nat) (h : i < n), l'[i] = f i l[i] h := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [mapFinIdx_mk, eq_mk, getElem_mk, Array.mapFinIdx_eq_iff, h]

@[simp] theorem mapFinIdx_eq_singleton_iff {l : Vector α 1} {f : (i : Nat) → α → (h : i < 1) → β} {b : β} :
    l.mapFinIdx f = #v[b] ↔ ∃ (a : α), l = #v[a] ∧ f 0 a (by omega) = b := by
  rcases l with ⟨l, h⟩
  simp only [mapFinIdx_mk, eq_mk, Array.mapFinIdx_eq_singleton_iff]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, by simp⟩

theorem mapFinIdx_eq_append_iff {l : Vector α (n + m)} {f : (i : Nat) → α → (h : i < n + m) → β}
    {l₁ : Vector β n} {l₂ : Vector β m} :
    l.mapFinIdx f = l₁ ++ l₂ ↔
      ∃ (l₁' : Vector α n) (l₂' : Vector α m), l = l₁' ++ l₂' ∧
        l₁'.mapFinIdx (fun i a h => f i a (by omega)) = l₁ ∧
        l₂'.mapFinIdx (fun i a h => f (i + n) a (by omega)) = l₂ := by
  rcases l with ⟨l, h⟩
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, rfl⟩
  simp only [mapFinIdx_mk, mk_append_mk, eq_mk, Array.mapFinIdx_eq_append_iff, toArray_mapFinIdx,
    mk_eq, toArray_append, exists_and_left, exists_prop]
  constructor
  · rintro ⟨l₁', l₂', rfl, h₁, h₂⟩
    have h₁' := congrArg Array.size h₁
    have h₂' := congrArg Array.size h₂
    simp only [Array.size_mapFinIdx] at h₁' h₂'
    exact ⟨⟨l₁', h₁'⟩, ⟨l₂', h₂'⟩, by simp_all⟩
  · rintro ⟨⟨l₁, s₁⟩, ⟨l₂, s₂⟩, rfl, h₁, h₂⟩
    refine ⟨l₁, l₂, by simp_all⟩

theorem mapFinIdx_eq_push_iff {l : Vector α (n + 1)} {b : β} {f : (i : Nat) → α → (h : i < n + 1) → β} {l₂ : Vector β n} :
    l.mapFinIdx f = l₂.push b ↔
      ∃ (l₁ : Vector α n) (a : α), l = l₁.push a ∧
        l₁.mapFinIdx (fun i a h => f i a (by omega)) = l₂ ∧ b = f n a (by omega) := by
  rcases l with ⟨l, h⟩
  rcases l₂ with ⟨l₂, rfl⟩
  simp only [mapFinIdx_mk, push_mk, eq_mk, Array.mapFinIdx_eq_push_iff, mk_eq, toArray_push,
    toArray_mapFinIdx]
  constructor
  · rintro ⟨l₁, a, rfl, h₁, rfl⟩
    simp only [Array.size_push, Nat.add_right_cancel_iff] at h
    exact ⟨⟨l₁, h⟩, a, by simp_all⟩
  · rintro ⟨⟨l₁, h⟩, a, rfl, h₁, rfl⟩
    exact ⟨l₁, a, by simp_all⟩

theorem mapFinIdx_eq_mapFinIdx_iff {l : Vector α n} {f g : (i : Nat) → α → (h : i < n) → β} :
    l.mapFinIdx f = l.mapFinIdx g ↔ ∀ (i : Nat) (h : i < n), f i l[i] h = g i l[i] h := by
  rw [eq_comm, mapFinIdx_eq_iff]
  simp

@[simp] theorem mapFinIdx_mapFinIdx {l : Vector α n}
    {f : (i : Nat) → α → (h : i < n) → β}
    {g : (i : Nat) → β → (h : i < n) → γ} :
    (l.mapFinIdx f).mapFinIdx g = l.mapFinIdx (fun i a h => g i (f i a h) h) := by
  simp [mapFinIdx_eq_iff]

theorem mapFinIdx_eq_mkVector_iff {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} {b : β} :
    l.mapFinIdx f = mkVector n b ↔ ∀ (i : Nat) (h : i < n), f i l[i] h = b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mapFinIdx_eq_mkArray_iff]

@[simp] theorem mapFinIdx_reverse {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    l.reverse.mapFinIdx f = (l.mapFinIdx (fun i a h => f (n - 1 - i) a (by omega))).reverse := by
  rcases l with ⟨l, rfl⟩
  simp

/-! ### mapIdx -/

@[simp]
theorem mapIdx_empty {f : Nat → α → β} : mapIdx f #v[] = #v[] :=
  rfl

@[simp] theorem mapFinIdx_eq_mapIdx {l : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} {g : Nat → α → β}
    (h : ∀ (i : Nat) (h : i < n), f i l[i] h = g i l[i]) :
    l.mapFinIdx f = l.mapIdx g := by
  simp_all [mapFinIdx_eq_iff]

theorem mapIdx_eq_mapFinIdx {l : Vector α n} {f : Nat → α → β} :
    l.mapIdx f = l.mapFinIdx (fun i a _ => f i a) := by
  simp [mapFinIdx_eq_mapIdx]

theorem mapIdx_eq_zipIdx_map {l : Vector α n} {f : Nat → α → β} :
    l.mapIdx f = l.zipIdx.map fun ⟨a, i⟩ => f i a := by
  ext <;> simp

@[deprecated mapIdx_eq_zipIdx_map (since := "2025-01-27")]
abbrev mapIdx_eq_zipWithIndex_map := @mapIdx_eq_zipIdx_map

theorem mapIdx_append {K : Vector α n} {L : Vector α m} :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i => f (i + K.size) := by
  rcases K with ⟨K, rfl⟩
  rcases L with ⟨L, rfl⟩
  simp [Array.mapIdx_append]

@[simp]
theorem mapIdx_push {l : Vector α n} {a : α} :
    mapIdx f (l.push a) = (mapIdx f l).push (f l.size a) := by
  simp [← append_singleton, mapIdx_append]

theorem mapIdx_singleton {a : α} : mapIdx f #v[a] = #v[f 0 a] := by
  simp

theorem exists_of_mem_mapIdx {b : β} {l : Vector α n}
    (h : b ∈ l.mapIdx f) : ∃ (i : Nat) (h : i < n), f i l[i] = b := by
  rw [mapIdx_eq_mapFinIdx] at h
  simpa [Fin.exists_iff] using exists_of_mem_mapFinIdx h

@[simp] theorem mem_mapIdx {b : β} {l : Vector α n} :
    b ∈ l.mapIdx f ↔ ∃ (i : Nat) (h : i < n), f i l[i] = b := by
  constructor
  · intro h
    exact exists_of_mem_mapIdx h
  · rintro ⟨i, h, rfl⟩
    rw [mem_iff_getElem]
    exact ⟨i, by simpa using h, by simp⟩

theorem mapIdx_eq_push_iff {l : Vector α (n + 1)} {b : β} :
    mapIdx f l = l₂.push b ↔
      ∃ (a : α) (l₁ : Vector α n), l = l₁.push a ∧ mapIdx f l₁ = l₂ ∧ f l₁.size a = b := by
  rw [mapIdx_eq_mapFinIdx, mapFinIdx_eq_push_iff]
  simp only [mapFinIdx_eq_mapIdx, exists_and_left, exists_prop]
  constructor
  · rintro ⟨l₁, a, rfl, rfl, rfl⟩
    exact ⟨a, l₁, by simp⟩
  · rintro ⟨a, l₁, rfl, rfl, rfl⟩
    exact ⟨l₁, a, rfl, by simp⟩

@[simp] theorem mapIdx_eq_singleton_iff {l : Vector α 1} {f : Nat → α → β} {b : β} :
    mapIdx f l = #v[b] ↔ ∃ (a : α), l = #v[a] ∧ f 0 a = b := by
  rcases l with ⟨l⟩
  simp

theorem mapIdx_eq_append_iff {l : Vector α (n + m)} {f : Nat → α → β} {l₁ : Vector β n} {l₂ : Vector β m} :
    mapIdx f l = l₁ ++ l₂ ↔
      ∃ (l₁' : Vector α n) (l₂' : Vector α m), l = l₁' ++ l₂' ∧
        l₁'.mapIdx f = l₁ ∧
        l₂'.mapIdx (fun i => f (i + l₁'.size)) = l₂ := by
  rcases l with ⟨l, h⟩
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, rfl⟩
  rw [mapIdx_eq_mapFinIdx, mapFinIdx_eq_append_iff]
  simp

theorem mapIdx_eq_iff {l : Vector α n} :
    mapIdx f l = l' ↔ ∀ (i : Nat) (h : i < n), f i l[i] = l'[i] := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp only [mapIdx_mk, eq_mk, Array.mapIdx_eq_iff, getElem_mk]
  constructor
  · rintro h' i h
    specialize h' i
    simp_all
  · intro h' i
    specialize h' i
    by_cases w : i < l.size
    · specialize h' w
      simp_all
    · simp only [Nat.not_lt] at w
      simp_all [Array.getElem?_eq_none_iff.mpr w]

theorem mapIdx_eq_mapIdx_iff {l : Vector α n} :
    mapIdx f l = mapIdx g l ↔ ∀ (i : Nat) (h : i < n), f i l[i] = g i l[i] := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mapIdx_eq_mapIdx_iff]

@[simp] theorem mapIdx_set {l : Vector α n} {i : Nat} {h : i < n} {a : α} :
    (l.set i a).mapIdx f = (l.mapIdx f).set i (f i a) (by simpa) := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem mapIdx_setIfInBounds {l : Vector α n} {i : Nat} {a : α} :
    (l.setIfInBounds i a).mapIdx f = (l.mapIdx f).setIfInBounds i (f i a) := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem back?_mapIdx {l : Vector α n} {f : Nat → α → β} :
    (mapIdx f l).back? = (l.back?).map (f (l.size - 1)) := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem back_mapIdx [NeZero n] {l : Vector α n} {f : Nat → α → β} :
    (mapIdx f l).back = f (l.size - 1) (l.back) := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem mapIdx_mapIdx {l : Vector α n} {f : Nat → α → β} {g : Nat → β → γ} :
    (l.mapIdx f).mapIdx g = l.mapIdx (fun i => g i ∘ f i) := by
  simp [mapIdx_eq_iff]

theorem mapIdx_eq_mkVector_iff {l : Vector α n} {f : Nat → α → β} {b : β} :
    mapIdx f l = mkVector n b ↔ ∀ (i : Nat) (h : i < n), f i l[i] = b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mapIdx_eq_mkArray_iff]

@[simp] theorem mapIdx_reverse {l : Vector α n} {f : Nat → α → β} :
    l.reverse.mapIdx f = (mapIdx (fun i => f (l.size - 1 - i)) l).reverse := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mapIdx_reverse]

end Vector
