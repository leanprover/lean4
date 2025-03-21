/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.MapIdx
import Init.Data.Vector.Attach
import Init.Data.Vector.Lemmas

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

/-! ### mapFinIdx -/

@[simp] theorem getElem_mapFinIdx (xs : Vector α n) (f : (i : Nat) → α → (h : i < n) → β) (i : Nat)
    (h : i < n) :
    (xs.mapFinIdx f)[i] = f i xs[i] h := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem getElem?_mapFinIdx (xs : Vector α n) (f : (i : Nat) → α → (h : i < n) → β) (i : Nat) :
    (xs.mapFinIdx f)[i]? =
      xs[i]?.pbind fun b h => f i b (getElem?_eq_some_iff.1 h).1 := by
  simp only [getElem?_def, getElem_mapFinIdx]
  split <;> simp_all

/-! ### mapIdx -/

@[simp] theorem getElem_mapIdx (f : Nat → α → β) (xs : Vector α n) (i : Nat) (h : i < n) :
    (xs.mapIdx f)[i] = f i (xs[i]'(by simp_all)) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem getElem?_mapIdx (f : Nat → α → β) (xs : Vector α n) (i : Nat) :
    (xs.mapIdx f)[i]? = xs[i]?.map (f i) := by
  rcases xs with ⟨xs, rfl⟩
  simp

end Vector

namespace Array

@[simp] theorem mapFinIdx_toVector (xs : Array α) (f : (i : Nat) → α → (h : i < xs.size) → β) :
    xs.toVector.mapFinIdx f = (xs.mapFinIdx f).toVector.cast (by simp) := by
  ext <;> simp

@[simp] theorem mapIdx_toVector (f : Nat → α → β) (xs : Array α) :
    xs.toVector.mapIdx f = (xs.mapIdx f).toVector.cast (by simp) := by
  ext <;> simp

end Array

namespace Vector

/-! ### zipIdx -/

@[simp] theorem toList_zipIdx (xs : Vector α n) (k : Nat := 0) :
    (xs.zipIdx k).toList = xs.toList.zipIdx k := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem getElem_zipIdx (xs : Vector α n) (i : Nat) (h : i < n) :
    (xs.zipIdx k)[i] = (xs[i]'(by simp_all), k + i) := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {x : α} {i : Nat} {xs : Vector α n} {k : Nat} :
    (x, i) ∈ xs.zipIdx k ↔ k ≤ i ∧ xs[i - k]? = x := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mk_mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mk_mem_zipIdx_iff_getElem? {x : α} {i : Nat} {xs : Vector α n} :
    (x, i) ∈ xs.zipIdx ↔ xs[i]? = x := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mk_mem_zipIdx_iff_le_and_getElem?_sub]

theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {xs : Vector α n} {k : Nat} :
    x ∈ xs.zipIdx k ↔ k ≤ x.2 ∧ xs[x.2 - k]? = some x.1 := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mem_zipIdx_iff_getElem? {x : α × Nat} {xs : Vector α n} :
    x ∈ xs.zipIdx ↔ xs[x.2]? = some x.1 := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mem_zipIdx_iff_getElem?]

@[deprecated toList_zipIdx (since := "2025-01-27")]
abbrev toList_zipWithIndex := @toList_zipIdx
@[deprecated getElem_zipIdx (since := "2025-01-27")]
abbrev getElem_zipWithIndex := @getElem_zipIdx
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

theorem mapFinIdx_append {xs : Vector α n} {ys : Vector α m} {f : (i : Nat) → α → (h : i < n + m) → β} :
    (xs ++ ys).mapFinIdx f =
      xs.mapFinIdx (fun i a h => f i a (by omega)) ++
        ys.mapFinIdx (fun i a h => f (i + n) a (by omega)) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.mapFinIdx_append]

@[simp]
theorem mapFinIdx_push {xs : Vector α n} {a : α} {f : (i : Nat) → α → (h : i < n + 1) → β} :
    mapFinIdx (xs.push a) f =
      (mapFinIdx xs (fun i a h => f i a (by omega))).push (f xs.size a (by simp)) := by
  simp [← append_singleton, mapFinIdx_append]

theorem mapFinIdx_singleton {a : α} {f : (i : Nat) → α → (h : i < 1) → β} :
    #v[a].mapFinIdx f = #v[f 0 a (by simp)] := by
  simp

theorem mapFinIdx_eq_zipIdx_map {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    xs.mapFinIdx f = xs.zipIdx.attach.map
      fun ⟨⟨x, i⟩, m⟩ =>
        f i x (by rw [mk_mem_zipIdx_iff_getElem?, getElem?_eq_some_iff] at m; exact m.1) := by
  ext <;> simp

theorem exists_of_mem_mapFinIdx {b : β} {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β}
    (h : b ∈ xs.mapFinIdx f) : ∃ (i : Nat) (h : i < n), f i xs[i] h = b := by
  rcases xs with ⟨xs, rfl⟩
  exact List.exists_of_mem_mapFinIdx (by simpa using h)

@[simp] theorem mem_mapFinIdx {b : β} {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    b ∈ xs.mapFinIdx f ↔ ∃ (i : Nat) (h : i < n), f i xs[i] h = b := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem mapFinIdx_eq_iff {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    xs.mapFinIdx f = xs' ↔ ∀ (i : Nat) (h : i < n), xs'[i] = f i xs[i] h := by
  rcases xs with ⟨xs, rfl⟩
  rcases xs' with ⟨xs', h⟩
  simp [mapFinIdx_mk, eq_mk, getElem_mk, Array.mapFinIdx_eq_iff, h]

@[simp] theorem mapFinIdx_eq_singleton_iff {xs : Vector α 1} {f : (i : Nat) → α → (h : i < 1) → β} {b : β} :
    xs.mapFinIdx f = #v[b] ↔ ∃ (a : α), xs = #v[a] ∧ f 0 a (by omega) = b := by
  rcases xs with ⟨xs, h⟩
  simp only [mapFinIdx_mk, eq_mk, Array.mapFinIdx_eq_singleton_iff]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, by simp⟩

theorem mapFinIdx_eq_append_iff {xs : Vector α (n + m)} {f : (i : Nat) → α → (h : i < n + m) → β}
    {ys : Vector β n} {zs : Vector β m} :
    xs.mapFinIdx f = ys ++ zs ↔
      ∃ (ys' : Vector α n) (zs' : Vector α m), xs = ys' ++ zs' ∧
        ys'.mapFinIdx (fun i a h => f i a (by omega)) = ys ∧
        zs'.mapFinIdx (fun i a h => f (i + n) a (by omega)) = zs := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  rcases zs with ⟨zs, rfl⟩
  simp only [mapFinIdx_mk, mk_append_mk, eq_mk, Array.mapFinIdx_eq_append_iff, toArray_mapFinIdx,
    mk_eq, toArray_append, exists_and_left, exists_prop]
  constructor
  · rintro ⟨ys', zs', rfl, h₁, h₂⟩
    have h₁' := congrArg Array.size h₁
    have h₂' := congrArg Array.size h₂
    simp only [Array.size_mapFinIdx] at h₁' h₂'
    exact ⟨⟨ys', h₁'⟩, ⟨zs', h₂'⟩, by simp_all⟩
  · rintro ⟨⟨ys', s₁⟩, ⟨zs', s₂⟩, rfl, h₁, h₂⟩
    refine ⟨ys', zs', by simp_all⟩

theorem mapFinIdx_eq_push_iff {xs : Vector α (n + 1)} {b : β} {f : (i : Nat) → α → (h : i < n + 1) → β} {ys : Vector β n} :
    xs.mapFinIdx f = ys.push b ↔
      ∃ (zs : Vector α n) (a : α), xs = zs.push a ∧
        zs.mapFinIdx (fun i a h => f i a (by omega)) = ys ∧ b = f n a (by omega) := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mapFinIdx_mk, push_mk, eq_mk, Array.mapFinIdx_eq_push_iff, mk_eq, toArray_push,
    toArray_mapFinIdx]
  constructor
  · rintro ⟨zs, a, rfl, h₁, rfl⟩
    simp only [Array.size_push, Nat.add_right_cancel_iff] at h
    exact ⟨⟨zs, h⟩, a, by simp_all⟩
  · rintro ⟨⟨zs, h⟩, a, rfl, h₁, rfl⟩
    exact ⟨zs, a, by simp_all⟩

theorem mapFinIdx_eq_mapFinIdx_iff {xs : Vector α n} {f g : (i : Nat) → α → (h : i < n) → β} :
    xs.mapFinIdx f = xs.mapFinIdx g ↔ ∀ (i : Nat) (h : i < n), f i xs[i] h = g i xs[i] h := by
  rw [eq_comm, mapFinIdx_eq_iff]
  simp

@[simp] theorem mapFinIdx_mapFinIdx {xs : Vector α n}
    {f : (i : Nat) → α → (h : i < n) → β}
    {g : (i : Nat) → β → (h : i < n) → γ} :
    (xs.mapFinIdx f).mapFinIdx g = xs.mapFinIdx (fun i a h => g i (f i a h) h) := by
  simp [mapFinIdx_eq_iff]

theorem mapFinIdx_eq_mkVector_iff {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} {b : β} :
    xs.mapFinIdx f = mkVector n b ↔ ∀ (i : Nat) (h : i < n), f i xs[i] h = b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mapFinIdx_eq_mkArray_iff]

@[simp] theorem mapFinIdx_reverse {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} :
    xs.reverse.mapFinIdx f = (xs.mapFinIdx (fun i a h => f (n - 1 - i) a (by omega))).reverse := by
  rcases xs with ⟨xs, rfl⟩
  simp

/-! ### mapIdx -/

@[simp]
theorem mapIdx_empty {f : Nat → α → β} : mapIdx f #v[] = #v[] :=
  rfl

@[simp] theorem mapFinIdx_eq_mapIdx {xs : Vector α n} {f : (i : Nat) → α → (h : i < n) → β} {g : Nat → α → β}
    (h : ∀ (i : Nat) (h : i < n), f i xs[i] h = g i xs[i]) :
    xs.mapFinIdx f = xs.mapIdx g := by
  simp_all [mapFinIdx_eq_iff]

theorem mapIdx_eq_mapFinIdx {xs : Vector α n} {f : Nat → α → β} :
    xs.mapIdx f = xs.mapFinIdx (fun i a _ => f i a) := by
  simp [mapFinIdx_eq_mapIdx]

theorem mapIdx_eq_zipIdx_map {xs : Vector α n} {f : Nat → α → β} :
    xs.mapIdx f = xs.zipIdx.map fun ⟨a, i⟩ => f i a := by
  ext <;> simp

@[deprecated mapIdx_eq_zipIdx_map (since := "2025-01-27")]
abbrev mapIdx_eq_zipWithIndex_map := @mapIdx_eq_zipIdx_map

theorem mapIdx_append {xs : Vector α n} {ys : Vector α m} :
    (xs ++ ys).mapIdx f = xs.mapIdx f ++ ys.mapIdx fun i => f (i + xs.size) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.mapIdx_append]

@[simp]
theorem mapIdx_push {xs : Vector α n} {a : α} :
    mapIdx f (xs.push a) = (mapIdx f xs).push (f xs.size a) := by
  simp [← append_singleton, mapIdx_append]

theorem mapIdx_singleton {a : α} : mapIdx f #v[a] = #v[f 0 a] := by
  simp

theorem exists_of_mem_mapIdx {b : β} {xs : Vector α n}
    (h : b ∈ xs.mapIdx f) : ∃ (i : Nat) (h : i < n), f i xs[i] = b := by
  rw [mapIdx_eq_mapFinIdx] at h
  simpa [Fin.exists_iff] using exists_of_mem_mapFinIdx h

@[simp] theorem mem_mapIdx {b : β} {xs : Vector α n} :
    b ∈ xs.mapIdx f ↔ ∃ (i : Nat) (h : i < n), f i xs[i] = b := by
  constructor
  · intro h
    exact exists_of_mem_mapIdx h
  · rintro ⟨i, h, rfl⟩
    rw [mem_iff_getElem]
    exact ⟨i, by simpa using h, by simp⟩

theorem mapIdx_eq_push_iff {xs : Vector α (n + 1)} {b : β} :
    mapIdx f xs = ys.push b ↔
      ∃ (a : α) (zs : Vector α n), xs = zs.push a ∧ mapIdx f zs = ys ∧ f zs.size a = b := by
  rw [mapIdx_eq_mapFinIdx, mapFinIdx_eq_push_iff]
  simp only [mapFinIdx_eq_mapIdx, exists_and_left, exists_prop]
  constructor
  · rintro ⟨zs, a, rfl, rfl, rfl⟩
    exact ⟨a, zs, by simp⟩
  · rintro ⟨a, zs, rfl, rfl, rfl⟩
    exact ⟨zs, a, rfl, by simp⟩

@[simp] theorem mapIdx_eq_singleton_iff {xs : Vector α 1} {f : Nat → α → β} {b : β} :
    mapIdx f xs = #v[b] ↔ ∃ (a : α), xs = #v[a] ∧ f 0 a = b := by
  rcases xs with ⟨xs⟩
  simp

theorem mapIdx_eq_append_iff {xs : Vector α (n + m)} {f : Nat → α → β} {ys : Vector β n} {zs : Vector β m} :
    mapIdx f xs = ys ++ zs ↔
      ∃ (ys' : Vector α n) (zs' : Vector α m), xs = ys' ++ zs' ∧
        ys'.mapIdx f = ys ∧
        zs'.mapIdx (fun i => f (i + ys'.size)) = zs := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  rcases zs with ⟨zs, rfl⟩
  rw [mapIdx_eq_mapFinIdx, mapFinIdx_eq_append_iff]
  simp

theorem mapIdx_eq_iff {xs : Vector α n} {f : Nat → α → β} {ys : Vector β n} :
    mapIdx f xs = ys ↔ ∀ (i : Nat) (h : i < n), f i xs[i] = ys[i] := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  simp only [mapIdx_mk, eq_mk, Array.mapIdx_eq_iff, getElem_mk]
  constructor
  · rintro h' i h
    specialize h' i
    simp_all
  · intro h' i
    specialize h' i
    by_cases w : i < xs.size
    · specialize h' w
      simp_all
    · simp only [Nat.not_lt] at w
      simp_all [Array.getElem?_eq_none_iff.mpr w]

theorem mapIdx_eq_mapIdx_iff {xs : Vector α n} :
    mapIdx f xs = mapIdx g xs ↔ ∀ (i : Nat) (h : i < n), f i xs[i] = g i xs[i] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mapIdx_eq_mapIdx_iff]

@[simp] theorem mapIdx_set {xs : Vector α n} {i : Nat} {h : i < n} {a : α} :
    (xs.set i a).mapIdx f = (xs.mapIdx f).set i (f i a) (by simpa) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem mapIdx_setIfInBounds {xs : Vector α n} {i : Nat} {a : α} :
    (xs.setIfInBounds i a).mapIdx f = (xs.mapIdx f).setIfInBounds i (f i a) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem back?_mapIdx {xs : Vector α n} {f : Nat → α → β} :
    (mapIdx f xs).back? = (xs.back?).map (f (xs.size - 1)) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem back_mapIdx [NeZero n] {xs : Vector α n} {f : Nat → α → β} :
    (mapIdx f xs).back = f (xs.size - 1) (xs.back) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem mapIdx_mapIdx {xs : Vector α n} {f : Nat → α → β} {g : Nat → β → γ} :
    (xs.mapIdx f).mapIdx g = xs.mapIdx (fun i => g i ∘ f i) := by
  simp [mapIdx_eq_iff]

theorem mapIdx_eq_mkVector_iff {xs : Vector α n} {f : Nat → α → β} {b : β} :
    mapIdx f xs = mkVector n b ↔ ∀ (i : Nat) (h : i < n), f i xs[i] = b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mapIdx_eq_mkArray_iff]

@[simp] theorem mapIdx_reverse {xs : Vector α n} {f : Nat → α → β} :
    xs.reverse.mapIdx f = (mapIdx (fun i => f (xs.size - 1 - i)) xs).reverse := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.mapIdx_reverse]

theorem toArray_mapFinIdxM [Monad m] [LawfulMonad m]
    (xs : Vector α n) (f : (i : Nat) → α → (h : i < n) → m β) :
    toArray <$> xs.mapFinIdxM f = xs.toArray.mapFinIdxM
      (fun i x h => f i x (size_toArray xs ▸ h)) := by
  let rec go (i j : Nat) (inv : i + j = n) (bs : Vector β (n - i)) :
      toArray <$> mapFinIdxM.map xs f i j inv bs
      = Array.mapFinIdxM.map xs.toArray (fun i x h => f i x (size_toArray xs ▸ h))
        i j (size_toArray _ ▸ inv) bs.toArray := by
    match i with
    | 0 => simp only [mapFinIdxM.map, map_pure, Array.mapFinIdxM.map, Nat.sub_zero]
    | k + 1 =>
      simp only [mapFinIdxM.map, map_bind, Array.mapFinIdxM.map, getElem_toArray]
      conv => lhs; arg 2; intro; rw [go]
      rfl
  simp only [mapFinIdxM, Array.mapFinIdxM, size_toArray]
  exact go _ _ _ _

theorem toArray_mapIdxM [Monad m] [LawfulMonad m] (xs : Vector α n) (f : Nat → α → m β) :
    toArray <$> xs.mapIdxM f = xs.toArray.mapIdxM f := by
  exact toArray_mapFinIdxM _ _

end Vector
