/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
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
