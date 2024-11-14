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
theorem mapFinIdx_induction (as : Array α) (f : Fin as.size → α → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → p i (f i as[i]) ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (Array.mapFinIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapFinIdx as f)[i]) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p ⟨i, h⟩ bs[i]) (hm : motive j) :
    let arr : Array β := Array.mapFinIdxM.map (m := Id) as f i j h bs
    motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ arr[i] := by
    induction i generalizing j bs with simp [mapFinIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      apply @ih (bs.push (f ⟨j, by omega⟩ as[j])) (j + 1) (by omega) (by simp; omega)
      · intro i i_lt h'
        rw [getElem_push]
        split
        · apply h₂
        · simp only [size_push] at h'
          obtain rfl : i = j := by omega
          apply (hs ⟨i, by omega⟩ hm).1
      · exact (hs ⟨j, by omega⟩ hm).2
  simp [mapFinIdx, mapFinIdxM]; exact go rfl nofun h0

theorem mapFinIdx_spec (as : Array α) (f : Fin as.size → α → β)
    (p : Fin as.size → β → Prop) (hs : ∀ i, p i (f i as[i])) :
    ∃ eq : (Array.mapFinIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapFinIdx as f)[i]) :=
  (mapFinIdx_induction _ _ (fun _ => True) trivial p fun _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapFinIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapFinIdx f).size = a.size :=
  (mapFinIdx_spec (p := fun _ _ => True) (hs := fun _ => trivial)).1

@[simp] theorem size_zipWithIndex (as : Array α) : as.zipWithIndex.size = as.size :=
  Array.size_mapFinIdx _ _

@[simp] theorem getElem_mapFinIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat)
    (h : i < (mapFinIdx a f).size) :
    (a.mapFinIdx f)[i] = f ⟨i, by simp_all⟩ (a[i]'(by simp_all)) :=
  (mapFinIdx_spec _ _ (fun i b => b = f i a[i]) fun _ => rfl).2 i _

@[simp] theorem getElem?_mapFinIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat) :
    (a.mapFinIdx f)[i]? =
      a[i]?.pbind fun b h => f ⟨i, (getElem?_eq_some_iff.1 h).1⟩ b := by
  simp only [getElem?_def, size_mapFinIdx, getElem_mapFinIdx]
  split <;> simp_all

@[simp] theorem toList_mapFinIdx (a : Array α) (f : Fin a.size → α → β) :
    (a.mapFinIdx f).toList = a.toList.mapFinIdx (fun i a => f ⟨i, by simp⟩ a) := by
  apply List.ext_getElem <;> simp

/-! ### mapIdx -/

theorem mapIdx_induction (f : Nat → α → β) (as : Array α)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → p i (f i as[i]) ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (as.mapIdx f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((as.mapIdx f)[i]) :=
  mapFinIdx_induction as (fun i a => f i a) motive h0 p hs

theorem mapIdx_spec (f : Nat → α → β) (as : Array α)
    (p : Fin as.size → β → Prop) (hs : ∀ i, p i (f i as[i])) :
    ∃ eq : (as.mapIdx f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((as.mapIdx f)[i]) :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (f : Nat → α → β) (as : Array α) : (as.mapIdx f).size = as.size :=
  (mapIdx_spec (p := fun _ _ => True) (hs := fun _ => trivial)).1

@[simp] theorem getElem_mapIdx (f : Nat → α → β) (as : Array α) (i : Nat)
    (h : i < (as.mapIdx f).size) :
    (as.mapIdx f)[i] = f i (as[i]'(by simp_all)) :=
  (mapIdx_spec _ _ (fun i b => b = f i as[i]) fun _ => rfl).2 i (by simp_all)

@[simp] theorem getElem?_mapIdx (f : Nat → α → β) (as : Array α) (i : Nat) :
    (as.mapIdx f)[i]? =
      as[i]?.map (f i) := by
  simp [getElem?_def, size_mapIdx, getElem_mapIdx]

@[simp] theorem toList_mapIdx (f : Nat → α → β) (as : Array α) :
    (as.mapIdx f).toList = as.toList.mapIdx (fun i a => f i a) := by
  apply List.ext_getElem <;> simp

end Array

namespace List

@[simp] theorem mapFinIdx_toArray (l : List α) (f : Fin l.length → α → β) :
    l.toArray.mapFinIdx f = (l.mapFinIdx f).toArray := by
  ext <;> simp

@[simp] theorem mapIdx_toArray (f : Nat → α → β) (l : List α) :
    l.toArray.mapIdx f = (l.mapIdx f).toArray := by
  ext <;> simp

end List
