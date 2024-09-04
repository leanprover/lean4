/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

prelude
import Init.Data.List.TakeDrop

/-!
## Bootstrapping theorems about arrays

This file contains some theorems about `Array` and `List` needed for `Init.Data.List.Impl`.
-/

namespace Array

theorem foldlM_eq_foldlM_data.aux [Monad m]
    (f : β → α → m β) (arr : Array α) (i j) (H : arr.size ≤ i + j) (b) :
    foldlM.loop f arr arr.size (Nat.le_refl _) i j b = (arr.data.drop j).foldlM f b := by
  unfold foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp [foldlM_eq_foldlM_data.aux f arr i (j+1) H]
    rw (config := {occs := .pos [2]}) [← List.get_drop_eq_drop _ _ ‹_›]
    rfl
  · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; rfl

theorem foldlM_eq_foldlM_data [Monad m]
    (f : β → α → m β) (init : β) (arr : Array α) :
    arr.foldlM f init = arr.data.foldlM f init := by
  simp [foldlM, foldlM_eq_foldlM_data.aux]

theorem foldl_eq_foldl_data (f : β → α → β) (init : β) (arr : Array α) :
    arr.foldl f init = arr.data.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_eq_foldlM_data ..

theorem foldrM_eq_reverse_foldlM_data.aux [Monad m]
    (f : α → β → m β) (arr : Array α) (init : β) (i h) :
    (arr.data.take i).reverse.foldlM (fun x y => f y x) init = foldrM.fold f arr 0 i h init := by
  unfold foldrM.fold
  match i with
  | 0 => simp [List.foldlM, List.take]
  | i+1 => rw [← List.take_concat_get _ _ h]; simp [← (aux f arr · i)]; rfl

theorem foldrM_eq_reverse_foldlM_data [Monad m] (f : α → β → m β) (init : β) (arr : Array α) :
    arr.foldrM f init = arr.data.reverse.foldlM (fun x y => f y x) init := by
  have : arr = #[] ∨ 0 < arr.size :=
    match arr with | ⟨[]⟩ => .inl rfl | ⟨a::l⟩ => .inr (Nat.zero_lt_succ _)
  match arr, this with | _, .inl rfl => rfl | arr, .inr h => ?_
  simp [foldrM, h, ← foldrM_eq_reverse_foldlM_data.aux, List.take_length]

theorem foldrM_eq_foldrM_data [Monad m]
    (f : α → β → m β) (init : β) (arr : Array α) :
    arr.foldrM f init = arr.data.foldrM f init := by
  rw [foldrM_eq_reverse_foldlM_data, List.foldlM_reverse]

theorem foldr_eq_foldr_data (f : α → β → β) (init : β) (arr : Array α) :
    arr.foldr f init = arr.data.foldr f init :=
  List.foldr_eq_foldrM .. ▸ foldrM_eq_foldrM_data ..

@[simp] theorem push_data (arr : Array α) (a : α) : (arr.push a).data = arr.data ++ [a] := by
  simp [push, List.concat_eq_append]

@[simp] theorem toListAppend_eq (arr : Array α) (l) : arr.toListAppend l = arr.data ++ l := by
  simp [toListAppend, foldr_eq_foldr_data]

@[simp] theorem toList_eq (arr : Array α) : arr.toList = arr.data := by
  simp [toList, foldr_eq_foldr_data]

@[simp] theorem pop_data (arr : Array α) : arr.pop.data = arr.data.dropLast := rfl

@[simp] theorem append_eq_append (arr arr' : Array α) : arr.append arr' = arr ++ arr' := rfl

@[simp] theorem append_data (arr arr' : Array α) :
    (arr ++ arr').data = arr.data ++ arr'.data := by
  rw [← append_eq_append]; unfold Array.append
  rw [foldl_eq_foldl_data]
  induction arr'.data generalizing arr <;> simp [*]

@[simp] theorem appendList_eq_append
    (arr : Array α) (l : List α) : arr.appendList l = arr ++ l := rfl

@[simp] theorem appendList_data (arr : Array α) (l : List α) :
    (arr ++ l).data = arr.data ++ l := by
  rw [← appendList_eq_append]; unfold Array.appendList
  induction l generalizing arr <;> simp [*]

end Array
