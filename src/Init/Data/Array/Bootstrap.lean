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

theorem foldlM_eq_foldlM_toList.aux [Monad m]
    (f : β → α → m β) (arr : Array α) (i j) (H : arr.size ≤ i + j) (b) :
    foldlM.loop f arr arr.size (Nat.le_refl _) i j b = (arr.toList.drop j).foldlM f b := by
  unfold foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp [foldlM_eq_foldlM_toList.aux f arr i (j+1) H]
    rw (occs := .pos [2]) [← List.getElem_cons_drop_succ_eq_drop ‹_›]
    rfl
  · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; rfl

theorem foldlM_eq_foldlM_toList [Monad m]
    (f : β → α → m β) (init : β) (arr : Array α) :
    arr.foldlM f init = arr.toList.foldlM f init := by
  simp [foldlM, foldlM_eq_foldlM_toList.aux]

theorem foldl_eq_foldl_toList (f : β → α → β) (init : β) (arr : Array α) :
    arr.foldl f init = arr.toList.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_eq_foldlM_toList ..

theorem foldrM_eq_reverse_foldlM_toList.aux [Monad m]
    (f : α → β → m β) (arr : Array α) (init : β) (i h) :
    (arr.toList.take i).reverse.foldlM (fun x y => f y x) init = foldrM.fold f arr 0 i h init := by
  unfold foldrM.fold
  match i with
  | 0 => simp [List.foldlM, List.take]
  | i+1 => rw [← List.take_concat_get _ _ h]; simp [← (aux f arr · i)]

theorem foldrM_eq_reverse_foldlM_toList [Monad m] (f : α → β → m β) (init : β) (arr : Array α) :
    arr.foldrM f init = arr.toList.reverse.foldlM (fun x y => f y x) init := by
  have : arr = #[] ∨ 0 < arr.size :=
    match arr with | ⟨[]⟩ => .inl rfl | ⟨a::l⟩ => .inr (Nat.zero_lt_succ _)
  match arr, this with | _, .inl rfl => rfl | arr, .inr h => ?_
  simp [foldrM, h, ← foldrM_eq_reverse_foldlM_toList.aux, List.take_length]

theorem foldrM_eq_foldrM_toList [Monad m]
    (f : α → β → m β) (init : β) (arr : Array α) :
    arr.foldrM f init = arr.toList.foldrM f init := by
  rw [foldrM_eq_reverse_foldlM_toList, List.foldlM_reverse]

theorem foldr_eq_foldr_toList (f : α → β → β) (init : β) (arr : Array α) :
    arr.foldr f init = arr.toList.foldr f init :=
  List.foldr_eq_foldrM .. ▸ foldrM_eq_foldrM_toList ..

@[simp] theorem push_toList (arr : Array α) (a : α) : (arr.push a).toList = arr.toList ++ [a] := by
  simp [push, List.concat_eq_append]

@[simp] theorem toListAppend_eq (arr : Array α) (l) : arr.toListAppend l = arr.toList ++ l := by
  simp [toListAppend, foldr_eq_foldr_toList]

@[simp] theorem toListImpl_eq (arr : Array α) : arr.toListImpl = arr.toList := by
  simp [toListImpl, foldr_eq_foldr_toList]

@[simp] theorem pop_toList (arr : Array α) : arr.pop.toList = arr.toList.dropLast := rfl

@[simp] theorem append_eq_append (arr arr' : Array α) : arr.append arr' = arr ++ arr' := rfl

@[simp] theorem toList_append (arr arr' : Array α) :
    (arr ++ arr').toList = arr.toList ++ arr'.toList := by
  rw [← append_eq_append]; unfold Array.append
  rw [foldl_eq_foldl_toList]
  induction arr'.toList generalizing arr <;> simp [*]

@[simp] theorem toList_empty : (#[] : Array α).toList = [] := rfl

@[simp] theorem append_nil (as : Array α) : as ++ #[] = as := by
  apply ext'; simp only [toList_append, toList_empty, List.append_nil]

@[simp] theorem nil_append (as : Array α) : #[] ++ as = as := by
  apply ext'; simp only [toList_append, toList_empty, List.nil_append]

@[simp] theorem append_assoc (as bs cs : Array α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  apply ext'; simp only [toList_append, List.append_assoc]

@[simp] theorem appendList_eq_append
    (arr : Array α) (l : List α) : arr.appendList l = arr ++ l := rfl

@[simp] theorem appendList_toList (arr : Array α) (l : List α) :
    (arr ++ l).toList = arr.toList ++ l := by
  rw [← appendList_eq_append]; unfold Array.appendList
  induction l generalizing arr <;> simp [*]

@[deprecated foldlM_eq_foldlM_toList (since := "2024-09-09")]
abbrev foldlM_eq_foldlM_data := @foldlM_eq_foldlM_toList

@[deprecated foldl_eq_foldl_toList (since := "2024-09-09")]
abbrev foldl_eq_foldl_data := @foldl_eq_foldl_toList

@[deprecated foldrM_eq_reverse_foldlM_toList (since := "2024-09-09")]
abbrev foldrM_eq_reverse_foldlM_data := @foldrM_eq_reverse_foldlM_toList

@[deprecated foldrM_eq_foldrM_toList (since := "2024-09-09")]
abbrev foldrM_eq_foldrM_data := @foldrM_eq_foldrM_toList

@[deprecated foldr_eq_foldr_toList (since := "2024-09-09")]
abbrev foldr_eq_foldr_data := @foldr_eq_foldr_toList

@[deprecated push_toList (since := "2024-09-09")]
abbrev push_data := @push_toList

@[deprecated toListImpl_eq (since := "2024-09-09")]
abbrev toList_eq := @toListImpl_eq

@[deprecated pop_toList (since := "2024-09-09")]
abbrev pop_data := @pop_toList

@[deprecated toList_append (since := "2024-09-09")]
abbrev append_data := @toList_append

@[deprecated appendList_toList (since := "2024-09-09")]
abbrev appendList_data := @appendList_toList

end Array
