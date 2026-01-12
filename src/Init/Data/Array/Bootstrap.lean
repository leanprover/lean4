/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

module

prelude
public import Init.Data.List.TakeDrop
import all Init.Data.Array.Basic

public section

/-!
## Bootstrapping theorems about arrays

This file contains some theorems about `Array` and `List` needed for `Init.Data.List.Impl`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

theorem foldlM_toList.aux [Monad m]
    {f : β → α → m β} {xs : Array α} {i j} (H : xs.size ≤ i + j) {b} :
    foldlM.loop f xs xs.size (Nat.le_refl _) i j b = (xs.toList.drop j).foldlM f b := by
  unfold foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp [foldlM_toList.aux (j := j+1) H]
    rw (occs := [2]) [← List.getElem_cons_drop ‹_›]
    simp
  · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; simp

@[simp, grind =] theorem foldlM_toList [Monad m]
    {f : β → α → m β} {init : β} {xs : Array α} :
    xs.toList.foldlM f init = xs.foldlM f init := by
  simp [foldlM, foldlM_toList.aux]

@[simp, grind =] theorem foldl_toList (f : β → α → β) {init : β} {xs : Array α} :
    xs.toList.foldl f init = xs.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_toList ..

theorem foldrM_eq_reverse_foldlM_toList.aux [Monad m]
    {f : α → β → m β} {xs : Array α} {init : β} {i} (h) :
    (xs.toList.take i).reverse.foldlM (fun x y => f y x) init = foldrM.fold f xs 0 i h init := by
  unfold foldrM.fold
  match i with
  | 0 => simp
  | i+1 => rw [← List.take_concat_get h]; simp [← aux]

theorem foldrM_eq_reverse_foldlM_toList [Monad m] {f : α → β → m β} {init : β} {xs : Array α} :
    xs.foldrM f init = xs.toList.reverse.foldlM (fun x y => f y x) init := by
  have : xs = #[] ∨ 0 < xs.size :=
    match xs with | ⟨[]⟩ => .inl rfl | ⟨a::l⟩ => .inr (Nat.zero_lt_succ _)
  match xs, this with | _, .inl rfl => simp [foldrM] | xs, .inr h => ?_
  simp only [foldrM, h, ← foldrM_eq_reverse_foldlM_toList.aux]
  simp [Array.size]

@[simp, grind =] theorem foldrM_toList [Monad m]
    {f : α → β → m β} {init : β} {xs : Array α} :
    xs.toList.foldrM f init = xs.foldrM f init := by
  rw [foldrM_eq_reverse_foldlM_toList, List.foldlM_reverse]

@[simp, grind =] theorem foldr_toList (f : α → β → β) {init : β} {xs : Array α} :
    xs.toList.foldr f init = xs.foldr f init :=
  List.foldr_eq_foldrM .. ▸ foldrM_toList ..

@[simp, grind =] theorem toList_push {xs : Array α} {x : α} : (xs.push x).toList = xs.toList ++ [x] := by
  rcases xs with ⟨xs⟩
  simp [push, List.concat_eq_append]

@[simp, grind =] theorem toListAppend_eq {xs : Array α} {l : List α} : xs.toListAppend l = xs.toList ++ l := by
  simp [toListAppend, ← foldr_toList]

@[simp, grind =] theorem toListImpl_eq {xs : Array α} : xs.toListImpl = xs.toList := by
  simp [toListImpl, ← foldr_toList]

@[simp, grind =] theorem toList_pop {xs : Array α} : xs.pop.toList = xs.toList.dropLast := rfl

@[simp] theorem append_eq_append {xs ys : Array α} : xs.append ys = xs ++ ys := rfl

@[simp, grind =] theorem toList_append {xs ys : Array α} :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by
  rw [← append_eq_append]; unfold Array.append
  rw [← foldl_toList]
  induction ys.toList generalizing xs <;> simp [*]

@[simp] theorem toList_empty : (#[] : Array α).toList = [] := rfl

@[simp, grind =] theorem append_empty {xs : Array α} : xs ++ #[] = xs := by
  apply ext'; simp only [toList_append, List.append_nil]

@[simp, grind =] theorem empty_append {xs : Array α} : #[] ++ xs = xs := by
  apply ext'; simp only [toList_append, List.nil_append]

@[simp] theorem append_assoc {xs ys zs : Array α} : xs ++ ys ++ zs = xs ++ (ys ++ zs) := by
  apply ext'; simp only [toList_append, List.append_assoc]

grind_pattern append_assoc => (xs ++ ys) ++ zs where
  xs =/= #[]; ys =/= #[]; zs =/= #[]

grind_pattern append_assoc => xs ++ (ys ++ zs) where
  xs =/= #[]; ys =/= #[]; zs =/= #[]

@[simp] theorem appendList_eq_append {xs : Array α} {l : List α} : xs.appendList l = xs ++ l := rfl

@[simp, grind =] theorem toList_appendList {xs : Array α} {l : List α} :
    (xs ++ l).toList = xs.toList ++ l := by
  rw [← appendList_eq_append]; unfold Array.appendList
  induction l generalizing xs <;> simp [*]

end Array
