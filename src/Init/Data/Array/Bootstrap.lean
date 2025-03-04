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

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/--
Use the indexing notation `a[i]` instead.

Access an element from an array without needing a runtime bounds checks,
using a `Nat` index and a proof that it is in bounds.

This function does not use `get_elem_tactic` to automatically find the proof that
the index is in bounds. This is because the tactic itself needs to look up values in
arrays.
-/
@[deprecated "Use indexing notation `as[i]` instead" (since := "2025-02-17")]
def get {α : Type u} (a : @& Array α) (i : @& Nat) (h : LT.lt i a.size) : α :=
  a.toList.get ⟨i, h⟩

/--
Use the indexing notation `a[i]!` instead.

Access an element from an array, or panic if the index is out of bounds.
-/
@[deprecated "Use indexing notation `as[i]!` instead" (since := "2025-02-17")]
def get! {α : Type u} [Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
  Array.getD a i default

theorem foldlM_toList.aux [Monad m]
    (f : β → α → m β) (xs : Array α) (i j) (H : xs.size ≤ i + j) (b) :
    foldlM.loop f xs xs.size (Nat.le_refl _) i j b = (xs.toList.drop j).foldlM f b := by
  unfold foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp [foldlM_toList.aux f xs i (j+1) H]
    rw (occs := [2]) [← List.getElem_cons_drop_succ_eq_drop ‹_›]
    rfl
  · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; rfl

@[simp] theorem foldlM_toList [Monad m]
    (f : β → α → m β) (init : β) (xs : Array α) :
    xs.toList.foldlM f init = xs.foldlM f init := by
  simp [foldlM, foldlM_toList.aux]

@[simp] theorem foldl_toList (f : β → α → β) (init : β) (xs : Array α) :
    xs.toList.foldl f init = xs.foldl f init :=
  List.foldl_eq_foldlM .. ▸ foldlM_toList ..

theorem foldrM_eq_reverse_foldlM_toList.aux [Monad m]
    (f : α → β → m β) (xs : Array α) (init : β) (i h) :
    (xs.toList.take i).reverse.foldlM (fun x y => f y x) init = foldrM.fold f xs 0 i h init := by
  unfold foldrM.fold
  match i with
  | 0 => simp [List.foldlM, List.take]
  | i+1 => rw [← List.take_concat_get _ _ h]; simp [← (aux f xs · i)]

theorem foldrM_eq_reverse_foldlM_toList [Monad m] (f : α → β → m β) (init : β) (xs : Array α) :
    xs.foldrM f init = xs.toList.reverse.foldlM (fun x y => f y x) init := by
  have : xs = #[] ∨ 0 < xs.size :=
    match xs with | ⟨[]⟩ => .inl rfl | ⟨a::l⟩ => .inr (Nat.zero_lt_succ _)
  match xs, this with | _, .inl rfl => rfl | xs, .inr h => ?_
  simp [foldrM, h, ← foldrM_eq_reverse_foldlM_toList.aux, List.take_length]

@[simp] theorem foldrM_toList [Monad m]
    (f : α → β → m β) (init : β) (xs : Array α) :
    xs.toList.foldrM f init = xs.foldrM f init := by
  rw [foldrM_eq_reverse_foldlM_toList, List.foldlM_reverse]

@[simp] theorem foldr_toList (f : α → β → β) (init : β) (xs : Array α) :
    xs.toList.foldr f init = xs.foldr f init :=
  List.foldr_eq_foldrM .. ▸ foldrM_toList ..

@[simp] theorem push_toList (xs : Array α) (a : α) : (xs.push a).toList = xs.toList ++ [a] := by
  simp [push, List.concat_eq_append]

@[simp] theorem toListAppend_eq (xs : Array α) (l : List α) : xs.toListAppend l = xs.toList ++ l := by
  simp [toListAppend, ← foldr_toList]

@[simp] theorem toListImpl_eq (xs : Array α) : xs.toListImpl = xs.toList := by
  simp [toListImpl, ← foldr_toList]

@[simp] theorem toList_pop (xs : Array α) : xs.pop.toList = xs.toList.dropLast := rfl

@[deprecated toList_pop (since := "2025-02-17")]
abbrev pop_toList := @Array.toList_pop

@[simp] theorem append_eq_append (xs ys : Array α) : xs.append ys = xs ++ ys := rfl

@[simp] theorem toList_append (xs ys : Array α) :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by
  rw [← append_eq_append]; unfold Array.append
  rw [← foldl_toList]
  induction ys.toList generalizing xs <;> simp [*]

@[simp] theorem toList_empty : (#[] : Array α).toList = [] := rfl

@[simp] theorem append_empty (xs : Array α) : xs ++ #[] = xs := by
  apply ext'; simp only [toList_append, toList_empty, List.append_nil]

@[deprecated append_empty (since := "2025-01-13")]
abbrev append_nil := @append_empty

@[simp] theorem empty_append (xs : Array α) : #[] ++ xs = xs := by
  apply ext'; simp only [toList_append, toList_empty, List.nil_append]

@[deprecated empty_append (since := "2025-01-13")]
abbrev nil_append := @empty_append

@[simp] theorem append_assoc (xs ys zs : Array α) : xs ++ ys ++ zs = xs ++ (ys ++ zs) := by
  apply ext'; simp only [toList_append, List.append_assoc]

@[simp] theorem appendList_eq_append
    (xs : Array α) (l : List α) : xs.appendList l = xs ++ l := rfl

@[simp] theorem toList_appendList (xs : Array α) (l : List α) :
    (xs ++ l).toList = xs.toList ++ l := by
  rw [← appendList_eq_append]; unfold Array.appendList
  induction l generalizing xs <;> simp [*]

@[deprecated toList_appendList (since := "2024-12-11")]
abbrev appendList_toList := @toList_appendList

@[deprecated "Use the reverse direction of `foldrM_toList`." (since := "2024-11-13")]
theorem foldrM_eq_foldrM_toList [Monad m]
    (f : α → β → m β) (init : β) (xs : Array α) :
    xs.foldrM f init = xs.toList.foldrM f init := by
  simp

@[deprecated "Use the reverse direction of `foldlM_toList`." (since := "2024-11-13")]
theorem foldlM_eq_foldlM_toList [Monad m]
    (f : β → α → m β) (init : β) (xs : Array α) :
    xs.foldlM f init = xs.toList.foldlM f init:= by
  simp

@[deprecated "Use the reverse direction of `foldr_toList`." (since := "2024-11-13")]
theorem foldr_eq_foldr_toList
    (f : α → β → β) (init : β) (xs : Array α) :
    xs.foldr f init = xs.toList.foldr f init := by
  simp

@[deprecated "Use the reverse direction of `foldl_toList`." (since := "2024-11-13")]
theorem foldl_eq_foldl_toList
    (f : β → α → β) (init : β) (xs : Array α) :
    xs.foldl f init = xs.toList.foldl f init:= by
  simp

@[deprecated foldlM_toList (since := "2024-09-09")]
abbrev foldlM_eq_foldlM_data := @foldlM_toList

@[deprecated foldl_toList (since := "2024-09-09")]
abbrev foldl_eq_foldl_data := @foldl_toList

@[deprecated foldrM_eq_reverse_foldlM_toList (since := "2024-09-09")]
abbrev foldrM_eq_reverse_foldlM_data := @foldrM_eq_reverse_foldlM_toList

@[deprecated foldrM_toList (since := "2024-09-09")]
abbrev foldrM_eq_foldrM_data := @foldrM_toList

@[deprecated foldr_toList (since := "2024-09-09")]
abbrev foldr_eq_foldr_data := @foldr_toList

@[deprecated push_toList (since := "2024-09-09")]
abbrev push_data := @push_toList

@[deprecated toListImpl_eq (since := "2024-09-09")]
abbrev toList_eq := @toListImpl_eq

@[deprecated pop_toList (since := "2024-09-09")]
abbrev pop_data := @toList_pop

@[deprecated toList_append (since := "2024-09-09")]
abbrev append_data := @toList_append

@[deprecated toList_appendList (since := "2024-09-09")]
abbrev appendList_data := @toList_appendList

end Array
