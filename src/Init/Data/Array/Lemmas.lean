/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.Nat.MinMax
import Init.Data.List.Lemmas
import Init.Data.Fin.Basic
import Init.Data.Array.Mem

/-!
## Bootstrapping theorems about arrays

This file contains some theorems about `Array` and `List` needed for `Std.List.Basic`.
-/

namespace Array

attribute [simp] data_toArray uset

@[simp] theorem mkEmpty_eq (α n) : @mkEmpty α n = #[] := rfl

@[simp] theorem size_toArray (as : List α) : as.toArray.size = as.length := by simp [size]

@[simp] theorem size_mk (as : List α) : (Array.mk as).size = as.length := by simp [size]

theorem getElem_eq_data_get (a : Array α) (h : i < a.size) : a[i] = a.data.get ⟨i, h⟩ := by
  by_cases i < a.size <;> (try simp [*]) <;> rfl

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
  · rw [List.drop_length_le (Nat.ge_of_not_lt ‹_›)]; rfl

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

theorem foldrM_push [Monad m] (f : α → β → m β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldrM f init = f a init >>= arr.foldrM f := by
  simp [foldrM_eq_reverse_foldlM_data, -size_push]

@[simp] theorem foldrM_push' [Monad m] (f : α → β → m β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldrM f init (start := arr.size + 1) = f a init >>= arr.foldrM f := by
  simp [← foldrM_push]

theorem foldr_push (f : α → β → β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldr f init = arr.foldr f (f a init) := foldrM_push ..

@[simp] theorem foldr_push' (f : α → β → β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldr f init (start := arr.size + 1) = arr.foldr f (f a init) := foldrM_push' ..

@[simp] theorem toListAppend_eq (arr : Array α) (l) : arr.toListAppend l = arr.data ++ l := by
  simp [toListAppend, foldr_eq_foldr_data]

@[simp] theorem toList_eq (arr : Array α) : arr.toList = arr.data := by
  simp [toList, foldr_eq_foldr_data]

/-- A more efficient version of `arr.toList.reverse`. -/
@[inline] def toListRev (arr : Array α) : List α := arr.foldl (fun l t => t :: l) []

@[simp] theorem toListRev_eq (arr : Array α) : arr.toListRev = arr.data.reverse := by
  rw [toListRev, foldl_eq_foldl_data, ← List.foldr_reverse, List.foldr_self]

theorem get_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    have : i < (a.push x).size := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (a.push x)[i] = a[i] := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append, List.get_append_left, h]

@[simp] theorem get_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, getElem_eq_data_get, List.concat_eq_append]
  rw [List.get_append_right] <;> simp [getElem_eq_data_get, Nat.zero_lt_one]

theorem get_push (a : Array α) (x : α) (i : Nat) (h : i < (a.push x).size) :
    (a.push x)[i] = if h : i < a.size then a[i] else x := by
  by_cases h' : i < a.size
  · simp [get_push_lt, h']
  · simp at h
    simp [get_push_lt, Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h')]

theorem mapM_eq_foldlM [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = arr.foldlM (fun bs a => bs.push <$> f a) #[] := by
  rw [mapM, aux, foldlM_eq_foldlM_data]; rfl
where
  aux (i r) :
      mapM.map f arr i r = (arr.data.drop i).foldlM (fun bs a => bs.push <$> f a) r := by
    unfold mapM.map; split
    · rw [← List.get_drop_eq_drop _ i ‹_›]
      simp [aux (i+1), map_eq_pure_bind]; rfl
    · rw [List.drop_length_le (Nat.ge_of_not_lt ‹_›)]; rfl
  termination_by arr.size - i

@[simp] theorem map_data (f : α → β) (arr : Array α) : (arr.map f).data = arr.data.map f := by
  rw [map, mapM_eq_foldlM]
  apply congrArg data (foldl_eq_foldl_data (fun bs a => push bs (f a)) #[] arr) |>.trans
  have H (l arr) : List.foldl (fun bs a => push bs (f a)) arr l = ⟨arr.data ++ l.map f⟩ := by
    induction l generalizing arr <;> simp [*]
  simp [H]

@[simp] theorem size_map (f : α → β) (arr : Array α) : (arr.map f).size = arr.size := by
  simp [size]

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

@[simp] theorem appendList_nil (arr : Array α) : arr ++ ([] : List α) = arr := Array.ext' (by simp)

@[simp] theorem appendList_cons (arr : Array α) (a : α) (l : List α) :
    arr ++ (a :: l) = arr.push a ++ l := Array.ext' (by simp)

theorem foldl_data_eq_bind (l : List α) (acc : Array β)
    (F : Array β → α → Array β) (G : α → List β)
    (H : ∀ acc a, (F acc a).data = acc.data ++ G a) :
    (l.foldl F acc).data = acc.data ++ l.bind G := by
  induction l generalizing acc <;> simp [*, List.bind]

theorem foldl_data_eq_map (l : List α) (acc : Array β) (G : α → β) :
    (l.foldl (fun acc a => acc.push (G a)) acc).data = acc.data ++ l.map G := by
  induction l generalizing acc <;> simp [*]

theorem size_uset (a : Array α) (v i h) : (uset a i v h).size = a.size := by simp

theorem anyM_eq_anyM_loop [Monad m] (p : α → m Bool) (as : Array α) (start stop) :
    anyM p as start stop = anyM.loop p as (min stop as.size) (Nat.min_le_right ..) start := by
  simp only [anyM, Nat.min_def]; split <;> rfl

theorem anyM_stop_le_start [Monad m] (p : α → m Bool) (as : Array α) (start stop)
    (h : min stop as.size ≤ start) : anyM p as start stop = pure false := by
  rw [anyM_eq_anyM_loop, anyM.loop, dif_neg (Nat.not_lt.2 h)]

theorem mem_def (a : α) (as : Array α) : a ∈ as ↔ a ∈ as.data :=
  ⟨fun | .mk h => h, Array.Mem.mk⟩
