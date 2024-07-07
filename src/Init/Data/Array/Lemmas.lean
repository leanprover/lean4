/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.Nat.MinMax
import Init.Data.Nat.Lemmas
import Init.Data.List.Lemmas
import Init.Data.Fin.Basic
import Init.Data.Array.Mem
import Init.TacticsExtra

/-!
## Bootstrapping theorems about arrays

This file contains some theorems about `Array` and `List` needed for `Init.Data.List.Impl`.
-/

namespace Array

attribute [simp] data_toArray uset

@[simp] theorem singleton_def (v : α) : singleton v = #[v] := rfl

@[simp] theorem toArray_data : (a : Array α) → a.data.toArray = a
  | ⟨l⟩ => ext' (data_toArray l)

@[simp] theorem data_length {l : Array α} : l.data.length = l.size := rfl

@[simp] theorem mkEmpty_eq (α n) : @mkEmpty α n = #[] := rfl

@[simp] theorem size_toArray (as : List α) : as.toArray.size = as.length := by simp [size]

@[simp] theorem size_mk (as : List α) : (Array.mk as).size = as.length := by simp [size]

theorem getElem_eq_data_getElem (a : Array α) (h : i < a.size) : a[i] = a.data[i] := by
  by_cases i < a.size <;> (try simp [*]) <;> rfl

@[deprecated getElem_eq_data_getElem (since := "2024-06-12")]
theorem getElem_eq_data_get (a : Array α) (h : i < a.size) : a[i] = a.data.get ⟨i, h⟩ := by
  simp [getElem_eq_data_getElem]

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
  simp only [push, getElem_eq_data_getElem, List.concat_eq_append, List.getElem_append_left, h]

@[simp] theorem get_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, getElem_eq_data_getElem, List.concat_eq_append]
  rw [List.getElem_append_right] <;> simp [getElem_eq_data_getElem, Nat.zero_lt_one]

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
      simp only [aux (i + 1), map_eq_pure_bind, data_length, List.foldlM_cons, bind_assoc, pure_bind]
      rfl
    · rw [List.drop_length_le (Nat.ge_of_not_lt ‹_›)]; rfl
  termination_by arr.size - i
  decreasing_by decreasing_trivial_pre_omega

@[simp] theorem map_data (f : α → β) (arr : Array α) : (arr.map f).data = arr.data.map f := by
  rw [map, mapM_eq_foldlM]
  apply congrArg data (foldl_eq_foldl_data (fun bs a => push bs (f a)) #[] arr) |>.trans
  have H (l arr) : List.foldl (fun bs a => push bs (f a)) arr l = ⟨arr.data ++ l.map f⟩ := by
    induction l generalizing arr <;> simp [*]
  simp [H]

@[simp] theorem size_map (f : α → β) (arr : Array α) : (arr.map f).size = arr.size := by
  simp only [← data_length]
  simp

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

/-! # get -/

@[simp] theorem get_eq_getElem (a : Array α) (i : Fin _) : a.get i = a[i.1] := rfl

theorem getElem?_lt
    (a : Array α) {i : Nat} (h : i < a.size) : a[i]? = some (a[i]) := dif_pos h

theorem getElem?_ge
    (a : Array α) {i : Nat} (h : i ≥ a.size) : a[i]? = none := dif_neg (Nat.not_lt_of_le h)

@[simp] theorem get?_eq_getElem? (a : Array α) (i : Nat) : a.get? i = a[i]? := rfl

theorem getElem?_len_le (a : Array α) {i : Nat} (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_ge, h]

theorem getD_get? (a : Array α) (i : Nat) (d : α) :
  Option.getD a[i]? d = if p : i < a.size then a[i]'p else d := by
  if h : i < a.size then
    simp [setD, h, getElem?_def]
  else
    have p : i ≥ a.size := Nat.le_of_not_gt h
    simp [setD, getElem?_len_le _ p, h]

@[simp] theorem getD_eq_get? (a : Array α) (n d) : a.getD n d = (a[n]?).getD d := by
  simp only [getD, get_eq_getElem, get?_eq_getElem?]; split <;> simp [getD_get?, *]

theorem get!_eq_getD [Inhabited α] (a : Array α) : a.get! n = a.getD n default := rfl

@[simp] theorem get!_eq_getElem? [Inhabited α] (a : Array α) (i : Nat) : a.get! i = (a.get? i).getD default := by
  by_cases p : i < a.size <;> simp [getD_get?, get!_eq_getD, p]

/-! # set -/

@[simp] theorem getElem_set_eq (a : Array α) (i : Fin a.size) (v : α) {j : Nat}
      (eq : i.val = j) (p : j < (a.set i v).size) :
    (a.set i v)[j]'p = v := by
  simp [set, getElem_eq_data_getElem, ←eq]

@[simp] theorem getElem_set_ne (a : Array α) (i : Fin a.size) (v : α) {j : Nat} (pj : j < (a.set i v).size)
    (h : i.val ≠ j) : (a.set i v)[j]'pj = a[j]'(size_set a i v ▸ pj) := by
  simp only [set, getElem_eq_data_getElem, List.getElem_set_ne h]

theorem getElem_set (a : Array α) (i : Fin a.size) (v : α) (j : Nat)
    (h : j < (a.set i v).size) :
    (a.set i v)[j]'h = if i = j then v else a[j]'(size_set a i v ▸ h) := by
  by_cases p : i.1 = j <;> simp [p]

@[simp] theorem getElem?_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1]? = v := by simp [getElem?_lt, i.2]

@[simp] theorem getElem?_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α)
    (ne : i.val ≠ j) : (a.set i v)[j]? = a[j]? := by
  by_cases h : j < a.size <;> simp [getElem?_lt, getElem?_ge, Nat.ge_of_not_lt, ne, h]

/-! # setD -/

@[simp] theorem set!_is_setD : @set! = @setD := rfl

@[simp] theorem size_setD (a : Array α) (index : Nat) (val : α) :
  (Array.setD a index val).size = a.size := by
  if h : index < a.size  then
    simp [setD, h]
  else
    simp [setD, h]

@[simp] theorem getElem_setD_eq (a : Array α) {i : Nat} (v : α) (h : _) :
  (setD a i v)[i]'h = v := by
  simp at h
  simp only [setD, h, dite_true, getElem_set, ite_true]

@[simp]
theorem getElem?_setD_eq (a : Array α) {i : Nat} (p : i < a.size) (v : α) : (a.setD i v)[i]? = some v := by
  simp [getElem?_lt, p]

/-- Simplifies a normal form from `get!` -/
@[simp] theorem getD_get?_setD (a : Array α) (i : Nat) (v d : α) :
  Option.getD (setD a i v)[i]? d = if i < a.size then v else d := by
  by_cases h : i < a.size <;>
    simp [setD, Nat.not_lt_of_le, h,  getD_get?]

/-! # ofFn -/

@[simp] theorem size_ofFn_go {n} (f : Fin n → α) (i acc) :
    (ofFn.go f i acc).size = acc.size + (n - i) := by
  if hin : i < n then
    unfold ofFn.go
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    rw [dif_pos hin, size_ofFn_go f (i+1), size_push, Nat.add_assoc, this]
  else
    have : n - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hin)
    unfold ofFn.go
    simp [hin, this]
termination_by n - i

@[simp] theorem size_ofFn (f : Fin n → α) : (ofFn f).size = n := by simp [ofFn]

theorem getElem_ofFn_go (f : Fin n → α) (i) {acc k}
    (hki : k < n) (hin : i ≤ n) (hi : i = acc.size)
    (hacc : ∀ j, ∀ hj : j < acc.size, acc[j] = f ⟨j, Nat.lt_of_lt_of_le hj (hi ▸ hin)⟩) :
    haveI : acc.size + (n - acc.size) = n := Nat.add_sub_cancel' (hi ▸ hin)
    (ofFn.go f i acc)[k]'(by simp [*]) = f ⟨k, hki⟩ := by
  unfold ofFn.go
  if hin : i < n then
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    simp only [dif_pos hin]
    rw [getElem_ofFn_go f (i+1) _ hin (by simp [*]) (fun j hj => ?hacc)]
    cases (Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ (by simpa using hj)) with
    | inl hj => simp [get_push, hj, hacc j hj]
    | inr hj => simp [get_push, *]
  else
    simp [hin, hacc k (Nat.lt_of_lt_of_le hki (Nat.le_of_not_lt (hi ▸ hin)))]
termination_by n - i

@[simp] theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h) :
    (ofFn f)[i] = f ⟨i, size_ofFn f ▸ h⟩ :=
  getElem_ofFn_go _ _ _ (by simp) (by simp) nofun

/-- # mkArray -/

@[simp] theorem mkArray_data (n : Nat) (v : α) : (mkArray n v).data = List.replicate n v := rfl

@[simp] theorem getElem_mkArray (n : Nat) (v : α) (h : i < (mkArray n v).size) :
    (mkArray n v)[i] = v := by simp [Array.getElem_eq_data_getElem]

/-- # mem -/

theorem mem_data {a : α} {l : Array α} : a ∈ l.data ↔ a ∈ l := (mem_def _ _).symm

theorem not_mem_nil (a : α) : ¬ a ∈ #[] := nofun

/-- # get lemmas -/

theorem getElem?_mem {l : Array α} {i : Fin l.size} : l[i] ∈ l := by
  erw [Array.mem_def, getElem_eq_data_getElem]
  apply List.get_mem

theorem getElem_fin_eq_data_get (a : Array α) (i : Fin _) : a[i] = a.data.get i := rfl

@[simp] theorem ugetElem_eq_getElem (a : Array α) {i : USize} (h : i.toNat < a.size) :
  a[i] = a[i.toNat] := rfl

theorem getElem?_eq_getElem (a : Array α) (i : Nat) (h : i < a.size) : a[i]? = a[i] :=
  getElem?_pos ..

theorem get?_len_le (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_neg, h]

theorem getElem_mem_data (a : Array α) (h : i < a.size) : a[i] ∈ a.data := by
  simp only [getElem_eq_data_getElem, List.getElem_mem]

theorem getElem?_eq_data_get? (a : Array α) (i : Nat) : a[i]? = a.data.get? i := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg, List.get?_eq_get, eq_comm]; rfl

theorem get?_eq_data_get? (a : Array α) (i : Nat) : a.get? i = a.data.get? i :=
  getElem?_eq_data_get? ..

theorem get!_eq_get? [Inhabited α] (a : Array α) : a.get! n = (a.get? n).getD default := by
  simp [get!_eq_getD]

@[simp] theorem back_eq_back? [Inhabited α] (a : Array α) : a.back = a.back?.getD default := by
  simp [back, back?]

@[simp] theorem back?_push (a : Array α) : (a.push x).back? = some x := by
  simp [back?, getElem?_eq_data_get?]

theorem back_push [Inhabited α] (a : Array α) : (a.push x).back = x := by simp

theorem get?_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]? = some a[i] := by
  rw [getElem?_pos, get_push_lt]

theorem get?_push_eq (a : Array α) (x : α) : (a.push x)[a.size]? = some x := by
  rw [getElem?_pos, get_push_eq]

theorem get?_push {a : Array α} : (a.push x)[i]? = if i = a.size then some x else a[i]? := by
  match Nat.lt_trichotomy i a.size with
  | Or.inl g =>
    have h1 : i < a.size + 1 := by omega
    have h2 : i ≠ a.size := by omega
    simp [getElem?_def, size_push, g, h1, h2, get_push_lt]
  | Or.inr (Or.inl heq) =>
    simp [heq, getElem?_pos, get_push_eq]
  | Or.inr (Or.inr g) =>
    simp only [getElem?_def, size_push]
    have h1 : ¬ (i < a.size) := by omega
    have h2 : ¬ (i < a.size + 1) := by omega
    have h3 : i ≠ a.size := by omega
    simp [h1, h2, h3]

@[simp] theorem get?_size {a : Array α} : a[a.size]? = none := by
  simp only [getElem?_def, Nat.lt_irrefl, dite_false]

@[simp] theorem data_set (a : Array α) (i v) : (a.set i v).data = a.data.set i.1 v := rfl

theorem get_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1] = v := by
  simp only [set, getElem_eq_data_getElem, List.getElem_set_eq]

theorem get?_set_eq (a : Array α) (i : Fin a.size) (v : α) :
    (a.set i v)[i.1]? = v := by simp [getElem?_pos, i.2]

@[simp] theorem get?_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α)
    (h : i.1 ≠ j) : (a.set i v)[j]? = a[j]? := by
  by_cases j < a.size <;> simp [getElem?_pos, getElem?_neg, *]

theorem get?_set (a : Array α) (i : Fin a.size) (j : Nat) (v : α) :
    (a.set i v)[j]? = if i.1 = j then some v else a[j]? := by
  if h : i.1 = j then subst j; simp [*] else simp [*]

theorem get_set (a : Array α) (i : Fin a.size) (j : Nat) (hj : j < a.size) (v : α) :
    (a.set i v)[j]'(by simp [*]) = if i = j then v else a[j] := by
  if h : i.1 = j then subst j; simp [*] else simp [*]

@[simp] theorem get_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  simp only [set, getElem_eq_data_getElem, List.getElem_set_ne h]

theorem getElem_setD (a : Array α) (i : Nat) (v : α) (h : i < (setD a i v).size) :
  (setD a i v)[i] = v := by
  simp at h
  simp only [setD, h, dite_true, get_set, ite_true]

theorem set_set (a : Array α) (i : Fin a.size) (v v' : α) :
    (a.set i v).set ⟨i, by simp [i.2]⟩ v' = a.set i v' := by simp [set, List.set_set]

private theorem fin_cast_val (e : n = n') (i : Fin n) : e ▸ i = ⟨i.1, e ▸ i.2⟩ := by cases e; rfl

theorem swap_def (a : Array α) (i j : Fin a.size) :
    a.swap i j = (a.set i (a.get j)).set ⟨j.1, by simp [j.2]⟩ (a.get i) := by
  simp [swap, fin_cast_val]

theorem data_swap (a : Array α) (i j : Fin a.size) :
    (a.swap i j).data = (a.data.set i (a.get j)).set j (a.get i) := by simp [swap_def]

theorem get?_swap (a : Array α) (i j : Fin a.size) (k : Nat) : (a.swap i j)[k]? =
    if j = k then some a[i.1] else if i = k then some a[j.1] else a[k]? := by
  simp [swap_def, get?_set, ← getElem_fin_eq_data_get]

@[simp] theorem swapAt_def (a : Array α) (i : Fin a.size) (v : α) :
    a.swapAt i v = (a[i.1], a.set i v) := rfl

-- @[simp] -- FIXME: gives a weird linter error
theorem swapAt!_def (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    a.swapAt! i v = (a[i], a.set ⟨i, h⟩ v) := by simp [swapAt!, h]

@[simp] theorem data_pop (a : Array α) : a.pop.data = a.data.dropLast := by simp [pop]

@[simp] theorem pop_empty : (#[] : Array α).pop = #[] := rfl

@[simp] theorem pop_push (a : Array α) : (a.push x).pop = a := by simp [pop]

@[simp] theorem getElem_pop (a : Array α) (i : Nat) (hi : i < a.pop.size) :
    a.pop[i] = a[i]'(Nat.lt_of_lt_of_le (a.size_pop ▸ hi) (Nat.sub_le _ _)) :=
  List.getElem_dropLast ..

theorem eq_empty_of_size_eq_zero {as : Array α} (h : as.size = 0) : as = #[] := by
  apply ext
  · simp [h]
  · intros; contradiction

theorem eq_push_pop_back_of_size_ne_zero [Inhabited α] {as : Array α} (h : as.size ≠ 0) :
    as = as.pop.push as.back := by
  apply ext
  · simp [Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero h)]
  · intros i h h'
    if hlt : i < as.pop.size then
      rw [get_push_lt (h:=hlt), getElem_pop]
    else
      have heq : i = as.pop.size :=
        Nat.le_antisymm (size_pop .. ▸ Nat.le_pred_of_lt h) (Nat.le_of_not_gt hlt)
      cases heq; rw [get_push_eq, back, ←size_pop, get!_eq_getD, getD, dif_pos h]; rfl

theorem eq_push_of_size_ne_zero {as : Array α} (h : as.size ≠ 0) :
    ∃ (bs : Array α) (c : α), as = bs.push c :=
  let _ : Inhabited α := ⟨as[0]⟩
  ⟨as.pop, as.back, eq_push_pop_back_of_size_ne_zero h⟩

theorem size_eq_length_data (as : Array α) : as.size = as.data.length := rfl

@[simp] theorem size_swap! (a : Array α) (i j) :
    (a.swap! i j).size = a.size := by unfold swap!; split <;> (try split) <;> simp [size_swap]

@[simp] theorem size_reverse (a : Array α) : a.reverse.size = a.size := by
  let rec go (as : Array α) (i j) : (reverse.loop as i j).size = as.size := by
    rw [reverse.loop]
    if h : i < j then
      have := reverse.termination h
      simp [(go · (i+1) ⟨j-1, ·⟩), h]
    else simp [h]
    termination_by j - i
  simp only [reverse]; split <;> simp [go]

@[simp] theorem size_range {n : Nat} : (range n).size = n := by
  unfold range
  induction n with
  | zero      => simp [Nat.fold]
  | succ k ih =>
    rw [Nat.fold, flip]
    simp only [mkEmpty_eq, size_push] at *
    omega

set_option linter.deprecated false in
@[simp] theorem reverse_data (a : Array α) : a.reverse.data = a.data.reverse := by
  let rec go (as : Array α) (i j hj)
      (h : i + j + 1 = a.size) (h₂ : as.size = a.size)
      (H : ∀ k, as.data.get? k = if i ≤ k ∧ k ≤ j then a.data.get? k else a.data.reverse.get? k)
      (k) : (reverse.loop as i ⟨j, hj⟩).data.get? k = a.data.reverse.get? k := by
    rw [reverse.loop]; dsimp; split <;> rename_i h₁
    · have p := reverse.termination h₁
      match j with | j+1 => ?_
      simp only [Nat.add_sub_cancel] at p ⊢
      rw [(go · (i+1) j)]
      · rwa [Nat.add_right_comm i]
      · simp [size_swap, h₂]
      · intro k
        rw [← getElem?_eq_data_get?, get?_swap]
        simp only [H, getElem_eq_data_get, ← List.get?_eq_get, Nat.le_of_lt h₁, getElem?_eq_data_get?]
        split <;> rename_i h₂
        · simp only [← h₂, Nat.not_le.2 (Nat.lt_succ_self _), Nat.le_refl, and_false]
          exact (List.get?_reverse' (j+1) i (Eq.trans (by simp_arith) h)).symm
        split <;> rename_i h₃
        · simp only [← h₃, Nat.not_le.2 (Nat.lt_succ_self _), Nat.le_refl, false_and]
          exact (List.get?_reverse' i (j+1) (Eq.trans (by simp_arith) h)).symm
        simp only [Nat.succ_le, Nat.lt_iff_le_and_ne.trans (and_iff_left h₃),
          Nat.lt_succ.symm.trans (Nat.lt_iff_le_and_ne.trans (and_iff_left (Ne.symm h₂)))]
    · rw [H]; split <;> rename_i h₂
      · cases Nat.le_antisymm (Nat.not_lt.1 h₁) (Nat.le_trans h₂.1 h₂.2)
        cases Nat.le_antisymm h₂.1 h₂.2
        exact (List.get?_reverse' _ _ h).symm
      · rfl
    termination_by j - i
  simp only [reverse]
  split
  · match a with | ⟨[]⟩ | ⟨[_]⟩ => rfl
  · have := Nat.sub_add_cancel (Nat.le_of_not_le ‹_›)
    refine List.ext_get? <| go _ _ _ _ (by simp [this]) rfl fun k => ?_
    split
    · rfl
    · rename_i h
      simp only [← show k < _ + 1 ↔ _ from Nat.lt_succ (n := a.size - 1), this, Nat.zero_le,
        true_and, Nat.not_lt] at h
      rw [List.get?_eq_none.2 ‹_›, List.get?_eq_none.2 (a.data.length_reverse ▸ ‹_›)]

/-! ### foldl / foldr -/

-- This proof is the pure version of `Array.SatisfiesM_foldlM`,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldl_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive as.size (as.foldl f init) := by
  let rec go {i j b} (h₁ : j ≤ as.size) (h₂ : as.size ≤ i + j) (H : motive j b) :
    (motive as.size) (foldlM.loop (m := Id) f as as.size (Nat.le_refl _) i j b) := by
    unfold foldlM.loop; split
    · next hj =>
      split
      · cases Nat.not_le_of_gt (by simp [hj]) h₂
      · exact go hj (by rwa [Nat.succ_add] at h₂) (hf ⟨j, hj⟩ b H)
    · next hj => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hj) ▸ H
  simpa [foldl, foldlM] using go (Nat.zero_le _) (Nat.le_refl _) h0

-- This proof is the pure version of `Array.SatisfiesM_foldrM`,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldr_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive as.size init) {f : α → β → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → motive i.1 (f as[i] b)) :
    motive 0 (as.foldr f init) := by
  let rec go {i b} (hi : i ≤ as.size) (H : motive i b) :
    (motive 0) (foldrM.fold (m := Id) f as 0 i hi b) := by
    unfold foldrM.fold; simp; split
    · next hi => exact (hi ▸ H)
    · next hi =>
      split; {simp at hi}
      · next i hi' =>
        exact go _ (hf ⟨i, hi'⟩ b H)
  simp [foldr, foldrM]; split; {exact go _ h0}
  · next h => exact (Nat.eq_zero_of_not_pos h ▸ h0)

/-! ### map -/

@[simp] theorem mem_map {f : α → β} {l : Array α} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  simp only [mem_def, map_data, List.mem_map]

theorem mapM_eq_mapM_data [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = return mk (← arr.data.mapM f) := by
  rw [mapM_eq_foldlM, foldlM_eq_foldlM_data, ← List.foldrM_reverse]
  conv => rhs; rw [← List.reverse_reverse arr.data]
  induction arr.data.reverse with
  | nil => simp; rfl
  | cons a l ih => simp [ih]; simp [map_eq_pure_bind, push]

theorem mapM_map_eq_foldl (as : Array α) (f : α → β) (i) :
    mapM.map (m := Id) f as i b = as.foldl (start := i) (fun r a => r.push (f a)) b := by
  unfold mapM.map
  split <;> rename_i h
  · simp only [Id.bind_eq]
    dsimp [foldl, Id.run, foldlM]
    rw [mapM_map_eq_foldl, dif_pos (by omega), foldlM.loop, dif_pos h]
    -- Calling `split` here gives a bad goal.
    have : size as - i = Nat.succ (size as - i - 1) := by omega
    rw [this]
    simp [foldl, foldlM, Id.run, Nat.sub_add_eq]
  · dsimp [foldl, Id.run, foldlM]
    rw [dif_pos (by omega), foldlM.loop, dif_neg h]
    rfl
termination_by as.size - i

theorem map_eq_foldl (as : Array α) (f : α → β) :
    as.map f = as.foldl (fun r a => r.push (f a)) #[] :=
  mapM_map_eq_foldl _ _ _

theorem map_induction (as : Array α) (f : α → β) (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop) (hs : ∀ i, motive i.1 → p i (f as[i]) ∧ motive (i+1)) :
    motive as.size ∧
      ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]) := by
  have t := foldl_induction (as := as) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i arr[i.1])
    (init := #[]) (f := fun r a => r.push (f a)) ?_ ?_
  obtain ⟨m, eq, w⟩ := t
  · refine ⟨m, by simpa [map_eq_foldl] using eq, ?_⟩
    intro i h
    simp [eq] at w
    specialize w ⟨i, h⟩ h
    simpa [map_eq_foldl] using w
  · exact ⟨h0, rfl, nofun⟩
  · intro i b ⟨m, ⟨eq, w⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (hs _ m).2
    · simp_all
    · intro j h
      simp at h ⊢
      by_cases h' : j < size b
      · rw [get_push]
        simp_all
      · rw [get_push, dif_neg h']
        simp only [show j = i by omega]
        exact (hs _ m).1

theorem map_spec (as : Array α) (f : α → β) (p : Fin as.size → β → Prop)
    (hs : ∀ i, p i (f as[i])) :
    ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]) := by
  simpa using map_induction as f (fun _ => True) trivial p (by simp_all)

@[simp] theorem getElem_map (f : α → β) (as : Array α) (i : Nat) (h) :
    ((as.map f)[i]) = f (as[i]'(size_map .. ▸ h)) := by
  have := map_spec as f (fun i b => b = f (as[i]))
  simp only [implies_true, true_implies] at this
  obtain ⟨eq, w⟩ := this
  apply w
  simp_all

/-! ### mapIdx -/

-- This could also be prove from `SatisfiesM_mapIdxM`.
theorem mapIdx_induction (as : Array α) (f : Fin as.size → α → β)
    (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop)
    (hs : ∀ i, motive i.1 → p i (f i as[i]) ∧ motive (i + 1)) :
    motive as.size ∧ ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]) := by
  let rec go {bs i j h} (h₁ : j = bs.size) (h₂ : ∀ i h h', p ⟨i, h⟩ bs[i]) (hm : motive j) :
    let arr : Array β := Array.mapIdxM.map (m := Id) as f i j h bs
    motive as.size ∧ ∃ eq : arr.size = as.size, ∀ i h, p ⟨i, h⟩ arr[i] := by
    induction i generalizing j bs with simp [mapIdxM.map]
    | zero =>
      have := (Nat.zero_add _).symm.trans h
      exact ⟨this ▸ hm, h₁ ▸ this, fun _ _ => h₂ ..⟩
    | succ i ih =>
      apply @ih (bs.push (f ⟨j, by omega⟩ as[j])) (j + 1) (by omega) (by simp; omega)
      · intro i i_lt h'
        rw [get_push]
        split
        · apply h₂
        · simp only [size_push] at h'
          obtain rfl : i = j := by omega
          apply (hs ⟨i, by omega⟩ hm).1
      · exact (hs ⟨j, by omega⟩ hm).2
  simp [mapIdx, mapIdxM]; exact go rfl nofun h0

theorem mapIdx_spec (as : Array α) (f : Fin as.size → α → β)
    (p : Fin as.size → β → Prop) (hs : ∀ i, p i (f i as[i])) :
    ∃ eq : (Array.mapIdx as f).size = as.size,
      ∀ i h, p ⟨i, h⟩ ((Array.mapIdx as f)[i]) :=
  (mapIdx_induction _ _ (fun _ => True) trivial p fun _ _ => ⟨hs .., trivial⟩).2

@[simp] theorem size_mapIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapIdx f).size = a.size :=
  (mapIdx_spec (p := fun _ _ => True) (hs := fun _ => trivial)).1

@[simp] theorem size_zipWithIndex (as : Array α) : as.zipWithIndex.size = as.size :=
  Array.size_mapIdx _ _

@[simp] theorem getElem_mapIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat)
    (h : i < (mapIdx a f).size) :
    haveI : i < a.size := by simp_all
    (a.mapIdx f)[i] = f ⟨i, this⟩ a[i] :=
  (mapIdx_spec _ _ (fun i b => b = f i a[i]) fun _ => rfl).2 i _

/-! ### modify -/

@[simp] theorem size_modify (a : Array α) (i : Nat) (f : α → α) : (a.modify i f).size = a.size := by
  unfold modify modifyM Id.run
  split <;> simp

theorem get_modify {arr : Array α} {x i} (h : i < arr.size) :
    (arr.modify x f).get ⟨i, by simp [h]⟩ =
    if x = i then f (arr.get ⟨i, h⟩) else arr.get ⟨i, h⟩ := by
  simp [modify, modifyM, Id.run]; split
  · simp [get_set _ _ _ h]; split <;> simp [*]
  · rw [if_neg (mt (by rintro rfl; exact h) ‹_›)]

/-! ### filter -/

@[simp] theorem filter_data (p : α → Bool) (l : Array α) :
    (l.filter p).data = l.data.filter p := by
  dsimp only [filter]
  rw [foldl_eq_foldl_data]
  generalize l.data = l
  suffices ∀ a, (List.foldl (fun r a => if p a = true then push r a else r) a l).data =
      a.data ++ List.filter p l by
    simpa using this #[]
  induction l with simp
  | cons => split <;> simp [*]

@[simp] theorem filter_filter (q) (l : Array α) :
    filter p (filter q l) = filter (fun a => p a ∧ q a) l := by
  apply ext'
  simp only [filter_data, List.filter_filter]

@[simp] theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  simp only [mem_def, filter_data, List.mem_filter]

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  (mem_filter.mp h).1

/-! ### filterMap -/

@[simp] theorem filterMap_data (f : α → Option β) (l : Array α) :
    (l.filterMap f).data = l.data.filterMap f := by
  dsimp only [filterMap, filterMapM]
  rw [foldlM_eq_foldlM_data]
  generalize l.data = l
  have this : ∀ a : Array β, (Id.run (List.foldlM (m := Id) ?_ a l)).data =
    a.data ++ List.filterMap f l := ?_
  exact this #[]
  induction l
  · simp_all [Id.run]
  · simp_all [Id.run, List.filterMap_cons]
    split <;> simp_all

@[simp] theorem mem_filterMap (f : α → Option β) (l : Array α) {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  simp only [mem_def, filterMap_data, List.mem_filterMap]

/-! ### empty -/

theorem size_empty : (#[] : Array α).size = 0 := rfl

theorem empty_data : (#[] : Array α).data = [] := rfl

/-! ### append -/

theorem push_eq_append_singleton (as : Array α) (x) : as.push x = as ++ #[x] := rfl

@[simp] theorem mem_append {a : α} {s t : Array α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  simp only [mem_def, append_data, List.mem_append]

theorem size_append (as bs : Array α) : (as ++ bs).size = as.size + bs.size := by
  simp only [size, append_data, List.length_append]

theorem get_append_left {as bs : Array α} {h : i < (as ++ bs).size} (hlt : i < as.size) :
    (as ++ bs)[i] = as[i] := by
  simp only [getElem_eq_data_getElem]
  have h' : i < (as.data ++ bs.data).length := by rwa [← data_length, append_data] at h
  conv => rhs; rw [← List.getElem_append_left (bs := bs.data) (h' := h')]
  apply List.get_of_eq; rw [append_data]

theorem get_append_right {as bs : Array α} {h : i < (as ++ bs).size} (hle : as.size ≤ i)
    (hlt : i - as.size < bs.size := Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) :
    (as ++ bs)[i] = bs[i - as.size] := by
  simp only [getElem_eq_data_getElem]
  have h' : i < (as.data ++ bs.data).length := by rwa [← data_length, append_data] at h
  conv => rhs; rw [← List.getElem_append_right (h' := h') (h := Nat.not_lt_of_ge hle)]
  apply List.get_of_eq; rw [append_data]

@[simp] theorem append_nil (as : Array α) : as ++ #[] = as := by
  apply ext'; simp only [append_data, empty_data, List.append_nil]

@[simp] theorem nil_append (as : Array α) : #[] ++ as = as := by
  apply ext'; simp only [append_data, empty_data, List.nil_append]

theorem append_assoc (as bs cs : Array α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  apply ext'; simp only [append_data, List.append_assoc]

/-! ### extract -/

theorem extract_loop_zero (as bs : Array α) (start : Nat) : extract.loop as 0 start bs = bs := by
  rw [extract.loop]; split <;> rfl

theorem extract_loop_succ (as bs : Array α) (size start : Nat) (h : start < as.size) :
    extract.loop as (size+1) start bs = extract.loop as size (start+1) (bs.push as[start]) := by
  rw [extract.loop, dif_pos h]; rfl

theorem extract_loop_of_ge (as bs : Array α) (size start : Nat) (h : start ≥ as.size) :
    extract.loop as size start bs = bs := by
  rw [extract.loop, dif_neg (Nat.not_lt_of_ge h)]

theorem extract_loop_eq_aux (as bs : Array α) (size start : Nat) :
    extract.loop as size start bs = bs ++ extract.loop as size start #[] := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, extract_loop_zero, append_nil]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih (bs.push _), push_eq_append_singleton]
      rw [extract_loop_succ (h:=h), ih (#[].push _), push_eq_append_singleton, nil_append]
      rw [append_assoc]
    else
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [append_nil]

theorem extract_loop_eq (as bs : Array α) (size start : Nat) (h : start + size ≤ as.size) :
  extract.loop as size start bs = bs ++ as.extract start (start + size) := by
  simp [extract]; rw [extract_loop_eq_aux, Nat.min_eq_left h, Nat.add_sub_cancel_left]

theorem size_extract_loop (as bs : Array α) (size start : Nat) :
    (extract.loop as size start bs).size = bs.size + min size (as.size - start) := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, Nat.zero_min, Nat.add_zero]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih, size_push, Nat.add_assoc, ←Nat.add_min_add_left,
        Nat.sub_succ, Nat.one_add, Nat.one_add, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
    else
      have h := Nat.le_of_not_gt h
      rw [extract_loop_of_ge (h:=h), Nat.sub_eq_zero_of_le h, Nat.min_zero, Nat.add_zero]

@[simp] theorem size_extract (as : Array α) (start stop : Nat) :
    (as.extract start stop).size = min stop as.size - start := by
  simp [extract]; rw [size_extract_loop, size_empty, Nat.zero_add, Nat.sub_min_sub_right,
    Nat.min_assoc, Nat.min_self]

theorem get_extract_loop_lt_aux (as bs : Array α) (size start : Nat) (hlt : i < bs.size) :
    i < (extract.loop as size start bs).size := by
  rw [size_extract_loop]
  apply Nat.lt_of_lt_of_le hlt
  exact Nat.le_add_right ..

theorem get_extract_loop_lt (as bs : Array α) (size start : Nat) (hlt : i < bs.size)
    (h := get_extract_loop_lt_aux as bs size start hlt) :
    (extract.loop as size start bs)[i] = bs[i] := by
  apply Eq.trans _ (get_append_left (bs:=extract.loop as size start #[]) hlt)
  · rw [size_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)
  · congr; rw [extract_loop_eq_aux]

theorem get_extract_loop_ge_aux (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size) : start + i - bs.size < as.size := by
  have h : i < bs.size + (as.size - start) := by
      apply Nat.lt_of_lt_of_le h
      rw [size_extract_loop]
      apply Nat.add_le_add_left
      exact Nat.min_le_right ..
  rw [Nat.add_sub_assoc hge]
  apply Nat.add_lt_of_lt_sub'
  exact Nat.sub_lt_left_of_lt_add hge h

theorem get_extract_loop_ge (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size)
    (h' := get_extract_loop_ge_aux as bs size start hge h) :
    (extract.loop as size start bs)[i] = as[start + i - bs.size] := by
  induction size using Nat.recAux generalizing start bs with
  | zero =>
    rw [size_extract_loop, Nat.zero_min, Nat.add_zero] at h
    omega
  | succ size ih =>
    have : start < as.size := by
      apply Nat.lt_of_le_of_lt (Nat.le_add_right start (i - bs.size))
      rwa [← Nat.add_sub_assoc hge]
    have : i < (extract.loop as size (start+1) (bs.push as[start])).size := by
      rwa [← extract_loop_succ]
    have heq : (extract.loop as (size+1) start bs)[i] =
        (extract.loop as size (start+1) (bs.push as[start]))[i] := by
      congr 1; rw [extract_loop_succ]
    rw [heq]
    if hi : bs.size = i then
      cases hi
      have h₁ : bs.size < (bs.push as[start]).size := by rw [size_push]; exact Nat.lt_succ_self ..
      have h₂ : bs.size < (extract.loop as size (start+1) (bs.push as[start])).size := by
        rw [size_extract_loop]; apply Nat.lt_of_lt_of_le h₁; exact Nat.le_add_right ..
      have h : (extract.loop as size (start + 1) (push bs as[start]))[bs.size] = as[start] := by
        rw [get_extract_loop_lt as (bs.push as[start]) size (start+1) h₁ h₂, get_push_eq]
      rw [h]; congr; rw [Nat.add_sub_cancel]
    else
      have hge : bs.size + 1 ≤ i := Nat.lt_of_le_of_ne hge hi
      rw [ih (bs.push as[start]) (start+1) ((size_push ..).symm ▸ hge)]
      congr 1; rw [size_push, Nat.add_right_comm, Nat.add_sub_add_right]

theorem get_extract_aux {as : Array α} {start stop : Nat} (h : i < (as.extract start stop).size) :
    start + i < as.size := by
  rw [size_extract] at h; apply Nat.add_lt_of_lt_sub'; apply Nat.lt_of_lt_of_le h
  apply Nat.sub_le_sub_right; apply Nat.min_le_right

@[simp] theorem get_extract {as : Array α} {start stop : Nat}
    (h : i < (as.extract start stop).size) :
    (as.extract start stop)[i] = as[start + i]'(get_extract_aux h) :=
  show (extract.loop as (min stop as.size - start) start #[])[i]
    = as[start + i]'(get_extract_aux h) by rw [get_extract_loop_ge]; rfl; exact Nat.zero_le _

@[simp] theorem extract_all (as : Array α) : as.extract 0 as.size = as := by
  apply ext
  · rw [size_extract, Nat.min_self, Nat.sub_zero]
  · intros; rw [get_extract]; congr; rw [Nat.zero_add]

theorem extract_empty_of_stop_le_start (as : Array α) {start stop : Nat} (h : stop ≤ start) :
    as.extract start stop = #[] := by
  simp [extract]; rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.zero_min,
    extract_loop_zero]

theorem extract_empty_of_size_le_start (as : Array α) {start stop : Nat} (h : as.size ≤ start) :
    as.extract start stop = #[] := by
  simp [extract]; rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.min_zero,
    extract_loop_zero]

@[simp] theorem extract_empty (start stop : Nat) : (#[] : Array α).extract start stop = #[] :=
  extract_empty_of_size_le_start _ (Nat.zero_le _)

/-! ### any -/

-- Auxiliary for `any_iff_exists`.
theorem anyM_loop_iff_exists (p : α → Bool) (as : Array α) (start stop) (h : stop ≤ as.size) :
    anyM.loop (m := Id) p as stop h start = true ↔
      ∃ i : Fin as.size, start ≤ ↑i ∧ ↑i < stop ∧ p as[i] = true := by
  unfold anyM.loop
  split <;> rename_i h₁
  · dsimp
    split <;> rename_i h₂
    · simp only [true_iff]
      refine ⟨⟨start, by omega⟩, by dsimp; omega, by dsimp; omega, h₂⟩
    · rw [anyM_loop_iff_exists]
      constructor
      · rintro ⟨i, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; omega
        exact ⟨i, by omega, lt, h⟩
      · rintro ⟨i, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; erw [h] at h₂; simp_all
        exact ⟨i, by omega, lt, h⟩
  · simp
    omega
termination_by stop - start

-- This could also be proved from `SatisfiesM_anyM_iff_exists` in `Batteries.Data.Array.Init.Monadic`
theorem any_iff_exists (p : α → Bool) (as : Array α) (start stop) :
    any as p start stop ↔ ∃ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop ∧ p as[i] := by
  dsimp [any, anyM, Id.run]
  split
  · rw [anyM_loop_iff_exists]; rfl
  · rw [anyM_loop_iff_exists]
    constructor
    · rintro ⟨i, ge, _, h⟩
      exact ⟨i, by omega, by omega, h⟩
    · rintro ⟨i, ge, _, h⟩
      exact ⟨i, by omega, by omega, h⟩

theorem any_eq_true (p : α → Bool) (as : Array α) :
    any as p ↔ ∃ i : Fin as.size, p as[i] := by simp [any_iff_exists, Fin.isLt]

theorem any_def {p : α → Bool} (as : Array α) : as.any p = as.data.any p := by
  rw [Bool.eq_iff_iff, any_eq_true, List.any_eq_true]; simp only [List.mem_iff_get]
  exact ⟨fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩, fun ⟨_, ⟨i, rfl⟩, h⟩ => ⟨i, h⟩⟩

/-! ### all -/

theorem all_eq_not_any_not (p : α → Bool) (as : Array α) (start stop) :
    all as p start stop = !(any as (!p ·) start stop) := by
  dsimp [all, allM]
  rfl

theorem all_iff_forall (p : α → Bool) (as : Array α) (start stop) :
    all as p start stop ↔ ∀ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop → p as[i] := by
  rw [all_eq_not_any_not]
  suffices ¬(any as (!p ·) start stop = true) ↔
      ∀ i : Fin as.size, start ≤ i.1 ∧ i.1 < stop → p as[i] by
    simp_all
  rw [any_iff_exists]
  simp

theorem all_eq_true (p : α → Bool) (as : Array α) : all as p ↔ ∀ i : Fin as.size, p as[i] := by
  simp [all_iff_forall, Fin.isLt]

theorem all_def {p : α → Bool} (as : Array α) : as.all p = as.data.all p := by
  rw [Bool.eq_iff_iff, all_eq_true, List.all_eq_true]; simp only [List.mem_iff_getElem]
  constructor
  · rintro w x ⟨r, h, rfl⟩
    rw [← getElem_eq_data_getElem]
    exact w ⟨r, h⟩
  · intro w i
    exact w as[i] ⟨i, i.2, (getElem_eq_data_getElem as i.2).symm⟩

theorem all_eq_true_iff_forall_mem {l : Array α} : l.all p ↔ ∀ x, x ∈ l → p x := by
  simp only [all_def, List.all_eq_true, mem_def]

/-! ### contains -/

theorem contains_def [DecidableEq α] {a : α} {as : Array α} : as.contains a ↔ a ∈ as := by
  rw [mem_def, contains, any_def, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_iff _ contains_def

/-! ### swap -/

open Fin

@[simp] theorem get_swap_right (a : Array α) {i j : Fin a.size} : (a.swap i j)[j.val] = a[i] :=
  by simp only [swap, fin_cast_val, get_eq_getElem, getElem_set_eq, getElem_fin]

@[simp] theorem get_swap_left (a : Array α) {i j : Fin a.size} : (a.swap i j)[i.val] = a[j] :=
  if he : ((Array.size_set _ _ _).symm ▸ j).val = i.val then by
    simp only [←he, fin_cast_val, get_swap_right, getElem_fin]
  else by
    apply Eq.trans
    · apply Array.get_set_ne
      · simp only [size_set, Fin.isLt]
      · assumption
    · simp [get_set_ne]

@[simp] theorem get_swap_of_ne (a : Array α) {i j : Fin a.size} (hp : p < a.size)
    (hi : p ≠ i) (hj : p ≠ j) : (a.swap i j)[p]'(a.size_swap .. |>.symm ▸ hp) = a[p] := by
  apply Eq.trans
  · have : ((a.size_set i (a.get j)).symm ▸ j).val = j.val := by simp only [fin_cast_val]
    apply Array.get_set_ne
    · simp only [this]
      apply Ne.symm
      · assumption
  · apply Array.get_set_ne
    · apply Ne.symm
      · assumption

theorem get_swap (a : Array α) (i j : Fin a.size) (k : Nat) (hk: k < a.size) :
    (a.swap i j)[k]'(by simp_all) = if k = i then a[j] else if k = j then a[i]  else a[k] := by
  split
  · simp_all only [get_swap_left]
  · split <;> simp_all

theorem get_swap' (a : Array α) (i j : Fin a.size) (k : Nat) (hk' : k < (a.swap i j).size) :
    (a.swap i j)[k] = if k = i then a[j] else if k = j then a[i] else a[k]'(by simp_all) := by
  apply get_swap

@[simp] theorem swap_swap (a : Array α) {i j : Fin a.size} :
    (a.swap i j).swap ⟨i.1, (a.size_swap ..).symm ▸i.2⟩ ⟨j.1, (a.size_swap ..).symm ▸j.2⟩ = a := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [get_swap']
    split
    · simp_all
    · split <;> simp_all

theorem swap_comm (a : Array α) {i j : Fin a.size} : a.swap i j = a.swap j i := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [get_swap']
    split
    · split <;> simp_all
    · split <;> simp_all


end Array
