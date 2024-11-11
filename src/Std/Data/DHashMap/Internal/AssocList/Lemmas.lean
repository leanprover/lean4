/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.AssocList.Basic
import Std.Data.DHashMap.Internal.List.Associative

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: Connecting operations on `AssocList` to operations defined in `List.Associative`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DHashMap.Internal
open List (Perm perm_middle)

universe w v u

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace Std.DHashMap.Internal.AssocList

open Internal.List

@[simp] theorem toList_nil : (nil : AssocList α β).toList = [] := rfl
@[simp] theorem toList_cons {l : AssocList α β} {a : α} {b : β a} :
    (l.cons a b).toList = ⟨a, b⟩ :: l.toList := rfl

@[simp]
theorem foldl_eq {f : δ → (a : α) → β a → δ} {init : δ} {l : AssocList α β} :
    l.foldl f init = l.toList.foldl (fun d p => f d p.1 p.2) init := by
  induction l generalizing init <;> simp_all [foldl, Id.run, foldlM]

@[simp]
theorem length_eq {l : AssocList α β} : l.length = l.toList.length := by
  rw [length, foldl_eq]
  suffices ∀ n, l.toList.foldl (fun d _ => d + 1) n = l.toList.length + n by simp
  induction l
  · simp
  · next _ _ t ih =>
    intro n
    simp [ih, Nat.add_assoc, Nat.add_comm n 1]

@[simp]
theorem get?_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} :
    l.get? a = getValue? a l.toList := by
  induction l <;> simp_all [get?, List.getValue?]

@[simp]
theorem getCast?_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} :
    l.getCast? a = getValueCast? a l.toList := by
  induction l <;> simp_all [getCast?, List.getValueCast?]

@[simp]
theorem contains_eq [BEq α] {l : AssocList α β} {a : α} :
    l.contains a = containsKey a l.toList := by
  induction l <;> simp_all [contains, List.containsKey]

@[simp]
theorem getCast_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} {h} :
    l.getCast a h = getValueCast a l.toList (contains_eq.symm.trans h) := by
  induction l
  · simp [contains] at h
  · next k v t ih => simp only [getCast, toList_cons, List.getValueCast_cons, ih]

@[simp]
theorem get_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} {h} :
    l.get a h = getValue a l.toList (contains_eq.symm.trans h) := by
  induction l
  · simp [contains] at h
  · next k v t ih => simp only [get, toList_cons, List.getValue_cons, ih]

@[simp]
theorem getCastD_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} {fallback : β a} :
    l.getCastD a fallback = getValueCastD a l.toList fallback := by
  induction l
  · simp [getCastD, List.getValueCastD]
  · simp_all [getCastD, List.getValueCastD, List.getValueCastD, List.getValueCast?_cons,
      apply_dite (fun x => Option.getD x fallback)]

@[simp]
theorem getD_eq {β : Type v} [BEq α] {l : AssocList α (fun _ => β)} {a : α} {fallback : β} :
    l.getD a fallback = getValueD a l.toList fallback := by
  induction l
  · simp [getD, List.getValueD]
  · simp_all [getD, List.getValueD, List.getValueD, List.getValue?_cons,
      Bool.apply_cond (fun x => Option.getD x fallback)]

@[simp]
theorem panicWithPosWithDecl_eq [Inhabited α] {modName declName line col msg} :
  panicWithPosWithDecl modName declName line col msg = (default : α) := rfl

@[simp]
theorem getCast!_eq [BEq α] [LawfulBEq α] {l : AssocList α β} {a : α} [Inhabited (β a)] :
    l.getCast! a = getValueCast! a l.toList := by
  induction l
  · simp [getCast!, List.getValueCast!]
  · simp_all [getCast!, List.getValueCast!, List.getValueCast!, List.getValueCast?_cons,
      apply_dite Option.get!]

@[simp]
theorem get!_eq {β : Type v} [BEq α] [Inhabited β] {l : AssocList α (fun _ => β)} {a : α} :
    l.get! a = getValue! a l.toList := by
  induction l
  · simp [get!, List.getValue!]
  · simp_all [get!, List.getValue!, List.getValue!, List.getValue?_cons,
      Bool.apply_cond Option.get!]

@[simp]
theorem getKey?_eq [BEq α] {l : AssocList α β} {a : α} :
    l.getKey? a = List.getKey? a l.toList := by
  induction l <;> simp_all [getKey?]

@[simp]
theorem getKey_eq [BEq α] {l : AssocList α β} {a : α} {h} :
    l.getKey a h = List.getKey a l.toList (contains_eq.symm.trans h) := by
  induction l
  · simp [contains] at h
  · next k v t ih => simp only [getKey, toList_cons, List.getKey_cons, ih]

@[simp]
theorem getKeyD_eq [BEq α] {l : AssocList α β} {a fallback : α} :
    l.getKeyD a fallback = List.getKeyD a l.toList fallback := by
  induction l
  · simp [getKeyD, List.getKeyD]
  · simp_all [getKeyD, List.getKeyD, Bool.apply_cond (fun x => Option.getD x fallback)]

@[simp]
theorem getKey!_eq [BEq α] [Inhabited α] {l : AssocList α β} {a : α} :
    l.getKey! a = List.getKey! a l.toList := by
  induction l
  · simp [getKey!, List.getKey!]
  · simp_all [getKey!, List.getKey!, Bool.apply_cond Option.get!]

@[simp]
theorem toList_replace [BEq α] {l : AssocList α β} {a : α} {b : β a} :
    (l.replace a b).toList = replaceEntry a b l.toList := by
  induction l
  · simp [replace]
  · next k v t ih => cases h : k == a <;> simp_all [replace, List.replaceEntry_cons]

@[simp]
theorem toList_erase [BEq α] {l : AssocList α β} {a : α} :
    (l.erase a).toList = eraseKey a l.toList := by
  induction l
  · simp [erase]
  · next k v t ih => cases h : k == a <;> simp_all [erase, List.eraseKey_cons]

theorem toList_filterMap {f : (a : α) → β a → Option (γ a)} {l : AssocList α β} :
    Perm (l.filterMap f).toList (l.toList.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  rw [filterMap]
  suffices ∀ l l', Perm (filterMap.go f l l').toList
      (l.toList ++ l'.toList.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) by
    simpa using this .nil l
  intros l l'
  induction l' generalizing l
  · simp [filterMap.go]
  · next k v t ih =>
    simp only [filterMap.go, toList_cons, List.filterMap_cons]
    split
    · next h => exact (ih _).trans (by simp [h])
    · next h =>
      refine (ih _).trans ?_
      simp only [toList_cons, List.cons_append]
      exact perm_middle.symm.trans (by simp [h])

theorem toList_map {f : (a : α) → β a → γ a} {l : AssocList α β} :
    Perm (l.map f).toList (l.toList.map fun p => ⟨p.1, f p.1 p.2⟩) := by
  rw [map]
  suffices ∀ l l', Perm (map.go f l l').toList
      (l.toList ++ l'.toList.map fun p => ⟨p.1, f p.1 p.2⟩) by
    simpa using this .nil l
  intros l l'
  induction l' generalizing l
  · simp [map.go]
  · next k v t ih =>
    simp only [map.go, toList_cons, List.map_cons]
    refine (ih _).trans ?_
    simpa using perm_middle.symm

theorem toList_filter {f : (a : α) → β a → Bool} {l : AssocList α β} :
    Perm (l.filter f).toList (l.toList.filter fun p => f p.1 p.2) := by
  rw [filter]
  suffices ∀ l l', Perm (filter.go f l l').toList
      (l.toList ++ l'.toList.filter fun p => f p.1 p.2) by
    simpa using this .nil l
  intros l l'
  induction l' generalizing l
  · simp [filter.go]
  · next k v t ih =>
    simp only [filter.go, toList_cons, List.filter_cons, cond_eq_if]
    split
    · exact (ih _).trans (by simpa using perm_middle.symm)
    · exact ih _

theorem foldl_apply {l : AssocList α β} {acc : List δ} (f : (a : α) → β a → δ) :
    l.foldl (fun acc k v => f k v :: acc) acc =
      (l.toList.map (fun p => f p.1 p.2)).reverse ++ acc := by
  induction l generalizing acc <;> simp_all [AssocList.foldl, AssocList.foldlM, Id.run]

end Std.DHashMap.Internal.AssocList
