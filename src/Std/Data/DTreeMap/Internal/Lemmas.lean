/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.HashMap.Basic
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Internal lemmas about the tree map

This file contains internal lemmas about `Std.DTreeMap.Internal.Impl`. Users of the tree map should
not rely on the contents of this file.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.Internal.List
open Std.Internal

universe u v w

namespace Std.DTreeMap.Internal.Impl

variable {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Impl α β}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

attribute [local instance low] beqOfOrd
attribute [local instance] equivBEq_of_transOrd
attribute [local instance] lawfulBEq_of_lawfulEqOrd

/-- Internal implementation detail of the tree map -/
scoped syntax "wf_trivial" : tactic

macro_rules
| `(tactic| wf_trivial) => `(tactic|
    (first
    | assumption | apply Ordered.distinctKeys
    | apply WF.ordered | apply WF.balanced | apply WF.empty
    | apply WF.insert | apply WF.insertIfNew
    | apply WF.erase | apply WF.insertMany
    | apply WF.constInsertMany | apply WF.constInsertManyIfNewUnit
    | apply WF.alter | apply WF.constAlter
    | apply WF.modify | apply WF.constModify) <;> wf_trivial)

/-- Internal implementation detail of the tree map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

theorem compare_ne_iff_beq_eq_false {a b : α} :
    compare a b ≠ Ordering.eq ↔ (a == b) = false := by
  simp only [ne_eq, compare_eq_iff_beq, Bool.not_eq_true]

private def helperLemmaNames : Array Name :=
  #[``compare_eq_iff_beq, ``compare_ne_iff_beq_eq_false, ``Bool.not_eq_true, ``mem_iff_contains]

private def modifyMap : Std.HashMap Name Name :=
  .ofList
    [⟨`insert, ``toListModel_insert⟩,
     ⟨`insertIfNew, ``toListModel_insertIfNew⟩,
     ⟨`erase, ``toListModel_erase⟩,
     (`insertMany, ``toListModel_insertMany_list),
     (`Const.insertMany, ``Const.toListModel_insertMany_list),
     (`Const.insertManyIfNewUnit, ``Const.toListModel_insertManyIfNewUnit_list),
     (`alter, ``toListModel_alter),
     (`Const.alter, ``Const.toListModel_alter),
     (`modify, ``toListModel_modify),
     (`Const.modify, ``Const.toListModel_modify)]

private def queryMap : Std.DHashMap Name (fun _ => Name × Array (MacroM (TSyntax `term))) :=
  .ofList
    [⟨`isEmpty, (``isEmpty_eq_isEmpty, #[``(_root_.List.Perm.isEmpty_eq)])⟩,
     ⟨`contains, (``contains_eq_containsKey, #[``(containsKey_of_perm)])⟩,
     ⟨`size, (``size_eq_length, #[``(_root_.List.Perm.length_eq)])⟩,
     ⟨`get?, (``get?_eq_getValueCast?, #[``(getValueCast?_of_perm _)])⟩,
     ⟨`Const.get?, (``Const.get?_eq_getValue?, #[``(getValue?_of_perm _)])⟩,
     ⟨`Const.get, (``Const.get_eq_getValue, #[``(getValue_of_perm _)])⟩,
     ⟨`get, (``get_eq_getValueCast, #[``(getValueCast_of_perm _)])⟩,
     ⟨`get!, (``get!_eq_getValueCast!, #[``(getValueCast!_of_perm _)])⟩,
     ⟨`getD, (``getD_eq_getValueCastD, #[``(getValueCastD_of_perm _)])⟩,
     ⟨`Const.get!, (``Const.get!_eq_getValue!, #[``(getValue!_of_perm _)])⟩,
     ⟨`Const.getD, (``Const.getD_eq_getValueD, #[``(getValueD_of_perm _)])⟩,
     ⟨`getKey?, (``getKey?_eq_getKey?, #[``(getKey?_of_perm _)])⟩,
     ⟨`getKey, (``getKey_eq_getKey, #[``(getKey_of_perm _)])⟩,
     ⟨`getKeyD, (``getKeyD_eq_getKeyD, #[``(getKeyD_of_perm _)])⟩,
     ⟨`getKey!, (``getKey!_eq_getKey!, #[``(getKey!_of_perm _)])⟩,
     ⟨`toList, (``toList_eq_toListModel, #[])⟩,
     ⟨`keys, (``keys_eq_keys, #[])⟩,
     ⟨`Const.toList, (``Const.toList_eq_toListModel_map, #[])⟩,
     ⟨`foldlM, (``foldlM_eq_foldlM_toListModel, #[])⟩,
     ⟨`foldl, (``foldl_eq_foldl, #[])⟩,
     ⟨`foldrM, (``foldrM_eq_foldrM, #[])⟩,
     ⟨`foldr, (``foldr_eq_foldr, #[])⟩,
     ⟨`forIn, (``forIn_eq_forIn_toListModel, #[])⟩,
     ⟨`forM, (``forM_eq_forM, #[])⟩,
     ⟨`minKey?, (``minKey?_eq_minKey?, #[``(minKey?_of_perm _)])⟩,
     ⟨`minKey, (``minKey_eq_minKey, #[``(minKey_of_perm _)])⟩,
     ⟨`minKey!, (``minKey!_eq_minKey!, #[``(minKey!_of_perm _)])⟩]

/-- Internal implementation detail of the tree map -/
scoped syntax "simp_to_model" (" [" (ident,*) "]")? ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[[$names,*]]? $[using $using?]?) => do
  let mut queryNames : Array Name := #[]
  let mut congrNames : Array Term := #[]
  if let some names := names then
    for query in names.getElems do
      let some (query, congr) := queryMap.get? query.getId | continue
      queryNames := queryNames.push query
      for c in congr do
        congrNames := congrNames.push (← c)
  if queryNames.isEmpty then
    for (q, c) in queryMap.valuesArray do
      queryNames := queryNames.push q
      for c' in c do
        congrNames := congrNames.push (← c')
  let mut congrModify : Array (TSyntax `term) := #[]
  if let some modifyNames := names then
    for modify in modifyNames.getElems.flatMap
        (fun n => modifyMap.get? (Lean.Syntax.getId n) |>.toArray) do
      for congr in congrNames do
        congrModify := congrModify.push (← `($congr:term ($(mkIdent modify) ..)))
  `(tactic|
    (simp (discharger := with_reducible wf_trivial) only
      [$[$(Array.map Lean.mkIdent (helperLemmaNames ++ queryNames) ++ congrModify):term],*]
     $[apply $(using?.toArray):term];*)
    <;> with_reducible try wf_trivial)

theorem isEmpty_empty : isEmpty (empty : Impl α β) := by
  rfl

theorem isEmpty_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.isEmpty = false := by
  simp_to_model [insert, isEmpty] using List.isEmpty_insertEntry

theorem isEmpty_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).isEmpty = false := by
  simpa only [insert_eq_insert!] using isEmpty_insert h

theorem contains_congr [TransOrd α] (h : t.WF) {k k' : α} : (hab : compare k k' = .eq) →
    t.contains k = t.contains k' := by
  simp_to_model [contains] using List.containsKey_congr

theorem mem_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : compare k k' = .eq) :
    k ∈ t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_congr h hab]

theorem contains_empty {a : α} : (empty : Impl α β).contains a = false := by
  rfl

theorem not_mem_empty {a : α} : a ∉ (empty : Impl α β) := by
  exact (Bool.not_eq_true _).mpr contains_empty

theorem contains_of_isEmpty [TransOrd α] (h : t.WF) {a : α}
    (h : t.isEmpty) : t.contains a = false := by
  match t, h with
  | .leaf, _ => exact contains_empty

theorem not_mem_of_isEmpty [TransOrd α] (h : t.WF) {a : α}
    (h : t.isEmpty) : a ∉ t := by
  match t, h with
  | .leaf, _ => exact not_mem_empty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransOrd α] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true := by
  simp_to_model [isEmpty, contains] using List.isEmpty_eq_false_iff_exists_containsKey

theorem isEmpty_eq_false_iff_exists_mem [TransOrd α] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t := by
  simpa only [mem_iff_contains] using isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_eq_false_of_contains [TransOrd α] (h : t.WF) {a : α} : (hc : t.contains a = true) →
    t.isEmpty = false := by
  simp_to_model [isEmpty, contains] using List.isEmpty_eq_false_of_containsKey

theorem isEmpty_iff_forall_contains [TransOrd α] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false := by
  simp_to_model [isEmpty, contains] using List.isEmpty_iff_forall_containsKey

theorem isEmpty_iff_forall_not_mem [TransOrd α] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t := by
  simpa only [mem_iff_contains, Bool.not_eq_true] using isEmpty_iff_forall_contains h

theorem contains_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model [insert, contains] using List.containsKey_insertEntry

theorem contains_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert! k v).contains a = (compare k a == .eq || t.contains a) :=
  insert_eq_insert! (h := h.balanced) ▸ contains_insert h

theorem mem_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insert k v h.balanced).impl ↔ compare k a = .eq ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insert h]

theorem mem_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert! k v ↔ compare k a = .eq ∨ a ∈ t := by
  simpa only [insert_eq_insert!] using mem_insert h

theorem contains_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains k := by
  simp_to_model [insert, contains] using List.containsKey_insertEntry_self

theorem contains_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).contains k :=
  insert_eq_insert! (h := h.balanced) ▸ contains_insert_self h

theorem mem_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ (t.insert k v h.balanced).impl := by
  simpa [mem_iff_contains] using contains_insert_self h

theorem mem_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insert! k v :=
  insert_eq_insert! (h := h.balanced) ▸ mem_insert_self h

theorem contains_of_contains_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains a → compare k a ≠ .eq → t.contains a := by
  simp_to_model [insert, contains] using List.containsKey_of_containsKey_insertEntry

theorem contains_of_contains_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert! k v).contains a → compare k a ≠ .eq → t.contains a := by
  simpa only [insert_eq_insert!] using contains_of_contains_insert h

theorem mem_of_mem_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insert k v h.balanced).impl → compare k a ≠ .eq → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insert h

theorem mem_of_mem_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert! k v → compare k a ≠ .eq → a ∈ t := by
  simpa only [insert_eq_insert!] using mem_of_mem_insert h

theorem size_empty : (empty : Impl α β).size = 0 :=
  rfl

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) := by
  simp_to_model [isEmpty, size]
  rw [Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, Nat.beq_eq_true_eq]

theorem size_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.size = if t.contains k then t.size else t.size + 1 := by
  simp_to_model [insert, size, contains] using List.length_insertEntry

theorem size_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).size = if t.contains k then t.size else t.size + 1 := by
  simpa only [insert_eq_insert!] using size_insert h

theorem size_le_size_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v h.balanced).impl.size := by
  simp_to_model [insert, size] using List.length_le_length_insertEntry

theorem size_le_size_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert! k v).size := by
  simpa only [insert_eq_insert!] using size_le_size_insert h

theorem size_insert_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.size ≤ t.size + 1 := by
  simp_to_model [insert, size] using List.length_insertEntry_le

theorem size_insert!_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).size ≤ t.size + 1 := by
  simpa only [insert_eq_insert!] using size_insert_le h

theorem erase_empty {k : α} :
    ((empty : Impl α β).erase k balanced_empty).impl = empty :=
  rfl

theorem erase!_empty {k : α} :
    (empty : Impl α β).erase! k = empty :=
  rfl

theorem isEmpty_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model [erase, isEmpty, size, contains] using List.isEmpty_eraseKey

theorem isEmpty_erase! [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simpa only [erase_eq_erase!] using isEmpty_erase h

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransOrd α] (h : t.WF) (k : α) :
    t.isEmpty = ((t.erase k h.balanced).impl.isEmpty && !(t.contains k)) := by
  simp_to_model [erase, isEmpty, contains] using
    List.isEmpty_eq_isEmpty_eraseKey_and_not_containsKey

theorem isEmpty_eq_isEmpty_erase!_and_not_containsKey [TransOrd α] (h : t.WF) (k : α) :
    t.isEmpty = ((t.erase! k).isEmpty && !(t.contains k)) := by
  simpa [erase_eq_erase!] using isEmpty_eq_isEmpty_erase_and_not_contains h k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransOrd α] (h : t.WF) {k : α} :
    (he : (t.erase k h.balanced).impl.isEmpty = false) →
    t.isEmpty = false := by
  simp_to_model [erase, isEmpty, contains] using List.isEmpty_eq_false_of_isEmpty_eraseKey_eq_false

theorem isEmpty_eq_false_of_isEmpty_erase!_eq_false [TransOrd α] (h : t.WF) {k : α} :
    (he : (t.erase! k).isEmpty = false) →
    t.isEmpty = false := by
  simpa [erase_eq_erase!] using isEmpty_eq_false_of_isEmpty_erase_eq_false h

theorem contains_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.contains a = (!(compare k a == .eq) && t.contains a) := by
  simp_to_model [erase, contains] using List.containsKey_eraseKey

theorem contains_erase! [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).contains a = (!(compare k a == .eq) && t.contains a) := by
  simpa only [erase_eq_erase!] using contains_erase h

theorem mem_erase [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ (t.erase k h.balanced).impl ↔ compare k a ≠ .eq ∧ a ∈ t := by
  simpa only [mem_iff_contains, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    using Bool.eq_iff_iff.mp <| contains_erase h

theorem mem_erase! [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ t.erase! k ↔ compare k a ≠ .eq ∧ a ∈ t := by
  simpa only [erase_eq_erase!] using mem_erase h

theorem contains_of_contains_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.contains a → t.contains a := by
  simp_to_model [erase, contains] using List.containsKey_of_containsKey_eraseKey

theorem contains_of_contains_erase! [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).contains a → t.contains a := by
  simpa only [erase_eq_erase!] using contains_of_contains_erase h

theorem mem_of_mem_erase [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ (t.erase k h.balanced).impl → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_erase h

theorem mem_of_mem_erase! [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ t.erase! k → a ∈ t := by
  simpa only [erase_eq_erase!] using mem_of_mem_erase h

theorem size_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.size = if t.contains k then t.size - 1 else t.size := by
  simp_to_model [erase, size, contains] using List.length_eraseKey

theorem size_erase! [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).size = if t.contains k then t.size - 1 else t.size := by
  simpa only [erase_eq_erase!] using size_erase h

theorem size_erase_le [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.size ≤ t.size := by
  simp_to_model [erase, size] using List.length_eraseKey_le

theorem size_erase!_le [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).size ≤ t.size := by
  simpa only [erase_eq_erase!] using size_erase_le h

theorem size_le_size_erase [TransOrd α] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k h.balanced).impl.size + 1 := by
  simp_to_model [erase, size] using List.length_le_length_eraseKey

theorem size_le_size_erase! [TransOrd α] (h : t.WF) {k : α} :
    t.size ≤ (t.erase! k).size + 1 := by
  simpa only [erase_eq_erase!] using size_le_size_erase h

theorem containsThenInsert_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v h.balanced).1 = t.contains k := by
  rw [containsThenInsert_fst_eq_containsₘ, contains_eq_containsₘ]
  exact h.ordered

theorem containsThenInsert!_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert! k v).1 = t.contains k := by
  rw [containsThenInsert!_fst_eq_containsThenInsert_fst, containsThenInsert_fst h]

theorem containsThenInsert_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v h.balanced).2.impl = (t.insert k v h.balanced).impl := by
  rfl

theorem containsThenInsert!_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert! k v).2 = t.insert! k v := by
  rw [containsThenInsert!_snd_eq_containsThenInsert_snd _ h.balanced, containsThenInsert_snd h,
    insert_eq_insert!]

theorem containsThenInsertIfNew_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v h.balanced).1 = t.contains k := by
  rw [containsThenInsertIfNew_fst_eq_containsₘ, contains_eq_containsₘ]

theorem containsThenInsertIfNew!_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew! k v).1 = t.contains k := by
  rw [containsThenInsertIfNew!_fst_eq_containsThenInsertIfNew_fst, containsThenInsertIfNew_fst h]

theorem containsThenInsertIfNew_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v h.balanced).2.impl = (t.insertIfNew k v h.balanced).impl := by
  rw [containsThenInsertIfNew_snd_eq_insertIfNew]

theorem containsThenInsertIfNew!_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew! k v).2 = t.insertIfNew! k v := by
  rw [containsThenInsertIfNew!_snd_eq_containsThenInsertIfNew_snd _ h.balanced, containsThenInsertIfNew_snd h,
    insertIfNew_eq_insertIfNew!]

theorem isEmpty_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.isEmpty = false := by
  simp_to_model [insertIfNew, isEmpty] using List.isEmpty_insertEntryIfNew

theorem isEmpty_insertIfNew! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).isEmpty = false := by
  simpa only [insertIfNew_eq_insertIfNew!] using isEmpty_insertIfNew h

theorem contains_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a = (k == a || t.contains a) := by
  simp_to_model [insertIfNew, contains] using List.containsKey_insertEntryIfNew

theorem contains_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).contains a = (k == a || t.contains a) := by
  simpa only [insertIfNew_eq_insertIfNew!] using contains_insertIfNew h

theorem mem_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl ↔ compare k a = .eq ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insertIfNew, h, beq_eq]

theorem mem_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew! k v ↔ compare k a = .eq ∨ a ∈ t := by
  simpa only [insertIfNew_eq_insertIfNew!] using mem_insertIfNew h

theorem contains_insertIfNew_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains k := by
  simp [contains_insertIfNew, h]

theorem contains_insertIfNew!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).contains k := by
  simpa only [insertIfNew_eq_insertIfNew!] using contains_insertIfNew_self h

theorem mem_insertIfNew_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ (t.insertIfNew k v h.balanced).impl := by
  simp [mem_insertIfNew, h]

theorem mem_insertIfNew!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNew! k v := by
  simpa only [insertIfNew_eq_insertIfNew!] using mem_insertIfNew_self h

theorem contains_of_contains_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a → compare k a ≠ .eq → t.contains a := by
  simp_to_model [insertIfNew, contains] using List.containsKey_of_containsKey_insertEntryIfNew

theorem contains_of_contains_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).contains a → compare k a ≠ .eq → t.contains a := by
  simpa only [insertIfNew_eq_insertIfNew!] using contains_of_contains_insertIfNew h

theorem mem_of_mem_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl → compare k a ≠ .eq → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew h

theorem mem_of_mem_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew! k v → compare k a ≠ .eq → a ∈ t := by
  simpa only [insertIfNew_eq_insertIfNew!] using mem_of_mem_insertIfNew h

theorem size_insertIfNew [TransOrd α] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v h.balanced).impl.size = if k ∈ t then t.size else t.size + 1 := by
  simp_to_model [insertIfNew, size, contains] using List.length_insertEntryIfNew

theorem size_insertIfNew! [TransOrd α] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew! k v).size = if k ∈ t then t.size else t.size + 1 := by
  simpa only [insertIfNew_eq_insertIfNew!] using size_insertIfNew h

theorem size_le_size_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v h.balanced).impl.size := by
  simp_to_model [insertIfNew, size] using List.length_le_length_insertEntryIfNew

theorem size_le_size_insertIfNew! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew! k v).size := by
  simpa only [insertIfNew_eq_insertIfNew!] using size_le_size_insertIfNew h

theorem size_insertIfNew_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.size ≤ t.size + 1 := by
  simp_to_model [insertIfNew, size] using List.length_insertEntryIfNew_le

theorem size_insertIfNew!_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).size ≤ t.size + 1 := by
  simpa only [insertIfNew_eq_insertIfNew!] using size_insertIfNew_le h

theorem get?_empty [TransOrd α] [LawfulEqOrd α] {a : α} : (empty : Impl α β).get? a = none := by
  simp_to_model [get?] using List.getValueCast?_nil

theorem get?_of_isEmpty [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none := by
  simp_to_model [get?, isEmpty]; empty

theorem get?_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v h.balanced).impl.get? a =
      if h : compare k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a := by
  simp_to_model [insert, get?] using List.getValueCast?_insertEntry

theorem get?_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert! k v).get? a =
      if h : compare k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a := by
  simpa only [insert_eq_insert!] using get?_insert h

theorem get?_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.get? k = some v := by
  simp_to_model [insert, get?] using List.getValueCast?_insertEntry_self

theorem get?_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).get? k = some v := by
  simpa only [insert_eq_insert!] using get?_insert_self h

theorem contains_eq_isSome_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome := by
  simp_to_model [contains, get?] using List.containsKey_eq_isSome_getValueCast?

theorem mem_iff_isSome_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.get? a).isSome := by
  simpa [mem_iff_contains] using contains_eq_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none := by
  simp_to_model [contains, get?] using List.getValueCast?_eq_none

theorem get?_eq_none [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.get? a = if compare k a = .eq then none else t.get? a := by
  simp_to_model [erase, get?] using List.getValueCast?_eraseKey

theorem get?_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).get? a = if compare k a = .eq then none else t.get? a := by
  simpa only [erase_eq_erase!] using get?_erase h

theorem get?_erase_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.get? k = none := by
  simp_to_model [erase, get?] using List.getValueCast?_eraseKey_self

theorem get?_erase!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} :
    (t.erase! k).get? k = none := by
  simpa only [erase_eq_erase!] using get?_erase_self h

namespace Const

variable {β : Type v} {t : Impl α β}

theorem get?_empty [TransOrd α] {a : α} : get? (empty : Impl α β) a = none := by
  simp_to_model [Const.get?] using List.getValue?_nil

theorem get?_of_isEmpty [TransOrd α] (h : t.WF) {a : α} :
    t.isEmpty = true → get? t a = none := by
  simp_to_model [Const.get?, isEmpty]; empty

theorem get?_insert [TransOrd α] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert k v h.balanced).impl a =
      if compare k a = .eq then some v else get? t a := by
  simp_to_model [Const.get?, insert] using List.getValue?_insertEntry

theorem get?_insert! [TransOrd α] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert! k v) a =
      if compare k a = .eq then some v else get? t a := by
  simpa only [insert_eq_insert!] using get?_insert h

theorem get?_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get? (t.insert k v h.balanced).impl k = some v := by
  simp_to_model [Const.get?, insert] using List.getValue?_insertEntry_self

theorem get?_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get? (t.insert! k v) k = some v := by
  simpa only [insert_eq_insert!] using get?_insert_self h

theorem contains_eq_isSome_get? [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = (get? t a).isSome := by
  simp_to_model [Const.get?, contains] using List.containsKey_eq_isSome_getValue?

theorem mem_iff_isSome_get? [TransOrd α] (h : t.WF) {a : α} :
    a ∈ t ↔ (get? t a).isSome := by
  simpa [mem_iff_contains] using contains_eq_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = false → get? t a = none := by
  simp_to_model [Const.get?, contains] using List.getValue?_eq_none.mpr

theorem get?_eq_none [TransOrd α] (h : t.WF) {a : α} :
    ¬ a ∈ t → get? t a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [TransOrd α] (h : t.WF) {k a : α} :
    get? (t.erase k h.balanced).impl a = if compare k a = .eq then none else get? t a := by
  simp_to_model [Const.get?, erase] using List.getValue?_eraseKey

theorem get?_erase! [TransOrd α] (h : t.WF) {k a : α} :
    get? (t.erase! k) a = if compare k a = .eq then none else get? t a := by
  simpa only [erase_eq_erase!] using get?_erase h

theorem get?_erase_self [TransOrd α] (h : t.WF) {k : α} :
    get? (t.erase k h.balanced).impl k = none := by
  simp_to_model [Const.get?, erase] using List.getValue?_eraseKey_self

theorem get?_erase!_self [TransOrd α] (h : t.WF) {k : α} :
    get? (t.erase! k) k = none := by
  simpa only [erase_eq_erase!] using get?_erase_self h

theorem get?_eq_get? [LawfulEqOrd α] [TransOrd α] (h : t.WF) {a : α} : get? t a = t.get? a := by
  simp_to_model [Const.get?, get?] using List.getValue?_eq_getValueCast?

theorem get?_congr [TransOrd α] (h : t.WF) {a b : α} : (hab : compare a b = .eq) →
    get? t a = get? t b := by
  simp_to_model [Const.get?] using List.getValue?_congr

end Const

theorem get_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v h.balanced).impl.get a h₁ =
      if h₂ : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (contains_of_contains_insert h h₁ h₂) := by
  simp_to_model [insert, get] using List.getValueCast_insertEntry

theorem get_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert! k v).get a h₁ =
      if h₂ : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (contains_of_contains_insert! h h₁ h₂) := by
  simpa only [insert_eq_insert!] using get_insert h (h₁ := by simpa [insert_eq_insert!])

theorem get_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.get k (contains_insert_self h) = v := by
  simp_to_model [insert, get] using List.getValueCast_insertEntry_self

theorem get_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).get k (contains_insert!_self h) = v := by
  simpa only [insert_eq_insert!] using get_insert_self h

@[simp]
theorem get_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase k h.balanced).impl.get a h' = t.get a (contains_of_contains_erase h h') := by
  simp_to_model [erase, get] using List.getValueCast_eraseKey

theorem get_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase! k).get a h' = t.get a (contains_of_contains_erase! h h') := by
  simpa only [erase_eq_erase!] using get_erase h (h' := by simpa [erase_eq_erase!])

theorem get?_eq_some_get [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {h'} : t.get? a = some (t.get a h') := by
  simp_to_model [get?, get] using List.getValueCast?_eq_some_getValueCast

namespace Const

variable {β : Type v} {t : Impl α β} (h : t.WF)

theorem get_insert [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert k v h.balanced).impl a h₁ =
      if h₂ : compare k a = .eq then v
      else get t a (contains_of_contains_insert h h₁ h₂) := by
  simp_to_model [insert, Const.get] using List.getValue_insertEntry

theorem get_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert! k v) a h₁ =
      if h₂ : compare k a = .eq then v
      else get t a (contains_of_contains_insert! h h₁ h₂) := by
  simpa only [insert_eq_insert!] using get_insert h (h₁ := by simpa [insert_eq_insert!])

theorem get_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v h.balanced).impl k (contains_insert_self h) = v := by
  simp_to_model [insert, Const.get] using List.getValue_insertEntry_self

theorem get_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get (t.insert! k v) k (contains_insert!_self h) = v := by
  simpa only [insert_eq_insert!] using get_insert_self h

@[simp]
theorem get_erase [TransOrd α] (h : t.WF) {k a : α} {h'} :
    get (t.erase k h.balanced).impl a h' = get t a (contains_of_contains_erase h h') := by
  simp_to_model [erase, Const.get] using List.getValue_eraseKey

theorem get_erase! [TransOrd α] (h : t.WF) {k a : α} {h'} :
    get (t.erase! k) a h' = get t a (contains_of_contains_erase! h h') := by
  simpa only [erase_eq_erase!] using get_erase h (h' := by simpa [erase_eq_erase!])

theorem get?_eq_some_get [TransOrd α] (h : t.WF) {a : α} {h} :
    get? t a = some (get t a h) := by
  simp_to_model [Const.get, Const.get?] using List.getValue?_eq_some_getValue

theorem get_eq_get [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {h} : get t a h = t.get a h := by
  simp_to_model [Const.get, get] using List.getValue_eq_getValueCast

theorem get_congr [TransOrd α] (h : t.WF) {a b : α} : (hab : compare a b = .eq) → {h' : _} →
    get t a h' = get t b ((contains_congr h hab).symm.trans h') := by
  simp_to_model [Const.get, contains] using List.getValue_congr

end Const

theorem get!_empty [TransOrd α] [LawfulEqOrd α] {a : α} [Inhabited (β a)] :
    get! (empty : Impl α β) a = default := by
  simp_to_model [get!] using List.getValueCast!_nil

theorem get!_of_isEmpty [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default := by
  simp_to_model [isEmpty, get!]; empty

theorem get!_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insert k v h.balanced).impl.get! a =
      if h : compare k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a := by
  simp_to_model [insert, get!] using List.getValueCast!_insertEntry

theorem get!_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insert! k v).get! a =
      if h : compare k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a := by
  simpa only [insert_eq_insert!] using get!_insert h

theorem get!_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (t.insert a b h.balanced).impl.get! a = b := by
  simp_to_model [insert, get!] using List.getValueCast!_insertEntry_self

theorem get!_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (t.insert! a b).get! a = b := by
  simpa only [insert_eq_insert!] using get!_insert_self h

theorem get!_eq_default_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default := by
  simp_to_model [contains, get!] using List.getValueCast!_eq_default

theorem get!_eq_default [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase k h.balanced).impl.get! a = if compare k a = .eq then default else t.get! a := by
  simp_to_model [erase, get!] using List.getValueCast!_eraseKey

theorem get!_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase! k).get! a = if compare k a = .eq then default else t.get! a := by
  simpa only [erase_eq_erase!] using get!_erase h

theorem get!_erase_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase k h.balanced).impl.get! k = default := by
  simp_to_model [erase, get!] using List.getValueCast!_eraseKey_self

theorem get!_erase!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase! k).get! k = default := by
  simpa only [erase_eq_erase!] using get!_erase_self h

theorem get?_eq_some_get!_of_contains [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.contains a = true → t.get? a = some (t.get! a) := by
  simp_to_model [contains, get?, get!] using List.getValueCast?_eq_some_getValueCast!

theorem get?_eq_some_get! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! := by
  simp_to_model [get!, get?] using List.getValueCast!_eq_getValueCast?

theorem get_eq_get! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] {h} :
    t.get a h = t.get! a := by
  simp_to_model [get, get!] using List.getValueCast_eq_getValueCast!

namespace Const

variable {β : Type v} {t : Impl α β} (h : t.WF)

theorem get!_empty [TransOrd α] [Inhabited β] {a : α} :
    get! (empty : Impl α β) a = default := by
  simp_to_model [Const.get!] using List.getValue!_nil

theorem get!_of_isEmpty [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → get! t a = default := by
  simp_to_model [Const.get!, isEmpty]; empty

theorem get!_insert [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v h.balanced).impl a = if compare k a = .eq then v else get! t a := by
  simp_to_model [insert, Const.get!] using List.getValue!_insertEntry

theorem get!_insert! [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert! k v) a = if compare k a = .eq then v else get! t a := by
  simpa only [insert_eq_insert!] using get!_insert h

theorem get!_insert_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α}
    {v : β} : get! (t.insert k v h.balanced).impl k = v := by
  simp_to_model [insert, Const.get!] using List.getValue!_insertEntry_self

theorem get!_insert!_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α}
    {v : β} : get! (t.insert! k v) k = v := by
  simpa only [insert_eq_insert!] using get!_insert_self h

theorem get!_eq_default_of_contains_eq_false [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → get! t a = default := by
  simp_to_model [contains, Const.get!] using List.getValue!_eq_default

theorem get!_eq_default [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → get! t a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k h.balanced).impl a = if compare k a = .eq then default else get! t a := by
  simp_to_model [erase, Const.get!] using List.getValue!_eraseKey

theorem get!_erase! [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase! k) a = if compare k a = .eq then default else get! t a := by
  simpa only [erase_eq_erase!] using get!_erase h

theorem get!_erase_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k h.balanced).impl k = default := by
  simp_to_model [erase, Const.get!] using List.getValue!_eraseKey_self

theorem get!_erase!_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase! k) k = default := by
  simpa only [erase_eq_erase!] using get!_erase_self h

theorem get?_eq_some_get!_of_contains [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → get? t a = some (get! t a) := by
  simp_to_model [contains, Const.get?, Const.get!] using List.getValue?_eq_some_getValue!

theorem get?_eq_some_get! [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → get? t a = some (get! t a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = (get? t a).get! := by
  simp_to_model [Const.get!, Const.get?] using List.getValue!_eq_getValue?

theorem get_eq_get! [TransOrd α] [Inhabited β] (h : t.WF) {a : α} {h} :
    get t a h = get! t a := by
  simp_to_model [Const.get, Const.get!] using List.getValue_eq_getValue!

theorem get!_eq_get! [TransOrd α] [LawfulEqOrd α] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = t.get! a := by
  simp_to_model [Const.get!, get!] using List.getValue!_eq_getValueCast!

theorem get!_congr [TransOrd α] [Inhabited β] (h : t.WF) {a b : α} :
    (hab : compare a b = .eq) → get! t a = get! t b := by
  simp_to_model [Const.get!] using List.getValue!_congr

end Const

theorem getD_empty [TransOrd α] [LawfulEqOrd α] {a : α} {fallback : β a} :
    (empty : Impl α β).getD a fallback = fallback := by
  simp [getD, empty]

theorem getD_of_isEmpty [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} : t.isEmpty = true → t.getD a fallback = fallback := by
  simp_to_model [getD, isEmpty]; empty

theorem getD_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v h.balanced).impl.getD a fallback =
      if h : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback := by
  simp_to_model [insert, getD] using List.getValueCastD_insertEntry

theorem getD_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert! k v).getD a fallback =
      if h : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback := by
  simpa only [insert_eq_insert!] using getD_insert h

theorem getD_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert a b h.balanced).impl.getD a fallback = b := by
  simp_to_model [insert, getD] using List.getValueCastD_insertEntry_self

theorem getD_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert! a b).getD a fallback = b := by
  simpa only [insert_eq_insert!] using getD_insert_self h

theorem getD_eq_fallback_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = false → t.getD a fallback = fallback := by
  simp_to_model [contains, getD] using List.getValueCastD_eq_fallback

theorem getD_eq_fallback [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase k h.balanced).impl.getD a fallback = if compare k a = .eq then fallback else t.getD a fallback := by
  simp_to_model [erase, getD] using List.getValueCastD_eraseKey

theorem getD_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase! k).getD a fallback = if compare k a = .eq then fallback else t.getD a fallback := by
  simpa only [erase_eq_erase!] using getD_erase h

theorem getD_erase_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase k h.balanced).impl.getD k fallback = fallback := by
  simp_to_model [erase, getD] using List.getValueCastD_eraseKey_self

theorem getD_erase!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase! k).getD k fallback = fallback := by
  simpa only [erase_eq_erase!] using getD_erase_self h

theorem get?_eq_some_getD_of_contains [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = true → t.get? a = some (t.getD a fallback) := by
  simp_to_model [contains, get?, getD] using List.getValueCast?_eq_some_getValueCastD

theorem get?_eq_some_getD [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback := by
  simp_to_model [getD, get?] using List.getValueCastD_eq_getValueCast?

theorem get_eq_getD [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} {h} :
    t.get a h = t.getD a fallback := by
  simp_to_model [get, getD] using List.getValueCast_eq_getValueCastD

theorem get!_eq_getD_default [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default := by
  simp_to_model [get!, getD] using List.getValueCast!_eq_getValueCastD_default

namespace Const

variable {β : Type v} {t : Impl α β} (h : t.WF)

theorem getD_empty [TransOrd α] {a : α} {fallback : β} :
    getD (empty : Impl α β) a fallback = fallback := by
  simp_to_model [Const.getD] using List.getValueD_nil

theorem getD_of_isEmpty [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback := by
  simp_to_model [isEmpty, Const.getD]; empty

theorem getD_insert [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v h.balanced).impl a fallback = if compare k a = .eq then v else getD t a fallback := by
  simp_to_model [insert, Const.getD] using List.getValueD_insertEntry

theorem getD_insert! [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert! k v) a fallback = if compare k a = .eq then v else getD t a fallback := by
  simpa only [insert_eq_insert!] using getD_insert h

theorem getD_insert_self [TransOrd α] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v h.balanced).impl k fallback = v := by
  simp_to_model [insert, Const.getD] using List.getValueD_insertEntry_self

theorem getD_insert!_self [TransOrd α] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert! k v) k fallback = v := by
  simpa only [insert_eq_insert!] using getD_insert_self h

theorem getD_eq_fallback_of_contains_eq_false [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback := by
  simp_to_model [contains, Const.getD] using List.getValueD_eq_fallback

theorem getD_eq_fallback [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [TransOrd α] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k h.balanced).impl a fallback = if compare k a = .eq then
      fallback
    else
      getD t a fallback := by
  simp_to_model [erase, Const.getD] using List.getValueD_eraseKey

theorem getD_erase! [TransOrd α] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase! k) a fallback = if compare k a = .eq then
      fallback
    else
      getD t a fallback := by
  simpa only [erase_eq_erase!] using getD_erase h

theorem getD_erase_self [TransOrd α] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k h.balanced).impl k fallback = fallback := by
  simp_to_model [erase, Const.getD] using List.getValueD_eraseKey_self

theorem getD_erase!_self [TransOrd α] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase! k) k fallback = fallback := by
  simpa only [erase_eq_erase!] using getD_erase_self h

theorem get?_eq_some_getD_of_contains [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) := by
  simp_to_model [contains, Const.get?, Const.getD] using List.getValue?_eq_some_getValueD

theorem get?_eq_some_getD [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback := by
  simp_to_model [Const.getD, Const.get?] using List.getValueD_eq_getValue?

theorem get_eq_getD [TransOrd α] (h : t.WF) {a : α} {fallback : β} {h} :
    get t a h = getD t a fallback := by
  simp_to_model [Const.get, Const.getD] using List.getValue_eq_getValueD

theorem get!_eq_getD_default [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = getD t a default := by
  simp_to_model [Const.get!, Const.getD] using List.getValue!_eq_getValueD_default

theorem getD_eq_getD [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback := by
  simp_to_model [Const.getD, getD] using List.getValueD_eq_getValueCastD

theorem getD_congr [TransOrd α] (h : t.WF) {a b : α} {fallback : β} :
    (hab : compare a b = .eq) → getD t a fallback = getD t b fallback := by
  simp_to_model [Const.getD] using List.getValueD_congr

end Const

theorem getKey?_empty {a : α} : (empty : Impl α β).getKey? a = none := by
  rfl

theorem getKey?_of_isEmpty [TransOrd α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none := by
  simp_to_model [getKey?, isEmpty]; empty

theorem getKey?_insert [TransOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKey? a = if compare k a = .eq then some k else t.getKey? a := by
  simp_to_model [insert, getKey?] using List.getKey?_insertEntry

theorem getKey?_insert! [TransOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert! k v).getKey? a = if compare k a = .eq then some k else t.getKey? a := by
  simpa only [insert_eq_insert!] using getKey?_insert h

theorem getKey?_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKey? k = some k := by
  simp_to_model [insert, getKey?] using List.getKey?_insertEntry_self

theorem getKey?_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).getKey? k = some k := by
  simpa only [insert_eq_insert!] using getKey?_insert_self h

theorem contains_eq_isSome_getKey? [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome := by
  simp_to_model [contains, getKey?] using List.containsKey_eq_isSome_getKey?

theorem mem_iff_isSome_getKey? [TransOrd α] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome := by
  simpa [mem_iff_contains] using contains_eq_isSome_getKey? h

theorem getKey?_eq_none_of_contains_eq_false [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none := by
  simp_to_model [contains, getKey?] using List.getKey?_eq_none

theorem getKey?_eq_none [TransOrd α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none := by
  simpa [mem_iff_contains] using getKey?_eq_none_of_contains_eq_false h

theorem getKey?_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.getKey? a = if compare k a = .eq then none else t.getKey? a := by
  simp_to_model [erase, getKey?] using List.getKey?_eraseKey

theorem getKey?_erase! [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).getKey? a = if compare k a = .eq then none else t.getKey? a := by
  simpa only [erase_eq_erase!] using getKey?_erase h

theorem getKey?_erase_self [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.getKey? k = none := by
  simp_to_model [erase, getKey?] using List.getKey?_eraseKey_self

theorem getKey?_erase!_self [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).getKey? k = none := by
  simpa only [erase_eq_erase!] using getKey?_erase_self h

theorem compare_getKey?_self [TransOrd α] (h : t.WF) {k : α} :
    (t.getKey? k).all (compare · k = .eq) := by
  simp only [compare_eq_iff_beq, Bool.decide_eq_true]
  simp_to_model using List.getKey?_beq

theorem getKey?_congr [TransOrd α] (h : t.WF) {k k' : α} (h' : compare k k' = .eq) :
    t.getKey? k = t.getKey? k' := by
  simp_to_model using List.getKey?_congr <| compare_eq_iff_beq.mp h'

theorem getKey?_eq_some_of_contains [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {k : α} : (h' : t.contains k) → t.getKey? k = some k := by
  simp_to_model using List.getKey?_eq_some

theorem getKey?_eq_some [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    (h' : k ∈ t) : t.getKey? k = some k :=
  getKey?_eq_some_of_contains h h'

theorem getKey_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v h.balanced).impl.getKey a h₁ =
      if h₂ : compare k a = .eq then
        k
      else
        t.getKey a (contains_of_contains_insert h h₁ h₂) := by
  simp_to_model [insert, getKey] using List.getKey_insertEntry

theorem getKey_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert! k v).getKey a h₁ =
      if h₂ : compare k a = .eq then
        k
      else
        t.getKey a (contains_of_contains_insert! h h₁ h₂) := by
  simpa only [insert_eq_insert!] using getKey_insert h (h₁ := by simpa [insert_eq_insert!])

theorem getKey_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKey k (contains_insert_self h) = k := by
  simp_to_model [insert, getKey] using List.getKey_insertEntry_self

theorem getKey_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).getKey k (contains_insert!_self h) = k := by
  simpa only [insert_eq_insert!] using getKey_insert_self h

@[simp]
theorem getKey_erase [TransOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase k h.balanced).impl.getKey a h' = t.getKey a (contains_of_contains_erase h h') := by
  simp_to_model [erase, getKey] using List.getKey_eraseKey

@[simp]
theorem getKey_erase! [TransOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase! k).getKey a h' = t.getKey a (contains_of_contains_erase! h h') := by
  simpa only [erase_eq_erase!] using getKey_erase h (h' := by simpa [erase_eq_erase!])

theorem getKey?_eq_some_getKey [TransOrd α] (h : t.WF) {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') := by
  simp_to_model [getKey?, getKey] using List.getKey?_eq_some_getKey

theorem compare_getKey_self [TransOrd α] (h : t.WF) {k : α} (h' : k ∈ t) :
    compare (t.getKey k h') k = .eq := by
  simp_to_model using List.getKey_beq

theorem getKey_congr [TransOrd α] (h : t.WF) {k₁ k₂ : α} (h' : compare k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h h').mp h₁) := by
  simp_to_model using List.getKey_congr <| compare_eq_iff_beq.mp h'

theorem getKey_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} :
    (h' : k ∈ t) → t.getKey k h' = k := by
  simp_to_model using List.getKey_eq

theorem getKey!_empty {a : α} [Inhabited α] :
    (empty : Impl α β).getKey! a = default := by
  simp only [empty, getKey!]; rfl

theorem getKey!_of_isEmpty [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default := by
  simp_to_model [isEmpty, getKey!]; empty

theorem getKey!_insert [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insert k v h.balanced).impl.getKey! a = if compare k a = .eq then k else t.getKey! a := by
  simp_to_model [insert, getKey!] using List.getKey!_insertEntry

theorem getKey!_insert! [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insert! k v).getKey! a = if compare k a = .eq then k else t.getKey! a := by
  simpa only [insert_eq_insert!] using getKey!_insert h

theorem getKey!_insert_self [TransOrd α] [Inhabited α] (h : t.WF) {a : α}
    {b : β a} : (t.insert a b h.balanced).impl.getKey! a = a := by
  simp_to_model [insert, getKey!] using List.getKey!_insertEntry_self

theorem getKey!_insert!_self [TransOrd α] [Inhabited α] (h : t.WF) {a : α}
    {b : β a} : (t.insert! a b).getKey! a = a := by
  simpa only [insert_eq_insert!] using getKey!_insert_self h

theorem getKey!_eq_default_of_contains_eq_false [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey! a = default := by
  simp_to_model [contains, getKey!] using List.getKey!_eq_default

theorem getKey!_eq_default [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey! a = default := by
  simpa [mem_iff_contains] using getKey!_eq_default_of_contains_eq_false h

theorem getKey!_erase [TransOrd α] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.getKey! a = if compare k a = .eq then default else t.getKey! a := by
  simp_to_model [erase, getKey!] using List.getKey!_eraseKey

theorem getKey!_erase! [TransOrd α] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase! k).getKey! a = if compare k a = .eq then default else t.getKey! a := by
  simpa only [erase_eq_erase!] using getKey!_erase h

theorem getKey!_erase_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.getKey! k = default := by
  simp_to_model [erase, getKey!] using List.getKey!_eraseKey_self

theorem getKey!_erase!_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase! k).getKey! k = default := by
  simpa only [erase_eq_erase!] using getKey!_erase_self h

theorem getKey?_eq_some_getKey!_of_contains [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) := by
  simp_to_model [contains, getKey?, getKey!] using List.getKey?_eq_some_getKey!

theorem getKey?_eq_some_getKey! [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKey!_of_contains h

theorem getKey!_eq_get!_getKey? [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = (t.getKey? a).get! := by
  simp_to_model [getKey?, getKey!] using List.getKey!_eq_getKey?

theorem getKey_eq_getKey! [TransOrd α] [Inhabited α] (h : t.WF) {a : α} {h} :
    t.getKey a h = t.getKey! a := by
  simp_to_model [getKey, getKey!] using List.getKey_eq_getKey!

theorem getKey!_congr [TransOrd α] [Inhabited α] (h : t.WF) {k k' : α} :
    (h' : compare k k' = .eq) → t.getKey! k = t.getKey! k' := by
  simp_to_model using List.getKey!_congr

theorem getKey!_eq_of_contains [TransOrd α] [LawfulEqOrd α] [Inhabited α]
    (h : t.WF) {k : α} : (h' : t.contains k) → t.getKey! k = k := by
  simp_to_model using List.getKey!_eq_of_containsKey

theorem getKey!_eq_of_mem [TransOrd α] [LawfulEqOrd α] [Inhabited α]
    (h : t.WF) {k : α} : (h' : k ∈ t) → t.getKey! k = k := by
  simpa [mem_iff_contains] using getKey!_eq_of_contains h

theorem getKeyD_empty {a : α} {fallback : α} :
    (empty : Impl α β).getKeyD a fallback = fallback := by
  simp [getKeyD, empty]

theorem getKeyD_of_isEmpty [TransOrd α] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback := by
  simp_to_model [isEmpty, getKeyD]; empty

theorem getKeyD_insert [TransOrd α] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKeyD a fallback =
      if compare k a = .eq then k else t.getKeyD a fallback := by
  simp_to_model [insert, getKeyD] using List.getKeyD_insertEntry

theorem getKeyD_insert! [TransOrd α] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert! k v).getKeyD a fallback =
      if compare k a = .eq then k else t.getKeyD a fallback := by
  simpa only [insert_eq_insert!] using getKeyD_insert h

theorem getKeyD_insert_self [TransOrd α] (h : t.WF) {a fallback : α}
    {b : β a} :
    (t.insert a b h.balanced).impl.getKeyD a fallback = a := by
  simp_to_model [insert, getKeyD] using List.getKeyD_insertEntry_self

theorem getKeyD_insert!_self [TransOrd α] (h : t.WF) {a fallback : α}
    {b : β a} :
    (t.insert! a b).getKeyD a fallback = a := by
  simpa only [insert_eq_insert!] using getKeyD_insert_self h

theorem getKeyD_eq_fallback_of_contains_eq_false [TransOrd α] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback := by
  simp_to_model [contains, getKeyD] using List.getKeyD_eq_fallback

theorem getKeyD_eq_fallback [TransOrd α] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback := by
  simpa [mem_iff_contains] using getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_erase [TransOrd α] (h : t.WF) {k a fallback : α} :
    (t.erase k h.balanced).impl.getKeyD a fallback =
      if compare k a = .eq then fallback else t.getKeyD a fallback := by
  simp_to_model [erase, getKeyD] using List.getKeyD_eraseKey

theorem getKeyD_erase! [TransOrd α] (h : t.WF) {k a fallback : α} :
    (t.erase! k).getKeyD a fallback =
      if compare k a = .eq then fallback else t.getKeyD a fallback := by
  simpa only [erase_eq_erase!] using getKeyD_erase h

theorem getKeyD_erase_self [TransOrd α] (h : t.WF) {k fallback : α} :
    (t.erase k h.balanced).impl.getKeyD k fallback = fallback := by
  simp_to_model [erase, getKeyD] using List.getKeyD_eraseKey_self

theorem getKeyD_erase!_self [TransOrd α] (h : t.WF) {k fallback : α} :
    (t.erase! k).getKeyD k fallback = fallback := by
  simpa only [erase_eq_erase!] using getKeyD_erase_self h

theorem getKey?_eq_some_getKeyD_of_contains [TransOrd α] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) := by
  simp_to_model [contains, getKeyD, getKey?] using List.getKey?_eq_some_getKeyD

theorem getKey?_eq_some_getKeyD [TransOrd α] (h : t.WF) {a fallback : α} :
    a ∈ t → t.getKey? a = some (t.getKeyD a fallback) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKeyD_of_contains h

theorem getKeyD_eq_getD_getKey? [TransOrd α] (h : t.WF) {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback := by
  simp_to_model [getKey?, getKeyD] using List.getKeyD_eq_getKey?

theorem getKey_eq_getKeyD [TransOrd α] (h : t.WF) {a fallback : α} {h} :
    t.getKey a h = t.getKeyD a fallback := by
  simp_to_model [getKey, getKeyD] using List.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [TransOrd α] [Inhabited α] (h : t.WF)
    {a : α} :
    t.getKey! a = t.getKeyD a default := by
  simp_to_model [getKey!, getKeyD] using List.getKey!_eq_getKeyD_default

theorem getKeyD_congr [TransOrd α] (h : t.WF) {k k' fallback : α} :
    (h' : compare k k' = .eq) → t.getKeyD k fallback = t.getKeyD k' fallback := by
  simp_to_model using List.getKeyD_congr

theorem getKeyD_eq_of_contains [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {k fallback : α} : (h' : t.contains k) → t.getKeyD k fallback = k := by
  simp_to_model using List.getKeyD_eq_of_containsKey

theorem getKeyD_eq_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {k fallback : α} (h' : k ∈ t) : t.getKeyD k fallback = k :=
  getKeyD_eq_of_contains h h'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransOrd α] (h : t.WF) {k a : α}
    {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl →
      ¬ (compare k a = .eq ∧ ¬ k ∈ t) → a ∈ t := by
  simp_to_model [insertIfNew, contains] using List.containsKey_of_containsKey_insertEntryIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew!` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew!`. -/
theorem mem_of_mem_insertIfNew!' [TransOrd α] (h : t.WF) {k a : α}
    {v : β k} :
    a ∈ (t.insertIfNew! k v) → ¬ (compare k a = .eq ∧ ¬ k ∈ t) → a ∈ t := by
  simpa only [insertIfNew_eq_insertIfNew!] using mem_of_mem_insertIfNew' h

theorem get?_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.get? a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a := by
  simp_to_model [insertIfNew, get?, contains] using List.getValueCast?_insertEntryIfNew

theorem get?_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).get? a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a := by
  simpa only [insertIfNew_eq_insertIfNew!] using get?_insertIfNew h

theorem get_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v h.balanced).impl.get a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp_to_model [insertIfNew, get, contains] using List.getValueCast_insertEntryIfNew

theorem get_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew! k v).get a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew!' h h₁ h₂) := by
  simpa only [insertIfNew_eq_insertIfNew!] using
    get_insertIfNew h (h₁ := by simpa [insertIfNew_eq_insertIfNew!])

theorem get!_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v h.balanced).impl.get! a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a := by
  simp_to_model [insertIfNew, get!, contains] using List.getValueCast!_insertEntryIfNew

theorem get!_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew! k v).get! a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a := by
  simpa only [insertIfNew_eq_insertIfNew!] using get!_insertIfNew h

theorem getD_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getD a fallback =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback := by
  simp_to_model [insertIfNew, getD, contains] using List.getValueCastD_insertEntryIfNew

theorem getD_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew! k v).getD a fallback =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback := by
  simpa only [insertIfNew_eq_insertIfNew!] using getD_insertIfNew h

namespace Const

variable {β : Type v} {t : Impl α β}

theorem get?_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew k v h.balanced).impl a =
      if compare k a = .eq ∧ ¬ k ∈ t then
        some v
      else
        get? t a := by
  simp_to_model [insertIfNew, Const.get?, contains] using List.getValue?_insertEntryIfNew

theorem get?_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew! k v) a =
      if compare k a = .eq ∧ ¬ k ∈ t then
        some v
      else
        get? t a := by
  simpa only [insertIfNew_eq_insertIfNew!] using get?_insertIfNew h

theorem get_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v h.balanced).impl a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp_to_model [insertIfNew, Const.get, contains] using List.getValue_insertEntryIfNew

theorem get_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew! k v) a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew!' h h₁ h₂) := by
  simpa only [insertIfNew_eq_insertIfNew!] using
    get_insertIfNew h (h₁ := by simpa [insertIfNew_eq_insertIfNew!])

theorem get!_insertIfNew [TransOrd α] [Inhabited β] (h : t.WF) {k a : α}
    {v : β} :
    get! (t.insertIfNew k v h.balanced).impl a =
      if compare k a = .eq ∧ ¬ k ∈ t then v else get! t a := by
  simp_to_model [insertIfNew, Const.get!, contains] using List.getValue!_insertEntryIfNew

theorem get!_insertIfNew! [TransOrd α] [Inhabited β] (h : t.WF) {k a : α}
    {v : β} :
    get! (t.insertIfNew! k v) a =
      if compare k a = .eq ∧ ¬ k ∈ t then v else get! t a := by
  simpa only [insertIfNew_eq_insertIfNew!] using get!_insertIfNew h

theorem getD_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v h.balanced).impl a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback := by
  simp_to_model [insertIfNew, Const.getD, contains] using List.getValueD_insertEntryIfNew

theorem getD_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew! k v) a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback := by
  simpa only [insertIfNew_eq_insertIfNew!] using getD_insertIfNew h

end Const

theorem getKey?_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getKey? a =
      if compare k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a := by
  simp_to_model [insertIfNew, getKey?, contains] using List.getKey?_insertEntryIfNew

theorem getKey?_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).getKey? a =
      if compare k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a := by
  simpa only [insertIfNew_eq_insertIfNew!] using getKey?_insertIfNew h

theorem getKey_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v h.balanced).impl.getKey a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp_to_model [insertIfNew, getKey, contains] using List.getKey_insertEntryIfNew

theorem getKey_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew! k v).getKey a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew!' h h₁ h₂) := by
  simpa only [insertIfNew_eq_insertIfNew!] using
    getKey_insertIfNew h (h₁ := by simpa [insertIfNew_eq_insertIfNew!])

theorem getKey!_insertIfNew [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getKey! a =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a := by
  simp_to_model [insertIfNew, getKey!, contains] using List.getKey!_insertEntryIfNew

theorem getKey!_insertIfNew! [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew! k v).getKey! a =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a := by
  simpa only [insertIfNew_eq_insertIfNew!] using getKey!_insertIfNew h

theorem getKeyD_insertIfNew [TransOrd α] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getKeyD a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback := by
  simp_to_model [insertIfNew, getKeyD, contains] using List.getKeyD_insertEntryIfNew

theorem getKeyD_insertIfNew! [TransOrd α] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew! k v).getKeyD a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback := by
  simpa only [insertIfNew_eq_insertIfNew!] using getKeyD_insertIfNew h

/-!
### getThenInsertIfNew?
-/

theorem getThenInsertIfNew?_fst [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v h.balanced).1 = t.get? k := by
  rw [getThenInsertIfNew?.eq_def]
  cases t.get? k <;> rfl

theorem getThenInsertIfNew?_snd [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v h.balanced).2 = (t.insertIfNew k v h.balanced).impl := by
  rw [getThenInsertIfNew?.eq_def]
  cases heq : t.get? k
  · rfl
  · rw [get?_eq_getValueCast? h.ordered] at heq
    rw [insertIfNew, contains_eq_containsKey h.ordered, List.containsKey_eq_isSome_getValueCast?, heq]
    rfl

/-!
### getThenInsertIfNew?!
-/

theorem getThenInsertIfNew?!_fst [TransOrd α] [LawfulEqOrd α] {k : α} {v : β k} :
    (t.getThenInsertIfNew?! k v).1 = t.get? k := by
  rw [getThenInsertIfNew?!.eq_def]
  cases t.get? k <;> rfl

theorem getThenInsertIfNew?!_snd [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew?! k v).2 = (t.insertIfNew! k v) := by
  rw [getThenInsertIfNew?!.eq_def]
  cases heq : t.get? k
  · rfl
  · rw [get?_eq_getValueCast? h.ordered] at heq
    rw [insertIfNew!, contains_eq_containsKey h.ordered, List.containsKey_eq_isSome_getValueCast?, heq]
    rfl

namespace Const

variable {β : Type v} {t : Impl α β}

/-!
### getThenInsertIfNew?
-/

theorem getThenInsertIfNew?_fst [TransOrd α] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v h.balanced).1 = get? t k := by
  rw [getThenInsertIfNew?.eq_def]
  cases get? t k <;> rfl

theorem getThenInsertIfNew?_snd [TransOrd α] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v h.balanced).2 = (t.insertIfNew k v h.balanced).impl := by
  rw [getThenInsertIfNew?.eq_def]
  cases heq : get? t k
  · rfl
  · rw [get?_eq_getValue? h.ordered] at heq
    rw [insertIfNew, contains_eq_containsKey h.ordered, List.containsKey_eq_isSome_getValue?, heq]
    rfl

/-!
### getThenInsertIfNew?!
-/

theorem getThenInsertIfNew?!_fst [TransOrd α] {k : α} {v : β} :
    (getThenInsertIfNew?! t k v).1 = get? t k := by
  rw [getThenInsertIfNew?!.eq_def]
  cases get? t k <;> rfl

theorem getThenInsertIfNew?!_snd [TransOrd α] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew?! t k v).2 = (t.insertIfNew! k v) := by
  rw [getThenInsertIfNew?!.eq_def]
  cases heq : get? t k
  · rfl
  · rw [get?_eq_getValue? h.ordered] at heq
    rw [insertIfNew!, contains_eq_containsKey h.ordered, List.containsKey_eq_isSome_getValue?, heq]
    rfl

end Const

theorem length_keys [TransOrd α] (h : t.WF) :
    t.keys.length = t.size := by
  simp_to_model [size, keys] using List.length_keys_eq_length

theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty := by
  simp_to_model [isEmpty, keys] using List.isEmpty_keys_eq_isEmpty

theorem contains_keys [BEq α] [beqOrd : LawfulBEqOrd α] [TransOrd α] {k : α} (h : t.WF) :
    t.keys.contains k = t.contains k := by
  simp_to_model [contains, keys] using (List.containsKey_eq_keys_contains).symm

theorem mem_keys [LawfulEqOrd α] [TransOrd α] {k : α} (h : t.WF) :
    k ∈ t.keys ↔ k ∈ t := by
  simpa only [mem_iff_contains, ← List.contains_iff, ← Bool.eq_iff_iff] using contains_keys h

theorem distinct_keys [TransOrd α] (h : t.WF) :
    t.keys.Pairwise (fun a b => ¬ compare a b = .eq) := by
  simp_to_model [keys] using h.ordered.distinctKeys.distinct

theorem map_fst_toList_eq_keys :
    t.toList.map Sigma.fst = t.keys := by
  simp_to_model [toList, keys] using (List.keys_eq_map ..).symm

theorem length_toList [TransOrd α] (h : t.WF) :
    t.toList.length = t.size := by
  simp_to_model [toList, size]

theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty := by
  simp_to_model [toList, isEmpty]

theorem mem_toList_iff_get?_eq_some [TransOrd α] [LawfulEqOrd α] {k : α} {v : β k} (h : t.WF) :
    ⟨k, v⟩ ∈ t.toList ↔ t.get? k = some v := by
  simp_to_model [toList, get?] using List.mem_iff_getValueCast?_eq_some

theorem find?_toList_eq_some_iff_get?_eq_some [TransOrd α] [LawfulEqOrd α] {k : α} {v : β k}
    (h : t.WF) :
    t.toList.find? (compare ·.1 k == .eq) = some ⟨k, v⟩ ↔ t.get? k = some v := by
  simp_to_model [toList, get?] using List.find?_eq_some_iff_getValueCast?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransOrd α] {k : α} (h : t.WF) :
    t.toList.find? (compare ·.1 k == .eq) = none ↔ t.contains k = false := by
  simp_to_model [toList, contains] using List.find?_eq_none_iff_containsKey_eq_false

theorem find?_toList_eq_none_iff_not_mem [TransOrd α] {k : α} (h : t.WF) :
    t.toList.find? (compare ·.1 k == .eq) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false h

theorem distinct_keys_toList [TransOrd α] (h : t.WF) :
    t.toList.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp_to_model [toList] using List.pairwise_fst_eq_false

namespace Const

variable {β : Type v} {t : Impl α β}

theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys := by
  simp_to_model [Const.toList, keys] using List.map_fst_map_toProd_eq_keys

theorem length_toList (h : t.WF) :
    (toList t).length = t.size := by
  simp_to_model [Const.toList, size] using List.length_map

theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff, isEmpty_eq_isEmpty, List.isEmpty_iff]
  simp_to_model [Const.toList, isEmpty] using List.map_eq_nil_iff

theorem mem_toList_iff_get?_eq_some [TransOrd α] [LawfulEqOrd α] {k : α} {v : β} (h : t.WF) :
    (k, v) ∈ toList t ↔ get? t k = some v := by
  simp_to_model [Const.toList, Const.get?] using List.mem_map_toProd_iff_getValue?_eq_some

theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [TransOrd α] {k : α} {v : β} (h : t.WF) :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ get? t k = some v := by
  simp_to_model [Const.toList, getKey?, Const.get?]
    using List.mem_map_toProd_iff_getKey?_eq_some_and_getValue?_eq_some

theorem get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransOrd α] {k : α} {v : β} (h : t.WF) :
    get? t k = some v ↔ ∃ (k' : α), compare k k' = .eq ∧ (k', v) ∈ toList t := by
  simp_to_model [Const.toList, Const.get?]
    using List.getValue?_eq_some_iff_exists_beq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransOrd α] {k k' : α} {v : β}
    (h : t.WF) : (toList t).find? (fun a => compare a.1 k == .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ get? t k = some v := by
  simp_to_model [Const.toList, getKey?, Const.get?]
    using List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransOrd α] {k : α} (h : t.WF) :
    (toList t).find? (compare ·.1 k == .eq) = none ↔ t.contains k = false := by
  simp_to_model [Const.toList, contains] using List.find?_map_eq_none_iff_containsKey_eq_false

theorem find?_toList_eq_none_iff_not_mem [TransOrd α] {k : α} (h : t.WF) :
    (toList t).find? (compare ·.1 k == .eq) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false h

theorem distinct_keys_toList [TransOrd α] (h : t.WF) :
    (toList t).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp_to_model [Const.toList] using List.pairwise_fst_eq_false_map_toProd

end Const

section monadic

variable {t : Impl α β} {δ : Type w} {m : Type w → Type w}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β a → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init := by
  simp_to_model [toList, foldlM]

theorem foldl_eq_foldl_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init := by
  simp_to_model [toList, foldl]

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init := by
  simp_to_model [toList, foldrM]

theorem foldr_eq_foldr_toList {f : (a : α) → β a → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init := by
  simp_to_model [toList, foldr]

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : (a : α) × β a → m PUnit} :
    t.forM (fun k v => f ⟨k, v⟩) = ForM.forM t.toList f := by
  simp_to_model [toList, forM] using rfl

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : (a : α) × β a → δ → m (ForInStep δ)} {init : δ} :
    t.forIn (fun k v => f ⟨k, v⟩) init = ForIn.forIn t.toList init f := by
  simp_to_model [toList, forIn]

theorem foldlM_eq_foldlM_keys [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init := by
  simp_to_model [foldlM, keys] using List.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init := by
  simp_to_model [foldl, keys] using List.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init := by
  simp_to_model [foldrM, keys] using List.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init := by
  simp_to_model [foldr, keys] using List.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    t.forM (fun a _ => f a) = t.keys.forM f := by
  simp_to_model [forM, keys] using List.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)}
    {init : δ} :
    t.forIn (fun a _ d => f a d) init = ForIn.forIn t.keys init f := by
  simp_to_model [forIn, keys] using List.forIn_eq_forIn_keys

namespace Const

variable {β : Type v} {t : Impl α β}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β → m δ} {init : δ} :
    t.foldlM f init = (Const.toList t).foldlM (fun a b => f a b.1 b.2) init := by
  simp_to_model [foldlM, Const.toList] using List.foldlM_eq_foldlM_toProd

theorem foldl_eq_foldl_toList {f : δ → (a : α) → β → δ} {init : δ} :
    t.foldl f init = (Const.toList t).foldl (fun a b => f a b.1 b.2) init := by
  simp_to_model [foldl, Const.toList] using List.foldl_eq_foldl_toProd

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m]
    {f : (a : α) → β → δ → m δ} {init : δ} :
    t.foldrM f init = (Const.toList t).foldrM (fun a b => f a.1 a.2 b) init := by
  simp_to_model [foldrM, Const.toList] using List.foldrM_eq_foldrM_toProd

theorem foldr_eq_foldr_toList {f : (a : α) → β → δ → δ} {init : δ} :
    t.foldr f init = (Const.toList t).foldr (fun a b => f a.1 a.2 b) init := by
  simp_to_model [foldr, Const.toList] using List.foldr_eq_foldr_toProd

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : (a : α) → β → m PUnit} :
    t.forM f = (Const.toList t).forM (fun a => f a.1 a.2) := by
  simp_to_model [forM, Const.toList] using List.forM_eq_forM_toProd

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn (Const.toList t) init (fun a b => f a.1 a.2 b) := by
  simp_to_model [forIn, Const.toList] using List.forIn_eq_forIn_toProd

end Const

end monadic

theorem insertMany_cons (h : t.WF) {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (t.insertMany (⟨k, v⟩ :: l) h.balanced).1 =
      ((t.insert k v h.balanced).impl.insertMany l h.insert.balanced).1 := by
  simp [insertMany_eq_foldl, insert_eq_insert!]

theorem insertMany!_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (t.insertMany! (⟨k, v⟩ :: l)).1 = ((t.insert! k v).insertMany! l).1 := by
  simp only [insertMany!_eq_foldl, List.foldl]

@[simp]
theorem contains_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany l h.balanced).1.contains k = (t.contains k || (l.map Sigma.fst).contains k) := by
  simp_to_model [insertMany, contains] using List.containsKey_insertList

@[simp]
theorem mem_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ (t.insertMany l h.balanced).1 ↔ k ∈ t ∨ (l.map Sigma.fst).contains k := by
  simp [mem_iff_contains, contains_insertMany_list h]

@[simp]
theorem contains_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany! l).1.contains k = (t.contains k || (l.map Sigma.fst).contains k) := by
  simpa only [insertMany_eq_insertMany!] using contains_insertMany_list h

@[simp]
theorem mem_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ (t.insertMany! l).1 ↔ k ∈ t ∨ (l.map Sigma.fst).contains k := by
  simpa only [insertMany_eq_insertMany!] using mem_insertMany_list h

theorem contains_of_contains_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany l h.balanced).1.contains k →
      (l.map Sigma.fst).contains k = false → t.contains k := by
  simp_to_model [insertMany, contains] using List.containsKey_of_containsKey_insertList

theorem mem_of_mem_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ (t.insertMany l h.balanced).1 → (l.map Sigma.fst).contains k = false → k ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertMany_list h

theorem contains_of_contains_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany! l).1.contains k → (l.map Sigma.fst).contains k = false → t.contains k := by
  simpa only [insertMany_eq_insertMany!] using contains_of_contains_insertMany_list h

theorem mem_of_mem_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ (t.insertMany! l).1 → (l.map Sigma.fst).contains k = false → k ∈ t := by
  simpa only [insertMany_eq_insertMany!] using mem_of_mem_insertMany_list h

theorem get?_insertMany_list_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] [BEq α]
    [LawfulBEqOrd α] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l h.balanced).1.get? k = t.get? k := by
  simp_to_model [insertMany, get?] using List.getValueCast?_insertList_of_contains_eq_false

theorem get?_insertMany!_list_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] [BEq α]
    [LawfulBEqOrd α] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany! l).1.get? k = t.get? k := by
  simpa only [insertMany_eq_insertMany!] using get?_insertMany_list_of_contains_eq_false h h'

theorem get?_insertMany_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    (t.insertMany l h.balanced).1.get? k' =
      some (cast (by congr; apply compare_eq_iff_eq.mp k_beq) v) := by
  simp_to_model [insertMany, get?] using List.getValueCast?_insertList_of_mem

theorem get?_insertMany!_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    (t.insertMany! l).1.get? k' = some (cast (by congr; apply compare_eq_iff_eq.mp k_beq) v) := by
  simpa only [insertMany_eq_insertMany!] using get?_insertMany_list_of_mem h

theorem get_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l h.balanced).1.get k h' =
    t.get k (contains_of_contains_insertMany_list h h' contains) := by
  simp_to_model [insertMany, get] using List.getValueCast_insertList_of_contains_eq_false

theorem get_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany! l).1.get k h' =
    t.get k (contains_of_contains_insertMany!_list h h' contains) := by
  simpa only [insertMany_eq_insertMany!] using
    get_insertMany_list_of_contains_eq_false h contains (h' := by simpa [insertMany_eq_insertMany!])

theorem get_insertMany_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    {h' : _} →
    (t.insertMany l h.balanced).1.get k' h' =
      cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  simp_to_model [insertMany, get, contains] using List.getValueCast_insertList_of_mem

theorem get_insertMany!_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    {h' : _} →
    (t.insertMany! l).1.get k' h' = cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  simpa only [insertMany_eq_insertMany!] using get_insertMany_list_of_mem h

theorem get!_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l h.balanced).1.get! k = t.get! k := by
  simp_to_model [insertMany, get!] using List.getValueCast!_insertList_of_contains_eq_false

theorem get!_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] (h : t.WF) {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany! l).1.get! k = t.get! k := by
  simpa only [insertMany_eq_insertMany!] using get!_insertMany_list_of_contains_eq_false h h'

theorem get!_insertMany_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    [Inhabited (β k')] →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    (t.insertMany l h.balanced).1.get! k' =
      cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  simp_to_model [insertMany, get!] using List.getValueCast!_insertList_of_mem

theorem get!_insertMany!_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    [Inhabited (β k')] →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    (t.insertMany! l).1.get! k' = cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  simpa only [insertMany_eq_insertMany!] using get!_insertMany_list_of_mem h

theorem getD_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] (h : t.WF) {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l h.balanced).1.getD k fallback = t.getD k fallback := by
  simp_to_model [insertMany, getD] using List.getValueCastD_insertList_of_contains_eq_false

theorem getD_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] (h : t.WF) {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany! l).1.getD k fallback = t.getD k fallback := by
  simpa only [insertMany_eq_insertMany!] using
    getD_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getD_insertMany_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    {fallback : β k'} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    (t.insertMany l h.balanced).1.getD k' fallback =
      cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  simp_to_model [insertMany, getD] using List.getValueCastD_insertList_of_mem

theorem getD_insertMany!_list_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β k} →
    {fallback : β k'} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : ⟨k, v⟩ ∈ l) →
    (t.insertMany! l).1.getD k' fallback = cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  simpa only [insertMany_eq_insertMany!] using getD_insertMany_list_of_mem h

theorem getKey?_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l h.balanced).1.getKey? k = t.getKey? k := by
  simp_to_model [insertMany, getKey?] using List.getKey?_insertList_of_contains_eq_false

theorem getKey?_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany! l).1.getKey? k = t.getKey? k := by
  simpa only [insertMany_eq_insertMany!] using getKey?_insertMany_list_of_contains_eq_false h h'

theorem getKey?_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    (t.insertMany l h.balanced).1.getKey? k' = some k := by
  simp_to_model [insertMany, getKey?] using List.getKey?_insertList_of_mem

theorem getKey?_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    (t.insertMany! l).1.getKey? k' = some k := by
  simpa only [insertMany_eq_insertMany!] using getKey?_insertMany_list_of_mem h

theorem getKey_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h₁ : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l h.balanced).1.getKey k h' =
    t.getKey k (contains_of_contains_insertMany_list h h' h₁) := by
  simp_to_model [insertMany, getKey] using List.getKey_insertList_of_contains_eq_false

theorem getKey_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h₁ : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany! l).1.getKey k h' =
    t.getKey k (contains_of_contains_insertMany!_list h h' h₁) := by
  simpa only [insertMany_eq_insertMany!] using
    getKey_insertMany_list_of_contains_eq_false h h₁ (h' := by simpa [insertMany_eq_insertMany!])

theorem getKey_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    {h' : _} →
    (t.insertMany l h.balanced).1.getKey k' h' = k := by
  simp_to_model [insertMany, getKey, contains] using List.getKey_insertList_of_mem

theorem getKey_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    {h' : _} →
    (t.insertMany! l).1.getKey k' h' = k := by
  simpa only [insertMany_eq_insertMany!] using getKey_insertMany_list_of_mem h

theorem getKey!_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l h.balanced).1.getKey! k = t.getKey! k := by
  simp_to_model [insertMany, getKey!] using List.getKey!_insertList_of_contains_eq_false

theorem getKey!_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany! l).1.getKey! k = t.getKey! k := by
  simpa only [insertMany_eq_insertMany!] using getKey!_insertMany_list_of_contains_eq_false h h'

theorem getKey!_insertMany_list_of_mem [TransOrd α] [Inhabited α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    (t.insertMany l h.balanced).1.getKey! k' = k := by
  simp_to_model [insertMany, getKey!] using List.getKey!_insertList_of_mem

theorem getKey!_insertMany!_list_of_mem [TransOrd α] [Inhabited α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    (t.insertMany! l).1.getKey! k' = k := by
  simpa only [insertMany_eq_insertMany!] using getKey!_insertMany_list_of_mem h

theorem getKeyD_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List ((a : α) × β a)} {k fallback : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l h.balanced).1.getKeyD k fallback = t.getKeyD k fallback := by
  simp_to_model [insertMany, getKeyD] using List.getKeyD_insertList_of_contains_eq_false

theorem getKeyD_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List ((a : α) × β a)} {k fallback : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (t.insertMany! l).1.getKeyD k fallback = t.getKeyD k fallback := by
  simpa only [insertMany_eq_insertMany!] using getKeyD_insertMany_list_of_contains_eq_false h h'

theorem getKeyD_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    (t.insertMany l h.balanced).1.getKeyD k' fallback = k := by
  simp_to_model [insertMany, getKeyD] using List.getKeyD_insertList_of_mem

theorem getKeyD_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Sigma.fst) →
    (t.insertMany! l).1.getKeyD k' fallback = k := by
  simpa only [insertMany_eq_insertMany!] using getKeyD_insertMany_list_of_mem h

theorem size_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} : (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (∀ (a : α), t.contains a → (l.map Sigma.fst).contains a = false) →
    (t.insertMany l h.balanced).1.size = t.size + l.length := by
  simp_to_model [insertMany, size, contains] using List.length_insertList

theorem size_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} : (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (∀ (a : α), t.contains a → (l.map Sigma.fst).contains a = false) →
    (t.insertMany! l).1.size = t.size + l.length := by
  simpa only [insertMany_eq_insertMany!] using size_insertMany_list h

theorem size_le_size_insertMany_list [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} :
    t.size ≤ (t.insertMany l h.balanced).1.size := by
  simp_to_model [insertMany, size] using List.length_le_length_insertList

theorem size_le_size_insertMany!_list [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} :
    t.size ≤ (t.insertMany! l).1.size := by
  simpa only [insertMany_eq_insertMany!] using size_le_size_insertMany_list h

theorem size_insertMany_list_le [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany l h.balanced).1.size ≤ t.size + l.length := by
  simp_to_model [insertMany, size] using List.length_insertList_le

theorem size_insertMany!_list_le [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany! l).1.size ≤ t.size + l.length := by
  simpa only [insertMany_eq_insertMany!] using size_insertMany_list_le h

@[simp]
theorem isEmpty_insertMany_list [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany l h.balanced).1.isEmpty = (t.isEmpty && l.isEmpty) := by
  simp_to_model [insertMany, isEmpty] using List.isEmpty_insertList

@[simp]
theorem isEmpty_insertMany!_list [TransOrd α] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany! l).1.isEmpty = (t.isEmpty && l.isEmpty) := by
  simpa only [insertMany_eq_insertMany!] using isEmpty_insertMany_list h

namespace Const

variable {β : Type v} {t : Impl α β}

theorem insertMany_cons (h : t.WF) {l : List (α × β)} {k : α} {v : β} :
    (Const.insertMany t ((k, v) :: l) h.balanced).1 =
      (Const.insertMany (t.insert k v h.balanced).impl l h.insert.balanced).1 := by
  simp [insertMany_eq_foldl, insert_eq_insert!]

theorem insertMany!_cons {l : List (α × β)} {k : α} {v : β} :
    (Const.insertMany! t ((k, v) :: l)).1 = (Const.insertMany! (t.insert! k v) l).1 := by
  simp only [insertMany!_eq_foldl, List.foldl_cons]

@[simp]
theorem contains_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (Const.insertMany t l h.balanced).1.contains k =
      (t.contains k || (l.map Prod.fst).contains k) := by
  simp_to_model [Const.insertMany, contains] using List.containsKey_insertListConst

@[simp]
theorem contains_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (Const.insertMany! t l).1.contains k = (t.contains k || (l.map Prod.fst).contains k) := by
  simpa only [insertMany_eq_insertMany!] using contains_insertMany_list h

@[simp]
theorem mem_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ (insertMany t l h.balanced).1 ↔ k ∈ t ∨ (l.map Prod.fst).contains k := by
  simp [mem_iff_contains, contains_insertMany_list h]

@[simp]
theorem mem_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ (insertMany! t l).1 ↔ k ∈ t ∨ (l.map Prod.fst).contains k := by
  simpa only [insertMany_eq_insertMany!] using mem_insertMany_list h

theorem contains_of_contains_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (insertMany t l h.balanced).1.contains k →
      (l.map Prod.fst).contains k = false → t.contains k := by
  simp_to_model [Const.insertMany, contains] using List.containsKey_of_containsKey_insertListConst

theorem mem_of_mem_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ (insertMany t l h.balanced).1 → (l.map Prod.fst).contains k = false → k ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertMany_list h

theorem contains_of_contains_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List ( α × β )} {k : α} :
    (insertMany! t l).1.contains k → (l.map Prod.fst).contains k = false → t.contains k := by
  simpa only [insertMany_eq_insertMany!] using contains_of_contains_insertMany_list h

theorem mem_of_mem_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ (insertMany! t l).1 → (l.map Prod.fst).contains k = false → k ∈ t := by
  simpa only [insertMany_eq_insertMany!] using mem_of_mem_insertMany_list h

theorem getKey?_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany t l h.balanced).1.getKey? k = t.getKey? k := by
  simp_to_model [Const.insertMany, getKey?] using List.getKey?_insertListConst_of_contains_eq_false

theorem getKey?_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany! t l).1.getKey? k = t.getKey? k := by
  simpa only [insertMany_eq_insertMany!] using getKey?_insertMany_list_of_contains_eq_false h h'

theorem getKey?_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    (insertMany t l h.balanced).1.getKey? k' = some k := by
  simp_to_model [Const.insertMany, getKey?] using List.getKey?_insertListConst_of_mem

theorem getKey?_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    (insertMany! t l).1.getKey? k' = some k := by
  simpa only [insertMany_eq_insertMany!] using getKey?_insertMany_list_of_mem h

theorem getKey_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany t l h.balanced).1.getKey k h' =
    t.getKey k (contains_of_contains_insertMany_list h h' h₁) := by
  simp_to_model [Const.insertMany, getKey] using List.getKey_insertListConst_of_contains_eq_false

theorem getKey_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany! t l).1.getKey k h' =
    t.getKey k (contains_of_contains_insertMany!_list h h' h₁) := by
  simpa only [insertMany_eq_insertMany!] using
    getKey_insertMany_list_of_contains_eq_false h h₁ (h' := by simpa [insertMany_eq_insertMany!])

theorem getKey_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    {h' : _} →
    (insertMany t l h.balanced).1.getKey k' h' = k := by
  simp_to_model [Const.insertMany, getKey, contains] using List.getKey_insertListConst_of_mem

theorem getKey_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    {h' : _} →
    (insertMany! t l).1.getKey k' h' = k := by
  simpa only [insertMany_eq_insertMany!] using getKey_insertMany_list_of_mem h

theorem getKey!_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] (h : t.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany t l h.balanced).1.getKey! k = t.getKey! k := by
  simp_to_model [Const.insertMany, getKey!] using List.getKey!_insertListConst_of_contains_eq_false

theorem getKey!_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] (h : t.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany! t l).1.getKey! k = t.getKey! k := by
  simpa only [insertMany_eq_insertMany!] using getKey!_insertMany_list_of_contains_eq_false h h'

theorem getKey!_insertMany_list_of_mem [TransOrd α] [Inhabited α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    (insertMany t l h.balanced).1.getKey! k' = k := by
  simp_to_model [Const.insertMany, getKey!] using List.getKey!_insertListConst_of_mem

theorem getKey!_insertMany!_list_of_mem [TransOrd α] [Inhabited α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    (insertMany! t l).1.getKey! k' = k := by
  simpa only [insertMany_eq_insertMany!] using getKey!_insertMany_list_of_mem h

theorem getKeyD_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List (α × β)} {k fallback : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany t l h.balanced).1.getKeyD k fallback = t.getKeyD k fallback := by
  simp_to_model [Const.insertMany, getKeyD] using List.getKeyD_insertListConst_of_contains_eq_false

theorem getKeyD_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List (α × β)} {k fallback : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany! t l).1.getKeyD k fallback = t.getKeyD k fallback := by
  simpa only [insertMany_eq_insertMany!] using getKeyD_insertMany_list_of_contains_eq_false h h'

theorem getKeyD_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)}
    {k k' fallback : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    (insertMany t l h.balanced).1.getKeyD k' fallback = k := by
  simp_to_model [Const.insertMany, getKeyD] using List.getKeyD_insertListConst_of_mem

theorem getKeyD_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)}
    {k k' fallback : α} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (mem : k ∈ l.map Prod.fst) →
    (insertMany! t l).1.getKeyD k' fallback = k := by
  simpa only [insertMany_eq_insertMany!] using getKeyD_insertMany_list_of_mem h

theorem size_insertMany_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} :
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (∀ (a : α), t.contains a → (l.map Prod.fst).contains a = false) →
    (insertMany t l h.balanced).1.size = t.size + l.length := by
  simp_to_model [Const.insertMany, size, contains] using List.length_insertListConst

theorem size_insertMany!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} :
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) →
    (∀ (a : α), t.contains a → (l.map Prod.fst).contains a = false) →
    (insertMany! t l).1.size = t.size + l.length := by
  simpa only [insertMany_eq_insertMany!] using size_insertMany_list h

theorem size_le_size_insertMany_list [TransOrd α] (h : t.WF)
    {l : List (α × β)} :
    t.size ≤ (insertMany t l h.balanced).1.size := by
  simp_to_model [Const.insertMany, size] using List.length_le_length_insertListConst

theorem size_le_size_insertMany!_list [TransOrd α] (h : t.WF)
    {l : List (α × β)} :
    t.size ≤ (insertMany! t l).1.size := by
  simpa only [insertMany_eq_insertMany!] using size_le_size_insertMany_list h

theorem size_insertMany_list_le [TransOrd α] (h : t.WF)
    {l : List (α × β)} :
    (insertMany t l h.balanced).1.size ≤ t.size + l.length := by
  simp_to_model [Const.insertMany, size] using List.length_insertListConst_le

theorem size_insertMany!_list_le [TransOrd α] (h : t.WF)
    {l : List (α × β)} :
    (insertMany! t l).1.size ≤ t.size + l.length := by
  simpa only [insertMany_eq_insertMany!] using size_insertMany_list_le h

@[simp]
theorem isEmpty_insertMany_list [TransOrd α] (h : t.WF)
    {l : List (α × β)} :
    (insertMany t l h.balanced).1.isEmpty = (t.isEmpty && l.isEmpty) := by
  simp_to_model [Const.insertMany, isEmpty] using List.isEmpty_insertListConst

@[simp]
theorem isEmpty_insertMany!_list [TransOrd α] (h : t.WF)
    {l : List (α × β)} :
    (insertMany! t l).1.isEmpty = (t.isEmpty && l.isEmpty) := by
  simpa only [insertMany_eq_insertMany!] using isEmpty_insertMany_list h

theorem get?_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get? (insertMany t l h.balanced).1 k = get? t k := by
  simp_to_model [Const.insertMany, Const.get?] using List.getValue?_insertListConst_of_contains_eq_false

theorem get?_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get? (insertMany! t l).1 k = get? t k := by
  simpa only [insertMany_eq_insertMany!] using get?_insertMany_list_of_contains_eq_false h h'

theorem get?_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) →
    get? (insertMany t l h.balanced).1 k' = v := by
  simp_to_model [Const.insertMany, Const.get?] using List.getValue?_insertListConst_of_mem

theorem get?_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) →
    get? (insertMany! t l).1 k' = v := by
  simpa only [insertMany_eq_insertMany!] using get?_insertMany_list_of_mem h

theorem get_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany t l h.balanced).1 k h' =
      get t k (contains_of_contains_insertMany_list h h' h₁) := by
  simp_to_model [Const.insertMany, Const.get] using List.getValue_insertListConst_of_contains_eq_false

theorem get_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany! t l).1 k h' = get t k (contains_of_contains_insertMany!_list h h' h₁) := by
  simpa only [insertMany_eq_insertMany!] using
    get_insertMany_list_of_contains_eq_false h h₁ (h' := by simpa [insertMany_eq_insertMany!])

theorem get_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) → {h' : _} →
    get (insertMany t l h.balanced).1 k' h' = v := by
  simp_to_model [Const.insertMany, Const.get, contains] using List.getValue_insertListConst_of_mem

theorem get_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)} {k k' : α} : (k_beq : compare k k' = .eq) → {v : β} →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) → {h' : _} →
    get (insertMany! t l).1 k' h' = v := by
  simpa only [insertMany_eq_insertMany!] using get_insertMany_list_of_mem h

theorem get!_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited β] (h : t.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get! (insertMany t l h.balanced).1 k = get! t k := by
  simp_to_model [Const.insertMany, Const.get!] using List.getValue!_insertListConst_of_contains_eq_false

theorem get!_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited β] (h : t.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get! (insertMany! t l).1 k = get! t k := by
  simpa only [insertMany_eq_insertMany!] using
    get!_insertMany_list_of_contains_eq_false h (h' := by simpa [insertMany_eq_insertMany!])

theorem get!_insertMany_list_of_mem [TransOrd α] [Inhabited β] (h : t.WF)
    {l : List (α × β)} {k k' : α} {v : β} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) →
    get! (insertMany t l h.balanced).1 k' = v := by
  simp_to_model [Const.insertMany, Const.get!] using List.getValue!_insertListConst_of_mem

theorem get!_insertMany!_list_of_mem [TransOrd α] [Inhabited β] (h : t.WF)
    {l : List (α × β)} {k k' : α} {v : β} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) →
    get! (insertMany! t l).1 k' = v := by
  simpa only [insertMany_eq_insertMany!] using get!_insertMany_list_of_mem h

theorem getD_insertMany_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} {fallback : β}
    (h' : (l.map Prod.fst).contains k = false) :
    getD (insertMany t l h.balanced).1 k fallback = getD t k fallback := by
  simp_to_model [Const.insertMany, Const.getD] using List.getValueD_insertListConst_of_contains_eq_false

theorem getD_insertMany!_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List (α × β)} {k : α} {fallback : β}
    (h' : (l.map Prod.fst).contains k = false) :
    getD (insertMany! t l).1 k fallback = getD t k fallback := by
  simpa only [insertMany_eq_insertMany!] using getD_insertMany_list_of_contains_eq_false h h'

theorem getD_insertMany_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)} {k k' : α} {v fallback : β} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) →
    getD (insertMany t l h.balanced).1 k' fallback = v := by
  simp_to_model [Const.insertMany, Const.getD] using List.getValueD_insertListConst_of_mem

theorem getD_insertMany!_list_of_mem [TransOrd α] (h : t.WF)
    {l : List (α × β)} {k k' : α} {v fallback : β} : (k_beq : compare k k' = .eq) →
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) → (mem : ⟨k, v⟩ ∈ l) →
    getD (insertMany! t l).1 k' fallback = v := by
  simpa only [insertMany_eq_insertMany!] using getD_insertMany_list_of_mem h

variable {t : Impl α Unit}

theorem insertManyIfNewUnit_cons (h : t.WF) {l : List α} {k : α} :
    (insertManyIfNewUnit t (k :: l) h.balanced).1 =
      (insertManyIfNewUnit (t.insertIfNew k () h.balanced).impl l h.insertIfNew.balanced).1 := by
  simp [insertManyIfNewUnit_eq_foldl, insertIfNew_eq_insertIfNew!]

theorem insertManyIfNewUnit!_cons {l : List α} {k : α} :
    (insertManyIfNewUnit! t (k :: l)).1 = (insertManyIfNewUnit! (t.insertIfNew! k ()) l).1 := by
  simp only [insertManyIfNewUnit!_eq_foldl, List.foldl_cons]

@[simp]
theorem contains_insertManyIfNewUnit_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l h.balanced).1.contains k = (t.contains k || l.contains k) := by
  simp_to_model [Const.insertManyIfNewUnit, contains] using List.containsKey_insertListIfNewUnit

@[simp]
theorem contains_insertManyIfNewUnit!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit! t l).1.contains k = (t.contains k || l.contains k) := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using contains_insertManyIfNewUnit_list h

@[simp]
theorem mem_insertManyIfNewUnit_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} :
    k ∈ (insertManyIfNewUnit t l h.balanced).1 ↔ k ∈ t ∨ l.contains k := by
  simp [mem_iff_contains, contains_insertManyIfNewUnit_list h]

@[simp]
theorem mem_insertManyIfNewUnit!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} :
    k ∈ (insertManyIfNewUnit! t l).1 ↔ k ∈ t ∨ l.contains k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using mem_insertManyIfNewUnit_list h

theorem contains_of_contains_insertManyIfNewUnit_list [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List α} {k : α} (h₂ : l.contains k = false) :
    (insertManyIfNewUnit t l h.balanced).1.contains k → t.contains k := by
  simp_to_model [Const.insertManyIfNewUnit, contains] using List.containsKey_of_containsKey_insertListIfNewUnit

theorem contains_of_contains_insertManyIfNewUnit!_list [TransOrd α] [BEq α] [LawfulBEqOrd α]
    (h : t.WF) {l : List α} {k : α} (h₂ : l.contains k = false) :
    (insertManyIfNewUnit! t l).1.contains k → t.contains k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using
    contains_of_contains_insertManyIfNewUnit_list h h₂

theorem mem_of_mem_insertManyIfNewUnit_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ (insertManyIfNewUnit t l h.balanced).1 → k ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertManyIfNewUnit_list h contains_eq_false

theorem mem_of_mem_insertManyIfNewUnit!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ (insertManyIfNewUnit! t l).1 → k ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertManyIfNewUnit!_list h contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [TransOrd α] [BEq α]
    [LawfulBEqOrd α] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false → getKey? (insertManyIfNewUnit t l h.balanced).1 k = none := by
  simp_to_model [Const.insertManyIfNewUnit, getKey?, contains] using
    List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKey?_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false [TransOrd α] [BEq α]
    [LawfulBEqOrd α] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false → getKey? (insertManyIfNewUnit! t l).1 k = none := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false h

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k k' : α} : (k_beq : compare k k' = .eq) →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKey? (insertManyIfNewUnit t l h.balanced).1 k' = some k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey?, contains] using
    List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey?_insertManyIfNewUnit!_list_of_not_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k k' : α} : (k_beq : compare k k' = .eq) →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKey? (insertManyIfNewUnit! t l).1 k' = some k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem h

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey? (insertManyIfNewUnit t l h.balanced).1 k = getKey? t k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey?, contains] using
    List.getKey?_insertListIfNewUnit_of_contains

theorem getKey?_insertManyIfNewUnit!_list_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey? (insertManyIfNewUnit! t l).1 k = getKey? t k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey?_insertManyIfNewUnit_list_of_mem h

theorem getKey_insertManyIfNewUnit_list_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l h.balanced).1 k h' = getKey t k contains := by
  simp_to_model [Const.insertManyIfNewUnit, getKey] using
    List.getKey_insertListIfNewUnit_of_contains

theorem getKey_insertManyIfNewUnit!_list_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit! t l).1 k h' = getKey t k contains := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using
    getKey_insertManyIfNewUnit_list_of_mem h contains
      (h' := by simpa [insertManyIfNewUnit_eq_insertManyIfNewUnit!])

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α}
    {k k' : α} : (k_beq : compare k k' = .eq) → {h' : _} →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKey (insertManyIfNewUnit t l h.balanced).1 k' h' = k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey, contains] using
    List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey_insertManyIfNewUnit!_list_of_not_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α}
    {k k' : α} : (k_beq : compare k k' = .eq) → {h' : _} →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKey (insertManyIfNewUnit! t l).1 k' h' = k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey_insertManyIfNewUnit_list_of_not_mem_of_mem h

theorem getKey_insertManyIfNewUnit_list_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k : α} (contains : k ∈ t) {h'} :
    getKey (insertManyIfNewUnit t l h.balanced).1 k h' = getKey t k contains := by
  simp_to_model [Const.insertManyIfNewUnit, getKey] using List.getKey_insertListIfNewUnit_of_contains

theorem getKey_insertManyIfNewUnit!_list_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k : α} (contains : k ∈ t) {h'} :
    getKey (insertManyIfNewUnit! t l).1 k h' = getKey t k contains := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using
    getKey_insertManyIfNewUnit_list_mem_of_mem h contains
      (h' := by simpa [insertManyIfNewUnit_eq_insertManyIfNewUnit!])

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [BEq α] [LawfulBEqOrd α]
    [TransOrd α] [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false →
      getKey! (insertManyIfNewUnit t l h.balanced).1 k = default := by
  simp_to_model [Const.insertManyIfNewUnit, getKey!, contains] using
    List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKey!_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false [BEq α] [LawfulBEqOrd α]
    [TransOrd α] [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false →
      getKey! (insertManyIfNewUnit! t l).1 k = default := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false h

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransOrd α]
    [Inhabited α] (h : t.WF) {l : List α} {k k' : α} : (k_beq : compare k k' = .eq) →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKey! (insertManyIfNewUnit t l h.balanced).1 k' = k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey!, contains] using
    List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey!_insertManyIfNewUnit!_list_of_not_mem_of_mem [TransOrd α]
    [Inhabited α] (h : t.WF) {l : List α} {k k' : α} : (k_beq : compare k k' = .eq) →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKey! (insertManyIfNewUnit! t l).1 k' = k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem h

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransOrd α]
    [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey! (insertManyIfNewUnit t l h.balanced).1 k = getKey! t k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey!, contains] using
    List.getKey!_insertListIfNewUnit_of_contains

theorem getKey!_insertManyIfNewUnit!_list_of_mem [TransOrd α]
    [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey! (insertManyIfNewUnit! t l).1 k = getKey! t k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKey!_insertManyIfNewUnit_list_of_mem h

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [BEq α] [LawfulBEqOrd α]
    [TransOrd α] (h : t.WF) {l : List α} {k fallback : α} :
    ¬ k ∈ t → l.contains k = false → getKeyD (insertManyIfNewUnit t l h.balanced).1 k fallback = fallback := by
  simp_to_model [Const.insertManyIfNewUnit, getKeyD, contains] using
    List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKeyD_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false [BEq α] [LawfulBEqOrd α]
    [TransOrd α] (h : t.WF) {l : List α} {k fallback : α} :
    ¬ k ∈ t → l.contains k = false → getKeyD (insertManyIfNewUnit! t l).1 k fallback = fallback := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false h

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k k' fallback : α} : (k_beq : compare k k' = .eq) →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKeyD (insertManyIfNewUnit t l h.balanced).1 k' fallback = k := by
  simp_to_model [Const.insertManyIfNewUnit, getKeyD, contains] using
    List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKeyD_insertManyIfNewUnit!_list_of_not_mem_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k k' fallback : α} : (k_beq : compare k k' = .eq) →
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ compare a b = .eq) → k ∈ l →
      getKeyD (insertManyIfNewUnit! t l).1 k' fallback = k := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem h

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k fallback : α} :
    k ∈ t → getKeyD (insertManyIfNewUnit t l h.balanced).1 k fallback = getKeyD t k fallback := by
  simp_to_model [Const.insertManyIfNewUnit, getKeyD, contains] using
    List.getKeyD_insertListIfNewUnit_of_contains

theorem getKeyD_insertManyIfNewUnit!_list_of_mem [TransOrd α]
    (h : t.WF) {l : List α} {k fallback : α} :
    k ∈ t → getKeyD (insertManyIfNewUnit! t l).1 k fallback = getKeyD t k fallback := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using getKeyD_insertManyIfNewUnit_list_of_mem h

theorem size_insertManyIfNewUnit_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} :
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq)) →
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l h.balanced).1.size = t.size + l.length := by
  simp_to_model [Const.insertManyIfNewUnit, size, contains] using List.length_insertListIfNewUnit

theorem size_insertManyIfNewUnit!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} :
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq)) →
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit! t l).1.size = t.size + l.length := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using size_insertManyIfNewUnit_list h

theorem size_le_size_insertManyIfNewUnit_list [TransOrd α] (h : t.WF)
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l h.balanced).1.size := by
  simp_to_model [Const.insertManyIfNewUnit, size] using List.length_le_length_insertListIfNewUnit

theorem size_le_size_insertManyIfNewUnit!_list [TransOrd α] (h : t.WF)
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit! t l).1.size := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using size_le_size_insertManyIfNewUnit_list h

theorem size_insertManyIfNewUnit_list_le [TransOrd α] (h : t.WF)
    {l : List α} :
    (insertManyIfNewUnit t l h.balanced).1.size ≤ t.size + l.length := by
  simp_to_model [Const.insertManyIfNewUnit, size] using List.length_insertListIfNewUnit_le

theorem size_insertManyIfNewUnit!_list_le [TransOrd α] (h : t.WF)
    {l : List α} :
    (insertManyIfNewUnit! t l).1.size ≤ t.size + l.length := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using size_insertManyIfNewUnit_list_le h

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransOrd α] (h : t.WF) {l : List α} :
    (insertManyIfNewUnit t l h.balanced).1.isEmpty = (t.isEmpty && l.isEmpty) := by
  simp_to_model [Const.insertManyIfNewUnit, isEmpty] using List.isEmpty_insertListIfNewUnit

@[simp]
theorem isEmpty_insertManyIfNewUnit!_list [TransOrd α] (h : t.WF) {l : List α} :
    (insertManyIfNewUnit! t l).1.isEmpty = (t.isEmpty && l.isEmpty) := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using isEmpty_insertManyIfNewUnit_list h

theorem get?_insertManyIfNewUnit_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit t l h.balanced).1 k =
      if k ∈ t ∨ l.contains k then some () else none := by
  simp_to_model [Const.insertManyIfNewUnit, Const.get?, contains] using
    List.getValue?_insertListIfNewUnit

theorem get?_insertManyIfNewUnit!_list [TransOrd α] [BEq α] [LawfulBEqOrd α] (h : t.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit! t l).1 k = if k ∈ t ∨ l.contains k then some () else none := by
  simpa only [insertManyIfNewUnit_eq_insertManyIfNewUnit!] using get?_insertManyIfNewUnit_list h

theorem get_insertManyIfNewUnit_list (h : t.WF) {l : List α} {k : α} {h'} :
    get (insertManyIfNewUnit t l h.balanced).1 k h' = () :=
  rfl

theorem get_insertManyIfNewUnit!_list {l : List α} {k : α} {h'} :
    get (insertManyIfNewUnit! t l).1 k h' = () :=
  rfl

theorem get!_insertManyIfNewUnit_list (h : t.WF) {l : List α} {k : α} :
    get! (insertManyIfNewUnit t l h.balanced).1 k = () :=
  rfl

theorem get!_insertManyIfNewUnit!_list {l : List α} {k : α} :
    get! (insertManyIfNewUnit! t l).1 k = () :=
  rfl

theorem getD_insertManyIfNewUnit_list (h : t.WF) {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit t l h.balanced).1 k fallback = () :=
  rfl

theorem getD_insertManyIfNewUnit!_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit! t l).1 k fallback = () :=
  rfl

end Const

@[simp]
theorem insertMany_empty_list_nil :
    (insertMany empty ([] : List ((a : α) × (β a))) WF.empty.balanced).1 = empty :=
  rfl

@[simp]
theorem insertMany!_empty_list_nil :
    (insertMany! empty ([] : List ((a : α) × (β a)))).1 = empty :=
  rfl

@[simp]
theorem insertMany_empty_list_singleton {k : α} {v : β k} :
    (insertMany empty [⟨k, v⟩] WF.empty.balanced).1 = (empty.insert k v WF.empty.balanced).impl :=
  rfl

@[simp]
theorem insertMany!_empty_list_singleton {k : α} {v : β k} :
    (insertMany! empty [⟨k, v⟩]).1 = (empty.insert k v WF.empty.balanced).impl :=
  rfl

theorem insertMany_empty_list_cons {k : α} {v : β k}
    {tl : List ((a : α) × (β a))} :
    (insertMany empty (⟨k, v⟩ :: tl) WF.empty.balanced).1 =
      ((empty.insert k v WF.empty.balanced).impl.insertMany tl WF.empty.insert.balanced).1 := by
  rw [insertMany_cons WF.empty]

theorem insertMany_empty_list_cons_eq_insertMany! {k : α} {v : β k}
    {tl : List ((a : α) × (β a))} :
    (insertMany empty (⟨k, v⟩ :: tl) WF.empty.balanced).1 =
      ((empty.insert! k v).insertMany! tl).1 := by
  rw [insertMany_cons WF.empty, insertMany_eq_insertMany!, insert_eq_insert!]

theorem contains_insertMany_empty_list [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {k : α} :
    (insertMany empty l WF.empty.balanced).1.contains k = (l.map Sigma.fst).contains k := by
  simp only [contains_insertMany_list WF.empty, contains_empty, Bool.false_or]

theorem get?_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l WF.empty.balanced).1.get? k = none := by
  simp only [get?_insertMany_list_of_contains_eq_false WF.empty h, get?_empty]

theorem get?_insertMany_empty_list_of_mem [TransOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : compare k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany empty l WF.empty.balanced).1.get? k' =
      some (cast (by congr; apply compare_eq_iff_eq.mp k_beq) v) := by
  rw [get?_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem get_insertMany_empty_list_of_mem [TransOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : compare k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (insertMany empty l WF.empty.balanced).1.get k' h =
      cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  rw [get_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem get!_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l WF.empty.balanced).1.get! k = default := by
  simp only [get!_insertMany_list_of_contains_eq_false WF.empty h]
  apply get!_empty

theorem get!_insertMany_empty_list_of_mem [TransOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : compare k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany empty l WF.empty.balanced).1.get! k' =
      cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  rw [get!_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getD_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l WF.empty.balanced).1.getD k fallback = fallback := by
  rw [getD_insertMany_list_of_contains_eq_false WF.empty contains_eq_false]
  apply getD_empty

theorem getD_insertMany_empty_list_of_mem [TransOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : compare k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany empty l WF.empty.balanced).1.getD k' fallback =
      cast (by congr; apply compare_eq_iff_eq.mp k_beq) v := by
  rw [getD_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKey?_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l WF.empty.balanced).1.getKey? k = none := by
  rw [getKey?_insertMany_list_of_contains_eq_false WF.empty h]
  apply getKey?_empty

theorem getKey?_insertMany_empty_list_of_mem [TransOrd α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany empty l WF.empty.balanced).1.getKey? k' = some k := by
  rw [getKey?_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKey_insertMany_empty_list_of_mem [TransOrd α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (insertMany empty l WF.empty.balanced).1.getKey k' h' = k := by
  rw [getKey_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKey!_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l WF.empty.balanced).1.getKey! k = default := by
  rw [getKey!_insertMany_list_of_contains_eq_false WF.empty h]
  apply getKey!_empty

theorem getKey!_insertMany_empty_list_of_mem [TransOrd α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany empty l WF.empty.balanced).1.getKey! k' = k := by
  rw [getKey!_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKeyD_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l WF.empty.balanced).1.getKeyD k fallback = fallback := by
  rw [getKeyD_insertMany_list_of_contains_eq_false WF.empty h]
  apply getKeyD_empty

theorem getKeyD_insertMany_empty_list_of_mem [TransOrd α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany empty l WF.empty.balanced).1.getKeyD k' fallback = k := by
  rw [getKeyD_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem size_insertMany_empty_list [TransOrd α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) :
    (insertMany empty l WF.empty.balanced).1.size = l.length := by
  rw [size_insertMany_list WF.empty distinct]
  · simp only [size_empty, Nat.zero_add]
  · simp only [contains_empty, Bool.false_eq_true, false_implies, implies_true]

theorem size_insertMany_empty_list_le [TransOrd α]
    {l : List ((a : α) × β a)} :
    (insertMany empty l WF.empty.balanced).1.size ≤ l.length := by
  rw [← Nat.zero_add l.length]
  apply size_insertMany_list_le WF.empty

theorem isEmpty_insertMany_empty_list [TransOrd α]
    {l : List ((a : α) × β a)} :
    (insertMany empty l WF.empty.balanced).1.isEmpty = l.isEmpty := by
  simp [isEmpty_insertMany_list WF.empty, isEmpty_empty]

namespace Const
variable {β : Type v}

@[simp]
theorem insertMany_empty_list_nil :
    (insertMany empty ([] : List (α × β)) WF.empty.balanced).1 = empty := by
  rfl

@[simp]
theorem insertMany_empty_list_singleton {k : α} {v : β} :
    (insertMany empty [⟨k, v⟩] WF.empty.balanced).1 = (empty.insert k v WF.empty.balanced).impl := by
  rfl

theorem insertMany_empty_list_cons {k : α} {v : β}
    {tl : List (α × β)} :
    (insertMany empty (⟨k, v⟩ :: tl) WF.empty.balanced) =
      (insertMany (empty.insert k v WF.empty.balanced).1 tl WF.empty.insert.balanced).1 := by
  rw [insertMany_cons WF.empty]

theorem insertMany_empty_list_cons_eq_insertMany! {k : α} {v : β}
    {tl : List (α × β)} :
    (insertMany empty (⟨k, v⟩ :: tl) WF.empty.balanced) =
      (insertMany! (empty.insert! k v) tl).1 := by
    rw [insertMany_cons WF.empty, insertMany_eq_insertMany!, insert_eq_insert!]

theorem contains_insertMany_empty_list [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List (α × β)} {k : α} :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.contains k =
      (l.map Prod.fst).contains k := by
  simp [contains_insertMany_list WF.empty, contains_empty]

theorem get?_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List (α × β)} {k : α} (h : (l.map Prod.fst).contains k = false) :
    get? (insertMany (empty : Impl α β) l WF.empty.balanced).1 k = none := by
  rw [get?_insertMany_list_of_contains_eq_false WF.empty h]
  apply get?_empty

theorem get?_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)} {k k' : α} (k_beq : compare k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany (empty : Impl α β) l WF.empty.balanced) k' = some v := by
  rw [get?_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem get_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)} {k k' : α} (k_beq : compare k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (insertMany (empty : Impl α β) l WF.empty.balanced) k' h = v := by
  rw [get_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem get!_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (h : (l.map Prod.fst).contains k = false) :
    get! (insertMany (empty : Impl α β) l WF.empty.balanced) k = (default : β) := by
  rw [get!_insertMany_list_of_contains_eq_false WF.empty h]
  apply get!_empty

theorem get!_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)} {k k' : α} (k_beq : compare k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany (empty : Impl α β) l WF.empty.balanced) k' = v := by
  rw [get!_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getD_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany (empty : Impl α β) l WF.empty.balanced) k fallback = fallback := by
  rw [getD_insertMany_list_of_contains_eq_false WF.empty contains_eq_false]
  apply getD_empty

theorem getD_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)} {k k' : α} (k_beq : compare k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany (empty : Impl α β) l WF.empty.balanced) k' fallback = v := by
  rw [getD_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKey?_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKey? k = none := by
  rw [getKey?_insertMany_list_of_contains_eq_false WF.empty h]
  apply getKey?_empty

theorem getKey?_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKey? k' = some k := by
  rw [getKey?_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKey_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKey k' h' = k := by
  rw [getKey_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKey!_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKey! k = default := by
  rw [getKey!_insertMany_list_of_contains_eq_false WF.empty h]
  apply getKey!_empty

theorem getKey!_insertMany_empty_list_of_mem [TransOrd α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKey! k' = k := by
  rw [getKey!_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem getKeyD_insertMany_empty_list_of_contains_eq_false [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List (α × β)} {k fallback : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKeyD k fallback = fallback := by
  rw [getKeyD_insertMany_list_of_contains_eq_false WF.empty h]
  apply getKeyD_empty

theorem getKeyD_insertMany_empty_list_of_mem [TransOrd α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.getKeyD k' fallback = k := by
  rw [getKeyD_insertMany_list_of_mem WF.empty k_beq distinct mem]

theorem size_insertMany_empty_list [TransOrd α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.size = l.length := by
  rw [size_insertMany_list WF.empty distinct]
  · simp only [size_empty, Nat.zero_add]
  · simp only [contains_empty, Bool.false_eq_true, false_implies, implies_true]

theorem size_insertMany_empty_list_le [TransOrd α]
    {l : List (α × β)} :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.size ≤ l.length := by
  rw [← Nat.zero_add l.length]
  apply (size_insertMany_list_le WF.empty)

theorem isEmpty_insertMany_empty_list [TransOrd α]
    {l : List (α × β)} :
    (insertMany (empty : Impl α β) l WF.empty.balanced).1.isEmpty = l.isEmpty := by
  simp [isEmpty_insertMany_list WF.empty, isEmpty_empty]

@[simp]
theorem insertManyIfNewUnit_empty_list_nil :
    insertManyIfNewUnit (empty : Impl α Unit) ([] : List α) WF.empty.balanced =
      (empty : Impl α Unit) :=
  rfl

@[simp]
theorem insertManyIfNewUnit_empty_list_singleton {k : α} :
    (insertManyIfNewUnit (empty : Impl α Unit) [k] WF.empty.balanced).1 =
      (empty.insertIfNew k () WF.empty.balanced).1 :=
  rfl

theorem insertManyIfNewUnit_empty_list_cons {hd : α} {tl : List α} :
    (insertManyIfNewUnit (empty : Impl α Unit) (hd :: tl) WF.empty.balanced).1 =
      (insertManyIfNewUnit (empty.insertIfNew hd () WF.empty.balanced).1 tl
        WF.empty.insertIfNew.balanced).1 := by
  rw [insertManyIfNewUnit_cons WF.empty]

theorem insertManyIfNewUnit_empty_list_cons_eq_insertManyIfNewUnit! {hd : α} {tl : List α} :
    (insertManyIfNewUnit (empty : Impl α Unit) (hd :: tl) WF.empty.balanced).1 =
      (insertManyIfNewUnit! (empty.insertIfNew! hd ()) tl).1 := by
  rw [insertManyIfNewUnit_empty_list_cons, insertManyIfNewUnit_eq_insertManyIfNewUnit!,
    insertIfNew_eq_insertIfNew!]

theorem contains_insertManyIfNewUnit_empty_list [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1.contains k =
      l.contains k := by
  simp [contains_insertManyIfNewUnit_list WF.empty, contains_empty]

theorem getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false [TransOrd α] [BEq α]
    [LawfulBEqOrd α] {l : List α} {k : α} (h' : l.contains k = false) :
    getKey? (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k = none := by
  exact getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false WF.empty
    not_mem_empty h'

theorem getKey?_insertManyIfNewUnit_empty_list_of_mem [TransOrd α]
    {l : List α} {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k' = some k := by
  exact getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem WF.empty k_beq
    not_mem_empty distinct mem

theorem getKey_insertManyIfNewUnit_empty_list_of_mem [TransOrd α]
    {l : List α}
    {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq))
    (mem : k ∈ l) {h'} :
    getKey (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k' h' = k := by
  exact getKey_insertManyIfNewUnit_list_of_not_mem_of_mem WF.empty k_beq
    not_mem_empty distinct mem

theorem getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false [TransOrd α] [BEq α]
    [LawfulBEqOrd α] [Inhabited α] {l : List α} {k : α}
    (h' : l.contains k = false) :
    getKey! (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k = default := by
  exact getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false WF.empty
    not_mem_empty h'

theorem getKey!_insertManyIfNewUnit_empty_list_of_mem [TransOrd α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq))
    (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k' = k := by
  exact getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem WF.empty k_beq
    not_mem_empty distinct mem

theorem getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false [TransOrd α] [BEq α]
    [LawfulBEqOrd α] {l : List α} {k fallback : α}
    (h' : l.contains k = false) :
    getKeyD (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k fallback =
      fallback := by
  exact getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    WF.empty not_mem_empty h'

theorem getKeyD_insertManyIfNewUnit_empty_list_of_mem [TransOrd α]
    {l : List α} {k k' fallback : α} (k_beq : compare k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq))
    (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1 k' fallback = k := by
  exact getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem WF.empty k_beq
    not_mem_empty distinct mem

theorem size_insertManyIfNewUnit_empty_list [TransOrd α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ compare a b = .eq)) :
    (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1.size = l.length := by
  rw [size_insertManyIfNewUnit_list WF.empty distinct]
  · simp [size_empty]
  · simp [not_mem_empty]

theorem size_insertManyIfNewUnit_empty_list_le [TransOrd α]
    {l : List α} :
    (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1.size ≤ l.length := by
  apply Nat.le_trans (size_insertManyIfNewUnit_list_le WF.empty)
  simp [size_empty]

theorem isEmpty_insertManyIfNewUnit_empty_list [TransOrd α]
    {l : List α} :
    (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced).1.isEmpty = l.isEmpty := by
  rw [isEmpty_insertManyIfNewUnit_list WF.empty]
  simp [isEmpty_empty]

theorem get?_insertManyIfNewUnit_empty_list [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced) k =
      if l.contains k then some () else none := by
  rw [get?_insertManyIfNewUnit_list WF.empty]
  simp [not_mem_empty]

theorem get_insertManyIfNewUnit_empty_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced) k h = () := by
  simp

theorem get!_insertManyIfNewUnit_empty_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced) k = () := by
  simp

theorem getD_insertManyIfNewUnit_empty_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit (empty : Impl α Unit) l WF.empty.balanced) k fallback = () := by
  simp

end Const

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.isEmpty =
      ((t.erase k h.balanced).1.isEmpty && (f (t.get? k)).isNone) := by
  simp_to_model [alter, erase, isEmpty, get?] using List.isEmpty_alterKey_eq_isEmpty_eraseKey

theorem isEmpty_alter!_eq_isEmpty_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).isEmpty = ((t.erase! k).isEmpty && (f (t.get? k)).isNone) := by
  simpa only [alter_eq_alter!, erase_eq_erase!] using isEmpty_alter_eq_isEmpty_erase h

@[simp]
theorem isEmpty_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (t.get? k)).isNone) := by
  simp_to_model [alter, isEmpty, size, contains, get?] using List.isEmpty_alterKey

@[simp]
theorem isEmpty_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (t.get? k)).isNone) := by
  simpa only [alter_eq_alter!] using isEmpty_alter h

theorem contains_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.contains k' =
      if compare k k' = .eq then (f (t.get? k)).isSome else t.contains k' := by
  simp_to_model [alter, get?, contains] using List.containsKey_alterKey

theorem contains_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).contains k' =
      if compare k k' = .eq then (f (t.get? k)).isSome else t.contains k' := by
  simpa only [alter_eq_alter!] using contains_alter h

theorem mem_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    k' ∈ (t.alter k f h.balanced).1 ↔
      if compare k k' = .eq then (f (t.get? k)).isSome = true else k' ∈ t := by
  simp [mem_iff_contains, contains_alter h]

theorem mem_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    k' ∈ t.alter! k f ↔
      if compare k k' = .eq then (f (t.get? k)).isSome = true else k' ∈ t := by
  simpa only [alter_eq_alter!] using mem_alter h

theorem mem_alter_of_compare_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k': α}
    {f : Option (β k) → Option (β k)}
    (he : compare k k' = .eq) :
    k' ∈ (t.alter k f h.balanced).1 ↔ (f (t.get? k)).isSome := by
  rw [mem_alter h, if_pos he]

theorem mem_alter!_of_compare_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k': α}
    {f : Option (β k) → Option (β k)} (he : compare k k' = .eq) :
    k' ∈ t.alter! k f ↔ (f (t.get? k)).isSome := by
  simpa only [alter_eq_alter!] using mem_alter_of_compare_eq h he

@[simp]
theorem contains_alter_self [TransOrd α] [LawfulEqOrd α] {k : α} (h : t.WF)
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.contains k = (f (t.get? k)).isSome := by
  simp only [contains_alter h, compare_eq_iff_eq, reduceIte]

@[simp]
theorem contains_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).contains k = (f (t.get? k)).isSome := by
  simpa only [alter_eq_alter!] using contains_alter_self h

@[simp]
theorem mem_alter_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    k ∈ (t.alter k f h.balanced).1 ↔ (f (t.get? k)).isSome := by
  rw [mem_iff_contains, contains_alter_self h]

@[simp]
theorem mem_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    k ∈ t.alter! k f ↔ (f (t.get? k)).isSome := by
  simpa only [alter_eq_alter!] using mem_alter_self h

theorem contains_alter_of_not_compare_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ compare k k' = .eq) :
    (t.alter k f h.balanced).1.contains k' = t.contains k' := by
  simp only [contains_alter h, he, beq_iff_eq, reduceIte]

theorem contains_alter!_of_not_compare_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ compare k k' = .eq) :
    (t.alter! k f).contains k' = t.contains k' := by
  simpa only [alter_eq_alter!] using contains_alter_of_not_compare_eq h he

theorem mem_alter_of_not_compare_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ compare k k' = .eq) :
    k' ∈ (t.alter k f h.balanced).1 ↔ k' ∈ t := by
  simp only [mem_iff_contains, contains_alter_of_not_compare_eq h he]

theorem mem_alter!_of_not_compare_eq [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ compare k k' = .eq) :
    k' ∈ t.alter! k f ↔ k' ∈ t := by
  simpa only [alter_eq_alter!] using mem_alter_of_not_compare_eq h he

theorem size_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.size =
      if k ∈ t ∧ (f (t.get? k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (t.get? k)).isSome then
        t.size + 1
      else
        t.size := by
  simp_to_model [alter, get?, size, contains] using List.length_alterKey'

theorem size_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).size =
      if k ∈ t ∧ (f (t.get? k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (t.get? k)).isSome then
        t.size + 1
      else
        t.size := by
  simpa only [alter_eq_alter!] using size_alter h

theorem size_alter_eq_add_one [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∉ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f h.balanced).1.size = t.size + 1 := by
  simp_all [mem_iff_contains, size_alter]

theorem size_alter!_eq_add_one [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∉ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter! k f).size = t.size + 1 := by
  simpa only [alter_eq_alter!] using size_alter_eq_add_one h h₁ h₂

theorem size_alter_eq_sub_one [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f h.balanced).1.size = t.size - 1 := by
  simp_all [mem_iff_contains, size_alter]

theorem size_alter!_eq_sub_one [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter! k f).size = t.size - 1 := by
  simpa only [alter_eq_alter!] using size_alter_eq_sub_one h h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : ¬ k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f h.balanced).1.size = t.size := by
  simp_all [mem_iff_contains, size_alter]

theorem size_alter!_eq_self_of_not_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : ¬ k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter! k f).size = t.size := by
  simpa only [alter_eq_alter!] using size_alter_eq_self_of_not_mem h h₁ h₂

theorem size_alter_eq_self_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f h.balanced).1.size = t.size := by
  simp_all [mem_iff_contains, size_alter, Option.isSome_iff_ne_none]

theorem size_alter!_eq_self_of_mem [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter! k f).size = t.size := by
  simpa only [alter_eq_alter!] using size_alter_eq_self_of_mem h h₁ h₂

theorem size_alter_le_size [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.size ≤ t.size + 1 := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_alter!_le_size [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).size ≤ t.size + 1 := by
  simpa only [alter_eq_alter!] using size_alter_le_size h

theorem size_le_size_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    t.size - 1 ≤ (t.alter k f h.balanced).1.size := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_le_size_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    t.size - 1 ≤ (t.alter! k f).size := by
  simpa only [alter_eq_alter!] using size_le_size_alter h

theorem get?_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.get? k' =
      if h : compare k k' = .eq then
        cast (congrArg (Option ∘ β) (compare_eq_iff_eq.mp h)) (f (t.get? k))
      else
        t.get? k' := by
  simp_to_model [alter, get?] using List.getValueCast?_alterKey

theorem get?_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).get? k' =
      if h : compare k k' = .eq then
        cast (congrArg (Option ∘ β) (compare_eq_iff_eq.mp h)) (f (t.get? k))
      else
        t.get? k' := by
  simpa only [alter_eq_alter!] using get?_alter h

@[simp]
theorem get?_alter_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.get? k = f (t.get? k) := by
  simp [get?_alter h]

@[simp]
theorem get?_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).get? k = f (t.get? k) := by
  simpa only [alter_eq_alter!] using get?_alter_self h

theorem get_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ (t.alter k f h.balanced).1} :
    (t.alter k f h.balanced).1.get k' hc =
      if heq : compare k k' = .eq then
        haveI h' : (f (t.get? k)).isSome := mem_alter_of_compare_eq h heq |>.mp hc
        cast (congrArg β (compare_eq_iff_eq.mp heq)) <| (f (t.get? k)).get <| h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.get k' h' := by
  simp_to_model [alter, get, get?] using List.getValueCast_alterKey

theorem get_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ (t.alter! k f)} :
    (t.alter! k f).get k' hc =
      if heq : compare k k' = .eq then
        haveI h' : (f (t.get? k)).isSome := mem_alter!_of_compare_eq h heq |>.mp hc
        cast (congrArg β (compare_eq_iff_eq.mp heq)) <| (f (t.get? k)).get <| h'
      else
        haveI h' : k' ∈ t := mem_alter!_of_not_compare_eq h heq |>.mp hc
        t.get k' h' := by
  simpa only [alter_eq_alter!] using get_alter h (hc := by simpa [alter_eq_alter!])

@[simp]
theorem get_alter_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ (t.alter k f h.balanced).1} :
    haveI h' : (f (t.get? k)).isSome := mem_alter_self h |>.mp hc
    (t.alter k f h.balanced).1.get k hc = (f (t.get? k)).get h' := by
  simp_to_model [alter, get, get?] using List.getValueCast_alterKey_self

@[simp]
theorem get_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter! k f} :
    haveI h' : (f (t.get? k)).isSome := mem_alter!_self h |>.mp hc
    (t.alter! k f).get k hc = (f (t.get? k)).get h' := by
  simpa only [alter_eq_alter!] using get_alter_self h (hc := by simpa [alter_eq_alter!])

theorem get!_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α} [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.get! k' =
      if heq : compare k k' = .eq then
        (f (t.get? k)).map (cast (congrArg β (compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' := by
  simp_to_model [alter, get!, get?] using List.getValueCast!_alterKey

theorem get!_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α} [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).get! k' =
      if heq : compare k k' = .eq then
        (f (t.get? k)).map (cast (congrArg β (compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' := by
  simpa only [alter_eq_alter!] using get!_alter h

private theorem Option.map_cast_apply {γ γ' : Type u} (h : γ = γ') (x : Option γ) :
    Option.map (cast h) x = cast (congrArg Option h) x := by
  cases h; cases x <;> rfl

@[simp]
theorem get!_alter_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} [Inhabited (β k)]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.get! k = (f (t.get? k)).get! := by
  simp [get!_alter h, Option.map_cast_apply]

@[simp]
theorem get!_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} [Inhabited (β k)]
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).get! k = (f (t.get? k)).get! := by
  simpa only [alter_eq_alter!] using get!_alter_self h

theorem getD_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α} {fallback : β k'}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getD k' fallback =
      if heq : compare k k' = .eq then
        f (t.get? k) |>.map (cast <| congrArg β <| compare_eq_iff_eq.mp heq) |>.getD fallback
      else
        t.getD k' fallback := by
  simp_to_model [alter, getD, get?] using List.getValueCastD_alterKey

theorem getD_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α} {fallback : β k'}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getD k' fallback =
      if heq : compare k k' = .eq then
        f (t.get? k) |>.map (cast <| congrArg β <| compare_eq_iff_eq.mp heq) |>.getD fallback
      else
        t.getD k' fallback := by
  simpa only [alter_eq_alter!] using getD_alter h

private theorem cast_eq_id {α : Type u} : cast (rfl : α = α) = id := by rfl

@[simp]
theorem getD_alter_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {fallback : β k}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getD k fallback = (f (t.get? k)).getD fallback := by
  simp only [getD_alter, h, compare_eq_iff_eq, reduceDIte, cast_eq_id, Option.map_id_fun, id_eq]

@[simp]
theorem getD_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {fallback : β k}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getD k fallback = (f (t.get? k)).getD fallback := by
  simpa only [alter_eq_alter!] using getD_alter_self h

theorem getKey?_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getKey? k' =
      if compare k k' = .eq then
        if (f (t.get? k)).isSome then some k else none
      else
        t.getKey? k' := by
  simp_to_model [alter, getKey?, get?] using List.getKey?_alterKey

theorem getKey?_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getKey? k' =
      if compare k k' = .eq then
        if (f (t.get? k)).isSome then some k else none
      else
        t.getKey? k' := by
  simpa only [alter_eq_alter!] using getKey?_alter h

theorem getKey?_alter_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getKey? k = if (f (t.get? k)).isSome then some k else none := by
  simp [getKey?_alter h]

theorem getKey?_alter!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getKey? k = if (f (t.get? k)).isSome then some k else none := by
  simpa only [alter_eq_alter!] using getKey?_alter_self h

theorem getKey!_alter [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getKey! k' =
      if compare k k' = .eq then
        if (f (t.get? k)).isSome then k else default
      else
        t.getKey! k' := by
  simp_to_model [alter, getKey!, get?] using List.getKey!_alterKey

theorem getKey!_alter! [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} : (t.alter! k f).getKey! k' =
      if compare k k' = .eq then
        if (f (t.get? k)).isSome then k else default
      else
        t.getKey! k' := by
  simpa only [alter_eq_alter!] using getKey!_alter h

theorem getKey!_alter_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getKey! k = if (f (t.get? k)).isSome then k else default := by
  simp [getKey!_alter h]

theorem getKey!_alter!_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getKey! k = if (f (t.get? k)).isSome then k else default := by
  simpa only [alter_eq_alter!] using getKey!_alter_self h

theorem getKey_alter [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ (t.alter k f h.balanced).1} :
    (t.alter k f h.balanced).1.getKey k' hc =
      if heq : compare k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' := by
  simp_to_model [alter, getKey] using List.getKey_alterKey

theorem getKey_alter! [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ t.alter! k f} :
    (t.alter! k f).getKey k' hc =
      if heq : compare k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter!_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' := by
  simpa only [alter_eq_alter!] using getKey_alter h (hc := by simpa [alter_eq_alter!])

@[simp]
theorem getKey_alter_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ (t.alter k f h.balanced).1} :
    (t.alter k f h.balanced).1.getKey k hc = k := by
  simp [getKey_alter h]

@[simp]
theorem getKey_alter!_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter! k f} :
    (t.alter! k f).getKey k hc = k := by
  simpa only [alter_eq_alter!] using getKey_alter_self h (hc := by simpa [alter_eq_alter!])

theorem getKeyD_alter [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' fallback : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getKeyD k' fallback =
      if compare k k' = .eq then
        if (f (t.get? k)).isSome then k else fallback
      else
        t.getKeyD k' fallback := by
  simp_to_model [alter, getKeyD, get?] using List.getKeyD_alterKey

theorem getKeyD_alter! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k k' fallback : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getKeyD k' fallback =
      if compare k k' = .eq then
        if (f (t.get? k)).isSome then k else fallback
      else
        t.getKeyD k' fallback := by
  simpa only [alter_eq_alter!] using getKeyD_alter h

@[simp]
theorem getKeyD_alter_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k : α}
    {fallback : α} {f : Option (β k) → Option (β k)} :
    (t.alter k f h.balanced).1.getKeyD k fallback =
      if (f (t.get? k)).isSome then k else fallback := by
  simp [getKeyD_alter h]

@[simp]
theorem getKeyD_alter!_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k : α}
    {fallback : α} {f : Option (β k) → Option (β k)} :
    (t.alter! k f).getKeyD k fallback = if (f (t.get? k)).isSome then k else fallback := by
  simpa only [alter_eq_alter!] using getKeyD_alter_self h

namespace Const

variable {β : Type v} {t : Impl α β}

theorem isEmpty_alter_eq_isEmpty_erase [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (Const.alter k f t h.balanced).1.isEmpty =
      ((t.erase k h.balanced).1.isEmpty && (f (get? t k)).isNone) := by
  simp_to_model [Const.alter, erase, isEmpty, Const.get?] using
    List.Const.isEmpty_alterKey_eq_isEmpty_eraseKey

theorem isEmpty_alter!_eq_isEmpty_erase [TransOrd α] (h : t.WF) {k : α}
    {f : Option β → Option β} :
    (alter! k f t).isEmpty = ((t.erase! k).isEmpty && (f (get? t k)).isNone) := by
  simpa only [alter_eq_alter!, erase_eq_erase!] using isEmpty_alter_eq_isEmpty_erase h

@[simp]
theorem isEmpty_alter [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (get? t k)).isNone) := by
  simp_to_model [Const.alter, isEmpty, size, contains, Const.get?] using List.Const.isEmpty_alterKey

@[simp]
theorem isEmpty_alter! [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter! k f t).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (get? t k)).isNone) := by
  simpa only [alter_eq_alter!] using isEmpty_alter h

theorem contains_alter [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.contains k' =
      if compare k k' = .eq then (f (get? t k)).isSome else t.contains k' := by
  simp_to_model [Const.alter, contains, Const.get?] using List.Const.containsKey_alterKey

theorem contains_alter! [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter! k f t).contains k' =
      if compare k k' = .eq then (f (get? t k)).isSome else t.contains k' := by
  simpa only [alter_eq_alter!] using contains_alter h

theorem mem_alter [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    k' ∈ (alter k f t h.balanced).1 ↔
      if compare k k' = .eq then (f (get? t k)).isSome = true else k' ∈ t := by
  simp [mem_iff_contains, contains_alter h]

theorem mem_alter! [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    k' ∈ alter! k f t ↔
      if compare k k' = .eq then (f (get? t k)).isSome = true else k' ∈ t := by
  simpa only [alter_eq_alter!] using mem_alter h

theorem mem_alter_of_compare_eq [TransOrd α] (h : t.WF) {k k': α} {f : Option β → Option β}
    (he : compare k k' = .eq) :
    k' ∈ (alter k f t h.balanced).1 ↔ (f (get? t k)).isSome := by
  rw [mem_alter h, if_pos he]

theorem mem_alter!_of_compare_eq [TransOrd α] (h : t.WF) {k k': α} {f : Option β → Option β}
    (he : compare k k' = .eq) :
    k' ∈ alter! k f t ↔ (f (get? t k)).isSome := by
  simpa only [alter_eq_alter!] using mem_alter_of_compare_eq h he

@[simp]
theorem contains_alter_self [TransOrd α] {k : α} (h : t.WF) {f : Option β → Option β} :
    (alter k f t h.balanced).1.contains k = (f (get? t k)).isSome := by
  simp only [contains_alter h, beq_iff_eq, compare_self, reduceIte]

@[simp]
theorem contains_alter!_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter! k f t).contains k = (f (get? t k)).isSome := by
  simpa only [alter_eq_alter!] using contains_alter_self h

@[simp]
theorem mem_alter_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    k ∈ (alter k f t h.balanced).1 ↔ (f (get? t k)).isSome := by
  rw [mem_iff_contains, contains_alter_self h]

@[simp]
theorem mem_alter!_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    k ∈ alter! k f t ↔ (f (get? t k)).isSome := by
  simpa only [alter_eq_alter!] using mem_alter_self h

theorem contains_alter_of_not_compare_eq [TransOrd α] (h : t.WF) {k k' : α}
    {f : Option β → Option β} (he : ¬ compare k k' = .eq) :
    (alter k f t h.balanced).1.contains k' = t.contains k' := by
  simp only [contains_alter h, he, beq_iff_eq, reduceIte]

theorem contains_alter!_of_not_compare_eq [TransOrd α] (h : t.WF) {k k' : α}
    {f : Option β → Option β} (he : ¬ compare k k' = .eq) :
    (alter! k f t).contains k' = t.contains k' := by
  simpa only [alter_eq_alter!] using contains_alter_of_not_compare_eq h he

theorem mem_alter_of_not_compare_eq [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    (he : ¬ compare k k' = .eq) :
    k' ∈ (alter k f t h.balanced).1 ↔ k' ∈ t := by
  simp only [mem_iff_contains, contains_alter_of_not_compare_eq h he]

theorem mem_alter!_of_not_compare_eq [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    (he : ¬ compare k k' = .eq) :
    k' ∈ alter! k f t ↔ k' ∈ t := by
  simpa only [alter_eq_alter!] using mem_alter_of_not_compare_eq h he

theorem size_alter [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.size =
      if k ∈ t ∧ (f (get? t k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (get? t k)).isSome then
        t.size + 1
      else
        t.size := by
  simp_to_model [Const.alter, size, Const.get?, contains] using List.Const.length_alterKey'

theorem size_alter! [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter! k f t).size =
      if k ∈ t ∧ (f (get? t k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (get? t k)).isSome then
        t.size + 1
      else
        t.size := by
  simpa only [alter_eq_alter!] using size_alter h

theorem size_alter_eq_add_one [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f (get? t k)).isSome) :
    (alter k f t h.balanced).1.size = t.size + 1 := by
  simp_all [mem_iff_contains, size_alter]

theorem size_alter!_eq_add_one [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f (get? t k)).isSome) :
    (alter! k f t).size = t.size + 1 := by
  simpa only [alter_eq_alter!] using size_alter_eq_add_one h h₁ h₂

theorem size_alter_eq_sub_one [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter k f t h.balanced).1.size = t.size - 1 := by
  simp_all [mem_iff_contains, size_alter]

theorem size_alter!_eq_sub_one [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter! k f t).size = t.size - 1 := by
  simpa only [alter_eq_alter!] using size_alter_eq_sub_one h h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter k f t h.balanced).1.size = t.size := by
  simp_all [mem_iff_contains, size_alter]

theorem size_alter!_eq_self_of_not_mem [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter! k f t).size = t.size := by
  simpa only [alter_eq_alter!] using size_alter_eq_self_of_not_mem h h₁ h₂

theorem size_alter_eq_self_of_mem [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isSome) :
    (alter k f t h.balanced).1.size = t.size := by
  simp_all [mem_iff_contains, size_alter, Option.isSome_iff_ne_none]

theorem size_alter!_eq_self_of_mem [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isSome) :
    (alter! k f t).size = t.size := by
  simpa only [alter_eq_alter!] using size_alter_eq_self_of_mem h h₁ h₂

theorem size_alter_le_size [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.size ≤ t.size + 1 := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_alter!_le_size [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter! k f t).size ≤ t.size + 1 := by
  simpa only [alter_eq_alter!] using size_alter_le_size h

theorem size_le_size_alter [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter k f t h.balanced).1.size := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_le_size_alter! [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter! k f t).size := by
  simpa only [alter_eq_alter!] using size_le_size_alter h

theorem get?_alter [TransOrd α] (h : t.WF) {k k' : α}
    {f : Option β → Option β} :
    get? (alter k f t h.balanced).1 k' =
      if compare k k' = .eq then
        f (get? t k)
      else
        get? t k' := by
  simp_to_model [Const.alter, Const.get?] using List.Const.getValue?_alterKey

theorem get?_alter! [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    get? (alter! k f t) k' =
      if compare k k' = .eq then
        f (get? t k)
      else
        get? t k' := by
  simpa only [alter_eq_alter!] using get?_alter h

@[simp]
theorem get?_alter_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    get? (alter k f t h.balanced).1 k = f (get? t k) := by
  simp [get?_alter h]

@[simp]
theorem get?_alter!_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    get? (alter! k f t) k = f (get? t k) := by
  simpa only [alter_eq_alter!] using get?_alter_self h

theorem get_alter [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter k f t h.balanced).1} :
    get (alter k f t h.balanced).1 k' hc =
      if heq : compare k k' = .eq then
        haveI h' : (f (get? t k)).isSome := mem_alter_of_compare_eq h heq |>.mp hc
        (f (get? t k)).get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        get t k' h' := by
  simp_to_model [Const.alter, Const.get, Const.get?] using List.Const.getValue_alterKey

theorem get_alter! [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter! k f t)} :
    get (alter! k f t) k' hc =
      if heq : compare k k' = .eq then
        haveI h' : (f (get? t k)).isSome := mem_alter!_of_compare_eq h heq |>.mp hc
        (f (get? t k)).get h'
      else
        haveI h' : k' ∈ t := mem_alter!_of_not_compare_eq h heq |>.mp hc
        get t k' h' := by
  simpa only [alter_eq_alter!] using get_alter h (hc := by simpa [alter_eq_alter!])

@[simp]
theorem get_alter_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ (alter k f t h.balanced).1} :
    haveI h' : (f (get? t k)).isSome := mem_alter_self h |>.mp hc
    get (alter k f t h.balanced).1 k hc = (f (get? t k)).get h' := by
  simp_to_model [Const.alter, Const.get, Const.get?] using List.Const.getValue_alterKey_self

@[simp]
theorem get_alter!_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ alter! k f t} :
    haveI h' : (f (get? t k)).isSome := mem_alter!_self h |>.mp hc
    get (alter! k f t) k hc = (f (get? t k)).get h' := by
  simpa only [alter_eq_alter!] using get_alter_self h (hc := by simpa [alter_eq_alter!])

theorem get!_alter [TransOrd α] (h : t.WF) {k k' : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter k f t h.balanced).1 k' =
      if compare k k' = .eq then
        (f (get? t k)).get!
      else
        get! t k' := by
  simp_to_model [Const.alter, Const.get!, Const.get?] using List.Const.getValue!_alterKey

theorem get!_alter! [TransOrd α] (h : t.WF) {k k' : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter! k f t) k' =
      if compare k k' = .eq then
        (f (get? t k)).get!
      else
        get! t k' := by
  simpa only [alter_eq_alter!] using get!_alter h

@[simp]
theorem get!_alter_self [TransOrd α] (h : t.WF) {k : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter k f t h.balanced).1 k = (f (get? t k)).get! := by
  simp [get!_alter h, Option.map_cast_apply]

@[simp]
theorem get!_alter!_self [TransOrd α] (h : t.WF) {k : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter! k f t) k = (f (get? t k)).get! := by
  simpa only [alter_eq_alter!] using get!_alter_self h

theorem getD_alter [TransOrd α] (h : t.WF) {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter k f t h.balanced).1 k' fallback =
      if compare k k' = .eq then
        f (get? t k) |>.getD fallback
      else
        getD t k' fallback := by
  simp_to_model [Const.alter, Const.getD, Const.get?] using List.Const.getValueD_alterKey

theorem getD_alter! [TransOrd α] (h : t.WF) {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter! k f t) k' fallback =
      if compare k k' = .eq then
        f (get? t k) |>.getD fallback
      else
        getD t k' fallback := by
  simpa only [alter_eq_alter!] using getD_alter h

@[simp]
theorem getD_alter_self [TransOrd α] (h : t.WF) {k : α} {fallback : β} {f : Option β → Option β} :
    getD (alter k f t h.balanced).1 k fallback = (f (get? t k)).getD fallback := by
  simp only [h, getD_alter, compare_self, beq_iff_eq, reduceIte]

@[simp]
theorem getD_alter!_self [TransOrd α] (h : t.WF) {k : α} {fallback : β} {f : Option β → Option β} :
    getD (alter! k f t) k fallback = (f (get? t k)).getD fallback := by
  simpa only [alter_eq_alter!] using getD_alter_self h

theorem getKey?_alter [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.getKey? k' =
      if compare k k' = .eq then
        if (f (get? t k)).isSome then some k else none
      else
        t.getKey? k' := by
  simp_to_model [Const.alter, getKey?, Const.get?] using List.Const.getKey?_alterKey

theorem getKey?_alter! [TransOrd α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter! k f t).getKey? k' =
      if compare k k' = .eq then
        if (f (get? t k)).isSome then some k else none
      else
        t.getKey? k' := by
  simpa only [alter_eq_alter!] using getKey?_alter h

theorem getKey?_alter_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.getKey? k = if (f (get? t k)).isSome then some k else none := by
  simp [getKey?_alter h]

theorem getKey?_alter!_self [TransOrd α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter! k f t).getKey? k = if (f (get? t k)).isSome then some k else none := by
  simpa only [alter_eq_alter!] using getKey?_alter_self h

theorem getKey!_alter [TransOrd α] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.getKey! k' =
      if compare k k' = .eq then
        if (f (get? t k)).isSome then k else default
      else
        t.getKey! k' := by
  simp_to_model [Const.alter, getKey!, Const.get?] using List.Const.getKey!_alterKey

theorem getKey!_alter! [TransOrd α] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter! k f t).getKey! k' =
      if compare k k' = .eq then
        if (f (get? t k)).isSome then k else default
      else
        t.getKey! k' := by
  simpa only [alter_eq_alter!] using getKey!_alter h

theorem getKey!_alter_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.getKey! k = if (f (get? t k)).isSome then k else default := by
  simp [getKey!_alter h]

theorem getKey!_alter!_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α}
    {f : Option β → Option β} :
    (alter! k f t).getKey! k = if (f (get? t k)).isSome then k else default := by
  simpa only [alter_eq_alter!] using getKey!_alter_self h

theorem getKey_alter [TransOrd α] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter k f t h.balanced).1} :
    (alter k f t h.balanced).1.getKey k' hc =
      if heq : compare k k' = .eq then
        k
      else
        haveI h' : t.contains k' := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' := by
  simp_to_model [Const.alter, getKey, Const.get?] using List.Const.getKey_alterKey

theorem getKey_alter! [TransOrd α] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter! k f t} :
    (alter! k f t).getKey k' hc =
      if heq : compare k k' = .eq then
        k
      else
        haveI h' : t.contains k' := mem_alter!_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' := by
  simpa only [alter_eq_alter!] using getKey_alter h (hc := by simpa [alter_eq_alter!])

@[simp]
theorem getKey_alter_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ (alter k f t h.balanced).1} :
    (alter k f t h.balanced).1.getKey k hc = k := by
  simp [getKey_alter h]

@[simp]
theorem getKey_alter!_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ alter! k f t} :
    (alter! k f t).getKey k hc = k := by
  simpa only [alter_eq_alter!] using getKey_alter_self h (hc := by simpa [alter_eq_alter!])

theorem getKeyD_alter [TransOrd α] (h : t.WF) {k k' fallback : α} {f : Option β → Option β} :
    (alter k f t h.balanced).1.getKeyD k' fallback =
      if compare k k' = .eq then
        if (f (get? t k)).isSome then k else fallback
      else
        t.getKeyD k' fallback := by
  simp_to_model [Const.alter, getKeyD, Const.get?] using List.Const.getKeyD_alterKey

theorem getKeyD_alter! [TransOrd α] (h : t.WF) {k k' fallback : α} {f : Option β → Option β} :
    (alter! k f t).getKeyD k' fallback =
      if compare k k' = .eq then
        if (f (get? t k)).isSome then k else fallback
      else
        t.getKeyD k' fallback := by
  simpa only [alter_eq_alter!] using getKeyD_alter h

@[simp]
theorem getKeyD_alter_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter k f t h.balanced).1.getKeyD k fallback =
      if (f (get? t k)).isSome then k else fallback := by
  simp [getKeyD_alter h]

@[simp]
theorem getKeyD_alter!_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter! k f t).getKeyD k fallback = if (f (get? t k)).isSome then k else fallback := by
  simpa only [alter_eq_alter!] using getKeyD_alter_self h

end Const

end Alter

section Modify

variable [TransOrd α]

section Dependent

variable [LawfulEqOrd α]

@[simp]
theorem isEmpty_modify (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).isEmpty = t.isEmpty := by
  simp_to_model [modify, isEmpty] using List.isEmpty_modifyKey

theorem contains_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    (t.modify k f).contains k' = t.contains k' := by
  simp_to_model [modify, contains] using List.containsKey_modifyKey

theorem mem_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    k' ∈ t.modify k f ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_modify h]

theorem size_modify (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).size = t.size := by
  simp_to_model [modify, size] using List.length_modifyKey

theorem get?_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    (t.modify k f).get? k' =
      if h : compare k k' = .eq then
        (cast (congrArg (Option ∘ β) (compare_eq_iff_eq.mp h)) ((t.get? k).map f))
      else
        t.get? k' := by
  simp_to_model [modify, get?] using List.getValueCast?_modifyKey

@[simp]
theorem get?_modify_self (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).get? k = (t.get? k).map f := by
  simp_to_model [modify, get?] using List.getValueCast?_modifyKey_self

theorem get_modify (h : t.WF) {k k' : α} {f : β k → β k} {hc : k' ∈ t.modify k f} :
    (t.modify k f).get k' hc =
      if heq : compare k k' = .eq then
        haveI h' : k ∈ t := by rwa [mem_modify h, ← compare_eq_iff_eq.mp heq] at hc
        cast (congrArg β (compare_eq_iff_eq.mp heq)) <| f (t.get k h')
      else
        haveI h' : k' ∈ t := (mem_modify h).mp hc
        t.get k' h' := by
  simp_to_model [modify, get] using List.getValueCast_modifyKey

@[simp]
theorem get_modify_self (h : t.WF) {k : α} {f : β k → β k} {hc : k ∈ t.modify k f} :
    haveI h' : k ∈ t := mem_modify h |>.mp hc
    (t.modify k f).get k hc = f (t.get k h') := by
  simp_to_model [modify, get] using List.getValueCast_modifyKey_self

theorem get!_modify (h : t.WF) {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (t.modify k f).get! k' =
      if heq : compare k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β (compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' := by
  simp_to_model [modify, get?, get!] using List.getValueCast!_modifyKey

@[simp]
theorem get!_modify_self (h : t.WF) {k : α} [Inhabited (β k)] {f : β k → β k} :
    (t.modify k f).get! k = ((t.get? k).map f).get! := by
  simp_to_model [modify, get?, get!] using List.getValueCast!_modifyKey_self

theorem getD_modify (h : t.WF) {k k' : α} {fallback : β k'} {f : β k → β k} :
    (t.modify k f).getD k' fallback =
      if heq : compare k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β <| compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback := by
  simp_to_model [modify, getD, get?] using List.getValueCastD_modifyKey

@[simp]
theorem getD_modify_self (h : t.WF) {k : α} {fallback : β k} {f : β k → β k} :
    (t.modify k f).getD k fallback = ((t.get? k).map f).getD fallback := by
  simp_to_model [modify, getD, get?] using List.getValueCastD_modifyKey_self

theorem getKey?_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey? k' =
      if compare k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' := by
  simp_to_model [modify, getKey?, contains] using List.getKey?_modifyKey

theorem getKey?_modify_self (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).getKey? k = if k ∈ t then some k else none := by
  simp_to_model [modify, getKey?, contains] using List.getKey?_modifyKey_self

theorem getKey!_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey! k' =
      if compare k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' := by
  simp_to_model [modify, getKey!, contains] using List.getKey!_modifyKey

theorem getKey!_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β k → β k} :
    (t.modify k f).getKey! k = if k ∈ t then k else default := by
  simp_to_model [modify, getKey!, contains] using List.getKey!_modifyKey_self

theorem getKey_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β k → β k}
    {hc : k' ∈ t.modify k f} :
    (t.modify k f).getKey k' hc =
      if compare k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        t.getKey k' h' := by
  simp_to_model [modify, getKey] using List.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β k → β k}
    {hc : k ∈ t.modify k f} : (t.modify k f).getKey k hc = k := by
  simp_to_model [modify, getKey] using List.getKey_modifyKey_self

theorem getKeyD_modify (h : t.WF) {k k' fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k' fallback =
      if compare k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback := by
  simp_to_model [modify, getKeyD, contains] using List.getKeyD_modifyKey

theorem getKeyD_modify_self (h : t.WF) [Inhabited α] {k fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k fallback = if k ∈ t then k else fallback := by
  simp_to_model [modify, getKeyD, contains] using List.getKeyD_modifyKey_self

end Dependent

namespace Const

variable {β : Type v} {t : Impl α β}

@[simp]
theorem isEmpty_modify (h : t.WF) {k : α} {f : β → β} :
    (modify k f t).isEmpty = t.isEmpty := by
  simp_to_model [Const.modify, isEmpty] using List.Const.isEmpty_modifyKey

theorem contains_modify (h : t.WF) {k k' : α} {f : β → β} :
    (modify k f t).contains k' = t.contains k' := by
  simp_to_model [Const.modify, contains] using List.Const.containsKey_modifyKey

theorem mem_modify (h : t.WF) {k k' : α} {f : β → β} :
    k' ∈ modify k f t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_modify h]

theorem size_modify (h : t.WF) {k : α} {f : β → β} :
    (modify k f t).size = t.size := by
  simp_to_model [Const.modify, size] using List.Const.length_modifyKey

theorem get?_modify (h : t.WF) {k k' : α} {f : β → β} :
    get? (modify k f t) k' =
      if compare k k' = .eq then
        (get? t k).map f
      else
        get? t k' := by
  simp_to_model [Const.modify, Const.get?] using List.Const.getValue?_modifyKey

@[simp]
theorem get?_modify_self (h : t.WF) {k : α} {f : β → β} :
    get? (modify k f t) k = (get? t k).map f := by
  simp_to_model [Const.modify, Const.get?] using List.Const.getValue?_modifyKey_self

theorem get_modify (h : t.WF) {k k' : α} {f : β → β} {hc : k' ∈ modify k f t} :
    get (modify k f t) k' hc =
      if heq : compare k k' = .eq then
        haveI h' : k ∈ t := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        f (get t k h')
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        get t k' h' := by
  simp_to_model [Const.modify, Const.get] using List.Const.getValue_modifyKey

@[simp]
theorem get_modify_self (h : t.WF) {k : α} {f : β → β} {hc : k ∈ modify k f t} :
    haveI h' : k ∈ t := mem_modify h |>.mp hc
    get (modify k f t) k hc = f (get t k h') := by
  simp_to_model [Const.modify, Const.get] using List.Const.getValue_modifyKey_self

theorem get!_modify (h : t.WF) {k k' : α} [hi : Inhabited β] {f : β → β} :
    get! (modify k f t) k' =
      if compare k k' = .eq then
        get? t k |>.map f |>.get!
      else
        get! t k' := by
  simp_to_model [Const.modify, Const.get!, Const.get?] using List.Const.getValue!_modifyKey

@[simp]
theorem get!_modify_self (h : t.WF) {k : α} [Inhabited β] {f : β → β} :
    get! (modify k f t) k = ((get? t k).map f).get! := by
  simp_to_model [Const.modify, Const.get?, Const.get!] using List.Const.getValue!_modifyKey_self

theorem getD_modify (h : t.WF) {k k' : α} {fallback : β} {f : β → β} :
    getD (modify k f t) k' fallback =
      if compare k k' = .eq then
        get? t k |>.map f |>.getD fallback
      else
        getD t k' fallback := by
  simp_to_model [Const.modify, Const.getD, Const.get?] using List.Const.getValueD_modifyKey

@[simp]
theorem getD_modify_self (h : t.WF) {k : α} {fallback : β} {f : β → β} :
    getD (modify k f t) k fallback = ((get? t k).map f).getD fallback := by
  simp_to_model [Const.modify, Const.getD, Const.get?] using List.Const.getValueD_modifyKey_self

theorem getKey?_modify (h : t.WF) {k k' : α} {f : β → β} :
    (modify k f t).getKey? k' =
      if compare k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' := by
  simp_to_model [Const.modify, getKey?, contains] using List.Const.getKey?_modifyKey

theorem getKey?_modify_self (h : t.WF) {k : α} {f : β → β} :
    (modify k f t).getKey? k = if k ∈ t then some k else none := by
  simp_to_model [Const.modify, getKey?, contains] using List.Const.getKey?_modifyKey_self

theorem getKey!_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β → β} :
    (modify k f t).getKey! k' =
      if compare k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' := by
  simp_to_model [Const.modify, getKey!, contains] using List.Const.getKey!_modifyKey

theorem getKey!_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β → β} :
    (modify k f t).getKey! k = if k ∈ t then k else default := by
  simp_to_model [Const.modify, getKey!, contains] using List.Const.getKey!_modifyKey_self

theorem getKey_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify k f t} :
    (modify k f t).getKey k' hc =
      if compare k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        t.getKey k' h' := by
  simp_to_model [Const.modify, getKey] using List.Const.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify k f t} : (modify k f t).getKey k hc = k := by
  simp_to_model [Const.modify, getKey] using List.Const.getKey_modifyKey_self

theorem getKeyD_modify (h : t.WF) {k k' fallback : α} {f : β → β} :
    (modify k f t).getKeyD k' fallback =
      if compare k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback := by
  simp_to_model [Const.modify, getKeyD, contains] using List.Const.getKeyD_modifyKey

theorem getKeyD_modify_self (h : t.WF) [Inhabited α] {k fallback : α} {f : β → β} :
    (modify k f t).getKeyD k fallback = if k ∈ t then k else fallback := by
  simp_to_model [Const.modify, getKeyD, contains] using List.Const.getKeyD_modifyKey_self

end Const

end Modify

section Min

theorem minKey?_empty :
    (empty : Impl α β).minKey? = none := by
  unfold minKey?; rfl

theorem minKey?_of_isEmpty [TransOrd α] (h : t.WF) :
    (he : t.isEmpty) → t.minKey? = none := by
  simp_to_model using List.minKey?_of_isEmpty

theorem minKey?_eq_none_iff [TransOrd α] (h : t.WF) :
    t.minKey? = none ↔ t.isEmpty := by
  simp_to_model using List.minKey?_eq_none_iff_isEmpty

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransOrd α] (h : t.WF) {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (compare km k).isLE := by
  simp_to_model using List.minKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem minKey?_eq_some_iff_mem_and_forall [TransOrd α] [LawfulEqOrd α] (h : t.WF) {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (compare km k).isLE := by
  simp_to_model using List.minKey?_eq_some_iff_mem_and_forall

theorem isNone_minKey?_eq_isEmpty [TransOrd α] (h : t.WF) :
    t.minKey?.isNone = t.isEmpty := by
  simp_to_model using List.isNone_minKey?_eq_isEmpty

theorem isSome_minKey?_eq_not_isEmpty [TransOrd α] (h : t.WF) :
    t.minKey?.isSome = !t.isEmpty := by
  simp_to_model using List.isSome_minKey?_eq_not_isEmpty

theorem isSome_minKey?_iff_isEmpty_eq_false [TransOrd α] (h : t.WF) :
    t.minKey?.isSome ↔ t.isEmpty = false := by
  simp [isSome_minKey?_eq_not_isEmpty h]

theorem minKey?_insert [TransOrd α] (h : t.WF) {k v} :
    (t.insert k v h.balanced).impl.minKey? =
      some (t.minKey?.elim k fun k' => if compare k k'|>.isLE then k else k') := by
  simp_to_model [insert] using List.minKey?_insertEntry

theorem minKey?_insert! [TransOrd α] (h : t.WF) {k v} :
    (t.insert! k v).minKey? =
      some (t.minKey?.elim k fun k' => if compare k k'|>.isLE then k else k') := by
  simpa only [insert_eq_insert!] using minKey?_insert h

theorem isSome_minKey?_insert [TransOrd α] (h : t.WF) {k v} :
    (t.insert k v h.balanced).impl.minKey?.isSome := by
  simp_to_model [insert] using List.isSome_minKey?_insertEntry

theorem isSome_minKey?_insert! [TransOrd α] (h : t.WF) {k v} :
    (t.insert! k v).minKey?.isSome := by
  simpa only [insert_eq_insert!] using isSome_minKey?_insert h

theorem minKey?_insert_le_minKey? [TransOrd α] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v h.balanced |>.impl.minKey? |>.get <| isSome_minKey?_insert h) = kmi) →
    compare kmi km |>.isLE := by
  simp_to_model [insert] using List.minKey?_insertEntry_le_minKey?

theorem minKey?_insert!_le_minKey? [TransOrd α] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert! k v |>.minKey? |>.get <| isSome_minKey?_insert! h) = kmi) →
    compare kmi km |>.isLE := by
  simpa only [insert_eq_insert!] using minKey?_insert_le_minKey? h

theorem minKey?_insert_le_self [TransOrd α] (h : t.WF) {k v kmi} :
    (hkmi : (t.insert k v h.balanced |>.impl.minKey?.get <| isSome_minKey?_insert h) = kmi) →
    compare kmi k |>.isLE := by
  simp_to_model [insert] using List.minKey?_insertEntry_le_self

theorem minKey?_insert!_le_self [TransOrd α] (h : t.WF) {k v kmi} :
    (hkmi : (t.insert! k v |>.minKey?.get <| isSome_minKey?_insert! h) = kmi) →
    compare kmi k |>.isLE := by
  simpa only [insert_eq_insert!] using minKey?_insert_le_self h

theorem contains_minKey? [TransOrd α] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) →
    t.contains km := by
  simp_to_model using List.containsKey_minKey?

theorem minKey?_mem [TransOrd α] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) →
    km ∈ t := by
  simp_to_model using List.containsKey_minKey?

theorem isSome_minKey?_of_contains [TransOrd α] (h : t.WF) {k} :
    (hc : t.contains k) → t.minKey?.isSome := by
  simp_to_model using List.isSome_minKey?_of_containsKey

theorem isSome_minKey?_of_mem [TransOrd α] (h : t.WF) {k} :
    k ∈ t → t.minKey?.isSome :=
  isSome_minKey?_of_contains h

theorem minKey?_le_of_contains [TransOrd α] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains h hc) = km) →
    compare km k |>.isLE := by
  simp_to_model using minKey?_le_of_containsKey

theorem minKey?_le_of_mem [TransOrd α] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem h hc) = km) →
    compare km k |>.isLE :=
  minKey?_le_of_contains h

theorem le_minKey? [TransOrd α] {k} (h : t.WF) :
    (∀ k', t.minKey? = some k' → (compare k k').isLE) ↔
      (∀ k', k' ∈ t → (compare k k').isLE) := by
  simp_to_model using List.le_minKey?

theorem getKey?_minKey? [TransOrd α] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km := by
  simp_to_model using List.getKey?_minKey?

@[simp]
theorem minKey?_bind_getKey? [TransOrd α] (h : t.WF) :
    t.minKey?.bind t.getKey? = t.minKey? := by
  change (t.minKey?.bind fun k => t.getKey? k) = t.minKey?
  simp_to_model using List.minKey?_bind_getKey?

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransOrd α] (h : t.WF) {k} :
    (t.erase k h.balanced |>.impl.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ compare k km = .eq := by
  simp_to_model [erase] using minKey?_eraseKey_eq_iff_beq_minKey?_eq_false

theorem minKey?_erase!_eq_iff_not_compare_eq_minKey? [TransOrd α] (h : t.WF) {k} :
    (t.erase! k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ compare k km = .eq := by
  simpa only [erase_eq_erase!] using minKey?_erase_eq_iff_not_compare_eq_minKey? h

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransOrd α] (h : t.WF) {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ compare k km = .eq) →
    (t.erase k h.balanced |>.impl.minKey?) = t.minKey? := by
  simp_to_model [erase] using minKey?_eraseKey_eq_of_beq_minKey?_eq_false

theorem minKey?_erase!_eq_of_not_compare_eq_minKey? [TransOrd α] (h : t.WF) {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ compare k km = .eq) →
    (t.erase! k |>.minKey?) = t.minKey? := by
  simpa only [erase_eq_erase!] using minKey?_erase_eq_of_not_compare_eq_minKey? h

theorem isSome_minKey?_of_isSome_minKey?_erase [TransOrd α] (h : t.WF) {k} :
    (hs : t.erase k h.balanced |>.impl.minKey?.isSome) →
    t.minKey?.isSome := by
  simp_to_model [erase] using isSome_minKey?_of_isSome_minKey?_eraseKey

theorem isSome_minKey?_of_isSome_minKey?_erase! [TransOrd α] (h : t.WF) {k} :
    (hs : t.erase! k |>.minKey?.isSome) →
    t.minKey?.isSome := by
  simpa only [erase_eq_erase!] using isSome_minKey?_of_isSome_minKey?_erase h

theorem minKey?_le_minKey?_erase [TransOrd α] (h : t.WF) {k km kme} :
    (hkme : (t.erase k h.balanced |>.impl.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase h <| hkme ▸ Option.isSome_some) = km) →
    compare km kme |>.isLE := by
  simp_to_model [erase] using minKey?_le_minKey?_eraseKey

theorem minKey?_le_minKey?_erase! [TransOrd α] (h : t.WF) {k km kme} :
    (hkme : (t.erase! k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase! h <| hkme ▸ Option.isSome_some) = km) →
    compare km kme |>.isLE := by
  simpa only [erase_eq_erase!] using minKey?_le_minKey?_erase h

theorem minKey?_insertIfNew [TransOrd α] (h : t.WF) {k v} :
    (t.insertIfNew k v h.balanced).impl.minKey? =
      t.minKey?.elim k fun k' => if compare k k' = .lt then k else k' := by
  simp_to_model [insertIfNew] using List.minKey?_insertEntryIfNew

theorem minKey?_insertIfNew! [TransOrd α] (h : t.WF) {k v} :
    (t.insertIfNew! k v).minKey? =
      t.minKey?.elim k fun k' => if compare k k' = .lt then k else k' := by
  simpa only [insertIfNew_eq_insertIfNew!] using minKey?_insertIfNew h

theorem isSome_minKey?_insertIfNew [TransOrd α] (h : t.WF) {k v} :
    (t.insertIfNew k v h.balanced).impl.minKey?.isSome := by
  simp_to_model [insertIfNew] using List.isSome_minKey?_insertEntryIfNew

theorem isSome_minKey?_insertIfNew! [TransOrd α] (h : t.WF) {k v} :
    (t.insertIfNew! k v).minKey?.isSome := by
  simpa only [insertIfNew_eq_insertIfNew!] using isSome_minKey?_insertIfNew h

theorem minKey?_insertIfNew_le_minKey? [TransOrd α] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v h.balanced |>.impl.minKey? |>.get <| isSome_minKey?_insertIfNew h) = kmi) →
    compare kmi km |>.isLE := by
  simp_to_model [insertIfNew] using List.minKey?_insertEntryIfNew_le_minKey?

theorem minKey?_insertIfNew!_le_minKey? [TransOrd α] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew! k v |>.minKey? |>.get <| isSome_minKey?_insertIfNew! h) = kmi) →
    compare kmi km |>.isLE := by
  simpa only [insertIfNew_eq_insertIfNew!] using minKey?_insertIfNew_le_minKey? h

theorem minKey?_insertIfNew_le_self [TransOrd α] (h : t.WF) {k v kmi} :
    (hkmi : (t.insertIfNew k v h.balanced |>.impl.minKey?.get <| isSome_minKey?_insertIfNew h) = kmi) →
    compare kmi k |>.isLE := by
  simp_to_model [insertIfNew] using List.minKey?_insertEntryIfNew_le_self

theorem minKey?_insertIfNew!_le_self [TransOrd α] (h : t.WF) {k v kmi} :
    (hkmi : (t.insertIfNew! k v |>.minKey?.get <| isSome_minKey?_insertIfNew! h) = kmi) →
    compare kmi k |>.isLE := by
  simpa only [insertIfNew_eq_insertIfNew!] using minKey?_insertIfNew_le_self h

theorem minKey?_modify [TransOrd α] [LawfulEqOrd α] {k f} (h : t.WF) :
    (t.modify k f).minKey? = t.minKey? := by
  simp_to_model [modify] using List.minKey?_modifyKey

theorem minKey?_alter_eq_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k f} :
    (t.alter k f h.balanced).impl.minKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simp_to_model [alter] using List.minKey?_alterKey_eq_self

theorem minKey?_alter!_eq_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k f} :
    (t.alter! k f).minKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simpa only [alter_eq_alter!] using minKey?_alter_eq_self h

namespace Const

variable {β : Type v} {t : Impl α β}

theorem minKey?_modify [TransOrd α] (h : t.WF) {k f} :
    (Const.modify k f t).minKey? = t.minKey?.map fun km => if compare km k = .eq then k else km := by
  simp_to_model [Const.modify] using List.Const.minKey?_modifyKey

theorem minKey?_modify_eq_minKey? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k f} :
    (Const.modify k f t).minKey? = t.minKey? := by
  simp_to_model [Const.modify] using List.Const.minKey?_modifyKey_eq_minKey?

theorem isSome_minKey?_modify [TransOrd α] {k f}  (h : t.WF) :
    (Const.modify k f t).minKey?.isSome = !t.isEmpty := by
  simp_to_model [Const.modify] using List.Const.isSome_minKey?_modifyKey

theorem isSome_minKey?_modify_eq_isSome [TransOrd α] (h : t.WF) {k f} :
    (Const.modify k f t).minKey?.isSome = t.minKey?.isSome := by
  simp_to_model [Const.modify] using List.Const.isSome_minKey?_modifyKey_eq_isSome

theorem compare_minKey?_modify_eq [TransOrd α] (h : t.WF) {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (Const.modify k f t |>.minKey? |>.get <|
        (isSome_minKey?_modify_eq_isSome h).trans <| hkm ▸ Option.isSome_some) = kmm) →
    compare kmm km = .eq := by
  simp_to_model [Const.modify] using List.Const.minKey?_modifyKey_beq

theorem minKey?_alter_eq_self [TransOrd α] (h : t.WF) {k f} :
    (Const.alter k f t h.balanced).impl.minKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simp_to_model [Const.alter] using List.Const.minKey?_alterKey_eq_self

theorem minKey?_alter!_eq_self [TransOrd α] (h : t.WF) {k f} :
    (Const.alter! k f t).minKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simpa [alter_eq_alter!] using minKey?_alter_eq_self h

end Const

theorem minKey_eq_get_minKey? [TransOrd α] (h : t.WF) {he} :
    t.minKey he = t.minKey?.get (isSome_minKey?_iff_isEmpty_eq_false h |>.mpr he) := by
  simp_to_model [minKey, minKey?] using List.minKey_eq_get_minKey?

theorem minKey?_eq_some_minKey [TransOrd α] (h : t.WF) {he} :
    t.minKey? = some (t.minKey he) := by
  simp_to_model [minKey, minKey?] using List.minKey?_eq_some_minKey

theorem minKey_eq_iff_getKey?_eq_self_and_forall [TransOrd α] (h : t.WF) {he km} :
    t.minKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (compare km k).isLE := by
  simp_to_model [minKey, getKey?, contains] using List.minKey_eq_iff_getKey?_eq_self_and_forall

theorem minKey_eq_some_iff_mem_and_forall [TransOrd α] [LawfulEqOrd α] (h : t.WF) {he km} :
    t.minKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (compare km k).isLE := by
  simp_to_model [minKey, contains] using List.minKey_eq_some_iff_mem_and_forall

theorem minKey_insert [TransOrd α] (h : t.WF) {k v} :
    (t.insert k v h.balanced).impl.minKey (isEmpty_insert h) =
      t.minKey?.elim k fun k' => if compare k k'|>.isLE then k else k' := by
  simp_to_model [insert, minKey, minKey?] using List.minKey_insertEntry

theorem minKey_insert_le_minKey [TransOrd α] (h : t.WF) {k v he} :
    compare (t.insert k v h.balanced |>.impl.minKey <| isEmpty_insert h) (t.minKey he) |>.isLE := by
  simp_to_model [minKey, insert] using List.minKey_insertEntry_le_minKey

theorem minKey_insert_le_self [TransOrd α] (h : t.WF) {k v} :
    compare (t.insert k v h.balanced |>.impl.minKey <| isEmpty_insert h) k |>.isLE := by
  simp_to_model [minKey, insert] using List.minKey_insertEntry_le_self

theorem contains_minKey [TransOrd α] (h : t.WF) {he} :
    t.contains (t.minKey he) := by
  simp_to_model [minKey, contains] using List.containsKey_minKey

theorem minKey_mem [TransOrd α] (h : t.WF) {he} :
    t.minKey he ∈ t :=
  contains_minKey h

theorem minKey_le_of_contains [TransOrd α] (h : t.WF) {k} :
    (hc : t.contains k) →
    compare (t.minKey <| (isEmpty_eq_false_iff_exists_contains_eq_true h).mpr ⟨k, hc⟩) k |>.isLE := by
   simp_to_model [minKey, contains] using minKey_le_of_containsKey

theorem minKey_le_of_mem [TransOrd α] (h : t.WF) {k} (hc : k ∈ t) :
    compare (t.minKey <| (isEmpty_eq_false_iff_exists_contains_eq_true h).mpr ⟨k, hc⟩) k |>.isLE :=
  minKey_le_of_contains h hc

theorem le_minKey [TransOrd α] (h : t.WF) {k he} :
    (compare k (t.minKey he)).isLE ↔ (∀ k', k' ∈ t → (compare k k').isLE) := by
  simp_to_model [minKey, contains] using List.le_minKey

theorem getKey?_minKey [TransOrd α] (h : t.WF) {he} :
    t.getKey? (t.minKey he) = some (t.minKey he) := by
  simp_to_model [getKey?, minKey] using List.getKey?_minKey

theorem getKey_minKey [TransOrd α] (h : t.WF) {he hc} :
    t.getKey (t.minKey he) hc = t.minKey he := by
  simp_to_model [getKey, minKey] using List.getKey_minKey

theorem getKey!_minKey [TransOrd α] [Inhabited α] (h : t.WF) {he} :
    t.getKey! (t.minKey he) = t.minKey he := by
  simp_to_model [getKey!, minKey] using List.getKey!_minKey

theorem getKeyD_minKey [TransOrd α] (h : t.WF) {he fallback} :
    t.getKeyD (t.minKey he) fallback = t.minKey he := by
  simp_to_model [getKeyD, minKey] using List.getKeyD_minKey

theorem minKey_erase_eq_iff_not_compare_eq_minKey [TransOrd α] (h : t.WF) {k he} :
    (t.erase k h.balanced |>.impl.minKey he) =
        t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false h he) ↔
      ¬ compare k (t.minKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false h he) = .eq := by
  simp_to_model [minKey, erase] using List.minKey_eraseKey_eq_iff_beq_minKey_eq_false

theorem minKey_erase_eq_of_not_compare_eq_minKey [TransOrd α] (h : t.WF) {k he} :
    (hc : ¬ compare k (t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false h he)) = .eq) →
    (t.erase k h.balanced |>.impl.minKey he) =
      t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false h he) := by
  simp_to_model [minKey, erase] using List.minKey_eraseKey_eq_of_beq_minKey_eq_false

theorem minKey_le_minKey_erase [TransOrd α] (h : t.WF) {k he} :
    compare (t.minKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false h he)
      (t.erase k h.balanced |>.impl.minKey he) |>.isLE := by
  simp_to_model [minKey, erase] using List.minKey_le_minKey_erase

theorem minKey_insertIfNew [TransOrd α] (h : t.WF) {k v} :
    (t.insertIfNew k v h.balanced).impl.minKey (isEmpty_insertIfNew h) =
      t.minKey?.elim k fun k' => if compare k k' = .lt then k else k' := by
  simp_to_model [minKey, minKey?, insertIfNew] using List.minKey_insertEntryIfNew

theorem minKey_insertIfNew_le_minKey [TransOrd α] (h : t.WF) {k v he} :
    compare (t.insertIfNew k v h.balanced |>.impl.minKey <| isEmpty_insertIfNew h)
      (t.minKey he) |>.isLE := by
  simp_to_model [minKey, insertIfNew] using List.minKey_insertEntryIfNew_le_minKey

theorem minKey_insertIfNew_le_self [TransOrd α] (h : t.WF) {k v} :
    compare (t.insertIfNew k v h.balanced |>.impl.minKey <| isEmpty_insertIfNew h) k |>.isLE := by
  simp_to_model [minKey, insertIfNew] using List.minKey_insertEntryIfNew_le_self

theorem minKey_modify [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k f he} :
    (t.modify k f).minKey he = t.minKey (isEmpty_modify h ▸ he):= by
  simp_to_model [minKey, modify] using List.minKey_modifyKey

theorem minKey_alter_eq_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k f he} :
    (t.alter k f h.balanced).impl.minKey he = k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simp_to_model [minKey, alter, get?, contains] using List.minKey_alterKey_eq_self

namespace Const

variable {β : Type v} {t : Impl α β}

theorem minKey_modify [TransOrd α] (h : t.WF) {k f he} :
    (modify k f t).minKey he =
      if compare (t.minKey <| isEmpty_modify h ▸ he) k = .eq then
        k
      else
        (t.minKey <| Const.isEmpty_modify h ▸ he) := by
  simp_to_model [minKey, Const.modify] using List.Const.minKey_modifyKey

theorem minKey_modify_eq_minKey [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k f he} :
    (modify k f t).minKey he = t.minKey (isEmpty_modify h ▸ he) := by
  simp_to_model [minKey, Const.modify] using List.Const.minKey_modifyKey_eq_minKey

theorem compare_minKey_modify_eq [TransOrd α] (h : t.WF) {k f he} :
    compare (modify k f t |>.minKey he) (t.minKey <| isEmpty_modify h ▸ he) = .eq := by
  simp_to_model [minKey, Const.modify] using List.Const.minKey_modifyKey_beq

theorem minKey_alter_eq_self [TransOrd α] (h : t.WF) {k f he} :
    (alter k f t h.balanced).impl.minKey he = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simp_to_model [minKey, Const.alter, contains, Const.get?] using List.Const.minKey_alterKey_eq_self

end Const

theorem minKey_eq_minKey! [TransOrd α] [Inhabited α] (h : t.WF) {he} :
    t.minKey he = t.minKey! := by
  simp_to_model [minKey, minKey!] using List.minKey_eq_minKey!

theorem minKey?_eq_some_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → t.minKey? = some t.minKey! := by
  simp_to_model [minKey?, minKey!, isEmpty] using List.minKey?_eq_some_minKey!

theorem minKey!_eq_default [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty) → t.minKey! = default := by
  simp_to_model [minKey!, isEmpty] using List.minKey!_eq_default

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {km},
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (compare km k).isLE := by
  simp_to_model [minKey!, getKey?, contains, isEmpty] using
    List.minKey!_eq_iff_getKey?_eq_self_and_forall

theorem minKey!_eq_some_iff_mem_and_forall [TransOrd α]
    [LawfulEqOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {km},
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (compare km k).isLE := by
  simp_to_model [minKey!, contains, isEmpty] using List.minKey!_eq_some_iff_mem_and_forall

theorem minKey!_insert [TransOrd α] [Inhabited α] (h : t.WF) {k v} :
    (t.insert k v h.balanced |>.impl.minKey!) =
      (t.minKey?.elim k fun k' => if compare k k'|>.isLE then k else k') := by
  simp_to_model [minKey!, minKey?, insert] using List.minKey!_insertEntry

theorem minKey!_insert! [TransOrd α] [Inhabited α] (h : t.WF) {k v} :
    (t.insert! k v |>.minKey!) =
      (t.minKey?.elim k fun k' => if compare k k'|>.isLE then k else k') := by
  simpa [insert_eq_insert!] using minKey!_insert h

theorem minKey!_insert_le_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {k v},
    compare (t.insert k v h.balanced |>.impl.minKey!) t.minKey! |>.isLE := by
  simp_to_model [minKey!, isEmpty, insert] using List.minKey!_insertEntry_le_minKey!

theorem minKey!_insert!_le_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {k v},
    compare (t.insert! k v |>.minKey!) t.minKey! |>.isLE := by
  simpa only [insert_eq_insert!] using minKey!_insert_le_minKey! h

theorem minKey!_insert_le_self [TransOrd α] [Inhabited α] (h : t.WF) {k v} :
    compare (t.insert k v h.balanced |>.impl.minKey!) k |>.isLE := by
  simp_to_model [minKey!, insert] using List.minKey!_insertEntry_le_self

theorem minKey!_insert!_le_self [TransOrd α] [Inhabited α] (h : t.WF) {k v} :
    compare (t.insert! k v |>.minKey!) k |>.isLE := by
  simpa only [insert_eq_insert!] using minKey!_insert_le_self h

theorem contains_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → t.contains t.minKey! := by
  simp_to_model [minKey!, isEmpty, contains] using List.containsKey_minKey!

theorem minKey!_mem [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → t.minKey! ∈ t :=
  contains_minKey! h

theorem minKey!_le_of_contains [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k}, (hc : t.contains k) →
    compare t.minKey! k |>.isLE := by
  simp_to_model [minKey!, contains] using List.minKey!_le_of_containsKey

theorem minKey!_le_of_mem [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k}, (hc : k ∈ t) →
    compare t.minKey! k |>.isLE :=
  minKey!_le_of_contains h

theorem le_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {k},
    (compare k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (compare k k').isLE) := by
  simp_to_model [minKey!, contains, isEmpty] using List.le_minKey!

theorem getKey?_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) →
    t.getKey? t.minKey! = some t.minKey! := by
  simp_to_model [minKey!, getKey?, isEmpty] using List.getKey?_minKey!

theorem getKey_minKey! [TransOrd α] [Inhabited α] (h : t.WF) : ∀ {he},
    t.getKey t.minKey! he = t.minKey! := by
  simp_to_model [minKey!, contains, isEmpty, getKey] using List.getKey_minKey!

theorem getKey_minKey!_eq_minKey [TransOrd α] [Inhabited α] (h : t.WF) : ∀ {hc},
    t.getKey t.minKey! hc = t.minKey (isEmpty_eq_false_of_contains h hc) := by
  simp_to_model [minKey!, minKey, contains, isEmpty, getKey] using List.getKey_minKey!_eq_minKey

theorem getKey!_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → t.getKey! t.minKey! = t.minKey! := by
  simp_to_model [minKey!, isEmpty, getKey!] using List.getKey!_minKey!

theorem getKeyD_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {fallback},
    t.getKeyD t.minKey! fallback = t.minKey! := by
  simp_to_model [minKey!, getKeyD, isEmpty] using List.getKeyD_minKey!

theorem minKey!_erase_eq_iff_not_compare_minKey!_eq [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k}, (he : (t.erase k h.balanced).impl.isEmpty = false) →
    (t.erase k h.balanced |>.impl.minKey!) = t.minKey! ↔
      ¬ compare k t.minKey! = .eq := by
  simp_to_model [minKey!, isEmpty, erase] using List.minKey!_eraseKey_eq_iff_beq_minKey!_eq_false

theorem minKey!_erase!_eq_iff_not_compare_minKey!_eq [TransOrd α] [Inhabited α] (h : t.WF) {k} :
    (he : (t.erase! k).isEmpty = false) →
    (t.erase! k |>.minKey!) = t.minKey! ↔
      ¬ compare k t.minKey! = .eq := by
  simpa only [erase_eq_erase!] using minKey!_erase_eq_iff_not_compare_minKey!_eq h

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k}, (he : (t.erase k h.balanced).impl.isEmpty = false) → (heq : ¬ compare k t.minKey! = .eq) →
    (t.erase k h.balanced |>.impl.minKey!) = t.minKey! := by
  simp_to_model [minKey!, isEmpty, erase] using
    List.minKey!_eraseKey_eq_of_beq_minKey!_eq_false

theorem minKey!_erase!_eq_of_not_compare_minKey!_eq [TransOrd α] [Inhabited α] (h : t.WF) {k} :
    (he : (t.erase! k).isEmpty = false) → (heq : ¬ compare k t.minKey! = .eq) →
    (t.erase! k |>.minKey!) = t.minKey! := by
  simpa only [erase_eq_erase!] using minKey!_erase_eq_of_not_compare_minKey!_eq h

theorem minKey!_le_minKey!_erase [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k}, (he : (t.erase k h.balanced).impl.isEmpty = false) →
    compare t.minKey! (t.erase k h.balanced |>.impl.minKey!) |>.isLE := by
  simp_to_model [minKey!, isEmpty, erase] using List.minKey!_le_minKey!_erase

theorem minKey!_le_minKey!_erase! [TransOrd α] [Inhabited α] (h : t.WF) {k} :
    (he : (t.erase! k).isEmpty = false) →
    compare t.minKey! (t.erase! k |>.minKey!) |>.isLE := by
  simpa only [erase_eq_erase!] using minKey!_le_minKey!_erase h

theorem minKey!_insertIfNew [TransOrd α] [Inhabited α] (h : t.WF) : ∀ {k v},
    (t.insertIfNew k v h.balanced |>.impl.minKey!) =
      t.minKey?.elim k fun k' => if compare k k' = .lt then k else k' := by
  simp_to_model [minKey!, minKey?, insertIfNew] using List.minKey!_insertEntryIfNew

theorem minKey!_insertIfNew! [TransOrd α] [Inhabited α] (h : t.WF) {k v} :
    (t.insertIfNew! k v |>.minKey!) =
      t.minKey?.elim k fun k' => if compare k k' = .lt then k else k' := by
  simpa only [insertIfNew_eq_insertIfNew!] using minKey!_insertIfNew h

theorem minKey!_insertIfNew_le_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {k v},
    compare (t.insertIfNew k v h.balanced |>.impl.minKey!) t.minKey! |>.isLE := by
  simp_to_model [minKey!, isEmpty, insertIfNew] using List.minKey!_insertEntryIfNew_le_minKey!

theorem minKey!_insertIfNew!_le_minKey! [TransOrd α] [Inhabited α] (h : t.WF) :
    (he : t.isEmpty = false) → ∀ {k v},
    compare (t.insertIfNew! k v |>.minKey!) t.minKey! |>.isLE := by
  simpa only [insertIfNew_eq_insertIfNew!] using minKey!_insertIfNew_le_minKey! h

theorem minKey!_insertIfNew_le_self [TransOrd α] [Inhabited α] (h : t.WF) : ∀ {k v},
    compare (t.insertIfNew k v h.balanced |>.impl.minKey!) k |>.isLE := by
  simp_to_model [minKey!, insertIfNew] using List.minKey!_insertEntryIfNew_le_self

theorem minKey!_insertIfNew!_le_self [TransOrd α] [Inhabited α] (h : t.WF) {k v} :
    compare (t.insertIfNew! k v |>.minKey!) k |>.isLE := by
  simpa only [insertIfNew_eq_insertIfNew!] using minKey!_insertIfNew_le_self h

theorem minKey!_modify [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) : ∀ {k f},
    (t.modify k f |>.minKey!) = t.minKey! := by
  simp_to_model [minKey!, modify] using List.minKey!_modifyKey

theorem minKey!_alter_eq_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k f}, (he : (t.alter k f h.balanced).impl.isEmpty = false) →
    (t.alter k f h.balanced |>.impl.minKey!) = k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simp_to_model [minKey!, alter, isEmpty, contains, get?] using List.minKey!_alterKey_eq_self

theorem minKey!_alter!_eq_self [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) {k f} :
    (he : (t.alter! k f).isEmpty = false) →
    (t.alter! k f |>.minKey!) = k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simpa only [alter_eq_alter!] using minKey!_alter_eq_self h

namespace Const

variable {β : Type v} {t : Impl α β}

theorem minKey!_modify [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k f}, (he : (modify k f t).isEmpty = false) →
    (modify k f t |> minKey!) = if compare t.minKey! k = .eq then k else t.minKey! := by
  simp_to_model [minKey!, minKey, isEmpty, Const.modify] using List.Const.minKey!_modifyKey

theorem minKey!_modify_eq_minKey! [TransOrd α] [LawfulEqOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k f}, (modify k f t |> minKey!) = t.minKey! := by
  simp_to_model [minKey!, Const.modify] using List.Const.minKey!_modifyKey_eq_minKey!

theorem compare_minKey!_modify_eq [TransOrd α] [Inhabited α] (h : t.WF) : ∀ {k f},
    compare (Const.modify k f t |> minKey!) t.minKey! = .eq := by
  simp_to_model [minKey!, Const.modify] using List.Const.minKey!_modifyKey_beq

theorem minKey!_alter_eq_self [TransOrd α] [Inhabited α] (h : t.WF) :
    ∀ {k f}, (he : (alter k f t h.balanced).impl.isEmpty = false) →
    (alter k f t h.balanced |>.impl.minKey!) = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simp_to_model [minKey!, Const.alter, contains, isEmpty, Const.get?] using
    List.Const.minKey!_alterKey_eq_self

theorem minKey!_alter!_eq_self [TransOrd α] [Inhabited α] (h : t.WF) {k f} :
    (he : (alter! k f t).isEmpty = false) →
    (alter! k f t |>.minKey!) = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (compare k k').isLE := by
  simpa only [alter_eq_alter!] using minKey!_alter_eq_self h

end Const

end Min

end Std.DTreeMap.Internal.Impl
