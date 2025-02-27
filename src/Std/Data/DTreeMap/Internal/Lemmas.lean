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

universe u v

namespace Std.DTreeMap.Internal.Impl

variable {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Impl α β}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

attribute [local instance] beqOfOrd
attribute [local instance] equivBEq_of_transOrd
attribute [local instance] lawfulBEq_of_lawfulEqOrd

/-- Internal implementation detail of the tree map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply WF.ordered | apply WF.balanced | apply WF.empty
    | apply WF.insert | apply WF.insert!
    | apply WF.insertIfNew | apply WF.insertIfNew!
    | apply WF.erase | apply WF.erase!
    | apply Ordered.distinctKeys
    | assumption
    ))

/-- Internal implementation detail of the tree map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

theorem compare_eq_eq_iff_beq {k a : α} : compare k a = .eq ↔ k == a := beq_iff_eq.symm

private def helperLemmaNames : Array Name :=
  #[``compare_eq_eq_iff_beq]

private def queryNames : Array Name :=
  #[``isEmpty_eq_isEmpty, ``contains_eq_containsKey, ``size_eq_length,
    ``get?_eq_getValueCast?, ``Const.get?_eq_getValue?,
    ``get_eq_getValueCast, ``Const.get_eq_getValue,
    ``get!_eq_getValueCast!, ``Const.get!_eq_getValue!,
    ``getD_eq_getValueCastD, ``Const.getD_eq_getValueD,
    ``getKey?_eq_getKey?, ``getKey_eq_getKey,
    ``getKey!_eq_getKey!, ``getKeyD_eq_getKeyD,
    ``keys_eq_keys, ``toList_eq_toListModel, ``Const.toList_eq_toListModel_map]

private def modifyMap : Std.HashMap Name Name :=
  .ofList
    [⟨`insert, ``toListModel_insert⟩,
     ⟨`insert!, ``toListModel_insert!⟩,
     ⟨`insertIfNew, ``toListModel_insertIfNew⟩,
     ⟨`insertIfNew!, ``toListModel_insertIfNew!⟩,
     ⟨`erase, ``toListModel_erase⟩,
     ⟨`erase!, ``toListModel_erase!⟩]

private def congrNames : MacroM (Array (TSyntax `term)) := do
  return #[← `(_root_.List.Perm.isEmpty_eq), ← `(containsKey_of_perm),
    ← `(_root_.List.Perm.length_eq), ← `(getValueCast?_of_perm _),
    ← `(getValue?_of_perm _), ← `(getValue_of_perm _), ← `(getValueCast_of_perm _),
    ← `(getValueCast!_of_perm _), ← `(getValueCastD_of_perm _), ← `(getValue!_of_perm _),
    ← `(getValueD_of_perm _), ← `(getKey?_of_perm _), ← `(getKey_of_perm _), ← `(getKeyD_of_perm _),
    ← `(getKey!_of_perm _)]

/-- Internal implementation detail of the tree map -/
scoped syntax "simp_to_model" (" [" (ident,*) "]")? ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[[$modifyNames,*]]? $[using $using?]?) => do
  let mut congrModify : Array (TSyntax `term) := #[]
  if let some modifyNames := modifyNames then
    for modify in modifyNames.getElems.flatMap
        (fun n => modifyMap.get? (Lean.Syntax.getId n) |>.toArray) do
      for congr in (← congrNames) do
        congrModify := congrModify.push (← `($congr:term ($(mkIdent modify) ..)))
  `(tactic|
    (simp (discharger := wf_trivial) only
      [$[$(Array.map Lean.mkIdent helperLemmaNames):term],*,
       $[$(Array.map Lean.mkIdent queryNames):term],*, $[$congrModify:term],*]
     $[apply $(using?.toArray):term];*)
    <;> wf_trivial)

theorem isEmpty_empty : isEmpty (empty : Impl α β) := by
  simp [Impl.isEmpty_eq_isEmpty]

theorem isEmpty_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.isEmpty = false := by
  simp_to_model [insert] using List.isEmpty_insertEntry

theorem isEmpty_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).isEmpty = false := by
  simp_to_model [insert!] using List.isEmpty_insertEntry

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Iff.rfl

theorem contains_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : compare k k' = .eq) :
    t.contains k = t.contains k' := by
  revert hab
  simp_to_model using List.containsKey_congr

theorem mem_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : compare k k' = .eq) :
    k ∈ t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_congr h hab]

theorem contains_empty {a : α} : (empty : Impl α β).contains a = false := by
  simp [contains, empty]

theorem not_mem_empty {a : α} : a ∉ (empty : Impl α β) := by
  simp [mem_iff_contains, contains_empty]

theorem contains_of_isEmpty [TransOrd α] (h : t.WF) {a : α} :
    t.isEmpty → t.contains a = false := by
  simp_to_model; empty

theorem not_mem_of_isEmpty [TransOrd α] (h : t.WF) {a : α} :
    t.isEmpty → a ∉ t := by
  simpa [mem_iff_contains] using contains_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransOrd α] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true := by
  simp_to_model using List.isEmpty_eq_false_iff_exists_containsKey

theorem isEmpty_eq_false_iff_exists_mem [TransOrd α] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t := by
  simpa [mem_iff_contains] using isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_iff_forall_contains [TransOrd α] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false := by
  simp_to_model using List.isEmpty_iff_forall_containsKey

theorem isEmpty_iff_forall_not_mem [TransOrd α] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t := by
  simpa [mem_iff_contains] using isEmpty_iff_forall_contains h

theorem contains_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model [insert] using List.containsKey_insertEntry

theorem contains_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert! k v).contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model [insert!] using List.containsKey_insertEntry

theorem mem_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insert k v h.balanced).impl ↔ compare k a = .eq ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insert h]

theorem mem_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert! k v ↔ compare k a = .eq ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insert! h]

theorem contains_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains k := by
  simp_to_model [insert] using List.containsKey_insertEntry_self

theorem contains_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).contains k := by
  simp_to_model [insert!] using List.containsKey_insertEntry_self

theorem mem_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ (t.insert k v h.balanced).impl := by
  simpa [mem_iff_contains] using contains_insert_self h

theorem mem_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insert! k v := by
  simpa [mem_iff_contains] using contains_insert!_self h

theorem contains_of_contains_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains a → compare k a ≠ .eq → t.contains a := by
  rw [← beq_eq_false_iff_ne]
  simp_to_model [insert] using List.containsKey_of_containsKey_insertEntry

theorem contains_of_contains_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert! k v).contains a → compare k a ≠ .eq → t.contains a := by
  rw [← beq_eq_false_iff_ne]
  simp_to_model [insert!] using List.containsKey_of_containsKey_insertEntry

theorem mem_of_mem_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insert k v h.balanced).impl → compare k a ≠ .eq → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insert h

theorem mem_of_mem_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert! k v → compare k a ≠ .eq → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insert! h

theorem size_empty : (empty : Impl α β).size = 0 :=
  rfl

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    letI : BEq Nat := instBEqOfDecidableEq
    t.isEmpty = (t.size == 0) := by
  simp_to_model
  rw [Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, Nat.beq_eq_true_eq]

theorem size_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.size = if t.contains k then t.size else t.size + 1 := by
  simp_to_model [insert] using List.length_insertEntry

theorem size_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).size = if t.contains k then t.size else t.size + 1 := by
  simp_to_model [insert!] using List.length_insertEntry

theorem size_le_size_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v h.balanced).impl.size := by
  simp_to_model [insert] using List.length_le_length_insertEntry

theorem size_le_size_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert! k v).size := by
  simp_to_model [insert!] using List.length_le_length_insertEntry

theorem size_insert_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.size ≤ t.size + 1 := by
  simp_to_model [insert] using List.length_insertEntry_le

theorem size_insert!_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).size ≤ t.size + 1 := by
  simp_to_model [insert!] using List.length_insertEntry_le

theorem erase_empty {k : α} :
    ((empty : Impl α β).erase k balanced_empty).impl = empty :=
  rfl

theorem erase!_empty {k : α} :
    (empty : Impl α β).erase! k = empty :=
  rfl

theorem isEmpty_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model [erase] using List.isEmpty_eraseKey

theorem isEmpty_erase! [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model [erase!] using List.isEmpty_eraseKey

theorem contains_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.contains a = (!(compare k a == .eq) && t.contains a) := by
  simp_to_model [erase] using List.containsKey_eraseKey

theorem contains_erase! [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).contains a = (!(compare k a == .eq) && t.contains a) := by
  simp_to_model [erase!] using List.containsKey_eraseKey

theorem mem_erase [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ (t.erase k h.balanced).impl ↔ compare k a ≠ .eq ∧ a ∈ t := by
  simpa only [mem_iff_contains, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    using Bool.eq_iff_iff.mp <| contains_erase h

theorem mem_erase! [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ t.erase! k ↔  compare k a ≠ .eq ∧ a ∈ t := by
  simp [mem_iff_contains, contains_erase! h]

theorem contains_of_contains_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.contains a → t.contains a := by
  simp_to_model [erase] using List.containsKey_of_containsKey_eraseKey

theorem contains_of_contains_erase! [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).contains a → t.contains a := by
  simp_to_model [erase!] using List.containsKey_of_containsKey_eraseKey

theorem mem_of_mem_erase [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ (t.erase k h.balanced).impl → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_erase h

theorem mem_of_mem_erase! [TransOrd α] (h : t.WF) {k a : α} :
    a ∈ t.erase! k → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_erase! h

theorem size_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.size = if t.contains k then t.size - 1 else t.size := by
  simp_to_model [erase] using List.length_eraseKey

theorem size_erase! [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).size = if t.contains k then t.size - 1 else t.size := by
  simp_to_model [erase!] using List.length_eraseKey

theorem size_erase_le [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.size ≤ t.size := by
  simp_to_model [erase] using List.length_eraseKey_le

theorem size_erase!_le [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).size ≤ t.size := by
  simp_to_model [erase!] using List.length_eraseKey_le

theorem size_le_size_erase [TransOrd α] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k h.balanced).impl.size + 1 := by
  simp_to_model [erase] using List.length_le_length_eraseKey

theorem size_le_size_erase! [TransOrd α] (h : t.WF) {k : α} :
    t.size ≤ (t.erase! k).size + 1 := by
  simp_to_model [erase!] using List.length_le_length_eraseKey

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
  simp_to_model [insertIfNew] using List.isEmpty_insertEntryIfNew

theorem isEmpty_insertIfNew! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).isEmpty = false := by
  simp_to_model [insertIfNew!] using List.isEmpty_insertEntryIfNew

theorem contains_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a = (k == a || t.contains a) := by
  simp_to_model [insertIfNew] using List.containsKey_insertEntryIfNew

theorem contains_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).contains a = (k == a || t.contains a) := by
  simp_to_model [insertIfNew!] using List.containsKey_insertEntryIfNew

theorem mem_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl ↔ compare k a = .eq ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insertIfNew, h, beq_eq]

theorem mem_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew! k v ↔ compare k a = .eq ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insertIfNew!, h, beq_eq]

theorem contains_insertIfNew_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains k := by
  simp [contains_insertIfNew, h]

theorem contains_insertIfNew!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).contains k := by
  simp [contains_insertIfNew!, h]

theorem mem_insertIfNew_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ (t.insertIfNew k v h.balanced).impl := by
  simp [mem_insertIfNew, h]

theorem mem_insertIfNew!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNew! k v := by
  simp [mem_insertIfNew!, h]

theorem contains_of_contains_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a → compare k a ≠ .eq → t.contains a := by
  rw [← beq_eq_false_iff_ne]
  simp_to_model [insertIfNew] using List.containsKey_of_containsKey_insertEntryIfNew

theorem contains_of_contains_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).contains a → compare k a ≠ .eq → t.contains a := by
  rw [← beq_eq_false_iff_ne]
  simp_to_model [insertIfNew!] using List.containsKey_of_containsKey_insertEntryIfNew

theorem mem_of_mem_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl → compare k a ≠ .eq → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew h

theorem mem_of_mem_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew! k v → compare k a ≠ .eq → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew! h

theorem size_insertIfNew [TransOrd α] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v h.balanced).impl.size = if k ∈ t then t.size else t.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_model [insertIfNew] using List.length_insertEntryIfNew

theorem size_insertIfNew! [TransOrd α] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew! k v).size = if k ∈ t then t.size else t.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_model [insertIfNew!] using List.length_insertEntryIfNew

theorem size_le_size_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v h.balanced).impl.size := by
  simp_to_model [insertIfNew] using List.length_le_length_insertEntryIfNew

theorem size_le_size_insertIfNew! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew! k v).size := by
  simp_to_model [insertIfNew!] using List.length_le_length_insertEntryIfNew

theorem size_insertIfNew_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.size ≤ t.size + 1 := by
  simp_to_model [insertIfNew] using List.length_insertEntryIfNew_le

theorem size_insertIfNew!_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).size ≤ t.size + 1 := by
  simp_to_model [insertIfNew!] using List.length_insertEntryIfNew_le

theorem get?_empty [TransOrd α] [LawfulEqOrd α] {a : α} : (empty : Impl α β).get? a = none := by
  simp_to_model using List.getValueCast?_nil

theorem get?_of_isEmpty [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none := by
  simp_to_model; empty

theorem get?_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v h.balanced).impl.get? a =
      if h : compare k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a := by
  simp_to_model [insert] using List.getValueCast?_insertEntry

theorem get?_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert! k v).get? a =
      if h : compare k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a := by
  simp_to_model [insert!] using List.getValueCast?_insertEntry

theorem get?_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.get? k = some v := by
  simp_to_model [insert] using List.getValueCast?_insertEntry_self

theorem get?_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).get? k = some v := by
  simp_to_model [insert!] using List.getValueCast?_insertEntry_self

theorem contains_eq_isSome_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValueCast?

theorem mem_iff_isSome_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.get? a).isSome := by
  simpa [mem_iff_contains] using contains_eq_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none := by
  simp_to_model using List.getValueCast?_eq_none

theorem get?_eq_none [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.get? a = if compare k a = .eq then none else t.get? a := by
  simp_to_model [erase] using List.getValueCast?_eraseKey

theorem get?_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).get? a = if compare k a = .eq then none else t.get? a := by
  simp_to_model [erase!] using List.getValueCast?_eraseKey

theorem get?_erase_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.get? k = none := by
  simp_to_model [erase] using List.getValueCast?_eraseKey_self

theorem get?_erase!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} :
    (t.erase! k).get? k = none := by
  simp_to_model [erase!] using List.getValueCast?_eraseKey_self

namespace Const

variable {β : Type v} {t : Impl α β}

theorem get?_empty [TransOrd α] {a : α} : get? (empty : Impl α β) a = none := by
  simp_to_model using List.getValue?_nil

theorem get?_of_isEmpty [TransOrd α] (h : t.WF) {a : α} :
    t.isEmpty = true → get? t a = none := by
  simp_to_model; empty

theorem get?_insert [TransOrd α] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert k v h.balanced).impl a =
      if compare k a = .eq then some v else get? t a := by
  simp_to_model [insert] using List.getValue?_insertEntry

theorem get?_insert! [TransOrd α] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert! k v) a =
      if compare k a = .eq then some v else get? t a := by
  simp_to_model [insert!] using List.getValue?_insertEntry

theorem get?_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get? (t.insert k v h.balanced).impl k = some v := by
  simp_to_model [insert] using List.getValue?_insertEntry_self

theorem get?_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get? (t.insert! k v) k = some v := by
  simp_to_model [insert!] using List.getValue?_insertEntry_self

theorem contains_eq_isSome_get? [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = (get? t a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValue?

theorem mem_iff_isSome_get? [TransOrd α] (h : t.WF) {a : α} :
    a ∈ t ↔ (get? t a).isSome := by
  simpa [mem_iff_contains] using contains_eq_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = false → get? t a = none := by
  simp_to_model using List.getValue?_eq_none.mpr

theorem get?_eq_none [TransOrd α] (h : t.WF) {a : α} :
    ¬ a ∈ t → get? t a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [TransOrd α] (h : t.WF) {k a : α} :
    get? (t.erase k h.balanced).impl a = if compare k a = .eq then none else get? t a := by
  simp_to_model [erase] using List.getValue?_eraseKey

theorem get?_erase! [TransOrd α] (h : t.WF) {k a : α} :
    get? (t.erase! k) a = if compare k a = .eq then none else get? t a := by
  simp_to_model [erase!] using List.getValue?_eraseKey

theorem get?_erase_self [TransOrd α] (h : t.WF) {k : α} :
    get? (t.erase k h.balanced).impl k = none := by
  simp_to_model [erase] using List.getValue?_eraseKey_self

theorem get?_erase!_self [TransOrd α] (h : t.WF) {k : α} :
    get? (t.erase! k) k = none := by
  simp_to_model [erase!] using List.getValue?_eraseKey_self

theorem get?_eq_get? [LawfulEqOrd α] [TransOrd α] (h : t.WF) {a : α} : get? t a = t.get? a := by
  simp_to_model using List.getValue?_eq_getValueCast?

theorem get?_congr [TransOrd α] (h : t.WF) {a b : α} (hab : compare a b = .eq) :
    get? t a = get? t b := by
  revert hab
  simp_to_model using List.getValue?_congr

end Const

theorem get_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v h.balanced).impl.get a h₁ =
      if h₂ : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (contains_of_contains_insert h h₁ h₂) := by
  simp_to_model [insert] using List.getValueCast_insertEntry

theorem get_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert! k v).get a h₁ =
      if h₂ : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (contains_of_contains_insert! h h₁ h₂) := by
  simp_to_model [insert!] using List.getValueCast_insertEntry

theorem get_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.get k (contains_insert_self h) = v := by
  simp_to_model [insert] using List.getValueCast_insertEntry_self

theorem get_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).get k (contains_insert!_self h) = v := by
  simp_to_model [insert!] using List.getValueCast_insertEntry_self

@[simp]
theorem get_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase k h.balanced).impl.get a h' = t.get a (contains_of_contains_erase h h') := by
  simp_to_model [erase] using List.getValueCast_eraseKey

theorem get_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase! k).get a h' = t.get a (contains_of_contains_erase! h h') := by
  simp_to_model [erase!] using List.getValueCast_eraseKey

theorem get?_eq_some_get [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {h'} : t.get? a = some (t.get a h') := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast

namespace Const

variable {β : Type v} {t : Impl α β} (h : t.WF)

theorem get_insert [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert k v h.balanced).impl a h₁ =
      if h₂ : compare k a = .eq then v
      else get t a (contains_of_contains_insert h h₁ h₂) := by
  simp_to_model [insert] using List.getValue_insertEntry

theorem get_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert! k v) a h₁ =
      if h₂ : compare k a = .eq then v
      else get t a (contains_of_contains_insert! h h₁ h₂) := by
  simp_to_model [insert!] using List.getValue_insertEntry

theorem get_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v h.balanced).impl k (contains_insert_self h) = v := by
  simp_to_model [insert] using List.getValue_insertEntry_self

theorem get_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β} :
    get (t.insert! k v) k (contains_insert!_self h) = v := by
  simp_to_model [insert!] using List.getValue_insertEntry_self

@[simp]
theorem get_erase [TransOrd α] (h : t.WF) {k a : α} {h'} :
    get (t.erase k h.balanced).impl a h' = get t a (contains_of_contains_erase h h') := by
  simp_to_model [erase] using List.getValue_eraseKey

theorem get_erase! [TransOrd α] (h : t.WF) {k a : α} {h'} :
    get (t.erase! k) a h' = get t a (contains_of_contains_erase! h h') := by
  simp_to_model [erase!] using List.getValue_eraseKey

theorem get?_eq_some_get [TransOrd α] (h : t.WF) {a : α} {h} :
    get? t a = some (get t a h) := by
  simp_to_model using List.getValue?_eq_some_getValue

theorem get_eq_get [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {h} : get t a h = t.get a h := by
  simp_to_model using List.getValue_eq_getValueCast

theorem get_congr [TransOrd α] (h : t.WF) {a b : α} (hab : compare a b = .eq) {h'} :
    get t a h' = get t b ((contains_congr h hab).symm.trans h') := by
  revert hab h'
  simp_to_model using List.getValue_congr

end Const

theorem get!_empty [TransOrd α] [LawfulEqOrd α] {a : α} [Inhabited (β a)] :
    get! (empty : Impl α β) a = default := by
  simp_to_model using List.getValueCast!_nil

theorem get!_of_isEmpty [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default := by
  simp_to_model; empty

theorem get!_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insert k v h.balanced).impl.get! a =
      if h : compare k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a := by
  simp_to_model [insert] using List.getValueCast!_insertEntry

theorem get!_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insert! k v).get! a =
      if h : compare k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a := by
  simp_to_model [insert!] using List.getValueCast!_insertEntry

theorem get!_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (t.insert a b h.balanced).impl.get! a = b := by
  simp_to_model [insert] using List.getValueCast!_insertEntry_self

theorem get!_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (t.insert! a b).get! a = b := by
  simp_to_model [insert!] using List.getValueCast!_insertEntry_self

theorem get!_eq_default_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default := by
  simp_to_model using List.getValueCast!_eq_default

theorem get!_eq_default [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase k h.balanced).impl.get! a = if compare k a = .eq then default else t.get! a := by
  simp_to_model [erase] using List.getValueCast!_eraseKey

theorem get!_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase! k).get! a = if compare k a = .eq then default else t.get! a := by
  simp_to_model [erase!] using List.getValueCast!_eraseKey

theorem get!_erase_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase k h.balanced).impl.get! k = default := by
  simp_to_model [erase] using List.getValueCast!_eraseKey_self

theorem get!_erase!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase! k).get! k = default := by
  simp_to_model [erase!] using List.getValueCast!_eraseKey_self

theorem get?_eq_some_get!_of_contains [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.contains a = true → t.get? a = some (t.get! a) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast!

theorem get?_eq_some_get! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! := by
  simp_to_model using List.getValueCast!_eq_getValueCast?

theorem get_eq_get! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] {h} :
    t.get a h = t.get! a := by
  simp_to_model using List.getValueCast_eq_getValueCast!

namespace Const

variable {β : Type v} {t : Impl α β} (h : t.WF)

theorem get!_empty [TransOrd α] [Inhabited β] {a : α} :
    get! (empty : Impl α β) a = default := by
  simp_to_model using List.getValue!_nil

theorem get!_of_isEmpty [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → get! t a = default := by
  simp_to_model; empty

theorem get!_insert [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v h.balanced).impl a = if compare k a = .eq then v else get! t a := by
  simp_to_model [insert] using List.getValue!_insertEntry

theorem get!_insert! [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert! k v) a = if compare k a = .eq then v else get! t a := by
  simp_to_model [insert!] using List.getValue!_insertEntry

theorem get!_insert_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α}
    {v : β} : get! (t.insert k v h.balanced).impl k = v := by
  simp_to_model [insert] using List.getValue!_insertEntry_self

theorem get!_insert!_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α}
    {v : β} : get! (t.insert! k v) k = v := by
  simp_to_model [insert!] using List.getValue!_insertEntry_self

theorem get!_eq_default_of_contains_eq_false [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → get! t a = default := by
  simp_to_model using List.getValue!_eq_default

theorem get!_eq_default [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → get! t a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k h.balanced).impl a = if compare k a = .eq then default else get! t a := by
  simp_to_model [erase] using List.getValue!_eraseKey

theorem get!_erase! [TransOrd α] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase! k) a = if compare k a = .eq then default else get! t a := by
  simp_to_model [erase!] using List.getValue!_eraseKey

theorem get!_erase_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k h.balanced).impl k = default := by
  simp_to_model [erase] using List.getValue!_eraseKey_self

theorem get!_erase!_self [TransOrd α] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase! k) k = default := by
  simp_to_model [erase!] using List.getValue!_eraseKey_self

theorem get?_eq_some_get!_of_contains [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → get? t a = some (get! t a) := by
  simp_to_model using List.getValue?_eq_some_getValue!

theorem get?_eq_some_get! [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → get? t a = some (get! t a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = (get? t a).get! := by
  simp_to_model using List.getValue!_eq_getValue?

theorem get_eq_get! [TransOrd α] [Inhabited β] (h : t.WF) {a : α} {h} :
    get t a h = get! t a := by
  simp_to_model using List.getValue_eq_getValue!

theorem get!_eq_get! [TransOrd α] [LawfulEqOrd α] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = t.get! a := by
  simp_to_model using List.getValue!_eq_getValueCast!

theorem get!_congr [TransOrd α] [Inhabited β] (h : t.WF) {a b : α}
    (hab : compare a b = .eq) : get! t a = get! t b := by
  revert hab
  simp_to_model using List.getValue!_congr

end Const

theorem getD_empty [TransOrd α] [LawfulEqOrd α] {a : α} {fallback : β a} :
    (empty : Impl α β).getD a fallback = fallback := by
  simp [getD, empty]

theorem getD_of_isEmpty [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} : t.isEmpty = true → t.getD a fallback = fallback := by
  simp_to_model; empty

theorem getD_insert [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v h.balanced).impl.getD a fallback =
      if h : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback := by
  simp_to_model [insert] using List.getValueCastD_insertEntry

theorem getD_insert! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert! k v).getD a fallback =
      if h : compare k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback := by
  simp_to_model [insert!] using List.getValueCastD_insertEntry

theorem getD_insert_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert a b h.balanced).impl.getD a fallback = b := by
  simp_to_model [insert] using List.getValueCastD_insertEntry_self

theorem getD_insert!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert! a b).getD a fallback = b := by
  simp_to_model [insert!] using List.getValueCastD_insertEntry_self

theorem getD_eq_fallback_of_contains_eq_false [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = false → t.getD a fallback = fallback := by
  simp_to_model using List.getValueCastD_eq_fallback

theorem getD_eq_fallback [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase k h.balanced).impl.getD a fallback = if compare k a = .eq then fallback else t.getD a fallback := by
  simp_to_model [erase] using List.getValueCastD_eraseKey

theorem getD_erase! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase! k).getD a fallback = if compare k a = .eq then fallback else t.getD a fallback := by
  simp_to_model [erase!] using List.getValueCastD_eraseKey

theorem getD_erase_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase k h.balanced).impl.getD k fallback = fallback := by
  simp_to_model [erase] using List.getValueCastD_eraseKey_self

theorem getD_erase!_self [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase! k).getD k fallback = fallback := by
  simp_to_model [erase!] using List.getValueCastD_eraseKey_self

theorem get?_eq_some_getD_of_contains [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = true → t.get? a = some (t.getD a fallback) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCastD

theorem get?_eq_some_getD [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback := by
  simp_to_model using List.getValueCastD_eq_getValueCast?

theorem get_eq_getD [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β a} {h} :
    t.get a h = t.getD a fallback := by
  simp_to_model using List.getValueCast_eq_getValueCastD

theorem get!_eq_getD_default [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default := by
  simp_to_model using List.getValueCast!_eq_getValueCastD_default

namespace Const

variable {β : Type v} {t : Impl α β} (h : t.WF)

theorem getD_empty [TransOrd α] {a : α} {fallback : β} :
    getD (empty : Impl α β) a fallback = fallback := by
  simp_to_model using List.getValueD_nil

theorem getD_of_isEmpty [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback := by
  simp_to_model; empty

theorem getD_insert [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v h.balanced).impl a fallback = if compare k a = .eq then v else getD t a fallback := by
  simp_to_model [insert] using List.getValueD_insertEntry

theorem getD_insert! [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert! k v) a fallback = if compare k a = .eq then v else getD t a fallback := by
  simp_to_model [insert!] using List.getValueD_insertEntry

theorem getD_insert_self [TransOrd α] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v h.balanced).impl k fallback = v := by
  simp_to_model [insert] using List.getValueD_insertEntry_self

theorem getD_insert!_self [TransOrd α] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert! k v) k fallback = v := by
  simp_to_model [insert!] using List.getValueD_insertEntry_self

theorem getD_eq_fallback_of_contains_eq_false [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback := by
  simp_to_model using List.getValueD_eq_fallback

theorem getD_eq_fallback [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [TransOrd α] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k h.balanced).impl a fallback = if compare k a = .eq then
      fallback
    else
      getD t a fallback := by
  simp_to_model [erase] using List.getValueD_eraseKey

theorem getD_erase! [TransOrd α] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase! k) a fallback = if compare k a = .eq then
      fallback
    else
      getD t a fallback := by
  simp_to_model [erase!] using List.getValueD_eraseKey

theorem getD_erase_self [TransOrd α] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k h.balanced).impl k fallback = fallback := by
  simp_to_model [erase] using List.getValueD_eraseKey_self

theorem getD_erase!_self [TransOrd α] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase! k) k fallback = fallback := by
  simp_to_model [erase!] using List.getValueD_eraseKey_self

theorem get?_eq_some_getD_of_contains [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) := by
  simp_to_model using List.getValue?_eq_some_getValueD

theorem get?_eq_some_getD [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [TransOrd α] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback := by
  simp_to_model using List.getValueD_eq_getValue?

theorem get_eq_getD [TransOrd α] (h : t.WF) {a : α} {fallback : β} {h} :
    get t a h = getD t a fallback := by
  simp_to_model using List.getValue_eq_getValueD

theorem get!_eq_getD_default [TransOrd α] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = getD t a default := by
  simp_to_model using List.getValue!_eq_getValueD_default

theorem getD_eq_getD [TransOrd α] [LawfulEqOrd α] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback := by
  simp_to_model using List.getValueD_eq_getValueCastD

theorem getD_congr [TransOrd α] (h : t.WF) {a b : α} {fallback : β}
    (hab : compare a b = .eq) : getD t a fallback = getD t b fallback := by
  revert hab
  simp_to_model using List.getValueD_congr

end Const

theorem getKey?_empty {a : α} : (empty : Impl α β).getKey? a = none := by
  simp [empty, getKey?]

theorem getKey?_of_isEmpty [TransOrd α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none := by
  simp_to_model; empty

theorem getKey?_insert [TransOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKey? a = if compare k a = .eq then some k else t.getKey? a := by
  simp_to_model [insert] using List.getKey?_insertEntry

theorem getKey?_insert! [TransOrd α] (h : t.WF) {a k : α} {v : β k} :
    (t.insert! k v).getKey? a = if compare k a = .eq then some k else t.getKey? a := by
  simp_to_model [insert!] using List.getKey?_insertEntry

theorem getKey?_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKey? k = some k := by
  simp_to_model [insert] using List.getKey?_insertEntry_self

theorem getKey?_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).getKey? k = some k := by
  simp_to_model [insert!] using List.getKey?_insertEntry_self

theorem contains_eq_isSome_getKey? [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getKey?

theorem mem_iff_isSome_getKey? [TransOrd α] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome := by
  simpa [mem_iff_contains] using contains_eq_isSome_getKey? h

theorem getKey?_eq_none_of_contains_eq_false [TransOrd α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none := by
  simp_to_model using List.getKey?_eq_none

theorem getKey?_eq_none [TransOrd α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none := by
  simpa [mem_iff_contains] using getKey?_eq_none_of_contains_eq_false h

theorem getKey?_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.getKey? a = if compare k a = .eq then none else t.getKey? a := by
  simp_to_model [erase] using List.getKey?_eraseKey

theorem getKey?_erase! [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase! k).getKey? a = if compare k a = .eq then none else t.getKey? a := by
  simp_to_model [erase!] using List.getKey?_eraseKey

theorem getKey?_erase_self [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.getKey? k = none := by
  simp_to_model [erase] using List.getKey?_eraseKey_self

theorem getKey?_erase!_self [TransOrd α] (h : t.WF) {k : α} :
    (t.erase! k).getKey? k = none := by
  simp_to_model [erase!] using List.getKey?_eraseKey_self

theorem getKey_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v h.balanced).impl.getKey a h₁ =
      if h₂ : compare k a = .eq then
        k
      else
        t.getKey a (contains_of_contains_insert h h₁ h₂) := by
  simp_to_model [insert] using List.getKey_insertEntry

theorem getKey_insert! [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert! k v).getKey a h₁ =
      if h₂ : compare k a = .eq then
        k
      else
        t.getKey a (contains_of_contains_insert! h h₁ h₂) := by
  simp_to_model [insert!] using List.getKey_insertEntry

theorem getKey_insert_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKey k (contains_insert_self h) = k := by
  simp_to_model [insert] using List.getKey_insertEntry_self

theorem getKey_insert!_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).getKey k (contains_insert!_self h) = k := by
  simp_to_model [insert!] using List.getKey_insertEntry_self

@[simp]
theorem getKey_erase [TransOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase k h.balanced).impl.getKey a h' = t.getKey a (contains_of_contains_erase h h') := by
  simp_to_model [erase] using List.getKey_eraseKey

@[simp]
theorem getKey_erase! [TransOrd α] (h : t.WF) {k a : α} {h'} :
    (t.erase! k).getKey a h' = t.getKey a (contains_of_contains_erase! h h') := by
  simp_to_model [erase!] using List.getKey_eraseKey

theorem getKey?_eq_some_getKey [TransOrd α] (h : t.WF) {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') := by
  simp_to_model using List.getKey?_eq_some_getKey

theorem getKey!_empty {a : α} [Inhabited α] :
    (empty : Impl α β).getKey! a = default := by
  simp only [empty, getKey!]; rfl

theorem getKey!_of_isEmpty [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default := by
  simp_to_model; empty;

theorem getKey!_insert [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insert k v h.balanced).impl.getKey! a = if compare k a = .eq then k else t.getKey! a := by
  simp_to_model [insert] using List.getKey!_insertEntry

theorem getKey!_insert! [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insert! k v).getKey! a = if compare k a = .eq then k else t.getKey! a := by
  simp_to_model [insert!] using List.getKey!_insertEntry

theorem getKey!_insert_self [TransOrd α] [Inhabited α] (h : t.WF) {a : α}
    {b : β a} : (t.insert a b h.balanced).impl.getKey! a = a := by
  simp_to_model [insert] using List.getKey!_insertEntry_self

theorem getKey!_insert!_self [TransOrd α] [Inhabited α] (h : t.WF) {a : α}
    {b : β a} : (t.insert! a b).getKey! a = a := by
  simp_to_model [insert!] using List.getKey!_insertEntry_self

theorem getKey!_eq_default_of_contains_eq_false [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey! a = default := by
  simp_to_model using List.getKey!_eq_default

theorem getKey!_eq_default [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey! a = default := by
  simpa [mem_iff_contains] using getKey!_eq_default_of_contains_eq_false h

theorem getKey!_erase [TransOrd α] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.getKey! a = if compare k a = .eq then default else t.getKey! a := by
  simp_to_model [erase] using List.getKey!_eraseKey

theorem getKey!_erase! [TransOrd α] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase! k).getKey! a = if compare k a = .eq then default else t.getKey! a := by
  simp_to_model [erase!] using List.getKey!_eraseKey

theorem getKey!_erase_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.getKey! k = default := by
  simp_to_model [erase] using List.getKey!_eraseKey_self

theorem getKey!_erase!_self [TransOrd α] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase! k).getKey! k = default := by
  simp_to_model [erase!] using List.getKey!_eraseKey_self

theorem getKey?_eq_some_getKey!_of_contains [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) := by
  simp_to_model using List.getKey?_eq_some_getKey!

theorem getKey?_eq_some_getKey! [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKey!_of_contains h

theorem getKey!_eq_get!_getKey? [TransOrd α] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = (t.getKey? a).get! := by
  simp_to_model using List.getKey!_eq_getKey?

theorem getKey_eq_getKey! [TransOrd α] [Inhabited α] (h : t.WF) {a : α} {h} :
    t.getKey a h = t.getKey! a := by
  simp_to_model using List.getKey_eq_getKey!

theorem getKeyD_empty {a : α} {fallback : α} :
    (empty : Impl α β).getKeyD a fallback = fallback := by
  simp [getKeyD, empty]

theorem getKeyD_of_isEmpty [TransOrd α] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback := by
  simp_to_model; empty

theorem getKeyD_insert [TransOrd α] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert k v h.balanced).impl.getKeyD a fallback =
      if compare k a = .eq then k else t.getKeyD a fallback := by
  simp_to_model [insert] using List.getKeyD_insertEntry

theorem getKeyD_insert! [TransOrd α] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert! k v).getKeyD a fallback =
      if compare k a = .eq then k else t.getKeyD a fallback := by
  simp_to_model [insert!] using List.getKeyD_insertEntry

theorem getKeyD_insert_self [TransOrd α] (h : t.WF) {a fallback : α}
    {b : β a} :
    (t.insert a b h.balanced).impl.getKeyD a fallback = a := by
  simp_to_model [insert] using List.getKeyD_insertEntry_self

theorem getKeyD_insert!_self [TransOrd α] (h : t.WF) {a fallback : α}
    {b : β a} :
    (t.insert! a b).getKeyD a fallback = a := by
  simp_to_model [insert!] using List.getKeyD_insertEntry_self

theorem getKeyD_eq_fallback_of_contains_eq_false [TransOrd α] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback := by
  simp_to_model using List.getKeyD_eq_fallback

theorem getKeyD_eq_fallback [TransOrd α] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback := by
  simpa [mem_iff_contains] using getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_erase [TransOrd α] (h : t.WF) {k a fallback : α} :
    (t.erase k h.balanced).impl.getKeyD a fallback =
      if compare k a = .eq then fallback else t.getKeyD a fallback := by
  simp_to_model [erase] using List.getKeyD_eraseKey

theorem getKeyD_erase! [TransOrd α] (h : t.WF) {k a fallback : α} :
    (t.erase! k).getKeyD a fallback =
      if compare k a = .eq then fallback else t.getKeyD a fallback := by
  simp_to_model [erase!] using List.getKeyD_eraseKey

theorem getKeyD_erase_self [TransOrd α] (h : t.WF) {k fallback : α} :
    (t.erase k h.balanced).impl.getKeyD k fallback = fallback := by
  simp_to_model [erase] using List.getKeyD_eraseKey_self

theorem getKeyD_erase!_self [TransOrd α] (h : t.WF) {k fallback : α} :
    (t.erase! k).getKeyD k fallback = fallback := by
  simp_to_model [erase!] using List.getKeyD_eraseKey_self

theorem getKey?_eq_some_getKeyD_of_contains [TransOrd α] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) := by
  simp_to_model using List.getKey?_eq_some_getKeyD

theorem getKey?_eq_some_getKeyD [TransOrd α] (h : t.WF) {a fallback : α} :
    a ∈ t → t.getKey? a = some (t.getKeyD a fallback) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKeyD_of_contains h

theorem getKeyD_eq_getD_getKey? [TransOrd α] (h : t.WF) {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback := by
  simp_to_model using List.getKeyD_eq_getKey?

theorem getKey_eq_getKeyD [TransOrd α] (h : t.WF) {a fallback : α} {h} :
    t.getKey a h = t.getKeyD a fallback := by
  simp_to_model using List.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [TransOrd α] [Inhabited α] (h : t.WF)
    {a : α} :
    t.getKey! a = t.getKeyD a default := by
  simp_to_model using List.getKey!_eq_getKeyD_default

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransOrd α] (h : t.WF) {k a : α}
    {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl →
      ¬ (compare k a = .eq ∧ ¬ k ∈ t) → a ∈ t := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.containsKey_of_containsKey_insertEntryIfNew'

/-- This is a restatement of `contains_of_contains_insertIfNew!` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew!`. -/
theorem mem_of_mem_insertIfNew!' [TransOrd α] (h : t.WF) {k a : α}
    {v : β k} :
    a ∈ (t.insertIfNew! k v) → ¬ (compare k a = .eq ∧ ¬ k ∈ t) → a ∈ t := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.containsKey_of_containsKey_insertEntryIfNew'

theorem get?_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.get? a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValueCast?_insertEntryIfNew

theorem get?_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).get? a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValueCast?_insertEntryIfNew

theorem get_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v h.balanced).impl.get a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValueCast_insertEntryIfNew

theorem get_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew! k v).get a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew!' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValueCast_insertEntryIfNew

theorem get!_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v h.balanced).impl.get! a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValueCast!_insertEntryIfNew

theorem get!_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew! k v).get! a =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValueCast!_insertEntryIfNew

theorem getD_insertIfNew [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getD a fallback =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValueCastD_insertEntryIfNew

theorem getD_insertIfNew! [TransOrd α] [LawfulEqOrd α] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew! k v).getD a fallback =
      if h : compare k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValueCastD_insertEntryIfNew

namespace Const

variable {β : Type v} {t : Impl α β}

theorem get?_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew k v h.balanced).impl a =
      if compare k a = .eq ∧ ¬ k ∈ t then
        some v
      else
        get? t a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValue?_insertEntryIfNew

theorem get?_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew! k v) a =
      if compare k a = .eq ∧ ¬ k ∈ t then
        some v
      else
        get? t a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValue?_insertEntryIfNew

theorem get_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v h.balanced).impl a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValue_insertEntryIfNew

theorem get_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew! k v) a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew!' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValue_insertEntryIfNew

theorem get!_insertIfNew [TransOrd α] [Inhabited β] (h : t.WF) {k a : α}
    {v : β} :
    get! (t.insertIfNew k v h.balanced).impl a =
      if compare k a = .eq ∧ ¬ k ∈ t then v else get! t a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValue!_insertEntryIfNew

theorem get!_insertIfNew! [TransOrd α] [Inhabited β] (h : t.WF) {k a : α}
    {v : β} :
    get! (t.insertIfNew! k v) a =
      if compare k a = .eq ∧ ¬ k ∈ t then v else get! t a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValue!_insertEntryIfNew

theorem getD_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v h.balanced).impl a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getValueD_insertEntryIfNew

theorem getD_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew! k v) a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getValueD_insertEntryIfNew

end Const

theorem getKey?_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getKey? a =
      if compare k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getKey?_insertEntryIfNew

theorem getKey?_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew! k v).getKey? a =
      if compare k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getKey?_insertEntryIfNew

theorem getKey_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v h.balanced).impl.getKey a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getKey_insertEntryIfNew

theorem getKey_insertIfNew! [TransOrd α] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew! k v).getKey a h₁ =
      if h₂ : compare k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew!' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getKey_insertEntryIfNew

theorem getKey!_insertIfNew [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getKey! a =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getKey!_insertEntryIfNew

theorem getKey!_insertIfNew! [TransOrd α] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew! k v).getKey! a =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getKey!_insertEntryIfNew

theorem getKeyD_insertIfNew [TransOrd α] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew k v h.balanced).impl.getKeyD a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew] using List.getKeyD_insertEntryIfNew

theorem getKeyD_insertIfNew! [TransOrd α] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew! k v).getKeyD a fallback =
      if compare k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_model [insertIfNew!] using List.getKeyD_insertEntryIfNew

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

@[simp]
theorem length_keys [TransOrd α] (h : t.WF) :
    t.keys.length = t.size := by
  simp_to_model using List.length_keys_eq_length

@[simp]
theorem isEmpty_keys [TransOrd α] :
    t.keys.isEmpty = t.isEmpty  := by
  simp_to_model using List.isEmpty_keys_eq_isEmpty

@[simp]
theorem contains_keys [TransOrd α] {k : α} (h : t.WF) :
    t.keys.contains k = t.contains k := by
  simp_to_model using List.containsKey_eq_keys_contains.symm

@[simp]
theorem mem_keys [LawfulBEq α] [TransOrd α] {k : α} (h : t.WF) :
    k ∈ t.keys ↔ k ∈ t := by
  simpa only [mem_iff_contains, ← List.contains_iff, ← Bool.eq_iff_iff] using contains_keys h

theorem distinct_keys [TransOrd α] (h : t.WF) :
    t.keys.Pairwise (fun a b => (a == b) = false) := by
  simp_to_model using h.ordered.distinctKeys.distinct

@[simp]
theorem map_sigma_fst_toList_eq_keys [TransOrd α] :
    t.toList.map Sigma.fst = t.keys := by
  simp_to_model using (List.keys_eq_map ..).symm

@[simp]
theorem length_toList [TransOrd α] (h : t.WF) :
    t.toList.length = t.size := by
  simp_to_model

@[simp]
theorem isEmpty_toList [TransOrd α] :
    t.toList.isEmpty = t.isEmpty := by
  simp_to_model

@[simp]
theorem mem_toList_iff_get?_eq_some [TransOrd α] [LawfulEqOrd α] {k : α} {v : β k} (h : t.WF) :
    ⟨k, v⟩ ∈ t.toList ↔ t.get? k = some v := by
  simp_to_model using List.mem_iff_getValueCast?_eq_some

theorem find?_toList_eq_some_iff_get?_eq_some [TransOrd α] [LawfulEqOrd α] {k : α} {v : β k}
    (h : t.WF) :
    t.toList.find? (·.1 == k) = some ⟨k, v⟩ ↔ t.get? k = some v := by
  simp_to_model using List.find?_eq_some_iff_getValueCast?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransOrd α] {k : α} (h : t.WF) :
    t.toList.find? (·.1 == k) = none ↔ t.contains k = false := by
  simp_to_model using List.find?_eq_none_iff_containsKey_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransOrd α] {k : α} (h : t.WF) :
    t.toList.find? (·.1 == k) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false h

theorem distinct_keys_toList [TransOrd α] (h : t.WF) :
    t.toList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  simp_to_model using List.pairwise_fst_eq_false

namespace Const

variable {β : Type v} {t : Impl α β}

@[simp]
theorem map_prod_fst_toList_eq_keys [TransOrd α] :
    (toList t).map Prod.fst = t.keys := by
  simp_to_model using List.map_prod_fst_map_toProd_eq_keys

@[simp]
theorem length_toList [TransOrd α] (h : t.WF) :
    (toList t).length = t.size := by
  simp_to_model using List.length_map

@[simp]
theorem isEmpty_toList [TransOrd α] :
    (toList t).isEmpty = t.isEmpty := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff, isEmpty_eq_isEmpty, List.isEmpty_iff]
  simp_to_model using List.map_eq_nil_iff

@[simp]
theorem mem_toList_iff_get?_eq_some [TransOrd α] [LawfulBEq α] {k : α} {v : β} (h : t.WF) :
    (k, v) ∈ toList t ↔ get? t k = some v := by
  simp_to_model using List.mem_map_toProd_iff_getValue?_eq_some

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [TransOrd α] {k : α} {v : β} (h : t.WF) :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ get? t k = some v := by
  simp_to_model using List.mem_map_toProd_iff_getKey?_eq_some_and_getValue?_eq_some

theorem get?_eq_some_iff_exists_beq_and_mem_toList [TransOrd α] {k : α} {v : β} (h : t.WF) :
    get? t k = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ toList t := by
  simp_to_model using List.getValue?_eq_some_iff_exists_beq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransOrd α] {k k' : α} {v : β}
    (h : t.WF) : (toList t).find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ get? t k = some v := by
  simp_to_model using List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransOrd α] {k : α} (h : t.WF) :
    (toList t).find? (·.1 == k) = none ↔ t.contains k = false := by
  simp_to_model using List.find?_map_eq_none_iff_containsKey_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransOrd α] {k : α} (h : t.WF) :
    (toList t).find? (·.1 == k) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false h

theorem distinct_keys_toList [TransOrd α] (h : t.WF) :
    (toList t).Pairwise (fun a b => (a.1 == b.1) = false) := by
  simp_to_model using List.pairwise_fst_eq_false_map_toProd

end Const

end Std.DTreeMap.Internal.Impl
