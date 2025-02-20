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

/-- Internal implementation detail of the tree map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply WF.ordered | apply WF.balanced | apply WF.insert | apply WF.insert!
    | apply WF.insertIfNew | apply WF.insertIfNew!
    | apply WF.erase | apply WF.erase!
    | apply Ordered.distinctKeys
    | assumption
    ))

/-- Internal implementation detail of the tree map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``isEmpty_eq_isEmpty, ``contains_eq_containsKey, ``size_eq_length]

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
      [$[$(Array.map Lean.mkIdent queryNames):term],*, $[$congrModify:term],*]
     $[apply $(using?.toArray):term];*)
    <;> wf_trivial)

attribute [local instance] beqOfOrd
attribute [local instance] equivBEq_of_transOrd

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
  rw [← beq_iff_eq (b := Ordering.eq), ← beq_eq] at hab
  simp_to_model using List.containsKey_congr

theorem mem_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : compare k k' = .eq) :
    k ∈ t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_congr h hab]

theorem isEmpty_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.isEmpty = false := by
  simp_to_model [insertIfNew] using List.isEmpty_insertEntryIfNew

theorem isEmpty_insertIfNew! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).isEmpty = false := by
  simp_to_model [insertIfNew!] using List.isEmpty_insertEntryIfNew

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

end Std.DTreeMap.Internal.Impl
