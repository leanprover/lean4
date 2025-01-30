/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.WF

/-!
# API lemmas for `DTreeMap.Impl`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.Internal.List
open Std.Internal

universe u v

namespace Std.DTreeMap.Internal.Impl

variable {α : Type u} {β : α → Type v} {_ : Ord α} {t : Impl α β}

/-- Internal implementation detail of the hash map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply WF.ordered | apply WF.balanced | apply WF.insert | apply WF.insertSlow
    | apply WF.erase | apply WF.eraseSlow
    | apply WF.containsThenInsert | apply WF.containsThenInsertSlow
    | apply WF.insertIfNew | apply WF.insertIfNewSlow
    | apply Ordered.distinctKeys
    | assumption
    ))

/-- Internal implementation detail of the hash map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``apply_isEmpty, ``apply_contains, ``apply_size]

private def modifyNames : Array Name :=
  #[``toListModel_insert, ``toListModel_insertSlow, ``toListModel_erase, ``toListModel_eraseSlow,
    ``toListModel_containsThenInsert, ``toListModel_containsThenInsertSlow,
    ``toListModel_insertIfNew, ``toListModel_insertIfNewSlow]

private def congrNames : MacroM (Array (TSyntax `term)) := do
  return #[← `(_root_.List.Perm.isEmpty_eq), ← `(containsKey_of_perm),
    ← `(_root_.List.Perm.length_eq), ← `(getValueCast?_of_perm _),
    ← `(getValue?_of_perm _), ← `(getValue_of_perm _), ← `(getValueCast_of_perm _),
    ← `(getValueCast!_of_perm _), ← `(getValueCastD_of_perm _), ← `(getValue!_of_perm _),
    ← `(getValueD_of_perm _), ← `(getKey?_of_perm _), ← `(getKey_of_perm _), ← `(getKeyD_of_perm _),
    ← `(getKey!_of_perm _)]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_model" ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[using $using?]?) => do
    let mut congrModify : Array (TSyntax `term) := #[]
    for congr in (← congrNames) do
      for modify in modifyNames do
        congrModify := congrModify.push (← `($congr:term ($(mkIdent modify) ..)))
    `(tactic|
      (simp (discharger := wf_trivial) only
        [$[$(Array.map Lean.mkIdent queryNames):term],*, $[$congrModify:term],*]
       $[apply $(using?.toArray):term];*)
      <;> wf_trivial)

attribute [local instance] beqOfOrd
attribute [local instance] equivBEq_of_transOrd

theorem isEmpty_empty : isEmpty (empty : Impl α β) := by
  simp [Impl.apply_isEmpty]

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Iff.rfl

theorem contains_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : k == k') :
    t.contains k = t.contains k' := by
  simp_to_model using List.containsKey_congr

theorem mem_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : k == k') : k ∈ t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_congr h hab]

theorem contains_empty {k : α} : (empty : Impl α β).contains k = false := by
  simp [contains, empty]

theorem mem_empty {k : α} : k ∉ (empty : Impl α β) := by
  simp [mem_iff_contains, contains_empty]

theorem isEmpty_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntry

theorem isEmpty_insertSlow [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertSlow k v).isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntry

theorem contains_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model using List.containsKey_insertEntry

theorem contains_insertSlow [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertSlow k v).contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model using List.containsKey_insertEntry

theorem size_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.size = if t.contains k then t.size else t.size + 1 := by
  simp_to_model using List.length_insertEntry

theorem size_insertSlow [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertSlow k v).size = if t.contains k then t.size else t.size + 1 := by
  simp_to_model using List.length_insertEntry

theorem size_le_size_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v h.balanced).impl.size := by
  simp_to_model using List.length_le_length_insertEntry

theorem size_le_size_insertSlow [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertSlow k v).size := by
  simp_to_model using List.length_le_length_insertEntry

theorem size_insert_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.size ≤ t.size + 1 := by
  simp_to_model using List.length_insertEntry_le

theorem size_insertSlow_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertSlow k v).size ≤ t.size + 1 := by
  simp_to_model using List.length_insertEntry_le

theorem isEmpty_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model using List.isEmpty_eraseKey

theorem isEmpty_eraseSlow [TransOrd α] (h : t.WF) {k : α} :
    (t.eraseSlow k).isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model using List.isEmpty_eraseKey

theorem contains_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.contains a = (!(k == a) && t.contains a) := by
  simp_to_model using List.containsKey_eraseKey

theorem contains_eraseSlow [TransOrd α] (h : t.WF) {k a : α} :
    (t.eraseSlow k).contains a = (!(k == a) && t.contains a) := by
  simp_to_model using List.containsKey_eraseKey

theorem contains_of_contains_erase [TransOrd α] (h : t.WF) {k a : α} :
    (t.erase k h.balanced).impl.contains a → t.contains a := by
  simp_to_model using List.containsKey_of_containsKey_eraseKey

theorem contains_of_contains_eraseSlow [TransOrd α] (h : t.WF) {k a : α} :
    (t.eraseSlow k).contains a → t.contains a := by
  simp_to_model using List.containsKey_of_containsKey_eraseKey

theorem size_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.size = if t.contains k then t.size - 1 else t.size := by
  simp_to_model using List.length_eraseKey

theorem sizeSlow_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.eraseSlow k).size = if t.contains k then t.size - 1 else t.size := by
  simp_to_model using List.length_eraseKey

theorem size_erase_le [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.size ≤ t.size := by
  simp_to_model using List.length_eraseKey_le

theorem sizeSlow_erase_le [TransOrd α] (h : t.WF) {k : α} :
    (t.eraseSlow k).size ≤ t.size := by
  simp_to_model using List.length_eraseKey_le

theorem size_le_size_erase [TransOrd α] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k h.balanced).impl.size + 1 := by
  simp_to_model using List.length_le_length_eraseKey

theorem sizeSlow_le_size_erase [TransOrd α] (h : t.WF) {k : α} :
    t.size ≤ (t.eraseSlow k).size + 1 := by
  simp_to_model using List.length_le_length_eraseKey

theorem containsThenInsert_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v h.balanced).1 = t.contains k := by
  rw [containsThenInsert_eq_containsₘ, contains_eq_containsₘ]
  exact h.ordered

theorem containsThenInsertSlow_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertSlow k v).1 = t.contains k := by
  rw [fst_containsThenInsertSlow_eq_containsThenInsert, containsThenInsert_fst h]

theorem containsThenInsert_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v h.balanced).2 = t.insert k v h.balanced := by
  rfl

theorem containsThenInsertSlow_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertSlow k v).2 = t.insertSlow k v := by
  rw [snd_containsThenInsertSlow_eq_containsThenInsert _ h.balanced, containsThenInsert_snd h,
    insert_eq_insertSlow]

theorem containsThenInsertIfNew_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v h.balanced).1 = t.contains k := by
  rw [fst_containsThenInsertIfNew_eq_containsₘ, contains_eq_containsₘ]

theorem containsThenInsertIfNewSlow_fst [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNewSlow k v).1 = t.contains k := by
  rw [fst_containsThenInsertIfNewSlow_eq_containsₘ, contains_eq_containsₘ]

theorem containsThenInsertIfNew_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v h.balanced).2 = t.insertIfNew k v h.balanced := by
  rw [snd_containsThenInsertIfNew_eq_insertIfNew]

theorem containsThenInsertIfNewSlow_snd [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNewSlow k v).2 = t.insertIfNewSlow k v := by
  rw [snd_containsThenInsertIfNewSlow_eq_insertIfNewSlow]

@[simp]
theorem isEmpty_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntryIfNew

@[simp]
theorem isEmpty_insertIfNewSlow [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNewSlow k v).isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntryIfNew

@[simp]
theorem contains_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a = (k == a || t.contains a) := by
  simp_to_model using List.containsKey_insertEntryIfNew

@[simp]
theorem contains_insertIfNewSlow [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNewSlow k v).contains a = (k == a || t.contains a) := by
  simp_to_model using List.containsKey_insertEntryIfNew

@[simp]
theorem mem_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl ↔ k == a ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insertIfNew, h]

@[simp]
theorem mem_insertIfNewSlow [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNewSlow k v ↔ k == a ∨ a ∈ t := by
  simp [mem_iff_contains, contains_insertIfNew, h]

theorem contains_insertIfNew_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains k := by
  simp [contains_insertIfNew, h]

theorem contains_insertIfNewSlow_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNewSlow k v).contains k := by
  simp [contains_insertIfNewSlow, h]

theorem mem_insertIfNew_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ (t.insertIfNew k v h.balanced).impl := by
  simp [contains_insertIfNew, h]

theorem mem_insertIfNewSlow_self [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNewSlow k v := by
  simp [contains_insertIfNewSlow, h]

theorem contains_of_contains_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a → (k == a) = false → t.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew

theorem contains_of_contains_insertIfNewSlow [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNewSlow k v).contains a → (k == a) = false → t.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew

theorem mem_of_mem_insertIfNew [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl → (k == a) = false → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew h

theorem mem_of_mem_insertIfNewSlow [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNewSlow k v → (k == a) = false → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNewSlow h

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.contains a → ¬((k == a) ∧ t.contains k = false) → t.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew'

/-- This is a restatement of `contains_of_contains_insertIfNewSlow` that is written to exactly match the proof
obligation in the statement of `get_insertIfNewSlow`. -/
theorem contains_of_contains_insertIfNewSlow' [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNewSlow k v).contains a → ¬((k == a) ∧ t.contains k = false) → t.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v h.balanced).impl → ¬((k == a) ∧ ¬k ∈ t) → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew' h

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNewSlow' [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNewSlow k v → ¬((k == a) ∧ ¬k ∈ t) → a ∈ t := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNewSlow' h

theorem size_insertIfNew [TransOrd α] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v h.balanced).impl.size = if k ∈ t then t.size else t.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_model using List.length_insertEntryIfNew

theorem size_insertIfNewSlow [TransOrd α] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNewSlow k v).size = if k ∈ t then t.size else t.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_model using List.length_insertEntryIfNew

theorem size_le_size_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v h.balanced).impl.size := by
  simp_to_model using List.length_le_length_insertEntryIfNew

theorem size_le_size_insertIfNewSlow [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNewSlow k v).size := by
  simp_to_model using List.length_le_length_insertEntryIfNew

theorem size_insertIfNew_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.size ≤ t.size + 1 := by
  simp_to_model using List.length_insertEntryIfNew_le

theorem size_insertIfNewSlow_le [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNewSlow k v).size ≤ t.size + 1 := by
  simp_to_model using List.length_insertEntryIfNew_le

end Std.DTreeMap.Internal.Impl

/-- Used as instance by the dependents of this file -/
theorem TransOrd.ofTransCmp {α : Type u} {cmp : α → α → Ordering} [TransCmp cmp] :
    letI _ : Ord α := ⟨cmp⟩; TransOrd α :=
  let _ : Ord α := ⟨cmp⟩
  have _ : OrientedOrd α := ⟨⟩
  ⟨TransCmp.le_trans⟩
