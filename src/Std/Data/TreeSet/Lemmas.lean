/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeSet.Basic

/-!
# API lemmas for `TreeMap`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.TreeSet

variable {α : Type u} {cmp : α → α → Ordering} {t : TreeSet α cmp}

private theorem ext {t t' : TreeSet α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

theorem isEmpty_empty : (empty : TreeSet α cmp).isEmpty :=
  TreeMap.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  TreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.mem_congr hab

theorem contains_empty {k : α} : (empty : TreeSet α cmp).contains k = false :=
  TreeMap.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : TreeSet α cmp) :=
  TreeMap.mem_empty

theorem isEmpty_insert [TransCmp cmp] {k : α} :
    (t.insert k).isEmpty = false :=
  TreeMap.isEmpty_insert

theorem contains_insert [h : TransCmp cmp] (t : TreeSet α cmp) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.contains_insert

theorem size_insert [TransCmp cmp] {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  TreeMap.size_insert

theorem size_le_size_insert [TransCmp cmp] {k : α} :
    t.size ≤ (t.insert k).size :=
  TreeMap.size_le_size_insert

theorem size_insert_le [TransCmp cmp] {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  TreeMap.size_insert_le

theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  TreeMap.isEmpty_erase

theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  DTreeMap.contains_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  DTreeMap.contains_of_contains_erase

theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  DTreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  DTreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  DTreeMap.size_le_size_erase

theorem containsThenInsert_fst [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  TreeMap.containsThenInsert_fst

theorem containsThenInsert_snd [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| TreeMap.containsThenInsert_snd

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} :
    (t.insertIfNew k).isEmpty = false :=
  DTreeMap.isEmpty_insertIfNew

@[simp]
theorem contains_insertIfNew [TransCmp cmp] {k a : α} :
    (t.insertIfNew k).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.contains_insertIfNew

@[simp]
theorem mem_insertIfNew [TransCmp cmp] {k a : α} :
    a ∈ t.insertIfNew k ↔ cmp k a == .eq ∨ a ∈ t :=
  DTreeMap.mem_insertIfNew

theorem contains_insertIfNew_self [TransCmp cmp] {k : α} :
    (t.insertIfNew k).contains k :=
  DTreeMap.contains_insertIfNew_self

theorem mem_insertIfNew_self [TransCmp cmp] {k : α} :
    k ∈ t.insertIfNew k :=
  DTreeMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [TransCmp cmp] {k a : α} :
    (t.insertIfNew k).contains a → (cmp k a == .eq) = false → t.contains a :=
  DTreeMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [TransCmp cmp] {k a : α} :
    a ∈ t.insertIfNew k → (cmp k a == .eq) = false → a ∈ t :=
  DTreeMap.contains_of_contains_insertIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [TransCmp cmp] {k a : α} :
    (t.insertIfNew k).contains a → ¬((cmp k a == .eq) ∧ t.contains k = false) → t.contains a :=
  DTreeMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] {k a : α} :
    a ∈ t.insertIfNew k → ¬((cmp k a == .eq) ∧ ¬k ∈ t) → a ∈ t :=
  DTreeMap.mem_of_mem_insertIfNew'

theorem size_insertIfNew [TransCmp cmp] {k : α} :
    (t.insertIfNew k).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.size_insertIfNew

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} :
    t.size ≤ (t.insertIfNew k).size :=
  DTreeMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [TransCmp cmp] {k : α} :
    (t.insertIfNew k).size ≤ t.size + 1 :=
  DTreeMap.size_insertIfNew_le

end Std.TreeSet
