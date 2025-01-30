/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.TreeMap.RawLemmas
import Std.Data.TreeSet.Raw

/-!
# API lemmas for `TreeMap.Raw`
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeSet.Raw

attribute [local instance] TransOrd.ofTransCmp

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeSet.Raw α cmp}

private theorem ext {t t' : Raw α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

theorem isEmpty_empty : (empty : TreeSet.Raw α cmp).isEmpty :=
  TreeMap.Raw.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  TreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.Raw.mem_congr h hab

theorem contains_empty {k : α} : (empty : TreeSet.Raw α cmp).contains k = false :=
  TreeMap.Raw.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : TreeSet.Raw α cmp) :=
  TreeMap.Raw.mem_empty

theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).isEmpty = false :=
  TreeMap.Raw.isEmpty_insert h

theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.Raw.contains_insert h

theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  TreeMap.Raw.size_insert h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.insert k).size :=
  DTreeMap.Raw.size_le_size_insert h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  DTreeMap.Raw.size_insert_le h

theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  TreeMap.Raw.isEmpty_erase h

theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  TreeMap.Raw.contains_erase h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.Raw.contains_of_contains_erase h

theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  TreeMap.Raw.size_erase h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  TreeMap.Raw.size_erase_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  TreeMap.Raw.size_le_size_erase h

theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  TreeMap.Raw.containsThenInsert_fst h

theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| TreeMap.Raw.containsThenInsert_snd h

end Std.TreeSet.Raw
