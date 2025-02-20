/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeSet.Basic

/-!
# Tree set lemmas

This file contains lemmas about `Std.Data.TreeSet`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeSet

variable {α : Type u} {cmp : α → α → Ordering} {t : TreeSet α cmp}

private theorem ext {t t' : TreeSet α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : TreeSet α cmp).isEmpty :=
  TreeMap.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [TransCmp cmp] {k : α} :
    (t.insert k).isEmpty = false :=
  TreeMap.isEmpty_insertIfNew

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  TreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.mem_congr hab

@[simp]
theorem contains_emptyc {k : α} : (∅ : TreeSet α cmp).contains k = false :=
  TreeMap.contains_emptyc

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : TreeSet α cmp) :=
  TreeMap.not_mem_emptyc

theorem contains_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → t.contains a = false :=
  DTreeMap.contains_of_isEmpty

theorem not_mem_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → a ∉ t :=
  DTreeMap.not_mem_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  DTreeMap.isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  DTreeMap.isEmpty_eq_false_iff_exists_mem

theorem isEmpty_iff_forall_contains [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  DTreeMap.isEmpty_iff_forall_contains

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  DTreeMap.isEmpty_iff_forall_not_mem

@[simp]
theorem insert_eq_insert {p : α} : Insert.insert p t = t.insert p :=
  rfl

@[simp]
theorem singleton_eq_insert {p : α} :
    Singleton.singleton p = (∅ : TreeSet α cmp).insert p :=
  rfl

@[simp]
theorem contains_insert [h : TransCmp cmp] {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.contains_insertIfNew

@[simp]
theorem mem_insert [TransCmp cmp] {k a : α} :
    a ∈ t.insert k ↔ cmp k a = .eq ∨ a ∈ t :=
  TreeMap.mem_insertIfNew

theorem contains_insert_self [TransCmp cmp] {k : α} :
    (t.insert k).contains k :=
  TreeMap.contains_insertIfNew_self

theorem mem_insert_self [TransCmp cmp] {k : α} :
    k ∈ t.insert k :=
  TreeMap.mem_insertIfNew_self

theorem contains_of_contains_insert [TransCmp cmp] {k a : α} :
    (t.insert k).contains a → cmp k a ≠ .eq → t.contains a :=
  TreeMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insert [TransCmp cmp] {k a : α} :
    a ∈ t.insert k → cmp k a ≠ .eq → a ∈ t :=
  TreeMap.mem_of_mem_insertIfNew

@[simp]
theorem size_emptyc : (∅ : TreeSet α cmp).size = 0 :=
  TreeMap.size_emptyc

theorem isEmpty_eq_size_eq_zero :
    t.isEmpty = (t.size == 0) :=
  TreeMap.isEmpty_eq_size_eq_zero

theorem size_insert [TransCmp cmp] {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  TreeMap.size_insertIfNew

theorem size_le_size_insert [TransCmp cmp] {k : α} :
    t.size ≤ (t.insert k).size :=
  TreeMap.size_le_size_insertIfNew

theorem size_insert_le [TransCmp cmp] {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  TreeMap.size_insertIfNew_le

@[simp]
theorem erase_emptyc {k : α} :
    (empty : TreeSet α cmp).erase k = empty :=
  ext <| TreeMap.erase_emptyc

@[simp]
theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  TreeMap.isEmpty_erase

@[simp]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  TreeMap.contains_erase

@[simp]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  TreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.mem_of_mem_erase

theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  TreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  TreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  TreeMap.size_le_size_erase

end Std.TreeSet
