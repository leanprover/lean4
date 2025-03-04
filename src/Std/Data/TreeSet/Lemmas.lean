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

/-- This is a restatement of `mem_of_mem_insert` that is written to exactly match the
proof obligation in the statement of `get_insert`. -/
theorem mem_of_mem_insert' [TransCmp cmp] {k a : α} :
    a ∈ t.insert k → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  TreeMap.mem_of_mem_insertIfNew'

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
    (∅ : TreeSet α cmp).erase k = ∅ :=
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

@[simp]
theorem get?_emptyc {a : α} : (∅ : TreeSet α cmp).get? a = none :=
  TreeMap.getKey?_emptyc

theorem get?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t.get? a = none :=
  TreeMap.getKey?_of_isEmpty

theorem get?_insert [TransCmp cmp] {k a : α} :
    (t.insert k).get? a = if cmp k a = .eq ∧ ¬k ∈ t then some k else t.get? a :=
  TreeMap.getKey?_insertIfNew

theorem contains_eq_isSome_get? [TransCmp cmp] {a : α} :
    t.contains a = (t.get? a).isSome :=
  TreeMap.contains_eq_isSome_getKey?

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.get? a = none :=
  TreeMap.getKey?_eq_none_of_contains_eq_false

theorem get?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  TreeMap.getKey?_eq_none

theorem get?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  TreeMap.getKey?_erase

@[simp]
theorem get?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).get? k = none :=
  TreeMap.getKey?_erase_self

theorem get_insert [TransCmp cmp] {k a : α} {h₁} :
    (t.insert k).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.get a (mem_of_mem_insert' h₁ h₂) :=
  TreeMap.getKey_insertIfNew

@[simp]
theorem get_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h') :=
  TreeMap.getKey_erase

theorem get?_eq_some_get [TransCmp cmp] {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  TreeMap.getKey?_eq_some_getKey

@[simp]
theorem get!_emptyc {a : α} [Inhabited α] :
    (∅ : TreeSet α cmp).get! a = default :=
  TreeMap.getKey!_emptyc

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited α] {a : α} :
    t.isEmpty = true → t.get! a = default :=
  TreeMap.getKey!_of_isEmpty

theorem get!_insert [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.insert k).get! a = if cmp k a = .eq ∧ ¬ k ∈ t then k else t.get! a :=
  TreeMap.getKey!_insertIfNew

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.get! a = default :=
  TreeMap.getKey!_eq_default_of_contains_eq_false

theorem get!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.get! a = default :=
  TreeMap.getKey!_eq_default

theorem get!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  TreeMap.getKey!_erase

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited α] {k : α} :
    (t.erase k).get! k = default :=
  TreeMap.getKey!_erase_self

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = true → t.get? a = some (t.get! a) :=
  TreeMap.getKey?_eq_some_getKey!_of_contains

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited α] {a : α} :
    a ∈ t → t.get? a = some (t.get! a) :=
  TreeMap.getKey?_eq_some_getKey!

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited α] {a : α} :
    t.get! a = (t.get? a).get! :=
  TreeMap.getKey!_eq_get!_getKey?

theorem get_eq_get! [TransCmp cmp] [Inhabited α] {a : α} {h} :
    t.get a h = t.get! a :=
  TreeMap.getKey_eq_getKey!

@[simp]
theorem getD_emptyc {a : α} {fallback : α} :
    (∅ : TreeSet α cmp).getD a fallback = fallback :=
  TreeMap.getKeyD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] {a fallback : α} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  TreeMap.getKeyD_of_isEmpty

theorem getD_insert [TransCmp cmp] {k a fallback : α} :
    (t.insert k).getD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getD a fallback :=
  TreeMap.getKeyD_insertIfNew

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getD a fallback = fallback :=
  TreeMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  TreeMap.getKeyD_eq_fallback

theorem getD_erase [TransCmp cmp] {k a fallback : α} :
    (t.erase k).getD a fallback =
      if cmp k a = .eq then fallback else t.getD a fallback :=
  TreeMap.getKeyD_erase

@[simp]
theorem getD_erase_self [TransCmp cmp] {k fallback : α} :
    (t.erase k).getD k fallback = fallback :=
  TreeMap.getKeyD_erase_self

theorem get?_eq_some_getD_of_contains [TransCmp cmp] {a fallback : α} :
    t.contains a = true → t.get? a = some (t.getD a fallback) :=
  TreeMap.getKey?_eq_some_getKeyD_of_contains

theorem get?_eq_some_getD [TransCmp cmp] {a fallback : α} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  TreeMap.getKey?_eq_some_getKeyD

theorem getD_eq_getD_get? [TransCmp cmp] {a fallback : α} :
    t.getD a fallback = (t.get? a).getD fallback :=
  TreeMap.getKeyD_eq_getD_getKey?

theorem get_eq_getD [TransCmp cmp] {a fallback : α} {h} :
    t.get a h = t.getD a fallback :=
  TreeMap.getKey_eq_getKeyD

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited α] {a : α} :
    t.get! a = t.getD a default :=
  TreeMap.getKey!_eq_getKeyD_default

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  TreeMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| TreeMap.containsThenInsertIfNew_snd

@[simp]
theorem length_toList [TransCmp cmp] :
    t.toList.length = t.size :=
  DTreeMap.length_keys

@[simp]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  DTreeMap.isEmpty_keys

@[simp]
theorem contains_toList [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.toList.contains k = t.contains k :=
  DTreeMap.contains_keys

@[simp]
theorem mem_toList [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.toList ↔ k ∈ t :=
  DTreeMap.mem_keys

theorem distinct_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.distinct_keys

end Std.TreeSet
