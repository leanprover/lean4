/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Markus Himmel, Paul Reichert
-/
module

prelude
public import Std.Data.ExtTreeMap.Lemmas
public import Std.Data.ExtTreeSet.Basic

@[expose] public section

/-!
# Tree set lemmas

This file contains lemmas about `Std.ExtTreeSet`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.ExtTreeSet

variable {α : Type u} {cmp : α → α → Ordering} {t : ExtTreeSet α cmp}

private theorem ext {t t' : ExtTreeSet α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

private theorem ext_iff {t t' : ExtTreeSet α cmp} : t = t' ↔ t.inner = t'.inner :=
  ⟨fun h => h ▸ rfl, ext⟩

@[simp]
theorem isEmpty_iff {t : ExtTreeSet α cmp} [TransCmp cmp] : t.isEmpty ↔ t = ∅ :=
  ExtTreeMap.isEmpty_iff.trans ext_iff.symm

@[simp]
theorem isEmpty_eq_false_iff {t : ExtTreeSet α cmp} [TransCmp cmp] : t.isEmpty = false ↔ ¬t = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[simp, grind =]
theorem isEmpty_empty : (∅ : ExtTreeSet α cmp).isEmpty :=
  ExtTreeMap.isEmpty_empty

@[simp]
theorem empty_eq : ∅ = t ↔ t = ∅ := eq_comm

@[simp]
theorem insert_ne_empty [TransCmp cmp] {k : α} :
    t.insert k ≠ ∅ :=
  mt ext_iff.mp ExtTreeMap.insertIfNew_ne_empty

@[grind =]
theorem mem_iff_contains [TransCmp cmp] {k : α} : k ∈ t ↔ t.contains k :=
  ExtTreeMap.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem [TransCmp cmp] {k : α} : t.contains k ↔ k ∈ t :=
  ExtTreeMap.contains_iff_mem

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  ExtTreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  ExtTreeMap.mem_congr hab

@[simp, grind =]
theorem contains_empty [TransCmp cmp] {k : α} : (∅ : ExtTreeSet α cmp).contains k = false :=
  rfl

@[simp]
theorem not_mem_empty [TransCmp cmp] {k : α} : k ∉ (∅ : ExtTreeSet α cmp) :=
  Bool.false_ne_true

theorem eq_empty_iff_forall_contains [TransCmp cmp] : t = ∅ ↔ ∀ a, t.contains a = false :=
  ext_iff.trans ExtTreeMap.eq_empty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem [TransCmp cmp] : t = ∅ ↔ ∀ a, ¬a ∈ t :=
  ext_iff.trans ExtTreeMap.eq_empty_iff_forall_not_mem

theorem ne_empty_of_mem [TransCmp cmp] {a : α} (h : a ∈ t) : t ≠ ∅ :=
  (not_congr eq_empty_iff_forall_not_mem).mpr fun h' => h' a h

@[simp]
theorem insert_eq_insert [TransCmp cmp] {p : α} : Insert.insert p t = t.insert p :=
  rfl

@[simp]
theorem singleton_eq_insert [TransCmp cmp] {p : α} :
    Singleton.singleton p = (∅ : ExtTreeSet α cmp).insert p :=
  rfl

@[simp, grind =]
theorem contains_insert [TransCmp cmp] {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  ExtTreeMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insert [TransCmp cmp] {k a : α} :
    a ∈ t.insert k ↔ cmp k a = .eq ∨ a ∈ t :=
  ExtTreeMap.mem_insertIfNew

theorem contains_insert_self [TransCmp cmp] {k : α} :
    (t.insert k).contains k :=
  ExtTreeMap.contains_insertIfNew_self

theorem mem_of_get_eq [TransCmp cmp] {k v : α} {w} (_ : t.get k w = v) : k ∈ t := w

theorem mem_insert_self [TransCmp cmp] {k : α} :
    k ∈ t.insert k :=
  ExtTreeMap.mem_insertIfNew_self

theorem contains_of_contains_insert [TransCmp cmp] {k a : α} :
    (t.insert k).contains a → cmp k a ≠ .eq → t.contains a :=
  ExtTreeMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insert [TransCmp cmp] {k a : α} :
    a ∈ t.insert k → cmp k a ≠ .eq → a ∈ t :=
  ExtTreeMap.mem_of_mem_insertIfNew

/-- This is a restatement of `mem_of_mem_insert` that is written to exactly match the
proof obligation in the statement of `get_insert`. -/
theorem mem_of_mem_insert' [TransCmp cmp] {k a : α} :
    a ∈ t.insert k → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  ExtTreeMap.mem_of_mem_insertIfNew'

@[simp, grind =]
theorem size_empty : (∅ : ExtTreeSet α cmp).size = 0 :=
  ExtTreeMap.size_empty

theorem isEmpty_eq_size_beq_zero : t.isEmpty = (t.size == 0) :=
  ExtTreeMap.isEmpty_eq_size_beq_zero

theorem eq_empty_iff_size_eq_zero [TransCmp cmp] : t = ∅ ↔ t.size = 0 :=
  ext_iff.trans ExtTreeMap.eq_empty_iff_size_eq_zero

@[grind =]
theorem size_insert [TransCmp cmp] {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  ExtTreeMap.size_insertIfNew

theorem size_le_size_insert [TransCmp cmp] {k : α} :
    t.size ≤ (t.insert k).size :=
  ExtTreeMap.size_le_size_insertIfNew

theorem size_insert_le [TransCmp cmp] {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  ExtTreeMap.size_insertIfNew_le

@[simp, grind =]
theorem erase_empty [TransCmp cmp] {k : α} : (∅ : ExtTreeSet α cmp).erase k = ∅ :=
  ext ExtTreeMap.erase_empty

@[simp, grind =]
theorem erase_eq_empty_iff [TransCmp cmp] {k : α} :
    t.erase k = ∅ ↔ t = ∅ ∨ (t.size = 1 ∧ k ∈ t) := by
  simpa only [ext_iff] using ExtTreeMap.erase_eq_empty_iff

theorem eq_empty_iff_erase_eq_empty_and_not_mem [TransCmp cmp] (k : α) :
    t = ∅ ↔ t.erase k = ∅ ∧ ¬k ∈ t := by
  simpa only [ext_iff] using ExtTreeMap.eq_empty_iff_erase_eq_empty_and_not_mem k

theorem ne_empty_of_erase_ne_empty [TransCmp cmp] {k : α} (h : t.erase k ≠ ∅) : t ≠ ∅ := by
  simp_all

@[simp, grind =]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  ExtTreeMap.contains_erase

@[simp, grind =]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  ExtTreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  ExtTreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  ExtTreeMap.mem_of_mem_erase

@[grind =]
theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  ExtTreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  ExtTreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  ExtTreeMap.size_le_size_erase

@[simp, grind =]
theorem get?_empty [TransCmp cmp] {a : α} : (∅ : ExtTreeSet α cmp).get? a = none :=
  ExtTreeMap.getKey?_empty

@[grind =] theorem get?_insert [TransCmp cmp] {k a : α} :
    (t.insert k).get? a = if cmp k a = .eq ∧ ¬k ∈ t then some k else t.get? a :=
  ExtTreeMap.getKey?_insertIfNew

theorem contains_eq_isSome_get? [TransCmp cmp] {a : α} :
    t.contains a = (t.get? a).isSome :=
  ExtTreeMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] {a : α} :
    (t.get? a).isSome = t.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  ExtTreeMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_get?_iff_mem [TransCmp cmp] {a : α} :
    (t.get? a).isSome ↔ a ∈ t :=
  mem_iff_isSome_get?.symm

theorem mem_of_get?_eq_some [TransCmp cmp] {k k' : α}
    (h : t.get? k = some k') : k' ∈ t :=
  ExtTreeMap.mem_of_getKey?_eq_some h

theorem get?_eq_some_iff [TransCmp cmp] {k k' : α} :
    t.get? k = some k' ↔ ∃ h, t.get k h = k' :=
  ExtTreeMap.getKey?_eq_some_iff

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.get? a = none :=
  ExtTreeMap.getKey?_eq_none_of_contains_eq_false

theorem get?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  ExtTreeMap.getKey?_eq_none

@[grind =] theorem get?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  ExtTreeMap.getKey?_erase

@[simp]
theorem get?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).get? k = none :=
  ExtTreeMap.getKey?_erase_self

theorem compare_get?_self [TransCmp cmp] {k : α} :
    (t.get? k).all (cmp · k = .eq) :=
  ExtTreeMap.compare_getKey?_self

theorem get?_congr [TransCmp cmp] {k k' : α} (h' : cmp k k' = .eq) :
    t.get? k = t.get? k' :=
  ExtTreeMap.getKey?_congr h'

theorem get?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : t.contains k) :
    t.get? k = some k :=
  ExtTreeMap.getKey?_eq_some_of_contains h'

theorem get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.get? k = some k :=
  ExtTreeMap.getKey?_eq_some_of_contains h'

@[grind =] theorem get_insert [TransCmp cmp] {k a : α} {h₁} :
    (t.insert k).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.get a (mem_of_mem_insert' h₁ h₂) :=
  ExtTreeMap.getKey_insertIfNew

@[simp, grind =] theorem get_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h') :=
  ExtTreeMap.getKey_erase

theorem get?_eq_some_get [TransCmp cmp] {a : α} (h') :
    t.get? a = some (t.get a h') :=
  ExtTreeMap.getKey?_eq_some_getKey h'

theorem get_eq_get_get? [TransCmp cmp] {k : α} {h} :
    t.get k h = (t.get? k).get (mem_iff_isSome_get?.mp h) :=
  ExtTreeMap.getKey_eq_get_getKey?

@[grind =] theorem get_get? [TransCmp cmp] {k : α} {h} :
    (t.get? k).get h = t.get k (mem_iff_isSome_get?.mpr h) :=
  ExtTreeMap.get_getKey?

theorem compare_get_self [TransCmp cmp] {k : α} (h' : k ∈ t) :
    cmp (t.get k h') k = .eq :=
  ExtTreeMap.compare_getKey_self h'

theorem get_congr [TransCmp cmp] {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.get k₁ h₁ = t.get k₂ ((mem_congr h').mp h₁) :=
  ExtTreeMap.getKey_congr h' h₁

@[simp, grind =]
theorem get_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.get k h' = k :=
  ExtTreeMap.getKey_eq h'

@[simp, grind =]
theorem get!_empty [TransCmp cmp] [Inhabited α] {a : α} :
    (∅ : ExtTreeSet α cmp).get! a = default :=
  ExtTreeMap.getKey!_empty

@[grind =] theorem get!_insert [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.insert k).get! a = if cmp k a = .eq ∧ ¬ k ∈ t then k else t.get! a :=
  ExtTreeMap.getKey!_insertIfNew

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.get! a = default :=
  ExtTreeMap.getKey!_eq_default_of_contains_eq_false

theorem get!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.get! a = default :=
  ExtTreeMap.getKey!_eq_default

@[grind =] theorem get!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  ExtTreeMap.getKey!_erase

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited α] {k : α} :
    (t.erase k).get! k = default :=
  ExtTreeMap.getKey!_erase_self

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = true → t.get? a = some (t.get! a) :=
  ExtTreeMap.getKey?_eq_some_getKey!_of_contains

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited α] {a : α} :
    a ∈ t → t.get? a = some (t.get! a) :=
  ExtTreeMap.getKey?_eq_some_getKey!

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited α] {a : α} :
    t.get! a = (t.get? a).get! :=
  ExtTreeMap.getKey!_eq_get!_getKey?

theorem get_eq_get! [TransCmp cmp] [Inhabited α] {a : α} {h} :
    t.get a h = t.get! a :=
  ExtTreeMap.getKey_eq_getKey!

theorem get!_congr [TransCmp cmp] [Inhabited α] {k k' : α} (h' : cmp k k' = .eq) :
    t.get! k = t.get! k' :=
  ExtTreeMap.getKey!_congr h'

theorem get!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    (h' : t.contains k) :
    t.get! k = k :=
  ExtTreeMap.getKey!_eq_of_contains h'

theorem get!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α} (h' : k ∈ t) :
    t.get! k = k :=
  ExtTreeMap.getKey!_eq_of_mem h'

@[simp, grind =]
theorem getD_empty [TransCmp cmp] {a : α} {fallback : α} :
    (∅ : ExtTreeSet α cmp).getD a fallback = fallback :=
  ExtTreeMap.getKeyD_empty

@[grind =] theorem getD_insert [TransCmp cmp] {k a fallback : α} :
    (t.insert k).getD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getD a fallback :=
  ExtTreeMap.getKeyD_insertIfNew

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getD a fallback = fallback :=
  ExtTreeMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  ExtTreeMap.getKeyD_eq_fallback

@[grind =] theorem getD_erase [TransCmp cmp] {k a fallback : α} :
    (t.erase k).getD a fallback =
      if cmp k a = .eq then fallback else t.getD a fallback :=
  ExtTreeMap.getKeyD_erase

@[simp]
theorem getD_erase_self [TransCmp cmp] {k fallback : α} :
    (t.erase k).getD k fallback = fallback :=
  ExtTreeMap.getKeyD_erase_self

theorem get?_eq_some_getD_of_contains [TransCmp cmp] {a fallback : α} :
    t.contains a = true → t.get? a = some (t.getD a fallback) :=
  ExtTreeMap.getKey?_eq_some_getKeyD_of_contains

theorem get?_eq_some_getD [TransCmp cmp] {a fallback : α} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  ExtTreeMap.getKey?_eq_some_getKeyD

theorem getD_eq_getD_get? [TransCmp cmp] {a fallback : α} :
    t.getD a fallback = (t.get? a).getD fallback :=
  ExtTreeMap.getKeyD_eq_getD_getKey?

theorem get_eq_getD [TransCmp cmp] {a fallback : α} {h} :
    t.get a h = t.getD a fallback :=
  ExtTreeMap.getKey_eq_getKeyD

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited α] {a : α} :
    t.get! a = t.getD a default :=
  ExtTreeMap.getKey!_eq_getKeyD_default

theorem getD_congr [TransCmp cmp] {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getD k fallback = t.getD k' fallback :=
  ExtTreeMap.getKeyD_congr h'

theorem getD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : t.contains k) :
    t.getD k fallback = k :=
  ExtTreeMap.getKeyD_eq_of_contains h'

theorem getD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : k ∈ t) :
    t.getD k fallback = k :=
  ExtTreeMap.getKeyD_eq_of_contains h'

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  ExtTreeMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| ExtTreeMap.containsThenInsertIfNew_snd

@[simp, grind =]
theorem length_toList [TransCmp cmp] :
    t.toList.length = t.size :=
  ExtTreeMap.length_keys

@[simp, grind =]
theorem isEmpty_toList [TransCmp cmp] :
    t.toList.isEmpty = t.isEmpty :=
  ExtTreeMap.isEmpty_keys

@[simp]
theorem toList_eq_nil_iff [TransCmp cmp] :
    t.toList = [] ↔ t = ∅ :=
  ExtTreeMap.keys_eq_nil_iff.trans ext_iff.symm

@[simp, grind =]
theorem contains_toList [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.toList.contains k = t.contains k :=
  ExtTreeMap.contains_keys

@[simp]
theorem mem_toList [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.toList ↔ k ∈ t :=
  ExtTreeMap.mem_keys

theorem distinct_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  ExtTreeMap.distinct_keys

theorem ordered_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => cmp a b = .lt) :=
  ExtTreeMap.ordered_keys

section Union

variable {t₁ t₂ : ExtTreeSet α cmp}

@[simp]
theorem union_eq [TransCmp cmp] : t₁.union t₂ = t₁ ∪ t₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [TransCmp cmp]
    {k : α} :
    (t₁ ∪ t₂).contains k = (t₁.contains k || t₂.contains k) :=
  ExtTreeMap.contains_union

/- mem -/
theorem mem_union_of_left [TransCmp cmp] {k : α} :
    k ∈ t₁ → k ∈ t₁ ∪ t₂ :=
  ExtTreeMap.mem_union_of_left

theorem mem_union_of_right [TransCmp cmp] {k : α} :
    k ∈ t₂ → k ∈ t₁ ∪ t₂ :=
   ExtTreeMap.mem_union_of_right

@[simp]
theorem mem_union_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ ↔ k ∈ t₁ ∨ k ∈ t₂ :=
  ExtTreeMap.mem_union_iff

theorem mem_of_mem_union_of_not_mem_right [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₂ → k ∈ t₁ :=
  ExtTreeMap.mem_of_mem_union_of_not_mem_right

theorem mem_of_mem_union_of_not_mem_left [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₁ → k ∈ t₂ :=
  ExtTreeMap.mem_of_mem_union_of_not_mem_left

/- get? -/
theorem get?_union [TransCmp cmp] {k : α} :
    (t₁ ∪ t₂).get? k = (t₂.get? k).or (t₁.get? k) :=
  ExtTreeMap.getKey?_union

theorem get?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get? k = t₂.get? k :=
  ExtTreeMap.getKey?_union_of_not_mem_left not_mem

/- get -/
theorem get_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).get k (mem_union_of_right mem) = t₂.get k mem :=
  ExtTreeMap.getKey_union_of_mem_right mem

theorem get_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).get k h' = t₂.get k (mem_of_mem_union_of_not_mem_left h' not_mem) :=
  ExtTreeMap.getKey_union_of_not_mem_left not_mem

theorem get_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂).get k h' = t₁.get k (mem_of_mem_union_of_not_mem_right h' not_mem) :=
  ExtTreeMap.getKey_union_of_not_mem_right not_mem

/- getD -/
theorem getD_union [TransCmp cmp] {k fallback : α} :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k (t₁.getD k fallback) :=
  ExtTreeMap.getKeyD_union

theorem getD_union_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k fallback :=
  ExtTreeMap.getKeyD_union_of_not_mem_left not_mem

theorem getD_union_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback :=
  ExtTreeMap.getKeyD_union_of_not_mem_right not_mem

/- get! -/
theorem get!_union [TransCmp cmp] [Inhabited α] {k : α} : (t₁ ∪ t₂).get! k = t₂.getD k (t₁.get! k) :=
  ExtTreeMap.getKey!_union

theorem get!_union_of_not_mem_left [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get! k = t₂.get! k :=
  ExtTreeMap.getKey!_union_of_not_mem_left not_mem

theorem get!_union_of_not_mem_right [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).get! k = t₁.get! k :=
  ExtTreeMap.getKey!_union_of_not_mem_right not_mem

/- size -/
theorem size_union_of_not_mem [TransCmp cmp] :
    (∀ (a : α), a ∈ t₁ → ¬a ∈ t₂) →
    (t₁ ∪ t₂).size = t₁.size + t₂.size :=
  ExtTreeMap.size_union_of_not_mem

theorem size_left_le_size_union [TransCmp cmp] : t₁.size ≤ (t₁ ∪ t₂).size :=
  ExtTreeMap.size_left_le_size_union

theorem size_right_le_size_union [TransCmp cmp] :
    t₂.size ≤ (t₁ ∪ t₂).size :=
  ExtTreeMap.size_right_le_size_union

theorem size_union_le_size_add_size [TransCmp cmp] :
    (t₁ ∪ t₂).size ≤ t₁.size + t₂.size :=
  ExtTreeMap.size_union_le_size_add_size

/- isEmpty -/
@[simp]
theorem isEmpty_union [TransCmp cmp] :
    (t₁ ∪ t₂).isEmpty = (t₁.isEmpty && t₂.isEmpty) :=
  ExtTreeMap.isEmpty_union

end Union

section Inter

variable {t₁ t₂ : ExtTreeSet α cmp}

@[simp]
theorem inter_eq [TransCmp cmp] : t₁.inter t₂ = t₁ ∩ t₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).contains k = (t₁.contains k && t₂.contains k) :=
  ExtTreeMap.contains_inter

/- mem -/
@[simp]
theorem mem_inter_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ :=
  ExtTreeMap.mem_inter_iff

theorem not_mem_inter_of_not_mem_left [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ ∩ t₂ :=
  ExtTreeMap.not_mem_inter_of_not_mem_left not_mem

theorem not_mem_inter_of_not_mem_right [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₂) :
    k ∉ t₁ ∩ t₂ :=
  ExtTreeMap.not_mem_inter_of_not_mem_right not_mem

/- get? -/
theorem get?_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).get? k =
    if k ∈ t₂ then t₁.get? k else none :=
  ExtTreeMap.getKey?_inter

theorem get?_inter_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get? k = t₁.get? k :=
  ExtTreeMap.getKey?_inter_of_mem_right mem

theorem get?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get? k = none :=
  ExtTreeMap.getKey?_inter_of_not_mem_left not_mem

theorem get?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get? k = none :=
  ExtTreeMap.getKey?_inter_of_not_mem_right not_mem

/- get -/
@[simp]
theorem get_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).get k h_mem =
    t₁.get k (mem_inter_iff.1 h_mem).1 :=
  ExtTreeMap.getKey_inter

/- getD -/
theorem getD_inter [TransCmp cmp] {k fallback : α} :
    (t₁ ∩ t₂).getD k fallback =
    if k ∈ t₂ then t₁.getD k fallback else fallback :=
  ExtTreeMap.getKeyD_inter

theorem getD_inter_of_mem_right [TransCmp cmp]
    {k fallback : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getD k fallback = t₁.getD k fallback :=
  ExtTreeMap.getKeyD_inter_of_mem_right mem

theorem getD_inter_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  ExtTreeMap.getKeyD_inter_of_not_mem_right not_mem

theorem getD_inter_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  ExtTreeMap.getKeyD_inter_of_not_mem_left not_mem

/- get! -/
theorem get!_inter [TransCmp cmp] [Inhabited α] {k : α} :
    (t₁ ∩ t₂).get! k =
    if k ∈ t₂ then t₁.get! k else default :=
  ExtTreeMap.getKey!_inter

theorem get!_inter_of_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get! k = t₁.get! k :=
  ExtTreeMap.getKey!_inter_of_mem_right mem

theorem get!_inter_of_not_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get! k = default :=
  ExtTreeMap.getKey!_inter_of_not_mem_right not_mem

theorem get!_inter_of_not_mem_left [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get! k = default :=
  ExtTreeMap.getKey!_inter_of_not_mem_left not_mem

/- size -/
theorem size_inter_le_size_left [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₁.size :=
  ExtTreeMap.size_inter_le_size_left

theorem size_inter_le_size_right [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₂.size :=
  ExtTreeMap.size_inter_le_size_right

theorem size_inter_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∈ t₂) :
    (t₁ ∩ t₂).size = t₁.size :=
  ExtTreeMap.size_inter_eq_size_left h

theorem size_inter_eq_size_right [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₂ → a ∈ t₁) :
    (t₁ ∩ t₂).size = t₂.size :=
  ExtTreeMap.size_inter_eq_size_right h

theorem size_add_size_eq_size_union_add_size_inter [TransCmp cmp] :
    t₁.size + t₂.size = (t₁ ∪ t₂).size + (t₁ ∩ t₂).size :=
  ExtTreeMap.size_add_size_eq_size_union_add_size_inter

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  ExtTreeMap.isEmpty_inter_left h

@[simp]
theorem isEmpty_inter_right [TransCmp cmp] (h : t₂.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  ExtTreeMap.isEmpty_inter_right h

theorem isEmpty_inter_iff [TransCmp cmp] :
    (t₁ ∩ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∉ t₂ :=
  ExtTreeMap.isEmpty_inter_iff

end Inter

section Diff

variable {t₁ t₂ : ExtTreeSet α cmp}

@[simp]
theorem diff_eq [TransCmp cmp] : t₁.diff t₂ = t₁ \ t₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).contains k = (t₁.contains k && !t₂.contains k) :=
  ExtTreeMap.contains_diff

/- mem -/
@[simp]
theorem mem_diff_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ \ t₂ ↔ k ∈ t₁ ∧ k ∉ t₂ :=
  ExtTreeMap.mem_diff_iff

theorem not_mem_diff_of_not_mem_left [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ \ t₂ :=
  ExtTreeMap.not_mem_diff_of_not_mem_left not_mem

theorem not_mem_diff_of_mem_right [TransCmp cmp] {k : α}
    (mem : k ∈ t₂) :
    k ∉ t₁ \ t₂ :=
  ExtTreeMap.not_mem_diff_of_mem_right mem

/- get? -/
theorem get?_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).get? k =
    if k ∈ t₂ then none else t₁.get? k :=
  ExtTreeMap.getKey?_diff

theorem get?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get? k = t₁.get? k :=
  ExtTreeMap.getKey?_diff_of_not_mem_right not_mem

theorem get?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get? k = none :=
  ExtTreeMap.getKey?_diff_of_not_mem_left not_mem

theorem get?_diff_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get? k = none :=
  ExtTreeMap.getKey?_diff_of_mem_right mem

/- get -/
theorem get_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).get k h_mem =
    t₁.get k (mem_diff_iff.1 h_mem).1 :=
  ExtTreeMap.getKey_diff

/- getD -/
theorem getD_diff [TransCmp cmp] {k fallback : α} :
    (t₁ \ t₂).getD k fallback =
    if k ∈ t₂ then fallback else t₁.getD k fallback :=
  ExtTreeMap.getKeyD_diff

theorem getD_diff_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getD k fallback = t₁.getD k fallback :=
  ExtTreeMap.getKeyD_diff_of_not_mem_right not_mem

theorem getD_diff_of_mem_right [TransCmp cmp]
    {k fallback : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getD k fallback = fallback :=
  ExtTreeMap.getKeyD_diff_of_mem_right mem

theorem getD_diff_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getD k fallback = fallback :=
  ExtTreeMap.getKeyD_diff_of_not_mem_left not_mem

/- get! -/
theorem get!_diff [TransCmp cmp] [Inhabited α] {k : α} :
    (t₁ \ t₂).get! k =
    if k ∈ t₂ then default else t₁.get! k :=
  ExtTreeMap.getKey!_diff

theorem get!_diff_of_not_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get! k = t₁.get! k :=
  ExtTreeMap.getKey!_diff_of_not_mem_right not_mem

theorem get!_diff_of_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get! k = default :=
  ExtTreeMap.getKey!_diff_of_mem_right mem

theorem get!_diff_of_not_mem_left [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get! k = default :=
  ExtTreeMap.getKey!_diff_of_not_mem_left not_mem

/- size -/
theorem size_diff_le_size_left [TransCmp cmp] :
    (t₁ \ t₂).size ≤ t₁.size :=
  ExtTreeMap.size_diff_le_size_left

theorem size_diff_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∉ t₂) :
    (t₁ \ t₂).size = t₁.size :=
  ExtTreeMap.size_diff_eq_size_left h

theorem size_diff_add_size_inter_eq_size_left [TransCmp cmp] :
    (t₁ \ t₂).size + (t₁ ∩ t₂).size = t₁.size :=
  ExtTreeMap.size_diff_add_size_inter_eq_size_left

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ \ t₂).isEmpty = true :=
  ExtTreeMap.isEmpty_diff_left h

theorem isEmpty_diff_iff [TransCmp cmp] :
    (t₁ \ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∈ t₂ :=
  ExtTreeMap.isEmpty_diff_iff

end Diff

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM f init :=
  ExtTreeMap.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_toList [TransCmp cmp] {f : δ → α → δ} {init : δ} :
    t.foldl f init = t.toList.foldl f init :=
  ExtTreeMap.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM f init :=
  ExtTreeMap.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_toList [TransCmp cmp] {f : α → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr f init :=
  ExtTreeMap.foldr_eq_foldr_keys

@[simp, grind =]
theorem forM_eq_forM [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    t.forM f = ForM.forM t f := rfl

theorem forM_eq_forM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t f = t.toList.forM f :=
  ExtTreeMap.forM_eq_forM_keys

@[simp, grind =]
theorem forIn_eq_forIn [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init f := rfl

theorem forIn_eq_forIn_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  ExtTreeMap.forIn_eq_forIn_keys

end monadic

@[simp, grind =]
theorem insertMany_nil [TransCmp cmp] : t.insertMany [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton [TransCmp cmp] {k : α} :
    t.insertMany [k] = t.insert k :=
  rfl

@[grind _=_]
theorem insertMany_cons [TransCmp cmp] {l : List α} {k : α} :
    t.insertMany (k :: l) = (t.insert k).insertMany l :=
  ext ExtTreeMap.insertManyIfNewUnit_cons

@[grind _=_]
theorem insertMany_append [TransCmp cmp] {l₁ l₂ : List α} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (t.insertMany l).contains k = (t.contains k || l.contains k) :=
  ExtTreeMap.contains_insertManyIfNewUnit_list

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    k ∈ insertMany t l ↔ k ∈ t ∨ l.contains k :=
  ExtTreeMap.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany t l → k ∈ t :=
  ExtTreeMap.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    get? (insertMany t l) k = none :=
  ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get? (insertMany t l) k' = some k :=
  ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem get?_insertMany_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} (mem : k ∈ t) :
    get? (insertMany t l) k = get? t k :=
  ExtTreeMap.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem get_insertMany_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} {h'} (contains : k ∈ t) :
    get (insertMany t l) k h' = get t k contains :=
  ExtTreeMap.getKey_insertManyIfNewUnit_list_of_mem contains

theorem get_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} (not_mem : ¬ k ∈ t)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get (insertMany t l) k' h' = k :=
  ExtTreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    get! (insertMany t l) k = default :=
  ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get!_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get! (insertMany t l) k' = k :=
  ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem get!_insertMany_list_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ t):
    get! (insertMany t l) k = get! t k :=
  ExtTreeMap.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getD_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getD (insertMany t l) k fallback = fallback :=
  ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getD_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getD (insertMany t l) k' fallback = k :=
  ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    {l : List α} {k fallback : α} (mem : k ∈ t) :
    getD (insertMany t l) k fallback = getD t k fallback :=
  ExtTreeMap.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertMany t l).size = t.size + l.length :=
  ExtTreeMap.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List α} :
    t.size ≤ (insertMany t l).size :=
  ExtTreeMap.size_le_size_insertManyIfNewUnit_list

grind_pattern size_le_size_insertMany_list => (insertMany t l).size

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List α} :
    (insertMany t l).size ≤ t.size + l.length :=
  ExtTreeMap.size_insertManyIfNewUnit_list_le

grind_pattern size_insertMany_list_le => (insertMany t l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] {l : List α} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  ExtTreeMap.isEmpty_insertManyIfNewUnit_list

@[simp]
theorem insertMany_list_eq_empty_iff [TransCmp cmp] {l : List α} :
    t.insertMany l = ∅ ↔ t = ∅ ∧ l = [] := by
  simpa only [ext_iff] using ExtTreeMap.insertManyIfNewUnit_list_eq_empty_iff

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List α) cmp =
      (∅ : ExtTreeSet α cmp) :=
  rfl

@[simp]
theorem ofList_singleton [TransCmp cmp] {k : α} :
    ofList [k] cmp = (∅ : ExtTreeSet α cmp).insert k :=
  rfl

@[grind _=_]
theorem ofList_cons [TransCmp cmp] {hd : α} {tl : List α} :
    ofList (hd :: tl) cmp =
      insertMany ((∅ : ExtTreeSet α cmp).insert hd) tl :=
  ext ExtTreeMap.unitOfList_cons

theorem ofList_eq_insertMany_empty [TransCmp cmp] {l : List α} :
    ofList l cmp = insertMany (∅ : ExtTreeSet α cmp) l :=
  match l with
  | [] => by simp
  | hd :: tl => by simp [ofList_cons, insertMany_cons]

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (ofList l cmp).contains k = l.contains k :=
  ExtTreeMap.contains_unitOfList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ ofList l cmp ↔ l.contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get? (ofList l cmp) k = none :=
  ExtTreeMap.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get? (ofList l cmp) k' = some k :=
  ExtTreeMap.getKey?_unitOfList_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    get (ofList l cmp) k' h' = k :=
  ExtTreeMap.getKey_unitOfList_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get! (ofList l cmp) k = default :=
  ExtTreeMap.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    get! (ofList l cmp) k' = k :=
  ExtTreeMap.getKey!_unitOfList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  ExtTreeMap.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getD (ofList l cmp) k' fallback = k :=
  ExtTreeMap.getKeyD_unitOfList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (ofList l cmp).size = l.length :=
  ExtTreeMap.size_unitOfList distinct

theorem size_ofList_le [TransCmp cmp] {l : List α} :
    (ofList l cmp).size ≤ l.length :=
  ExtTreeMap.size_unitOfList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp]
theorem ofList_eq_empty_iff [TransCmp cmp] {l : List α} :
    ofList l cmp = ∅ ↔ l = [] :=
  ext_iff.trans ExtTreeMap.unitOfList_eq_empty_iff

section Min

@[simp, grind =]
theorem min?_empty [TransCmp cmp] :
    (∅ : ExtTreeSet α cmp).min? = none :=
  ExtTreeMap.minKey?_empty

@[simp, grind =]
theorem min?_eq_none_iff [TransCmp cmp] :
    t.min? = none ↔ t = ∅ :=
  ExtTreeMap.minKey?_eq_none_iff.trans ext_iff.symm

theorem min?_eq_some_iff_get?_eq_self_and_forall [TransCmp cmp] {km} :
    t.min? = some km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtTreeMap.minKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem min?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.min? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtTreeMap.minKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_min?_eq_isEmpty [TransCmp cmp] :
    t.min?.isNone = t.isEmpty :=
  ExtTreeMap.isNone_minKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_min?_eq_not_isEmpty [TransCmp cmp] :
    t.min?.isSome = !t.isEmpty :=
  ExtTreeMap.isSome_minKey?_eq_not_isEmpty

theorem isSome_min?_iff_ne_empty [TransCmp cmp] :
    t.min?.isSome ↔ t ≠ ∅ :=
  ExtTreeMap.isSome_minKey?_iff_ne_empty.trans (not_congr ext_iff).symm

@[grind =] theorem min?_insert [TransCmp cmp] {k} :
    (t.insert k).min? =
      some (t.min?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  ExtTreeMap.minKey?_insertIfNew

theorem isSome_min?_insert [TransCmp cmp] {k} :
    (t.insert k).min?.isSome :=
  ExtTreeMap.isSome_minKey?_insertIfNew

theorem min_insert_of_isEmpty [TransCmp cmp] {k} (he : t.isEmpty) :
    (t.insert k).min insert_ne_empty = k :=
  ExtTreeMap.minKey_insertIfNew_of_isEmpty he

theorem min?_insert_of_isEmpty [TransCmp cmp] {k} (he : t.isEmpty) :
    (t.insert k).min? = some k :=
  ExtTreeMap.minKey?_insertIfNew_of_isEmpty he

theorem min!_insert_of_isEmpty [TransCmp cmp] [Inhabited α] {k} (he : t.isEmpty) :
    (t.insert k).min! = k :=
  ExtTreeMap.minKey!_insertIfNew_of_isEmpty he

theorem minD_insert_of_isEmpty [TransCmp cmp] {k} (he : t.isEmpty) {fallback : α} :
    (t.insert k).minD fallback = k :=
  ExtTreeMap.minKeyD_insertIfNew_of_isEmpty he

theorem min?_insert_le_min? [TransCmp cmp] {k km kmi} :
    (hkm : t.min? = some km) →
    (hkmi : (t.insert k |>.min? |>.get isSome_min?_insert) = kmi) →
    cmp kmi km |>.isLE :=
  ExtTreeMap.minKey?_insertIfNew_le_minKey?

theorem min?_insert_le_self [TransCmp cmp] {k kmi} :
    (hkmi : (t.insert k |>.min?.get isSome_min?_insert) = kmi) →
    cmp kmi k |>.isLE :=
  ExtTreeMap.minKey?_insertIfNew_le_self

theorem contains_min? [TransCmp cmp] {km} :
    (hkm : t.min? = some km) → t.contains km :=
  ExtTreeMap.contains_minKey?

theorem min?_mem [TransCmp cmp] {km} :
    (hkm : t.min? = some km) → km ∈ t :=
  ExtTreeMap.minKey?_mem

@[simp] theorem min?_toList [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.toList.min? = t.min? :=
  ExtDTreeMap.min?_keys

@[simp] theorem head?_toList [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.toList.head? = t.min? :=
  ExtDTreeMap.head?_keys

theorem isSome_min?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.min?.isSome :=
  ExtTreeMap.isSome_minKey?_of_contains

theorem isSome_min?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.min?.isSome :=
  ExtTreeMap.isSome_minKey?_of_mem

theorem min?_le_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.min?.get <| isSome_min?_of_contains hc) = km) →
    cmp km k |>.isLE :=
  ExtTreeMap.minKey?_le_of_contains

theorem min?_le_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.min?.get <| isSome_min?_of_mem hc) = km) →
    cmp km k |>.isLE :=
  ExtTreeMap.minKey?_le_of_mem

theorem le_min? [TransCmp cmp] {k} :
    (∀ k', t.min? = some k' → (cmp k k').isLE) ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtTreeMap.le_minKey?

theorem get?_min? [TransCmp cmp] {km} :
    (hkm : t.min? = some km) → t.get? km = some km :=
  ExtTreeMap.getKey?_minKey?

theorem get_min? [TransCmp cmp] {km hc} :
    (hkm : t.min?.get (isSome_min?_of_contains hc) = km) → t.get km hc = km :=
  ExtTreeMap.getKey_minKey?

theorem get!_min? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.min? = some km) → t.get! km = km :=
  ExtTreeMap.getKey!_minKey?

theorem getD_min? [TransCmp cmp] {km fallback} :
    (hkm : t.min? = some km) → t.getD km fallback = km :=
  ExtTreeMap.getKeyD_minKey?

@[simp]
theorem min?_bind_get? [TransCmp cmp] :
    t.min?.bind t.get? = t.min? :=
  ExtTreeMap.minKey?_bind_getKey?

theorem min?_erase_eq_iff_not_compare_eq_min? [TransCmp cmp] {k} :
    (t.erase k |>.min?) = t.min? ↔
      ∀ {km}, t.min? = some km → ¬ cmp k km = .eq :=
  ExtTreeMap.minKey?_erase_eq_iff_not_compare_eq_minKey?

theorem min?_erase_eq_of_not_compare_eq_min? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.min? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.min?) = t.min? :=
  ExtTreeMap.minKey?_erase_eq_of_not_compare_eq_minKey?

theorem isSome_min?_of_isSome_min?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.min?.isSome) →
    t.min?.isSome :=
  ExtTreeMap.isSome_minKey?_of_isSome_minKey?_erase

theorem min?_le_min?_erase [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.min?) = some kme) →
    (hkm : (t.min?.get <|
      isSome_min?_of_isSome_min?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  ExtTreeMap.minKey?_le_minKey?_erase

@[grind =_] theorem min?_eq_head?_toList [TransCmp cmp] :
    t.min? = t.toList.head? :=
  ExtTreeMap.minKey?_eq_head?_keys

theorem min_eq_get_min? [TransCmp cmp] {he} :
    t.min he = t.min?.get (isSome_min?_iff_ne_empty.mpr he) :=
  ExtTreeMap.minKey_eq_get_minKey?

theorem min?_eq_some_min [TransCmp cmp] (he) :
    t.min? = some (t.min he) :=
  ExtTreeMap.minKey?_eq_some_minKey (mt ext he)

theorem min_eq_iff_get?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.min he = km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtTreeMap.minKey_eq_iff_getKey?_eq_self_and_forall

theorem min_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.min he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtTreeMap.minKey_eq_iff_mem_and_forall

@[grind =] theorem min_insert [TransCmp cmp] {k} :
    (t.insert k).min insert_ne_empty =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  ExtTreeMap.minKey_insertIfNew

theorem min_insert_le_min [TransCmp cmp] {k he} :
    cmp (t.insert k |>.min insert_ne_empty)
      (t.min he) |>.isLE :=
  ExtTreeMap.minKey_insertIfNew_le_minKey

theorem min_insert_le_self [TransCmp cmp] {k} :
    cmp (t.insert k |>.min <| insert_ne_empty) k |>.isLE :=
  ExtTreeMap.minKey_insertIfNew_le_self

@[grind =] theorem contains_min [TransCmp cmp] {he} :
    t.contains (t.min he) :=
  ExtTreeMap.contains_minKey

theorem min_mem [TransCmp cmp] {he} :
    t.min he ∈ t :=
  ExtTreeMap.minKey_mem

grind_pattern min_mem => t.min he ∈ t

theorem min_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp (t.min (ne_empty_of_mem hc)) k |>.isLE :=
  ExtTreeMap.minKey_le_of_contains hc

theorem min_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp (t.min (ne_empty_of_mem hc)) k |>.isLE :=
  ExtTreeMap.minKey_le_of_mem hc

theorem le_min [TransCmp cmp] {k he} :
    (cmp k (t.min he)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtTreeMap.le_minKey

@[simp, grind =]
theorem get?_min [TransCmp cmp] {he} :
    t.get? (t.min he) = some (t.min he) :=
  ExtTreeMap.getKey?_minKey

@[simp, grind =]
theorem get_min [TransCmp cmp] {he hc} :
    t.get (t.min he) hc = t.min he :=
  ExtTreeMap.getKey_minKey

@[simp, grind =]
theorem get!_min [TransCmp cmp] [Inhabited α] {he} :
    t.get! (t.min he) = t.min he :=
  ExtTreeMap.getKey!_minKey

@[simp, grind =]
theorem getD_min [TransCmp cmp] {he fallback} :
    t.getD (t.min he) fallback = t.min he :=
  ExtTreeMap.getKeyD_minKey

@[simp]
theorem min_erase_eq_iff_not_compare_eq_min [TransCmp cmp] {k he} :
    (t.erase k |>.min he) =
        t.min (ne_empty_of_erase_ne_empty he) ↔
      ¬ cmp k (t.min <| ne_empty_of_erase_ne_empty he) = .eq :=
  ExtTreeMap.minKey_erase_eq_iff_not_compare_eq_minKey

theorem min_erase_eq_of_not_compare_eq_min [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.min (ne_empty_of_erase_ne_empty he)) = .eq) →
    (t.erase k |>.min he) =
      t.min (ne_empty_of_erase_ne_empty he) :=
  ExtTreeMap.minKey_erase_eq_of_not_compare_eq_minKey

theorem min_le_min_erase [TransCmp cmp] {k he} :
    cmp (t.min <| ne_empty_of_erase_ne_empty he)
      (t.erase k |>.min he) |>.isLE :=
  ExtTreeMap.minKey_le_minKey_erase

theorem min_eq_head_toList [TransCmp cmp] {he} :
    t.min he = t.toList.head (mt toList_eq_nil_iff.mp he) :=
  ExtTreeMap.minKey_eq_head_keys

theorem min?_eq_some_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.min? = some t.min! :=
  ExtTreeMap.minKey?_eq_some_minKey! (mt ext he)

theorem min_eq_min! [TransCmp cmp] [Inhabited α] {he : t ≠ ∅} :
    t.min he = t.min! :=
  ExtTreeMap.minKey_eq_minKey!

theorem min!_empty [TransCmp cmp] [Inhabited α] :
    (∅ : ExtTreeSet α cmp).min! = default :=
  ExtTreeMap.minKey!_empty

theorem min!_eq_iff_get?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.min! = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtTreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem min!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.min! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtTreeMap.minKey!_eq_iff_mem_and_forall (mt ext he)

@[grind =] theorem min!_insert [TransCmp cmp] [Inhabited α] {k} :
    (t.insert k |>.min!) =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  ExtTreeMap.minKey!_insertIfNew

theorem min!_insert_le_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    cmp (t.insert k |>.min!) t.min! |>.isLE :=
  ExtTreeMap.minKey!_insertIfNew_le_minKey! (mt ext he)

theorem min!_insert_le_self [TransCmp cmp] [Inhabited α] {k} :
    cmp (t.insert k |>.min!) k |>.isLE :=
  ExtTreeMap.minKey!_insertIfNew_le_self

@[grind =] theorem contains_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.contains t.min! :=
  ExtTreeMap.contains_minKey! (mt ext he)

theorem min!_mem [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.min! ∈ t :=
  ExtTreeMap.minKey!_mem (mt ext he)

grind_pattern min!_mem => t.min! ∈ t

theorem min!_le_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp t.min! k |>.isLE :=
  ExtTreeMap.minKey!_le_of_contains hc

theorem min!_le_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp t.min! k |>.isLE :=
  ExtTreeMap.minKey!_le_of_mem hc

theorem le_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    (cmp k t.min!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtTreeMap.le_minKey! (mt ext he)

theorem get?_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.get? t.min! = some t.min! :=
  ExtTreeMap.getKey?_minKey! (mt ext he)

@[grind =] theorem get_min! [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.min! hc = t.min! :=
  ExtTreeMap.getKey_minKey!

@[simp, grind =]
theorem get_min!_eq_min [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.min! hc = t.min (ne_empty_of_mem hc) :=
  ExtTreeMap.getKey_minKey!_eq_minKey

theorem get!_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.get! t.min! = t.min! :=
  ExtTreeMap.getKey!_minKey! (mt ext he)

theorem getD_min! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getD t.min! fallback = t.min! :=
  ExtTreeMap.getKeyD_minKey! (mt ext he)

theorem min!_erase_eq_of_not_compare_min!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k t.min! = .eq) :
    (t.erase k |>.min!) = t.min! :=
  ExtTreeMap.minKey!_erase_eq_of_not_compare_minKey!_eq (mt ext he) heq

theorem min!_le_min!_erase [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) :
    cmp t.min! (t.erase k |>.min!) |>.isLE :=
  ExtTreeMap.minKey!_le_minKey!_erase (mt ext he)

theorem min!_eq_head!_toList [TransCmp cmp] [Inhabited α] :
    t.min! = t.toList.head! :=
  ExtTreeMap.minKey!_eq_head!_keys

theorem min?_eq_some_minD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.min? = some (t.minD fallback) :=
  ExtTreeMap.minKey?_eq_some_minKeyD (mt ext he)

theorem minD_empty [TransCmp cmp] {fallback} :
    (∅ : ExtTreeSet α cmp).minD fallback = fallback :=
  ExtTreeMap.minKeyD_empty

theorem min!_eq_minD_default [TransCmp cmp] [Inhabited α] :
    t.min! = t.minD default :=
  ExtTreeMap.minKey!_eq_minKeyD_default

theorem minD_eq_iff_get?_eq_self_and_forall [TransCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.minD fallback = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtTreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem minD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.minD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtTreeMap.minKeyD_eq_iff_mem_and_forall (mt ext he)

@[grind =] theorem minD_insert [TransCmp cmp] {k fallback} :
    (t.insert k |>.minD fallback) =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  ExtTreeMap.minKeyD_insertIfNew

theorem minD_insert_le_minD [TransCmp cmp]
    (he : t ≠ ∅) {k fallback} :
    cmp (t.insert k |>.minD fallback) (t.minD fallback) |>.isLE :=
  ExtTreeMap.minKeyD_insertIfNew_le_minKeyD (mt ext he)

theorem minD_insert_le_self [TransCmp cmp] {k fallback} :
    cmp (t.insert k |>.minD fallback) k |>.isLE :=
  ExtTreeMap.minKeyD_insertIfNew_le_self

@[grind =] theorem contains_minD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.contains (t.minD fallback) :=
  ExtTreeMap.contains_minKeyD (mt ext he)

theorem minD_mem [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.minD fallback ∈ t :=
  ExtTreeMap.minKeyD_mem (mt ext he)

grind_pattern minD_mem => t.minD fallback ∈ t

theorem minD_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp (t.minD fallback) k |>.isLE :=
  ExtTreeMap.minKeyD_le_of_contains hc

theorem minD_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp (t.minD fallback) k |>.isLE :=
  ExtTreeMap.minKeyD_le_of_mem hc

theorem le_minD [TransCmp cmp] (he : t ≠ ∅) {k fallback} :
    (cmp k (t.minD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtTreeMap.le_minKeyD (mt ext he)

theorem get?_minD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.get? (t.minD fallback) = some (t.minD fallback) :=
  ExtTreeMap.getKey?_minKeyD (mt ext he)

@[grind =] theorem get_minD [TransCmp cmp] {fallback hc} :
    t.get (t.minD fallback) hc = t.minD fallback :=
  ExtTreeMap.getKey_minKeyD

theorem get!_minD [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.get! (t.minD fallback) = t.minD fallback :=
  ExtTreeMap.getKey!_minKeyD (mt ext he)

theorem getD_minD [TransCmp cmp] (he : t ≠ ∅) {fallback fallback'} :
    t.getD (t.minD fallback) fallback' = t.minD fallback :=
  ExtTreeMap.getKeyD_minKeyD (mt ext he)

theorem minD_erase_eq_of_not_compare_minD_eq [TransCmp cmp] {k fallback}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k (t.minD fallback) = .eq) :
    (t.erase k |>.minD fallback) = t.minD fallback :=
  ExtTreeMap.minKeyD_erase_eq_of_not_compare_minKeyD_eq (mt ext he) heq

theorem minD_le_minD_erase [TransCmp cmp] {k}
    (he : t.erase k ≠ ∅) {fallback} :
    cmp (t.minD fallback) (t.erase k |>.minD fallback) |>.isLE :=
  ExtTreeMap.minKeyD_le_minKeyD_erase (mt ext he)

theorem minD_eq_headD_toList [TransCmp cmp] {fallback} :
    t.minD fallback = t.toList.headD fallback :=
  ExtTreeMap.minKeyD_eq_headD_keys

end Min

section Max

@[simp, grind =]
theorem max?_empty [TransCmp cmp] :
    (∅ : ExtTreeSet α cmp).max? = none :=
  ExtTreeMap.maxKey?_empty

@[simp, grind =]
theorem max?_eq_none_iff [TransCmp cmp] :
    t.max? = none ↔ t = ∅ :=
  ExtTreeMap.maxKey?_eq_none_iff.trans ext_iff.symm

theorem max?_eq_some_iff_get?_eq_self_and_forall [TransCmp cmp] {km} :
    t.max? = some km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtTreeMap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem max?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.max? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_max?_eq_isEmpty [TransCmp cmp] :
    t.max?.isNone = t.isEmpty :=
  ExtTreeMap.isNone_maxKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_max?_eq_not_isEmpty [TransCmp cmp] :
    t.max?.isSome = !t.isEmpty :=
  ExtTreeMap.isSome_maxKey?_eq_not_isEmpty

theorem isSome_max?_iff_ne_empty [TransCmp cmp] :
    t.max?.isSome ↔ t ≠ ∅ :=
  ExtTreeMap.isSome_maxKey?_iff_ne_empty.trans (not_congr ext_iff).symm

@[grind =] theorem max?_insert [TransCmp cmp] {k} :
    (t.insert k).max? =
      some (t.max?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  ExtTreeMap.maxKey?_insertIfNew

theorem isSome_max?_insert [TransCmp cmp] {k} :
    (t.insert k).max?.isSome :=
  ExtTreeMap.isSome_maxKey?_insertIfNew

theorem max?_le_max?_insert [TransCmp cmp] {k km kmi} :
    (hkm : t.max? = some km) →
    (hkmi : (t.insert k |>.max? |>.get isSome_max?_insert) = kmi) →
    cmp km kmi |>.isLE :=
  ExtTreeMap.maxKey?_le_maxKey?_insertIfNew

theorem self_le_max?_insert [TransCmp cmp] {k kmi} :
    (hkmi : (t.insert k |>.max?.get isSome_max?_insert) = kmi) →
    cmp k kmi |>.isLE :=
  ExtTreeMap.self_le_maxKey?_insertIfNew

theorem contains_max? [TransCmp cmp] {km} :
    (hkm : t.max? = some km) → t.contains km :=
  ExtTreeMap.contains_maxKey?

theorem max?_mem [TransCmp cmp] {km} :
    (hkm : t.max? = some km) → km ∈ t :=
  ExtTreeMap.maxKey?_mem

theorem isSome_max?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.max?.isSome :=
  ExtTreeMap.isSome_maxKey?_of_contains

theorem isSome_max?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.max?.isSome :=
  ExtTreeMap.isSome_maxKey?_of_mem

theorem le_max?_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.max?.get <| isSome_max?_of_contains hc) = km) →
    cmp k km |>.isLE :=
  ExtTreeMap.le_maxKey?_of_contains

theorem le_max?_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.max?.get <| isSome_max?_of_mem hc) = km) →
    cmp k km |>.isLE :=
  ExtTreeMap.le_maxKey?_of_mem

theorem max?_le [TransCmp cmp] {k} :
    (∀ k', t.max? = some k' → (cmp k' k).isLE) ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtTreeMap.maxKey?_le

theorem get?_max? [TransCmp cmp] {km} :
    (hkm : t.max? = some km) → t.get? km = some km :=
  ExtTreeMap.getKey?_maxKey?

theorem get_max? [TransCmp cmp] {km hc} :
    (hkm : t.max?.get (isSome_max?_of_contains hc) = km) → t.get km hc = km :=
  ExtTreeMap.getKey_maxKey?

theorem get!_max? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.max? = some km) → t.get! km = km :=
  ExtTreeMap.getKey!_maxKey?

theorem getD_max? [TransCmp cmp] {km fallback} :
    (hkm : t.max? = some km) → t.getD km fallback = km :=
  ExtTreeMap.getKeyD_maxKey?

@[simp]
theorem max?_bind_get? [TransCmp cmp] :
    t.max?.bind t.get? = t.max? :=
  ExtTreeMap.maxKey?_bind_getKey?

theorem max?_erase_eq_iff_not_compare_eq_max? [TransCmp cmp] {k} :
    (t.erase k |>.max?) = t.max? ↔
      ∀ {km}, t.max? = some km → ¬ cmp k km = .eq :=
  ExtTreeMap.maxKey?_erase_eq_iff_not_compare_eq_maxKey?

theorem max?_erase_eq_of_not_compare_eq_max? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.max? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.max?) = t.max? :=
  ExtTreeMap.maxKey?_erase_eq_of_not_compare_eq_maxKey?

theorem isSome_max?_of_isSome_max?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.max?.isSome) →
    t.max?.isSome :=
  ExtTreeMap.isSome_maxKey?_of_isSome_maxKey?_erase

theorem max?_erase_le_max? [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.max?) = some kme) →
    (hkm : (t.max?.get <|
      isSome_max?_of_isSome_max?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  ExtTreeMap.maxKey?_erase_le_maxKey?

theorem max?_eq_getLast?_toList [TransCmp cmp] :
    t.max? = t.toList.getLast? :=
  ExtTreeMap.maxKey?_eq_getLast?_keys

theorem max_eq_get_max? [TransCmp cmp] {he} :
    t.max he = t.max?.get (isSome_max?_iff_ne_empty.mpr he) :=
  ExtTreeMap.maxKey_eq_get_maxKey?

theorem max?_eq_some_max [TransCmp cmp] (he) :
    t.max? = some (t.max he) :=
  ExtTreeMap.maxKey?_eq_some_maxKey (mt ext he)

theorem max_eq_iff_get?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.max he = km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtTreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall

theorem max_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.max he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtTreeMap.maxKey_eq_iff_mem_and_forall

@[grind =] theorem max_insert [TransCmp cmp] {k} :
    (t.insert k).max insert_ne_empty =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  ExtTreeMap.maxKey_insertIfNew

theorem max_le_max_insert [TransCmp cmp] {k he} :
    cmp (t.max he)
      (t.insert k |>.max insert_ne_empty) |>.isLE :=
  ExtTreeMap.maxKey_le_maxKey_insertIfNew

theorem self_le_max_insert [TransCmp cmp] {k} :
    cmp k (t.insert k |>.max <| insert_ne_empty) |>.isLE :=
  ExtTreeMap.self_le_maxKey_insertIfNew

@[grind =] theorem contains_max [TransCmp cmp] {he} :
    t.contains (t.max he) :=
  ExtTreeMap.contains_maxKey

theorem max_mem [TransCmp cmp] {he} :
    t.max he ∈ t :=
  ExtTreeMap.maxKey_mem

grind_pattern max_mem => t.max he ∈ t

theorem le_max_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp k (t.max (ne_empty_of_mem hc)) |>.isLE :=
  ExtTreeMap.le_maxKey_of_contains hc

theorem le_max_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp k (t.max (ne_empty_of_mem hc)) |>.isLE :=
  ExtTreeMap.le_maxKey_of_mem hc

theorem max_le [TransCmp cmp] {k he} :
    (cmp (t.max he) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtTreeMap.maxKey_le

@[simp, grind =]
theorem get?_max [TransCmp cmp] {he} :
    t.get? (t.max he) = some (t.max he) :=
  ExtTreeMap.getKey?_maxKey

@[simp, grind =]
theorem get_max [TransCmp cmp] {he hc} :
    t.get (t.max he) hc = t.max he :=
  ExtTreeMap.getKey_maxKey

@[simp, grind =]
theorem get!_max [TransCmp cmp] [Inhabited α] {he} :
    t.get! (t.max he) = t.max he :=
  ExtTreeMap.getKey!_maxKey

@[simp, grind =]
theorem getD_max [TransCmp cmp] {he fallback} :
    t.getD (t.max he) fallback = t.max he :=
  ExtTreeMap.getKeyD_maxKey

@[simp]
theorem max_erase_eq_iff_not_compare_eq_max [TransCmp cmp] {k he} :
    (t.erase k |>.max he) =
        t.max (ne_empty_of_erase_ne_empty he) ↔
      ¬ cmp k (t.max <| ne_empty_of_erase_ne_empty he) = .eq :=
  ExtTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey

theorem max_erase_eq_of_not_compare_eq_max [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.max (ne_empty_of_erase_ne_empty he)) = .eq) →
    (t.erase k |>.max he) =
      t.max (ne_empty_of_erase_ne_empty he) :=
  ExtTreeMap.maxKey_erase_eq_of_not_compare_eq_maxKey

theorem max_erase_le_max [TransCmp cmp] {k he} :
    cmp (t.erase k |>.max he)
      (t.max <| ne_empty_of_erase_ne_empty he) |>.isLE :=
  ExtTreeMap.maxKey_erase_le_maxKey

@[grind =_]
theorem max_eq_getLast_toList [TransCmp cmp] {he} :
    t.max he = t.toList.getLast (mt toList_eq_nil_iff.mp he) :=
  ExtTreeMap.maxKey_eq_getLast_keys

theorem max?_eq_some_max! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.max? = some t.max! :=
  ExtTreeMap.maxKey?_eq_some_maxKey! (mt ext he)

theorem max_eq_max! [TransCmp cmp] [Inhabited α] {he : t ≠ ∅} :
    t.max he = t.max! :=
  ExtTreeMap.maxKey_eq_maxKey!

theorem max!_empty [TransCmp cmp] [Inhabited α] :
    (∅ : ExtTreeSet α cmp).max! = default :=
  ExtTreeMap.maxKey!_empty

theorem max!_eq_iff_get?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.max! = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtTreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem max!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.max! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtTreeMap.maxKey!_eq_iff_mem_and_forall (mt ext he)

@[grind =] theorem max!_insert [TransCmp cmp] [Inhabited α] {k} :
    (t.insert k |>.max!) =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  ExtTreeMap.maxKey!_insertIfNew

theorem max!_le_max!_insert [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    cmp t.max! (t.insert k |>.max!) |>.isLE :=
  ExtTreeMap.maxKey!_le_maxKey!_insertIfNew (mt ext he)

theorem self_le_max!_insert [TransCmp cmp] [Inhabited α] {k} :
    cmp k (t.insert k |>.max!) |>.isLE :=
  ExtTreeMap.self_le_maxKey!_insertIfNew

@[grind =] theorem contains_max! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.contains t.max! :=
  ExtTreeMap.contains_maxKey! (mt ext he)

theorem max!_mem [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.max! ∈ t :=
  ExtTreeMap.maxKey!_mem (mt ext he)

grind_pattern max!_mem => t.max! ∈ t

theorem le_max!_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp k t.max! |>.isLE :=
  ExtTreeMap.le_maxKey!_of_contains hc

theorem le_max!_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp k t.max! |>.isLE :=
  ExtTreeMap.le_maxKey!_of_mem hc

theorem max!_le [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    (cmp t.max! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtTreeMap.maxKey!_le (mt ext he)

theorem get?_max! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.get? t.max! = some t.max! :=
  ExtTreeMap.getKey?_maxKey! (mt ext he)

@[grind =] theorem get_max! [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.max! hc = t.max! :=
  ExtTreeMap.getKey_maxKey!

@[simp, grind =]
theorem get_max!_eq_max [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.max! hc = t.max (ne_empty_of_mem hc) :=
  ExtTreeMap.getKey_maxKey!_eq_maxKey

theorem get!_max! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.get! t.max! = t.max! :=
  ExtTreeMap.getKey!_maxKey! (mt ext he)

theorem getD_max! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getD t.max! fallback = t.max! :=
  ExtTreeMap.getKeyD_maxKey! (mt ext he)

theorem max!_erase_eq_of_not_compare_max!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k t.max! = .eq) :
    (t.erase k |>.max!) = t.max! :=
  ExtTreeMap.maxKey!_erase_eq_of_not_compare_maxKey!_eq (mt ext he) heq

theorem max!_erase_le_max! [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) :
    cmp (t.erase k |>.max!) t.max! |>.isLE :=
  ExtTreeMap.maxKey!_erase_le_maxKey! (mt ext he)

@[grind =_]
theorem max!_eq_getLast!_toList [TransCmp cmp] [Inhabited α] :
    t.max! = t.toList.getLast! :=
  ExtTreeMap.maxKey!_eq_getLast!_keys

theorem max?_eq_some_maxD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.max? = some (t.maxD fallback) :=
  ExtTreeMap.maxKey?_eq_some_maxKeyD (mt ext he)

theorem maxD_empty [TransCmp cmp] {fallback} :
    (∅ : ExtTreeSet α cmp).maxD fallback = fallback :=
  ExtTreeMap.maxKeyD_empty

theorem max!_eq_maxD_default [TransCmp cmp] [Inhabited α] :
    t.max! = t.maxD default :=
  ExtTreeMap.maxKey!_eq_maxKeyD_default

theorem maxD_eq_iff_get?_eq_self_and_forall [TransCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.maxD fallback = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtTreeMap.maxKeyD_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem maxD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.maxD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtTreeMap.maxKeyD_eq_iff_mem_and_forall (mt ext he)

@[grind =] theorem maxD_insert [TransCmp cmp] {k fallback} :
    (t.insert k |>.maxD fallback) =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  ExtTreeMap.maxKeyD_insertIfNew

theorem maxD_le_maxD_insert [TransCmp cmp]
    (he : t ≠ ∅) {k fallback} :
    cmp (t.maxD fallback) (t.insert k |>.maxD fallback) |>.isLE :=
  ExtTreeMap.maxKeyD_le_maxKeyD_insertIfNew (mt ext he)

theorem self_le_maxD_insert [TransCmp cmp] {k fallback} :
    cmp k (t.insert k |>.maxD fallback) |>.isLE :=
  ExtTreeMap.self_le_maxKeyD_insertIfNew

@[grind =] theorem contains_maxD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.contains (t.maxD fallback) :=
  ExtTreeMap.contains_maxKeyD (mt ext he)

theorem maxD_mem [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.maxD fallback ∈ t :=
  ExtTreeMap.maxKeyD_mem (mt ext he)

grind_pattern maxD_mem => t.maxD fallback ∈ t

theorem le_maxD_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxD fallback) |>.isLE :=
  ExtTreeMap.le_maxKeyD_of_contains hc

theorem le_maxD_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxD fallback) |>.isLE :=
  ExtTreeMap.le_maxKeyD_of_mem hc

theorem maxD_le [TransCmp cmp] (he : t ≠ ∅) {k fallback} :
    (cmp (t.maxD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtTreeMap.maxKeyD_le (mt ext he)

theorem get?_maxD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.get? (t.maxD fallback) = some (t.maxD fallback) :=
  ExtTreeMap.getKey?_maxKeyD (mt ext he)

@[grind =] theorem get_maxD [TransCmp cmp] {fallback hc} :
    t.get (t.maxD fallback) hc = t.maxD fallback :=
  ExtTreeMap.getKey_maxKeyD

theorem get!_maxD [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.get! (t.maxD fallback) = t.maxD fallback :=
  ExtTreeMap.getKey!_maxKeyD (mt ext he)

theorem getD_maxD [TransCmp cmp] (he : t ≠ ∅) {fallback fallback'} :
    t.getD (t.maxD fallback) fallback' = t.maxD fallback :=
  ExtTreeMap.getKeyD_maxKeyD (mt ext he)

theorem maxD_erase_eq_of_not_compare_maxD_eq [TransCmp cmp] {k fallback}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k (t.maxD fallback) = .eq) :
    (t.erase k |>.maxD fallback) = t.maxD fallback :=
  ExtTreeMap.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq (mt ext he) heq

theorem maxD_erase_le_maxD [TransCmp cmp] {k}
    (he : t.erase k ≠ ∅) {fallback} :
    cmp (t.erase k |>.maxD fallback) (t.maxD fallback) |>.isLE :=
  ExtTreeMap.maxKeyD_erase_le_maxKeyD (mt ext he)

theorem maxD_eq_getLastD_toList [TransCmp cmp] {fallback} :
    t.maxD fallback = t.toList.getLastD fallback :=
  ExtTreeMap.maxKeyD_eq_getLastD_keys

end Max

section Ext

variable {t₁ t₂ : ExtTreeSet α cmp}

@[ext 900, grind ext]
theorem ext_get? [TransCmp cmp] {t₁ t₂ : ExtTreeSet α cmp}
    (h : ∀ k, t₁.get? k = t₂.get? k) : t₁ = t₂ :=
  ext (ExtTreeMap.ext_getKey?_unit h)

theorem ext_contains [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : ExtTreeSet α cmp}
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ = t₂ :=
  ext (ExtTreeMap.ext_contains_unit h)

@[ext]
theorem ext_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : ExtTreeSet α cmp}
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ = t₂ :=
  ext (ExtTreeMap.ext_mem_unit h)

theorem ext_toList [TransCmp cmp] (h : t₁.toList.Perm t₂.toList) : t₁ = t₂ :=
  ext (ExtTreeMap.ext_keys_unit h)

theorem toList_inj [TransCmp cmp] : t₁.toList = t₂.toList ↔ t₁ = t₂ :=
  ⟨ext_toList ∘ .of_eq, fun h => h ▸ rfl⟩

end Ext

section filter

variable {t : ExtTreeSet α cmp}

theorem toList_filter [TransCmp cmp] {f : α → Bool} :
    (t.filter f).toList = t.toList.filter f :=
  ExtTreeMap.keys_filter_key

theorem filter_eq_empty_iff [TransCmp cmp] {f : α → Bool} :
    t.filter f = ∅ ↔ ∀ k h, f (t.get k h) = false :=
  ext_iff.trans ExtTreeMap.filter_eq_empty_iff

-- TODO: `contains_filter` is missing.

@[simp, grind =]
theorem mem_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    k ∈ t.filter f ↔ ∃ h, f (t.get k h) :=
  ExtTreeMap.mem_filter

theorem contains_of_contains_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    (t.filter f).contains k → t.contains k :=
  ExtTreeMap.contains_of_contains_filter

theorem mem_of_mem_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    k ∈ t.filter f → k ∈ t :=
  ExtTreeMap.mem_of_mem_filter

theorem size_filter_le_size [TransCmp cmp]
    {f : α → Bool} :
    (t.filter f).size ≤ t.size :=
  ExtTreeMap.size_filter_le_size

grind_pattern size_filter_le_size => (t.filter f).size

theorem size_filter_eq_size_iff [TransCmp cmp]
    {f : α → Bool} :
    (t.filter f).size = t.size ↔ ∀ k h, f (t.get k h) :=
  ExtTreeMap.size_filter_eq_size_iff

theorem filter_eq_self_iff [TransCmp cmp]
    {f : α → Bool} :
    t.filter f = t ↔ ∀ k h, f (t.get k h) :=
  ext_iff.trans ExtTreeMap.filter_eq_self_iff

@[simp, grind =]
theorem get?_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    (t.filter f).get? k = (t.get? k).filter f :=
  ExtTreeMap.getKey?_filter_key

@[simp, grind =]
theorem get_filter [TransCmp cmp]
    {f : α → Bool} {k : α} {h} :
    (t.filter f).get k h = t.get k (mem_of_mem_filter h) :=
  ExtTreeMap.getKey_filter

@[grind =]
theorem get!_filter [TransCmp cmp] [Inhabited α]
    {f : α → Bool} {k : α} :
    (t.filter f).get! k = ((t.get? k).filter f).get! :=
  ExtTreeMap.getKey!_filter_key

@[grind =]
theorem getD_filter [TransCmp cmp]
    {f : α → Bool} {k fallback : α} :
    (t.filter f).getD k fallback = ((t.get? k).filter f).getD fallback :=
  ExtTreeMap.getKeyD_filter_key

end filter

end Std.ExtTreeSet
