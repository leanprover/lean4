/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
module

prelude
import Std.Data.TreeMap.Lemmas
import Std.Data.DTreeMap.Lemmas
public import Std.Data.TreeSet.AdditionalOperations

@[expose] public section

/-!
# Tree set lemmas

This file contains lemmas about `Std.TreeSet`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.TreeSet

variable {α : Type u} {cmp : α → α → Ordering} {t : TreeSet α cmp}

private theorem ext {t t' : TreeSet α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyc : (∅ : TreeSet α cmp).isEmpty :=
  TreeMap.isEmpty_emptyc

@[simp, grind =]
theorem isEmpty_insert [TransCmp cmp] {k : α} :
    (t.insert k).isEmpty = false :=
  TreeMap.isEmpty_insertIfNew

@[grind =]
theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {k : α} : t.contains k ↔ k ∈ t :=
  TreeMap.contains_iff_mem

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  TreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.mem_congr hab

@[simp, grind =]
theorem contains_emptyc {k : α} : (∅ : TreeSet α cmp).contains k = false :=
  TreeMap.contains_emptyc

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : TreeSet α cmp) :=
  TreeMap.not_mem_emptyc

theorem contains_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → t.contains a = false :=
  TreeMap.contains_of_isEmpty

theorem not_mem_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → a ∉ t :=
  TreeMap.not_mem_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  TreeMap.isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  TreeMap.isEmpty_eq_false_iff_exists_mem

theorem isEmpty_eq_false_of_contains [TransCmp cmp] {a : α} (hc : t.contains a = true) :
    t.isEmpty = false :=
  TreeMap.isEmpty_eq_false_of_contains hc

theorem isEmpty_iff_forall_contains [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  TreeMap.isEmpty_iff_forall_contains

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  TreeMap.isEmpty_iff_forall_not_mem

@[simp]
theorem insert_eq_insert {p : α} : Insert.insert p t = t.insert p :=
  rfl

@[simp]
theorem singleton_eq_insert {p : α} :
    Singleton.singleton p = (∅ : TreeSet α cmp).insert p :=
  rfl

@[simp, grind =]
theorem contains_insert [h : TransCmp cmp] {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insert [TransCmp cmp] {k a : α} :
    a ∈ t.insert k ↔ cmp k a = .eq ∨ a ∈ t :=
  TreeMap.mem_insertIfNew

theorem contains_insert_self [TransCmp cmp] {k : α} :
    (t.insert k).contains k :=
  TreeMap.contains_insertIfNew_self

theorem mem_of_get_eq  {k v : α} {w} (_ : t.get k w = v) : k ∈ t := w

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

@[simp, grind =]
theorem size_emptyc : (∅ : TreeSet α cmp).size = 0 :=
  TreeMap.size_emptyc

theorem isEmpty_eq_size_eq_zero :
    t.isEmpty = (t.size == 0) :=
  TreeMap.isEmpty_eq_size_eq_zero

@[grind =]
theorem size_insert [TransCmp cmp] {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  TreeMap.size_insertIfNew

theorem size_le_size_insert [TransCmp cmp] {k : α} :
    t.size ≤ (t.insert k).size :=
  TreeMap.size_le_size_insertIfNew

theorem size_insert_le [TransCmp cmp] {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  TreeMap.size_insertIfNew_le

@[simp, grind =]
theorem erase_emptyc {k : α} :
    (∅ : TreeSet α cmp).erase k = ∅ :=
  ext <| TreeMap.erase_emptyc

@[simp, grind =]
theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  TreeMap.isEmpty_erase

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransCmp cmp] (k : α) :
    t.isEmpty = ((t.erase k).isEmpty && !(t.contains k)) :=
  TreeMap.isEmpty_eq_isEmpty_erase_and_not_contains k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransCmp cmp] {k : α}
    (he : (t.erase k).isEmpty = false) :
    t.isEmpty = false :=
  TreeMap.isEmpty_eq_false_of_isEmpty_erase_eq_false he

@[simp, grind =]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  TreeMap.contains_erase

@[simp, grind =]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  TreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.mem_of_mem_erase

@[grind =]
theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  TreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  TreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  TreeMap.size_le_size_erase

@[simp, grind =]
theorem get?_emptyc {a : α} : (∅ : TreeSet α cmp).get? a = none :=
  TreeMap.getKey?_emptyc

theorem get?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t.get? a = none :=
  TreeMap.getKey?_of_isEmpty

@[grind =] theorem get?_insert [TransCmp cmp] {k a : α} :
    (t.insert k).get? a = if cmp k a = .eq ∧ ¬k ∈ t then some k else t.get? a :=
  TreeMap.getKey?_insertIfNew

theorem contains_eq_isSome_get? [TransCmp cmp] {a : α} :
    t.contains a = (t.get? a).isSome :=
  TreeMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] {a : α} :
    (t.get? a).isSome = t.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  TreeMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_get?_iff_mem [TransCmp cmp] {a : α} :
    (t.get? a).isSome ↔ a ∈ t :=
  mem_iff_isSome_get?.symm

theorem mem_of_get?_eq_some [TransCmp cmp] {k k' : α}
    (h : t.get? k = some k') : k' ∈ t :=
  TreeMap.mem_of_getKey?_eq_some h

theorem get?_eq_some_iff [TransCmp cmp] {k k' : α} :
    t.get? k = some k' ↔ ∃ h, t.get k h = k' :=
  TreeMap.getKey?_eq_some_iff

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.get? a = none :=
  TreeMap.getKey?_eq_none_of_contains_eq_false

theorem get?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  TreeMap.getKey?_eq_none

@[grind =] theorem get?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  TreeMap.getKey?_erase

@[simp]
theorem get?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).get? k = none :=
  TreeMap.getKey?_erase_self

theorem compare_getKey?_self [TransCmp cmp] {k : α} :
    (t.get? k).all (cmp · k = .eq) :=
  TreeMap.compare_getKey?_self

theorem get?_congr [TransCmp cmp] {k k' : α} (h' : cmp k k' = .eq) :
    t.get? k = t.get? k' :=
  TreeMap.getKey?_congr h'

theorem get?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : t.contains k) :
    t.get? k = some k :=
  TreeMap.getKey?_eq_some_of_contains h'

theorem get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.get? k = some k :=
  TreeMap.getKey?_eq_some_of_contains h'

@[grind =] theorem get_insert [TransCmp cmp] {k a : α} {h₁} :
    (t.insert k).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.get a (mem_of_mem_insert' h₁ h₂) :=
  TreeMap.getKey_insertIfNew

theorem toList_insert_perm [BEq α] [TransCmp cmp] [LawfulBEqCmp cmp] {k : α} :
    (t.insert k).toList.Perm (if k ∈ t then t.toList else k :: t.toList) :=
  DTreeMap.keys_insertIfNew_perm

@[simp, grind =] theorem get_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h') :=
  TreeMap.getKey_erase

theorem get?_eq_some_get [TransCmp cmp] {a : α} (h') :
    t.get? a = some (t.get a h') :=
  TreeMap.getKey?_eq_some_getKey h'

theorem get_eq_get_get? [TransCmp cmp] {k : α} {h} :
    t.get k h = (t.get? k).get (mem_iff_isSome_get?.mp h) :=
  TreeMap.getKey_eq_get_getKey?

@[grind =] theorem get_get? [TransCmp cmp] {k : α} {h} :
    (t.get? k).get h = t.get k (mem_iff_isSome_get?.mpr h) :=
  TreeMap.get_getKey?

theorem compare_get_self [TransCmp cmp] {k : α} (h' : k ∈ t) :
    cmp (t.get k h') k = .eq :=
  TreeMap.compare_getKey_self h'

theorem get_congr [TransCmp cmp] {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.get k₁ h₁ = t.get k₂ ((mem_congr h').mp h₁) :=
  TreeMap.getKey_congr h' h₁

@[simp, grind =]
theorem get_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.get k h' = k :=
  TreeMap.getKey_eq h'

@[simp, grind =]
theorem get!_emptyc {a : α} [Inhabited α] :
    (∅ : TreeSet α cmp).get! a = default :=
  TreeMap.getKey!_emptyc

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited α] {a : α} :
    t.isEmpty = true → t.get! a = default :=
  TreeMap.getKey!_of_isEmpty

@[grind =] theorem get!_insert [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.insert k).get! a = if cmp k a = .eq ∧ ¬ k ∈ t then k else t.get! a :=
  TreeMap.getKey!_insertIfNew

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.get! a = default :=
  TreeMap.getKey!_eq_default_of_contains_eq_false

theorem get!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.get! a = default :=
  TreeMap.getKey!_eq_default

@[grind =] theorem get!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
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

theorem get!_congr [TransCmp cmp] [Inhabited α] {k k' : α} (h' : cmp k k' = .eq) :
    t.get! k = t.get! k' :=
  TreeMap.getKey!_congr h'

theorem get!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    (h' : t.contains k) :
    t.get! k = k :=
  TreeMap.getKey!_eq_of_contains h'

theorem get!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α} (h' : k ∈ t) :
    t.get! k = k :=
  TreeMap.getKey!_eq_of_mem h'

@[simp, grind =]
theorem getD_emptyc {a : α} {fallback : α} :
    (∅ : TreeSet α cmp).getD a fallback = fallback :=
  TreeMap.getKeyD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] {a fallback : α} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  TreeMap.getKeyD_of_isEmpty

@[grind =] theorem getD_insert [TransCmp cmp] {k a fallback : α} :
    (t.insert k).getD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getD a fallback :=
  TreeMap.getKeyD_insertIfNew

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getD a fallback = fallback :=
  TreeMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  TreeMap.getKeyD_eq_fallback

@[grind =] theorem getD_erase [TransCmp cmp] {k a fallback : α} :
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

theorem getD_congr [TransCmp cmp] {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getD k fallback = t.getD k' fallback :=
  TreeMap.getKeyD_congr h'

theorem getD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : t.contains k) :
    t.getD k fallback = k :=
  TreeMap.getKeyD_eq_of_contains h'

theorem getD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : k ∈ t) :
    t.getD k fallback = k :=
  TreeMap.getKeyD_eq_of_contains h'

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  TreeMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| TreeMap.containsThenInsertIfNew_snd

@[simp, grind =]
theorem length_toList [TransCmp cmp] :
    t.toList.length = t.size :=
  TreeMap.length_keys

@[simp, grind =]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  TreeMap.isEmpty_keys

@[simp, grind =]
theorem contains_toList [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.toList.contains k = t.contains k :=
  TreeMap.contains_keys

@[simp]
theorem mem_toList [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.toList ↔ k ∈ t :=
  TreeMap.mem_keys

theorem mem_of_mem_toList [TransCmp cmp] {k : α} :
    k ∈ t.toList → k ∈ t :=
  TreeMap.mem_of_mem_keys

theorem distinct_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  TreeMap.distinct_keys

theorem ordered_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => cmp a b = .lt) :=
  TreeMap.ordered_keys

section Union

variable (t₁ t₂ : TreeSet α cmp)

variable {t₁ t₂}

@[simp]
theorem union_eq : t₁.union t₂ = t₁ ∪ t₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [TransCmp cmp] {k : α} :
    (t₁ ∪ t₂).contains k = (t₁.contains k || t₂.contains k) :=
  TreeMap.contains_union

/- mem -/
theorem mem_union_of_left [TransCmp cmp] {k : α} :
    k ∈ t₁ → k ∈ t₁ ∪ t₂ :=
  TreeMap.mem_union_of_left

theorem mem_union_of_right [TransCmp cmp] {k : α} :
    k ∈ t₂ → k ∈ t₁ ∪ t₂ :=
  TreeMap.mem_union_of_right

@[simp]
theorem mem_union_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ ↔ k ∈ t₁ ∨ k ∈ t₂ :=
  TreeMap.mem_union_iff

theorem mem_of_mem_union_of_not_mem_right [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₂ → k ∈ t₁ :=
  TreeMap.mem_of_mem_union_of_not_mem_right

theorem mem_of_mem_union_of_not_mem_left [TransCmp cmp]
    {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₁ → k ∈ t₂ :=
  TreeMap.mem_of_mem_union_of_not_mem_left

theorem Equiv.union_left {t₃ : TreeSet α cmp} [TransCmp cmp] (equiv : t₁.Equiv t₂) :
    (t₁ ∪ t₃).Equiv (t₂ ∪ t₃) :=
  ⟨TreeMap.Equiv.union_left equiv.1⟩

theorem Equiv.union_right {t₃ : TreeSet α cmp} [TransCmp cmp] (equiv : t₂.Equiv t₃) :
    (t₁ ∪ t₂).Equiv (t₁ ∪ t₃) :=
  ⟨TreeMap.Equiv.union_right equiv.1⟩

theorem Equiv.union_congr {t₃ t₄ : TreeSet α cmp} [TransCmp cmp]
    (equiv₁ : t₁.Equiv t₃) (equiv₂ : t₂.Equiv t₄) :
    (t₁ ∪ t₂).Equiv (t₃ ∪ t₄) :=
  ⟨TreeMap.Equiv.union_congr equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_union [TransCmp cmp]
    {k : α} :
    (t₁ ∪ t₂).get? k = (t₂.get? k).or (t₁.get? k) :=
  TreeMap.getKey?_union

theorem get?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get? k = t₂.get? k :=
  TreeMap.getKey?_union_of_not_mem_left not_mem

theorem get?_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).get? k = t₁.get? k :=
  TreeMap.getKey?_union_of_not_mem_right not_mem

/- get -/
theorem get_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).get k (mem_union_of_right mem) = t₂.get k mem :=
  TreeMap.getKey_union_of_mem_right mem

theorem get_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).get k h' = t₂.get k (mem_of_mem_union_of_not_mem_left h' not_mem) :=
  TreeMap.getKey_union_of_not_mem_left not_mem

theorem get_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂).get k h' = t₁.get k (mem_of_mem_union_of_not_mem_right h' not_mem) :=
  TreeMap.getKey_union_of_not_mem_right not_mem

/- getD -/
theorem getD_union [TransCmp cmp] {k fallback : α} :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k (t₁.getD k fallback) :=
  TreeMap.getKeyD_union

theorem getD_union_of_not_mem_left [TransCmp cmp] {k fallback : α} (mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k fallback :=
  TreeMap.getKeyD_union_of_not_mem_left mem

theorem getD_union_of_not_mem_right [TransCmp cmp] {k fallback : α} (mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback :=
   TreeMap.getKeyD_union_of_not_mem_right mem

/- get! -/
theorem get!_union [TransCmp cmp] [Inhabited α]
    {k : α} :
    (t₁ ∪ t₂).get! k = t₂.getD k (t₁.get! k) :=
  TreeMap.getKey!_union

theorem get!_union_of_not_mem_left [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get! k = t₂.get! k :=
  TreeMap.getKey!_union_of_not_mem_left not_mem

theorem get!_union_of_not_mem_right [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).get! k = t₁.get! k :=
  TreeMap.getKey!_union_of_not_mem_right not_mem

/- size -/
theorem size_union_of_not_mem [TransCmp cmp] : (∀ (a : α), a ∈ t₁ → ¬a ∈ t₂) →
    (t₁ ∪ t₂).size = t₁.size + t₂.size :=
  DTreeMap.size_union_of_not_mem

theorem size_left_le_size_union [TransCmp cmp] : t₁.size ≤ (t₁ ∪ t₂).size :=
  DTreeMap.size_left_le_size_union

theorem size_right_le_size_union [TransCmp cmp] : t₂.size ≤ (t₁ ∪ t₂).size :=
  DTreeMap.size_right_le_size_union

theorem size_union_le_size_add_size [TransCmp cmp] :
    (t₁ ∪ t₂).size ≤ t₁.size + t₂.size :=
  DTreeMap.size_union_le_size_add_size

/- isEmpty -/
@[simp]
theorem isEmpty_union [TransCmp cmp] :
    (t₁ ∪ t₂).isEmpty = (t₁.isEmpty && t₂.isEmpty) :=
  DTreeMap.isEmpty_union

end Union

section Inter

variable {t₁ t₂ : TreeSet α cmp}

@[simp]
theorem inter_eq : t₁.inter t₂ = t₁ ∩ t₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).contains k = (t₁.contains k && t₂.contains k) :=
  TreeMap.contains_inter

/- mem -/
@[simp]
theorem mem_inter_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ :=
  TreeMap.mem_inter_iff

theorem not_mem_inter_of_not_mem_left [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ ∩ t₂ :=
  TreeMap.not_mem_inter_of_not_mem_left not_mem

theorem not_mem_inter_of_not_mem_right [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₂) :
    k ∉ t₁ ∩ t₂ :=
  TreeMap.not_mem_inter_of_not_mem_right not_mem

/- Equiv -/
theorem Equiv.inter_left {t₃ : TreeSet α cmp} [TransCmp cmp]
    (equiv : t₁ ~m t₂) :
    (t₁ ∩ t₃).Equiv (t₂ ∩ t₃) := by
  constructor
  apply TreeMap.Equiv.inter_left equiv.1

theorem Equiv.inter_right {t₃ : TreeSet α cmp} [TransCmp cmp]
    (equiv : t₂ ~m t₃) :
    (t₁ ∩ t₂).Equiv (t₁ ∩ t₃) := by
  constructor
  apply TreeMap.Equiv.inter_right equiv.1

theorem Equiv.inter_congr {t₃ t₄ : TreeSet α cmp} [TransCmp cmp]
    (equiv₁ : t₁ ~m t₃) (equiv₂ : t₂ ~m t₄) :
    (t₁ ∩ t₂).Equiv (t₃ ∩ t₄) := by
  constructor
  apply TreeMap.Equiv.inter_congr equiv₁.1 equiv₂.1

/- get? -/
theorem get?_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).get? k =
    if k ∈ t₂ then t₁.get? k else none :=
  TreeMap.getKey?_inter

theorem get?_inter_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get? k = t₁.get? k :=
  TreeMap.getKey?_inter_of_mem_right mem

theorem get?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get? k = none :=
  TreeMap.getKey?_inter_of_not_mem_left not_mem

theorem get?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get? k = none :=
  TreeMap.getKey?_inter_of_not_mem_right not_mem

/- get -/
@[simp]
theorem get_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).get k h_mem =
    t₁.get k (mem_inter_iff.1 h_mem).1 :=
  TreeMap.getKey_inter

/- getD -/
theorem getD_inter [TransCmp cmp] {k fallback : α} :
    (t₁ ∩ t₂).getD k fallback =
    if k ∈ t₂ then t₁.getD k fallback else fallback :=
  TreeMap.getKeyD_inter

theorem getD_inter_of_mem_right [TransCmp cmp]
    {k fallback : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getD k fallback = t₁.getD k fallback :=
  TreeMap.getKeyD_inter_of_mem_right mem

theorem getD_inter_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  TreeMap.getKeyD_inter_of_not_mem_right not_mem

theorem getD_inter_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  TreeMap.getKeyD_inter_of_not_mem_left not_mem

/- get! -/
theorem get!_inter [TransCmp cmp] [Inhabited α] {k : α} :
    (t₁ ∩ t₂).get! k =
    if k ∈ t₂ then t₁.get! k else default :=
  TreeMap.getKey!_inter

theorem get!_inter_of_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get! k = t₁.get! k :=
  TreeMap.getKey!_inter_of_mem_right mem

theorem get!_inter_of_not_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get! k = default :=
  TreeMap.getKey!_inter_of_not_mem_right not_mem

theorem get!_inter_of_not_mem_left [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get! k = default :=
  TreeMap.getKey!_inter_of_not_mem_left not_mem

/- size -/
theorem size_inter_le_size_left [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₁.size :=
  TreeMap.size_inter_le_size_left

theorem size_inter_le_size_right [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₂.size :=
  TreeMap.size_inter_le_size_right

theorem size_inter_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∈ t₂) :
    (t₁ ∩ t₂).size = t₁.size :=
  TreeMap.size_inter_eq_size_left h

theorem size_inter_eq_size_right [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₂ → a ∈ t₁) :
    (t₁ ∩ t₂).size = t₂.size :=
  TreeMap.size_inter_eq_size_right h

theorem size_add_size_eq_size_union_add_size_inter [TransCmp cmp] :
    t₁.size + t₂.size = (t₁ ∪ t₂).size + (t₁ ∩ t₂).size :=
  TreeMap.size_add_size_eq_size_union_add_size_inter

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  TreeMap.isEmpty_inter_left h

@[simp]
theorem isEmpty_inter_right [TransCmp cmp] (h : t₂.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  TreeMap.isEmpty_inter_right h

theorem isEmpty_inter_iff [TransCmp cmp] :
    (t₁ ∩ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∉ t₂ :=
  TreeMap.isEmpty_inter_iff

end Inter

section
variable {m₁ m₂ : TreeSet α cmp}

theorem Equiv.beq [TransCmp cmp] (h : m₁ ~m m₂) : m₁ == m₂ :=
  TreeMap.Equiv.beq h.1

theorem equiv_of_beq [TransCmp cmp] [LawfulEqCmp cmp] (h : m₁ == m₂) : m₁ ~m m₂ :=
  ⟨TreeMap.equiv_of_beq h⟩

theorem Equiv.beq_congr [TransCmp cmp] {m₃ m₄ : TreeSet α cmp} (w₁ : m₁ ~m m₃) (w₂ : m₂ ~m m₄) : (m₁ == m₂) = (m₃ == m₄) :=
  TreeMap.Equiv.beq_congr w₁.1 w₂.1

end

section Diff

variable {t₁ t₂ : TreeSet α cmp}

@[simp]
theorem diff_eq : t₁.diff t₂ = t₁ \ t₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).contains k = (t₁.contains k && !t₂.contains k) :=
  TreeMap.contains_diff

/- mem -/
@[simp]
theorem mem_diff_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ \ t₂ ↔ k ∈ t₁ ∧ k ∉ t₂ :=
  TreeMap.mem_diff_iff

theorem not_mem_diff_of_not_mem_left [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ \ t₂ :=
  TreeMap.not_mem_diff_of_not_mem_left not_mem

theorem not_mem_diff_of_mem_right [TransCmp cmp] {k : α}
    (mem : k ∈ t₂) :
    k ∉ t₁ \ t₂ :=
  TreeMap.not_mem_diff_of_mem_right mem

/- Equiv -/
theorem Equiv.diff_left {t₃ : TreeSet α cmp} [TransCmp cmp]
    (equiv : t₁ ~m t₂) :
    (t₁ \ t₃).Equiv (t₂ \ t₃) := by
  constructor
  apply TreeMap.Equiv.diff_left equiv.1

theorem Equiv.diff_right {t₃ : TreeSet α cmp} [TransCmp cmp]
    (equiv : t₂ ~m t₃) :
    (t₁ \ t₂).Equiv (t₁ \ t₃) := by
  constructor
  apply TreeMap.Equiv.diff_right equiv.1

theorem Equiv.diff_congr {t₃ t₄ : TreeSet α cmp} [TransCmp cmp]
    (equiv₁ : t₁ ~m t₃) (equiv₂ : t₂ ~m t₄) :
    (t₁ \ t₂).Equiv (t₃ \ t₄) := by
  constructor
  apply TreeMap.Equiv.diff_congr equiv₁.1 equiv₂.1

/- get? -/
theorem get?_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).get? k =
    if k ∈ t₂ then none else t₁.get? k :=
  TreeMap.getKey?_diff

theorem get?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get? k = t₁.get? k :=
  TreeMap.getKey?_diff_of_not_mem_right not_mem

theorem get?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get? k = none :=
  TreeMap.getKey?_diff_of_not_mem_left not_mem

theorem get?_diff_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get? k = none :=
  TreeMap.getKey?_diff_of_mem_right mem

/- get -/
theorem get_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).get k h_mem =
    t₁.get k (mem_diff_iff.1 h_mem).1 :=
  TreeMap.getKey_diff

/- getD -/
theorem getD_diff [TransCmp cmp] {k fallback : α} :
    (t₁ \ t₂).getD k fallback =
    if k ∈ t₂ then fallback else t₁.getD k fallback :=
  TreeMap.getKeyD_diff

theorem getD_diff_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getD k fallback = t₁.getD k fallback :=
  TreeMap.getKeyD_diff_of_not_mem_right not_mem

theorem getD_diff_of_mem_right [TransCmp cmp]
    {k fallback : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getD k fallback = fallback :=
  TreeMap.getKeyD_diff_of_mem_right mem

theorem getD_diff_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getD k fallback = fallback :=
  TreeMap.getKeyD_diff_of_not_mem_left not_mem

/- get! -/
theorem get!_diff [TransCmp cmp] [Inhabited α] {k : α} :
    (t₁ \ t₂).get! k =
    if k ∈ t₂ then default else t₁.get! k :=
  TreeMap.getKey!_diff

theorem get!_diff_of_not_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get! k = t₁.get! k :=
  TreeMap.getKey!_diff_of_not_mem_right not_mem

theorem get!_diff_of_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get! k = default :=
  TreeMap.getKey!_diff_of_mem_right mem

theorem get!_diff_of_not_mem_left [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get! k = default :=
  TreeMap.getKey!_diff_of_not_mem_left not_mem

/- size -/
theorem size_diff_le_size_left [TransCmp cmp] :
    (t₁ \ t₂).size ≤ t₁.size :=
  TreeMap.size_diff_le_size_left

theorem size_diff_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∉ t₂) :
    (t₁ \ t₂).size = t₁.size :=
  TreeMap.size_diff_eq_size_left h

theorem size_diff_add_size_inter_eq_size_left [TransCmp cmp] :
    (t₁ \ t₂).size + (t₁ ∩ t₂).size = t₁.size :=
  TreeMap.size_diff_add_size_inter_eq_size_left

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ \ t₂).isEmpty = true :=
  TreeMap.isEmpty_diff_left h

theorem isEmpty_diff_iff [TransCmp cmp] :
    (t₁ \ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∈ t₂ :=
  TreeMap.isEmpty_diff_iff

end Diff

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM f init :=
  TreeMap.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_toList {f : δ → α → δ} {init : δ} :
    t.foldl f init = t.toList.foldl f init :=
  TreeMap.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM f init :=
  TreeMap.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_toList {f : α → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr f init :=
  TreeMap.foldr_eq_foldr_keys

@[simp, grind =]
theorem forM_eq_forM [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    t.forM f = ForM.forM t f := rfl

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t f = t.toList.forM f :=
  TreeMap.forM_eq_forM_keys

@[simp, grind =]
theorem forIn_eq_forIn [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init f := rfl

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  TreeMap.forIn_eq_forIn_keys

end monadic

@[simp, grind =]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton {k : α} :
    t.insertMany [k] = t.insert k :=
  rfl

@[grind _=_]
theorem insertMany_cons {l : List α} {k : α} :
    t.insertMany (k :: l) = (t.insert k).insertMany l :=
  ext TreeMap.insertManyIfNewUnit_cons

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List α} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (t.insertMany l).contains k = (t.contains k || l.contains k) :=
  TreeMap.contains_insertManyIfNewUnit_list

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    k ∈ insertMany t l ↔ k ∈ t ∨ l.contains k :=
  TreeMap.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany t l → k ∈ t :=
  TreeMap.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    get? (insertMany t l) k = none :=
  TreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get? (insertMany t l) k' = some k :=
  TreeMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem get?_insertMany_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} (mem : k ∈ t) :
    get? (insertMany t l) k = get? t k :=
  TreeMap.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem get_insertMany_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} {h'} (contains : k ∈ t) :
    get (insertMany t l) k h' = get t k contains :=
  TreeMap.getKey_insertManyIfNewUnit_list_of_mem contains

theorem get_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} (not_mem : ¬ k ∈ t)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get (insertMany t l) k' h' = k :=
  TreeMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    get! (insertMany t l) k = default :=
  TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get!_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get! (insertMany t l) k' = k :=
  TreeMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem get!_insertMany_list_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ t):
    get! (insertMany t l) k = get! t k :=
  TreeMap.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getD_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getD (insertMany t l) k fallback = fallback :=
  TreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getD_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getD (insertMany t l) k' fallback = k :=
  TreeMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    {l : List α} {k fallback : α} (mem : k ∈ t) :
    getD (insertMany t l) k fallback = getD t k fallback :=
  TreeMap.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertMany t l).size = t.size + l.length :=
  TreeMap.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List α} :
    t.size ≤ (insertMany t l).size :=
  TreeMap.size_le_size_insertManyIfNewUnit_list

grind_pattern size_le_size_insertMany_list => (insertMany t l).size

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List α} :
    (insertMany t l).size ≤ t.size + l.length :=
  TreeMap.size_insertManyIfNewUnit_list_le

grind_pattern size_insertMany_list_le => (insertMany t l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] {l : List α} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  TreeMap.isEmpty_insertManyIfNewUnit_list

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List α) cmp =
      (∅ : TreeSet α cmp) :=
  rfl

@[simp]
theorem ofList_singleton {k : α} :
    ofList [k] cmp = (∅ : TreeSet α cmp).insert k :=
  rfl

@[grind _=_]
theorem ofList_cons {hd : α} {tl : List α} :
    ofList (hd :: tl) cmp =
      insertMany ((∅ : TreeSet α cmp).insert hd) tl :=
  ext TreeMap.unitOfList_cons

theorem ofList_eq_insertMany_empty {l : List α} :
    ofList l cmp = insertMany (∅ : TreeSet α cmp) l :=
  match l with
  | [] => by simp
  | hd :: tl => by simp [ofList_cons, insertMany_cons]

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (ofList l cmp).contains k = l.contains k :=
  TreeMap.contains_unitOfList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ ofList l cmp ↔ l.contains k := by
  simp [← contains_iff_mem]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get? (ofList l cmp) k = none :=
  TreeMap.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get? (ofList l cmp) k' = some k :=
  TreeMap.getKey?_unitOfList_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    get (ofList l cmp) k' h' = k :=
  TreeMap.getKey_unitOfList_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get! (ofList l cmp) k = default :=
  TreeMap.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    get! (ofList l cmp) k' = k :=
  TreeMap.getKey!_unitOfList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  TreeMap.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getD (ofList l cmp) k' fallback = k :=
  TreeMap.getKeyD_unitOfList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (ofList l cmp).size = l.length :=
  TreeMap.size_unitOfList distinct

theorem size_ofList_le [TransCmp cmp] {l : List α} :
    (ofList l cmp).size ≤ l.length :=
  TreeMap.size_unitOfList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp, grind =]
theorem isEmpty_ofList [TransCmp cmp] {l : List α} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  TreeMap.isEmpty_unitOfList

section Min

@[simp, grind =]
theorem min?_emptyc :
    (∅ : TreeSet α cmp).min? = none :=
  TreeMap.minKey?_emptyc

theorem min?_of_isEmpty [TransCmp cmp] :
    (he : t.isEmpty) → t.min? = none :=
  TreeMap.minKey?_of_isEmpty

@[simp, grind =]
theorem min?_eq_none_iff [TransCmp cmp] :
    t.min? = none ↔ t.isEmpty :=
  TreeMap.minKey?_eq_none_iff

@[simp] theorem min?_toList [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α][LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.toList.min? = t.min? :=
  TreeMap.min?_keys

@[simp] theorem head?_toList [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α][LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.toList.head? = t.min? :=
  TreeMap.head?_keys

theorem min?_eq_some_iff_get?_eq_self_and_forall [TransCmp cmp] {km} :
    t.min? = some km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  TreeMap.minKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem min?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.min? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  TreeMap.minKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_min?_eq_isEmpty [TransCmp cmp] :
    t.min?.isNone = t.isEmpty :=
  TreeMap.isNone_minKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_min?_eq_not_isEmpty [TransCmp cmp] :
    t.min?.isSome = !t.isEmpty :=
  TreeMap.isSome_minKey?_eq_not_isEmpty

theorem isSome_min?_iff_isEmpty_eq_false [TransCmp cmp] :
    t.min?.isSome ↔ t.isEmpty = false :=
  TreeMap.isSome_minKey?_iff_isEmpty_eq_false

@[grind =] theorem min?_insert [TransCmp cmp] {k} :
    (t.insert k).min? =
      some (t.min?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  TreeMap.minKey?_insertIfNew

theorem isSome_min?_insert [TransCmp cmp] {k} :
    (t.insert k).min?.isSome :=
  TreeMap.isSome_minKey?_insertIfNew

theorem min_insert_of_isEmpty [TransCmp cmp] {k} (he : t.isEmpty) :
    (t.insert k).min isEmpty_insert = k :=
  TreeMap.minKey_insertIfNew_of_isEmpty he

theorem min?_insert_of_isEmpty [TransCmp cmp] {k} (he : t.isEmpty) :
    (t.insert k).min? = some k :=
  TreeMap.minKey?_insertIfNew_of_isEmpty he

theorem min!_insert_of_isEmpty [TransCmp cmp] [Inhabited α] {k} (he : t.isEmpty) :
    (t.insert k).min! = k :=
  TreeMap.minKey!_insertIfNew_of_isEmpty he

theorem minD_insert_of_isEmpty [TransCmp cmp] {k} (he : t.isEmpty) {fallback : α} :
    (t.insert k).minD fallback = k :=
  TreeMap.minKeyD_insertIfNew_of_isEmpty he

theorem min?_insert_le_min? [TransCmp cmp] {k km kmi} :
    (hkm : t.min? = some km) →
    (hkmi : (t.insert k |>.min? |>.get isSome_min?_insert) = kmi) →
    cmp kmi km |>.isLE :=
  TreeMap.minKey?_insertIfNew_le_minKey?

theorem min?_insert_le_self [TransCmp cmp] {k kmi} :
    (hkmi : (t.insert k |>.min?.get isSome_min?_insert) = kmi) →
    cmp kmi k |>.isLE :=
  TreeMap.minKey?_insertIfNew_le_self

theorem contains_min? [TransCmp cmp] {km} :
    (hkm : t.min? = some km) →
    t.contains km :=
  TreeMap.contains_minKey?

theorem isSome_min?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.min?.isSome :=
  TreeMap.isSome_minKey?_of_contains

theorem isSome_min?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.min?.isSome :=
  TreeMap.isSome_minKey?_of_mem

theorem min?_le_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.min?.get <| isSome_min?_of_contains hc) = km) →
    cmp km k |>.isLE :=
  TreeMap.minKey?_le_of_contains

theorem min?_le_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.min?.get <| isSome_min?_of_mem hc) = km) →
    cmp km k |>.isLE :=
  TreeMap.minKey?_le_of_mem

theorem le_min? [TransCmp cmp] {k} :
    (∀ k', t.min? = some k' → (cmp k k').isLE) ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  TreeMap.le_minKey?

theorem get?_min? [TransCmp cmp] {km} :
    (hkm : t.min? = some km) → t.get? km = some km :=
  TreeMap.getKey?_minKey?

theorem get_min? [TransCmp cmp] {km hc} :
    (hkm : t.min?.get (isSome_min?_of_contains hc) = km) → t.get km hc = km :=
  TreeMap.getKey_minKey?

theorem get!_min? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.min? = some km) → t.get! km = km :=
  TreeMap.getKey!_minKey?

theorem getD_min? [TransCmp cmp] {km fallback} :
    (hkm : t.min? = some km) → t.getD km fallback = km :=
  TreeMap.getKeyD_minKey?

@[simp]
theorem min?_bind_get? [TransCmp cmp] :
    t.min?.bind t.get? = t.min? :=
  TreeMap.minKey?_bind_getKey?

theorem min?_erase_eq_iff_not_compare_eq_min? [TransCmp cmp] {k} :
    (t.erase k |>.min?) = t.min? ↔
      ∀ {km}, t.min? = some km → ¬ cmp k km = .eq :=
  TreeMap.minKey?_erase_eq_iff_not_compare_eq_minKey?

theorem min?_erase_eq_of_not_compare_eq_min? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.min? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.min?) = t.min? :=
  TreeMap.minKey?_erase_eq_of_not_compare_eq_minKey?

theorem isSome_min?_of_isSome_min?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.min?.isSome) →
    t.min?.isSome :=
  TreeMap.isSome_minKey?_of_isSome_minKey?_erase

theorem min?_le_min?_erase [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.min?) = some kme) →
    (hkm : (t.min?.get <|
      isSome_min?_of_isSome_min?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  TreeMap.minKey?_le_minKey?_erase

@[grind =_] theorem min?_eq_head?_toList [TransCmp cmp] :
    t.min? = t.toList.head? :=
  TreeMap.minKey?_eq_head?_keys

theorem min_eq_get_min? [TransCmp cmp] {he} :
    t.min he = t.min?.get (isSome_min?_iff_isEmpty_eq_false.mpr he) :=
  TreeMap.minKey_eq_get_minKey?

theorem min?_eq_some_min [TransCmp cmp] {he} :
    t.min? = some (t.min he) :=
  TreeMap.minKey?_eq_some_minKey

theorem min_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.min he = km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  TreeMap.minKey_eq_iff_getKey?_eq_self_and_forall

theorem min_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.min he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  TreeMap.minKey_eq_iff_mem_and_forall

@[grind =] theorem min_insert [TransCmp cmp] {k} :
    (t.insert k).min isEmpty_insert =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  TreeMap.minKey_insertIfNew

theorem min_insert_le_min [TransCmp cmp] {k he} :
    cmp (t.insert k |>.min isEmpty_insert)
      (t.min he) |>.isLE :=
  TreeMap.minKey_insertIfNew_le_minKey

theorem min_insert_le_self [TransCmp cmp] {k} :
    cmp (t.insert k |>.min <| isEmpty_insert) k |>.isLE :=
  TreeMap.minKey_insertIfNew_le_self

@[grind =] theorem contains_min [TransCmp cmp] {he} :
    t.contains (t.min he) :=
  TreeMap.contains_minKey

theorem min_mem [TransCmp cmp] {he} :
    t.min he ∈ t :=
  TreeMap.minKey_mem

grind_pattern min_mem => t.min he ∈ t

theorem min_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp (t.min <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) k |>.isLE :=
  TreeMap.minKey_le_of_contains hc

theorem min_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp (t.min <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) k |>.isLE :=
  TreeMap.minKey_le_of_mem hc

theorem le_min [TransCmp cmp] {k he} :
    (cmp k (t.min he)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  TreeMap.le_minKey

@[simp, grind =]
theorem get?_min [TransCmp cmp] {he} :
    t.get? (t.min he) = some (t.min he) :=
  TreeMap.getKey?_minKey

@[simp, grind =]
theorem get_min [TransCmp cmp] {he hc} :
    t.get (t.min he) hc = t.min he :=
  TreeMap.getKey_minKey

@[simp, grind =]
theorem get!_min [TransCmp cmp] [Inhabited α] {he} :
    t.get! (t.min he) = t.min he :=
  TreeMap.getKey!_minKey

@[simp, grind =]
theorem getD_min [TransCmp cmp] {he fallback} :
    t.getD (t.min he) fallback = t.min he :=
  TreeMap.getKeyD_minKey

@[simp]
theorem min_erase_eq_iff_not_compare_eq_min [TransCmp cmp] {k he} :
    (t.erase k |>.min he) =
        t.min (isEmpty_eq_false_of_isEmpty_erase_eq_false he) ↔
      ¬ cmp k (t.min <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) = .eq :=
  TreeMap.minKey_erase_eq_iff_not_compare_eq_minKey

theorem min_erase_eq_of_not_compare_eq_min [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.min (isEmpty_eq_false_of_isEmpty_erase_eq_false he)) = .eq) →
    (t.erase k |>.min he) =
      t.min (isEmpty_eq_false_of_isEmpty_erase_eq_false he) :=
  TreeMap.minKey_erase_eq_of_not_compare_eq_minKey

theorem min_le_min_erase [TransCmp cmp] {k he} :
    cmp (t.min <| isEmpty_eq_false_of_isEmpty_erase_eq_false he)
      (t.erase k |>.min he) |>.isLE :=
  TreeMap.minKey_le_minKey_erase

theorem min_eq_head_toList [TransCmp cmp] {he} :
    t.min he = t.toList.head (List.isEmpty_eq_false_iff.mp <| isEmpty_toList ▸ he) :=
  TreeMap.minKey_eq_head_keys

theorem min?_eq_some_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.min? = some t.min! :=
  TreeMap.minKey?_eq_some_minKey! he

theorem min_eq_min! [TransCmp cmp] [Inhabited α] {he : t.isEmpty = false} :
    t.min he = t.min! :=
  TreeMap.minKey_eq_minKey!

theorem min!_eq_default [TransCmp cmp] [Inhabited α] (he : t.isEmpty) :
    t.min! = default :=
  TreeMap.minKey!_eq_default he

theorem min!_eq_iff_get?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.min! = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  TreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall he

theorem min!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.min! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  TreeMap.minKey!_eq_iff_mem_and_forall he

@[grind =] theorem min!_insert [TransCmp cmp] [Inhabited α] {k} :
    (t.insert k |>.min!) =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  TreeMap.minKey!_insertIfNew

theorem min!_insert_le_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    cmp (t.insert k |>.min!) t.min! |>.isLE :=
  TreeMap.minKey!_insertIfNew_le_minKey! he

theorem min!_insert_le_self [TransCmp cmp] [Inhabited α] {k} :
    cmp (t.insert k |>.min!) k |>.isLE :=
  TreeMap.minKey!_insertIfNew_le_self

@[grind =] theorem contains_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.contains t.min! :=
  TreeMap.contains_minKey! he

theorem min!_mem [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.min! ∈ t :=
  TreeMap.minKey!_mem he

grind_pattern min!_mem => t.min! ∈ t

theorem min!_le_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp t.min! k |>.isLE :=
  TreeMap.minKey!_le_of_contains hc

theorem min!_le_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp t.min! k |>.isLE :=
  TreeMap.minKey!_le_of_mem hc

theorem le_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    (cmp k t.min!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  TreeMap.le_minKey! he

theorem get?_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.get? t.min! = some t.min! :=
  TreeMap.getKey?_minKey! he

@[grind =] theorem get_min! [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.min! hc = t.min! :=
  TreeMap.getKey_minKey!

@[simp, grind =]
theorem get_min!_eq_min [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.min! hc = t.min (isEmpty_eq_false_of_contains hc) :=
  TreeMap.getKey_minKey!_eq_minKey

theorem get!_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.get! t.min! = t.min! :=
  TreeMap.getKey!_minKey! he

theorem getD_min! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getD t.min! fallback = t.min! :=
  TreeMap.getKeyD_minKey! he

theorem min!_erase_eq_of_not_compare_min!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.min! = .eq) :
    (t.erase k |>.min!) = t.min! :=
  TreeMap.minKey!_erase_eq_of_not_compare_minKey!_eq he heq

theorem min!_le_min!_erase [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) :
    cmp t.min! (t.erase k |>.min!) |>.isLE :=
  TreeMap.minKey!_le_minKey!_erase he

theorem min!_eq_head!_toList [TransCmp cmp] [Inhabited α] :
    t.min! = t.toList.head! :=
  TreeMap.minKey!_eq_head!_keys

theorem min?_eq_some_minD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.min? = some (t.minD fallback) :=
  TreeMap.minKey?_eq_some_minKeyD he

theorem minD_eq_fallback [TransCmp cmp] (he : t.isEmpty) {fallback} :
    t.minD fallback = fallback :=
  TreeMap.minKeyD_eq_fallback he

theorem min!_eq_minD_default [TransCmp cmp] [Inhabited α] :
    t.min! = t.minD default :=
  TreeMap.minKey!_eq_minKeyD_default

theorem minD_eq_iff_get?_eq_self_and_forall [TransCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.minD fallback = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  TreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall he

theorem minD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.minD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  TreeMap.minKeyD_eq_iff_mem_and_forall he

@[grind =] theorem minD_insert [TransCmp cmp] {k fallback} :
    (t.insert k |>.minD fallback) =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  TreeMap.minKeyD_insertIfNew

theorem minD_insert_le_minD [TransCmp cmp]
    (he : t.isEmpty = false) {k fallback} :
    cmp (t.insert k |>.minD fallback) (t.minD fallback) |>.isLE :=
  TreeMap.minKeyD_insertIfNew_le_minKeyD he

theorem minD_insert_le_self [TransCmp cmp] {k fallback} :
    cmp (t.insert k |>.minD fallback) k |>.isLE :=
  TreeMap.minKeyD_insertIfNew_le_self

@[grind =] theorem contains_minD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.contains (t.minD fallback) :=
  TreeMap.contains_minKeyD he

theorem minD_mem [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.minD fallback ∈ t :=
  TreeMap.minKeyD_mem he

grind_pattern minD_mem => t.minD fallback ∈ t

theorem minD_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp (t.minD fallback) k |>.isLE :=
  TreeMap.minKeyD_le_of_contains hc

theorem minD_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp (t.minD fallback) k |>.isLE :=
  TreeMap.minKeyD_le_of_mem hc

theorem le_minD [TransCmp cmp] (he : t.isEmpty = false) {k fallback} :
    (cmp k (t.minD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  TreeMap.le_minKeyD he

theorem get?_minD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.get? (t.minD fallback) = some (t.minD fallback) :=
  TreeMap.getKey?_minKeyD he

@[grind =] theorem get_minD [TransCmp cmp] {fallback hc} :
    t.get (t.minD fallback) hc = t.minD fallback :=
  TreeMap.getKey_minKeyD

theorem get!_minD [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.get! (t.minD fallback) = t.minD fallback :=
  TreeMap.getKey!_minKeyD he

theorem getD_minD [TransCmp cmp] (he : t.isEmpty = false) {fallback fallback'} :
    t.getD (t.minD fallback) fallback' = t.minD fallback :=
  TreeMap.getKeyD_minKeyD he

theorem minD_erase_eq_of_not_compare_minD_eq [TransCmp cmp] {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.minD fallback) = .eq) :
    (t.erase k |>.minD fallback) = t.minD fallback :=
  TreeMap.minKeyD_erase_eq_of_not_compare_minKeyD_eq he heq

theorem minD_le_minD_erase [TransCmp cmp] {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.minD fallback) (t.erase k |>.minD fallback) |>.isLE :=
  TreeMap.minKeyD_le_minKeyD_erase he

theorem minD_eq_headD_toList [TransCmp cmp] {fallback} :
    t.minD fallback = t.toList.headD fallback :=
  TreeMap.minKeyD_eq_headD_keys

end Min

section Max

@[simp, grind =]
theorem max?_emptyc :
    (∅ : TreeSet α cmp).max? = none :=
  TreeMap.maxKey?_emptyc

theorem max?_of_isEmpty [TransCmp cmp] :
    (he : t.isEmpty) → t.max? = none :=
  TreeMap.maxKey?_of_isEmpty

@[simp, grind =]
theorem max?_eq_none_iff [TransCmp cmp] :
    t.max? = none ↔ t.isEmpty :=
  TreeMap.maxKey?_eq_none_iff

theorem max?_eq_some_iff_get?_eq_self_and_forall [TransCmp cmp] {km} :
    t.max? = some km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  TreeMap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem max?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.max? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  TreeMap.maxKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_max?_eq_isEmpty [TransCmp cmp] :
    t.max?.isNone = t.isEmpty :=
  TreeMap.isNone_maxKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_max?_eq_not_isEmpty [TransCmp cmp] :
    t.max?.isSome = !t.isEmpty :=
  TreeMap.isSome_maxKey?_eq_not_isEmpty

theorem isSome_max?_iff_isEmpty_eq_false [TransCmp cmp] :
    t.max?.isSome ↔ t.isEmpty = false :=
  TreeMap.isSome_maxKey?_iff_isEmpty_eq_false

@[grind =] theorem max?_insert [TransCmp cmp] {k} :
    (t.insert k).max? =
      some (t.max?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  TreeMap.maxKey?_insertIfNew

theorem isSome_max?_insert [TransCmp cmp] {k} :
    (t.insert k).max?.isSome :=
  TreeMap.isSome_maxKey?_insertIfNew

theorem max?_le_max?_insert [TransCmp cmp] {k km kmi} :
    (hkm : t.max? = some km) →
    (hkmi : (t.insert k |>.max? |>.get isSome_max?_insert) = kmi) →
    cmp km kmi |>.isLE :=
  TreeMap.maxKey?_le_maxKey?_insertIfNew

theorem self_le_max?_insert [TransCmp cmp] {k kmi} :
    (hkmi : (t.insert k |>.max?.get isSome_max?_insert) = kmi) →
    cmp k kmi |>.isLE :=
  TreeMap.self_le_maxKey?_insertIfNew

theorem contains_max? [TransCmp cmp] {km} :
    (hkm : t.max? = some km) →
    t.contains km :=
  TreeMap.contains_maxKey?

theorem isSome_max?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.max?.isSome :=
  TreeMap.isSome_maxKey?_of_contains

theorem isSome_max?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.max?.isSome :=
  TreeMap.isSome_maxKey?_of_mem

theorem le_max?_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.max?.get <| isSome_max?_of_contains hc) = km) →
    cmp k km |>.isLE :=
  TreeMap.le_maxKey?_of_contains

theorem le_max?_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.max?.get <| isSome_max?_of_mem hc) = km) →
    cmp k km |>.isLE :=
  TreeMap.le_maxKey?_of_mem

theorem max?_le [TransCmp cmp] {k} :
    (∀ k', t.max? = some k' → (cmp k' k).isLE) ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  TreeMap.maxKey?_le

theorem get?_max? [TransCmp cmp] {km} :
    (hkm : t.max? = some km) → t.get? km = some km :=
  TreeMap.getKey?_maxKey?

theorem get_max? [TransCmp cmp] {km hc} :
    (hkm : t.max?.get (isSome_max?_of_contains hc) = km) → t.get km hc = km :=
  TreeMap.getKey_maxKey?

theorem get!_max? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.max? = some km) → t.get! km = km :=
  TreeMap.getKey!_maxKey?

theorem getD_max? [TransCmp cmp] {km fallback} :
    (hkm : t.max? = some km) → t.getD km fallback = km :=
  TreeMap.getKeyD_maxKey?

@[simp]
theorem max?_bind_get? [TransCmp cmp] :
    t.max?.bind t.get? = t.max? :=
  TreeMap.maxKey?_bind_getKey?

theorem max?_erase_eq_iff_not_compare_eq_max? [TransCmp cmp] {k} :
    (t.erase k |>.max?) = t.max? ↔
      ∀ {km}, t.max? = some km → ¬ cmp k km = .eq :=
  TreeMap.maxKey?_erase_eq_iff_not_compare_eq_maxKey?

theorem max?_erase_eq_of_not_compare_eq_max? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.max? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.max?) = t.max? :=
  TreeMap.maxKey?_erase_eq_of_not_compare_eq_maxKey?

theorem isSome_max?_of_isSome_max?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.max?.isSome) →
    t.max?.isSome :=
  TreeMap.isSome_maxKey?_of_isSome_maxKey?_erase

theorem max?_erase_le_max? [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.max?) = some kme) →
    (hkm : (t.max?.get <|
      isSome_max?_of_isSome_max?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  TreeMap.maxKey?_erase_le_maxKey?

theorem max?_eq_getLast?_toList [TransCmp cmp] :
    t.max? = t.toList.getLast? :=
  TreeMap.maxKey?_eq_getLast?_keys

theorem max_eq_get_max? [TransCmp cmp] {he} :
    t.max he = t.max?.get (isSome_max?_iff_isEmpty_eq_false.mpr he) :=
  TreeMap.maxKey_eq_get_maxKey?

theorem max?_eq_some_max [TransCmp cmp] {he} :
    t.max? = some (t.max he) :=
  TreeMap.maxKey?_eq_some_maxKey

theorem max_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.max he = km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  TreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall

theorem max_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.max he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  TreeMap.maxKey_eq_iff_mem_and_forall

@[grind =] theorem max_insert [TransCmp cmp] {k} :
    (t.insert k).max isEmpty_insert =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  TreeMap.maxKey_insertIfNew

theorem max_le_max_insert [TransCmp cmp] {k he} :
    cmp (t.max he)
      (t.insert k |>.max isEmpty_insert) |>.isLE :=
  TreeMap.maxKey_le_maxKey_insertIfNew

theorem self_le_max_insert [TransCmp cmp] {k} :
    cmp k (t.insert k |>.max <| isEmpty_insert) |>.isLE :=
  TreeMap.self_le_maxKey_insertIfNew

@[grind =] theorem contains_max [TransCmp cmp] {he} :
    t.contains (t.max he) :=
  TreeMap.contains_maxKey

theorem max_mem [TransCmp cmp] {he} :
    t.max he ∈ t :=
  TreeMap.maxKey_mem

grind_pattern max_mem => t.max he ∈ t

theorem le_max_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp k (t.max <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) |>.isLE :=
  TreeMap.le_maxKey_of_contains hc

theorem le_max_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp k (t.max <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) |>.isLE :=
  TreeMap.le_maxKey_of_mem hc

theorem max_le [TransCmp cmp] {k he} :
    (cmp (t.max he) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  TreeMap.maxKey_le

@[simp, grind =]
theorem get?_max [TransCmp cmp] {he} :
    t.get? (t.max he) = some (t.max he) :=
  TreeMap.getKey?_maxKey

@[simp, grind =]
theorem get_max [TransCmp cmp] {he hc} :
    t.get (t.max he) hc = t.max he :=
  TreeMap.getKey_maxKey

@[simp, grind =]
theorem get!_max [TransCmp cmp] [Inhabited α] {he} :
    t.get! (t.max he) = t.max he :=
  TreeMap.getKey!_maxKey

@[simp, grind =]
theorem getD_max [TransCmp cmp] {he fallback} :
    t.getD (t.max he) fallback = t.max he :=
  TreeMap.getKeyD_maxKey

@[simp]
theorem max_erase_eq_iff_not_compare_eq_max [TransCmp cmp] {k he} :
    (t.erase k |>.max he) =
        t.max (isEmpty_eq_false_of_isEmpty_erase_eq_false he) ↔
      ¬ cmp k (t.max <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) = .eq :=
  TreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey

theorem max_erase_eq_of_not_compare_eq_max [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.max (isEmpty_eq_false_of_isEmpty_erase_eq_false he)) = .eq) →
    (t.erase k |>.max he) =
      t.max (isEmpty_eq_false_of_isEmpty_erase_eq_false he) :=
  TreeMap.maxKey_erase_eq_of_not_compare_eq_maxKey

theorem max_erase_le_max [TransCmp cmp] {k he} :
    cmp (t.erase k |>.max he)
      (t.max <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) |>.isLE :=
  TreeMap.maxKey_erase_le_maxKey

@[grind =_]
theorem max_eq_getLast_toList [TransCmp cmp] {he} :
    t.max he = t.toList.getLast (List.isEmpty_eq_false_iff.mp <| isEmpty_toList ▸ he) :=
  TreeMap.maxKey_eq_getLast_keys

theorem max?_eq_some_max! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.max? = some t.max! :=
  TreeMap.maxKey?_eq_some_maxKey! he

theorem max_eq_max! [TransCmp cmp] [Inhabited α] {he : t.isEmpty = false} :
    t.max he = t.max! :=
  TreeMap.maxKey_eq_maxKey!

theorem max!_eq_default [TransCmp cmp] [Inhabited α] (he : t.isEmpty) :
    t.max! = default :=
  TreeMap.maxKey!_eq_default he

theorem max!_eq_iff_get?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.max! = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  TreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall he

theorem max!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.max! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  TreeMap.maxKey!_eq_iff_mem_and_forall he

@[grind =] theorem max!_insert [TransCmp cmp] [Inhabited α] {k} :
    (t.insert k |>.max!) =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  TreeMap.maxKey!_insertIfNew

theorem max!_le_max!_insert [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    cmp t.max! (t.insert k |>.max!) |>.isLE :=
  TreeMap.maxKey!_le_maxKey!_insertIfNew he

theorem self_le_max!_insert [TransCmp cmp] [Inhabited α] {k} :
    cmp k (t.insert k |>.max!) |>.isLE :=
  TreeMap.self_le_maxKey!_insertIfNew

@[grind =] theorem contains_max! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.contains t.max! :=
  TreeMap.contains_maxKey! he

theorem max!_mem [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.max! ∈ t :=
  TreeMap.maxKey!_mem he

grind_pattern max!_mem => t.max! ∈ t

theorem le_max!_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp k t.max! |>.isLE :=
  TreeMap.le_maxKey!_of_contains hc

theorem le_max!_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp k t.max! |>.isLE :=
  TreeMap.le_maxKey!_of_mem hc

theorem max!_le [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    (cmp t.max! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  TreeMap.maxKey!_le he

theorem get?_max! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.get? t.max! = some t.max! :=
  TreeMap.getKey?_maxKey! he

@[grind =] theorem get_max! [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.max! hc = t.max! :=
  TreeMap.getKey_maxKey!

@[simp, grind =]
theorem get_max!_eq_max [TransCmp cmp] [Inhabited α] {hc} :
    t.get t.max! hc = t.max (isEmpty_eq_false_of_contains hc) :=
  TreeMap.getKey_maxKey!_eq_maxKey

theorem get!_max! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.get! t.max! = t.max! :=
  TreeMap.getKey!_maxKey! he

theorem getD_max! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getD t.max! fallback = t.max! :=
  TreeMap.getKeyD_maxKey! he

theorem max!_erase_eq_of_not_compare_max!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.max! = .eq) :
    (t.erase k |>.max!) = t.max! :=
  TreeMap.maxKey!_erase_eq_of_not_compare_maxKey!_eq he heq

theorem max!_erase_le_max! [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) :
    cmp (t.erase k |>.max!) t.max! |>.isLE :=
  TreeMap.maxKey!_erase_le_maxKey! he

@[grind =_]
theorem max!_eq_getLast!_toList [TransCmp cmp] [Inhabited α] :
    t.max! = t.toList.getLast! :=
  TreeMap.maxKey!_eq_getLast!_keys

theorem max?_eq_some_maxD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.max? = some (t.maxD fallback) :=
  TreeMap.maxKey?_eq_some_maxKeyD he

theorem maxD_eq_fallback [TransCmp cmp] (he : t.isEmpty) {fallback} :
    t.maxD fallback = fallback :=
  TreeMap.maxKeyD_eq_fallback he

theorem max!_eq_maxD_default [TransCmp cmp] [Inhabited α] :
    t.max! = t.maxD default :=
  TreeMap.maxKey!_eq_maxKeyD_default

theorem maxD_eq_iff_get?_eq_self_and_forall [TransCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.maxD fallback = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  TreeMap.maxKeyD_eq_iff_getKey?_eq_self_and_forall he

theorem maxD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.maxD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  TreeMap.maxKeyD_eq_iff_mem_and_forall he

@[grind =] theorem maxD_insert [TransCmp cmp] {k fallback} :
    (t.insert k |>.maxD fallback) =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  TreeMap.maxKeyD_insertIfNew

theorem maxD_le_maxD_insert [TransCmp cmp]
    (he : t.isEmpty = false) {k fallback} :
    cmp (t.maxD fallback) (t.insert k |>.maxD fallback) |>.isLE :=
  TreeMap.maxKeyD_le_maxKeyD_insertIfNew he

theorem self_le_maxD_insert [TransCmp cmp] {k fallback} :
    cmp k (t.insert k |>.maxD fallback) |>.isLE :=
  TreeMap.self_le_maxKeyD_insertIfNew

@[grind =] theorem contains_maxD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.contains (t.maxD fallback) :=
  TreeMap.contains_maxKeyD he

theorem maxD_mem [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.maxD fallback ∈ t :=
  TreeMap.maxKeyD_mem he

grind_pattern maxD_mem => t.maxD fallback ∈ t

theorem le_maxD_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxD fallback) |>.isLE :=
  TreeMap.le_maxKeyD_of_contains hc

theorem le_maxD_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxD fallback) |>.isLE :=
  TreeMap.le_maxKeyD_of_mem hc

theorem maxD_le [TransCmp cmp] (he : t.isEmpty = false) {k fallback} :
    (cmp (t.maxD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  TreeMap.maxKeyD_le he

theorem get?_maxD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.get? (t.maxD fallback) = some (t.maxD fallback) :=
  TreeMap.getKey?_maxKeyD he

@[grind =] theorem get_maxD [TransCmp cmp] {fallback hc} :
    t.get (t.maxD fallback) hc = t.maxD fallback :=
  TreeMap.getKey_maxKeyD

theorem get!_maxD [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.get! (t.maxD fallback) = t.maxD fallback :=
  TreeMap.getKey!_maxKeyD he

theorem getD_maxD [TransCmp cmp] (he : t.isEmpty = false) {fallback fallback'} :
    t.getD (t.maxD fallback) fallback' = t.maxD fallback :=
  TreeMap.getKeyD_maxKeyD he

theorem maxD_erase_eq_of_not_compare_maxD_eq [TransCmp cmp] {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.maxD fallback) = .eq) :
    (t.erase k |>.maxD fallback) = t.maxD fallback :=
  TreeMap.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq he heq

theorem maxD_erase_le_maxD [TransCmp cmp] {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.erase k |>.maxD fallback) (t.maxD fallback) |>.isLE :=
  TreeMap.maxKeyD_erase_le_maxKeyD he

theorem maxD_eq_getLastD_toList [TransCmp cmp] {fallback} :
    t.maxD fallback = t.toList.getLastD fallback :=
  TreeMap.maxKeyD_eq_getLastD_keys

end Max

namespace Equiv

variable {t₁ t₂ t₃ t₄ : TreeSet α cmp} {δ : Type w} {m : Type w → Type w'}

@[refl, simp] theorem rfl : Equiv t t := ⟨.rfl⟩

@[symm] theorem symm : Equiv t₁ t₂ → Equiv t₂ t₁
  | ⟨h⟩ => ⟨h.symm⟩

theorem trans : Equiv t₁ t₂ → Equiv t₂ t₃ → Equiv t₁ t₃
  | ⟨h⟩, ⟨h'⟩ => ⟨h.trans h'⟩

instance instTrans : @Trans (TreeSet α cmp) _ _ Equiv Equiv Equiv := ⟨trans⟩

theorem comm : t₁ ~m t₂ ↔ t₂ ~m t₁ := ⟨symm, symm⟩
theorem congr_left (h : t₁ ~m t₂) : t₁ ~m t₃ ↔ t₂ ~m t₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : t₁ ~m t₂) : t₃ ~m t₁ ↔ t₃ ~m t₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

-- congruence lemmas

theorem isEmpty_eq (h : t₁ ~m t₂) : t₁.isEmpty = t₂.isEmpty :=
  h.1.isEmpty_eq

theorem contains_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.contains k = t₂.contains k :=
  h.1.contains_eq

theorem mem_iff [TransCmp cmp] (h : t₁ ~m t₂) {k : α} :
    k ∈ t₁ ↔ k ∈ t₂ :=
  h.1.mem_iff

theorem size_eq (h : t₁ ~m t₂) : t₁.size = t₂.size :=
  h.1.size_eq

theorem get?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.get? k = t₂.get? k :=
  h.1.getKey?_eq

theorem get_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h : t₁ ~m t₂) :
    t₁.get k hk = t₂.get k (h.mem_iff.mp hk) :=
  h.1.getKey_eq

theorem get!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.get! k = t₂.get! k :=
  h.1.getKey!_eq

theorem getD_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getD k fallback = t₂.getD k fallback :=
  h.1.getKeyD_eq

theorem toList_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.toList = t₂.toList :=
  h.1.keys_eq

theorem toArray_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.toArray = t₂.toArray :=
  h.1.keysArray_eq

theorem foldlM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ}
    (h : t₁ ~m t₂) : t₁.foldlM f init = t₂.foldlM f init :=
  h.1.foldlM_eq

theorem foldl_eq [TransCmp cmp] {f : δ → α → δ} {init : δ} (h : t₁ ~m t₂) :
    t₁.foldl f init = t₂.foldl f init :=
  h.1.foldl_eq

theorem foldrM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ}
    (h : t₁ ~m t₂) :
    t₁.foldrM f init = t₂.foldrM f init :=
  h.1.foldrM_eq

theorem foldr_eq [TransCmp cmp] {f : α → δ → δ} {init : δ} (h : t₁ ~m t₂) :
    t₁.foldr f init = t₂.foldr f init :=
  h.1.foldr_eq

theorem forIn_eq [TransCmp cmp] [Monad m] [LawfulMonad m]
    {b : δ} {f : α → δ → m (ForInStep δ)} (h : t₁ ~m t₂) :
    ForIn.forIn t₁ b f = ForIn.forIn t₂ b f :=
  h.1.forIn_eq (f := fun x => f x.1)

theorem forM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → m PUnit} (h : t₁ ~m t₂) :
    ForM.forM t₁ f = ForM.forM t₂ f :=
  h.1.forM_eq (f := fun x => f x.1)

theorem any_eq [TransCmp cmp] {p : α → Bool} (h : t₁ ~m t₂) : t₁.any p = t₂.any p :=
  h.1.any_eq

theorem all_eq [TransCmp cmp] {p : α → Bool} (h : t₁ ~m t₂) : t₁.all p = t₂.all p :=
  h.1.all_eq

theorem min?_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.min? = t₂.min? :=
  h.1.minKey?_eq

theorem min_eq [TransCmp cmp] {h' : t₁.isEmpty = false} (h : t₁ ~m t₂) :
    t₁.min h' = t₂.min (h.isEmpty_eq.symm.trans h') :=
  h.1.minKey_eq

theorem min!_eq [TransCmp cmp] [Inhabited α] (h : t₁ ~m t₂) :
    t₁.min! = t₂.min! :=
  h.1.minKey!_eq

theorem minD_eq [TransCmp cmp] {fallback : α} (h : t₁ ~m t₂) :
    t₁.minD fallback = t₂.minD fallback :=
  h.1.minKeyD_eq

theorem max?_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.max? = t₂.max? :=
  h.1.maxKey?_eq

theorem max_eq [TransCmp cmp] {h' : t₁.isEmpty = false} (h : t₁ ~m t₂) :
    t₁.max h' = t₂.max (h.isEmpty_eq.symm.trans h') :=
  h.1.maxKey_eq

theorem max!_eq [TransCmp cmp] [Inhabited α] (h : t₁ ~m t₂) :
    t₁.max! = t₂.max! :=
  h.1.maxKey!_eq

theorem maxD_eq [TransCmp cmp] {fallback : α} (h : t₁ ~m t₂) :
    t₁.maxD fallback = t₂.maxD fallback :=
  h.1.maxKeyD_eq

theorem atIdx?_eq [TransCmp cmp] {i : Nat} (h : t₁ ~m t₂) :
    t₁.atIdx? i = t₂.atIdx? i :=
  h.1.keyAtIdx?_eq

theorem atIdx_eq [TransCmp cmp] {i : Nat} {h' : i < t₁.size} (h : t₁ ~m t₂) :
    t₁.atIdx i h' = t₂.atIdx i (h.size_eq ▸ h') :=
  h.1.keyAtIdx_eq

theorem atIdx!_eq [TransCmp cmp] [Inhabited α] {i : Nat} (h : t₁ ~m t₂) :
    t₁.atIdx! i = t₂.atIdx! i :=
  h.1.keyAtIdx!_eq

theorem atIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α} (h : t₁ ~m t₂) :
    t₁.atIdxD i fallback = t₂.atIdxD i fallback :=
  h.1.keyAtIdxD_eq

theorem getGE?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getGE? k = t₂.getGE? k :=
  h.1.getKeyGE?_eq

theorem getGE_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getGE k h' = t₂.getGE k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyGE_eq

theorem getGE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getGE! k = t₂.getGE! k :=
  h.1.getKeyGE!_eq

theorem getGED_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getGED k fallback = t₂.getGED k fallback :=
  h.1.getKeyGED_eq

theorem getGT?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getGT? k = t₂.getGT? k :=
  h.1.getKeyGT?_eq

theorem getGT_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getGT k h' = t₂.getGT k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyGT_eq

theorem getGT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getGT! k = t₂.getGT! k :=
  h.1.getKeyGT!_eq

theorem getGTD_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getGTD k fallback = t₂.getGTD k fallback :=
  h.1.getKeyGTD_eq

theorem getLE?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getLE? k = t₂.getLE? k :=
  h.1.getKeyLE?_eq

theorem getLE_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getLE k h' = t₂.getLE k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyLE_eq

theorem getLE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getLE! k = t₂.getLE! k :=
  h.1.getKeyLE!_eq

theorem getLED_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getLED k fallback = t₂.getLED k fallback :=
  h.1.getKeyLED_eq

theorem getLT?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getLT? k = t₂.getLT? k :=
  h.1.getKeyLT?_eq

theorem getLT_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getLT k h' = t₂.getLT k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyLT_eq

theorem getLT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getLT! k = t₂.getLT! k :=
  h.1.getKeyLT!_eq

theorem getLTD_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getLTD k fallback = t₂.getLTD k fallback :=
  h.1.getKeyLTD_eq

theorem insert [TransCmp cmp] (h : t₁ ~m t₂) (k : α) : t₁.insert k ~m t₂.insert k :=
  ⟨h.1.insertIfNew k ()⟩

theorem erase [TransCmp cmp] (h : t₁ ~m t₂) (k : α) : t₁.erase k ~m t₂.erase k :=
  ⟨h.1.erase k⟩

theorem filter (h : t₁ ~m t₂) (f : α → Bool) : t₁.filter f ~m t₂.filter f :=
  ⟨h.1.filter _⟩

theorem insertMany_list [TransCmp cmp] (h : t₁ ~m t₂) (l : List α) :
    t₁.insertMany l ~m t₂.insertMany l :=
  ⟨h.1.insertManyIfNewUnit_list l⟩

theorem eraseMany_list [TransCmp cmp] (h : t₁ ~m t₂) (l : List α) :
    t₁.eraseMany l ~m t₂.eraseMany l :=
  ⟨h.1.eraseMany_list l⟩

theorem merge [TransCmp cmp] [LawfulEqCmp cmp]
    (h : t₁ ~m t₂) (h' : t₃ ~m t₄) : t₁.merge t₃ ~m t₂.merge t₄ :=
  ⟨h.1.mergeWith _ h'.1⟩

-- extensionalities

theorem of_forall_get?_eq [TransCmp cmp] (h : ∀ k, t₁.get? k = t₂.get? k) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey?_unit_eq h⟩

theorem of_forall_contains_eq [TransCmp cmp] [LawfulEqCmp cmp]
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ ~m t₂ :=
  ⟨.of_forall_contains_unit_eq h⟩

theorem of_forall_mem_iff [TransCmp cmp] [LawfulEqCmp cmp]
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ ~m t₂ :=
  ⟨.of_forall_mem_unit_iff h⟩

end Equiv

section Equiv

variable {t₁ t₂ : TreeSet α cmp}

private theorem equiv_iff_equiv : t₁ ~m t₂ ↔ t₁.1.Equiv t₂.1 :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem equiv_empty_iff_isEmpty : t ~m empty ↔ t.isEmpty :=
  equiv_iff_equiv.trans TreeMap.equiv_empty_iff_isEmpty

theorem empty_equiv_iff_isEmpty : empty ~m t ↔ t.isEmpty :=
  Equiv.comm.trans equiv_empty_iff_isEmpty

theorem equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList :=
  equiv_iff_equiv.trans TreeMap.equiv_iff_keys_unit_perm

theorem Equiv.of_toList_perm (h : t₁.toList.Perm t₂.toList) : t₁ ~m t₂ :=
  ⟨.of_keys_unit_perm h⟩

theorem equiv_iff_toList_eq [TransCmp cmp] :
    t₁ ~m t₂ ↔ t₁.toList = t₂.toList :=
  equiv_iff_equiv.trans TreeMap.equiv_iff_keys_unit_eq

end Equiv

section filter

variable {t : TreeSet α cmp}

theorem toList_filter {f : α → Bool} :
    (t.filter f).toList = t.toList.filter f :=
  TreeMap.keys_filter_key

@[grind =] theorem isEmpty_filter_iff [TransCmp cmp]
    {f : α → Bool} :
    (t.filter f).isEmpty ↔ ∀ k h, f (t.get k h) = false :=
  TreeMap.isEmpty_filter_iff

theorem isEmpty_filter_eq_false_iff [TransCmp cmp]
    {f : α → Bool} :
    (t.filter f).isEmpty = false ↔ ∃ k h, f (t.get k h) :=
  TreeMap.isEmpty_filter_eq_false_iff

-- TODO: `contains_filter` is missing.

@[simp, grind =]
theorem mem_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    k ∈ t.filter f ↔ ∃ h, f (t.get k h) :=
  TreeMap.mem_filter

theorem contains_of_contains_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    (t.filter f).contains k → t.contains k :=
  TreeMap.contains_of_contains_filter

theorem mem_of_mem_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    k ∈ t.filter f → k ∈ t :=
  TreeMap.mem_of_mem_filter

theorem size_filter_le_size [TransCmp cmp]
    {f : α → Bool} :
    (t.filter f).size ≤ t.size :=
  TreeMap.size_filter_le_size

grind_pattern size_filter_le_size => (t.filter f).size

theorem size_filter_eq_size_iff [TransCmp cmp]
    {f : α → Bool} :
    (t.filter f).size = t.size ↔ ∀ k h, f (t.get k h) :=
  TreeMap.size_filter_eq_size_iff

theorem filter_equiv_self_iff [TransCmp cmp]
    {f : α → Bool} :
    t.filter f ~m t ↔ ∀ k h, f (t.get k h) :=
  ⟨fun h => TreeMap.filter_equiv_self_iff.mp h.1,
    fun h => ⟨TreeMap.filter_equiv_self_iff.mpr h⟩⟩

@[simp, grind =]
theorem get?_filter [TransCmp cmp]
    {f : α → Bool} {k : α} :
    (t.filter f).get? k = (t.get? k).filter f :=
  TreeMap.getKey?_filter_key

@[simp, grind =]
theorem get_filter [TransCmp cmp]
    {f : α → Bool} {k : α} {h} :
    (t.filter f).get k h = t.get k (mem_of_mem_filter h) :=
  TreeMap.getKey_filter

@[grind =]
theorem get!_filter [TransCmp cmp] [Inhabited α]
    {f : α → Bool} {k : α} :
    (t.filter f).get! k = ((t.get? k).filter f).get! :=
  TreeMap.getKey!_filter_key

@[grind =]
theorem getD_filter [TransCmp cmp]
    {f : α → Bool} {k fallback : α} :
    (t.filter f).getD k fallback = ((t.get? k).filter f).getD fallback :=
  TreeMap.getKeyD_filter_key

end filter

end Std.TreeSet
