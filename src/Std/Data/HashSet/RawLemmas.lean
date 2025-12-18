/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Std.Data.HashMap.RawLemmas
public import Std.Data.HashSet.Raw

@[expose] public section

/-!
# Hash set lemmas

This module contains lemmas about `Std.Data.HashSet.Raw`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u}

namespace Std.HashSet

namespace Raw

variable {m : Raw α}

private theorem ext {m m' : Raw α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp, grind =]
theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α).size = 0 :=
  HashMap.Raw.size_emptyWithCapacity

@[simp, grind =]
theorem size_empty : (∅ : Raw α).size = 0 :=
  HashMap.Raw.size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.Raw.isEmpty_eq_size_eq_zero

@[simp]
theorem toList_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α).toList = [] :=
  HashMap.Raw.keys_emptyWithCapacity

@[simp]
theorem toList_empty : (∅ : Raw α).toList = [] :=
  toList_emptyWithCapacity

variable [BEq α] [Hashable α]

@[simp, grind =]
theorem isEmpty_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_emptyWithCapacity

@[simp, grind =]
theorem isEmpty_empty : (∅ : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_empty

@[simp, grind =]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.insert a).isEmpty = false :=
  HashMap.Raw.isEmpty_insertIfNew h.out

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.Raw.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m :=
  HashMap.Raw.contains_iff_mem

-- The following lemma becomes a simp lemma at the bottom of the file.
theorem contains_eq_false_iff_not_mem {k : α} : m.contains k = false ↔ ¬k ∈ m :=
  HashMap.Raw.contains_eq_false_iff_not_mem

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  HashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m :=
  HashMap.Raw.mem_congr h.out hab

@[simp, grind =] theorem contains_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : Raw α).contains a = false :=
  HashMap.Raw.contains_emptyWithCapacity

@[simp, grind ←] theorem not_mem_emptyWithCapacity {a : α} {c} : ¬a ∈ (emptyWithCapacity c : Raw α) :=
  HashMap.Raw.not_mem_emptyWithCapacity

@[simp, grind =] theorem contains_empty {a : α} : (∅ : Raw α).contains a = false :=
  HashMap.Raw.contains_empty

@[simp] theorem not_mem_empty {a : α} : ¬a ∈ (∅ : Raw α) :=
  HashMap.Raw.not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty → m.contains a = false :=
  HashMap.Raw.contains_of_isEmpty h.out

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty → ¬a ∈ m :=
  HashMap.Raw.not_mem_of_isEmpty h.out

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = false ↔ ∃ a, m.contains a = true :=
  HashMap.Raw.isEmpty_eq_false_iff_exists_contains_eq_true h.out

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = false ↔ ∃ a, a ∈ m :=
  HashMap.Raw.isEmpty_eq_false_iff_exists_mem h.out

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = true ↔ ∀ a, m.contains a = false :=
  HashMap.Raw.isEmpty_iff_forall_contains h.out

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m :=
  HashMap.Raw.isEmpty_iff_forall_not_mem h.out

@[simp] theorem insert_eq_insert {a : α} : Insert.insert a m = m.insert a := rfl

@[simp] theorem singleton_eq_insert {a : α} : Singleton.singleton a = (∅ : Raw α).insert a := rfl

@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).contains a = (k == a || m.contains a) :=
  HashMap.Raw.contains_insertIfNew h.out

@[simp, grind =]
theorem mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.insert k ↔ k == a ∨ a ∈ m :=
  HashMap.Raw.mem_insertIfNew h.out

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).contains a → (k == a) = false → m.contains a :=
  HashMap.Raw.contains_of_contains_insertIfNew h.out

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.insert k → (k == a) = false → a ∈ m :=
  HashMap.Raw.mem_of_mem_insertIfNew h.out

/-- This is a restatement of `contains_insert` that is written to exactly match the proof
obligation in the statement of `get_insert`. -/
theorem contains_of_contains_insert' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  HashMap.Raw.contains_of_contains_insertIfNew' h.out

/-- This is a restatement of `mem_insert` that is written to exactly match the proof obligation
in the statement of `get_insert`. -/
theorem mem_of_mem_insert' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.insert k → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  HashMap.Raw.mem_of_mem_insertIfNew' h.out

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).contains k :=
  HashMap.Raw.contains_insertIfNew_self h.out

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} : k ∈ m.insert k :=
  HashMap.Raw.mem_insertIfNew_self h.out

theorem mem_of_get_eq {k v : α} {w} (_ : m.get k w = v) : k ∈ m := w

@[grind =] theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).size = if k ∈ m then m.size else m.size + 1 :=
  HashMap.Raw.size_insertIfNew h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.insert k).size :=
  HashMap.Raw.size_le_size_insertIfNew h.out

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).size ≤ m.size + 1 :=
  HashMap.Raw.size_insertIfNew_le h.out

@[simp, grind =]
theorem erase_emptyWithCapacity {k : α} {c : Nat} : (emptyWithCapacity c : Raw α).erase k = emptyWithCapacity c :=
  ext HashMap.Raw.erase_emptyWithCapacity

@[simp, grind =]
theorem erase_empty {k : α} : (∅ : Raw α).erase k = ∅ :=
  ext HashMap.Raw.erase_empty

@[simp, grind =]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.Raw.isEmpty_erase h.out

@[simp, grind =]
theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  HashMap.Raw.contains_erase h.out

@[simp, grind =]
theorem mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  HashMap.Raw.mem_erase h.out

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a → m.contains a :=
  HashMap.Raw.contains_of_contains_erase h.out

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k → a ∈ m :=
  HashMap.Raw.mem_of_mem_erase h.out

@[grind =]
theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  HashMap.Raw.size_erase h.out

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size ≤ m.size :=
  HashMap.Raw.size_erase_le h.out

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  HashMap.Raw.size_le_size_erase h.out

@[simp, grind =]
theorem get?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : Raw α).get? a = none :=
  HashMap.Raw.getKey?_emptyWithCapacity

@[simp, grind =]
theorem get?_empty {a : α} : (∅ : Raw α).get? a = none :=
  HashMap.Raw.getKey?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.get? a = none :=
  HashMap.Raw.getKey?_of_isEmpty h.out

@[grind =] theorem get?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).get? a = if k == a ∧ ¬k ∈ m then some k else m.get? a :=
  HashMap.Raw.getKey?_insertIfNew h.out

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (m.get? a).isSome :=
  HashMap.Raw.contains_eq_isSome_getKey? h.out

@[simp, grind =]
theorem isSome_get?_eq_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.get? a).isSome = m.contains a :=
  (contains_eq_isSome_get? h).symm

theorem mem_iff_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    a ∈ m ↔ (m.get? a).isSome :=
  HashMap.Raw.mem_iff_isSome_getKey? h.out

@[simp]
theorem isSome_get?_iff_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.get? a).isSome ↔ a ∈ m :=
  (mem_iff_isSome_get? h).symm

theorem get?_eq_some_iff [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} :
    m.get? k = some k' ↔ ∃ h : k ∈ m, m.get k h = k' :=
  HashMap.Raw.getKey?_eq_some_iff h.out

theorem mem_of_get?_eq_some [EquivBEq α] [LawfulHashable α] (h : m.WF) {a a' : α} :
    m.get? a = some a' → a' ∈ m :=
  HashMap.Raw.mem_of_getKey?_eq_some h.out

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.get? a = none :=
  HashMap.Raw.getKey?_eq_none_of_contains_eq_false h.out

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.get? a = none :=
  HashMap.Raw.getKey?_eq_none h.out

@[grind =] theorem get?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  HashMap.Raw.getKey?_erase h.out

theorem get?_beq [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.get? k).all (· == k) :=
  HashMap.Raw.getKey?_beq h.out

theorem get?_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} (h' : k == k') :
    m.get? k = m.get? k' :=
  HashMap.Raw.getKey?_congr h.out h'

theorem get?_eq_some_of_contains [LawfulBEq α] (h : m.WF) {k : α} (h' : m.contains k) :
    m.get? k = some k :=
  HashMap.Raw.getKey?_eq_some_of_contains h.out h'

theorem get?_eq_some [LawfulBEq α] (h : m.WF) {k : α} (h' : k ∈ m) :
    m.get? k = some k :=
  HashMap.Raw.getKey?_eq_some h.out h'

@[grind =] theorem get_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h₁} :
    (m.insert k).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.get a (mem_of_mem_insert' h h₁ h₂) :=
  HashMap.Raw.getKey_insertIfNew (h₁ := h₁) h.out

theorem toList_insert_perm [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).toList.Perm (if k ∈ m then m.toList else k :: m.toList) :=
  HashMap.Raw.keys_insertIfNew_perm (v := ()) h.out

@[simp, grind =]
theorem get_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h h') :=
  HashMap.Raw.getKey_erase (h' := h') h.out

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} (h' : a ∈ m) :
    m.get? a = some (m.get a h') :=
  HashMap.Raw.getKey?_eq_some_getKey h.out h'

theorem get_eq_get_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {h'} :
    m.get k h' = (m.get? k).get ((mem_iff_isSome_get? h).mp h') :=
  HashMap.Raw.getKey_eq_get_getKey? h.out

@[grind =] theorem get_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {h'} :
    (m.get? k).get h' = m.get k ((mem_iff_isSome_get? h).mpr h') :=
  HashMap.Raw.get_getKey? h.out

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).get? k = none :=
  HashMap.Raw.getKey?_erase_self h.out

theorem get_beq [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} (h' : k ∈ m) :
    m.get k h' == k :=
  HashMap.Raw.getKey_beq h.out h'

theorem get_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k₁ k₂ : α}
    (h' : k₁ == k₂) (h₁ : k₁ ∈ m) :
    m.get k₁ h₁ = m.get k₂ (((mem_congr h h').mp h₁)) :=
  HashMap.Raw.getKey_congr h.out h' h₁

@[simp, grind =]
theorem get_eq [LawfulBEq α] (h : m.WF) {k : α} (h' : m.contains k) :
    m.get k h' = k :=
  HashMap.Raw.getKey_eq h.out h'

@[simp, grind =]
theorem get!_emptyWithCapacity [Inhabited α] {a : α} {c} : (emptyWithCapacity c : Raw α).get! a = default :=
  HashMap.Raw.getKey!_emptyWithCapacity

@[simp, grind =]
theorem get!_empty [Inhabited α] {a : α} : (∅ : Raw α).get! a = default :=
  HashMap.Raw.getKey!_empty

theorem get!_of_isEmpty [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.get! a = default :=
  HashMap.Raw.getKey!_of_isEmpty h.out

@[grind =] theorem get!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).get! a = if k == a ∧ ¬k ∈ m then k else m.get! a :=
  HashMap.Raw.getKey!_insertIfNew h.out

theorem get!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {a : α} :
    m.contains a = false → m.get! a = default :=
  HashMap.Raw.getKey!_eq_default_of_contains_eq_false h.out

theorem get!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.get! a = default :=
  HashMap.Raw.getKey!_eq_default h.out

@[grind =] theorem get!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).get! a = if k == a then default else m.get! a :=
  HashMap.Raw.getKey!_erase h.out

@[simp]
theorem get!_erase_self [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).get! k = default :=
  HashMap.Raw.getKey!_erase_self h.out

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {a : α} : m.contains a = true → m.get? a = some (m.get! a) :=
  HashMap.Raw.getKey?_eq_some_getKey!_of_contains h.out

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    a ∈ m → m.get? a = some (m.get! a) :=
  HashMap.Raw.getKey?_eq_some_getKey! h.out

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.get! a = (m.get? a).get! :=
  HashMap.Raw.getKey!_eq_get!_getKey? h.out

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} {h'} :
    m.get a h' = m.get! a :=
  HashMap.Raw.getKey_eq_getKey! h.out

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k k' : α}
    (h' : k == k') : m.get! k = m.get! k' :=
  HashMap.Raw.getKey!_congr h.out h'

theorem get!_eq_of_contains [LawfulBEq α] [Inhabited α] (h : m.WF) {k : α} (h' : m.contains k) :
    m.get! k = k :=
  HashMap.Raw.getKey!_eq_of_contains h.out h'

theorem get!_eq_of_mem [LawfulBEq α] [Inhabited α] (h : m.WF) {k : α} (h' : k ∈ m) : m.get! k = k :=
  HashMap.Raw.getKey!_eq_of_mem h.out h'

@[simp, grind =]
theorem getD_emptyWithCapacity {a fallback : α} {c} : (emptyWithCapacity c : Raw α).getD a fallback = fallback :=
  HashMap.Raw.getKeyD_emptyWithCapacity

@[simp, grind =]
theorem getD_empty {a fallback : α} : (∅ : Raw α).getD a fallback = fallback :=
  HashMap.Raw.getKeyD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  HashMap.Raw.getKeyD_of_isEmpty h.out

@[grind =] theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.insert k).getD a fallback = if k == a ∧ ¬k ∈ m then k else m.getD a fallback :=
  HashMap.Raw.getKeyD_insertIfNew h.out

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} :
    m.contains a = false → m.getD a fallback = fallback :=
  HashMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h.out

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  HashMap.Raw.getKeyD_eq_fallback h.out

@[grind =] theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  HashMap.Raw.getKeyD_erase h.out

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k fallback : α} :
    (m.erase k).getD k fallback = fallback :=
  HashMap.Raw.getKeyD_erase_self h.out

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α}
    {fallback : α} : m.contains a = true → m.get? a = some (m.getD a fallback) :=
  HashMap.Raw.getKey?_eq_some_getKeyD_of_contains h.out

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : α} :
    a ∈ m → m.get? a = some (m.getD a fallback) :=
  HashMap.Raw.getKey?_eq_some_getKeyD h.out

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : α} :
    m.getD a fallback = (m.get? a).getD fallback :=
  HashMap.Raw.getKeyD_eq_getD_getKey? h.out

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : α} {h'} :
    m.get a h' = m.getD a fallback :=
  @HashMap.Raw.getKey_eq_getKeyD _ _ _ _ _ _ _ h.out _ _ h'

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {a : α} :
    m.get! a = m.getD a default :=
  HashMap.Raw.getKey!_eq_getKeyD_default h.out

theorem getD_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' fallback : α}
    (h' : k == k') : m.getD k fallback = m.getD k' fallback :=
  HashMap.Raw.getKeyD_congr h.out h'

theorem getD_eq_of_contains [LawfulBEq α] (h : m.WF) {k fallback : α} (h' : m.contains k) :
    m.getD k fallback = k :=
  HashMap.Raw.getKeyD_eq_of_contains h.out h'

theorem getD_eq_of_mem [LawfulBEq α] (h : m.WF) {k fallback : α} (h' : k ∈ m) :
    m.getD k fallback = k :=
  HashMap.Raw.getKeyD_eq_of_mem h.out h'

@[simp, grind =]
theorem containsThenInsert_fst (h : m.WF) {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.Raw.containsThenInsertIfNew_fst h.out

@[simp, grind =]
theorem containsThenInsert_snd (h : m.WF) {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext (HashMap.Raw.containsThenInsertIfNew_snd h.out)

@[simp, grind =]
theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.length = m.size :=
  HashMap.Raw.length_keys h.1

@[simp, grind =]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.isEmpty = m.isEmpty :=
  HashMap.Raw.isEmpty_keys h.1

@[simp, grind =]
theorem contains_toList [EquivBEq α] [LawfulHashable α] {k : α} (h : m.WF) :
    m.toList.contains k = m.contains k :=
  HashMap.Raw.contains_keys h.1

@[simp, grind =]
theorem mem_toList [LawfulBEq α] (h : m.WF) {k : α} :
    k ∈ m.toList ↔ k ∈ m :=
  HashMap.Raw.mem_keys h.1

theorem mem_of_mem_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    k ∈ m.toList → k ∈ m :=
  HashMap.Raw.mem_of_mem_keys h.1

theorem distinct_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.Pairwise (fun a b => (a == b) = false) :=
  HashMap.Raw.distinct_keys h.1

@[simp]
theorem toArray_toList (h : m.WF) :
    m.toList.toArray = m.toArray :=
  HashMap.Raw.toArray_keys h.out

@[simp]
theorem toList_toArray (h : m.WF) :
    m.toArray.toList = m.toList :=
  HashMap.Raw.toList_keysArray h.out

@[simp]
theorem size_toArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toArray.size = m.size :=
  HashMap.Raw.size_keysArray h.out

@[simp]
theorem isEmpty_toArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toArray.isEmpty = m.isEmpty :=
  HashMap.Raw.isEmpty_keysArray h.out

@[simp]
theorem contains_toArray [EquivBEq α] [LawfulHashable α]
    {k : α} (h : m.WF) :
    m.toArray.contains k = m.contains k :=
  HashMap.Raw.contains_keysArray h.out

@[simp]
theorem mem_toArray [LawfulBEq α] {k : α} (h : m.WF) :
    k ∈ m.toArray ↔ k ∈ m :=
  HashMap.Raw.mem_keysArray h.out

theorem forall_mem_toArray_iff_forall_mem_get [EquivBEq α] [LawfulHashable α]
    {p : α → Prop} (h : m.WF) :
    (∀ k ∈ m.toArray, p k) ↔ ∀ (k : α) (h : k ∈ m), p (m.get k h) :=
  HashMap.Raw.forall_mem_keysArray_iff_forall_mem_getKey h.out

theorem contains_of_mem_toArray [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α}
    (h' : k ∈ m.toArray) : m.contains k :=
  HashMap.Raw.contains_of_mem_keysArray h.out h'

section monadic

variable {m : Raw α} {δ : Type v} {m' : Type v → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → α → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM f init :=
  HashMap.Raw.foldM_eq_foldlM_keys h.out

theorem fold_eq_foldl_toList (h : m.WF) {f : δ → α → δ} {init : δ} :
    m.fold f init = m.toList.foldl f init :=
  HashMap.Raw.fold_eq_foldl_keys h.out

omit [BEq α] [Hashable α] in
@[simp, grind =]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.forM f = ForM.forM m f := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] (h : m.WF) {f : α → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  HashMap.Raw.forM_eq_forM_keys h.out

omit [BEq α] [Hashable α] in
@[simp, grind =]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn m init f := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  HashMap.Raw.forIn_eq_forIn_keys h.out

theorem foldM_eq_foldlM_toArray [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} (h : m.WF) :
    m.foldM (fun d a => f d a) init = m.toArray.foldlM f init :=
  HashMap.Raw.foldM_eq_foldlM_keysArray h.out

theorem fold_eq_foldl_toArray {f : δ → α → δ} {init : δ} (h : m.WF) :
    m.fold (fun d a => f d a) init = m.toArray.foldl f init :=
  HashMap.Raw.fold_eq_foldl_keysArray h.out

theorem forM_eq_forM_toArray [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} (h : m.WF) :
    m.forM (fun a => f a) = m.toArray.forM f :=
  HashMap.Raw.forM_eq_forM_keysArray h.out

theorem forIn_eq_forIn_toArray [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} (h : m.WF) :
    m.forIn (fun a d => f a d) init = ForIn.forIn m.toArray init f :=
  HashMap.Raw.forIn_eq_forIn_keysArray h.out

end monadic


theorem all_eq_not_any_not {p : α → Bool} (h : m.WF) :
    m.all p = ! m.any (fun a => ! p a) := HashMap.Raw.all_eq_not_any_not h.out

theorem any_eq_not_all_not {p : α → Bool} (h : m.WF) :
    m.any p = ! m.all (fun a => ! p a) := HashMap.Raw.any_eq_not_all_not h.out

@[simp]
theorem any_toList [LawfulHashable α] [EquivBEq α] {p : α → Bool} (h : m.WF) :
    m.toList.any p = m.any p :=
  HashMap.Raw.any_keys h.out

theorem any_eq_true_iff_exists_mem_get [LawfulHashable α] [EquivBEq α]
    {p : α → Bool} (h : m.WF) :
    m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p (m.get a h) :=
  HashMap.Raw.any_eq_true_iff_exists_mem_getKey_getElem h.out

theorem any_eq_true_iff_exists_mem [LawfulBEq α] {p : α → Bool} (h : m.WF) :
    m.any p = true ↔ ∃ (a : α), a ∈ m ∧ p a := by
  simpa using @HashMap.Raw.any_eq_true_iff_exists_mem_getElem _ _ _ _ _ _ (fun a b => p a) h.out

theorem any_eq_false_iff_forall_mem_get [LawfulHashable α] [EquivBEq α]
    {p : α → Bool} (h : m.WF) :
    m.any p = false ↔
      ∀ (a : α) (h : a ∈ m), p (m.get a h) = false :=
  HashMap.Raw.any_eq_false_iff_forall_mem_getKey_getElem h.out

theorem any_eq_false_iff_forall_mem [LawfulBEq α] {p : α → Bool} (h : m.WF) :
    m.any p = false ↔
      ∀ (a : α), a ∈ m → p a = false := by
  simpa using @HashMap.Raw.any_eq_false_iff_forall_mem_getElem _ _ _ _ _ _ (fun a b => p a) h.out

@[simp]
theorem all_toList [LawfulHashable α] [EquivBEq α] {p : α → Bool} (h : m.WF) :
    m.toList.all p = m.all p :=
  HashMap.Raw.all_keys h.out

theorem all_eq_true_iff_forall_mem_get [EquivBEq α] [LawfulHashable α]
    {p : α → Bool} (h : m.WF) :
    m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.get a h) :=
  HashMap.Raw.all_eq_true_iff_forall_mem_getKey_getElem h.out

theorem all_eq_true_iff_forall_mem [LawfulBEq α] {p : α → Bool} (h : m.WF) :
    m.all p = true ↔ ∀ (a : α), a ∈ m → p a := by
  simpa using HashMap.Raw.all_eq_true_iff_forall_mem_getElem h.out

theorem all_eq_false_iff_exists_mem_get [EquivBEq α] [LawfulHashable α]
    {p : α → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p (m.get a h) = false :=
  HashMap.Raw.all_eq_false_iff_exists_mem_getKey_getElem h.out

theorem all_eq_false_iff_exists_mem_getElem [LawfulBEq α] {p : α → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p a = false := by
  simpa using @HashMap.Raw.all_eq_false_iff_exists_mem_getElem _ _ _ _ _ _ (fun a b => p a) h.out

variable {ρ : Type v} [ForIn Id ρ α]

@[simp, grind =]
theorem insertMany_nil (h : m.WF) :
    insertMany m [] = m :=
  ext (HashMap.Raw.insertManyIfNewUnit_nil h.1)

@[simp, grind =]
theorem insertMany_list_singleton (h : m.WF) {k : α} :
    insertMany m [k] = m.insert k :=
  ext (HashMap.Raw.insertManyIfNewUnit_list_singleton h.1)

@[grind _=_]
theorem insertMany_cons (h : m.WF) {l : List α} {k : α} :
    insertMany m (k :: l) = insertMany (m.insert k) l :=
  ext (HashMap.Raw.insertManyIfNewUnit_cons h.1)

theorem insertMany_append (h : m.WF) {l₁ l₂ : List α} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp [h]
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons h, insertMany_cons h, ih h.insert]

grind_pattern insertMany_append => insertMany m (l₁ ++ l₂) where
  l₁ =/= []
  l₂ =/= []
grind_pattern insertMany_append => insertMany (insertMany m l₁) l₂ where
  l₁ =/= []
  l₂ =/= []

@[elab_as_elim]
theorem insertMany_ind {motive : Raw α → Prop} (m : Raw α) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insert a)) :
    motive (insertMany m l) :=
  show motive ⟨m.1.insertManyIfNewUnit l⟩ from
    HashMap.Raw.insertManyIfNewUnit_ind m.inner l init fun m => insert ⟨m⟩

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    (insertMany m l).contains k = (m.contains k || l.contains k) :=
  HashMap.Raw.contains_insertManyIfNewUnit_list h.1

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ l.contains k :=
  HashMap.Raw.mem_insertManyIfNewUnit_list h.1

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany m l → k ∈ m :=
  HashMap.Raw.mem_of_mem_insertManyIfNewUnit_list h.1 contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} {k : α} : k ∈ m → k ∈ insertMany m l :=
  HashMap.Raw.mem_insertManyIfNewUnit_of_mem h.out

theorem get?_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get? (insertMany m l) k = none :=
  HashMap.Raw.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h.1 not_mem contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get? (insertMany m l) k' = some k :=
  HashMap.Raw.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.1 k_beq not_mem distinct mem

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k : α} (mem : k ∈ m) :
    get? (insertMany m l) k = get? m k :=
  HashMap.Raw.getKey?_insertManyIfNewUnit_list_of_mem h.1 mem

theorem get_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) {h'} :
    get (insertMany m l) k' h' = k :=
  HashMap.Raw.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.1 k_beq not_mem distinct mem

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k : α} (mem : k ∈ m) {h₃} :
    get (insertMany m l) k h₃ = get m k mem :=
  HashMap.Raw.getKey_insertManyIfNewUnit_list_of_mem h.1 mem

theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get! (insertMany m l) k = default :=
  HashMap.Raw.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h.1 not_mem contains_eq_false

theorem get!_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.WF) {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get! (insertMany m l) k' = k :=
  HashMap.Raw.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.1 k_beq not_mem distinct mem

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.WF) {l : List α} {k : α} (mem : k ∈ m) :
    get! (insertMany m l) k = get! m k :=
  HashMap.Raw.getKey!_insertManyIfNewUnit_list_of_mem h.1 mem

theorem getD_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getD (insertMany m l) k fallback = fallback :=
  HashMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h.1 not_mem contains_eq_false

theorem getD_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getD (insertMany m l) k' fallback = k :=
  HashMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.1 k_beq not_mem distinct mem

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k fallback : α} (mem : k ∈ m) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  HashMap.Raw.getKeyD_insertManyIfNewUnit_list_of_mem h.1 mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  HashMap.Raw.size_insertManyIfNewUnit_list h.1 distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    m.size ≤ (insertMany m l).size :=
  HashMap.Raw.size_le_size_insertManyIfNewUnit_list h.1

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  HashMap.Raw.size_le_size_insertManyIfNewUnit h.out

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertMany m l).size ≤ m.size + l.length :=
  HashMap.Raw.size_insertManyIfNewUnit_list_le h.1

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  HashMap.Raw.isEmpty_insertManyIfNewUnit_list h.1

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} : (insertMany m l).isEmpty → m.isEmpty :=
  HashMap.Raw.isEmpty_of_isEmpty_insertManyIfNewUnit h.out

section
variable {m₁ m₂ : Raw α}

theorem Equiv.beq [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁ ~m m₂) : beq m₁ m₂ :=
  HashMap.Raw.Equiv.beq h₁.1 h₂.1 h.1

theorem equiv_of_beq [LawfulBEq α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁ == m₂) : m₁ ~m m₂ :=
  ⟨HashMap.Raw.equiv_of_beq h₁.1 h₂.1 h⟩

theorem Equiv.beq_congr [EquivBEq α] [LawfulHashable α] {m₃ m₄ : Raw α} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF) (w₁ : m₁ ~m m₃) (w₂ : m₂ ~m m₄) : (m₁ == m₂) = (m₃ == m₄) :=
  HashMap.Raw.Equiv.beq_congr h₁.1 h₂.1 h₃.1 h₄.1 w₁.1 w₂.1

end

section Union

variable (m₁ m₂ : Raw α)

variable {m₁ m₂}

@[simp]
theorem union_eq : m₁.union m₂ = m₁ ∪ m₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∪ m₂).contains k = (m₁.contains k || m₂.contains k) :=
  @HashMap.Raw.contains_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

/- mem -/
theorem mem_union_of_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ → k ∈ m₁ ∪ m₂ :=
  @HashMap.Raw.mem_union_of_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem mem_union_of_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₂ → k ∈ m₁ ∪ m₂ :=
  @HashMap.Raw.mem_union_of_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

@[simp]
theorem mem_union_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∪ m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ :=
  @HashMap.Raw.mem_union_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem mem_of_mem_union_of_not_mem_right [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₂ → k ∈ m₁ :=
  @HashMap.Raw.mem_of_mem_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem mem_of_mem_union_of_not_mem_left [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂ :=
  @HashMap.Raw.mem_of_mem_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

/- Equiv -/
theorem Equiv.union_left {m₃ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₁ ~m m₂) :
    (m₁ ∪ m₃) ~m (m₂ ∪ m₃) :=
  ⟨@HashMap.Raw.Equiv.union_left _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.union_right {m₃ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₂ ~m m₃) :
    (m₁ ∪ m₂) ~m (m₁ ∪ m₃) :=
  ⟨@HashMap.Raw.Equiv.union_right _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.union_congr {m₃ m₄ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF)
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ ∪ m₂) ~m (m₃ ∪ m₄) :=
  ⟨@HashMap.Raw.Equiv.union_congr _ _ _ _ m₁.inner m₂.inner m₃.inner m₄.inner _ _ h₁.out h₂.out h₃.out h₄.out equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_union [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} :
    (m₁ ∪ m₂).get? k = (m₂.get? k).or (m₁.get? k) :=
  @HashMap.Raw.getKey?_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem get?_union_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).get? k = m₂.get? k :=
  @HashMap.Raw.getKey?_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem get?_union_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).get? k = m₁.get? k :=
  @HashMap.Raw.getKey?_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- get -/
theorem get_union_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂).get k (mem_union_of_right h₁ h₂ mem) = m₂.get k mem :=
  @HashMap.Raw.getKey_union_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

theorem get_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) {h'} :
    (m₁ ∪ m₂).get k h' = m₂.get k (mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  @HashMap.Raw.getKey_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

theorem get_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) {h'} :
    (m₁ ∪ m₂).get k h' = m₁.get k (mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  @HashMap.Raw.getKey_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

/- getD -/
theorem getD_union [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} :
    (m₁ ∪ m₂).getD k fallback = m₂.getD k (m₁.getD k fallback) :=
  @HashMap.Raw.getKeyD_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getD_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).getD k fallback = m₂.getD k fallback :=
  @HashMap.Raw.getKeyD_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getD_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).getD k fallback = m₁.getD k fallback :=
  @HashMap.Raw.getKeyD_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- get! -/
theorem get!_union [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∪ m₂).get! k = m₂.getD k (m₁.get! k) :=
  @HashMap.Raw.getKey!_union _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem get!_union_of_not_mem_left [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).get! k = m₂.get! k :=
  @HashMap.Raw.getKey!_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem get!_union_of_not_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).get! k = m₁.get! k :=
   @HashMap.Raw.getKey!_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- size -/
theorem size_union_of_not_mem [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) : (∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) →
    (m₁ ∪ m₂).size = m₁.size + m₂.size :=
  @HashMap.Raw.size_union_of_not_mem _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_left_le_size_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) : m₁.size ≤ (m₁ ∪ m₂).size :=
  @HashMap.Raw.size_left_le_size_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_right_le_size_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) : m₂.size ≤ (m₁ ∪ m₂).size :=
  @HashMap.Raw.size_right_le_size_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_union_le_size_add_size [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∪ m₂).size ≤ m₁.size + m₂.size :=
  @HashMap.Raw.size_union_le_size_add_size _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

/- isEmpty -/
@[simp]
theorem isEmpty_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∪ m₂).isEmpty = (m₁.isEmpty && m₂.isEmpty) :=
  @HashMap.Raw.isEmpty_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out


end Union

section Inter

variable {m₁ m₂ : Raw α}

@[simp]
theorem inter_eq : m₁.inter m₂ = m₁ ∩ m₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).contains k = (m₁.contains k && m₂.contains k) :=
  @HashMap.Raw.contains_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

/- mem -/
@[simp]
theorem mem_inter_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∩ m₂ ↔ k ∈ m₁ ∧ k ∈ m₂ :=
  @HashMap.Raw.mem_inter_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem not_mem_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ ∩ m₂ :=
  @HashMap.Raw.not_mem_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem not_mem_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₂) :
    k ∉ m₁ ∩ m₂ :=
  @HashMap.Raw.not_mem_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- Equiv -/
theorem Equiv.inter_left {m₃ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₁ ~m m₂) :
    (m₁ ∩ m₃) ~m (m₂ ∩ m₃) :=
  ⟨@HashMap.Raw.Equiv.inter_left _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.inter_right {m₃ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₂ ~m m₃) :
    (m₁ ∩ m₂) ~m (m₁ ∩ m₃) :=
  ⟨@HashMap.Raw.Equiv.inter_right _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.inter_congr {m₃ m₄ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF)
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ ∩ m₂) ~m (m₃ ∩ m₄) :=
  ⟨@HashMap.Raw.Equiv.inter_congr _ _ _ _ m₁.inner m₂.inner m₃.inner m₄.inner _ _ h₁.out h₂.out h₃.out h₄.out equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_inter [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} :
    (m₁ ∩ m₂).get? k =
    if k ∈ m₂ then m₁.get? k else none :=
  @HashMap.Raw.getKey?_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem get?_inter_of_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).get? k = m₁.get? k :=
  @HashMap.Raw.getKey?_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

theorem get?_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).get? k = none :=
  @HashMap.Raw.getKey?_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem get?_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).get? k = none :=
  @HashMap.Raw.getKey?_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- get -/
@[simp] theorem get_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ ∩ m₂} :
    (m₁ ∩ m₂).get k h_mem =
    m₁.get k ((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  @HashMap.Raw.getKey_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- getD -/
theorem getD_inter [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} :
    (m₁ ∩ m₂).getD k fallback =
    if k ∈ m₂ then m₁.getD k fallback else fallback :=
  @HashMap.Raw.getKeyD_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getD_inter_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).getD k fallback = m₁.getD k fallback :=
  @HashMap.Raw.getKeyD_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback mem

theorem getD_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).getD k fallback = fallback :=
  @HashMap.Raw.getKeyD_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getD_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).getD k fallback = fallback :=
  @HashMap.Raw.getKeyD_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- get! -/
theorem get!_inter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).get! k =
    if k ∈ m₂ then m₁.get! k else default :=
  @HashMap.Raw.getKey!_inter _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem get!_inter_of_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (mem : k ∈ m₂) :
    (m₁ ∩ m₂).get! k = m₁.get! k :=
  @HashMap.Raw.getKey!_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

theorem get!_inter_of_not_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).get! k = default :=
  @HashMap.Raw.getKey!_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem get!_inter_of_not_mem_left [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).get! k = default :=
  @HashMap.Raw.getKey!_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- size -/
theorem size_inter_le_size_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) :
    (m₁ ∩ m₂).size ≤ m₁.size :=
  @HashMap.Raw.size_inter_le_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_inter_le_size_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) :
    (m₁ ∩ m₂).size ≤ m₂.size :=
  @HashMap.Raw.size_inter_le_size_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_inter_eq_size_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF)
    (h : ∀ (a : α), a ∈ m₁ → a ∈ m₂) :
    (m₁ ∩ m₂).size = m₁.size :=
  @HashMap.Raw.size_inter_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem size_inter_eq_size_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF)
    (h : ∀ (a : α), a ∈ m₂ → a ∈ m₁) :
    (m₁ ∩ m₂).size = m₂.size :=
  @HashMap.Raw.size_inter_eq_size_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem size_add_size_eq_size_union_add_size_inter [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    m₁.size + m₂.size = (m₁ ∪ m₂).size + (m₁ ∩ m₂).size :=
  @HashMap.Raw.size_add_size_eq_size_union_add_size_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁.isEmpty) :
    (m₁ ∩ m₂).isEmpty = true :=
  @HashMap.Raw.isEmpty_inter_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

@[simp]
theorem isEmpty_inter_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₂.isEmpty) :
    (m₁ ∩ m₂).isEmpty = true :=
  @HashMap.Raw.isEmpty_inter_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem isEmpty_inter_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∩ m₂).isEmpty ↔ ∀ k, k ∈ m₁ → k ∉ m₂ :=
  @HashMap.Raw.isEmpty_inter_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

end Inter

section Diff

variable {m₁ m₂ : Raw α}

@[simp]
theorem diff_eq : m₁.diff m₂ = m₁ \ m₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂).contains k = (m₁.contains k && !m₂.contains k) :=
  @HashMap.Raw.contains_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

/- mem -/
@[simp]
theorem mem_diff_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ \ m₂ ↔ k ∈ m₁ ∧ k ∉ m₂ :=
  @HashMap.Raw.mem_diff_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem not_mem_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ \ m₂ :=
  @HashMap.Raw.not_mem_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem not_mem_diff_of_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (mem : k ∈ m₂) :
    k ∉ m₁ \ m₂ :=
  @HashMap.Raw.not_mem_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

/- Equiv -/
theorem Equiv.diff_left {m₃ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₁ ~m m₂) :
    (m₁ \ m₃) ~m (m₂ \ m₃) :=
  ⟨@HashMap.Raw.Equiv.diff_left _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.diff_right {m₃ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₂ ~m m₃) :
    (m₁ \ m₂) ~m (m₁ \ m₃) :=
  ⟨@HashMap.Raw.Equiv.diff_right _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.diff_congr {m₃ m₄ : Raw α} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF)
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ \ m₂) ~m (m₃ \ m₄) :=
  ⟨@HashMap.Raw.Equiv.diff_congr _ _ _ _ m₁.inner m₂.inner m₃.inner m₄.inner _ _ h₁.out h₂.out h₃.out h₄.out equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_diff [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} :
    (m₁ \ m₂).get? k =
    if k ∈ m₂ then none else m₁.get? k :=
  @HashMap.Raw.getKey?_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem get?_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).get? k = m₁.get? k :=
  @HashMap.Raw.getKey?_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem get?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).get? k = none :=
  @HashMap.Raw.getKey?_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem get?_diff_of_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).get? k = none :=
  @HashMap.Raw.getKey?_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

/- get -/
@[simp] theorem get_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ \ m₂} :
    (m₁ \ m₂).get k h_mem =
    m₁.get k ((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  @HashMap.Raw.getKey_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- getD -/
theorem getD_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} :
    (m₁ \ m₂).getD k fallback =
    if k ∈ m₂ then fallback else m₁.getD k fallback :=
  @HashMap.Raw.getKeyD_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getD_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).getD k fallback = m₁.getD k fallback :=
  @HashMap.Raw.getKeyD_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getD_diff_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).getD k fallback = fallback :=
  @HashMap.Raw.getKeyD_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback mem

theorem getD_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getD k fallback = fallback :=
  @HashMap.Raw.getKeyD_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- get! -/
theorem get!_diff [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂).get! k =
    if k ∈ m₂ then default else m₁.get! k :=
  @HashMap.Raw.getKey!_diff _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem get!_diff_of_not_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₂) :
    (m₁ \ m₂).get! k = m₁.get! k :=
  @HashMap.Raw.getKey!_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem get!_diff_of_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (mem : k ∈ m₂) :
    (m₁ \ m₂).get! k = default :=
  @HashMap.Raw.getKey!_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

theorem get!_diff_of_not_mem_left [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₁) :
    (m₁ \ m₂).get! k = default :=
  @HashMap.Raw.getKey!_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- size -/
theorem size_diff_le_size_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) :
    (m₁ \ m₂).size ≤ m₁.size :=
  @HashMap.Raw.size_diff_le_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_diff_eq_size_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF)
    (h : ∀ (a : α), a ∈ m₁ → a ∉ m₂) :
    (m₁ \ m₂).size = m₁.size :=
  @HashMap.Raw.size_diff_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem size_diff_add_size_inter_eq_size_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ \ m₂).size + (m₁ ∩ m₂).size = m₁.size :=
  @HashMap.Raw.size_diff_add_size_inter_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁.isEmpty) :
    (m₁ \ m₂).isEmpty = true :=
  @HashMap.Raw.isEmpty_diff_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem isEmpty_diff_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ \ m₂).isEmpty ↔ ∀ k, k ∈ m₁ → k ∈ m₂ :=
  @HashMap.Raw.isEmpty_diff_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

end Diff

@[simp, grind =]
theorem ofArray_eq_ofList (a : Array α) :
    ofArray a = ofList a.toList := by
  apply ext
  apply HashMap.Raw.unitOfArray_eq_unitOfList

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List α) = ∅ :=
  ext HashMap.Raw.unitOfList_nil

@[simp, grind =]
theorem ofList_singleton {k : α} :
    ofList [k] = (∅ : Raw α).insert k :=
  ext HashMap.Raw.unitOfList_singleton

@[grind _=_]
theorem ofList_cons {hd : α} {tl : List α} :
    ofList (hd :: tl) = insertMany ((∅ : Raw α).insert hd) tl :=
  ext HashMap.Raw.unitOfList_cons

theorem ofList_eq_insertMany_empty {l : List α} :
    ofList l = insertMany (∅ : Raw α) l :=
  match l with
  | [] => by simp [insertMany_nil .empty]
  | hd :: tl => by simp [ofList_cons, insertMany_cons .empty]

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (ofList l).contains k = l.contains k :=
  HashMap.Raw.contains_unitOfList

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ ofList l ↔ l.contains k :=
  HashMap.Raw.mem_unitOfList

theorem get?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    get? (ofList l) k = none :=
  HashMap.Raw.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get? (ofList l) k' = some k :=
  HashMap.Raw.getKey?_unitOfList_of_mem k_beq distinct mem

theorem get_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h'} :
    get (ofList l) k' h' = k :=
  HashMap.Raw.getKey_unitOfList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get! (ofList l) k = default :=
  HashMap.Raw.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    get! (ofList l) k' = k :=
  HashMap.Raw.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getD (ofList l) k fallback = fallback :=
  HashMap.Raw.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getD (ofList l) k' fallback = k :=
  HashMap.Raw.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (ofList l).size = l.length :=
  HashMap.Raw.size_unitOfList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (ofList l).size ≤ l.length :=
  HashMap.Raw.size_unitOfList_le

grind_pattern size_ofList_le => (ofList l).size

@[simp, grind =]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (ofList l).isEmpty = l.isEmpty :=
  HashMap.Raw.isEmpty_unitOfList


namespace Equiv

section Raw

variable {α : Type u} {β : Type v} {m m₁ m₂ m₃ : Raw α}

@[refl, simp] theorem refl (m : Raw α) : m ~m m := ⟨.rfl⟩
theorem rfl : m ~m m := ⟨.rfl⟩
@[symm] theorem symm : m₁ ~m m₂ → m₂ ~m m₁
  | ⟨h⟩ => ⟨h.symm⟩
theorem trans : m₁ ~m m₂ → m₂ ~m m₃ → m₁ ~m m₃
  | ⟨h₁⟩, ⟨h₂⟩ => ⟨h₁.trans h₂⟩

instance instTrans : Trans (α := Raw α) Equiv Equiv Equiv := ⟨trans⟩

theorem comm : m₁ ~m m₂ ↔ m₂ ~m m₁ := ⟨symm, symm⟩
theorem congr_left (h : m₁ ~m m₂) : m₁ ~m m₃ ↔ m₂ ~m m₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : m₁ ~m m₂) : m₃ ~m m₁ ↔ m₃ ~m m₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

theorem toList_perm (h : m₁ ~m m₂) : m₁.toList.Perm m₂.toList :=
  h.1.keys_perm

theorem of_toList_perm (h : m₁.toList.Perm m₂.toList) : m₁ ~m m₂ :=
  ⟨.of_keys_unit_perm h⟩

end Raw

variable {m₁ m₂ : Raw α}

theorem isEmpty_eq [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.isEmpty = m₂.isEmpty :=
  h.1.isEmpty_eq h₁.1 h₂.1

theorem size_eq [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.size = m₂.size :=
  h.1.size_eq h₁.1 h₂.1

theorem contains_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.contains k = m₂.contains k :=
  h.1.contains_eq h₁.1 h₂.1

theorem mem_iff [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : k ∈ m₁ ↔ k ∈ m₂ :=
  h.1.mem_iff h₁.1 h₂.1

theorem get?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.get? k = m₂.get? k :=
  h.1.getKey?_eq h₁.1 h₂.1

theorem get_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (hk : k ∈ m₁) (h : m₁ ~m m₂) : m₁.get k hk = m₂.get k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.getKey_eq h₁.1 h₂.1 hk

theorem get!_eq [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.get! k = m₂.get! k :=
  h.1.getKey!_eq h₁.1 h₂.1

theorem getD_eq [EquivBEq α] [LawfulHashable α] {k fallback : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.getD k fallback = m₂.getD k fallback :=
  h.1.getKeyD_eq h₁.1 h₂.1

theorem insert [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (k : α)
    (h : m₁ ~m m₂) : m₁.insert k ~m m₂.insert k :=
  ⟨h.1.insertIfNew h₁.1 h₂.1 k ()⟩

theorem erase [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (k : α)
    (h : m₁ ~m m₂) : m₁.erase k ~m m₂.erase k :=
  ⟨h.1.erase h₁.1 h₂.1 k⟩

theorem insertMany_list [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (l : List α)
    (h : m₁ ~m m₂) : m₁.insertMany l ~m m₂.insertMany l :=
  ⟨h.1.insertManyIfNewUnit_list h₁.1 h₂.1 l⟩

theorem filter (h₁ : m₁.WF) (h₂ : m₂.WF) (f : α → Bool) (h : m₁ ~m m₂) :
    m₁.filter f ~m m₂.filter f :=
  ⟨h.1.filter h₁.1 h₂.1 _⟩

theorem of_forall_get?_eq [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ ~m m₂ :=
  ⟨.of_forall_getKey?_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_contains_eq [LawfulBEq α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ ~m m₂ :=
  ⟨.of_forall_contains_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_mem_iff [LawfulBEq α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ ~m m₂ :=
  ⟨.of_forall_mem_unit_iff h₁.1 h₂.1 h⟩

end Equiv

theorem equiv_emptyWithCapacity_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} (h : m.WF) :
    m ~m emptyWithCapacity c ↔ m.isEmpty :=
  ⟨fun ⟨h'⟩ => (HashMap.Raw.equiv_emptyWithCapacity_iff_isEmpty h.1).mp h',
    fun h' => ⟨(HashMap.Raw.equiv_emptyWithCapacity_iff_isEmpty h.1).mpr h'⟩⟩

theorem equiv_empty_iff_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m ~m ∅ ↔ m.isEmpty :=
  equiv_emptyWithCapacity_iff_isEmpty h

theorem equiv_iff_toList_perm {m₁ m₂ : Raw α} [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ m₁.toList.Perm m₂.toList :=
  ⟨Equiv.toList_perm, Equiv.of_toList_perm⟩

section filter

theorem toList_filter {f : α → Bool} (h : m.WF) :
    (m.filter f).toList.Perm (m.toList.filter f) :=
  HashMap.Raw.keys_filter_key h.1

@[grind =] theorem isEmpty_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.WF) :
    (m.filter f).isEmpty ↔
      ∀ (k : α) (h : k ∈ m), f (m.get k h) = false :=
  HashMap.Raw.isEmpty_filter_iff h.out

theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.WF) :
    (m.filter f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), f (m.get k h) :=
  HashMap.Raw.isEmpty_filter_eq_false_iff h.out

-- TODO: `contains_filter` is missing.

@[simp, grind =]
theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} (h : m.WF) :
    (k ∈ m.filter f) ↔ ∃ (h' : k ∈ m), f (m.get k h') :=
  HashMap.Raw.mem_filter h.out

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} (h : m.WF) :
    k ∈ (m.filter f) → k ∈ m :=
  HashMap.Raw.mem_of_mem_filter h.out

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.WF) :
    (m.filter f).size ≤ m.size :=
  HashMap.Raw.size_filter_le_size h.out

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.WF) :
    (m.filter f).size = m.size ↔ ∀ (k : α) (h : k ∈ m), f (m.get k h) :=
  HashMap.Raw.size_filter_eq_size_iff h.out

theorem filter_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → Bool} (h : m.WF) :
    (m.filter f) ~m m ↔ ∀ (a : α) (h : a ∈ m), f (m.get a h) = true :=
  ⟨fun h' => (HashMap.Raw.filter_equiv_self_iff h.out).mp h'.1,
    fun h' => ⟨(HashMap.Raw.filter_equiv_self_iff h.out).mpr h'⟩⟩

@[simp, grind =]
theorem get?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} (h : m.WF) :
    (m.filter f).get? k = (m.get? k).filter f :=
  HashMap.Raw.getKey?_filter_key h.out

@[simp, grind =]
theorem get_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} {h'} (h : m.WF) :
    (m.filter f).get k h' = (m.get k (mem_of_mem_filter h h')) :=
  HashMap.Raw.getKey_filter h.out

@[grind =] theorem get!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} (h : m.WF) :
    (m.filter f).get! k = ((m.get? k).filter f).get! :=
  HashMap.Raw.getKey!_filter_key h.out

@[grind =] theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} (h : m.WF) :
    (m.filter f).getD k fallback = ((m.get? k).filter f).getD fallback :=
  HashMap.Raw.getKeyD_filter_key h.out

end filter

attribute [simp] contains_eq_false_iff_not_mem
end Raw

end Std.HashSet
