/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Std.Data.HashMap.Lemmas
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# Hash set lemmas

This module contains lemmas about `Std.Data.HashSet`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {_ : BEq α} {_ : Hashable α}

namespace Std.HashSet

section

variable {m : HashSet α}

private theorem ext {m m' : HashSet α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyWithCapacity {c} : (emptyWithCapacity c : HashSet α).isEmpty :=
  HashMap.isEmpty_emptyWithCapacity

@[simp, grind =]
theorem isEmpty_empty : (∅ : HashSet α).isEmpty :=
  HashMap.isEmpty_empty

@[simp, grind =]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} : (m.insert a).isEmpty = false :=
  HashMap.isEmpty_insertIfNew

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m :=
  HashMap.contains_iff_mem

-- The following lemma becomes a simp lemma at the bottom of the file.
theorem contains_eq_false_iff_not_mem {k : α} : m.contains k = false ↔ ¬k ∈ m :=
  HashMap.contains_eq_false_iff_not_mem

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  HashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  HashMap.mem_congr hab

@[simp, grind =]
theorem contains_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : HashSet α).contains a = false :=
  HashMap.contains_emptyWithCapacity

@[simp, grind ←] theorem not_mem_emptyWithCapacity {a : α} {c} : ¬a ∈ (emptyWithCapacity c : HashSet α) :=
  HashMap.not_mem_emptyWithCapacity

@[simp, grind =] theorem contains_empty {a : α} : (∅ : HashSet α).contains a = false :=
  HashMap.contains_empty

@[simp] theorem not_mem_empty {a : α} : ¬a ∈ (∅ : HashSet α) :=
  HashMap.not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → m.contains a = false :=
  HashMap.contains_of_isEmpty

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → ¬a ∈ m :=
  HashMap.not_mem_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, m.contains a = true :=
  HashMap.isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, a ∈ m :=
  HashMap.isEmpty_eq_false_iff_exists_mem

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, m.contains a = false :=
  HashMap.isEmpty_iff_forall_contains

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m :=
  HashMap.isEmpty_iff_forall_not_mem

@[simp] theorem insert_eq_insert {a : α} : Insert.insert a m = m.insert a := rfl

@[simp] theorem singleton_eq_insert {a : α} : Singleton.singleton a = (∅ : HashSet α).insert a := rfl

@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a = (k == a || m.contains a) :=
  HashMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ k == a ∨ a ∈ m :=
  HashMap.mem_insertIfNew

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → (k == a) = false → m.contains a :=
  HashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → (k == a) = false → a ∈ m :=
  HashMap.mem_of_mem_insertIfNew

/-- This is a restatement of `contains_insert` that is written to exactly match the proof
obligation in the statement of `get_insert`. -/
theorem contains_of_contains_insert' [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  HashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_insert` that is written to exactly match the proof obligation
in the statement of `get_insert`. -/
theorem mem_of_mem_insert' [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  DHashMap.mem_of_mem_insertIfNew'

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).contains k := by
  simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k := by simp

theorem mem_of_get_eq {k v : α} {w} (_ : m.get k w = v) : k ∈ m := w

@[simp, grind =]
theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : HashSet α).size = 0 :=
  HashMap.size_emptyWithCapacity

@[simp, grind =]
theorem size_empty : (∅ : HashSet α).size = 0 :=
  HashMap.size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.isEmpty_eq_size_eq_zero

@[simp]
theorem toList_emptyWithCapacity {c} : (emptyWithCapacity c : HashSet α).toList = [] :=
  HashMap.keys_emptyWithCapacity

@[simp]
theorem toList_empty : (∅ : HashSet α).toList = [] :=
  toList_emptyWithCapacity

@[grind =] theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size = if k ∈ m then m.size else m.size + 1 :=
  HashMap.size_insertIfNew

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  HashMap.size_le_size_insertIfNew

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size ≤ m.size + 1 :=
  HashMap.size_insertIfNew_le

@[simp, grind =]
theorem erase_emptyWithCapacity {a : α} {c : Nat} : (emptyWithCapacity c : HashSet α).erase a = emptyWithCapacity c :=
  ext HashMap.erase_emptyWithCapacity

@[simp, grind =]
theorem erase_empty {a : α} : (∅ : HashSet α).erase a = ∅ :=
  ext HashMap.erase_empty

@[simp, grind =]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.isEmpty_erase

@[simp, grind =]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  HashMap.contains_erase

@[simp, grind =]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  HashMap.mem_erase

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  HashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m :=
  HashMap.mem_of_mem_erase

@[grind =] theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  HashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  HashMap.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  HashMap.size_le_size_erase

@[simp, grind =]
theorem get?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : HashSet α).get? a = none :=
  HashMap.getKey?_emptyWithCapacity

@[simp, grind =]
theorem get?_empty {a : α} : (∅ : HashSet α).get? a = none :=
  HashMap.getKey?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.get? a = none :=
  HashMap.getKey?_of_isEmpty

@[grind =] theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).get? a = if k == a ∧ ¬k ∈ m then some k else m.get? a :=
  HashMap.getKey?_insertIfNew

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.get? a).isSome :=
  HashMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_get?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.get? a).isSome = m.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ (m.get? a).isSome :=
  HashMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_get?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.get? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_get?.symm

theorem get?_eq_some_iff [EquivBEq α] [LawfulHashable α] {k k' : α} :
    m.get? k = some k' ↔ ∃ h : k ∈ m, m.get k h = k' :=
  HashMap.getKey?_eq_some_iff

theorem mem_of_get?_eq_some [EquivBEq α] [LawfulHashable α] {k k' : α}
    (h : m.get? k = some k') : k' ∈ m :=
  HashMap.mem_of_getKey?_eq_some h

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.get? a = none :=
  HashMap.getKey?_eq_none_of_contains_eq_false

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.get? a = none :=
  HashMap.getKey?_eq_none

@[grind =] theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  HashMap.getKey?_erase

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).get? k = none :=
  HashMap.getKey?_erase_self

theorem get?_beq [EquivBEq α] [LawfulHashable α] {k : α} : (m.get? k).all (· == k) :=
  HashMap.getKey?_beq

theorem get?_congr [EquivBEq α] [LawfulHashable α] {k k' : α} (h : k == k') :
    m.get? k = m.get? k' :=
  HashMap.getKey?_congr h

theorem get?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) : m.get? k = some k :=
  HashMap.getKey?_eq_some_of_contains h

theorem get?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.get? k = some k :=
  HashMap.getKey?_eq_some h

@[grind =] theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {h₁} :
    (m.insert k).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.get a (mem_of_mem_insert' h₁ h₂) :=
  HashMap.getKey_insertIfNew (h₁ := h₁)

theorem toList_insert_perm [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).toList.Perm (if k ∈ m then m.toList else k :: m.toList) :=
  HashMap.keys_insertIfNew_perm

@[simp, grind =]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  HashMap.getKey_erase (h' := h')

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) :
    m.get? a = some (m.get a h') :=
  HashMap.getKey?_eq_some_getKey h'

theorem get_eq_get_get? [EquivBEq α] [LawfulHashable α] {k : α} {h} :
    m.get k h = (m.get? k).get (mem_iff_isSome_get?.mp h) :=
  HashMap.getKey_eq_get_getKey?

@[grind =] theorem get_get? [EquivBEq α] [LawfulHashable α] {k : α} {h} :
    (m.get? k).get h = m.get k (mem_iff_isSome_get?.mpr h) :=
  HashMap.get_getKey?

theorem get_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.get k h == k :=
  HashMap.getKey_beq h

theorem get_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.get k₁ h₁ = m.get k₂ ((mem_congr h).mp h₁) :=
  HashMap.getKey_congr h h₁

@[simp, grind =]
theorem get_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.get k h = k :=
  HashMap.getKey_eq h

@[simp, grind =]
theorem get!_emptyWithCapacity [Inhabited α] {a : α} {c} : (emptyWithCapacity c : HashSet α).get! a = default :=
  HashMap.getKey!_emptyWithCapacity

@[simp, grind =]
theorem get!_empty [Inhabited α] {a : α} : (∅ : HashSet α).get! a = default :=
  HashMap.getKey!_empty

theorem get!_of_isEmpty [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.get! a = default :=
  HashMap.getKey!_of_isEmpty

@[grind =] theorem get!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).get! a = if k == a ∧ ¬k ∈ m then k else m.get! a :=
  HashMap.getKey!_insertIfNew

theorem get!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.get! a = default :=
  HashMap.getKey!_eq_default_of_contains_eq_false

theorem get!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    ¬a ∈ m → m.get! a = default :=
  HashMap.getKey!_eq_default

@[grind =] theorem get!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).get! a = if k == a then default else m.get! a :=
  HashMap.getKey!_erase

@[simp]
theorem get!_erase_self [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).get! k = default :=
  HashMap.getKey!_erase_self

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = true → m.get? a = some (m.get! a) :=
  HashMap.getKey?_eq_some_getKey!_of_contains

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.get? a = some (m.get! a) :=
  HashMap.getKey?_eq_some_getKey!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.get! a = (m.get? a).get! :=
  HashMap.getKey!_eq_get!_getKey?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h'} :
    m.get a h' = m.get! a :=
  HashMap.getKey_eq_getKey!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : k == k') :
    m.get! k = m.get! k' :=
  HashMap.getKey!_congr h

theorem get!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) : m.get! k = k :=
  HashMap.getKey!_eq_of_contains h

theorem get!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.get! k = k :=
  HashMap.getKey!_eq_of_mem h

@[simp, grind =]
theorem getD_emptyWithCapacity {a fallback : α} {c} : (emptyWithCapacity c : HashSet α).getD a fallback = fallback :=
  HashMap.getKeyD_emptyWithCapacity

@[simp, grind =]
theorem getD_empty {a fallback : α} : (∅ : HashSet α).getD a fallback = fallback :=
  HashMap.getKeyD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  HashMap.getKeyD_of_isEmpty

@[grind =] theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.insert k).getD a fallback = if k == a ∧ ¬k ∈ m then k else m.getD a fallback :=
  HashMap.getKeyD_insertIfNew

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {a fallback : α} :
    m.contains a = false → m.getD a fallback = fallback :=
  HashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  HashMap.getKeyD_eq_fallback

@[grind =] theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  HashMap.getKeyD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m.erase k).getD k fallback = fallback :=
  HashMap.getKeyD_erase_self

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.contains a = true → m.get? a = some (m.getD a fallback) :=
  HashMap.getKey?_eq_some_getKeyD_of_contains

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    a ∈ m → m.get? a = some (m.getD a fallback) :=
  HashMap.getKey?_eq_some_getKeyD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.getD a fallback = (m.get? a).getD fallback :=
  HashMap.getKeyD_eq_getD_getKey?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a fallback : α} {h'} :
    m.get a h' = m.getD a fallback :=
  @HashMap.getKey_eq_getKeyD _ _ _ _ _ _ _ _ _ h'

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.get! a = m.getD a default :=
  HashMap.getKey!_eq_getKeyD_default

theorem getD_congr [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    (h : k == k') : m.getD k fallback = m.getD k' fallback :=
  HashMap.getKeyD_congr h

theorem getD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getD k fallback = k :=
  HashMap.getKeyD_eq_of_contains h

theorem getD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) : m.getD k fallback = k :=
  HashMap.getKeyD_eq_of_mem h

@[simp, grind =]
theorem containsThenInsert_fst {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsert_snd {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext HashMap.containsThenInsertIfNew_snd

@[simp, grind =]
theorem length_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.length = m.size :=
  HashMap.length_keys

@[simp, grind =]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.isEmpty = m.isEmpty :=
  HashMap.isEmpty_keys

@[simp, grind =]
theorem contains_toList [EquivBEq α] [LawfulHashable α] {k : α} :
    m.toList.contains k = m.contains k :=
  HashMap.contains_keys

@[simp, grind =]
theorem mem_toList [LawfulBEq α] {k : α} :
    k ∈ m.toList ↔ k ∈ m :=
  HashMap.mem_keys

theorem mem_of_mem_toList [EquivBEq α] [LawfulHashable α] {k : α} :
    k ∈ m.toList → k ∈ m :=
  HashMap.mem_of_mem_keys

theorem distinct_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.Pairwise (fun a b => (a == b) = false) :=
  HashMap.distinct_keys

@[simp]
theorem toArray_toList :
    m.toList.toArray = m.toArray :=
  HashMap.toArray_keys

@[simp]
theorem toList_toArray :
    m.toArray.toList = m.toList :=
  HashMap.toList_keysArray

@[simp]
theorem size_toArray [EquivBEq α] [LawfulHashable α] :
    m.toArray.size = m.size :=
  HashMap.size_keysArray

@[simp]
theorem isEmpty_toArray [EquivBEq α] [LawfulHashable α] :
    m.toArray.isEmpty = m.isEmpty :=
  HashMap.isEmpty_keysArray

@[simp]
theorem contains_toArray [EquivBEq α] [LawfulHashable α]
    {k : α} :
    m.toArray.contains k = m.contains k :=
  HashMap.contains_keysArray

@[simp]
theorem mem_toArray [LawfulBEq α] {k : α} :
    k ∈ m.toArray ↔ k ∈ m :=
  HashMap.mem_keysArray

theorem forall_mem_toArray_iff_forall_mem_get [EquivBEq α] [LawfulHashable α]
    {p : α → Prop} :
    (∀ k ∈ m.toArray, p k) ↔ ∀ (k : α) (h : k ∈ m), p (m.get k h) :=
  HashMap.forall_mem_keysArray_iff_forall_mem_getKey

theorem contains_of_mem_toArray [EquivBEq α] [LawfulHashable α] {k : α}
    (h' : k ∈ m.toArray) : m.contains k :=
  HashMap.contains_of_mem_keysArray h'

section monadic

variable {δ : Type v} {m' : Type v → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM f init :=
  HashMap.foldM_eq_foldlM_keys

theorem fold_eq_foldl_toList {f : δ → α → δ} {init : δ} :
    m.fold f init = m.toList.foldl f init :=
  HashMap.fold_eq_foldl_keys

@[simp, grind =]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.forM f = ForM.forM m f := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  HashMap.forM_eq_forM_keys

@[simp, grind =]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m init f := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  HashMap.forIn_eq_forIn_keys

theorem foldM_eq_foldlM_toArray [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a => f d a) init = m.toArray.foldlM f init :=
  HashMap.foldM_eq_foldlM_keysArray

theorem fold_eq_foldl_toArray {f : δ → α → δ} {init : δ} :
    m.fold (fun d a => f d a) init = m.toArray.foldl f init :=
  HashMap.fold_eq_foldl_keysArray

theorem forM_eq_forM_toArray [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.forM (fun a => f a) = m.toArray.forM f :=
  HashMap.forM_eq_forM_keysArray

theorem forIn_eq_forIn_toArray [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn (fun a d => f a d) init = ForIn.forIn m.toArray init f :=
  HashMap.forIn_eq_forIn_keysArray

end monadic

theorem all_eq_not_any_not {p : α → Bool} :
    m.all p = ! m.any (fun a => ! p a) := HashMap.all_eq_not_any_not

theorem any_eq_not_all_not {p : α → Bool} :
    m.any p = ! m.all (fun a => ! p a) := HashMap.any_eq_not_all_not

@[simp]
theorem any_toList [LawfulHashable α] [EquivBEq α] {p : α → Bool} :
    m.toList.any p = m.any p :=
  HashMap.any_keys

theorem any_eq_true_iff_exists_mem_get [LawfulHashable α] [EquivBEq α]
    {p : α → Bool} :
    m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p (m.get a h) :=
  HashMap.any_eq_true_iff_exists_mem_getKey_getElem

theorem any_eq_true_iff_exists_mem [LawfulBEq α] {p : α → Bool} :
    m.any p = true ↔ ∃ (a : α), a ∈ m ∧ p a := by
  simpa using @HashMap.any_eq_true_iff_exists_mem_getElem _ _ _ _ _ _ (fun a b => p a)

theorem any_eq_false_iff_forall_mem_get [LawfulHashable α] [EquivBEq α]
    {p : α → Bool} :
    m.any p = false ↔
      ∀ (a : α) (h : a ∈ m), p (m.get a h) = false :=
  HashMap.any_eq_false_iff_forall_mem_getKey_getElem

theorem any_eq_false_iff_forall_mem [LawfulBEq α] {p : α → Bool} :
    m.any p = false ↔
      ∀ (a : α), a ∈ m → p a = false := by
  simpa using @HashMap.any_eq_false_iff_forall_mem_getElem _ _ _ _ _ _ (fun a b => p a)

@[simp]
theorem all_toList [LawfulHashable α] [EquivBEq α] {p : α → Bool} :
    m.toList.all p =m.all p :=
  HashMap.all_keys

theorem all_eq_true_iff_forall_mem_get [EquivBEq α] [LawfulHashable α]
    {p : α → Bool} :
    m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.get a h) :=
  HashMap.all_eq_true_iff_forall_mem_getKey_getElem

theorem all_eq_true_iff_forall_mem [LawfulBEq α] {p : α → Bool} :
    m.all p = true ↔ ∀ (a : α), a ∈ m → p a :=
  HashMap.all_eq_true_iff_forall_mem_getElem

theorem all_eq_false_iff_exists_mem_get [EquivBEq α] [LawfulHashable α]
    {p : α → Bool} :
    m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p (m.get a h) = false :=
  HashMap.all_eq_false_iff_exists_mem_getKey_getElem

theorem all_eq_false_iff_exists_mem [LawfulBEq α] {p : α → Bool} :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p a = false := by
  simpa using @HashMap.all_eq_false_iff_exists_mem_getElem _ _ _ _ _ _ (fun a b => p a)

variable {ρ : Type v} [ForIn Id ρ α]

@[simp, grind =]
theorem insertMany_nil :
    insertMany m [] = m :=
  ext HashMap.insertManyIfNewUnit_nil

@[simp, grind =]
theorem insertMany_list_singleton {k : α} :
    insertMany m [k] = m.insert k :=
  ext HashMap.insertManyIfNewUnit_list_singleton

@[grind _=_] theorem insertMany_cons {l : List α} {k : α} :
    insertMany m (k :: l) = insertMany (m.insert k) l :=
  ext HashMap.insertManyIfNewUnit_cons

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List α} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[elab_as_elim]
theorem insertMany_ind {motive : HashSet α → Prop} (m : HashSet α) {l : ρ}
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insert a)) :
    motive (m.insertMany l) :=
  show motive ⟨m.1.insertManyIfNewUnit l⟩ from
    HashMap.insertManyIfNewUnit_ind m.inner l init fun m => insert ⟨m⟩

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertMany m l).contains k = (m.contains k || l.contains k) :=
  HashMap.contains_insertManyIfNewUnit_list

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ l.contains k :=
  HashMap.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany m l → k ∈ m :=
  HashMap.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l :=
  HashMap.mem_insertManyIfNewUnit_of_mem

theorem get?_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get? (insertMany m l) k = none :=
  HashMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get? (insertMany m l) k' = some k :=
  HashMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) :
    get? (insertMany m l) k = get? m k :=
  HashMap.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem get_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) {h} :
    get (insertMany m l) k' h = k :=
  HashMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    get (insertMany m l) k h = get m k mem :=
  HashMap.getKey_insertManyIfNewUnit_list_of_mem mem

theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get! (insertMany m l) k = default :=
  HashMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get!_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get! (insertMany m l) k' = k :=
  HashMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    get! (insertMany m l) k = get! m k :=
  HashMap.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getD_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getD (insertMany m l) k fallback = fallback :=
  HashMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getD_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l)  :
    getD (insertMany m l) k' fallback = k :=
  HashMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  HashMap.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  HashMap.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    m.size ≤ (insertMany m l).size :=
  HashMap.size_le_size_insertManyIfNewUnit_list

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  HashMap.size_le_size_insertManyIfNewUnit

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertMany m l).size ≤ m.size + l.length :=
  HashMap.size_insertManyIfNewUnit_list_le

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  HashMap.isEmpty_insertManyIfNewUnit_list

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : (insertMany m l).isEmpty → m.isEmpty :=
  HashMap.isEmpty_of_isEmpty_insertManyIfNewUnit

end

section
variable {m₁ m₂ : HashSet α}

theorem Equiv.beq [EquivBEq α] [LawfulHashable α] (h : m₁ ~m m₂) : m₁ == m₂ :=
  HashMap.Equiv.beq h.1

theorem equiv_of_beq [LawfulBEq α] (h : m₁ == m₂) : m₁ ~m m₂ :=
  ⟨HashMap.equiv_of_beq h⟩

theorem Equiv.beq_congr [EquivBEq α] [LawfulHashable α] {m₃ m₄ : HashSet α} (h₁ : m₁ ~m m₃) (h₂ : m₂ ~m m₄) : (m₁ == m₂) = (m₃ == m₄) :=
  HashMap.Equiv.beq_congr h₁.1 h₂.1

end

section Union

variable (m₁ m₂ : HashSet α)

variable {m₁ m₂}

@[simp]
theorem union_eq : m₁.union m₂ = m₁ ∪ m₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [EquivBEq α] [LawfulHashable α]
    {k : α} :
    (m₁ ∪ m₂).contains k = (m₁.contains k || m₂.contains k) :=
  @HashMap.contains_union _ _ _ _ m₁.inner m₂.inner _ _  k

/- mem -/
theorem mem_union_of_left [EquivBEq α] [LawfulHashable α] {k : α} :
    k ∈ m₁ → k ∈ m₁ ∪ m₂:=
  @HashMap.mem_union_of_left _ _ _ _ m₁.inner m₂.inner _ _ k

theorem mem_union_of_right [EquivBEq α] [LawfulHashable α] {k : α} :
    k ∈ m₂ → k ∈ m₁ ∪ m₂:=
  @HashMap.mem_union_of_right _ _ _ _ m₁.inner m₂.inner _ _  k

@[simp]
theorem mem_union_iff [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ ∪ m₂).contains k ↔ m₁.contains k ∨ m₂.contains k :=
  @HashMap.mem_union_iff _ _ _ _ m₁.inner m₂.inner _ _  k

theorem mem_of_mem_union_of_not_mem_right [EquivBEq α]
    [LawfulHashable α] {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₂ → k ∈ m₁ :=
  @HashMap.mem_of_mem_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _  k

theorem mem_of_mem_union_of_not_mem_left [EquivBEq α]
    [LawfulHashable α] {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂ :=
  @HashMap.mem_of_mem_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _  k

/- Equiv -/
theorem Equiv.union_left {m₃ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv : m₁ ~m m₂) :
    (m₁ ∪ m₃) ~m (m₂ ∪ m₃) :=
  ⟨HashMap.Equiv.union_left equiv.1⟩

theorem Equiv.union_right {m₃ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv : m₂ ~m m₃) :
    (m₁ ∪ m₂) ~m (m₁ ∪ m₃) :=
  ⟨HashMap.Equiv.union_right equiv.1⟩

theorem Equiv.union_congr {m₃ m₄ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv₁ : m₁ ~m m₃)
    (equiv₂ : m₂ ~m m₄) :
    (m₁ ∪ m₂) ~m (m₃ ∪ m₄) :=
  ⟨HashMap.Equiv.union_congr equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_union [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ ∪ m₂).get? k = (m₂.get? k).or (m₁.get? k) :=
  @HashMap.getKey?_union _ _ _ _ m₁.inner m₂.inner _ _  k

theorem get?_union_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).get? k = m₂.get? k :=
  @HashMap.getKey?_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _  k not_mem

theorem get?_union_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).get? k = m₁.get? k :=
  @HashMap.getKey?_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _  k not_mem

/- get -/
theorem get_union_of_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂).get k (mem_union_of_right mem) = m₂.get k mem :=
  @HashMap.getKey_union_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _  k mem

theorem get_union_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : ¬k ∈ m₁) {h'} :
    (m₁ ∪ m₂).get k h' = m₂.get k (mem_of_mem_union_of_not_mem_left h' not_mem) :=
  @HashMap.getKey_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _  k not_mem h'

theorem get_union_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : ¬k ∈ m₂) {h'} :
    (m₁ ∪ m₂).get k h' = m₁.get k (mem_of_mem_union_of_not_mem_right h' not_mem) :=
  @HashMap.getKey_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _  k not_mem h'

/- getD -/
theorem getD_union [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m₁ ∪ m₂).getD k fallback = m₂.getD k (m₁.getD k fallback) :=
  @HashMap.getKeyD_union _ _ _ _ m₁.inner m₂.inner _ _  k fallback

theorem getD_union_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).getD k fallback = m₂.getD k fallback :=
  @HashMap.getKeyD_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _  k fallback not_mem

theorem getD_union_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).getD k fallback = m₁.getD k fallback :=
  @HashMap.getKeyD_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _  k fallback not_mem

/- get! -/
theorem get!_union [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m₁ ∪ m₂).get! k = m₂.getD k (m₁.get! k) :=
  @HashMap.getKey!_union _ _ _ _ m₁.inner m₂.inner _ _ _  k

theorem get!_union_of_not_mem_left [Inhabited α]
    [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).get! k = m₂.get! k :=
  @HashMap.getKey!_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _  k not_mem

theorem get!_union_of_not_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).get! k = m₁.get! k :=
  @HashMap.getKey!_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _  k not_mem

/- size -/
theorem size_union_of_not_mem [EquivBEq α] [LawfulHashable α] :
    (∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) →
    (m₁ ∪ m₂).size = m₁.size + m₂.size :=
  @HashMap.size_union_of_not_mem _ _ _ _ m₁.inner m₂.inner _ _

theorem size_left_le_size_union [EquivBEq α] [LawfulHashable α] : m₁.size ≤ (m₁ ∪ m₂).size :=
  @HashMap.size_left_le_size_union _ _ _ _ m₁.inner m₂.inner _ _

theorem size_right_le_size_union [EquivBEq α] [LawfulHashable α] :
    m₂.size ≤ (m₁ ∪ m₂).size :=
  @HashMap.size_right_le_size_union _ _ _ _ m₁.inner m₂.inner _ _

theorem size_union_le_size_add_size [EquivBEq α] [LawfulHashable α] :
    (m₁ ∪ m₂).size ≤ m₁.size + m₂.size :=
  @HashMap.size_union_le_size_add_size _ _ _ _ m₁.inner m₂.inner _ _

/- isEmpty -/
@[simp]
theorem isEmpty_union [EquivBEq α] [LawfulHashable α] :
    (m₁ ∪ m₂).isEmpty = (m₁.isEmpty && m₂.isEmpty) :=
  @HashMap.isEmpty_union α _ _ _ m₁.inner m₂.inner _ _

end Union

section Inter

variable {m₁ m₂ : HashSet α}

@[simp]
theorem inter_eq : m₁.inter m₂ = m₁ ∩ m₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ ∩ m₂).contains k = (m₁.contains k && m₂.contains k) :=
  @HashMap.contains_inter _ _ _ _ m₁.inner m₂.inner _ _ k

/- mem -/
@[simp]
theorem mem_inter_iff [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ ∩ m₂).contains k ↔ m₁.contains k ∧ m₂.contains k :=
  @HashMap.mem_inter_iff _ _ _ _ m₁.inner m₂.inner _ _ k

theorem not_mem_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ ∩ m₂ :=
  @HashMap.not_mem_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

theorem not_mem_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : k ∉ m₂) :
    k ∉ m₁ ∩ m₂ :=
  @HashMap.not_mem_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

/- Equiv -/
theorem Equiv.inter_left {m₃ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv : m₁ ~m m₂) :
    (m₁ ∩ m₃) ~m (m₂ ∩ m₃) :=
  ⟨HashMap.Equiv.inter_left equiv.1⟩

theorem Equiv.inter_right {m₃ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv : m₂ ~m m₃) :
    (m₁ ∩ m₂) ~m (m₁ ∩ m₃) :=
  ⟨HashMap.Equiv.inter_right equiv.1⟩

theorem Equiv.inter_congr {m₃ m₄ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ ∩ m₂) ~m (m₃ ∩ m₄) :=
  ⟨HashMap.Equiv.inter_congr equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_inter [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ ∩ m₂).get? k =
    if k ∈ m₂ then m₁.get? k else none :=
  @HashMap.getKey?_inter _ _ _ _ m₁.inner m₂.inner _ _ k

theorem get?_inter_of_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).get? k = m₁.get? k :=
  @HashMap.getKey?_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k mem

theorem get?_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).get? k = none :=
  @HashMap.getKey?_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

theorem get?_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).get? k = none :=
  @HashMap.getKey?_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

/- get -/
@[simp] theorem get_inter [EquivBEq α] [LawfulHashable α]
    {k : α} {h_mem : k ∈ m₁ ∩ m₂} :
    (m₁ ∩ m₂).get k h_mem =
    m₁.get k ((mem_inter_iff.1 h_mem).1) :=
  @HashMap.getKey_inter _ _ _ _ m₁.inner m₂.inner _ _ k h_mem

/- getD -/
theorem getD_inter [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m₁ ∩ m₂).getD k fallback =
    if k ∈ m₂ then m₁.getD k fallback else fallback :=
  @HashMap.getKeyD_inter _ _ _ _ m₁.inner m₂.inner _ _ k fallback

theorem getD_inter_of_mem_right [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).getD k fallback = m₁.getD k fallback :=
  @HashMap.getKeyD_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k fallback mem

theorem getD_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).getD k fallback = fallback :=
  @HashMap.getKeyD_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k fallback not_mem

theorem getD_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).getD k fallback = fallback :=
  @HashMap.getKeyD_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k fallback not_mem

/- get! -/
theorem get!_inter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m₁ ∩ m₂).get! k =
    if k ∈ m₂ then m₁.get! k else default :=
  @HashMap.getKey!_inter _ _ _ _ m₁.inner m₂.inner _ _ _ k

theorem get!_inter_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).get! k = m₁.get! k :=
  @HashMap.getKey!_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ k mem

theorem get!_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).get! k = default :=
  @HashMap.getKey!_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ k not_mem

theorem get!_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).get! k = default :=
  @HashMap.getKey!_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ k not_mem

/- size -/
theorem size_inter_le_size_left [EquivBEq α] [LawfulHashable α] :
    (m₁ ∩ m₂).size ≤ m₁.size :=
  @HashMap.size_inter_le_size_left _ _ _ _ m₁.inner m₂.inner _ _

theorem size_inter_le_size_right [EquivBEq α] [LawfulHashable α] :
    (m₁ ∩ m₂).size ≤ m₂.size :=
  @HashMap.size_inter_le_size_right _ _ _ _ m₁.inner m₂.inner _ _

theorem size_inter_eq_size_left [EquivBEq α] [LawfulHashable α]
    (h : ∀ (a : α), a ∈ m₁ → a ∈ m₂) :
    (m₁ ∩ m₂).size = m₁.size :=
  @HashMap.size_inter_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h

theorem size_inter_eq_size_right [EquivBEq α] [LawfulHashable α]
    (h : ∀ (a : α), a ∈ m₂ → a ∈ m₁) :
    (m₁ ∩ m₂).size = m₂.size :=
  @HashMap.size_inter_eq_size_right _ _ _ _ m₁.inner m₂.inner _ _ h

theorem size_add_size_eq_size_union_add_size_inter [EquivBEq α] [LawfulHashable α] :
    m₁.size + m₂.size = (m₁ ∪ m₂).size + (m₁ ∩ m₂).size :=
  @HashMap.size_add_size_eq_size_union_add_size_inter _ _ _ _ m₁.inner m₂.inner _ _

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [EquivBEq α] [LawfulHashable α] (h : m₁.isEmpty) :
    (m₁ ∩ m₂).isEmpty = true :=
  @HashMap.isEmpty_inter_left α _ _ _ m₁.inner m₂.inner _ _ h

@[simp]
theorem isEmpty_inter_right [EquivBEq α] [LawfulHashable α] (h : m₂.isEmpty) :
    (m₁ ∩ m₂).isEmpty = true :=
  @HashMap.isEmpty_inter_right α _ _ _ m₁.inner m₂.inner _ _ h

theorem isEmpty_inter_iff [EquivBEq α] [LawfulHashable α] :
    (m₁ ∩ m₂).isEmpty ↔ ∀ k, k ∈ m₁ → k ∉ m₂ :=
  @HashMap.isEmpty_inter_iff α _ _ _ m₁.inner m₂.inner _ _

end Inter

section Diff

variable {m₁ m₂ : HashSet α}

@[simp]
theorem diff_eq : m₁.diff m₂ = m₁ \ m₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ \ m₂).contains k = (m₁.contains k && !m₂.contains k) :=
  @HashMap.contains_diff _ _ _ _ m₁.inner m₂.inner _ _ k

/- mem -/
@[simp]
theorem mem_diff_iff [EquivBEq α] [LawfulHashable α] {k : α} :
    k ∈ m₁ \ m₂ ↔ k ∈ m₁ ∧ k ∉ m₂ :=
  @HashMap.mem_diff_iff _ _ _ _ m₁.inner m₂.inner _ _ k

theorem not_mem_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ \ m₂ :=
  @HashMap.not_mem_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

theorem not_mem_diff_of_mem_right [EquivBEq α] [LawfulHashable α] {k : α}
    (mem : k ∈ m₂) :
    k ∉ m₁ \ m₂ :=
  @HashMap.not_mem_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k mem

/- Equiv -/
theorem Equiv.diff_left {m₃ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv : m₁ ~m m₂) :
    (m₁ \ m₃) ~m (m₂ \ m₃) :=
  ⟨HashMap.Equiv.diff_left equiv.1⟩

theorem Equiv.diff_right {m₃ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv : m₂ ~m m₃) :
    (m₁ \ m₂) ~m (m₁ \ m₃) :=
  ⟨HashMap.Equiv.diff_right equiv.1⟩

theorem Equiv.diff_congr {m₃ m₄ : HashSet α} [EquivBEq α] [LawfulHashable α]
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ \ m₂) ~m (m₃ \ m₄) :=
  ⟨HashMap.Equiv.diff_congr equiv₁.1 equiv₂.1⟩

/- get? -/
theorem get?_diff [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ \ m₂).get? k =
    if k ∈ m₂ then none else m₁.get? k :=
  @HashMap.getKey?_diff _ _ _ _ m₁.inner m₂.inner _ _ k

theorem get?_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).get? k = m₁.get? k :=
  @HashMap.getKey?_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

theorem get?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).get? k = none :=
  @HashMap.getKey?_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k not_mem

theorem get?_diff_of_mem_right [EquivBEq α] [LawfulHashable α]
    {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).get? k = none :=
  @HashMap.getKey?_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k mem

/- get -/
@[simp] theorem get_diff [EquivBEq α] [LawfulHashable α]
    {k : α} {h_mem : k ∈ m₁ \ m₂} :
    (m₁ \ m₂).get k h_mem =
    m₁.get k ((mem_diff_iff.1 h_mem).1) :=
  @HashMap.getKey_diff _ _ _ _ m₁.inner m₂.inner _ _ k h_mem

/- getD -/
theorem getD_diff [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m₁ \ m₂).getD k fallback =
    if k ∈ m₂ then fallback else m₁.getD k fallback :=
  @HashMap.getKeyD_diff _ _ _ _ m₁.inner m₂.inner _ _ k fallback

theorem getD_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).getD k fallback = m₁.getD k fallback :=
  @HashMap.getKeyD_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k fallback not_mem

theorem getD_diff_of_mem_right [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).getD k fallback = fallback :=
  @HashMap.getKeyD_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ k fallback mem

theorem getD_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k fallback : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getD k fallback = fallback :=
  @HashMap.getKeyD_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k fallback not_mem

/- get! -/
theorem get!_diff [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m₁ \ m₂).get! k =
    if k ∈ m₂ then default else m₁.get! k :=
  @HashMap.getKey!_diff _ _ _ _ m₁.inner m₂.inner _ _ _ k

theorem get!_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).get! k = m₁.get! k :=
  @HashMap.getKey!_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ k not_mem

theorem get!_diff_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).get! k = default :=
  @HashMap.getKey!_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ k mem

theorem get!_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).get! k = default :=
  @HashMap.getKey!_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ k not_mem

/- size -/
theorem size_diff_le_size_left [EquivBEq α] [LawfulHashable α] :
    (m₁ \ m₂).size ≤ m₁.size :=
  @HashMap.size_diff_le_size_left _ _ _ _ m₁.inner m₂.inner _ _

theorem size_diff_eq_size_left [EquivBEq α] [LawfulHashable α]
    (h : ∀ (a : α), a ∈ m₁ → a ∉ m₂) :
    (m₁ \ m₂).size = m₁.size :=
  @HashMap.size_diff_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h

theorem size_diff_add_size_inter_eq_size_left [EquivBEq α] [LawfulHashable α] :
    (m₁ \ m₂).size + (m₁ ∩ m₂).size = m₁.size :=
  @HashMap.size_diff_add_size_inter_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [EquivBEq α] [LawfulHashable α] (h : m₁.isEmpty) :
    (m₁ \ m₂).isEmpty = true :=
  @HashMap.isEmpty_diff_left α _ _ _ m₁.inner m₂.inner _ _ h

theorem isEmpty_diff_iff [EquivBEq α] [LawfulHashable α] :
    (m₁ \ m₂).isEmpty ↔ ∀ k, k ∈ m₁ → k ∈ m₂ :=
  @HashMap.isEmpty_diff_iff α _ _ _ m₁.inner m₂.inner _ _

end Diff

section

@[simp, grind =]
theorem ofArray_eq_ofList (a : Array α) :
    ofArray a = ofList a.toList := by
  apply ext
  apply HashMap.unitOfArray_eq_unitOfList

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List α) = ∅ :=
  ext HashMap.unitOfList_nil

@[simp, grind =]
theorem ofList_singleton {k : α} :
    ofList [k] = (∅ : HashSet α).insert k :=
  ext HashMap.unitOfList_singleton

@[grind _=_] theorem ofList_cons {hd : α} {tl : List α} :
    ofList (hd :: tl) =
      insertMany ((∅ : HashSet α).insert hd) tl :=
  ext HashMap.unitOfList_cons

theorem ofList_eq_insertMany_empty {l : List α} :
    ofList l = insertMany (∅ : HashSet α) l :=
  match l with
  | [] => by simp
  | hd :: tl => by simp [ofList_cons, insertMany_cons]

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (ofList l).contains k = l.contains k :=
  HashMap.contains_unitOfList

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ ofList l ↔ l.contains k :=
  HashMap.mem_unitOfList

theorem get?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    get? (ofList l) k = none :=
  HashMap.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get? (ofList l) k' = some k :=
  HashMap.getKey?_unitOfList_of_mem k_beq distinct mem

theorem get_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    get (ofList l) k' h = k :=
  HashMap.getKey_unitOfList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get! (ofList l) k = default :=
  HashMap.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    get! (ofList l) k' = k :=
  HashMap.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getD (ofList l) k fallback = fallback :=
  HashMap.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getD (ofList l) k' fallback = k :=
  HashMap.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (ofList l).size = l.length :=
  HashMap.size_unitOfList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (ofList l).size ≤ l.length :=
  HashMap.size_unitOfList_le

grind_pattern size_ofList_le => (ofList l).size

@[simp, grind =]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (ofList l).isEmpty = l.isEmpty :=
  HashMap.isEmpty_unitOfList

end

namespace Equiv

variable {m m₁ m₂ m₃ : HashSet α}

@[refl, simp] theorem refl (m : HashSet α) : m ~m m := ⟨.rfl⟩
theorem rfl : m ~m m := ⟨.rfl⟩
@[symm] theorem symm : m₁ ~m m₂ → m₂ ~m m₁
  | ⟨h⟩ => ⟨h.symm⟩
theorem trans : m₁ ~m m₂ → m₂ ~m m₃ → m₁ ~m m₃
  | ⟨h₁⟩, ⟨h₂⟩ => ⟨h₁.trans h₂⟩

instance instTrans : Trans (α := HashSet α) Equiv Equiv Equiv := ⟨trans⟩

theorem comm : m₁ ~m m₂ ↔ m₂ ~m m₁ := ⟨symm, symm⟩
theorem congr_left (h : m₁ ~m m₂) : m₁ ~m m₃ ↔ m₂ ~m m₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : m₁ ~m m₂) : m₃ ~m m₁ ↔ m₃ ~m m₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

theorem isEmpty_eq [EquivBEq α] [LawfulHashable α] (h : m₁ ~m m₂) : m₁.isEmpty = m₂.isEmpty :=
  h.1.isEmpty_eq

theorem size_eq [EquivBEq α] [LawfulHashable α] (h : m₁ ~m m₂) : m₁.size = m₂.size :=
  h.1.size_eq

theorem contains_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁.contains k = m₂.contains k :=
  h.1.contains_eq

theorem mem_iff [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) : k ∈ m₁ ↔ k ∈ m₂ :=
  h.1.mem_iff

theorem toList_perm (h : m₁ ~m m₂) : m₁.toList.Perm m₂.toList :=
  h.1.keys_perm

theorem of_toList_perm (h : m₁.toList.Perm m₂.toList) : m₁ ~m m₂ :=
  ⟨.of_keys_unit_perm h⟩

theorem get?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁.get? k = m₂.get? k :=
  h.1.getKey?_eq

theorem get_eq [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁ ~m m₂) :
    m₁.get k hk = m₂.get k (h.mem_iff.mp hk) :=
  h.1.getKey_eq hk

theorem get!_eq [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h : m₁ ~m m₂) :
    m₁.get! k = m₂.get! k :=
  h.1.getKey!_eq

theorem getD_eq [EquivBEq α] [LawfulHashable α] {k fallback : α} (h : m₁ ~m m₂) :
    m₁.getD k fallback = m₂.getD k fallback :=
  h.1.getKeyD_eq

theorem insert [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁ ~m m₂) :
    m₁.insert k ~m m₂.insert k :=
  ⟨h.1.insertIfNew k ()⟩

theorem erase [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁ ~m m₂) :
    m₁.erase k ~m m₂.erase k :=
  ⟨h.1.erase k⟩

theorem insertMany_list [EquivBEq α] [LawfulHashable α] (l : List α) (h : m₁ ~m m₂) :
    m₁.insertMany l ~m m₂.insertMany l :=
  ⟨h.1.insertManyIfNewUnit_list l⟩

theorem filter (f : α → Bool) (h : m₁ ~m m₂) : m₁.filter f ~m m₂.filter f :=
  ⟨h.1.filter _⟩

theorem of_forall_get?_eq [EquivBEq α] [LawfulHashable α]
    (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ ~m m₂ :=
  ⟨.of_forall_getKey?_unit_eq h⟩

theorem of_forall_contains_eq [LawfulBEq α] (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ ~m m₂ :=
  ⟨.of_forall_contains_unit_eq h⟩

theorem of_forall_mem_iff [LawfulBEq α] (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ ~m m₂ :=
  ⟨.of_forall_mem_unit_iff h⟩

end Equiv

section Equiv

variable {m m₁ m₂ : HashSet α}

@[simp]
theorem equiv_emptyWithCapacity_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} :
    m ~m emptyWithCapacity c ↔ m.isEmpty :=
  ⟨fun ⟨h⟩ => HashMap.equiv_emptyWithCapacity_iff_isEmpty.mp h,
    fun h => ⟨HashMap.equiv_emptyWithCapacity_iff_isEmpty.mpr h⟩⟩

@[simp]
theorem equiv_empty_iff_isEmpty [EquivBEq α] [LawfulHashable α] : m ~m ∅ ↔ m.isEmpty :=
  equiv_emptyWithCapacity_iff_isEmpty

@[simp]
theorem emptyWithCapacity_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} :
    emptyWithCapacity c ~m m ↔ m.isEmpty :=
  Equiv.comm.trans equiv_emptyWithCapacity_iff_isEmpty

@[simp]
theorem empty_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] : ∅ ~m m ↔ m.isEmpty :=
  emptyWithCapacity_equiv_iff_isEmpty

theorem equiv_iff_toList_perm [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ m₁.toList.Perm m₂.toList :=
  ⟨Equiv.toList_perm, Equiv.of_toList_perm⟩

end Equiv

section filter

variable {m : HashSet α}

theorem toList_filter {f : α → Bool} :
    (m.filter f).toList.Perm (m.toList.filter f) :=
  HashMap.keys_filter_key

@[grind =] theorem isEmpty_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter f).isEmpty ↔ ∀ k h, f (m.get k h) = false :=
  HashMap.isEmpty_filter_iff

theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter f).isEmpty = false ↔ ∃ k h, f (m.get k h) :=
  HashMap.isEmpty_filter_eq_false_iff

-- TODO: `contains_filter` is missing.

@[simp, grind =]
theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ h, f (m.get k h) :=
  HashMap.mem_filter

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter f).contains k → m.contains k :=
  HashMap.contains_of_contains_filter

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    k ∈ m.filter f → k ∈ m :=
  HashMap.mem_of_mem_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter f).size ≤ m.size :=
  HashMap.size_filter_le_size

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f (m.get k h) :=
  HashMap.size_filter_eq_size_iff

theorem filter_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    m.filter f ~m m ↔ ∀ k h, f (m.get k h) :=
  ⟨fun h => HashMap.filter_equiv_self_iff.mp h.1,
    fun h => ⟨HashMap.filter_equiv_self_iff.mpr h⟩⟩

@[simp, grind =]
theorem get?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter f).get? k = (m.get? k).filter f :=
  HashMap.getKey?_filter_key

@[simp, grind =]
theorem get_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} {h} :
    (m.filter f).get k h = m.get k (mem_of_mem_filter h) :=
  HashMap.getKey_filter

@[grind =]
theorem get!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter f).get! k = ((m.get? k).filter f).get! :=
  HashMap.getKey!_filter_key

@[grind =]
theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} :
    (m.filter f).getD k fallback = ((m.get? k).filter f).getD fallback :=
  HashMap.getKeyD_filter_key

end filter
attribute [simp] contains_eq_false_iff_not_mem
end Std.HashSet
