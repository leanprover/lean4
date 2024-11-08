/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Basic

/-!
# Hash set lemmas

This module contains lemmas about `Std.Data.HashSet`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {_ : BEq α} {_ : Hashable α}

namespace Std.HashSet

section

variable {m : HashSet α}

private theorem ext {m m' : HashSet α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_empty {c} : (empty c : HashSet α).isEmpty :=
  HashMap.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : HashSet α).isEmpty :=
  HashMap.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} : (m.insert a).isEmpty = false :=
  HashMap.isEmpty_insertIfNew

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.mem_iff_contains

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  HashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  HashMap.mem_congr hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : HashSet α).contains a = false :=
  HashMap.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : HashSet α) :=
  HashMap.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : HashSet α).contains a = false :=
  HashMap.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : HashSet α) :=
  HashMap.not_mem_emptyc

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

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a = (k == a || m.contains a) :=
  HashMap.contains_insertIfNew

@[simp]
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

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α}  : (m.insert k).contains k :=
  HashMap.contains_insertIfNew_self

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k :=
  HashMap.mem_insertIfNew_self

@[simp]
theorem size_empty {c} : (empty c : HashSet α).size = 0 :=
  HashMap.size_empty

@[simp]
theorem size_emptyc : (∅ : HashSet α).size = 0 :=
  HashMap.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size = if k ∈ m then m.size else m.size + 1 :=
  HashMap.size_insertIfNew

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  HashMap.size_le_size_insertIfNew

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size ≤ m.size + 1 :=
  HashMap.size_insertIfNew_le

@[simp]
theorem erase_empty {a : α} {c : Nat} : (empty c : HashSet α).erase a = empty c :=
  ext HashMap.erase_empty

@[simp]
theorem erase_emptyc {a : α} : (∅ : HashSet α).erase a = ∅ :=
  ext HashMap.erase_emptyc

@[simp]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.isEmpty_erase

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  HashMap.contains_erase

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  HashMap.mem_erase

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  HashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m :=
  HashMap.mem_of_mem_erase

theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  HashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  HashMap.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  HashMap.size_le_size_erase

@[simp]
theorem get?_empty {a : α} {c} : (empty c : HashSet α).get? a = none :=
  HashMap.getKey?_empty

@[simp]
theorem get?_emptyc {a : α} : (∅ : HashSet α).get? a = none :=
  HashMap.getKey?_emptyc

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.get? a = none :=
  HashMap.getKey?_of_isEmpty

theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).get? a = if k == a ∧ ¬k ∈ m then some k else m.get? a :=
  HashMap.getKey?_insertIfNew

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.get? a).isSome :=
  HashMap.contains_eq_isSome_getKey?

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.get? a = none :=
  HashMap.getKey?_eq_none_of_contains_eq_false

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.get? a = none :=
  HashMap.getKey?_eq_none

theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  HashMap.getKey?_erase

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).get? k = none :=
  HashMap.getKey?_erase_self

theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {h₁} :
    (m.insert k).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.get a (mem_of_mem_insert' h₁ h₂) :=
  HashMap.getKey_insertIfNew (h₁ := h₁)

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  HashMap.getKey_erase (h' := h')

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} {h' : a ∈ m} :
    m.get? a = some (m.get a h') :=
  @HashMap.getKey?_eq_some_getKey _ _ _ _ _ _ _ _ h'

@[simp]
theorem get!_empty [Inhabited α] {a : α} {c} : (empty c : HashSet α).get! a = default :=
  HashMap.getKey!_empty

@[simp]
theorem get!_emptyc [Inhabited α] {a : α} : (∅ : HashSet α).get! a = default :=
  HashMap.getKey!_emptyc

theorem get!_of_isEmpty [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.get! a = default :=
  HashMap.getKey!_of_isEmpty

theorem get!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).get! a = if k == a ∧ ¬k ∈ m then k else m.get! a :=
  HashMap.getKey!_insertIfNew

theorem get!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.get! a = default :=
  HashMap.getKey!_eq_default_of_contains_eq_false

theorem get!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    ¬a ∈ m → m.get! a = default :=
  HashMap.getKey!_eq_default

theorem get!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
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

@[simp]
theorem getD_empty {a fallback : α} {c} : (empty c : HashSet α).getD a fallback = fallback :=
  HashMap.getKeyD_empty

@[simp]
theorem getD_emptyc {a fallback : α} : (∅ : HashSet α).getD a fallback = fallback :=
  HashMap.getKeyD_emptyc

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  HashMap.getKeyD_of_isEmpty

theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.insert k).getD a fallback = if k == a ∧ ¬k ∈ m then k else m.getD a fallback :=
  HashMap.getKeyD_insertIfNew

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {a fallback : α} :
    m.contains a = false → m.getD a fallback = fallback :=
  HashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  HashMap.getKeyD_eq_fallback

theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
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

@[simp]
theorem containsThenInsert_fst {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsert_snd {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext HashMap.containsThenInsertIfNew_snd

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] : 
    m.toList.length = m.size :=
  HashMap.length_keys

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.isEmpty = m.isEmpty :=
  HashMap.isEmpty_keys

@[simp]
theorem contains_toList [EquivBEq α] [LawfulHashable α] {k : α}:
    m.toList.contains k = m.contains k :=
  HashMap.contains_keys

@[simp]
theorem mem_toList [LawfulBEq α] [LawfulHashable α]  {k : α}:
    k ∈ m.toList ↔ k ∈ m :=
  HashMap.mem_keys

theorem distinct_toList [EquivBEq α] [LawfulHashable α]:
    m.toList.Pairwise (fun a b => (a == b) = false) :=
  HashMap.distinct_keys
end

end Std.HashSet
