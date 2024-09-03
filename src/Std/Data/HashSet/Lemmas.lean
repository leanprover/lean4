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
obligation in the statement of `getKey_insert`. -/
theorem contains_of_contains_insert' [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  HashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_insert` that is written to exactly match the proof obligation
in the statement of `getKey_insert`. -/
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
theorem getKey?_empty {a : α} {c} : (empty c : HashSet α).getKey? a = none :=
  HashMap.getKey?_empty

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : HashSet α).getKey? a = none :=
  HashMap.getKey?_emptyc

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  HashMap.getKey?_of_isEmpty

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).getKey? a = if k == a ∧ ¬k ∈ m then some k else m.getKey? a :=
  HashMap.getKey?_insertIfNew

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  HashMap.contains_eq_isSome_getKey?

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey? a = none :=
  HashMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none :=
  HashMap.getKey?_eq_none

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  HashMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).getKey? k = none :=
  HashMap.getKey?_erase_self

theorem getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {h₁} :
    (m.insert k).getKey a h₁ =
      if h₂ : k == a ∧ ¬ k ∈ m then k else m.getKey a (mem_of_mem_insert' h₁ h₂) :=
  HashMap.getKey_insertIfNew (h₁ := h₁)

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  HashMap.getKey_erase (h' := h')

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α} {h' : a ∈ m} :
    m.getKey? a = some (m.getKey a h') :=
  @HashMap.getKey?_eq_some_getKey _ _ _ _ _ _ _ _ h'

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} {c} : (empty c : HashSet α).getKey! a = default :=
  HashMap.getKey!_empty

@[simp]
theorem getKey!_emptyc [Inhabited α] {a : α} : (∅ : HashSet α).getKey! a = default :=
  HashMap.getKey!_emptyc

theorem getKey!_of_isEmpty [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  HashMap.getKey!_of_isEmpty

theorem getKey!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).getKey! a = if k == a ∧ ¬k ∈ m then k else m.getKey! a :=
  HashMap.getKey!_insertIfNew

theorem getKey!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey! a = default :=
  HashMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  HashMap.getKey!_eq_default

theorem getKey!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  HashMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).getKey! k = default :=
  HashMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  HashMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  HashMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  HashMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h'} :
    m.getKey a h' = m.getKey! a :=
  HashMap.getKey_eq_getKey!

@[simp]
theorem getKeyD_empty {a fallback : α} {c} : (empty c : HashSet α).getKeyD a fallback = fallback :=
  HashMap.getKeyD_empty

@[simp]
theorem getKeyD_emptyc {a fallback : α} : (∅ : HashSet α).getKeyD a fallback = fallback :=
  HashMap.getKeyD_emptyc

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  HashMap.getKeyD_of_isEmpty

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.insert k).getKeyD a fallback = if k == a ∧ ¬k ∈ m then k else m.getKeyD a fallback :=
  HashMap.getKeyD_insertIfNew

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {a fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback :=
  HashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  HashMap.getKeyD_eq_fallback

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  HashMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  HashMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  HashMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  HashMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  HashMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] {a fallback : α} {h'} :
    m.getKey a h' = m.getKeyD a fallback :=
  @HashMap.getKey_eq_getKeyD _ _ _ _ _ _ _ _ _ h'

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = m.getKeyD a default :=
  HashMap.getKey!_eq_getKeyD_default

@[simp]
theorem containsThenInsert_fst {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsert_snd {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext HashMap.containsThenInsertIfNew_snd

end

end Std.HashSet
