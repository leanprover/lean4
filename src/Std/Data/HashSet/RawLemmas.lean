/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.HashMap.RawLemmas
import Std.Data.HashSet.Raw

/-!
# Hash set lemmas

This module contains lemmas about `Std.Data.HashSet.Raw`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u}

namespace Std.HashSet

namespace Raw

variable {m : Raw α}

private theorem ext {m m' : Raw α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem size_empty {c} : (empty c : Raw α).size = 0 :=
  HashMap.Raw.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α).size = 0 :=
  HashMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.Raw.isEmpty_eq_size_eq_zero

variable [BEq α] [Hashable α]

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.insert a).isEmpty = false :=
  HashMap.Raw.isEmpty_insertIfNew h.out

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.Raw.mem_iff_contains

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  HashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m :=
  HashMap.Raw.mem_congr h.out hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α).contains a = false :=
  HashMap.Raw.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α) :=
  HashMap.Raw.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α).contains a = false :=
  HashMap.Raw.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α) :=
  HashMap.Raw.not_mem_emptyc

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

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).contains a = (k == a || m.contains a) :=
  HashMap.Raw.contains_insertIfNew h.out

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.insert k ↔ k == a ∨ a ∈ m :=
  HashMap.Raw.mem_insertIfNew h.out

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).contains a → (k == a) = false → m.contains a :=
  HashMap.Raw.contains_of_contains_insertIfNew h.out

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.insert k → (k == a) = false → a ∈ m :=
  HashMap.Raw.mem_of_mem_insertIfNew h.out

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).contains k :=
  HashMap.Raw.contains_insertIfNew_self h.out

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} : k ∈ m.insert k :=
  HashMap.Raw.mem_insertIfNew_self h.out

theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).size = if k ∈ m then m.size else m.size + 1 :=
  HashMap.Raw.size_insertIfNew h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.insert k).size :=
  HashMap.Raw.size_le_size_insertIfNew h.out

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.insert k).size ≤ m.size + 1 :=
  HashMap.Raw.size_insertIfNew_le h.out

@[simp]
theorem erase_empty {k : α} {c : Nat} : (empty c : Raw α).erase k = empty c :=
  ext HashMap.Raw.erase_empty

@[simp]
theorem erase_emptyc {k : α} : (∅ : Raw α).erase k = ∅ :=
  ext HashMap.Raw.erase_emptyc

@[simp]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.Raw.isEmpty_erase h.out

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  HashMap.Raw.contains_erase h.out

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  HashMap.Raw.mem_erase h.out

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a → m.contains a :=
  HashMap.Raw.contains_of_contains_erase h.out

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k → a ∈ m :=
  HashMap.Raw.mem_of_mem_erase h.out

theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  HashMap.Raw.size_erase h.out

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size ≤ m.size :=
  HashMap.Raw.size_erase_le h.out

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  HashMap.Raw.size_le_size_erase h.out

@[simp]
theorem getKey?_empty {a : α} {c} : (empty c : Raw α).getKey? a = none :=
  HashMap.Raw.getKey?_empty

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : Raw α).getKey? a = none :=
  HashMap.Raw.getKey?_emptyc

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  HashMap.Raw.getKey?_of_isEmpty h.out

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).getKey? a = if k == a ∧ ¬k ∈ m then some k else m.getKey? a :=
  HashMap.Raw.getKey?_insertIfNew h.out

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  HashMap.Raw.contains_eq_isSome_getKey? h.out

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.getKey? a = none :=
  HashMap.Raw.getKey?_eq_none_of_contains_eq_false h.out

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey? a = none :=
  HashMap.Raw.getKey?_eq_none h.out

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  HashMap.Raw.getKey?_erase h.out

theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h₁} :
    (m.insert k).getKey a h₁ =
      if h₂ : k == a then k else m.getKey a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) :=
  sorry
  --HashMap.Raw.getKey_insertIfNew (h₁ := h₁) h.out

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h h') :=
  HashMap.Raw.getKey_erase (h' := h') h.out

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h' : a ∈ m} :
    m.getKey? a = some (m.getKey a h') :=
  @HashMap.Raw.getKey?_eq_some_getKey _ _ _ _ _ _ _ h.out _ h'

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).getKey? k = none :=
  HashMap.Raw.getKey?_erase_self h.out

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} {c} : (empty c : Raw α).getKey! a = default :=
  HashMap.Raw.getKey!_empty

@[simp]
theorem getKey!_emptyc [Inhabited α] {a : α} : (∅ : Raw α).getKey! a = default :=
  HashMap.Raw.getKey!_emptyc

theorem getKey!_of_isEmpty [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  HashMap.Raw.getKey!_of_isEmpty h.out

theorem getKey!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).getKey! a = if k == a ∧ ¬k ∈ m then some k else m.getKey! a :=
  sorry
  --HashMap.Raw.getKey!_insertIfNew h.out

theorem getKey!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.getKey! a = default :=
  HashMap.Raw.getKey!_eq_default_of_contains_eq_false h.out

theorem getKey!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  HashMap.Raw.getKey!_eq_default h.out

theorem getKey!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  HashMap.Raw.getKey!_erase h.out

@[simp]
theorem getKey!_erase_self [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).getKey! k = default :=
  HashMap.Raw.getKey!_erase_self h.out

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {a : α} : m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  HashMap.Raw.getKey?_eq_some_getKey!_of_contains h.out

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  HashMap.Raw.getKey?_eq_some_getKey! h.out

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  HashMap.Raw.getKey!_eq_get!_getKey? h.out

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} {h'} :
    m.getKey a h' = m.getKey! a :=
  HashMap.Raw.getKey_eq_getKey! h.out

@[simp]
theorem getKeyD_empty {a fallback : α} {c} : (empty c : Raw α).getKeyD a fallback = fallback :=
  HashMap.Raw.getKeyD_empty

@[simp]
theorem getKeyD_emptyc {a fallback : α} : (∅ : Raw α).getKeyD a fallback = fallback :=
  HashMap.Raw.getKeyD_emptyc

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  HashMap.Raw.getKeyD_of_isEmpty h.out

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.insert k).getKeyD a fallback = if k == a ∧ ¬k ∈ m then some k else m.getKeyD a fallback :=
  sorry
  --HashMap.Raw.getKeyD_insertIfNew h.out

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback :=
  HashMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h.out

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  HashMap.Raw.getKeyD_eq_fallback h.out

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  HashMap.Raw.getKeyD_erase h.out

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  HashMap.Raw.getKeyD_erase_self h.out

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α}
    {fallback : α} : m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  HashMap.Raw.getKey?_eq_some_getKeyD_of_contains h.out

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  HashMap.Raw.getKey?_eq_some_getKeyD h.out

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  HashMap.Raw.getKeyD_eq_getD_getKey? h.out

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : α} {h'} :
    m.getKey a h' = m.getKeyD a fallback :=
  @HashMap.Raw.getKey_eq_getKeyD _ _ _ _ _ _ _ h.out _ _ h'

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {a : α} :
    m.getKey! a = m.getKeyD a default :=
  HashMap.Raw.getKey!_eq_getKeyD_default h.out

@[simp]
theorem containsThenInsert_fst (h : m.WF) {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.Raw.containsThenInsertIfNew_fst h.out

@[simp]
theorem containsThenInsert_snd (h : m.WF) {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext (HashMap.Raw.containsThenInsertIfNew_snd h.out)

end Raw

end Std.HashSet
