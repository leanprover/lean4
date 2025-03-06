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

@[simp] theorem insert_eq_insert {a : α} : Insert.insert a m = m.insert a := rfl

@[simp] theorem singleton_eq_insert {a : α} : Singleton.singleton a = (∅ : Raw α).insert a := rfl

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
theorem get?_empty {a : α} {c} : (empty c : Raw α).get? a = none :=
  HashMap.Raw.getKey?_empty

@[simp]
theorem get?_emptyc {a : α} : (∅ : Raw α).get? a = none :=
  HashMap.Raw.getKey?_emptyc

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.get? a = none :=
  HashMap.Raw.getKey?_of_isEmpty h.out

theorem get?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).get? a = if k == a ∧ ¬k ∈ m then some k else m.get? a :=
  HashMap.Raw.getKey?_insertIfNew h.out

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (m.get? a).isSome :=
  HashMap.Raw.contains_eq_isSome_getKey? h.out

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.get? a = none :=
  HashMap.Raw.getKey?_eq_none_of_contains_eq_false h.out

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.get? a = none :=
  HashMap.Raw.getKey?_eq_none h.out

theorem get?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
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

theorem get_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h₁} :
    (m.insert k).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.get a (mem_of_mem_insert' h h₁ h₂) :=
  HashMap.Raw.getKey_insertIfNew (h₁ := h₁) h.out

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h h') :=
  HashMap.Raw.getKey_erase (h' := h') h.out

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h' : a ∈ m} :
    m.get? a = some (m.get a h') :=
  @HashMap.Raw.getKey?_eq_some_getKey _ _ _ _ _ _ _ h.out _ h'

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

theorem get_eq [LawfulBEq α] (h : m.WF) {k : α} (h' : m.contains k) :
    m.get k h' = k :=
  HashMap.Raw.getKey_eq h.out h'

@[simp]
theorem get!_empty [Inhabited α] {a : α} {c} : (empty c : Raw α).get! a = default :=
  HashMap.Raw.getKey!_empty

@[simp]
theorem get!_emptyc [Inhabited α] {a : α} : (∅ : Raw α).get! a = default :=
  HashMap.Raw.getKey!_emptyc

theorem get!_of_isEmpty [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.get! a = default :=
  HashMap.Raw.getKey!_of_isEmpty h.out

theorem get!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.insert k).get! a = if k == a ∧ ¬k ∈ m then k else m.get! a :=
  HashMap.Raw.getKey!_insertIfNew h.out

theorem get!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {a : α} :
    m.contains a = false → m.get! a = default :=
  HashMap.Raw.getKey!_eq_default_of_contains_eq_false h.out

theorem get!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.get! a = default :=
  HashMap.Raw.getKey!_eq_default h.out

theorem get!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
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

@[simp]
theorem getD_empty {a fallback : α} {c} : (empty c : Raw α).getD a fallback = fallback :=
  HashMap.Raw.getKeyD_empty

@[simp]
theorem getD_emptyc {a fallback : α} : (∅ : Raw α).getD a fallback = fallback :=
  HashMap.Raw.getKeyD_emptyc

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  HashMap.Raw.getKeyD_of_isEmpty h.out

theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.insert k).getD a fallback = if k == a ∧ ¬k ∈ m then k else m.getD a fallback :=
  HashMap.Raw.getKeyD_insertIfNew h.out

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} :
    m.contains a = false → m.getD a fallback = fallback :=
  HashMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h.out

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  HashMap.Raw.getKeyD_eq_fallback h.out

theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
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

@[simp]
theorem containsThenInsert_fst (h : m.WF) {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.Raw.containsThenInsertIfNew_fst h.out

@[simp]
theorem containsThenInsert_snd (h : m.WF) {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext (HashMap.Raw.containsThenInsertIfNew_snd h.out)

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.length = m.size :=
  HashMap.Raw.length_keys h.1

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.isEmpty = m.isEmpty :=
  HashMap.Raw.isEmpty_keys h.1

@[simp]
theorem contains_toList [EquivBEq α] [LawfulHashable α] {k : α} (h : m.WF) :
    m.toList.contains k = m.contains k :=
  HashMap.Raw.contains_keys h.1

@[simp]
theorem mem_toList [LawfulBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    k ∈ m.toList ↔ k ∈ m :=
  HashMap.Raw.mem_keys h.1

theorem distinct_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.Pairwise (fun a b => (a == b) = false) :=
  HashMap.Raw.distinct_keys h.1

section monadic

variable {m : Raw α} {δ : Type v} {m' : Type v → Type v}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → α → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM f init :=
  HashMap.Raw.foldM_eq_foldlM_keys h.out

theorem fold_eq_foldl_toList (h : m.WF) {f : δ → α → δ} {init : δ} :
    m.fold f init = m.toList.foldl f init :=
  HashMap.Raw.fold_eq_foldl_keys h.out

omit [BEq α] [Hashable α] in
@[simp]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.forM f = ForM.forM m f := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] (h : m.WF) {f : α → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  HashMap.Raw.forM_eq_forM_keys h.out

omit [BEq α] [Hashable α] in
@[simp]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn m init f := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  HashMap.Raw.forIn_eq_forIn_keys h.out

end monadic

@[simp]
theorem insertMany_nil (h : m.WF) :
    insertMany m [] = m :=
  ext (HashMap.Raw.insertManyIfNewUnit_nil h.1)

@[simp]
theorem insertMany_list_singleton (h : m.WF) {k : α} :
    insertMany m [k] = m.insert k :=
  ext (HashMap.Raw.insertManyIfNewUnit_list_singleton h.1)

theorem insertMany_cons (h : m.WF) {l : List α} {k : α} :
    insertMany m (k :: l) = insertMany (m.insert k) l :=
  ext (HashMap.Raw.insertManyIfNewUnit_cons h.1)

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    (insertMany m l).contains k = (m.contains k || l.contains k) :=
  HashMap.Raw.contains_insertManyIfNewUnit_list h.1

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ l.contains k :=
  HashMap.Raw.mem_insertManyIfNewUnit_list h.1

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany m l → k ∈ m :=
  HashMap.Raw.mem_of_mem_insertManyIfNewUnit_list h.1 contains_eq_false

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

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertMany m l).size ≤ m.size + l.length :=
  HashMap.Raw.size_insertManyIfNewUnit_list_le h.1

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  HashMap.Raw.isEmpty_insertManyIfNewUnit_list h.1

@[simp]
theorem ofList_nil :
    ofList ([] : List α) = ∅ :=
  ext HashMap.Raw.unitOfList_nil

@[simp]
theorem ofList_singleton {k : α} :
    ofList [k] = (∅ : Raw α).insert k :=
  ext HashMap.Raw.unitOfList_singleton

theorem ofList_cons {hd : α} {tl : List α} :
    ofList (hd :: tl) = insertMany ((∅ : Raw α).insert hd) tl :=
  ext HashMap.Raw.unitOfList_cons

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (ofList l).contains k = l.contains k :=
  HashMap.Raw.contains_unitOfList

@[simp]
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

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (ofList l).isEmpty = l.isEmpty :=
  HashMap.Raw.isEmpty_unitOfList

end Raw

end Std.HashSet
