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

variable {α : Type u} {_ : BEq α} {_ : Hashable α} [EquivBEq α] [LawfulHashable α]

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

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a = (a == k || m.contains a) :=
  HashMap.contains_insertIfNew

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ a == k ∨ a ∈ m :=
  HashMap.mem_insertIfNew

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → (a == k) = false → m.contains a :=
  HashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → (a == k) = false → a ∈ m :=
  HashMap.mem_of_mem_insertIfNew

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
    (m.insert k).size = bif m.contains k then m.size else m.size + 1 :=
  HashMap.size_insertIfNew

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  HashMap.size_le_size_insertIfNew

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
    (m.erase k).contains a = (!(a == k) && m.contains a) :=
  HashMap.contains_erase

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (a == k) = false ∧ a ∈ m :=
  HashMap.mem_erase

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  HashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m :=
  HashMap.mem_of_mem_erase

theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = bif m.contains k then m.size - 1 else m.size :=
  HashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  HashMap.size_erase_le

@[simp]
theorem containsThenInsert_fst {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsert_snd {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext HashMap.containsThenInsertIfNew_snd

end

end Std.HashSet
