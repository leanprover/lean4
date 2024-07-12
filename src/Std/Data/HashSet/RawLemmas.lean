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

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace Std.HashSet

namespace Raw

variable {m : Raw α} (h : m.WF)

private theorem ext {m m' : Raw α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α).isEmpty :=
  HashMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {a : α} : (m.insert a).isEmpty = false :=
  HashMap.Raw.isEmpty_insertIfNew h.out

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  HashMap.Raw.mem_iff_contains

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  HashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  HashMap.Raw.mem_congr h.out hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α).contains a = false :=
  HashMap.Raw.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α) :=
  HashMap.Raw.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α).contains a = false :=
  HashMap.Raw.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α) :=
  HashMap.Raw.not_mem_emptyc

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a = (k == a || m.contains a) :=
  HashMap.Raw.contains_insertIfNew h.out

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ k == a ∨ a ∈ m :=
  HashMap.Raw.mem_insertIfNew h.out

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → (k == a) = false → m.contains a :=
  HashMap.Raw.contains_of_contains_insertIfNew h.out

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → (k == a) = false → a ∈ m :=
  HashMap.Raw.mem_of_mem_insertIfNew h.out

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α}  : (m.insert k).contains k :=
  HashMap.Raw.contains_insertIfNew_self h.out

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k :=
  HashMap.Raw.mem_insertIfNew_self h.out

@[simp]
theorem size_empty {c} : (empty c : Raw α).size = 0 :=
  HashMap.Raw.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α).size = 0 :=
  HashMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  HashMap.Raw.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size = bif m.contains k then m.size else m.size + 1 :=
  HashMap.Raw.size_insertIfNew h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  HashMap.Raw.size_le_size_insertIfNew h.out

@[simp]
theorem remove_empty {k : α} {c : Nat} : (empty c : Raw α).remove k = empty c :=
  ext HashMap.Raw.remove_empty

@[simp]
theorem remove_emptyc {k : α} : (∅ : Raw α).remove k = ∅ :=
  ext HashMap.Raw.remove_emptyc

@[simp]
theorem isEmpty_remove [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.remove k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  HashMap.Raw.isEmpty_remove h.out

@[simp]
theorem contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.remove k).contains a = (!(k == a) && m.contains a) :=
  HashMap.Raw.contains_remove h.out

@[simp]
theorem mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.remove k ↔ (k == a) = false ∧ a ∈ m :=
  HashMap.Raw.mem_remove h.out

theorem contains_of_contains_remove [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.remove k).contains a → m.contains a :=
  HashMap.Raw.contains_of_contains_remove h.out

theorem mem_of_mem_remove [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.remove k → a ∈ m :=
  HashMap.Raw.mem_of_mem_remove h.out

theorem size_remove [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.remove k).size = bif m.contains k then m.size - 1 else m.size :=
  HashMap.Raw.size_remove h.out

theorem size_remove_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.remove k).size ≤ m.size :=
  HashMap.Raw.size_remove_le h.out

@[simp]
theorem containsThenInsert_fst {k : α} : (m.containsThenInsert k).1 = m.contains k :=
  HashMap.Raw.containsThenInsertIfNew_fst h.out

@[simp]
theorem containsThenInsert_snd {k : α} : (m.containsThenInsert k).2 = m.insert k :=
  ext (HashMap.Raw.containsThenInsertIfNew_snd h.out)

end Raw

end Std.HashSet
