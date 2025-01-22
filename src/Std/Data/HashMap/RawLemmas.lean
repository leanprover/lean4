/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.RawLemmas
import Std.Data.HashMap.Raw

/-!
# Hash map lemmas

This module contains lemmas about `Std.Data.HashMap.Raw`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace Std.HashMap

namespace Raw

variable {m : Raw α β}

@[simp]
theorem size_empty {c} : (empty c : Raw α β).size = 0 :=
  DHashMap.Raw.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α β).size = 0 :=
  DHashMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  DHashMap.Raw.isEmpty_eq_size_eq_zero

private theorem ext {m m' : Raw α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

variable [BEq α] [Hashable α]

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty :=
  DHashMap.Raw.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  DHashMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).isEmpty = false :=
  DHashMap.Raw.isEmpty_insert h.out

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  DHashMap.Raw.mem_iff_contains

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  DHashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m :=
  DHashMap.Raw.mem_congr h.out hab

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α β).contains a = false :=
  DHashMap.Raw.contains_empty

@[simp] theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
@[simp] theorem get?_eq_getElem? {a : α} : get? m a = m[a]? := rfl
@[simp] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! m a = m[a]! := rfl

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α β) :=
  DHashMap.Raw.not_mem_empty

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  DHashMap.Raw.contains_emptyc

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α β) :=
  DHashMap.Raw.not_mem_emptyc

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty → m.contains a = false :=
  DHashMap.Raw.contains_of_isEmpty h.out

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty → ¬a ∈ m :=
  DHashMap.Raw.not_mem_of_isEmpty h.out

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = false ↔ ∃ a, m.contains a = true :=
  DHashMap.Raw.isEmpty_eq_false_iff_exists_contains_eq_true h.out

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = false ↔ ∃ a, a ∈ m :=
  DHashMap.Raw.isEmpty_eq_false_iff_exists_mem h.out

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = true ↔ ∀ a, m.contains a = false :=
  DHashMap.Raw.isEmpty_iff_forall_contains h.out

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m :=
  DHashMap.Raw.isEmpty_iff_forall_not_mem h.out

@[simp] theorem insert_eq_insert {p : α × β} : Insert.insert p m = m.insert p.1 p.2 := rfl

@[simp] theorem singleton_eq_insert {p : α × β} :
    Singleton.singleton p = (∅ : Raw α β).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  DHashMap.Raw.contains_insert h.out

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m :=
  DHashMap.Raw.mem_insert h.out

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  DHashMap.Raw.contains_of_contains_insert h.out

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m :=
  DHashMap.Raw.mem_of_mem_insert h.out

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).contains k :=
  DHashMap.Raw.contains_insert_self h.out

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    k ∈ m.insert k v :=
  DHashMap.Raw.mem_insert_self h.out

theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  DHashMap.Raw.size_insert h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    m.size ≤ (m.insert k v).size :=
  DHashMap.Raw.size_le_size_insert h.out

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).size ≤ m.size + 1 :=
  DHashMap.Raw.size_insert_le h.out

@[simp]
theorem erase_empty {k : α} {c : Nat} : (empty c : Raw α β).erase k = empty c :=
  ext DHashMap.Raw.erase_empty

@[simp]
theorem erase_emptyc {k : α} : (∅ : Raw α β).erase k = ∅ :=
  ext DHashMap.Raw.erase_emptyc

@[simp]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  DHashMap.Raw.isEmpty_erase h.out

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  DHashMap.Raw.contains_erase h.out

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  DHashMap.Raw.mem_erase h.out

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a → m.contains a :=
  DHashMap.Raw.contains_of_contains_erase h.out

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k → a ∈ m :=
  DHashMap.Raw.mem_of_mem_erase h.out

theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  DHashMap.Raw.size_erase h.out

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size ≤ m.size :=
  DHashMap.Raw.size_erase_le h.out

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  DHashMap.Raw.size_le_size_erase h.out

@[simp]
theorem containsThenInsert_fst (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsert k v).1 = m.contains k :=
  DHashMap.Raw.containsThenInsert_fst h.out

@[simp]
theorem containsThenInsert_snd (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsert k v).2 = m.insert k v :=
  ext (DHashMap.Raw.containsThenInsert_snd h.out)

@[simp]
theorem containsThenInsertIfNew_fst (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  DHashMap.Raw.containsThenInsertIfNew_fst h.out

@[simp]
theorem containsThenInsertIfNew_snd (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  ext (DHashMap.Raw.containsThenInsertIfNew_snd h.out)

@[simp]
theorem getElem?_empty {a : α} {c} : (empty c : Raw α β)[a]? = none :=
  DHashMap.Raw.Const.get?_empty

@[simp]
theorem getElem?_emptyc {a : α} : (∅ : Raw α β)[a]? = none :=
  DHashMap.Raw.Const.get?_emptyc

theorem getElem?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m[a]? = none :=
  DHashMap.Raw.Const.get?_of_isEmpty h.out

theorem getElem?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  DHashMap.Raw.Const.get?_insert h.out

@[simp]
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v)[k]? = some v :=
  DHashMap.Raw.Const.get?_insert_self h.out

theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = m[a]?.isSome :=
  DHashMap.Raw.Const.contains_eq_isSome_get? h.out

theorem getElem?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m[a]? = none :=
  DHashMap.Raw.Const.get?_eq_none_of_contains_eq_false h.out

theorem getElem?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m[a]? = none :=
  DHashMap.Raw.Const.get?_eq_none h.out

theorem getElem?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k)[a]? = if k == a then none else m[a]? :=
  DHashMap.Raw.Const.get?_erase h.out

@[simp]
theorem getElem?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k)[k]? = none :=
  DHashMap.Raw.Const.get?_erase_self h.out

theorem getElem?_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m[a]? = m[b]? :=
  DHashMap.Raw.Const.get?_congr h.out hab

theorem getElem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insert k v)[a]'h₁ =
      if h₂ : k == a then v else m[a]'(mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Raw.Const.get_insert (h₁ := h₁) h.out

@[simp]
theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v)[k]'(mem_insert_self h) = v :=
  DHashMap.Raw.Const.get_insert_self h.out

@[simp]
theorem getElem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k)[a]'h' = m[a]'(mem_of_mem_erase h h') :=
  DHashMap.Raw.Const.get_erase (h' := h') h.out

theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h' : a ∈ m} :
    m[a]? = some (m[a]'h') :=
  @DHashMap.Raw.Const.get?_eq_some_get _ _ _ _ _ _ _ h.out _ h'

theorem getElem_congr [LawfulBEq α] (h : m.WF) {a b : α} (hab : a == b) {h'} :
    m[a]'h' = m[b]'((mem_congr h hab).1 h') :=
  DHashMap.Raw.Const.get_congr h.out hab (h' := h')

@[simp]
theorem getElem!_empty [Inhabited β] {a : α} {c} : (empty c : Raw α β)[a]! = default :=
  DHashMap.Raw.Const.get!_empty

@[simp]
theorem getElem!_emptyc [Inhabited β] {a : α} : (∅ : Raw α β)[a]! = default :=
  DHashMap.Raw.Const.get!_emptyc

theorem getElem!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    m.isEmpty = true → m[a]! = default :=
  DHashMap.Raw.Const.get!_of_isEmpty h.out

theorem getElem!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v)[a]! = if k == a then v else m[a]! :=
  DHashMap.Raw.Const.get!_insert h.out

@[simp]
theorem getElem!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k : α}
    {v : β} : (m.insert k v)[k]! = v :=
  DHashMap.Raw.Const.get!_insert_self h.out

theorem getElem!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (h : m.WF) {a : α} : m.contains a = false → m[a]! = default :=
  DHashMap.Raw.Const.get!_eq_default_of_contains_eq_false h.out

theorem getElem!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    ¬a ∈ m → m[a]! = default :=
  DHashMap.Raw.Const.get!_eq_default h.out

theorem getElem!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α} :
    (m.erase k)[a]! = if k == a then default else m[a]! :=
  DHashMap.Raw.Const.get!_erase h.out

@[simp]
theorem getElem!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k : α} :
    (m.erase k)[k]! = default :=
  DHashMap.Raw.Const.get!_erase_self h.out

theorem getElem?_eq_some_getElem!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (h : m.WF) {a : α} : m.contains a = true → m[a]? = some m[a]! :=
  DHashMap.Raw.Const.get?_eq_some_get!_of_contains h.out

theorem getElem?_eq_some_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    a ∈ m → m[a]? = some m[a]! :=
  DHashMap.Raw.Const.get?_eq_some_get! h.out

theorem getElem!_eq_get!_getElem? [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    m[a]! = m[a]?.get! :=
  DHashMap.Raw.Const.get!_eq_get!_get? h.out

theorem getElem_eq_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} {h'} :
    m[a]'h' = m[a]! :=
  @DHashMap.Raw.Const.get_eq_get! _ _ _ _ _ _ _ _ h.out _ h'

theorem getElem!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a b : α}
    (hab : a == b) : m[a]! = m[b]! :=
  DHashMap.Raw.Const.get!_congr h.out hab

@[simp]
theorem getD_empty {a : α} {fallback : β} {c} : (empty c : Raw α β).getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_empty

@[simp]
theorem getD_emptyc {a : α} {fallback : β} : (∅ : Raw α β).getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_of_isEmpty h.out

theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback v : β} :
    (m.insert k v).getD a fallback = if k == a then v else m.getD a fallback :=
  DHashMap.Raw.Const.getD_insert h.out

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {fallback v : β} :
   (m.insert k v).getD k fallback = v :=
  DHashMap.Raw.Const.getD_insert_self h.out

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α}
    {fallback : β} : m.contains a = false → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_eq_fallback_of_contains_eq_false h.out

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_eq_fallback h.out

theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback : β} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  DHashMap.Raw.Const.getD_erase h.out

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {fallback : β} :
    (m.erase k).getD k fallback = fallback :=
  DHashMap.Raw.Const.getD_erase_self h.out

theorem getElem?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α}
    {fallback : β} : m.contains a = true → m[a]? = some (m.getD a fallback) :=
  DHashMap.Raw.Const.get?_eq_some_getD_of_contains h.out

theorem getElem?_eq_some_getD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    a ∈ m → m[a]? = some (m.getD a fallback) :=
  DHashMap.Raw.Const.get?_eq_some_getD h.out

theorem getD_eq_getD_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    m.getD a fallback = m[a]?.getD fallback :=
  DHashMap.Raw.Const.getD_eq_getD_get? h.out

theorem getElem_eq_getD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} {h'} :
    m[a]'h' = m.getD a fallback :=
  @DHashMap.Raw.Const.get_eq_getD _ _ _ _ _ _ _ h.out _ _ h'

theorem getElem!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    m[a]! = m.getD a default :=
  DHashMap.Raw.Const.get!_eq_getD_default h.out

theorem getD_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} {fallback : β}
    (hab : a == b) : m.getD a fallback = m.getD b fallback :=
  DHashMap.Raw.Const.getD_congr h.out hab

@[simp]
theorem getKey?_empty {a : α} {c} : (empty c : Raw α β).getKey? a = none :=
  DHashMap.Raw.getKey?_empty

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : Raw α β).getKey? a = none :=
  DHashMap.Raw.getKey?_emptyc

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  DHashMap.Raw.getKey?_of_isEmpty h.out

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  DHashMap.Raw.getKey?_insert h.out

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).getKey? k = some k :=
  DHashMap.Raw.getKey?_insert_self h.out

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  DHashMap.Raw.contains_eq_isSome_getKey? h.out

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.getKey? a = none :=
  DHashMap.Raw.getKey?_eq_none_of_contains_eq_false h.out

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey? a = none :=
  DHashMap.Raw.getKey?_eq_none h.out

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  DHashMap.Raw.getKey?_erase h.out

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).getKey? k = none :=
  DHashMap.Raw.getKey?_erase_self h.out

theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then k else m.getKey a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Raw.getKey_insert (h₁ := h₁) h.out

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).getKey k (mem_insert_self h) = k :=
  DHashMap.Raw.getKey_insert_self h.out

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h h') :=
  DHashMap.Raw.getKey_erase (h' := h') h.out

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h' : a ∈ m} :
    m.getKey? a = some (m.getKey a h') :=
  @DHashMap.Raw.getKey?_eq_some_getKey _ _ _ _ _ _ _ h.out _ h'

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} {c} : (empty c : Raw α β).getKey! a = default :=
  DHashMap.Raw.getKey!_empty

@[simp]
theorem getKey!_emptyc [Inhabited α] {a : α} : (∅ : Raw α β).getKey! a = default :=
  DHashMap.Raw.getKey!_emptyc

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  DHashMap.Raw.getKey!_of_isEmpty h.out

theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).getKey! a = if k == a then k else m.getKey! a :=
  DHashMap.Raw.getKey!_insert h.out

@[simp]
theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k : α}
    {v : β} : (m.insert k v).getKey! k = k :=
  DHashMap.Raw.getKey!_insert_self h.out

theorem getKey!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {a : α} : m.contains a = false → m.getKey! a = default :=
  DHashMap.Raw.getKey!_eq_default_of_contains_eq_false h.out

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  DHashMap.Raw.getKey!_eq_default h.out

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  DHashMap.Raw.getKey!_erase h.out

@[simp]
theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k : α} :
    (m.erase k).getKey! k = default :=
  DHashMap.Raw.getKey!_erase_self h.out

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {a : α} : m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  DHashMap.Raw.getKey?_eq_some_getKey!_of_contains h.out

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  DHashMap.Raw.getKey?_eq_some_getKey! h.out

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  DHashMap.Raw.getKey!_eq_get!_getKey? h.out

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} {h'} :
    m.getKey a h' = m.getKey! a :=
  DHashMap.Raw.getKey_eq_getKey! h.out

@[simp]
theorem getKeyD_empty {a fallback : α} {c} :
    (empty c : Raw α β).getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_empty

@[simp]
theorem getKeyD_emptyc {a fallback : α} : (∅ : Raw α β).getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_empty

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_of_isEmpty h.out

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} {v : β} :
    (m.insert k v).getKeyD a fallback = if k == a then k else m.getKeyD a fallback :=
  DHashMap.Raw.getKeyD_insert h.out

@[simp]
theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k fallback : α} {v : β} :
   (m.insert k v).getKeyD k fallback = k :=
  DHashMap.Raw.getKeyD_insert_self h.out

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} : m.contains a = false → m.getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h.out

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_eq_fallback h.out

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  DHashMap.Raw.getKeyD_erase h.out

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  DHashMap.Raw.getKeyD_erase_self h.out

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} : m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  DHashMap.Raw.getKey?_eq_some_getKeyD_of_contains h.out

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  DHashMap.Raw.getKey?_eq_some_getKeyD h.out

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  DHashMap.Raw.getKeyD_eq_getD_getKey? h.out

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} {h'} :
    m.getKey a h' = m.getKeyD a fallback :=
  @DHashMap.Raw.getKey_eq_getKeyD _ _ _ _ _ _ _ h.out _ _ h'

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {a : α} :
    m.getKey! a = m.getKeyD a default :=
  DHashMap.Raw.getKey!_eq_getKeyD_default h.out

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).isEmpty = false :=
  DHashMap.Raw.isEmpty_insertIfNew h.out

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  DHashMap.Raw.contains_insertIfNew h.out

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m :=
  DHashMap.Raw.mem_insertIfNew h.out

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).contains k :=
  DHashMap.Raw.contains_insertIfNew_self h.out

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    k ∈ m.insertIfNew k v :=
  DHashMap.Raw.mem_insertIfNew_self h.out

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α}
    {v : β} : (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  DHashMap.Raw.contains_of_contains_insertIfNew h.out

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m :=
  DHashMap.Raw.mem_of_mem_insertIfNew h.out

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `getElem_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α}
    {v : β} : (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  DHashMap.Raw.contains_of_contains_insertIfNew' h.out

/-- This is a restatement of `mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `getElem_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  DHashMap.Raw.mem_of_mem_insertIfNew' h.out

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  DHashMap.Raw.size_insertIfNew h.out

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    m.size ≤ (m.insertIfNew k v).size :=
  DHashMap.Raw.size_le_size_insertIfNew h.out

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  DHashMap.Raw.size_insertIfNew_le h.out

theorem getElem?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v)[a]? = if k == a ∧ ¬k ∈ m then some v else m[a]? :=
  DHashMap.Raw.Const.get?_insertIfNew h.out

theorem getElem_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insertIfNew k v)[a]'h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else m[a]'(mem_of_mem_insertIfNew' h h₁ h₂) :=
  DHashMap.Raw.Const.get_insertIfNew h.out (h₁ := h₁)

theorem getElem!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α}
    {v : β} : (m.insertIfNew k v)[a]! = if k == a ∧ ¬k ∈ m then v else m[a]! :=
  DHashMap.Raw.Const.get!_insertIfNew h.out

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback v : β} :
    (m.insertIfNew k v).getD a fallback =
      if k == a ∧ ¬k ∈ m then v else m.getD a fallback :=
  DHashMap.Raw.Const.getD_insertIfNew h.out

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).getKey? a = if k == a ∧ ¬k ∈ m then some k else m.getKey? a :=
  DHashMap.Raw.getKey?_insertIfNew h.out

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insertIfNew k v).getKey a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  DHashMap.Raw.getKey_insertIfNew h.out

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).getKey! a = if k == a ∧ ¬k ∈ m then k else m.getKey! a :=
  DHashMap.Raw.getKey!_insertIfNew h.out

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} {v : β} :
    (m.insertIfNew k v).getKeyD a fallback = if k == a ∧ ¬k ∈ m then k else m.getKeyD a fallback :=
  DHashMap.Raw.getKeyD_insertIfNew h.out

@[simp]
theorem getThenInsertIfNew?_fst (h : m.WF) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).1 = get? m k :=
  DHashMap.Raw.Const.getThenInsertIfNew?_fst h.out

@[simp]
theorem getThenInsertIfNew?_snd (h : m.WF) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  ext (DHashMap.Raw.Const.getThenInsertIfNew?_snd h.out)

@[simp]
theorem length_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.length = m.size :=
  DHashMap.Raw.length_keys h.out

@[simp]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.isEmpty = m.isEmpty :=
  DHashMap.Raw.isEmpty_keys h.out

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.keys.contains k = m.contains k :=
  DHashMap.Raw.contains_keys h.out

@[simp]
theorem mem_keys [LawfulBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    k ∈ m.keys ↔ k ∈ m :=
  DHashMap.Raw.mem_keys h.out

theorem distinct_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.Pairwise (fun a b => (a == b) = false) :=
  DHashMap.Raw.distinct_keys h.out

@[simp]
theorem insertMany_nil (h : m.WF) :
    insertMany m [] = m :=
  ext (DHashMap.Raw.Const.insertMany_nil h.out)

@[simp]
theorem insertMany_list_singleton (h : m.WF)
    {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v :=
  ext (DHashMap.Raw.Const.insertMany_list_singleton h.out)

theorem insertMany_cons (h : m.WF) {l : List (α × β)}
    {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l :=
  ext (DHashMap.Raw.Const.insertMany_cons h.out)

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    (insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) :=
  DHashMap.Raw.Const.contains_insertMany_list h.out

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k :=
  DHashMap.Raw.Const.mem_insertMany_list h.out

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l → (l.map Prod.fst).contains k = false → k ∈ m :=
  DHashMap.Raw.Const.mem_of_mem_insertMany_list h.out

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k :=
  DHashMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k :=
  DHashMap.Raw.Const.getKey?_insertMany_list_of_mem h.out k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany m l).getKey k h' =
      m.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  DHashMap.Raw.Const.getKey_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany m l).getKey k' h' = k :=
  DHashMap.Raw.Const.getKey_insertMany_list_of_mem h.out k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k :=
  DHashMap.Raw.Const.getKey!_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k :=
  DHashMap.Raw.Const.getKey!_insertMany_list_of_mem h.out k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback :=
  DHashMap.Raw.Const.getKeyD_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k :=
  DHashMap.Raw.Const.getKeyD_insertMany_list_of_mem h.out k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  DHashMap.Raw.Const.size_insertMany_list h.out distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} :
    m.size ≤ (insertMany m l).size :=
  DHashMap.Raw.Const.size_le_size_insertMany_list h.out

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length :=
  DHashMap.Raw.Const.size_insertMany_list_le h.out

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  DHashMap.Raw.Const.isEmpty_insertMany_list h.out

theorem getElem?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]? = m[k]? :=
  DHashMap.Raw.Const.get?_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getElem?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']? = v :=
  DHashMap.Raw.Const.get?_insertMany_list_of_mem h.out k_beq distinct mem

theorem getElem_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany m l)[k] =
      m[k]'(mem_of_mem_insertMany_list h h' contains_eq_false) :=
  DHashMap.Raw.Const.get_insertMany_list_of_contains_eq_false h.out contains_eq_false (h':= h')

theorem getElem_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    (insertMany m l)[k'] = v :=
  DHashMap.Raw.Const.get_insertMany_list_of_mem h.out k_beq distinct mem (h' := h')

theorem getElem!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β] (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]! = m[k]! :=
  DHashMap.Raw.Const.get!_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getElem!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (h : m.WF) {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']! = v :=
  DHashMap.Raw.Const.get!_insertMany_list_of_mem h.out k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  DHashMap.Raw.Const.getD_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v :=
  DHashMap.Raw.Const.getD_insertMany_list_of_mem h.out k_beq distinct mem

variable {m : Raw α Unit}

@[simp]
theorem insertManyIfNewUnit_nil (h : m.WF) :
    insertManyIfNewUnit m [] = m :=
  ext (DHashMap.Raw.Const.insertManyIfNewUnit_nil h.out)

@[simp]
theorem insertManyIfNewUnit_list_singleton (h : m.WF) {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () :=
  ext (DHashMap.Raw.Const.insertManyIfNewUnit_list_singleton h.out)

theorem insertManyIfNewUnit_cons (h : m.WF) {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l :=
  ext (DHashMap.Raw.Const.insertManyIfNewUnit_cons h.out)

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) :=
  DHashMap.Raw.Const.contains_insertManyIfNewUnit_list h.out

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k :=
  DHashMap.Raw.Const.mem_insertManyIfNewUnit_list h.out

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m :=
  DHashMap.Raw.Const.mem_of_mem_insertManyIfNewUnit_list h.out contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false: l.contains k = false) :
    getKey? (insertManyIfNewUnit m l) k = none :=
  DHashMap.Raw.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h.out not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit m l) k' = some k :=
  DHashMap.Raw.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.out k_beq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k : α} (mem : k ∈ m) :
    getKey? (insertManyIfNewUnit m l) k = getKey? m k :=
  DHashMap.Raw.Const.getKey?_insertManyIfNewUnit_list_of_mem h.out mem

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) {h'} :
    getKey (insertManyIfNewUnit m l) k' h' = k :=
  DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.out k_beq not_mem distinct mem

theorem getKey_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k : α} (mem: k ∈ m) {h₃} :
    getKey (insertManyIfNewUnit m l) k h₃ = getKey m k mem :=
  DHashMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem h.out mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default :=
  DHashMap.Raw.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h.out not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.WF) {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k :=
  DHashMap.Raw.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.out k_beq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.WF) {l : List α} {k : α} (mem : k ∈ m) :
    getKey! (insertManyIfNewUnit m l) k = getKey! m k :=
  DHashMap.Raw.Const.getKey!_insertManyIfNewUnit_list_of_mem h.out mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit m l) k fallback = fallback :=
  DHashMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h.out not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k :=
  DHashMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    h.out k_beq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k fallback : α} (mem : k ∈ m) :
    getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback :=
  DHashMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_mem h.out mem

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length :=
  DHashMap.Raw.Const.size_insertManyIfNewUnit_list h.out distinct

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size :=
  DHashMap.Raw.Const.size_le_size_insertManyIfNewUnit_list h.out

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length :=
  DHashMap.Raw.Const.size_insertManyIfNewUnit_list_le h.out

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  DHashMap.Raw.Const.isEmpty_insertManyIfNewUnit_list h.out

@[simp]
theorem getElem?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l)[k]? =
      if k ∈ m ∨ l.contains k then some () else none :=
  DHashMap.Raw.Const.get?_insertManyIfNewUnit_list h.out

@[simp]
theorem getElem_insertManyIfNewUnit_list
    {l : List α} {k : α} {h} :
    (insertManyIfNewUnit m l)[k] = () :=
  DHashMap.Raw.Const.get_insertManyIfNewUnit_list (h:=h)

@[simp]
theorem getElem!_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l)[k]! = () :=
  DHashMap.Raw.Const.get!_insertManyIfNewUnit_list

@[simp]
theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () := by
  simp

end Raw

namespace Raw

variable [BEq α] [Hashable α]

@[simp]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ :=
  ext DHashMap.Raw.Const.ofList_nil

@[simp]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : Raw α β).insert k v :=
  ext DHashMap.Raw.Const.ofList_singleton

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : Raw α β).insert k v) tl :=
  ext DHashMap.Raw.Const.ofList_cons

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  DHashMap.Raw.Const.contains_ofList

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ (ofList l) ↔ (l.map Prod.fst).contains k :=
  DHashMap.Raw.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]? = none :=
  DHashMap.Raw.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']? = some v :=
  DHashMap.Raw.Const.get?_ofList_of_mem k_beq distinct mem

theorem getElem_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l)[k'] = v :=
  DHashMap.Raw.Const.get_ofList_of_mem k_beq distinct mem (h:=h)

theorem getElem!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]! = default :=
  DHashMap.Raw.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']! = v :=
  DHashMap.Raw.Const.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback :=
  DHashMap.Raw.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v :=
  DHashMap.Raw.Const.getD_ofList_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  DHashMap.Raw.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k :=
  DHashMap.Raw.Const.getKey?_ofList_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l).getKey k' h' = k :=
  DHashMap.Raw.Const.getKey_ofList_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  DHashMap.Raw.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k :=
  DHashMap.Raw.Const.getKey!_ofList_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  DHashMap.Raw.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k :=
  DHashMap.Raw.Const.getKeyD_ofList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  DHashMap.Raw.Const.size_ofList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).size ≤ l.length :=
  DHashMap.Raw.Const.size_ofList_le

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).isEmpty = l.isEmpty :=
  DHashMap.Raw.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) = ∅ :=
  ext DHashMap.Raw.Const.unitOfList_nil

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (∅ : Raw α Unit).insertIfNew k () :=
  ext DHashMap.Raw.Const.unitOfList_singleton

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) = insertManyIfNewUnit ((∅ : Raw α Unit).insertIfNew hd ()) tl :=
  ext DHashMap.Raw.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k :=
  DHashMap.Raw.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k :=
  DHashMap.Raw.Const.mem_unitOfList

theorem getKey?_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none :=
  DHashMap.Raw.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k :=
  DHashMap.Raw.Const.getKey?_unitOfList_of_mem k_beq distinct mem

theorem getKey_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l) k' h' = k :=
  DHashMap.Raw.Const.getKey_unitOfList_of_mem k_beq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default :=
  DHashMap.Raw.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k :=
  DHashMap.Raw.Const.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback :=
  DHashMap.Raw.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (unitOfList l) k' fallback = k :=
  DHashMap.Raw.Const.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length :=
  DHashMap.Raw.Const.size_unitOfList distinct

theorem size_unitOfList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).size ≤ l.length :=
  DHashMap.Raw.Const.size_unitOfList_le

@[simp]
theorem isEmpty_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).isEmpty = l.isEmpty :=
  DHashMap.Raw.Const.isEmpty_unitOfList

@[simp]
theorem getElem?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l)[k]? =
    if l.contains k then some () else none :=
  DHashMap.Raw.Const.get?_unitOfList

@[simp]
theorem getElem_unitOfList
    {l : List α} {k : α} {h} :
    (unitOfList l)[k] = () :=
  DHashMap.Raw.Const.get_unitOfList (h:=h)

@[simp]
theorem getElem!_unitOfList
    {l : List α} {k : α} :
    (unitOfList l)[k]! = () :=
  DHashMap.Raw.Const.get!_unitOfList

@[simp]
theorem getD_unitOfList
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () := by
  simp

end Raw

namespace Raw

variable [BEq α] [Hashable α] {m : Raw α β}

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α}
    {f : Option β → Option β} (h : m.WF) :
    (alter m k f).isEmpty = ((m.erase k).isEmpty && (f (get? m k)).isNone) :=
  DHashMap.Raw.Const.isEmpty_alter_eq_isEmpty_erase h.out

@[simp]
theorem isEmpty_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) && (f (get? m k)).isNone) :=
  DHashMap.Raw.Const.isEmpty_alter h.out

theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).contains k' =
      if k == k' then (f (get? m k)).isSome else m.contains k' :=
  DHashMap.Raw.Const.contains_alter h.out

theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} (h : m.WF) :
    k' ∈ alter m k f ↔ if k == k' then (f (get? m k)).isSome = true else k' ∈ m :=
  DHashMap.Raw.Const.mem_alter h.out

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : m.WF) (he : k == k') : k' ∈ alter m k f ↔ (f (get? m k)).isSome :=
  DHashMap.Raw.Const.mem_alter_of_beq h.out he

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).contains k = (f (get? m k)).isSome :=
  DHashMap.Raw.Const.contains_alter_self h.out

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : k ∈ alter m k f ↔ (f (get? m k)).isSome :=
  DHashMap.Raw.Const.mem_alter_self h.out

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) (he : (k == k') = false) :
    (alter m k f).contains k' = m.contains k' :=
  DHashMap.Raw.Const.contains_alter_of_beq_eq_false h.out he

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) (he : (k == k') = false) : k' ∈ alter m k f ↔ k' ∈ m :=
  DHashMap.Raw.Const.mem_alter_of_beq_eq_false h.out he

theorem size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f).size =
      if m.contains k && (f (get? m k)).isNone then
        m.size - 1
      else if !m.contains k && (f (get? m k)).isSome then
        m.size + 1
      else
        m.size :=
  DHashMap.Raw.Const.size_alter h.out

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∉ m) (h₂ : (f (get? m k)).isSome) :
    (alter m k f).size = m.size + 1 :=
  DHashMap.Raw.Const.size_alter_eq_add_one h.out h₁ h₂

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∈ m) (h₂ : (f (get? m k)).isNone) :
    (alter m k f).size = m.size - 1 :=
  DHashMap.Raw.Const.size_alter_eq_sub_one h.out h₁ h₂

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∉ m) (h₂ : (f (get? m k)).isNone) : (alter m k f).size = m.size :=
  DHashMap.Raw.Const.size_alter_eq_self_of_not_mem h.out h₁ h₂

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∈ m) (h₂ : (f (get? m k)).isSome) : (alter m k f).size = m.size :=
  DHashMap.Raw.Const.size_alter_eq_self_of_mem h.out h₁ h₂

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f).size ≤ m.size + 1 :=
  DHashMap.Raw.Const.size_alter_le_size h.out

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    m.size - 1 ≤ (alter m k f).size :=
  DHashMap.Raw.Const.size_le_size_alter h.out

theorem get?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} (h : m.WF) :
    get? (alter m k f) k' =
      if k == k' then
        f (get? m k)
      else
        get? m k' :=
  DHashMap.Raw.Const.get?_alter h.out

@[simp]
theorem get?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : get? (alter m k f) k = f (get? m k) :=
  DHashMap.Raw.Const.get?_alter_self h.out

theorem get_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    (h : m.WF) {hc : k' ∈ alter m k f} :
    get (alter m k f) k' hc =
      if heq : k == k' then
        haveI h' : (f (get? m k)).isSome := mem_alter_of_beq h heq |>.mp hc
        f (get? m k) |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        get m k' h' :=
  DHashMap.Raw.Const.get_alter h.out

@[simp]
theorem get_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) {hc : k ∈ alter m k f} :
    haveI h' : (f (get? m k)).isSome := mem_alter_self h |>.mp hc
    get (alter m k f) k hc = (f (get? m k)).get h' :=
  DHashMap.Raw.Const.get_alter_self h.out

theorem get!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} (h : m.WF) : get! (alter m k f) k' =
      if k == k' then
        f (get? m k) |>.get!
      else
        get! m k' :=
  DHashMap.Raw.Const.get!_alter h.out

@[simp]
theorem get!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} (h : m.WF) : get! (alter m k f) k = (f (get? m k)).get! :=
  DHashMap.Raw.Const.get!_alter_self h.out

theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β}
    {f : Option β → Option β} (h : m.WF) : getD (alter m k f) k' fallback =
      if k == k' then
        f (get? m k) |>.getD fallback
      else
        getD m k' fallback :=
  DHashMap.Raw.Const.getD_alter h.out

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} (h : m.WF) :
    getD (alter m k f) k fallback = (f (get? m k)).getD fallback :=
  DHashMap.Raw.Const.getD_alter_self h.out

theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).getKey? k' =
      if k == k' then
        if (f (get? m k)).isSome then some k else none
      else
        m.getKey? k' :=
  DHashMap.Raw.Const.getKey?_alter h.out

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).getKey? k = if (f (get? m k)).isSome then some k else none :=
  DHashMap.Raw.Const.getKey?_alter_self h.out

theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) : (alter m k f).getKey! k' =
      if k == k' then
        if (f (get? m k)).isSome then k else default
      else
        m.getKey! k' :=
  DHashMap.Raw.Const.getKey!_alter h.out

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} (h : m.WF) :
    (alter m k f).getKey! k = if (f (get? m k)).isSome then k else default :=
  DHashMap.Raw.Const.getKey!_alter_self h.out

theorem getKey_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) {hc : k' ∈ alter m k f} :
    (alter m k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        m.getKey k' h' :=
  DHashMap.Raw.Const.getKey_alter h.out

@[simp]
theorem getKey_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} (h : m.WF) {hc : k ∈ alter m k f} :
    (alter m k f).getKey k hc = k :=
  DHashMap.Raw.Const.getKey_alter_self h.out

theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  DHashMap.Raw.Const.getKeyD_alter h.out

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : Option β → Option β} (h : m.WF) :
    (alter m k f).getKeyD k fallback = if (f (get? m k)).isSome then k else fallback :=
  DHashMap.Raw.Const.getKeyD_alter_self h.out

end Alter

section Modify

@[simp]
theorem isEmpty_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (modify m k f).isEmpty = m.isEmpty :=
  DHashMap.Raw.Const.isEmpty_modify h.out

@[simp]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} (h : m.WF) :
    (modify m k f).contains k' = m.contains k' :=
  DHashMap.Raw.Const.contains_modify h.out

@[simp]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} (h : m.WF) :
    k' ∈ modify m k f ↔ k' ∈ m :=
  DHashMap.Raw.Const.mem_modify h.out

@[simp]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (modify m k f).size = m.size :=
  DHashMap.Raw.Const.size_modify h.out

theorem get?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} (h : m.WF) :
    get? (modify m k f) k' =
      if k == k' then
        get? m k |>.map f
      else
        get? m k' :=
  DHashMap.Raw.Const.get?_modify h.out

@[simp]
theorem get?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    get? (modify m k f) k = (get? m k).map f :=
  DHashMap.Raw.Const.get?_modify_self h.out

theorem get_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    (h : m.WF) {hc : k' ∈ modify m k f} :
    get (modify m k f) k' hc =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        f (get m k h')
      else
        haveI h' : k' ∈ m := mem_modify h |>.mp hc
        get m k' h' :=
  DHashMap.Raw.Const.get_modify h.out

@[simp]
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF)
    {hc : k ∈ modify m k f} :
    haveI h' : k ∈ m := mem_modify h |>.mp hc
    get (modify m k f) k hc = f (get m k h') :=
  DHashMap.Raw.Const.get_modify_self h.out

theorem get!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β}
    (h : m.WF) : get! (modify m k f) k' =
      if k == k' then
        get? m k |>.map f |>.get!
      else
        get! m k' :=
  DHashMap.Raw.Const.get!_modify h.out

@[simp]
theorem get!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β}
    (h : m.WF) : get! (modify m k f) k = ((get? m k).map f).get! :=
  DHashMap.Raw.Const.get!_modify_self h.out

theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} (h : m.WF) :
    getD (modify m k f) k' fallback =
      if k == k' then
        get? m k |>.map f |>.getD fallback
      else
        getD m k' fallback :=
  DHashMap.Raw.Const.getD_modify h.out

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} (h : m.WF) :
    getD (modify m k f) k fallback = ((get? m k).map f).getD fallback :=
  DHashMap.Raw.Const.getD_modify_self h.out

theorem getKey?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} (h : m.WF) :
    (modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  DHashMap.Raw.Const.getKey?_modify h.out

theorem getKey?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (modify m k f).getKey? k = if k ∈ m then some k else none :=
  DHashMap.Raw.Const.getKey?_modify_self h.out

theorem getKey!_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    (h : m.WF) : (modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  DHashMap.Raw.Const.getKey!_modify h.out

theorem getKey!_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    (h : m.WF) : (modify m k f).getKey! k = if k ∈ m then k else default :=
  DHashMap.Raw.Const.getKey!_modify_self h.out

theorem getKey_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    (h : m.WF) {hc : k' ∈ modify m k f} :
    (modify m k f).getKey k' hc =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify h |>.mp hc
        m.getKey k' h' :=
  DHashMap.Raw.Const.getKey_modify h.out

@[simp]
theorem getKey_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    (h : m.WF) {hc : k ∈ modify m k f} : (modify m k f).getKey k hc = k :=
  DHashMap.Raw.Const.getKey_modify_self h.out

theorem getKeyD_modify [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} (h : m.WF) :
    (modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  DHashMap.Raw.Const.getKeyD_modify h.out

theorem getKeyD_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : β → β} (h : m.WF) : (modify m k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  DHashMap.Raw.Const.getKeyD_modify_self h.out

end Modify

end Raw

end Std.HashMap
