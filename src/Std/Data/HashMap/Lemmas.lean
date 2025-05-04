/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Lemmas
import Std.Data.HashMap.Basic
import Std.Data.HashMap.AdditionalOperations

/-!
# Hash map lemmas

This module contains lemmas about `Std.Data.HashMap`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} {_ : BEq α} {_ : Hashable α}

namespace Std.HashMap

section

variable {m : HashMap α β}

private theorem ext {m m' : HashMap α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyWithCapacity {c} : (emptyWithCapacity c : HashMap α β).isEmpty :=
  DHashMap.isEmpty_emptyWithCapacity

@[simp]
theorem isEmpty_empty : (∅ : HashMap α β).isEmpty :=
  DHashMap.isEmpty_empty

set_option linter.missingDocs false in
@[deprecated isEmpty_empty (since := "2025-03-12")]
abbrev isEmpty_emptyc := @isEmpty_empty

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).isEmpty = false :=
  DHashMap.isEmpty_insert

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  DHashMap.mem_iff_contains

@[simp]
theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m :=
  DHashMap.contains_iff_mem

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  DHashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m :=
  DHashMap.mem_congr hab

@[simp]
theorem contains_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : HashMap α β).contains a = false :=
  DHashMap.contains_emptyWithCapacity

@[simp] theorem not_mem_emptyWithCapacity {a : α} {c} : ¬a ∈ (emptyWithCapacity c : HashMap α β) :=
  DHashMap.not_mem_emptyWithCapacity

@[simp] theorem contains_empty {a : α} : (∅ : HashMap α β).contains a = false :=
  DHashMap.contains_empty

set_option linter.missingDocs false in
@[deprecated contains_empty (since := "2025-03-12")]
abbrev contains_emptyc := @contains_empty

@[simp] theorem not_mem_empty {a : α} : ¬a ∈ (∅ : HashMap α β) :=
  DHashMap.not_mem_empty

set_option linter.missingDocs false in
@[deprecated not_mem_empty (since := "2025-03-12")]
abbrev not_mem_emptyc := @not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → m.contains a = false :=
  DHashMap.contains_of_isEmpty

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → ¬a ∈ m :=
  DHashMap.not_mem_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, m.contains a = true :=
  DHashMap.isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, a ∈ m :=
  DHashMap.isEmpty_eq_false_iff_exists_mem

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, m.contains a = false :=
  DHashMap.isEmpty_iff_forall_contains

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m :=
  DHashMap.isEmpty_iff_forall_not_mem

@[simp] theorem insert_eq_insert {p : α × β} : Insert.insert p m = m.insert p.1 p.2 := rfl

@[simp] theorem singleton_eq_insert {p : α × β} :
    Singleton.singleton p = (∅ : HashMap α β).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  DHashMap.contains_insert

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m :=
  DHashMap.mem_insert

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  DHashMap.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m :=
  DHashMap.mem_of_mem_insert

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).contains k := by simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : k ∈ m.insert k v := by
  simp

@[simp]
theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : HashMap α β).size = 0 :=
  DHashMap.size_emptyWithCapacity

@[simp]
theorem size_empty : (∅ : HashMap α β).size = 0 :=
  DHashMap.size_empty

set_option linter.missingDocs false in
@[deprecated size_empty (since := "2025-03-12")]
abbrev size_emptyc := @size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  DHashMap.isEmpty_eq_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  DHashMap.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    m.size ≤ (m.insert k v).size :=
  DHashMap.size_le_size_insert

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).size ≤ m.size + 1 :=
  DHashMap.size_insert_le

@[simp]
theorem erase_emptyWithCapacity {a : α} {c : Nat} : (emptyWithCapacity c : HashMap α β).erase a = emptyWithCapacity c :=
  ext DHashMap.erase_emptyWithCapacity

@[simp]
theorem erase_empty {a : α} : (∅ : HashMap α β).erase a = ∅ :=
  ext DHashMap.erase_empty

set_option linter.missingDocs false in
@[deprecated erase_empty (since := "2025-03-12")]
abbrev erase_emptyc := @erase_empty

@[simp]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  DHashMap.isEmpty_erase

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  DHashMap.contains_erase

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  DHashMap.mem_erase

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  DHashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m :=
  DHashMap.mem_of_mem_erase

theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  DHashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  DHashMap.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  DHashMap.size_le_size_erase

@[simp]
theorem containsThenInsert_fst {k : α} {v : β} : (m.containsThenInsert k v).1 = m.contains k :=
  DHashMap.containsThenInsert_fst

@[simp]
theorem containsThenInsert_snd {k : α} {v : β} : (m.containsThenInsert k v).2 = m.insert k v :=
  ext (DHashMap.containsThenInsert_snd)

@[simp]
theorem containsThenInsertIfNew_fst {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  DHashMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsertIfNew_snd {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  ext DHashMap.containsThenInsertIfNew_snd

@[simp] theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
@[simp] theorem get?_eq_getElem? {a : α} : get? m a = m[a]? := rfl
@[simp] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! m a = m[a]! := rfl

@[simp]
theorem getElem?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : HashMap α β)[a]? = none :=
  DHashMap.Const.get?_emptyWithCapacity

@[simp]
theorem getElem?_empty {a : α} : (∅ : HashMap α β)[a]? = none :=
  DHashMap.Const.get?_empty

set_option linter.missingDocs false in
@[deprecated getElem?_empty (since := "2025-03-12")]
abbrev getElem?_emptyc := @getElem?_empty

theorem getElem?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m[a]? = none :=
  DHashMap.Const.get?_of_isEmpty

theorem getElem?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  DHashMap.Const.get?_insert

@[simp]
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v)[k]? = some v :=
  DHashMap.Const.get?_insert_self

theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = m[a]?.isSome :=
  DHashMap.Const.contains_eq_isSome_get?

@[simp]
theorem isSome_getElem?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    m[a]?.isSome = m.contains a :=
  contains_eq_isSome_getElem?.symm

theorem mem_iff_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ m[a]?.isSome :=
  DHashMap.Const.mem_iff_isSome_get?

@[simp]
theorem isSome_getElem?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    m[a]?.isSome ↔ a ∈ m :=
  mem_iff_isSome_getElem?.symm

theorem getElem?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m[a]? = none :=
  DHashMap.Const.get?_eq_none_of_contains_eq_false

theorem getElem?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m[a]? = none :=
  DHashMap.Const.get?_eq_none

theorem getElem?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k)[a]? = if k == a then none else m[a]? :=
  DHashMap.Const.get?_erase

@[simp]
theorem getElem?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k)[k]? = none :=
  DHashMap.Const.get?_erase_self

theorem getElem?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m[a]? = m[b]? :=
  DHashMap.Const.get?_congr hab

theorem getElem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    (m.insert k v)[a]'h₁ =
      if h₂ : k == a then v else m[a]'(mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Const.get_insert (h₁ := h₁)

@[simp]
theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v)[k]'mem_insert_self = v :=
  DHashMap.Const.get_insert_self

@[simp]
theorem getElem_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k)[a]'h' = m[a]'(mem_of_mem_erase h') :=
  DHashMap.Const.get_erase (h' := h')

theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) :
    m[a]? = some (m[a]'h') :=
  DHashMap.Const.get?_eq_some_get h'

theorem getElem_eq_get_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m[a]'h = m[a]?.get (mem_iff_isSome_getElem?.mp h) :=
  DHashMap.Const.get_eq_get_get?

theorem get_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m[a]?.get h = m[a]'(mem_iff_isSome_getElem?.mpr h) :=
  DHashMap.Const.get_get?

theorem getElem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) {h'} :
    m[a]'h' = m[b]'((mem_congr hab).1 h') :=
  DHashMap.Const.get_congr hab (h' := h')

@[simp]
theorem getElem!_emptyWithCapacity [Inhabited β] {a : α} {c} : (emptyWithCapacity c : HashMap α β)[a]! = default :=
  DHashMap.Const.get!_emptyWithCapacity

@[simp]
theorem getElem!_empty [Inhabited β] {a : α} : (∅ : HashMap α β)[a]! = default :=
  DHashMap.Const.get!_empty

set_option linter.missingDocs false in
@[deprecated getElem!_empty (since := "2025-03-12")]
abbrev getElem!_emptyc := @getElem!_empty

theorem getElem!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.isEmpty = true → m[a]! = default :=
  DHashMap.Const.get!_of_isEmpty

theorem getElem!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    (m.insert k v)[a]! = if k == a then v else m[a]! :=
  DHashMap.Const.get!_insert

@[simp]
theorem getElem!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} :
    (m.insert k v)[k]! = v :=
  DHashMap.Const.get!_insert_self

theorem getElem!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {a : α} : m.contains a = false → m[a]! = default :=
  DHashMap.Const.get!_eq_default_of_contains_eq_false

theorem getElem!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → m[a]! = default :=
  DHashMap.Const.get!_eq_default

theorem getElem!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} :
    (m.erase k)[a]! = if k == a then default else m[a]! :=
  DHashMap.Const.get!_erase

@[simp]
theorem getElem!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    (m.erase k)[k]! = default :=
  DHashMap.Const.get!_erase_self

theorem getElem?_eq_some_getElem!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {a : α} : m.contains a = true → m[a]? = some m[a]! :=
  DHashMap.Const.get?_eq_some_get!_of_contains

theorem getElem?_eq_some_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → m[a]? = some m[a]! :=
  DHashMap.Const.get?_eq_some_get!

theorem getElem!_eq_get!_getElem? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m[a]?.get! :=
  DHashMap.Const.get!_eq_get!_get?

theorem getElem_eq_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h'} :
    m[a]'h' = m[a]! :=
  @DHashMap.Const.get_eq_get! _ _ _ _ _ _ _ _ _ h'

theorem getElem!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    m[a]! = m[b]! :=
  DHashMap.Const.get!_congr hab

@[simp]
theorem getD_emptyWithCapacity {a : α} {fallback : β} {c} :
    (emptyWithCapacity c : HashMap α β).getD a fallback = fallback :=
  DHashMap.Const.getD_emptyWithCapacity

@[simp]
theorem getD_empty {a : α} {fallback : β} : (∅ : HashMap α β).getD a fallback = fallback :=
  DHashMap.Const.getD_empty

set_option linter.missingDocs false in
@[deprecated getD_empty (since := "2025-03-12")]
abbrev getD_emptyc := @getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  DHashMap.Const.getD_of_isEmpty

theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    (m.insert k v).getD a fallback = if k == a then v else m.getD a fallback :=
  DHashMap.Const.getD_insert

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback v : β} :
   (m.insert k v).getD k fallback = v :=
  DHashMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : β} : m.contains a = false → m.getD a fallback = fallback :=
  DHashMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  DHashMap.Const.getD_eq_fallback

theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  DHashMap.Const.getD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    (m.erase k).getD k fallback = fallback :=
  DHashMap.Const.getD_erase_self

theorem getElem?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → m[a]? = some (m.getD a fallback) :=
  DHashMap.Const.get?_eq_some_getD_of_contains

theorem getElem?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → m[a]? = some (m.getD a fallback) :=
  DHashMap.Const.get?_eq_some_getD

theorem getD_eq_getD_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.getD a fallback = m[a]?.getD fallback :=
  DHashMap.Const.getD_eq_getD_get?

theorem getElem_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h'} :
    m[a]'h' = m.getD a fallback :=
  @DHashMap.Const.get_eq_getD _ _ _ _ _ _ _ _ _ h'

theorem getElem!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m.getD a default :=
  DHashMap.Const.get!_eq_getD_default

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    m.getD a fallback = m.getD b fallback :=
  DHashMap.Const.getD_congr hab

@[simp]
theorem getKey?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : HashMap α β).getKey? a = none :=
  DHashMap.getKey?_emptyWithCapacity

@[simp]
theorem getKey?_empty {a : α} : (∅ : HashMap α β).getKey? a = none :=
  DHashMap.getKey?_empty

set_option linter.missingDocs false in
@[deprecated getKey?_empty (since := "2025-03-12")]
abbrev getKey?_emptyc := @getKey?_empty

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  DHashMap.getKey?_of_isEmpty

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  DHashMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).getKey? k = some k :=
  DHashMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  DHashMap.contains_eq_isSome_getKey?

@[simp]
theorem isSome_getKey?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome = m.contains a :=
  contains_eq_isSome_getKey?.symm

theorem mem_iff_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ (m.getKey? a).isSome :=
  DHashMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_getKey?.symm

theorem mem_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] {k k' : α}
    (h : m.getKey? k = some k') : k' ∈ m :=
  DHashMap.mem_of_getKey?_eq_some h

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey? a = none :=
  DHashMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none :=
  DHashMap.getKey?_eq_none

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  DHashMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).getKey? k = none :=
  DHashMap.getKey?_erase_self

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] {k : α} : (m.getKey? k).all (· == k) :=
  DHashMap.getKey?_beq

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] {k k' : α} (h : k == k') :
    m.getKey? k = m.getKey? k' :=
  DHashMap.getKey?_congr h

theorem getKey?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) :
    m.getKey? k = some k :=
  DHashMap.getKey?_eq_some h

theorem getKey?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k = some k := by
  simpa only [mem_iff_contains] using getKey?_eq_some_of_contains h

theorem getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then k else m.getKey a (mem_of_mem_insert h₁ (by simpa using h₂)) :=
  DHashMap.getKey_insert (h₁ := h₁)

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).getKey k mem_insert_self = k :=
  DHashMap.getKey_insert_self

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  DHashMap.getKey_erase (h' := h')

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α} (h : a ∈ m) :
    m.getKey? a = some (m.getKey a h) :=
  DHashMap.getKey?_eq_some_getKey h

theorem getKey_eq_get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m.getKey a h = (m.getKey? a).get (mem_iff_isSome_getKey?.mp h) :=
  DHashMap.getKey_eq_get_getKey?

@[simp]
theorem get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  DHashMap.get_getKey?

theorem getKey_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.getKey k h == k :=
  DHashMap.getKey_beq h

theorem getKey_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) :=
  DHashMap.getKey_congr h h₁

@[simp]
theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k :=
  DHashMap.getKey_eq h

@[simp]
theorem getKey!_emptyWithCapacity [Inhabited α] {a : α} {c} : (emptyWithCapacity c : HashMap α β).getKey! a = default :=
  DHashMap.getKey!_emptyWithCapacity

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} : (∅ : HashMap α β).getKey! a = default :=
  DHashMap.getKey!_empty

set_option linter.missingDocs false in
@[deprecated getKey!_empty (since := "2025-03-12")]
abbrev getKey!_emptyc := @getKey!_empty

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  DHashMap.getKey!_of_isEmpty

theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β} :
    (m.insert k v).getKey! a = if k == a then k else m.getKey! a :=
  DHashMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {v : β} :
    (m.insert k v).getKey! k = k :=
  DHashMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = false → m.getKey! a = default :=
  DHashMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  DHashMap.getKey!_eq_default

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  DHashMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m.erase k).getKey! k = default :=
  DHashMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  DHashMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  DHashMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  DHashMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h'} :
    m.getKey a h' = m.getKey! a :=
  @DHashMap.getKey_eq_getKey! _ _ _ _ _ _ _ _ _ h'

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : k == k') :
    m.getKey! k = m.getKey! k' :=
  DHashMap.getKey!_congr h

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) :
    m.getKey! k = k :=
  DHashMap.getKey!_eq_of_contains h

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.getKey! k = k :=
  DHashMap.getKey!_eq_of_mem h

@[simp]
theorem getKeyD_emptyWithCapacity {a : α} {fallback : α} {c} :
    (emptyWithCapacity c : HashMap α β).getKeyD a fallback = fallback :=
  DHashMap.getKeyD_emptyWithCapacity

@[simp]
theorem getKeyD_empty {a : α} {fallback : α} : (∅ : HashMap α β).getKeyD a fallback = fallback :=
  DHashMap.getKeyD_empty

set_option linter.missingDocs false in
@[deprecated getKeyD_empty (since := "2025-03-12")]
abbrev getKeyD_emptyc := @getKeyD_empty

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  DHashMap.getKeyD_of_isEmpty

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β} :
    (m.insert k v).getKeyD a fallback = if k == a then k else m.getKeyD a fallback :=
  DHashMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] {k fallback : α} {v : β} :
   (m.insert k v).getKeyD k fallback = k :=
  DHashMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : α} : m.contains a = false → m.getKeyD a fallback = fallback :=
  DHashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  DHashMap.getKeyD_eq_fallback

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  DHashMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  DHashMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  DHashMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  DHashMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  DHashMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} {h'} :
    m.getKey a h' = m.getKeyD a fallback :=
  @DHashMap.getKey_eq_getKeyD _ _ _ _ _ _ _ _ _ h'

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = m.getKeyD a default :=
  DHashMap.getKey!_eq_getKeyD_default

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    (h : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback :=
  DHashMap.getKeyD_congr h

theorem getKeyD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getKeyD k fallback = k :=
  DHashMap.getKeyD_eq_of_contains h

theorem getKeyD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) :
    m.getKeyD k fallback = k :=
  DHashMap.getKeyD_eq_of_mem h

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).isEmpty = false :=
  DHashMap.isEmpty_insertIfNew

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  DHashMap.contains_insertIfNew

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m :=
  DHashMap.mem_insertIfNew

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).contains k :=
  DHashMap.contains_insertIfNew_self

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    k ∈ m.insertIfNew k v :=
  DHashMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  DHashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m :=
  DHashMap.mem_of_mem_insertIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `getElem_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  DHashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `getElem_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  DHashMap.mem_of_mem_insertIfNew'

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  DHashMap.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    m.size ≤ (m.insertIfNew k v).size :=
  DHashMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  DHashMap.size_insertIfNew_le

theorem getElem?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v)[a]? = if k == a ∧ ¬k ∈ m then some v else m[a]? :=
  DHashMap.Const.get?_insertIfNew

theorem getElem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    (m.insertIfNew k v)[a]'h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else m[a]'(mem_of_mem_insertIfNew' h₁ h₂) :=
  DHashMap.Const.get_insertIfNew (h₁ := h₁)

theorem getElem!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    (m.insertIfNew k v)[a]! = if k == a ∧ ¬k ∈ m then v else m[a]! :=
  DHashMap.Const.get!_insertIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    (m.insertIfNew k v).getD a fallback =
      if k == a ∧ ¬k ∈ m then v else m.getD a fallback :=
  DHashMap.Const.getD_insertIfNew

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a :=
  DHashMap.getKey?_insertIfNew

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂) :=
  DHashMap.getKey_insertIfNew

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a :=
  DHashMap.getKey!_insertIfNew

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β} :
    getKeyD (m.insertIfNew k v) a fallback = if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback :=
  DHashMap.getKeyD_insertIfNew

@[simp]
theorem getThenInsertIfNew?_fst {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k :=
  DHashMap.Const.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  ext (DHashMap.Const.getThenInsertIfNew?_snd)

instance [EquivBEq α] [LawfulHashable α] : LawfulGetElem (HashMap α β) α β (fun m a => a ∈ m) where
  getElem?_def m a _ := by
    split
    · exact getElem?_eq_some_getElem ‹_›
    · exact getElem?_eq_none ‹_›
  getElem!_def m a := by
    rw [getElem!_eq_get!_getElem?]
    split <;> simp_all

@[simp]
theorem length_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.length = m.size :=
  DHashMap.length_keys

@[simp]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α]:
    m.keys.isEmpty = m.isEmpty :=
  DHashMap.isEmpty_keys

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] {k : α} :
    m.keys.contains k = m.contains k :=
  DHashMap.contains_keys

@[simp]
theorem mem_keys [LawfulBEq α] [LawfulHashable α] {k : α} :
    k ∈ m.keys ↔ k ∈ m :=
  DHashMap.mem_keys

theorem mem_of_mem_keys [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m.keys) : k ∈ m :=
  DHashMap.mem_of_mem_keys h

theorem distinct_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.Pairwise (fun a b => (a == b) = false) :=
  DHashMap.distinct_keys

@[simp]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.toList.map Prod.fst = m.keys :=
  DHashMap.Const.map_fst_toList_eq_keys

@[deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_prod_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.toList.map Prod.fst = m.keys :=
  DHashMap.Const.map_fst_toList_eq_keys

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.length = m.size :=
  DHashMap.Const.length_toList

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.isEmpty = m.isEmpty :=
  DHashMap.Const.isEmpty_toList

@[simp]
theorem mem_toList_iff_getElem?_eq_some [LawfulBEq α]
    {k : α} {v : β} :
    (k, v) ∈ m.toList ↔ m[k]? = some v :=
  DHashMap.Const.mem_toList_iff_get?_eq_some

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} :
    (k, v) ∈ m.toList ↔ m.getKey? k = some k ∧ m[k]? = some v :=
  DHashMap.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some

theorem getElem?_eq_some_iff_exists_beq_and_mem_toList [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} :
    m[k]? = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ m.toList :=
  DHashMap.Const.get?_eq_some_iff_exists_beq_and_mem_toList

set_option linter.missingDocs false in
@[deprecated getElem?_eq_some_iff_exists_beq_and_mem_toList (since := "2025-04-13")]
abbrev get?_eq_some_iff_exists_beq_and_mem_toList := @getElem?_eq_some_iff_exists_beq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some
    [EquivBEq α] [LawfulHashable α] {k k' : α} {v : β} :
    m.toList.find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ m[k]? = some v :=
  DHashMap.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {k : α} :
    m.toList.find? (·.1 == k) = none ↔ m.contains k = false :=
  DHashMap.Const.find?_toList_eq_none_iff_contains_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [EquivBEq α] [LawfulHashable α]
    {k : α} :
    m.toList.find? (·.1 == k) = none ↔ ¬ k ∈ m :=
  DHashMap.Const.find?_toList_eq_none_iff_not_mem

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.Pairwise (fun a b => (a.1 == b.1) = false) :=
  DHashMap.Const.distinct_keys_toList

section monadic

variable {m : HashMap α β} {δ : Type w} {m' : Type w → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM (fun a b => f a b.1 b.2) init :=
  DHashMap.Const.foldM_eq_foldlM_toList

theorem fold_eq_foldl_toList {f : δ → (a : α) → β → δ} {init : δ} :
    m.fold f init = m.toList.foldl (fun a b => f a b.1 b.2) init :=
  DHashMap.Const.fold_eq_foldl_toList

@[simp]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : (a : α) → β → m' PUnit} :
    m.forM f = ForM.forM m (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : α × β → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  DHashMap.Const.forMUncurried_eq_forM_toList

@[simp]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : (a : α) → β → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn m init (fun a d => f a.1 a.2 d) := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : α × β → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  DHashMap.Const.forInUncurried_eq_forIn_toList

theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init :=
  DHashMap.foldM_eq_foldlM_keys

theorem fold_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  DHashMap.fold_eq_foldl_keys

theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    ForM.forM m (fun a => f a.1) = m.keys.forM f :=
  DHashMap.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f :=
  DHashMap.forIn_eq_forIn_keys

end monadic

variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[simp]
theorem insertMany_nil :
    insertMany m [] = m :=
  ext DHashMap.Const.insertMany_nil

@[simp]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v :=
  ext DHashMap.Const.insertMany_list_singleton

theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l :=
  ext DHashMap.Const.insertMany_cons

theorem insertMany_append {l₁ l₂ : List (α × β)} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[elab_as_elim]
theorem insertMany_ind {motive : HashMap α β → Prop} (m : HashMap α β) {l : ρ}
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) :=
  show motive ⟨DHashMap.Const.insertMany m.1 l⟩ from
    DHashMap.Const.insertMany_ind m.inner l init fun m => insert ⟨m⟩

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) :=
  DHashMap.Const.contains_insertMany_list

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k :=
  DHashMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} (mem : k ∈ insertMany m l)
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    k ∈ m :=
  DHashMap.Const.mem_of_mem_insertMany_list mem contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l :=
  DHashMap.Const.mem_insertMany_of_mem

theorem getElem?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]? = m[k]? :=
  DHashMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']? = some v :=
  DHashMap.Const.get?_insertMany_list_of_mem k_beq distinct mem

theorem getElem?_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (insertMany m l)[k]? = (l.findSomeRev? (fun ⟨a, b⟩ => if a == k then some b else none)).or m[k]? :=
  DHashMap.Const.get?_insertMany_list

theorem getElem_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l)[k] = m[k]'(mem_of_mem_insertMany_list h contains_eq_false) :=
  DHashMap.Const.get_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h} :
    (insertMany m l)[k'] = v :=
  DHashMap.Const.get_insertMany_list_of_mem k_beq distinct mem

theorem getElem!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]! = m[k]! :=
  DHashMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']! = v :=
  DHashMap.Const.get!_insertMany_list_of_mem k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  DHashMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v :=
  DHashMap.Const.getD_insertMany_list_of_mem k_beq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k :=
  DHashMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k :=
  DHashMap.Const.getKey?_insertMany_list_of_mem k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) :=
  DHashMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (insertMany m l).getKey k' h = k :=
  DHashMap.Const.getKey_insertMany_list_of_mem k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k :=
  DHashMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k :=
  DHashMap.Const.getKey!_insertMany_list_of_mem k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback :=
  DHashMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k :=
  DHashMap.Const.getKeyD_insertMany_list_of_mem k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  DHashMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    m.size ≤ (insertMany m l).size :=
  DHashMap.Const.size_le_size_insertMany_list

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  DHashMap.Const.size_le_size_insertMany

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length :=
  DHashMap.Const.size_insertMany_list_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  DHashMap.Const.isEmpty_insertMany_list

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : (insertMany m l).isEmpty → m.isEmpty :=
  DHashMap.Const.isEmpty_of_isEmpty_insertMany

variable {m : HashMap α Unit}
variable {ρ : Type w} [ForIn Id ρ α]

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit m [] = m :=
  ext DHashMap.Const.insertManyIfNewUnit_nil

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () :=
  ext DHashMap.Const.insertManyIfNewUnit_list_singleton

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l :=
  ext DHashMap.Const.insertManyIfNewUnit_cons

@[elab_as_elim]
theorem insertManyIfNewUnit_ind {motive : HashMap α Unit → Prop} (m : HashMap α Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l) :=
  show motive ⟨DHashMap.Const.insertManyIfNewUnit m.1 l⟩ from
    DHashMap.Const.insertManyIfNewUnit_ind m.inner l init fun m => insert ⟨m⟩

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) :=
  DHashMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k :=
  DHashMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m :=
  DHashMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem mem_insertManyIfNewUnit_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} : k ∈ m → k ∈ insertManyIfNewUnit m l :=
  DHashMap.Const.mem_insertManyIfNewUnit_of_mem

theorem getElem?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l)[k]? =
      if k ∈ m ∨ l.contains k then some () else none :=
  DHashMap.Const.get?_insertManyIfNewUnit_list

theorem getElem_insertManyIfNewUnit_list
    {l : List α} {k : α} {h} :
    (insertManyIfNewUnit m l)[k] = () :=
  DHashMap.Const.get_insertManyIfNewUnit_list

theorem getElem!_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l)[k]! = () :=
  DHashMap.Const.get!_insertManyIfNewUnit_list

theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () := by
  simp

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit m l) k = none :=
  DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k') (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit m l) k' = some k :=
  DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) :
    getKey? (insertManyIfNewUnit m l) k = getKey? m k :=
  DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k') (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) {h} :
    getKey (insertManyIfNewUnit m l) k' h = k :=
  DHashMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKey_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    getKey (insertManyIfNewUnit m l) k h = getKey m k mem :=
  DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default :=
  DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k :=
  DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    getKey! (insertManyIfNewUnit m l) k = getKey! m k :=
  DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit m l) k fallback = fallback :=
  DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l ) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k :=
  DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback :=
  DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length :=
  DHashMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size :=
  DHashMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_le_size_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertManyIfNewUnit m l).size :=
  DHashMap.Const.size_le_size_insertManyIfNewUnit

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length :=
  DHashMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  DHashMap.Const.isEmpty_insertManyIfNewUnit_list

theorem isEmpty_of_isEmpty_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {l : ρ} : (m.insertManyIfNewUnit l).isEmpty → m.isEmpty :=
  DHashMap.Const.isEmpty_of_isEmpty_insertManyIfNewUnit

end

section

@[simp]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ :=
  ext DHashMap.Const.ofList_nil

@[simp]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : HashMap α β).insert k v :=
  ext DHashMap.Const.ofList_singleton

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : HashMap α β).insert k v) tl :=
  ext DHashMap.Const.ofList_cons

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l = insertMany (∅ : HashMap α β) l :=
  ext DHashMap.Const.ofList_eq_insertMany_empty

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  DHashMap.Const.contains_ofList

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ ofList l ↔ (l.map Prod.fst).contains k :=
  DHashMap.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]? = none :=
  DHashMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']? = some v :=
  DHashMap.Const.get?_ofList_of_mem k_beq distinct mem

theorem getElem_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l)[k'] = v :=
  DHashMap.Const.get_ofList_of_mem k_beq distinct mem

theorem getElem!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]! = (default : β) :=
  DHashMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']! = v :=
  DHashMap.Const.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback :=
  DHashMap.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v :=
  DHashMap.Const.getD_ofList_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  DHashMap.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k :=
  DHashMap.Const.getKey?_ofList_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  DHashMap.Const.getKey_ofList_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  DHashMap.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k :=
  DHashMap.Const.getKey!_ofList_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  DHashMap.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k :=
  DHashMap.Const.getKeyD_ofList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  DHashMap.Const.size_ofList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).size ≤ l.length :=
  DHashMap.Const.size_ofList_le

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).isEmpty = l.isEmpty :=
  DHashMap.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) = ∅ :=
  ext DHashMap.Const.unitOfList_nil

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (∅ : HashMap α Unit).insertIfNew k () :=
  ext DHashMap.Const.unitOfList_singleton

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      insertManyIfNewUnit ((∅ : HashMap α Unit).insertIfNew hd ()) tl :=
  ext DHashMap.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k :=
  DHashMap.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k :=
  DHashMap.Const.mem_unitOfList

@[simp]
theorem getElem?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l)[k]? =
    if l.contains k then some () else none :=
  DHashMap.Const.get?_unitOfList

@[simp]
theorem getElem_unitOfList
    {l : List α} {k : α} {h} :
    (unitOfList l)[k] = () :=
  DHashMap.Const.get_unitOfList

@[simp]
theorem getElem!_unitOfList
    {l : List α} {k : α} :
    (unitOfList l)[k]! = () :=
  DHashMap.Const.get!_unitOfList

@[simp]
theorem getD_unitOfList
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () := by
  simp

theorem getKey?_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none :=
  DHashMap.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k :=
  DHashMap.Const.getKey?_unitOfList_of_mem k_beq distinct mem

theorem getKey_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (unitOfList l) k' h = k :=
  DHashMap.Const.getKey_unitOfList_of_mem k_beq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default :=
  DHashMap.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k :=
  DHashMap.Const.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback :=
  DHashMap.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (unitOfList l) k' fallback = k :=
  DHashMap.Const.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length :=
  DHashMap.Const.size_unitOfList distinct

theorem size_unitOfList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).size ≤ l.length :=
  DHashMap.Const.size_unitOfList_le

@[simp]
theorem isEmpty_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).isEmpty = l.isEmpty :=
  DHashMap.Const.isEmpty_unitOfList

end

section Alter

variable {m : HashMap α β}

theorem isEmpty_alter_eq_isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α}
    {f : Option β → Option β} :
    (alter m k f).isEmpty = ((m.erase k).isEmpty && (f m[k]?).isNone) :=
  DHashMap.Const.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem isEmpty_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) && (f m[k]?).isNone) :=
  DHashMap.Const.isEmpty_alter

theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    (alter m k f).contains k' = if k == k' then (f m[k]?).isSome else m.contains k' :=
  DHashMap.Const.contains_alter

theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    k' ∈ alter m k f ↔ if k == k' then (f m[k]?).isSome = true else k' ∈ m :=
  DHashMap.Const.mem_alter

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : k == k') : k' ∈ alter m k f ↔ (f m[k]?).isSome :=
  DHashMap.Const.mem_alter_of_beq h

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).contains k = (f m[k]?).isSome :=
  DHashMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    k ∈ alter m k f ↔ (f m[k]?).isSome :=
  DHashMap.Const.mem_alter_self

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) :
    (alter m k f).contains k' = m.contains k' :=
  DHashMap.Const.contains_alter_of_beq_eq_false h

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) : k' ∈ alter m k f ↔ k' ∈ m :=
  DHashMap.Const.mem_alter_of_beq_eq_false h

theorem size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (m.alter k f).size =
      if k ∈ m ∧ (f m[k]?).isNone then
        m.size - 1
      else if k ∉ m ∧ (f m[k]?).isSome then
        m.size + 1
      else
        m.size :=
  DHashMap.Const.size_alter

theorem size_alter_eq_add_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f m[k]?).isSome) :
    (alter m k f).size = m.size + 1 :=
  DHashMap.Const.size_alter_eq_add_one h h'

theorem size_alter_eq_sub_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f m[k]?).isNone) :
    (alter m k f).size = m.size - 1 :=
  DHashMap.Const.size_alter_eq_sub_one h h'

theorem size_alter_eq_self_of_not_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f m[k]?).isNone) :
    (alter m k f).size = m.size :=
  DHashMap.Const.size_alter_eq_self_of_not_mem h h'

theorem size_alter_eq_self_of_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f m[k]?).isSome) :
    (alter m k f).size = m.size :=
  DHashMap.Const.size_alter_eq_self_of_mem h h'

theorem size_alter_le_size [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).size ≤ m.size + 1 :=
  DHashMap.Const.size_alter_le_size

theorem size_le_size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    m.size - 1 ≤ (alter m k f).size :=
  DHashMap.Const.size_le_size_alter

theorem getElem?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (alter m k f)[k']? =
      if k == k' then
        f m[k]?
      else
        m[k']? :=
  DHashMap.Const.get?_alter

@[deprecated getElem?_alter (since := "2025-02-09")]
theorem get?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    get? (alter m k f) k' =
      if k == k' then
        f (get? m k)
      else
        get? m k' :=
  DHashMap.Const.get?_alter

@[simp]
theorem getElem?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f)[k]? = f m[k]? :=
  DHashMap.Const.get?_alter_self

@[deprecated getElem?_alter_self (since := "2025-02-09")]
theorem get?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    get? (alter m k f) k = f (get? m k) :=
  DHashMap.Const.get?_alter_self

theorem getElem_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    {h : k' ∈ alter m k f} :
    (alter m k f)[k'] =
      if heq : k == k' then
        haveI h' : (f m[k]?).isSome := mem_alter_of_beq heq |>.mp h
        f m[k]? |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m[(k')]'h' :=
  DHashMap.Const.get_alter

@[deprecated getElem_alter (since := "2025-02-09")]
theorem get_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    {h : k' ∈ alter m k f} :
    get (alter m k f) k' h =
      if heq : k == k' then
        haveI h' : (f (get? m k)).isSome := mem_alter_of_beq heq |>.mp h
        f (get? m k) |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        get m k' h' :=
  DHashMap.Const.get_alter

@[simp]
theorem getElem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    {h : k ∈ alter m k f} :
    haveI h' : (f m[k]?).isSome := mem_alter_self.mp h
    (alter m k f)[k] = (f m[k]?).get h' :=
  DHashMap.Const.get_alter_self

@[deprecated getElem_alter_self (since := "2025-02-09")]
theorem get_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    {h : k ∈ alter m k f} :
    haveI h' : (f (get? m k)).isSome := mem_alter_self.mp h
    get (alter m k f) k h = (f (get? m k)).get h' :=
  DHashMap.Const.get_alter_self

theorem getElem!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} : (alter m k f)[k']! =
      if k == k' then
        f m[k]? |>.get!
      else
        m[k']! :=
  DHashMap.Const.get!_alter

@[deprecated getElem!_alter (since := "2025-02-09")]
theorem get!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} : get! (alter m k f) k' =
      if k == k' then
        f (get? m k) |>.get!
      else
        get! m k' :=
  DHashMap.Const.get!_alter

@[simp]
theorem getElem!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} : (alter m k f)[k]! = (f m[k]?).get! :=
  DHashMap.Const.get!_alter_self

@[deprecated getElem!_alter_self (since := "2025-02-09")]
theorem get!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} : get! (alter m k f) k = (f (get? m k)).get! :=
  DHashMap.Const.get!_alter_self

theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter m k f) k' fallback =
      if k == k' then
        f m[k]? |>.getD fallback
      else
        getD m k' fallback :=
  DHashMap.Const.getD_alter

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter m k f) k fallback = (f m[k]?).getD fallback :=
  DHashMap.Const.getD_alter_self

theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (alter m k f).getKey? k' =
      if k == k' then
        if (f m[k]?).isSome then some k else none
      else
        m.getKey? k' :=
  DHashMap.Const.getKey?_alter

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).getKey? k = if (f m[k]?).isSome then some k else none :=
  DHashMap.Const.getKey?_alter_self

theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} : (alter m k f).getKey! k' =
      if k == k' then
        if (f m[k]?).isSome then k else default
      else
        m.getKey! k' :=
  DHashMap.Const.getKey!_alter

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (alter m k f).getKey! k = if (f m[k]?).isSome then k else default :=
  DHashMap.Const.getKey!_alter_self

theorem getKey_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} {h : k' ∈ alter m k f} :
    (alter m k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  DHashMap.Const.getKey_alter

@[simp]
theorem getKey_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} {h : k ∈ alter m k f} :
    (alter m k f).getKey k h = k :=
  DHashMap.Const.getKey_alter_self

theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    {f : Option β → Option β} :
    (alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f m[k]?).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  DHashMap.Const.getKeyD_alter

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : Option β → Option β} :
    (alter m k f).getKeyD k fallback = if (f m[k]?).isSome then k else fallback :=
  DHashMap.Const.getKeyD_alter_self

end Alter

section Modify

variable {m : HashMap α β}

@[simp]
theorem isEmpty_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f).isEmpty = m.isEmpty :=
  DHashMap.Const.isEmpty_modify

@[simp]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    (modify m k f).contains k' = m.contains k' :=
  DHashMap.Const.contains_modify

@[simp]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    k' ∈ modify m k f ↔ k' ∈ m :=
  DHashMap.Const.mem_modify

@[simp]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f).size = m.size :=
  DHashMap.Const.size_modify

theorem getElem?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    (modify m k f)[k']? =
      if k == k' then
        m[k]?.map f
      else
        m[k']? :=
  DHashMap.Const.get?_modify

@[deprecated getElem?_modify (since := "2025-02-09")]
theorem get?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    get? (modify m k f) k' =
      if k == k' then
        get? m k |>.map f
      else
        get? m k' :=
  DHashMap.Const.get?_modify

@[simp]
theorem getElem?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f)[k]? = m[k]?.map f :=
  DHashMap.Const.get?_modify_self

@[deprecated getElem?_modify_self (since := "2025-02-09")]
theorem get?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    get? (modify m k f) k = (get? m k).map f :=
  DHashMap.Const.get?_modify_self

theorem getElem_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    {h : k' ∈ modify m k f} :
    (modify m k f)[k'] =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        f m[k]
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m[k'] :=
  DHashMap.Const.get_modify

@[deprecated getElem_modify (since := "2025-02-09")]
theorem get_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    {h : k' ∈ modify m k f} :
    get (modify m k f) k' h =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        f (get m k h')
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        get m k' h' :=
  DHashMap.Const.get_modify

@[simp]
theorem getElem_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    (modify m k f)[k] = f m[k] :=
  DHashMap.Const.get_modify_self

@[deprecated getElem_modify_self (since := "2025-02-09")]
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    get (modify m k f) k h = f (get m k h') :=
  DHashMap.Const.get_modify_self

theorem getElem!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    (modify m k f)[k']! =
      if k == k' then
        m[k]?.map f |>.get!
      else
        m[k']! :=
  DHashMap.Const.get!_modify

@[deprecated getElem!_modify (since := "2025-02-09")]
theorem get!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    get! (modify m k f) k' =
      if k == k' then
        get? m k |>.map f |>.get!
      else
        get! m k' :=
  DHashMap.Const.get!_modify

@[simp]
theorem getElem!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} :
    (modify m k f)[k]! = (m[k]?.map f).get! :=
  DHashMap.Const.get!_modify_self

@[deprecated getElem!_modify_self (since := "2025-02-09")]
theorem get!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} :
    get! (modify m k f) k = ((get? m k).map f).get! :=
  DHashMap.Const.get!_modify_self

theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} :
    getD (modify m k f) k' fallback =
      if k == k' then
        m[k]?.map f |>.getD fallback
      else
        getD m k' fallback :=
  DHashMap.Const.getD_modify

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} :
    getD (modify m k f) k fallback = (m[k]?.map f).getD fallback :=
  DHashMap.Const.getD_modify_self

theorem getKey?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    (modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  DHashMap.Const.getKey?_modify

theorem getKey?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f).getKey? k = if k ∈ m then some k else none :=
  DHashMap.Const.getKey?_modify_self

theorem getKey!_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β} :
    (modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  DHashMap.Const.getKey!_modify

theorem getKey!_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β} :
    (modify m k f).getKey! k = if k ∈ m then k else default :=
  DHashMap.Const.getKey!_modify_self

theorem getKey_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    {h : k' ∈ modify m k f} :
    (modify m k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  DHashMap.Const.getKey_modify

@[simp]
theorem getKey_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    {h : k ∈ modify m k f} : (modify m k f).getKey k h = k :=
  DHashMap.Const.getKey_modify_self

theorem getKeyD_modify [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} :
    (modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  DHashMap.Const.getKeyD_modify

theorem getKeyD_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : β → β} : (modify m k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  DHashMap.Const.getKeyD_modify_self

end Modify

namespace Equiv

variable {m m₁ m₂ m₃ : HashMap α β}

@[refl, simp] theorem refl (m : HashMap α β) : m ~m m := ⟨.rfl⟩
theorem rfl : m ~m m := ⟨.rfl⟩
@[symm] theorem symm : m₁ ~m m₂ → m₂ ~m m₁
  | ⟨h⟩ => ⟨h.symm⟩
theorem trans : m₁ ~m m₂ → m₂ ~m m₃ → m₁ ~m m₃
  | ⟨h₁⟩, ⟨h₂⟩ => ⟨h₁.trans h₂⟩

instance instTrans : Trans (α := HashMap α β) Equiv Equiv Equiv := ⟨trans⟩

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
  h.1.constToList_perm

theorem of_toList_perm (h : m₁.toList.Perm m₂.toList) : m₁ ~m m₂ :=
  ⟨.of_constToList_perm h⟩

theorem keys_perm (h : m₁ ~m m₂) : m₁.keys.Perm m₂.keys :=
  h.1.keys_perm

theorem of_keys_unit_perm {m₁ m₂ : HashMap α Unit} (h : m₁.keys.Perm m₂.keys) : m₁ ~m m₂ :=
  ⟨.of_keys_unit_perm h⟩

theorem getElem?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁[k]? = m₂[k]? :=
  h.1.constGet?_eq

theorem getElem_eq [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁ ~m m₂) :
    m₁[k] = m₂[k]'(h.mem_iff.mp hk) :=
  h.1.constGet_eq hk

theorem getElem!_eq [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (h : m₁ ~m m₂) :
    m₁[k]! = m₂[k]! :=
  h.1.constGet!_eq

theorem getD_eq [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (h : m₁ ~m m₂) :
    m₁.getD k fallback = m₂.getD k fallback :=
  h.1.constGetD_eq

theorem getKey?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁.getKey? k = m₂.getKey? k :=
  h.1.getKey?_eq

theorem getKey_eq [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁ ~m m₂) :
    m₁.getKey k hk = m₂.getKey k (h.mem_iff.mp hk) :=
  h.1.getKey_eq hk

theorem getKey!_eq [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h : m₁ ~m m₂) :
    m₁.getKey! k = m₂.getKey! k :=
  h.1.getKey!_eq

theorem getKeyD_eq [EquivBEq α] [LawfulHashable α] {k fallback : α} (h : m₁ ~m m₂) :
    m₁.getKeyD k fallback = m₂.getKeyD k fallback :=
  h.1.getKeyD_eq

theorem insert [EquivBEq α] [LawfulHashable α] (k : α) (v : β) (h : m₁ ~m m₂) :
    m₁.insert k v ~m m₂.insert k v :=
  ⟨h.1.insert (β := fun _ => β) k v⟩

theorem erase [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁ ~m m₂) :
    m₁.erase k ~m m₂.erase k :=
  ⟨h.1.erase k⟩

theorem insertIfNew [EquivBEq α] [LawfulHashable α] (k : α) (v : β) (h : m₁ ~m m₂) :
    m₁.insertIfNew k v ~m m₂.insertIfNew k v :=
  ⟨h.1.insertIfNew (β := fun _ => β) k v⟩

theorem insertMany_list [EquivBEq α] [LawfulHashable α] (l : List (α × β)) (h : m₁ ~m m₂) :
    m₁.insertMany l ~m m₂.insertMany l :=
  ⟨h.1.constInsertMany_list l⟩

theorem insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] {m₁ m₂ : HashMap α Unit}
    (l : List α) (h : m₁ ~m m₂) :
    m₁.insertManyIfNewUnit l ~m m₂.insertManyIfNewUnit l :=
  ⟨h.1.constInsertManyIfNewUnit_list l⟩

theorem alter [EquivBEq α] [LawfulHashable α] (k : α) (f : Option β → Option β) (h : m₁ ~m m₂) :
    m₁.alter k f ~m m₂.alter k f :=
  ⟨h.1.constAlter k f⟩

theorem modify [EquivBEq α] [LawfulHashable α] (k : α) (f : β → β) (h : m₁ ~m m₂) :
    m₁.modify k f ~m m₂.modify k f :=
  ⟨h.1.constModify k f⟩

theorem filter (f : α → β → Bool) (h : m₁ ~m m₂) : m₁.filter f ~m m₂.filter f :=
  ⟨h.1.filter f⟩

theorem map (f : α → β → γ) (h : m₁ ~m m₂) : m₁.map f ~m m₂.map f :=
  ⟨h.1.map f⟩

theorem filterMap (f : α → β → Option γ) (h : m₁ ~m m₂) : m₁.filterMap f ~m m₂.filterMap f :=
  ⟨h.1.filterMap f⟩

theorem of_forall_getKey_eq_of_forall_getElem?_eq [EquivBEq α] [LawfulHashable α]
    (hk : ∀ k hk hk', m₁.getKey k hk = m₂.getKey k hk') (hv : ∀ k : α, m₁[k]? = m₂[k]?) :
    m₁ ~m m₂ :=
  ⟨.of_forall_getKey_eq_of_forall_constGet?_eq hk hv⟩

set_option linter.deprecated false in
@[deprecated of_forall_getKey_eq_of_forall_getElem?_eq (since := "2025-04-25")]
theorem of_forall_getKey?_eq_of_forall_getElem?_eq [EquivBEq α] [LawfulHashable α]
    (hk : ∀ k, m₁.getKey? k = m₂.getKey? k) (hv : ∀ k : α, m₁[k]? = m₂[k]?) :
    m₁ ~m m₂ :=
  ⟨.of_forall_getKey?_eq_of_forall_constGet?_eq hk hv⟩

theorem of_forall_getElem?_eq [LawfulBEq α] (h : ∀ k : α, m₁[k]? = m₂[k]?) : m₁ ~m m₂ :=
  ⟨.of_forall_constGet?_eq h⟩

theorem of_forall_getKey?_unit_eq [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : HashMap α Unit} (h : ∀ k, m₁.getKey? k = m₂.getKey? k) : m₁ ~m m₂ :=
  ⟨.of_forall_getKey?_unit_eq h⟩

theorem of_forall_contains_unit_eq [LawfulBEq α]
    {m₁ m₂ : HashMap α Unit} (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ ~m m₂ :=
  ⟨.of_forall_contains_unit_eq h⟩

theorem of_forall_mem_unit_iff [LawfulBEq α]
    {m₁ m₂ : HashMap α Unit} (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ ~m m₂ :=
  ⟨.of_forall_mem_unit_iff h⟩

end Equiv

section Equiv

variable {m m₁ m₂ : HashMap α β}

@[simp]
theorem equiv_emptyWithCapacity_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} :
    m ~m emptyWithCapacity c ↔ m.isEmpty :=
  ⟨fun ⟨h⟩ => DHashMap.equiv_emptyWithCapacity_iff_isEmpty.mp h,
    fun h => ⟨DHashMap.equiv_emptyWithCapacity_iff_isEmpty.mpr h⟩⟩

@[simp]
theorem equiv_empty_iff_isEmpty [EquivBEq α] [LawfulHashable α] : m ~m ∅ ↔ m.isEmpty :=
  equiv_emptyWithCapacity_iff_isEmpty

set_option linter.missingDocs false in
@[deprecated equiv_empty_iff_isEmpty (since := "2025-03-12")]
abbrev equiv_emptyc_iff_isEmpty := @equiv_empty_iff_isEmpty

@[simp]
theorem emptyWithCapacity_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} :
    emptyWithCapacity c ~m m ↔ m.isEmpty :=
  Equiv.comm.trans equiv_emptyWithCapacity_iff_isEmpty

@[simp]
theorem empty_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] : ∅ ~m m ↔ m.isEmpty :=
  emptyWithCapacity_equiv_iff_isEmpty

set_option linter.missingDocs false in
@[deprecated empty_equiv_iff_isEmpty (since := "2025-03-12")]
abbrev emptyc_equiv_iff_isEmpty := @empty_equiv_iff_isEmpty

theorem equiv_iff_toList_perm [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ m₁.toList.Perm m₂.toList :=
  ⟨Equiv.toList_perm, Equiv.of_toList_perm⟩

theorem equiv_iff_keys_unit_perm {m₁ m₂ : HashMap α Unit} [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ m₁.keys.Perm m₂.keys :=
  ⟨Equiv.keys_perm, Equiv.of_keys_unit_perm⟩

end Equiv

section filterMap

variable {m : HashMap α β}

theorem toList_filterMap {f : (a : α) → β → Option γ} :
    (m.filterMap f).toList.Perm
      (m.toList.filterMap (fun p => (f p.1 p.2).map (fun x => (p.1, x)))) :=
  DHashMap.Const.toList_filterMap

theorem isEmpty_filterMap_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).isEmpty ↔ ∀ k h, f (m.getKey k h) m[k] = none :=
  DHashMap.Const.isEmpty_filterMap_iff

theorem isEmpty_filterMap_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).isEmpty = false ↔ ∃ k h, (f (m.getKey k h) m[k]).isSome :=
  DHashMap.Const.isEmpty_filterMap_eq_false_iff

theorem mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f (m.getKey k h) m[k]).isSome :=
  DHashMap.Const.mem_filterMap

theorem contains_of_contains_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).contains k = true → m.contains k = true :=
  DHashMap.contains_of_contains_filterMap

theorem mem_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f → k ∈ m :=
  DHashMap.mem_of_mem_filterMap

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).size ≤ m.size :=
  DHashMap.size_filterMap_le_size

theorem size_filterMap_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).size = m.size ↔ ∀ k h, (f (m.getKey k h) m[k]).isSome :=
  DHashMap.Const.size_filterMap_eq_size_iff

theorem getElem?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f)[k]? = m[k]?.pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x) :=
  DHashMap.Const.get?_filterMap

theorem getElem?_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.filterMap f)[k]? = m[k]?.bind (f k') :=
  DHashMap.Const.get?_filterMap_of_getKey?_eq_some h

theorem isSome_apply_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ m.filterMap f),
      (f (m.getKey k (mem_of_mem_filterMap h))
        (m[k]'(mem_of_mem_filterMap h))).isSome :=
  DHashMap.Const.isSome_apply_of_mem_filterMap

@[simp]
theorem getElem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    (m.filterMap f)[k]'h =
      (f (m.getKey k (mem_of_mem_filterMap h))
        (m[k]'(mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  DHashMap.Const.get_filterMap

theorem getElem!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f)[k]! =
      (m[k]?.pbind (fun x h' =>
        f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  DHashMap.Const.get!_filterMap

theorem getElem!_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.filterMap f)[k]! = (m[k]?.bind (f k')).get! :=
  DHashMap.Const.get!_filterMap_of_getKey?_eq_some h

theorem getD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    (m.filterMap f).getD k fallback =
      (m[k]?.pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  DHashMap.Const.getD_filterMap

theorem getD_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    (m.filterMap f).getD k fallback = (m[k]?.bind (f k')).getD fallback :=
  DHashMap.Const.getD_filterMap_of_getKey?_eq_some h

theorem getKey?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))).isSome) :=
  DHashMap.Const.getKey?_filterMap

@[simp]
theorem getKey_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h'} :
    (m.filterMap f).getKey k h' = m.getKey k (mem_of_mem_filterMap h') :=
  DHashMap.getKey_filterMap

theorem getKey!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))).isSome)).get! :=
  DHashMap.Const.getKey!_filterMap

theorem getKeyD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  DHashMap.Const.getKeyD_filterMap

end filterMap

section filter

variable {m : HashMap α β}

theorem filterMap_equiv_filter {f : α → β → Bool} :
    (m.filterMap (fun k => Option.guard (fun v => f k v))) ~m m.filter f :=
  ⟨DHashMap.filterMap_equiv_filter⟩

theorem toList_filter {f : α → β → Bool} :
    (m.filter f).toList.Perm (m.toList.filter (fun p => f p.1 p.2)) :=
  DHashMap.Const.toList_filter

theorem keys_filter_key {f : α → Bool} :
    (m.filter fun k _ => f k).keys.Perm (m.keys.filter f) :=
  DHashMap.keys_filter_key

theorem isEmpty_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = false :=
  DHashMap.Const.isEmpty_filter_iff

theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = true :=
  DHashMap.Const.isEmpty_filter_eq_false_iff

theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ (h' : k ∈ m), f (m.getKey k h') m[k] :=
  DHashMap.Const.mem_filter

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).contains k = true → m.contains k = true :=
  DHashMap.contains_of_contains_filter

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f → k ∈ m :=
  DHashMap.mem_of_mem_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size ≤ m.size :=
  DHashMap.size_filter_le_size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f (m.getKey k h) (m.get k h) :=
  DHashMap.Const.size_filter_eq_size_iff

theorem filter_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    m.filter f ~m m ↔ ∀ k h, f (m.getKey k h) (m.get k h) :=
  ⟨fun h => DHashMap.Const.filter_equiv_self_iff.mp h.1,
    fun h => ⟨DHashMap.Const.filter_equiv_self_iff.mpr h⟩⟩

theorem getElem?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f)[k]? = m[k]?.pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x) :=
  DHashMap.Const.get?_filter

theorem getElem?_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      (m.filter f)[k]? = m[k]?.filter (fun x => f k' x) :=
  DHashMap.Const.get?_filter_of_getKey?_eq_some

@[simp]
theorem getElem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} :
    (m.filter f)[k]'(h') = m[k]'(mem_of_mem_filter h') :=
  DHashMap.Const.get_filter

theorem getElem!_filter [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    (m.filter f)[k]! =
      (m[k]?.pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  DHashMap.Const.get!_filter

theorem getElem!_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      (m.filter f)[k]! = (m[k]?.filter (f k')).get! :=
  DHashMap.Const.get!_filter_of_getKey?_eq_some

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} :
    (m.filter f).getD k fallback = (m[k]?.pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  DHashMap.Const.getD_filter

theorem getD_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} {fallback : β} :
    m.getKey? k = some k' →
      (m.filter f).getD k fallback =
        (m[k]?.filter (fun x => f k' x)).getD fallback :=
  DHashMap.Const.getD_filter_of_getKey?_eq_some

theorem keys_filter [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    (m.filter f).keys.Perm
      (m.keys.attach.filter (fun ⟨x, h'⟩ => f x (get m x (mem_of_mem_keys h')))).unattach :=
  DHashMap.Const.keys_filter

theorem getKey?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h')))) :=
  DHashMap.Const.getKey?_filter

theorem getKey?_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f :=
  DHashMap.getKey?_filter_key

@[simp]
theorem getKey_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} :
    (m.filter f).getKey k h' = m.getKey k (mem_of_mem_filter h') :=
  DHashMap.getKey_filter

theorem getKey!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))))).get! :=
  DHashMap.Const.getKey!_filter

theorem getKey!_filter_key [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! :=
  DHashMap.getKey!_filter_key

theorem getKeyD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))))).getD fallback :=
  DHashMap.Const.getKeyD_filter

theorem getKeyD_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback :=
  DHashMap.getKeyD_filter_key

end filter

section map

variable {m : HashMap α β}

theorem map_id_equiv : m.map (fun _ v => v) ~m m :=
  ⟨DHashMap.map_id_equiv⟩

theorem map_map_equiv {f : α → β → γ} {g : α → γ → δ} :
    (m.map f).map g ~m m.map fun k v => g k (f k v) :=
  ⟨DHashMap.map_map_equiv⟩

theorem toList_map {f : α → β → γ} :
    (m.map f).toList.Perm (m.toList.map (fun p => (p.1, f p.1 p.2))) :=
  DHashMap.Const.toList_map

theorem keys_map {f : α → β → γ} : (m.map f).keys.Perm m.keys :=
  DHashMap.keys_map

theorem filterMap_equiv_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} :
    (m.filterMap (fun k v => some (f k v))) ~m m.map f :=
  ⟨DHashMap.filterMap_equiv_map⟩

@[simp]
theorem isEmpty_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} :
    (m.map f).isEmpty = m.isEmpty :=
  DHashMap.isEmpty_map

@[simp]
theorem contains_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f).contains k = m.contains k :=
  DHashMap.contains_map

theorem contains_of_contains_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f).contains k = true → m.contains k = true :=
  DHashMap.contains_of_contains_map

@[simp]
theorem mem_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    k ∈ m.map f ↔ k ∈ m := by
  simp only [mem_iff_contains, contains_map]

theorem mem_of_mem_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    k ∈ m.map f → k ∈ m :=
  DHashMap.contains_of_contains_map

@[simp]
theorem size_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} :
    (m.map f).size = m.size :=
  DHashMap.size_map

@[simp]
theorem getElem?_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) :=
  DHashMap.Const.get?_map

/-- Variant of `getElem?_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem getElem?_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h')) :=
  DHashMap.Const.get?_map'

theorem getElem?_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.map f)[k]? = m[k]?.map (f k') :=
  DHashMap.Const.get?_map_of_getKey?_eq_some h

@[simp]
theorem getElem_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    (m.map f)[k]'(h') =
      f k (m[k]'(mem_of_mem_map h')) :=
  DHashMap.Const.get_map

/-- Variant of `getElem_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem getElem_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    (m.map f)[k]'(h') =
      f (m.getKey k (mem_of_mem_map h')) (m[k]'(mem_of_mem_map h')) :=
  DHashMap.Const.get_map'

theorem getElem!_map [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]! =
      (m[k]?.map (f k)).get! :=
  DHashMap.Const.get!_map

/-- Variant of `getElem!_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getElem!_map' [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]! =
      (m[k]?.pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_mem h'))).get! :=
  DHashMap.Const.get!_map'

theorem getElem!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.map f)[k]! = (m[k]?.map (f k')).get! :=
  DHashMap.Const.get!_map_of_getKey?_eq_some h

theorem getD_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    (m.map f).getD k fallback =
      (m[k]?.map (f k)).getD fallback :=
  DHashMap.Const.getD_map

/-- Variant of `getD_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getD_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    (m.map f).getD k fallback =
      (m[k]?.pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  DHashMap.Const.getD_map'

theorem getD_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    (m.map f).getD k fallback = (m[k]?.map (f k')).getD fallback :=
  DHashMap.Const.getD_map_of_getKey?_eq_some h

@[simp]
theorem getKey?_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f).getKey? k = m.getKey? k :=
  DHashMap.getKey?_map

@[simp]
theorem getKey_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    (m.map f).getKey k h' = m.getKey k (mem_of_mem_map h') :=
  DHashMap.getKey_map

@[simp]
theorem getKey!_map [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → γ} {k : α} :
    (m.map f).getKey! k = m.getKey! k :=
  DHashMap.getKey!_map

@[simp]
theorem getKeyD_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k fallback : α} :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback :=
  DHashMap.getKeyD_map

end map

end Std.HashMap
