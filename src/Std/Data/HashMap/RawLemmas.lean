/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Std.Data.DHashMap.RawLemmas
public import Std.Data.HashMap.Raw
import all Std.Data.DHashMap.Raw
import Init.Data.List.Pairwise

@[expose] public section

/-!
# Hash map lemmas

This module contains lemmas about `Std.Data.HashMap.Raw`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'}

namespace Std.HashMap

namespace Raw

variable {m : Raw α β}

@[simp, grind =]
theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α β).size = 0 :=
  DHashMap.Raw.size_emptyWithCapacity

@[simp, grind =]
theorem size_empty : (∅ : Raw α β).size = 0 :=
  DHashMap.Raw.size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) :=
  DHashMap.Raw.isEmpty_eq_size_eq_zero

@[simp]
theorem toList_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α β).toList = [] :=
  DHashMap.Raw.Const.toList_emptyWithCapacity

@[simp]
theorem toList_empty : (∅ : Raw α β).toList = [] :=
  toList_emptyWithCapacity

@[simp]
theorem keys_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α β).keys = [] :=
  DHashMap.Raw.keys_emptyWithCapacity

@[simp]
theorem keys_empty : (∅ : Raw α β).keys = [] :=
  keys_emptyWithCapacity

@[simp]
theorem values_emptyWithCapacity {c} {β : Type v} : (emptyWithCapacity c : Raw α β).values = [] :=
  DHashMap.Raw.Const.values_emptyWithCapacity

@[simp]
theorem values_empty {β : Type v} : (∅ : Raw α β).values = [] :=
  values_emptyWithCapacity

private theorem ext {m m' : Raw α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

variable [BEq α] [Hashable α]

@[simp, grind =]
theorem isEmpty_emptyWithCapacity {c} : (emptyWithCapacity c : Raw α β).isEmpty :=
  DHashMap.Raw.isEmpty_emptyWithCapacity

@[simp, grind =]
theorem isEmpty_empty : (∅ : Raw α β).isEmpty :=
  DHashMap.Raw.isEmpty_empty

@[simp, grind =]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).isEmpty = false :=
  DHashMap.Raw.isEmpty_insert h.out

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  DHashMap.Raw.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m :=
  DHashMap.Raw.contains_iff_mem

theorem contains_eq_false_iff_not_mem {k : α} : m.contains k = false ↔ ¬k ∈ m :=
  DHashMap.Raw.contains_eq_false_iff_not_mem

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  DHashMap.Raw.contains_congr h.out hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m :=
  DHashMap.Raw.mem_congr h.out hab

@[simp, grind =]
theorem contains_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : Raw α β).contains a = false :=
  DHashMap.Raw.contains_emptyWithCapacity

@[simp, grind ←] theorem not_mem_emptyWithCapacity {a : α} {c} : ¬a ∈ (emptyWithCapacity c : Raw α β) :=
  DHashMap.Raw.not_mem_emptyWithCapacity

@[simp, grind =] theorem contains_empty {a : α} : (∅ : Raw α β).contains a = false :=
  DHashMap.Raw.contains_empty

@[simp] theorem not_mem_empty {a : α} : ¬a ∈ (∅ : Raw α β) :=
  DHashMap.Raw.not_mem_empty

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

@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  DHashMap.Raw.contains_insert h.out

@[simp, grind =]
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

@[grind =] theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  DHashMap.Raw.size_insert h.out

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    m.size ≤ (m.insert k v).size :=
  DHashMap.Raw.size_le_size_insert h.out

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).size ≤ m.size + 1 :=
  DHashMap.Raw.size_insert_le h.out

@[simp, grind =]
theorem erase_emptyWithCapacity {k : α} {c : Nat} : (emptyWithCapacity c : Raw α β).erase k = emptyWithCapacity c :=
  ext DHashMap.Raw.erase_emptyWithCapacity

@[simp, grind =]
theorem erase_empty {k : α} : (∅ : Raw α β).erase k = ∅ :=
  ext DHashMap.Raw.erase_empty

@[simp, grind =]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  DHashMap.Raw.isEmpty_erase h.out

@[simp, grind =]
theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  DHashMap.Raw.contains_erase h.out

@[simp, grind =]
theorem mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  DHashMap.Raw.mem_erase h.out

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a → m.contains a :=
  DHashMap.Raw.contains_of_contains_erase h.out

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k → a ∈ m :=
  DHashMap.Raw.mem_of_mem_erase h.out

@[grind =] theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  DHashMap.Raw.size_erase h.out

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size ≤ m.size :=
  DHashMap.Raw.size_erase_le h.out

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  DHashMap.Raw.size_le_size_erase h.out

@[simp, grind =]
theorem containsThenInsert_fst (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsert k v).1 = m.contains k :=
  DHashMap.Raw.containsThenInsert_fst h.out

@[simp, grind =]
theorem containsThenInsert_snd (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsert k v).2 = m.insert k v :=
  ext (DHashMap.Raw.containsThenInsert_snd h.out)

@[simp, grind =]
theorem containsThenInsertIfNew_fst (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  DHashMap.Raw.containsThenInsertIfNew_fst h.out

@[simp, grind =]
theorem containsThenInsertIfNew_snd (h : m.WF) {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  ext (DHashMap.Raw.containsThenInsertIfNew_snd h.out)

@[simp, grind =] theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
@[simp, grind =] theorem get?_eq_getElem? {a : α} : get? m a = m[a]? := rfl
@[simp, grind =] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! m a = m[a]! := rfl

@[simp, grind =]
theorem getElem?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : Raw α β)[a]? = none :=
  DHashMap.Raw.Const.get?_emptyWithCapacity

@[simp]
theorem getElem?_empty {a : α} : (∅ : Raw α β)[a]? = none :=
  DHashMap.Raw.Const.get?_empty

theorem getElem?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m[a]? = none :=
  DHashMap.Raw.Const.get?_of_isEmpty h.out

@[grind =] theorem getElem?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  DHashMap.Raw.Const.get?_insert h.out

@[simp]
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v)[k]? = some v :=
  DHashMap.Raw.Const.get?_insert_self h.out

theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = m[a]?.isSome :=
  DHashMap.Raw.Const.contains_eq_isSome_get? h.out

@[simp]
theorem isSome_getElem?_eq_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m[a]?.isSome = m.contains a :=
  (contains_eq_isSome_getElem? h).symm

theorem mem_iff_isSome_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    a ∈ m ↔ (m[a]?).isSome :=
  DHashMap.Raw.Const.mem_iff_isSome_get? h.out

@[simp]
theorem isSome_getElem?_iff_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m[a]?).isSome ↔ a ∈ m :=
  (mem_iff_isSome_getElem? h).symm

theorem getElem?_eq_some_iff [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    m[k]? = some v ↔ ∃ h : k ∈ m, m[k] = v :=
  DHashMap.Raw.Const.get?_eq_some_iff h.out

theorem getElem?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m[a]? = none :=
  DHashMap.Raw.Const.get?_eq_none_of_contains_eq_false h.out

theorem getElem?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m[a]? = none :=
  DHashMap.Raw.Const.get?_eq_none h.out

@[grind =] theorem getElem?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k)[a]? = if k == a then none else m[a]? :=
  DHashMap.Raw.Const.get?_erase h.out

@[simp]
theorem getElem?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k)[k]? = none :=
  DHashMap.Raw.Const.get?_erase_self h.out

theorem getElem?_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m[a]? = m[b]? :=
  DHashMap.Raw.Const.get?_congr h.out hab

@[grind =] theorem getElem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insert k v)[a]'h₁ =
      if h₂ : k == a then v else m[a]'(mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Raw.Const.get_insert (h₁ := h₁) h.out

theorem toList_insert_perm [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).toList.Perm (⟨k, v⟩ :: m.toList.filter (¬k == ·.1)) :=
  DHashMap.Raw.Const.toList_insert_perm h.out

theorem keys_insertIfNew_perm [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).keys.Perm (if k ∈ m then m.keys else k :: m.keys) :=
  DHashMap.Raw.keys_insertIfNew_perm h.out

@[simp]
theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v)[k]'(mem_insert_self h) = v :=
  DHashMap.Raw.Const.get_insert_self h.out

@[simp, grind =]
theorem getElem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k)[a]'h' = m[a]'(mem_of_mem_erase h h') :=
  DHashMap.Raw.Const.get_erase (h' := h') h.out

theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} (h' : a ∈ m) :
    m[a]? = some (m[a]'h') :=
  DHashMap.Raw.Const.get?_eq_some_get h.out h'

theorem getElem_eq_get_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h' : a ∈ m} :
    m[a]'(h') = m[a]?.get ((mem_iff_isSome_getElem? h).mp h') :=
  DHashMap.Raw.Const.get_eq_get_get? h.out (h' := h')

@[grind =] theorem get_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h'} :
    m[a]?.get h' = m[a]'((mem_iff_isSome_getElem? h).mpr h') :=
  DHashMap.Raw.Const.get_get? h.out

theorem getElem_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) {h'} :
    m[a]'h' = m[b]'((mem_congr h hab).1 h') :=
  DHashMap.Raw.Const.get_congr h.out hab (h' := h')

@[simp, grind =]
theorem getElem!_emptyWithCapacity [Inhabited β] {a : α} {c} : (emptyWithCapacity c : Raw α β)[a]! = default :=
  DHashMap.Raw.Const.get!_emptyWithCapacity

@[simp, grind =]
theorem getElem!_empty [Inhabited β] {a : α} : (∅ : Raw α β)[a]! = default :=
  DHashMap.Raw.Const.get!_empty

theorem getElem!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    m.isEmpty = true → m[a]! = default :=
  DHashMap.Raw.Const.get!_of_isEmpty h.out

@[grind =] theorem getElem!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α} {v : β} :
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

@[grind =] theorem getElem!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α} :
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

@[simp, grind =]
theorem getD_emptyWithCapacity {a : α} {fallback : β} {c} : (emptyWithCapacity c : Raw α β).getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_emptyWithCapacity

@[simp, grind =]
theorem getD_empty {a : α} {fallback : β} : (∅ : Raw α β).getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  DHashMap.Raw.Const.getD_of_isEmpty h.out

@[grind =] theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback v : β} :
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

@[grind =] theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback : β} :
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

@[simp, grind =]
theorem getKey?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : Raw α β).getKey? a = none :=
  DHashMap.Raw.getKey?_emptyWithCapacity

@[simp, grind =]
theorem getKey?_empty {a : α} : (∅ : Raw α β).getKey? a = none :=
  DHashMap.Raw.getKey?_empty

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  DHashMap.Raw.getKey?_of_isEmpty h.out

@[grind =] theorem getKey?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  DHashMap.Raw.getKey?_insert h.out

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).getKey? k = some k :=
  DHashMap.Raw.getKey?_insert_self h.out

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  DHashMap.Raw.contains_eq_isSome_getKey? h.out

@[simp, grind =]
theorem isSome_getKey?_eq_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.getKey? a).isSome = m.contains a :=
  (contains_eq_isSome_getKey? h).symm

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.getKey? a = none :=
  DHashMap.Raw.getKey?_eq_none_of_contains_eq_false h.out

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey? a = none :=
  DHashMap.Raw.getKey?_eq_none h.out

@[grind =] theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  DHashMap.Raw.getKey?_erase h.out

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).getKey? k = none :=
  DHashMap.Raw.getKey?_erase_self h.out

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.getKey? k).all (· == k) :=
  DHashMap.Raw.getKey?_beq h.out

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} (h' : k == k') :
    m.getKey? k = m.getKey? k' :=
  DHashMap.Raw.getKey?_congr h.out h'

theorem getKey?_eq_some_of_contains [LawfulBEq α] (h : m.WF) {k : α} (h' : m.contains k) :
    m.getKey? k = some k :=
  DHashMap.Raw.getKey?_eq_some_of_contains h.out h'

theorem getKey?_eq_some [LawfulBEq α] (h : m.WF) {k : α} (h' : k ∈ m) : m.getKey? k = some k :=
  DHashMap.Raw.getKey?_eq_some h.out h'

@[grind =] theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then k else m.getKey a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) :=
  DHashMap.Raw.getKey_insert (h₁ := h₁) h.out

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insert k v).getKey k (mem_insert_self h) = k :=
  DHashMap.Raw.getKey_insert_self h.out

theorem mem_iff_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    a ∈ m ↔ (m.getKey? a).isSome :=
  DHashMap.Raw.mem_iff_isSome_getKey? h.out

@[simp]
theorem isSome_getKey?_iff_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.getKey? a).isSome ↔ a ∈ m :=
  (mem_iff_isSome_getKey? h).symm

theorem mem_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] {a a' : α} (h : m.WF) :
    m.getKey? a = some a' → a' ∈ m :=
  DHashMap.Raw.mem_of_getKey?_eq_some h.out

theorem getKey?_eq_some_iff [EquivBEq α] [LawfulHashable α] {k k' : α} (h : m.WF) :
    m.getKey? k = some k' ↔ ∃ h : k ∈ m, m.getKey k h = k' :=
  DHashMap.Raw.getKey?_eq_some_iff h.out

@[simp, grind =]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h h') :=
  DHashMap.Raw.getKey_erase (h' := h') h.out

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} (h' : a ∈ m) :
    m.getKey? a = some (m.getKey a h') :=
  DHashMap.Raw.getKey?_eq_some_getKey h.out h'

theorem getKey_eq_get_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h' : a ∈ m} :
    m.getKey a h' = (m.getKey? a).get ((mem_iff_isSome_getKey? h).mp h') :=
  DHashMap.Raw.getKey_eq_get_getKey? h.out

@[simp, grind =]
theorem get_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h'} :
    (m.getKey? a).get h' = m.getKey a ((mem_iff_isSome_getKey? h).mpr h') :=
  DHashMap.Raw.get_getKey? h.out

theorem getKey_beq [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} (h' : k ∈ m) :
    m.getKey k h' == k :=
  DHashMap.Raw.getKey_beq h.out h'

theorem getKey_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k₁ k₂ : α}
    (h' : k₁ == k₂) (h₁ : k₁ ∈ m) :
    m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h h').mp h₁) :=
  DHashMap.Raw.getKey_congr h.out h' h₁

@[simp, grind =]
theorem getKey_eq [LawfulBEq α] (h : m.WF) {k : α} (h' : k ∈ m) :
    m.getKey k h' = k :=
  DHashMap.Raw.getKey_eq h.out h'

@[simp, grind =]
theorem getKey!_emptyWithCapacity [Inhabited α] {a : α} {c} : (emptyWithCapacity c : Raw α β).getKey! a = default :=
  DHashMap.Raw.getKey!_emptyWithCapacity

@[simp, grind =]
theorem getKey!_empty [Inhabited α] {a : α} : (∅ : Raw α β).getKey! a = default :=
  DHashMap.Raw.getKey!_empty

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  DHashMap.Raw.getKey!_of_isEmpty h.out

@[grind =] theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} {v : β} :
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

@[grind =] theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} :
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

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k k' : α}
    (h' : k == k') : m.getKey! k = m.getKey! k' :=
  DHashMap.Raw.getKey!_congr h.out h'

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] (h : m.WF) {k : α} (h' : m.contains k) :
    m.getKey! k = k :=
  DHashMap.Raw.getKey!_eq_of_contains h.out h'

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] (h : m.WF) {k : α} (h' : k ∈ m) :
    m.getKey! k = k :=
  DHashMap.Raw.getKey!_eq_of_mem h.out h'

@[simp, grind =]
theorem getKeyD_emptyWithCapacity {a fallback : α} {c} :
    (emptyWithCapacity c : Raw α β).getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_emptyWithCapacity

@[simp, grind =]
theorem getKeyD_empty {a fallback : α} : (∅ : Raw α β).getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_empty

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  DHashMap.Raw.getKeyD_of_isEmpty h.out

@[grind =] theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} {v : β} :
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

@[grind =] theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
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

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' fallback : α}
    (h' : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback :=
  DHashMap.Raw.getKeyD_congr h.out h'

theorem getKeyD_eq_of_contains [LawfulBEq α] (h : m.WF) {k fallback : α} (h' : m.contains k) :
    m.getKeyD k fallback = k :=
  DHashMap.Raw.getKeyD_eq_of_contains h.out h'

theorem getKeyD_eq_of_mem [LawfulBEq α] (h : m.WF) {k fallback : α} (h' : k ∈ m) :
    m.getKeyD k fallback = k :=
  DHashMap.Raw.getKeyD_eq_of_mem h.out h'

@[simp, grind =]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).isEmpty = false :=
  DHashMap.Raw.isEmpty_insertIfNew h.out

@[simp, grind =]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  DHashMap.Raw.contains_insertIfNew h.out

@[simp, grind =]
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

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `getElem_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α}
    {v : β} : (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  DHashMap.Raw.contains_of_contains_insertIfNew' h.out

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `getElem_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  DHashMap.Raw.mem_of_mem_insertIfNew' h.out

@[grind =] theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  DHashMap.Raw.size_insertIfNew h.out

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    m.size ≤ (m.insertIfNew k v).size :=
  DHashMap.Raw.size_le_size_insertIfNew h.out

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  DHashMap.Raw.size_insertIfNew_le h.out

@[grind =] theorem getElem?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v)[a]? = if k == a ∧ ¬k ∈ m then some v else m[a]? :=
  DHashMap.Raw.Const.get?_insertIfNew h.out

@[grind =] theorem getElem_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insertIfNew k v)[a]'h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else m[a]'(mem_of_mem_insertIfNew' h h₁ h₂) :=
  DHashMap.Raw.Const.get_insertIfNew h.out (h₁ := h₁)

@[grind =] theorem getElem!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α}
    {v : β} : (m.insertIfNew k v)[a]! = if k == a ∧ ¬k ∈ m then v else m[a]! :=
  DHashMap.Raw.Const.get!_insertIfNew h.out

@[grind =] theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback v : β} :
    (m.insertIfNew k v).getD a fallback =
      if k == a ∧ ¬k ∈ m then v else m.getD a fallback :=
  DHashMap.Raw.Const.getD_insertIfNew h.out

@[grind =] theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).getKey? a = if k == a ∧ ¬k ∈ m then some k else m.getKey? a :=
  DHashMap.Raw.getKey?_insertIfNew h.out

@[grind =] theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    (m.insertIfNew k v).getKey a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  DHashMap.Raw.getKey_insertIfNew h.out

@[grind =] theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).getKey! a = if k == a ∧ ¬k ∈ m then k else m.getKey! a :=
  DHashMap.Raw.getKey!_insertIfNew h.out

@[grind =] theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} {v : β} :
    (m.insertIfNew k v).getKeyD a fallback = if k == a ∧ ¬k ∈ m then k else m.getKeyD a fallback :=
  DHashMap.Raw.getKeyD_insertIfNew h.out

@[simp, grind =]
theorem getThenInsertIfNew?_fst (h : m.WF) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).1 = m[k]? :=
  DHashMap.Raw.Const.getThenInsertIfNew?_fst h.out

@[simp, grind =]
theorem getThenInsertIfNew?_snd (h : m.WF) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  ext (DHashMap.Raw.Const.getThenInsertIfNew?_snd h.out)

@[simp, grind =]
theorem length_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.length = m.size :=
  DHashMap.Raw.length_keys h.out

@[simp, grind =]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.isEmpty = m.isEmpty :=
  DHashMap.Raw.isEmpty_keys h.out

@[simp, grind =]
theorem contains_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.keys.contains k = m.contains k :=
  DHashMap.Raw.contains_keys h.out

@[simp, grind =]
theorem mem_keys [LawfulBEq α] (h : m.WF) {k : α} :
    k ∈ m.keys ↔ k ∈ m :=
  DHashMap.Raw.mem_keys h.out

theorem mem_of_mem_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    k ∈ m.keys → k ∈ m :=
  DHashMap.Raw.mem_of_mem_keys h.out

theorem distinct_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.Pairwise (fun a b => (a == b) = false) :=
  DHashMap.Raw.distinct_keys h.out

theorem nodup_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.Nodup :=
  (m.distinct_keys h).imp ne_of_beq_false

@[simp]
theorem toArray_keys (h : m.WF) :
    m.keys.toArray = m.keysArray :=
  DHashMap.Raw.toArray_keys h.out

@[simp]
theorem toList_keysArray (h : m.WF) :
    m.keysArray.toList = m.keys :=
  DHashMap.Raw.toList_keysArray h.out

@[simp]
theorem size_keysArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysArray.size = m.size :=
  DHashMap.Raw.size_keysArray h.out

@[simp]
theorem isEmpty_keysArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysArray.isEmpty = m.isEmpty :=
  DHashMap.Raw.isEmpty_keysArray h.out

@[simp]
theorem contains_keysArray [EquivBEq α] [LawfulHashable α]
    {k : α} (h : m.WF) :
    m.keysArray.contains k = m.contains k :=
  DHashMap.Raw.contains_keysArray h.out

@[simp]
theorem mem_keysArray [LawfulBEq α] {k : α} (h : m.WF) :
    k ∈ m.keysArray ↔ k ∈ m :=
  DHashMap.Raw.mem_keysArray h.out

theorem forall_mem_keysArray_iff_forall_mem_getKey [EquivBEq α] [LawfulHashable α]
    {p : α → Prop} (h : m.WF) :
    (∀ k ∈ m.keysArray, p k) ↔ ∀ (k : α) (h : k ∈ m), p (m.getKey k h) :=
  DHashMap.Raw.forall_mem_keysArray_iff_forall_mem_getKey h.out

theorem contains_of_mem_keysArray [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α}
    (h' : k ∈ m.keysArray) : m.contains k :=
  DHashMap.Raw.contains_of_mem_keysArray h.out h'

@[simp, grind _=_]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.map Prod.fst = m.keys :=
  DHashMap.Raw.Const.map_fst_toList_eq_keys h.out

@[simp, grind =]
theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.length = m.size :=
  DHashMap.Raw.Const.length_toList h.out

@[simp, grind =]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.isEmpty = m.isEmpty :=
  DHashMap.Raw.Const.isEmpty_toList h.out

@[simp, grind =]
theorem mem_toList_iff_getElem?_eq_some [LawfulBEq α] (h : m.WF)
    {k : α} {v : β} :
    (k, v) ∈ m.toList ↔ m[k]? = some v :=
  DHashMap.Raw.Const.mem_toList_iff_get?_eq_some h.out

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} {v : β} :
    (k, v) ∈ m.toList ↔ m.getKey? k = some k ∧ m[k]? = some v :=
  DHashMap.Raw.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some h.out

theorem getElem?_eq_some_iff_exists_beq_and_mem_toList [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {k : α} {v : β} :
    m[k]? = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ m.toList :=
  DHashMap.Raw.Const.get?_eq_some_iff_exists_beq_and_mem_toList h.out

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} {v : β} :
    m.toList.find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ m[k]? = some v :=
  DHashMap.Raw.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some h.out

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} :
    m.toList.find? (·.1 == k) = none ↔ m.contains k = false :=
  DHashMap.Raw.Const.find?_toList_eq_none_iff_contains_eq_false h.out

@[simp]
theorem find?_toList_eq_none_iff_not_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} :
    m.toList.find? (·.1 == k) = none ↔ ¬ k ∈ m :=
  DHashMap.Raw.Const.find?_toList_eq_none_iff_not_mem h.out

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.Pairwise (fun a b => (a.1 == b.1) = false) :=
  DHashMap.Raw.Const.distinct_keys_toList h.out

@[simp]
theorem toArray_toList (h : m.WF) :
    m.toList.toArray = m.toArray :=
  DHashMap.Raw.Const.toArray_toList h.out

@[simp]
theorem toList_toArray (h : m.WF) :
    m.toArray.toList = m.toList :=
  DHashMap.Raw.Const.toList_toArray h.out

@[simp]
theorem map_fst_toArray_eq_keysArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toArray.map Prod.fst = m.keysArray :=
  DHashMap.Raw.Const.map_fst_toArray_eq_keysArray h.out

@[simp]
theorem size_toArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toArray.size = m.size :=
  DHashMap.Raw.Const.size_toArray h.out

@[simp]
theorem isEmpty_toArray [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toArray.isEmpty = m.isEmpty :=
  DHashMap.Raw.Const.isEmpty_toArray h.out

theorem mem_toArray_iff_getElem?_eq_some [LawfulBEq α]
    {k : α} {v : β} (h : m.WF) :
    (k, v) ∈ m.toArray ↔ m[k]? = some v :=
  DHashMap.Raw.Const.mem_toArray_iff_get?_eq_some h.out

theorem getElem?_eq_some_iff_exists_beq_and_mem_toArray [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} (h : m.WF) :
    m[k]? = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ m.toArray :=
  DHashMap.Raw.Const.get?_eq_some_iff_exists_beq_and_mem_toArray h.out

@[deprecated getElem?_eq_some_iff_exists_beq_and_mem_toArray (since := "2025-12-10")]
theorem get?_eq_some_iff_exists_beq_and_mem_toArray [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} (h : m.WF) :
    get? m k = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ m.toArray :=
  DHashMap.Raw.Const.get?_eq_some_iff_exists_beq_and_mem_toArray h.out

theorem find?_toArray_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} {v : β} :
    m.toArray.find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ m[k]? = some v :=
  DHashMap.Raw.Const.find?_toArray_eq_some_iff_getKey?_eq_some_and_get?_eq_some h.out

theorem find?_toArray_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {k : α} (h : m.WF) :
    m.toArray.find? (·.1 == k) = none ↔ m.contains k = false :=
  DHashMap.Raw.Const.find?_toArray_eq_none_iff_contains_eq_false h.out

theorem mem_toArray_iff_getKey?_eq_some_and_getElem?_eq_some [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k: α} {v : β} :
    (k, v) ∈ m.toArray ↔ m.getKey? k = some k ∧ m[k]? = some v := by
  simp [← toArray_toList, h, mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some]

section monadic

variable {m : Raw α β} {δ : Type w} {m' : Type w → Type w'}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → (a : α) → β → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM (fun a b => f a b.1 b.2) init :=
  DHashMap.Raw.Const.foldM_eq_foldlM_toList h.out

theorem fold_eq_foldl_toList (h : m.WF) {f : δ → (a : α) → β → δ} {init : δ} :
    m.fold f init = m.toList.foldl (fun a b => f a b.1 b.2) init :=
  DHashMap.Raw.Const.fold_eq_foldl_toList h.out

omit [BEq α] [Hashable α] in
@[simp, grind =]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : (a : α) → β → m' PUnit} :
    m.forM f = ForM.forM m (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] (h : m.WF) {f : α × β → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  DHashMap.Raw.Const.forMUncurried_eq_forM_toList h.out

omit [BEq α] [Hashable α] in
@[simp, grind =]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : (a : α) → β → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn m init (fun a d => f a.1 a.2 d) := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α × β → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  DHashMap.Raw.Const.forInUncurried_eq_forIn_toList h.out

theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init :=
  DHashMap.Raw.foldM_eq_foldlM_keys h.out

theorem fold_eq_foldl_keys (h : m.WF) {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  DHashMap.Raw.fold_eq_foldl_keys h.out

theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] (h : m.WF) {f : α → m' PUnit} :
    ForM.forM m (fun a => f a.1) = m.keys.forM f :=
  DHashMap.Raw.forM_eq_forM_keys h.out

theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f :=
  DHashMap.Raw.forIn_eq_forIn_keys h.out

theorem foldM_eq_foldlM_keysArray [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} (h : m.WF) :
    m.foldM (fun d a _ => f d a) init = m.keysArray.foldlM f init :=
  DHashMap.Raw.foldM_eq_foldlM_keysArray h.out

theorem fold_eq_foldl_keysArray {f : δ → α → δ} {init : δ} (h : m.WF) :
    m.fold (fun d a _ => f d a) init = m.keysArray.foldl f init :=
  DHashMap.Raw.fold_eq_foldl_keysArray h.out

theorem forM_eq_forM_keysArray [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} (h : m.WF) :
    m.forM (fun a _ => f a) = m.keysArray.forM f :=
  DHashMap.Raw.forM_eq_forM_keysArray h.out

theorem forIn_eq_forIn_keysArray [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} (h : m.WF) :
    m.forIn (fun a _ d => f a d) init = ForIn.forIn m.keysArray init f :=
  DHashMap.Raw.forIn_eq_forIn_keysArray h.out

theorem foldM_eq_foldlM_toArray [Monad m'] [LawfulMonad m']
    {f : δ → α → β → m' δ} {init : δ} (h : m.WF) :
    m.foldM f init = m.toArray.foldlM (fun a b => f a b.1 b.2) init :=
  DHashMap.Raw.Const.foldM_eq_foldlM_toArray h.out

theorem fold_eq_foldl_toArray {f : δ → α → β → δ} {init : δ} (h : m.WF) :
    m.fold f init = m.toArray.foldl (fun a b => f a b.1 b.2) init :=
  DHashMap.Raw.Const.fold_eq_foldl_toArray h.out

theorem forM_eq_forM_toArray [Monad m'] [LawfulMonad m'] {f : α → β → m' PUnit} (h : m.WF) :
    m.forM f = m.toArray.forM (fun a => f a.1 a.2) :=
  DHashMap.Raw.Const.forM_eq_forM_toArray h.out

theorem forIn_eq_forIn_toArray [Monad m'] [LawfulMonad m']
    {f : α → β → δ → m' (ForInStep δ)} {init : δ} (h : m.WF) :
    m.forIn f init = ForIn.forIn m.toArray init (fun a b => f a.1 a.2 b) :=
  DHashMap.Raw.Const.forIn_eq_forIn_toArray h.out

end monadic

theorem all_eq_not_any_not {p : α → β → Bool} (h : m.WF) :
    m.all p = ! m.any (fun a b => ! p a b) := DHashMap.Raw.all_eq_not_any_not h.out

theorem any_eq_not_all_not {p : α → β → Bool} (h : m.WF) :
    m.any p = ! m.all (fun a b => ! p a b) := DHashMap.Raw.any_eq_not_all_not h.out

@[simp]
theorem any_toList {p : α → β → Bool} (h : m.WF) :
    m.toList.any (fun x => p x.1 x.2) = m.any p :=
  DHashMap.Raw.Const.any_toList h.out

theorem any_eq_true_iff_exists_mem_getKey_getElem [LawfulHashable α] [EquivBEq α]
    {p : α → β → Bool} (h : m.WF) :
    m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) :=
  DHashMap.Raw.Const.any_eq_true_iff_exists_contains_getKey_get h.out

theorem any_eq_true_iff_exists_mem_getElem [LawfulBEq α] {p : α → β → Bool} (h : m.WF) :
    m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p a (m[a]'h) :=
  DHashMap.Raw.Const.any_eq_true_iff_exists_contains_get h.out

theorem any_eq_false_iff_forall_mem_getKey_getElem [LawfulHashable α] [EquivBEq α]
    {p : α → β → Bool} (h : m.WF) :
    m.any p = false ↔
      ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false :=
  DHashMap.Raw.Const.any_eq_false_iff_forall_contains_getKey_get h.out

theorem any_eq_false_iff_forall_mem_getElem [LawfulBEq α] {p : α → β → Bool} (h : m.WF) :
    m.any p = false ↔
      ∀ (a : α) (h : a ∈ m), p a (m[a]'h) = false :=
  DHashMap.Raw.Const.any_eq_false_iff_forall_contains_get h.out

@[simp]
theorem all_toList {p : α → β → Bool} (h : m.WF) :
    m.toList.all (fun x => p x.1 x.2) = m.all p :=
  DHashMap.Raw.Const.all_toList h.out

theorem all_eq_true_iff_forall_mem_getKey_getElem [EquivBEq α] [LawfulHashable α]
    {p : α → β → Bool} (h : m.WF) :
    m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) :=
  DHashMap.Raw.Const.all_eq_true_iff_forall_mem_getKey_get h.out

theorem all_eq_true_iff_forall_mem_getElem [LawfulBEq α] {p : α → β → Bool} (h : m.WF) :
    m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h) :=
  DHashMap.Raw.Const.all_eq_true_iff_forall_contains_get h.out

theorem all_eq_false_iff_exists_mem_getKey_getElem [EquivBEq α] [LawfulHashable α]
    {p : α → β → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false :=
  DHashMap.Raw.Const.all_eq_false_iff_exists_contains_getKey_get h.out

theorem all_eq_false_iff_exists_mem_getElem [LawfulBEq α] {p : α → β → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p a (m[a]'h) = false :=
  DHashMap.Raw.Const.all_eq_false_iff_exists_contains_get h.out

theorem any_keys [LawfulHashable α] [EquivBEq α] {p : α → Bool} (h : m.WF) :
    m.keys.any p = m.any (fun a _ => p a) := DHashMap.Raw.Const.any_keys h.out

theorem all_keys [LawfulHashable α] [EquivBEq α] {p : α → Bool} (h : m.WF) :
    m.keys.all p = m.all (fun a _ => p a) := DHashMap.Raw.Const.all_keys h.out

variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[simp, grind =]
theorem insertMany_nil (h : m.WF) :
    insertMany m [] = m :=
  ext (DHashMap.Raw.Const.insertMany_nil h.out)

@[simp, grind =]
theorem insertMany_list_singleton (h : m.WF)
    {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v :=
  ext (DHashMap.Raw.Const.insertMany_list_singleton h.out)

@[grind _=_]
theorem insertMany_cons (h : m.WF) {l : List (α × β)}
    {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l :=
  ext (DHashMap.Raw.Const.insertMany_cons h.out)

theorem insertMany_append (h : m.WF) {l₁ l₂ : List (α × β)} :
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
theorem insertMany_ind {motive : Raw α β → Prop} (m : Raw α β) {l : ρ}
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) :=
  show motive ⟨DHashMap.Raw.Const.insertMany m.1 l⟩ from
    DHashMap.Raw.Const.insertMany_ind m.inner l init fun m => insert ⟨m⟩

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    (insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) :=
  DHashMap.Raw.Const.contains_insertMany_list h.out

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k :=
  DHashMap.Raw.Const.mem_insertMany_list h.out

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l → (l.map Prod.fst).contains k = false → k ∈ m :=
  DHashMap.Raw.Const.mem_of_mem_insertMany_list h.out

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l :=
  DHashMap.Raw.Const.mem_insertMany_of_mem h.out

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

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  DHashMap.Raw.Const.size_le_size_insertMany h.out

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length :=
  DHashMap.Raw.Const.size_insertMany_list_le h.out

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  DHashMap.Raw.Const.isEmpty_insertMany_list h.out

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} : (insertMany m l).isEmpty → m.isEmpty :=
  DHashMap.Raw.Const.isEmpty_of_isEmpty_insertMany h.out

section
variable {β : Type v} {m₁ m₂ : Raw α β}

theorem Equiv.beq [EquivBEq α] [LawfulHashable α] [BEq β] [ReflBEq β] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁ ~m m₂) : m₁ == m₂ :=
  DHashMap.Raw.Const.Equiv.beq h₁.1 h₂.1 h.1

theorem equiv_of_beq [LawfulBEq α] [BEq β] [LawfulBEq β] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁ == m₂) : m₁ ~m m₂ :=
  ⟨DHashMap.Raw.Const.equiv_of_beq h₁.1 h₂.1 h⟩

theorem beq_iff_equiv [LawfulBEq α] [BEq β] [LawfulBEq β] (h₁ : m₁.WF) (h₂ : m₂.WF) : (m₁ == m₂) ↔ m₁ ~m m₂ :=
  ⟨equiv_of_beq h₁ h₂, Equiv.beq h₁ h₂⟩

theorem Equiv.beq_congr [EquivBEq α] [LawfulHashable α] [BEq β] {m₃ m₄ : Raw α β} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF) (w₁ : m₁ ~m m₃) (w₂ : m₂ ~m m₄) : (m₁ == m₂) = (m₃ == m₄) :=
  DHashMap.Raw.Const.Equiv.beq_congr h₁.1 h₂.1 h₃.1 h₄.1 w₁.1 w₂.1

end

section Union

variable {β : Type v}

variable {m₁ m₂ : Raw α β}

@[simp]
theorem union_eq : m₁.union m₂ = m₁ ∪ m₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∪ m₂).contains k = (m₁.contains k || m₂.contains k) :=
  @DHashMap.Raw.contains_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

/- mem -/
theorem mem_union_of_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ → k ∈ m₁ ∪ m₂ :=
  @DHashMap.Raw.mem_union_of_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem mem_union_of_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₂ → k ∈ m₁ ∪ m₂ :=
  @DHashMap.Raw.mem_union_of_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

@[simp]
theorem mem_union_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∪ m₂ ↔ k ∈ m₁ ∨ k ∈ m₂ :=
  @DHashMap.Raw.mem_union_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem mem_of_mem_union_of_not_mem_right [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₂ → k ∈ m₁ :=
  @DHashMap.Raw.mem_of_mem_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem mem_of_mem_union_of_not_mem_left [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂ :=
  @DHashMap.Raw.mem_of_mem_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

/- Equiv -/
theorem Equiv.union_left {m₃ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₁ ~m m₂) :
    (m₁ ∪ m₃) ~m (m₂ ∪ m₃) :=
  ⟨@DHashMap.Raw.Equiv.union_left _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.union_right {m₃ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₂ ~m m₃) :
    (m₁ ∪ m₂) ~m (m₁ ∪ m₃) :=
  ⟨@DHashMap.Raw.Equiv.union_right _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.union_congr {m₃ m₄ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF)
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ ∪ m₂) ~m (m₃ ∪ m₄) :=
  ⟨@DHashMap.Raw.Equiv.union_congr _ _ _ _ m₁.inner m₂.inner m₃.inner m₄.inner _ _ h₁.out h₂.out h₃.out h₄.out equiv₁.1 equiv₂.1⟩

theorem union_insert_right_equiv_insert_union [EquivBEq α] [LawfulHashable α] {p : α × β}
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∪ (m₂.insert p.fst p.snd)).Equiv ((m₁ ∪ m₂).insert p.fst p.snd) :=
  ⟨@DHashMap.Raw.union_insert_right_equiv_insert_union _ _ _ _ m₁.inner m₂.inner _ _ ⟨p.fst, p.snd⟩ h₁.out h₂.out⟩

@[deprecated union_insert_right_equiv_insert_union (since := "2025-11-03")]
theorem union_insert_right_equiv_union_insert [EquivBEq α] [LawfulHashable α] {p : α × β}
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∪ (m₂.insert p.fst p.snd)).Equiv ((m₁ ∪ m₂).insert p.fst p.snd) :=
  union_insert_right_equiv_insert_union h₁ h₂

/- getElem? -/
theorem getElem?_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ ∪ m₂)[k]? = m₂[k]?.or m₁[k]? :=
  @DHashMap.Raw.Const.get?_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem getElem?_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂)[k]? = m₂[k]? :=
  @DHashMap.Raw.Const.get?_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getElem?_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂)[k]? = m₁[k]? :=
  @DHashMap.Raw.Const.get?_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- get? -/
@[deprecated getElem?_union (since := "2025-12-10")]
theorem get?_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    get? (m₁ ∪ m₂) k = (get? m₂ k).or (get? m₁ k) :=
  @DHashMap.Raw.Const.get?_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

@[deprecated getElem?_union_of_not_mem_left (since := "2025-12-10")]
theorem get?_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) :
    get? (m₁ ∪ m₂) k = get? m₂ k :=
  @DHashMap.Raw.Const.get?_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

@[deprecated getElem?_union_of_not_mem_right (since := "2025-12-10")]
theorem get?_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) :
    get? (m₁ ∪ m₂) k = get? m₁ k :=
  @DHashMap.Raw.Const.get?_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- getElem -/
theorem getElem_union_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂)[k]'(mem_union_of_right h₁ h₂ mem) = m₂[k]'mem :=
  @DHashMap.Raw.Const.get_union_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

theorem getElem_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) {h'} :
    (m₁ ∪ m₂)[k]'h' = m₂[k]'(mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  @DHashMap.Raw.Const.get_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

theorem getElem_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) {h'} :
    (m₁ ∪ m₂)[k]'h' = m₁[k]'(mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  @DHashMap.Raw.Const.get_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

/- get -/
@[deprecated getElem_union_of_mem_right (since := "2025-12-10")]
theorem get_union_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    get (m₁ ∪ m₂) k (mem_union_of_right h₁ h₂ mem) = get m₂ k mem :=
  @DHashMap.Raw.Const.get_union_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

@[deprecated getElem_union_of_not_mem_left (since := "2025-12-10")]
theorem get_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) {h'} :
    get (m₁ ∪ m₂) k h' = get m₂ k (mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  @DHashMap.Raw.Const.get_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

@[deprecated getElem_union_of_not_mem_right (since := "2025-12-10")]
theorem get_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) {h'} :
    get (m₁ ∪ m₂) k h' = get m₁ k (mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  @DHashMap.Raw.Const.get_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

/- getD -/
theorem getD_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} {fallback : β} :
    getD (m₁ ∪ m₂) k fallback = getD m₂ k (getD m₁ k fallback) :=
  @DHashMap.Raw.Const.getD_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getD_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (not_mem : ¬k ∈ m₁) :
    getD (m₁ ∪ m₂) k fallback = getD m₂ k fallback :=
  @DHashMap.Raw.Const.getD_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getD_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (not_mem : ¬k ∈ m₂) :
    getD (m₁ ∪ m₂) k fallback = getD m₁ k fallback :=
  @DHashMap.Raw.Const.getD_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- getElem! -/
theorem getElem!_union [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ ∪ m₂)[k]! = getD m₂ k m₁[k]! :=
  @DHashMap.Raw.Const.get!_union _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem getElem!_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂)[k]! = m₂[k]! :=
  @DHashMap.Raw.Const.get!_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem getElem!_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂)[k]! = m₁[k]! :=
  @DHashMap.Raw.Const.get!_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- get! -/
@[deprecated getElem!_union (since := "2025-12-10")]
theorem get!_union [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    get! (m₁ ∪ m₂) k = getD m₂ k (get! m₁ k) :=
  @DHashMap.Raw.Const.get!_union _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

@[deprecated getElem!_union_of_not_mem_left (since := "2025-12-10")]
theorem get!_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) :
    get! (m₁ ∪ m₂) k = get! m₂ k :=
  @DHashMap.Raw.Const.get!_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

@[deprecated getElem!_union_of_not_mem_right (since := "2025-12-10")]
theorem get!_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) :
    get! (m₁ ∪ m₂) k = get! m₁ k :=
  @DHashMap.Raw.Const.get!_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- getKey? -/
theorem getKey?_union [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} :
    (m₁ ∪ m₂).getKey? k = (m₂.getKey? k).or (m₁.getKey? k) :=
  @DHashMap.Raw.getKey?_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem getKey?_union_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).getKey? k = m₂.getKey? k :=
  @DHashMap.Raw.getKey?_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getKey?_union_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).getKey? k = m₁.getKey? k :=
  @DHashMap.Raw.getKey?_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- getKey -/
theorem getKey_union_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂).getKey k (mem_union_of_right h₁ h₂ mem) = m₂.getKey k mem :=
  @DHashMap.Raw.getKey_union_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

theorem getKey_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₁) {h'} :
    (m₁ ∪ m₂).getKey k h' = m₂.getKey k (mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  @DHashMap.Raw.getKey_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

theorem getKey_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : ¬k ∈ m₂) {h'} :
    (m₁ ∪ m₂).getKey k h' = m₁.getKey k (mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  @DHashMap.Raw.getKey_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem h'

/- getKeyD -/
theorem getKeyD_union [EquivBEq α]
    [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} :
    (m₁ ∪ m₂).getKeyD k fallback = m₂.getKeyD k (m₁.getKeyD k fallback) :=
  @DHashMap.Raw.getKeyD_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getKeyD_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).getKeyD k fallback = m₂.getKeyD k fallback :=
  @DHashMap.Raw.getKeyD_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getKeyD_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).getKeyD k fallback = m₁.getKeyD k fallback :=
  @DHashMap.Raw.getKeyD_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- getKey! -/
theorem getKey!_union [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∪ m₂).getKey! k = m₂.getKeyD k (m₁.getKey! k) :=
  @DHashMap.Raw.getKey!_union _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem getKey!_union_of_not_mem_left [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : ¬k ∈ m₁) :
    (m₁ ∪ m₂).getKey! k = m₂.getKey! k :=
   @DHashMap.Raw.getKey!_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem getKey!_union_of_not_mem_right [Inhabited α]
    [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : ¬k ∈ m₂) :
    (m₁ ∪ m₂).getKey! k = m₁.getKey! k :=
   @DHashMap.Raw.getKey!_union_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- size -/
theorem size_union_of_not_mem [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) : (∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) →
    (m₁ ∪ m₂).size = m₁.size + m₂.size :=
  @DHashMap.Raw.size_union_of_not_mem _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_left_le_size_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) : m₁.size ≤ (m₁ ∪ m₂).size :=
  @DHashMap.Raw.size_left_le_size_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_right_le_size_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) : m₂.size ≤ (m₁ ∪ m₂).size :=
  @DHashMap.Raw.size_right_le_size_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_union_le_size_add_size [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∪ m₂).size ≤ m₁.size + m₂.size :=
  @DHashMap.Raw.size_union_le_size_add_size _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

/- isEmpty -/
@[simp]
theorem isEmpty_union [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∪ m₂).isEmpty = (m₁.isEmpty && m₂.isEmpty) :=
  @DHashMap.Raw.isEmpty_union _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

end Union

section Inter

variable {β : Type v}

variable {m₁ m₂ : Raw α β}

@[simp]
theorem inter_eq : m₁.inter m₂ = m₁ ∩ m₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).contains k = (m₁.contains k && m₂.contains k) :=
  @DHashMap.Raw.contains_inter _ _ _ _ m₁.inner m₂.inner _ _ k h₁.out h₂.out

/- mem -/
@[simp]
theorem mem_inter_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ ∩ m₂ ↔ k ∈ m₁ ∧ k ∈ m₂ :=
  @DHashMap.Raw.mem_inter_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem not_mem_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ ∩ m₂ :=
  @DHashMap.Raw.not_mem_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem not_mem_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₂) :
    k ∉ m₁ ∩ m₂ :=
  @DHashMap.Raw.not_mem_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- Equiv -/
theorem Equiv.inter_left {m₃ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₁ ~m m₂) :
    (m₁ ∩ m₃) ~m (m₂ ∩ m₃) :=
  ⟨@DHashMap.Raw.Equiv.inter_left _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.inter_right {m₃ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₂ ~m m₃) :
    (m₁ ∩ m₂) ~m (m₁ ∩ m₃) :=
  ⟨@DHashMap.Raw.Equiv.inter_right _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.inter_congr {m₃ m₄ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF)
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ ∩ m₂) ~m (m₃ ∩ m₄) :=
  ⟨@DHashMap.Raw.Equiv.inter_congr _ _ _ _ m₁.inner m₂.inner m₃.inner m₄.inner _ _ h₁.out h₂.out h₃.out h₄.out equiv₁.1 equiv₂.1⟩

/- getElem? -/
theorem getElem?_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂)[k]? = if k ∈ m₂ then m₁[k]? else none :=
  @DHashMap.Raw.Const.get?_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem getElem?_inter_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂)[k]? = m₁[k]? :=
  @DHashMap.Raw.Const.get?_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

theorem getElem?_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂)[k]? = none :=
  @DHashMap.Raw.Const.get?_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getElem?_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂)[k]? = none :=
  @DHashMap.Raw.Const.get?_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- get? -/
@[deprecated getElem?_inter (since := "2025-12-10")]
theorem get?_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    get? (m₁ ∩ m₂) k = if k ∈ m₂ then get? m₁ k else none :=
  @DHashMap.Raw.Const.get?_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

@[deprecated getElem?_inter_of_mem_right (since := "2025-12-10")]
theorem get?_inter_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    get? (m₁ ∩ m₂) k = get? m₁ k :=
  @DHashMap.Raw.Const.get?_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

@[deprecated getElem?_inter_of_not_mem_left (since := "2025-12-10")]
theorem get?_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    get? (m₁ ∩ m₂) k = none :=
  @DHashMap.Raw.Const.get?_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

@[deprecated getElem?_inter_of_not_mem_right (since := "2025-12-10")]
theorem get?_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    get? (m₁ ∩ m₂) k = none :=
  @DHashMap.Raw.Const.get?_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- getElem -/
@[simp]
theorem getElem_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ ∩ m₂} :
    (m₁ ∩ m₂)[k]'h_mem = m₁[k]'((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  @DHashMap.Raw.Const.get_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- get -/
@[deprecated getElem_inter (since := "2025-12-10")]
theorem get_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ ∩ m₂} :
    get (m₁ ∩ m₂) k h_mem = get m₁ k ((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  @DHashMap.Raw.Const.get_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- getD -/
theorem getD_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} :
    getD (m₁ ∩ m₂) k fallback =
    if k ∈ m₂ then getD m₁ k fallback else fallback :=
  @DHashMap.Raw.Const.getD_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getD_inter_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (mem : k ∈ m₂) :
    getD (m₁ ∩ m₂) k fallback = getD m₁ k fallback :=
  @DHashMap.Raw.Const.getD_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback mem

theorem getD_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ m₂) :
    getD (m₁ ∩ m₂) k fallback = fallback :=
  @DHashMap.Raw.Const.getD_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getD_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ m₁) :
    getD (m₁ ∩ m₂) k fallback = fallback :=
  @DHashMap.Raw.Const.getD_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- getElem! -/
theorem getElem!_inter [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂)[k]! = if k ∈ m₂ then m₁[k]! else default :=
  @DHashMap.Raw.Const.get!_inter _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem getElem!_inter_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂)[k]! = m₁[k]! :=
  @DHashMap.Raw.Const.get!_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

theorem getElem!_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂)[k]! = default :=
  @DHashMap.Raw.Const.get!_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem getElem!_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂)[k]! = default :=
  @DHashMap.Raw.Const.get!_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- get! -/
@[deprecated getElem!_inter (since := "2025-12-10")]
theorem get!_inter [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    get! (m₁ ∩ m₂) k = if k ∈ m₂ then get! m₁ k else default :=
  @DHashMap.Raw.Const.get!_inter _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

@[deprecated getElem!_inter_of_mem_right (since := "2025-12-10")]
theorem get!_inter_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    get! (m₁ ∩ m₂) k = get! m₁ k :=
  @DHashMap.Raw.Const.get!_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

@[deprecated getElem!_inter_of_not_mem_right (since := "2025-12-10")]
theorem get!_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    get! (m₁ ∩ m₂) k = default :=
  @DHashMap.Raw.Const.get!_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

@[deprecated getElem!_inter_of_not_mem_left (since := "2025-12-10")]
theorem get!_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    get! (m₁ ∩ m₂) k = default :=
  @DHashMap.Raw.Const.get!_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- getKey? -/
theorem getKey?_inter [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).getKey? k =
    if k ∈ m₂ then m₁.getKey? k else none :=
  @DHashMap.Raw.getKey?_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem getKey?_inter_of_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).getKey? k = m₁.getKey? k :=
  @DHashMap.Raw.getKey?_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

theorem getKey?_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).getKey? k = none :=
  @DHashMap.Raw.getKey?_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getKey?_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).getKey? k = none :=
  @DHashMap.Raw.getKey?_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

/- getKey -/
@[simp] theorem getKey_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ ∩ m₂} :
    (m₁ ∩ m₂).getKey k h_mem =
    m₁.getKey k ((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  @DHashMap.Raw.getKey_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- getKeyD -/
theorem getKeyD_inter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} :
    (m₁ ∩ m₂).getKeyD k fallback =
    if k ∈ m₂ then m₁.getKeyD k fallback else fallback :=
  @DHashMap.Raw.getKeyD_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getKeyD_inter_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).getKeyD k fallback = m₁.getKeyD k fallback :=
  @DHashMap.Raw.getKeyD_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback mem

theorem getKeyD_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).getKeyD k fallback = fallback :=
  @DHashMap.Raw.getKeyD_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getKeyD_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).getKeyD k fallback = fallback :=
  @DHashMap.Raw.getKeyD_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- getKey! -/
theorem getKey!_inter [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).getKey! k =
    if k ∈ m₂ then m₁.getKey! k else default :=
  @DHashMap.Raw.getKey!_inter _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem getKey!_inter_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} (mem : k ∈ m₂) :
    (m₁ ∩ m₂).getKey! k = m₁.getKey! k :=
  @DHashMap.Raw.getKey!_inter_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

theorem getKey!_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₂) :
    (m₁ ∩ m₂).getKey! k = default :=
  @DHashMap.Raw.getKey!_inter_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem getKey!_inter_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₁) :
    (m₁ ∩ m₂).getKey! k = default :=
  @DHashMap.Raw.getKey!_inter_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- size -/
theorem size_inter_le_size_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∩ m₂).size ≤ m₁.size :=
  @DHashMap.Raw.size_inter_le_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_inter_le_size_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∩ m₂).size ≤ m₂.size :=
  @DHashMap.Raw.size_inter_le_size_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_inter_eq_size_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ (a : α), a ∈ m₁ → a ∈ m₂) :
    (m₁ ∩ m₂).size = m₁.size :=
  @DHashMap.Raw.size_inter_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem size_inter_eq_size_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ (a : α), a ∈ m₂ → a ∈ m₁) :
    (m₁ ∩ m₂).size = m₂.size :=
  @DHashMap.Raw.size_inter_eq_size_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem size_add_size_eq_size_union_add_size_inter [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    m₁.size + m₂.size = (m₁ ∪ m₂).size + (m₁ ∩ m₂).size :=
  @DHashMap.Raw.size_add_size_eq_size_union_add_size_inter _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁.isEmpty) :
    (m₁ ∩ m₂).isEmpty = true :=
  @DHashMap.Raw.isEmpty_inter_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

@[simp]
theorem isEmpty_inter_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₂.isEmpty) :
    (m₁ ∩ m₂).isEmpty = true :=
  @DHashMap.Raw.isEmpty_inter_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem isEmpty_inter_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ ∩ m₂).isEmpty ↔ ∀ k, k ∈ m₁ → k ∉ m₂ :=
  @DHashMap.Raw.isEmpty_inter_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

end Inter

section Diff

variable {β : Type v}

variable {m₁ m₂ : Raw α β}

@[simp]
theorem diff_eq : m₁.diff m₂ = m₁ \ m₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂).contains k = (m₁.contains k && !m₂.contains k) :=
  @DHashMap.Raw.contains_diff _ _ _ _ m₁.inner m₂.inner  _  _ h₁.out h₂.out k

/- mem -/
@[simp]
theorem mem_diff_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    k ∈ m₁ \ m₂ ↔ k ∈ m₁ ∧ k ∉ m₂ :=
  @DHashMap.Raw.mem_diff_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem not_mem_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ \ m₂ :=
  @DHashMap.Raw.not_mem_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem not_mem_diff_of_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α}
    (mem : k ∈ m₂) :
    k ∉ m₁ \ m₂ :=
  @DHashMap.Raw.not_mem_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

/- Equiv -/
theorem Equiv.diff_left {m₃ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₁ ~m m₂) :
    (m₁ \ m₃) ~m (m₂ \ m₃) :=
  ⟨@DHashMap.Raw.Equiv.diff_left _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.diff_right {m₃ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF)
    (equiv : m₂ ~m m₃) :
    (m₁ \ m₂) ~m (m₁ \ m₃) :=
  ⟨@DHashMap.Raw.Equiv.diff_right _ _ _ _ m₁.inner m₂.inner m₃.inner _ _ h₁.out h₂.out h₃.out equiv.1⟩

theorem Equiv.diff_congr {m₃ m₄ : Raw α β} [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF)
    (equiv₁ : m₁ ~m m₃) (equiv₂ : m₂ ~m m₄) :
    (m₁ \ m₂) ~m (m₃ \ m₄) :=
  ⟨@DHashMap.Raw.Equiv.diff_congr _ _ _ _ m₁.inner m₂.inner m₃.inner m₄.inner _ _ h₁.out h₂.out h₃.out h₄.out equiv₁.1 equiv₂.1⟩

/- getElem? -/
theorem getElem?_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂)[k]? = if k ∈ m₂ then none else m₁[k]? :=
  @DHashMap.Raw.Const.get?_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem getElem?_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂)[k]? = m₁[k]? :=
  @DHashMap.Raw.Const.get?_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getElem?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂)[k]? = none :=
  @DHashMap.Raw.Const.get?_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getElem?_diff_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂)[k]? = none :=
  @DHashMap.Raw.Const.get?_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

/- get? -/
@[deprecated getElem?_diff (since := "2025-12-10")]
theorem get?_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    get? (m₁ \ m₂) k = if k ∈ m₂ then none else get? m₁ k :=
  @DHashMap.Raw.Const.get?_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

@[deprecated getElem?_diff_of_not_mem_right (since := "2025-12-10")]
theorem get?_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    get? (m₁ \ m₂) k = get? m₁ k :=
  @DHashMap.Raw.Const.get?_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

@[deprecated getElem?_diff_of_not_mem_left (since := "2025-12-10")]
theorem get?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    get? (m₁ \ m₂) k = none :=
  @DHashMap.Raw.Const.get?_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

@[deprecated getElem?_diff_of_mem_right (since := "2025-12-10")]
theorem get?_diff_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    get? (m₁ \ m₂) k = none :=
  @DHashMap.Raw.Const.get?_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

/- getElem -/
@[simp]
theorem getElem_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ \ m₂} :
    (m₁ \ m₂)[k]'h_mem = m₁[k]'((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  @DHashMap.Raw.Const.get_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- get -/
@[deprecated getElem_diff (since := "2025-12-10")]
theorem get_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ \ m₂} :
    get (m₁ \ m₂) k h_mem = get m₁ k ((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  @DHashMap.Raw.Const.get_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- getD -/
theorem getD_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} :
    getD (m₁ \ m₂) k fallback =
    if k ∈ m₂ then fallback else getD m₁ k fallback :=
  @DHashMap.Raw.Const.getD_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getD_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ m₂) :
    getD (m₁ \ m₂) k fallback = getD m₁ k fallback :=
  @DHashMap.Raw.Const.getD_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getD_diff_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (mem : k ∈ m₂) :
    getD (m₁ \ m₂) k fallback = fallback :=
  @DHashMap.Raw.Const.getD_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback mem

theorem getD_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ m₁) :
    getD (m₁ \ m₂) k fallback = fallback :=
  @DHashMap.Raw.Const.getD_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- getElem! -/
theorem getElem!_diff [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂)[k]! = if k ∈ m₂ then default else m₁[k]! :=
  @DHashMap.Raw.Const.get!_diff _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem getElem!_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂)[k]! = m₁[k]! :=
  @DHashMap.Raw.Const.get!_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem getElem!_diff_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂)[k]! = default :=
  @DHashMap.Raw.Const.get!_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

theorem getElem!_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂)[k]! = default :=
  @DHashMap.Raw.Const.get!_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- get! -/
@[deprecated getElem!_diff (since := "2025-12-10")]
theorem get!_diff [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    get! (m₁ \ m₂) k = if k ∈ m₂ then default else get! m₁ k :=
  @DHashMap.Raw.Const.get!_diff _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

@[deprecated getElem!_diff_of_not_mem_right (since := "2025-12-10")]
theorem get!_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₂) :
    get! (m₁ \ m₂) k = get! m₁ k :=
  @DHashMap.Raw.Const.get!_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

@[deprecated getElem!_diff_of_mem_right (since := "2025-12-10")]
theorem get!_diff_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    get! (m₁ \ m₂) k = default :=
  @DHashMap.Raw.Const.get!_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

@[deprecated getElem!_diff_of_not_mem_left (since := "2025-12-10")]
theorem get!_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (not_mem : k ∉ m₁) :
    get! (m₁ \ m₂) k = default :=
  @DHashMap.Raw.Const.get!_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- getKey? -/
theorem getKey?_diff [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂).getKey? k =
    if k ∈ m₂ then none else m₁.getKey? k :=
  @DHashMap.Raw.getKey?_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k

theorem getKey?_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).getKey? k = m₁.getKey? k :=
  @DHashMap.Raw.getKey?_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getKey?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getKey? k = none :=
  @DHashMap.Raw.getKey?_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k not_mem

theorem getKey?_diff_of_mem_right [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).getKey? k = none :=
  @DHashMap.Raw.getKey?_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k mem

/- getKey -/
@[simp] theorem getKey_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} {h_mem : k ∈ m₁ \ m₂} :
    (m₁ \ m₂).getKey k h_mem =
    m₁.getKey k ((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  @DHashMap.Raw.getKey_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k h_mem

/- getKeyD -/
theorem getKeyD_diff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} :
    (m₁ \ m₂).getKeyD k fallback =
    if k ∈ m₂ then fallback else m₁.getKeyD k fallback :=
  @DHashMap.Raw.getKeyD_diff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback

theorem getKeyD_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).getKeyD k fallback = m₁.getKeyD k fallback :=
  @DHashMap.Raw.getKeyD_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

theorem getKeyD_diff_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).getKeyD k fallback = fallback :=
  @DHashMap.Raw.getKeyD_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback mem

theorem getKeyD_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k fallback : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getKeyD k fallback = fallback :=
  @DHashMap.Raw.getKeyD_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out k fallback not_mem

/- getKey! -/
theorem getKey!_diff [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂).getKey! k =
    if k ∈ m₂ then default else m₁.getKey! k :=
  @DHashMap.Raw.getKey!_diff _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k

theorem getKey!_diff_of_not_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₂) :
    (m₁ \ m₂).getKey! k = m₁.getKey! k :=
  @DHashMap.Raw.getKey!_diff_of_not_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

theorem getKey!_diff_of_mem_right [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} (mem : k ∈ m₂) :
    (m₁ \ m₂).getKey! k = default :=
  @DHashMap.Raw.getKey!_diff_of_mem_right _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k mem

theorem getKey!_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] [Inhabited α] (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getKey! k = default :=
  @DHashMap.Raw.getKey!_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ _ h₁.out h₂.out k not_mem

/- size -/
theorem size_diff_le_size_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ \ m₂).size ≤ m₁.size :=
  @DHashMap.Raw.size_diff_le_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

theorem size_diff_eq_size_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ (a : α), a ∈ m₁ → a ∉ m₂) :
    (m₁ \ m₂).size = m₁.size :=
  @DHashMap.Raw.size_diff_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem size_diff_add_size_inter_eq_size_left [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ \ m₂).size + (m₁ ∩ m₂).size = m₁.size :=
  @DHashMap.Raw.size_diff_add_size_inter_eq_size_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁.isEmpty) :
    (m₁ \ m₂).isEmpty = true :=
  @DHashMap.Raw.isEmpty_diff_left _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out h

theorem isEmpty_diff_iff [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) :
    (m₁ \ m₂).isEmpty ↔ ∀ k, k ∈ m₁ → k ∈ m₂ :=
  @DHashMap.Raw.isEmpty_diff_iff _ _ _ _ m₁.inner m₂.inner _ _ h₁.out h₂.out

end Diff

theorem getElem?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]? = m[k]? :=
  DHashMap.Raw.Const.get?_insertMany_list_of_contains_eq_false h.out contains_eq_false

theorem getElem?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']? = some v :=
  DHashMap.Raw.Const.get?_insertMany_list_of_mem h.out k_beq distinct mem

@[grind =]
theorem getElem?_insertMany_list [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List (α × β)} {k : α} :
    (insertMany m l)[k]? = (l.findSomeRev? (fun ⟨a, b⟩ => if a == k then some b else none)).or m[k]? :=
  DHashMap.Raw.Const.get?_insertMany_list h.out

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
variable {ρ : Type w} [ForIn Id ρ α]

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

@[elab_as_elim]
theorem insertManyIfNewUnit_ind {motive : Raw α Unit → Prop} (m : Raw α Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l) :=
  show motive ⟨DHashMap.Raw.Const.insertManyIfNewUnit m.1 l⟩ from
    DHashMap.Raw.Const.insertManyIfNewUnit_ind m.inner l init fun m => insert ⟨m⟩

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

theorem mem_insertManyIfNewUnit_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} {k : α} : k ∈ m → k ∈ insertManyIfNewUnit m l :=
  DHashMap.Raw.Const.mem_insertManyIfNewUnit_of_mem h.out

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
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

theorem size_le_size_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} : m.size ≤ (insertManyIfNewUnit m l).size :=
  DHashMap.Raw.Const.size_le_size_insertManyIfNewUnit h.out

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length :=
  DHashMap.Raw.Const.size_insertManyIfNewUnit_list_le h.out

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  DHashMap.Raw.Const.isEmpty_insertManyIfNewUnit_list h.out

theorem isEmpty_of_isEmpty_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : ρ} : (m.insertManyIfNewUnit l).isEmpty → m.isEmpty :=
  DHashMap.Raw.Const.isEmpty_of_isEmpty_insertManyIfNewUnit h.out

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

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ :=
  ext DHashMap.Raw.Const.ofList_nil

@[simp, grind =]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : Raw α β).insert k v :=
  ext DHashMap.Raw.Const.ofList_singleton

@[grind _=_]
theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : Raw α β).insert k v) tl :=
  ext DHashMap.Raw.Const.ofList_cons

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l = insertMany (∅ : Raw α β) l :=
  ext DHashMap.Raw.Const.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  DHashMap.Raw.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ (ofList l) ↔ (l.map Prod.fst).contains k :=
  DHashMap.Raw.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]? = none :=
  DHashMap.Raw.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']? = some v :=
  DHashMap.Raw.Const.get?_ofList_of_mem k_beq distinct mem

theorem getElem_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l)[k'] = v :=
  DHashMap.Raw.Const.get_ofList_of_mem k_beq distinct mem (h:=h)

theorem getElem!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]! = default :=
  DHashMap.Raw.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']! = v :=
  DHashMap.Raw.Const.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback :=
  DHashMap.Raw.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
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

grind_pattern size_ofList_le => (ofList l).size

@[simp, grind =]
theorem ofArray_eq_ofList (a : Array (α × β)) :
    ofArray a = ofList a.toList := by
  apply ext
  apply DHashMap.Raw.Const.ofArray_eq_ofList

@[simp, grind =]
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

theorem unitOfList_eq_insertManyIfNewUnit_empty {l : List α} :
    unitOfList l = insertManyIfNewUnit ∅ l :=
  ext DHashMap.Raw.Const.unitOfList_eq_insertManyIfNewUnit_empty

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

@[simp, grind =]
theorem unitOfArray_eq_unitOfList (a : Array α) :
    unitOfArray a = unitOfList a.toList := by
  apply ext
  apply DHashMap.Raw.Const.unitOfArray_eq_unitOfList

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
    (alter m k f).isEmpty = ((m.erase k).isEmpty && (f m[k]?).isNone) :=
  DHashMap.Raw.Const.isEmpty_alter_eq_isEmpty_erase h.out

@[simp, grind =]
theorem isEmpty_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) && (f m[k]?).isNone) :=
  DHashMap.Raw.Const.isEmpty_alter h.out

@[grind =]
theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).contains k' =
      if k == k' then (f m[k]?).isSome else m.contains k' :=
  DHashMap.Raw.Const.contains_alter h.out

@[grind =]
theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} (h : m.WF) :
    k' ∈ alter m k f ↔ if k == k' then (f m[k]?).isSome = true else k' ∈ m :=
  DHashMap.Raw.Const.mem_alter h.out

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : m.WF) (he : k == k') : k' ∈ alter m k f ↔ (f m[k]?).isSome :=
  DHashMap.Raw.Const.mem_alter_of_beq h.out he

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).contains k = (f m[k]?).isSome :=
  DHashMap.Raw.Const.contains_alter_self h.out

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : k ∈ alter m k f ↔ (f m[k]?).isSome :=
  DHashMap.Raw.Const.mem_alter_self h.out

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) (he : (k == k') = false) :
    (alter m k f).contains k' = m.contains k' :=
  DHashMap.Raw.Const.contains_alter_of_beq_eq_false h.out he

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) (he : (k == k') = false) : k' ∈ alter m k f ↔ k' ∈ m :=
  DHashMap.Raw.Const.mem_alter_of_beq_eq_false h.out he

@[grind =]
theorem size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f).size =
      if k ∈ m ∧ (f m[k]?).isNone then
        m.size - 1
      else if k ∉ m ∧ (f m[k]?).isSome then
        m.size + 1
      else
        m.size :=
  DHashMap.Raw.Const.size_alter h.out

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∉ m) (h₂ : (f m[k]?).isSome) :
    (alter m k f).size = m.size + 1 :=
  DHashMap.Raw.Const.size_alter_eq_add_one h.out h₁ h₂

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∈ m) (h₂ : (f m[k]?).isNone) :
    (alter m k f).size = m.size - 1 :=
  DHashMap.Raw.Const.size_alter_eq_sub_one h.out h₁ h₂

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∉ m) (h₂ : (f m[k]?).isNone) : (alter m k f).size = m.size :=
  DHashMap.Raw.Const.size_alter_eq_self_of_not_mem h.out h₁ h₂

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF)
    (h₁ : k ∈ m) (h₂ : (f m[k]?).isSome) : (alter m k f).size = m.size :=
  DHashMap.Raw.Const.size_alter_eq_self_of_mem h.out h₁ h₂

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f).size ≤ m.size + 1 :=
  DHashMap.Raw.Const.size_alter_le_size h.out

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    m.size - 1 ≤ (alter m k f).size :=
  DHashMap.Raw.Const.size_le_size_alter h.out

@[grind =]
theorem getElem?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} (h : m.WF) :
    (alter m k f)[k']? =
      if k == k' then
        f m[k]?
      else
        m[k']? :=
  DHashMap.Raw.Const.get?_alter h.out

@[simp]
theorem getElem?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f)[k]? = f m[k]? :=
  DHashMap.Raw.Const.get?_alter_self h.out

@[grind =]
theorem getElem_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    (h : m.WF) {hc : k' ∈ alter m k f} :
    (alter m k f)[k'] =
      if heq : k == k' then
        haveI h' : (f m[k]?).isSome := mem_alter_of_beq h heq |>.mp hc
        f m[k]? |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        m[k']'h' :=
  DHashMap.Raw.Const.get_alter h.out (hc := hc)

@[simp]
theorem getElem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) {hc : k ∈ alter m k f} :
    haveI h' : (f m[k]?).isSome := mem_alter_self h |>.mp hc
    (alter m k f)[k] = (f m[k]?).get h' :=
  DHashMap.Raw.Const.get_alter_self h.out (hc := hc)

@[grind =]
theorem getElem!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} (h : m.WF) : (alter m k f)[k']! =
      if k == k' then
        f m[k]? |>.get!
      else
        m[k']! :=
  DHashMap.Raw.Const.get!_alter h.out

@[simp]
theorem getElem!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} (h : m.WF) : (alter m k f)[k]! = (f m[k]?).get! :=
  DHashMap.Raw.Const.get!_alter_self h.out

@[grind =]
theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β}
    {f : Option β → Option β} (h : m.WF) : getD (alter m k f) k' fallback =
      if k == k' then
        f m[k]? |>.getD fallback
      else
        getD m k' fallback :=
  DHashMap.Raw.Const.getD_alter h.out

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} (h : m.WF) :
    getD (alter m k f) k fallback = (f m[k]?).getD fallback :=
  DHashMap.Raw.Const.getD_alter_self h.out

@[grind =]
theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).getKey? k' =
      if k == k' then
        if (f m[k]?).isSome then some k else none
      else
        m.getKey? k' :=
  DHashMap.Raw.Const.getKey?_alter h.out

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).getKey? k = if (f m[k]?).isSome then some k else none :=
  DHashMap.Raw.Const.getKey?_alter_self h.out

@[grind =]
theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) : (alter m k f).getKey! k' =
      if k == k' then
        if (f m[k]?).isSome then k else default
      else
        m.getKey! k' :=
  DHashMap.Raw.Const.getKey!_alter h.out

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} (h : m.WF) :
    (alter m k f).getKey! k = if (f m[k]?).isSome then k else default :=
  DHashMap.Raw.Const.getKey!_alter_self h.out

@[grind =]
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

@[grind =]
theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : Option β → Option β}
    (h : m.WF) : (alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f m[k]?).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  DHashMap.Raw.Const.getKeyD_alter h.out

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : Option β → Option β} (h : m.WF) :
    (alter m k f).getKeyD k fallback = if (f m[k]?).isSome then k else fallback :=
  DHashMap.Raw.Const.getKeyD_alter_self h.out

end Alter

section Modify

@[simp, grind =]
theorem isEmpty_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (modify m k f).isEmpty = m.isEmpty :=
  DHashMap.Raw.Const.isEmpty_modify h.out

@[simp, grind =]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} (h : m.WF) :
    (modify m k f).contains k' = m.contains k' :=
  DHashMap.Raw.Const.contains_modify h.out

@[simp, grind =]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} (h : m.WF) :
    k' ∈ modify m k f ↔ k' ∈ m :=
  DHashMap.Raw.Const.mem_modify h.out

@[simp, grind =]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (modify m k f).size = m.size :=
  DHashMap.Raw.Const.size_modify h.out

@[grind =]
theorem getElem?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} (h : m.WF) :
    (modify m k f)[k']? =
      if k == k' then
        m[k]?.map f
      else
        m[k']? :=
  DHashMap.Raw.Const.get?_modify h.out

@[simp]
theorem getElem?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (modify m k f)[k]? = m[k]?.map f :=
  DHashMap.Raw.Const.get?_modify_self h.out

@[grind =]
theorem getElem_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    (h : m.WF) {hc : k' ∈ modify m k f} :
    (modify m k f)[k']'hc =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        f (m[k]'h')
      else
        haveI h' : k' ∈ m := mem_modify h |>.mp hc
        m[k']'h' := by
  simpa only [← get_eq_getElem] using! DHashMap.Raw.Const.get_modify h.out

@[simp]
theorem getElem_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF)
    {hc : k ∈ modify m k f} :
    haveI h' : k ∈ m := mem_modify h |>.mp hc
    (modify m k f)[k]'hc = f (m[k]'h') := by
  simpa only [← get_eq_getElem] using! DHashMap.Raw.Const.get_modify_self h.out

@[grind =]
theorem getElem!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β}
    (h : m.WF) : (modify m k f)[k']! =
      if k == k' then
        m[k]?.map f |>.get!
      else
        m[k']! :=
  DHashMap.Raw.Const.get!_modify h.out

@[simp]
theorem getElem!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β}
    (h : m.WF) : (modify m k f)[k]! = (m[k]?.map f).get! :=
  DHashMap.Raw.Const.get!_modify_self h.out

@[grind =]
theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} (h : m.WF) :
    getD (modify m k f) k' fallback =
      if k == k' then
        m[k]?.map f |>.getD fallback
      else
        getD m k' fallback :=
  DHashMap.Raw.Const.getD_modify h.out

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} (h : m.WF) :
    getD (modify m k f) k fallback = (m[k]?.map f).getD fallback :=
  DHashMap.Raw.Const.getD_modify_self h.out

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

namespace Equiv

section Raw

variable {α : Type u} {β : Type v} {m m₁ m₂ m₃ : Raw α β}

@[refl, simp] theorem refl (m : Raw α β) : m ~m m := ⟨.rfl⟩
theorem rfl : m ~m m := ⟨.rfl⟩
@[symm] theorem symm : m₁ ~m m₂ → m₂ ~m m₁
  | ⟨h⟩ => ⟨h.symm⟩
theorem trans : m₁ ~m m₂ → m₂ ~m m₃ → m₁ ~m m₃
  | ⟨h₁⟩, ⟨h₂⟩ => ⟨h₁.trans h₂⟩

instance instTrans : Trans (α := Raw α β) Equiv Equiv Equiv := ⟨trans⟩

theorem comm : m₁ ~m m₂ ↔ m₂ ~m m₁ := ⟨symm, symm⟩
theorem congr_left (h : m₁ ~m m₂) : m₁ ~m m₃ ↔ m₂ ~m m₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : m₁ ~m m₂) : m₃ ~m m₁ ↔ m₃ ~m m₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

theorem toList_perm (h : m₁ ~m m₂) : m₁.toList.Perm m₂.toList :=
  h.1.constToList_perm

theorem of_toList_perm (h : m₁.toList.Perm m₂.toList) : m₁ ~m m₂ :=
  ⟨.of_constToList_perm h⟩

theorem keys_perm (h : m₁ ~m m₂) : m₁.keys.Perm m₂.keys :=
  h.1.keys_perm

theorem of_keys_unit_perm {m₁ m₂ : Raw α Unit} (h : m₁.keys.Perm m₂.keys) : m₁ ~m m₂ :=
  ⟨.of_keys_unit_perm h⟩

end Raw

variable {m₁ m₂ : Raw α β}

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

theorem getElem?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁[k]? = m₂[k]? :=
  h.1.constGet?_eq h₁.1 h₂.1

theorem getElem_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (hk : k ∈ m₁) (h : m₁ ~m m₂) : m₁[k] = m₂[k]'((h.mem_iff h₁ h₂).mp hk) :=
  h.1.constGet_eq h₁.1 h₂.1 hk

theorem getElem!_eq [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁[k]! = m₂[k]! :=
  h.1.constGet!_eq h₁.1 h₂.1

theorem getD_eq [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.getD k fallback = m₂.getD k fallback :=
  h.1.constGetD_eq h₁.1 h₂.1

theorem getKey?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.getKey? k = m₂.getKey? k :=
  h.1.getKey?_eq h₁.1 h₂.1

theorem getKey_eq [EquivBEq α] [LawfulHashable α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (hk : k ∈ m₁) (h : m₁ ~m m₂) : m₁.getKey k hk = m₂.getKey k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.getKey_eq h₁.1 h₂.1 hk

theorem getKey!_eq [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.getKey! k = m₂.getKey! k :=
  h.1.getKey!_eq h₁.1 h₂.1

theorem getKeyD_eq [EquivBEq α] [LawfulHashable α] {k fallback : α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : m₁ ~m m₂) : m₁.getKeyD k fallback = m₂.getKeyD k fallback :=
  h.1.getKeyD_eq h₁.1 h₂.1

theorem insert [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (k : α) (v : β)
    (h : m₁ ~m m₂) : m₁.insert k v ~m m₂.insert k v :=
  ⟨h.1.insert h₁.1 h₂.1 k v⟩

theorem erase [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (k : α)
    (h : m₁ ~m m₂) : m₁.erase k ~m m₂.erase k :=
  ⟨h.1.erase h₁.1 h₂.1 k⟩

theorem insertIfNew [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF) (k : α) (v : β)
    (h : m₁ ~m m₂) : m₁.insertIfNew k v ~m m₂.insertIfNew k v :=
  ⟨h.1.insertIfNew h₁.1 h₂.1 k v⟩

theorem insertMany_list [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (l : List (α × β)) (h : m₁ ~m m₂) : m₁.insertMany l ~m m₂.insertMany l :=
  ⟨h.1.constInsertMany_list h₁.1 h₂.1 l⟩

theorem insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Raw α Unit}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (l : List α) (h : m₁ ~m m₂) :
    m₁.insertManyIfNewUnit l ~m m₂.insertManyIfNewUnit l :=
  ⟨h.1.constInsertManyIfNewUnit_list h₁.1 h₂.1 l⟩

theorem alter [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (k : α) (f : Option β → Option β)
    (h : m₁ ~m m₂) : m₁.alter k f ~m m₂.alter k f :=
  ⟨h.1.constAlter h₁.1 h₂.1 k f⟩

theorem modify [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (k : α) (f : β → β)
    (h : m₁ ~m m₂) : m₁.modify k f ~m m₂.modify k f :=
  ⟨h.1.constModify h₁.1 h₂.1 k f⟩

theorem filter (h₁ : m₁.WF) (h₂ : m₂.WF) (f : α → β → Bool) (h : m₁ ~m m₂) :
    m₁.filter f ~m m₂.filter f :=
  ⟨h.1.filter h₁.1 h₂.1 f⟩

theorem map (h₁ : m₁.WF) (h₂ : m₂.WF) (f : α → β → γ) (h : m₁ ~m m₂) : m₁.map f ~m m₂.map f :=
  ⟨h.1.map h₁.1 h₂.1 f⟩

theorem filterMap (h₁ : m₁.WF) (h₂ : m₂.WF) (f : α → β → Option γ) (h : m₁ ~m m₂) :
    m₁.filterMap f ~m m₂.filterMap f :=
  ⟨h.1.filterMap h₁.1 h₂.1 f⟩

theorem of_forall_getKey_eq_of_forall_getElem?_eq [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.WF) (h₂ : m₂.WF) (hk : ∀ k hk hk', m₁.getKey k hk = m₂.getKey k hk')
    (hv : ∀ k : α, m₁[k]? = m₂[k]?) : m₁ ~m m₂ :=
  ⟨.of_forall_getKey_eq_of_forall_constGet?_eq h₁.1 h₂.1 hk hv⟩

theorem of_forall_getElem?_eq [LawfulBEq α] (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k : α, m₁[k]? = m₂[k]?) : m₁ ~m m₂ :=
  ⟨.of_forall_constGet?_eq h₁.1 h₂.1 h⟩

theorem of_forall_getKey?_unit_eq [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : HashMap.Raw α Unit} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k, m₁.getKey? k = m₂.getKey? k) : m₁ ~m m₂ :=
  ⟨.of_forall_getKey?_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_contains_unit_eq [LawfulBEq α]
    {m₁ m₂ : HashMap.Raw α Unit} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ ~m m₂ :=
  ⟨.of_forall_contains_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_mem_unit_iff [LawfulBEq α]
    {m₁ m₂ : HashMap.Raw α Unit} (h₁ : m₁.WF) (h₂ : m₂.WF)
    (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ ~m m₂ :=
  ⟨.of_forall_mem_unit_iff h₁.1 h₂.1 h⟩

end Equiv

theorem equiv_emptyWithCapacity_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} (h : m.WF) :
    m ~m emptyWithCapacity c ↔ m.isEmpty :=
  ⟨fun ⟨h'⟩ => (DHashMap.Raw.equiv_emptyWithCapacity_iff_isEmpty h.1).mp h',
    fun h' => ⟨(DHashMap.Raw.equiv_emptyWithCapacity_iff_isEmpty h.1).mpr h'⟩⟩

theorem equiv_empty_iff_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m ~m ∅ ↔ m.isEmpty :=
  equiv_emptyWithCapacity_iff_isEmpty h

theorem emptyWithCapacity_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} (h : m.WF) :
    emptyWithCapacity c ~m m ↔ m.isEmpty :=
  Equiv.comm.trans (equiv_emptyWithCapacity_iff_isEmpty h)

theorem empty_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    ∅ ~m m ↔ m.isEmpty :=
  Equiv.comm.trans (equiv_empty_iff_isEmpty h)

theorem equiv_iff_toList_perm {m₁ m₂ : Raw α β} [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ m₁.toList.Perm m₂.toList :=
  ⟨Equiv.toList_perm, Equiv.of_toList_perm⟩

theorem equiv_iff_keys_unit_perm [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Raw α Unit} :
    m₁ ~m m₂ ↔ m₁.keys.Perm m₂.keys :=
  ⟨Equiv.keys_perm, Equiv.of_keys_unit_perm⟩

theorem insertMany_list_equiv_foldl {m : HashMap.Raw α β} {l : List (α × β)} (h : m.WF) :
    m.insertMany l ~m l.foldl (init := m) fun acc p => acc.insert p.1 p.2 := by
  constructor
  rw [← List.foldl_hom inner (g₂ := fun acc p => acc.insert p.1 p.2)]
  · exact DHashMap.Raw.Const.insertMany_list_equiv_foldl h.1
  · exact fun _ _ => rfl

theorem ofList_equiv_foldl {l : List (α × β)} :
    ofList l ~m l.foldl (init := ∅) fun acc p => acc.insert p.1 p.2 :=
  insertMany_list_equiv_foldl .empty

theorem insertManyIfNewUnit_list_equiv_foldl {m : HashMap.Raw α Unit}
    {l : List α} (h : m.WF) :
    insertManyIfNewUnit m l ~m l.foldl (init := m) fun acc a => acc.insertIfNew a () := by
  constructor
  rw [← List.foldl_hom inner (g₂ := fun acc a => acc.insertIfNew a ())]
  · exact DHashMap.Raw.Const.insertManyIfNewUnit_list_equiv_foldl h.1
  · exact fun _ _ => rfl

theorem unitOfList_equiv_foldl {l : List α} :
    unitOfList l ~m l.foldl (init := ∅) fun acc a => acc.insertIfNew a () :=
  insertManyIfNewUnit_list_equiv_foldl .empty

section filterMap

theorem toList_filterMap {f : α → β → Option γ} (h : m.WF) :
    (m.filterMap f).toList.Perm
      (m.toList.filterMap (fun p => (f p.1 p.2).map (fun x => ⟨p.1, x⟩))) :=
  DHashMap.Raw.Const.toList_filterMap h.out

@[grind =]
theorem isEmpty_filterMap_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.WF) :
    (m.filterMap f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ m), f (m.getKey k h) (m[k]'h) = none :=
  DHashMap.Raw.Const.isEmpty_filterMap_iff h.out

theorem isEmpty_filterMap_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.WF) :
    (m.filterMap f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), (f (m.getKey k h) (m[k]'h)).isSome :=
  DHashMap.Raw.Const.isEmpty_filterMap_eq_false_iff h.out

-- TODO: `contains_filterMap` is missing

@[grind =]
theorem mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    k ∈ (m.filterMap f) ↔ ∃ (g : k ∈ m),
      (f (m.getKey k g) (m[k]'g)).isSome :=
  DHashMap.Raw.Const.mem_filterMap h.out

theorem mem_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.WF) (h' : k ∈ (m.filterMap f)) :
    k ∈ m :=
  DHashMap.Raw.mem_of_mem_filterMap h.out h'

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.WF) :
    (m.filterMap f).size ≤ m.size :=
  DHashMap.Raw.size_filterMap_le_size h.out

grind_pattern size_filterMap_le_size => (m.filterMap f).size
theorem size_filterMap_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.WF) :
    (m.filterMap f).size = m.size ↔ ∀ (a : α) (h : a ∈ m),
      (f (m.getKey a h) (m[a]'h)).isSome :=
  DHashMap.Raw.Const.size_filterMap_eq_size_iff h.out

@[simp]
theorem getElem?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    (m.filterMap f)[k]? = m[k]?.pbind (fun x h' =>
      f (m.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x) :=
  DHashMap.Raw.Const.get?_filterMap h.out

/-- Simpler variant of `getElem?_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem?_filterMap' [LawfulBEq α]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    (m.filterMap f)[k]? = m[k]?.bind fun x => f k x := by
  simp [getElem?_filterMap, h]

theorem getElem?_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} (h : m.WF) :
    m.getKey? k = some k' → (m.filterMap f)[k]? = m[k]?.bind
      fun x => f k' x :=
  DHashMap.Raw.Const.get?_filterMap_of_getKey?_eq_some h.out

theorem isSome_apply_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    ∀ (h' : k ∈ m.filterMap f),
      (f (m.getKey k (mem_of_mem_filterMap h h'))
        (m[k]'(mem_of_mem_filterMap h h'))).isSome :=
  DHashMap.Raw.Const.isSome_apply_of_mem_filterMap h.out

@[simp]
theorem getElem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {g} (h : m.WF) :
    (m.filterMap f)[k]'g =
      (f (m.getKey k (mem_of_mem_filterMap h g))
        (m[k]'(mem_of_mem_filterMap h g))).get
          (isSome_apply_of_mem_filterMap h g) :=
  DHashMap.Raw.Const.get_filterMap h.out (h':= g)

/-- Simpler variant of `getElem_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem_filterMap' [LawfulBEq α]
    {f : α → β → Option γ} {k : α} {g} (h : m.WF) :
    (m.filterMap f)[k]'g =
      (f k (m[k]'(mem_of_mem_filterMap h g))).get (by simpa [h] using isSome_apply_of_mem_filterMap h g) := by
  simp [getElem_filterMap, h]

theorem getElem!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    (m.filterMap f)[k]! =
      (m[k]?.pbind (fun x h' =>
      f (m.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h')))
          x)).get! :=
  DHashMap.Raw.Const.get!_filterMap h.out

/-- Simpler variant of `getElem!_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem!_filterMap' [LawfulBEq α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    (m.filterMap f)[k]! = (m[k]?.bind (f k)).get! := by
  simp [getElem!_filterMap, h]

theorem getElem!_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.WF) :
    m.getKey? k = some k' → (m.filterMap f)[k]! = (m[k]?.bind
      fun x => f k' x).get! :=
  DHashMap.Raw.Const.get!_filterMap_of_getKey?_eq_some h.out

theorem getD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} (h : m.WF) :
    getD (m.filterMap f) k fallback =
      (m[k]?.pbind (fun x h' =>
      f (m.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  DHashMap.Raw.Const.getD_filterMap h.out

/-- Simpler variant of `getD_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getD_filterMap' [LawfulBEq α]
    {f : α → β → Option γ} {k : α} {fallback : γ} (h : m.WF) :
    getD (m.filterMap f) k fallback = (m[k]?.bind (f k)).getD fallback := by
  simp [getD_filterMap, h]

theorem getD_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.WF) :
    m.getKey? k = some k' → getD (m.filterMap f) k fallback = (m[k]?.bind
      fun x => f k' x).getD fallback :=
  DHashMap.Raw.Const.getD_filterMap_of_getKey?_eq_some h.out

@[grind =]
theorem getKey?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h h'))).isSome) :=
  DHashMap.Raw.Const.getKey?_filterMap h.out

@[simp]
theorem getKey_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β → Option γ} {k : α} {h'} (h : m.WF) :
    (m.filterMap f).getKey k h' = m.getKey k (mem_of_mem_filterMap h h') :=
  DHashMap.Raw.getKey_filterMap h.out

@[grind =]
theorem getKey!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Option γ} {k : α} (h : m.WF) :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h h'))).isSome)).get! :=
  DHashMap.Raw.Const.getKey!_filterMap h.out

@[grind =]
theorem getKeyD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k fallback : α} (h : m.WF) :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h h'))).isSome)).getD fallback :=
  DHashMap.Raw.Const.getKeyD_filterMap h.out

end filterMap

section filter

theorem filterMap_equiv_filter {f : α → β → Bool} (h : m.WF) :
    (m.filterMap (fun k => Option.guard (fun v => f k v))) ~m (m.filter f) :=
  ⟨DHashMap.Raw.filterMap_equiv_filter h.out⟩

theorem toList_filter
    {f : (a : α) → β → Bool} (h : m.WF) :
    (m.filter f).toList.Perm (m.toList.filter (fun p => f p.1 p.2)) :=
  DHashMap.Raw.Const.toList_filter h.out

theorem keys_filter_key {f : α → Bool} (h : m.WF) :
    (m.filter fun k _ => f k).keys.Perm (m.keys.filter f) :=
  DHashMap.Raw.keys_filter_key h.out

@[grind =]
theorem isEmpty_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.WF) :
    (m.filter f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ m), f (m.getKey k h) (m[k]' h) = false :=
  DHashMap.Raw.Const.isEmpty_filter_iff h.out

theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.WF) :
    (m.filter f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), f (m.getKey k h) (m[k]'h) :=
  DHashMap.Raw.Const.isEmpty_filter_eq_false_iff h.out

-- TODO: `contains_filter` is missing

@[grind =]
theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    k ∈ m.filter f ↔ ∃ (h' : k ∈ m),
      f (m.getKey k h') (m[k]' h') :=
  DHashMap.Raw.Const.mem_filter h.out

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    k ∈ m.filter f → k ∈ m :=
  DHashMap.Raw.mem_of_mem_filter h.out

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.WF) :
    (m.filter f).size ≤ m.size :=
  DHashMap.Raw.size_filter_le_size h.out

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.WF) :
    (m.filter f).size = m.size ↔ ∀ (a : α) (h : a ∈ m),
      f (m.getKey a h) m[a] :=
  DHashMap.Raw.Const.size_filter_eq_size_iff h.out

theorem filter_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.WF) :
    (m.filter f) ~m m ↔ ∀ (a : α) (h : a ∈ m),
      f (m.getKey a h) m[a] :=
  ⟨fun h' => (DHashMap.Raw.Const.filter_equiv_self_iff h.out).mp h'.1,
    fun h' => ⟨(DHashMap.Raw.Const.filter_equiv_self_iff h.out).mpr h'⟩⟩

@[simp]
theorem getElem?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    (m.filter f)[k]? = m[k]?.pfilter (fun x h' =>
      f (m.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x) :=
  DHashMap.Raw.Const.get?_filter h.out

/-- Simpler variant of `getElem?_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem?_filter' [LawfulBEq α]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    (m.filter f)[k]? = m[k]?.filter (f k) := by
  simp [getElem?_filter, h]

theorem getElem?_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} (h : m.WF) :
    m.getKey? k = some k' →
      (m.filter f)[k]? = m[k]?.filter (f k') :=
  DHashMap.Raw.Const.get?_filter_of_getKey?_eq_some h.out

@[simp, grind =]
theorem getElem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} (h : m.WF) :
    (m.filter f)[k]' h' = m[k]' (mem_of_mem_filter h h') :=
  DHashMap.Raw.Const.get_filter h.out (h' := h')

theorem getElem!_filter [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    (m.filter f)[k]! =
      (m[k]?.pfilter (fun x h' =>
      f (m.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  DHashMap.Raw.Const.get!_filter h.out

/-- Simpler variant of `getElem!_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem!_filter' [LawfulBEq α] [Inhabited β]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    (m.filter f)[k]! = (m[k]?.filter (f k)).get! := by
  simp [getElem!_filter, h]

theorem getElem!_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k k' : α} (h : m.WF) :
    m.getKey? k = some k' →
      (m.filter f)[k]! = (m[k]?.filter (fun x => f k' x)).get! :=
  DHashMap.Raw.Const.get!_filter_of_getKey?_eq_some h.out

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} (h : m.WF) :
    getD (m.filter f) k fallback = (m[k]?.pfilter (fun x h' =>
      f (m.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  DHashMap.Raw.Const.getD_filter h.out

/-- Simpler variant of `getD_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem getD_filter' [LawfulBEq α]
    {f : α → β → Bool} {k : α} {fallback : β} (h : m.WF) :
    getD (m.filter f) k fallback = (m[k]?.filter (f k)).getD fallback := by
  simp [getD_filter, h]

theorem getD_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} {fallback : β} (h : m.WF) :
    m.getKey? k = some k' →
      getD (m.filter f) k fallback =
        (m[k]?.filter (fun x => f k' x)).getD fallback :=
  DHashMap.Raw.Const.getD_filter_of_getKey?_eq_some h.out

theorem keys_filter [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} (h : m.WF) :
    (m.filter f).keys.Perm
      (m.keys.attach.filter (fun ⟨x, h'⟩ => f x (m[x]' (mem_of_mem_keys h h')))).unattach :=
  DHashMap.Raw.Const.keys_filter h.out

@[grind =]
theorem getKey?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]' (mem_of_getKey?_eq_some h h')))) :=
  DHashMap.Raw.Const.getKey?_filter h.out

theorem getKey?_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} (h : m.WF) :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f :=
  DHashMap.Raw.getKey?_filter_key h.out

@[simp, grind =]
theorem getKey_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.WF) {h'} :
    (m.filter f).getKey k h' = m.getKey k (mem_of_mem_filter h h') :=
  DHashMap.Raw.getKey_filter h.out

@[grind =]
theorem getKey!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Bool} {k : α} (h : m.WF) :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]' (mem_of_getKey?_eq_some h h'))))).get! :=
  DHashMap.Raw.Const.getKey!_filter h.out

theorem getKey!_filter_key [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} (h : m.WF) :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! :=
  DHashMap.Raw.getKey!_filter_key h.out

@[grind =]
theorem getKeyD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k fallback : α} (h : m.WF) :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]' (mem_of_getKey?_eq_some h h'))))).getD fallback :=
  DHashMap.Raw.Const.getKeyD_filter h.out

theorem getKeyD_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} (h : m.WF) :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback :=
  DHashMap.Raw.getKeyD_filter_key h.out

end filter

section map

theorem map_id_equiv (h : m.WF) : (m.map fun _ v => v) ~m m :=
  ⟨DHashMap.Raw.map_id_equiv h.out⟩

theorem map_map_equiv {f : α → β → γ} {g : α → γ → δ} (h : m.WF) :
    ((m.map f).map g) ~m (m.map fun k v => g k (f k v)) :=
  ⟨DHashMap.Raw.map_map_equiv h.out⟩

theorem toList_map {f : (a : α) → β → γ} (h : m.WF) :
    (m.map f).toList.Perm (m.toList.map (fun p => ⟨p.1, f p.1 p.2⟩)) :=
  DHashMap.Raw.Const.toList_map h.out

theorem keys_map {f : α → β → γ} (h : m.WF) : (m.map f).keys.Perm m.keys :=
  DHashMap.Raw.keys_map h.out

theorem filterMap_equiv_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} (h : m.WF) :
    (m.filterMap (fun k v => Option.some (f k v))) ~m (m.map f) :=
  ⟨DHashMap.Raw.filterMap_equiv_map h.out⟩

@[simp, grind =]
theorem isEmpty_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} (h : m.WF) :
    (m.map f).isEmpty = m.isEmpty :=
  DHashMap.Raw.isEmpty_map h.out

@[simp, grind =]
theorem contains_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f).contains k = m.contains k :=
  DHashMap.Raw.contains_map h.out

theorem contains_of_contains_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f).contains k = true → m.contains k = true :=
  DHashMap.Raw.contains_of_contains_map h.out

@[simp, grind =]
theorem mem_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β → γ} {k : α} (h : m.WF) :
    k ∈ (m.map f) ↔ k ∈ m :=
  DHashMap.Raw.mem_map h.out

theorem mem_of_mem_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    k ∈ (m.map f) → k ∈ m :=
  DHashMap.Raw.mem_of_mem_map h.out

@[simp, grind =]
theorem size_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} (h : m.WF) :
    (m.map f).size = m.size :=
  DHashMap.Raw.size_map h.out

@[simp, grind =]
theorem getKey?_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f).getKey? k = m.getKey? k :=
  DHashMap.Raw.getKey?_map h.out

@[simp, grind =]
theorem getKey_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} (h : m.WF) :
    (m.map f).getKey k h' = m.getKey k (mem_of_mem_map h h') :=
  DHashMap.Raw.getKey_map h.out

@[simp, grind =]
theorem getKey!_map [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f).getKey! k = m.getKey! k :=
  DHashMap.Raw.getKey!_map h.out

@[simp, grind =]
theorem getKeyD_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k fallback : α} (h : m.WF) :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback :=
  DHashMap.Raw.getKeyD_map h.out

@[simp, grind =]
theorem getElem?_map [LawfulBEq α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f)[k]? = m[k]?.map (f k) :=
  DHashMap.Raw.Const.get?_map h.out

/-- Variant of `getElem?_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem getElem?_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f)[k]? = m[k]?.pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => (mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h')) :=
  DHashMap.Raw.Const.get?_map' h.out

theorem getElem?_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} (h : m.WF) (h' : m.getKey? k = some k') :
    (m.map f)[k]? = m[k]?.map (f k') :=
  DHashMap.Raw.Const.get?_map_of_getKey?_eq_some h.out h'

@[simp, grind =]
theorem getElem_map [LawfulBEq α]
    {f : α → β → γ} {k : α} {h'} (h : m.WF) :
    (m.map f)[k]' h' =
      (f k (m[k]' (mem_of_mem_map h h'))) :=
  DHashMap.Raw.Const.get_map h.out (h':= h')

/-- Variant of `getElem_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem getElem_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} (h : m.WF) :
    (m.map f)[k]' h' =
      (f (m.getKey k (mem_of_mem_map h h'))
        (m[k]' (mem_of_mem_map h h'))) :=
  DHashMap.Raw.Const.get_map' h.out (h':= h')

@[grind =]
theorem getElem!_map [LawfulBEq α] [Inhabited γ]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f)[k]! =
      (m[k]?.map (f k)).get! :=
  DHashMap.Raw.Const.get!_map h.out

/-- Variant of `getElem!_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getElem!_map' [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} (h : m.WF) :
    (m.map f)[k]! =
      (m[k]?.pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => (mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))).get! :=
  DHashMap.Raw.Const.get!_map' h.out

theorem getElem!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.WF) (h' : m.getKey? k = some k') :
    (m.map f)[k]! = (m[k]?.map (f k')).get! :=
  DHashMap.Raw.Const.get!_map_of_getKey?_eq_some h.out h'

@[grind =]
theorem getD_map [LawfulBEq α]
    {f : α → β → γ} {k : α} {fallback : γ} (h : m.WF) :
    (m.map f).getD k fallback =
      (m[k]?.map (f k)).getD fallback :=
  DHashMap.Raw.Const.getD_map h.out

/-- Variant of `getD_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getD_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} (h : m.WF) :
    getD (m.map f) k fallback =
      (m[k]?.pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => (mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  DHashMap.Raw.Const.getD_map' h.out

theorem getD_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.WF) (h' : m.getKey? k = some k') :
    (m.map f).getD k fallback = (m[k]?.map (f k')).getD fallback :=
  DHashMap.Raw.Const.getD_map_of_getKey?_eq_some h.out h'

end map
attribute [simp] contains_eq_false_iff_not_mem
end Raw

end Std.HashMap
