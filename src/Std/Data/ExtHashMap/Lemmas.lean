/-
Copyright (c) 2025 Robin Arnez, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Std.Data.ExtHashMap.Basic
import Std.Data.ExtDHashMap.Lemmas

/-!
# Extensional hash map lemmas

This module contains lemmas about `Std.ExtHashMap`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} {_ : BEq α} {_ : Hashable α}

namespace Std.ExtHashMap

section

variable {m : ExtHashMap α β}

private theorem ext {m m' : ExtHashMap α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

private theorem ext_iff {m m' : ExtHashMap α β} : m = m' ↔ m.inner = m'.inner :=
  ⟨fun h => h ▸ rfl, ext⟩

@[simp, grind =]
theorem isEmpty_iff [EquivBEq α] [LawfulHashable α] : m.isEmpty ↔ m = ∅ :=
  ExtDHashMap.isEmpty_iff.trans ext_iff.symm

@[simp]
theorem isEmpty_eq_false_iff [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ¬m = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[simp]
theorem empty_eq : ∅ = m ↔ m = ∅ := eq_comm

@[simp, grind =]
theorem emptyWithCapacity_eq [EquivBEq α] [LawfulHashable α] {c} : (emptyWithCapacity c : ExtHashMap α β) = ∅ :=
  ext ExtDHashMap.emptyWithCapacity_eq

@[simp]
theorem not_insert_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    ¬m.insert k v = ∅ :=
  (not_congr ext_iff).mpr ExtDHashMap.not_insert_eq_empty

theorem mem_iff_contains [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ m.contains a :=
  ExtDHashMap.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a ↔ a ∈ m :=
  Iff.rfl

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  ExtDHashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m :=
  ExtDHashMap.mem_congr hab

@[simp, grind =] theorem contains_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : ExtHashMap α β).contains a = false :=
  ExtDHashMap.contains_empty

@[simp] theorem not_mem_empty [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ (∅ : ExtHashMap α β) :=
  ExtDHashMap.not_mem_empty

theorem eq_empty_iff_forall_contains [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ ∀ a, m.contains a = false :=
  ext_iff.trans ExtDHashMap.eq_empty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ ∀ a, ¬a ∈ m :=
  ext_iff.trans ExtDHashMap.eq_empty_iff_forall_not_mem

@[simp] theorem insert_eq_insert [EquivBEq α] [LawfulHashable α] {p : α × β} :
    Insert.insert p m = m.insert p.1 p.2 :=
  rfl

@[simp] theorem singleton_eq_insert [EquivBEq α] [LawfulHashable α] {p : α × β} :
    Singleton.singleton p = (∅ : ExtHashMap α β).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  ExtDHashMap.contains_insert

@[simp, grind =]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m :=
  ExtDHashMap.mem_insert

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  ExtDHashMap.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m :=
  ExtDHashMap.mem_of_mem_insert

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).contains k := by simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : k ∈ m.insert k v := by
  simp

@[simp, grind =]
theorem size_empty [EquivBEq α] [LawfulHashable α] : (∅ : ExtHashMap α β).size = 0 :=
  ExtDHashMap.size_empty

theorem eq_empty_iff_size_eq_zero [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ m.size = 0 :=
  ext_iff.trans ExtDHashMap.eq_empty_iff_size_eq_zero

@[grind =]
theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  ExtDHashMap.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    m.size ≤ (m.insert k v).size :=
  ExtDHashMap.size_le_size_insert

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).size ≤ m.size + 1 :=
  ExtDHashMap.size_insert_le

@[simp, grind =]
theorem erase_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : ExtHashMap α β).erase a = ∅ :=
  ext ExtDHashMap.erase_empty

@[simp]
theorem erase_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} :
    m.erase k = ∅ ↔ m = ∅ ∨ m.size = 1 ∧ k ∈ m := by
  simpa only [ext_iff] using ExtDHashMap.erase_eq_empty_iff

@[simp, grind =]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  ExtDHashMap.contains_erase

@[simp, grind =]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  ExtDHashMap.mem_erase

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  ExtDHashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m :=
  ExtDHashMap.mem_of_mem_erase

@[grind =] theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  ExtDHashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  ExtDHashMap.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  ExtDHashMap.size_le_size_erase

@[simp, grind =]
theorem containsThenInsert_fst [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.containsThenInsert k v).1 = m.contains k :=
  ExtDHashMap.containsThenInsert_fst

@[simp, grind =]
theorem containsThenInsert_snd [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.containsThenInsert k v).2 = m.insert k v :=
  ext (ExtDHashMap.containsThenInsert_snd)

@[simp, grind =]
theorem containsThenInsertIfNew_fst [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  ExtDHashMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsertIfNew_snd [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  ext ExtDHashMap.containsThenInsertIfNew_snd

@[simp, grind =] theorem get_eq_getElem [EquivBEq α] [LawfulHashable α] {a : α} {h} : get m a h = m[a]'h := rfl
@[simp, grind =] theorem get?_eq_getElem? [EquivBEq α] [LawfulHashable α] {a : α} : get? m a = m[a]? := rfl
@[simp, grind =] theorem get!_eq_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : get! m a = m[a]! := rfl

@[simp, grind =]
theorem getElem?_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : ExtHashMap α β)[a]? = none :=
  ExtDHashMap.Const.get?_empty

@[grind =]
theorem getElem?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  ExtDHashMap.Const.get?_insert

@[simp]
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v)[k]? = some v :=
  ExtDHashMap.Const.get?_insert_self

theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = m[a]?.isSome :=
  ExtDHashMap.Const.contains_eq_isSome_get?

@[simp]
theorem isSome_getElem?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    m[a]?.isSome = m.contains a :=
  contains_eq_isSome_getElem?.symm

theorem mem_iff_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ m[a]?.isSome :=
  ExtDHashMap.Const.mem_iff_isSome_get?

@[simp]
theorem isSome_getElem?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    m[a]?.isSome ↔ a ∈ m :=
  mem_iff_isSome_getElem?.symm

theorem getElem?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m[a]? = none :=
  ExtDHashMap.Const.get?_eq_none_of_contains_eq_false

theorem getElem?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m[a]? = none :=
  ExtDHashMap.Const.get?_eq_none

@[grind =] theorem getElem?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k)[a]? = if k == a then none else m[a]? :=
  ExtDHashMap.Const.get?_erase

@[simp]
theorem getElem?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k)[k]? = none :=
  ExtDHashMap.Const.get?_erase_self

theorem getElem?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m[a]? = m[b]? :=
  ExtDHashMap.Const.get?_congr hab

@[grind =] theorem getElem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    (m.insert k v)[a]'h₁ =
      if h₂ : k == a then v else m[a]'(mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  ExtDHashMap.Const.get_insert (h₁ := h₁)

@[simp]
theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v)[k]'mem_insert_self = v :=
  ExtDHashMap.Const.get_insert_self

@[simp, grind =]
theorem getElem_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k)[a]'h' = m[a]'(mem_of_mem_erase h') :=
  ExtDHashMap.Const.get_erase (h' := h')

theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) :
    m[a]? = some (m[a]'h') :=
  ExtDHashMap.Const.get?_eq_some_get h'

theorem getElem_eq_get_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m[a]'h = m[a]?.get (mem_iff_isSome_getElem?.mp h) :=
  ExtDHashMap.Const.get_eq_get_get? (h := h)

@[grind =]
theorem get_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m[a]?.get h = m[a]'(mem_iff_isSome_getElem?.mpr h) :=
  ExtDHashMap.Const.get_get?

theorem getElem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) {h'} :
    m[a]'h' = m[b]'((mem_congr hab).1 h') :=
  ExtDHashMap.Const.get_congr hab (h' := h')

@[simp, grind =]
theorem getElem!_empty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    (∅ : ExtHashMap α β)[a]! = default :=
  ExtDHashMap.Const.get!_empty

@[grind =] theorem getElem!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    (m.insert k v)[a]! = if k == a then v else m[a]! :=
  ExtDHashMap.Const.get!_insert

@[simp]
theorem getElem!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} :
    (m.insert k v)[k]! = v :=
  ExtDHashMap.Const.get!_insert_self

theorem getElem!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {a : α} : m.contains a = false → m[a]! = default :=
  ExtDHashMap.Const.get!_eq_default_of_contains_eq_false

theorem getElem!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → m[a]! = default :=
  ExtDHashMap.Const.get!_eq_default

@[grind =] theorem getElem!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} :
    (m.erase k)[a]! = if k == a then default else m[a]! :=
  ExtDHashMap.Const.get!_erase

@[simp]
theorem getElem!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    (m.erase k)[k]! = default :=
  ExtDHashMap.Const.get!_erase_self

theorem getElem?_eq_some_getElem!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {a : α} : m.contains a = true → m[a]? = some m[a]! :=
  ExtDHashMap.Const.get?_eq_some_get!_of_contains

theorem getElem?_eq_some_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → m[a]? = some m[a]! :=
  ExtDHashMap.Const.get?_eq_some_get!

theorem getElem!_eq_get!_getElem? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m[a]?.get! :=
  ExtDHashMap.Const.get!_eq_get!_get?

theorem getElem_eq_getElem! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h'} :
    m[a]'h' = m[a]! :=
  @ExtDHashMap.Const.get_eq_get! _ _ _ _ _ _ _ _ _ h'

theorem getElem!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    m[a]! = m[b]! :=
  ExtDHashMap.Const.get!_congr hab

@[simp, grind =]
theorem getD_empty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    (∅ : ExtHashMap α β).getD a fallback = fallback :=
  ExtDHashMap.Const.getD_empty

@[grind =] theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    (m.insert k v).getD a fallback = if k == a then v else m.getD a fallback :=
  ExtDHashMap.Const.getD_insert

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback v : β} :
   (m.insert k v).getD k fallback = v :=
  ExtDHashMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : β} : m.contains a = false → m.getD a fallback = fallback :=
  ExtDHashMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  ExtDHashMap.Const.getD_eq_fallback

@[grind =] theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  ExtDHashMap.Const.getD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    (m.erase k).getD k fallback = fallback :=
  ExtDHashMap.Const.getD_erase_self

theorem getElem?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → m[a]? = some (m.getD a fallback) :=
  ExtDHashMap.Const.get?_eq_some_getD_of_contains

theorem getElem?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → m[a]? = some (m.getD a fallback) :=
  ExtDHashMap.Const.get?_eq_some_getD

theorem getD_eq_getD_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.getD a fallback = m[a]?.getD fallback :=
  ExtDHashMap.Const.getD_eq_getD_get?

theorem getElem_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h'} :
    m[a]'h' = m.getD a fallback :=
  @ExtDHashMap.Const.get_eq_getD _ _ _ _ _ _ _ _ _ h'

theorem getElem!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m[a]! = m.getD a default :=
  ExtDHashMap.Const.get!_eq_getD_default

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    m.getD a fallback = m.getD b fallback :=
  ExtDHashMap.Const.getD_congr hab

@[simp, grind =]
theorem getKey?_empty [EquivBEq α] [LawfulHashable α] {a : α} :
    (∅ : ExtHashMap α β).getKey? a = none :=
  ExtDHashMap.getKey?_empty

@[grind =] theorem getKey?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  ExtDHashMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).getKey? k = some k :=
  ExtDHashMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  ExtDHashMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_getKey?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome = m.contains a :=
  contains_eq_isSome_getKey?.symm

theorem mem_iff_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ (m.getKey? a).isSome :=
  ExtDHashMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_getKey?.symm

theorem mem_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] {k k' : α}
    (h : m.getKey? k = some k') : k' ∈ m :=
  ExtDHashMap.mem_of_getKey?_eq_some h

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey? a = none :=
  ExtDHashMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none :=
  ExtDHashMap.getKey?_eq_none

@[grind =] theorem getKey?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  ExtDHashMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).getKey? k = none :=
  ExtDHashMap.getKey?_erase_self

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] {k : α} : (m.getKey? k).all (· == k) :=
  ExtDHashMap.getKey?_beq

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] {k k' : α} (h : k == k') :
    m.getKey? k = m.getKey? k' :=
  ExtDHashMap.getKey?_congr h

theorem getKey?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) :
    m.getKey? k = some k :=
  ExtDHashMap.getKey?_eq_some h

theorem getKey?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k = some k := by
  simpa only [mem_iff_contains] using getKey?_eq_some_of_contains h

@[grind =] theorem getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then k else m.getKey a ((mem_of_mem_insert h₁ (by simpa using h₂))) :=
  ExtDHashMap.getKey_insert (h₁ := h₁)

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).getKey k mem_insert_self = k :=
  ExtDHashMap.getKey_insert_self

@[simp, grind =]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  ExtDHashMap.getKey_erase (h' := h')

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α} (h : a ∈ m) :
    m.getKey? a = some (m.getKey a h) :=
  ExtDHashMap.getKey?_eq_some_getKey h

theorem getKey_eq_get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m.getKey a h = (m.getKey? a).get (mem_iff_isSome_getKey?.mp h) :=
  ExtDHashMap.getKey_eq_get_getKey?

@[simp, grind =]
theorem get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  ExtDHashMap.get_getKey?

theorem getKey_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.getKey k h == k :=
  ExtDHashMap.getKey_beq h

theorem getKey_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) :=
  ExtDHashMap.getKey_congr h h₁

@[simp, grind =]
theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k :=
  ExtDHashMap.getKey_eq h

@[simp, grind =]
theorem getKey!_empty [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    (∅ : ExtHashMap α β).getKey! a = default :=
  ExtDHashMap.getKey!_empty

@[grind =] theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β} :
    (m.insert k v).getKey! a = if k == a then k else m.getKey! a :=
  ExtDHashMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {v : β} :
    (m.insert k v).getKey! k = k :=
  ExtDHashMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = false → m.getKey! a = default :=
  ExtDHashMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  ExtDHashMap.getKey!_eq_default

@[grind =] theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  ExtDHashMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m.erase k).getKey! k = default :=
  ExtDHashMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  ExtDHashMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  ExtDHashMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  ExtDHashMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h'} :
    m.getKey a h' = m.getKey! a :=
  @ExtDHashMap.getKey_eq_getKey! _ _ _ _ _ _ _ _ _ h'

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : k == k') :
    m.getKey! k = m.getKey! k' :=
  ExtDHashMap.getKey!_congr h

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) :
    m.getKey! k = k :=
  ExtDHashMap.getKey!_eq_of_contains h

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.getKey! k = k :=
  ExtDHashMap.getKey!_eq_of_mem h

@[simp, grind =]
theorem getKeyD_empty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    (∅ : ExtHashMap α β).getKeyD a fallback = fallback :=
  ExtDHashMap.getKeyD_empty

@[grind =] theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β} :
    (m.insert k v).getKeyD a fallback = if k == a then k else m.getKeyD a fallback :=
  ExtDHashMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] {k fallback : α} {v : β} :
   (m.insert k v).getKeyD k fallback = k :=
  ExtDHashMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : α} : m.contains a = false → m.getKeyD a fallback = fallback :=
  ExtDHashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  ExtDHashMap.getKeyD_eq_fallback

@[grind =] theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  ExtDHashMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  ExtDHashMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  ExtDHashMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  ExtDHashMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  ExtDHashMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : α} {h'} :
    m.getKey a h' = m.getKeyD a fallback :=
  @ExtDHashMap.getKey_eq_getKeyD _ _ _ _ _ _ _ _ _ h'

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = m.getKeyD a default :=
  ExtDHashMap.getKey!_eq_getKeyD_default

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    (h : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback :=
  ExtDHashMap.getKeyD_congr h

theorem getKeyD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getKeyD k fallback = k :=
  ExtDHashMap.getKeyD_eq_of_contains h

theorem getKeyD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) :
    m.getKeyD k fallback = k :=
  ExtDHashMap.getKeyD_eq_of_mem h

@[simp]
theorem not_insertIfNew_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    ¬m.insertIfNew k v = ∅ :=
  (not_congr ext_iff).mpr ExtDHashMap.not_insertIfNew_eq_empty

@[simp, grind =]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  ExtDHashMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m :=
  ExtDHashMap.mem_insertIfNew

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).contains k :=
  ExtDHashMap.contains_insertIfNew_self

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    k ∈ m.insertIfNew k v :=
  ExtDHashMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  ExtDHashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m :=
  ExtDHashMap.mem_of_mem_insertIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `getElem_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  ExtDHashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `getElem_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  ExtDHashMap.mem_of_mem_insertIfNew'

@[grind =] theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  ExtDHashMap.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    m.size ≤ (m.insertIfNew k v).size :=
  ExtDHashMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  ExtDHashMap.size_insertIfNew_le

@[grind =] theorem getElem?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v)[a]? = if k == a ∧ ¬k ∈ m then some v else m[a]? :=
  ExtDHashMap.Const.get?_insertIfNew

@[grind =] theorem getElem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    (m.insertIfNew k v)[a]'h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else m[a]'(mem_of_mem_insertIfNew' h₁ h₂) :=
  ExtDHashMap.Const.get_insertIfNew (h₁ := h₁)

@[grind =] theorem getElem!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    (m.insertIfNew k v)[a]! = if k == a ∧ ¬k ∈ m then v else m[a]! :=
  ExtDHashMap.Const.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    (m.insertIfNew k v).getD a fallback =
      if k == a ∧ ¬k ∈ m then v else m.getD a fallback :=
  ExtDHashMap.Const.getD_insertIfNew

@[grind =] theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a :=
  ExtDHashMap.getKey?_insertIfNew

@[grind =] theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂) :=
  ExtDHashMap.getKey_insertIfNew

@[grind =] theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a :=
  ExtDHashMap.getKey!_insertIfNew

@[grind =] theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β} :
    getKeyD (m.insertIfNew k v) a fallback = if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback :=
  ExtDHashMap.getKeyD_insertIfNew

@[simp, grind =]
theorem getThenInsertIfNew?_fst [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (getThenInsertIfNew? m k v).1 = get? m k :=
  ExtDHashMap.Const.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  ext (ExtDHashMap.Const.getThenInsertIfNew?_snd)

instance [EquivBEq α] [LawfulHashable α] : LawfulGetElem (ExtHashMap α β) α β (fun m a => a ∈ m) where
  getElem?_def m a _ := by
    split
    · exact getElem?_eq_some_getElem ‹_›
    · exact getElem?_eq_none ‹_›
  getElem!_def m a := by
    rw [getElem!_eq_get!_getElem?]
    split <;> simp_all

variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[simp, grind =]
theorem insertMany_nil [EquivBEq α] [LawfulHashable α] :
    insertMany m [] = m :=
  ext ExtDHashMap.Const.insertMany_nil

@[simp, grind =]
theorem insertMany_list_singleton [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v :=
  ext ExtDHashMap.Const.insertMany_list_singleton

@[grind =]
theorem insertMany_cons [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l :=
  ext ExtDHashMap.Const.insertMany_cons

@[grind _=_]
theorem insertMany_append [EquivBEq α] [LawfulHashable α] {l₁ l₂ : List (α × β)} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[elab_as_elim]
theorem insertMany_ind [EquivBEq α] [LawfulHashable α]
    {motive : ExtHashMap α β → Prop} (m : ExtHashMap α β) {l : ρ}
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) :=
  show motive ⟨ExtDHashMap.Const.insertMany m.1 l⟩ from
    ExtDHashMap.Const.insertMany_ind m.inner l init fun m => insert ⟨m⟩

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) :=
  ExtDHashMap.Const.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k :=
  ExtDHashMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} (mem : k ∈ insertMany m l)
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    k ∈ m :=
  ExtDHashMap.Const.mem_of_mem_insertMany_list mem contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l :=
  ExtDHashMap.Const.mem_insertMany_of_mem

theorem getElem?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]? = m[k]? :=
  ExtDHashMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']? = some v :=
  ExtDHashMap.Const.get?_insertMany_list_of_mem k_beq distinct mem

@[grind =] theorem getElem?_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (insertMany m l)[k]? = (l.findSomeRev? (fun ⟨a, b⟩ => if a == k then some b else none)).or m[k]? :=
  ExtDHashMap.Const.get?_insertMany_list

theorem getElem_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l)[k] = m[k]'(mem_of_mem_insertMany_list h contains_eq_false) :=
  ExtDHashMap.Const.get_insertMany_list_of_contains_eq_false contains_eq_false (h := h)

theorem getElem_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h} :
    (insertMany m l)[k'] = v :=
  ExtDHashMap.Const.get_insertMany_list_of_mem k_beq distinct mem (h := h)

theorem getElem!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l)[k]! = m[k]! :=
  ExtDHashMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    (insertMany m l)[k']! = v :=
  ExtDHashMap.Const.get!_insertMany_list_of_mem k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  ExtDHashMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v :=
  ExtDHashMap.Const.getD_insertMany_list_of_mem k_beq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k :=
  ExtDHashMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k :=
  ExtDHashMap.Const.getKey?_insertMany_list_of_mem k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) :=
  ExtDHashMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (insertMany m l).getKey k' h = k :=
  ExtDHashMap.Const.getKey_insertMany_list_of_mem k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k :=
  ExtDHashMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k :=
  ExtDHashMap.Const.getKey!_insertMany_list_of_mem k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback :=
  ExtDHashMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k :=
  ExtDHashMap.Const.getKeyD_insertMany_list_of_mem k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  ExtDHashMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    m.size ≤ (insertMany m l).size :=
  ExtDHashMap.Const.size_le_size_insertMany_list

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  ExtDHashMap.Const.size_le_size_insertMany

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length :=
  ExtDHashMap.Const.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp]
theorem insertMany_list_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    m.insertMany l = ∅ ↔ m = ∅ ∧ l = [] := by
  simpa only [ext_iff] using ExtDHashMap.Const.insertMany_list_eq_empty_iff

theorem eq_empty_of_insertMany_eq_empty [EquivBEq α] [LawfulHashable α] {l : ρ} :
    m.insertMany l = ∅ → m = ∅ := by
  simpa only [ext_iff] using ExtDHashMap.Const.eq_empty_of_insertMany_eq_empty

variable {m : ExtHashMap α Unit}
variable {ρ : Type w} [ForIn Id ρ α]

@[simp]
theorem insertManyIfNewUnit_nil [EquivBEq α] [LawfulHashable α] :
    insertManyIfNewUnit m [] = m :=
  ext ExtDHashMap.Const.insertManyIfNewUnit_nil

@[simp]
theorem insertManyIfNewUnit_list_singleton [EquivBEq α] [LawfulHashable α] {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () :=
  ext ExtDHashMap.Const.insertManyIfNewUnit_list_singleton

theorem insertManyIfNewUnit_cons [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l :=
  ext ExtDHashMap.Const.insertManyIfNewUnit_cons

@[elab_as_elim]
theorem insertManyIfNewUnit_ind [EquivBEq α] [LawfulHashable α]
    {motive : ExtHashMap α Unit → Prop} (m : ExtHashMap α Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l) :=
  show motive ⟨ExtDHashMap.Const.insertManyIfNewUnit m.1 l⟩ from
    ExtDHashMap.Const.insertManyIfNewUnit_ind m.inner l init fun m => insert ⟨m⟩

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) :=
  ExtDHashMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k :=
  ExtDHashMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m :=
  ExtDHashMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem mem_insertManyIfNewUnit_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} : k ∈ m → k ∈ insertManyIfNewUnit m l :=
  ExtDHashMap.Const.mem_insertManyIfNewUnit_of_mem

theorem getElem?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l)[k]? =
      if k ∈ m ∨ l.contains k then some () else none :=
  ExtDHashMap.Const.get?_insertManyIfNewUnit_list

theorem getElem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {h} :
    (insertManyIfNewUnit m l)[k] = () :=
  rfl

theorem getElem!_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l)[k]! = () :=
  rfl

theorem getD_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () := by
  rfl

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit m l) k = none :=
  ExtDHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k') (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit m l) k' = some k :=
  ExtDHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) :
    getKey? (insertManyIfNewUnit m l) k = getKey? m k :=
  ExtDHashMap.Const.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k') (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) {h} :
    getKey (insertManyIfNewUnit m l) k' h = k :=
  ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKey_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    getKey (insertManyIfNewUnit m l) k h = getKey m k mem :=
  ExtDHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default :=
  ExtDHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k :=
  ExtDHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    getKey! (insertManyIfNewUnit m l) k = getKey! m k :=
  ExtDHashMap.Const.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit m l) k fallback = fallback :=
  ExtDHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l ) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k :=
  ExtDHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback :=
  ExtDHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length :=
  ExtDHashMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size :=
  ExtDHashMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_le_size_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertManyIfNewUnit m l).size :=
  ExtDHashMap.Const.size_le_size_insertManyIfNewUnit

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length :=
  ExtDHashMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem insertManyIfNewUnit_list_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List α} :
    insertManyIfNewUnit m l = ∅ ↔ m = ∅ ∧ l = [] := by
  simpa only [ext_iff] using ExtDHashMap.Const.insertManyIfNewUnit_list_eq_empty_iff

theorem eq_empty_of_insertManyIfNewUnit_eq_empty [EquivBEq α] [LawfulHashable α] {l : ρ} :
    insertManyIfNewUnit m l = ∅ → m = ∅ := by
  simpa only [ext_iff] using ExtDHashMap.Const.eq_empty_of_insertManyIfNewUnit_eq_empty

end

section

@[simp, grind =]
theorem ofList_nil [EquivBEq α] [LawfulHashable α] :
    ofList ([] : List (α × β)) = ∅ :=
  ext ExtDHashMap.Const.ofList_nil

@[simp, grind =]
theorem ofList_singleton [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : ExtHashMap α β).insert k v :=
  ext ExtDHashMap.Const.ofList_singleton

@[grind _=_]
theorem ofList_cons [EquivBEq α] [LawfulHashable α] {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : ExtHashMap α β).insert k v) tl :=
  ext ExtDHashMap.Const.ofList_cons

theorem ofList_eq_insertMany_empty [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    ofList l = insertMany (∅ : ExtHashMap α β) l :=
  ext ExtDHashMap.Const.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  ExtDHashMap.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ ofList l ↔ (l.map Prod.fst).contains k :=
  ExtDHashMap.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]? = none :=
  ExtDHashMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']? = some v :=
  ExtDHashMap.Const.get?_ofList_of_mem k_beq distinct mem

theorem getElem_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l)[k'] = v :=
  ExtDHashMap.Const.get_ofList_of_mem k_beq distinct mem (h := h)

theorem getElem!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l)[k]! = (default : β) :=
  ExtDHashMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l)[k']! = v :=
  ExtDHashMap.Const.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback :=
  ExtDHashMap.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v :=
  ExtDHashMap.Const.getD_ofList_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  ExtDHashMap.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k :=
  ExtDHashMap.Const.getKey?_ofList_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  ExtDHashMap.Const.getKey_ofList_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  ExtDHashMap.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k :=
  ExtDHashMap.Const.getKey!_ofList_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  ExtDHashMap.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k :=
  ExtDHashMap.Const.getKeyD_ofList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  ExtDHashMap.Const.size_ofList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).size ≤ l.length :=
  ExtDHashMap.Const.size_ofList_le

grind_pattern size_ofList => (ofList l).size

@[simp]
theorem ofList_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    ofList l = ∅ ↔ l = [] :=
  ext_iff.trans ExtDHashMap.Const.ofList_eq_empty_iff

@[simp]
theorem unitOfList_nil [EquivBEq α] [LawfulHashable α] :
    unitOfList ([] : List α) = ∅ :=
  ext ExtDHashMap.Const.unitOfList_nil

@[simp]
theorem unitOfList_singleton [EquivBEq α] [LawfulHashable α] {k : α} :
    unitOfList [k] = (∅ : ExtHashMap α Unit).insertIfNew k () :=
  ext ExtDHashMap.Const.unitOfList_singleton

theorem unitOfList_cons [EquivBEq α] [LawfulHashable α] {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      insertManyIfNewUnit ((∅ : ExtHashMap α Unit).insertIfNew hd ()) tl :=
  ext ExtDHashMap.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k :=
  ExtDHashMap.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k :=
  ExtDHashMap.Const.mem_unitOfList

@[simp]
theorem getElem?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l)[k]? =
    if l.contains k then some () else none :=
  ExtDHashMap.Const.get?_unitOfList

@[simp]
theorem getElem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {h} :
    (unitOfList l)[k] = () :=
  rfl

@[simp]
theorem getElem!_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l)[k]! = () :=
  rfl

@[simp]
theorem getD_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () :=
  rfl

theorem getKey?_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none :=
  ExtDHashMap.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k :=
  ExtDHashMap.Const.getKey?_unitOfList_of_mem k_beq distinct mem

theorem getKey_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (unitOfList l) k' h = k :=
  ExtDHashMap.Const.getKey_unitOfList_of_mem k_beq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default :=
  ExtDHashMap.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k :=
  ExtDHashMap.Const.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback :=
  ExtDHashMap.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (unitOfList l) k' fallback = k :=
  ExtDHashMap.Const.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length :=
  ExtDHashMap.Const.size_unitOfList distinct

theorem size_unitOfList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).size ≤ l.length :=
  ExtDHashMap.Const.size_unitOfList_le

@[simp]
theorem unitOfList_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List α} :
    unitOfList l = ∅ ↔ l = [] :=
  ext_iff.trans ExtDHashMap.Const.unitOfList_eq_empty_iff

end

section Alter

variable {m : ExtHashMap α β}

theorem alter_eq_empty_iff_erase_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    alter m k f = ∅ ↔ m.erase k = ∅ ∧ f m[k]? = none := by
  simpa only [ext_iff] using ExtDHashMap.Const.alter_eq_empty_iff_erase_eq_empty

@[simp]
theorem alter_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    alter m k f = ∅ ↔ (m = ∅ ∨ (m.size = 1 ∧ k ∈ m)) ∧ f m[k]? = none := by
  simpa only [ext_iff] using ExtDHashMap.Const.alter_eq_empty_iff

@[grind =] theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    (alter m k f).contains k' = if k == k' then (f m[k]?).isSome else m.contains k' :=
  ExtDHashMap.Const.contains_alter

@[grind =] theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    k' ∈ alter m k f ↔ if k == k' then (f m[k]?).isSome = true else k' ∈ m :=
  ExtDHashMap.Const.mem_alter

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : k == k') : k' ∈ alter m k f ↔ (f m[k]?).isSome :=
  ExtDHashMap.Const.mem_alter_of_beq h

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).contains k = (f m[k]?).isSome :=
  ExtDHashMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    k ∈ alter m k f ↔ (f m[k]?).isSome :=
  ExtDHashMap.Const.mem_alter_self

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) :
    (alter m k f).contains k' = m.contains k' :=
  ExtDHashMap.Const.contains_alter_of_beq_eq_false h

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) : k' ∈ alter m k f ↔ k' ∈ m :=
  ExtDHashMap.Const.mem_alter_of_beq_eq_false h

@[grind =] theorem size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (m.alter k f).size =
      if k ∈ m ∧ (f m[k]?).isNone then
        m.size - 1
      else if k ∉ m ∧ (f m[k]?).isSome then
        m.size + 1
      else
        m.size :=
  ExtDHashMap.Const.size_alter

theorem size_alter_eq_add_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f m[k]?).isSome) :
    (alter m k f).size = m.size + 1 :=
  ExtDHashMap.Const.size_alter_eq_add_one h h'

theorem size_alter_eq_sub_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f m[k]?).isNone) :
    (alter m k f).size = m.size - 1 :=
  ExtDHashMap.Const.size_alter_eq_sub_one h h'

theorem size_alter_eq_self_of_not_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f m[k]?).isNone) :
    (alter m k f).size = m.size :=
  ExtDHashMap.Const.size_alter_eq_self_of_not_mem h h'

theorem size_alter_eq_self_of_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f m[k]?).isSome) :
    (alter m k f).size = m.size :=
  ExtDHashMap.Const.size_alter_eq_self_of_mem h h'

theorem size_alter_le_size [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).size ≤ m.size + 1 :=
  ExtDHashMap.Const.size_alter_le_size

theorem size_le_size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    m.size - 1 ≤ (alter m k f).size :=
  ExtDHashMap.Const.size_le_size_alter

@[grind =] theorem getElem?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (alter m k f)[k']? =
      if k == k' then
        f m[k]?
      else
        m[k']? :=
  ExtDHashMap.Const.get?_alter

@[deprecated getElem?_alter (since := "2025-02-09")]
theorem get?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    get? (alter m k f) k' =
      if k == k' then
        f (get? m k)
      else
        get? m k' :=
  ExtDHashMap.Const.get?_alter

@[simp]
theorem getElem?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f)[k]? = f m[k]? :=
  ExtDHashMap.Const.get?_alter_self

@[deprecated getElem?_alter_self (since := "2025-02-09")]
theorem get?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    get? (alter m k f) k = f (get? m k) :=
  ExtDHashMap.Const.get?_alter_self

@[grind =] theorem getElem_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    {h : k' ∈ alter m k f} :
    (alter m k f)[k'] =
      if heq : k == k' then
        haveI h' : (f m[k]?).isSome := mem_alter_of_beq heq |>.mp h
        f m[k]? |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m[(k')]'h' :=
  ExtDHashMap.Const.get_alter (h := h)

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
  ExtDHashMap.Const.get_alter

@[simp]
theorem getElem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    {h : k ∈ alter m k f} :
    haveI h' : (f m[k]?).isSome := mem_alter_self.mp h
    (alter m k f)[k] = (f m[k]?).get h' :=
  ExtDHashMap.Const.get_alter_self (h := h)

@[deprecated getElem_alter_self (since := "2025-02-09")]
theorem get_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    {h : k ∈ alter m k f} :
    haveI h' : (f (get? m k)).isSome := mem_alter_self.mp h
    get (alter m k f) k h = (f (get? m k)).get h' :=
  ExtDHashMap.Const.get_alter_self

@[grind =] theorem getElem!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} : (alter m k f)[k']! =
      if k == k' then
        f m[k]? |>.get!
      else
        m[k']! :=
  ExtDHashMap.Const.get!_alter

@[deprecated getElem!_alter (since := "2025-02-09")]
theorem get!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} : get! (alter m k f) k' =
      if k == k' then
        f (get? m k) |>.get!
      else
        get! m k' :=
  ExtDHashMap.Const.get!_alter

@[simp]
theorem getElem!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} : (alter m k f)[k]! = (f m[k]?).get! :=
  ExtDHashMap.Const.get!_alter_self

@[deprecated getElem!_alter_self (since := "2025-02-09")]
theorem get!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} : get! (alter m k f) k = (f (get? m k)).get! :=
  ExtDHashMap.Const.get!_alter_self

@[grind =] theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter m k f) k' fallback =
      if k == k' then
        f m[k]? |>.getD fallback
      else
        getD m k' fallback :=
  ExtDHashMap.Const.getD_alter

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter m k f) k fallback = (f m[k]?).getD fallback :=
  ExtDHashMap.Const.getD_alter_self

@[grind =] theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (alter m k f).getKey? k' =
      if k == k' then
        if (f m[k]?).isSome then some k else none
      else
        m.getKey? k' :=
  ExtDHashMap.Const.getKey?_alter

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (alter m k f).getKey? k = if (f m[k]?).isSome then some k else none :=
  ExtDHashMap.Const.getKey?_alter_self

@[grind =] theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} : (alter m k f).getKey! k' =
      if k == k' then
        if (f m[k]?).isSome then k else default
      else
        m.getKey! k' :=
  ExtDHashMap.Const.getKey!_alter

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (alter m k f).getKey! k = if (f m[k]?).isSome then k else default :=
  ExtDHashMap.Const.getKey!_alter_self

@[grind =] theorem getKey_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} {h : k' ∈ alter m k f} :
    (alter m k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  ExtDHashMap.Const.getKey_alter

@[simp]
theorem getKey_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} {h : k ∈ alter m k f} :
    (alter m k f).getKey k h = k :=
  ExtDHashMap.Const.getKey_alter_self

@[grind =] theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    {f : Option β → Option β} :
    (alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f m[k]?).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  ExtDHashMap.Const.getKeyD_alter

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : Option β → Option β} :
    (alter m k f).getKeyD k fallback = if (f m[k]?).isSome then k else fallback :=
  ExtDHashMap.Const.getKeyD_alter_self

end Alter

section Modify

variable {m : ExtHashMap α β}

@[simp]
theorem modify_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    modify m k f = ∅ ↔ m = ∅ := by
  simpa only [ext_iff] using ExtDHashMap.Const.modify_eq_empty_iff

@[simp, grind =]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    (modify m k f).contains k' = m.contains k' :=
  ExtDHashMap.Const.contains_modify

@[simp, grind =]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    k' ∈ modify m k f ↔ k' ∈ m :=
  ExtDHashMap.Const.mem_modify

@[simp, grind =]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f).size = m.size :=
  ExtDHashMap.Const.size_modify

@[grind =] theorem getElem?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    (modify m k f)[k']? =
      if k == k' then
        m[k]?.map f
      else
        m[k']? :=
  ExtDHashMap.Const.get?_modify

@[deprecated getElem?_modify (since := "2025-02-09")]
theorem get?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    get? (modify m k f) k' =
      if k == k' then
        get? m k |>.map f
      else
        get? m k' :=
  ExtDHashMap.Const.get?_modify

@[simp]
theorem getElem?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f)[k]? = m[k]?.map f :=
  ExtDHashMap.Const.get?_modify_self

@[deprecated getElem?_modify_self (since := "2025-02-09")]
theorem get?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    get? (modify m k f) k = (get? m k).map f :=
  ExtDHashMap.Const.get?_modify_self

@[grind =] theorem getElem_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    {h : k' ∈ modify m k f} :
    (modify m k f)[k'] =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        f m[k]
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m[k'] :=
  ExtDHashMap.Const.get_modify (h := h)

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
  ExtDHashMap.Const.get_modify

@[simp]
theorem getElem_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    (modify m k f)[k] = f m[k] :=
  ExtDHashMap.Const.get_modify_self (h := h)

@[deprecated getElem_modify_self (since := "2025-02-09")]
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    get (modify m k f) k h = f (get m k h') :=
  ExtDHashMap.Const.get_modify_self

@[grind =] theorem getElem!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    (modify m k f)[k']! =
      if k == k' then
        m[k]?.map f |>.get!
      else
        m[k']! :=
  ExtDHashMap.Const.get!_modify

@[deprecated getElem!_modify (since := "2025-02-09")]
theorem get!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    get! (modify m k f) k' =
      if k == k' then
        get? m k |>.map f |>.get!
      else
        get! m k' :=
  ExtDHashMap.Const.get!_modify

@[simp]
theorem getElem!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} :
    (modify m k f)[k]! = (m[k]?.map f).get! :=
  ExtDHashMap.Const.get!_modify_self

@[deprecated getElem!_modify_self (since := "2025-02-09")]
theorem get!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} :
    get! (modify m k f) k = ((get? m k).map f).get! :=
  ExtDHashMap.Const.get!_modify_self

@[grind =] theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} :
    getD (modify m k f) k' fallback =
      if k == k' then
        m[k]?.map f |>.getD fallback
      else
        getD m k' fallback :=
  ExtDHashMap.Const.getD_modify

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} :
    getD (modify m k f) k fallback = (m[k]?.map f).getD fallback :=
  ExtDHashMap.Const.getD_modify_self

@[grind =] theorem getKey?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    (modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  ExtDHashMap.Const.getKey?_modify

theorem getKey?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (modify m k f).getKey? k = if k ∈ m then some k else none :=
  ExtDHashMap.Const.getKey?_modify_self

@[grind =] theorem getKey!_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β} :
    (modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  ExtDHashMap.Const.getKey!_modify

theorem getKey!_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β} :
    (modify m k f).getKey! k = if k ∈ m then k else default :=
  ExtDHashMap.Const.getKey!_modify_self

@[grind =] theorem getKey_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    {h : k' ∈ modify m k f} :
    (modify m k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  ExtDHashMap.Const.getKey_modify

@[simp]
theorem getKey_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    {h : k ∈ modify m k f} : (modify m k f).getKey k h = k :=
  ExtDHashMap.Const.getKey_modify_self

@[grind =] theorem getKeyD_modify [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} :
    (modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  ExtDHashMap.Const.getKeyD_modify

theorem getKeyD_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : β → β} : (modify m k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  ExtDHashMap.Const.getKeyD_modify_self

end Modify

section Ext

variable {m₁ m₂ : ExtHashMap α β}

@[ext 900]
theorem ext_getKey_getElem? [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : ExtHashMap α β}
    (hk : ∀ k hk hk', m₁.getKey k hk = m₂.getKey k hk')
    (hv : ∀ k : α, m₁[k]? = m₂[k]?) : m₁ = m₂ :=
  ext (ExtDHashMap.Const.ext_getKey_get? hk hv)

@[ext]
theorem ext_getElem? [LawfulBEq α] {m₁ m₂ : ExtHashMap α β}
    (h : ∀ k : α, m₁[k]? = m₂[k]?) : m₁ = m₂ :=
  ext (ExtDHashMap.Const.ext_get? h)

theorem ext_getKey?_unit [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : ExtHashMap α Unit} (h : ∀ k, m₁.getKey? k = m₂.getKey? k) : m₁ = m₂ :=
  ext (ExtDHashMap.Const.ext_getKey?_unit h)

theorem ext_contains_unit [LawfulBEq α]
    {m₁ m₂ : ExtHashMap α Unit} (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ = m₂ :=
  ext (ExtDHashMap.Const.ext_contains_unit h)

theorem ext_mem_unit [LawfulBEq α]
    {m₁ m₂ : ExtHashMap α Unit} (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ = m₂ :=
  ext (ExtDHashMap.Const.ext_mem_unit h)

end Ext

section filterMap

variable {m : ExtHashMap α β}

theorem filterMap_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} :
    m.filterMap f = ∅ ↔ ∀ k h, f (m.getKey k h) (m[k]'h) = none :=
  ext_iff.trans ExtDHashMap.Const.filterMap_eq_empty_iff

@[grind =] theorem mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f (m.getKey k h) m[k]).isSome :=
  ExtDHashMap.Const.mem_filterMap

theorem contains_of_contains_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).contains k = true → m.contains k = true :=
  ExtDHashMap.contains_of_contains_filterMap

theorem mem_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f → k ∈ m :=
  ExtDHashMap.mem_of_mem_filterMap

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).size ≤ m.size :=
  ExtDHashMap.size_filterMap_le_size

grind_pattern size_filterMap_le_size => (m.filterMap f).size

theorem size_filterMap_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).size = m.size ↔ ∀ k h, (f (m.getKey k h) m[k]).isSome :=
  ExtDHashMap.Const.size_filterMap_eq_size_iff

@[simp]
theorem getElem?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f)[k]? = m[k]?.pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x) :=
  ExtDHashMap.Const.get?_filterMap

/-- Simpler variant of `getElem?_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem?_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f)[k]? = m[k]?.bind fun x => f k x := by
  simp [getElem?_filterMap]

theorem getElem?_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.filterMap f)[k]? = m[k]?.bind (f k') :=
  ExtDHashMap.Const.get?_filterMap_of_getKey?_eq_some h

theorem isSome_apply_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ m.filterMap f),
      (f (m.getKey k (mem_of_mem_filterMap h))
        (m[k]'(mem_of_mem_filterMap h))).isSome :=
  ExtDHashMap.Const.isSome_apply_of_mem_filterMap

@[simp] theorem getElem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    (m.filterMap f)[k]'h =
      (f (m.getKey k (mem_of_mem_filterMap h))
        (m[k]'(mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  ExtDHashMap.Const.get_filterMap (h := h)

/-- Simpler variant of `getElem_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    (m.filterMap f)[k]'h =
      (f k (m[k]'(mem_of_mem_filterMap h))).get (by simpa using isSome_apply_of_mem_filterMap h) := by
  simp [getElem_filterMap]

@[grind =] theorem getElem!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f)[k]! =
      (m[k]?.pbind (fun x h' =>
        f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  ExtDHashMap.Const.get!_filterMap

theorem getElem!_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.filterMap f)[k]! = (m[k]?.bind (f k')).get! :=
  ExtDHashMap.Const.get!_filterMap_of_getKey?_eq_some h

@[grind =] theorem getD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    (m.filterMap f).getD k fallback =
      (m[k]?.pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  ExtDHashMap.Const.getD_filterMap

theorem getD_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    (m.filterMap f).getD k fallback = (m[k]?.bind (f k')).getD fallback :=
  ExtDHashMap.Const.getD_filterMap_of_getKey?_eq_some h

@[grind =] theorem getKey?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))).isSome) :=
  ExtDHashMap.Const.getKey?_filterMap

@[simp, grind =]
theorem getKey_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h'} :
    (m.filterMap f).getKey k h' = m.getKey k (mem_of_mem_filterMap h') :=
  ExtDHashMap.getKey_filterMap

@[grind =] theorem getKey!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))).isSome)).get! :=
  ExtDHashMap.Const.getKey!_filterMap

@[grind =] theorem getKeyD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  ExtDHashMap.Const.getKeyD_filterMap

end filterMap

section filter

variable {m : ExtHashMap α β}

theorem filterMap_eq_filter [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    (m.filterMap (fun k => Option.guard (fun v => f k v))) = m.filter f :=
  ext ExtDHashMap.filterMap_eq_filter

theorem filter_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    m.filter f = ∅ ↔ ∀ k h, f (m.getKey k h) (m[k]'h) = false :=
  ext_iff.trans ExtDHashMap.Const.filter_eq_empty_iff

@[grind =] theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ (h' : k ∈ m), f (m.getKey k h') m[k] :=
  ExtDHashMap.Const.mem_filter

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).contains k = true → m.contains k = true :=
  ExtDHashMap.contains_of_contains_filter

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f → k ∈ m :=
  ExtDHashMap.mem_of_mem_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size ≤ m.size :=
  ExtDHashMap.size_filter_le_size

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f (m.getKey k h) (m.get k h) :=
  ExtDHashMap.Const.size_filter_eq_size_iff

theorem filter_eq_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    m.filter f = m ↔ ∀ k h, f (m.getKey k h) (m.get k h) :=
  ext_iff.trans ExtDHashMap.Const.filter_eq_self_iff

theorem getElem?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f)[k]? = m[k]?.pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x) :=
  ExtDHashMap.Const.get?_filter

/-- Simpler variant of `getElem?_filter` when `LawfulBEq` is available. -/
@[simp, grind =]
theorem getElem?_filter' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f)[k]? = m[k]?.filter (f k) := by
  simp [getElem?_filter]

theorem getElem?_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      (m.filter f)[k]? = m[k]?.filter (fun x => f k' x) :=
  ExtDHashMap.Const.get?_filter_of_getKey?_eq_some

@[simp, grind =] theorem getElem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} :
    (m.filter f)[k]'(h') = m[k]'(mem_of_mem_filter h') :=
  ExtDHashMap.Const.get_filter (h' := h')

theorem getElem!_filter [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    (m.filter f)[k]! =
      (m[k]?.pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  ExtDHashMap.Const.get!_filter

/-- Simpler variant of `getElem!_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem getElem!_filter' [LawfulBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    (m.filter f)[k]! = (m[k]?.filter (f k)).get! := by
  simp [getElem!_filter]

theorem getElem!_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      (m.filter f)[k]! = (m[k]?.filter (f k')).get! :=
  ExtDHashMap.Const.get!_filter_of_getKey?_eq_some

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} :
    (m.filter f).getD k fallback = (m[k]?.pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  ExtDHashMap.Const.getD_filter

/-- Simpler variant of `getD_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem getD_filter' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} :
    (m.filter f).getD k fallback = (m[k]?.filter (f k)).getD fallback := by
  simp [getD_filter]

theorem getD_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} {fallback : β} :
    m.getKey? k = some k' →
      (m.filter f).getD k fallback =
        (m[k]?.filter (fun x => f k' x)).getD fallback :=
  ExtDHashMap.Const.getD_filter_of_getKey?_eq_some

@[grind =] theorem getKey?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h')))) :=
  ExtDHashMap.Const.getKey?_filter

theorem getKey?_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f :=
  ExtDHashMap.getKey?_filter_key

@[simp, grind =]
theorem getKey_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} :
    (m.filter f).getKey k h' = m.getKey k (mem_of_mem_filter h') :=
  ExtDHashMap.getKey_filter

@[grind =] theorem getKey!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))))).get! :=
  ExtDHashMap.Const.getKey!_filter

theorem getKey!_filter_key [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! :=
  ExtDHashMap.getKey!_filter_key

@[grind =] theorem getKeyD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m[x]'(mem_of_getKey?_eq_some h'))))).getD fallback :=
  ExtDHashMap.Const.getKeyD_filter

theorem getKeyD_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback :=
  ExtDHashMap.getKeyD_filter_key

end filter

section map

variable {m : ExtHashMap α β}

@[simp]
theorem map_id_fun [EquivBEq α] [LawfulHashable α] : m.map (fun _ v => v) = m :=
  ext ExtDHashMap.map_id_fun

@[simp]
theorem map_map [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {g : α → γ → δ} :
    (m.map f).map g = m.map fun k v => g k (f k v) :=
  ext ExtDHashMap.map_map

theorem filterMap_equiv_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} :
    (m.filterMap (fun k v => some (f k v))) = m.map f :=
  ext ExtDHashMap.filterMap_eq_map

@[simp]
theorem map_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → β → γ} :
    m.map f = ∅ ↔ m = ∅ := by
  simpa only [ext_iff] using ExtDHashMap.map_eq_empty_iff

@[simp, grind =]
theorem contains_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f).contains k = m.contains k :=
  ExtDHashMap.contains_map

theorem contains_of_contains_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f).contains k = true → m.contains k = true :=
  ExtDHashMap.contains_of_contains_map

@[simp, grind =]
theorem mem_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    k ∈ m.map f ↔ k ∈ m := by
  simp only [mem_iff_contains, contains_map]

theorem mem_of_mem_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    k ∈ m.map f → k ∈ m :=
  ExtDHashMap.contains_of_contains_map

@[simp, grind =]
theorem size_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} :
    (m.map f).size = m.size :=
  ExtDHashMap.size_map

@[simp, grind =]
theorem getElem?_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.map (f k) :=
  ExtDHashMap.Const.get?_map

/-- Variant of `getElem?_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem getElem?_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h')) :=
  ExtDHashMap.Const.get?_map'

theorem getElem?_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.map f)[k]? = m[k]?.map (f k') :=
  ExtDHashMap.Const.get?_map_of_getKey?_eq_some h

@[simp, grind =]
theorem getElem_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    (m.map f)[k]' h' =
      f k (m[k]'(mem_of_mem_map h')) :=
  ExtDHashMap.Const.get_map (h' := h')

/-- Variant of `getElem_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem getElem_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    (m.map f)[k]'(h') =
      f (m.getKey k (mem_of_mem_map h')) (m[k]'(mem_of_mem_map h')) :=
  ExtDHashMap.Const.get_map' (h' := h')

@[grind =] theorem getElem!_map [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]! =
      (m[k]?.map (f k)).get! :=
  ExtDHashMap.Const.get!_map

/-- Variant of `getElem!_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getElem!_map' [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    (m.map f)[k]! =
      (m[k]?.pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_mem h'))).get! :=
  ExtDHashMap.Const.get!_map'

theorem getElem!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.map f)[k]! = (m[k]?.map (f k')).get! :=
  ExtDHashMap.Const.get!_map_of_getKey?_eq_some h

@[grind =] theorem getD_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    (m.map f).getD k fallback =
      (m[k]?.map (f k)).getD fallback :=
  ExtDHashMap.Const.getD_map

/-- Variant of `getD_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getD_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    (m.map f).getD k fallback =
      (m[k]?.pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  ExtDHashMap.Const.getD_map'

theorem getD_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    (m.map f).getD k fallback = (m[k]?.map (f k')).getD fallback :=
  ExtDHashMap.Const.getD_map_of_getKey?_eq_some h

@[simp, grind =]
theorem getKey?_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    (m.map f).getKey? k = m.getKey? k :=
  ExtDHashMap.getKey?_map

@[simp, grind =]
theorem getKey_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    (m.map f).getKey k h' = m.getKey k (mem_of_mem_map h') :=
  ExtDHashMap.getKey_map

@[simp, grind =]
theorem getKey!_map [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → γ} {k : α} :
    (m.map f).getKey! k = m.getKey! k :=
  ExtDHashMap.getKey!_map

@[simp, grind =]
theorem getKeyD_map [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k fallback : α} :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback :=
  ExtDHashMap.getKeyD_map

end map

end Std.ExtHashMap
