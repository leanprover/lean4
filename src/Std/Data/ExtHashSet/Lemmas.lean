/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.ExtHashMap.Lemmas
import Std.Data.ExtHashSet.Basic

/-!
# Extensional hash set lemmas

This module contains lemmas about `Std.ExtHashSet`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {_ : BEq α} {_ : Hashable α}

namespace Std.ExtHashSet

section

variable {m : ExtHashSet α}

private theorem ext {m m' : ExtHashSet α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

private theorem ext_iff {m m' : ExtHashSet α} : m = m' ↔ m.inner = m'.inner :=
  ⟨fun h => h ▸ rfl, ext⟩

@[simp]
theorem isEmpty_iff [EquivBEq α] [LawfulHashable α] : m.isEmpty ↔ m = ∅ :=
  ExtHashMap.isEmpty_iff.trans ext_iff.symm

@[simp]
theorem isEmpty_eq_false_iff [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ¬m = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[simp]
theorem empty_eq : ∅ = m ↔ m = ∅ := eq_comm

@[simp]
theorem emptyWithCapacity_eq [EquivBEq α] [LawfulHashable α] {c} : (emptyWithCapacity c : ExtHashSet α) = ∅ :=
  ext ExtHashMap.emptyWithCapacity_eq

@[simp]
theorem not_insert_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} :
    ¬m.insert k = ∅ :=
  (not_congr ext_iff).mpr ExtHashMap.not_insertIfNew_eq_empty

theorem mem_iff_contains [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ m.contains a :=
  ExtHashMap.mem_iff_contains

@[simp]
theorem contains_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a ↔ a ∈ m :=
  ExtHashMap.contains_iff_mem

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  ExtHashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  ExtHashMap.mem_congr hab

@[simp] theorem contains_empty [EquivBEq α] [LawfulHashable α] {a : α} :
    (∅ : ExtHashSet α).contains a = false :=
  ExtHashMap.contains_empty

@[simp] theorem not_mem_empty [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ (∅ : ExtHashSet α) :=
  ExtHashMap.not_mem_empty

theorem eq_empty_iff_forall_contains [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ ∀ a, m.contains a = false :=
  ext_iff.trans ExtHashMap.eq_empty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ ∀ a, ¬a ∈ m :=
  ext_iff.trans ExtHashMap.eq_empty_iff_forall_not_mem

@[simp] theorem insert_eq_insert [EquivBEq α] [LawfulHashable α] {a : α} :
    Insert.insert a m = m.insert a :=
  rfl

@[simp] theorem singleton_eq_insert [EquivBEq α] [LawfulHashable α] {a : α} :
    Singleton.singleton a = (∅ : ExtHashSet α).insert a :=
  rfl

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a = (k == a || m.contains a) :=
  ExtHashMap.contains_insertIfNew

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ k == a ∨ a ∈ m :=
  ExtHashMap.mem_insertIfNew

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → (k == a) = false → m.contains a :=
  ExtHashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → (k == a) = false → a ∈ m :=
  ExtHashMap.mem_of_mem_insertIfNew

/-- This is a restatement of `contains_insert` that is written to exactly match the proof
obligation in the statement of `get_insert`. -/
theorem contains_of_contains_insert' [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  ExtHashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_insert` that is written to exactly match the proof obligation
in the statement of `get_insert`. -/
theorem mem_of_mem_insert' [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.insert k → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  ExtHashMap.mem_of_mem_insertIfNew'

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).contains k := by
  simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k := by simp

@[simp]
theorem size_empty [EquivBEq α] [LawfulHashable α] : (∅ : ExtHashSet α).size = 0 :=
  ExtHashMap.size_empty

theorem eq_empty_iff_size_eq_zero [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ m.size = 0 :=
  ext_iff.trans ExtHashMap.eq_empty_iff_size_eq_zero

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size = if k ∈ m then m.size else m.size + 1 :=
  ExtHashMap.size_insertIfNew

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size :=
  ExtHashMap.size_le_size_insertIfNew

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.insert k).size ≤ m.size + 1 :=
  ExtHashMap.size_insertIfNew_le

@[simp]
theorem erase_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : ExtHashSet α).erase a = ∅ :=
  ext ExtHashMap.erase_empty

@[simp]
theorem erase_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} :
    m.erase k = ∅ ↔ m = ∅ ∨ m.size = 1 ∧ k ∈ m := by
  simpa only [ext_iff] using ExtHashMap.erase_eq_empty_iff

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  ExtHashMap.contains_erase

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m :=
  ExtHashMap.mem_erase

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  ExtHashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m :=
  ExtHashMap.mem_of_mem_erase

theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  ExtHashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  ExtHashMap.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  ExtHashMap.size_le_size_erase

@[simp]
theorem get?_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : ExtHashSet α).get? a = none :=
  ExtHashMap.getKey?_empty

theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).get? a = if k == a ∧ ¬k ∈ m then some k else m.get? a :=
  ExtHashMap.getKey?_insertIfNew

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.get? a).isSome :=
  ExtHashMap.contains_eq_isSome_getKey?

@[simp]
theorem isSome_get?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.get? a).isSome = m.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ (m.get? a).isSome :=
  ExtHashMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_get?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.get? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_get?.symm

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.get? a = none :=
  ExtHashMap.getKey?_eq_none_of_contains_eq_false

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.get? a = none :=
  ExtHashMap.getKey?_eq_none

theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  ExtHashMap.getKey?_erase

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).get? k = none :=
  ExtHashMap.getKey?_erase_self

theorem get?_beq [EquivBEq α] [LawfulHashable α] {k : α} : (m.get? k).all (· == k) :=
  ExtHashMap.getKey?_beq

theorem get?_congr [EquivBEq α] [LawfulHashable α] {k k' : α} (h : k == k') :
    m.get? k = m.get? k' :=
  ExtHashMap.getKey?_congr h

theorem get?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) : m.get? k = some k :=
  ExtHashMap.getKey?_eq_some_of_contains h

theorem get?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.get? k = some k :=
  ExtHashMap.getKey?_eq_some h

theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {h₁} :
    (m.insert k).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else m.get a (mem_of_mem_insert' h₁ h₂) :=
  ExtHashMap.getKey_insertIfNew (h₁ := h₁)

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  ExtHashMap.getKey_erase (h' := h')

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) :
    m.get? a = some (m.get a h') :=
  ExtHashMap.getKey?_eq_some_getKey h'

theorem get_eq_get_get? [EquivBEq α] [LawfulHashable α] {k : α} {h} :
    m.get k h = (m.get? k).get (mem_iff_isSome_get?.mp h) :=
  ExtHashMap.getKey_eq_get_getKey?

theorem get_get? [EquivBEq α] [LawfulHashable α] {k : α} {h} :
    (m.get? k).get h = m.get k (mem_iff_isSome_get?.mpr h) :=
  ExtHashMap.get_getKey?

theorem get_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.get k h == k :=
  ExtHashMap.getKey_beq h

theorem get_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.get k₁ h₁ = m.get k₂ ((mem_congr h).mp h₁) :=
  ExtHashMap.getKey_congr h h₁

@[simp]
theorem get_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.get k h = k :=
  ExtHashMap.getKey_eq h

@[simp]
theorem get!_empty [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    (∅ : ExtHashSet α).get! a = default :=
  ExtHashMap.getKey!_empty

theorem get!_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.insert k).get! a = if k == a ∧ ¬k ∈ m then k else m.get! a :=
  ExtHashMap.getKey!_insertIfNew

theorem get!_eq_default_of_contains_eq_false [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.get! a = default :=
  ExtHashMap.getKey!_eq_default_of_contains_eq_false

theorem get!_eq_default [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} :
    ¬a ∈ m → m.get! a = default :=
  ExtHashMap.getKey!_eq_default

theorem get!_erase [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).get! a = if k == a then default else m.get! a :=
  ExtHashMap.getKey!_erase

@[simp]
theorem get!_erase_self [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).get! k = default :=
  ExtHashMap.getKey!_erase_self

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} : m.contains a = true → m.get? a = some (m.get! a) :=
  ExtHashMap.getKey?_eq_some_getKey!_of_contains

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.get? a = some (m.get! a) :=
  ExtHashMap.getKey?_eq_some_getKey!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.get! a = (m.get? a).get! :=
  ExtHashMap.getKey!_eq_get!_getKey?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h'} :
    m.get a h' = m.get! a :=
  ExtHashMap.getKey_eq_getKey!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : k == k') :
    m.get! k = m.get! k' :=
  ExtHashMap.getKey!_congr h

theorem get!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) : m.get! k = k :=
  ExtHashMap.getKey!_eq_of_contains h

theorem get!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.get! k = k :=
  ExtHashMap.getKey!_eq_of_mem h

@[simp]
theorem getD_empty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    (∅ : ExtHashSet α).getD a fallback = fallback :=
  ExtHashMap.getKeyD_empty

theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.insert k).getD a fallback = if k == a ∧ ¬k ∈ m then k else m.getD a fallback :=
  ExtHashMap.getKeyD_insertIfNew

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {a fallback : α} :
    m.contains a = false → m.getD a fallback = fallback :=
  ExtHashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  ExtHashMap.getKeyD_eq_fallback

theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  ExtHashMap.getKeyD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m.erase k).getD k fallback = fallback :=
  ExtHashMap.getKeyD_erase_self

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.contains a = true → m.get? a = some (m.getD a fallback) :=
  ExtHashMap.getKey?_eq_some_getKeyD_of_contains

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    a ∈ m → m.get? a = some (m.getD a fallback) :=
  ExtHashMap.getKey?_eq_some_getKeyD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.getD a fallback = (m.get? a).getD fallback :=
  ExtHashMap.getKeyD_eq_getD_getKey?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a fallback : α} {h'} :
    m.get a h' = m.getD a fallback :=
  @ExtHashMap.getKey_eq_getKeyD _ _ _ _ _ _ _ _ _ h'

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.get! a = m.getD a default :=
  ExtHashMap.getKey!_eq_getKeyD_default

theorem getD_congr [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    (h : k == k') : m.getD k fallback = m.getD k' fallback :=
  ExtHashMap.getKeyD_congr h

theorem getD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getD k fallback = k :=
  ExtHashMap.getKeyD_eq_of_contains h

theorem getD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) : m.getD k fallback = k :=
  ExtHashMap.getKeyD_eq_of_mem h

@[simp]
theorem containsThenInsert_fst [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.containsThenInsert k).1 = m.contains k :=
  ExtHashMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsert_snd [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.containsThenInsert k).2 = m.insert k :=
  ext ExtHashMap.containsThenInsertIfNew_snd

variable {ρ : Type v} [ForIn Id ρ α]

@[simp]
theorem insertMany_nil [EquivBEq α] [LawfulHashable α] :
    insertMany m [] = m :=
  ext ExtHashMap.insertManyIfNewUnit_nil

@[simp]
theorem insertMany_list_singleton [EquivBEq α] [LawfulHashable α] {k : α} :
    insertMany m [k] = m.insert k :=
  ext ExtHashMap.insertManyIfNewUnit_list_singleton

theorem insertMany_cons [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} :
    insertMany m (k :: l) = insertMany (m.insert k) l :=
  ext ExtHashMap.insertManyIfNewUnit_cons

theorem insertMany_append [EquivBEq α] [LawfulHashable α] {l₁ l₂ : List α} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[elab_as_elim]
theorem insertMany_ind [EquivBEq α] [LawfulHashable α]
    {motive : ExtHashSet α → Prop} (m : ExtHashSet α) {l : ρ}
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insert a)) :
    motive (m.insertMany l) :=
  show motive ⟨m.1.insertManyIfNewUnit l⟩ from
    ExtHashMap.insertManyIfNewUnit_ind m.inner l init fun m => insert ⟨m⟩

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertMany m l).contains k = (m.contains k || l.contains k) :=
  ExtHashMap.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ l.contains k :=
  ExtHashMap.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany m l → k ∈ m :=
  ExtHashMap.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l :=
  ExtHashMap.mem_insertManyIfNewUnit_of_mem

theorem get?_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get? (insertMany m l) k = none :=
  ExtHashMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get? (insertMany m l) k' = some k :=
  ExtHashMap.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) :
    get? (insertMany m l) k = get? m k :=
  ExtHashMap.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem get_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) {h} :
    get (insertMany m l) k' h = k :=
  ExtHashMap.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    get (insertMany m l) k h = get m k mem :=
  ExtHashMap.getKey_insertManyIfNewUnit_list_of_mem mem

theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get! (insertMany m l) k = default :=
  ExtHashMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem get!_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get! (insertMany m l) k' = k :=
  ExtHashMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    get! (insertMany m l) k = get! m k :=
  ExtHashMap.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getD_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getD (insertMany m l) k fallback = fallback :=
  ExtHashMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getD_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l)  :
    getD (insertMany m l) k' fallback = k :=
  ExtHashMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  ExtHashMap.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  ExtHashMap.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    m.size ≤ (insertMany m l).size :=
  ExtHashMap.size_le_size_insertManyIfNewUnit_list

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  ExtHashMap.size_le_size_insertManyIfNewUnit

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertMany m l).size ≤ m.size + l.length :=
  ExtHashMap.size_insertManyIfNewUnit_list_le

@[simp]
theorem insertMany_list_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List α} :
    m.insertMany l = ∅ ↔ m = ∅ ∧ l = [] := by
  simpa only [ext_iff] using ExtHashMap.insertManyIfNewUnit_list_eq_empty_iff

theorem eq_empty_of_insertMany_eq_empty [EquivBEq α] [LawfulHashable α] {l : ρ} :
    m.insertMany l = ∅ → m = ∅ := by
  simpa only [ext_iff] using ExtHashMap.eq_empty_of_insertManyIfNewUnit_eq_empty

end

section

@[simp]
theorem ofList_nil [EquivBEq α] [LawfulHashable α] :
    ofList ([] : List α) = ∅ :=
  ext ExtHashMap.unitOfList_nil

@[simp]
theorem ofList_singleton [EquivBEq α] [LawfulHashable α] {k : α} :
    ofList [k] = (∅ : ExtHashSet α).insert k :=
  ext ExtHashMap.unitOfList_singleton

theorem ofList_cons [EquivBEq α] [LawfulHashable α] {hd : α} {tl : List α} :
    ofList (hd :: tl) =
      insertMany ((∅ : ExtHashSet α).insert hd) tl :=
  ext ExtHashMap.unitOfList_cons

theorem ofList_eq_insertMany_empty [EquivBEq α] [LawfulHashable α] {l : List α} :
    ofList l = insertMany (∅ : ExtHashSet α) l :=
  match l with
  | [] => by simp
  | hd :: tl => by simp [ofList_cons, insertMany_cons]

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (ofList l).contains k = l.contains k :=
  ExtHashMap.contains_unitOfList

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ ofList l ↔ l.contains k :=
  ExtHashMap.mem_unitOfList

theorem get?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    get? (ofList l) k = none :=
  ExtHashMap.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get? (ofList l) k' = some k :=
  ExtHashMap.getKey?_unitOfList_of_mem k_beq distinct mem

theorem get_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    get (ofList l) k' h = k :=
  ExtHashMap.getKey_unitOfList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get! (ofList l) k = default :=
  ExtHashMap.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    get! (ofList l) k' = k :=
  ExtHashMap.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getD (ofList l) k fallback = fallback :=
  ExtHashMap.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getD (ofList l) k' fallback = k :=
  ExtHashMap.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (ofList l).size = l.length :=
  ExtHashMap.size_unitOfList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (ofList l).size ≤ l.length :=
  ExtHashMap.size_unitOfList_le

@[simp]
theorem ofList_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List α} :
    ofList l = ∅ ↔ l = [] :=
  ext_iff.trans ExtHashMap.unitOfList_eq_empty_iff

end

section Ext

@[ext 900]
theorem ext_get? [EquivBEq α] [LawfulHashable α] {m₁ m₂ : ExtHashSet α}
    (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ = m₂ :=
  ext (ExtHashMap.ext_getKey?_unit h)

theorem ext_contains [LawfulBEq α] {m₁ m₂ : ExtHashSet α}
    (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ = m₂ :=
  ext (ExtHashMap.ext_contains_unit h)

@[ext]
theorem ext_mem [LawfulBEq α] {m₁ m₂ : ExtHashSet α} (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ = m₂ :=
  ext (ExtHashMap.ext_mem_unit h)

end Ext

section filter

variable {m : ExtHashSet α}

theorem filter_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → Bool} :
    m.filter f = ∅ ↔ ∀ k h, f (m.get k h) = false :=
  ext_iff.trans ExtHashMap.filter_eq_empty_iff

@[simp]
theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ h, f (m.get k h) :=
  ExtHashMap.mem_filter

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter f).contains k → m.contains k :=
  ExtHashMap.contains_of_contains_filter

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    k ∈ m.filter f → k ∈ m :=
  ExtHashMap.mem_of_mem_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter f).size ≤ m.size :=
  ExtHashMap.size_filter_le_size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f (m.get k h) :=
  ExtHashMap.size_filter_eq_size_iff

theorem filter_eq_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    m.filter f = m ↔ ∀ k h, f (m.get k h) :=
  ext_iff.trans ExtHashMap.filter_eq_self_iff

@[simp]
theorem get?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter f).get? k = (m.get? k).filter f :=
  ExtHashMap.getKey?_filter_key

@[simp]
theorem get_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} {h} :
    (m.filter f).get k h = m.get k (mem_of_mem_filter h) :=
  ExtHashMap.getKey_filter

theorem get!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter f).get! k = ((m.get? k).filter f).get! :=
  ExtHashMap.getKey!_filter_key

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} :
    (m.filter f).getD k fallback = ((m.get? k).filter f).getD fallback :=
  ExtHashMap.getKeyD_filter_key

end filter

end Std.ExtHashSet
