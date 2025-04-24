/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Std.Data.ExtDHashMap.Basic

/-!
# Extensional dependent hash map lemmas

This file contains lemmas about `Std.ExtDHashMap`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {_ : BEq α} {_ : Hashable α} {_ : EquivBEq α} {_ : LawfulHashable α}
variable {β : α → Type v} {γ : α → Type w}

namespace Std.ExtDHashMap

variable {m : ExtDHashMap α β}

@[simp]
theorem isEmpty_iff : m.isEmpty ↔ m = ∅ := by
  rcases m with ⟨m⟩
  refine m.equiv_empty_iff_isEmpty.symm.trans ?_
  exact ⟨fun h => Quotient.sound h, Quotient.exact⟩

@[simp]
theorem isEmpty_eq_false_iff : m.isEmpty = false ↔ ¬m = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[simp]
theorem empty_eq : ∅ = m ↔ m = ∅ := eq_comm

@[simp]
theorem emptyWithCapacity_eq {c} : (emptyWithCapacity c : ExtDHashMap α β) = ∅ :=
  isEmpty_iff.mp DHashMap.isEmpty_emptyWithCapacity

@[simp]
theorem not_insert_eq_empty {k : α} {v : β k} :
    ¬m.insert k v = ∅ :=
  m.inductionOn fun _ => isEmpty_eq_false_iff.mp DHashMap.isEmpty_insert

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  Iff.rfl

theorem contains_congr {a b : α} (hab : a == b) : m.contains a = m.contains b :=
  m.inductionOn fun _ => DHashMap.contains_congr hab

theorem mem_congr {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_congr hab

@[simp]
theorem contains_empty {a : α} : (∅ : DHashMap α β).contains a = false :=
  DHashMap.contains_empty

@[simp]
theorem not_mem_empty {a : α} : ¬a ∈ (∅ : DHashMap α β) :=
  DHashMap.not_mem_empty

theorem eq_empty_iff_forall_contains : m = ∅ ↔ ∀ a, m.contains a = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem : m = ∅ ↔ ∀ a, ¬a ∈ m :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_iff_forall_not_mem

@[simp] theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p m = m.insert p.1 p.2 := rfl

@[simp] theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : DHashMap α β).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert {k a : α} {v : β k} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  m.inductionOn fun _ => DHashMap.contains_insert

@[simp]
theorem mem_insert {k a : α} {v : β k} : a ∈ m.insert k v ↔ k == a ∨ a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_insert

theorem contains_of_contains_insert {k a : α} {v : β k} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_insert

theorem mem_of_mem_insert {k a : α} {v : β k} : a ∈ m.insert k v → (k == a) = false → a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_insert

theorem contains_insert_self {k : α} {v : β k} : (m.insert k v).contains k := by simp

theorem mem_insert_self {k : α} {v : β k} : k ∈ m.insert k v := by simp

@[simp]
theorem size_empty : (∅ : ExtDHashMap α β).size = 0 := rfl

theorem eq_empty_iff_size_eq_zero : m = ∅ ↔ m.size = 0 :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ =>
    (Bool.eq_iff_iff.mp DHashMap.isEmpty_eq_size_eq_zero).trans beq_iff_eq

theorem size_insert {k : α} {v : β k} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insert

theorem size_le_size_insert {k : α} {v : β k} : m.size ≤ (m.insert k v).size :=
  m.inductionOn fun _ => DHashMap.size_le_size_insert

theorem size_insert_le {k : α} {v : β k} : (m.insert k v).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insert_le

@[simp]
theorem erase_empty {k : α} : (∅ : ExtDHashMap α β).erase k = ∅ :=
  congrArg Quotient.mk' DHashMap.erase_empty

@[simp]
theorem erase_eq_empty_iff {k : α} : m.erase k = ∅ ↔ m = ∅ ∨ m.size = 1 ∧ k ∈ m := by
  apply isEmpty_iff.symm.trans
  rcases m with ⟨m⟩
  rw [← isEmpty_iff]
  dsimp only [erase, isEmpty, Quotient.mk', Quotient.mk, Quotient.lift]
  simp only [DHashMap.isEmpty_erase, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rfl

@[simp]
theorem contains_erase {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  m.inductionOn fun _ => DHashMap.contains_erase

@[simp]
theorem mem_erase {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [mem_iff_contains, contains_erase]

theorem contains_of_contains_erase {k a : α} :
    (m.erase k).contains a → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_erase

theorem mem_of_mem_erase {k a : α} : a ∈ m.erase k → a ∈ m := by
  simp

theorem size_erase {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  m.inductionOn fun _ => DHashMap.size_erase

theorem size_erase_le {k : α} : (m.erase k).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_erase_le

theorem size_le_size_erase {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  m.inductionOn fun _ => DHashMap.size_le_size_erase

@[simp]
theorem containsThenInsert_fst {k : α} {v : β k} : (m.containsThenInsert k v).1 = m.contains k :=
  m.inductionOn fun _ => DHashMap.containsThenInsert_fst

@[simp]
theorem containsThenInsert_snd {k : α} {v : β k} : (m.containsThenInsert k v).2 = m.insert k v :=
  m.inductionOn fun _ => congrArg Quotient.mk' DHashMap.containsThenInsert_snd

@[simp]
theorem containsThenInsertIfNew_fst {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  m.inductionOn fun _ => DHashMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsertIfNew_snd {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  m.inductionOn fun _ => congrArg Quotient.mk' DHashMap.containsThenInsertIfNew_snd

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} : (∅ : ExtDHashMap α β).get? a = none :=
  DHashMap.get?_empty

theorem get?_insert [LawfulBEq α] {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a :=
  m.inductionOn fun _ => DHashMap.get?_insert

@[simp]
theorem get?_insert_self [LawfulBEq α] {k : α} {v : β k} : (m.insert k v).get? k = some v :=
  m.inductionOn fun _ => DHashMap.get?_insert_self

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome :=
  m.inductionOn fun _ => DHashMap.contains_eq_isSome_get?

theorem mem_iff_isSome_get? [LawfulBEq α] {a : α} : a ∈ m ↔ (m.get? a).isSome :=
  m.inductionOn fun _ => DHashMap.mem_iff_isSome_get?

theorem get?_eq_none_of_contains_eq_false [LawfulBEq α] {a : α} :
    m.contains a = false → m.get? a = none :=
  m.inductionOn fun _ => DHashMap.get?_eq_none_of_contains_eq_false

theorem get?_eq_none [LawfulBEq α] {a : α} : ¬a ∈ m → m.get? a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false

theorem get?_erase [LawfulBEq α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  m.inductionOn fun _ => DHashMap.get?_erase

@[simp]
theorem get?_erase_self [LawfulBEq α] {k : α} : (m.erase k).get? k = none :=
  m.inductionOn fun _ => DHashMap.get?_erase_self

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp]
theorem get?_empty {a : α} : get? (∅ : ExtDHashMap α (fun _ => β)) a = none :=
  DHashMap.Const.get?_empty

theorem get?_insert {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a :=
  m.inductionOn fun _ => DHashMap.Const.get?_insert

@[simp]
theorem get?_insert_self {k : α} {v : β} :
    get? (m.insert k v) k = some v :=
  m.inductionOn fun _ => DHashMap.Const.get?_insert_self

theorem contains_eq_isSome_get? {a : α} :
    m.contains a = (get? m a).isSome :=
  m.inductionOn fun _ => DHashMap.Const.contains_eq_isSome_get?

theorem mem_iff_isSome_get? {a : α} : a ∈ m ↔ (get? m a).isSome :=
  m.inductionOn fun _ => DHashMap.Const.mem_iff_isSome_get?

theorem get?_eq_none_of_contains_eq_false {a : α} :
    m.contains a = false → get? m a = none :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_none_of_contains_eq_false

theorem get?_eq_none {a : α} : ¬a ∈ m → get? m a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false

theorem get?_erase {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a :=
  m.inductionOn fun _ => DHashMap.Const.get?_erase

@[simp]
theorem get?_erase_self {k : α} : get? (m.erase k) k = none :=
  m.inductionOn fun _ => DHashMap.Const.get?_erase_self

theorem get?_eq_get? [LawfulBEq α] {a : α} : get? m a = m.get? a :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_get?

theorem get?_congr {a b : α} (hab : a == b) : get? m a = get? m b :=
  m.inductionOn fun _ => DHashMap.Const.get?_congr hab

end Const

theorem get_insert [LawfulBEq α] {k a : α} {v : β k} {h₁} :
    (m.insert k v).get a h₁ =
      if h₂ : k == a then
        cast (congrArg β (eq_of_beq h₂)) v
      else
        m.get a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  m.inductionOn (fun _ _ => DHashMap.get_insert) h₁

@[simp]
theorem get_insert_self [LawfulBEq α] {k : α} {v : β k} :
    (m.insert k v).get k mem_insert_self = v :=
  m.inductionOn fun _ => DHashMap.get_insert_self

@[simp]
theorem get_erase [LawfulBEq α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  m.inductionOn (fun _ _ => DHashMap.get_erase) h'

theorem get?_eq_some_get [LawfulBEq α] {a : α} (h) : m.get? a = some (m.get a h) :=
  m.inductionOn (fun _ h => DHashMap.get?_eq_some_get h) h

theorem get_eq_get_get? [LawfulBEq α] {a : α} {h} :
    m.get a h = (m.get? a).get (mem_iff_isSome_get?.mp h) :=
  m.inductionOn (fun _ _ => DHashMap.get_eq_get_get?) h

theorem get_get? [LawfulBEq α] {a : α} {h} :
    (m.get? a).get h = m.get a (mem_iff_isSome_get?.mpr h) :=
  m.inductionOn (fun _ _ => DHashMap.get_get?) h

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

theorem get_insert {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v else get m a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_insert) h₁

@[simp]
theorem get_insert_self {k : α} {v : β} :
    get (m.insert k v) k mem_insert_self = v :=
  m.inductionOn fun _ => DHashMap.Const.get_insert_self

@[simp]
theorem get_erase {k a : α} {h'} :
    get (m.erase k) a h' = get m a (mem_of_mem_erase h') :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_erase) h'

theorem get?_eq_some_get {a : α} (h) :
    get? m a = some (get m a h) :=
  m.inductionOn (fun _ h => DHashMap.Const.get?_eq_some_get h) h

theorem get_eq_get_get? {a : α} {h} :
    get m a h = (get? m a).get (mem_iff_isSome_get?.mp h) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_get_get?) h

theorem get_get? {a : α} {h} :
    (get? m a).get h = get m a (mem_iff_isSome_get?.mpr h) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_get?) h

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_get) h

theorem get_congr {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((mem_congr hab).1 h') :=
  m.inductionOn (fun _ hab _ => DHashMap.Const.get_congr hab) hab h'

end Const

@[simp]
theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] :
    (∅ : ExtDHashMap α β).get! a = default :=
  DHashMap.get!_empty

theorem get!_insert [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insert k v).get! a =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.get! a :=
  m.inductionOn fun _ => DHashMap.get!_insert

@[simp]
theorem get!_insert_self [LawfulBEq α] {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b :=
  m.inductionOn fun _ => DHashMap.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default :=
  m.inductionOn fun _ => DHashMap.get!_eq_default_of_contains_eq_false

theorem get!_eq_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    ¬a ∈ m → m.get! a = default :=
  m.inductionOn fun _ => DHashMap.get!_eq_default

theorem get!_erase [LawfulBEq α] {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a :=
  m.inductionOn fun _ => DHashMap.get!_erase

@[simp]
theorem get!_erase_self [LawfulBEq α] {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default :=
  m.inductionOn fun _ => DHashMap.get!_erase_self

theorem get?_eq_some_get!_of_contains [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) :=
  m.inductionOn fun _ => DHashMap.get?_eq_some_get!_of_contains

theorem get?_eq_some_get! [LawfulBEq α] {a : α} [Inhabited (β a)] :
    a ∈ m → m.get? a = some (m.get! a) :=
  m.inductionOn fun _ => DHashMap.get?_eq_some_get!

theorem get!_eq_get!_get? [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! :=
  m.inductionOn fun _ => DHashMap.get!_eq_get!_get?

theorem get_eq_get! [LawfulBEq α] {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a :=
  m.inductionOn (fun _ _ => DHashMap.get_eq_get!) h

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp]
theorem get!_empty [Inhabited β] {a : α} : get! (∅ : ExtDHashMap α (fun _ => β)) a = default :=
  DHashMap.Const.get!_empty

theorem get!_insert [Inhabited β] {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a :=
  m.inductionOn fun _ => DHashMap.Const.get!_insert

@[simp]
theorem get!_insert_self [Inhabited β] {k : α} {v : β} :
    get! (m.insert k v) k = v :=
  m.inductionOn fun _ => DHashMap.Const.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [Inhabited β] {a : α} :
    m.contains a = false → get! m a = default :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_default_of_contains_eq_false

theorem get!_eq_default [Inhabited β] {a : α} :
    ¬a ∈ m → get! m a = default :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_default

theorem get!_erase [Inhabited β] {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a :=
  m.inductionOn fun _ => DHashMap.Const.get!_erase

@[simp]
theorem get!_erase_self [Inhabited β] {k : α} :
    get! (m.erase k) k = default :=
  m.inductionOn fun _ => DHashMap.Const.get!_erase_self

theorem get?_eq_some_get!_of_contains [Inhabited β] {a : α} :
    m.contains a = true → get? m a = some (get! m a) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_get!_of_contains

theorem get?_eq_some_get! [Inhabited β] {a : α} :
    a ∈ m → get? m a = some (get! m a) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_get!

theorem get!_eq_get!_get? [Inhabited β] {a : α} :
    get! m a = (get? m a).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_get!_get?

theorem get_eq_get! [Inhabited β] {a : α} {h} :
    get m a h = get! m a :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_get!) h

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] {a : α} :
    get! m a = m.get! a :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_get!

theorem get!_congr [Inhabited β] {a b : α} (hab : a == b) :
    get! m a = get! m b :=
  m.inductionOn (fun _ hab => DHashMap.Const.get!_congr hab) hab

end Const

@[simp]
theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} :
    (∅ : ExtDHashMap α β).getD a fallback = fallback :=
  DHashMap.getD_empty

theorem getD_insert [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insert k v).getD a fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.getD a fallback :=
  m.inductionOn fun _ => DHashMap.getD_insert

@[simp]
theorem getD_insert_self [LawfulBEq α] {k : α} {fallback v : β k} :
    (m.insert k v).getD k fallback = v :=
  m.inductionOn fun _ => DHashMap.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [LawfulBEq α] {a : α} {fallback : β a} :
    ¬a ∈ m → m.getD a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getD_eq_fallback

theorem getD_erase [LawfulBEq α] {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  m.inductionOn fun _ => DHashMap.getD_erase

@[simp]
theorem getD_erase_self [LawfulBEq α] {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getD_erase_self

theorem get?_eq_some_getD_of_contains [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) :=
  m.inductionOn fun _ => DHashMap.get?_eq_some_getD_of_contains

theorem get?_eq_some_getD [LawfulBEq α] {a : α} {fallback : β a} :
    a ∈ m → m.get? a = some (m.getD a fallback) :=
  m.inductionOn fun _ => DHashMap.get?_eq_some_getD

theorem getD_eq_getD_get? [LawfulBEq α] {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_eq_getD_get?

theorem get_eq_getD [LawfulBEq α] {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback :=
  m.inductionOn (fun _ _ => DHashMap.get_eq_getD) h

theorem get!_eq_getD_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default :=
  m.inductionOn fun _ => DHashMap.get!_eq_getD_default

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp]
theorem getD_empty {a : α} {fallback : β} :
    getD (∅ : ExtDHashMap α (fun _ => β)) a fallback = fallback :=
  DHashMap.Const.getD_empty

theorem getD_insert {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_insert

@[simp]
theorem getD_insert_self {k : α} {fallback v : β} :
   getD (m.insert k v) k fallback = v :=
  m.inductionOn fun _ => DHashMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false {a : α}
    {fallback : β} : m.contains a = false → getD m a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback {a : α} {fallback : β} :
    ¬a ∈ m → getD m a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_fallback

theorem getD_erase {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_erase

@[simp]
theorem getD_erase_self {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_erase_self

theorem get?_eq_some_getD_of_contains {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_getD_of_contains

theorem get?_eq_some_getD {a : α} {fallback : β} :
    a ∈ m → get? m a = some (getD m a fallback) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_getD

theorem getD_eq_getD_get? {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_getD_get?

theorem get_eq_getD {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_getD) h

theorem get!_eq_getD_default [Inhabited β] {a : α} :
    get! m a = getD m a default :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_getD_default

theorem getD_eq_getD [LawfulBEq α] {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_getD

theorem getD_congr {a b : α} {fallback : β} (hab : a == b) :
    getD m a fallback = getD m b fallback :=
  m.inductionOn (fun _ hab => DHashMap.Const.getD_congr hab) hab

end Const

@[simp]
theorem getKey?_empty {a : α} : (∅ : ExtDHashMap α β).getKey? a = none :=
  DHashMap.getKey?_empty

theorem getKey?_insert {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  m.inductionOn fun _ => DHashMap.getKey?_insert

@[simp]
theorem getKey?_insert_self {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k :=
  m.inductionOn fun _ => DHashMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  m.inductionOn fun _ => DHashMap.contains_eq_isSome_getKey?

theorem mem_iff_isSome_getKey? {a : α} :
    a ∈ m ↔ (m.getKey? a).isSome :=
  m.inductionOn fun _ => DHashMap.mem_iff_isSome_getKey?

theorem mem_of_getKey?_eq_some {k k' : α}
    (h : m.getKey? k = some k') : k' ∈ m :=
  m.inductionOn (fun _ h => DHashMap.mem_of_getKey?_eq_some h) h

theorem getKey?_eq_none_of_contains_eq_false {a : α} :
    m.contains a = false → m.getKey? a = none :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none {a : α} : ¬a ∈ m → m.getKey? a = none :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_none

theorem getKey?_erase {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  m.inductionOn fun _ => DHashMap.getKey?_erase

@[simp]
theorem getKey?_erase_self {k : α} : (m.erase k).getKey? k = none :=
  m.inductionOn fun _ => DHashMap.getKey?_erase_self

theorem getKey?_beq {k : α} :
    (m.getKey? k).all (· == k) :=
  m.inductionOn fun _ => DHashMap.getKey?_beq

theorem getKey?_congr {k k' : α} (h : k == k') :
    m.getKey? k = m.getKey? k' :=
  m.inductionOn (fun _ h => DHashMap.getKey?_congr h) h

theorem getKey?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) :
    m.getKey? k = some k :=
  m.inductionOn (fun _ h => DHashMap.getKey?_eq_some_of_contains h) h

theorem getKey?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k = some k :=
  m.inductionOn (fun _ h => DHashMap.getKey?_eq_some h) h

theorem getKey_insert {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  m.inductionOn (fun _ _ => DHashMap.getKey_insert) h₁

@[simp]
theorem getKey_insert_self {k : α} {v : β k} :
    (m.insert k v).getKey k mem_insert_self = k :=
  m.inductionOn fun _ => DHashMap.getKey_insert_self

@[simp]
theorem getKey_erase {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_erase) h'

theorem getKey?_eq_some_getKey {a : α} (h) :
    m.getKey? a = some (m.getKey a h) :=
  m.inductionOn (fun _ h => DHashMap.getKey?_eq_some_getKey h) h

theorem getKey_eq_get_getKey? {a : α} {h} :
    m.getKey a h = (m.getKey? a).get (mem_iff_isSome_getKey?.mp h) :=
  m.inductionOn (fun _ _ => DHashMap.getKey_eq_get_getKey?) h

theorem get_getKey? {a : α} {h} :
    (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  m.inductionOn (fun _ _ => DHashMap.get_getKey?) h

theorem getKey_beq {k : α} (h : k ∈ m) : m.getKey k h == k :=
  m.inductionOn (fun _ h => DHashMap.getKey_beq h) h

theorem getKey_congr {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) :=
  m.inductionOn (fun _ h h₁ => DHashMap.getKey_congr h h₁) h h₁

theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k :=
  m.inductionOn (fun _ h => DHashMap.getKey_eq h) h

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} :
    (∅ : ExtDHashMap α β).getKey! a = default :=
  DHashMap.getKey!_empty

theorem getKey!_insert [Inhabited α] {k a : α} {v : β k} :
    (m.insert k v).getKey! a =
      if k == a then k else m.getKey! a :=
  m.inductionOn fun _ => DHashMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [Inhabited α] {a : α} {b : β a} :
    (m.insert a b).getKey! a = a :=
  m.inductionOn fun _ => DHashMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [Inhabited α]
    {a : α} :
    m.contains a = false → m.getKey! a = default :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [Inhabited α] {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_default

theorem getKey!_erase [Inhabited α] {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  m.inductionOn fun _ => DHashMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [Inhabited α] {k : α} :
    (m.erase k).getKey! k = default :=
  m.inductionOn fun _ => DHashMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [Inhabited α] {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [Inhabited α] {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [Inhabited α] {a : α} {h} :
    m.getKey a h = m.getKey! a :=
  m.inductionOn (fun _ _ => DHashMap.getKey_eq_getKey!) h

theorem getKey!_congr [Inhabited α] {k k' : α} (h : k == k') :
    m.getKey! k = m.getKey! k' :=
  m.inductionOn (fun _ h => DHashMap.getKey!_congr h) h

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) :
    m.getKey! k = k :=
  m.inductionOn (fun _ h => DHashMap.getKey!_eq_of_contains h) h

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.getKey! k = k :=
  m.inductionOn (fun _ h => DHashMap.getKey!_eq_of_mem h) h

@[simp]
theorem getKeyD_empty {a fallback : α} :
    (∅ : ExtDHashMap α β).getKeyD a fallback = fallback :=
  DHashMap.getKeyD_empty

theorem getKeyD_insert {k a fallback : α} {v : β k} :
    (m.insert k v).getKeyD a fallback =
      if k == a then k else m.getKeyD a fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self {k fallback : α} {v : β k} :
    (m.insert k v).getKeyD k fallback = k :=
  m.inductionOn fun _ => DHashMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false {a : α}
    {fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_eq_fallback

theorem getKeyD_erase {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD {a fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD {a fallback : α} {h} :
    m.getKey a h = m.getKeyD a fallback :=
  m.inductionOn (fun _ _ => DHashMap.getKey_eq_getKeyD) h

theorem getKey!_eq_getKeyD_default [Inhabited α] {a : α} :
    m.getKey! a = m.getKeyD a default :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_getKeyD_default

theorem getKeyD_congr {k k' fallback : α}
    (h : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback :=
  m.inductionOn (fun _ h => DHashMap.getKeyD_congr h) h

theorem getKeyD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getKeyD k fallback = k :=
  m.inductionOn (fun _ h => DHashMap.getKeyD_eq_of_contains h) h

theorem getKeyD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) :
    m.getKeyD k fallback = k :=
  m.inductionOn (fun _ h => DHashMap.getKeyD_eq_of_mem h) h

@[simp]
theorem not_insertIfNew_eq_empty {k : α} {v : β k} :
    ¬m.insertIfNew k v = ∅ :=
  isEmpty_eq_false_iff.mp <| m.inductionOn fun _ => DHashMap.isEmpty_insertIfNew

@[simp]
theorem contains_insertIfNew {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  m.inductionOn fun _ => DHashMap.contains_insertIfNew

@[simp]
theorem mem_insertIfNew {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_insertIfNew

theorem contains_insertIfNew_self {k : α} {v : β k} :
    (m.insertIfNew k v).contains k :=
  m.inductionOn fun _ => DHashMap.contains_insertIfNew_self

theorem mem_insertIfNew_self {k : α} {v : β k} :
    k ∈ m.insertIfNew k v :=
  m.inductionOn fun _ => DHashMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_insertIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_insertIfNew'

theorem size_insertIfNew {k : α} {v : β k} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insertIfNew

theorem size_le_size_insertIfNew {k : α} {v : β k} :
    m.size ≤ (m.insertIfNew k v).size :=
  m.inductionOn fun _ => DHashMap.size_le_size_insertIfNew

theorem size_insertIfNew_le {k : α} {v : β k} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insertIfNew_le

theorem get?_insertIfNew [LawfulBEq α] {k a : α} {v : β k} : (m.insertIfNew k v).get? a =
    if h : k == a ∧ ¬k ∈ m then some (cast (congrArg β (eq_of_beq h.1)) v) else m.get? a :=
  m.inductionOn fun _ => DHashMap.get?_insertIfNew

theorem get_insertIfNew [LawfulBEq α] {k a : α} {v : β k} {h₁} : (m.insertIfNew k v).get a h₁ =
    if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v else m.get a
      (mem_of_mem_insertIfNew' h₁ h₂) :=
  m.inductionOn (fun _ _ => DHashMap.get_insertIfNew) h₁

theorem get!_insertIfNew [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v else m.get! a :=
  m.inductionOn fun _ => DHashMap.get!_insertIfNew

theorem getD_insertIfNew [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback :=
  m.inductionOn fun _ => DHashMap.getD_insertIfNew

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

theorem get?_insertIfNew {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some v else get? m a :=
  m.inductionOn fun _ => DHashMap.Const.get?_insertIfNew

theorem get_insertIfNew {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else get m a (mem_of_mem_insertIfNew' h₁ h₂) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_insertIfNew) h₁

theorem get!_insertIfNew [Inhabited β] {k a : α} {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then v else get! m a :=
  m.inductionOn fun _ => DHashMap.Const.get!_insertIfNew

theorem getD_insertIfNew {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then v else getD m a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_insertIfNew

end Const

theorem getKey?_insertIfNew {k a : α} {v : β k} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a :=
  m.inductionOn fun _ => DHashMap.getKey?_insertIfNew

theorem getKey_insertIfNew {k a : α} {v : β k} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂) :=
  m.inductionOn (fun _ _ => DHashMap.getKey_insertIfNew) h₁

theorem getKey!_insertIfNew [Inhabited α] {k a : α} {v : β k} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a :=
  m.inductionOn fun _ => DHashMap.getKey!_insertIfNew

theorem getKeyD_insertIfNew {k a fallback : α} {v : β k} :
    getKeyD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_insertIfNew

@[simp]
theorem getThenInsertIfNew?_fst [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k :=
  m.inductionOn fun _ => DHashMap.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v :=
  m.inductionOn fun _ => congrArg Quotient.mk' DHashMap.getThenInsertIfNew?_snd

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp]
theorem getThenInsertIfNew?_fst {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k :=
  m.inductionOn fun _ => DHashMap.Const.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  m.inductionOn fun _ => congrArg Quotient.mk' DHashMap.Const.getThenInsertIfNew?_snd

end Const

section insertMany

variable {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]

@[simp]
theorem insertMany_nil : m.insertMany [] = m := rfl

@[simp]
theorem insertMany_list_singleton {k : α} {v : β k} :
    m.insertMany [⟨k, v⟩] = m.insert k v := rfl

theorem insertMany_cons {l : List ((a : α) × β a)} {p : (a : α) × β a} :
    m.insertMany (p :: l) = (m.insert p.1 p.2).insertMany l := by
  rcases p with ⟨k, v⟩
  unfold insertMany
  simp only [Id.pure_eq, Id.bind_eq, Id.run, List.forIn_yield_eq_foldl, List.foldl_cons]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insert a.1 a.2) (m.insert k v) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

private theorem insertMany_list_mk {m : DHashMap α β} {l : List ((a : α) × β a)} :
    (ExtDHashMap.insertMany (Quotient.mk _ m) l : ExtDHashMap α β) = Quotient.mk _ (m.insertMany l) := by
  simp only [Quotient.mk]
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    rcases x with ⟨k, v⟩
    simp only [insertMany_cons, DHashMap.insertMany_cons, insert,
      Quotient.mk', Quotient.mk, Quotient.lift, ih]

@[elab_as_elim]
theorem insertMany_ind {motive : ExtDHashMap α β → Prop} (m : ExtDHashMap α β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) := by
  change motive (Subtype.val ?my_mvar)
  exact Subtype.property ?my_mvar motive init (insert _ _ _)

@[simp]
theorem contains_insertMany_list
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).contains k = (m.contains k || (l.map Sigma.fst).contains k) := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.contains_insertMany_list

@[simp]
theorem mem_insertMany_list
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ m.insertMany l ↔ k ∈ m ∨ (l.map Sigma.fst).contains k := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.mem_insertMany_list

theorem mem_of_mem_insertMany_list
    {l : List ((a : α) × β a)} {k : α} (mem : k ∈ m.insertMany l)
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    k ∈ m := by
  refine m.inductionOn (fun _ mem contains_eq_false => ?_) mem contains_eq_false
  simp only [insertMany_list_mk] at mem
  exact DHashMap.mem_of_mem_insertMany_list mem contains_eq_false

theorem mem_insertMany_of_mem {l : ρ} {k : α} (h' : k ∈ m) : k ∈ m.insertMany l :=
  insertMany_ind m l h' fun _ _ _ h => mem_insert.mpr (.inr h)

theorem get?_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).get? k = m.get? k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem get?_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.get?_insertMany_list_of_mem k_beq distinct mem

theorem get_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h} :
    (m.insertMany l).get k h =
      m.get k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.get_insertMany_list_of_contains_eq_false contains_eq_false

theorem get_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (m.insertMany l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.get_insertMany_list_of_mem k_beq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).get! k = m.get! k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem get!_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.get!_insertMany_list_of_mem k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getD k fallback = m.getD k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getD_insertMany_list_of_mem k_beq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey? k = m.getKey? k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey? k' = some k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getKey?_insertMany_list_of_mem k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h} :
    (m.insertMany l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (m.insertMany l).getKey k' h = k := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.getKey_insertMany_list_of_mem k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey! k = m.getKey! k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey! k' = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getKey!_insertMany_list_of_mem k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKeyD k fallback = m.getKeyD k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKeyD k' fallback = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getKeyD_insertMany_list_of_mem k_beq distinct mem

theorem size_insertMany_list
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Sigma.fst).contains a = false) →
      (m.insertMany l).size = m.size + l.length := by
  refine m.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertMany_list_mk]
  exact DHashMap.size_insertMany_list distinct

theorem size_le_size_insertMany_list
    {l : List ((a : α) × β a)} :
    m.size ≤ (m.insertMany l).size := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.size_le_size_insertMany_list

theorem size_le_size_insertMany {l : ρ} : m.size ≤ (m.insertMany l).size :=
  insertMany_ind m l (Nat.le_refl _) fun _ _ _ h => Nat.le_trans h size_le_size_insert

theorem size_insertMany_list_le
    {l : List ((a : α) × β a)} :
    (m.insertMany l).size ≤ m.size + l.length := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.size_insertMany_list_le

@[simp]
theorem insertMany_list_eq_empty_iff {l : List ((a : α) × β a)} :
    m.insertMany l = ∅ ↔ m = ∅ ∧ l = [] := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk, ← isEmpty_iff, ← List.isEmpty_iff,
    Bool.coe_iff_coe, ← Bool.and_eq_true]
  exact DHashMap.isEmpty_insertMany_list

theorem eq_empty_of_insertMany_eq_empty {l : ρ} :
    m.insertMany l = ∅ → m = ∅ :=
  insertMany_ind m l id fun _ _ _ _ h => absurd h not_insert_eq_empty

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}
variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[simp]
theorem insertMany_nil : insertMany m [] = m :=
  rfl

@[simp]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v := rfl

theorem insertMany_cons {l : List (α × β)} {p : α × β} :
    insertMany m (p :: l) = insertMany (m.insert p.1 p.2) l := by
  rcases p with ⟨k, v⟩
  unfold insertMany
  simp only [Id.pure_eq, Id.bind_eq, Id.run, List.forIn_yield_eq_foldl, List.foldl_cons]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insert a.1 a.2) (m.insert k v) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

private theorem insertMany_list_mk {m : DHashMap α fun _ => β} {l : List (α × β)} :
    (insertMany (Quotient.mk _ m) l : ExtDHashMap α fun _ => β) =
      Quotient.mk _ (DHashMap.Const.insertMany m l) := by
  simp only [Quotient.mk]
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    rcases x with ⟨k, v⟩
    simp only [insertMany_cons, DHashMap.Const.insertMany_cons, insert,
      Quotient.mk', Quotient.mk, Quotient.lift, ih]

@[elab_as_elim]
theorem insertMany_ind {motive : ExtDHashMap α (fun _ => β) → Prop}
    (m : ExtDHashMap α fun _ => β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (insertMany m l) := by
  change motive (Subtype.val ?my_mvar)
  exact Subtype.property ?my_mvar motive init (insert _ _ _)

@[simp]
theorem contains_insertMany_list
    {l : List (α × β)} {k : α} :
    (Const.insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.contains_insertMany_list

@[simp]
theorem mem_insertMany_list
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list
    {l : List (α × β)} {k : α} (mem : k ∈ insertMany m l)
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    k ∈ m := by
  refine m.inductionOn (fun _ mem contains_eq_false => ?_) mem contains_eq_false
  simp only [insertMany_list_mk] at mem
  exact DHashMap.Const.mem_of_mem_insertMany_list mem contains_eq_false

theorem mem_insertMany_of_mem {l : ρ} {k : α} (h' : k ∈ m) : k ∈ insertMany m l :=
  insertMany_ind m l h' fun _ _ _ h => mem_insert.mpr (.inr h)

theorem getKey?_insertMany_list_of_contains_eq_false
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey?_insertMany_list_of_mem k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (insertMany m l).getKey k' h = k := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey_insertMany_list_of_mem k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey!_insertMany_list_of_mem k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKeyD_insertMany_list_of_mem k_beq distinct mem

theorem size_insertMany_list
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length := by
  refine m.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertMany_list_mk]
  exact DHashMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list
    {l : List (α × β)} :
    m.size ≤ (insertMany m l).size := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.size_le_size_insertMany_list

theorem size_le_size_insertMany {l : ρ} : m.size ≤ (insertMany m l).size :=
  insertMany_ind m l (Nat.le_refl _) fun _ _ _ h => Nat.le_trans h size_le_size_insert

theorem size_insertMany_list_le
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.size_insertMany_list_le

@[simp]
theorem insertMany_list_eq_empty_iff {l : List (α × β)} :
    insertMany m l = ∅ ↔ m = ∅ ∧ l = [] := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk, ← isEmpty_iff, ← List.isEmpty_iff,
    Bool.coe_iff_coe, ← Bool.and_eq_true]
  exact DHashMap.Const.isEmpty_insertMany_list

theorem eq_empty_of_insertMany_eq_empty {l : ρ} : insertMany m l = ∅ → m = ∅ :=
  insertMany_ind m l id fun _ _ _ _ h => absurd h not_insert_eq_empty

theorem get?_insertMany_list_of_contains_eq_false
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l) k = get? m k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem get?_insertMany_list_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l) k' = v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get?_insertMany_list_of_mem k_beq distinct mem

theorem get_insertMany_list_of_contains_eq_false
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    get (insertMany m l) k h = get m k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get_insertMany_list_of_contains_eq_false contains_eq_false

theorem get_insertMany_list_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h} :
    get (insertMany m l) k' h = v := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get_insertMany_list_of_mem k_beq distinct mem

theorem get!_insertMany_list_of_contains_eq_false
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany m l) k = get! m k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem get!_insertMany_list_of_mem [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany m l) k' = v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get!_insertMany_list_of_mem k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getD_insertMany_list_of_mem k_beq distinct mem

variable {m : ExtDHashMap α (fun _ => Unit)}
variable {ρ : Type w} [ForIn Id ρ α]

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit m [] = m :=
  rfl

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () := rfl

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l := by
  unfold insertManyIfNewUnit
  simp only [Id.pure_eq, Id.bind_eq, Id.run, List.forIn_yield_eq_foldl, List.foldl_cons]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insertIfNew a ()) (m.insertIfNew k ()) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

private theorem insertManyIfNewUnit_list_mk {m : DHashMap α fun _ => Unit} {l : List α} :
    (insertManyIfNewUnit (Quotient.mk _ m) l : ExtDHashMap α fun _ => Unit) =
      Quotient.mk _ (DHashMap.Const.insertManyIfNewUnit m l) := by
  simp only [Quotient.mk]
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    simp only [insertManyIfNewUnit_cons, DHashMap.Const.insertManyIfNewUnit_cons, insertIfNew,
      Quotient.mk', Quotient.mk, Quotient.lift, ih]

@[elab_as_elim]
theorem insertManyIfNewUnit_ind {motive : ExtDHashMap α (fun _ => Unit) → Prop}
    (m : ExtDHashMap α fun _ => Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l) := by
  change motive (Subtype.val ?my_mvar)
  exact Subtype.property ?my_mvar motive init (insert _ _)

@[simp]
theorem contains_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem mem_insertManyIfNewUnit_of_mem {l : ρ} {k : α} (h : k ∈ m) :
    k ∈ insertManyIfNewUnit m l :=
  insertManyIfNewUnit_ind m l h fun _ _ h => mem_insertIfNew.mpr (.inr h)

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit m l) k = none := by
  refine m.inductionOn (fun _ not_mem contains_eq_false => ?_) not_mem contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem
    {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit m l) k' = some k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem => ?_) k_beq not_mem distinct mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem
    {l : List α} {k : α} (h' : k ∈ m) :
    getKey? (insertManyIfNewUnit m l) k = getKey? m k := by
  refine m.inductionOn (fun _ h' => ?_) h'
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_mem h'

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (insertManyIfNewUnit m l) k' h = k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem _ => ?_) k_beq not_mem distinct mem h
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKey_insertManyIfNewUnit_list_of_mem
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    getKey (insertManyIfNewUnit m l) k h = getKey m k mem := by
  refine m.inductionOn (fun _ mem _ => ?_) mem h
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default := by
  refine m.inductionOn (fun _ not_mem contains_eq_false => ?_) not_mem contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem => ?_) k_beq not_mem distinct mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    getKey! (insertManyIfNewUnit m l) k = getKey! m k := by
  refine m.inductionOn (fun _ mem => ?_) mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit m l) k fallback = fallback := by
  refine m.inductionOn (fun _ not_mem contains_eq_false => ?_) not_mem contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem => ?_) k_beq not_mem distinct mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback := by
  refine m.inductionOn (fun _ mem => ?_) mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertManyIfNewUnit_list
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length := by
  refine m.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_le_size_insertManyIfNewUnit
    {l : ρ} : m.size ≤ (insertManyIfNewUnit m l).size :=
  insertManyIfNewUnit_ind m l (Nat.le_refl _) fun _ _ h => Nat.le_trans h size_le_size_insertIfNew

theorem size_insertManyIfNewUnit_list_le
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem insertManyIfNewUnit_list_eq_empty_iff {l : List α} :
    insertManyIfNewUnit m l = ∅ ↔ m = ∅ ∧ l = [] := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk, ← isEmpty_iff, ← List.isEmpty_iff,
    Bool.coe_iff_coe, ← Bool.and_eq_true]
  exact DHashMap.Const.isEmpty_insertManyIfNewUnit_list

theorem eq_empty_of_insertManyIfNewUnit_eq_empty {l : ρ} :
    insertManyIfNewUnit m l = ∅ → m = ∅ :=
  insertManyIfNewUnit_ind m l id fun _ _ _ h => absurd h not_insertIfNew_eq_empty

theorem get?_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit m l) k =
      if k ∈ m ∨ l.contains k then some () else none := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.get?_insertManyIfNewUnit_list

theorem get_insertManyIfNewUnit_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit m l) k h = () :=
  rfl

theorem get!_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit m l) k = () :=
  rfl

theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () :=
  rfl

end Const

end insertMany

end ExtDHashMap

namespace ExtDHashMap

@[simp]
theorem ofList_nil :
    ofList ([] : List ((a : α) × β a)) = ∅ := rfl

@[simp]
theorem ofList_singleton {k : α} {v : β k} :
    ofList [⟨k, v⟩] = (∅ : ExtDHashMap α β).insert k v := rfl

theorem ofList_cons {k : α} {v : β k} {tl : List ((a : α) × β a)} :
    ofList (⟨k, v⟩ :: tl) = ((∅ : ExtDHashMap α β).insert k v).insertMany tl :=
  insertMany_cons

private theorem ofList_eq_mk {l : List ((a : α) × β a)} :
    (ofList l : ExtDHashMap α β) = Quotient.mk _ (DHashMap.ofList l) := by
  change insertMany (Quotient.mk _ _) _ = _
  rw [insertMany_list_mk]
  rfl

@[simp]
theorem contains_ofList
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l).contains k = (l.map Sigma.fst).contains k := by
  simp only [ofList_eq_mk]
  exact DHashMap.contains_ofList

@[simp]
theorem mem_ofList
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l ↔ (l.map Sigma.fst).contains k := by
  simp only [ofList_eq_mk]
  exact DHashMap.mem_ofList

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get? k = none := by
  simp only [ofList_eq_mk]
  exact DHashMap.get?_ofList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  simp only [ofList_eq_mk]
  exact DHashMap.get?_ofList_of_mem k_beq distinct mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp only [ofList_eq_mk]
  exact DHashMap.get_ofList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get! k = default := by
  simp only [ofList_eq_mk]
  exact DHashMap.get!_ofList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp only [ofList_eq_mk]
  exact DHashMap.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getD k fallback = fallback := by
  simp only [ofList_eq_mk]
  exact DHashMap.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp only [ofList_eq_mk]
  exact DHashMap.getD_ofList_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey? k = none := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey? k' = some k := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKey?_ofList_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (ofList l).getKey k' h = k := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKey_ofList_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey! k = default := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey! k' = k := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKey!_ofList_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKeyD k' fallback = k := by
  simp only [ofList_eq_mk]
  exact DHashMap.getKeyD_ofList_of_mem k_beq distinct mem

theorem size_ofList
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length := by
  simp only [ofList_eq_mk]
  exact DHashMap.size_ofList distinct

theorem size_ofList_le
    {l : List ((a : α) × β a)} :
    (ofList l).size ≤ l.length := by
  simp only [ofList_eq_mk]
  exact DHashMap.size_ofList_le

@[simp]
theorem ofList_eq_empty_iff {l : List ((a : α) × β a)} :
    ofList l = ∅ ↔ l = [] := by
  simp only [ofList_eq_mk, ← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe]
  exact DHashMap.isEmpty_ofList

namespace Const

variable {β : Type v}

@[simp]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ :=
  rfl

@[simp]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : ExtDHashMap α (fun _ => β)).insert k v :=
  rfl

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : ExtDHashMap α (fun _ => β)).insert k v) tl :=
  insertMany_cons

private theorem ofList_eq_mk {l : List (α × β)} :
    (ofList l : ExtDHashMap α fun _ => β) = Quotient.mk _ (DHashMap.Const.ofList l) := by
  change insertMany (Quotient.mk _ _) _ = _
  rw [insertMany_list_mk]
  rfl

@[simp]
theorem contains_ofList
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.contains_ofList

@[simp]
theorem mem_ofList
    {l : List (α × β)} {k : α} :
    k ∈ ofList l ↔ (l.map Prod.fst).contains k := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.mem_ofList

theorem get?_ofList_of_contains_eq_false
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l) k = none := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l) k' = some v := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.get?_ofList_of_mem k_beq distinct mem

theorem get_ofList_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l) k' h = v := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.get_ofList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l) k = (default : β) := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l) k' = v := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getD_ofList_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKey?_ofList_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (ofList l).getKey k' h = k := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKey_ofList_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKey!_ofList_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.getKeyD_ofList_of_mem k_beq distinct mem

theorem size_ofList
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.size_ofList distinct

theorem size_ofList_le
    {l : List (α × β)} :
    (ofList l).size ≤ l.length := by
  simp only [ofList_eq_mk]
  exact DHashMap.Const.size_ofList_le

@[simp]
theorem ofList_eq_empty_iff {l : List (α × β)} :
    ofList l = ∅ ↔ l = [] := by
  simp only [ofList_eq_mk, ← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe]
  exact DHashMap.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) = ∅ :=
  rfl

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (∅ : ExtDHashMap α (fun _ => Unit)).insertIfNew k () :=
  rfl

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      insertManyIfNewUnit ((∅ : ExtDHashMap α (fun _ => Unit)).insertIfNew hd ()) tl :=
  insertManyIfNewUnit_cons

private theorem unitOfList_eq_mk {l : List α} :
    (unitOfList l : ExtDHashMap α fun _ => Unit) = Quotient.mk _ (DHashMap.Const.unitOfList l) := by
  change insertManyIfNewUnit (Quotient.mk _ _) _ = _
  rw [insertManyIfNewUnit_list_mk]
  rfl

@[simp]
theorem contains_unitOfList
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.mem_unitOfList

theorem getKey?_unitOfList_of_contains_eq_false
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKey?_unitOfList_of_mem k_beq distinct mem

theorem getKey_unitOfList_of_mem
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (unitOfList l) k' h = k := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKey_unitOfList_of_mem k_beq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKey!_unitOfList_of_mem k_beq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (unitOfList l) k' fallback = k := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.getKeyD_unitOfList_of_mem k_beq distinct mem

theorem size_unitOfList
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.size_unitOfList distinct

theorem size_unitOfList_le
    {l : List α} :
    (unitOfList l).size ≤ l.length := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.size_unitOfList_le

@[simp]
theorem unitOfList_eq_empty_iff {l : List α} :
    unitOfList l = ∅ ↔ l = [] := by
  simp only [unitOfList_eq_mk, ← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe]
  exact DHashMap.Const.isEmpty_unitOfList

@[simp]
theorem get?_unitOfList
    {l : List α} {k : α} :
    get? (unitOfList l) k =
    if l.contains k then some () else none := by
  simp only [unitOfList_eq_mk]
  exact DHashMap.Const.get?_unitOfList

@[simp]
theorem get_unitOfList
    {l : List α} {k : α} {h} :
    get (unitOfList l) k h = () :=
  rfl

@[simp]
theorem get!_unitOfList
    {l : List α} {k : α} :
    get! (unitOfList l) k = () :=
  rfl

@[simp]
theorem getD_unitOfList
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () :=
  rfl

end Const

variable {m : ExtDHashMap α β}

section Alter

theorem alter_eq_empty_iff_erase_eq_empty [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    m.alter k f = ∅ ↔ m.erase k = ∅ ∧ f (m.get? k) = none := by
  rcases m with ⟨m⟩
  simp only [← isEmpty_iff]
  dsimp only [isEmpty, alter, Quotient.lift, Quotient.mk', Quotient.mk]
  simp only [DHashMap.isEmpty_alter_eq_isEmpty_erase, Bool.and_eq_true, Option.isNone_iff_eq_none]
  rfl

@[simp]
theorem alter_eq_empty_iff [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    alter m k f = ∅ ↔ (m = ∅ ∨ (m.size = 1 ∧ k ∈ m)) ∧ f (get? m k) = none := by
  simp only [alter_eq_empty_iff_erase_eq_empty, erase_eq_empty_iff]

theorem contains_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' :=
  m.inductionOn fun _ => DHashMap.contains_alter

theorem mem_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    k' ∈ m.alter k f ↔ if k == k' then (f (m.get? k)).isSome = true else k' ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_alter

theorem mem_alter_of_beq [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} (h : k == k') :
    k' ∈ m.alter k f ↔ (f (m.get? k)).isSome :=
  m.inductionOn (fun _ h => DHashMap.mem_alter_of_beq h) h

@[simp]
theorem contains_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k = (f (m.get? k)).isSome :=
  m.inductionOn fun _ => DHashMap.contains_alter_self

@[simp]
theorem mem_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    k ∈ m.alter k f ↔ (f (m.get? k)).isSome :=
  m.inductionOn fun _ => DHashMap.mem_alter_self

theorem contains_alter_of_beq_eq_false [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : (k == k') = false) : (m.alter k f).contains k' = m.contains k' :=
  m.inductionOn (fun _ h => DHashMap.contains_alter_of_beq_eq_false h) h

theorem mem_alter_of_beq_eq_false [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : (k == k') = false) : k' ∈ m.alter k f ↔ k' ∈ m :=
  m.inductionOn (fun _ h => DHashMap.mem_alter_of_beq_eq_false h) h

theorem size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).size =
      if k ∈ m ∧ (f (m.get? k)).isNone then
        m.size - 1
      else if k ∉ m ∧ (f (m.get? k)).isSome then
        m.size + 1
      else
        m.size :=
  m.inductionOn fun _ => DHashMap.size_alter

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∉ m) (h' : (f (m.get? k)).isSome) :
    (m.alter k f).size = m.size + 1 :=
  m.inductionOn (fun _ h h' => DHashMap.size_alter_eq_add_one h h') h h'

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∈ m) (h' : (f (m.get? k)).isNone) :
    (m.alter k f).size = m.size - 1 :=
  m.inductionOn (fun _ h h' => DHashMap.size_alter_eq_sub_one h h') h h'

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∉ m) (h' : (f (m.get? k)).isNone) : (m.alter k f).size = m.size :=
  m.inductionOn (fun _ h h' => DHashMap.size_alter_eq_self_of_not_mem h h') h h'

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∈ m) (h' : (f (m.get? k)).isSome) : (m.alter k f).size = m.size :=
  m.inductionOn (fun _ h h' => DHashMap.size_alter_eq_self_of_mem h h') h h'

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_alter_le_size

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    m.size - 1 ≤ (m.alter k f).size :=
  m.inductionOn fun _ => DHashMap.size_le_size_alter

theorem get?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).get? k' =
      if h : k == k' then
        (cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (m.get? k)))
      else
        m.get? k' :=
  m.inductionOn fun _ => DHashMap.get?_alter

@[simp]
theorem get?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).get? k = f (m.get? k) :=
  m.inductionOn fun _ => DHashMap.get?_alter_self

theorem get_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    {h : k' ∈ m.alter k f} :
    (m.alter k f).get k' h =
      if heq : k == k' then
        haveI h' : (f (m.get? k)).isSome := mem_alter_of_beq heq |>.mp h
        cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get <| h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.get k' h' :=
  m.inductionOn (fun _ _ => DHashMap.get_alter) h

@[simp]
theorem get_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    {h : k ∈ m.alter k f} :
    haveI h' : (f (m.get? k)).isSome := mem_alter_self.mp h
    (m.alter k f).get k h = (f (m.get? k)).get h' :=
  m.inductionOn (fun _ _ => DHashMap.get_alter_self) h

theorem get!_alter [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')]
    {f : Option (β k) → Option (β k)} : (m.alter k f).get! k' =
      if heq : k == k' then
        (f (m.get? k)).map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' :=
  m.inductionOn fun _ => DHashMap.get!_alter

@[simp]
theorem get!_alter_self [LawfulBEq α] {k : α} [Inhabited (β k)] {f : Option (β k) → Option (β k)} :
    (m.alter k f).get! k = (f (m.get? k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_alter_self

theorem getD_alter [LawfulBEq α] {k k' : α} {fallback : β k'} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k' fallback =
      if heq : k == k' then
        f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback :=
  m.inductionOn fun _ => DHashMap.getD_alter

@[simp]
theorem getD_alter_self [LawfulBEq α] {k : α} {fallback : β k} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k fallback = (f (m.get? k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_alter_self

theorem getKey?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k' =
      if k == k' then
        if (f (m.get? k)).isSome then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.getKey?_alter

theorem getKey?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k = if (f (m.get? k)).isSome then some k else none :=
  m.inductionOn fun _ => DHashMap.getKey?_alter_self

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.getKey!_alter

theorem getKey!_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k = if (f (m.get? k)).isSome then k else default :=
  m.inductionOn fun _ => DHashMap.getKey!_alter_self

theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    {h : k' ∈ m.alter k f} :
    (m.alter k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  m.inductionOn (fun _ _ => DHashMap.getKey_alter) h

@[simp]
theorem getKey_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)}
    {h : k ∈ m.alter k f} : (m.alter k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.getKey_alter_self) h

theorem getKeyD_alter [LawfulBEq α] {k k' fallback : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k' fallback =
      if k == k' then
        if (f (m.get? k)).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_alter

@[simp]
theorem getKeyD_alter_self [LawfulBEq α] [Inhabited α] {k : α} {fallback : α}
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k fallback = if (f (m.get? k)).isSome then k else fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_alter_self

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

theorem alter_eq_empty_iff_erase_eq_empty {k : α} {f : Option β → Option β} :
    alter m k f = ∅ ↔ m.erase k = ∅ ∧ f (get? m k) = none := by
  rcases m with ⟨m⟩
  simp only [← isEmpty_iff]
  dsimp only [isEmpty, alter, Quotient.lift, Quotient.mk', Quotient.mk]
  simp only [DHashMap.Const.isEmpty_alter_eq_isEmpty_erase, Bool.and_eq_true,
    Option.isNone_iff_eq_none]
  rfl

@[simp]
theorem alter_eq_empty_iff {k : α} {f : Option β → Option β} :
    alter m k f = ∅ ↔ (m = ∅ ∨ (m.size = 1 ∧ k ∈ m)) ∧ f (get? m k) = none := by
  simp only [alter_eq_empty_iff_erase_eq_empty, erase_eq_empty_iff]

theorem contains_alter {k k': α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
      if k == k' then (f (Const.get? m k)).isSome else m.contains k' :=
  m.inductionOn fun _ => DHashMap.Const.contains_alter

theorem mem_alter {k k': α} {f : Option β → Option β} :
    k' ∈ Const.alter m k f ↔ if k == k' then (f (Const.get? m k)).isSome = true else k' ∈ m :=
  m.inductionOn fun _ => DHashMap.Const.mem_alter

theorem mem_alter_of_beq {k k': α} {f : Option β → Option β}
    (h : k == k') : k' ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome :=
  m.inductionOn (fun _ h => DHashMap.Const.mem_alter_of_beq h) h

@[simp]
theorem contains_alter_self {k : α} {f : Option β → Option β} :
    (Const.alter m k f).contains k = (f (Const.get? m k)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self {k : α} {f : Option β → Option β} :
    k ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.mem_alter_self

theorem contains_alter_of_beq_eq_false {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) :
    (Const.alter m k f).contains k' = m.contains k' :=
  m.inductionOn (fun _ h => DHashMap.Const.contains_alter_of_beq_eq_false h) h

theorem mem_alter_of_beq_eq_false {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) : k' ∈ Const.alter m k f ↔ k' ∈ m :=
  m.inductionOn (fun _ h => DHashMap.Const.mem_alter_of_beq_eq_false h) h

theorem size_alter {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size =
      if k ∈ m ∧ (f (Const.get? m k)).isNone then
        m.size - 1
      else if k ∉ m ∧ (f (Const.get? m k)).isSome then
        m.size + 1
      else
        m.size :=
  m.inductionOn fun _ => DHashMap.Const.size_alter

theorem size_alter_eq_add_one {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).size = m.size + 1 :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_add_one h h') h h'

theorem size_alter_eq_sub_one {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).size = m.size - 1 :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_sub_one h h') h h'

theorem size_alter_eq_self_of_not_mem {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isNone) : (Const.alter m k f).size = m.size :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_self_of_not_mem h h') h h'

theorem size_alter_eq_self_of_mem {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isSome) : (Const.alter m k f).size = m.size :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_self_of_mem h h') h h'

theorem size_alter_le_size {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.Const.size_alter_le_size

theorem size_le_size_alter {k : α} {f : Option β → Option β} :
    m.size - 1 ≤ (Const.alter m k f).size :=
  m.inductionOn fun _ => DHashMap.Const.size_le_size_alter

theorem get?_alter {k k' : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k)
      else
        Const.get? m k' :=
  m.inductionOn fun _ => DHashMap.Const.get?_alter

@[simp]
theorem get?_alter_self {k : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k = f (Const.get? m k) :=
  m.inductionOn fun _ => DHashMap.Const.get?_alter_self

theorem get_alter {k k' : α} {f : Option β → Option β}
    {h : k' ∈ Const.alter m k f} :
    Const.get (Const.alter m k f) k' h =
      if heq : k == k' then
        haveI h' : (f (Const.get? m k)).isSome := mem_alter_of_beq heq |>.mp h
        f (Const.get? m k) |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        Const.get m k' h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_alter) h

@[simp]
theorem get_alter_self {k : α} {f : Option β → Option β}
    {h : k ∈ Const.alter m k f} :
    haveI h' : (f (Const.get? m k)).isSome := mem_alter_self.mp h
    Const.get (Const.alter m k f) k h = (f (Const.get? m k)).get h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_alter_self) h

theorem get!_alter {k k' : α} [Inhabited β]
    {f : Option β → Option β} : Const.get! (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k) |>.get!
      else
        Const.get! m k' :=
  m.inductionOn fun _ => DHashMap.Const.get!_alter

@[simp]
theorem get!_alter_self {k : α} [Inhabited β]
    {f : Option β → Option β} : Const.get! (Const.alter m k f) k = (f (Const.get? m k)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_alter_self

theorem getD_alter {k k' : α} {fallback : β}
    {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k' fallback =
      if k == k' then
        f (Const.get? m k) |>.getD fallback
      else
        Const.getD m k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_alter

@[simp]
theorem getD_alter_self {k : α} {fallback : β}
    {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k fallback = (f (Const.get? m k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_alter_self

theorem getKey?_alter {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_alter

theorem getKey?_alter_self {k : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k = if (f (Const.get? m k)).isSome then some k else none :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_alter_self

theorem getKey!_alter [Inhabited α] {k k' : α}
    {f : Option β → Option β} : (Const.alter m k f).getKey! k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_alter

theorem getKey!_alter_self [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (Const.alter m k f).getKey! k = if (f (Const.get? m k)).isSome then k else default :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_alter_self

theorem getKey_alter [Inhabited α] {k k' : α}
    {f : Option β → Option β} {h : k' ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_alter) h

@[simp]
theorem getKey_alter_self [Inhabited α] {k : α}
    {f : Option β → Option β} {h : k ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_alter_self) h

theorem getKeyD_alter {k k' fallback : α} {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_alter

theorem getKeyD_alter_self [Inhabited α] {k fallback : α}
    {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k fallback =
      if (f (Const.get? m k)).isSome then k else fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_alter_self

end Const

end Alter

section Modify

@[simp]
theorem modify_eq_empty_iff [LawfulBEq α] {k : α} {f : β k → β k} :
    m.modify k f = ∅ ↔ m = ∅ := by
  simp only [← isEmpty_iff, Bool.coe_iff_coe]
  exact m.inductionOn fun _ => DHashMap.isEmpty_modify

@[simp]
theorem contains_modify [LawfulBEq α] {k k': α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' :=
  m.inductionOn fun _ => DHashMap.contains_modify

@[simp]
theorem mem_modify [LawfulBEq α] {k k': α} {f : β k → β k} : k' ∈ m.modify k f ↔ k' ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_modify

@[simp]
theorem size_modify [LawfulBEq α] {k : α} {f : β k → β k} : (m.modify k f).size = m.size :=
  m.inductionOn fun _ => DHashMap.size_modify

theorem get?_modify [LawfulBEq α] {k k' : α} {f : β k → β k} :
    (m.modify k f).get? k' = if h : k == k' then
      (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f))
    else
      m.get? k' :=
  m.inductionOn fun _ => DHashMap.get?_modify

@[simp]
theorem get?_modify_self [LawfulBEq α] {k : α} {f : β k → β k} :
    (m.modify k f).get? k = (m.get? k).map f :=
  m.inductionOn fun _ => DHashMap.get?_modify_self

theorem get_modify [LawfulBEq α] {k k' : α} {f : β k → β k}
    (h : k' ∈ m.modify k f) :
    (m.modify k f).get k' h =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        cast (congrArg β (eq_of_beq heq)) <| f (m.get k h')
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.get k' h' :=
  m.inductionOn (fun _ h => DHashMap.get_modify h) h

@[simp]
theorem get_modify_self [LawfulBEq α] {k : α} {f : β k → β k} {h : k ∈ m.modify k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    (m.modify k f).get k h = f (m.get k h') :=
  m.inductionOn (fun _ _ => DHashMap.get_modify_self) h

theorem get!_modify [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (m.modify k f).get! k' =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' :=
  m.inductionOn fun _ => DHashMap.get!_modify

@[simp]
theorem get!_modify_self [LawfulBEq α] {k : α} [Inhabited (β k)] {f : β k → β k} :
    (m.modify k f).get! k = ((m.get? k).map f).get! :=
  m.inductionOn fun _ => DHashMap.get!_modify_self

theorem getD_modify [LawfulBEq α] {k k' : α} {fallback : β k'} {f : β k → β k} :
    (m.modify k f).getD k' fallback =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback :=
  m.inductionOn fun _ => DHashMap.getD_modify

@[simp]
theorem getD_modify_self [LawfulBEq α] {k : α} {fallback : β k} {f : β k → β k} :
    (m.modify k f).getD k fallback = ((m.get? k).map f).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_modify_self

theorem getKey?_modify [LawfulBEq α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.getKey?_modify

theorem getKey?_modify_self [LawfulBEq α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey? k = if k ∈ m then some k else none :=
  m.inductionOn fun _ => DHashMap.getKey?_modify_self

theorem getKey!_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.getKey!_modify

theorem getKey!_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey! k = if k ∈ m then k else default :=
  m.inductionOn fun _ => DHashMap.getKey!_modify_self

theorem getKey_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k}
    {h : k' ∈ m.modify k f} :
    (m.modify k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  m.inductionOn (fun _ _ => DHashMap.getKey_modify) h

@[simp]
theorem getKey_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k}
    {h : k ∈ m.modify k f} : (m.modify k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.getKey_modify_self) h

theorem getKeyD_modify [LawfulBEq α] {k k' fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_modify

theorem getKeyD_modify_self [LawfulBEq α] [Inhabited α] {k fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_modify_self

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp]
theorem modify_eq_empty_iff {k : α} {f : β → β} :
    Const.modify m k f = ∅ ↔ m = ∅ := by
  simp only [← isEmpty_iff, Bool.coe_iff_coe]
  exact m.inductionOn fun _ => DHashMap.Const.isEmpty_modify

@[simp]
theorem contains_modify {k k': α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' :=
  m.inductionOn fun _ => DHashMap.Const.contains_modify

@[simp]
theorem mem_modify {k k': α} {f : β → β} :
    k' ∈ Const.modify m k f ↔ k' ∈ m :=
  m.inductionOn fun _ => DHashMap.Const.mem_modify

@[simp]
theorem size_modify {k : α} {f : β → β} :
    (Const.modify m k f).size = m.size :=
  m.inductionOn fun _ => DHashMap.Const.size_modify

theorem get?_modify {k k' : α} {f : β → β} :
    Const.get? (Const.modify m k f) k' = if k == k' then
      Const.get? m k |>.map f
    else
      Const.get? m k' :=
  m.inductionOn fun _ => DHashMap.Const.get?_modify

@[simp]
theorem get?_modify_self {k : α} {f : β → β} :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f :=
  m.inductionOn fun _ => DHashMap.Const.get?_modify_self

theorem get_modify {k k' : α} {f : β → β}
    {h : k' ∈ Const.modify m k f} :
    Const.get (Const.modify m k f) k' h =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        f (Const.get m k h')
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        Const.get m k' h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_modify) h

@[simp]
theorem get_modify_self {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    Const.get (Const.modify m k f) k h = f (Const.get m k h') :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_modify_self) h

theorem get!_modify {k k' : α} [Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f |>.get!
      else
        Const.get! m k' :=
  m.inductionOn fun _ => DHashMap.Const.get!_modify

@[simp]
theorem get!_modify_self {k : α} [Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_modify_self

theorem getD_modify {k k' : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k' fallback =
      if k == k' then
        Const.get? m k |>.map f |>.getD fallback
      else
        Const.getD m k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_modify

@[simp]
theorem getD_modify_self {k : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k fallback = ((Const.get? m k).map f).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_modify_self

theorem getKey?_modify {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_modify

theorem getKey?_modify_self {k : α} {f : β → β} :
    (Const.modify m k f).getKey? k = if k ∈ m then some k else none :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_modify_self

theorem getKey!_modify [Inhabited α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_modify

theorem getKey!_modify_self [Inhabited α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey! k = if k ∈ m then k else default :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_modify_self

theorem getKey_modify [Inhabited α] {k k' : α} {f : β → β}
    {h : k' ∈ Const.modify m k f} :
    (Const.modify m k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_modify) h

@[simp]
theorem getKey_modify_self [Inhabited α] {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} : (Const.modify m k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_modify_self) h

theorem getKeyD_modify {k k' fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_modify

theorem getKeyD_modify_self [Inhabited α] {k fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_modify_self

end Const

end Modify

section Equiv

variable {m₁ m₂ m₃ : Std.ExtDHashMap α β}

theorem ext_get? [LawfulBEq α] (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => Quotient.sound (.of_forall_get?_eq h)) h

namespace Const

variable {β : Type v} {m₁ m₂ : ExtDHashMap α fun _ => β}

theorem ext_getKey?_get? (hk : ∀ k, m₁.getKey? k = m₂.getKey? k)
    (hv : ∀ k, Const.get? m₁ k = Const.get? m₂ k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ hk hv => Quotient.sound
    (.of_forall_getKey?_eq_of_forall_constGet?_eq hk hv)) hk hv

theorem ext_getKey?_unit {m₁ m₂ : ExtDHashMap α fun _ => Unit}
    (h : ∀ k, m₁.getKey? k = m₂.getKey? k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => Quotient.sound (.of_forall_getKey?_unit_eq h)) h

theorem ext_contains_unit [LawfulBEq α] {m₁ m₂ : ExtDHashMap α fun _ => Unit}
    (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => Quotient.sound (.of_forall_contains_unit_eq h)) h

theorem ext_mem_unit [LawfulBEq α] {m₁ m₂ : ExtDHashMap α fun _ => Unit}
    (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => Quotient.sound (.of_forall_mem_unit_iff h)) h

end Const

end Equiv

section filterMap

variable {γ : α → Type w}

theorem filterMap_eq_empty_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    m.filterMap f = ∅ ↔ ∀ k h, f k (m.get k h) = none :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_filterMap_iff

theorem contains_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).contains k = (m.get? k).any (f k · |>.isSome) :=
  m.inductionOn fun _ => DHashMap.contains_filterMap

theorem mem_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f k (m.get k h)).isSome :=
  m.inductionOn fun _ => DHashMap.mem_filterMap

theorem contains_of_contains_filterMap
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).contains k = true → m.contains k = true :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_filterMap

theorem mem_of_mem_filterMap
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ m.filterMap f → k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_filterMap

theorem size_filterMap_le_size
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_filterMap_le_size

theorem size_filterMap_eq_size_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).size = m.size ↔ ∀ (a : α) (h : a ∈ m), (f a (m.get a h)).isSome :=
  m.inductionOn fun _ => DHashMap.size_filterMap_eq_size_iff

@[simp]
theorem get?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).get? k = (m.get? k).bind (f k) :=
  m.inductionOn fun _ => DHashMap.get?_filterMap

theorem isSome_apply_of_mem_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    ∀ (h' : k ∈ m.filterMap f),
      (f k (m.get k (mem_of_mem_filterMap h'))).isSome :=
  m.inductionOn fun _ => DHashMap.isSome_apply_of_mem_filterMap

@[simp]
theorem get_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (m.filterMap f).get k h' =
      (f k (m.get k (mem_of_mem_filterMap h'))).get
        (isSome_apply_of_mem_filterMap h') :=
  m.inductionOn (fun _ _ => DHashMap.get_filterMap) h'

theorem get!_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} [Inhabited (γ k)] :
    (m.filterMap f).get! k = ((m.get? k).bind (f k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_filterMap

theorem getD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {fallback : γ k} :
    (m.filterMap f).getD k fallback = ((m.get? k).bind (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_filterMap

theorem getKey?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome) :=
  m.inductionOn fun _ => DHashMap.getKey?_filterMap

@[simp]
theorem getKey_filterMap
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (m.filterMap f).getKey k h' = m.getKey k (mem_of_mem_filterMap h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_filterMap) h'

theorem getKey!_filterMap [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_filterMap

theorem getKeyD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_filterMap

namespace Const

variable {β : Type v} {γ : Type w} {m : ExtDHashMap α (fun _ => β)}

theorem filterMap_eq_empty_iff {f : α → β → Option γ} :
    m.filterMap f = ∅ ↔ ∀ k h, f (m.getKey k h) (get m k h) = none :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.Const.isEmpty_filterMap_iff

theorem mem_filterMap
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f (m.getKey k h) (Const.get m k h)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.mem_filterMap

theorem size_filterMap_eq_size_iff
    {f : α → β → Option γ} :
    (m.filterMap f).size = m.size ↔ ∀ k h, (f (m.getKey k h) (Const.get m k h)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.size_filterMap_eq_size_iff

theorem get?_filterMap
    {f : α → β → Option γ} {k : α} :
    Const.get? (m.filterMap f) k = (Const.get? m k).pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  m.inductionOn fun _ => DHashMap.Const.get?_filterMap

theorem get?_filterMap_of_getKey?_eq_some
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get? (m.filterMap f) k = (Const.get? m k).bind (f k') :=
  m.inductionOn (fun _ h => DHashMap.Const.get?_filterMap_of_getKey?_eq_some h) h

theorem isSome_apply_of_mem_filterMap
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ m.filterMap f),
      (f (m.getKey k (mem_of_mem_filterMap h))
        (Const.get m k (mem_of_mem_filterMap h))).isSome :=
  m.inductionOn fun _ => DHashMap.Const.isSome_apply_of_mem_filterMap

@[simp]
theorem get_filterMap
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (m.filterMap f) k h =
      (f (m.getKey k (mem_of_mem_filterMap h))
        (Const.get m k (mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_filterMap) h

theorem get!_filterMap [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (m.filterMap f) k =
      ((Const.get? m k).pbind (fun x h' =>
        f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_filterMap

theorem get!_filterMap_of_getKey?_eq_some [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get! (m.filterMap f) k = ((Const.get? m k).bind (f k')).get! :=
  m.inductionOn (fun _ h => DHashMap.Const.get!_filterMap_of_getKey?_eq_some h) h

theorem getD_filterMap
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (m.filterMap f) k fallback =
      ((Const.get? m k).pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_filterMap

theorem getD_filterMap_of_getKey?_eq_some
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    Const.getD (m.filterMap f) k fallback = ((Const.get? m k).bind (f k')).getD fallback :=
  m.inductionOn (fun _ h => DHashMap.Const.getD_filterMap_of_getKey?_eq_some h) h

theorem getKey?_filterMap
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome) :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_filterMap

theorem getKey!_filterMap [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_filterMap

theorem getKeyD_filterMap
    {f : α → β → Option γ} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_filterMap

end Const

end filterMap

section filter

theorem filterMap_eq_filter {f : (a : α) → β a → Bool} :
    m.filterMap (fun k => Option.guard (fun v => f k v)) = m.filter f :=
  m.inductionOn fun _ => Quotient.sound DHashMap.filterMap_equiv_filter

@[simp]
theorem filter_eq_empty_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} :
    m.filter f = ∅ ↔ ∀ k h, f k (m.get k h) = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_filter_iff

theorem filter_key_eq_empty_iff {f : α → Bool} :
    m.filter (fun a _ => f a) = ∅ ↔ ∀ k h, f (m.getKey k h) = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_filter_key_iff

theorem contains_filter [LawfulBEq α] {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).contains k = (m.get? k).any (f k) :=
  m.inductionOn fun _ => DHashMap.contains_filter

theorem mem_filter [LawfulBEq α] {f : (a : α) → β a → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ h, f k (m.get k h) :=
  m.inductionOn fun _ => DHashMap.mem_filter

theorem mem_filter_key {f : α → Bool} {k : α} :
    k ∈ m.filter (fun a _ => f a) ↔ ∃ h, f (m.getKey k h) :=
  m.inductionOn fun _ => DHashMap.mem_filter_key

theorem contains_of_contains_filter {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).contains k = true → m.contains k = true :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_filter

theorem mem_of_mem_filter {f : (a : α) → β a → Bool} {k : α} :
    k ∈ (m.filter f) → k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_filter

theorem size_filter_le_size {f : (a : α) → β a → Bool} :
    (m.filter f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_filter_le_size

theorem size_filter_eq_size_iff [LawfulBEq α] {f : (a : α) → β a → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f k (m.get k h) :=
  m.inductionOn fun _ => DHashMap.size_filter_eq_size_iff

theorem filter_eq_self_iff [LawfulBEq α] {f : (a : α) → β a → Bool} :
    m.filter f = m ↔ ∀ k h, f k (m.get k h) :=
  m.inductionOn fun _ => Iff.trans ⟨Quotient.exact, Quotient.sound⟩ DHashMap.filter_equiv_self_iff

theorem filter_key_equiv_self_iff {f : (a : α) → Bool} :
    m.filter (fun k _ => f k) = m ↔ ∀ k h, f (m.getKey k h) :=
  m.inductionOn fun _ => Iff.trans ⟨Quotient.exact, Quotient.sound⟩ DHashMap.filter_key_equiv_self_iff

theorem size_filter_key_eq_size_iff {f : α → Bool} :
    (m.filter fun k _ => f k).size = m.size ↔ ∀ k h, f (m.getKey k h) :=
  m.inductionOn fun _ => DHashMap.size_filter_key_eq_size_iff

@[simp]
theorem get?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).get? k = (m.get? k).filter (f k) :=
  m.inductionOn fun _ => DHashMap.get?_filter

@[simp]
theorem get_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (m.filter f).get k h' = m.get k (mem_of_mem_filter h') :=
  m.inductionOn (fun _ _ => DHashMap.get_filter) h'

theorem get!_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} [Inhabited (β k)] :
    (m.filter f).get! k = ((m.get? k).filter (f k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_filter

theorem getD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {fallback : β k} :
    (m.filter f).getD k fallback = ((m.get? k).filter (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_filter

theorem getKey?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h'))) :=
  m.inductionOn fun _ => DHashMap.getKey?_filter

theorem getKey?_filter_key
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f :=
  m.inductionOn fun _ => DHashMap.getKey?_filter_key

@[simp]
theorem getKey_filter
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (m.filter f).getKey k h' = m.getKey k (mem_of_mem_filter h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_filter) h'

theorem getKey!_filter [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h')))).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_filter

theorem getKey!_filter_key [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_filter_key

theorem getKeyD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h')))).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_filter

theorem getKeyD_filter_key
    {f : α → Bool} {k fallback : α} :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_filter_key

namespace Const

variable {β : Type v} {γ : Type w} {m : ExtDHashMap α (fun _ => β)}

theorem filter_eq_empty_iff {f : α → β → Bool} :
    m.filter f = ∅ ↔ ∀ k h, f (m.getKey k h) (Const.get m k h) = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.Const.isEmpty_filter_iff

theorem mem_filter
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ (h' : k ∈ m),
      f (m.getKey k h') (Const.get m k h') :=
  m.inductionOn fun _ => DHashMap.Const.mem_filter

theorem size_filter_le_size
    {f : α → β → Bool} :
    (m.filter f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.Const.size_filter_le_size

theorem size_filter_eq_size_iff
    {f : α → β → Bool} :
    (m.filter f).size = m.size ↔ ∀ (a : α) (h : a ∈ m),
      f (m.getKey a h) (Const.get m a h) :=
  m.inductionOn fun _ => DHashMap.Const.size_filter_eq_size_iff

theorem filter_eq_self_iff {f : α → β → Bool} :
    m.filter f = m ↔ ∀ k h, f (m.getKey k h) (Const.get m k h) :=
  m.inductionOn fun _ => Iff.trans ⟨Quotient.exact, Quotient.sound⟩ DHashMap.Const.filter_equiv_self_iff

theorem get?_filter
    {f : α → β → Bool} {k : α} :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  m.inductionOn fun _ => DHashMap.Const.get?_filter

theorem get?_filter_of_getKey?_eq_some
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      Const.get? (m.filter f) k = (Const.get? m k).filter (fun x => f k' x) :=
  m.inductionOn fun _ => DHashMap.Const.get?_filter_of_getKey?_eq_some

@[simp]
theorem get_filter
    {f : α → β → Bool} {k : α} {h'} :
    Const.get (m.filter f) k h' = Const.get m k (mem_of_mem_filter h') :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_filter) h'

theorem get!_filter [Inhabited β]
    {f : α → β → Bool} {k : α} :
    Const.get! (m.filter f) k =
      ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_filter

theorem get!_filter_of_getKey?_eq_some [Inhabited β]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      Const.get! (m.filter f) k = ((Const.get? m k).filter (fun x => f k' x)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_filter_of_getKey?_eq_some

theorem getD_filter
    {f : α → β → Bool} {k : α} {fallback : β} :
    Const.getD (m.filter f) k fallback = ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_filter

theorem getD_filter_of_getKey?_eq_some
    {f : α → β → Bool} {k k' : α} {fallback : β} :
    m.getKey? k = some k' →
      Const.getD (m.filter f) k fallback =
        ((Const.get? m k).filter (fun x => f k' x)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_filter_of_getKey?_eq_some

theorem getKey?_filter
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h')))) :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_filter

theorem getKey!_filter [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))))).get! :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_filter

theorem getKeyD_filter
    {f : α → β → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))))).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_filter

end Const

end filter

section map

variable {γ : α → Type w} {δ : α → Type w'}

@[simp]
theorem map_id_fun : m.map (fun _ v => v) = m :=
  m.inductionOn fun _ => Quotient.sound DHashMap.map_id_equiv

@[simp]
theorem map_map {f : (a : α) → β a → γ a} {g : (a : α) → γ a → δ a} :
    (m.map f).map g = m.map fun k v => g k (f k v) :=
  m.inductionOn fun _ => Quotient.sound DHashMap.map_map_equiv

theorem filterMap_eq_map {f : (a : α) → β a → γ a} :
    (m.filterMap (fun k v => some (f k v))) = m.map f :=
  m.inductionOn fun _ => Quotient.sound DHashMap.filterMap_equiv_map

@[simp]
theorem map_eq_empty_iff {f : (a : α) → β a → γ a} :
    m.map f = ∅ ↔ m = ∅ := by
  simp only [← isEmpty_iff, Bool.coe_iff_coe]
  exact m.inductionOn fun _ => DHashMap.isEmpty_map

theorem contains_map
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).contains k = m.contains k :=
  m.inductionOn fun _ => DHashMap.contains_map

theorem contains_of_contains_map
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).contains k = true → m.contains k = true :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_map

@[simp]
theorem mem_map
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ m.map f ↔ k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_map

theorem mem_of_mem_map
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ m.map f → k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_map

@[simp]
theorem size_map
    {f : (a : α) → β a → γ a} :
    (m.map f).size = m.size :=
  m.inductionOn fun _ => DHashMap.size_map

@[simp]
theorem get?_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).get? k = (m.get? k).map (f k) :=
  m.inductionOn fun _ => DHashMap.get?_map

@[simp]
theorem get_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (m.map f).get k h' = f k (m.get k (mem_of_mem_map h')) :=
  m.inductionOn (fun _ _ => DHashMap.get_map) h'

theorem get!_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} [Inhabited (γ k)] :
    (m.map f).get! k = ((m.get? k).map (f k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_map

theorem getD_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {fallback : γ k} :
    (m.map f).getD k fallback = ((m.get? k).map (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_map

@[simp]
theorem getKey?_map
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).getKey? k = m.getKey? k :=
  m.inductionOn fun _ => DHashMap.getKey?_map

@[simp]
theorem getKey_map
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (m.map f).getKey k h' = m.getKey k (mem_of_mem_map h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_map) h'

@[simp]
theorem getKey!_map [Inhabited α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).getKey! k = m.getKey! k :=
  m.inductionOn fun _ => DHashMap.getKey!_map

@[simp]
theorem getKeyD_map
    {f : (a : α) → β a → γ a} {k fallback : α} :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_map

namespace Const

variable {β : Type v} {γ : Type w} {m : ExtDHashMap α fun _ => β}

theorem get?_map
    {f : α → β → γ} {k : α} :
    Const.get? (m.map f) k = (Const.get? m k).pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h')) :=
  m.inductionOn fun _ => DHashMap.Const.get?_map

theorem get?_map_of_getKey?_eq_some
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get? (m.map f) k = (Const.get? m k).map (f k') :=
  m.inductionOn (fun _ h => DHashMap.Const.get?_map_of_getKey?_eq_some h) h

@[simp]
theorem get_map
    {f : α → β → γ} {k : α} {h'} :
    Const.get (m.map f) k h' =
      f (m.getKey k (mem_of_mem_map h')) (Const.get m k (mem_of_mem_map h')) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_map) h'

theorem get!_map [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (m.map f) k =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_mem h'))).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_map

theorem get!_map_of_getKey?_eq_some [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get! (m.map f) k = ((Const.get? m k).map (f k')).get! :=
  m.inductionOn (fun _ h => DHashMap.Const.get!_map_of_getKey?_eq_some h) h

theorem getD_map
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (m.map f) k fallback =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_map

theorem getD_map_of_getKey?_eq_some [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k')).getD fallback :=
  m.inductionOn (fun _ h => DHashMap.Const.getD_map_of_getKey?_eq_some h) h

end Const

end map

end Std.ExtDHashMap
