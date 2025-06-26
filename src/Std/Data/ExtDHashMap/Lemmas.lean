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

attribute [local instance] Std.DHashMap.isSetoid

universe u v w w'

variable {α : Type u} {_ : BEq α} {_ : Hashable α}
variable {β : α → Type v} {γ : α → Type w}

namespace Std.ExtDHashMap

variable {m : ExtDHashMap α β}

@[simp, grind =]
theorem isEmpty_iff [EquivBEq α] [LawfulHashable α] : m.isEmpty ↔ m = ∅ := by
  cases m with | mk m
  refine m.equiv_empty_iff_isEmpty.symm.trans ?_
  exact ⟨fun h => sound h, exact⟩

@[simp]
theorem isEmpty_eq_false_iff [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ¬m = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[simp]
theorem empty_eq : ∅ = m ↔ m = ∅ := eq_comm

@[simp, grind =]
theorem emptyWithCapacity_eq [EquivBEq α] [LawfulHashable α] {c} : (emptyWithCapacity c : ExtDHashMap α β) = ∅ :=
  isEmpty_iff.mp DHashMap.isEmpty_emptyWithCapacity

@[simp]
theorem not_insert_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    ¬m.insert k v = ∅ :=
  m.inductionOn fun _ => isEmpty_eq_false_iff.mp DHashMap.isEmpty_insert

theorem mem_iff_contains [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ m.contains a :=
  Iff.rfl

@[simp, grind _=_]
theorem contains_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a ↔ a ∈ m :=
  Iff.rfl

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : m.contains a = m.contains b :=
  m.inductionOn fun _ => DHashMap.contains_congr hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_congr hab

@[simp, grind =]
theorem contains_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : DHashMap α β).contains a = false :=
  DHashMap.contains_empty

@[simp]
theorem not_mem_empty [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ (∅ : DHashMap α β) :=
  DHashMap.not_mem_empty

theorem eq_empty_iff_forall_contains [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ ∀ a, m.contains a = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ ∀ a, ¬a ∈ m :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_iff_forall_not_mem

@[simp]
theorem insert_eq_insert [EquivBEq α] [LawfulHashable α] {p : (a : α) × β a} :
    Insert.insert p m = m.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert [EquivBEq α] [LawfulHashable α] {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : DHashMap α β).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  m.inductionOn fun _ => DHashMap.contains_insert

@[simp, grind =]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} : a ∈ m.insert k v ↔ k == a ∨ a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_insert

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} : a ∈ m.insert k v → (k == a) = false → a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_insert

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : (m.insert k v).contains k := by simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : k ∈ m.insert k v := by simp

@[simp, grind =]
theorem size_empty [EquivBEq α] [LawfulHashable α] : (∅ : ExtDHashMap α β).size = 0 := rfl

theorem eq_empty_iff_size_eq_zero [EquivBEq α] [LawfulHashable α] : m = ∅ ↔ m.size = 0 :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ =>
    (Bool.eq_iff_iff.mp DHashMap.isEmpty_eq_size_eq_zero).trans beq_iff_eq

@[grind =] theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : m.size ≤ (m.insert k v).size :=
  m.inductionOn fun _ => DHashMap.size_le_size_insert

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : (m.insert k v).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insert_le

@[simp, grind =]
theorem erase_empty [EquivBEq α] [LawfulHashable α] {k : α} : (∅ : ExtDHashMap α β).erase k = ∅ :=
  congrArg mk DHashMap.erase_empty

@[simp]
theorem erase_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} :
    m.erase k = ∅ ↔ m = ∅ ∨ m.size = 1 ∧ k ∈ m := by
  cases m with | mk m
  simp only [← isEmpty_iff, ← decide_eq_decide, Bool.decide_eq_true, Bool.decide_or,
    Bool.decide_and, mem_iff_contains]
  exact DHashMap.isEmpty_erase

@[simp, grind =]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  m.inductionOn fun _ => DHashMap.contains_erase

@[simp, grind =]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [← contains_iff_mem, contains_erase]

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m := by
  simp

@[grind =] theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  m.inductionOn fun _ => DHashMap.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  m.inductionOn fun _ => DHashMap.size_le_size_erase

@[simp, grind =]
theorem containsThenInsert_fst [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : (m.containsThenInsert k v).1 = m.contains k :=
  m.inductionOn fun _ => DHashMap.containsThenInsert_fst

@[simp, grind =]
theorem containsThenInsert_snd [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : (m.containsThenInsert k v).2 = m.insert k v :=
  m.inductionOn fun _ => congrArg mk DHashMap.containsThenInsert_snd

@[simp, grind =]
theorem containsThenInsertIfNew_fst [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  m.inductionOn fun _ => DHashMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsertIfNew_snd [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  m.inductionOn fun _ => congrArg mk DHashMap.containsThenInsertIfNew_snd

@[simp, grind =]
theorem get?_empty [LawfulBEq α] {a : α} : (∅ : ExtDHashMap α β).get? a = none :=
  DHashMap.get?_empty

@[grind =] theorem get?_insert [LawfulBEq α] {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a :=
  m.inductionOn fun _ => DHashMap.get?_insert

@[simp]
theorem get?_insert_self [LawfulBEq α] {k : α} {v : β k} : (m.insert k v).get? k = some v :=
  m.inductionOn fun _ => DHashMap.get?_insert_self

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome :=
  m.inductionOn fun _ => DHashMap.contains_eq_isSome_get?

@[simp]
theorem isSome_get?_eq_contains [LawfulBEq α] {a : α} : (m.get? a).isSome = m.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [LawfulBEq α] {a : α} : a ∈ m ↔ (m.get? a).isSome :=
  m.inductionOn fun _ => DHashMap.mem_iff_isSome_get?

@[simp]
theorem isSome_get?_iff_mem [LawfulBEq α] {a : α} : (m.get? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_get?.symm

theorem get?_eq_none_of_contains_eq_false [LawfulBEq α] {a : α} :
    m.contains a = false → m.get? a = none :=
  m.inductionOn fun _ => DHashMap.get?_eq_none_of_contains_eq_false

theorem get?_eq_none [LawfulBEq α] {a : α} : ¬a ∈ m → m.get? a = none := by
  simpa [← contains_iff_mem] using get?_eq_none_of_contains_eq_false

@[grind =] theorem get?_erase [LawfulBEq α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  m.inductionOn fun _ => DHashMap.get?_erase

@[simp]
theorem get?_erase_self [LawfulBEq α] {k : α} : (m.erase k).get? k = none :=
  m.inductionOn fun _ => DHashMap.get?_erase_self

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp, grind =]
theorem get?_empty [EquivBEq α] [LawfulHashable α] {a : α} : get? (∅ : ExtDHashMap α (fun _ => β)) a = none :=
  DHashMap.Const.get?_empty

@[grind =] theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a :=
  m.inductionOn fun _ => DHashMap.Const.get?_insert

@[simp]
theorem get?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get? (m.insert k v) k = some v :=
  m.inductionOn fun _ => DHashMap.Const.get?_insert_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (get? m a).isSome :=
  m.inductionOn fun _ => DHashMap.Const.contains_eq_isSome_get?

@[simp]
theorem isSome_get?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (get? m a).isSome = m.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ (get? m a).isSome :=
  m.inductionOn fun _ => DHashMap.Const.mem_iff_isSome_get?

@[simp]
theorem isSome_get?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (get? m a).isSome ↔ a ∈ m :=
  mem_iff_isSome_get?.symm

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → get? m a = none :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_none_of_contains_eq_false

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → get? m a = none := by
  simpa [← contains_iff_mem] using get?_eq_none_of_contains_eq_false

@[grind =] theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a :=
  m.inductionOn fun _ => DHashMap.Const.get?_erase

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : get? (m.erase k) k = none :=
  m.inductionOn fun _ => DHashMap.Const.get?_erase_self

theorem get?_eq_get? [LawfulBEq α] {a : α} : get? m a = m.get? a :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_get?

theorem get?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : get? m a = get? m b :=
  m.inductionOn fun _ => DHashMap.Const.get?_congr hab

end Const

@[grind =] theorem get_insert [LawfulBEq α] {k a : α} {v : β k} {h₁} :
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

@[simp, grind =]
theorem get_erase [LawfulBEq α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  m.inductionOn (fun _ _ => DHashMap.get_erase) h'

theorem get?_eq_some_get [LawfulBEq α] {a : α} (h) : m.get? a = some (m.get a h) :=
  m.inductionOn (fun _ h => DHashMap.get?_eq_some_get h) h

theorem get_eq_get_get? [LawfulBEq α] {a : α} {h} :
    m.get a h = (m.get? a).get (mem_iff_isSome_get?.mp h) :=
  m.inductionOn (fun _ _ => DHashMap.get_eq_get_get?) h

@[grind =] theorem get_get? [LawfulBEq α] {a : α} {h} :
    (m.get? a).get h = m.get a (mem_iff_isSome_get?.mpr h) :=
  m.inductionOn (fun _ _ => DHashMap.get_get?) h

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[grind =] theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v else get m a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_insert) h₁

@[simp]
theorem get_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get (m.insert k v) k mem_insert_self = v :=
  m.inductionOn fun _ => DHashMap.Const.get_insert_self

@[simp, grind =]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    get (m.erase k) a h' = get m a (mem_of_mem_erase h') :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_erase) h'

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} (h) :
    get? m a = some (get m a h) :=
  m.inductionOn (fun _ h => DHashMap.Const.get?_eq_some_get h) h

theorem get_eq_get_get? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    get m a h = (get? m a).get (mem_iff_isSome_get?.mp h) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_get_get?) h

@[grind =] theorem get_get? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (get? m a).get h = get m a (mem_iff_isSome_get?.mpr h) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_get?) h

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_get) h

theorem get_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((mem_congr hab).1 h') :=
  m.inductionOn (fun _ hab _ => DHashMap.Const.get_congr hab) hab h'

end Const

@[simp, grind =]
theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] :
    (∅ : ExtDHashMap α β).get! a = default :=
  DHashMap.get!_empty

@[grind =] theorem get!_insert [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
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

@[grind =] theorem get!_erase [LawfulBEq α] {k a : α} [Inhabited (β a)] :
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

@[simp, grind =]
theorem get!_empty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : get! (∅ : ExtDHashMap α (fun _ => β)) a = default :=
  DHashMap.Const.get!_empty

@[grind =] theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a :=
  m.inductionOn fun _ => DHashMap.Const.get!_insert

@[simp]
theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} :
    get! (m.insert k v) k = v :=
  m.inductionOn fun _ => DHashMap.Const.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → get! m a = default :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_default_of_contains_eq_false

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → get! m a = default :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_default

@[grind =] theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a :=
  m.inductionOn fun _ => DHashMap.Const.get!_erase

@[simp]
theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    get! (m.erase k) k = default :=
  m.inductionOn fun _ => DHashMap.Const.get!_erase_self

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → get? m a = some (get! m a) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_get!_of_contains

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → get? m a = some (get! m a) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_get!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = (get? m a).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_get!_get?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h} :
    get m a h = get! m a :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_get!) h

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] {a : α} :
    get! m a = m.get! a :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_get!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    get! m a = get! m b :=
  m.inductionOn (fun _ hab => DHashMap.Const.get!_congr hab) hab

end Const

@[simp, grind =]
theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} :
    (∅ : ExtDHashMap α β).getD a fallback = fallback :=
  DHashMap.getD_empty

@[grind =] theorem getD_insert [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
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

@[grind =] theorem getD_erase [LawfulBEq α] {k a : α} {fallback : β a} :
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

@[simp, grind =]
theorem getD_empty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    getD (∅ : ExtDHashMap α (fun _ => β)) a fallback = fallback :=
  DHashMap.Const.getD_empty

@[grind =] theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_insert

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback v : β} :
   getD (m.insert k v) k fallback = v :=
  m.inductionOn fun _ => DHashMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : β} : m.contains a = false → getD m a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → getD m a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_fallback

@[grind =] theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_erase_self

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_getD_of_contains

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → get? m a = some (getD m a fallback) :=
  m.inductionOn fun _ => DHashMap.Const.get?_eq_some_getD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_getD_get?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_eq_getD) h

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = getD m a default :=
  m.inductionOn fun _ => DHashMap.Const.get!_eq_getD_default

theorem getD_eq_getD [LawfulBEq α] {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_eq_getD

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    getD m a fallback = getD m b fallback :=
  m.inductionOn (fun _ hab => DHashMap.Const.getD_congr hab) hab

end Const

@[simp, grind =]
theorem getKey?_empty [EquivBEq α] [LawfulHashable α] {a : α} : (∅ : ExtDHashMap α β).getKey? a = none :=
  DHashMap.getKey?_empty

@[grind =] theorem getKey?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  m.inductionOn fun _ => DHashMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k :=
  m.inductionOn fun _ => DHashMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  m.inductionOn fun _ => DHashMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_getKey?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome = m.contains a :=
  contains_eq_isSome_getKey?.symm

theorem mem_iff_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ (m.getKey? a).isSome :=
  m.inductionOn fun _ => DHashMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_getKey?.symm

theorem mem_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] {k k' : α}
    (h : m.getKey? k = some k') : k' ∈ m :=
  m.inductionOn (fun _ h => DHashMap.mem_of_getKey?_eq_some h) h

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey? a = none :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_none

@[grind =] theorem getKey?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  m.inductionOn fun _ => DHashMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).getKey? k = none :=
  m.inductionOn fun _ => DHashMap.getKey?_erase_self

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.getKey? k).all (· == k) :=
  m.inductionOn fun _ => DHashMap.getKey?_beq

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] {k k' : α} (h : k == k') :
    m.getKey? k = m.getKey? k' :=
  m.inductionOn (fun _ h => DHashMap.getKey?_congr h) h

theorem getKey?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) :
    m.getKey? k = some k :=
  m.inductionOn (fun _ h => DHashMap.getKey?_eq_some_of_contains h) h

theorem getKey?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k = some k :=
  m.inductionOn (fun _ h => DHashMap.getKey?_eq_some h) h

@[grind =] theorem getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  m.inductionOn (fun _ _ => DHashMap.getKey_insert) h₁

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).getKey k mem_insert_self = k :=
  m.inductionOn fun _ => DHashMap.getKey_insert_self

@[simp, grind =]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_erase) h'

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α} (h) :
    m.getKey? a = some (m.getKey a h) :=
  m.inductionOn (fun _ h => DHashMap.getKey?_eq_some_getKey h) h

theorem getKey_eq_get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m.getKey a h = (m.getKey? a).get (mem_iff_isSome_getKey?.mp h) :=
  m.inductionOn (fun _ _ => DHashMap.getKey_eq_get_getKey?) h

@[simp, grind =]
theorem get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  m.inductionOn (fun _ _ => DHashMap.get_getKey?) h

theorem getKey_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.getKey k h == k :=
  m.inductionOn (fun _ h => DHashMap.getKey_beq h) h

theorem getKey_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) :=
  m.inductionOn (fun _ h h₁ => DHashMap.getKey_congr h h₁) h h₁

@[simp, grind =]
theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k :=
  m.inductionOn (fun _ h => DHashMap.getKey_eq h) h

@[simp, grind =]
theorem getKey!_empty [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    (∅ : ExtDHashMap α β).getKey! a = default :=
  DHashMap.getKey!_empty

@[grind =] theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β k} :
    (m.insert k v).getKey! a =
      if k == a then k else m.getKey! a :=
  m.inductionOn fun _ => DHashMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {b : β a} :
    (m.insert a b).getKey! a = a :=
  m.inductionOn fun _ => DHashMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} :
    m.contains a = false → m.getKey! a = default :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    ¬a ∈ m → m.getKey! a = default :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_default

@[grind =] theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  m.inductionOn fun _ => DHashMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m.erase k).getKey! k = default :=
  m.inductionOn fun _ => DHashMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h} :
    m.getKey a h = m.getKey! a :=
  m.inductionOn (fun _ _ => DHashMap.getKey_eq_getKey!) h

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : k == k') :
    m.getKey! k = m.getKey! k' :=
  m.inductionOn (fun _ h => DHashMap.getKey!_congr h) h

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) :
    m.getKey! k = k :=
  m.inductionOn (fun _ h => DHashMap.getKey!_eq_of_contains h) h

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.getKey! k = k :=
  m.inductionOn (fun _ h => DHashMap.getKey!_eq_of_mem h) h

@[simp, grind =]
theorem getKeyD_empty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    (∅ : ExtDHashMap α β).getKeyD a fallback = fallback :=
  DHashMap.getKeyD_empty

@[grind =] theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β k} :
    (m.insert k v).getKeyD a fallback =
      if k == a then k else m.getKeyD a fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] {k fallback : α} {v : β k} :
    (m.insert k v).getKeyD k fallback = k :=
  m.inductionOn fun _ => DHashMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_eq_fallback

@[grind =] theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) :=
  m.inductionOn fun _ => DHashMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] {a fallback : α} {h} :
    m.getKey a h = m.getKeyD a fallback :=
  m.inductionOn (fun _ _ => DHashMap.getKey_eq_getKeyD) h

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = m.getKeyD a default :=
  m.inductionOn fun _ => DHashMap.getKey!_eq_getKeyD_default

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    (h : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback :=
  m.inductionOn (fun _ h => DHashMap.getKeyD_congr h) h

theorem getKeyD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getKeyD k fallback = k :=
  m.inductionOn (fun _ h => DHashMap.getKeyD_eq_of_contains h) h

theorem getKeyD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) :
    m.getKeyD k fallback = k :=
  m.inductionOn (fun _ h => DHashMap.getKeyD_eq_of_mem h) h

@[simp]
theorem not_insertIfNew_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    ¬m.insertIfNew k v = ∅ :=
  isEmpty_eq_false_iff.mp <| m.inductionOn fun _ => DHashMap.isEmpty_insertIfNew

@[simp, grind =]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  m.inductionOn fun _ => DHashMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_insertIfNew

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).contains k :=
  m.inductionOn fun _ => DHashMap.contains_insertIfNew_self

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insertIfNew k v :=
  m.inductionOn fun _ => DHashMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_insertIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_insertIfNew'

@[grind =] theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insertIfNew k v).size :=
  m.inductionOn fun _ => DHashMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.size_insertIfNew_le

@[grind =] theorem get?_insertIfNew [LawfulBEq α] {k a : α} {v : β k} : (m.insertIfNew k v).get? a =
    if h : k == a ∧ ¬k ∈ m then some (cast (congrArg β (eq_of_beq h.1)) v) else m.get? a :=
  m.inductionOn fun _ => DHashMap.get?_insertIfNew

@[grind =] theorem get_insertIfNew [LawfulBEq α] {k a : α} {v : β k} {h₁} : (m.insertIfNew k v).get a h₁ =
    if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v else m.get a
      (mem_of_mem_insertIfNew' h₁ h₂) :=
  m.inductionOn (fun _ _ => DHashMap.get_insertIfNew) h₁

@[grind =] theorem get!_insertIfNew [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v else m.get! a :=
  m.inductionOn fun _ => DHashMap.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback :=
  m.inductionOn fun _ => DHashMap.getD_insertIfNew

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[grind =] theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some v else get? m a :=
  m.inductionOn fun _ => DHashMap.Const.get?_insertIfNew

@[grind =] theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else get m a (mem_of_mem_insertIfNew' h₁ h₂) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_insertIfNew) h₁

@[grind =] theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then v else get! m a :=
  m.inductionOn fun _ => DHashMap.Const.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then v else getD m a fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_insertIfNew

end Const

@[grind =] theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a :=
  m.inductionOn fun _ => DHashMap.getKey?_insertIfNew

@[grind =] theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂) :=
  m.inductionOn (fun _ _ => DHashMap.getKey_insertIfNew) h₁

@[grind =] theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β k} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a :=
  m.inductionOn fun _ => DHashMap.getKey!_insertIfNew

@[grind =] theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β k} :
    getKeyD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_insertIfNew

@[simp, grind =]
theorem getThenInsertIfNew?_fst [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k :=
  m.inductionOn fun _ => DHashMap.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v :=
  m.inductionOn fun _ => congrArg mk DHashMap.getThenInsertIfNew?_snd

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}

@[simp, grind =]
theorem getThenInsertIfNew?_fst [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k :=
  m.inductionOn fun _ => DHashMap.Const.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  m.inductionOn fun _ => congrArg mk DHashMap.Const.getThenInsertIfNew?_snd

end Const

section insertMany

variable {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]

@[simp, grind =]
theorem insertMany_nil [EquivBEq α] [LawfulHashable α] : m.insertMany [] = m := rfl

@[simp, grind =]
theorem insertMany_list_singleton [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.insertMany [⟨k, v⟩] = m.insert k v := rfl

@[grind _=_]
theorem insertMany_cons [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {p : (a : α) × β a} :
    m.insertMany (p :: l) = (m.insert p.1 p.2).insertMany l := by
  rcases p with ⟨k, v⟩
  unfold insertMany
  simp only [bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons, Id.run_pure]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insert a.1 a.2) (m.insert k v) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

@[grind _=_]
theorem insertMany_append [EquivBEq α] [LawfulHashable α] {l₁ l₂ : List ((a : α) × β a)} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

private theorem insertMany_list_mk [EquivBEq α] [LawfulHashable α]
    {m : DHashMap α β} {l : List ((a : α) × β a)} :
    (ExtDHashMap.insertMany (mk m) l : ExtDHashMap α β) = mk (m.insertMany l) := by
  simp only [mk, Quotient.mk]
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    rcases x with ⟨k, v⟩
    simp only [insertMany_cons, insert, mk, Quotient.mk, ih, DHashMap.insertMany_cons]

@[elab_as_elim]
theorem insertMany_ind [EquivBEq α] [LawfulHashable α] {motive : ExtDHashMap α β → Prop}
    (m : ExtDHashMap α β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) := by
  change motive (Subtype.val ?my_mvar)
  exact Subtype.property ?my_mvar motive init (insert _ _ _)

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).contains k = (m.contains k || (l.map Sigma.fst).contains k) := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ m.insertMany l ↔ k ∈ m ∨ (l.map Sigma.fst).contains k := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.mem_insertMany_list

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} (mem : k ∈ m.insertMany l)
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    k ∈ m := by
  refine m.inductionOn (fun _ mem contains_eq_false => ?_) mem contains_eq_false
  simp only [insertMany_list_mk] at mem
  exact DHashMap.mem_of_mem_insertMany_list mem contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α] {l : ρ} {k : α} (h' : k ∈ m) : k ∈ m.insertMany l :=
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

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey? k = m.getKey? k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey? k' = some k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getKey?_insertMany_list_of_mem k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h} :
    (m.insertMany l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (m.insertMany l).getKey k' h = k := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.getKey_insertMany_list_of_mem k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey! k = m.getKey! k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey! k' = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getKey!_insertMany_list_of_mem k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKeyD k fallback = m.getKeyD k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKeyD k' fallback = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.getKeyD_insertMany_list_of_mem k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Sigma.fst).contains a = false) →
      (m.insertMany l).size = m.size + l.length := by
  refine m.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertMany_list_mk]
  exact DHashMap.size_insertMany_list distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    m.size ≤ (m.insertMany l).size := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.size_le_size_insertMany_list

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α] {l : ρ} : m.size ≤ (m.insertMany l).size :=
  insertMany_ind m l (Nat.le_refl _) fun _ _ _ h => Nat.le_trans h size_le_size_insert

grind_pattern size_le_size_insertMany_list => (m.insertMany l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (m.insertMany l).size ≤ m.size + l.length := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (m.insertMany l).size

@[simp]
theorem insertMany_list_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List ((a : α) × β a)} :
    m.insertMany l = ∅ ↔ m = ∅ ∧ l = [] := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk, ← isEmpty_iff, ← List.isEmpty_iff,
    Bool.coe_iff_coe, ← Bool.and_eq_true]
  exact DHashMap.isEmpty_insertMany_list

theorem eq_empty_of_insertMany_eq_empty [EquivBEq α] [LawfulHashable α] {l : ρ} :
    m.insertMany l = ∅ → m = ∅ :=
  insertMany_ind m l id fun _ _ _ _ h => absurd h not_insert_eq_empty

namespace Const

variable {β : Type v} {m : ExtDHashMap α (fun _ => β)}
variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[simp, grind =]
theorem insertMany_nil [EquivBEq α] [LawfulHashable α] : insertMany m [] = m :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v := rfl

@[grind _=_]
theorem insertMany_cons [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {p : α × β} :
    insertMany m (p :: l) = insertMany (m.insert p.1 p.2) l := by
  rcases p with ⟨k, v⟩
  unfold insertMany
  simp only [bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons, Id.run_pure]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insert a.1 a.2) (m.insert k v) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

@[grind _=_]
theorem insertMany_append [EquivBEq α] [LawfulHashable α] {l₁ l₂ : List (α × β)} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

private theorem insertMany_list_mk [EquivBEq α] [LawfulHashable α]
    {m : DHashMap α fun _ => β} {l : List (α × β)} :
    (insertMany (mk m) l : ExtDHashMap α fun _ => β) =
      mk (DHashMap.Const.insertMany m l) := by
  simp only [mk, Quotient.mk]
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    rcases x with ⟨k, v⟩
    simp only [insertMany_cons, insert, mk, Quotient.mk, ih, DHashMap.Const.insertMany_cons]

@[elab_as_elim]
theorem insertMany_ind [EquivBEq α] [LawfulHashable α] {motive : ExtDHashMap α (fun _ => β) → Prop}
    (m : ExtDHashMap α fun _ => β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (insertMany m l) := by
  change motive (Subtype.val ?my_mvar)
  exact Subtype.property ?my_mvar motive init (insert _ _ _)

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (Const.insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} (mem : k ∈ insertMany m l)
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    k ∈ m := by
  refine m.inductionOn (fun _ mem contains_eq_false => ?_) mem contains_eq_false
  simp only [insertMany_list_mk] at mem
  exact DHashMap.Const.mem_of_mem_insertMany_list mem contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α] {l : ρ} {k : α} (h' : k ∈ m) : k ∈ insertMany m l :=
  insertMany_ind m l h' fun _ _ _ h => mem_insert.mpr (.inr h)

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey?_insertMany_list_of_mem k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (insertMany m l).getKey k' h = k := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey_insertMany_list_of_mem k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKey!_insertMany_list_of_mem k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getKeyD_insertMany_list_of_mem k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length := by
  refine m.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertMany_list_mk]
  exact DHashMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    m.size ≤ (insertMany m l).size := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.size_le_size_insertMany_list

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α] {l : ρ} : m.size ≤ (insertMany m l).size :=
  insertMany_ind m l (Nat.le_refl _) fun _ _ _ h => Nat.le_trans h size_le_size_insert

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DHashMap.Const.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp]
theorem insertMany_list_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    insertMany m l = ∅ ↔ m = ∅ ∧ l = [] := by
  refine m.inductionOn fun _ => ?_
  simp only [insertMany_list_mk, ← isEmpty_iff, ← List.isEmpty_iff,
    Bool.coe_iff_coe, ← Bool.and_eq_true]
  exact DHashMap.Const.isEmpty_insertMany_list

theorem eq_empty_of_insertMany_eq_empty [EquivBEq α] [LawfulHashable α] {l : ρ} : insertMany m l = ∅ → m = ∅ :=
  insertMany_ind m l id fun _ _ _ _ h => absurd h not_insert_eq_empty

theorem get?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l) k = get? m k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l) k' = some v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get?_insertMany_list_of_mem k_beq distinct mem

@[grind =] theorem get?_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    get? (insertMany m l) k =
      (l.findSomeRev? (fun ⟨a, b⟩ => if a == k then some b else none)).or (get? m k) := by
  refine m.inductionOn (fun _ => ?_)
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get?_insertMany_list

theorem get_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    get (insertMany m l) k h = get m k (mem_of_mem_insertMany_list h contains_eq_false) := by
  refine m.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get_insertMany_list_of_contains_eq_false contains_eq_false

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h} :
    get (insertMany m l) k' h = v := by
  refine m.inductionOn (fun _ k_beq distinct mem _ => ?_) k_beq distinct mem h
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get_insertMany_list_of_mem k_beq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany m l) k = get! m k := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany m l) k' = v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.get!_insertMany_list_of_mem k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v := by
  refine m.inductionOn (fun _ k_beq distinct mem => ?_) k_beq distinct mem
  simp only [insertMany_list_mk]
  exact DHashMap.Const.getD_insertMany_list_of_mem k_beq distinct mem

variable {m : ExtDHashMap α (fun _ => Unit)}
variable {ρ : Type w} [ForIn Id ρ α]

@[simp]
theorem insertManyIfNewUnit_nil [EquivBEq α] [LawfulHashable α] :
    insertManyIfNewUnit m [] = m :=
  rfl

@[simp]
theorem insertManyIfNewUnit_list_singleton [EquivBEq α] [LawfulHashable α] {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () := rfl

theorem insertManyIfNewUnit_cons [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l := by
  unfold insertManyIfNewUnit
  simp only [bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons, Id.run_pure]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insertIfNew a ()) (m.insertIfNew k ()) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

private theorem insertManyIfNewUnit_list_mk [EquivBEq α] [LawfulHashable α]
    {m : DHashMap α fun _ => Unit} {l : List α} :
    (insertManyIfNewUnit (mk m) l : ExtDHashMap α fun _ => Unit) =
      mk (DHashMap.Const.insertManyIfNewUnit m l) := by
  simp only [mk, Quotient.mk]
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    simp only [insertManyIfNewUnit_cons, insertIfNew, mk, Quotient.mk, ih,
      DHashMap.Const.insertManyIfNewUnit_cons]

@[elab_as_elim]
theorem insertManyIfNewUnit_ind [EquivBEq α] [LawfulHashable α] {motive : ExtDHashMap α (fun _ => Unit) → Prop}
    (m : ExtDHashMap α fun _ => Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l) := by
  change motive (Subtype.val ?my_mvar)
  exact Subtype.property ?my_mvar motive init (insert _ _)

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m := by
  refine m.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem mem_insertManyIfNewUnit_of_mem [EquivBEq α] [LawfulHashable α] {l : ρ} {k : α} (h : k ∈ m) :
    k ∈ insertManyIfNewUnit m l :=
  insertManyIfNewUnit_ind m l h fun _ _ h => mem_insertIfNew.mpr (.inr h)

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit m l) k = none := by
  refine m.inductionOn (fun _ not_mem contains_eq_false => ?_) not_mem contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit m l) k' = some k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem => ?_) k_beq not_mem distinct mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (h' : k ∈ m) :
    getKey? (insertManyIfNewUnit m l) k = getKey? m k := by
  refine m.inductionOn (fun _ h' => ?_) h'
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey?_insertManyIfNewUnit_list_of_mem h'

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (insertManyIfNewUnit m l) k' h = k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem _ => ?_) k_beq not_mem distinct mem h
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKey_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    getKey (insertManyIfNewUnit m l) k h = getKey m k mem := by
  refine m.inductionOn (fun _ mem _ => ?_) mem h
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey_insertManyIfNewUnit_list_of_mem mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default := by
  refine m.inductionOn (fun _ not_mem contains_eq_false => ?_) not_mem contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem => ?_) k_beq not_mem distinct mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    getKey! (insertManyIfNewUnit m l) k = getKey! m k := by
  refine m.inductionOn (fun _ mem => ?_) mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit m l) k fallback = fallback := by
  refine m.inductionOn (fun _ not_mem contains_eq_false => ?_) not_mem contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k := by
  refine m.inductionOn (fun _ k_beq not_mem distinct mem => ?_) k_beq not_mem distinct mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_beq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback := by
  refine m.inductionOn (fun _ mem => ?_) mem
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length := by
  refine m.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_le_size_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertManyIfNewUnit m l).size :=
  insertManyIfNewUnit_ind m l (Nat.le_refl _) fun _ _ h => Nat.le_trans h size_le_size_insertIfNew

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem insertManyIfNewUnit_list_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List α} :
    insertManyIfNewUnit m l = ∅ ↔ m = ∅ ∧ l = [] := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk, ← isEmpty_iff, ← List.isEmpty_iff,
    Bool.coe_iff_coe, ← Bool.and_eq_true]
  exact DHashMap.Const.isEmpty_insertManyIfNewUnit_list

theorem eq_empty_of_insertManyIfNewUnit_eq_empty [EquivBEq α] [LawfulHashable α] {l : ρ} :
    insertManyIfNewUnit m l = ∅ → m = ∅ :=
  insertManyIfNewUnit_ind m l id fun _ _ _ h => absurd h not_insertIfNew_eq_empty

theorem get?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit m l) k =
      if k ∈ m ∨ l.contains k then some () else none := by
  refine m.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DHashMap.Const.get?_insertManyIfNewUnit_list

theorem get_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit m l) k h = () :=
  rfl

theorem get!_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit m l) k = () :=
  rfl

theorem getD_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () :=
  rfl

end Const

end insertMany

end ExtDHashMap

namespace ExtDHashMap

@[simp, grind =]
theorem ofList_nil [EquivBEq α] [LawfulHashable α] :
    ofList ([] : List ((a : α) × β a)) = ∅ := rfl

@[simp, grind =]
theorem ofList_singleton [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    ofList [⟨k, v⟩] = (∅ : ExtDHashMap α β).insert k v := rfl

@[grind _=_]
theorem ofList_cons [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} {tl : List ((a : α) × β a)} :
    ofList (⟨k, v⟩ :: tl) = ((∅ : ExtDHashMap α β).insert k v).insertMany tl := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DHashMap.ofList_cons

theorem ofList_eq_insertMany_empty [EquivBEq α] [LawfulHashable α] {l : List ((a : α) × β a)} :
    ofList l = insertMany (∅ : ExtDHashMap α β) l := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DHashMap.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l).contains k = (l.map Sigma.fst).contains k :=
  DHashMap.contains_ofList

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l ↔ (l.map Sigma.fst).contains k :=
  DHashMap.mem_ofList

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get? k = none :=
  DHashMap.get?_ofList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) :=
  DHashMap.get?_ofList_of_mem k_beq distinct mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  DHashMap.get_ofList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get! k = default :=
  DHashMap.get!_ofList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  DHashMap.get!_ofList_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getD k fallback = fallback :=
  DHashMap.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  DHashMap.getD_ofList_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  DHashMap.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey? k' = some k :=
  DHashMap.getKey?_ofList_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  DHashMap.getKey_ofList_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  DHashMap.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey! k' = k :=
  DHashMap.getKey!_ofList_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  DHashMap.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKeyD k' fallback = k :=
  DHashMap.getKeyD_ofList_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  DHashMap.size_ofList distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).size ≤ l.length :=
  DHashMap.size_ofList_le

grind_pattern size_ofList_le => (ofList l).size

@[simp]
theorem ofList_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List ((a : α) × β a)} :
    ofList l = ∅ ↔ l = [] := by
  simpa only [← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe] using
    DHashMap.isEmpty_ofList

namespace Const

variable {β : Type v}

@[simp, grind =]
theorem ofList_nil [EquivBEq α] [LawfulHashable α] :
    ofList ([] : List (α × β)) = ∅ :=
  rfl

@[simp, grind =]
theorem ofList_singleton [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : ExtDHashMap α (fun _ => β)).insert k v :=
  rfl

@[grind _=_]
theorem ofList_cons [EquivBEq α] [LawfulHashable α] {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : ExtDHashMap α (fun _ => β)).insert k v) tl := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DHashMap.Const.ofList_cons

theorem ofList_eq_insertMany_empty [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    ofList l = insertMany (∅ : ExtDHashMap α (fun _ => β)) l := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DHashMap.Const.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  DHashMap.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ ofList l ↔ (l.map Prod.fst).contains k :=
  DHashMap.Const.mem_ofList

theorem get?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l) k = none :=
  DHashMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l) k' = some v :=
  DHashMap.Const.get?_ofList_of_mem k_beq distinct mem

theorem get_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l) k' h = v :=
  DHashMap.Const.get_ofList_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l) k = (default : β) :=
  DHashMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l) k' = v :=
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

grind_pattern size_ofList_le => (ofList l).size

@[simp]
theorem ofList_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    ofList l = ∅ ↔ l = [] := by
  simpa only [← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe] using
    DHashMap.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil [EquivBEq α] [LawfulHashable α] :
    unitOfList ([] : List α) = ∅ :=
  congrArg mk DHashMap.Const.unitOfList_nil

@[simp]
theorem unitOfList_singleton [EquivBEq α] [LawfulHashable α] {k : α} :
    unitOfList [k] = (∅ : ExtDHashMap α (fun _ => Unit)).insertIfNew k () :=
  congrArg mk DHashMap.Const.unitOfList_singleton

theorem unitOfList_cons [EquivBEq α] [LawfulHashable α] {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      insertManyIfNewUnit ((∅ : ExtDHashMap α (fun _ => Unit)).insertIfNew hd ()) tl := by
  conv => rhs; apply insertManyIfNewUnit_list_mk
  exact congrArg mk DHashMap.Const.unitOfList_cons

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
theorem unitOfList_eq_empty_iff [EquivBEq α] [LawfulHashable α] {l : List α} :
    unitOfList l = ∅ ↔ l = [] := by
  simpa only [← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe] using
    DHashMap.Const.isEmpty_unitOfList

@[simp]
theorem get?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (unitOfList l) k =
    if l.contains k then some () else none :=
  DHashMap.Const.get?_unitOfList

@[simp]
theorem get_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {h} :
    get (unitOfList l) k h = () :=
  DHashMap.Const.get_unitOfList

@[simp]
theorem get!_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get! (unitOfList l) k = () :=
  DHashMap.Const.get!_unitOfList

@[simp]
theorem getD_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () :=
  DHashMap.Const.getD_unitOfList

end Const

variable {m : ExtDHashMap α β}

section Alter

theorem alter_eq_empty_iff_erase_eq_empty [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    m.alter k f = ∅ ↔ m.erase k = ∅ ∧ f (m.get? k) = none := by
  cases m with | mk m
  simpa only [← isEmpty_iff, ← Option.isNone_iff_eq_none, ← Bool.and_eq_true, Bool.coe_iff_coe] using
    DHashMap.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem alter_eq_empty_iff [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    alter m k f = ∅ ↔ (m = ∅ ∨ (m.size = 1 ∧ k ∈ m)) ∧ f (get? m k) = none := by
  rw [alter_eq_empty_iff_erase_eq_empty, erase_eq_empty_iff]

@[grind =] theorem contains_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' :=
  m.inductionOn fun _ => DHashMap.contains_alter

@[grind =] theorem mem_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
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

@[grind =] theorem size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
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

@[grind =] theorem get?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
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

@[grind =] theorem get_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
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

@[grind =] theorem get!_alter [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')]
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

@[grind =] theorem getD_alter [LawfulBEq α] {k k' : α} {fallback : β k'} {f : Option (β k) → Option (β k)} :
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

@[grind =] theorem getKey?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k' =
      if k == k' then
        if (f (m.get? k)).isSome then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.getKey?_alter

theorem getKey?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k = if (f (m.get? k)).isSome then some k else none :=
  m.inductionOn fun _ => DHashMap.getKey?_alter_self

@[grind =] theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.getKey!_alter

theorem getKey!_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k = if (f (m.get? k)).isSome then k else default :=
  m.inductionOn fun _ => DHashMap.getKey!_alter_self

@[deprecated getKey_eq (since := "2025-01-05")]
theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    {h : k' ∈ m.alter k f} :
    (m.alter k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' := by
  split <;> simp_all

@[simp]
theorem getKey_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)}
    {h : k ∈ m.alter k f} : (m.alter k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.getKey_alter_self) h

@[grind =] theorem getKeyD_alter [LawfulBEq α] {k k' fallback : α} {f : Option (β k) → Option (β k)} :
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

theorem alter_eq_empty_iff_erase_eq_empty [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    alter m k f = ∅ ↔ m.erase k = ∅ ∧ f (get? m k) = none := by
  cases m with | mk m
  simpa only [← isEmpty_iff, ← Option.isNone_iff_eq_none, ← Bool.and_eq_true, Bool.coe_iff_coe] using
    DHashMap.Const.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem alter_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    alter m k f = ∅ ↔ (m = ∅ ∨ (m.size = 1 ∧ k ∈ m)) ∧ f (get? m k) = none := by
  simp only [alter_eq_empty_iff_erase_eq_empty, erase_eq_empty_iff]

@[grind =] theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
      if k == k' then (f (Const.get? m k)).isSome else m.contains k' :=
  m.inductionOn fun _ => DHashMap.Const.contains_alter

@[grind =] theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    k' ∈ Const.alter m k f ↔ if k == k' then (f (Const.get? m k)).isSome = true else k' ∈ m :=
  m.inductionOn fun _ => DHashMap.Const.mem_alter

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : k == k') : k' ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome :=
  m.inductionOn (fun _ h => DHashMap.Const.mem_alter_of_beq h) h

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).contains k = (f (Const.get? m k)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    k ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.mem_alter_self

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) :
    (Const.alter m k f).contains k' = m.contains k' :=
  m.inductionOn (fun _ h => DHashMap.Const.contains_alter_of_beq_eq_false h) h

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) : k' ∈ Const.alter m k f ↔ k' ∈ m :=
  m.inductionOn (fun _ h => DHashMap.Const.mem_alter_of_beq_eq_false h) h

@[grind =] theorem size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size =
      if k ∈ m ∧ (f (Const.get? m k)).isNone then
        m.size - 1
      else if k ∉ m ∧ (f (Const.get? m k)).isSome then
        m.size + 1
      else
        m.size :=
  m.inductionOn fun _ => DHashMap.Const.size_alter

theorem size_alter_eq_add_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).size = m.size + 1 :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_add_one h h') h h'

theorem size_alter_eq_sub_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).size = m.size - 1 :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_sub_one h h') h h'

theorem size_alter_eq_self_of_not_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isNone) : (Const.alter m k f).size = m.size :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_self_of_not_mem h h') h h'

theorem size_alter_eq_self_of_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isSome) : (Const.alter m k f).size = m.size :=
  m.inductionOn (fun _ h h' => DHashMap.Const.size_alter_eq_self_of_mem h h') h h'

theorem size_alter_le_size [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size ≤ m.size + 1 :=
  m.inductionOn fun _ => DHashMap.Const.size_alter_le_size

theorem size_le_size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    m.size - 1 ≤ (Const.alter m k f).size :=
  m.inductionOn fun _ => DHashMap.Const.size_le_size_alter

@[grind =] theorem get?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k)
      else
        Const.get? m k' :=
  m.inductionOn fun _ => DHashMap.Const.get?_alter

@[simp]
theorem get?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k = f (Const.get? m k) :=
  m.inductionOn fun _ => DHashMap.Const.get?_alter_self

@[grind =] theorem get_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
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
theorem get_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    {h : k ∈ Const.alter m k f} :
    haveI h' : (f (Const.get? m k)).isSome := mem_alter_self.mp h
    Const.get (Const.alter m k f) k h = (f (Const.get? m k)).get h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_alter_self) h

@[grind =] theorem get!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} : Const.get! (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k) |>.get!
      else
        Const.get! m k' :=
  m.inductionOn fun _ => DHashMap.Const.get!_alter

@[simp]
theorem get!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} : Const.get! (Const.alter m k f) k = (f (Const.get? m k)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_alter_self

@[grind =] theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β}
    {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k' fallback =
      if k == k' then
        f (Const.get? m k) |>.getD fallback
      else
        Const.getD m k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_alter

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k fallback = (f (Const.get? m k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_alter_self

@[grind =] theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_alter

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k = if (f (Const.get? m k)).isSome then some k else none :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_alter_self

@[grind =] theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} : (Const.alter m k f).getKey! k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_alter

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (Const.alter m k f).getKey! k = if (f (Const.get? m k)).isSome then k else default :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_alter_self

@[grind =] theorem getKey_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} {h : k' ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_alter) h

@[simp]
theorem getKey_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} {h : k ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_alter_self) h

@[grind =] theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_alter

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
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

@[simp, grind =]
theorem contains_modify [LawfulBEq α] {k k': α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' :=
  m.inductionOn fun _ => DHashMap.contains_modify

@[simp, grind =]
theorem mem_modify [LawfulBEq α] {k k': α} {f : β k → β k} : k' ∈ m.modify k f ↔ k' ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_modify

@[simp, grind =]
theorem size_modify [LawfulBEq α] {k : α} {f : β k → β k} : (m.modify k f).size = m.size :=
  m.inductionOn fun _ => DHashMap.size_modify

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[deprecated getKey_eq (since := "2025-01-05")]
theorem getKey_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k}
    {h : k' ∈ m.modify k f} :
    (m.modify k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' := by
  split <;> simp_all

@[simp]
theorem getKey_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k}
    {h : k ∈ m.modify k f} : (m.modify k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.getKey_modify_self) h

@[grind =]
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
theorem modify_eq_empty_iff [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    Const.modify m k f = ∅ ↔ m = ∅ := by
  simp only [← isEmpty_iff, Bool.coe_iff_coe]
  exact m.inductionOn fun _ => DHashMap.Const.isEmpty_modify

@[simp, grind =]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' :=
  m.inductionOn fun _ => DHashMap.Const.contains_modify

@[simp, grind =]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    k' ∈ Const.modify m k f ↔ k' ∈ m :=
  m.inductionOn fun _ => DHashMap.Const.mem_modify

@[simp, grind =]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).size = m.size :=
  m.inductionOn fun _ => DHashMap.Const.size_modify

@[grind =]
theorem get?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    Const.get? (Const.modify m k f) k' = if k == k' then
      Const.get? m k |>.map f
    else
      Const.get? m k' :=
  m.inductionOn fun _ => DHashMap.Const.get?_modify

@[simp]
theorem get?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f :=
  m.inductionOn fun _ => DHashMap.Const.get?_modify_self

@[grind =]
theorem get_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
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
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    Const.get (Const.modify m k f) k h = f (Const.get m k h') :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_modify_self) h

@[grind =]
theorem get!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f |>.get!
      else
        Const.get! m k' :=
  m.inductionOn fun _ => DHashMap.Const.get!_modify

@[simp]
theorem get!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_modify_self

@[grind =]
theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k' fallback =
      if k == k' then
        Const.get? m k |>.map f |>.getD fallback
      else
        Const.getD m k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_modify

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k fallback = ((Const.get? m k).map f).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_modify_self

@[grind =]
theorem getKey?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_modify

theorem getKey?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey? k = if k ∈ m then some k else none :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_modify_self

@[grind =]
theorem getKey!_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_modify

theorem getKey!_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey! k = if k ∈ m then k else default :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_modify_self

@[grind =]
theorem getKey_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    {h : k' ∈ Const.modify m k f} :
    (Const.modify m k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_modify) h

@[simp]
theorem getKey_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} : (Const.modify m k f).getKey k h = k :=
  m.inductionOn (fun _ _ => DHashMap.Const.getKey_modify_self) h

@[grind =]
theorem getKeyD_modify [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_modify

theorem getKeyD_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_modify_self

end Const

end Modify

section Ext

variable {m₁ m₂ : Std.ExtDHashMap α β}

@[ext]
theorem ext_get? [LawfulBEq α] {m₁ m₂ : Std.ExtDHashMap α β} (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => sound (.of_forall_get?_eq h)) h

namespace Const

variable {β : Type v} {m₁ m₂ : ExtDHashMap α fun _ => β}

theorem ext_getKey_get? [EquivBEq α] [LawfulHashable α]
    (hk : ∀ k hk hk', m₁.getKey k hk = m₂.getKey k hk')
    (hv : ∀ k, Const.get? m₁ k = Const.get? m₂ k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ hk hv => sound
    (.of_forall_getKey_eq_of_forall_constGet?_eq hk hv)) hk hv

theorem ext_get? [LawfulBEq α] (h : ∀ k, get? m₁ k = get? m₂ k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => sound (.of_forall_constGet?_eq h)) h

theorem ext_getKey?_unit [EquivBEq α] [LawfulHashable α] {m₁ m₂ : ExtDHashMap α fun _ => Unit}
    (h : ∀ k, m₁.getKey? k = m₂.getKey? k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => sound (.of_forall_getKey?_unit_eq h)) h

theorem ext_contains_unit [LawfulBEq α] {m₁ m₂ : ExtDHashMap α fun _ => Unit}
    (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => sound (.of_forall_contains_unit_eq h)) h

theorem ext_mem_unit [LawfulBEq α] {m₁ m₂ : ExtDHashMap α fun _ => Unit}
    (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) : m₁ = m₂ :=
  m₁.inductionOn₂ m₂ (fun _ _ h => sound (.of_forall_mem_unit_iff h)) h

end Const

end Ext

section filterMap

variable {γ : α → Type w}

theorem filterMap_eq_empty_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    m.filterMap f = ∅ ↔ ∀ k h, f k (m.get k h) = none :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_filterMap_iff

@[grind =]
theorem contains_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).contains k = (m.get? k).any (f k · |>.isSome) :=
  m.inductionOn fun _ => DHashMap.contains_filterMap

@[grind =]
theorem mem_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f k (m.get k h)).isSome :=
  m.inductionOn fun _ => DHashMap.mem_filterMap

theorem contains_of_contains_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).contains k = true → m.contains k = true :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_filterMap

theorem mem_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ m.filterMap f → k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_filterMap

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_filterMap_le_size

grind_pattern size_filterMap_le_size => (m.filterMap f).size

theorem size_filterMap_eq_size_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).size = m.size ↔ ∀ (a : α) (h : a ∈ m), (f a (m.get a h)).isSome :=
  m.inductionOn fun _ => DHashMap.size_filterMap_eq_size_iff

@[simp, grind =]
theorem get?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).get? k = (m.get? k).bind (f k) :=
  m.inductionOn fun _ => DHashMap.get?_filterMap

theorem isSome_apply_of_mem_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    ∀ (h' : k ∈ m.filterMap f),
      (f k (m.get k (mem_of_mem_filterMap h'))).isSome :=
  m.inductionOn fun _ => DHashMap.isSome_apply_of_mem_filterMap

@[simp, grind =]
theorem get_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (m.filterMap f).get k h' =
      (f k (m.get k (mem_of_mem_filterMap h'))).get
        (isSome_apply_of_mem_filterMap h') :=
  m.inductionOn (fun _ _ => DHashMap.get_filterMap) h'

@[grind =]
theorem get!_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} [Inhabited (γ k)] :
    (m.filterMap f).get! k = ((m.get? k).bind (f k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_filterMap

@[grind =]
theorem getD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {fallback : γ k} :
    (m.filterMap f).getD k fallback = ((m.get? k).bind (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_filterMap

@[grind =]
theorem getKey?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome) :=
  m.inductionOn fun _ => DHashMap.getKey?_filterMap

@[simp, grind =]
theorem getKey_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (m.filterMap f).getKey k h' = m.getKey k (mem_of_mem_filterMap h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_filterMap) h'

@[grind =]
theorem getKey!_filterMap [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_filterMap

@[grind =]
theorem getKeyD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_filterMap

namespace Const

variable {β : Type v} {γ : Type w} {m : ExtDHashMap α (fun _ => β)}

theorem filterMap_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} :
    m.filterMap f = ∅ ↔ ∀ k h, f (m.getKey k h) (get m k h) = none :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.Const.isEmpty_filterMap_iff

@[grind =]
theorem mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f (m.getKey k h) (Const.get m k h)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.mem_filterMap

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β → Option γ} :
    (m.filterMap f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_filterMap_le_size

grind_pattern size_filterMap_le_size => (m.filterMap f).size

theorem size_filterMap_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).size = m.size ↔ ∀ k h, (f (m.getKey k h) (Const.get m k h)).isSome :=
  m.inductionOn fun _ => DHashMap.Const.size_filterMap_eq_size_iff

@[simp]
theorem get?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    Const.get? (m.filterMap f) k = (Const.get? m k).pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  m.inductionOn fun _ => DHashMap.Const.get?_filterMap

/-- Simpler variant of `get?_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem get?_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    Const.get? (m.filterMap f) k = (Const.get? m k).bind (f k) := by
  simp [get?_filterMap]

theorem get?_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get? (m.filterMap f) k = (Const.get? m k).bind (f k') :=
  m.inductionOn (fun _ h => DHashMap.Const.get?_filterMap_of_getKey?_eq_some h) h

theorem isSome_apply_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ m.filterMap f),
      (f (m.getKey k (mem_of_mem_filterMap h))
        (Const.get m k (mem_of_mem_filterMap h))).isSome :=
  m.inductionOn fun _ => DHashMap.Const.isSome_apply_of_mem_filterMap

@[simp]
theorem get_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (m.filterMap f) k h =
      (f (m.getKey k (mem_of_mem_filterMap h))
        (Const.get m k (mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_filterMap) h

/-- Simpler variant of `get_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem get_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (m.filterMap f) k h = (f k (Const.get m k (mem_of_mem_filterMap h))).get (by simpa using isSome_apply_of_mem_filterMap h) := by
  simp [get_filterMap]

theorem get!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (m.filterMap f) k =
      ((Const.get? m k).pbind (fun x h' =>
        f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_filterMap

/-- Simpler variant of `get!_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem get!_filterMap' [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (m.filterMap f) k = ((Const.get? m k).bind (f k)).get! := by
  simp [get!_filterMap]

theorem get!_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get! (m.filterMap f) k = ((Const.get? m k).bind (f k')).get! :=
  m.inductionOn (fun _ h => DHashMap.Const.get!_filterMap_of_getKey?_eq_some h) h

theorem getD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (m.filterMap f) k fallback =
      ((Const.get? m k).pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_filterMap

/-- Simpler variant of `getD_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getD_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (m.filterMap f) k fallback = ((Const.get? m k).bind (f k)).getD fallback := by
  simp [getD_filterMap]

theorem getD_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    Const.getD (m.filterMap f) k fallback = ((Const.get? m k).bind (f k')).getD fallback :=
  m.inductionOn (fun _ h => DHashMap.Const.getD_filterMap_of_getKey?_eq_some h) h

@[grind =]
theorem getKey?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome) :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_filterMap

@[grind =]
theorem getKey!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_filterMap

@[grind =]
theorem getKeyD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getKeyD_filterMap

end Const

end filterMap

section filter

theorem filterMap_eq_filter [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → Bool} :
    m.filterMap (fun k => Option.guard (fun v => f k v)) = m.filter f :=
  m.inductionOn fun _ => sound DHashMap.filterMap_equiv_filter

@[simp]
theorem filter_eq_empty_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} :
    m.filter f = ∅ ↔ ∀ k h, f k (m.get k h) = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_filter_iff

theorem filter_key_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → Bool} :
    m.filter (fun a _ => f a) = ∅ ↔ ∀ k h, f (m.getKey k h) = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.isEmpty_filter_key_iff

@[grind =] theorem contains_filter [LawfulBEq α] {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).contains k = (m.get? k).any (f k) :=
  m.inductionOn fun _ => DHashMap.contains_filter

@[grind =] theorem mem_filter [LawfulBEq α] {f : (a : α) → β a → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ h, f k (m.get k h) :=
  m.inductionOn fun _ => DHashMap.mem_filter

theorem mem_filter_key [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} :
    k ∈ m.filter (fun a _ => f a) ↔ ∃ h, f (m.getKey k h) :=
  m.inductionOn fun _ => DHashMap.mem_filter_key

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).contains k = true → m.contains k = true :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_filter

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → Bool} {k : α} :
    k ∈ (m.filter f) → k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → Bool} :
    (m.filter f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.size_filter_le_size

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [LawfulBEq α] {f : (a : α) → β a → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f k (m.get k h) :=
  m.inductionOn fun _ => DHashMap.size_filter_eq_size_iff

theorem filter_eq_self_iff [LawfulBEq α] {f : (a : α) → β a → Bool} :
    m.filter f = m ↔ ∀ k h, f k (m.get k h) :=
  m.inductionOn fun _ => Iff.trans ⟨exact, sound⟩ DHashMap.filter_equiv_self_iff

theorem filter_key_equiv_self_iff [EquivBEq α] [LawfulHashable α] {f : (a : α) → Bool} :
    m.filter (fun k _ => f k) = m ↔ ∀ k h, f (m.getKey k h) :=
  m.inductionOn fun _ => Iff.trans ⟨exact, sound⟩ DHashMap.filter_key_equiv_self_iff

theorem size_filter_key_eq_size_iff [EquivBEq α] [LawfulHashable α] {f : α → Bool} :
    (m.filter fun k _ => f k).size = m.size ↔ ∀ k h, f (m.getKey k h) :=
  m.inductionOn fun _ => DHashMap.size_filter_key_eq_size_iff

@[simp, grind =]
theorem get?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).get? k = (m.get? k).filter (f k) :=
  m.inductionOn fun _ => DHashMap.get?_filter

@[simp, grind =]
theorem get_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (m.filter f).get k h' = m.get k (mem_of_mem_filter h') :=
  m.inductionOn (fun _ _ => DHashMap.get_filter) h'

@[grind =]
theorem get!_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} [Inhabited (β k)] :
    (m.filter f).get! k = ((m.get? k).filter (f k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_filter

@[grind =]
theorem getD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {fallback : β k} :
    (m.filter f).getD k fallback = ((m.get? k).filter (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_filter

@[grind =]
theorem getKey?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h'))) :=
  m.inductionOn fun _ => DHashMap.getKey?_filter

theorem getKey?_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f :=
  m.inductionOn fun _ => DHashMap.getKey?_filter_key

@[simp, grind =]
theorem getKey_filter [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (m.filter f).getKey k h' = m.getKey k (mem_of_mem_filter h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_filter) h'

@[grind =]
theorem getKey!_filter [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h')))).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_filter

theorem getKey!_filter_key [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! :=
  m.inductionOn fun _ => DHashMap.getKey!_filter_key

@[grind =]
theorem getKeyD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h')))).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_filter

theorem getKeyD_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_filter_key

namespace Const

variable {β : Type v} {γ : Type w} {m : ExtDHashMap α (fun _ => β)}

theorem filter_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    m.filter f = ∅ ↔ ∀ k h, f (m.getKey k h) (Const.get m k h) = false :=
  isEmpty_iff.symm.trans <| m.inductionOn fun _ => DHashMap.Const.isEmpty_filter_iff

@[grind =] theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ (h' : k ∈ m),
      f (m.getKey k h') (Const.get m k h') :=
  m.inductionOn fun _ => DHashMap.Const.mem_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size ≤ m.size :=
  m.inductionOn fun _ => DHashMap.Const.size_filter_le_size

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size = m.size ↔ ∀ (a : α) (h : a ∈ m),
      f (m.getKey a h) (Const.get m a h) :=
  m.inductionOn fun _ => DHashMap.Const.size_filter_eq_size_iff

theorem filter_eq_self_iff [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    m.filter f = m ↔ ∀ k h, f (m.getKey k h) (Const.get m k h) :=
  m.inductionOn fun _ => Iff.trans ⟨exact, sound⟩ DHashMap.Const.filter_equiv_self_iff

theorem get?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  m.inductionOn fun _ => DHashMap.Const.get?_filter

/-- Simpler variant of `get?_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem get?_filter' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    Const.get? (m.filter f) k = (Const.get? m k).filter (f k) := by
  simp [get?_filter]

theorem get?_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      Const.get? (m.filter f) k = (Const.get? m k).filter (fun x => f k' x) :=
  m.inductionOn fun _ => DHashMap.Const.get?_filter_of_getKey?_eq_some

@[simp, grind =]
theorem get_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} :
    Const.get (m.filter f) k h' = Const.get m k (mem_of_mem_filter h') :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_filter) h'

theorem get!_filter [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    Const.get! (m.filter f) k =
      ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_filter

/-- Simpler variant of `get!_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem get!_filter' [LawfulBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    Const.get! (m.filter f) k = ((Const.get? m k).filter (f k)).get! := by
  simp [get!_filter]

theorem get!_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      Const.get! (m.filter f) k = ((Const.get? m k).filter (fun x => f k' x)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_filter_of_getKey?_eq_some

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} :
    Const.getD (m.filter f) k fallback = ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_filter

/-- Simpler variant of `getD_filter` when `LawfulBEq` is available. -/
@[grind =]
theorem getD_filter' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} :
    Const.getD (m.filter f) k fallback = ((Const.get? m k).filter (f k)).getD fallback := by
  simp [getD_filter]

theorem getD_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} {fallback : β} :
    m.getKey? k = some k' →
      Const.getD (m.filter f) k fallback =
        ((Const.get? m k).filter (fun x => f k' x)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_filter_of_getKey?_eq_some

@[grind =] theorem getKey?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h')))) :=
  m.inductionOn fun _ => DHashMap.Const.getKey?_filter

@[grind =] theorem getKey!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))))).get! :=
  m.inductionOn fun _ => DHashMap.Const.getKey!_filter

@[grind =] theorem getKeyD_filter [EquivBEq α] [LawfulHashable α]
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
theorem map_id_fun [EquivBEq α] [LawfulHashable α] : m.map (fun _ v => v) = m :=
  m.inductionOn fun _ => sound DHashMap.map_id_equiv

@[simp]
theorem map_map [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → γ a} {g : (a : α) → γ a → δ a} :
    (m.map f).map g = m.map fun k v => g k (f k v) :=
  m.inductionOn fun _ => sound DHashMap.map_map_equiv

theorem filterMap_eq_map [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → γ a} :
    (m.filterMap (fun k v => some (f k v))) = m.map f :=
  m.inductionOn fun _ => sound DHashMap.filterMap_equiv_map

@[simp]
theorem map_eq_empty_iff [EquivBEq α] [LawfulHashable α] {f : (a : α) → β a → γ a} :
    m.map f = ∅ ↔ m = ∅ := by
  simp only [← isEmpty_iff, Bool.coe_iff_coe]
  exact m.inductionOn fun _ => DHashMap.isEmpty_map

@[grind =] theorem contains_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).contains k = m.contains k :=
  m.inductionOn fun _ => DHashMap.contains_map

theorem contains_of_contains_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).contains k = true → m.contains k = true :=
  m.inductionOn fun _ => DHashMap.contains_of_contains_map

@[simp, grind =]
theorem mem_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ m.map f ↔ k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_map

theorem mem_of_mem_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ m.map f → k ∈ m :=
  m.inductionOn fun _ => DHashMap.mem_of_mem_map

@[simp, grind =]
theorem size_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} :
    (m.map f).size = m.size :=
  m.inductionOn fun _ => DHashMap.size_map

@[simp, grind =]
theorem get?_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).get? k = (m.get? k).map (f k) :=
  m.inductionOn fun _ => DHashMap.get?_map

@[simp, grind =]
theorem get_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (m.map f).get k h' = f k (m.get k (mem_of_mem_map h')) :=
  m.inductionOn (fun _ _ => DHashMap.get_map) h'

@[grind =]
theorem get!_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} [Inhabited (γ k)] :
    (m.map f).get! k = ((m.get? k).map (f k)).get! :=
  m.inductionOn fun _ => DHashMap.get!_map

@[grind =]
theorem getD_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {fallback : γ k} :
    (m.map f).getD k fallback = ((m.get? k).map (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.getD_map

@[simp, grind =]
theorem getKey?_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).getKey? k = m.getKey? k :=
  m.inductionOn fun _ => DHashMap.getKey?_map

@[simp, grind =]
theorem getKey_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (m.map f).getKey k h' = m.getKey k (mem_of_mem_map h') :=
  m.inductionOn (fun _ _ => DHashMap.getKey_map) h'

@[simp, grind =]
theorem getKey!_map [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).getKey! k = m.getKey! k :=
  m.inductionOn fun _ => DHashMap.getKey!_map

@[simp, grind =]
theorem getKeyD_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k fallback : α} :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback :=
  m.inductionOn fun _ => DHashMap.getKeyD_map

namespace Const

variable {β : Type v} {γ : Type w} {m : ExtDHashMap α fun _ => β}

@[simp, grind =]
theorem get?_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    Const.get? (m.map f) k = (Const.get? m k).map (f k) :=
  m.inductionOn fun _ => DHashMap.Const.get?_map

/-- Variant of `get?_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem get?_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    Const.get? (m.map f) k = (Const.get? m k).pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h')) :=
  m.inductionOn fun _ => DHashMap.Const.get?_map'

theorem get?_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get? (m.map f) k = (Const.get? m k).map (f k') :=
  m.inductionOn (fun _ h => DHashMap.Const.get?_map_of_getKey?_eq_some h) h

@[simp, grind =]
theorem get_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    Const.get (m.map f) k h' = f k (Const.get m k (mem_of_mem_map h')) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_map) h'

/-- Variant of `get_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem get_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    Const.get (m.map f) k h' =
      f (m.getKey k (mem_of_mem_map h')) (Const.get m k (mem_of_mem_map h')) :=
  m.inductionOn (fun _ _ => DHashMap.Const.get_map') h'

@[grind =] theorem get!_map [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (m.map f) k = ((Const.get? m k).map (f k)).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_map

/-- Variant of `get!_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem get!_map' [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (m.map f) k =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_mem h'))).get! :=
  m.inductionOn fun _ => DHashMap.Const.get!_map'

theorem get!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get! (m.map f) k = ((Const.get? m k).map (f k')).get! :=
  m.inductionOn (fun _ h => DHashMap.Const.get!_map_of_getKey?_eq_some h) h

@[grind =] theorem getD_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k)).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_map

/-- Variant of `getD_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getD_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (m.map f) k fallback =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  m.inductionOn fun _ => DHashMap.Const.getD_map'

theorem getD_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k')).getD fallback :=
  m.inductionOn (fun _ h => DHashMap.Const.getD_map_of_getKey?_eq_some h) h

end Const

end map

end Std.ExtDHashMap
