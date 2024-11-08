/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.Raw
import Std.Data.DHashMap.Internal.RawLemmas

/-!
# Dependent hash map lemmas

This file contains lemmas about `Std.Data.DHashMap`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

open Std.DHashMap.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {β : α → Type v} {_ : BEq α} {_ : Hashable α}

namespace Std.DHashMap

variable {m : DHashMap α β}

@[simp]
theorem isEmpty_empty {c} : (empty c : DHashMap α β).isEmpty :=
  Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : DHashMap α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).isEmpty = false :=
  Raw₀.isEmpty_insert _ m.2

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  Iff.rfl

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  Raw₀.contains_congr _ m.2 hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m := by
  simp [mem_iff_contains, contains_congr hab]

@[simp] theorem contains_empty {a : α} {c} : (empty c : DHashMap α β).contains a = false :=
  Raw₀.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : DHashMap α β) := by
  simp [mem_iff_contains]

@[simp] theorem contains_emptyc {a : α} : (∅ : DHashMap α β).contains a = false :=
  contains_empty

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : DHashMap α β) :=
  not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → m.contains a = false :=
  Raw₀.contains_of_isEmpty ⟨m.1, _⟩ m.2

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → ¬a ∈ m := by
  simpa [mem_iff_contains] using contains_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, m.contains a = true :=
  Raw₀.isEmpty_eq_false_iff_exists_contains_eq_true ⟨m.1, _⟩ m.2

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, a ∈ m := by
  simpa [mem_iff_contains] using isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, m.contains a = false :=
  Raw₀.isEmpty_iff_forall_contains ⟨m.1, _⟩ m.2

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m := by
  simpa [mem_iff_contains] using isEmpty_iff_forall_contains

@[simp] theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p m = m.insert p.1 p.2 := rfl

@[simp] theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : DHashMap α β).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  Raw₀.contains_insert ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m := by
  simp [mem_iff_contains, contains_insert]

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  Raw₀.contains_of_contains_insert ⟨m.1, _⟩ m.2

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m := by
  simpa [mem_iff_contains, -contains_insert] using contains_of_contains_insert

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).contains k :=
  Raw₀.contains_insert_self ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insert k v := by
  simp [mem_iff_contains, contains_insert_self]

@[simp]
theorem size_empty {c} : (empty c : DHashMap α β).size = 0 :=
  Raw₀.size_empty

@[simp]
theorem size_emptyc : (∅ : DHashMap α β).size = 0 :=
  size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) := rfl

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  Raw₀.size_insert ⟨m.1, _⟩ m.2

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insert k v).size :=
  Raw₀.size_le_size_insert ⟨m.1, _⟩ m.2

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).size ≤ m.size + 1 :=
  Raw₀.size_insert_le ⟨m.1, _⟩ m.2

@[simp]
theorem erase_empty {k : α} {c : Nat} : (empty c : DHashMap α β).erase k = empty c :=
  Subtype.eq (congrArg Subtype.val (Raw₀.erase_empty (k := k)) :) -- Lean code is happy

@[simp]
theorem erase_emptyc {k : α} : (∅ : DHashMap α β).erase k = ∅ :=
  erase_empty

@[simp]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  Raw₀.isEmpty_erase _ m.2

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  Raw₀.contains_erase ⟨m.1, _⟩ m.2

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [mem_iff_contains, contains_erase]

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  Raw₀.contains_of_contains_erase ⟨m.1, _⟩ m.2

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m := by
  simp

theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  Raw₀.size_erase _ m.2

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  Raw₀.size_erase_le _ m.2

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  Raw₀.size_le_size_erase ⟨m.1, _⟩ m.2

@[simp]
theorem containsThenInsert_fst {k : α} {v : β k} : (m.containsThenInsert k v).1 = m.contains k :=
  Raw₀.containsThenInsert_fst _

@[simp]
theorem containsThenInsert_snd {k : α} {v : β k} : (m.containsThenInsert k v).2 = m.insert k v :=
  Subtype.eq <| (congrArg Subtype.val (Raw₀.containsThenInsert_snd _ (k := k)) :)

@[simp]
theorem containsThenInsertIfNew_fst {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  Raw₀.containsThenInsertIfNew_fst _

@[simp]
theorem containsThenInsertIfNew_snd {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  Subtype.eq <| (congrArg Subtype.val (Raw₀.containsThenInsertIfNew_snd _ (k := k)) :)

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} {c} : (empty c : DHashMap α β).get? a = none :=
  Raw₀.get?_empty

@[simp]
theorem get?_emptyc [LawfulBEq α] {a : α} : (∅ : DHashMap α β).get? a = none :=
  get?_empty

theorem get?_of_isEmpty [LawfulBEq α] {a : α} : m.isEmpty = true → m.get? a = none :=
  Raw₀.get?_of_isEmpty ⟨m.1, _⟩ m.2

theorem get?_insert [LawfulBEq α] {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a :=
  Raw₀.get?_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get?_insert_self [LawfulBEq α] {k : α} {v : β k} : (m.insert k v).get? k = some v :=
  Raw₀.get?_insert_self ⟨m.1, _⟩ m.2

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome :=
  Raw₀.contains_eq_isSome_get? ⟨m.1, _⟩ m.2

theorem get?_eq_none_of_contains_eq_false [LawfulBEq α] {a : α} :
    m.contains a = false → m.get? a = none :=
  Raw₀.get?_eq_none ⟨m.1, _⟩ m.2

theorem get?_eq_none [LawfulBEq α] {a : α} : ¬a ∈ m → m.get? a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false

theorem get?_erase [LawfulBEq α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  Raw₀.get?_erase ⟨m.1, _⟩ m.2

@[simp]
theorem get?_erase_self [LawfulBEq α] {k : α} : (m.erase k).get? k = none :=
  Raw₀.get?_erase_self ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem get?_empty {a : α} {c} : get? (empty c : DHashMap α (fun _ => β)) a = none :=
  Raw₀.Const.get?_empty

@[simp]
theorem get?_emptyc {a : α} : get? (∅ : DHashMap α (fun _ => β)) a = none :=
  get?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → get? m a = none :=
  Raw₀.Const.get?_of_isEmpty ⟨m.1, _⟩ m.2

theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a :=
  Raw₀.Const.get?_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get? (m.insert k v) k = some v :=
  Raw₀.Const.get?_insert_self ⟨m.1, _⟩ m.2

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (get? m a).isSome :=
  Raw₀.Const.contains_eq_isSome_get? ⟨m.1, _⟩ m.2

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → get? m a = none :=
  Raw₀.Const.get?_eq_none ⟨m.1, _⟩ m.2

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α } : ¬a ∈ m → get? m a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false

theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a :=
  Raw₀.Const.get?_erase ⟨m.1, _⟩ m.2

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : get? (m.erase k) k = none :=
  Raw₀.Const.get?_erase_self ⟨m.1, _⟩ m.2

theorem get?_eq_get? [LawfulBEq α] {a : α} : get? m a = m.get? a :=
  Raw₀.Const.get?_eq_get? ⟨m.1, _⟩ m.2

theorem get?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : get? m a = get? m b :=
  Raw₀.Const.get?_congr ⟨m.1, _⟩ m.2 hab

end Const

theorem get_insert [LawfulBEq α] {k a : α} {v : β k} {h₁} :
    (m.insert k v).get a h₁ =
      if h₂ : k == a then
        cast (congrArg β (eq_of_beq h₂)) v
      else
        m.get a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  Raw₀.get_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get_insert_self [LawfulBEq α] {k : α} {v : β k} :
    (m.insert k v).get k mem_insert_self = v :=
  Raw₀.get_insert_self ⟨m.1, _⟩ m.2

@[simp]
theorem get_erase [LawfulBEq α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  Raw₀.get_erase ⟨m.1, _⟩ m.2

theorem get?_eq_some_get [LawfulBEq α] {a : α} {h} : m.get? a = some (m.get a h) :=
  Raw₀.get?_eq_some_get ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v else get m a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  Raw₀.Const.get_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get (m.insert k v) k mem_insert_self = v :=
  Raw₀.Const.get_insert_self ⟨m.1, _⟩ m.2

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    get (m.erase k) a h' = get m a (mem_of_mem_erase h') :=
  Raw₀.Const.get_erase ⟨m.1, _⟩ m.2

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    get? m a = some (get m a h) :=
  Raw₀.Const.get?_eq_some_get ⟨m.1, _⟩ m.2

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h :=
  Raw₀.Const.get_eq_get ⟨m.1, _⟩ m.2

theorem get_congr [LawfulBEq α] {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((mem_congr hab).1 h') :=
  Raw₀.Const.get_congr ⟨m.1, _⟩ m.2 hab

end Const

@[simp]
theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] {c} :
    (empty c : DHashMap α β).get! a = default :=
  Raw₀.get!_empty

@[simp]
theorem get!_emptyc [LawfulBEq α] {a : α} [Inhabited (β a)] :
    (∅ : DHashMap α β).get! a = default :=
  get!_empty

theorem get!_of_isEmpty [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.isEmpty = true → m.get! a = default :=
  Raw₀.get!_of_isEmpty ⟨m.1, _⟩ m.2

theorem get!_insert [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insert k v).get! a =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.get! a :=
  Raw₀.get!_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get!_insert_self [LawfulBEq α] {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b :=
  Raw₀.get!_insert_self ⟨m.1, _⟩ m.2

theorem get!_eq_default_of_contains_eq_false [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default :=
  Raw₀.get!_eq_default ⟨m.1, _⟩ m.2

theorem get!_eq_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    ¬a ∈ m → m.get! a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false

theorem get!_erase [LawfulBEq α] {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a :=
  Raw₀.get!_erase ⟨m.1, _⟩ m.2

@[simp]
theorem get!_erase_self [LawfulBEq α] {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default :=
  Raw₀.get!_erase_self ⟨m.1, _⟩ m.2

theorem get?_eq_some_get!_of_contains [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) :=
  Raw₀.get?_eq_some_get! ⟨m.1, _⟩ m.2

theorem get?_eq_some_get! [LawfulBEq α] {a : α} [Inhabited (β a)] :
    a ∈ m → m.get? a = some (m.get! a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains

theorem get!_eq_get!_get? [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! :=
  Raw₀.get!_eq_get!_get? ⟨m.1, _⟩ m.2

theorem get_eq_get! [LawfulBEq α] {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a :=
  Raw₀.get_eq_get! ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem get!_empty [Inhabited β] {a : α} {c} :
    get! (empty c : DHashMap α (fun _ => β)) a = default :=
  Raw₀.Const.get!_empty

@[simp]
theorem get!_emptyc [Inhabited β] {a : α} : get! (∅ : DHashMap α (fun _ => β)) a = default :=
  get!_empty

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.isEmpty = true → get! m a = default :=
  Raw₀.Const.get!_of_isEmpty ⟨m.1, _⟩ m.2

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a :=
  Raw₀.Const.get!_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} :
    get! (m.insert k v) k = v :=
  Raw₀.Const.get!_insert_self ⟨m.1, _⟩ m.2

theorem get!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → get! m a = default :=
  Raw₀.Const.get!_eq_default ⟨m.1, _⟩ m.2

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → get! m a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false

theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a :=
  Raw₀.Const.get!_erase ⟨m.1, _⟩ m.2

@[simp]
theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    get! (m.erase k) k = default :=
  Raw₀.Const.get!_erase_self ⟨m.1, _⟩ m.2

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → get? m a = some (get! m a) :=
  Raw₀.Const.get?_eq_some_get! ⟨m.1, _⟩ m.2

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → get? m a = some (get! m a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = (get? m a).get! :=
  Raw₀.Const.get!_eq_get!_get? ⟨m.1, _⟩ m.2

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h} :
    get m a h = get! m a :=
  Raw₀.Const.get_eq_get! ⟨m.1, _⟩ m.2

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] {a : α} :
    get! m a = m.get! a :=
  Raw₀.Const.get!_eq_get! ⟨m.1, _⟩ m.2

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    get! m a = get! m b :=
  Raw₀.Const.get!_congr ⟨m.1, _⟩ m.2 hab

end Const

@[simp]
theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} {c} :
    (empty c : DHashMap α β).getD a fallback = fallback :=
  Raw₀.getD_empty

@[simp]
theorem getD_emptyc [LawfulBEq α] {a : α} {fallback : β a} :
    (∅ : DHashMap α β).getD a fallback = fallback :=
  getD_empty

theorem getD_of_isEmpty [LawfulBEq α] {a : α} {fallback : β a} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  Raw₀.getD_of_isEmpty ⟨m.1, _⟩ m.2

theorem getD_insert [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insert k v).getD a fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.getD a fallback :=
  Raw₀.getD_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getD_insert_self [LawfulBEq α] {k : α} {fallback v : β k} :
    (m.insert k v).getD k fallback = v :=
  Raw₀.getD_insert_self ⟨m.1, _⟩ m.2

theorem getD_eq_fallback_of_contains_eq_false [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback :=
  Raw₀.getD_eq_fallback ⟨m.1, _⟩ m.2

theorem getD_eq_fallback [LawfulBEq α] {a : α} {fallback : β a} :
    ¬a ∈ m → m.getD a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false

theorem getD_erase [LawfulBEq α] {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback :=
  Raw₀.getD_erase ⟨m.1, _⟩ m.2

@[simp]
theorem getD_erase_self [LawfulBEq α] {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback :=
  Raw₀.getD_erase_self ⟨m.1, _⟩ m.2

theorem get?_eq_some_getD_of_contains [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) :=
  Raw₀.get?_eq_some_getD ⟨m.1, _⟩ m.2

theorem get?_eq_some_getD [LawfulBEq α] {a : α} {fallback : β a} :
    a ∈ m → m.get? a = some (m.getD a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains

theorem getD_eq_getD_get? [LawfulBEq α] {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback :=
  Raw₀.getD_eq_getD_get? ⟨m.1, _⟩ m.2

theorem get_eq_getD [LawfulBEq α] {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback :=
  Raw₀.get_eq_getD ⟨m.1, _⟩ m.2

theorem get!_eq_getD_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default :=
  Raw₀.get!_eq_getD_default ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem getD_empty {a : α} {fallback : β} {c} :
    getD (empty c : DHashMap α (fun _ => β)) a fallback = fallback :=
  Raw₀.Const.getD_empty

@[simp]
theorem getD_emptyc {a : α} {fallback : β} :
    getD (∅ : DHashMap α (fun _ => β)) a fallback = fallback :=
  getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.isEmpty = true → getD m a fallback = fallback :=
  Raw₀.Const.getD_of_isEmpty ⟨m.1, _⟩ m.2

theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback :=
  Raw₀.Const.getD_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback v : β} :
   getD (m.insert k v) k fallback = v :=
  Raw₀.Const.getD_insert_self ⟨m.1, _⟩ m.2

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : β} : m.contains a = false → getD m a fallback = fallback :=
  Raw₀.Const.getD_eq_fallback ⟨m.1, _⟩ m.2

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → getD m a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false

theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback :=
  Raw₀.Const.getD_erase ⟨m.1, _⟩ m.2

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback :=
  Raw₀.Const.getD_erase_self ⟨m.1, _⟩ m.2

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) :=
  Raw₀.Const.get?_eq_some_getD ⟨m.1, _⟩ m.2

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → get? m a = some (getD m a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback :=
  Raw₀.Const.getD_eq_getD_get? ⟨m.1, _⟩ m.2

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback :=
  Raw₀.Const.get_eq_getD ⟨m.1, _⟩ m.2

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = getD m a default :=
  Raw₀.Const.get!_eq_getD_default ⟨m.1, _⟩ m.2

theorem getD_eq_getD [LawfulBEq α] {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback :=
  Raw₀.Const.getD_eq_getD ⟨m.1, _⟩ m.2

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    getD m a fallback = getD m b fallback :=
  Raw₀.Const.getD_congr ⟨m.1, _⟩ m.2 hab

end Const

@[simp]
theorem getKey?_empty {a : α} {c} : (empty c : DHashMap α β).getKey? a = none :=
  Raw₀.getKey?_empty

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : DHashMap α β).getKey? a = none :=
  Raw₀.getKey?_empty

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  Raw₀.getKey?_of_isEmpty ⟨m.1, _⟩ m.2

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  Raw₀.getKey?_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k :=
  Raw₀.getKey?_insert_self ⟨m.1, _⟩ m.2

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  Raw₀.contains_eq_isSome_getKey? ⟨m.1, _⟩ m.2

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey? a = none :=
  Raw₀.getKey?_eq_none ⟨m.1, _⟩ m.2

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none := by
  simpa [mem_iff_contains] using getKey?_eq_none_of_contains_eq_false

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a :=
  Raw₀.getKey?_erase ⟨m.1, _⟩ m.2

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).getKey? k = none :=
  Raw₀.getKey?_erase_self ⟨m.1, _⟩ m.2

theorem getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  Raw₀.getKey_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).getKey k mem_insert_self = k :=
  Raw₀.getKey_insert_self ⟨m.1, _⟩ m.2

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  Raw₀.getKey_erase ⟨m.1, _⟩ m.2

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α}
    {h} :
    m.getKey? a = some (m.getKey a h) :=
  Raw₀.getKey?_eq_some_getKey ⟨m.1, _⟩ m.2

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} {c} :
    (empty c : DHashMap α β).getKey! a = default :=
  Raw₀.getKey!_empty

@[simp]
theorem getKey!_emptyc [Inhabited α] {a : α} :
    (∅ : DHashMap α β).getKey! a = default :=
  getKey!_empty

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  Raw₀.getKey!_of_isEmpty ⟨m.1, _⟩ m.2

theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β k} :
    (m.insert k v).getKey! a =
      if k == a then k else m.getKey! a :=
  Raw₀.getKey!_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {b : β a} :
    (m.insert a b).getKey! a = a :=
  Raw₀.getKey!_insert_self ⟨m.1, _⟩ m.2

theorem getKey!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {a : α} :
    m.contains a = false → m.getKey! a = default :=
  Raw₀.getKey!_eq_default ⟨m.1, _⟩ m.2

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    ¬a ∈ m → m.getKey! a = default := by
  simpa [mem_iff_contains] using getKey!_eq_default_of_contains_eq_false

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a :=
  Raw₀.getKey!_erase ⟨m.1, _⟩ m.2

@[simp]
theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} :
    (m.erase k).getKey! k = default :=
  Raw₀.getKey!_erase_self ⟨m.1, _⟩ m.2

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) :=
  Raw₀.getKey?_eq_some_getKey! ⟨m.1, _⟩ m.2

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKey!_of_contains

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = (m.getKey? a).get! :=
  Raw₀.getKey!_eq_get!_getKey? ⟨m.1, _⟩ m.2

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h} :
    m.getKey a h = m.getKey! a :=
  Raw₀.getKey_eq_getKey! ⟨m.1, _⟩ m.2

@[simp]
theorem getKeyD_empty {a fallback : α} {c} :
    (empty c : DHashMap α β).getKeyD a fallback = fallback :=
  Raw₀.getKeyD_empty

@[simp]
theorem getKeyD_emptyc {a fallback : α} :
    (∅ : DHashMap α β).getKeyD a fallback = fallback :=
  getKeyD_empty

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  Raw₀.getKeyD_of_isEmpty ⟨m.1, _⟩ m.2

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β k} :
    (m.insert k v).getKeyD a fallback =
      if k == a then k else m.getKeyD a fallback :=
  Raw₀.getKeyD_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] {k fallback : α} {v : β k} :
    (m.insert k v).getKeyD k fallback = k :=
  Raw₀.getKeyD_insert_self ⟨m.1, _⟩ m.2

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback :=
  Raw₀.getKeyD_eq_fallback ⟨m.1, _⟩ m.2

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback := by
  simpa [mem_iff_contains] using getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback :=
  Raw₀.getKeyD_erase ⟨m.1, _⟩ m.2

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback :=
  Raw₀.getKeyD_erase_self ⟨m.1, _⟩ m.2

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) :=
  Raw₀.getKey?_eq_some_getKeyD ⟨m.1, _⟩ m.2

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKeyD_of_contains

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback :=
  Raw₀.getKeyD_eq_getD_getKey? ⟨m.1, _⟩ m.2

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] {a fallback : α} {h} :
    m.getKey a h = m.getKeyD a fallback :=
  Raw₀.getKey_eq_getKeyD ⟨m.1, _⟩ m.2

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.getKey! a = m.getKeyD a default :=
  Raw₀.getKey!_eq_getKeyD_default ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).isEmpty = false :=
  Raw₀.isEmpty_insertIfNew ⟨m.1, _⟩ m.2

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  Raw₀.contains_insertIfNew ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m := by
  simp [mem_iff_contains, contains_insertIfNew]

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).contains k :=
  Raw₀.contains_insertIfNew_self ⟨m.1, _⟩ m.2

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insertIfNew k v := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_insertIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  Raw₀.contains_of_contains_insertIfNew ⟨m.1, _⟩ m.2

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_of_contains_insertIfNew

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  Raw₀.contains_of_contains_insertIfNew' ⟨m.1, _⟩ m.2

/-- This is a restatement of `mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_of_contains_insertIfNew'

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  Raw₀.size_insertIfNew ⟨m.1, _⟩ m.2

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insertIfNew k v).size :=
  Raw₀.size_le_size_insertIfNew ⟨m.1, _⟩ m.2

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  Raw₀.size_insertIfNew_le _ m.2

theorem get?_insertIfNew [LawfulBEq α] {k a : α} {v : β k} : (m.insertIfNew k v).get? a =
    if h : k == a ∧ ¬k ∈ m then some (cast (congrArg β (eq_of_beq h.1)) v) else m.get? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.get?_insertIfNew ⟨m.1, _⟩ m.2

theorem get_insertIfNew [LawfulBEq α] {k a : α} {v : β k} {h₁} : (m.insertIfNew k v).get a h₁ =
    if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v else m.get a
      (mem_of_mem_insertIfNew' h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.get_insertIfNew ⟨m.1, _⟩ m.2

theorem get!_insertIfNew [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v else m.get! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.get!_insertIfNew ⟨m.1, _⟩ m.2

theorem getD_insertIfNew [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.getD_insertIfNew ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some v else get? m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.get?_insertIfNew ⟨m.1, _⟩ m.2

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else get m a (mem_of_mem_insertIfNew' h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.get_insertIfNew ⟨m.1, _⟩ m.2

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then v else get! m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.get!_insertIfNew ⟨m.1, _⟩ m.2

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then v else getD m a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.getD_insertIfNew ⟨m.1, _⟩ m.2

end Const

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a := by
  simp [mem_iff_contains, contains_insertIfNew]
  exact Raw₀.getKey?_insertIfNew ⟨m.1, _⟩ m.2

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂) := by
  simp [mem_iff_contains, contains_insertIfNew]
  exact Raw₀.getKey_insertIfNew ⟨m.1, _⟩ m.2

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β k} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a := by
  simp [mem_iff_contains, contains_insertIfNew]
  exact Raw₀.getKey!_insertIfNew ⟨m.1, _⟩ m.2

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β k} :
    getKeyD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback := by
  simp [mem_iff_contains, contains_insertIfNew]
  exact Raw₀.getKeyD_insertIfNew ⟨m.1, _⟩ m.2


@[simp]
theorem getThenInsertIfNew?_fst [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k :=
  Raw₀.getThenInsertIfNew?_fst _

@[simp]
theorem getThenInsertIfNew?_snd [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v :=
  Subtype.eq <| (congrArg Subtype.val (Raw₀.getThenInsertIfNew?_snd _ (k := k)) :)

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem getThenInsertIfNew?_fst {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k :=
  Raw₀.Const.getThenInsertIfNew?_fst _

@[simp]
theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  Subtype.eq <| (congrArg Subtype.val (Raw₀.Const.getThenInsertIfNew?_snd _ (k := k)) :)

end Const

@[simp]
theorem length_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.length = m.size :=
  Raw₀.length_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α]:
    m.keys.isEmpty = m.isEmpty  :=
  Raw₀.isEmpty_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] {k : α} :
    m.keys.contains k = m.contains k :=
  Raw₀.contains_keys ⟨m.1, _⟩ m.2

@[simp]
theorem mem_keys [LawfulBEq α] [LawfulHashable α] {k : α} :
    k ∈ m.keys ↔ k ∈ m := by 
  rw [mem_iff_contains]
  exact Raw₀.mem_keys ⟨m.1, _⟩ m.2

theorem distinct_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.Pairwise (fun a b => (a == b) = false) := 
  Raw₀.distinct_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

end Std.DHashMap
