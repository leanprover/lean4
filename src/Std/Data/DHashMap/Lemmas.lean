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

universe u v w

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

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).contains k := by simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insert k v := by simp

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

theorem get_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) {h'} :
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

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.getKey? k).all (· == k) :=
  Raw₀.getKey?_beq ⟨m.1, _⟩ m.2

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] {k k' : α} (h : k == k') :
    m.getKey? k = m.getKey? k' :=
  Raw₀.getKey?_congr ⟨m.1, _⟩ m.2 h

theorem getKey?_eq_some_of_contains [LawfulBEq α] {k : α} (h : m.contains k) :
    m.getKey? k = some k :=
  Raw₀.getKey?_eq_some ⟨m.1, _⟩ m.2 h

theorem getKey?_eq_some [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k = some k := by
  simpa only [mem_iff_contains] using getKey?_eq_some_of_contains h

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

theorem getKey_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.getKey k h == k :=
  Raw₀.getKey_beq ⟨m.1, _⟩ m.2 h

theorem getKey_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) :=
  Raw₀.getKey_congr ⟨m.1, _⟩ m.2 h h₁

theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k :=
  Raw₀.getKey_eq ⟨m.1, _⟩ m.2 h

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

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : k == k') :
    m.getKey! k = m.getKey! k' :=
  Raw₀.getKey!_congr ⟨m.1, _⟩ m.2 h

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k) :
    m.getKey! k = k :=
  Raw₀.getKey!_eq_of_contains ⟨m.1, _⟩ m.2 h

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.getKey! k = k :=
  getKey!_eq_of_contains h

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

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] {k k' fallback : α}
    (h : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback :=
  Raw₀.getKeyD_congr ⟨m.1, _⟩ m.2 h

theorem getKeyD_eq_of_contains [LawfulBEq α] {k fallback : α} (h : m.contains k) :
    m.getKeyD k fallback = k :=
  Raw₀.getKeyD_eq_of_contains ⟨m.1, _⟩ m.2 h

theorem getKeyD_eq_of_mem [LawfulBEq α] {k fallback : α} (h : k ∈ m) :
    m.getKeyD k fallback = k :=
  getKeyD_eq_of_contains h

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

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  Raw₀.contains_of_contains_insertIfNew' ⟨m.1, _⟩ m.2

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
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
theorem mem_keys [LawfulBEq α] {k : α} :
    k ∈ m.keys ↔ k ∈ m := by
  rw [mem_iff_contains]
  exact Raw₀.mem_keys ⟨m.1, _⟩ m.2

theorem distinct_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.Pairwise (fun a b => (a == b) = false) :=
  Raw₀.distinct_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.1.toList.map Sigma.fst = m.1.keys  :=
  Raw₀.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[simp, deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_sigma_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.1.toList.map Sigma.fst = m.1.keys  :=
  Raw₀.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.length = m.size :=
  Raw₀.length_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.isEmpty = m.isEmpty :=
  Raw₀.isEmpty_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem mem_toList_iff_get?_eq_some [LawfulBEq α]
    {k : α} {v : β k} :
    ⟨k, v⟩ ∈ m.toList ↔ m.get? k = some v :=
  Raw₀.mem_toList_iff_get?_eq_some ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem find?_toList_eq_some_iff_get?_eq_some [LawfulBEq α]
    {k : α} {v : β k} :
    m.toList.find? (·.1 == k) = some ⟨k, v⟩ ↔ m.get? k = some v :=
  Raw₀.find?_toList_eq_some_iff_get?_eq_some ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {k : α} :
    m.toList.find? (·.1 == k) = none ↔ m.contains k = false :=
  Raw₀.find?_toList_eq_none_iff_contains_eq_false ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem find?_toList_eq_none_iff_not_mem [EquivBEq α] [LawfulHashable α]
    {k : α} :
    m.toList.find? (·.1 == k) = none ↔ ¬ k ∈ m := by
  simp only [Bool.not_eq_true, mem_iff_contains]
  apply Raw₀.find?_toList_eq_none_iff_contains_eq_false ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.Pairwise (fun a b => (a.1 == b.1) = false) :=
  Raw₀.distinct_keys_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    (toList m).map Prod.fst = m.keys :=
  Raw₀.Const.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[simp, deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_prod_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    (toList m).map Prod.fst = m.keys :=
  Raw₀.Const.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] :
    (toList m).length = m.size :=
  Raw₀.Const.length_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    (toList m).isEmpty = m.isEmpty :=
  Raw₀.Const.isEmpty_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem mem_toList_iff_get?_eq_some [LawfulBEq α]
    {k : α} {v : β} :
    (k, v) ∈ toList m ↔ get? m k = some v :=
  Raw₀.Const.mem_toList_iff_get?_eq_some ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} :
    (k, v) ∈ toList m ↔ m.getKey? k = some k ∧ get? m k = some v :=
  Raw₀.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem get?_eq_some_iff_exists_beq_and_mem_toList [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} :
    get? m k = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ toList m :=
  Raw₀.Const.get?_eq_some_iff_exists_beq_and_mem_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
    [EquivBEq α] [LawfulHashable α] {k k' : α} {v : β} :
    (toList m).find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ get? m k = some v :=
  Raw₀.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
    ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {k : α} :
    (toList m).find? (·.1 == k) = none ↔ m.contains k = false :=
  Raw₀.Const.find?_toList_eq_none_iff_contains_eq_false ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp]
theorem find?_toList_eq_none_iff_not_mem [EquivBEq α] [LawfulHashable α]
    {k : α} :
    (toList m).find? (·.1 == k) = none ↔ ¬ k ∈ m := by
  simp only [Bool.not_eq_true, mem_iff_contains]
  apply Raw₀.Const.find?_toList_eq_none_iff_contains_eq_false ⟨m.1, m.2.size_buckets_pos⟩ m.2

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] :
    (toList m).Pairwise (fun a b => (a.1 == b.1) = false) :=
  Raw₀.Const.distinct_keys_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

end Const

section monadic

variable {m : DHashMap α β} {δ : Type w} {m' : Type w → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM (fun a b => f a b.1 b.2) init :=
  Raw₀.foldM_eq_foldlM_toList ⟨m.1, m.2.size_buckets_pos⟩

theorem fold_eq_foldl_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    m.fold f init = m.toList.foldl (fun a b => f a b.1 b.2) init :=
  Raw₀.fold_eq_foldl_toList ⟨m.1, m.2.size_buckets_pos⟩

@[simp]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : (a : α) → β a → m' PUnit} :
    DHashMap.forM f m = ForM.forM m (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : (a : α) × β a → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  Raw₀.forM_eq_forM_toList ⟨m.1, m.2.size_buckets_pos⟩

@[simp]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ} :
    DHashMap.forIn f init m = ForIn.forIn m init (fun a b => f a.1 a.2 b) := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : (a : α) × β a → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  Raw₀.forIn_eq_forIn_toList ⟨m.1, m.2.size_buckets_pos⟩

theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m'] {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init :=
  Raw₀.foldM_eq_foldlM_keys ⟨m.1, m.2.size_buckets_pos⟩

theorem fold_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  Raw₀.fold_eq_foldl_keys ⟨m.1, m.2.size_buckets_pos⟩

theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    ForM.forM m (fun a => f a.1) = m.keys.forM f :=
  Raw₀.forM_eq_forM_keys ⟨m.1, m.2.size_buckets_pos⟩

theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m'] {f : α → δ → m' (ForInStep δ)}
    {init : δ} :
    ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f :=
  Raw₀.forIn_eq_forIn_keys ⟨m.1, m.2.size_buckets_pos⟩

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β → m' δ} {init : δ} :
    m.foldM f init = (Const.toList m).foldlM (fun a b => f a b.1 b.2) init :=
  Raw₀.Const.foldM_eq_foldlM_toList ⟨m.1, m.2.size_buckets_pos⟩

theorem fold_eq_foldl_toList {f : δ → (a : α) → β → δ} {init : δ} :
    m.fold f init = (Const.toList m).foldl (fun a b => f a b.1 b.2) init :=
  Raw₀.Const.fold_eq_foldl_toList ⟨m.1, m.2.size_buckets_pos⟩

theorem forM_eq_forMUncurried [Monad m'] [LawfulMonad m'] {f : α → β → m' PUnit} :
    DHashMap.forM f m = forMUncurried (fun a => f a.1 a.2) m := rfl

theorem forMUncurried_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : α × β → m' PUnit} :
    Const.forMUncurried f m = (Const.toList m).forM f :=
  Raw₀.Const.forM_eq_forM_toList ⟨m.1, m.2.size_buckets_pos⟩

/--
Deprecated, use `forMUncurried_eq_forM_toList` together with `forM_eq_forMUncurried` instead.
-/
@[deprecated forMUncurried_eq_forM_toList (since := "2025-03-02")]
theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : α → β → m' PUnit} :
    DHashMap.forM f m = (Const.toList m).forM (fun a => f a.1 a.2) :=
  Raw₀.Const.forM_eq_forM_toList ⟨m.1, m.2.size_buckets_pos⟩

theorem forIn_eq_forInUncurried [Monad m'] [LawfulMonad m']
    {f : α → β → δ → m' (ForInStep δ)} {init : δ} :
    DHashMap.forIn f init m = forInUncurried (fun a b => f a.1 a.2 b) init m := rfl

theorem forInUncurried_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : α × β → δ → m' (ForInStep δ)} {init : δ} :
    Const.forInUncurried f init m = ForIn.forIn (Const.toList m) init f :=
  Raw₀.Const.forIn_eq_forIn_toList ⟨m.1, m.2.size_buckets_pos⟩

/--
Deprecated, use `forInUncurried_eq_forIn_toList` together with `forIn_eq_forInUncurried` instead.
-/
@[deprecated forInUncurried_eq_forIn_toList (since := "2025-03-02")]
theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : α × β → δ → m' (ForInStep δ)} {init : δ} :
    Const.forInUncurried f init m = ForIn.forIn (Const.toList m) init f :=
  Raw₀.Const.forIn_eq_forIn_toList ⟨m.1, m.2.size_buckets_pos⟩

variable {m : DHashMap α (fun _ => Unit)}

@[deprecated DHashMap.foldM_eq_foldlM_keys (since := "2025-02-28")]
theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init :=
  Raw₀.foldM_eq_foldlM_keys ⟨m.1, m.2.size_buckets_pos⟩

@[deprecated DHashMap.fold_eq_foldl_keys (since := "2025-02-28")]
theorem fold_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  Raw₀.fold_eq_foldl_keys ⟨m.1, m.2.size_buckets_pos⟩

@[deprecated DHashMap.forM_eq_forM_keys (since := "2025-02-28")]
theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.forM (fun a _ => f a) = m.keys.forM f :=
  Raw₀.forM_eq_forM_keys ⟨m.1, m.2.size_buckets_pos⟩

@[deprecated DHashMap.forIn_eq_forIn_keys (since := "2025-02-28")]
theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn (fun a _ d => f a d) init = ForIn.forIn m.keys init f :=
  Raw₀.forIn_eq_forIn_keys ⟨m.1, m.2.size_buckets_pos⟩

end Const

end monadic

@[simp]
theorem insertMany_nil :
    m.insertMany [] = m :=
  Subtype.eq (congrArg Subtype.val (Raw₀.insertMany_nil ⟨m.1, m.2.size_buckets_pos⟩) :)

@[simp]
theorem insertMany_list_singleton {k : α} {v : β k} :
    m.insertMany [⟨k, v⟩] = m.insert k v :=
  Subtype.eq (congrArg Subtype.val (Raw₀.insertMany_list_singleton ⟨m.1, m.2.size_buckets_pos⟩) :)

theorem insertMany_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    m.insertMany (⟨k, v⟩ :: l) = (m.insert k v).insertMany l :=
  Subtype.eq (congrArg Subtype.val (Raw₀.insertMany_cons ⟨m.1, m.2.size_buckets_pos⟩) :)

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).contains k = (m.contains k || (l.map Sigma.fst).contains k) :=
  Raw₀.contains_insertMany_list ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ m.insertMany l ↔ k ∈ m ∨ (l.map Sigma.fst).contains k := by
  simp [mem_iff_contains]

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}  (mem : k ∈ m.insertMany l)
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    k ∈ m :=
  Raw₀.contains_of_contains_insertMany_list ⟨m.1, _⟩ m.2 mem contains_eq_false

theorem get?_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).get? k = m.get? k :=
  Raw₀.get?_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get?_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) :=
  Raw₀.get?_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem get_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h} :
    (m.insertMany l).get k h =
      m.get k (mem_of_mem_insertMany_list h contains_eq_false) :=
  Raw₀.get_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (m.insertMany l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.get_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).get! k = m.get! k :=
  Raw₀.get!_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get!_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.get!_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getD k fallback = m.getD k fallback :=
  Raw₀.getD_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getD_insertMany_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.getD_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey? k = m.getKey? k :=
  Raw₀.getKey?_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey? k' = some k :=
  Raw₀.getKey?_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h} :
    (m.insertMany l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) :=
  Raw₀.getKey_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (m.insertMany l).getKey k' h = k :=
  Raw₀.getKey_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey! k = m.getKey! k :=
  Raw₀.getKey!_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey! k' = k :=
  Raw₀.getKey!_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKeyD k fallback = m.getKeyD k fallback :=
  Raw₀.getKeyD_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKeyD k' fallback = k :=
  Raw₀.getKeyD_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Sigma.fst).contains a = false) →
      (m.insertMany l).size = m.size + l.length :=
  Raw₀.size_insertMany_list ⟨m.1, _⟩ m.2 distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    m.size ≤ (m.insertMany l).size :=
  Raw₀.size_le_size_insertMany_list ⟨m.1, _⟩ m.2

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (m.insertMany l).size ≤ m.size + l.length :=
  Raw₀.size_insertMany_list_le ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (m.insertMany l).isEmpty = (m.isEmpty && l.isEmpty) :=
  Raw₀.isEmpty_insertMany_list ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem insertMany_nil :
    insertMany m [] = m :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertMany_nil ⟨m.1, m.2.size_buckets_pos⟩) :)

@[simp]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v :=
  Subtype.eq (congrArg Subtype.val
    (Raw₀.Const.insertMany_list_singleton ⟨m.1, m.2.size_buckets_pos⟩) :)

theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertMany_cons ⟨m.1, m.2.size_buckets_pos⟩) :)

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (Const.insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) :=
  Raw₀.Const.contains_insertMany_list ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k := by
  simp [mem_iff_contains]

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} (mem : k ∈ insertMany m l)
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    k ∈ m :=
  Raw₀.Const.contains_of_contains_insertMany_list ⟨m.1, _⟩ m.2 mem contains_eq_false

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k :=
  Raw₀.Const.getKey?_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k :=
  Raw₀.Const.getKey?_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    (insertMany m l).getKey k h =
      m.getKey k (mem_of_mem_insertMany_list h contains_eq_false) :=
  Raw₀.Const.getKey_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (insertMany m l).getKey k' h = k :=
  Raw₀.Const.getKey_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k :=
  Raw₀.Const.getKey!_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k :=
  Raw₀.Const.getKey!_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback :=
  Raw₀.Const.getKeyD_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k :=
  Raw₀.Const.getKeyD_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length :=
  Raw₀.Const.size_insertMany_list ⟨m.1, _⟩ m.2 distinct

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    m.size ≤ (insertMany m l).size :=
  Raw₀.Const.size_le_size_insertMany_list ⟨m.1, _⟩ m.2

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length :=
  Raw₀.Const.size_insertMany_list_le ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  Raw₀.Const.isEmpty_insertMany_list ⟨m.1, _⟩ m.2

theorem get?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l) k = get? m k :=
  Raw₀.Const.get?_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l) k' = v :=
  Raw₀.Const.get?_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem get_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h} :
    get (insertMany m l) k h = get m k (mem_of_mem_insertMany_list h contains_eq_false) :=
  Raw₀.Const.get_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h} :
    get (insertMany m l) k' h = v :=
  Raw₀.Const.get_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany m l) k = get! m k :=
  Raw₀.Const.get!_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany m l) k' = v :=
  Raw₀.Const.get!_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback :=
  Raw₀.Const.getD_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v :=
  Raw₀.Const.getD_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

variable {m : DHashMap α (fun _ => Unit)}

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit m [] = m :=
  Subtype.eq (congrArg Subtype.val
    (Raw₀.Const.insertManyIfNewUnit_nil ⟨m.1, m.2.size_buckets_pos⟩) :)

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () :=
  Subtype.eq (congrArg Subtype.val
    (Raw₀.Const.insertManyIfNewUnit_list_singleton ⟨m.1, m.2.size_buckets_pos⟩) :)

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l :=
  Subtype.eq (congrArg Subtype.val
    (Raw₀.Const.insertManyIfNewUnit_cons ⟨m.1, m.2.size_buckets_pos⟩) :)

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) :=
  Raw₀.Const.contains_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k := by
  simp [mem_iff_contains]

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m :=
  Raw₀.Const.contains_of_contains_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2 contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit m l) k = none := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    ⟨m.1, _⟩ m.2 not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit m l) k' = some k := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_mem ⟨m.1, _⟩
    m.2 k_beq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (h' : k ∈ m) :
    getKey? (insertManyIfNewUnit m l) k = getKey? m k :=
  Raw₀.Const.getKey?_insertManyIfNewUnit_list_of_contains ⟨m.1, _⟩ m.2 h'

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (insertManyIfNewUnit m l) k' h = k := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains_eq_false_of_mem ⟨m.1, _⟩ m.2 k_beq
    not_mem distinct mem

theorem getKey_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (mem : k ∈ m) {h} :
    getKey (insertManyIfNewUnit m l) k h = getKey m k mem :=
  Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains ⟨m.1, _⟩ m.2 _

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    ⟨m.1, _⟩ m.2 not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_mem ⟨m.1, _⟩ m.2 k_beq
    not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) :
    getKey! (insertManyIfNewUnit m l) k = getKey! m k :=
  Raw₀.Const.getKey!_insertManyIfNewUnit_list_of_contains ⟨m.1, _⟩ m.2 mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit m l) k fallback = fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    ⟨m.1, _⟩ m.2 not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k := by
  simp only [mem_iff_contains, Bool.not_eq_true] at not_mem
  exact Raw₀.Const.getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_mem ⟨m.1, _⟩ m.2 k_beq
    not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α} (mem : k ∈ m) :
    getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback :=
  Raw₀.Const.getKeyD_insertManyIfNewUnit_list_of_contains ⟨m.1, _⟩ m.2 mem

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2 distinct

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size :=
  Raw₀.Const.size_le_size_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_list_le ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  Raw₀.Const.isEmpty_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2

theorem get?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit m l) k =
      if k ∈ m ∨ l.contains k then some () else none :=
  Raw₀.Const.get?_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2

theorem get_insertManyIfNewUnit_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit m l) k h = () :=
  Raw₀.Const.get_insertManyIfNewUnit_list ⟨m.1, _⟩

theorem get!_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit m l) k = () :=
  Raw₀.Const.get!_insertManyIfNewUnit_list ⟨m.1, _⟩

theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () := by
  simp

end Const

end DHashMap

namespace DHashMap

@[simp]
theorem ofList_nil :
    ofList ([] : List ((a : α) × (β a))) = ∅ :=
  Subtype.eq (congrArg Subtype.val (Raw₀.insertMany_empty_list_nil (α := α)) :)

@[simp]
theorem ofList_singleton {k : α} {v : β k} :
    ofList [⟨k, v⟩] = (∅: DHashMap α β).insert k v :=
  Subtype.eq (congrArg Subtype.val (Raw₀.insertMany_empty_list_singleton (α := α)) :)

theorem ofList_cons {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) = ((∅ : DHashMap α β).insert k v).insertMany tl :=
  Subtype.eq (congrArg Subtype.val (Raw₀.insertMany_empty_list_cons (α := α)) :)

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l).contains k = (l.map Sigma.fst).contains k :=
  Raw₀.contains_insertMany_empty_list

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l ↔ (l.map Sigma.fst).contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get? k = none :=
  Raw₀.get?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) :=
  Raw₀.get?_insertMany_empty_list_of_mem k_beq distinct mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.get_insertMany_empty_list_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get! k = default :=
  Raw₀.get!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.get!_insertMany_empty_list_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getD k fallback = fallback :=
  Raw₀.getD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.getD_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  Raw₀.getKey?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey? k' = some k :=
  Raw₀.getKey?_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  Raw₀.getKey_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  Raw₀.getKey!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey! k' = k :=
  Raw₀.getKey!_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  Raw₀.getKeyD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKeyD k' fallback = k :=
  Raw₀.getKeyD_insertMany_empty_list_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  Raw₀.size_insertMany_empty_list distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).size ≤ l.length :=
  Raw₀.size_insertMany_empty_list_le

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).isEmpty = l.isEmpty :=
  Raw₀.isEmpty_insertMany_empty_list

namespace Const

variable {β : Type v}

@[simp]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertMany_empty_list_nil (α:= α)) :)

@[simp]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : DHashMap α (fun _ => β)).insert k v :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertMany_empty_list_singleton (α:= α)) :)

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : DHashMap α (fun _ => β)).insert k v) tl :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertMany_empty_list_cons (α:= α)) :)

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  Raw₀.Const.contains_insertMany_empty_list

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ ofList l ↔ (l.map Prod.fst).contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l) k = none :=
  Raw₀.Const.get?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l) k' = some v :=
  Raw₀.Const.get?_insertMany_empty_list_of_mem k_beq distinct mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l) k' h = v :=
  Raw₀.Const.get_insertMany_empty_list_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l) k = (default : β) :=
  Raw₀.Const.get!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l) k' = v :=
  Raw₀.Const.get!_insertMany_empty_list_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback :=
  Raw₀.Const.getD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v :=
  Raw₀.Const.getD_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  Raw₀.Const.getKey?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k :=
  Raw₀.Const.getKey?_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  Raw₀.Const.getKey_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  Raw₀.Const.getKey!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k :=
  Raw₀.Const.getKey!_insertMany_empty_list_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  Raw₀.Const.getKeyD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k :=
  Raw₀.Const.getKeyD_insertMany_empty_list_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  Raw₀.Const.size_insertMany_empty_list distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).size ≤ l.length :=
  Raw₀.Const.size_insertMany_empty_list_le

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).isEmpty = l.isEmpty :=
  Raw₀.Const.isEmpty_insertMany_empty_list

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) = ∅ :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_empty_list_nil (α := α)) :)

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (∅ : DHashMap α (fun _ => Unit)).insertIfNew k () :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_empty_list_singleton (α := α)) :)

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      insertManyIfNewUnit ((∅ : DHashMap α (fun _ => Unit)).insertIfNew hd ()) tl :=
  Subtype.eq (congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_empty_list_cons (α := α)) :)

@[simp]
theorem contains_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k :=
  Raw₀.Const.contains_insertManyIfNewUnit_empty_list

@[simp]
theorem mem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k := by
  simp [mem_iff_contains]

theorem getKey?_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none :=
  Raw₀.Const.getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k :=
  Raw₀.Const.getKey?_insertManyIfNewUnit_empty_list_of_mem k_beq distinct mem

theorem getKey_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (unitOfList l) k' h = k :=
  Raw₀.Const.getKey_insertManyIfNewUnit_empty_list_of_mem k_beq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default :=
  Raw₀.Const.getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k :=
  Raw₀.Const.getKey!_insertManyIfNewUnit_empty_list_of_mem k_beq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback :=
  Raw₀.Const.getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (unitOfList l) k' fallback = k :=
  Raw₀.Const.getKeyD_insertManyIfNewUnit_empty_list_of_mem k_beq distinct mem

theorem size_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_empty_list distinct

theorem size_unitOfList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).size ≤ l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_empty_list_le

@[simp]
theorem isEmpty_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).isEmpty = l.isEmpty :=
  Raw₀.Const.isEmpty_insertManyIfNewUnit_empty_list

@[simp]
theorem get?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (unitOfList l) k =
    if l.contains k then some () else none :=
  Raw₀.Const.get?_insertManyIfNewUnit_empty_list

@[simp]
theorem get_unitOfList
    {l : List α} {k : α} {h} :
    get (unitOfList l) k h = () :=
  Raw₀.Const.get_insertManyIfNewUnit_empty_list

@[simp]
theorem get!_unitOfList
    {l : List α} {k : α} :
    get! (unitOfList l) k = () :=
  Raw₀.Const.get!_insertManyIfNewUnit_empty_list

@[simp]
theorem getD_unitOfList
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () := by
  simp

end Const

variable {m : DHashMap α β}

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).isEmpty = ((m.erase k).isEmpty && (f (m.get? k)).isNone) :=
  Raw₀.isEmpty_alter_eq_isEmpty_erase _ m.2

@[simp]
theorem isEmpty_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) && (f (get? m k)).isNone) :=
  Raw₀.isEmpty_alter _ m.2

theorem contains_alter [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' :=
  Raw₀.contains_alter ⟨_, _⟩ m.2

theorem mem_alter [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} :
    k' ∈ m.alter k f ↔ if k == k' then (f (m.get? k)).isSome = true else k' ∈ m := by
  simp only [mem_iff_contains, contains_alter, beq_iff_eq, Bool.ite_eq_true_distrib]

theorem mem_alter_of_beq [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} (h : k == k') :
    k' ∈ m.alter k f ↔ (f (m.get? k)).isSome := by
  rw [mem_alter, if_pos h]

@[simp]
theorem contains_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k = (f (m.get? k)).isSome := by
  simp only [contains_alter, beq_self_eq_true, reduceIte]

@[simp]
theorem mem_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    k ∈ m.alter k f ↔ (f (m.get? k)).isSome := by
  rw [mem_iff_contains, contains_alter_self]

theorem contains_alter_of_beq_eq_false [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : (k == k') = false) : (m.alter k f).contains k' = m.contains k' := by
  simp only [contains_alter, h, Bool.false_eq_true, reduceIte]

theorem mem_alter_of_beq_eq_false [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : (k == k') = false) : k' ∈ m.alter k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_alter_of_beq_eq_false, h]

theorem size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).size =
      if m.contains k && (f (m.get? k)).isNone then
        m.size - 1
      else if !m.contains k && (f (m.get? k)).isSome then
        m.size + 1
      else
        m.size :=
  Raw₀.size_alter ⟨m.1, _⟩ m.2

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∉ m) (h' : (f (m.get? k)).isSome) :
    (m.alter k f).size = m.size + 1 := by
  rw [mem_iff_contains, Bool.not_eq_true] at h
  exact Raw₀.size_alter_eq_add_one ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∈ m) (h' : (f (m.get? k)).isNone) :
    (m.alter k f).size = m.size - 1 :=
  Raw₀.size_alter_eq_sub_one ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∉ m) (h' : (f (m.get? k)).isNone) : (m.alter k f).size = m.size := by
  rw [mem_iff_contains, Bool.not_eq_true] at h
  exact Raw₀.size_alter_eq_self_of_not_mem ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : k ∈ m) (h' : (f (m.get? k)).isSome) : (m.alter k f).size = m.size :=
  Raw₀.size_alter_eq_self_of_mem ⟨m.1, _⟩ m.2 h h'

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).size ≤ m.size + 1 :=
  Raw₀.size_alter_le_size ⟨m.1, _⟩ m.2

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    m.size - 1 ≤ (m.alter k f).size :=
  Raw₀.size_le_size_alter ⟨m.1, _⟩ m.2

theorem get?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).get? k' =
      if h : k == k' then
        (cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (m.get? k)))
      else
        m.get? k' :=
  Raw₀.get?_alter ⟨m.1, _⟩ m.2

@[simp]
theorem get?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).get? k = f (m.get? k) := by
  simp only [get?_alter, beq_self_eq_true, reduceDIte, Function.comp_apply, cast_eq]

theorem get_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    {h : k' ∈ m.alter k f} :
    (m.alter k f).get k' h =
      if heq : k == k' then
        haveI h' : (f (m.get? k)).isSome := mem_alter_of_beq heq |>.mp h
        cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get <| h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.get k' h' :=
  Raw₀.get_alter ⟨m.1, _⟩ m.2 h

@[simp]
theorem get_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    {h : k ∈ m.alter k f} :
    haveI h' : (f (m.get? k)).isSome := mem_alter_self.mp h
    (m.alter k f).get k h = (f (m.get? k)).get h' :=
  Raw₀.get_alter_self ⟨m.1, _⟩ m.2

theorem get!_alter [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')]
    {f : Option (β k) → Option (β k)} : (m.alter k f).get! k' =
      if heq : k == k' then
        (f (m.get? k)).map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' :=
  Raw₀.get!_alter ⟨m.1, _⟩ m.2

private theorem Option.map_cast_apply {γ γ' : Type u} (h : γ = γ') (x : Option γ) :
    Option.map (cast h) x = cast (congrArg Option h) x := by
  cases h; cases x <;> simp

@[simp]
theorem get!_alter_self [LawfulBEq α] {k : α} [Inhabited (β k)] {f : Option (β k) → Option (β k)} :
    (m.alter k f).get! k = (f (m.get? k)).get! := by
  simp only [get!_alter, beq_self_eq_true, reduceDIte, cast_eq, Option.map_cast_apply]

theorem getD_alter [LawfulBEq α] {k k' : α} {fallback : β k'} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k' fallback =
      if heq : k == k' then
        f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback :=
  Raw₀.getD_alter ⟨m.1, _⟩ m.2

@[simp]
theorem getD_alter_self [LawfulBEq α] {k : α} {fallback : β k} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k fallback = (f (m.get? k)).getD fallback :=
  Raw₀.getD_alter_self ⟨m.1, _⟩ m.2

theorem getKey?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k' =
      if k == k' then
        if (f (m.get? k)).isSome then some k else none
      else
        m.getKey? k' :=
  Raw₀.getKey?_alter ⟨m.1, _⟩ m.2

theorem getKey?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k = if (f (m.get? k)).isSome then some k else none := by
  simp only [getKey?_alter, beq_self_eq_true, ↓reduceIte]

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' := by
  simp [getKey!_eq_get!_getKey?, getKey?_alter]
  split
  · next heq =>
    cases eq_of_beq heq
    split <;> rfl
  · next heq =>
    rfl

theorem getKey!_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k = if (f (m.get? k)).isSome then k else default := by
  simp only [getKey!_alter, beq_self_eq_true, reduceIte]

theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    {h : k' ∈ m.alter k f} :
    (m.alter k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  Raw₀.getKey_alter ⟨m.1, _⟩ m.2 h

@[simp]
theorem getKey_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)}
    {h : k ∈ m.alter k f} : (m.alter k f).getKey k h = k := by
  simp [getKey_alter]

theorem getKeyD_alter [LawfulBEq α] {k k' fallback : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k' fallback =
      if k == k' then
        if (f (m.get? k)).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  Raw₀.getKeyD_alter ⟨m.1, _⟩ m.2

@[simp]
theorem getKeyD_alter_self [LawfulBEq α] [Inhabited α] {k : α} {fallback : α}
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k fallback = if (f (m.get? k)).isSome then k else fallback := by
  simp [getKeyD_alter]

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

theorem isEmpty_alter_eq_isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α}
    {f : Option β → Option β} :
    (Const.alter m k f).isEmpty = ((m.erase k).isEmpty && (f (Const.get? m k)).isNone) :=
  Raw₀.Const.isEmpty_alter_eq_isEmpty_erase _ m.2

@[simp]
theorem isEmpty_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k))
      && (f (Const.get? m k)).isNone) :=
  Raw₀.Const.isEmpty_alter _ m.2

theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
      if k == k' then (f (Const.get? m k)).isSome else m.contains k' :=
  Raw₀.Const.contains_alter ⟨m.1, _⟩ m.2

theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    k' ∈ Const.alter m k f ↔ if k == k' then (f (Const.get? m k)).isSome = true else k' ∈ m := by
    simp only [mem_iff_contains, contains_alter, Bool.ite_eq_true_distrib]

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : k == k') : k' ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome := by
  rw [mem_alter, if_pos h]

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).contains k = (f (Const.get? m k)).isSome := by
  simp only [contains_alter, BEq.refl, reduceIte]

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    k ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome := by
  rw [mem_iff_contains, contains_alter_self]

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) :
    (Const.alter m k f).contains k' = m.contains k' := by
  simp only [contains_alter, h, Bool.false_eq_true, reduceIte]

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : (k == k') = false) : k' ∈ Const.alter m k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_alter_of_beq_eq_false, h]

theorem size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size =
      if m.contains k && (f (Const.get? m k)).isNone then
        m.size - 1
      else if !m.contains k && (f (Const.get? m k)).isSome then
        m.size + 1
      else
        m.size :=
  Raw₀.Const.size_alter ⟨m.1, _⟩ m.2

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).size = m.size + 1 := by
  rw [mem_iff_contains, Bool.not_eq_true] at h
  exact Raw₀.Const.size_alter_eq_add_one ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).size = m.size - 1 :=
  Raw₀.Const.size_alter_eq_sub_one ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isNone) : (Const.alter m k f).size = m.size := by
  rw [mem_iff_contains, Bool.not_eq_true] at h
  exact Raw₀.Const.size_alter_eq_self_of_not_mem ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isSome) : (Const.alter m k f).size = m.size :=
  Raw₀.Const.size_alter_eq_self_of_mem ⟨m.1, _⟩ m.2 h h'

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size ≤ m.size + 1 :=
  Raw₀.Const.size_alter_le_size ⟨m.1, _⟩ m.2

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} :
    m.size - 1 ≤ (Const.alter m k f).size :=
  Raw₀.Const.size_le_size_alter ⟨m.1, _⟩ m.2

theorem get?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k)
      else
        Const.get? m k' :=
  Raw₀.Const.get?_alter ⟨m.1, _⟩ m.2

@[simp]
theorem get?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k = f (Const.get? m k) := by
  simp [get?_alter]

theorem get_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    {h : k' ∈ Const.alter m k f} :
    Const.get (Const.alter m k f) k' h =
      if heq : k == k' then
        haveI h' : (f (Const.get? m k)).isSome := mem_alter_of_beq heq |>.mp h
        f (Const.get? m k) |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        Const.get m k' h' :=
  Raw₀.Const.get_alter ⟨m.1, _⟩ m.2 h

@[simp]
theorem get_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    {h : k ∈ Const.alter m k f} :
    haveI h' : (f (Const.get? m k)).isSome := mem_alter_self.mp h
    Const.get (Const.alter m k f) k h = (f (Const.get? m k)).get h' := by
  simp [get_alter]

theorem get!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} : Const.get! (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k) |>.get!
      else
        Const.get! m k' :=
  Raw₀.Const.get!_alter ⟨m.1, _⟩ m.2

@[simp]
theorem get!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} : Const.get! (Const.alter m k f) k = (f (Const.get? m k)).get! := by
  simp [get!_alter]

theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β}
    {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k' fallback =
      if k == k' then
        f (Const.get? m k) |>.getD fallback
      else
        Const.getD m k' fallback :=
  Raw₀.Const.getD_alter ⟨m.1, _⟩ m.2

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k fallback = (f (Const.get? m k)).getD fallback := by
  simp [getD_alter]

theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then some k else none
      else
        m.getKey? k' :=
  Raw₀.Const.getKey?_alter ⟨m.1, _⟩ m.2

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k = if (f (Const.get? m k)).isSome then some k else none := by
  simp [getKey?_alter]

theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} : (Const.alter m k f).getKey! k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else default
      else
        m.getKey! k' :=
  Raw₀.Const.getKey!_alter ⟨m.1, _⟩ m.2

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (Const.alter m k f).getKey! k = if (f (Const.get? m k)).isSome then k else default := by
  simp [getKey!_alter]

theorem getKey_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} {h : k' ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  Raw₀.Const.getKey_alter ⟨m.1, _⟩ m.2 h

@[simp]
theorem getKey_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} {h : k ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k h = k := by
  simp [getKey_alter]

theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback :=
  Raw₀.Const.getKeyD_alter ⟨m.1, _⟩ m.2

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k fallback =
      if (f (Const.get? m k)).isSome then k else fallback := by
  simp [getKeyD_alter]

end Const

end Alter

section Modify

@[simp]
theorem isEmpty_modify [LawfulBEq α] {k : α} {f : β k → β k} :
    (m.modify k f).isEmpty = m.isEmpty :=
  Raw₀.isEmpty_modify _ m.2

@[simp]
theorem contains_modify [LawfulBEq α] {k k': α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' :=
  Raw₀.contains_modify ⟨m.1, _⟩ m.2

@[simp]
theorem mem_modify [LawfulBEq α] {k k': α} {f : β k → β k} : k' ∈ m.modify k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_modify]

@[simp]
theorem size_modify [LawfulBEq α] {k : α} {f : β k → β k} : (m.modify k f).size = m.size :=
  Raw₀.size_modify ⟨m.1, _⟩ m.2

theorem get?_modify [LawfulBEq α] {k k' : α} {f : β k → β k} :
    (m.modify k f).get? k' = if h : k == k' then
      (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f))
    else
      m.get? k' :=
  Raw₀.get?_modify ⟨m.1, _⟩ m.2

@[simp]
theorem get?_modify_self [LawfulBEq α] {k : α} {f : β k → β k} :
    (m.modify k f).get? k = (m.get? k).map f :=
  Raw₀.get?_modify_self ⟨m.1, _⟩ m.2

theorem get_modify [LawfulBEq α] {k k' : α} {f : β k → β k}
    (h : k' ∈ m.modify k f) :
    (m.modify k f).get k' h =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        cast (congrArg β (eq_of_beq heq)) <| f (m.get k h')
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.get k' h' :=
  Raw₀.get_modify ⟨m.1, _⟩ m.2 h

@[simp]
theorem get_modify_self [LawfulBEq α] {k : α} {f : β k → β k} {h : k ∈ m.modify k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    (m.modify k f).get k h = f (m.get k h') :=
  Raw₀.get_modify_self ⟨m.1, _⟩ m.2

theorem get!_modify [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (m.modify k f).get! k' =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' :=
  Raw₀.get!_modify ⟨m.1, _⟩ m.2

@[simp]
theorem get!_modify_self [LawfulBEq α] {k : α} [Inhabited (β k)] {f : β k → β k} :
    (m.modify k f).get! k = ((m.get? k).map f).get! :=
  Raw₀.get!_modify_self ⟨m.1, _⟩ m.2

theorem getD_modify [LawfulBEq α] {k k' : α} {fallback : β k'} {f : β k → β k} :
    (m.modify k f).getD k' fallback =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback :=
  Raw₀.getD_modify ⟨m.1, _⟩ m.2

@[simp]
theorem getD_modify_self [LawfulBEq α] {k : α} {fallback : β k} {f : β k → β k} :
    (m.modify k f).getD k fallback = ((m.get? k).map f).getD fallback :=
  Raw₀.getD_modify_self ⟨m.1, _⟩ m.2

theorem getKey?_modify [LawfulBEq α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  Raw₀.getKey?_modify ⟨m.1, _⟩ m.2

theorem getKey?_modify_self [LawfulBEq α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey? k = if k ∈ m then some k else none :=
  Raw₀.getKey?_modify_self ⟨m.1, _⟩ m.2

theorem getKey!_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  Raw₀.getKey!_modify ⟨m.1, _⟩ m.2

theorem getKey!_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey! k = if k ∈ m then k else default :=
  Raw₀.getKey!_modify_self ⟨m.1, _⟩ m.2

theorem getKey_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k}
    {h : k' ∈ m.modify k f} :
    (m.modify k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  Raw₀.getKey_modify ⟨m.1, _⟩ m.2 h

@[simp]
theorem getKey_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k}
    {h : k ∈ m.modify k f} : (m.modify k f).getKey k h = k :=
  Raw₀.getKey_modify_self ⟨m.1, _⟩ m.2 h

theorem getKeyD_modify [LawfulBEq α] {k k' fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  Raw₀.getKeyD_modify ⟨m.1, _⟩ m.2

theorem getKeyD_modify_self [LawfulBEq α] [Inhabited α] {k fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  Raw₀.getKeyD_modify_self ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp]
theorem isEmpty_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).isEmpty = m.isEmpty :=
  Raw₀.Const.isEmpty_modify _ m.2

@[simp]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' :=
  Raw₀.Const.contains_modify ⟨m.1, _⟩ m.2

@[simp]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    k' ∈ Const.modify m k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_modify]

@[simp]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).size = m.size :=
  Raw₀.Const.size_modify ⟨m.1, _⟩ m.2

theorem get?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    Const.get? (Const.modify m k f) k' = if k == k' then
      Const.get? m k |>.map f
    else
      Const.get? m k' :=
  Raw₀.Const.get?_modify ⟨m.1, _⟩ m.2

@[simp]
theorem get?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f :=
  Raw₀.Const.get?_modify_self ⟨m.1, _⟩ m.2

theorem get_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    {h : k' ∈ Const.modify m k f} :
    Const.get (Const.modify m k f) k' h =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr heq |>.mpr <| mem_modify.mp h
        f (Const.get m k h')
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        Const.get m k' h' :=
  Raw₀.Const.get_modify ⟨m.1, _⟩ m.2 h

@[simp]
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    Const.get (Const.modify m k f) k h = f (Const.get m k h') :=
  Raw₀.Const.get_modify_self ⟨m.1, _⟩ m.2

theorem get!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f |>.get!
      else
        Const.get! m k' :=
  Raw₀.Const.get!_modify ⟨m.1, _⟩ m.2

@[simp]
theorem get!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! :=
  Raw₀.Const.get!_modify_self ⟨m.1, _⟩ m.2

theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k' fallback =
      if k == k' then
        Const.get? m k |>.map f |>.getD fallback
      else
        Const.getD m k' fallback :=
  Raw₀.Const.getD_modify ⟨m.1, _⟩ m.2

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k fallback = ((Const.get? m k).map f).getD fallback :=
  Raw₀.Const.getD_modify_self ⟨m.1, _⟩ m.2

theorem getKey?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' :=
  Raw₀.Const.getKey?_modify ⟨m.1, _⟩ m.2

theorem getKey?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey? k = if k ∈ m then some k else none :=
  Raw₀.Const.getKey?_modify_self ⟨m.1, _⟩ m.2

theorem getKey!_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' :=
  Raw₀.Const.getKey!_modify ⟨m.1, _⟩ m.2

theorem getKey!_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey! k = if k ∈ m then k else default :=
  Raw₀.Const.getKey!_modify_self ⟨m.1, _⟩ m.2

theorem getKey_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    {h : k' ∈ Const.modify m k f} :
    (Const.modify m k f).getKey k' h =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify.mp h
        m.getKey k' h' :=
  Raw₀.Const.getKey_modify ⟨m.1, _⟩ m.2 h

@[simp]
theorem getKey_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} : (Const.modify m k f).getKey k h = k :=
  Raw₀.Const.getKey_modify_self ⟨m.1, _⟩ m.2 h

theorem getKeyD_modify [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback :=
  Raw₀.Const.getKeyD_modify ⟨m.1, _⟩ m.2

theorem getKeyD_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k fallback = if k ∈ m then k else fallback :=
  Raw₀.Const.getKeyD_modify_self ⟨m.1, _⟩ m.2

end Const

end Modify

end Std.DHashMap
