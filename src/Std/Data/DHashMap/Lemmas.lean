/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.Raw
import Std.Data.DHashMap.Internal.RawLemmas
import Std.Data.DHashMap.AdditionalOperations

/-!
# Dependent hash map lemmas

This file contains lemmas about `Std.DHashMap`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

open Std.DHashMap.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {_ : BEq α} {_ : Hashable α}

namespace Std.DHashMap

variable {m : DHashMap α β}

private theorem ext {t t' : DHashMap α β} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyWithCapacity {c} : (emptyWithCapacity c : DHashMap α β).isEmpty :=
  Raw₀.isEmpty_emptyWithCapacity

@[simp, grind =]
theorem isEmpty_empty : (∅ : DHashMap α β).isEmpty :=
  isEmpty_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated isEmpty_empty (since := "2025-03-12")]
abbrev isEmpty_emptyc := @isEmpty_empty

@[simp, grind =]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).isEmpty = false :=
  Raw₀.isEmpty_insert _ m.2

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a :=
  Iff.rfl

-- While setting up the API, often use this in the reverse direction,
-- but prefer this direction for users.
@[simp, grind _=_]
theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m :=
  Iff.rfl

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b :=
  Raw₀.contains_congr _ m.2 hab

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m := by
  simp [← contains_iff_mem, contains_congr hab]

@[simp, grind =]
theorem contains_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : DHashMap α β).contains a = false :=
  Raw₀.contains_emptyWithCapacity

@[simp, grind] theorem not_mem_emptyWithCapacity {a : α} {c} : ¬a ∈ (emptyWithCapacity c : DHashMap α β) := by
  simp [← contains_iff_mem]

@[simp, grind =] theorem contains_empty {a : α} : (∅ : DHashMap α β).contains a = false :=
  contains_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated contains_empty (since := "2025-03-12")]
abbrev contains_emptyc := @contains_empty

@[simp] theorem not_mem_empty {a : α} : ¬a ∈ (∅ : DHashMap α β) :=
  not_mem_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated not_mem_empty (since := "2025-03-12")]
abbrev not_mem_emptyc := @not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → m.contains a = false :=
  Raw₀.contains_of_isEmpty ⟨m.1, _⟩ m.2

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → ¬a ∈ m := by
  simpa [← contains_iff_mem] using contains_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, m.contains a = true :=
  Raw₀.isEmpty_eq_false_iff_exists_contains_eq_true ⟨m.1, _⟩ m.2

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, a ∈ m := by
  simpa [← contains_iff_mem] using isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, m.contains a = false :=
  Raw₀.isEmpty_iff_forall_contains ⟨m.1, _⟩ m.2

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m := by
  simpa [← contains_iff_mem] using isEmpty_iff_forall_contains

@[simp] theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p m = m.insert p.1 p.2 := rfl

@[simp] theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : DHashMap α β).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insert k v).contains a = (k == a || m.contains a) :=
  Raw₀.contains_insert ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m := by
  simp [← contains_iff_mem, contains_insert]

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insert k v).contains a → (k == a) = false → m.contains a :=
  Raw₀.contains_of_contains_insert ⟨m.1, _⟩ m.2

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m := by
  simpa [← contains_iff_mem, -contains_insert] using contains_of_contains_insert

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).contains k := by simp

theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insert k v := by simp

@[simp, grind =]
theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : DHashMap α β).size = 0 :=
  Raw₀.size_emptyWithCapacity

@[simp, grind =]
theorem size_empty : (∅ : DHashMap α β).size = 0 :=
  size_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated size_empty (since := "2025-03-12")]
abbrev size_emptyc := @size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) := rfl

@[grind =] theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  Raw₀.size_insert ⟨m.1, _⟩ m.2

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insert k v).size :=
  Raw₀.size_le_size_insert ⟨m.1, _⟩ m.2

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).size ≤ m.size + 1 :=
  Raw₀.size_insert_le ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem erase_emptyWithCapacity {k : α} {c : Nat} : (emptyWithCapacity c : DHashMap α β).erase k = emptyWithCapacity c :=
  ext <| congrArg Subtype.val (Raw₀.erase_emptyWithCapacity (k := k))

@[simp, grind =]
theorem erase_empty {k : α} : (∅ : DHashMap α β).erase k = ∅ :=
  erase_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated erase_empty (since := "2025-03-12")]
abbrev erase_emptyc := @erase_empty

@[simp, grind =]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) :=
  Raw₀.isEmpty_erase _ m.2

@[simp, grind =]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) :=
  Raw₀.contains_erase ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [← contains_iff_mem, contains_erase]

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a :=
  Raw₀.contains_of_contains_erase ⟨m.1, _⟩ m.2

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m := by
  simp

@[grind =] theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  Raw₀.size_erase _ m.2

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size :=
  Raw₀.size_erase_le _ m.2

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 :=
  Raw₀.size_le_size_erase ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem containsThenInsert_fst {k : α} {v : β k} : (m.containsThenInsert k v).1 = m.contains k :=
  Raw₀.containsThenInsert_fst _

@[simp, grind =]
theorem containsThenInsert_snd {k : α} {v : β k} : (m.containsThenInsert k v).2 = m.insert k v :=
  ext <| congrArg Subtype.val (Raw₀.containsThenInsert_snd _ (k := k))

@[simp, grind =]
theorem containsThenInsertIfNew_fst {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k :=
  Raw₀.containsThenInsertIfNew_fst _

@[simp, grind =]
theorem containsThenInsertIfNew_snd {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v :=
  ext <| congrArg Subtype.val (Raw₀.containsThenInsertIfNew_snd _ (k := k))

@[simp, grind =]
theorem get?_emptyWithCapacity [LawfulBEq α] {a : α} {c} : (emptyWithCapacity c : DHashMap α β).get? a = none :=
  Raw₀.get?_emptyWithCapacity

@[simp, grind =]
theorem get?_empty [LawfulBEq α] {a : α} : (∅ : DHashMap α β).get? a = none :=
  get?_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get?_empty (since := "2025-03-12")]
abbrev get?_emptyc := @get?_empty

theorem get?_of_isEmpty [LawfulBEq α] {a : α} : m.isEmpty = true → m.get? a = none :=
  Raw₀.get?_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem get?_insert [LawfulBEq α] {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a :=
  Raw₀.get?_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get?_insert_self [LawfulBEq α] {k : α} {v : β k} : (m.insert k v).get? k = some v :=
  Raw₀.get?_insert_self ⟨m.1, _⟩ m.2

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome :=
  Raw₀.contains_eq_isSome_get? ⟨m.1, _⟩ m.2

@[simp]
theorem isSome_get?_eq_contains [LawfulBEq α] {a : α} : (m.get? a).isSome = m.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [LawfulBEq α] {a : α} : a ∈ m ↔ (m.get? a).isSome :=
  Bool.eq_iff_iff.mp contains_eq_isSome_get?

@[simp]
theorem isSome_get?_iff_mem [LawfulBEq α] {a : α} : (m.get? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_get?.symm

theorem get?_eq_none_of_contains_eq_false [LawfulBEq α] {a : α} :
    m.contains a = false → m.get? a = none :=
  Raw₀.get?_eq_none ⟨m.1, _⟩ m.2

theorem get?_eq_none [LawfulBEq α] {a : α} : ¬a ∈ m → m.get? a = none := by
  simpa [← contains_iff_mem] using get?_eq_none_of_contains_eq_false

@[grind =] theorem get?_erase [LawfulBEq α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  Raw₀.get?_erase ⟨m.1, _⟩ m.2

@[simp]
theorem get?_erase_self [LawfulBEq α] {k : α} : (m.erase k).get? k = none :=
  Raw₀.get?_erase_self ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp, grind =]
theorem get?_emptyWithCapacity {a : α} {c} : get? (emptyWithCapacity c : DHashMap α (fun _ => β)) a = none :=
  Raw₀.Const.get?_emptyWithCapacity

@[simp, grind =]
theorem get?_empty {a : α} : get? (∅ : DHashMap α (fun _ => β)) a = none :=
  get?_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get?_empty (since := "2025-03-12")]
abbrev get?_emptyc := @get?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → get? m a = none :=
  Raw₀.Const.get?_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a :=
  Raw₀.Const.get?_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get? (m.insert k v) k = some v :=
  Raw₀.Const.get?_insert_self ⟨m.1, _⟩ m.2

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (get? m a).isSome :=
  Raw₀.Const.contains_eq_isSome_get? ⟨m.1, _⟩ m.2

@[simp]
theorem isSome_get?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (get? m a).isSome = m.contains a :=
  contains_eq_isSome_get?.symm

theorem mem_iff_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ (get? m a).isSome :=
  Bool.eq_iff_iff.mp contains_eq_isSome_get?

@[simp]
theorem isSome_get?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} : (get? m a).isSome ↔ a ∈ m :=
  mem_iff_isSome_get?.symm

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → get? m a = none :=
  Raw₀.Const.get?_eq_none ⟨m.1, _⟩ m.2

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → get? m a = none := by
  simpa [← contains_iff_mem] using get?_eq_none_of_contains_eq_false

@[grind =] theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
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

@[grind =] theorem get_insert [LawfulBEq α] {k a : α} {v : β k} {h₁} :
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

@[simp, grind =]
theorem get_erase [LawfulBEq α] {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (mem_of_mem_erase h') :=
  Raw₀.get_erase ⟨m.1, _⟩ m.2

theorem get?_eq_some_get [LawfulBEq α] {a : α} (h) : m.get? a = some (m.get a h) :=
  Raw₀.get?_eq_some_get ⟨m.1, _⟩ m.2

theorem get_eq_get_get? [LawfulBEq α] {a : α} {h} :
    m.get a h = (m.get? a).get (mem_iff_isSome_get?.mp h) := by
  simp only [get?_eq_some_get h, Option.get_some]

@[grind =] theorem get_get? [LawfulBEq α] {a : α} {h} :
    (m.get? a).get h = m.get a (mem_iff_isSome_get?.mpr h) :=
  get_eq_get_get?.symm

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[grind =] theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v else get m a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂)) :=
  Raw₀.Const.get_insert ⟨m.1, _⟩ m.2

@[simp]
theorem get_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get (m.insert k v) k mem_insert_self = v :=
  Raw₀.Const.get_insert_self ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    get (m.erase k) a h' = get m a (mem_of_mem_erase h') :=
  Raw₀.Const.get_erase ⟨m.1, _⟩ m.2

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} (h) :
    get? m a = some (get m a h) :=
  Raw₀.Const.get?_eq_some_get ⟨m.1, _⟩ m.2

theorem get_eq_get_get? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    get m a h = (get? m a).get (mem_iff_isSome_get?.mp h) := by
  simp only [get?_eq_some_get h, Option.get_some]

@[grind =] theorem get_get? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (get? m a).get h = get m a (mem_iff_isSome_get?.mpr h) :=
  get_eq_get_get?.symm

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h :=
  Raw₀.Const.get_eq_get ⟨m.1, _⟩ m.2

theorem get_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((mem_congr hab).1 h') :=
  Raw₀.Const.get_congr ⟨m.1, _⟩ m.2 hab

end Const

@[simp, grind =]
theorem get!_emptyWithCapacity [LawfulBEq α] {a : α} [Inhabited (β a)] {c} :
    (emptyWithCapacity c : DHashMap α β).get! a = default :=
  Raw₀.get!_emptyWithCapacity

@[simp, grind =]
theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] :
    (∅ : DHashMap α β).get! a = default :=
  get!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get!_empty (since := "2025-03-12")]
abbrev get!_emptyc := @get!_empty

theorem get!_of_isEmpty [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.isEmpty = true → m.get! a = default :=
  Raw₀.get!_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem get!_insert [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
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
  simpa [← contains_iff_mem] using get!_eq_default_of_contains_eq_false

@[grind =] theorem get!_erase [LawfulBEq α] {k a : α} [Inhabited (β a)] :
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
  simpa [← contains_iff_mem] using get?_eq_some_get!_of_contains

theorem get!_eq_get!_get? [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! :=
  Raw₀.get!_eq_get!_get? ⟨m.1, _⟩ m.2

theorem get_eq_get! [LawfulBEq α] {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a :=
  Raw₀.get_eq_get! ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp, grind =]
theorem get!_emptyWithCapacity [Inhabited β] {a : α} {c} :
    get! (emptyWithCapacity c : DHashMap α (fun _ => β)) a = default :=
  Raw₀.Const.get!_emptyWithCapacity

@[simp, grind =]
theorem get!_empty [Inhabited β] {a : α} : get! (∅ : DHashMap α (fun _ => β)) a = default :=
  get!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get!_empty (since := "2025-03-12")]
abbrev get!_emptyc := @get!_empty

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.isEmpty = true → get! m a = default :=
  Raw₀.Const.get!_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
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
  simpa [← contains_iff_mem] using get!_eq_default_of_contains_eq_false

@[grind =] theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} :
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
  simpa [← contains_iff_mem] using get?_eq_some_get!_of_contains

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

@[simp, grind =]
theorem getD_emptyWithCapacity [LawfulBEq α] {a : α} {fallback : β a} {c} :
    (emptyWithCapacity c : DHashMap α β).getD a fallback = fallback :=
  Raw₀.getD_emptyWithCapacity

@[simp, grind =]
theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} :
    (∅ : DHashMap α β).getD a fallback = fallback :=
  getD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getD_empty (since := "2025-03-12")]
abbrev getD_emptyc := @getD_empty

theorem getD_of_isEmpty [LawfulBEq α] {a : α} {fallback : β a} :
    m.isEmpty = true → m.getD a fallback = fallback :=
  Raw₀.getD_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem getD_insert [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
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
  simpa [← contains_iff_mem] using getD_eq_fallback_of_contains_eq_false

@[grind =] theorem getD_erase [LawfulBEq α] {k a : α} {fallback : β a} :
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
  simpa [← contains_iff_mem] using get?_eq_some_getD_of_contains

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

@[simp, grind =]
theorem getD_emptyWithCapacity {a : α} {fallback : β} {c} :
    getD (emptyWithCapacity c : DHashMap α (fun _ => β)) a fallback = fallback :=
  Raw₀.Const.getD_emptyWithCapacity

@[simp, grind =]
theorem getD_empty {a : α} {fallback : β} :
    getD (∅ : DHashMap α (fun _ => β)) a fallback = fallback :=
  getD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getD_empty (since := "2025-03-12")]
abbrev getD_emptyc := @getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.isEmpty = true → getD m a fallback = fallback :=
  Raw₀.Const.getD_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
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
  simpa [← contains_iff_mem] using getD_eq_fallback_of_contains_eq_false

@[grind =] theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} :
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
  simpa [← contains_iff_mem] using get?_eq_some_getD_of_contains

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

@[simp, grind =]
theorem getKey?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : DHashMap α β).getKey? a = none :=
  Raw₀.getKey?_emptyWithCapacity

@[simp, grind =]
theorem getKey?_empty {a : α} : (∅ : DHashMap α β).getKey? a = none :=
  getKey?_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKey?_empty (since := "2025-03-12")]
abbrev getKey?_emptyc := @getKey?_empty

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → m.getKey? a = none :=
  Raw₀.getKey?_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem getKey?_insert [EquivBEq α] [LawfulHashable α] {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a :=
  Raw₀.getKey?_insert ⟨m.1, _⟩ m.2

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k :=
  Raw₀.getKey?_insert_self ⟨m.1, _⟩ m.2

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (m.getKey? a).isSome :=
  Raw₀.contains_eq_isSome_getKey? ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem isSome_getKey?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome = m.contains a :=
  contains_eq_isSome_getKey?.symm

theorem mem_iff_isSome_getKey? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ (m.getKey? a).isSome :=
  Bool.eq_iff_iff.mp contains_eq_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [EquivBEq α] [LawfulHashable α] {a : α} :
    (m.getKey? a).isSome ↔ a ∈ m :=
  mem_iff_isSome_getKey?.symm

theorem mem_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] {k k' : α}
    (h : m.getKey? k = some k') : k' ∈ m :=
  Raw₀.contains_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → m.getKey? a = none :=
  Raw₀.getKey?_eq_none ⟨m.1, _⟩ m.2

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none := by
  simpa [← contains_iff_mem] using getKey?_eq_none_of_contains_eq_false

@[grind =] theorem getKey?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
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

@[grind =] theorem getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
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

@[simp, grind =]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h') :=
  Raw₀.getKey_erase ⟨m.1, _⟩ m.2

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α} (h) :
    m.getKey? a = some (m.getKey a h) :=
  Raw₀.getKey?_eq_some_getKey ⟨m.1, _⟩ m.2

theorem getKey_eq_get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m.getKey a h = (m.getKey? a).get (mem_iff_isSome_getKey?.mp h) := by
  simp only [getKey?_eq_some_getKey h, Option.get_some]

@[simp, grind =]
theorem get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  getKey_eq_get_getKey?.symm

theorem getKey_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.getKey k h == k :=
  Raw₀.getKey_beq ⟨m.1, _⟩ m.2 h

theorem getKey_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) :=
  Raw₀.getKey_congr ⟨m.1, _⟩ m.2 h h₁

@[simp, grind =]
theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k :=
  Raw₀.getKey_eq ⟨m.1, _⟩ m.2 h

@[simp, grind =]
theorem getKey!_emptyWithCapacity [Inhabited α] {a : α} {c} :
    (emptyWithCapacity c : DHashMap α β).getKey! a = default :=
  Raw₀.getKey!_emptyWithCapacity

@[simp, grind =]
theorem getKey!_empty [Inhabited α] {a : α} :
    (∅ : DHashMap α β).getKey! a = default :=
  getKey!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKey!_empty (since := "2025-03-12")]
abbrev getKey!_emptyc := @getKey!_empty

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.isEmpty = true → m.getKey! a = default :=
  Raw₀.getKey!_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β k} :
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
  simpa [← contains_iff_mem] using getKey!_eq_default_of_contains_eq_false

@[grind =] theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} :
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
  simpa [← contains_iff_mem] using getKey?_eq_some_getKey!_of_contains

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

@[simp, grind =]
theorem getKeyD_emptyWithCapacity {a fallback : α} {c} :
    (emptyWithCapacity c : DHashMap α β).getKeyD a fallback = fallback :=
  Raw₀.getKeyD_emptyWithCapacity

@[simp, grind =]
theorem getKeyD_empty {a fallback : α} :
    (∅ : DHashMap α β).getKeyD a fallback = fallback :=
  getKeyD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKeyD_empty (since := "2025-03-12")]
abbrev getKeyD_emptyc := @getKeyD_empty

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback :=
  Raw₀.getKeyD_of_isEmpty ⟨m.1, _⟩ m.2

@[grind =] theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β k} :
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
  simpa [← contains_iff_mem] using getKeyD_eq_fallback_of_contains_eq_false

@[grind =] theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] {k a fallback : α} :
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
  simpa [← contains_iff_mem] using getKey?_eq_some_getKeyD_of_contains

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

@[simp, grind =]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).isEmpty = false :=
  Raw₀.isEmpty_insertIfNew ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) :=
  Raw₀.contains_insertIfNew ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m := by
  simp [← contains_iff_mem, contains_insertIfNew]

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).contains k :=
  Raw₀.contains_insertIfNew_self ⟨m.1, _⟩ m.2

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insertIfNew k v := by
  simpa [← contains_iff_mem, -contains_insertIfNew] using contains_insertIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a :=
  Raw₀.contains_of_contains_insertIfNew ⟨m.1, _⟩ m.2

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m := by
  simpa [← contains_iff_mem, -contains_insertIfNew] using contains_of_contains_insertIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a :=
  Raw₀.contains_of_contains_insertIfNew' ⟨m.1, _⟩ m.2

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m := by
  simpa [← contains_iff_mem, -contains_insertIfNew] using contains_of_contains_insertIfNew'

@[grind =]
theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 :=
  Raw₀.size_insertIfNew ⟨m.1, _⟩ m.2

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insertIfNew k v).size :=
  Raw₀.size_le_size_insertIfNew ⟨m.1, _⟩ m.2

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size ≤ m.size + 1 :=
  Raw₀.size_insertIfNew_le _ m.2

@[grind =]
theorem get?_insertIfNew [LawfulBEq α] {k a : α} {v : β k} : (m.insertIfNew k v).get? a =
    if h : k == a ∧ ¬k ∈ m then some (cast (congrArg β (eq_of_beq h.1)) v) else m.get? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.get?_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem get_insertIfNew [LawfulBEq α] {k a : α} {v : β k} {h₁} : (m.insertIfNew k v).get a h₁ =
    if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v else m.get a
      (mem_of_mem_insertIfNew' h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.get_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem get!_insertIfNew [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v else m.get! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.get!_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem getD_insertIfNew [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.getD_insertIfNew ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[grind =]
theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some v else get? m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.get?_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v else get m a (mem_of_mem_insertIfNew' h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.get_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then v else get! m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.get!_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then v else getD m a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  exact Raw₀.Const.getD_insertIfNew ⟨m.1, _⟩ m.2

end Const

@[grind =]
theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a := by
  simp [← contains_iff_mem, contains_insertIfNew]
  exact Raw₀.getKey?_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂) := by
  simp [← contains_iff_mem, contains_insertIfNew]
  exact Raw₀.getKey_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β k} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a := by
  simp [← contains_iff_mem, contains_insertIfNew]
  exact Raw₀.getKey!_insertIfNew ⟨m.1, _⟩ m.2

@[grind =]
theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β k} :
    getKeyD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback := by
  simp [← contains_iff_mem, contains_insertIfNew]
  exact Raw₀.getKeyD_insertIfNew ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getThenInsertIfNew?_fst [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k :=
  Raw₀.getThenInsertIfNew?_fst _

@[simp, grind =]
theorem getThenInsertIfNew?_snd [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v :=
  ext <| congrArg Subtype.val (Raw₀.getThenInsertIfNew?_snd _ (k := k))

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}

@[simp, grind =]
theorem getThenInsertIfNew?_fst {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k :=
  Raw₀.Const.getThenInsertIfNew?_fst _

@[simp, grind =]
theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  ext <| congrArg Subtype.val (Raw₀.Const.getThenInsertIfNew?_snd _ (k := k))

end Const

@[simp, grind =]
theorem length_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.length = m.size :=
  Raw₀.length_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α]:
    m.keys.isEmpty = m.isEmpty :=
  Raw₀.isEmpty_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
theorem contains_keys [EquivBEq α] [LawfulHashable α] {k : α} :
    m.keys.contains k = m.contains k :=
  Raw₀.contains_keys ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_keys [LawfulBEq α] {k : α} :
    k ∈ m.keys ↔ k ∈ m := by
  rw [mem_iff_contains]
  exact Raw₀.mem_keys ⟨m.1, _⟩ m.2

theorem mem_of_mem_keys [EquivBEq α] [LawfulHashable α] {k : α}
    (h : k ∈ m.keys) : k ∈ m :=
  Raw₀.contains_of_mem_keys ⟨m.1, _⟩ m.2 h

theorem distinct_keys [EquivBEq α] [LawfulHashable α] :
    m.keys.Pairwise (fun a b => (a == b) = false) :=
  Raw₀.distinct_keys ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind _=_]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.toList.map Sigma.fst = m.keys :=
  Raw₀.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_sigma_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.toList.map Sigma.fst = m.keys :=
  Raw₀.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[simp, grind =]
theorem length_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.length = m.size :=
  Raw₀.length_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    m.toList.isEmpty = m.isEmpty :=
  Raw₀.isEmpty_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
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

@[simp, grind _=_]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    (toList m).map Prod.fst = m.keys :=
  Raw₀.Const.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_prod_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    (toList m).map Prod.fst = m.keys :=
  Raw₀.Const.map_fst_toList_eq_keys ⟨m.1, m.2.size_buckets_pos⟩

@[simp, grind =]
theorem length_toList [EquivBEq α] [LawfulHashable α] :
    (toList m).length = m.size :=
  Raw₀.Const.length_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] :
    (toList m).isEmpty = m.isEmpty :=
  Raw₀.Const.isEmpty_toList ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
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

@[simp, grind =]
theorem forM_eq_forM [Monad m'] [LawfulMonad m'] {f : (a : α) → β a → m' PUnit} :
    DHashMap.forM f m = ForM.forM m (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : (a : α) × β a → m' PUnit} :
    ForM.forM m f = ForM.forM m.toList f :=
  Raw₀.forM_eq_forM_toList ⟨m.1, m.2.size_buckets_pos⟩

@[simp, grind =]
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

variable {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]

@[simp, grind =]
theorem insertMany_nil :
    m.insertMany [] = m :=
  ext <| congrArg Subtype.val (Raw₀.insertMany_nil ⟨m.1, m.2.size_buckets_pos⟩)

@[simp, grind =]
theorem insertMany_list_singleton {k : α} {v : β k} :
    m.insertMany [⟨k, v⟩] = m.insert k v :=
  ext <| congrArg Subtype.val (Raw₀.insertMany_list_singleton ⟨m.1, m.2.size_buckets_pos⟩)

@[grind _=_] theorem insertMany_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    m.insertMany (⟨k, v⟩ :: l) = (m.insert k v).insertMany l :=
  ext <| congrArg Subtype.val (Raw₀.insertMany_cons ⟨m.1, m.2.size_buckets_pos⟩)

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List ((a : α) × β a)} :
    m.insertMany (l₁ ++ l₂) = (m.insertMany l₁).insertMany l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[elab_as_elim]
theorem insertMany_ind {motive : DHashMap α β → Prop} (m : DHashMap α β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) :=
  (Raw₀.insertMany_ind ⟨m.1, _⟩ l ⟨m.2, init⟩
    (fun m a b ⟨h, h'⟩ => ⟨h.insert₀, insert ⟨m, h⟩ a b h'⟩) :
    ∃ h, motive ⟨(Raw₀.insertMany _ l).1, h⟩).2

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).contains k = (m.contains k || (l.map Sigma.fst).contains k) :=
  Raw₀.contains_insertMany_list ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ m.insertMany l ↔ k ∈ m ∨ (l.map Sigma.fst).contains k := by
  simp [← contains_iff_mem]

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} (mem : k ∈ m.insertMany l)
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    k ∈ m :=
  Raw₀.contains_of_contains_insertMany_list ⟨m.1, _⟩ m.2 mem contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} (h : k ∈ m) : k ∈ (m.insertMany l) :=
  Raw₀.contains_insertMany_of_contains ⟨m.1, _⟩ m.2 h

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

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (m.insertMany l).size :=
  Raw₀.size_le_size_insertMany ⟨m.1, _⟩ m.2

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (m.insertMany l).size ≤ m.size + l.length :=
  Raw₀.size_insertMany_list_le ⟨m.1, _⟩ m.2

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (m.insertMany l).isEmpty = (m.isEmpty && l.isEmpty) :=
  Raw₀.isEmpty_insertMany_list ⟨m.1, _⟩ m.2

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : (m.insertMany l).isEmpty → m.isEmpty :=
  Raw₀.isEmpty_of_isEmpty_insertMany ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {m : DHashMap α (fun _ => β)}
variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[simp, grind =]
theorem insertMany_nil :
    insertMany m [] = m :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertMany_nil ⟨m.1, m.2.size_buckets_pos⟩)

@[simp, grind =]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v :=
  ext <| congrArg Subtype.val
    (Raw₀.Const.insertMany_list_singleton ⟨m.1, m.2.size_buckets_pos⟩)

@[grind _=_] theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertMany_cons ⟨m.1, m.2.size_buckets_pos⟩)

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List (α × β)} :
    insertMany m (l₁ ++ l₂) = insertMany (insertMany m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[elab_as_elim]
theorem insertMany_ind {motive : DHashMap α (fun _ => β) → Prop} (m : DHashMap α fun _ => β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (insertMany m l) :=
  (Raw₀.Const.insertMany_ind ⟨m.1, _⟩ l ⟨m.2, init⟩
    (fun m a b ⟨h, h'⟩ => ⟨h.insert₀, insert ⟨m, h⟩ a b h'⟩) :
    ∃ h, motive ⟨(Raw₀.Const.insertMany _ l).1, h⟩).2

@[simp, grind =]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (Const.insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) :=
  Raw₀.Const.contains_insertMany_list ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k := by
  simp [← contains_iff_mem]

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} (mem : k ∈ insertMany m l)
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    k ∈ m :=
  Raw₀.Const.contains_of_contains_insertMany_list ⟨m.1, _⟩ m.2 mem contains_eq_false

theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} (h : k ∈ m) : k ∈ insertMany m l :=
  Raw₀.Const.contains_insertMany_of_contains ⟨m.1, _⟩ m.2 h

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

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertMany m l).size :=
  Raw₀.Const.size_le_size_insertMany ⟨m.1, _⟩ m.2

grind_pattern size_le_size_insertMany => (insertMany m l).size

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length :=
  Raw₀.Const.size_insertMany_list_le ⟨m.1, _⟩ m.2

grind_pattern size_insertMany_list_le => (insertMany m l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  Raw₀.Const.isEmpty_insertMany_list ⟨m.1, _⟩ m.2

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α]
    {l : ρ} : (insertMany m l).isEmpty → m.isEmpty :=
  Raw₀.Const.isEmpty_of_isEmpty_insertMany ⟨m.1, _⟩ m.2

theorem get?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l) k = get? m k :=
  Raw₀.Const.get?_insertMany_list_of_contains_eq_false ⟨m.1, _⟩ m.2 contains_eq_false

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l) k' = some v :=
  Raw₀.Const.get?_insertMany_list_of_mem ⟨m.1, _⟩ m.2 k_beq distinct mem

@[grind =]
theorem get?_insertMany_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    get? (insertMany m l) k =
      (l.findSomeRev? (fun ⟨a, b⟩ => if a == k then some b else none)).or (get? m k) := by
  induction l generalizing m with
  | nil =>
    rw [get?_insertMany_list_of_contains_eq_false] <;> simp
  | cons x l ih =>
    rcases x with ⟨a, b⟩
    rw [insertMany_cons, ih, get?_insert]
    by_cases h : a == k <;> simp [h]

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
variable {ρ : Type w} [ForIn Id ρ α]

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit m [] = m :=
  ext <| congrArg Subtype.val
    (Raw₀.Const.insertManyIfNewUnit_nil ⟨m.1, m.2.size_buckets_pos⟩)

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () :=
  ext <| congrArg Subtype.val
    (Raw₀.Const.insertManyIfNewUnit_list_singleton ⟨m.1, m.2.size_buckets_pos⟩)

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l :=
  ext <| congrArg Subtype.val
    (Raw₀.Const.insertManyIfNewUnit_cons ⟨m.1, m.2.size_buckets_pos⟩)

@[elab_as_elim]
theorem insertManyIfNewUnit_ind {motive : DHashMap α (fun _ => Unit) → Prop}
    (m : DHashMap α fun _ => Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l) :=
  (Raw₀.Const.insertManyIfNewUnit_ind ⟨m.1, _⟩ l ⟨m.2, init⟩
    (fun m a ⟨h, h'⟩ => ⟨h.insertIfNew₀, insert ⟨m, h⟩ a h'⟩) :
    ∃ h, motive ⟨(Raw₀.Const.insertManyIfNewUnit _ l).1, h⟩).2

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) :=
  Raw₀.Const.contains_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k := by
  simp [← contains_iff_mem]

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m :=
  Raw₀.Const.contains_of_contains_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2 contains_eq_false

theorem mem_insertManyIfNewUnit_of_mem [EquivBEq α] [LawfulHashable α]
    {l : ρ} {k : α} (h : k ∈ m) : k ∈ insertManyIfNewUnit m l :=
  Raw₀.Const.contains_insertManyIfNewUnit_of_contains ⟨m.1, _⟩ m.2 h

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

theorem size_le_size_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {l : ρ} : m.size ≤ (insertManyIfNewUnit m l).size :=
  Raw₀.Const.size_le_size_insertManyIfNewUnit ⟨m.1, _⟩ m.2

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_list_le ⟨m.1, _⟩ m.2

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit m l).isEmpty = (m.isEmpty && l.isEmpty) :=
  Raw₀.Const.isEmpty_insertManyIfNewUnit_list ⟨m.1, _⟩ m.2

theorem isEmpty_of_isEmpty_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {l : ρ} : (insertManyIfNewUnit m l).isEmpty → m.isEmpty :=
  Raw₀.Const.isEmpty_of_isEmpty_insertManyIfNewUnit ⟨m.1, _⟩ m.2

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

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List ((a : α) × (β a))) = ∅ :=
  ext <| congrArg Subtype.val (Raw₀.insertMany_emptyWithCapacity_list_nil (α := α))

@[simp, grind =]
theorem ofList_singleton {k : α} {v : β k} :
    ofList [⟨k, v⟩] = (∅: DHashMap α β).insert k v :=
  ext <| congrArg Subtype.val (Raw₀.insertMany_emptyWithCapacity_list_singleton (α := α))

@[grind _=_] theorem ofList_cons {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) = ((∅ : DHashMap α β).insert k v).insertMany tl :=
  ext <| congrArg Subtype.val (Raw₀.insertMany_emptyWithCapacity_list_cons (α := α))

theorem ofList_eq_insertMany_empty {l : List ((a : α) × β a)} :
    ofList l = insertMany (∅ : DHashMap α β) l := rfl

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l).contains k = (l.map Sigma.fst).contains k :=
  Raw₀.contains_insertMany_emptyWithCapacity_list

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l ↔ (l.map Sigma.fst).contains k := by
  simp [← contains_iff_mem]

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get? k = none :=
  Raw₀.get?_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) :=
  Raw₀.get?_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.get_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get! k = default :=
  Raw₀.get!_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.get!_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getD k fallback = fallback :=
  Raw₀.getD_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v :=
  Raw₀.getD_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  Raw₀.getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey? k' = some k :=
  Raw₀.getKey?_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  Raw₀.getKey_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  Raw₀.getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey! k' = k :=
  Raw₀.getKey!_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  Raw₀.getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKeyD k' fallback = k :=
  Raw₀.getKeyD_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  Raw₀.size_insertMany_emptyWithCapacity_list distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).size ≤ l.length :=
  Raw₀.size_insertMany_emptyWithCapacity_list_le

grind_pattern size_ofList_le => (ofList l).size

@[simp, grind =]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).isEmpty = l.isEmpty :=
  Raw₀.isEmpty_insertMany_emptyWithCapacity_list

namespace Const

variable {β : Type v}

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertMany_emptyWithCapacity_list_nil (α:= α))

@[simp, grind =]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : DHashMap α (fun _ => β)).insert k v :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertMany_emptyWithCapacity_list_singleton (α:= α))

@[grind _=_] theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : DHashMap α (fun _ => β)).insert k v) tl :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertMany_emptyWithCapacity_list_cons (α:= α))

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l = insertMany (∅ : DHashMap α (fun _ => β)) l := rfl

@[simp, grind =]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k :=
  Raw₀.Const.contains_insertMany_emptyWithCapacity_list

@[simp, grind =]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ ofList l ↔ (l.map Prod.fst).contains k := by
  simp [← contains_iff_mem]

theorem get?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l) k = none :=
  Raw₀.Const.get?_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l) k' = some v :=
  Raw₀.Const.get?_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem get_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l) k' h = v :=
  Raw₀.Const.get_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem get!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l) k = (default : β) :=
  Raw₀.Const.get!_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l) k' = v :=
  Raw₀.Const.get!_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback :=
  Raw₀.Const.getD_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v :=
  Raw₀.Const.getD_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none :=
  Raw₀.Const.getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k :=
  Raw₀.Const.getKey?_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h} :
    (ofList l).getKey k' h = k :=
  Raw₀.Const.getKey_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default :=
  Raw₀.Const.getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k :=
  Raw₀.Const.getKey!_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback :=
  Raw₀.Const.getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k :=
  Raw₀.Const.getKeyD_insertMany_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length :=
  Raw₀.Const.size_insertMany_emptyWithCapacity_list distinct

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).size ≤ l.length :=
  Raw₀.Const.size_insertMany_emptyWithCapacity_list_le

grind_pattern size_ofList_le => (ofList l).size

@[simp, grind =]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).isEmpty = l.isEmpty :=
  Raw₀.Const.isEmpty_insertMany_emptyWithCapacity_list

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) = ∅ :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_emptyWithCapacity_list_nil (α := α))

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (∅ : DHashMap α (fun _ => Unit)).insertIfNew k () :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_emptyWithCapacity_list_singleton (α := α))

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      insertManyIfNewUnit ((∅ : DHashMap α (fun _ => Unit)).insertIfNew hd ()) tl :=
  ext <| congrArg Subtype.val (Raw₀.Const.insertManyIfNewUnit_emptyWithCapacity_list_cons (α := α))

@[simp]
theorem contains_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k :=
  Raw₀.Const.contains_insertManyIfNewUnit_emptyWithCapacity_list

@[simp]
theorem mem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k := by
  simp [← contains_iff_mem]

theorem getKey?_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none :=
  Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k :=
  Raw₀.Const.getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h} :
    getKey (unitOfList l) k' h = k :=
  Raw₀.Const.getKey_insertManyIfNewUnit_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default :=
  Raw₀.Const.getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k :=
  Raw₀.Const.getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback :=
  Raw₀.Const.getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (unitOfList l) k' fallback = k :=
  Raw₀.Const.getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_mem k_beq distinct mem

theorem size_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_emptyWithCapacity_list distinct

theorem size_unitOfList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).size ≤ l.length :=
  Raw₀.Const.size_insertManyIfNewUnit_emptyWithCapacity_list_le

@[simp]
theorem isEmpty_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).isEmpty = l.isEmpty :=
  Raw₀.Const.isEmpty_insertManyIfNewUnit_emptyWithCapacity_list

@[simp]
theorem get?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (unitOfList l) k =
    if l.contains k then some () else none :=
  Raw₀.Const.get?_insertManyIfNewUnit_emptyWithCapacity_list

@[simp]
theorem get_unitOfList
    {l : List α} {k : α} {h} :
    get (unitOfList l) k h = () :=
  Raw₀.Const.get_insertManyIfNewUnit_emptyWithCapacity_list

@[simp]
theorem get!_unitOfList
    {l : List α} {k : α} :
    get! (unitOfList l) k = () :=
  Raw₀.Const.get!_insertManyIfNewUnit_emptyWithCapacity_list

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

@[simp, grind =]
theorem isEmpty_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) && (f (get? m k)).isNone) :=
  Raw₀.isEmpty_alter _ m.2

@[grind =]
theorem contains_alter [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' :=
  Raw₀.contains_alter ⟨_, _⟩ m.2

@[grind =]
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

@[grind =]
theorem size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).size =
      if k ∈ m ∧ (f (m.get? k)).isNone then
        m.size - 1
      else if k ∉ m ∧ (f (m.get? k)).isSome then
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' := by
  simp only [getKey!_eq_get!_getKey?, getKey?_alter, beq_iff_eq]
  split
  · next heq =>
    split <;> rfl
  · next heq =>
    rfl

theorem getKey!_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k = if (f (m.get? k)).isSome then k else default := by
  simp only [getKey!_alter, beq_self_eq_true, reduceIte]

@[deprecated getKey_eq (since := "2025-01-05")]
theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    {h : k' ∈ m.alter k f} :
    (m.alter k f).getKey k' h =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false (Bool.not_eq_true _ ▸ heq) |>.mp h
        m.getKey k' h' :=
  Raw₀.getKey_alter ⟨m.1, _⟩ m.2 h

theorem getKey_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)}
    {h : k ∈ m.alter k f} : (m.alter k f).getKey k h = k := by
  simp

@[grind =]
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

@[simp, grind =]
theorem isEmpty_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k))
      && (f (Const.get? m k)).isNone) :=
  Raw₀.Const.isEmpty_alter _ m.2

@[grind =]
theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
      if k == k' then (f (Const.get? m k)).isSome else m.contains k' :=
  Raw₀.Const.contains_alter ⟨m.1, _⟩ m.2

@[grind =]
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

@[grind =]
theorem size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size =
      if k ∈ m ∧ (f (Const.get? m k)).isNone then
        m.size - 1
      else if k ∉ m ∧ (f (Const.get? m k)).isSome then
        m.size + 1
      else
        m.size :=
  Raw₀.Const.size_alter ⟨m.1, _⟩ m.2

theorem size_alter_eq_add_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).size = m.size + 1 := by
  rw [mem_iff_contains, Bool.not_eq_true] at h
  exact Raw₀.Const.size_alter_eq_add_one ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_sub_one [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).size = m.size - 1 :=
  Raw₀.Const.size_alter_eq_sub_one ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_self_of_not_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∉ m) (h' : (f (Const.get? m k)).isNone) : (Const.alter m k f).size = m.size := by
  rw [mem_iff_contains, Bool.not_eq_true] at h
  exact Raw₀.Const.size_alter_eq_self_of_not_mem ⟨m.1, _⟩ m.2 h h'

theorem size_alter_eq_self_of_mem [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : k ∈ m) (h' : (f (Const.get? m k)).isSome) : (Const.alter m k f).size = m.size :=
  Raw₀.Const.size_alter_eq_self_of_mem ⟨m.1, _⟩ m.2 h h'

theorem size_alter_le_size [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    (Const.alter m k f).size ≤ m.size + 1 :=
  Raw₀.Const.size_alter_le_size ⟨m.1, _⟩ m.2

theorem size_le_size_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} :
    m.size - 1 ≤ (Const.alter m k f).size :=
  Raw₀.Const.size_le_size_alter ⟨m.1, _⟩ m.2

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[simp, grind =]
theorem isEmpty_modify [LawfulBEq α] {k : α} {f : β k → β k} :
    (m.modify k f).isEmpty = m.isEmpty :=
  Raw₀.isEmpty_modify _ m.2

@[simp, grind =]
theorem contains_modify [LawfulBEq α] {k k': α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' :=
  Raw₀.contains_modify ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_modify [LawfulBEq α] {k k': α} {f : β k → β k} : k' ∈ m.modify k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_modify]

@[simp, grind =]
theorem size_modify [LawfulBEq α] {k : α} {f : β k → β k} : (m.modify k f).size = m.size :=
  Raw₀.size_modify ⟨m.1, _⟩ m.2

@[grind =]
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
  Raw₀.get_modify ⟨m.1, _⟩ m.2 h

@[simp]
theorem get_modify_self [LawfulBEq α] {k : α} {f : β k → β k} {h : k ∈ m.modify k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    (m.modify k f).get k h = f (m.get k h') :=
  Raw₀.get_modify_self ⟨m.1, _⟩ m.2

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[deprecated getKey_eq (since := "2025-01-05")]
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

@[grind =]
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

@[simp, grind =]
theorem isEmpty_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).isEmpty = m.isEmpty :=
  Raw₀.Const.isEmpty_modify _ m.2

@[simp, grind =]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' :=
  Raw₀.Const.contains_modify ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} :
    k' ∈ Const.modify m k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_modify]

@[simp, grind =]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
    (Const.modify m k f).size = m.size :=
  Raw₀.Const.size_modify ⟨m.1, _⟩ m.2

@[grind =]
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
  Raw₀.Const.get_modify ⟨m.1, _⟩ m.2 h

@[simp]
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    {h : k ∈ Const.modify m k f} :
    haveI h' : k ∈ m := mem_modify.mp h
    Const.get (Const.modify m k f) k h = f (Const.get m k h') :=
  Raw₀.Const.get_modify_self ⟨m.1, _⟩ m.2

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

@[grind =]
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

namespace Equiv

variable {m₁ m₂ m₃ : Std.DHashMap α β}

@[refl, simp] theorem refl (m : Std.DHashMap α β) : m ~m m := ⟨⟨.rfl⟩⟩
theorem rfl : m ~m m := ⟨⟨.rfl⟩⟩
@[symm] theorem symm : m₁ ~m m₂ → m₂ ~m m₁
  | ⟨⟨h⟩⟩ => ⟨⟨h.symm⟩⟩
theorem trans : m₁ ~m m₂ → m₂ ~m m₃ → m₁ ~m m₃
  | ⟨⟨h₁⟩⟩, ⟨⟨h₂⟩⟩ => ⟨⟨h₁.trans h₂⟩⟩

instance instTrans : Trans (α := Std.DHashMap α β) Equiv Equiv Equiv := ⟨trans⟩

theorem comm : m₁ ~m m₂ ↔ m₂ ~m m₁ := ⟨symm, symm⟩
theorem congr_left (h : m₁ ~m m₂) : m₁ ~m m₃ ↔ m₂ ~m m₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : m₁ ~m m₂) : m₃ ~m m₁ ↔ m₃ ~m m₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

theorem isEmpty_eq [EquivBEq α] [LawfulHashable α] (h : m₁ ~m m₂) : m₁.isEmpty = m₂.isEmpty :=
  Raw₀.isEmpty_eq_of_equiv ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ m₁.2 m₂.2 h.1

theorem size_eq [EquivBEq α] [LawfulHashable α] (h : m₁ ~m m₂) : m₁.size = m₂.size :=
  Raw₀.size_eq_of_equiv ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ m₁.2 m₂.2 h.1

theorem contains_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁.contains k = m₂.contains k :=
  Raw₀.contains_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem mem_iff [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) : k ∈ m₁ ↔ k ∈ m₂ := by
  simpa only [mem_iff_contains, Bool.coe_iff_coe] using contains_eq h

theorem toList_perm (h : m₁ ~m m₂) : m₁.toList.Perm m₂.toList :=
  (Raw₀.equiv_iff_toList_perm_toList m₁.1 m₂.1).mp h.1

theorem of_toList_perm (h : m₁.toList.Perm m₂.toList) : m₁ ~m m₂ :=
  ⟨(Raw₀.equiv_iff_toList_perm_toList m₁.1 m₂.1).mpr h⟩

theorem keys_perm (h : m₁ ~m m₂) : m₁.keys.Perm m₂.keys :=
  Raw₀.keys_perm_keys_of_equiv m₁.1 m₂.1 h.1

theorem get?_eq [LawfulBEq α] {k : α} (h : m₁ ~m m₂) : m₁.get? k = m₂.get? k :=
  Raw₀.get?_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem get_eq [LawfulBEq α] {k : α} (hk : k ∈ m₁) (h : m₁ ~m m₂) :
    m₁.get k hk = m₂.get k (h.mem_iff.mp hk) :=
  Raw₀.get_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 hk

theorem get!_eq [LawfulBEq α] {k : α} [Inhabited (β k)] (h : m₁ ~m m₂) :
    m₁.get! k = m₂.get! k :=
  Raw₀.get!_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem getD_eq [LawfulBEq α] {k : α} {fallback : β k} (h : m₁ ~m m₂) :
    m₁.getD k fallback = m₂.getD k fallback :=
  Raw₀.getD_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem getKey?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁.getKey? k = m₂.getKey? k :=
  Raw₀.getKey?_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem getKey_eq [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁ ~m m₂) :
    m₁.getKey k hk = m₂.getKey k (h.mem_iff.mp hk) :=
  Raw₀.getKey_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 hk

theorem getKey!_eq [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h : m₁ ~m m₂) :
    m₁.getKey! k = m₂.getKey! k :=
  Raw₀.getKey!_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem getKeyD_eq [EquivBEq α] [LawfulHashable α] {k fallback : α} (h : m₁ ~m m₂) :
    m₁.getKeyD k fallback = m₂.getKeyD k fallback :=
  Raw₀.getKeyD_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem insert [EquivBEq α] [LawfulHashable α] (k : α) (v : β k) (h : m₁ ~m m₂) :
    m₁.insert k v ~m m₂.insert k v :=
  ⟨Raw₀.insert_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1⟩

theorem erase [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁ ~m m₂) :
    m₁.erase k ~m m₂.erase k :=
  ⟨Raw₀.erase_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1⟩

theorem insertIfNew [EquivBEq α] [LawfulHashable α] (k : α) (v : β k) (h : m₁ ~m m₂) :
    m₁.insertIfNew k v ~m m₂.insertIfNew k v :=
  ⟨Raw₀.insertIfNew_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1⟩

theorem insertMany_list [EquivBEq α] [LawfulHashable α]
    (l : List ((a : α) × β a)) (h : m₁ ~m m₂) :
    m₁.insertMany l ~m m₂.insertMany l :=
  ⟨Raw₀.insertMany_list_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1⟩

theorem alter [LawfulBEq α] (k : α) (f : Option (β k) → Option (β k)) (h : m₁ ~m m₂) :
    m₁.alter k f ~m m₂.alter k f :=
  ⟨Raw₀.alter_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 f⟩

theorem modify [LawfulBEq α] (k : α) (f : β k → β k) (h : m₁ ~m m₂) :
    m₁.modify k f ~m m₂.modify k f :=
  ⟨Raw₀.modify_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 f⟩

theorem filter (f : (a : α) → β a → Bool) (h : m₁ ~m m₂) : m₁.filter f ~m m₂.filter f :=
  ⟨Raw₀.filter_equiv_congr ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ h.1⟩

theorem map (f : (a : α) → β a → γ a) (h : m₁ ~m m₂) : m₁.map f ~m m₂.map f :=
  ⟨Raw₀.map_equiv_congr ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ h.1⟩

theorem filterMap (f : (a : α) → β a → Option (γ a)) (h : m₁ ~m m₂) :
    m₁.filterMap f ~m m₂.filterMap f :=
  ⟨Raw₀.filterMap_equiv_congr ⟨m₁.1, m₁.2.size_buckets_pos⟩ ⟨m₂.1, m₂.2.size_buckets_pos⟩ h.1⟩

theorem of_forall_get?_eq [LawfulBEq α] (h : ∀ k, m₁.get? k = m₂.get? k) : m₁ ~m m₂ :=
  ⟨Raw₀.equiv_of_forall_get?_eq ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h⟩

section Const

variable {β : Type v} {m₁ m₂ : DHashMap α fun _ => β}

theorem constToList_perm (h : m₁ ~m m₂) : (Const.toList m₁).Perm (Const.toList m₂) :=
  (Raw₀.Const.equiv_iff_toList_perm_toList m₁.1 m₂.1).mp h.1

theorem of_constToList_perm (h : (Const.toList m₁).Perm (Const.toList m₂)) : m₁ ~m m₂ :=
  ⟨(Raw₀.Const.equiv_iff_toList_perm_toList m₁.1 m₂.1).mpr h⟩

theorem of_keys_unit_perm {m₁ m₂ : DHashMap α fun _ => Unit}
    (h : m₁.keys.Perm m₂.keys) : m₁ ~m m₂ :=
  ⟨(Raw₀.Const.equiv_iff_keys_perm_keys m₁.1 m₂.1).mpr h⟩

theorem constGet?_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    Const.get? m₁ k = Const.get? m₂ k :=
  Raw₀.Const.get?_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem constGet_eq [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁ ~m m₂) :
    Const.get m₁ k hk = Const.get m₂ k (h.mem_iff.mp hk) :=
  Raw₀.Const.get_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 hk

theorem constGet!_eq [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} (h : m₁ ~m m₂) :
    Const.get! m₁ k = Const.get! m₂ k :=
  Raw₀.Const.get!_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem constGetD_eq [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (h : m₁ ~m m₂) :
    Const.getD m₁ k fallback = Const.getD m₂ k fallback :=
  Raw₀.Const.getD_eq_of_equiv ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1

theorem constInsertMany_list [EquivBEq α] [LawfulHashable α]
    (l : List (α × β)) (h : m₁ ~m m₂) :
    Const.insertMany m₁ l ~m Const.insertMany m₂ l :=
  ⟨Raw₀.Const.insertMany_list_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1⟩

theorem constInsertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : DHashMap α fun _ => Unit} (l : List α) (h : m₁ ~m m₂) :
    Const.insertManyIfNewUnit m₁ l ~m Const.insertManyIfNewUnit m₂ l :=
  ⟨Raw₀.Const.insertManyIfNewUnit_list_equiv_congr m₁.2 m₂.2 h.1⟩

theorem constAlter [EquivBEq α] [LawfulHashable α] (k : α) (f : Option β → Option β)
    (h : m₁ ~m m₂) : Const.alter m₁ k f ~m Const.alter m₂ k f :=
  ⟨Raw₀.Const.alter_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 f⟩

theorem constModify [EquivBEq α] [LawfulHashable α] (k : α) (f : β → β) (h : m₁ ~m m₂) :
    Const.modify m₁ k f ~m Const.modify m₂ k f :=
  ⟨Raw₀.Const.modify_equiv_congr ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 h.1 f⟩

theorem of_forall_getKey_eq_of_forall_constGet?_eq [EquivBEq α] [LawfulHashable α]
    (hk : ∀ k hk hk', m₁.getKey k hk = m₂.getKey k hk') (hv : ∀ k, Const.get? m₁ k = Const.get? m₂ k) :
    m₁ ~m m₂ :=
  ⟨Raw₀.Const.equiv_of_forall_getKey_eq_of_forall_get?_eq ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 hk hv⟩

set_option linter.deprecated false in
@[deprecated of_forall_getKey_eq_of_forall_constGet?_eq (since := "2025-04-25")]
theorem of_forall_getKey?_eq_of_forall_constGet?_eq [EquivBEq α] [LawfulHashable α]
    (hk : ∀ k, m₁.getKey? k = m₂.getKey? k) (hv : ∀ k, Const.get? m₁ k = Const.get? m₂ k) :
    m₁ ~m m₂ :=
  ⟨Raw₀.Const.equiv_of_forall_getKey?_eq_of_forall_get?_eq ⟨m₁.1, _⟩ ⟨m₂.1, _⟩ m₁.2 m₂.2 hk hv⟩

theorem of_forall_constGet?_eq [LawfulBEq α] (hv : ∀ k, Const.get? m₁ k = Const.get? m₂ k) :
    m₁ ~m m₂ :=
  ⟨Raw₀.Const.equiv_of_forall_get?_eq m₁.2 m₂.2 hv⟩

theorem of_forall_getKey?_unit_eq [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : DHashMap α fun _ => Unit} (h : ∀ k, m₁.getKey? k = m₂.getKey? k) : m₁ ~m m₂ :=
  ⟨Raw₀.Const.equiv_of_forall_getKey?_unit_eq m₁.2 m₂.2 h⟩

theorem of_forall_contains_unit_eq [LawfulBEq α]
    {m₁ m₂ : DHashMap α fun _ => Unit} (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ ~m m₂ :=
  ⟨Raw₀.Const.equiv_of_forall_contains_unit_eq m₁.2 m₂.2 h⟩

theorem of_forall_mem_unit_iff [LawfulBEq α]
    {m₁ m₂ : DHashMap α fun _ => Unit} : (h : ∀ k, k ∈ m₁ ↔ k ∈ m₂) → m₁ ~m m₂ := by
  simpa only [mem_iff_contains, Bool.coe_iff_coe] using of_forall_contains_unit_eq

end Const

end Equiv

/-- Internal implementation detail of the hash map. -/
def isSetoid (α β) [BEq α] [Hashable α] : Setoid (DHashMap α β) where
  r := Equiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

@[simp]
theorem equiv_emptyWithCapacity_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} :
    m ~m emptyWithCapacity c ↔ m.isEmpty :=
  ⟨fun ⟨h⟩ => (Raw₀.equiv_emptyWithCapacity_iff_isEmpty ⟨m.1, m.2.size_buckets_pos⟩ m.2).mp h,
    fun h => ⟨(Raw₀.equiv_emptyWithCapacity_iff_isEmpty ⟨m.1, m.2.size_buckets_pos⟩ m.2).mpr h⟩⟩

@[simp]
theorem equiv_empty_iff_isEmpty [EquivBEq α] [LawfulHashable α] : m ~m ∅ ↔ m.isEmpty :=
  equiv_emptyWithCapacity_iff_isEmpty

set_option linter.missingDocs false in
@[deprecated equiv_empty_iff_isEmpty (since := "2025-03-11")]
abbrev equiv_emptyc_iff_isEmpty := @equiv_empty_iff_isEmpty

@[simp]
theorem emptyWithCapacity_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] {c : Nat} :
    emptyWithCapacity c ~m m ↔ m.isEmpty :=
  Equiv.comm.trans equiv_emptyWithCapacity_iff_isEmpty

@[simp]
theorem empty_equiv_iff_isEmpty [EquivBEq α] [LawfulHashable α] : ∅ ~m m ↔ m.isEmpty :=
  emptyWithCapacity_equiv_iff_isEmpty

set_option linter.missingDocs false in
@[deprecated empty_equiv_iff_isEmpty (since := "2025-03-11")]
abbrev emptyc_equiv_iff_isEmpty := @empty_equiv_iff_isEmpty

theorem equiv_iff_toList_perm {m₁ m₂ : DHashMap α β} [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ m₁.toList.Perm m₂.toList :=
  ⟨Equiv.toList_perm, Equiv.of_toList_perm⟩

namespace Const

variable {β : Type v} {m₁ m₂ : DHashMap α fun _ => β}

theorem equiv_iff_toList_perm [EquivBEq α] [LawfulHashable α] :
    m₁ ~m m₂ ↔ (Const.toList m₁).Perm (Const.toList m₂) :=
  ⟨Equiv.constToList_perm, Equiv.of_constToList_perm⟩

theorem equiv_iff_keys_unit_perm [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : DHashMap α fun _ => Unit} :
    m₁ ~m m₂ ↔ m₁.keys.Perm m₂.keys :=
  ⟨Equiv.keys_perm, Equiv.of_keys_unit_perm⟩

end Const

section filterMap

variable {γ : α → Type w}

theorem toList_filterMap {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).toList.Perm
      (m.toList.filterMap (fun p => (f p.1 p.2).map (fun x => ⟨p.1, x⟩))) :=
  Raw₀.toList_filterMap ⟨m.1, m.2.size_buckets_pos⟩

@[grind =]
theorem isEmpty_filterMap_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ m), f k (m.get k h) = none :=
  Raw₀.isEmpty_filterMap_iff ⟨m.1, _⟩ m.2

theorem isEmpty_filterMap_eq_false_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), (f k (m.get k h)).isSome :=
  Raw₀.isEmpty_filterMap_eq_false_iff ⟨m.1, _⟩ m.2

@[grind =]
theorem contains_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).contains k = (m.get? k).any (f k · |>.isSome) :=
  Raw₀.contains_filterMap ⟨m.1, _⟩ m.2

@[grind =]
theorem mem_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f k (m.get k h)).isSome := by
  simp only [mem_iff_contains, contains_filterMap, Option.any_eq_true_iff_get,
    ← contains_eq_isSome_get?, get_get?]

theorem contains_of_contains_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).contains k = true → m.contains k = true :=
  Raw₀.contains_of_contains_filterMap ⟨m.1, _⟩ m.2

theorem mem_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ m.filterMap f → k ∈ m :=
  Raw₀.contains_of_contains_filterMap ⟨m.1, _⟩ m.2

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).size ≤ m.size :=
  Raw₀.size_filterMap_le_size ⟨m.1, m.2.size_buckets_pos⟩ m.2

grind_pattern size_filterMap_le_size => (m.filterMap f).size

theorem size_filterMap_eq_size_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).size = m.size ↔ ∀ (a : α) (h : a ∈ m), (f a (m.get a h)).isSome :=
  Raw₀.size_filterMap_eq_size_iff ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).get? k = (m.get? k).bind (f k) :=
  Raw₀.get?_filterMap ⟨m.1, _⟩ m.2

theorem isSome_apply_of_mem_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    ∀ (h' : k ∈ m.filterMap f),
      (f k (m.get k (mem_of_mem_filterMap h'))).isSome :=
  Raw₀.isSome_apply_of_contains_filterMap ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (m.filterMap f).get k h' =
      (f k (m.get k (mem_of_mem_filterMap h'))).get
        (isSome_apply_of_mem_filterMap h') :=
  Raw₀.get_filterMap ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get!_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} [Inhabited (γ k)] :
    (m.filterMap f).get! k = ((m.get? k).bind (f k)).get! :=
  Raw₀.get!_filterMap ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {fallback : γ k} :
    (m.filterMap f).getD k fallback = ((m.get? k).bind (f k)).getD fallback :=
  Raw₀.getD_filterMap ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome) :=
  Raw₀.getKey?_filterMap ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getKey_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (m.filterMap f).getKey k h' = m.getKey k (mem_of_mem_filterMap h') :=
  Raw₀.getKey_filterMap ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey!_filterMap [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  Raw₀.getKey!_filterMap ⟨m.1, _⟩ m.2

@[grind =]
theorem getKeyD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  Raw₀.getKeyD_filterMap ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {γ : Type w} {m : DHashMap α (fun _ => β)}

@[grind =]
theorem isEmpty_filterMap_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).isEmpty ↔ ∀ k h, f (m.getKey k h) (get m k h) = none :=
  Raw₀.Const.isEmpty_filterMap_iff ⟨m.1, _⟩ m.2

theorem isEmpty_filterMap_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).isEmpty = false ↔ ∃ k h, (f (m.getKey k h) (get m k h)).isSome :=
  Raw₀.Const.isEmpty_filterMap_eq_false_iff ⟨m.1, _⟩ m.2

-- TODO: `contains_filterMap` is missing

@[grind =]
theorem mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f (m.getKey k h) (Const.get m k h)).isSome :=
  Raw₀.Const.contains_filterMap_iff ⟨m.1, _⟩ m.2

-- TODO: `size_filterMap_le_size` is missing

theorem size_filterMap_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} :
    (m.filterMap f).size = m.size ↔ ∀ k h, (f (m.getKey k h) (Const.get m k h)).isSome :=
  Raw₀.Const.size_filterMap_eq_size_iff ⟨m.1, _⟩ m.2

@[simp]
theorem get?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    Const.get? (m.filterMap f) k = (Const.get? m k).pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  Raw₀.Const.get?_filterMap ⟨m.1, _⟩ m.2

/-- Simpler variant of `get?_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem get?_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    Const.get? (m.filterMap f) k = (Const.get? m k).bind fun x => f k x := by
  simp [get?_filterMap]

theorem get?_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get? (m.filterMap f) k = (Const.get? m k).bind (f k') :=
  Raw₀.Const.get?_filterMap_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

theorem isSome_apply_of_mem_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ m.filterMap f),
      (f (m.getKey k (mem_of_mem_filterMap h))
        (Const.get m k (mem_of_mem_filterMap h))).isSome :=
  Raw₀.Const.isSome_apply_of_contains_filterMap ⟨m.1, _⟩ m.2

@[simp]
theorem get_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (m.filterMap f) k h =
      (f (m.getKey k (mem_of_mem_filterMap h))
        (Const.get m k (mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  Raw₀.Const.get_filterMap ⟨m.1, _⟩ m.2

/-- Simpler variant of `get_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem get_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (m.filterMap f) k h =
      (f k (Const.get m k (mem_of_mem_filterMap h))).get (by simpa using isSome_apply_of_mem_filterMap h) := by
  simp [get_filterMap]

theorem get!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (m.filterMap f) k =
      ((Const.get? m k).pbind (fun x h' =>
        f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  Raw₀.Const.get!_filterMap ⟨m.1, _⟩ m.2

/-- Simpler variant of `get!_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem get!_filterMap' [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (m.filterMap f) k = ((Const.get? m k).bind (f k) ).get!:= by
  simp [get!_filterMap]

theorem get!_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get! (m.filterMap f) k = ((Const.get? m k).bind (f k')).get! :=
  Raw₀.Const.get!_filterMap_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

theorem getD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (m.filterMap f) k fallback =
      ((Const.get? m k).pbind (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  Raw₀.Const.getD_filterMap ⟨m.1, _⟩ m.2

/-- Simpler variant of `getD_filterMap` when `LawfulBEq` is available. -/
@[grind =]
theorem getD_filterMap' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (m.filterMap f) k fallback = ((Const.get? m k).bind (f k)).getD fallback := by
  simp [getD_filterMap]

theorem getD_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    Const.getD (m.filterMap f) k fallback = ((Const.get? m k).bind (f k')).getD fallback :=
  Raw₀.Const.getD_filterMap_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

theorem toList_filterMap
    {f : α → β → Option γ} :
    (Const.toList (m.filterMap fun k v => f k v)).Perm
      ((Const.toList m).filterMap (fun p => (f p.1 p.2).map (fun x => (p.1, x)))) :=
  Raw₀.Const.toList_filterMap ⟨m.1, m.2.size_buckets_pos⟩

@[grind =]
theorem getKey?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome) :=
  Raw₀.Const.getKey?_filterMap ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  Raw₀.Const.getKey!_filterMap ⟨m.1, _⟩ m.2

@[grind =]
theorem getKeyD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k fallback : α} :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  Raw₀.Const.getKeyD_filterMap ⟨m.1, _⟩ m.2

end Const

end filterMap

section filter

theorem filterMap_equiv_filter {f : (a : α) → β a → Bool} :
    m.filterMap (fun k => Option.guard (fun v => f k v)) ~m m.filter f :=
  ⟨Raw₀.filterMap_equiv_filter ⟨m.1, m.2.size_buckets_pos⟩⟩

theorem toList_filter {f : (a : α) → β a → Bool} :
    (m.filter f).toList.Perm (m.toList.filter (fun p => f p.1 p.2)) :=
  Raw₀.toList_filter ⟨m.1, m.2.size_buckets_pos⟩

theorem keys_filter_key {f : α → Bool} :
    (m.filter fun k _ => f k).keys.Perm (m.keys.filter f) :=
  Raw₀.keys_filter_key ⟨m.1, m.2.size_buckets_pos⟩

@[grind =]
theorem isEmpty_filter_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} :
    (m.filter f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ m), f k (m.get k h) = false :=
  Raw₀.isEmpty_filter_iff ⟨m.1, _⟩ m.2

theorem isEmpty_filter_eq_false_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} :
    (m.filter f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), f k (m.get k h) = true :=
  Raw₀.isEmpty_filter_eq_false_iff ⟨m.1, _⟩ m.2

theorem isEmpty_filter_key_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter (fun a _ => f a)).isEmpty ↔
      ∀ (k : α) (h : k ∈ m), f (m.getKey k h) = false :=
  Raw₀.isEmpty_filter_key_iff ⟨m.1, _⟩ m.2

theorem isEmpty_filter_key_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter (fun a _ => f a)).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), f (m.getKey k h) :=
  Raw₀.isEmpty_filter_key_eq_false_iff ⟨m.1, _⟩ m.2

@[grind =]
theorem contains_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).contains k = (m.get? k).any (f k) :=
  Raw₀.contains_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem mem_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ h, f k (m.get k h) := by
  simp only [mem_iff_contains, contains_filter, Option.any_eq_true_iff_get,
    ← contains_eq_isSome_get?, get_get?]

theorem mem_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    k ∈ m.filter (fun a _ => f a) ↔ ∃ h, f (m.getKey k h) :=
  Raw₀.contains_filter_key_iff ⟨m.1, _⟩ m.2

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).contains k = true → m.contains k = true :=
  Raw₀.contains_of_contains_filter ⟨m.1, _⟩ m.2

theorem mem_of_mem_filter [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} {k : α} :
    k ∈ (m.filter f) → k ∈ m :=
  Raw₀.contains_of_contains_filter ⟨m.1, _⟩ m.2

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} :
    (m.filter f).size ≤ m.size :=
  Raw₀.size_filter_le_size ⟨m.1, m.2.size_buckets_pos⟩ m.2

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} :
    (m.filter f).size = m.size ↔ ∀ k h, f k (m.get k h) :=
  Raw₀.size_filter_eq_size_iff ⟨m.1, _⟩ m.2

theorem filter_equiv_self_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} :
    m.filter f ~m m ↔ ∀ k h, f k (m.get k h) :=
  ⟨fun h => (Raw₀.filter_equiv_self_iff ⟨m.1, _⟩ m.2).mp h.1,
    fun h => ⟨(Raw₀.filter_equiv_self_iff ⟨m.1, _⟩ m.2).mpr h⟩⟩

theorem filter_key_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → Bool} :
    m.filter (fun k _ => f k) ~m m ↔ ∀ k h, f (m.getKey k h) :=
  ⟨fun h => (Raw₀.filter_key_equiv_self_iff ⟨m.1, _⟩ m.2).mp h.1,
    fun h => ⟨(Raw₀.filter_key_equiv_self_iff ⟨m.1, _⟩ m.2).mpr h⟩⟩

theorem size_filter_key_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} :
    (m.filter fun k _ => f k).size = m.size ↔ ∀ (k : α) (h : k ∈ m), f (m.getKey k h) :=
  Raw₀.size_filter_key_eq_size_iff ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).get? k = (m.get? k).filter (f k) :=
  Raw₀.get?_filter ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (m.filter f).get k h' = m.get k (mem_of_mem_filter h') :=
  Raw₀.get_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem get!_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} [Inhabited (β k)] :
    (m.filter f).get! k = ((m.get? k).filter (f k)).get! :=
  Raw₀.get!_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem getD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {fallback : β k} :
    (m.filter f).getD k fallback = ((m.get? k).filter (f k)).getD fallback :=
  Raw₀.getD_filter ⟨m.1, _⟩ m.2

theorem keys_filter [LawfulBEq α] {f : (a : α) → β a → Bool} :
    (m.filter f).keys.Perm
      (m.keys.attach.filter (fun ⟨x, h'⟩ => f x (m.get x (mem_of_mem_keys h')))).unattach :=
  Raw₀.keys_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h'))) :=
  Raw₀.getKey?_filter ⟨m.1, _⟩ m.2

theorem getKey?_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f :=
  Raw₀.getKey?_filter_key ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getKey_filter [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (m.filter f).getKey k h' = m.getKey k (mem_of_mem_filter h') :=
  Raw₀.getKey_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey!_filter [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h')))).get! :=
  Raw₀.getKey!_filter ⟨m.1, _⟩ m.2

theorem getKey!_filter_key [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! :=
  Raw₀.getKey!_filter_key ⟨m.1, _⟩ m.2

@[grind =]
theorem getKeyD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (mem_of_getKey?_eq_some h')))).getD fallback :=
  Raw₀.getKeyD_filter ⟨m.1, _⟩ m.2

theorem getKeyD_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback :=
  Raw₀.getKeyD_filter_key ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {γ : Type w} {m : DHashMap α (fun _ => β)}

@[grind =]
theorem isEmpty_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ m), f (m.getKey k h) (Const.get m k h) = false :=
  Raw₀.Const.isEmpty_filter_iff ⟨m.1, _⟩ m.2

theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ m), (f (m.getKey k h) (Const.get m k h)) = true :=
  Raw₀.Const.isEmpty_filter_eq_false_iff ⟨m.1, _⟩ m.2

-- TODO: `contains_filter` is missing

@[grind =]
theorem mem_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    k ∈ m.filter f ↔ ∃ (h' : k ∈ m),
      f (m.getKey k h') (Const.get m k h') :=
  Raw₀.Const.contains_filter_iff ⟨m.1, _⟩ m.2

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size ≤ m.size :=
  Raw₀.Const.size_filter_le_size ⟨m.1, m.2.size_buckets_pos⟩ m.2

grind_pattern size_filter_le_size => (m.filter f).size

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    (m.filter f).size = m.size ↔ ∀ (a : α) (h : a ∈ m),
      f (m.getKey a h) (Const.get m a h) :=
  Raw₀.Const.size_filter_eq_size_iff ⟨m.1, _⟩ m.2

theorem filter_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} :
    m.filter f ~m m ↔ ∀ k h, f (m.getKey k h) (Const.get m k h) :=
  ⟨fun h => (Raw₀.Const.filter_equiv_self_iff ⟨m.1, _⟩ m.2).mp h.1,
    fun h => ⟨(Raw₀.Const.filter_equiv_self_iff ⟨m.1, _⟩ m.2).mpr h⟩ ⟩

theorem get?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  Raw₀.Const.get?_filter ⟨m.1, _⟩ m.2

/-- Simpler variant of `get?_filter` when `LawfulBEq` is available. -/
@[simp, grind =]
theorem get?_filter' [LawfulBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    Const.get? (m.filter f) k = (Const.get? m k).filter (f k) := by
  simp [get?_filter]

theorem get?_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} :
    m.getKey? k = some k' →
      Const.get? (m.filter f) k = (Const.get? m k).filter (fun x => f k' x) :=
  Raw₀.Const.get?_filter_of_getKey?_eq_some ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {h'} :
    Const.get (m.filter f) k h' = Const.get m k (mem_of_mem_filter h') :=
  Raw₀.Const.get_filter ⟨m.1, _⟩ m.2

theorem get!_filter [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    Const.get! (m.filter f) k =
      ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  Raw₀.Const.get!_filter ⟨m.1, _⟩ m.2

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
  Raw₀.Const.get!_filter_of_getKey?_eq_some ⟨m.1, _⟩ m.2

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} :
    Const.getD (m.filter f) k fallback = ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  Raw₀.Const.getD_filter ⟨m.1, _⟩ m.2

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
  Raw₀.Const.getD_filter_of_getKey?_eq_some ⟨m.1, _⟩ m.2

theorem toList_filter {f : α → β → Bool} :
    (toList (m.filter f)).Perm
      ((toList m).filter (fun p => f p.1 p.2)) :=
  Raw₀.Const.toList_filter ⟨m.1, m.2.size_buckets_pos⟩

theorem keys_filter [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    (m.filter f).keys.Perm
      (m.keys.attach.filter (fun ⟨x, h'⟩ => f x (get m x (mem_of_mem_keys h')))).unattach :=
  Raw₀.Const.keys_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h')))) :=
  Raw₀.Const.getKey?_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem getKey!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))))).get! :=
  Raw₀.Const.getKey!_filter ⟨m.1, _⟩ m.2

@[grind =]
theorem getKeyD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k fallback : α} :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (mem_of_getKey?_eq_some h'))))).getD fallback :=
  Raw₀.Const.getKeyD_filter ⟨m.1, _⟩ m.2

end Const

end filter

section map

variable {γ : α → Type w} {δ : α → Type w'}

theorem map_id_equiv : m.map (fun _ v => v) ~m m :=
  ⟨Raw₀.map_id_equiv ⟨m.1, m.2.size_buckets_pos⟩⟩

theorem map_map_equiv {f : (a : α) → β a → γ a} {g : (a : α) → γ a → δ a} :
    (m.map f).map g ~m m.map fun k v => g k (f k v) :=
  ⟨Raw₀.map_map_equiv ⟨m.1, m.2.size_buckets_pos⟩⟩

theorem toList_map {f : (a : α) → β a → γ a} :
    (m.map f).toList.Perm (m.toList.map (fun p => ⟨p.1, f p.1 p.2⟩)) :=
  Raw₀.toList_map ⟨m.1, m.2.size_buckets_pos⟩

theorem keys_map {f : (a : α) → β a → γ a} : (m.map f).keys.Perm m.keys :=
  Raw₀.keys_map ⟨m.1, m.2.size_buckets_pos⟩

theorem filterMap_equiv_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} :
    (m.filterMap (fun k v => some (f k v))) ~m m.map f :=
  ⟨Raw₀.filterMap_equiv_map ⟨m.1, m.2.size_buckets_pos⟩ m.2⟩

@[simp, grind =]
theorem isEmpty_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} :
    (m.map f).isEmpty = m.isEmpty :=
  Raw₀.isEmpty_map ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[grind =]
theorem contains_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).contains k = m.contains k :=
  Raw₀.contains_map ⟨m.1, _⟩ m.2

theorem contains_of_contains_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).contains k = true → m.contains k = true :=
  Raw₀.contains_of_contains_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem mem_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ m.map f ↔ k ∈ m := by
  simp only [mem_iff_contains, contains_map]

theorem mem_of_mem_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ m.map f → k ∈ m :=
  Raw₀.contains_of_contains_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem size_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} :
    (m.map f).size = m.size :=
  Raw₀.size_map ⟨m.1, m.2.size_buckets_pos⟩ m.2

@[simp, grind =]
theorem get?_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).get? k = (m.get? k).map (f k) :=
  Raw₀.get?_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem get_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (m.map f).get k h' = f k (m.get k (mem_of_mem_map h')) :=
  Raw₀.get_map ⟨m.1, _⟩ m.2

@[grind =]
theorem get!_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} [Inhabited (γ k)] :
    (m.map f).get! k = ((m.get? k).map (f k)).get! :=
  Raw₀.get!_map ⟨m.1, _⟩ m.2

@[grind =]
theorem getD_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {fallback : γ k} :
    (m.map f).getD k fallback = ((m.get? k).map (f k)).getD fallback :=
  Raw₀.getD_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getKey?_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).getKey? k = m.getKey? k :=
  Raw₀.getKey?_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getKey_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (m.map f).getKey k h' = m.getKey k (mem_of_mem_map h') :=
  Raw₀.getKey_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getKey!_map [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : (a : α) → β a → γ a} {k : α} :
    (m.map f).getKey! k = m.getKey! k :=
  Raw₀.getKey!_map ⟨m.1, _⟩ m.2

@[simp, grind =]
theorem getKeyD_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k fallback : α} :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback :=
  Raw₀.getKeyD_map ⟨m.1, _⟩ m.2

namespace Const

variable {β : Type v} {γ : Type w} {m : DHashMap α fun _ => β}

@[simp, grind =]
theorem get?_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    Const.get? (m.map f) k = (Const.get? m k).map (f k) :=
  Raw₀.Const.get?_map ⟨m.1, _⟩ m.2

/-- Variant of `get?_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem get?_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} :
    Const.get? (m.map f) k = (Const.get? m k).pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h')) :=
  Raw₀.Const.get?_map' ⟨m.1, _⟩ m.2

theorem get?_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get? (m.map f) k = (Const.get? m k).map (f k') :=
  Raw₀.Const.get?_map_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

@[simp, grind =]
theorem get_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    Const.get (m.map f) k h' = f k (Const.get m k (mem_of_mem_map h')) :=
  Raw₀.Const.get_map ⟨m.1, _⟩ m.2

/-- Variant of `get_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
@[simp (low)]
theorem get_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {h'} :
    Const.get (m.map f) k h' =
      f (m.getKey k (mem_of_mem_map h')) (Const.get m k (mem_of_mem_map h')) :=
  Raw₀.Const.get_map' ⟨m.1, _⟩ m.2

@[grind =]
theorem get!_map [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (m.map f) k = ((Const.get? m k).map (f k)).get! :=
  Raw₀.Const.get!_map ⟨m.1, _⟩ m.2

/-- Variant of `get!_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem get!_map' [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (m.map f) k =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_mem h'))).get! :=
  Raw₀.Const.get!_map' ⟨m.1, _⟩ m.2

theorem get!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    Const.get! (m.map f) k = ((Const.get? m k).map (f k')).get! :=
  Raw₀.Const.get!_map_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

@[grind =]
theorem getD_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k)).getD fallback :=
  Raw₀.Const.getD_map ⟨m.1, _⟩ m.2

/-- Variant of `getD_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getD_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (m.map f) k fallback =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  Raw₀.Const.getD_map' ⟨m.1, _⟩ m.2

theorem getD_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') :
    Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k')).getD fallback :=
  Raw₀.Const.getD_map_of_getKey?_eq_some ⟨m.1, _⟩ m.2 h

theorem toList_map {m : DHashMap α fun _ => β}
    {f : α → β → γ} :
    (Raw.Const.toList (m.map f).1).Perm
      ((Raw.Const.toList m.1).map (fun p => (p.1, f p.1 p.2))) :=
  Raw₀.Const.toList_map ⟨m.1, m.2.size_buckets_pos⟩

end Const

end map

end Std.DHashMap
