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

This file contains lemmas about `Std.Data.DHashMap.Raw`. Most of the lemmas require
`EquivBEq α` and `LawfulHashable α` for the key type `α`. The easiest way to obtain these instances
is to provide an instance of `LawfulBEq α`.
-/

open Std.DHashMap.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v}

namespace Std.DHashMap

namespace Internal.Raw

open Lean Elab Meta Tactic

private def baseNames : Array Name :=
  #[``Raw.empty_eq, ``Raw.emptyc_eq,
    ``insert_eq, ``insertIfNew_eq, ``erase_eq, ``contains_eq,
    ``containsThenInsert_fst_eq, ``containsThenInsert_snd_eq,
    ``containsThenInsertIfNew_fst_eq, ``containsThenInsertIfNew_snd_eq,
    ``getThenInsertIfNew?_fst_eq, ``getThenInsertIfNew?_snd_eq,
    ``Const.getThenInsertIfNew?_snd_eq, ``Const.getThenInsertIfNew?_fst_eq,
    ``map_eq, ``filter_eq, ``filterMap_eq,
    ``get?_eq, ``get_eq, ``get!_eq, ``getD_eq,
    ``Const.get?_eq, ``Const.get_eq, ``Const.getD_eq, ``Const.get!_eq,
    ``getKey?_eq, ``getKey_eq, ``getKey!_eq, ``getKeyD_eq,
    ``insertMany_eq, ``Const.insertMany_eq, ``Const.insertManyIfNewUnit_eq,
    ``ofList_eq, ``Const.ofList_eq, ``Const.unitOfList_eq,
    ``alter_eq, ``Const.alter_eq, ``modify_eq, ``Const.modify_eq,
    ``Subtype.eta]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_raw" ("using" term)? : tactic

open Internal.Raw₀

macro_rules
| `(tactic| simp_to_raw $[using $using?]?) => do
  `(tactic|
    (try simp (discharger := with_reducible wf_trivial) only [$[$(Array.map Lean.mkIdent baseNames):term],*]
     $[apply $(using?.toArray):term];*)
     <;> with_reducible try wf_trivial)

end Internal.Raw

namespace Raw

open Internal.Raw₀ Internal.Raw

variable {m : Raw α β}

@[simp]
theorem size_empty {c} : (empty c : Raw α β).size = 0 := by
  simp_to_raw using Raw₀.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α β).size = 0 :=
  size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) := by
  simp [isEmpty]

variable [BEq α] [Hashable α]

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty := by
  simp_to_raw using Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).isEmpty = false := by
  simp_to_raw using Raw₀.isEmpty_insert

theorem mem_iff_contains {m : Raw α β} {a : α} :
    a ∈ m ↔ m.contains a := Iff.rfl

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b := by
  simp_to_raw using Raw₀.contains_congr

theorem mem_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m := by
  simp [mem_iff_contains, contains_congr h hab]

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α β).contains a = false := by
  simp_to_raw using Raw₀.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α β) := by
  simp [mem_iff_contains]

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  contains_empty

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α β) :=
  not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty → m.contains a = false := by
  simp_to_raw using Raw₀.contains_of_isEmpty ⟨m, _⟩

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty → ¬a ∈ m := by
  simpa [mem_iff_contains] using contains_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = false ↔ ∃ a, m.contains a = true := by
  simp_to_raw using Raw₀.isEmpty_eq_false_iff_exists_contains_eq_true ⟨m, _⟩

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = false ↔ ∃ a, a ∈ m := by
  simpa [mem_iff_contains] using isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = true ↔ ∀ a, m.contains a = false := by
  simp_to_raw using Raw₀.isEmpty_iff_forall_contains ⟨m, _⟩

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m := by
  simpa [mem_iff_contains] using isEmpty_iff_forall_contains h

@[simp] theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p m = m.insert p.1 p.2 := rfl

@[simp] theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : Raw α β).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {a k : α} {v : β k} :
    (m.insert k v).contains a = (k == a || m.contains a) := by
  simp_to_raw using Raw₀.contains_insert

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m := by
  simp [mem_iff_contains, contains_insert h]

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {a k : α} {v : β k} :
    (m.insert k v).contains a → (k == a) = false → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_insert h

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).contains k := by
  simp_to_raw using Raw₀.contains_insert_self

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    k ∈ m.insert k v := by
  simp [mem_iff_contains, contains_insert_self h]

theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    m.size ≤ (m.insert k v).size := by
  simp_to_raw using Raw₀.size_le_size_insert ⟨m, _⟩ h

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).size ≤ m.size + 1 := by
  simp_to_raw using Raw₀.size_insert_le ⟨m, _⟩ h

@[simp]
theorem erase_empty {k : α} {c : Nat} : (empty c : Raw α β).erase k = empty c := by
  rw [erase_eq (by wf_trivial)]
  exact congrArg Subtype.val Raw₀.erase_empty

@[simp]
theorem erase_emptyc {k : α} : (∅ : Raw α β).erase k = ∅ :=
  erase_empty

@[simp]
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) := by
  simp_to_raw using Raw₀.isEmpty_erase

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) := by
  simp_to_raw using Raw₀.contains_erase

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [mem_iff_contains, contains_erase h]

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).contains a → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    a ∈ m.erase k → a ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_erase h

theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).size ≤ m.size := by
  simp_to_raw using Raw₀.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.size ≤ (m.erase k).size + 1 := by
  simp_to_raw using Raw₀.size_le_size_erase ⟨m, _⟩

@[simp]
theorem containsThenInsert_fst (h : m.WF) {k : α} {v : β k} :
    (m.containsThenInsert k v).1 = m.contains k := by
  simp_to_raw using Raw₀.containsThenInsert_fst

@[simp]
theorem containsThenInsert_snd (h : m.WF) {k : α} {v : β k} :
    (m.containsThenInsert k v).2 = m.insert k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.containsThenInsert_snd _)

@[simp]
theorem containsThenInsertIfNew_fst (h : m.WF) {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k := by
  simp_to_raw using Raw₀.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsertIfNew_snd (h : m.WF) {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.containsThenInsertIfNew_snd _)

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} {c} : (empty c : Raw α β).get? a = none := by
  simp_to_raw using Raw₀.get?_empty

@[simp]
theorem get?_emptyc [LawfulBEq α] {a : α} : (∅ : Raw α β).get? a = none :=
  get?_empty

theorem get?_of_isEmpty [LawfulBEq α] (h : m.WF) {a : α} : m.isEmpty = true → m.get? a = none := by
  simp_to_raw using Raw₀.get?_of_isEmpty ⟨m, _⟩

theorem get?_insert [LawfulBEq α] (h : m.WF) {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a := by
  simp_to_raw using Raw₀.get?_insert

@[simp]
theorem get?_insert_self [LawfulBEq α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).get? k = some v := by
  simp_to_raw using Raw₀.get?_insert_self

theorem contains_eq_isSome_get? [LawfulBEq α] (h : m.WF) {a : α} :
    m.contains a = (m.get? a).isSome := by
  simp_to_raw using Raw₀.contains_eq_isSome_get?

theorem get?_eq_none_of_contains_eq_false [LawfulBEq α] (h : m.WF) {a : α} :
    m.contains a = false → m.get? a = none := by
  simp_to_raw using Raw₀.get?_eq_none

theorem get?_eq_none [LawfulBEq α] (h : m.WF) {a : α} : ¬a ∈ m → m.get? a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [LawfulBEq α] (h : m.WF) {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  simp_to_raw using Raw₀.get?_erase

@[simp]
theorem get?_erase_self [LawfulBEq α] (h : m.WF) {k : α} : (m.erase k).get? k = none := by
  simp_to_raw using Raw₀.get?_erase_self

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

@[simp]
theorem get?_empty {a : α} {c} : get? (empty c : Raw α (fun _ => β)) a = none := by
  simp_to_raw using Raw₀.Const.get?_empty

@[simp]
theorem get?_emptyc {a : α} : get? (∅ : Raw α (fun _ => β)) a = none :=
  get?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → get? m a = none := by
  simp_to_raw using Raw₀.Const.get?_of_isEmpty ⟨m, _⟩

theorem get?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a := by
  simp_to_raw using Raw₀.Const.get?_insert

@[simp]
theorem get?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    get? (m.insert k v) k = some v := by
  simp_to_raw using Raw₀.Const.get?_insert_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (get? m a).isSome := by
  simp_to_raw using Raw₀.Const.contains_eq_isSome_get?

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → get? m a = none := by
  simp_to_raw using Raw₀.Const.get?_eq_none

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → get? m a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a := by
  simp_to_raw using Raw₀.Const.get?_erase

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    get? (m.erase k) k = none := by
  simp_to_raw using Raw₀.Const.get?_erase_self

theorem get?_eq_get? [LawfulBEq α] (h : m.WF) {a : α} : get? m a = m.get? a := by
  simp_to_raw using Raw₀.Const.get?_eq_get?

theorem get?_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) :
    get? m a = get? m b := by
  simp_to_raw using Raw₀.Const.get?_congr

end Const

theorem get_insert [LawfulBEq α] (h : m.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).get a h₁ =
      if h₂ : k == a then
        cast (congrArg β (eq_of_beq h₂)) v
      else
        m.get a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.get_insert ⟨m, _⟩

@[simp]
theorem get_insert_self [LawfulBEq α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).get k (mem_insert_self h) = v := by
  simp_to_raw using Raw₀.get_insert_self ⟨m, _⟩

@[simp]
theorem get_erase [LawfulBEq α] (h : m.WF) {k a : α} {h'} :
    (m.erase a).get k h' = m.get k (mem_of_mem_erase h h') := by
  simp_to_raw using Raw₀.get_erase ⟨m, _⟩

theorem get?_eq_some_get [LawfulBEq α] (h : m.WF) {a : α} {h} : m.get? a = some (m.get a h) := by
  simp_to_raw using Raw₀.get?_eq_some_get

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v else get m a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.Const.get_insert ⟨m, _⟩

@[simp]
theorem get_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β} :
    get (m.insert k v) k (mem_insert_self h) = v := by
  simp_to_raw using Raw₀.Const.get_insert_self ⟨m, _⟩

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    get (m.erase k) a h' = get m a (mem_of_mem_erase h h') := by
  simp_to_raw using Raw₀.Const.get_erase ⟨m, _⟩

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h : a ∈ m} :
    get? m a = some (get m a h) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_get

theorem get_eq_get [LawfulBEq α] (h : m.WF) {a : α} {h} : get m a h = m.get a h := by
  simp_to_raw using Raw₀.Const.get_eq_get

theorem get_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((mem_congr h hab).1 h') := by
  simp_to_raw using Raw₀.Const.get_congr

end Const

@[simp]
theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] {c} :
    (empty c : Raw α β).get! a = default := by
  simp_to_raw using Raw₀.get!_empty

@[simp]
theorem get!_emptyc [LawfulBEq α] {a : α} [Inhabited (β a)] :
    (∅ : Raw α β).get! a = default :=
  get!_empty

theorem get!_of_isEmpty [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    m.isEmpty = true → m.get! a = default := by
  simp_to_raw using Raw₀.get!_of_isEmpty ⟨m, _⟩

theorem get!_insert [LawfulBEq α] (h : m.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insert k v).get! a = if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.get! a := by
  simp_to_raw using Raw₀.get!_insert

@[simp]
theorem get!_insert_self [LawfulBEq α] (h : m.WF) {k : α} [Inhabited (β k)] {v : β k} :
    (m.insert k v).get! k = v := by
  simp_to_raw using Raw₀.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_raw using Raw₀.get!_eq_default

theorem get!_eq_default [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    ¬a ∈ m → m.get! a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [LawfulBEq α] (h : m.WF) {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a := by
  simp_to_raw using Raw₀.get!_erase

@[simp]
theorem get!_erase_self [LawfulBEq α] (h : m.WF) {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default := by
  simp_to_raw using Raw₀.get!_erase_self

theorem get?_eq_some_get!_of_contains [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) := by
  simp_to_raw using Raw₀.get?_eq_some_get!

theorem get?_eq_some_get! [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    a ∈ m → m.get? a = some (m.get! a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! := by
  simp_to_raw using Raw₀.get!_eq_get!_get?

theorem get_eq_get! [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a := by
  simp_to_raw using Raw₀.get_eq_get!

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

@[simp]
theorem get!_empty [Inhabited β] {a : α} {c} : get! (empty c : Raw α (fun _ => β)) a = default := by
  simp_to_raw using Raw₀.Const.get!_empty

@[simp]
theorem get!_emptyc [Inhabited β] {a : α} : get! (∅ : Raw α (fun _ => β)) a = default :=
  get!_empty

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    m.isEmpty = true → get! m a = default := by
  simp_to_raw using Raw₀.Const.get!_of_isEmpty ⟨m, _⟩

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a := by
  simp_to_raw using Raw₀.Const.get!_insert

@[simp]
theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k : α} {v : β} :
    get! (m.insert k v) k = v := by
  simp_to_raw using Raw₀.Const.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (h : m.WF) {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_raw using Raw₀.Const.get!_eq_default

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    ¬a ∈ m → get! m a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a := by
  simp_to_raw using Raw₀.Const.get!_erase

@[simp]
theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k : α} :
    get! (m.erase k) k = default := by
  simp_to_raw using Raw₀.Const.get!_erase_self

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF)
    {a : α} : m.contains a = true → get? m a = some (get! m a) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_get!

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    a ∈ m → get? m a = some (get! m a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    get! m a = (get? m a).get! := by
  simp_to_raw using Raw₀.Const.get!_eq_get!_get?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} {h} :
    get m a h = get! m a := by
  simp_to_raw using Raw₀.Const.get_eq_get!

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] (h : m.WF) {a : α} :
    get! m a = m.get! a := by
  simp_to_raw using Raw₀.Const.get!_eq_get!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a b : α}
    (hab : a == b) : get! m a = get! m b := by
  simp_to_raw using Raw₀.Const.get!_congr

end Const

@[simp]
theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} {c} :
    (empty c : Raw α β).getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_empty

@[simp]
theorem getD_emptyc [LawfulBEq α] {a : α} {fallback : β a} :
    (∅ : Raw α β).getD a fallback = fallback :=
  getD_empty

theorem getD_of_isEmpty [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} :
    m.isEmpty = true → m.getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_of_isEmpty ⟨m, _⟩

theorem getD_insert [LawfulBEq α] (h : m.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insert k v).getD a fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.getD a fallback := by
  simp_to_raw using Raw₀.getD_insert

@[simp]
theorem getD_insert_self [LawfulBEq α] (h : m.WF) {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_raw using Raw₀.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_eq_fallback

theorem getD_eq_fallback [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} :
    ¬a ∈ m → m.getD a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [LawfulBEq α] (h : m.WF) {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback := by
  simp_to_raw using Raw₀.getD_erase

@[simp]
theorem getD_erase_self [LawfulBEq α] (h : m.WF) {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback := by
  simp_to_raw using Raw₀.getD_erase_self

theorem get?_eq_some_getD_of_contains [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) := by
  simp_to_raw using Raw₀.get?_eq_some_getD

theorem get?_eq_some_getD [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} :
    a ∈ m → m.get? a = some (m.getD a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback := by
  simp_to_raw using Raw₀.getD_eq_getD_get?

theorem get_eq_getD [LawfulBEq α] (h : m.WF) {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback := by
  simp_to_raw using Raw₀.get_eq_getD

theorem get!_eq_getD_default [LawfulBEq α] (h : m.WF) {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  simp_to_raw using Raw₀.get!_eq_getD_default

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

@[simp]
theorem getD_empty {a : α} {fallback : β} {c} :
    getD (empty c : Raw α (fun _ => β)) a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_empty

@[simp]
theorem getD_emptyc {a : α} {fallback : β} : getD (∅ : Raw α (fun _ => β)) a fallback = fallback :=
  getD_empty

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    m.isEmpty = true → getD m a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_of_isEmpty ⟨m, _⟩

theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback := by
  simp_to_raw using Raw₀.Const.getD_insert

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {fallback v : β} :
   getD (m.insert k v) k fallback = v := by
  simp_to_raw using Raw₀.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α}
    {fallback : β} : m.contains a = false → getD m a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_fallback

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    ¬a ∈ m → getD m a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback := by
  simp_to_raw using Raw₀.Const.getD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_erase_self

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α}
    {fallback : β} : m.contains a = true → get? m a = some (getD m a fallback) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_getD

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    a ∈ m → get? m a = some (getD m a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_getD_get?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback := by
  simp_to_raw using Raw₀.Const.get_eq_getD

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {a : α} :
    get! m a = getD m a default := by
  simp_to_raw using Raw₀.Const.get!_eq_getD_default

theorem getD_eq_getD [LawfulBEq α] (h : m.WF) {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_getD

theorem getD_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {a b : α} {fallback : β}
    (hab : a == b) : getD m a fallback = getD m b fallback := by
  simp_to_raw using Raw₀.Const.getD_congr

end Const

@[simp]
theorem getKey?_empty {a : α} {c} :
    (empty c : Raw α β).getKey? a = none := by
  simp_to_raw using Raw₀.getKey?_empty

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : Raw α β).getKey? a = none :=
  getKey?_empty

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey? a = none := by
  simp_to_raw using Raw₀.getKey?_of_isEmpty ⟨m, _⟩

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a := by
  simp_to_raw using Raw₀.getKey?_insert

@[simp]
theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k := by
  simp_to_raw using Raw₀.getKey?_insert_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome := by
  simp_to_raw using Raw₀.contains_eq_isSome_getKey?

theorem getKey?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    m.contains a = false → m.getKey? a = none := by
  simp_to_raw using Raw₀.getKey?_eq_none

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey? a = none := by
  simpa [mem_iff_contains] using getKey?_eq_none_of_contains_eq_false h

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a := by
  simp_to_raw using Raw₀.getKey?_erase

@[simp]
theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    (m.erase k).getKey? k = none := by
  simp_to_raw using Raw₀.getKey?_erase_self

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} :
    (m.getKey? a).all (· == a) := by
  simp_to_raw using Raw₀.getKey?_beq

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} (h' : k == k') :
    m.getKey? k = m.getKey? k' := by
  simp_to_raw using Raw₀.getKey?_congr

theorem getKey?_eq_some_of_contains [LawfulBEq α] (h : m.WF) {k : α} :
    m.contains k → m.getKey? k = some k := by
  simp_to_raw using Raw₀.getKey?_eq_some

theorem getKey?_eq_some [LawfulBEq α] (h : m.WF) {k : α} :
    k ∈ m → m.getKey? k = some k := by
  simpa only [mem_iff_contains] using getKey?_eq_some_of_contains h

theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.getKey_insert ⟨m, _⟩

@[simp]
theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insert k v).getKey k (mem_insert_self h) = k := by
  simp_to_raw using Raw₀.getKey_insert_self ⟨m, _⟩

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {h'} :
    (m.erase a).getKey k h' = m.getKey k (mem_of_mem_erase h h') := by
  simp_to_raw using Raw₀.getKey_erase ⟨m, _⟩

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h} :
    m.getKey? a = some (m.getKey a h) := by
  simp_to_raw using Raw₀.getKey?_eq_some_getKey

theorem getKey_beq [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} (h') :
    m.getKey a h' == a := by
  simp_to_raw using Raw₀.getKey_beq

theorem getKey_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k₁ k₂ : α}
    (h' : k₁ == k₂) (h₁ : k₁ ∈ m) :
    m.getKey k₁ h₁ = m.getKey k₂ (((mem_congr h h').mp h₁)) := by
  simp_to_raw using Raw₀.getKey_congr

theorem getKey_eq [LawfulBEq α] (h : m.WF) {k : α} (h') :
    m.getKey k h' = k := by
  simp_to_raw using Raw₀.getKey_eq

@[simp]
theorem getKey!_empty [Inhabited α] {a : α} {c} :
    (empty c : Raw α β).getKey! a = default := by
  simp_to_raw using Raw₀.getKey!_empty

@[simp]
theorem getKey!_emptyc [Inhabited α] {a : α} :
    (∅ : Raw α β).getKey! a = default :=
  getKey!_empty

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.isEmpty = true → m.getKey! a = default := by
  simp_to_raw using Raw₀.getKey!_of_isEmpty ⟨m, _⟩

theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} {v : β k} :
    (m.insert k v).getKey! a = if k == a then k else m.getKey! a := by
  simp_to_raw using Raw₀.getKey!_insert

@[simp]
theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k : α}
    {v : β k} :
    (m.insert k v).getKey! k = k := by
  simp_to_raw using Raw₀.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {a : α} :
    m.contains a = false → m.getKey! a = default := by
  simp_to_raw using Raw₀.getKey!_eq_default

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    ¬a ∈ m → m.getKey! a = default := by
  simpa [mem_iff_contains] using getKey!_eq_default_of_contains_eq_false h

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a := by
  simp_to_raw using Raw₀.getKey!_erase

@[simp]
theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k : α} :
    (m.erase k).getKey! k = default := by
  simp_to_raw using Raw₀.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) := by
  simp_to_raw using Raw₀.getKey?_eq_some_getKey!

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKey!_of_contains h

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} :
    m.getKey! a = (m.getKey? a).get! := by
  simp_to_raw using Raw₀.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {a : α} {h} :
    m.getKey a h = m.getKey! a := by
  simp_to_raw using Raw₀.getKey_eq_getKey!

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {k₁ k₂ : α} (h' : k₁ == k₂) : m.getKey! k₁ = m.getKey! k₂ := by
  simp_to_raw using Raw₀.getKey!_congr

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] (h : m.WF) {k : α} :
    m.contains k → m.getKey! k = k := by
  simp_to_raw using Raw₀.getKey!_eq_of_contains

theorem getKey!_eq_of_mem [LawfulBEq α] [Inhabited α] (h : m.WF) {k : α} :
    k ∈ m → m.getKey! k = k := by
  simpa only [mem_iff_contains] using getKey!_eq_of_contains h

@[simp]
theorem getKeyD_empty {a fallback : α} {c} :
    (empty c : Raw α β).getKeyD a fallback = fallback := by
  simp_to_raw using Raw₀.getKeyD_empty

@[simp]
theorem getKeyD_emptyc {a fallback : α} :
    (∅ : Raw α β).getKeyD a fallback = fallback :=
  getKeyD_empty

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.isEmpty = true → m.getKeyD a fallback = fallback := by
  simp_to_raw using Raw₀.getKeyD_of_isEmpty ⟨m, _⟩

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} {v : β k} :
    (m.insert k v).getKeyD a fallback =
      if k == a then k else m.getKeyD a fallback := by
  simp_to_raw using Raw₀.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} {b : β a} :
    (m.insert a b).getKeyD a fallback = a := by
  simp_to_raw using Raw₀.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback := by
  simp_to_raw using Raw₀.getKeyD_eq_fallback

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    ¬a ∈ m → m.getKeyD a fallback = fallback := by
  simpa [mem_iff_contains] using getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback := by
  simp_to_raw using Raw₀.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback := by
  simp_to_raw using Raw₀.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) := by
  simp_to_raw using Raw₀.getKey?_eq_some_getKeyD

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    a ∈ m → m.getKey? a = some (m.getKeyD a fallback) := by
  simpa [mem_iff_contains] using getKey?_eq_some_getKeyD_of_contains h

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback := by
  simp_to_raw using Raw₀.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.WF) {a fallback : α} {h} :
    m.getKey a h = m.getKeyD a fallback := by
  simp_to_raw using Raw₀.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {a : α} :
    m.getKey! a = m.getKeyD a default := by
  simp_to_raw using Raw₀.getKey!_eq_getKeyD_default

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] (h : m.WF) {k₁ k₂ fallback : α}
    (h' : k₁ == k₂) : m.getKeyD k₁ fallback = m.getKeyD k₂ fallback := by
  simp_to_raw using Raw₀.getKeyD_congr

theorem getKeyD_eq_of_contains [LawfulBEq α] (h : m.WF) {k fallback : α} :
    m.contains k → m.getKeyD k fallback = k := by
  simp_to_raw using Raw₀.getKeyD_eq_of_contains

theorem getKeyD_eq_of_mem [LawfulBEq α] (h : m.WF) {k fallback : α} :
    k ∈ m → m.getKeyD k fallback = k := by
  simpa only [mem_iff_contains] using getKeyD_eq_of_contains h

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).isEmpty = false := by
  simp_to_raw using Raw₀.isEmpty_insertIfNew

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) := by
  simp_to_raw using Raw₀.contains_insertIfNew

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m := by
  simp [mem_iff_contains, contains_insertIfNew h]

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).contains k := by
  simp_to_raw using Raw₀.contains_insertIfNew_self

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    k ∈ m.insertIfNew k v := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_insertIfNew_self h

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α}
    {v : β k} : (m.insertIfNew k v).contains a → (k == a) = false → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_of_contains_insertIfNew h

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew' h

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    m.size ≤ (m.insertIfNew k v).size := by
  simp_to_raw using Raw₀.size_le_size_insertIfNew ⟨m, _⟩

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).size ≤ m.size + 1 := by
  simp_to_raw using Raw₀.size_insertIfNew_le

theorem get?_insertIfNew [LawfulBEq α] (h : m.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).get? a =
      if h : k == a ∧ ¬k ∈ m then some (cast (congrArg β (eq_of_beq h.1)) v)
      else m.get? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get?_insertIfNew ⟨m, _⟩

theorem get_insertIfNew [LawfulBEq α] (h : m.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.get a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get_insertIfNew ⟨m, _⟩

theorem get!_insertIfNew [LawfulBEq α] (h : m.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v else m.get! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get!_insertIfNew ⟨m, _⟩

theorem getD_insertIfNew [LawfulBEq α] (h : m.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getD_insertIfNew

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some v else get? m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get?_insertIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v
      else get m a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get_insertIfNew ⟨m, _⟩

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF) {k a : α}
    {v : β} : get! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then v else get! m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get!_insertIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then v else getD m a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getD_insertIfNew

end Const

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} :
    getKey? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some k else getKey? m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getKey?_insertIfNew

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a : α} {v : β k} {h₁} :
    getKey (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getKey_insertIfNew ⟨m, _⟩

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {k a : α}
    {v : β k} :
    getKey! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKey! m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getKey!_insertIfNew

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.WF) {k a fallback : α}
    {v : β k} :
    getKeyD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then k else getKeyD m a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getKeyD_insertIfNew

@[simp]
theorem getThenInsertIfNew?_fst [LawfulBEq α] (h : m.WF) {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k := by
  simp_to_raw using Raw₀.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd [LawfulBEq α] (h : m.WF) {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.getThenInsertIfNew?_snd _)

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

@[simp]
theorem getThenInsertIfNew?_fst (h : m.WF) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).1 = get? m k := by
  simp_to_raw using Raw₀.Const.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd (h : m.WF) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.Const.getThenInsertIfNew?_snd _)

end Const

@[simp]
theorem length_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.length = m.size := by
  simp_to_raw using Raw₀.length_keys ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.isEmpty = m.isEmpty := by
  simp_to_raw using Raw₀.isEmpty_keys ⟨m, h.size_buckets_pos⟩

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    m.keys.contains k = m.contains k := by
  simp_to_raw using Raw₀.contains_keys ⟨m, _⟩ h

@[simp]
theorem mem_keys [LawfulBEq α] [LawfulHashable α] (h : m.WF) {k : α} :
    k ∈ m.keys ↔ k ∈ m := by
  rw [mem_iff_contains]
  simp_to_raw using Raw₀.mem_keys ⟨m, _⟩ h

theorem distinct_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keys.Pairwise (fun a b => (a == b) = false) := by
  simp_to_raw using Raw₀.distinct_keys ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.map Sigma.fst = m.keys := by
  apply Raw₀.map_fst_toList_eq_keys ⟨m, h.size_buckets_pos⟩

@[simp, deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_sigma_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.map Sigma.fst = m.keys := by
  apply Raw₀.map_fst_toList_eq_keys ⟨m, h.size_buckets_pos⟩

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.length = m.size := by
  apply Raw₀.length_toList ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.isEmpty = m.isEmpty := by
  apply Raw₀.isEmpty_toList ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem mem_toList_iff_get?_eq_some [LawfulBEq α] (h : m.WF)
    {k : α} {v : β k} :
    ⟨k, v⟩ ∈ m.toList ↔ m.get? k = some v := by
  simp_to_raw using Raw₀.mem_toList_iff_get?_eq_some ⟨m, _⟩ h

theorem find?_toList_eq_some_iff_get?_eq_some [LawfulBEq α]
    (h : m.WF) {k : α} {v : β k} :
    m.toList.find? (·.1 == k) = some ⟨k, v⟩ ↔ m.get? k = some v := by
  simp_to_raw using Raw₀.find?_toList_eq_some_iff_get?_eq_some ⟨m, _⟩ h

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} :
    m.toList.find? (·.1 == k) = none ↔ m.contains k = false := by
  simp_to_raw using Raw₀.find?_toList_eq_none_iff_contains_eq_false ⟨m, _⟩ h

@[simp]
theorem find?_toList_eq_none_iff_not_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} :
    m.toList.find? (·.1 == k) = none ↔ ¬ k ∈ m := by
  simp only [Bool.not_eq_true, mem_iff_contains]
  simp_to_raw using Raw₀.find?_toList_eq_none_iff_contains_eq_false ⟨m, h.size_buckets_pos⟩ h

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.toList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  apply Raw₀.distinct_keys_toList ⟨m, h.size_buckets_pos⟩ h

namespace Const

variable {β : Type v} {m : Raw α (fun _ => β)}

@[simp]
theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    (Raw.Const.toList m).map Prod.fst = m.keys := by
  apply Raw₀.Const.map_fst_toList_eq_keys ⟨m, h.size_buckets_pos⟩

@[simp, deprecated map_fst_toList_eq_keys (since := "2025-02-28")]
theorem map_prod_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    (Raw.Const.toList m).map Prod.fst = m.keys := by
  apply Raw₀.Const.map_fst_toList_eq_keys ⟨m, h.size_buckets_pos⟩

@[simp]
theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    (Raw.Const.toList m).length = m.size := by
  apply Raw₀.Const.length_toList ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    (Raw.Const.toList m).isEmpty = m.isEmpty := by
  apply Raw₀.Const.isEmpty_toList ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem mem_toList_iff_get?_eq_some [LawfulBEq α] (h : m.WF)
    {k : α} {v : β} :
    (k, v) ∈ Raw.Const.toList m ↔ get? m k = some v := by
  simp_to_raw using Raw₀.Const.mem_toList_iff_get?_eq_some ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} {v : β} :
    (k, v) ∈ Raw.Const.toList m ↔ m.getKey? k = some k ∧ get? m k = some v := by
  simp_to_raw using Raw₀.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some
    ⟨m, h.size_buckets_pos⟩ h

theorem get?_eq_some_iff_exists_beq_and_mem_toList [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {k : α} {v : β} :
    get? m k = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ Raw.Const.toList m := by
  simp_to_raw using Raw₀.Const.get?_eq_some_iff_exists_beq_and_mem_toList ⟨m, h.size_buckets_pos⟩ h

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {k k' : α} {v : β} :
    (Raw.Const.toList m).find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ get? m k = some v := by
  simp_to_raw using Raw₀.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
    ⟨m, h.size_buckets_pos⟩ h

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} :
    (Raw.Const.toList m).find? (·.1 == k) = none ↔ m.contains k = false := by
  simp_to_raw using Raw₀.Const.find?_toList_eq_none_iff_contains_eq_false
    ⟨m, h.size_buckets_pos⟩ h

@[simp]
theorem find?_toList_eq_none_iff_not_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {k : α} :
    (Raw.Const.toList m).find? (·.1 == k) = none ↔ ¬ k ∈ m := by
  simp only [Bool.not_eq_true, mem_iff_contains]
  simp_to_raw using Raw₀.Const.find?_toList_eq_none_iff_contains_eq_false
    ⟨m, h.size_buckets_pos⟩ h

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    (Raw.Const.toList m).Pairwise (fun a b => (a.1 == b.1) = false) := by
  apply Raw₀.Const.distinct_keys_toList ⟨m, h.size_buckets_pos⟩ h

end Const

section monadic

variable {m : Raw α β} {δ : Type w} {m' : Type w → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    m.foldM f init = m.toList.foldlM (fun a b => f a b.1 b.2) init :=
  Raw₀.foldM_eq_foldlM_toList ⟨m, h.size_buckets_pos⟩

theorem fold_eq_foldl_toList (h : m.WF) {f : δ → (a : α) → β a → δ} {init : δ} :
    m.fold f init = m.toList.foldl (fun a b => f a b.1 b.2) init :=
  Raw₀.fold_eq_foldl_toList ⟨m, h.size_buckets_pos⟩

omit [BEq α] [Hashable α] in
@[simp]
theorem forM_eq_forM [Monad m'] [LawfulMonad m']
    {f : (a : α) → β a → m' PUnit} :
    Raw.forM f m = ForM.forM m (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] (h : m.WF) {f : (a : α) × β a → m' PUnit} :
    ForM.forM m f = m.toList.forM f :=
  Raw₀.forM_eq_forM_toList ⟨m, h.size_buckets_pos⟩

omit [BEq α] [Hashable α] in
@[simp]
theorem forIn_eq_forIn [Monad m'] [LawfulMonad m']
    {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ} :
    Raw.forIn f init m = ForIn.forIn m init (fun a b => f a.1 a.2 b) := rfl

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : (a : α) × β a → δ → m' (ForInStep δ)} {init : δ} (h : m.WF) :
    ForIn.forIn m init f = ForIn.forIn m.toList init f :=
  Raw₀.forIn_eq_forIn_toList ⟨m, h.size_buckets_pos⟩

theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init :=
  Raw₀.foldM_eq_foldlM_keys ⟨m, h.size_buckets_pos⟩

theorem fold_eq_foldl_keys (h : m.WF) {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  Raw₀.fold_eq_foldl_keys ⟨m, h.size_buckets_pos⟩

theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] (h : m.WF) {f : α → m' PUnit} :
    ForM.forM m (fun a => f a.1) = m.keys.forM f :=
  Raw₀.forM_eq_forM_keys ⟨m, h.size_buckets_pos⟩

theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn m init (fun a d => f a.1 d) = ForIn.forIn m.keys init f :=
  Raw₀.forIn_eq_forIn_keys ⟨m, h.size_buckets_pos⟩

namespace Const

variable {β : Type v} {m : Raw α (fun _ => β)}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → (a : α) → β → m' δ} {init : δ} :
    m.foldM f init = (Const.toList m).foldlM (fun a b => f a b.1 b.2) init :=
  Raw₀.Const.foldM_eq_foldlM_toList ⟨m, h.size_buckets_pos⟩

theorem fold_eq_foldl_toList (h : m.WF) {f : δ → (a : α) → β → δ} {init : δ} :
    m.fold f init = (Raw.Const.toList m).foldl (fun a b => f a b.1 b.2) init :=
  Raw₀.Const.fold_eq_foldl_toList ⟨m, h.size_buckets_pos⟩

omit [BEq α] [Hashable α] in
theorem forM_eq_forMUncurried [Monad m'] [LawfulMonad m']
    {f : α → β → m' PUnit} :
    Raw.forM f m = Const.forMUncurried (fun a => f a.1 a.2) m := rfl

theorem forMUncurried_eq_forM_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α × β → m' PUnit} :
    forMUncurried f m = (toList m).forM f :=
  Raw₀.Const.forM_eq_forM_toList ⟨m, h.size_buckets_pos⟩

/--
Deprecated, use `forMUncurried_eq_forM_toList` together with `forM_eq_forMUncurried` instead.
-/
@[deprecated forMUncurried_eq_forM_toList (since := "2025-03-02")]
theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] (h : m.WF) {f : (a : α) → β → m' PUnit} :
    m.forM f = (Raw.Const.toList m).forM (fun a => f a.1 a.2) :=
  Raw₀.Const.forM_eq_forM_toList ⟨m, h.size_buckets_pos⟩

omit [BEq α] [Hashable α] in
@[simp]
theorem forIn_eq_forInUncurried [Monad m'] [LawfulMonad m']
    {f : α → β → δ → m' (ForInStep δ)} {init : δ} :
    forIn f init m = forInUncurried (fun a b => f a.1 a.2 b) init m := rfl

theorem forInUncurried_eq_forIn_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α × β → δ → m' (ForInStep δ)} {init : δ} :
    forInUncurried f init m = ForIn.forIn (toList m) init f :=
  Raw₀.Const.forIn_eq_forIn_toList ⟨m, h.size_buckets_pos⟩

/--
Deprecated, use `forInUncurried_eq_forIn_toList` together with `forIn_eq_forInUncurried` instead.
-/
@[deprecated forInUncurried_eq_forIn_toList (since := "2025-03-02")]
theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : (a : α) → β → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn (Raw.Const.toList m) init (fun a b => f a.1 a.2 b) :=
  Raw₀.Const.forIn_eq_forIn_toList ⟨m, h.size_buckets_pos⟩

variable {m : Raw α (fun _ => Unit)}

@[deprecated Raw.foldM_eq_foldlM_keys (since := "2025-02-28")]
theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : δ → α → m' δ} {init : δ} :
    m.foldM (fun d a _ => f d a) init = m.keys.foldlM f init :=
  Raw₀.foldM_eq_foldlM_keys ⟨m, h.size_buckets_pos⟩

@[deprecated Raw.fold_eq_foldl_keys (since := "2025-02-28")]
theorem fold_eq_foldl_keys (h : m.WF) {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init :=
  Raw₀.fold_eq_foldl_keys ⟨m, h.size_buckets_pos⟩

@[deprecated Raw.forM_eq_forM_keys (since := "2025-02-28")]
theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] (h : m.WF) {f : α → m' PUnit} :
    m.forM (fun a _ => f a) = m.keys.forM f :=
  Raw₀.forM_eq_forM_keys ⟨m, h.size_buckets_pos⟩

@[deprecated Raw.forIn_eq_forIn_keys (since := "2025-02-28")]
theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m'] (h : m.WF)
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.forIn (fun a _ d => f a d) init = ForIn.forIn m.keys init f :=
  Raw₀.forIn_eq_forIn_keys ⟨m, h.size_buckets_pos⟩

end Const

end monadic

@[simp]
theorem insertMany_nil [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.insertMany [] = m := by
  simp_to_raw
  rw [Raw₀.insertMany_nil]

@[simp]
theorem insertMany_list_singleton {k : α} {v : β k} [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.insertMany [⟨k, v⟩] = m.insert k v := by
  simp_to_raw
  rw [Raw₀.insertMany_list_singleton]

theorem insertMany_cons {l : List ((a : α) × β a)} {k : α} {v : β k} [EquivBEq α] [LawfulHashable α]
    (h : m.WF) :
    m.insertMany (⟨k, v⟩ :: l) = (m.insert k v).insertMany l := by
  simp_to_raw
  rw [Raw₀.insertMany_cons]

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).contains k = (m.contains k || (l.map Sigma.fst).contains k) := by
  simp_to_raw using Raw₀.contains_insertMany_list

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ (m.insertMany l) ↔ k ∈ m ∨ (l.map Sigma.fst).contains k := by
  simp [mem_iff_contains, contains_insertMany_list h]

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ (m.insertMany l) → (l.map Sigma.fst).contains k = false → k ∈ m := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.contains_of_contains_insertMany_list

theorem get?_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).get? k = m.get? k := by
  simp_to_raw using Raw₀.get?_insertMany_list_of_contains_eq_false

theorem get?_insertMany_list_of_mem [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  simp_to_raw using Raw₀.get?_insertMany_list_of_mem

theorem get_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h'} :
    (m.insertMany l).get k h' =
      m.get k (mem_of_mem_insertMany_list h h' contains_eq_false) := by
  simp_to_raw using Raw₀.get_insertMany_list_of_contains_eq_false

theorem get_insertMany_list_of_mem [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (m.insertMany l).get k' h' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_raw using Raw₀.get_insertMany_list_of_mem

theorem get!_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).get! k = m.get! k := by
  simp_to_raw using Raw₀.get!_insertMany_list_of_contains_eq_false

theorem get!_insertMany_list_of_mem [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_raw using Raw₀.get!_insertMany_list_of_mem

theorem getD_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getD k fallback = m.getD k fallback := by
  simp_to_raw using Raw₀.getD_insertMany_list_of_contains_eq_false

theorem getD_insertMany_list_of_mem [LawfulBEq α] (h : m.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_raw using Raw₀.getD_insertMany_list_of_mem

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey? k = m.getKey? k := by
  simp_to_raw using Raw₀.getKey?_insertMany_list_of_contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey? k' = some k := by
  simp_to_raw using Raw₀.getKey?_insertMany_list_of_mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h'} :
    (m.insertMany l).getKey k h' =
      m.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) := by
  simp_to_raw using Raw₀.getKey_insertMany_list_of_contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (m.insertMany l).getKey k' h' = k := by
  simp_to_raw using Raw₀.getKey_insertMany_list_of_mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKey! k = m.getKey! k := by
  simp_to_raw using Raw₀.getKey!_insertMany_list_of_contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKey! k' = k := by
  simp_to_raw using Raw₀.getKey!_insertMany_list_of_mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_raw using Raw₀.getKeyD_insertMany_list_of_contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).getKeyD k' fallback = k := by
  simp_to_raw using Raw₀.getKeyD_insertMany_list_of_mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Sigma.fst).contains a = false) →
      (m.insertMany l).size = m.size + l.length := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_insertMany_list

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} :
    m.size ≤ (m.insertMany l).size := by
  simp_to_raw using Raw₀.size_le_size_insertMany_list ⟨m, _⟩

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} :
    (m.insertMany l).size ≤ m.size + l.length := by
  simp_to_raw using Raw₀.size_insertMany_list_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List ((a : α) × β a)} :
    (m.insertMany l).isEmpty = (m.isEmpty && l.isEmpty) := by
  simp_to_raw using Raw₀.isEmpty_insertMany_list

namespace Const

variable {β : Type v} {m : Raw α (fun _ => β)}

@[simp]
theorem insertMany_nil (h : m.WF) :
    insertMany m [] = m := by
  simp_to_raw
  rw [Raw₀.Const.insertMany_nil]

@[simp]
theorem insertMany_list_singleton (h : m.WF)
    {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v := by
  simp_to_raw
  rw [Raw₀.Const.insertMany_list_singleton]

theorem insertMany_cons (h : m.WF) {l : List (α × β)}
    {k : α} {v : β} :
    insertMany m (⟨k, v⟩ :: l) = insertMany (m.insert k v) l := by
  simp_to_raw
  rw [Raw₀.Const.insertMany_cons]

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    (insertMany m l).contains k = (m.contains k || (l.map Prod.fst).contains k) := by
  simp_to_raw using Raw₀.Const.contains_insertMany_list

@[simp]
theorem mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l ↔ k ∈ m ∨ (l.map Prod.fst).contains k := by
  simp [mem_iff_contains, contains_insertMany_list h]

theorem mem_of_mem_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} :
    k ∈ insertMany m l → (l.map Prod.fst).contains k = false → k ∈ m := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.contains_of_contains_insertMany_list

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey? k = m.getKey? k := by
  simp_to_raw using Raw₀.Const.getKey?_insertMany_list_of_contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey? k' = some k := by
  simp_to_raw using Raw₀.Const.getKey?_insertMany_list_of_mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany m l).getKey k h' =
      m.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) := by
  simp_to_raw using Raw₀.Const.getKey_insertMany_list_of_contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany m l).getKey k' h' = k := by
  simp_to_raw using Raw₀.Const.getKey_insertMany_list_of_mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKey! k = m.getKey! k := by
  simp_to_raw using Raw₀.Const.getKey!_insertMany_list_of_contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKey! k' = k := by
  simp_to_raw using Raw₀.Const.getKey!_insertMany_list_of_mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany m l).getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_raw using Raw₀.Const.getKeyD_insertMany_list_of_contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).getKeyD k' fallback = k := by
  simp_to_raw using Raw₀.Const.getKeyD_insertMany_list_of_mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), a ∈ m → (l.map Prod.fst).contains a = false) →
      (insertMany m l).size = m.size + l.length := by
  simp [mem_iff_contains]
  simp_to_raw using Raw₀.Const.size_insertMany_list

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} :
    m.size ≤ (insertMany m l).size := by
  simp_to_raw using Raw₀.Const.size_le_size_insertMany_list ⟨m, _⟩

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} :
    (insertMany m l).size ≤ m.size + l.length := by
  simp_to_raw using Raw₀.Const.size_insertMany_list_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} :
    (insertMany m l).isEmpty = (m.isEmpty && l.isEmpty) := by
  simp_to_raw using Raw₀.Const.isEmpty_insertMany_list

theorem get?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l) k = get? m k := by
  simp_to_raw using Raw₀.Const.get?_insertMany_list_of_contains_eq_false

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l) k' = v := by
  simp_to_raw using Raw₀.Const.get?_insertMany_list_of_mem

theorem get_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany m l) k h' =
      get m k (mem_of_mem_insertMany_list h h' contains_eq_false) := by
  simp_to_raw using Raw₀.Const.get_insertMany_list_of_contains_eq_false

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l){h'} :
    get (insertMany m l) k' h' = v := by
  simp_to_raw using Raw₀.Const.get_insertMany_list_of_mem

theorem get!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β] (h : m.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany m l) k = get! m k := by
  simp_to_raw using Raw₀.Const.get!_insertMany_list_of_contains_eq_false

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany m l) k' = v := by
  simp_to_raw using Raw₀.Const.get!_insertMany_list_of_mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l) k fallback = getD m k fallback := by
  simp_to_raw using Raw₀.Const.getD_insertMany_list_of_contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l) k' fallback = v := by
  simp_to_raw using Raw₀.Const.getD_insertMany_list_of_mem

variable {m : Raw α (fun _ => Unit)}

@[simp]
theorem insertManyIfNewUnit_nil (h : m.WF) :
    insertManyIfNewUnit m [] = m := by
  simp_to_raw
  rw [Raw₀.Const.insertManyIfNewUnit_nil]

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} (h : m.WF) :
    insertManyIfNewUnit m [k] = m.insertIfNew k () := by
  simp_to_raw
  rw [Raw₀.Const.insertManyIfNewUnit_list_singleton]

theorem insertManyIfNewUnit_cons (h : m.WF) {l : List α} {k : α} :
    insertManyIfNewUnit m (k :: l) = insertManyIfNewUnit (m.insertIfNew k ()) l := by
  simp_to_raw
  rw [Raw₀.Const.insertManyIfNewUnit_cons]

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) := by
  simp_to_raw using Raw₀.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k := by
  simp [mem_iff_contains, contains_insertManyIfNewUnit_list h]

theorem mem_of_mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit m l → k ∈ m := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.contains_of_contains_insertManyIfNewUnit_list

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k : α} :
    ¬ k ∈ m → l.contains k = false →
      getKey? (insertManyIfNewUnit m l) k = none := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k k' : α} (k_beq : k == k') :
    ¬ k ∈ m → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey? (insertManyIfNewUnit m l) k' = some k := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k : α} :
    k ∈ m → getKey? (insertManyIfNewUnit m l) k = getKey? m k := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKey?_insertManyIfNewUnit_list_of_contains

theorem getKey_insertManyIfNewUnit_list_of_mem
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k : α} {h'} (mem : k ∈ m) :
    getKey (insertManyIfNewUnit m l) k h' = getKey m k mem := by
  simp_to_raw using Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α}
    {k k' : α} (k_beq : k == k') {h'} :
    ¬ k ∈ m → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey (insertManyIfNewUnit m l) k' h' = k := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getKey_insertManyIfNewUnit_list_of_contains_eq_false_of_mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.WF) {l : List α} {k : α} :
    ¬ k ∈ m → l.contains k = false → getKey! (insertManyIfNewUnit m l) k = default := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using
    Raw₀.Const.getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.WF) {l : List α} {k k' : α} (k_beq : k == k') :
    ¬ k ∈ m → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey! (insertManyIfNewUnit m l) k' = k := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.WF) {l : List α} {k : α} :
    k ∈ m → getKey! (insertManyIfNewUnit m l) k = getKey! m k := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKey!_insertManyIfNewUnit_list_of_contains

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.WF) {l : List α} {k fallback : α} :
    ¬ k ∈ m → l.contains k = false →
      getKeyD (insertManyIfNewUnit m l) k fallback = fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using
    Raw₀.Const.getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k k' fallback : α} (k_beq : k == k') :
    ¬ k ∈ m → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKeyD (insertManyIfNewUnit m l) k' fallback = k := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.WF) {l : List α} {k fallback : α} :
    k ∈ m → getKeyD (insertManyIfNewUnit m l) k fallback = getKeyD m k fallback := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKeyD_insertManyIfNewUnit_list_of_contains

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), a ∈ m → l.contains a = false) →
      (insertManyIfNewUnit m l).size = m.size + l.length := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.size_insertManyIfNewUnit_list

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    m.size ≤ (insertManyIfNewUnit m l).size := by
  simp_to_raw using Raw₀.Const.size_le_size_insertManyIfNewUnit_list ⟨m, _⟩

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).size ≤ m.size + l.length := by
  simp_to_raw using Raw₀.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).isEmpty = (m.isEmpty && l.isEmpty) := by
  simp_to_raw using Raw₀.Const.isEmpty_insertManyIfNewUnit_list

@[simp]
theorem get?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit m l) k =
      if k ∈ m ∨ l.contains k then some () else none := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.get?_insertManyIfNewUnit_list

@[simp]
theorem get_insertManyIfNewUnit_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit m l) k h = () := by
  simp

@[simp]
theorem get!_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit m l) k = () := by
  simp

@[simp]
theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l) k fallback = () := by
  simp

end Const

end Raw

namespace Raw

variable [BEq α] [Hashable α]

open Internal.Raw Internal.Raw₀

@[simp]
theorem ofList_nil :
    ofList ([] : List ((a : α) × (β a))) = ∅ := by
  simp_to_raw
  rw [Raw₀.insertMany_empty_list_nil]

@[simp]
theorem ofList_singleton {k : α} {v : β k} :
    ofList [⟨k, v⟩] = (∅ : Raw α β).insert k v := by
  simp_to_raw
  rw [Raw₀.insertMany_empty_list_singleton]

theorem ofList_cons [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) = ((∅ : Raw α β).insert k v).insertMany tl := by
  simp_to_raw
  rw [Raw₀.insertMany_empty_list_cons]

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l).contains k = (l.map Sigma.fst).contains k := by
  simp_to_raw using Raw₀.contains_insertMany_empty_list

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l ↔ (l.map Sigma.fst).contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get? k = none := by
  simp_to_raw using Raw₀.get?_insertMany_empty_list_of_contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  simp_to_raw using Raw₀.get?_insertMany_empty_list_of_mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l).get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_raw using Raw₀.get_insertMany_empty_list_of_mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).get! k = default := by
  simp_to_raw using get!_insertMany_empty_list_of_contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_raw using Raw₀.get!_insertMany_empty_list_of_mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getD k fallback = fallback := by
  simp_to_raw using Raw₀.getD_insertMany_empty_list_of_contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l).getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_raw using Raw₀.getD_insertMany_empty_list_of_mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey? k = none := by
  simp_to_raw using Raw₀.getKey?_insertMany_empty_list_of_contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey? k' = some k := by
  simp_to_raw using Raw₀.getKey?_insertMany_empty_list_of_mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (ofList l).getKey k' h' = k := by
  simp_to_raw using Raw₀.getKey_insertMany_empty_list_of_mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKey! k = default := by
  simp_to_raw using Raw₀.getKey!_insertMany_empty_list_of_contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKey! k' = k := by
  simp_to_raw using Raw₀.getKey!_insertMany_empty_list_of_mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback := by
  simp_to_raw using Raw₀.getKeyD_insertMany_empty_list_of_contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l).getKeyD k' fallback = k := by
  simp_to_raw using Raw₀.getKeyD_insertMany_empty_list_of_mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length := by
  simp_to_raw using Raw₀.size_insertMany_empty_list

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).size ≤ l.length := by
  simp_to_raw using Raw₀.size_insertMany_empty_list_le

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (ofList l).isEmpty = l.isEmpty := by
  simp_to_raw using Raw₀.isEmpty_insertMany_empty_list

namespace Const

variable {β : Type v}

@[simp]
theorem ofList_nil :
    ofList ([] : List (α × β)) = ∅ := by
  simp_to_raw
  simp

@[simp]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] = (∅ : Raw α (fun _ => β)).insert k v := by
  simp_to_raw
  simp

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) = insertMany ((∅ : Raw α (fun _ => β)).insert k v) tl := by
  simp_to_raw
  rw [Raw₀.Const.insertMany_empty_list_cons]

@[simp]
theorem contains_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (ofList l).contains k = (l.map Prod.fst).contains k := by
  simp_to_raw using Raw₀.Const.contains_insertMany_empty_list

@[simp]
theorem mem_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    k ∈ (ofList l) ↔ (l.map Prod.fst).contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l) k = none := by
  simp_to_raw using Raw₀.Const.get?_insertMany_empty_list_of_contains_eq_false

theorem get?_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l) k' = some v := by
  simp_to_raw using Raw₀.Const.get?_insertMany_empty_list_of_mem

theorem get_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l) k' h = v := by
  simp_to_raw using Raw₀.Const.get_insertMany_empty_list_of_mem

theorem get!_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l) k = default := by
  simp_to_raw using Raw₀.Const.get!_insertMany_empty_list_of_contains_eq_false

theorem get!_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l) k' = v := by
  simp_to_raw using Raw₀.Const.get!_insertMany_empty_list_of_mem

theorem getD_ofList_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l) k fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_insertMany_empty_list_of_contains_eq_false

theorem getD_ofList_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l) k' fallback = v := by
  simp_to_raw using Raw₀.Const.getD_insertMany_empty_list_of_mem

theorem getKey?_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey? k = none := by
  simp_to_raw using Raw₀.Const.getKey?_insertMany_empty_list_of_contains_eq_false

theorem getKey?_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey? k' = some k := by
  simp_to_raw using Raw₀.Const.getKey?_insertMany_empty_list_of_mem

theorem getKey_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l).getKey k' h' = k := by
  simp_to_raw using Raw₀.Const.getKey_insertMany_empty_list_of_mem

theorem getKey!_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKey! k = default := by
  simp_to_raw using Raw₀.Const.getKey!_insertMany_empty_list_of_contains_eq_false

theorem getKey!_ofList_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKey! k' = k := by
  simp_to_raw using Raw₀.Const.getKey!_insertMany_empty_list_of_mem

theorem getKeyD_ofList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l).getKeyD k fallback = fallback := by
  simp_to_raw using Raw₀.Const.getKeyD_insertMany_empty_list_of_contains_eq_false

theorem getKeyD_ofList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l).getKeyD k' fallback = k := by
  simp_to_raw using Raw₀.Const.getKeyD_insertMany_empty_list_of_mem

theorem size_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (ofList l).size = l.length := by
  simp_to_raw using Raw₀.Const.size_insertMany_empty_list

theorem size_ofList_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).size ≤ l.length := by
  simp_to_raw using Raw₀.Const.size_insertMany_empty_list_le

@[simp]
theorem isEmpty_ofList [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (ofList l).isEmpty = l.isEmpty := by
  simp_to_raw using Raw₀.Const.isEmpty_insertMany_empty_list

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) = ∅ := by
  simp_to_raw
  simp

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (∅ : Raw α (fun _ => Unit)).insertIfNew k () := by
  simp_to_raw
  simp

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) = insertManyIfNewUnit ((∅ : Raw α (fun _ => Unit)).insertIfNew hd ()) tl := by
  simp_to_raw
  rw [Raw₀.Const.insertManyIfNewUnit_empty_list_cons]

@[simp]
theorem contains_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (unitOfList l).contains k = l.contains k := by
  simp_to_raw using Raw₀.Const.contains_insertManyIfNewUnit_empty_list

@[simp]
theorem mem_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    k ∈ unitOfList l ↔ l.contains k := by
  simp [mem_iff_contains]

theorem getKey?_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l) k = none := by
  simp_to_raw using Raw₀.Const.getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false

theorem getKey?_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (unitOfList l) k' = some k := by
  simp_to_raw using Raw₀.Const.getKey?_insertManyIfNewUnit_empty_list_of_mem

theorem getKey_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l) k' h' = k := by
  simp_to_raw using Raw₀.Const.getKey_insertManyIfNewUnit_empty_list_of_mem

theorem getKey!_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l) k = default := by
  simp_to_raw using Raw₀.Const.getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false

theorem getKey!_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (unitOfList l) k' = k := by
  simp_to_raw using Raw₀.Const.getKey!_insertManyIfNewUnit_empty_list_of_mem

theorem getKeyD_unitOfList_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l) k fallback = fallback := by
  simp_to_raw using Raw₀.Const.getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false

theorem getKeyD_unitOfList_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l ) :
    getKeyD (unitOfList l) k' fallback = k := by
  simp_to_raw using Raw₀.Const.getKeyD_insertManyIfNewUnit_empty_list_of_mem

theorem size_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (unitOfList l).size = l.length := by
  simp_to_raw using Raw₀.Const.size_insertManyIfNewUnit_empty_list

theorem size_unitOfList_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).size ≤ l.length := by
  simp_to_raw using Raw₀.Const.size_insertManyIfNewUnit_empty_list_le

@[simp]
theorem isEmpty_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (unitOfList l).isEmpty = l.isEmpty := by
  simp_to_raw using Raw₀.Const.isEmpty_insertManyIfNewUnit_empty_list

@[simp]
theorem get?_unitOfList [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (unitOfList l) k = if l.contains k then some () else none := by
  simp_to_raw using Raw₀.Const.get?_insertManyIfNewUnit_empty_list

@[simp]
theorem get_unitOfList
    {l : List α} {k : α} {h} :
    get (unitOfList l) k h = () := by
  simp

@[simp]
theorem get!_unitOfList
    {l : List α} {k : α} :
    get! (unitOfList l) k = () := by
  simp

@[simp]
theorem getD_unitOfList
    {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l) k fallback = () := by
  simp

end Const
end Raw

namespace Raw

variable [BEq α] [Hashable α] {m : Raw α β}

open Internal.Raw Internal.Raw₀

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) : (m.alter k f).isEmpty = ((m.erase k).isEmpty && (f (m.get? k)).isNone) := by
  simp_to_raw using Raw₀.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem isEmpty_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) && (f (m.get? k)).isNone) := by
  simp_to_raw using Raw₀.isEmpty_alter

theorem contains_alter [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' := by
  simp_to_raw using Raw₀.contains_alter

theorem mem_alter [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    k' ∈ m.alter k f ↔ if k == k' then (f (m.get? k)).isSome = true else k' ∈ m := by
  simp [mem_iff_contains, contains_alter h]

theorem mem_alter_of_beq [LawfulBEq α] {k k': α} {f : Option (β k) → Option (β k)} (h : m.WF)
    (he : k == k') : k' ∈ m.alter k f ↔ (f (m.get? k)).isSome := by
  rw [mem_alter h, if_pos he]

@[simp]
theorem contains_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).contains k = (f (m.get? k)).isSome := by
  simp only [contains_alter h, beq_self_eq_true, reduceIte]

@[simp]
theorem mem_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    k ∈ m.alter k f ↔ (f (m.get? k)).isSome := by
  rw [mem_iff_contains, contains_alter_self h]

theorem contains_alter_of_beq_eq_false [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) (he : (k == k') = false) : (m.alter k f).contains k' = m.contains k' := by
  simp only [contains_alter h, he, Bool.false_eq_true, reduceIte]

theorem mem_alter_of_beq_eq_false [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) (he : (k == k') = false) : k' ∈ m.alter k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_alter_of_beq_eq_false h, he]

theorem size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).size =
      if m.contains k && (f (m.get? k)).isNone then
        m.size - 1
      else if !m.contains k && (f (m.get? k)).isSome then
        m.size + 1
      else
        m.size := by
  simp_to_raw using Raw₀.size_alter

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) (h₁ : k ∉ m) (h₂ : (f (m.get? k)).isSome) :
    (m.alter k f).size = m.size + 1 := by
  revert h₁ h₂
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.size_alter_eq_add_one

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) (h₁ : k ∈ m) (h₂ : (f (m.get? k)).isNone)  :
    (m.alter k f).size = m.size - 1 := by
  revert h₁ h₂
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_alter_eq_sub_one

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) (h₁ : k ∉ m) (h₂ : (f (m.get? k)).isNone)  :
    (m.alter k f).size = m.size := by
  revert h₁ h₂
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.size_alter_eq_self_of_not_mem

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) (h₁ : k ∈ m) (h₂ : (f (m.get? k)).isSome)  :
    (m.alter k f).size = m.size := by
  revert h₁ h₂
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_alter_eq_self_of_mem

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).size ≤ m.size + 1 := by
  simp_to_raw using Raw₀.size_alter_le_size

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    m.size - 1 ≤ (m.alter k f).size := by
  simp_to_raw using Raw₀.size_le_size_alter ⟨m, h.size_buckets_pos⟩

theorem get?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).get? k' = if h : k == k' then
      (cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (m.get? k)))
    else m.get? k' := by
  simp_to_raw using Raw₀.get?_alter

@[simp]
theorem get?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).get? k = f (m.get? k) := by
  simp [get?_alter h]

theorem get_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) {hc : k' ∈ m.alter k f} :
    (m.alter k f).get k' hc =
      if heq : k == k' then
        haveI h' : (f (m.get? k)).isSome := mem_alter_of_beq h heq |>.mp hc
        cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get <| h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        m.get k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.get_alter

@[simp]
theorem get_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) {hc : k ∈ m.alter k f} :
    haveI h' : (f (m.get? k)).isSome := mem_alter_self h |>.mp hc
    (m.alter k f).get k hc = (f (m.get? k)).get h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.get_alter_self

theorem get!_alter [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')]
    {f : Option (β k) → Option (β k)} (h : m.WF) : (m.alter k f).get! k' =
      if heq : k == k' then
        (f (m.get? k)).map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' := by
  simp_to_raw using Raw₀.get!_alter

private theorem Option.map_cast_apply {γ γ' : Type u} (h : γ = γ') (x : Option γ) :
    Option.map (cast h) x = cast (congrArg Option h) x := by
  cases h; cases x <;> simp

@[simp]
theorem get!_alter_self [LawfulBEq α] {k : α} [Inhabited (β k)] {f : Option (β k) → Option (β k)}
    (h : m.WF) : (m.alter k f).get! k = (f (m.get? k)).get! := by
  simp [get!_alter h, Option.map_cast_apply]

theorem getD_alter [LawfulBEq α] {k k' : α} {fallback : β k'} {f : Option (β k) → Option (β k)}
    (h : m.WF) : (m.alter k f).getD k' fallback =
      if heq : k == k' then
        f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback := by
  simp_to_raw using Raw₀.getD_alter

@[simp]
theorem getD_alter_self [LawfulBEq α] {k : α} {fallback : β k} {f : Option (β k) → Option (β k)}
    (h : m.WF) : (m.alter k f).getD k fallback = (f (m.get? k)).getD fallback := by
  simp_to_raw using Raw₀.getD_alter_self

theorem getKey?_alter [LawfulBEq α] {k k' : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).getKey? k' =
      if k == k' then
        if (f (m.get? k)).isSome then some k else none
      else
        m.getKey? k' := by
  simp_to_raw using Raw₀.getKey?_alter

theorem getKey?_alter_self [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).getKey? k = if (f (m.get? k)).isSome then some k else none := by
  simp [getKey?_alter h]

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) : (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' := by
  simp_to_raw using Raw₀.getKey!_alter

theorem getKey!_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) : (m.alter k f).getKey! k = if (f (m.get? k)).isSome then k else default := by
  simp [getKey!_alter h]

theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) {hc : k' ∈ m.alter k f} :
    (m.alter k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        m.getKey k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.getKey_alter

@[simp]
theorem getKey_alter_self [LawfulBEq α] [Inhabited α] {k : α} {f : Option (β k) → Option (β k)}
    (h : m.WF) {hc : k ∈ m.alter k f} : (m.alter k f).getKey k hc = k := by
  simp [getKey_alter h]

theorem getKeyD_alter [LawfulBEq α] {k k' fallback : α} {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).getKeyD k' fallback =
      if k == k' then
        if (f (m.get? k)).isSome then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_raw using Raw₀.getKeyD_alter

@[simp]
theorem getKeyD_alter_self [LawfulBEq α] [Inhabited α] {k : α} {fallback : α}
    {f : Option (β k) → Option (β k)} (h : m.WF) :
    (m.alter k f).getKeyD k fallback = if (f (m.get? k)).isSome then k else fallback := by
  simp [getKeyD_alter h]

namespace Const

variable {β : Type v} {m : Raw α (fun _ => β)}

theorem isEmpty_alter_eq_isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α}
    {f : Option β → Option β} (h : m.WF) :
    (Const.alter m k f).isEmpty = ((m.erase k).isEmpty && (f (Const.get? m k)).isNone) := by
  simp_to_raw using Raw₀.Const.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem isEmpty_alter [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (Const.alter m k f).isEmpty = ((m.isEmpty || (m.size == 1 && m.contains k)) &&
      (f (get? m k)).isNone) := by
  simp_to_raw using Raw₀.Const.isEmpty_alter

theorem contains_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : m.WF) : (Const.alter m k f).contains k' =
      if k == k' then (f (Const.get? m k)).isSome else m.contains k' := by
  simp_to_raw using Raw₀.Const.contains_alter

theorem mem_alter [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β} (h : m.WF) :
    k' ∈ Const.alter m k f ↔ if k == k' then (f (Const.get? m k)).isSome = true else k' ∈ m := by
    simp only [mem_iff_contains, contains_alter h, Bool.ite_eq_true_distrib]

theorem mem_alter_of_beq [EquivBEq α] [LawfulHashable α] {k k': α} {f : Option β → Option β}
    (h : m.WF) (he : k == k') : k' ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome := by
  rw [mem_alter h, if_pos he]

@[simp]
theorem contains_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : (Const.alter m k f).contains k = (f (Const.get? m k)).isSome := by
  simp only [contains_alter h, BEq.refl, reduceIte]

@[simp]
theorem mem_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : k ∈ Const.alter m k f ↔ (f (Const.get? m k)).isSome := by
  rw [mem_iff_contains, contains_alter_self h]

theorem contains_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) (he : (k == k') = false) :
    (Const.alter m k f).contains k' = m.contains k' := by
  simp only [contains_alter h, he, Bool.false_eq_true, reduceIte]

theorem mem_alter_of_beq_eq_false [EquivBEq α] [LawfulHashable α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) (he : (k == k') = false) :
    k' ∈ Const.alter m k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_alter_of_beq_eq_false h, he]

theorem size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (Const.alter m k f).size =
      if m.contains k && (f (Const.get? m k)).isNone then
        m.size - 1
      else if !m.contains k && (f (Const.get? m k)).isSome then
        m.size + 1
      else
        m.size := by
  simp_to_raw using Raw₀.Const.size_alter

theorem size_alter_eq_add_one [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : m.WF) (h₁ : k ∉ m) (h₂ : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).size = m.size + 1 := by
  revert h₁ h₂
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.size_alter_eq_add_one

theorem size_alter_eq_sub_one [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : m.WF) (h₁ : k ∈ m) (h₂ : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).size = m.size - 1 := by
  revert h₁ h₂
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.size_alter_eq_sub_one

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : m.WF) (h₁ : k ∉ m) (h₂ : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).size = m.size := by
  revert h₁ h₂
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.size_alter_eq_self_of_not_mem

theorem size_alter_eq_self_of_mem [LawfulBEq α] {k : α} {f : Option β → Option β}
    (h : m.WF) (h₁ : k ∈ m) (h₂ : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).size = m.size := by
  revert h₁ h₂
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.size_alter_eq_self_of_mem

theorem size_alter_le_size [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    (Const.alter m k f).size ≤ m.size + 1 := by
  simp_to_raw using Raw₀.Const.size_alter_le_size

theorem size_le_size_alter [LawfulBEq α] {k : α} {f : Option β → Option β} (h : m.WF) :
    m.size - 1 ≤ (Const.alter m k f).size := by
  simp_to_raw using Raw₀.Const.size_le_size_alter ⟨m, h.size_buckets_pos⟩

theorem get?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} (h : m.WF) :
    Const.get? (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k)
      else
        Const.get? m k' := by
  simp_to_raw using Raw₀.Const.get?_alter

@[simp]
theorem get?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) : Const.get? (Const.alter m k f) k = f (Const.get? m k) := by
  simp [get?_alter h]

theorem get_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    (h : m.WF) {hc : k' ∈ Const.alter m k f} :
    Const.get (Const.alter m k f) k' hc =
      if heq : k == k' then
        haveI h' : (f (Const.get? m k)).isSome := mem_alter_of_beq h heq |>.mp hc
        f (Const.get? m k) |>.get h'
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        Const.get m k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.Const.get_alter

@[simp]
theorem get_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) {hc : k ∈ Const.alter m k f} :
    haveI h' : (f (Const.get? m k)).isSome := mem_alter_self h |>.mp hc
    Const.get (Const.alter m k f) k hc = (f (Const.get? m k)).get h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp [get_alter h]

theorem get!_alter [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β]
    {f : Option β → Option β} (h : m.WF) : Const.get! (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k) |>.get!
      else
        Const.get! m k' := by
  simp_to_raw using Raw₀.Const.get!_alter

@[simp]
theorem get!_alter_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β]
    {f : Option β → Option β} (h : m.WF) :
    Const.get! (Const.alter m k f) k = (f (Const.get? m k)).get! := by
  simp [get!_alter h]

theorem getD_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : Option β → Option β}
    (h : m.WF) : Const.getD (Const.alter m k f) k' fallback =
      if k == k' then
        f (Const.get? m k) |>.getD fallback
      else
        Const.getD m k' fallback := by
  simp_to_raw using Raw₀.Const.getD_alter

@[simp]
theorem getD_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β}
    {f : Option β → Option β} (h : m.WF) :
    Const.getD (Const.alter m k f) k fallback = (f (Const.get? m k)).getD fallback := by
  simp [getD_alter h]

theorem getKey?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β}
    (h : m.WF) : (Const.alter m k f).getKey? k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then some k else none
      else
        m.getKey? k' := by
  simp_to_raw using Raw₀.Const.getKey?_alter

theorem getKey?_alter_self [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β}
    (h : m.WF) :
    (Const.alter m k f).getKey? k = if (f (Const.get? m k)).isSome then some k else none := by
  simp [getKey?_alter h]

theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) : (Const.alter m k f).getKey! k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else default
      else
        m.getKey! k' := by
  simp_to_raw using Raw₀.Const.getKey!_alter

theorem getKey!_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} (h : m.WF) :
    (Const.alter m k f).getKey! k = if (f (Const.get? m k)).isSome then k else default := by
  simp [getKey!_alter h]

theorem getKey_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} (h : m.WF) {hc : k' ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_alter_of_beq_eq_false h (Bool.not_eq_true _ ▸ heq) |>.mp hc
        m.getKey k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.Const.getKey_alter

@[simp]
theorem getKey_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α}
    {f : Option β → Option β} (h : m.WF) {hc : k ∈ Const.alter m k f} :
    (Const.alter m k f).getKey k hc = k := by
  simp [getKey_alter h]

theorem getKeyD_alter [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : Option β → Option β}
    (h : m.WF) : (Const.alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_raw using Raw₀.Const.getKeyD_alter

theorem getKeyD_alter_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α}
    {f : Option β → Option β} (h : m.WF) :
    (Const.alter m k f).getKeyD k fallback = if (f (Const.get? m k)).isSome then k else fallback := by
  simp [getKeyD_alter h]

end Const

end Alter

section Modify

@[simp]
theorem isEmpty_modify [LawfulBEq α] {k : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).isEmpty = m.isEmpty := by
  simp_to_raw using Raw₀.isEmpty_modify

@[simp]
theorem contains_modify [LawfulBEq α] {k k': α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).contains k' = m.contains k' := by
  simp_to_raw using Raw₀.contains_modify

@[simp]
theorem mem_modify [LawfulBEq α] {k k': α} {f : β k → β k} (h : m.WF) :
    k' ∈ m.modify k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_modify h]

@[simp]
theorem size_modify [LawfulBEq α] {k : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).size = m.size := by
  simp_to_raw using Raw₀.size_modify

theorem get?_modify [LawfulBEq α] {k k' : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).get? k' =
      if h : k == k' then
        (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f))
      else
        m.get? k' := by
  simp_to_raw using Raw₀.get?_modify

@[simp]
theorem get?_modify_self [LawfulBEq α] {k : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).get? k = (m.get? k).map f := by
  simp_to_raw using Raw₀.get?_modify_self

theorem get_modify [LawfulBEq α] {k k' : α} {f : β k → β k}
    (h : m.WF) {hc : k' ∈ m.modify k f} :
    (m.modify k f).get k' hc =
     if heq : k == k' then
       haveI h' : k ∈ m := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
       cast (congrArg β (eq_of_beq heq)) <| f (m.get k h')
     else
       haveI h' : k' ∈ m := mem_modify h |>.mp hc
       m.get k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.get_modify

@[simp]
theorem get_modify_self [LawfulBEq α] {k : α} {f : β k → β k} (h : m.WF) {hc : k ∈ m.modify k f} :
    haveI h' : k ∈ m := mem_modify h |>.mp hc
    (m.modify k f).get k hc = f (m.get k h') := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.get_modify_self

theorem get!_modify [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} (h : m.WF) :
    (m.modify k f).get! k' =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' := by
  simp_to_raw using Raw₀.get!_modify

@[simp]
theorem get!_modify_self [LawfulBEq α] {k : α} [Inhabited (β k)] {f : β k → β k} (h : m.WF) :
    (m.modify k f).get! k = ((m.get? k).map f).get! := by
  simp_to_raw using Raw₀.get!_modify_self

theorem getD_modify [LawfulBEq α] {k k' : α} {fallback : β k'} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getD k' fallback =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback := by
  simp_to_raw using Raw₀.getD_modify

@[simp]
theorem getD_modify_self [LawfulBEq α] {k : α} {fallback : β k} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getD k fallback = ((m.get? k).map f).getD fallback := by
  simp_to_raw using Raw₀.getD_modify_self

theorem getKey?_modify [LawfulBEq α] {k k' : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.getKey?_modify

theorem getKey?_modify_self [LawfulBEq α] {k : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getKey? k = if k ∈ m then some k else none := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.getKey?_modify_self

theorem getKey!_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.getKey!_modify

theorem getKey!_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getKey! k = if k ∈ m then k else default := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.getKey!_modify_self

theorem getKey_modify [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k}
    (h : m.WF) {hc : k' ∈ m.modify k f} :
    (m.modify k f).getKey k' hc =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify h |>.mp hc
        m.getKey k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.getKey_modify

@[simp]
theorem getKey_modify_self [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k}
    (h : m.WF) {hc : k ∈ m.modify k f} : (m.modify k f).getKey k hc = k := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.getKey_modify_self

theorem getKeyD_modify [LawfulBEq α] {k k' fallback : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.getKeyD_modify

theorem getKeyD_modify_self [LawfulBEq α] [Inhabited α] {k fallback : α} {f : β k → β k} (h : m.WF) :
    (m.modify k f).getKeyD k fallback = if k ∈ m then k else fallback := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.getKeyD_modify_self

namespace Const

variable {β : Type v} {m : Raw α (fun _ => β)}

@[simp]
theorem isEmpty_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (Const.modify m k f).isEmpty = m.isEmpty := by
  simp_to_raw using Raw₀.Const.isEmpty_modify

@[simp]
theorem contains_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} (h : m.WF) :
    (Const.modify m k f).contains k' = m.contains k' := by
  simp_to_raw using Raw₀.Const.contains_modify

@[simp]
theorem mem_modify [EquivBEq α] [LawfulHashable α] {k k': α} {f : β → β} (h : m.WF) :
    k' ∈ Const.modify m k f ↔ k' ∈ m := by
  simp only [mem_iff_contains, contains_modify h]

@[simp]
theorem size_modify [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (Const.modify m k f).size = m.size := by
  simp_to_raw using Raw₀.Const.size_modify

theorem get?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} (h : m.WF) :
    Const.get? (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f
      else
        Const.get? m k' := by
  simp_to_raw using Raw₀.Const.get?_modify

@[simp]
theorem get?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f := by
  simp_to_raw using Raw₀.Const.get?_modify_self

theorem get_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β}
    (h : m.WF) {hc : k' ∈ Const.modify m k f} :
    Const.get (Const.modify m k f) k' hc =
      if heq : k == k' then
        haveI h' : k ∈ m := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        f (Const.get m k h')
      else
        haveI h' : k' ∈ m := mem_modify h |>.mp hc
        Const.get m k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.Const.get_modify

@[simp]
theorem get_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β}
    (h : m.WF) {hc : k ∈ Const.modify m k f} :
    haveI h' : k ∈ m := mem_modify h |>.mp hc
    Const.get (Const.modify m k f) k hc = f (Const.get m k h') := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.Const.get_modify_self

theorem get!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β}
    (h : m.WF) : Const.get! (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f |>.get!
      else
        Const.get! m k' := by
  simp_to_raw using Raw₀.Const.get!_modify

@[simp]
theorem get!_modify_self [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β}
    (h : m.WF) : Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! := by
  simp_to_raw using Raw₀.Const.get!_modify_self

theorem getD_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} (h : m.WF) :
    Const.getD (Const.modify m k f) k' fallback =
      if k == k' then
        Const.get? m k |>.map f |>.getD fallback
      else
        Const.getD m k' fallback := by
  simp_to_raw using Raw₀.Const.getD_modify

@[simp]
theorem getD_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} (h : m.WF) :
    Const.getD (Const.modify m k f) k fallback = ((Const.get? m k).map f).getD fallback := by
  simp_to_raw using Raw₀.Const.getD_modify_self

theorem getKey?_modify [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} (h : m.WF) :
    (Const.modify m k f).getKey? k' =
      if k == k' then
        if k ∈ m then some k else none
      else
        m.getKey? k' := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKey?_modify

theorem getKey?_modify_self [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} (h : m.WF) :
    (Const.modify m k f).getKey? k = if k ∈ m then some k else none := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKey?_modify_self

theorem getKey!_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    (h : m.WF) : (Const.modify m k f).getKey! k' =
      if k == k' then
        if k ∈ m then k else default
      else
        m.getKey! k' := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKey!_modify

theorem getKey!_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    (h : m.WF) : (Const.modify m k f).getKey! k = if k ∈ m then k else default := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKey!_modify_self

theorem getKey_modify [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β}
    (h : m.WF) {hc : k' ∈ Const.modify m k f} :
    (Const.modify m k f).getKey k' hc =
      if k == k' then
        k
      else
        haveI h' : k' ∈ m := mem_modify h |>.mp hc
        m.getKey k' h' := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.Const.getKey_modify

@[simp]
theorem getKey_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β}
    (h : m.WF) {hc : k ∈ Const.modify m k f} : (Const.modify m k f).getKey k hc = k := by
  simp only [mem_iff_contains] at hc
  revert hc
  simp_to_raw using Raw₀.Const.getKey_modify_self

theorem getKeyD_modify [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} (h : m.WF) :
    (Const.modify m k f).getKeyD k' fallback =
      if k == k' then
        if k ∈ m then k else fallback
      else
        m.getKeyD k' fallback := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKeyD_modify

theorem getKeyD_modify_self [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α} {f : β → β}
    (h : m.WF) : (Const.modify m k f).getKeyD k fallback = if k ∈ m then k else fallback := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.Const.getKeyD_modify_self

end Const

end Modify

end Raw

end Std.DHashMap
