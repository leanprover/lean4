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

universe u v

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]

namespace Std.DHashMap

namespace Internal.Raw

open Lean Elab Meta Tactic

private def baseNames : Array Name :=
  #[``Raw.empty_eq, ``Raw.emptyc_eq,
    ``insert_eq, ``insert_val,
    ``insertIfNew_eq, ``insertIfNew_val,
    ``containsThenInsert_snd_eq, ``containsThenInsert_snd_val,
    ``containsThenInsertIfNew_snd_eq, ``containsThenInsertIfNew_snd_val,
    ``getThenInsertIfNew?_snd_eq, ``getThenInsertIfNew?_snd_val,
    ``map_eq, ``map_val,
    ``filter_eq, ``filter_val,
    ``erase_eq, ``erase_val,
    ``filterMap_eq, ``filterMap_val,
    ``Const.getThenInsertIfNew?_snd_eq, ``Const.getThenInsertIfNew?_snd_val,
    ``containsThenInsert_fst_eq, ``containsThenInsert_fst_val,
    ``containsThenInsertIfNew_fst_eq, ``containsThenInsertIfNew_fst_val,
    ``Const.get?_eq, ``Const.get?_val,
    ``Const.get_eq, ``Const.get_val,
    ``Const.getD_eq, ``Const.getD_val,
    ``Const.get!_eq, ``Const.get!_val,
    ``getThenInsertIfNew?_fst_eq, ``getThenInsertIfNew?_fst_val,
    ``Const.getThenInsertIfNew?_fst_eq, ``Const.getThenInsertIfNew?_fst_val,
    ``get?_eq, ``get?_val,
    ``contains_eq, ``contains_val,
    ``get_eq, ``get_val,
    ``getD_eq, ``getD_val,
    ``get!_eq, ``get!_val]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_raw" ("using" term)? : tactic

open Internal.Raw₀

macro_rules
| `(tactic| simp_to_raw $[using $using?]?) => do
  `(tactic|
    (try simp (discharger := wf_trivial) only [$[$(Array.map Lean.mkIdent baseNames):term],*]
     $[apply $(using?.toArray):term];*)
     <;> wf_trivial)

end Internal.Raw

namespace Raw

open Internal.Raw₀ Internal.Raw

variable {m : Raw α β} (h : m.WF)
set_option deprecated.oldSectionVars true

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw α β).isEmpty := by
  simp_to_raw using Raw₀.isEmpty_empty

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α β).isEmpty :=
  isEmpty_empty

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).isEmpty = false := by
  simp_to_raw using Raw₀.isEmpty_insert

theorem mem_iff_contains [BEq α] [Hashable α] {m : Raw α β} {a : α} :
    a ∈ m ↔ m.contains a := Iff.rfl

theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b := by
  simp_to_raw using Raw₀.contains_congr

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m := by
  simp [mem_iff_contains, contains_congr h hab]

@[simp] theorem contains_empty {a : α} {c} : (empty c : Raw α β).contains a = false := by
  simp_to_raw using Raw₀.contains_empty

@[simp] theorem not_mem_empty {a : α} {c} : ¬a ∈ (empty c : Raw α β) := by
  simp [mem_iff_contains]

@[simp] theorem contains_emptyc {a : α} : (∅ : Raw α β).contains a = false :=
  contains_empty

@[simp] theorem not_mem_emptyc {a : α} : ¬a ∈ (∅ : Raw α β) :=
  not_mem_empty

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → m.contains a = false := by
  simp_to_raw using Raw₀.contains_of_isEmpty ⟨m, _⟩

theorem not_mem_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty → ¬a ∈ m := by
  simpa [mem_iff_contains] using contains_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, m.contains a = true := by
  simp_to_raw using Raw₀.isEmpty_eq_false_iff_exists_contains_eq_true ⟨m, _⟩

theorem isEmpty_eq_false_iff_exists_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = false ↔ ∃ a, a ∈ m := by
  simpa [mem_iff_contains] using isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, m.contains a = false := by
  simp_to_raw using Raw₀.isEmpty_iff_forall_contains ⟨m, _⟩

theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m := by
  simpa [mem_iff_contains] using isEmpty_iff_forall_contains h

@[simp]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {v : β k} :
    (m.insert k v).contains a = (k == a || m.contains a) := by
  simp_to_raw using Raw₀.contains_insert

@[simp]
theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m := by
  simp [mem_iff_contains, contains_insert h]

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {a k : α} {v : β k} :
    (m.insert k v).contains a → (k == a) = false → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_insert

theorem mem_of_mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insert k v → (k == a) = false → a ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_insert h

@[simp]
theorem contains_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).contains k := by
  simp_to_raw using Raw₀.contains_insert_self

@[simp]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} : k ∈ m.insert k v := by
  simp [mem_iff_contains, contains_insert_self h]

@[simp]
theorem size_empty {c} : (empty c : Raw α β).size = 0 := by
  simp_to_raw using Raw₀.size_empty

@[simp]
theorem size_emptyc : (∅ : Raw α β).size = 0 :=
  size_empty

theorem isEmpty_eq_size_eq_zero : m.isEmpty = (m.size == 0) := by
  simp [isEmpty]

theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_insert

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insert k v).size := by
  simp_to_raw using Raw₀.size_le_size_insert ⟨m, _⟩ h

theorem size_insert_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
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
theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).isEmpty = (m.isEmpty || (m.size == 1 && m.contains k)) := by
  simp_to_raw using Raw₀.isEmpty_erase

@[simp]
theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) := by
  simp_to_raw using Raw₀.contains_erase

@[simp]
theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [mem_iff_contains, contains_erase h]

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_erase

theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_erase h

theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_erase

theorem size_erase_le [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size := by
  simp_to_raw using Raw₀.size_erase_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    m.size ≤ (m.erase k).size + 1 := by
  simp_to_raw using Raw₀.size_le_size_erase ⟨m, _⟩

@[simp]
theorem containsThenInsert_fst {k : α} {v : β k} : (m.containsThenInsert k v).1 = m.contains k := by
  simp_to_raw using Raw₀.containsThenInsert_fst

@[simp]
theorem containsThenInsert_snd {k : α} {v : β k} : (m.containsThenInsert k v).2 = m.insert k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.containsThenInsert_snd _)

@[simp]
theorem containsThenInsertIfNew_fst {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k := by
  simp_to_raw using Raw₀.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsertIfNew_snd {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.containsThenInsertIfNew_snd _)

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} {c} : (empty c : Raw α β).get? a = none := by
  simp_to_raw using Raw₀.get?_empty

@[simp]
theorem get?_emptyc [LawfulBEq α] {a : α} : (∅ : Raw α β).get? a = none :=
  get?_empty

theorem get?_of_isEmpty [LawfulBEq α] {a : α} : m.isEmpty = true → m.get? a = none := by
  simp_to_raw using Raw₀.get?_of_isEmpty ⟨m, _⟩

theorem get?_insert [LawfulBEq α] {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a := by
  simp_to_raw using Raw₀.get?_insert

@[simp]
theorem get?_insert_self [LawfulBEq α] {k : α} {v : β k} : (m.insert k v).get? k = some v := by
  simp_to_raw using Raw₀.get?_insert_self

theorem contains_eq_isSome_get? [LawfulBEq α] {a : α} : m.contains a = (m.get? a).isSome := by
  simp_to_raw using Raw₀.contains_eq_isSome_get?

theorem get?_eq_none_of_contains_eq_false [LawfulBEq α] {a : α} :
    m.contains a = false → m.get? a = none := by
  simp_to_raw using Raw₀.get?_eq_none

theorem get?_eq_none [LawfulBEq α] {a : α} : ¬a ∈ m → m.get? a = none := by
  simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [LawfulBEq α] {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  simp_to_raw using Raw₀.get?_erase

@[simp]
theorem get?_erase_self [LawfulBEq α] {k : α} : (m.erase k).get? k = none := by
  simp_to_raw using Raw₀.get?_erase_self

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

@[simp]
theorem get?_empty {a : α} {c} : get? (empty c : Raw α (fun _ => β)) a = none := by
  simp_to_raw using Raw₀.Const.get?_empty

@[simp]
theorem get?_emptyc {a : α} : get? (∅ : Raw α (fun _ => β)) a = none :=
  get?_empty

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} :
    m.isEmpty = true → get? m a = none := by
  simp_to_raw using Raw₀.Const.get?_of_isEmpty ⟨m, _⟩

theorem get?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a := by
  simp_to_raw using Raw₀.Const.get?_insert

@[simp]
theorem get?_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get? (m.insert k v) k = some v := by
  simp_to_raw using Raw₀.Const.get?_insert_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = (get? m a).isSome := by
  simp_to_raw using Raw₀.Const.contains_eq_isSome_get?

theorem get?_eq_none_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = false → get? m a = none := by
  simp_to_raw using Raw₀.Const.get?_eq_none

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → get? m a = none := by
    simpa [mem_iff_contains] using get?_eq_none_of_contains_eq_false h

theorem get?_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a := by
  simp_to_raw using Raw₀.Const.get?_erase

@[simp]
theorem get?_erase_self [EquivBEq α] [LawfulHashable α] {k : α} : get? (m.erase k) k = none := by
  simp_to_raw using Raw₀.Const.get?_erase_self

theorem get?_eq_get? [LawfulBEq α] {a : α} : get? m a = m.get? a := by
  simp_to_raw using Raw₀.Const.get?_eq_get?

theorem get?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    get? m a = get? m b := by
  simp_to_raw using Raw₀.Const.get?_congr

end Const

theorem get_insert [LawfulBEq α] {k a : α} {v : β k} {h₁} :
    (m.insert k v).get a h₁ =
      if h₂ : k == a then
        cast (congrArg β (eq_of_beq h₂)) v
      else
        m.get a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.get_insert ⟨m, _⟩

@[simp]
theorem get_insert_self [LawfulBEq α] {k : α} {v : β k} :
    (m.insert k v).get k (mem_insert_self h) = v := by
  simp_to_raw using Raw₀.get_insert_self ⟨m, _⟩

@[simp]
theorem get_erase [LawfulBEq α] {k a : α} {h'} :
    (m.erase a).get k h' = m.get k (mem_of_mem_erase h h') := by
  simp_to_raw using Raw₀.get_erase ⟨m, _⟩

theorem get?_eq_some_get [LawfulBEq α] {a : α} {h} : m.get? a = some (m.get a h) := by
  simp_to_raw using Raw₀.get?_eq_some_get

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v else get m a (mem_of_mem_insert h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_raw using Raw₀.Const.get_insert ⟨m, _⟩

@[simp]
theorem get_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    get (m.insert k v) k (mem_insert_self h) = v := by
  simp_to_raw using Raw₀.Const.get_insert_self ⟨m, _⟩

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
    get (m.erase k) a h' = get m a (mem_of_mem_erase h h') := by
  simp_to_raw using Raw₀.Const.get_erase ⟨m, _⟩

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} {h : a ∈ m} :
    get? m a = some (get m a h) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_get

theorem get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h := by
  simp_to_raw using Raw₀.Const.get_eq_get

theorem get_congr [LawfulBEq α] {a b : α} (hab : a == b) {h'} :
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

theorem get!_of_isEmpty [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.isEmpty = true → m.get! a = default := by
  simp_to_raw using Raw₀.get!_of_isEmpty ⟨m, _⟩

theorem get!_insert [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} : (m.insert k v).get! a =
    if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.get! a := by
  simp_to_raw using Raw₀.get!_insert

@[simp]
theorem get!_insert_self [LawfulBEq α] {k : α} [Inhabited (β k)] {v : β k} :
    (m.insert k v).get! k = v := by
  simp_to_raw using Raw₀.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_raw using Raw₀.get!_eq_default

theorem get!_eq_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
    ¬a ∈ m → m.get! a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [LawfulBEq α] {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a := by
  simp_to_raw using Raw₀.get!_erase

@[simp]
theorem get!_erase_self [LawfulBEq α] {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default := by
  simp_to_raw using Raw₀.get!_erase_self

theorem get?_eq_some_get!_of_contains [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) := by
  simp_to_raw using Raw₀.get?_eq_some_get!

theorem get?_eq_some_get! [LawfulBEq α] {a : α} [Inhabited (β a)] :
    a ∈ m → m.get? a = some (m.get! a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [LawfulBEq α] {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! := by
  simp_to_raw using Raw₀.get!_eq_get!_get?

theorem get_eq_get! [LawfulBEq α] {a : α} [Inhabited (β a)] {h} :
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

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.isEmpty = true → get! m a = default := by
  simp_to_raw using Raw₀.Const.get!_of_isEmpty ⟨m, _⟩

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a := by
  simp_to_raw using Raw₀.Const.get!_insert

@[simp]
theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} :
    get! (m.insert k v) k = v := by
  simp_to_raw using Raw₀.Const.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_raw using Raw₀.Const.get!_eq_default

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    ¬a ∈ m → get! m a = default := by
  simpa [mem_iff_contains] using get!_eq_default_of_contains_eq_false h

theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a := by
  simp_to_raw using Raw₀.Const.get!_erase

@[simp]
theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} :
    get! (m.erase k) k = default := by
  simp_to_raw using Raw₀.Const.get!_erase_self

theorem get?_eq_some_get!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    m.contains a = true → get? m a = some (get! m a) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_get!

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    a ∈ m → get? m a = some (get! m a) := by
  simpa [mem_iff_contains] using get?_eq_some_get!_of_contains h

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = (get? m a).get! := by
  simp_to_raw using Raw₀.Const.get!_eq_get!_get?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h} :
    get m a h = get! m a := by
  simp_to_raw using Raw₀.Const.get_eq_get!

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] {a : α} :
    get! m a = m.get! a := by
  simp_to_raw using Raw₀.Const.get!_eq_get!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : a == b) :
    get! m a = get! m b := by
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

theorem getD_of_isEmpty [LawfulBEq α] {a : α} {fallback : β a} :
    m.isEmpty = true → m.getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_of_isEmpty ⟨m, _⟩

theorem getD_insert [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insert k v).getD a fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.getD a fallback := by
  simp_to_raw using Raw₀.getD_insert

@[simp]
theorem getD_insert_self [LawfulBEq α] {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_raw using Raw₀.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_raw using Raw₀.getD_eq_fallback

theorem getD_eq_fallback [LawfulBEq α] {a : α} {fallback : β a} :
    ¬a ∈ m → m.getD a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [LawfulBEq α] {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback := by
  simp_to_raw using Raw₀.getD_erase

@[simp]
theorem getD_erase_self [LawfulBEq α] {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback := by
  simp_to_raw using Raw₀.getD_erase_self

theorem get?_eq_some_getD_of_contains [LawfulBEq α] {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) := by
  simp_to_raw using Raw₀.get?_eq_some_getD

theorem get?_eq_some_getD [LawfulBEq α] {a : α} {fallback : β a} :
    a ∈ m → m.get? a = some (m.getD a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [LawfulBEq α] {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback := by
  simp_to_raw using Raw₀.getD_eq_getD_get?

theorem get_eq_getD [LawfulBEq α] {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback := by
  simp_to_raw using Raw₀.get_eq_getD

theorem get!_eq_getD_default [LawfulBEq α] {a : α} [Inhabited (β a)] :
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

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.isEmpty = true → getD m a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_of_isEmpty ⟨m, _⟩

theorem getD_insert [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback := by
  simp_to_raw using Raw₀.Const.getD_insert

@[simp]
theorem getD_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback v : β} :
   getD (m.insert k v) k fallback = v := by
  simp_to_raw using Raw₀.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : β} : m.contains a = false → getD m a fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_fallback

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    ¬a ∈ m → getD m a fallback = fallback := by
  simpa [mem_iff_contains] using getD_eq_fallback_of_contains_eq_false h

theorem getD_erase [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback := by
  simp_to_raw using Raw₀.Const.getD_erase

@[simp]
theorem getD_erase_self [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback := by
  simp_to_raw using Raw₀.Const.getD_erase_self

theorem get?_eq_some_getD_of_contains [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) := by
  simp_to_raw using Raw₀.Const.get?_eq_some_getD

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    a ∈ m → get? m a = some (getD m a fallback) := by
  simpa [mem_iff_contains] using get?_eq_some_getD_of_contains h

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_getD_get?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback := by
  simp_to_raw using Raw₀.Const.get_eq_getD

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} :
    get! m a = getD m a default := by
  simp_to_raw using Raw₀.Const.get!_eq_getD_default

theorem getD_eq_getD [LawfulBEq α] {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback := by
  simp_to_raw using Raw₀.Const.getD_eq_getD

theorem getD_congr [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : a == b) :
    getD m a fallback = getD m b fallback := by
  simp_to_raw using Raw₀.Const.getD_congr

end Const

@[simp]
theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).isEmpty = false := by
  simp_to_raw using Raw₀.isEmpty_insertIfNew

@[simp]
theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) := by
  simp_to_raw using Raw₀.contains_insertIfNew

@[simp]
theorem mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v ↔ k == a ∨ a ∈ m := by
  simp [mem_iff_contains, contains_insertIfNew h]

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).contains k := by
  simp_to_raw using Raw₀.contains_insertIfNew_self

theorem mem_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    k ∈ m.insertIfNew k v := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_insertIfNew_self h

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m := by
  simpa [mem_iff_contains, -contains_insertIfNew] using contains_of_contains_insertIfNew h

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a := by
  simp_to_raw using Raw₀.contains_of_contains_insertIfNew'

/-- This is a restatement of `mem_insertIfNew` that is written to exactly match the proof obligation
in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} :
    a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m := by
  simpa [mem_iff_contains] using contains_of_contains_insertIfNew' h

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1 := by
  simp only [mem_iff_contains]
  simp_to_raw using Raw₀.size_insertIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    m.size ≤ (m.insertIfNew k v).size := by
  simp_to_raw using Raw₀.size_le_size_insertIfNew ⟨m, _⟩

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] {k : α} {v : β k} :
    (m.insertIfNew k v).size ≤ m.size + 1 := by
  simp_to_raw using Raw₀.size_insertIfNew_le

theorem get?_insertIfNew [LawfulBEq α] {k a : α} {v : β k} :
    (m.insertIfNew k v).get? a =
      if h : k == a ∧ ¬k ∈ m then some (cast (congrArg β (eq_of_beq h.1)) v)
      else m.get? a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get?_insertIfNew ⟨m, _⟩

theorem get_insertIfNew [LawfulBEq α] {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).get a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.get a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get_insertIfNew ⟨m, _⟩

theorem get!_insertIfNew [LawfulBEq α] {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v else m.get! a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.get!_insertIfNew ⟨m, _⟩

theorem getD_insertIfNew [LawfulBEq α] {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.getD_insertIfNew

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then some v else get? m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get?_insertIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ ¬k ∈ m then v
      else get m a (mem_of_mem_insertIfNew' h h₁ h₂) := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get_insertIfNew ⟨m, _⟩

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then v else get! m a := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.get!_insertIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ ¬k ∈ m then v else getD m a fallback := by
  simp only [mem_iff_contains, Bool.not_eq_true]
  simp_to_raw using Raw₀.Const.getD_insertIfNew

end Const

@[simp]
theorem getThenInsertIfNew?_fst [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k := by
  simp_to_raw using Raw₀.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.getThenInsertIfNew?_snd _)

namespace Const

variable {β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)

@[simp]
theorem getThenInsertIfNew?_fst {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k := by
  simp_to_raw using Raw₀.Const.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v := by
  simp_to_raw using congrArg Subtype.val (Raw₀.Const.getThenInsertIfNew?_snd _)

end Const

end Raw

end Std.DHashMap
