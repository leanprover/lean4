/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.WF

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: verification of operations on `Raw₀`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.Internal.List
open Std.Internal

universe u v w

variable {α : Type u} {β : α → Type v}

namespace Std.DHashMap.Internal

section empty

@[simp]
theorem Raw₀.buckets_empty {c} {i : Nat} {h} :
    (empty c : Raw₀ α β).1.buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem Raw.buckets_empty {c} {i : Nat} {h} :
    (Raw.empty c : Raw α β).buckets[i]'h = AssocList.nil := by
  simp [Raw.empty]

@[simp]
theorem Raw.buckets_emptyc {i : Nat} {h} :
    (∅ : Raw α β).buckets[i]'h = AssocList.nil :=
  buckets_empty

variable [BEq α] [Hashable α]

@[simp]
theorem buckets_empty {c} {i : Nat} {h} :
    (empty c : DHashMap α β).1.buckets[i]'h = AssocList.nil := by
  simp [empty]

@[simp]
theorem buckets_emptyc {i : Nat} {h} :
    (∅ : DHashMap α β).1.buckets[i]'h = AssocList.nil :=
  buckets_empty

end empty

namespace Raw₀

variable (m : Raw₀ α β)

@[simp]
theorem size_empty {c} : (empty c : Raw₀ α β).1.size = 0 := rfl

theorem isEmpty_eq_size_eq_zero : m.1.isEmpty = (m.1.size == 0) := by
  simp [Raw.isEmpty]

variable [BEq α] [Hashable α]

/-- Internal implementation detail of the hash map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply Raw₀.wfImp_insert | apply Raw₀.wfImp_insertIfNew | apply Raw₀.wfImp_insertMany
    | apply Raw₀.Const.wfImp_insertMany | apply Raw₀.Const.wfImp_insertManyIfNewUnit
    | apply Raw₀.wfImp_alter | apply Raw₀.wfImp_modify
    | apply Raw₀.Const.wfImp_alter | apply Raw₀.Const.wfImp_modify
    | apply Raw₀.wfImp_erase | apply Raw.WF.out | assumption | apply Raw₀.wfImp_empty
    | apply Raw.WFImp.distinct | apply Raw.WF.empty₀))

/-- Internal implementation detail of the hash map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``contains_eq_containsKey, ``Raw.isEmpty_eq_isEmpty, ``Raw.size_eq_length,
    ``get?_eq_getValueCast?, ``Const.get?_eq_getValue?, ``get_eq_getValueCast,
    ``Const.get_eq_getValue, ``get!_eq_getValueCast!, ``getD_eq_getValueCastD,
    ``Const.get!_eq_getValue!, ``Const.getD_eq_getValueD, ``getKey?_eq_getKey?,
    ``getKey_eq_getKey, ``getKeyD_eq_getKeyD, ``getKey!_eq_getKey!,
    ``Raw.toList_eq_toListModel, ``Raw.keys_eq_keys_toListModel,
    ``Raw.Const.toList_eq_toListModel_map, ``Raw.foldM_eq_foldlM_toListModel,
    ``Raw.fold_eq_foldl_toListModel, ``Raw.foldRevM_eq_foldrM_toListModel,
    ``Raw.foldRev_eq_foldr_toListModel, ``Raw.forIn_eq_forIn_toListModel,
    ``Raw.forM_eq_forM_toListModel]

private def modifyMap : Std.DHashMap Name (fun _ => Name) :=
  .ofList
    [⟨`insert, ``toListModel_insert⟩,
     ⟨`erase, ``toListModel_erase⟩,
     ⟨`insertIfNew, ``toListModel_insertIfNew⟩,
     ⟨`insertMany, ``toListModel_insertMany_list⟩,
     ⟨`Const.insertMany, ``Const.toListModel_insertMany_list⟩,
     ⟨`Const.insertManyIfNewUnit, ``Const.toListModel_insertManyIfNewUnit_list⟩,
     ⟨`alter, ``toListModel_alter⟩,
     ⟨`modify, ``toListModel_modify⟩,
     ⟨`Const.alter, ``Const.toListModel_alter⟩,
     ⟨`Const.modify, ``Const.toListModel_modify⟩]

private def congrNames : MacroM (Array (TSyntax `term)) := do
  return #[← `(_root_.List.Perm.isEmpty_eq), ← `(containsKey_of_perm),
    ← `(_root_.List.Perm.length_eq), ← `(getValueCast?_of_perm _),
    ← `(getValue?_of_perm _), ← `(getValue_of_perm _), ← `(getValueCast_of_perm _),
    ← `(getValueCast!_of_perm _), ← `(getValueCastD_of_perm _), ← `(getValue!_of_perm _),
    ← `(getValueD_of_perm _), ← `(getKey?_of_perm _), ← `(getKey_of_perm _), ← `(getKeyD_of_perm _),
    ← `(getKey!_of_perm _)]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_model" (" [" (ident,*) "]")? ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[[$modifyNames,*]]? $[using $using?]?) => do
  let mut congrModify : Array (TSyntax `term) := #[]
  if let some modifyNames := modifyNames then
    for modify in modifyNames.getElems.flatMap
        (fun n => modifyMap.get? (Lean.Syntax.getId n) |>.toArray) do
      for congr in (← congrNames) do
        congrModify := congrModify.push (← `($congr:term ($(mkIdent modify) ..)))
  `(tactic|
    (simp (discharger := wf_trivial) only
      [$[$(Array.map Lean.mkIdent queryNames):term],*, $[$congrModify:term],*]
     $[apply $(using?.toArray):term];*)
    <;> wf_trivial)

@[simp]
theorem isEmpty_empty {c} : (empty c : Raw₀ α β).1.isEmpty := by
  rw [Raw.isEmpty_eq_isEmpty wfImp_empty, toListModel_buckets_empty, List.isEmpty_nil]

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.isEmpty = false := by
  simp_to_model [insert] using List.isEmpty_insertEntry

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b := by
  simp_to_model using List.containsKey_congr hab

@[simp]
theorem contains_empty {a : α} {c : Nat} : (empty c : Raw₀ α β).contains a = false := by
  simp [contains]

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.contains a = false := by
  simp_to_model; empty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.isEmpty = false ↔ ∃ a, m.contains a = true := by
  simp_to_model using List.isEmpty_eq_false_iff_exists_containsKey

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.isEmpty ↔ ∀ a, m.contains a = false := by
  simp_to_model using List.isEmpty_iff_forall_containsKey

theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insert k v).contains a = ((k == a) || m.contains a) := by
  simp_to_model [insert] using List.containsKey_insertEntry

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} : (m.insert k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model [insert] using List.containsKey_of_containsKey_insertEntry

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).contains k := by
  simp_to_model [insert] using List.containsKey_insertEntry_self

theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.size = if m.contains k then m.1.size else m.1.size + 1 := by
  simp_to_model [insert] using List.length_insertEntry

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    m.1.size ≤ (m.insert k v).1.size := by
  simp_to_model [insert] using List.length_le_length_insertEntry

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.size ≤ m.1.size + 1 := by
  simp_to_model [insert] using List.length_insertEntry_le

@[simp]
theorem erase_empty {k : α} {c : Nat} : (empty c : Raw₀ α β).erase k = empty c := by
  simp [erase, empty]

theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.isEmpty = (m.1.isEmpty || (m.1.size == 1 && m.contains k)) := by
  simp_to_model [erase] using List.isEmpty_eraseKey

theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) := by
  simp_to_model [erase] using List.containsKey_eraseKey

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).contains a → m.contains a := by
  simp_to_model [erase] using List.containsKey_of_containsKey_eraseKey

theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.size = if m.contains k then m.1.size - 1 else m.1.size := by
  simp_to_model [erase] using List.length_eraseKey

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.size ≤ m.1.size := by
  simp_to_model [erase] using List.length_eraseKey_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    m.1.size ≤ (m.erase k).1.size + 1 := by
  simp_to_model [erase] using List.length_le_length_eraseKey

@[simp]
theorem containsThenInsert_fst {k : α} {v : β k} : (m.containsThenInsert k v).1 = m.contains k := by
  rw [containsThenInsert_eq_containsₘ, contains_eq_containsₘ]

@[simp]
theorem containsThenInsert_snd {k : α} {v : β k} : (m.containsThenInsert k v).2 = m.insert k v := by
  rw [containsThenInsert_eq_insertₘ, insert_eq_insertₘ]

@[simp]
theorem containsThenInsertIfNew_fst {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).1 = m.contains k := by
  rw [containsThenInsertIfNew_eq_containsₘ, contains_eq_containsₘ]

@[simp]
theorem containsThenInsertIfNew_snd {k : α} {v : β k} :
    (m.containsThenInsertIfNew k v).2 = m.insertIfNew k v := by
  rw [containsThenInsertIfNew_eq_insertIfNewₘ, insertIfNew_eq_insertIfNewₘ]

@[simp]
theorem get?_empty [LawfulBEq α] {a : α} {c} : (empty c : Raw₀ α β).get? a = none := by
  simp [get?]

theorem get?_of_isEmpty [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.get? a = none := by
  simp_to_model; empty

theorem get?_insert [LawfulBEq α] (h : m.1.WF) {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a := by
  simp_to_model [insert] using List.getValueCast?_insertEntry

theorem get?_insert_self [LawfulBEq α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).get? k = some v := by
  simp_to_model [insert] using List.getValueCast?_insertEntry_self

theorem contains_eq_isSome_get? [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a = (m.get? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValueCast?

theorem get?_eq_none [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.get? a = none := by
  simp_to_model using List.getValueCast?_eq_none

theorem get?_erase [LawfulBEq α] (h : m.1.WF) {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  simp_to_model [erase] using List.getValueCast?_eraseKey

theorem get?_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} : (m.erase k).get? k = none := by
  simp_to_model [erase] using List.getValueCast?_eraseKey_self

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

@[simp]
theorem get?_empty {a : α} {c} : get? (empty c : Raw₀ α (fun _ => β)) a = none := by
  simp [get?]

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → get? m a = none := by
  simp_to_model; empty

theorem get?_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a := by
  simp_to_model [insert] using List.getValue?_insertEntry

theorem get?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β} :
    get? (m.insert k v) k = some v := by
  simp_to_model [insert] using List.getValue?_insertEntry_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = (get? m a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValue?

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = false → get? m a = none := by
  simp_to_model using List.getValue?_eq_none.2

theorem get?_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a := by
  simp_to_model [erase] using List.getValue?_eraseKey

theorem get?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    get? (m.erase k) k = none := by
  simp_to_model [erase] using List.getValue?_eraseKey_self

theorem get?_eq_get? [LawfulBEq α] (h : m.1.WF) {a : α} : get? m a = m.get? a := by
  simp_to_model using List.getValue?_eq_getValueCast?

theorem get?_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} (hab : a == b) :
    get? m a = get? m b := by
  simp_to_model using List.getValue?_congr

end Const

theorem get_insert [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).get a h₁ =
      if h₂ : k == a then
        cast (congrArg β (eq_of_beq h₂)) v
      else
        m.get a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model [insert] using List.getValueCast_insertEntry

theorem get_insert_self [LawfulBEq α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).get k (contains_insert_self _ h) = v := by
  simp_to_model [insert] using List.getValueCast_insertEntry_self

@[simp]
theorem get_erase [LawfulBEq α] (h : m.1.WF) {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (contains_of_contains_erase _ h h') := by
  simp_to_model [erase] using List.getValueCast_eraseKey

theorem get?_eq_some_get [LawfulBEq α] (h : m.1.WF) {a : α} {h'} : m.get? a = some (m.get a h') := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v
      else get m a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model [insert] using List.getValue_insertEntry

theorem get_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β} :
    get (m.insert k v) k (contains_insert_self _ h) = v := by
  simp_to_model [insert] using List.getValue_insertEntry_self

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {h'} :
    get (m.erase k) a h' = get m a (contains_of_contains_erase _ h h') := by
  simp_to_model [erase] using List.getValue_eraseKey

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {h} :
    get? m a = some (get m a h) := by
  simp_to_model using List.getValue?_eq_some_getValue

theorem get_eq_get [LawfulBEq α] (h : m.1.WF) {a : α} {h} : get m a h = m.get a h := by
  simp_to_model using List.getValue_eq_getValueCast

theorem get_congr [LawfulBEq α] (h : m.1.WF) {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((contains_congr _ h hab).symm.trans h') := by
  simp_to_model using List.getValue_congr

end Const

theorem get!_empty [LawfulBEq α] {a : α} [Inhabited (β a)] {c} :
    (empty c : Raw₀ α β).get! a = default := by
  simp [get!, empty]

theorem get!_of_isEmpty [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.1.isEmpty = true → m.get! a = default := by
  simp_to_model; empty

theorem get!_insert [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insert k v).get! a =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.get! a := by
  simp_to_model [insert] using List.getValueCast!_insertEntry

theorem get!_insert_self [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b := by
  simp_to_model [insert] using List.getValueCast!_insertEntry_self

theorem get!_eq_default [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_model using List.getValueCast!_eq_default

theorem get!_erase [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a := by
  simp_to_model [erase] using List.getValueCast!_eraseKey

theorem get!_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default := by
  simp_to_model [erase] using List.getValueCast!_eraseKey_self

theorem get?_eq_some_get! [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast!

theorem get!_eq_get!_get? [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! := by
  simp_to_model using List.getValueCast!_eq_getValueCast?

theorem get_eq_get! [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a := by
  simp_to_model using List.getValueCast_eq_getValueCast!

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get!_empty [Inhabited β] {a : α} {c} :
    get! (empty c : Raw₀ α (fun _ => β)) a = default := by
  simp [get!, empty]

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → get! m a = default := by
  simp_to_model; empty

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a := by
  simp_to_model [insert] using List.getValue!_insertEntry

theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k : α}
    {v : β} : get! (m.insert k v) k = v := by
  simp_to_model [insert] using List.getValue!_insertEntry_self

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_model using List.getValue!_eq_default

theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a := by
  simp_to_model [erase] using List.getValue!_eraseKey

theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k : α} :
    get! (m.erase k) k = default := by
  simp_to_model [erase] using List.getValue!_eraseKey_self

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.contains a = true → get? m a = some (get! m a) := by
  simp_to_model using List.getValue?_eq_some_getValue!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    get! m a = (get? m a).get! := by
  simp_to_model using List.getValue!_eq_getValue?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} {h} :
    get m a h = get! m a := by
  simp_to_model using List.getValue_eq_getValue!

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] (h : m.1.WF) {a : α} :
    get! m a = m.get! a := by
  simp_to_model using List.getValue!_eq_getValueCast!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a b : α}
    (hab : a == b) : get! m a = get! m b := by
  simp_to_model using List.getValue!_congr

end Const

theorem getD_empty [LawfulBEq α] {a : α} {fallback : β a} {c} :
    (empty c : Raw₀ α β).getD a fallback = fallback := by
  simp [getD, empty]

theorem getD_of_isEmpty [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.1.isEmpty = true → m.getD a fallback = fallback := by
  simp_to_model; empty

theorem getD_insert [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insert k v).getD a fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.getD a fallback := by
  simp_to_model [insert] using List.getValueCastD_insertEntry

theorem getD_insert_self [LawfulBEq α] (h : m.1.WF) {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_model [insert] using List.getValueCastD_insertEntry_self

theorem getD_eq_fallback [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_model using List.getValueCastD_eq_fallback

theorem getD_erase [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback := by
  simp_to_model [erase] using List.getValueCastD_eraseKey

theorem getD_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback := by
  simp_to_model [erase] using List.getValueCastD_eraseKey_self

theorem get?_eq_some_getD [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCastD

theorem getD_eq_getD_get? [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback := by
  simp_to_model using List.getValueCastD_eq_getValueCast?

theorem get_eq_getD [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback := by
  simp_to_model using List.getValueCast_eq_getValueCastD

theorem get!_eq_getD_default [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  simp_to_model using List.getValueCast!_eq_getValueCastD_default

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem getD_empty {a : α} {fallback : β} {c} :
    getD (empty c : Raw₀ α (fun _ => β)) a fallback = fallback := by
  simp [getD, empty]

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.1.isEmpty = true → getD m a fallback = fallback := by
  simp_to_model; empty

theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback := by
  simp_to_model [insert] using List.getValueD_insertEntry

theorem getD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {fallback v : β} :
    getD (m.insert k v) k fallback = v := by
  simp_to_model [insert] using List.getValueD_insertEntry_self

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.contains a = false → getD m a fallback = fallback := by
  simp_to_model using List.getValueD_eq_fallback

theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback := by
  simp_to_model [erase] using List.getValueD_eraseKey

theorem getD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback := by
  simp_to_model [erase] using List.getValueD_eraseKey_self

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) := by
  simp_to_model using List.getValue?_eq_some_getValueD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback := by
  simp_to_model using List.getValueD_eq_getValue?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback := by
  simp_to_model using List.getValue_eq_getValueD

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    get! m a = getD m a default := by
  simp_to_model using List.getValue!_eq_getValueD_default

theorem getD_eq_getD [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback := by
  simp_to_model using List.getValueD_eq_getValueCastD

theorem getD_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} {fallback : β}
    (hab : a == b) : getD m a fallback = getD m b fallback := by
  simp_to_model using List.getValueD_congr

end Const

@[simp]
theorem getKey?_empty {a : α} {c} : (empty c : Raw₀ α β).getKey? a = none := by
  simp [getKey?]

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.getKey? a = none := by
  simp_to_model; empty

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a := by
  simp_to_model [insert] using List.getKey?_insertEntry

theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k := by
  simp_to_model [insert] using List.getKey?_insertEntry_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getKey?

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.getKey? a = none := by
  simp_to_model using List.getKey?_eq_none

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a := by
  simp_to_model [erase] using List.getKey?_eraseKey

theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).getKey? k = none := by
  simp_to_model [erase] using List.getKey?_eraseKey_self

theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model [insert] using List.getKey_insertEntry

theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).getKey k (contains_insert_self _ h) = k := by
  simp_to_model [insert] using List.getKey_insertEntry_self

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (contains_of_contains_erase _ h h') := by
  simp_to_model [erase] using List.getKey_eraseKey

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {h'} :
    m.getKey? a = some (m.getKey a h') := by
  simp_to_model using List.getKey?_eq_some_getKey

theorem getKey!_empty {a : α} [Inhabited α] {c} :
    (empty c : Raw₀ α β).getKey! a = default := by
  simp [getKey!, empty]

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.getKey! a = default := by
  simp_to_model; empty;

theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insert k v).getKey! a = if k == a then k else m.getKey! a := by
  simp_to_model [insert] using List.getKey!_insertEntry

theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α}
    {b : β a} : (m.insert a b).getKey! a = a := by
  simp_to_model [insert] using List.getKey!_insertEntry_self

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.getKey! a = default := by
  simp_to_model using List.getKey!_eq_default

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a := by
  simp_to_model [erase] using List.getKey!_eraseKey

theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k : α} :
    (m.erase k).getKey! k = default := by
  simp_to_model [erase] using List.getKey!_eraseKey_self

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) := by
  simp_to_model using List.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.getKey! a = (m.getKey? a).get! := by
  simp_to_model using List.getKey!_eq_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} {h} :
    m.getKey a h = m.getKey! a := by
  simp_to_model using List.getKey_eq_getKey!

theorem getKeyD_empty {a : α} {fallback : α} {c} :
    (empty c : Raw₀ α β).getKeyD a fallback = fallback := by
  simp [getKeyD, empty]

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.1.isEmpty = true → m.getKeyD a fallback = fallback := by
  simp_to_model; empty

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α} {v : β k} :
    (m.insert k v).getKeyD a fallback =
      if k == a then k else m.getKeyD a fallback := by
  simp_to_model [insert] using List.getKeyD_insertEntry

theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α}
    {b : β a} :
    (m.insert a b).getKeyD a fallback = a := by
  simp_to_model [insert] using List.getKeyD_insertEntry_self

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback := by
  simp_to_model using List.getKeyD_eq_fallback

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback := by
  simp_to_model [erase] using List.getKeyD_eraseKey

theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback := by
  simp_to_model [erase] using List.getKeyD_eraseKey_self

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) := by
  simp_to_model using List.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback := by
  simp_to_model using List.getKeyD_eq_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} {h} :
    m.getKey a h = m.getKeyD a fallback := by
  simp_to_model using List.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {a : α} :
    m.getKey! a = m.getKeyD a default := by
  simp_to_model using List.getKey!_eq_getKeyD_default

theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.isEmpty = false := by
  simp_to_model [insertIfNew] using List.isEmpty_insertEntryIfNew

theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) := by
  simp_to_model [insertIfNew] using List.containsKey_insertEntryIfNew

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).contains k := by
  simp_to_model [insertIfNew] using List.containsKey_insertEntryIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} : (m.insertIfNew k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model [insertIfNew] using List.containsKey_of_containsKey_insertEntryIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a := by
  simp_to_model [insertIfNew] using List.containsKey_of_containsKey_insertEntryIfNew'

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.size = if m.contains k then m.1.size else m.1.size + 1 := by
  simp_to_model [insertIfNew] using List.length_insertEntryIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    m.1.size ≤ (m.insertIfNew k v).1.size := by
  simp_to_model [insertIfNew] using List.length_le_length_insertEntryIfNew

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.size ≤ m.1.size + 1 := by
  simp_to_model [insertIfNew] using List.length_insertEntryIfNew_le

theorem get?_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).get? a =
      if h : k == a ∧ m.contains k = false then some (cast (congrArg β (eq_of_beq h.1)) v)
      else m.get? a := by
  simp_to_model [insertIfNew] using List.getValueCast?_insertEntryIfNew

theorem get_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).get a h₁ =
      if h₂ : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.get a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model [insertIfNew] using List.getValueCast_insertEntryIfNew

theorem get!_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h.1)) v
      else m.get! a := by
  simp_to_model [insertIfNew] using List.getValueCast!_insertEntryIfNew

theorem getD_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp_to_model [insertIfNew] using List.getValueCastD_insertEntryIfNew

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ m.contains k = false then some v else get? m a := by
  simp_to_model [insertIfNew] using List.getValue?_insertEntryIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ m.contains k = false then v
      else get m a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model [insertIfNew] using List.getValue_insertEntryIfNew

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α}
    {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ m.contains k = false then v else get! m a := by
  simp_to_model [insertIfNew] using List.getValue!_insertEntryIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ m.contains k = false then v else getD m a fallback := by
  simp_to_model [insertIfNew] using List.getValueD_insertEntryIfNew

end Const

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).getKey? a =
      if k == a ∧ m.contains k = false then some k else m.getKey? a := by
  simp_to_model [insertIfNew] using List.getKey?_insertEntryIfNew

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).getKey a h₁ =
      if h₂ : k == a ∧ m.contains k = false then k
      else m.getKey a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model [insertIfNew] using List.getKey_insertEntryIfNew

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).getKey! a =
      if k == a ∧ m.contains k = false then k else m.getKey! a := by
  simp_to_model [insertIfNew] using List.getKey!_insertEntryIfNew

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α}
    {v : β k} :
    (m.insertIfNew k v).getKeyD a fallback =
      if k == a ∧ m.contains k = false then k else m.getKeyD a fallback := by
  simp_to_model [insertIfNew] using List.getKeyD_insertEntryIfNew

@[simp]
theorem getThenInsertIfNew?_fst [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).1 = m.get? k := by
  rw [getThenInsertIfNew?_eq_get?ₘ, get?_eq_get?ₘ]

@[simp]
theorem getThenInsertIfNew?_snd [LawfulBEq α] {k : α} {v : β k} :
    (m.getThenInsertIfNew? k v).2 = m.insertIfNew k v := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ, insertIfNew_eq_insertIfNewₘ]

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

@[simp]
theorem getThenInsertIfNew?_fst {k : α} {v : β} : (getThenInsertIfNew? m k v).1 = get? m k := by
  rw [getThenInsertIfNew?_eq_get?ₘ, get?_eq_get?ₘ]

@[simp]
theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ, insertIfNew_eq_insertIfNewₘ]

end Const

@[simp]
theorem length_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.keys.length = m.1.size := by
  simp_to_model using List.length_keys_eq_length

@[simp]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.keys.isEmpty = m.1.isEmpty := by
  simp_to_model using List.isEmpty_keys_eq_isEmpty

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    m.1.keys.contains k = m.contains k := by
  simp_to_model using List.containsKey_eq_keys_contains.symm

@[simp]
theorem mem_keys [LawfulBEq α] (h : m.1.WF) {k : α} :
    k ∈ m.1.keys ↔ m.contains k := by
  rw [← List.contains_iff]
  simp_to_model
  rw [List.containsKey_eq_keys_contains]

theorem distinct_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.keys.Pairwise (fun a b => (a == b) = false) := by
  simp_to_model using (Raw.WF.out h).distinct.distinct

theorem map_sigma_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.1.toList.map Sigma.fst = m.1.keys := by
  simp_to_model
  rw [List.keys_eq_map]

theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.toList.length = m.1.size := by
  simp_to_model

theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.toList.isEmpty = m.1.isEmpty := by
  simp_to_model

theorem mem_toList_iff_get?_eq_some [LawfulBEq α] (h : m.1.WF)
    {k : α} {v : β k} :
    ⟨k, v⟩ ∈ m.1.toList ↔ m.get? k = some v := by
  simp_to_model using List.mem_iff_getValueCast?_eq_some

theorem find?_toList_eq_some_iff_get?_eq_some [LawfulBEq α]
    (h : m.1.WF) {k : α} {v : β k} :
    m.1.toList.find? (·.1 == k) = some ⟨k, v⟩ ↔ m.get? k = some v := by
  simp_to_model using List.find?_eq_some_iff_getValueCast?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {k : α} :
    m.1.toList.find? (·.1 == k) = none ↔ m.contains k = false := by
  simp_to_model using List.find?_eq_none_iff_containsKey_eq_false

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.toList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  simp_to_model using List.pairwise_fst_eq_false

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β))

theorem map_prod_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    (Raw.Const.toList m.1).map Prod.fst = m.1.keys := by
  simp_to_model using List.map_prod_fst_map_toProd_eq_keys

theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    (Raw.Const.toList m.1).length = m.1.size := by
  simp_to_model using List.length_map

theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    (Raw.Const.toList m.1).isEmpty = m.1.isEmpty := by
  simp_to_model
  rw [Bool.eq_iff_iff, List.isEmpty_iff,List.isEmpty_iff, List.map_eq_nil_iff]

theorem mem_toList_iff_get?_eq_some [LawfulBEq α] (h : m.1.WF)
    {k : α} {v : β} :
    (k, v) ∈ Raw.Const.toList m.1 ↔ get? m k = some v := by
  simp_to_model using List.mem_map_toProd_iff_getValue?_eq_some

theorem get?_eq_some_iff_exists_beq_and_mem_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {k : α} {v : β} :
    get? m k = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ Raw.Const.toList m.1 := by
  simp_to_model using getValue?_eq_some_iff_exists_beq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
    [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k k' : α} {v : β} :
    (Raw.Const.toList m.1).find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ get? m k = some v := by
  simp_to_model using List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {k : α} :
    (Raw.Const.toList m.1).find? (·.1 == k) = none ↔ m.contains k = false := by
  simp_to_model using List.find?_map_eq_none_iff_containsKey_eq_false

theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {k: α} {v : β} :
    (k, v) ∈ (Raw.Const.toList m.1) ↔ m.getKey? k = some k ∧ get? m k = some v := by
  simp_to_model using List.mem_map_toProd_iff_getKey?_eq_some_and_getValue?_eq_some

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    (Raw.Const.toList m.1).Pairwise (fun a b => (a.1 == b.1) = false) := by
  simp_to_model using List.pairwise_fst_eq_false_map_toProd

end Const

section monadic

-- The types are redefined because fold/for does not need BEq/Hashable
variable {α : Type u} {β : α → Type v} (m : Raw₀ α β) {δ : Type w} {m' : Type w → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    m.1.foldM f init = m.1.toList.foldlM (fun a b => f a b.1 b.2) init := by
  simp_to_model

theorem fold_eq_foldl_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    m.1.fold f init = m.1.toList.foldl (fun a b => f a b.1 b.2) init := by
  simp_to_model

theorem foldRevM_eq_foldrM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    m.1.foldRevM f init = m.1.toList.foldrM (fun a b => f b a.1 a.2) init := by
  simp_to_model

theorem foldRev_eq_foldr_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    m.1.foldRev f init = m.1.toList.foldr (fun a b => f b a.1 a.2) init := by
  simp_to_model

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : (a : α) → β a → m' PUnit} :
    m.1.forM f = m.1.toList.forM (fun a => f a.1 a.2) := by
  simp_to_model

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ} :
    m.1.forIn f init = ForIn.forIn m.1.toList init (fun a b => f a.1 a.2 b) := by
  simp_to_model

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β))

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β → m' δ} {init : δ} :
    m.1.foldM f init = (Raw.Const.toList m.1).foldlM (fun a b => f a b.1 b.2) init := by
  simp_to_model using List.foldlM_eq_foldlM_toProd

theorem fold_eq_foldl_toList {f : δ → (a : α) → β → δ} {init : δ} :
    m.1.fold f init = (Raw.Const.toList m.1).foldl (fun a b => f a b.1 b.2) init := by
  simp_to_model using List.foldl_eq_foldl_toProd

theorem foldRevM_eq_foldrM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β → m' δ} {init : δ} :
    m.1.foldRevM f init = (Raw.Const.toList m.1).foldrM (fun a b => f b a.1 a.2) init := by
  simp_to_model using List.foldrM_eq_foldrM_toProd

theorem foldRev_eq_foldr_toList {f : δ → (a : α) → β → δ} {init : δ} :
    m.1.foldRev f init = (Raw.Const.toList m.1).foldr (fun a b => f b a.1 a.2) init := by
  simp_to_model using List.foldr_eq_foldr_toProd

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : (a : α) → β → m' PUnit} :
    m.1.forM f = (Raw.Const.toList m.1).forM (fun a => f a.1 a.2) := by
  simp_to_model using List.forM_eq_forM_toProd

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : (a : α) → β → δ → m' (ForInStep δ)} {init : δ} :
    m.1.forIn f init = ForIn.forIn (Raw.Const.toList m.1) init (fun a b => f a.1 a.2 b) := by
  simp_to_model using List.forIn_eq_forIn_toProd

variable (m : Raw₀ α (fun _ => Unit))

theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} :
    m.1.foldM (fun d a _ => f d a) init = m.1.keys.foldlM f init := by
  simp_to_model using List.foldlM_eq_foldlM_keys

theorem fold_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    m.1.fold (fun d a _ => f d a) init = m.1.keys.foldl f init := by
  simp_to_model using List.foldl_eq_foldl_keys

theorem foldRevM_eq_foldrM_keys [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → m' δ} {init : δ} :
    m.1.foldRevM (fun d a _ => f d a) init = m.1.keys.foldrM (fun a b => f b a) init := by
  simp_to_model using List.foldrM_eq_foldrM_keys

theorem foldRev_eq_foldr_keys {f : δ → (a : α) → δ} {init : δ} :
    m.1.foldRev (fun d a _ => f d a) init = m.1.keys.foldr (fun a b => f b a) init := by
  simp_to_model using List.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.1.forM (fun a _ => f a) = m.1.keys.forM f := by
  simp_to_model using List.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.1.forIn (fun a _ d => f a d) init = ForIn.forIn m.1.keys init f := by
  simp_to_model using List.forIn_eq_forIn_keys

end Const

end monadic

@[simp]
theorem insertMany_nil :
    m.insertMany [] = m := by
  simp [insertMany, Id.run]

@[simp]
theorem insertMany_list_singleton {k : α} {v : β k} :
    m.insertMany [⟨k, v⟩] = m.insert k v := by
  simp [insertMany, Id.run]

theorem insertMany_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (m.insertMany (⟨k, v⟩ :: l)).1 = ((m.insert k v).insertMany l).1 := by
  simp only [insertMany_eq_insertListₘ]
  cases l with
  | nil => simp [insertListₘ]
  | cons hd tl => simp [insertListₘ]

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).1.contains k = (m.contains k || (l.map Sigma.fst).contains k) := by
  simp_to_model [insertMany] using List.containsKey_insertList

theorem contains_of_contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).1.contains k → (l.map Sigma.fst).contains k = false → m.contains k := by
  simp_to_model [insertMany] using List.containsKey_of_containsKey_insertList

theorem get?_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.get? k = m.get? k := by
  simp_to_model [insertMany] using List.getValueCast?_insertList_of_contains_eq_false

theorem get?_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).1.get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  simp_to_model [insertMany] using List.getValueCast?_insertList_of_mem

theorem get_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (m.insertMany l).1.get k h' =
    m.get k (contains_of_contains_insertMany_list _ h h' contains) := by
  simp_to_model [insertMany] using List.getValueCast_insertList_of_contains_eq_false

theorem get_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (m.insertMany l).1.get k' h' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_model [insertMany] using List.getValueCast_insertList_of_mem

theorem get!_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.get! k = m.get! k := by
  simp_to_model [insertMany] using List.getValueCast!_insertList_of_contains_eq_false

theorem get!_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).1.get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_model [insertMany] using List.getValueCast!_insertList_of_mem

theorem getD_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getD k fallback = m.getD k fallback := by
  simp_to_model [insertMany] using List.getValueCastD_insertList_of_contains_eq_false

theorem getD_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).1.getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_model [insertMany] using List.getValueCastD_insertList_of_mem

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getKey? k = m.getKey? k := by
  simp_to_model [insertMany] using List.getKey?_insertList_of_contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).1.getKey? k' = some k := by
  simp_to_model [insertMany] using List.getKey?_insertList_of_mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h₁ : (l.map Sigma.fst).contains k = false)
    {h'} :
    (m.insertMany l).1.getKey k h' =
    m.getKey k (contains_of_contains_insertMany_list _ h h' h₁) := by
  simp_to_model [insertMany] using List.getKey_insertList_of_contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (m.insertMany l).1.getKey k' h' = k := by
  simp_to_model [insertMany] using List.getKey_insertList_of_mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.1.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getKey! k = m.getKey! k := by
  simp_to_model [insertMany] using List.getKey!_insertList_of_contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).1.getKey! k' = k := by
  simp_to_model [insertMany] using List.getKey!_insertList_of_mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k fallback : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_model [insertMany] using List.getKeyD_insertList_of_contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).1.getKeyD k' fallback = k := by
  simp_to_model [insertMany] using List.getKeyD_insertList_of_mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), m.contains a → (l.map Sigma.fst).contains a = false) →
    (m.insertMany l).1.1.size = m.1.size + l.length := by
  simp_to_model [insertMany] using List.length_insertList

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} :
    m.1.size ≤ (m.insertMany l).1.1.size := by
  simp_to_model [insertMany] using List.length_le_length_insertList

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} :
    (m.insertMany l).1.1.size ≤ m.1.size + l.length := by
  simp_to_model [insertMany] using List.length_insertList_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} :
    (m.insertMany l).1.1.isEmpty = (m.1.isEmpty && l.isEmpty) := by
  simp_to_model [insertMany] using List.isEmpty_insertList

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β))

@[simp]
theorem insertMany_nil :
    insertMany m [] = m := by
  simp [insertMany, Id.run]

@[simp]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany m [⟨k, v⟩] = m.insert k v := by
  simp [insertMany, Id.run]

theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    (insertMany m (⟨k, v⟩ :: l)).1 = (insertMany (m.insert k v) l).1 := by
  simp only [insertMany_eq_insertListₘ]
  cases l with
  | nil => simp [insertListₘ]
  | cons hd tl => simp [insertListₘ]

@[simp]
theorem contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α} :
    (Const.insertMany m l).1.contains k = (m.contains k || (l.map Prod.fst).contains k) := by
  simp_to_model [Const.insertMany] using List.containsKey_insertListConst

theorem contains_of_contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ( α × β )} {k : α} :
    (insertMany m l).1.contains k → (l.map Prod.fst).contains k = false → m.contains k := by
  simp_to_model [Const.insertMany] using List.containsKey_of_containsKey_insertListConst

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany m l).1.getKey? k = m.getKey? k := by
  simp_to_model [Const.insertMany] using List.getKey?_insertListConst_of_contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List  (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).1.getKey? k' = some k := by
  simp_to_model [Const.insertMany] using List.getKey?_insertListConst_of_mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany m l).1.getKey k h' =
    m.getKey k (contains_of_contains_insertMany_list _ h h' h₁) := by
  simp_to_model [Const.insertMany] using List.getKey_insertListConst_of_contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany m l).1.getKey k' h' = k := by
  simp_to_model [Const.insertMany] using List.getKey_insertListConst_of_mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.1.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany m l).1.getKey! k = m.getKey! k := by
  simp_to_model [Const.insertMany] using List.getKey!_insertListConst_of_contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).1.getKey! k' = k := by
  simp_to_model [Const.insertMany] using List.getKey!_insertListConst_of_mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k fallback : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany m l).1.getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_model [Const.insertMany] using List.getKeyD_insertListConst_of_contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).1.getKeyD k' fallback = k := by
  simp_to_model [Const.insertMany] using List.getKeyD_insertListConst_of_mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), m.contains a → (l.map Prod.fst).contains a = false) →
    (insertMany m l).1.1.size = m.1.size + l.length := by
  simp_to_model [Const.insertMany] using List.length_insertListConst

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} :
    m.1.size ≤ (insertMany m l).1.1.size := by
  simp_to_model [Const.insertMany] using List.length_le_length_insertListConst

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} :
    (insertMany m l).1.1.size ≤ m.1.size + l.length := by
  simp_to_model [Const.insertMany] using List.length_insertListConst_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} :
    (insertMany m l).1.1.isEmpty = (m.1.isEmpty && l.isEmpty) := by
  simp_to_model [Const.insertMany] using List.isEmpty_insertListConst

theorem get?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l).1 k = get? m k := by
  simp_to_model [Const.insertMany] using List.getValue?_insertListConst_of_contains_eq_false

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l).1 k' = v := by
  simp_to_model [Const.insertMany] using List.getValue?_insertListConst_of_mem

theorem get_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany m l).1 k h' = get m k (contains_of_contains_insertMany_list _ h h' h₁) := by
  simp_to_model [Const.insertMany] using List.getValue_insertListConst_of_contains_eq_false

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    get (insertMany m l).1 k' h' = v := by
  simp_to_model [Const.insertMany] using List.getValue_insertListConst_of_mem

theorem get!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β]  (h : m.1.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get! (insertMany m l).1 k = get! m k := by
  simp_to_model [Const.insertMany] using List.getValue!_insertListConst_of_contains_eq_false

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany m l).1 k' = v := by
  simp_to_model [Const.insertMany] using List.getValue!_insertListConst_of_mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α} {fallback : β}
    (h' : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l).1 k fallback = getD m k fallback := by
  simp_to_model [Const.insertMany] using List.getValueD_insertListConst_of_contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l).1 k' fallback = v := by
  simp_to_model [Const.insertMany] using List.getValueD_insertListConst_of_mem

variable (m : Raw₀ α (fun _ => Unit))

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit m [] = m := by
  simp [insertManyIfNewUnit, Id.run]

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit m [k] = m.insertIfNew k () := by
  simp [insertManyIfNewUnit, Id.run]

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    (insertManyIfNewUnit m (k :: l)).1 = (insertManyIfNewUnit (m.insertIfNew k ()) l).1 := by
  simp only [insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  cases l with
  | nil => simp [insertListIfNewUnitₘ]
  | cons hd tl => simp [insertListIfNewUnitₘ]

@[simp]
theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit m l).1.contains k = (m.contains k || l.contains k) := by
  simp_to_model [Const.insertManyIfNewUnit] using List.containsKey_insertListIfNewUnit

theorem contains_of_contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} {k : α} (h₂ : l.contains k = false) :
    (insertManyIfNewUnit m l).1.contains k → m.contains k := by
  simp_to_model [Const.insertManyIfNewUnit] using List.containsKey_of_containsKey_insertListIfNewUnit

theorem getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} :
    m.contains k = false → l.contains k = false → getKey? (insertManyIfNewUnit m l).1 k = none := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k k' : α} (k_beq : k == k') :
    m.contains k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey? (insertManyIfNewUnit m l).1 k' = some k := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey?_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} :
    m.contains k → getKey? (insertManyIfNewUnit m l).1 k = getKey? m k := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey?_insertListIfNewUnit_of_contains

theorem getKey_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} {h'} (contains : m.contains k) :
    getKey (insertManyIfNewUnit m l).1 k h' = getKey m k contains := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey_insertListIfNewUnit_of_contains

theorem getKey_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α}
    {k k' : α} (k_beq : k == k') {h'} :
    m.contains k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey (insertManyIfNewUnit m l).1 k' h' = k := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey_insertManyIfNewUnit_list_mem_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} (contains : m.contains k) {h'} :
    getKey (insertManyIfNewUnit m l).1 k h' = getKey m k contains := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey_insertListIfNewUnit_of_contains

theorem getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {l : List α} {k : α} :
    m.contains k = false → l.contains k = false →
      getKey! (insertManyIfNewUnit m l).1 k = default := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.1.WF) {l : List α} {k k' : α} (k_beq : k == k') :
    contains m k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey! (insertManyIfNewUnit m l).1 k' = k := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey!_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.1.WF) {l : List α} {k : α} :
    m.contains k → getKey! (insertManyIfNewUnit m l).1 k = getKey! m k  := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKey!_insertListIfNewUnit_of_contains

theorem getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {l : List α} {k fallback : α} :
    m.contains k = false → l.contains k = false → getKeyD (insertManyIfNewUnit m l).1 k fallback = fallback := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k k' fallback : α} (k_beq : k == k') :
    m.contains k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKeyD (insertManyIfNewUnit m l).1 k' fallback = k := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKeyD_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k fallback : α} :
    m.contains k → getKeyD (insertManyIfNewUnit m l).1 k fallback = getKeyD m k fallback := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getKeyD_insertListIfNewUnit_of_contains

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), m.contains a → l.contains a = false) →
    (insertManyIfNewUnit m l).1.1.size = m.1.size + l.length := by
  simp_to_model [Const.insertManyIfNewUnit] using List.length_insertListIfNewUnit

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} :
    m.1.size ≤ (insertManyIfNewUnit m l).1.1.size := by
  simp_to_model [Const.insertManyIfNewUnit] using List.length_le_length_insertListIfNewUnit

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).1.1.size ≤ m.1.size + l.length := by
  simp_to_model [Const.insertManyIfNewUnit] using List.length_insertListIfNewUnit_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).1.1.isEmpty = (m.1.isEmpty && l.isEmpty) := by
  simp_to_model [Const.insertManyIfNewUnit] using List.isEmpty_insertListIfNewUnit

theorem get?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit m l).1 k =
    if m.contains k ∨ l.contains k then some () else none := by
  simp_to_model [Const.insertManyIfNewUnit] using List.getValue?_insertListIfNewUnit

theorem get_insertManyIfNewUnit_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit m l).1 k h = ()  := by
  simp

theorem get!_insertManyIfNewUnit_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit m l).1 k = ()  := by
  simp

theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit m l).1 k fallback = () := by
  simp

end Const

@[simp]
theorem insertMany_empty_list_nil :
    (insertMany empty ([] : List ((a : α) × (β a)))).1 = empty := by
  simp

@[simp]
theorem insertMany_empty_list_singleton {k : α} {v : β k} :
    (insertMany empty [⟨k, v⟩]).1 = empty.insert k v := by
  simp

theorem insertMany_empty_list_cons {k : α} {v : β k}
    {tl : List ((a : α) × (β a))} :
    (insertMany empty (⟨k, v⟩ :: tl)).1 = ((empty.insert k v).insertMany tl).1 := by
  rw [insertMany_cons]

theorem contains_insertMany_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (insertMany empty l).1.contains k = (l.map Sigma.fst).contains k := by
  simp [contains_insertMany_list _ Raw.WF.empty₀]

theorem get?_insertMany_empty_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l).1.get? k = none := by
  simp [get?_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]

theorem get?_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany empty l).1.get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  rw [get?_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem get_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (insertMany empty l).1.get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  rw [get_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem get!_insertMany_empty_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l).1.get! k = default := by
  simp only [get!_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply get!_empty

theorem get!_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany empty l).1.get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  rw [get!_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getD_insertMany_empty_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l).1.getD k fallback = fallback := by
  rw [getD_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ contains_eq_false]
  apply getD_empty

theorem getD_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany empty l).1.getD k' fallback =
      cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  rw [getD_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKey?_insertMany_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l).1.getKey? k = none := by
  rw [getKey?_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply getKey?_empty

theorem getKey?_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany empty l).1.getKey? k' = some k := by
  rw [getKey?_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKey_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (insertMany empty l).1.getKey k' h' = k := by
  rw [getKey_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKey!_insertMany_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l).1.getKey! k = default := by
  rw [getKey!_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply getKey!_empty

theorem getKey!_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany empty l).1.getKey! k' = k := by
  rw [getKey!_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKeyD_insertMany_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany empty l).1.getKeyD k fallback = fallback := by
  rw [getKeyD_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply getKeyD_empty

theorem getKeyD_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany empty l).1.getKeyD k' fallback = k := by
  rw [getKeyD_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem size_insertMany_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (insertMany empty l).1.1.size = l.length := by
  rw [size_insertMany_list _ Raw.WF.empty₀ distinct]
  · simp only [size_empty, Nat.zero_add]
  · simp only [contains_empty, Bool.false_eq_true, false_implies, implies_true]

theorem size_insertMany_empty_list_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (insertMany empty l).1.1.size ≤ l.length := by
  rw [← Nat.zero_add l.length]
  apply (size_insertMany_list_le _ Raw.WF.empty₀)

theorem isEmpty_insertMany_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (insertMany empty l).1.1.isEmpty = l.isEmpty := by
  simp [isEmpty_insertMany_list _ Raw.WF.empty₀]

namespace Const
variable {β : Type v}

@[simp]
theorem insertMany_empty_list_nil :
    (insertMany empty ([] : List (α × β))).1 = empty := by
  simp only [insertMany_nil]

@[simp]
theorem insertMany_empty_list_singleton {k : α} {v : β} :
    (insertMany empty [⟨k, v⟩]).1 = empty.insert k v := by
  simp only [insertMany_list_singleton]

theorem insertMany_empty_list_cons {k : α} {v : β}
    {tl : List (α × β)} :
    (insertMany empty (⟨k, v⟩ :: tl)) = (insertMany (empty.insert k v) tl).1 := by
  rw [insertMany_cons]

theorem contains_insertMany_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.contains k = (l.map Prod.fst).contains k := by
  simp [contains_insertMany_list _ Raw.WF.empty₀]

theorem get?_insertMany_empty_list_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    get? (insertMany (empty : Raw₀ α (fun _ => β)) l).1 k = none := by
  rw [get?_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply get?_empty

theorem get?_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany (empty : Raw₀ α (fun _ => β)) l) k' = some v := by
  rw [get?_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem get_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (insertMany (empty : Raw₀ α (fun _ => β)) l) k' h = v := by
  rw [get_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem get!_insertMany_empty_list_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (h : (l.map Prod.fst).contains k = false) :
    get! (insertMany (empty : Raw₀ α (fun _ => β)) l) k = (default : β) := by
  rw [get!_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply get!_empty

theorem get!_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany (empty : Raw₀ α (fun _ => β)) l) k' = v := by
  rw [get!_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getD_insertMany_empty_list_of_contains_eq_false [LawfulBEq α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany (empty : Raw₀ α (fun _ => β)) l) k fallback = fallback := by
  rw [getD_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ contains_eq_false]
  apply getD_empty

theorem getD_insertMany_empty_list_of_mem [LawfulBEq α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany (empty : Raw₀ α (fun _ => β)) l) k' fallback = v := by
  rw [getD_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKey?_insertMany_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKey? k = none := by
  rw [getKey?_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply getKey?_empty

theorem getKey?_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKey? k' = some k := by
  rw [getKey?_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKey_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKey k' h' = k := by
  rw [getKey_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKey!_insertMany_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKey! k = default := by
  rw [getKey!_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply getKey!_empty

theorem getKey!_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKey! k' = k := by
  rw [getKey!_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem getKeyD_insertMany_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKeyD k fallback = fallback := by
  rw [getKeyD_insertMany_list_of_contains_eq_false _ Raw.WF.empty₀ h]
  apply getKeyD_empty

theorem getKeyD_insertMany_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.getKeyD k' fallback = k := by
  rw [getKeyD_insertMany_list_of_mem _ Raw.WF.empty₀ k_beq distinct mem]

theorem size_insertMany_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.1.size = l.length := by
  rw [size_insertMany_list _ Raw.WF.empty₀ distinct]
  · simp only [size_empty, Nat.zero_add]
  · simp only [contains_empty, Bool.false_eq_true, false_implies, implies_true]

theorem size_insertMany_empty_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.1.size ≤ l.length := by
  rw [← Nat.zero_add l.length]
  apply (size_insertMany_list_le _ Raw.WF.empty₀)

theorem isEmpty_insertMany_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany (empty : Raw₀ α (fun _ => β)) l).1.1.isEmpty = l.isEmpty := by
  simp [isEmpty_insertMany_list _ Raw.WF.empty₀]

@[simp]
theorem insertManyIfNewUnit_empty_list_nil :
    insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) ([] : List α) =
      (empty : Raw₀ α (fun _ => Unit)) := by
  simp

@[simp]
theorem insertManyIfNewUnit_empty_list_singleton {k : α} :
    (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) [k]).1 = empty.insertIfNew k () := by
  simp

theorem insertManyIfNewUnit_empty_list_cons {hd : α} {tl : List α} :
    insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) (hd :: tl) =
      (insertManyIfNewUnit (empty.insertIfNew hd ()) tl).1 := by
  rw [insertManyIfNewUnit_cons]

theorem contains_insertManyIfNewUnit_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1.contains k = l.contains k := by
  simp [contains_insertManyIfNewUnit_list _ Raw.WF.empty₀]

theorem getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (h' : l.contains k = false) :
    getKey? (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k = none := by
  exact getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false _ Raw.WF.empty₀
    contains_empty h'

theorem getKey?_insertManyIfNewUnit_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k' = some k := by
  exact getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.empty₀ k_beq
    contains_empty distinct mem

theorem getKey_insertManyIfNewUnit_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h'} :
    getKey (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k' h' = k := by
  exact getKey_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.empty₀ k_beq
    contains_empty distinct mem

theorem getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (h' : l.contains k = false) :
    getKey! (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k = default := by
  exact getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false _ Raw.WF.empty₀
    contains_empty h'

theorem getKey!_insertManyIfNewUnit_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k' = k := by
  exact getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.empty₀ k_beq
    contains_empty distinct mem

theorem getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (h' : l.contains k = false) :
    getKeyD (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k fallback = fallback := by
  exact getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    _ Raw.WF.empty₀ contains_empty h'

theorem getKeyD_insertManyIfNewUnit_empty_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1 k' fallback = k := by
  exact getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.empty₀ k_beq
    contains_empty distinct mem

theorem size_insertManyIfNewUnit_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1.1.size = l.length := by
  simp [size_insertManyIfNewUnit_list _ Raw.WF.empty₀ distinct]

theorem size_insertManyIfNewUnit_empty_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1.1.size ≤ l.length := by
  apply Nat.le_trans (size_insertManyIfNewUnit_list_le _ Raw.WF.empty₀)
  simp

theorem isEmpty_insertManyIfNewUnit_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l).1.1.isEmpty = l.isEmpty := by
  rw [isEmpty_insertManyIfNewUnit_list _ Raw.WF.empty₀]
  simp

theorem get?_insertManyIfNewUnit_empty_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l) k =
      if l.contains k then some () else none := by
  rw [get?_insertManyIfNewUnit_list _ Raw.WF.empty₀]
  simp

theorem get_insertManyIfNewUnit_empty_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l) k h = ()  := by
  simp

theorem get!_insertManyIfNewUnit_empty_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l) k = ()  := by
  simp

theorem getD_insertManyIfNewUnit_empty_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit (empty : Raw₀ α (fun _ => Unit)) l) k fallback = () := by
  simp

end Const

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [LawfulBEq α] (h : m.1.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (m.get? k)).isNone) := by
  simp_to_model [alter, erase] using List.isEmpty_alterKey_eq_isEmpty_eraseKey

@[simp]
theorem isEmpty_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = (((m.1.isEmpty || (m.1.size == 1 && m.contains k))) &&
      (f (m.get? k)).isNone) := by
  simp_to_model [alter] using List.isEmpty_alterKey

theorem contains_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' := by
  simp_to_model [alter] using List.containsKey_alterKey

theorem size_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.size =
      if m.contains k && (f (m.get? k)).isNone then
        m.1.size - 1
      else if !m.contains k && (f (m.get? k)).isSome then
        m.1.size + 1
      else
        m.1.size := by
  simp_to_model [alter] using List.length_alterKey'

theorem size_alter_eq_add_one [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    (h₁ : m.contains k = false) (h₂ : (f (m.get? k)).isSome) :
    (m.alter k f).1.size = m.1.size + 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_sub_one [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    (h₁ : m.contains k) (h₂ : (f (m.get? k)).isNone) :
    (m.alter k f).1.size = m.1.size - 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self_of_not_mem [LawfulBEq α] (h : m.1.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : m.contains k = false) (h₂ : (f (m.get? k)).isNone) :
    (m.alter k f).1.size = m.1.size := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self_of_mem [LawfulBEq α] (h : m.1.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : m.contains k) (h₂ : (f (m.get? k)).isSome) :
    (m.alter k f).1.size = m.1.size := by
  simp [size_alter, h, h₁, Option.isSome_iff_ne_none.mp h₂]

theorem size_alter_le_size [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.size ≤ m.1.size + 1 := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_le_size_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    m.1.size - 1 ≤ (m.alter k f).1.size := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem get?_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).get? k' =
      if h : k == k' then
        cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (m.get? k))
      else
        m.get? k' := by
  simp_to_model [alter] using List.getValueCast?_alterKey

theorem get_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)}
    (hc : (m.alter k f).contains k') :
    (m.alter k f).get k' hc =
      if heq : k == k' then
        haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, if_pos heq] at hc
        cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get <| h'
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        m.get k' h' := by
  simp_to_model [alter] using List.getValueCast_alterKey

theorem get_alter_self [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    {hc : (m.alter k f).contains k} :
    haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, beq_self_eq_true] at hc
    (m.alter k f).get k hc = (f (m.get? k)).get h' := by
  simp_to_model [alter] using List.getValueCast_alterKey_self

theorem get!_alter [LawfulBEq α] {k k' : α} (h : m.1.WF) [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).get! k' =
      if heq : k == k' then
        (f (m.get? k)).map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' := by
  simp_to_model [alter] using List.getValueCast!_alterKey

theorem getD_alter [LawfulBEq α] {k k' : α} {fallback : β k'} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k' fallback =
      if heq : k == k' then
        f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback := by
  simp_to_model [alter] using List.getValueCastD_alterKey

private theorem cast_eq_id {α : Type u} : cast (rfl : α = α) = id := by rfl

theorem getD_alter_self [LawfulBEq α] {k : α} {fallback : β k} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k fallback = (f (m.get? k)).getD fallback := by
  simp only [getD_alter, h, beq_self_eq_true, reduceDIte, cast_eq_id, Option.map_id_fun, id_eq]

theorem getKey?_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k' =
      if k == k' then
        if (f (m.get? k)).isSome then some k else none
      else
        m.getKey? k' := by
  simp_to_model [alter] using List.getKey?_alterKey

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} : (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' := by
  simp_to_model [alter] using List.getKey!_alterKey

theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} (hc : (m.alter k f).contains k') :
    (m.alter k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        m.getKey k' h' := by
  simp_to_model [alter] using List.getKey_alterKey

theorem getKeyD_alter [LawfulBEq α] {k k' fallback : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k' fallback =
      if k == k' then
        if (f (m.get? k)).isSome then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [alter] using List.getKeyD_alterKey

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => β))

theorem isEmpty_alter_eq_isEmpty_erase (h : m.1.WF)  {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (Const.get? m k)).isNone) := by
  simp_to_model [Const.alter, erase] using List.Const.isEmpty_alterKey_eq_isEmpty_eraseKey

@[simp]
theorem isEmpty_alter (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty = ((m.1.isEmpty || (m.1.size == 1 && m.contains k)) &&
      (f (Const.get? m k)).isNone) := by
  simp_to_model [Const.alter] using List.Const.isEmpty_alterKey

theorem contains_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
      if k == k' then
        (f (Const.get? m k)).isSome
      else
        m.contains k' := by
  simp_to_model [Const.alter] using List.Const.containsKey_alterKey

theorem size_alter (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.size =
      if m.contains k && (f (Const.get? m k)).isNone then
        m.1.size - 1
      else if !m.contains k && (f (Const.get? m k)).isSome then
        m.1.size + 1
      else
        m.1.size := by
  simp_to_model [Const.alter] using List.Const.length_alterKey'

theorem size_alter_eq_add_one (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k = false) (h₂ : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).1.size = m.1.size + 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_sub_one (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k) (h₂ : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).1.size = m.1.size - 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self_of_not_mem (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k = false) (h₂ : (f (Const.get? m k)).isNone) :
    (Const.alter m k f).1.size = m.1.size := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self_of_mem (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k) (h₂ : (f (Const.get? m k)).isSome) :
    (Const.alter m k f).1.size = m.1.size := by
  simp [size_alter, h, h₁, Option.isSome_iff_ne_none.mp h₂]

theorem size_alter_le_size [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.size ≤ m.1.size + 1 := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_le_size_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option β → Option β} :
    m.1.size - 1 ≤ (Const.alter m k f).1.size := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem get?_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    Const.get? (Const.alter m k f) k' =
      if k == k' then
        f (Const.get? m k)
      else
        Const.get? m k' := by
  simp_to_model [Const.alter] using List.Const.getValue?_alterKey

theorem get_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β}
    (hc : (Const.alter m k f).contains k') :
    Const.get (Const.alter m k f) k' hc =
      if heq : k == k' then
        haveI h' : (f (Const.get? m k)).isSome := by rwa [contains_alter _ h, if_pos heq] at hc
        (f (Const.get? m k)).get <| h'
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        Const.get m k' h' := by
  simp_to_model [Const.alter] using List.Const.getValue_alterKey

theorem get_alter_self (h : m.1.WF) {k : α} {f : Option β → Option β}
    {hc : (Const.alter m k f).contains k} :
    haveI h' : (f (Const.get? m k)).isSome := by rwa [contains_alter _ h, BEq.refl] at hc
    Const.get (Const.alter m k f) k hc = (f (Const.get? m k)).get h' := by
  simp_to_model [Const.alter] using List.Const.getValue_alterKey_self

theorem get!_alter {k k' : α} (h : m.1.WF) [Inhabited β] {f : Option β → Option β} :
    Const.get! (Const.alter m k f) k' =
      if k == k' then
        (f (Const.get? m k)).get!
      else
        Const.get! m k' := by
  simp_to_model [Const.alter] using List.Const.getValue!_alterKey

theorem getD_alter {k k' : α} {fallback : β} (h : m.1.WF) {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k' fallback =
      if k == k' then
        f (Const.get? m k) |>.getD fallback
      else
        Const.getD m k' fallback := by
  simp_to_model [Const.alter] using List.Const.getValueD_alterKey

theorem getD_alter_self {k : α} {fallback : β} (h : m.1.WF) {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k fallback = (f (Const.get? m k)).getD fallback := by
  simp only [h, getD_alter, BEq.refl, reduceIte]

theorem getKey?_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then some k else none
      else
        m.getKey? k' := by
  simp_to_model [Const.alter] using List.Const.getKey?_alterKey

theorem getKey!_alter [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option β → Option β} :
    (Const.alter m k f).getKey! k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else default
      else
        m.getKey! k' := by
  simp_to_model [Const.alter] using List.Const.getKey!_alterKey

theorem getKey_alter [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option β → Option β}
    (hc : (Const.alter m k f).contains k') :
    (Const.alter m k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        m.getKey k' h' := by
  simp_to_model [Const.alter] using List.Const.getKey_alterKey

theorem getKeyD_alter {k k' fallback : α} (h : m.1.WF) {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [Const.alter] using List.Const.getKeyD_alterKey

end Const

end Alter

section Modify

variable [LawfulBEq α]

@[simp]
theorem isEmpty_modify (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model [modify] using List.isEmpty_modifyKey

theorem contains_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' := by
  simp_to_model [modify] using List.containsKey_modifyKey

theorem size_modify (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).1.size = m.1.size := by
  simp_to_model [modify] using List.length_modifyKey

theorem get?_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).get? k' =
      if h : k == k' then
        (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f))
      else
        m.get? k' := by
  simp_to_model [modify] using List.getValueCast?_modifyKey

@[simp]
theorem get?_modify_self (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).get? k = (m.get? k).map f := by
  simp_to_model [modify] using List.getValueCast?_modifyKey_self

theorem get_modify (h : m.1.WF) {k k' : α} {f : β k → β k}
    (hc : (m.modify k f).contains k') :
    (m.modify k f).get k' hc =
      if heq : k == k' then
        haveI h' : m.contains k := by rwa [contains_modify _ h, ← eq_of_beq heq] at hc
        cast (congrArg β (eq_of_beq heq)) <| f (m.get k h')
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        m.get k' h' := by
  simp_to_model [modify] using List.getValueCast_modifyKey

@[simp]
theorem get_modify_self (h : m.1.WF) {k : α} {f : β k → β k} {hc : (m.modify k f).contains k} :
    haveI h' : m.contains k := by rwa [contains_modify _ h] at hc
    (m.modify k f).get k hc = f (m.get k h') := by
  simp_to_model [modify] using List.getValueCast_modifyKey_self

theorem get!_modify (h : m.1.WF) {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (m.modify k f).get! k' =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' := by
  simp_to_model [modify] using List.getValueCast!_modifyKey

@[simp]
theorem get!_modify_self (h : m.1.WF) {k : α} [Inhabited (β k)] {f : β k → β k} :
    (m.modify k f).get! k = ((m.get? k).map f).get! := by
  simp_to_model [modify] using List.getValueCast!_modifyKey_self

theorem getD_modify (h : m.1.WF) {k k' : α} {fallback : β k'} {f : β k → β k} :
    (m.modify k f).getD k' fallback =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback := by
  simp_to_model [modify] using List.getValueCastD_modifyKey

@[simp]
theorem getD_modify_self (h : m.1.WF) {k : α} {fallback : β k} {f : β k → β k} :
    (m.modify k f).getD k fallback = ((m.get? k).map f).getD fallback := by
  simp_to_model [modify] using List.getValueCastD_modifyKey_self

theorem getKey?_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey? k' =
      if k == k' then
        if m.contains k then some k else none
      else
        m.getKey? k' := by
  simp_to_model [modify] using List.getKey?_modifyKey

theorem getKey?_modify_self (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).getKey? k = if m.contains k then some k else none := by
  simp_to_model [modify] using List.getKey?_modifyKey_self

theorem getKey!_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey! k' =
      if k == k' then
        if m.contains k then k else default
      else
        m.getKey! k' := by
  simp_to_model [modify] using List.getKey!_modifyKey

theorem getKey!_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey! k = if m.contains k then k else default := by
  simp_to_model [modify] using List.getKey!_modifyKey_self

theorem getKey_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β k → β k}
    (hc : (m.modify k f).contains k') :
    (m.modify k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        m.getKey k' h' := by
  simp_to_model [modify] using List.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β k → β k}
    (hc : (m.modify k f).contains k) : (m.modify k f).getKey k hc = k := by
  simp_to_model [modify] using List.getKey_modifyKey_self

theorem getKeyD_modify (h : m.1.WF) {k k' fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k' fallback =
      if k == k' then
        if m.contains k then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [modify] using List.getKeyD_modifyKey

theorem getKeyD_modify_self (h : m.1.WF) [Inhabited α] {k fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k fallback = if m.contains k then k else fallback := by
  simp_to_model [modify] using List.getKeyD_modifyKey_self

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => β))
omit [LawfulBEq α]

@[simp]
theorem isEmpty_modify (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model [Const.modify] using List.Const.isEmpty_modifyKey

theorem contains_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' := by
  simp_to_model [Const.modify] using List.Const.containsKey_modifyKey

theorem size_modify (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.size = m.1.size := by
  simp_to_model [Const.modify] using List.Const.length_modifyKey

theorem get?_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    Const.get? (Const.modify m k f) k' =
      if k == k' then
        (Const.get? m k).map f
      else
        Const.get? m k' := by
  simp_to_model [Const.modify] using List.Const.getValue?_modifyKey

@[simp]
theorem get?_modify_self (h : m.1.WF) {k : α} {f : β → β} :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f := by
  simp_to_model [Const.modify] using List.Const.getValue?_modifyKey_self

theorem get_modify (h : m.1.WF) {k k' : α} {f : β → β}
    (hc : (Const.modify m k f).contains k') :
    Const.get (Const.modify m k f) k' hc =
      if heq : k == k' then
        haveI h' : m.contains k := by rwa [contains_modify _ h, ← contains_congr _ h heq] at hc
        f (Const.get m k h')
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        Const.get m k' h' := by
  simp_to_model [Const.modify] using List.Const.getValue_modifyKey

@[simp]
theorem get_modify_self (h : m.1.WF) {k : α} {f : β → β} {hc : (Const.modify m k f).contains k} :
    haveI h' : m.contains k := by rwa [contains_modify _ h] at hc
    Const.get (Const.modify m k f) k hc = f (Const.get m k h') := by
  simp_to_model [Const.modify] using List.Const.getValue_modifyKey_self

theorem get!_modify (h : m.1.WF) {k k' : α} [hi : Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f |>.get!
      else
        Const.get! m k' := by
  simp_to_model [Const.modify] using List.Const.getValue!_modifyKey

@[simp]
theorem get!_modify_self (h : m.1.WF) {k : α} [Inhabited (β)] {f : β → β} :
    Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! := by
  simp_to_model [Const.modify] using List.Const.getValue!_modifyKey_self

theorem getD_modify (h : m.1.WF) {k k' : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k' fallback =
      if k == k' then
        Const.get? m k |>.map f |>.getD fallback
      else
        Const.getD m k' fallback := by
  simp_to_model [Const.modify] using List.Const.getValueD_modifyKey

@[simp]
theorem getD_modify_self (h : m.1.WF) {k : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k fallback = ((Const.get? m k).map f).getD fallback := by
  simp_to_model [Const.modify] using List.Const.getValueD_modifyKey_self

theorem getKey?_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey? k' =
      if k == k' then
        if m.contains k then some k else none
      else
        m.getKey? k' := by
  simp_to_model [Const.modify] using List.Const.getKey?_modifyKey

theorem getKey?_modify_self (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).getKey? k = if m.contains k then some k else none := by
  simp_to_model [Const.modify] using List.Const.getKey?_modifyKey_self

theorem getKey!_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey! k' =
      if k == k' then
        if m.contains k then k else default
      else
        m.getKey! k' := by
  simp_to_model [Const.modify] using List.Const.getKey!_modifyKey

theorem getKey!_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey! k = if m.contains k then k else default := by
  simp_to_model [Const.modify] using List.Const.getKey!_modifyKey_self

theorem getKey_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β → β}
    (hc : (Const.modify m k f).contains k') :
    (Const.modify m k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        m.getKey k' h' := by
  simp_to_model [Const.modify] using List.Const.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β → β}
    (hc : (Const.modify m k f).contains k) : (Const.modify m k f).getKey k hc = k := by
  simp_to_model [Const.modify] using List.Const.getKey_modifyKey_self

theorem getKeyD_modify (h : m.1.WF) {k k' fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k' fallback =
      if k == k' then
        if m.contains k then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [Const.modify] using List.Const.getKeyD_modifyKey

theorem getKeyD_modify_self (h : m.1.WF) [Inhabited α] {k fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k fallback = if m.contains k then k else fallback := by
  simp_to_model [Const.modify] using List.Const.getKeyD_modifyKey_self

end Const

end Modify

end Raw₀

end Std.DHashMap.Internal
