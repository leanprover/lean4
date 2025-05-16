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

universe u v w w'

variable {α : Type u} {β : α → Type v}

namespace Std.DHashMap.Internal

section empty

@[simp]
theorem Raw₀.buckets_emptyWithCapacity {c} {i : Nat} {h} :
    (emptyWithCapacity c : Raw₀ α β).1.buckets[i]'h = AssocList.nil := by
  simp [emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated Raw₀.buckets_emptyWithCapacity (since := "2025-03-12")]
abbrev Raw₀.buckets_empty := @Raw₀.buckets_emptyWithCapacity

@[simp]
theorem Raw.buckets_emptyWithCapacity {c} {i : Nat} {h} :
    (Raw.emptyWithCapacity c : Raw α β).buckets[i]'h = AssocList.nil := by
  simp [Raw.emptyWithCapacity]

@[simp]
theorem Raw.buckets_empty {i : Nat} {h} :
    (∅ : Raw α β).buckets[i]'h = AssocList.nil :=
  buckets_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated Raw.buckets_empty (since := "2025-03-12")]
abbrev Raw.buckets_emptyc := @Raw.buckets_empty

variable [BEq α] [Hashable α]

@[simp]
theorem buckets_emptyWithCapacity {c} {i : Nat} {h} :
    (emptyWithCapacity c : DHashMap α β).1.buckets[i]'h = AssocList.nil := by
  simp [emptyWithCapacity]

@[simp]
theorem buckets_empty {i : Nat} {h} :
    (∅ : DHashMap α β).1.buckets[i]'h = AssocList.nil :=
  buckets_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated buckets_empty (since := "2025-03-12")]
abbrev buckets_emptyc := @buckets_empty

end empty

namespace Raw₀

variable (m : Raw₀ α β)

@[simp]
theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : Raw₀ α β).1.size = 0 := rfl

set_option linter.missingDocs false in
@[deprecated size_emptyWithCapacity (since := "2025-03-12")]
abbrev size_empty := @size_emptyWithCapacity

theorem isEmpty_eq_size_eq_zero : m.1.isEmpty = (m.1.size == 0) := by
  simp [Raw.isEmpty]

variable [BEq α] [Hashable α]

/-- Internal implementation detail of the hash map -/
scoped syntax "wf_trivial" : tactic

macro_rules
| `(tactic| wf_trivial) => `(tactic|
    (first
      | assumption | apply Raw.WFImp.distinct
      | apply Raw.WF.out
      | apply Raw.WF.insert₀ | apply Raw.WF.insertIfNew₀ | apply Raw.WF.erase₀
      | apply Raw.WF.alter₀ | apply Raw.WF.modify₀
      | apply Raw.WF.constAlter₀ | apply Raw.WF.constModify₀
      | apply Raw₀.wf_insertMany₀ | apply Raw₀.Const.wf_insertMany₀
      | apply Raw₀.Const.wf_insertManyIfNewUnit₀
      | apply Raw.WF.filter₀ | apply Raw₀.wf_map₀ | apply Raw₀.wf_filterMap₀
      | apply Raw.WF.emptyWithCapacity₀) <;> wf_trivial)

/-- Internal implementation detail of the hash map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

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
     ⟨`Const.modify, ``Const.toListModel_modify⟩,
     ⟨`filter, ``toListModel_filter⟩,
     ⟨`map, ``toListModel_map⟩,
     ⟨`filterMap, ``toListModel_filterMap⟩]

private theorem perm_map_congr_left {α : Type u} {β : Type v} {l l' : List α} {f : α → β}
    {l₂ : List β} (h : l.Perm l') : (l.map f).Perm l₂ ↔ (l'.map f).Perm l₂ :=
  (h.map f).congr_left _

private theorem perm_keys_congr_left {α : Type u} {β : α → Type v} {l l' : List ((a : α) × β a)}
    {l₂ : List α} (h : l.Perm l') : (List.keys l).Perm l₂ ↔ (List.keys l').Perm l₂ := by
  simp [List.keys_eq_map, perm_map_congr_left h]

private def queryMap : Std.DHashMap Name (fun _ => Name × Array (MacroM (TSyntax `term))) :=
  .ofList
    [⟨`isEmpty, (``Raw.isEmpty_eq_isEmpty, #[`(_root_.List.Perm.isEmpty_eq)])⟩,
     ⟨`contains, (``contains_eq_containsKey, #[`(containsKey_of_perm)])⟩,
     ⟨`size, (``Raw.size_eq_length, #[`(_root_.List.Perm.length_eq)])⟩,
     ⟨`get?, (``get?_eq_getValueCast?, #[`(getValueCast?_of_perm _)])⟩,
     ⟨`Const.get?, (``Const.get?_eq_getValue?, #[`(getValue?_of_perm _)])⟩,
     ⟨`Const.get, (``Const.get_eq_getValue, #[`(getValue_of_perm _)])⟩,
     ⟨`get, (``get_eq_getValueCast, #[`(getValueCast_of_perm _)])⟩,
     ⟨`get!, (``get!_eq_getValueCast!, #[`(getValueCast!_of_perm _)])⟩,
     ⟨`getD, (``getD_eq_getValueCastD, #[`(getValueCastD_of_perm _)])⟩,
     ⟨`Const.get!, (``Const.get!_eq_getValue!, #[`(getValue!_of_perm _)])⟩,
     ⟨`Const.getD, (``Const.getD_eq_getValueD, #[`(getValueD_of_perm _)])⟩,
     ⟨`getKey?, (``getKey?_eq_getKey?, #[`(getKey?_of_perm _)])⟩,
     ⟨`getKey, (``getKey_eq_getKey, #[`(getKey_of_perm _)])⟩,
     ⟨`getKeyD, (``getKeyD_eq_getKeyD, #[`(getKeyD_of_perm _)])⟩,
     ⟨`getKey!, (``getKey!_eq_getKey!, #[`(getKey!_of_perm _)])⟩,
     ⟨`toList, (``Raw.toList_eq_toListModel, #[])⟩,
     ⟨`keys, (``Raw.keys_eq_keys_toListModel, #[`(perm_keys_congr_left)])⟩,
     ⟨`Const.toList, (``Raw.Const.toList_eq_toListModel_map, #[`(perm_map_congr_left)])⟩,
     ⟨`foldM, (``Raw.foldM_eq_foldlM_toListModel, #[])⟩,
     ⟨`fold, (``Raw.fold_eq_foldl_toListModel, #[])⟩,
     ⟨`foldRevM, (``Raw.foldRevM_eq_foldrM_toListModel, #[])⟩,
     ⟨`foldRev, (``Raw.foldRev_eq_foldr_toListModel, #[])⟩,
     ⟨`forIn, (``Raw.forIn_eq_forIn_toListModel, #[])⟩,
     ⟨`forM, (``Raw.forM_eq_forM_toListModel, #[])⟩,
     ⟨`Equiv, (``Raw.equiv_iff_toListModel_perm,
      #[`(_root_.List.Perm.congr_left), `(_root_.List.Perm.congr_right)])⟩]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_model" (" [" (ident,*) "]")? ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[[$names,*]]? $[using $using?]?) => do
  let mut queryNames : Array Name := #[]
  let mut congrNames : Array Term := #[]
  if let some names := names then
    for query in names.getElems do
      let some (query, congr) := queryMap.get? query.getId | continue
      queryNames := queryNames.push query
      for c in congr do
        congrNames := congrNames.push (← c)
  if queryNames.isEmpty then
    for (q, c) in queryMap.valuesArray do
      queryNames := queryNames.push q
      for c' in c do
        congrNames := congrNames.push (← c')
  let mut congrModify : Array (TSyntax `term) := #[]
  if let some modifyNames := names then
    for modify in modifyNames.getElems.flatMap
        (fun n => modifyMap.get? (Lean.Syntax.getId n) |>.toArray) do
      for congr in congrNames do
        congrModify := congrModify.push (← `($congr:term ($(mkIdent modify) ..)))
  `(tactic|
    (simp (discharger := with_reducible wf_trivial) only
      [$[$(Array.map Lean.mkIdent queryNames ++ congrModify):term],*]
     $[apply $(using?.toArray):term];*)
    <;> with_reducible try wf_trivial)

@[simp]
theorem isEmpty_emptyWithCapacity {c} : (emptyWithCapacity c : Raw₀ α β).1.isEmpty := by
  rw [Raw.isEmpty_eq_isEmpty wfImp_emptyWithCapacity, toListModel_buckets_emptyWithCapacity, List.isEmpty_nil]

set_option linter.missingDocs false in
@[deprecated isEmpty_emptyWithCapacity (since := "2025-03-12")]
abbrev isEmpty_empty := @isEmpty_emptyWithCapacity

@[simp]
theorem isEmpty_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.isEmpty = false := by
  simp_to_model [insert, isEmpty] using List.isEmpty_insertEntry

theorem contains_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} (hab : a == b) :
    m.contains a = m.contains b := by
  simp_to_model [contains] using List.containsKey_congr hab

@[simp]
theorem contains_emptyWithCapacity {a : α} {c : Nat} : (emptyWithCapacity c : Raw₀ α β).contains a = false := by
  simp [contains]

set_option linter.missingDocs false in
@[deprecated contains_emptyWithCapacity (since := "2025-03-12")]
abbrev contains_empty := @contains_emptyWithCapacity

theorem contains_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.contains a = false := by
  simp_to_model [isEmpty, contains]; empty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.isEmpty = false ↔ ∃ a, m.contains a = true := by
  simp_to_model [isEmpty, contains] using List.isEmpty_eq_false_iff_exists_containsKey

theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.isEmpty ↔ ∀ a, m.contains a = false := by
  simp_to_model [isEmpty, contains] using List.isEmpty_iff_forall_containsKey

theorem contains_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insert k v).contains a = ((k == a) || m.contains a) := by
  simp_to_model [insert, contains] using List.containsKey_insertEntry

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} : (m.insert k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model [insert, contains] using List.containsKey_of_containsKey_insertEntry

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).contains k := by
  simp_to_model [insert, contains] using List.containsKey_insertEntry_self

theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.size = if m.contains k then m.1.size else m.1.size + 1 := by
  simp_to_model [insert, contains, size] using List.length_insertEntry

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    m.1.size ≤ (m.insert k v).1.size := by
  simp_to_model [insert, size] using List.length_le_length_insertEntry

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.size ≤ m.1.size + 1 := by
  simp_to_model [insert, size] using List.length_insertEntry_le

@[simp]
theorem erase_emptyWithCapacity {k : α} {c : Nat} : (emptyWithCapacity c : Raw₀ α β).erase k = emptyWithCapacity c := by
  simp [erase, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated erase_emptyWithCapacity (since := "2025-03-12")]
abbrev erase_empty := @erase_emptyWithCapacity

theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.isEmpty = (m.1.isEmpty || (m.1.size == 1 && m.contains k)) := by
  simp_to_model [erase, isEmpty, size, contains] using List.isEmpty_eraseKey

theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) := by
  simp_to_model [erase, contains] using List.containsKey_eraseKey

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).contains a → m.contains a := by
  simp_to_model [erase, contains] using List.containsKey_of_containsKey_eraseKey

theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.size = if m.contains k then m.1.size - 1 else m.1.size := by
  simp_to_model [erase, size, contains] using List.length_eraseKey

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.size ≤ m.1.size := by
  simp_to_model [erase, size] using List.length_eraseKey_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    m.1.size ≤ (m.erase k).1.size + 1 := by
  simp_to_model [erase, size] using List.length_le_length_eraseKey

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
theorem get?_emptyWithCapacity [LawfulBEq α] {a : α} {c} : (emptyWithCapacity c : Raw₀ α β).get? a = none := by
  simp [get?]

set_option linter.missingDocs false in
@[deprecated get?_emptyWithCapacity (since := "2025-03-12")]
abbrev get?_empty := @get?_emptyWithCapacity

theorem get?_of_isEmpty [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.get? a = none := by
  simp_to_model [isEmpty, get?]; empty

theorem get?_insert [LawfulBEq α] (h : m.1.WF) {a k : α} {v : β k} : (m.insert k v).get? a =
    if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else m.get? a := by
  simp_to_model [insert, get?] using List.getValueCast?_insertEntry

theorem get?_insert_self [LawfulBEq α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).get? k = some v := by
  simp_to_model [insert, get?] using List.getValueCast?_insertEntry_self

theorem contains_eq_isSome_get? [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a = (m.get? a).isSome := by
  simp_to_model [contains, get?] using List.containsKey_eq_isSome_getValueCast?

theorem get?_eq_none [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.get? a = none := by
  simp_to_model [contains, get?] using List.getValueCast?_eq_none

theorem get?_erase [LawfulBEq α] (h : m.1.WF) {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  simp_to_model [erase, get?] using List.getValueCast?_eraseKey

theorem get?_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} : (m.erase k).get? k = none := by
  simp_to_model [erase, get?] using List.getValueCast?_eraseKey_self

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

@[simp]
theorem get?_emptyWithCapacity {a : α} {c} : get? (emptyWithCapacity c : Raw₀ α (fun _ => β)) a = none := by
  simp [get?]

set_option linter.missingDocs false in
@[deprecated get?_emptyWithCapacity (since := "2025-03-12")]
abbrev get?_empty := @get?_emptyWithCapacity

theorem get?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → get? m a = none := by
  simp_to_model [isEmpty, Const.get?]; empty

theorem get?_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} :
    get? (m.insert k v) a = if k == a then some v else get? m a := by
  simp_to_model [insert, Const.get?] using List.getValue?_insertEntry

theorem get?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β} :
    get? (m.insert k v) k = some v := by
  simp_to_model [insert, Const.get?] using List.getValue?_insertEntry_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = (get? m a).isSome := by
  simp_to_model [contains, Const.get?] using List.containsKey_eq_isSome_getValue?

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = false → get? m a = none := by
  simp_to_model [contains, Const.get?] using List.getValue?_eq_none.2

theorem get?_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a := by
  simp_to_model [erase, Const.get?] using List.getValue?_eraseKey

theorem get?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    get? (m.erase k) k = none := by
  simp_to_model [erase, Const.get?] using List.getValue?_eraseKey_self

theorem get?_eq_get? [LawfulBEq α] (h : m.1.WF) {a : α} : get? m a = m.get? a := by
  simp_to_model [get?, Const.get?] using List.getValue?_eq_getValueCast?

theorem get?_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} (hab : a == b) :
    get? m a = get? m b := by
  simp_to_model [Const.get?] using List.getValue?_congr

end Const

theorem get_insert [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).get a h₁ =
      if h₂ : k == a then
        cast (congrArg β (eq_of_beq h₂)) v
      else
        m.get a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model [insert, get] using List.getValueCast_insertEntry

theorem get_insert_self [LawfulBEq α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).get k (contains_insert_self _ h) = v := by
  simp_to_model [insert, get] using List.getValueCast_insertEntry_self

@[simp]
theorem get_erase [LawfulBEq α] (h : m.1.WF) {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (contains_of_contains_erase _ h h') := by
  simp_to_model [erase, get] using List.getValueCast_eraseKey

theorem get?_eq_some_get [LawfulBEq α] (h : m.1.WF) {a : α} {h'} : m.get? a = some (m.get a h') := by
  simp_to_model [get, get?] using List.getValueCast?_eq_some_getValueCast

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v
      else get m a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model [insert, Const.get] using List.getValue_insertEntry

theorem get_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β} :
    get (m.insert k v) k (contains_insert_self _ h) = v := by
  simp_to_model [insert, Const.get] using List.getValue_insertEntry_self

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {h'} :
    get (m.erase k) a h' = get m a (contains_of_contains_erase _ h h') := by
  simp_to_model [erase, Const.get] using List.getValue_eraseKey

theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {h} :
    get? m a = some (get m a h) := by
  simp_to_model [Const.get, Const.get?] using List.getValue?_eq_some_getValue

theorem get_eq_get [LawfulBEq α] (h : m.1.WF) {a : α} {h} : get m a h = m.get a h := by
  simp_to_model [Const.get, get] using List.getValue_eq_getValueCast

theorem get_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} (hab : a == b) {h'} :
    get m a h' = get m b ((contains_congr _ h hab).symm.trans h') := by
  simp_to_model [Const.get] using List.getValue_congr

end Const

theorem get!_emptyWithCapacity [LawfulBEq α] {a : α} [Inhabited (β a)] {c} :
    (emptyWithCapacity c : Raw₀ α β).get! a = default := by
  simp [get!, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated get!_emptyWithCapacity (since := "2025-03-12")]
abbrev get!_empty := @get!_emptyWithCapacity

theorem get!_of_isEmpty [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.1.isEmpty = true → m.get! a = default := by
  simp_to_model [isEmpty, get!]; empty

theorem get!_insert [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insert k v).get! a =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.get! a := by
  simp_to_model [insert, get!] using List.getValueCast!_insertEntry

theorem get!_insert_self [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b := by
  simp_to_model [insert, get!] using List.getValueCast!_insertEntry_self

theorem get!_eq_default [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_model [contains, get!] using List.getValueCast!_eq_default

theorem get!_erase [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a := by
  simp_to_model [erase, get!] using List.getValueCast!_eraseKey

theorem get!_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default := by
  simp_to_model [erase, get!] using List.getValueCast!_eraseKey_self

theorem get?_eq_some_get! [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.contains a = true → m.get? a = some (m.get! a) := by
  simp_to_model [contains, get?, get!] using List.getValueCast?_eq_some_getValueCast!

theorem get!_eq_get!_get? [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.get! a = (m.get? a).get! := by
  simp_to_model [get?, get!] using List.getValueCast!_eq_getValueCast?

theorem get_eq_get! [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] {h} :
    m.get a h = m.get! a := by
  simp_to_model [get, get!] using List.getValueCast_eq_getValueCast!

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get!_emptyWithCapacity [Inhabited β] {a : α} {c} :
    get! (emptyWithCapacity c : Raw₀ α (fun _ => β)) a = default := by
  simp [get!, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated get!_emptyWithCapacity (since := "2025-03-12")]
abbrev get!_empty := @get!_emptyWithCapacity

theorem get!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → get! m a = default := by
  simp_to_model [isEmpty, Const.get!]; empty

theorem get!_insert [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α} {v : β} :
    get! (m.insert k v) a = if k == a then v else get! m a := by
  simp_to_model [insert, Const.get!] using List.getValue!_insertEntry

theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k : α}
    {v : β} : get! (m.insert k v) k = v := by
  simp_to_model [insert, Const.get!] using List.getValue!_insertEntry_self

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_model [contains, Const.get!] using List.getValue!_eq_default

theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a := by
  simp_to_model [erase, Const.get!] using List.getValue!_eraseKey

theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k : α} :
    get! (m.erase k) k = default := by
  simp_to_model [erase, Const.get!] using List.getValue!_eraseKey_self

theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.contains a = true → get? m a = some (get! m a) := by
  simp_to_model [contains, Const.get!, Const.get?] using List.getValue?_eq_some_getValue!

theorem get!_eq_get!_get? [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    get! m a = (get? m a).get! := by
  simp_to_model [Const.get?, Const.get!] using List.getValue!_eq_getValue?

theorem get_eq_get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} {h} :
    get m a h = get! m a := by
  simp_to_model [Const.get, Const.get!] using List.getValue_eq_getValue!

theorem get!_eq_get! [LawfulBEq α] [Inhabited β] (h : m.1.WF) {a : α} :
    get! m a = m.get! a := by
  simp_to_model [Const.get!, get!] using List.getValue!_eq_getValueCast!

theorem get!_congr [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a b : α}
    (hab : a == b) : get! m a = get! m b := by
  simp_to_model [Const.get!] using List.getValue!_congr

end Const

theorem getD_emptyWithCapacity [LawfulBEq α] {a : α} {fallback : β a} {c} :
    (emptyWithCapacity c : Raw₀ α β).getD a fallback = fallback := by
  simp [getD, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated getD_emptyWithCapacity (since := "2025-03-12")]
abbrev getD_empty := @getD_emptyWithCapacity

theorem getD_of_isEmpty [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.1.isEmpty = true → m.getD a fallback = fallback := by
  simp_to_model [isEmpty, getD]; empty

theorem getD_insert [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insert k v).getD a fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else m.getD a fallback := by
  simp_to_model [insert, getD] using List.getValueCastD_insertEntry

theorem getD_insert_self [LawfulBEq α] (h : m.1.WF) {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_model [insert, getD] using List.getValueCastD_insertEntry_self

theorem getD_eq_fallback [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_model [contains, getD] using List.getValueCastD_eq_fallback

theorem getD_erase [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback := by
  simp_to_model [erase, getD] using List.getValueCastD_eraseKey

theorem getD_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback := by
  simp_to_model [erase, getD] using List.getValueCastD_eraseKey_self

theorem get?_eq_some_getD [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.contains a = true → m.get? a = some (m.getD a fallback) := by
  simp_to_model [contains, get?, getD] using List.getValueCast?_eq_some_getValueCastD

theorem getD_eq_getD_get? [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.getD a fallback = (m.get? a).getD fallback := by
  simp_to_model [getD, get?] using List.getValueCastD_eq_getValueCast?

theorem get_eq_getD [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} {h} :
    m.get a h = m.getD a fallback := by
  simp_to_model [get, getD] using List.getValueCast_eq_getValueCastD

theorem get!_eq_getD_default [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.get! a = m.getD a default := by
  simp_to_model [get!, getD] using List.getValueCast!_eq_getValueCastD_default

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem getD_emptyWithCapacity {a : α} {fallback : β} {c} :
    getD (emptyWithCapacity c : Raw₀ α (fun _ => β)) a fallback = fallback := by
  simp [getD, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated getD_emptyWithCapacity (since := "2025-03-12")]
abbrev getD_empty := @getD_emptyWithCapacity

theorem getD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.1.isEmpty = true → getD m a fallback = fallback := by
  simp_to_model [isEmpty, Const.getD]; empty

theorem getD_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback v : β} :
    getD (m.insert k v) a fallback = if k == a then v else getD m a fallback := by
  simp_to_model [insert, Const.getD] using List.getValueD_insertEntry

theorem getD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {fallback v : β} :
    getD (m.insert k v) k fallback = v := by
  simp_to_model [insert, Const.getD] using List.getValueD_insertEntry_self

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.contains a = false → getD m a fallback = fallback := by
  simp_to_model [contains, Const.getD] using List.getValueD_eq_fallback

theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback := by
  simp_to_model [erase, Const.getD] using List.getValueD_eraseKey

theorem getD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback := by
  simp_to_model [erase, Const.getD] using List.getValueD_eraseKey_self

theorem get?_eq_some_getD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.contains a = true → get? m a = some (getD m a fallback) := by
  simp_to_model [contains, Const.get?, Const.getD] using List.getValue?_eq_some_getValueD

theorem getD_eq_getD_get? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    getD m a fallback = (get? m a).getD fallback := by
  simp_to_model [Const.getD, Const.get?] using List.getValueD_eq_getValue?

theorem get_eq_getD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} {h} :
    get m a h = getD m a fallback := by
  simp_to_model [Const.get, Const.getD] using List.getValue_eq_getValueD

theorem get!_eq_getD_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    get! m a = getD m a default := by
  simp_to_model [Const.get!, Const.getD] using List.getValue!_eq_getValueD_default

theorem getD_eq_getD [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β} :
    getD m a fallback = m.getD a fallback := by
  simp_to_model [Const.getD, getD] using List.getValueD_eq_getValueCastD

theorem getD_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a b : α} {fallback : β}
    (hab : a == b) : getD m a fallback = getD m b fallback := by
  simp_to_model [Const.getD] using List.getValueD_congr

end Const

@[simp]
theorem getKey?_emptyWithCapacity {a : α} {c} : (emptyWithCapacity c : Raw₀ α β).getKey? a = none := by
  simp [getKey?]

set_option linter.missingDocs false in
@[deprecated getKey?_emptyWithCapacity (since := "2025-03-12")]
abbrev getKey?_empty := @getKey?_emptyWithCapacity

theorem getKey?_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.getKey? a = none := by
  simp_to_model [getKey?, isEmpty]; empty

theorem getKey?_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a k : α} {v : β k} :
    (m.insert k v).getKey? a = if k == a then some k else m.getKey? a := by
  simp_to_model [insert, getKey?] using List.getKey?_insertEntry

theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k := by
  simp_to_model [insert, getKey?] using List.getKey?_insertEntry_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome := by
  simp_to_model [getKey?, contains] using List.containsKey_eq_isSome_getKey?

theorem contains_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {a a' : α} (h : m.1.WF) :
    m.getKey? a = some a' → m.contains a' = true := by
  simp_to_model [getKey?, contains] using List.containsKey_of_getKey?_eq_some

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.getKey? a = none := by
  simp_to_model [getKey?, contains] using List.getKey?_eq_none

theorem getKey?_beq [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    (m.getKey? a).all (· == a) := by
  simp_to_model [getKey?] using List.getKey?_beq

theorem getKey?_eq_some [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a → m.getKey? a = some a := by
  simp_to_model [getKey?, contains] using List.getKey?_eq_some

theorem getKey?_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {k k' : α} (h : k == k') :
    m.getKey? k = m.getKey? k' := by
  simp_to_model [getKey?] using List.getKey?_congr

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a := by
  simp_to_model [erase, getKey?] using List.getKey?_eraseKey

theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).getKey? k = none := by
  simp_to_model [erase, getKey?] using List.getKey?_eraseKey_self

theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model [insert, getKey] using List.getKey_insertEntry

theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).getKey k (contains_insert_self _ h) = k := by
  simp_to_model [insert, getKey] using List.getKey_insertEntry_self

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (contains_of_contains_erase _ h h') := by
  simp_to_model [erase, getKey] using List.getKey_eraseKey

theorem getKey_beq [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} (h' : m.contains a) :
    m.getKey a h' == a := by
  simp_to_model [getKey] using List.getKey_beq

@[simp]
theorem getKey_eq [LawfulBEq α] (h : m.1.WF) {a : α} (h' : m.contains a) : m.getKey a h' = a := by
  simp_to_model [getKey] using List.getKey_eq

theorem getKey_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {k k' : α} (h' : k == k') (h'' : m.contains k) :
    m.getKey k h'' = m.getKey k' ((contains_congr _ h h').symm.trans h'') := by
  simp_to_model [getKey] using List.getKey_congr

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {h'} :
    m.getKey? a = some (m.getKey a h') := by
  simp_to_model [getKey?, getKey] using List.getKey?_eq_some_getKey

theorem getKey!_emptyWithCapacity {a : α} [Inhabited α] {c} :
    (emptyWithCapacity c : Raw₀ α β).getKey! a = default := by
  simp [getKey!, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated getKey!_emptyWithCapacity (since := "2025-03-12")]
abbrev getKey!_empty := @getKey!_emptyWithCapacity

theorem getKey!_of_isEmpty [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.1.isEmpty = true → m.getKey! a = default := by
  simp_to_model [isEmpty, getKey!]; empty;

theorem getKey!_insert [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insert k v).getKey! a = if k == a then k else m.getKey! a := by
  simp_to_model [insert, getKey!] using List.getKey!_insertEntry

theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α}
    {b : β a} : (m.insert a b).getKey! a = a := by
  simp_to_model [insert, getKey!] using List.getKey!_insertEntry_self

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.getKey! a = default := by
  simp_to_model [contains, getKey!] using List.getKey!_eq_default

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a := by
  simp_to_model [erase, getKey!] using List.getKey!_eraseKey

theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k : α} :
    (m.erase k).getKey! k = default := by
  simp_to_model [erase, getKey!] using List.getKey!_eraseKey_self

theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) := by
  simp_to_model [contains, getKey?, getKey!] using List.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.getKey! a = (m.getKey? a).get! := by
  simp_to_model [getKey!, getKey?] using List.getKey!_eq_getKey?

theorem getKey_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} {h} :
    m.getKey a h = m.getKey! a := by
  simp_to_model [getKey, getKey!] using List.getKey_eq_getKey!

theorem getKey!_congr [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {k k' : α} (h : k == k') : m.getKey! k = m.getKey! k' := by
  simp_to_model [getKey!] using List.getKey!_congr

theorem getKey!_eq_of_contains [LawfulBEq α] [Inhabited α] (h : m.1.WF) {k : α} :
    m.contains k → m.getKey! k = k := by
  simp_to_model [getKey!, contains] using List.getKey!_eq_of_containsKey

theorem getKeyD_emptyWithCapacity {a : α} {fallback : α} {c} :
    (emptyWithCapacity c : Raw₀ α β).getKeyD a fallback = fallback := by
  simp [getKeyD, emptyWithCapacity]

set_option linter.missingDocs false in
@[deprecated getKeyD_emptyWithCapacity (since := "2025-03-12")]
abbrev getKeyD_empty := @getKeyD_emptyWithCapacity

theorem getKeyD_of_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.1.isEmpty = true → m.getKeyD a fallback = fallback := by
  simp_to_model [isEmpty, getKeyD]; empty

theorem getKeyD_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α} {v : β k} :
    (m.insert k v).getKeyD a fallback =
      if k == a then k else m.getKeyD a fallback := by
  simp_to_model [insert, getKeyD] using List.getKeyD_insertEntry

theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α}
    {b : β a} :
    (m.insert a b).getKeyD a fallback = a := by
  simp_to_model [insert, getKeyD] using List.getKeyD_insertEntry_self

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback := by
  simp_to_model [contains, getKeyD] using List.getKeyD_eq_fallback

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback := by
  simp_to_model [erase, getKeyD] using List.getKeyD_eraseKey

theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback := by
  simp_to_model [erase, getKeyD] using List.getKeyD_eraseKey_self

theorem getKey?_eq_some_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.contains a = true → m.getKey? a = some (m.getKeyD a fallback) := by
  simp_to_model [contains, getKeyD, getKey?] using List.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.getKeyD a fallback = (m.getKey? a).getD fallback := by
  simp_to_model [getKey?, getKeyD] using List.getKeyD_eq_getKey?

theorem getKey_eq_getKeyD [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} {h} :
    m.getKey a h = m.getKeyD a fallback := by
  simp_to_model [getKey, getKeyD] using List.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {a : α} :
    m.getKey! a = m.getKeyD a default := by
  simp_to_model [getKey!, getKeyD] using List.getKey!_eq_getKeyD_default

theorem getKeyD_congr [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {k k' fallback : α} (h : k == k') : m.getKeyD k fallback = m.getKeyD k' fallback := by
  simp_to_model [getKeyD] using List.getKeyD_congr

theorem getKeyD_eq_of_contains [LawfulBEq α] (h : m.1.WF) {k fallback : α} :
    m.contains k → m.getKeyD k fallback = k := by
  simp_to_model [getKeyD, contains] using List.getKeyD_eq_of_containsKey

theorem isEmpty_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.isEmpty = false := by
  simp_to_model [insertIfNew, isEmpty] using List.isEmpty_insertEntryIfNew

theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) := by
  simp_to_model [insertIfNew, contains] using List.containsKey_insertEntryIfNew

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).contains k := by
  simp_to_model [insertIfNew, contains] using List.containsKey_insertEntryIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} : (m.insertIfNew k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model [insertIfNew, contains] using List.containsKey_of_containsKey_insertEntryIfNew

/-- This is a restatement of `contains_of_contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a := by
  simp_to_model [insertIfNew, contains] using List.containsKey_of_containsKey_insertEntryIfNew'

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.size = if m.contains k then m.1.size else m.1.size + 1 := by
  simp_to_model [insertIfNew, size, contains] using List.length_insertEntryIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    m.1.size ≤ (m.insertIfNew k v).1.size := by
  simp_to_model [insertIfNew, size] using List.length_le_length_insertEntryIfNew

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.size ≤ m.1.size + 1 := by
  simp_to_model [insertIfNew, size] using List.length_insertEntryIfNew_le

theorem get?_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).get? a =
      if h : k == a ∧ m.contains k = false then some (cast (congrArg β (eq_of_beq h.1)) v)
      else m.get? a := by
  simp_to_model [insertIfNew, get?, contains] using List.getValueCast?_insertEntryIfNew

theorem get_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).get a h₁ =
      if h₂ : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.get a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model [insertIfNew, get, contains] using List.getValueCast_insertEntryIfNew

theorem get!_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h.1)) v
      else m.get! a := by
  simp_to_model [insertIfNew, get!, contains] using List.getValueCast!_insertEntryIfNew

theorem getD_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp_to_model [insertIfNew, getD, contains] using List.getValueCastD_insertEntryIfNew

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ m.contains k = false then some v else get? m a := by
  simp_to_model [Const.get?, contains, insertIfNew] using List.getValue?_insertEntryIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ m.contains k = false then v
      else get m a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model [Const.get, contains, insertIfNew] using List.getValue_insertEntryIfNew

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α}
    {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ m.contains k = false then v else get! m a := by
  simp_to_model [Const.get!, contains, insertIfNew] using List.getValue!_insertEntryIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ m.contains k = false then v else getD m a fallback := by
  simp_to_model [Const.getD, contains, insertIfNew] using List.getValueD_insertEntryIfNew

end Const

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).getKey? a =
      if k == a ∧ m.contains k = false then some k else m.getKey? a := by
  simp_to_model [getKey?, contains, insertIfNew] using List.getKey?_insertEntryIfNew

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).getKey a h₁ =
      if h₂ : k == a ∧ m.contains k = false then k
      else m.getKey a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model [getKey, contains, insertIfNew] using List.getKey_insertEntryIfNew

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).getKey! a =
      if k == a ∧ m.contains k = false then k else m.getKey! a := by
  simp_to_model [getKey!, contains, insertIfNew] using List.getKey!_insertEntryIfNew

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α}
    {v : β k} :
    (m.insertIfNew k v).getKeyD a fallback =
      if k == a ∧ m.contains k = false then k else m.getKeyD a fallback := by
  simp_to_model [getKeyD, contains, insertIfNew] using List.getKeyD_insertEntryIfNew

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
  simp_to_model [size, keys] using List.length_keys_eq_length

@[simp]
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.keys.isEmpty = m.1.isEmpty := by
  simp_to_model [isEmpty, keys] using List.isEmpty_keys_eq_isEmpty

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    m.1.keys.contains k = m.contains k := by
  simp_to_model [contains, keys] using List.containsKey_eq_keys_contains.symm

@[simp]
theorem mem_keys [LawfulBEq α] (h : m.1.WF) {k : α} :
    k ∈ m.1.keys ↔ m.contains k := by
  rw [← List.contains_iff]
  simp_to_model [contains, keys]
  rw [List.containsKey_eq_keys_contains]

theorem forall_mem_keys_iff_forall_contains_getKey [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {p : α → Prop} :
    (∀ k ∈ m.1.keys, p k) ↔ ∀ (k : α) (h : m.contains k), p (m.getKey k h) := by
  simp_to_model [keys, getKey, contains] using List.forall_mem_keys_iff_forall_containsKey_getKey

theorem contains_of_mem_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α}
    (h' : k ∈ m.1.keys) : m.contains k :=
  (contains_keys m h).symm.trans (List.elem_eq_true_of_mem h')

theorem distinct_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.keys.Pairwise (fun a b => (a == b) = false) := by
  simp_to_model [keys] using (Raw.WF.out h).distinct.distinct

theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    m.1.toList.map Sigma.fst = m.1.keys := by
  simp_to_model [toList, keys]
  rw [List.keys_eq_map]

theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.toList.length = m.1.size := by
  simp_to_model [toList, size]

theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.toList.isEmpty = m.1.isEmpty := by
  simp_to_model [toList, isEmpty]

theorem mem_toList_iff_get?_eq_some [LawfulBEq α] (h : m.1.WF)
    {k : α} {v : β k} :
    ⟨k, v⟩ ∈ m.1.toList ↔ m.get? k = some v := by
  simp_to_model [get?, toList] using List.mem_iff_getValueCast?_eq_some

theorem find?_toList_eq_some_iff_get?_eq_some [LawfulBEq α]
    (h : m.1.WF) {k : α} {v : β k} :
    m.1.toList.find? (·.1 == k) = some ⟨k, v⟩ ↔ m.get? k = some v := by
  simp_to_model [toList, get?] using List.find?_eq_some_iff_getValueCast?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {k : α} :
    m.1.toList.find? (·.1 == k) = none ↔ m.contains k = false := by
  simp_to_model [toList, contains] using List.find?_eq_none_iff_containsKey_eq_false

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.toList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  simp_to_model [toList] using List.pairwise_fst_eq_false

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β))

theorem map_fst_toList_eq_keys [EquivBEq α] [LawfulHashable α] :
    (Raw.Const.toList m.1).map Prod.fst = m.1.keys := by
  simp_to_model [keys, Const.toList] using List.map_fst_map_toProd_eq_keys

theorem length_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    (Raw.Const.toList m.1).length = m.1.size := by
  simp_to_model [size, Const.toList] using List.length_map

theorem isEmpty_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    (Raw.Const.toList m.1).isEmpty = m.1.isEmpty := by
  simp_to_model [isEmpty, Const.toList]
  rw [Bool.eq_iff_iff, List.isEmpty_iff,List.isEmpty_iff, List.map_eq_nil_iff]

theorem mem_toList_iff_get?_eq_some [LawfulBEq α] (h : m.1.WF)
    {k : α} {v : β} :
    (k, v) ∈ Raw.Const.toList m.1 ↔ get? m k = some v := by
  simp_to_model [Const.toList, Const.get?] using List.mem_map_toProd_iff_getValue?_eq_some

theorem get?_eq_some_iff_exists_beq_and_mem_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {k : α} {v : β} :
    get? m k = some v ↔ ∃ (k' : α), k == k' ∧ (k', v) ∈ Raw.Const.toList m.1 := by
  simp_to_model [Const.get?, Const.toList] using getValue?_eq_some_iff_exists_beq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
    [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k k' : α} {v : β} :
    (Raw.Const.toList m.1).find? (fun a => a.1 == k) = some ⟨k', v⟩ ↔
      m.getKey? k = some k' ∧ get? m k = some v := by
  simp_to_model [getKey?, Const.get?, Const.toList]
    using List.find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {k : α} :
    (Raw.Const.toList m.1).find? (·.1 == k) = none ↔ m.contains k = false := by
  simp_to_model [Const.toList, contains] using List.find?_map_eq_none_iff_containsKey_eq_false

theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {k: α} {v : β} :
    (k, v) ∈ (Raw.Const.toList m.1) ↔ m.getKey? k = some k ∧ get? m k = some v := by
  simp_to_model [Const.toList, getKey?, Const.get?]
    using List.mem_map_toProd_iff_getKey?_eq_some_and_getValue?_eq_some

theorem distinct_keys_toList [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    (Raw.Const.toList m.1).Pairwise (fun a b => (a.1 == b.1) = false) := by
  simp_to_model [Const.toList] using List.pairwise_fst_eq_false_map_toProd

end Const

section monadic

-- The types are redefined because fold/for does not need BEq/Hashable
variable {α : Type u} {β : α → Type v} (m : Raw₀ α β) {δ : Type w} {m' : Type w → Type w}

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    m.1.foldM f init = m.1.toList.foldlM (fun a b => f a b.1 b.2) init := by
  simp_to_model [foldM, toList]

theorem fold_eq_foldl_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    m.1.fold f init = m.1.toList.foldl (fun a b => f a b.1 b.2) init := by
  simp_to_model [fold, toList]

theorem foldRevM_eq_foldrM_toList [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → β a → m' δ} {init : δ} :
    Raw.Internal.foldRevM f init m.1 = m.1.toList.foldrM (fun a b => f b a.1 a.2) init := by
  simp_to_model [foldRevM, toList]

theorem foldRev_eq_foldr_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    Raw.Internal.foldRev f init m.1 = m.1.toList.foldr (fun a b => f b a.1 a.2) init := by
  simp_to_model [foldRev, toList]

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : (a : α) → β a → m' PUnit} :
    m.1.forM f = m.1.toList.forM (fun a => f a.1 a.2) := by
  simp_to_model [forM, toList]

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : (a : α) → β a → δ → m' (ForInStep δ)} {init : δ} :
    m.1.forIn f init = ForIn.forIn m.1.toList init (fun a b => f a.1 a.2 b) := by
  simp_to_model [forIn, toList]

theorem foldM_eq_foldlM_keys [Monad m'] [LawfulMonad m']
    {f : δ → α → m' δ} {init : δ} :
    m.1.foldM (fun d a _ => f d a) init = m.1.keys.foldlM f init := by
  simp_to_model [foldM, keys] using List.foldlM_eq_foldlM_keys

theorem fold_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    m.1.fold (fun d a _ => f d a) init = m.1.keys.foldl f init := by
  simp_to_model [fold, keys] using List.foldl_eq_foldl_keys

theorem foldRevM_eq_foldrM_keys [Monad m'] [LawfulMonad m']
    {f : δ → (a : α) → m' δ} {init : δ} :
    Raw.Internal.foldRevM (fun d a _ => f d a) init m.1 =
      m.1.keys.foldrM (fun a b => f b a) init := by
  simp_to_model [foldRevM, keys] using List.foldrM_eq_foldrM_keys'

theorem foldRev_eq_foldr_keys {f : δ → (a : α) → δ} {init : δ} :
    Raw.Internal.foldRev (fun d a _ => f d a) init m.1 =
      m.1.keys.foldr (fun a b => f b a) init := by
  simp_to_model [foldRev, keys] using List.foldr_eq_foldr_keys'

theorem forM_eq_forM_keys [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} :
    m.1.forM (fun a _ => f a) = m.1.keys.forM f := by
  simp_to_model [forM, keys] using List.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} :
    m.1.forIn (fun a _ d => f a d) init = ForIn.forIn m.1.keys init f := by
  simp_to_model [forIn, keys] using List.forIn_eq_forIn_keys

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β))

theorem foldM_eq_foldlM_toList [Monad m'] [LawfulMonad m']
    {f : δ → α → β → m' δ} {init : δ} :
    m.1.foldM f init = (Raw.Const.toList m.1).foldlM (fun a b => f a b.1 b.2) init := by
  simp_to_model [foldM, Const.toList] using List.foldlM_eq_foldlM_toProd

theorem fold_eq_foldl_toList {f : δ → α → β → δ} {init : δ} :
    m.1.fold f init = (Raw.Const.toList m.1).foldl (fun a b => f a b.1 b.2) init := by
  simp_to_model [fold, Const.toList] using List.foldl_eq_foldl_toProd

theorem foldRevM_eq_foldrM_toList [Monad m'] [LawfulMonad m']
    {f : δ → α → β → m' δ} {init : δ} :
    Raw.Internal.foldRevM f init m.1 =
      (Raw.Const.toList m.1).foldrM (fun a b => f b a.1 a.2) init := by
  simp_to_model [foldRevM, Const.toList] using List.foldrM_eq_foldrM_toProd'

theorem foldRev_eq_foldr_toList {f : δ → α → β → δ} {init : δ} :
    Raw.Internal.foldRev f init m.1 = (Raw.Const.toList m.1).foldr (fun a b => f b a.1 a.2) init := by
  simp_to_model [foldRev, Const.toList] using List.foldr_eq_foldr_toProd'

theorem forM_eq_forM_toList [Monad m'] [LawfulMonad m'] {f : α → β → m' PUnit} :
    m.1.forM f = (Raw.Const.toList m.1).forM (fun a => f a.1 a.2) := by
  simp_to_model [forM, Const.toList] using List.forM_eq_forM_toProd

theorem forIn_eq_forIn_toList [Monad m'] [LawfulMonad m']
    {f : α → β → δ → m' (ForInStep δ)} {init : δ} :
    m.1.forIn f init = ForIn.forIn (Raw.Const.toList m.1) init (fun a b => f a.1 a.2 b) := by
  simp_to_model [forIn, Const.toList] using List.forIn_eq_forIn_toProd

end Const

end monadic

section insertMany

variable {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]

@[elab_as_elim]
theorem insertMany_ind {motive : Raw₀ α β → Prop} (m : Raw₀ α β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l).1 :=
  (m.insertMany l).2 motive (insert _ _ _) init

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
  simp_to_model [insertMany, contains] using List.containsKey_insertList

theorem contains_of_contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (m.insertMany l).1.contains k → (l.map Sigma.fst).contains k = false → m.contains k := by
  simp_to_model [insertMany, contains] using List.containsKey_of_containsKey_insertList

theorem contains_insertMany_of_contains [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} {k : α} (h' : m.contains k) : (m.insertMany l).1.contains k := by
  refine (?_ : _ ∧ (m.insertMany l).1.1.WF).1
  refine insertMany_ind m l ⟨h', h⟩ ?_
  intro m a b ⟨h', h⟩
  simp only [h, contains_insert, h', Bool.or_true, true_and]
  exact h.insert₀

theorem get?_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.get? k = m.get? k := by
  simp_to_model [insertMany, get?] using List.getValueCast?_insertList_of_contains_eq_false

theorem get?_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).1.get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  simp_to_model [insertMany, get?] using List.getValueCast?_insertList_of_mem

theorem get_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (m.insertMany l).1.get k h' =
    m.get k (contains_of_contains_insertMany_list _ h h' contains) := by
  simp_to_model [insertMany, get] using List.getValueCast_insertList_of_contains_eq_false

theorem get_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (m.insertMany l).1.get k' h' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_model [insertMany, get] using List.getValueCast_insertList_of_mem

theorem get!_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.get! k = m.get! k := by
  simp_to_model [insertMany, get!] using List.getValueCast!_insertList_of_contains_eq_false

theorem get!_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).1.get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_model [insertMany, get!] using List.getValueCast!_insertList_of_mem

theorem getD_insertMany_list_of_contains_eq_false [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getD k fallback = m.getD k fallback := by
  simp_to_model [insertMany, getD] using List.getValueCastD_insertList_of_contains_eq_false

theorem getD_insertMany_list_of_mem [LawfulBEq α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (m.insertMany l).1.getD k' fallback = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  simp_to_model [insertMany, getD] using List.getValueCastD_insertList_of_mem

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getKey? k = m.getKey? k := by
  simp_to_model [insertMany, getKey?] using List.getKey?_insertList_of_contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).1.getKey? k' = some k := by
  simp_to_model [insertMany, getKey?] using List.getKey?_insertList_of_mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k : α}
    (h₁ : (l.map Sigma.fst).contains k = false)
    {h'} :
    (m.insertMany l).1.getKey k h' =
    m.getKey k (contains_of_contains_insertMany_list _ h h' h₁) := by
  simp_to_model [insertMany, getKey] using List.getKey_insertList_of_contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (m.insertMany l).1.getKey k' h' = k := by
  simp_to_model [insertMany, getKey] using List.getKey_insertList_of_mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.1.WF) {l : List ((a : α) × β a)} {k : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getKey! k = m.getKey! k := by
  simp_to_model [insertMany, getKey!] using List.getKey!_insertList_of_contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).1.getKey! k' = k := by
  simp_to_model [insertMany, getKey!] using List.getKey!_insertList_of_mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} {k fallback : α}
    (h' : (l.map Sigma.fst).contains k = false) :
    (m.insertMany l).1.getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_model [insertMany, getKeyD] using List.getKeyD_insertList_of_contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (m.insertMany l).1.getKeyD k' fallback = k := by
  simp_to_model [insertMany, getKeyD] using List.getKeyD_insertList_of_mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), m.contains a → (l.map Sigma.fst).contains a = false) →
    (m.insertMany l).1.1.size = m.1.size + l.length := by
  simp_to_model [insertMany, size, contains] using List.length_insertList

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} :
    m.1.size ≤ (m.insertMany l).1.1.size := by
  simp_to_model [insertMany, size] using List.length_le_length_insertList

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} : m.1.size ≤ (m.insertMany l).1.1.size := by
  refine (?_ : _ ∧ (m.insertMany l).1.1.WF).1
  refine insertMany_ind m l ⟨Nat.le_refl _, h⟩ ?_
  intro m' a b ⟨h', h⟩
  constructor
  · exact Nat.le_trans h' (size_le_size_insert m' h)
  · exact h.insert₀

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} :
    (m.insertMany l).1.1.size ≤ m.1.size + l.length := by
  simp_to_model [insertMany, size] using List.length_insertList_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ((a : α) × β a)} :
    (m.insertMany l).1.1.isEmpty = (m.1.isEmpty && l.isEmpty) := by
  simp_to_model [insertMany, isEmpty] using List.isEmpty_insertList

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} : (m.insertMany l).1.1.isEmpty → m.1.isEmpty := by
  refine (?_ : _ ∧ (m.insertMany l).1.1.WF).1
  refine insertMany_ind m l ⟨id, h⟩ ?_
  intro m' a b ⟨h', h⟩
  constructor
  · intro h''
    simp only [isEmpty_insert, h, Bool.false_eq_true] at h''
  · exact h.insert₀

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β))
variable {ρ : Type w} [ForIn Id ρ (α × β)]

@[elab_as_elim]
theorem insertMany_ind {motive : Raw₀ α (fun _ => β) → Prop} (m : Raw₀ α fun _ => β) (l : ρ)
    (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (insertMany m l).1 :=
  (insertMany m l).2 motive (insert _ _ _) init

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
  simp_to_model [Const.insertMany, contains] using List.containsKey_insertListConst

theorem contains_of_contains_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List ( α × β )} {k : α} :
    (insertMany m l).1.contains k → (l.map Prod.fst).contains k = false → m.contains k := by
  simp_to_model [Const.insertMany, contains] using List.containsKey_of_containsKey_insertListConst

theorem contains_insertMany_of_contains [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} {k : α} (h' : m.contains k) : (insertMany m l).1.contains k := by
  refine (?_ : _ ∧ (insertMany m l).1.1.WF).1
  refine insertMany_ind m l ⟨h', h⟩ ?_
  intro m a b ⟨h', h⟩
  simp only [h, contains_insert, h', Bool.or_true, true_and]
  exact h.insert₀

theorem getKey?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany m l).1.getKey? k = m.getKey? k := by
  simp_to_model [Const.insertMany, getKey?] using List.getKey?_insertListConst_of_contains_eq_false

theorem getKey?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List  (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).1.getKey? k' = some k := by
  simp_to_model [Const.insertMany, getKey?] using List.getKey?_insertListConst_of_mem

theorem getKey_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany m l).1.getKey k h' =
    m.getKey k (contains_of_contains_insertMany_list _ h h' h₁) := by
  simp_to_model [Const.insertMany, getKey] using List.getKey_insertListConst_of_contains_eq_false

theorem getKey_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany m l).1.getKey k' h' = k := by
  simp_to_model [Const.insertMany, getKey] using List.getKey_insertListConst_of_mem

theorem getKey!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h : m.1.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany m l).1.getKey! k = m.getKey! k := by
  simp_to_model [Const.insertMany, getKey!] using List.getKey!_insertListConst_of_contains_eq_false

theorem getKey!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF)
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).1.getKey! k' = k := by
  simp_to_model [Const.insertMany, getKey!] using List.getKey!_insertListConst_of_mem

theorem getKeyD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k fallback : α}
    (h' : (l.map Prod.fst).contains k = false) :
    (insertMany m l).1.getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_model [Const.insertMany, getKeyD] using List.getKeyD_insertListConst_of_contains_eq_false

theorem getKeyD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany m l).1.getKeyD k' fallback = k := by
  simp_to_model [Const.insertMany, getKeyD] using List.getKeyD_insertListConst_of_mem

theorem size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (∀ (a : α), m.contains a → (l.map Prod.fst).contains a = false) →
    (insertMany m l).1.1.size = m.1.size + l.length := by
  simp_to_model [Const.insertMany, size, contains] using List.length_insertListConst

theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} :
    m.1.size ≤ (insertMany m l).1.1.size := by
  simp_to_model [Const.insertMany, size] using List.length_le_length_insertListConst

theorem size_le_size_insertMany [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} : m.1.size ≤ (insertMany m l).1.1.size := by
  refine (?_ : _ ∧ (insertMany m l).1.1.WF).1
  refine insertMany_ind m l ⟨Nat.le_refl _, h⟩ ?_
  intro m' a b ⟨h', h⟩
  constructor
  · exact Nat.le_trans h' (size_le_size_insert m' h)
  · exact h.insert₀

theorem size_insertMany_list_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} :
    (insertMany m l).1.1.size ≤ m.1.size + l.length := by
  simp_to_model [Const.insertMany, size] using List.length_insertListConst_le

@[simp]
theorem isEmpty_insertMany_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} :
    (insertMany m l).1.1.isEmpty = (m.1.isEmpty && l.isEmpty) := by
  simp_to_model [Const.insertMany, isEmpty] using List.isEmpty_insertListConst

theorem isEmpty_of_isEmpty_insertMany [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} : (insertMany m l).1.1.isEmpty → m.1.isEmpty := by
  refine (?_ : _ ∧ (insertMany m l).1.1.WF).1
  refine insertMany_ind m l ⟨id, h⟩ ?_
  intro m' a b ⟨h', h⟩
  constructor
  · intro h''
    simp only [isEmpty_insert, h, Bool.false_eq_true] at h''
  · exact h.insert₀

theorem get?_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get? (insertMany m l).1 k = get? m k := by
  simp_to_model [Const.insertMany, Const.get?]
    using List.getValue?_insertListConst_of_contains_eq_false

theorem get?_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany m l).1 k' = some v := by
  simp_to_model [Const.insertMany, Const.get?] using List.getValue?_insertListConst_of_mem

theorem get_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α}
    (h₁ : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany m l).1 k h' = get m k (contains_of_contains_insertMany_list _ h h' h₁) := by
  simp_to_model [Const.insertMany, Const.get]
    using List.getValue_insertListConst_of_contains_eq_false

theorem get_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    get (insertMany m l).1 k' h' = v := by
  simp_to_model [Const.insertMany, Const.get] using List.getValue_insertListConst_of_mem

theorem get!_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited β]  (h : m.1.WF) {l : List (α × β)} {k : α}
    (h' : (l.map Prod.fst).contains k = false) :
    get! (insertMany m l).1 k = get! m k := by
  simp_to_model [Const.insertMany, Const.get!]
    using List.getValue!_insertListConst_of_contains_eq_false

theorem get!_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany m l).1 k' = v := by
  simp_to_model [Const.insertMany, Const.get!] using List.getValue!_insertListConst_of_mem

theorem getD_insertMany_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k : α} {fallback : β}
    (h' : (l.map Prod.fst).contains k = false) :
    getD (insertMany m l).1 k fallback = getD m k fallback := by
  simp_to_model [Const.insertMany, Const.getD]
    using List.getValueD_insertListConst_of_contains_eq_false

theorem getD_insertMany_list_of_mem [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany m l).1 k' fallback = v := by
  simp_to_model [Const.insertMany, Const.getD] using List.getValueD_insertListConst_of_mem

variable (m : Raw₀ α (fun _ => Unit))

variable {ρ : Type w} [ForIn Id ρ α]

@[elab_as_elim]
theorem insertManyIfNewUnit_ind {motive : Raw₀ α (fun _ => Unit) → Prop}
    (m : Raw₀ α fun _ => Unit) (l : ρ)
    (init : motive m) (insert : ∀ m a, motive m → motive (m.insertIfNew a ())) :
    motive (insertManyIfNewUnit m l).1 :=
  (insertManyIfNewUnit m l).2 motive (insert _ _) init

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
  simp_to_model [Const.insertManyIfNewUnit, contains] using List.containsKey_insertListIfNewUnit

theorem contains_of_contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} {k : α} (h₂ : l.contains k = false) :
    (insertManyIfNewUnit m l).1.contains k → m.contains k := by
  simp_to_model [Const.insertManyIfNewUnit, contains]
    using List.containsKey_of_containsKey_insertListIfNewUnit

theorem contains_insertManyIfNewUnit_of_contains [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} {k : α} (h' : m.contains k) : (insertManyIfNewUnit m l).1.contains k := by
  refine (?_ : _ ∧ (insertManyIfNewUnit m l).1.1.WF).1
  refine insertManyIfNewUnit_ind m l ⟨h', h⟩ ?_
  intro m a ⟨h', h⟩
  simp only [h, contains_insertIfNew, h', Bool.or_true, true_and]
  exact h.insertIfNew₀

theorem getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} :
    m.contains k = false → l.contains k = false → getKey? (insertManyIfNewUnit m l).1 k = none := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKey?]
    using List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k k' : α} (k_beq : k == k') :
    m.contains k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey? (insertManyIfNewUnit m l).1 k' = some k := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKey?]
    using List.getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey?_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} :
    m.contains k → getKey? (insertManyIfNewUnit m l).1 k = getKey? m k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey?, contains]
    using List.getKey?_insertListIfNewUnit_of_contains

theorem getKey_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} {h'} (contains : m.contains k) :
    getKey (insertManyIfNewUnit m l).1 k h' = getKey m k contains := by
  simp_to_model [Const.insertManyIfNewUnit, getKey]
    using List.getKey_insertListIfNewUnit_of_contains

theorem getKey_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α}
    {k k' : α} (k_beq : k == k') {h'} :
    m.contains k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey (insertManyIfNewUnit m l).1 k' h' = k := by
  simp_to_model [Const.insertManyIfNewUnit, getKey, contains]
    using List.getKey_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey_insertManyIfNewUnit_list_mem_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k : α} (contains : m.contains k) {h'} :
    getKey (insertManyIfNewUnit m l).1 k h' = getKey m k contains := by
  simp_to_model [Const.insertManyIfNewUnit, getKey]
    using List.getKey_insertListIfNewUnit_of_contains

theorem getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {l : List α} {k : α} :
    m.contains k = false → l.contains k = false →
      getKey! (insertManyIfNewUnit m l).1 k = default := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKey!]
    using List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.1.WF) {l : List α} {k k' : α} (k_beq : k == k') :
    contains m k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKey! (insertManyIfNewUnit m l).1 k' = k := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKey!]
    using List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKey!_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    [Inhabited α] (h : m.1.WF) {l : List α} {k : α} :
    m.contains k → getKey! (insertManyIfNewUnit m l).1 k = getKey! m k  := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKey!]
    using List.getKey!_insertListIfNewUnit_of_contains

theorem getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {l : List α} {k fallback : α} :
    m.contains k = false → l.contains k = false → getKeyD (insertManyIfNewUnit m l).1 k fallback = fallback := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKeyD]
    using List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_mem [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k k' fallback : α} (k_beq : k == k') :
    m.contains k = false → l.Pairwise (fun a b => (a == b) = false) → k ∈ l →
      getKeyD (insertManyIfNewUnit m l).1 k' fallback = k := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKeyD]
    using List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem

theorem getKeyD_insertManyIfNewUnit_list_of_contains [EquivBEq α] [LawfulHashable α]
    (h : m.1.WF) {l : List α} {k fallback : α} :
    m.contains k → getKeyD (insertManyIfNewUnit m l).1 k fallback = getKeyD m k fallback := by
  simp_to_model [Const.insertManyIfNewUnit, contains, getKeyD]
    using List.getKeyD_insertListIfNewUnit_of_contains

theorem size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (∀ (a : α), m.contains a → l.contains a = false) →
    (insertManyIfNewUnit m l).1.1.size = m.1.size + l.length := by
  simp_to_model [Const.insertManyIfNewUnit, contains, size] using List.length_insertListIfNewUnit

theorem size_le_size_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} :
    m.1.size ≤ (insertManyIfNewUnit m l).1.1.size := by
  simp_to_model [Const.insertManyIfNewUnit, size] using List.length_le_length_insertListIfNewUnit

theorem size_le_size_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} : m.1.size ≤ (insertManyIfNewUnit m l).1.1.size := by
  refine (?_ : _ ∧ (insertManyIfNewUnit m l).1.1.WF).1
  refine insertManyIfNewUnit_ind m l ⟨Nat.le_refl _, h⟩ ?_
  intro m' a ⟨h', h⟩
  constructor
  · exact Nat.le_trans h' (size_le_size_insertIfNew m' h)
  · exact h.insertIfNew₀

theorem size_insertManyIfNewUnit_list_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).1.1.size ≤ m.1.size + l.length := by
  simp_to_model [Const.insertManyIfNewUnit, size] using List.length_insertListIfNewUnit_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} :
    (insertManyIfNewUnit m l).1.1.isEmpty = (m.1.isEmpty && l.isEmpty) := by
  simp_to_model [Const.insertManyIfNewUnit, isEmpty] using List.isEmpty_insertListIfNewUnit

theorem isEmpty_of_isEmpty_insertManyIfNewUnit [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : ρ} : (insertManyIfNewUnit m l).1.1.isEmpty → m.1.isEmpty := by
  refine (?_ : _ ∧ (insertManyIfNewUnit m l).1.1.WF).1
  refine insertManyIfNewUnit_ind m l ⟨id, h⟩ ?_
  intro m' a ⟨h', h⟩
  constructor
  · intro h''
    simp only [isEmpty_insertIfNew, h, Bool.false_eq_true] at h''
  · exact h.insertIfNew₀

theorem get?_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (h : m.1.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit m l).1 k =
    if m.contains k ∨ l.contains k then some () else none := by
  simp_to_model [Const.insertManyIfNewUnit, contains, Const.get?]
    using List.getValue?_insertListIfNewUnit

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
theorem insertMany_emptyWithCapacity_list_nil :
    (insertMany emptyWithCapacity ([] : List ((a : α) × (β a)))).1 = emptyWithCapacity := by
  simp

set_option linter.missingDocs false in
@[deprecated insertMany_emptyWithCapacity_list_nil (since := "2025-03-12")]
abbrev insertMany_empty_list_nil := @insertMany_emptyWithCapacity_list_nil

@[simp]
theorem insertMany_emptyWithCapacity_list_singleton {k : α} {v : β k} :
    (insertMany emptyWithCapacity [⟨k, v⟩]).1 = emptyWithCapacity.insert k v := by
  simp

set_option linter.missingDocs false in
@[deprecated insertMany_emptyWithCapacity_list_singleton (since := "2025-03-12")]
abbrev insertMany_empty_list_singleton := @insertMany_emptyWithCapacity_list_singleton

theorem insertMany_emptyWithCapacity_list_cons {k : α} {v : β k}
    {tl : List ((a : α) × (β a))} :
    (insertMany emptyWithCapacity (⟨k, v⟩ :: tl)).1 = ((emptyWithCapacity.insert k v).insertMany tl).1 := by
  rw [insertMany_cons]

set_option linter.missingDocs false in
@[deprecated insertMany_emptyWithCapacity_list_cons (since := "2025-03-12")]
abbrev insertMany_empty_list_cons := @insertMany_emptyWithCapacity_list_cons

theorem contains_insertMany_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α} :
    (insertMany emptyWithCapacity l).1.contains k = (l.map Sigma.fst).contains k := by
  simp [contains_insertMany_list _ Raw.WF.emptyWithCapacity₀]

set_option linter.missingDocs false in
@[deprecated contains_insertMany_emptyWithCapacity_list (since := "2025-03-12")]
abbrev contains_insertMany_empty_list := @contains_insertMany_emptyWithCapacity_list

theorem get?_insertMany_emptyWithCapacity_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.get? k = none := by
  simp [get?_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]

set_option linter.missingDocs false in
@[deprecated get?_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev get?_insertMany_empty_list_of_contains_eq_false := @get?_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem get?_insertMany_emptyWithCapacity_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany emptyWithCapacity l).1.get? k' = some (cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v) := by
  rw [get?_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated get?_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev get?_insertMany_empty_list_of_mem := @get?_insertMany_emptyWithCapacity_list_of_mem

theorem get_insertMany_emptyWithCapacity_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (insertMany emptyWithCapacity l).1.get k' h = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  rw [get_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated get_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev get_insertMany_empty_list_of_mem := @get_insertMany_emptyWithCapacity_list_of_mem

theorem get!_insertMany_emptyWithCapacity_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.get! k = default := by
  simp only [get!_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply get!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get!_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev get!_insertMany_empty_list_of_contains_eq_false := @get!_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem get!_insertMany_emptyWithCapacity_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany emptyWithCapacity l).1.get! k' = cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  rw [get!_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated get!_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev get!_insertMany_empty_list_of_mem := @get!_insertMany_emptyWithCapacity_list_of_mem

theorem getD_insertMany_emptyWithCapacity_list_of_contains_eq_false [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.getD k fallback = fallback := by
  rw [getD_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ contains_eq_false]
  apply getD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getD_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getD_insertMany_empty_list_of_contains_eq_false := @getD_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getD_insertMany_emptyWithCapacity_list_of_mem [LawfulBEq α]
    {l : List ((a : α) × β a)} {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    (insertMany emptyWithCapacity l).1.getD k' fallback =
      cast (by congr; apply LawfulBEq.eq_of_beq k_beq) v := by
  rw [getD_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getD_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getD_insertMany_empty_list_of_mem := @getD_insertMany_emptyWithCapacity_list_of_mem

theorem getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.getKey? k = none := by
  rw [getKey?_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply getKey?_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKey?_insertMany_empty_list_of_contains_eq_false := @getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getKey?_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany emptyWithCapacity l).1.getKey? k' = some k := by
  rw [getKey?_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKey?_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey?_insertMany_empty_list_of_mem := @getKey?_insertMany_emptyWithCapacity_list_of_mem

theorem getKey_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (insertMany emptyWithCapacity l).1.getKey k' h' = k := by
  rw [getKey_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKey_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey_insertMany_empty_list_of_mem := @getKey_insertMany_emptyWithCapacity_list_of_mem

theorem getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List ((a : α) × β a)} {k : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.getKey! k = default := by
  rw [getKey!_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply getKey!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKey!_insertMany_empty_list_of_contains_eq_false := @getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getKey!_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany emptyWithCapacity l).1.getKey! k' = k := by
  rw [getKey!_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKey!_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey!_insertMany_empty_list_of_mem := @getKey!_insertMany_emptyWithCapacity_list_of_mem

theorem getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} {k fallback : α}
    (h : (l.map Sigma.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.getKeyD k fallback = fallback := by
  rw [getKeyD_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply getKeyD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKeyD_insertMany_empty_list_of_contains_eq_false := @getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getKeyD_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Sigma.fst) :
    (insertMany emptyWithCapacity l).1.getKeyD k' fallback = k := by
  rw [getKeyD_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKeyD_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKeyD_insertMany_empty_list_of_mem := @getKeyD_insertMany_emptyWithCapacity_list_of_mem

theorem size_insertMany_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (insertMany emptyWithCapacity l).1.1.size = l.length := by
  rw [size_insertMany_list _ Raw.WF.emptyWithCapacity₀ distinct]
  · simp only [size_emptyWithCapacity, Nat.zero_add]
  · simp only [contains_emptyWithCapacity, Bool.false_eq_true, false_implies, implies_true]

set_option linter.missingDocs false in
@[deprecated size_insertMany_emptyWithCapacity_list (since := "2025-03-12")]
abbrev size_insertMany_empty_list := @size_insertMany_emptyWithCapacity_list

theorem size_insertMany_emptyWithCapacity_list_le [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (insertMany emptyWithCapacity l).1.1.size ≤ l.length := by
  rw [← Nat.zero_add l.length]
  apply (size_insertMany_list_le _ Raw.WF.emptyWithCapacity₀)

set_option linter.missingDocs false in
@[deprecated size_insertMany_emptyWithCapacity_list_le (since := "2025-03-12")]
abbrev size_insertMany_empty_list_le := @size_insertMany_emptyWithCapacity_list_le

theorem isEmpty_insertMany_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List ((a : α) × β a)} :
    (insertMany emptyWithCapacity l).1.1.isEmpty = l.isEmpty := by
  simp [isEmpty_insertMany_list _ Raw.WF.emptyWithCapacity₀]

set_option linter.missingDocs false in
@[deprecated isEmpty_insertMany_emptyWithCapacity_list (since := "2025-03-12")]
abbrev isEmpty_insertMany_empty_list := @isEmpty_insertMany_emptyWithCapacity_list

namespace Const
variable {β : Type v}

@[simp]
theorem insertMany_emptyWithCapacity_list_nil :
    (insertMany emptyWithCapacity ([] : List (α × β))).1 = emptyWithCapacity := by
  simp only [insertMany_nil]

set_option linter.missingDocs false in
@[deprecated insertMany_emptyWithCapacity_list_nil (since := "2025-03-12")]
abbrev insertMany_empty_list_nil := @insertMany_emptyWithCapacity_list_nil

@[simp]
theorem insertMany_emptyWithCapacity_list_singleton {k : α} {v : β} :
    (insertMany emptyWithCapacity [⟨k, v⟩]).1 = emptyWithCapacity.insert k v := by
  simp only [insertMany_list_singleton]

set_option linter.missingDocs false in
@[deprecated insertMany_emptyWithCapacity_list_singleton (since := "2025-03-12")]
abbrev insertMany_empty_list_singleton := @insertMany_emptyWithCapacity_list_singleton

theorem insertMany_emptyWithCapacity_list_cons {k : α} {v : β}
    {tl : List (α × β)} :
    (insertMany emptyWithCapacity (⟨k, v⟩ :: tl)) = (insertMany (emptyWithCapacity.insert k v) tl).1 := by
  rw [insertMany_cons]

set_option linter.missingDocs false in
@[deprecated insertMany_emptyWithCapacity_list_cons (since := "2025-03-12")]
abbrev insertMany_empty_list_cons := @insertMany_emptyWithCapacity_list_cons

theorem contains_insertMany_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} :
    (insertMany emptyWithCapacity l).1.contains k = (l.map Prod.fst).contains k := by
  simp [contains_insertMany_list _ Raw.WF.emptyWithCapacity₀]

set_option linter.missingDocs false in
@[deprecated contains_insertMany_emptyWithCapacity_list (since := "2025-03-12")]
abbrev contains_insertMany_empty_list := @contains_insertMany_emptyWithCapacity_list

theorem get?_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    get? (insertMany emptyWithCapacity l).1 k = none := by
  rw [get?_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply get?_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get?_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev get?_insertMany_empty_list_of_contains_eq_false := @get?_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem get?_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l) k' = some v := by
  rw [get?_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated get?_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev get?_insertMany_empty_list_of_mem := @get?_insertMany_emptyWithCapacity_list_of_mem

theorem get_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (insertMany emptyWithCapacity l) k' h = v := by
  rw [get_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated get_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev get_insertMany_empty_list_of_mem := @get_insertMany_emptyWithCapacity_list_of_mem

theorem get!_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} [Inhabited β]
    (h : (l.map Prod.fst).contains k = false) :
    get! (insertMany emptyWithCapacity l) k = (default : β) := by
  rw [get!_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply get!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated get!_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev get!_insertMany_empty_list_of_contains_eq_false := @get!_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem get!_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l) k' = v := by
  rw [get!_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated get!_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev get!_insertMany_empty_list_of_mem := @get!_insertMany_emptyWithCapacity_list_of_mem

theorem getD_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany emptyWithCapacity l) k fallback = fallback := by
  rw [getD_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ contains_eq_false]
  apply getD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getD_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getD_insertMany_empty_list_of_contains_eq_false := @getD_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getD_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k k' : α} (k_beq : k == k') {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l) k' fallback = v := by
  rw [getD_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getD_insertMany_empty_list_of_mem (since := "2025-03-12")]
abbrev getD_insertMany_empty_list_of_mem := @getD_insertMany_emptyWithCapacity_list_of_mem

theorem getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.getKey? k = none := by
  rw [getKey?_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply getKey?_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKey?_insertMany_empty_list_of_contains_eq_false := @getKey?_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getKey?_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.getKey? k' = some k := by
  rw [getKey?_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKey?_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey?_insertMany_empty_list_of_mem := @getKey?_insertMany_emptyWithCapacity_list_of_mem

theorem getKey_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.getKey k' h' = k := by
  rw [getKey_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKey_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey_insertMany_empty_list_of_mem := @getKey_insertMany_emptyWithCapacity_list_of_mem

theorem getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List (α × β)} {k : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany emptyWithCapacity l).1.getKey! k = default := by
  rw [getKey!_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply getKey!_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKey!_insertMany_empty_list_of_contains_eq_false := @getKey!_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getKey!_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.getKey! k' = k := by
  rw [getKey!_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKey!_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey!_insertMany_empty_list_of_mem := @getKey!_insertMany_emptyWithCapacity_list_of_mem

theorem getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} {k fallback : α}
    (h : (l.map Prod.fst).contains k = false) :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.getKeyD k fallback = fallback := by
  rw [getKeyD_insertMany_list_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀ h]
  apply getKeyD_emptyWithCapacity

set_option linter.missingDocs false in
@[deprecated getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKeyD_insertMany_empty_list_of_contains_eq_false := @getKeyD_insertMany_emptyWithCapacity_list_of_contains_eq_false

theorem getKeyD_insertMany_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.getKeyD k' fallback = k := by
  rw [getKeyD_insertMany_list_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq distinct mem]

set_option linter.missingDocs false in
@[deprecated getKeyD_insertMany_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKeyD_insertMany_empty_list_of_mem := @getKeyD_insertMany_emptyWithCapacity_list_of_mem

theorem size_insertMany_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.1.size = l.length := by
  rw [size_insertMany_list _ Raw.WF.emptyWithCapacity₀ distinct]
  · simp only [size_emptyWithCapacity, Nat.zero_add]
  · simp only [contains_emptyWithCapacity, Bool.false_eq_true, false_implies, implies_true]

set_option linter.missingDocs false in
@[deprecated size_insertMany_emptyWithCapacity_list (since := "2025-03-12")]
abbrev size_insertMany_empty_list := @size_insertMany_emptyWithCapacity_list

theorem size_insertMany_emptyWithCapacity_list_le [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.1.size ≤ l.length := by
  rw [← Nat.zero_add l.length]
  apply (size_insertMany_list_le _ Raw.WF.emptyWithCapacity₀)

set_option linter.missingDocs false in
@[deprecated size_insertMany_emptyWithCapacity_list_le (since := "2025-03-12")]
abbrev size_insertMany_empty_list_le := @size_insertMany_emptyWithCapacity_list_le

theorem isEmpty_insertMany_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List (α × β)} :
    (insertMany (emptyWithCapacity : Raw₀ α (fun _ => β)) l).1.1.isEmpty = l.isEmpty := by
  simp [isEmpty_insertMany_list _ Raw.WF.emptyWithCapacity₀]

set_option linter.missingDocs false in
@[deprecated isEmpty_insertMany_emptyWithCapacity_list (since := "2025-03-12")]
abbrev isEmpty_insertMany_empty_list := @isEmpty_insertMany_emptyWithCapacity_list

@[simp]
theorem insertManyIfNewUnit_emptyWithCapacity_list_nil :
    insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) ([] : List α) =
      (emptyWithCapacity : Raw₀ α (fun _ => Unit)) := by
  simp

set_option linter.missingDocs false in
@[deprecated insertManyIfNewUnit_emptyWithCapacity_list_nil (since := "2025-03-12")]
abbrev insertManyIfNewUnit_empty_list_nil := @insertManyIfNewUnit_emptyWithCapacity_list_nil

@[simp]
theorem insertManyIfNewUnit_emptyWithCapacity_list_singleton {k : α} :
    (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) [k]).1 = emptyWithCapacity.insertIfNew k () := by
  simp

set_option linter.missingDocs false in
@[deprecated insertManyIfNewUnit_emptyWithCapacity_list_singleton (since := "2025-03-12")]
abbrev insertManyIfNewUnit_empty_list_singleton := @insertManyIfNewUnit_emptyWithCapacity_list_singleton

theorem insertManyIfNewUnit_emptyWithCapacity_list_cons {hd : α} {tl : List α} :
    insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) (hd :: tl) =
      (insertManyIfNewUnit (emptyWithCapacity.insertIfNew hd ()) tl).1 := by
  rw [insertManyIfNewUnit_cons]

set_option linter.missingDocs false in
@[deprecated insertManyIfNewUnit_emptyWithCapacity_list_cons (since := "2025-03-12")]
abbrev insertManyIfNewUnit_empty_list_cons := @insertManyIfNewUnit_emptyWithCapacity_list_cons

theorem contains_insertManyIfNewUnit_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1.contains k = l.contains k := by
  simp [contains_insertManyIfNewUnit_list _ Raw.WF.emptyWithCapacity₀]

set_option linter.missingDocs false in
@[deprecated contains_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev contains_insertManyIfNewUnit_empty_list := @contains_insertManyIfNewUnit_emptyWithCapacity_list

theorem getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} (h' : l.contains k = false) :
    getKey? (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k = none := by
  exact getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀
    contains_emptyWithCapacity h'

set_option linter.missingDocs false in
@[deprecated getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false := @getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false

theorem getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k' = some k := by
  exact getKey?_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq
    contains_emptyWithCapacity distinct mem

set_option linter.missingDocs false in
@[deprecated getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey?_insertManyIfNewUnit_empty_list_of_mem := @getKey?_insertManyIfNewUnit_emptyWithCapacity_list_of_mem

theorem getKey_insertManyIfNewUnit_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α}
    {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) {h'} :
    getKey (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k' h' = k := by
  exact getKey_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq
    contains_emptyWithCapacity distinct mem

set_option linter.missingDocs false in
@[deprecated getKey_insertManyIfNewUnit_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey_insertManyIfNewUnit_empty_list_of_mem := @getKey_insertManyIfNewUnit_emptyWithCapacity_list_of_mem

theorem getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k : α}
    (h' : l.contains k = false) :
    getKey! (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k = default := by
  exact getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false _ Raw.WF.emptyWithCapacity₀
    contains_emptyWithCapacity h'

set_option linter.missingDocs false in
@[deprecated getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false := @getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false

theorem getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k' = k := by
  exact getKey!_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq
    contains_emptyWithCapacity distinct mem

set_option linter.missingDocs false in
@[deprecated getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKey!_insertManyIfNewUnit_empty_list_of_mem := @getKey!_insertManyIfNewUnit_emptyWithCapacity_list_of_mem

theorem getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false [EquivBEq α] [LawfulHashable α]
    {l : List α} {k fallback : α}
    (h' : l.contains k = false) :
    getKeyD (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k fallback = fallback := by
  exact getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_contains_eq_false
    _ Raw.WF.emptyWithCapacity₀ contains_emptyWithCapacity h'

set_option linter.missingDocs false in
@[deprecated getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false (since := "2025-03-12")]
abbrev getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false := @getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_contains_eq_false

theorem getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (distinct : l.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1 k' fallback = k := by
  exact getKeyD_insertManyIfNewUnit_list_of_contains_eq_false_of_mem _ Raw.WF.emptyWithCapacity₀ k_beq
    contains_emptyWithCapacity distinct mem

set_option linter.missingDocs false in
@[deprecated getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_mem (since := "2025-03-12")]
abbrev getKeyD_insertManyIfNewUnit_empty_list_of_mem := @getKeyD_insertManyIfNewUnit_emptyWithCapacity_list_of_mem

theorem size_insertManyIfNewUnit_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List α}
    (distinct : l.Pairwise (fun a b => (a == b) = false)) :
    (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1.1.size = l.length := by
  simp [size_insertManyIfNewUnit_list _ Raw.WF.emptyWithCapacity₀ distinct]

set_option linter.missingDocs false in
@[deprecated size_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev size_insertManyIfNewUnit_empty_list := @size_insertManyIfNewUnit_emptyWithCapacity_list

theorem size_insertManyIfNewUnit_emptyWithCapacity_list_le [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1.1.size ≤ l.length := by
  apply Nat.le_trans (size_insertManyIfNewUnit_list_le _ Raw.WF.emptyWithCapacity₀)
  simp

set_option linter.missingDocs false in
@[deprecated size_insertManyIfNewUnit_emptyWithCapacity_list_le (since := "2025-03-12")]
abbrev size_insertManyIfNewUnit_empty_list_le := @size_insertManyIfNewUnit_emptyWithCapacity_list_le

theorem isEmpty_insertManyIfNewUnit_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List α} :
    (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l).1.1.isEmpty = l.isEmpty := by
  rw [isEmpty_insertManyIfNewUnit_list _ Raw.WF.emptyWithCapacity₀]
  simp

set_option linter.missingDocs false in
@[deprecated isEmpty_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev isEmpty_insertManyIfNewUnit_empty_list := @isEmpty_insertManyIfNewUnit_emptyWithCapacity_list

theorem get?_insertManyIfNewUnit_emptyWithCapacity_list [EquivBEq α] [LawfulHashable α]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l) k =
      if l.contains k then some () else none := by
  rw [get?_insertManyIfNewUnit_list _ Raw.WF.emptyWithCapacity₀]
  simp

set_option linter.missingDocs false in
@[deprecated get?_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev get?_insertManyIfNewUnit_empty_list := @get?_insertManyIfNewUnit_emptyWithCapacity_list

theorem get_insertManyIfNewUnit_emptyWithCapacity_list
    {l : List α} {k : α} {h} :
    get (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l) k h = ()  := by
  simp

set_option linter.missingDocs false in
@[deprecated get_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev get_insertManyIfNewUnit_empty_list := @get_insertManyIfNewUnit_emptyWithCapacity_list

theorem get!_insertManyIfNewUnit_emptyWithCapacity_list
    {l : List α} {k : α} :
    get! (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l) k = ()  := by
  simp

set_option linter.missingDocs false in
@[deprecated get!_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev get!_insertManyIfNewUnit_empty_list := @get!_insertManyIfNewUnit_emptyWithCapacity_list

theorem getD_insertManyIfNewUnit_emptyWithCapacity_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit (emptyWithCapacity : Raw₀ α (fun _ => Unit)) l) k fallback = () := by
  simp

set_option linter.missingDocs false in
@[deprecated getD_insertManyIfNewUnit_emptyWithCapacity_list (since := "2025-03-12")]
abbrev getD_insertManyIfNewUnit_empty_list := @getD_insertManyIfNewUnit_emptyWithCapacity_list

end Const

end insertMany

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [LawfulBEq α] (h : m.1.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (m.get? k)).isNone) := by
  simp_to_model [alter, erase, isEmpty, get?] using List.isEmpty_alterKey_eq_isEmpty_eraseKey

@[simp]
theorem isEmpty_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = (((m.1.isEmpty || (m.1.size == 1 && m.contains k))) &&
      (f (m.get? k)).isNone) := by
  simp_to_model [alter, isEmpty, size, contains, get?] using List.isEmpty_alterKey

theorem contains_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' := by
  simp_to_model [alter, contains, get?] using List.containsKey_alterKey

theorem size_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.size =
      if m.contains k ∧ (f (m.get? k)).isNone then
        m.1.size - 1
      else if ¬ m.contains k ∧ (f (m.get? k)).isSome then
        m.1.size + 1
      else
        m.1.size := by
  simp only [Bool.not_eq_true]
  simp_to_model [alter, contains, get?, size] using List.length_alterKey'

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
  simp_to_model [alter, get?] using List.getValueCast?_alterKey

theorem get_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)}
    (hc : (m.alter k f).contains k') :
    (m.alter k f).get k' hc =
      if heq : k == k' then
        haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, if_pos heq] at hc
        cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get <| h'
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        m.get k' h' := by
  simp_to_model [alter, contains, get, get?] using List.getValueCast_alterKey

theorem get_alter_self [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    {hc : (m.alter k f).contains k} :
    haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, beq_self_eq_true] at hc
    (m.alter k f).get k hc = (f (m.get? k)).get h' := by
  simp_to_model [alter, get, get?] using List.getValueCast_alterKey_self

theorem get!_alter [LawfulBEq α] {k k' : α} (h : m.1.WF) [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).get! k' =
      if heq : k == k' then
        (f (m.get? k)).map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' := by
  simp_to_model [alter, get?, get!] using List.getValueCast!_alterKey

theorem getD_alter [LawfulBEq α] {k k' : α} {fallback : β k'} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k' fallback =
      if heq : k == k' then
        f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback := by
  simp_to_model [alter, getD, get?] using List.getValueCastD_alterKey

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
  simp_to_model [alter, getKey?, get?] using List.getKey?_alterKey

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} : (m.alter k f).getKey! k' =
      if k == k' then
        if (f (m.get? k)).isSome then k else default
      else
        m.getKey! k' := by
  simp_to_model [alter, get?, getKey!] using List.getKey!_alterKey

-- Note that in many use cases `getKey_eq` gives a simpler right hand side.
theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} (hc : (m.alter k f).contains k') :
    (m.alter k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        m.getKey k' h' := by
  simp_to_model [alter, getKey, contains] using List.getKey_alterKey

theorem getKeyD_alter [LawfulBEq α] {k k' fallback : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k' fallback =
      if k == k' then
        if (f (m.get? k)).isSome then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [alter, getKeyD, get?] using List.getKeyD_alterKey

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => β))

theorem isEmpty_alter_eq_isEmpty_erase (h : m.1.WF)  {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (Const.get? m k)).isNone) := by
  simp_to_model [Const.alter, erase, isEmpty, Const.get?]
    using List.Const.isEmpty_alterKey_eq_isEmpty_eraseKey

@[simp]
theorem isEmpty_alter (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty = ((m.1.isEmpty || (m.1.size == 1 && m.contains k)) &&
      (f (Const.get? m k)).isNone) := by
  simp_to_model [Const.alter, isEmpty, size, contains, Const.get?] using List.Const.isEmpty_alterKey

theorem contains_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
      if k == k' then
        (f (Const.get? m k)).isSome
      else
        m.contains k' := by
  simp_to_model [Const.alter, Const.get?, contains] using List.Const.containsKey_alterKey

theorem size_alter (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.size =
      if m.contains k ∧ (f (Const.get? m k)).isNone then
        m.1.size - 1
      else if ¬ m.contains k ∧ (f (Const.get? m k)).isSome then
        m.1.size + 1
      else
        m.1.size := by
  simp only [Bool.not_eq_true]
  simp_to_model [Const.alter, size, contains, Const.get?] using List.Const.length_alterKey'

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

theorem size_alter_le_size (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.size ≤ m.1.size + 1 := by
  simp [size_alter, h]
  split <;> try split
  all_goals omega

theorem size_le_size_alter (h : m.1.WF) {k : α} {f : Option β → Option β} :
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
  simp_to_model [Const.alter, Const.get?] using List.Const.getValue?_alterKey

theorem get_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β}
    (hc : (Const.alter m k f).contains k') :
    Const.get (Const.alter m k f) k' hc =
      if heq : k == k' then
        haveI h' : (f (Const.get? m k)).isSome := by rwa [contains_alter _ h, if_pos heq] at hc
        (f (Const.get? m k)).get <| h'
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        Const.get m k' h' := by
  simp_to_model [Const.alter, Const.get, Const.get?] using List.Const.getValue_alterKey

theorem get_alter_self (h : m.1.WF) {k : α} {f : Option β → Option β}
    {hc : (Const.alter m k f).contains k} :
    haveI h' : (f (Const.get? m k)).isSome := by rwa [contains_alter _ h, BEq.refl] at hc
    Const.get (Const.alter m k f) k hc = (f (Const.get? m k)).get h' := by
  simp_to_model [Const.alter, Const.get?, Const.get] using List.Const.getValue_alterKey_self

theorem get!_alter {k k' : α} (h : m.1.WF) [Inhabited β] {f : Option β → Option β} :
    Const.get! (Const.alter m k f) k' =
      if k == k' then
        (f (Const.get? m k)).get!
      else
        Const.get! m k' := by
  simp_to_model [Const.alter, Const.get!, Const.get?] using List.Const.getValue!_alterKey

theorem getD_alter {k k' : α} {fallback : β} (h : m.1.WF) {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k' fallback =
      if k == k' then
        f (Const.get? m k) |>.getD fallback
      else
        Const.getD m k' fallback := by
  simp_to_model [Const.alter, Const.get?, Const.getD] using List.Const.getValueD_alterKey

theorem getD_alter_self {k : α} {fallback : β} (h : m.1.WF) {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k fallback = (f (Const.get? m k)).getD fallback := by
  simp only [h, getD_alter, BEq.refl, reduceIte]

theorem getKey?_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then some k else none
      else
        m.getKey? k' := by
  simp_to_model [Const.alter, Const.get?, getKey?] using List.Const.getKey?_alterKey

theorem getKey!_alter [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option β → Option β} :
    (Const.alter m k f).getKey! k' =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else default
      else
        m.getKey! k' := by
  simp_to_model [Const.alter, Const.get?, getKey!] using List.Const.getKey!_alterKey

theorem getKey_alter [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option β → Option β}
    (hc : (Const.alter m k f).contains k') :
    (Const.alter m k f).getKey k' hc =
      if heq : k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
        m.getKey k' h' := by
  simp_to_model [Const.alter, Const.get?, getKey] using List.Const.getKey_alterKey

theorem getKeyD_alter {k k' fallback : α} (h : m.1.WF) {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k' fallback =
      if k == k' then
        if (f (Const.get? m k)).isSome then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [Const.alter, Const.get?, getKeyD] using List.Const.getKeyD_alterKey

end Const

end Alter

section Modify

variable [LawfulBEq α]

@[simp]
theorem isEmpty_modify (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model [modify, isEmpty] using List.isEmpty_modifyKey

theorem contains_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' := by
  simp_to_model [modify, contains] using List.containsKey_modifyKey

theorem size_modify (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).1.size = m.1.size := by
  simp_to_model [modify, size] using List.length_modifyKey

theorem get?_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).get? k' =
      if h : k == k' then
        (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f))
      else
        m.get? k' := by
  simp_to_model [modify, get?] using List.getValueCast?_modifyKey

@[simp]
theorem get?_modify_self (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).get? k = (m.get? k).map f := by
  simp_to_model [modify, get?] using List.getValueCast?_modifyKey_self

theorem get_modify (h : m.1.WF) {k k' : α} {f : β k → β k}
    (hc : (m.modify k f).contains k') :
    (m.modify k f).get k' hc =
      if heq : k == k' then
        haveI h' : m.contains k := by rwa [contains_modify _ h, ← eq_of_beq heq] at hc
        cast (congrArg β (eq_of_beq heq)) <| f (m.get k h')
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        m.get k' h' := by
  simp_to_model [modify, contains, get] using List.getValueCast_modifyKey

@[simp]
theorem get_modify_self (h : m.1.WF) {k : α} {f : β k → β k} {hc : (m.modify k f).contains k} :
    haveI h' : m.contains k := by rwa [contains_modify _ h] at hc
    (m.modify k f).get k hc = f (m.get k h') := by
  simp_to_model [modify, get] using List.getValueCast_modifyKey_self

theorem get!_modify (h : m.1.WF) {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (m.modify k f).get! k' =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        m.get! k' := by
  simp_to_model [modify, get!, get?] using List.getValueCast!_modifyKey

@[simp]
theorem get!_modify_self (h : m.1.WF) {k : α} [Inhabited (β k)] {f : β k → β k} :
    (m.modify k f).get! k = ((m.get? k).map f).get! := by
  simp_to_model [modify, get!, get?] using List.getValueCast!_modifyKey_self

theorem getD_modify (h : m.1.WF) {k k' : α} {fallback : β k'} {f : β k → β k} :
    (m.modify k f).getD k' fallback =
      if heq : k == k' then
        m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        m.getD k' fallback := by
  simp_to_model [modify, getD, get?] using List.getValueCastD_modifyKey

@[simp]
theorem getD_modify_self (h : m.1.WF) {k : α} {fallback : β k} {f : β k → β k} :
    (m.modify k f).getD k fallback = ((m.get? k).map f).getD fallback := by
  simp_to_model [modify, get?, getD] using List.getValueCastD_modifyKey_self

theorem getKey?_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey? k' =
      if k == k' then
        if m.contains k then some k else none
      else
        m.getKey? k' := by
  simp_to_model [modify, getKey?, contains] using List.getKey?_modifyKey

theorem getKey?_modify_self (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).getKey? k = if m.contains k then some k else none := by
  simp_to_model [modify, getKey?, contains] using List.getKey?_modifyKey_self

theorem getKey!_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey! k' =
      if k == k' then
        if m.contains k then k else default
      else
        m.getKey! k' := by
  simp_to_model [modify, getKey!, contains] using List.getKey!_modifyKey

theorem getKey!_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey! k = if m.contains k then k else default := by
  simp_to_model [modify, getKey!, contains] using List.getKey!_modifyKey_self

theorem getKey_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β k → β k}
    (hc : (m.modify k f).contains k') :
    (m.modify k f).getKey k' hc =
      if k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        m.getKey k' h' := by
  simp_to_model [modify, contains, getKey] using List.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β k → β k}
    (hc : (m.modify k f).contains k) : (m.modify k f).getKey k hc = k := by
  simp_to_model [modify, contains, getKey] using List.getKey_modifyKey_self

theorem getKeyD_modify (h : m.1.WF) {k k' fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k' fallback =
      if k == k' then
        if m.contains k then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [modify, getKeyD, contains] using List.getKeyD_modifyKey

theorem getKeyD_modify_self (h : m.1.WF) [Inhabited α] {k fallback : α} {f : β k → β k} :
    (m.modify k f).getKeyD k fallback = if m.contains k then k else fallback := by
  simp_to_model [modify, getKeyD, contains] using List.getKeyD_modifyKey_self

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => β))
omit [LawfulBEq α]

@[simp]
theorem isEmpty_modify (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model [Const.modify, isEmpty] using List.Const.isEmpty_modifyKey

theorem contains_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' := by
  simp_to_model [Const.modify, contains] using List.Const.containsKey_modifyKey

theorem size_modify (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.size = m.1.size := by
  simp_to_model [Const.modify, size] using List.Const.length_modifyKey

theorem get?_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    Const.get? (Const.modify m k f) k' =
      if k == k' then
        (Const.get? m k).map f
      else
        Const.get? m k' := by
  simp_to_model [Const.modify, Const.get?] using List.Const.getValue?_modifyKey

@[simp]
theorem get?_modify_self (h : m.1.WF) {k : α} {f : β → β} :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f := by
  simp_to_model [Const.modify, Const.get?] using List.Const.getValue?_modifyKey_self

theorem get_modify (h : m.1.WF) {k k' : α} {f : β → β}
    (hc : (Const.modify m k f).contains k') :
    Const.get (Const.modify m k f) k' hc =
      if heq : k == k' then
        haveI h' : m.contains k := by rwa [contains_modify _ h, ← contains_congr _ h heq] at hc
        f (Const.get m k h')
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        Const.get m k' h' := by
  simp_to_model [Const.modify, Const.get] using List.Const.getValue_modifyKey

@[simp]
theorem get_modify_self (h : m.1.WF) {k : α} {f : β → β} {hc : (Const.modify m k f).contains k} :
    haveI h' : m.contains k := by rwa [contains_modify _ h] at hc
    Const.get (Const.modify m k f) k hc = f (Const.get m k h') := by
  simp_to_model [Const.modify, Const.get] using List.Const.getValue_modifyKey_self

theorem get!_modify (h : m.1.WF) {k k' : α} [hi : Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k' =
      if k == k' then
        Const.get? m k |>.map f |>.get!
      else
        Const.get! m k' := by
  simp_to_model [Const.modify, Const.get?, Const.get!] using List.Const.getValue!_modifyKey

@[simp]
theorem get!_modify_self (h : m.1.WF) {k : α} [Inhabited (β)] {f : β → β} :
    Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! := by
  simp_to_model [Const.modify, Const.get!, Const.get?] using List.Const.getValue!_modifyKey_self

theorem getD_modify (h : m.1.WF) {k k' : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k' fallback =
      if k == k' then
        Const.get? m k |>.map f |>.getD fallback
      else
        Const.getD m k' fallback := by
  simp_to_model [Const.modify, Const.get?, Const.getD] using List.Const.getValueD_modifyKey

@[simp]
theorem getD_modify_self (h : m.1.WF) {k : α} {fallback : β} {f : β → β} :
    Const.getD (Const.modify m k f) k fallback = ((Const.get? m k).map f).getD fallback := by
  simp_to_model [Const.modify, Const.getD, Const.get?] using List.Const.getValueD_modifyKey_self

theorem getKey?_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey? k' =
      if k == k' then
        if m.contains k then some k else none
      else
        m.getKey? k' := by
  simp_to_model [Const.modify, contains, getKey?] using List.Const.getKey?_modifyKey

theorem getKey?_modify_self (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).getKey? k = if m.contains k then some k else none := by
  simp_to_model [Const.modify, contains, getKey?] using List.Const.getKey?_modifyKey_self

theorem getKey!_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey! k' =
      if k == k' then
        if m.contains k then k else default
      else
        m.getKey! k' := by
  simp_to_model [Const.modify, contains, getKey!] using List.Const.getKey!_modifyKey

theorem getKey!_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey! k = if m.contains k then k else default := by
  simp_to_model [Const.modify, contains, getKey!] using List.Const.getKey!_modifyKey_self

theorem getKey_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β → β}
    (hc : (Const.modify m k f).contains k') :
    (Const.modify m k f).getKey k' hc =
      if k == k' then
        k
      else
        haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
        m.getKey k' h' := by
  simp_to_model [Const.modify, getKey] using List.Const.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β → β}
    (hc : (Const.modify m k f).contains k) : (Const.modify m k f).getKey k hc = k := by
  simp_to_model [Const.modify, getKey] using List.Const.getKey_modifyKey_self

theorem getKeyD_modify (h : m.1.WF) {k k' fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k' fallback =
      if k == k' then
        if m.contains k then k else fallback
      else
        m.getKeyD k' fallback := by
  simp_to_model [Const.modify, getKeyD, contains] using List.Const.getKeyD_modifyKey

theorem getKeyD_modify_self (h : m.1.WF) [Inhabited α] {k fallback : α} {f : β → β} :
    (Const.modify m k f).getKeyD k fallback = if m.contains k then k else fallback := by
  simp_to_model [Const.modify, getKeyD, contains] using List.Const.getKeyD_modifyKey_self

end Const

end Modify

section Equiv

open scoped DHashMap.Raw

section Raw

-- these lemmas work without any instance or well-formedness assumptions

variable {α : Type u}
variable {β : α → Type v} (m₁ m₂ : Raw α β)

theorem equiv_iff_toList_perm_toList : m₁ ~m m₂ ↔ m₁.toList.Perm m₂.toList := by
  simp_to_model [toList, Equiv]

theorem keys_perm_keys_of_equiv (h : m₁ ~m m₂) : m₁.keys.Perm m₂.keys := by
  simp_to_model [keys]
  simp only [List.keys_eq_map]
  exact h.1.map _

variable (m₁ m₂ : Raw₀ α β)

theorem filter_equiv_congr (h : m₁.1 ~m m₂.1) {f : (a : α) → β a → Bool} :
    (m₁.filter f).1 ~m (m₂.filter f).1 := by
  simp_to_model [filter, Equiv] using h.1.filter _

theorem map_equiv_congr {γ : α → Type w} (m₁ m₂ : Raw₀ α β) (h : m₁.1 ~m m₂.1)
    {f : (a : α) → β a → γ a} : (m₁.map f).1 ~m (m₂.map f).1 := by
  simp_to_model [map, Equiv] using h.1.map _

theorem filterMap_equiv_congr {γ : α → Type w} (h : m₁.1 ~m m₂.1)
    {f : (a : α) → β a → Option (γ a)} : (m₁.filterMap f).1 ~m (m₂.filterMap f).1 := by
  simp_to_model [filterMap, Equiv] using h.1.filterMap _

namespace Const

theorem equiv_iff_toList_perm_toList {β : Type v} (m₁ m₂ : Raw α fun _ => β) :
    m₁ ~m m₂ ↔ (Raw.Const.toList m₁).Perm (Raw.Const.toList m₂) := by
  simp_to_model [Const.toList, Equiv]
  constructor
  · exact List.Perm.map _
  · intro h
    have := h.map (fun (x, y) => (⟨x, y⟩ : (_ : α) × β))
    simpa only [List.map_map, Function.comp_def, List.map_id'] using this

theorem equiv_iff_keys_perm_keys (m₁ m₂ : Raw α fun _ => Unit) :
    m₁ ~m m₂ ↔ m₁.keys.Perm m₂.keys := by
  simp_to_model [keys, Equiv]
  simp only [List.keys_eq_map]
  constructor
  · exact List.Perm.map _
  · intro h
    have := h.map (fun x => (⟨x, ()⟩ : (_ : α) × Unit))
    simpa only [List.map_map, Function.comp_def, List.map_id'] using this

end Const

end Raw

variable (m₁ m₂ : Raw₀ α β)

theorem equiv_emptyWithCapacity_iff_isEmpty [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {c : Nat} :
    m.1 ~m (emptyWithCapacity c).1 ↔ m.1.isEmpty := by
  simp_to_model [Equiv, isEmpty]
  simp only [toListModel_buckets_emptyWithCapacity, List.perm_nil, List.isEmpty_iff]

set_option linter.missingDocs false in
@[deprecated equiv_emptyWithCapacity_iff_isEmpty (since := "2025-03-12")]
abbrev equiv_empty_iff_isEmpty := @equiv_emptyWithCapacity_iff_isEmpty

theorem isEmpty_eq_of_equiv [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) :
    m₁.1.isEmpty = m₂.1.isEmpty := by
  simp_to_model [isEmpty] using List.Perm.isEmpty_eq h.1

theorem contains_eq_of_equiv [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k : α} :
    m₁.contains k = m₂.contains k := by
  simp_to_model [contains] using List.containsKey_of_perm h.1

theorem size_eq_of_equiv [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) :
    m₁.1.size = m₂.1.size := by
  simp_to_model [size] using List.Perm.length_eq h.1

theorem get?_eq_of_equiv [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k : α} :
    m₁.get? k = m₂.get? k := by
  simp_to_model [get?] using List.getValueCast?_of_perm _ h.1

theorem get_eq_of_equiv [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} (h' : m₁.contains k) :
    m₁.get k h' = m₂.get k ((contains_eq_of_equiv _ _ h₁ h₂ h).symm.trans h') := by
  simp_to_model [get] using List.getValueCast_of_perm _ h.1

theorem get!_eq_of_equiv [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} [Inhabited (β k)] : m₁.get! k = m₂.get! k := by
  simp_to_model [get!] using List.getValueCast!_of_perm _ h.1

theorem getD_eq_of_equiv [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} {fallback : β k} : m₁.getD k fallback = m₂.getD k fallback := by
  simp_to_model [getD] using List.getValueCastD_of_perm _ h.1

theorem getKey?_eq_of_equiv [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k : α} :
    m₁.getKey? k = m₂.getKey? k := by
  simp_to_model [getKey?] using List.getKey?_of_perm _ h.1

theorem getKey_eq_of_equiv [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k : α} (h' : m₁.contains k) :
    m₁.getKey k h' = m₂.getKey k ((contains_eq_of_equiv _ _ h₁ h₂ h).symm.trans h') := by
  simp_to_model [getKey] using List.getKey_of_perm _ h.1

theorem getKey!_eq_of_equiv [EquivBEq α] [LawfulHashable α] [Inhabited α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k : α} :
    m₁.getKey! k = m₂.getKey! k := by
  simp_to_model [getKey!] using List.getKey!_of_perm _ h.1

theorem getKeyD_eq_of_equiv [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k fallback : α} :
    m₁.getKeyD k fallback = m₂.getKeyD k fallback := by
  simp_to_model [getKeyD] using List.getKeyD_of_perm _ h.1

theorem insert_equiv_congr [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} {v : β k} : (m₁.insert k v).1 ~m (m₂.insert k v).1 := by
  simp_to_model [Equiv, insert] using List.insertEntry_of_perm _ h.1

theorem erase_equiv_congr [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} : (m₁.erase k).1 ~m (m₂.erase k).1 := by
  simp_to_model [Equiv, erase] using List.eraseKey_of_perm _ h.1

theorem insertIfNew_equiv_congr [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} {v : β k} : (m₁.insertIfNew k v).1 ~m (m₂.insertIfNew k v).1 := by
  simp_to_model [Equiv, insertIfNew] using List.insertEntryIfNew_of_perm _ h.1

theorem insertMany_list_equiv_congr [EquivBEq α] [LawfulHashable α]
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {l : List ((a : α) × β a)} :
    (m₁.insertMany l).1.1 ~m (m₂.insertMany l).1.1 := by
  simp_to_model [Equiv, insertMany] using List.insertList_perm_of_perm_first h.1

theorem alter_equiv_congr [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} (f : Option (β k) → Option (β k)) : (m₁.alter k f).1 ~m (m₂.alter k f).1 := by
  simp_to_model [Equiv, alter] using List.alterKey_of_perm _ h.1

theorem modify_equiv_congr [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} (f : β k → β k) : (m₁.modify k f).1 ~m (m₂.modify k f).1 := by
  simp_to_model [Equiv, modify] using List.modifyKey_of_perm _ h.1

theorem equiv_of_forall_get?_eq [LawfulBEq α] (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) :
    (∀ k, m₁.get? k = m₂.get? k) → m₁.1 ~m m₂.1 := by
  simp_to_model [get?, Equiv] using List.getValueCast?_ext

namespace Const

variable {β : Type v} (m₁ m₂ : Raw₀ α fun _ => β)
variable [EquivBEq α] [LawfulHashable α]

theorem get?_eq_of_equiv (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {k : α} :
    get? m₁ k = get? m₂ k := by
  simp_to_model [Const.get?] using List.getValue?_of_perm _ h.1

theorem get_eq_of_equiv (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} (h' : m₁.contains k) :
    get m₁ k h' = get m₂ k ((contains_eq_of_equiv _ _ h₁ h₂ h).symm.trans h') := by
  simp_to_model [Const.get] using List.getValue_of_perm _ h.1

theorem get!_eq_of_equiv (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} [Inhabited β] : get! m₁ k = get! m₂ k := by
  simp_to_model [Const.get!] using List.getValue!_of_perm _ h.1

theorem getD_eq_of_equiv (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} {fallback : β} : getD m₁ k fallback = getD m₂ k fallback := by
  simp_to_model [Const.getD] using List.getValueD_of_perm _ h.1

theorem insertMany_list_equiv_congr (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {l : List (α × β)} : (insertMany m₁ l).1.1 ~m (insertMany m₂ l).1.1 := by
  simp_to_model [Equiv, Const.insertMany] using List.insertList_perm_of_perm_first h.1

theorem insertManyIfNewUnit_list_equiv_congr {m₁ m₂ : Raw₀ α fun _ => Unit}
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1) {l : List α} :
    (insertManyIfNewUnit m₁ l).1.1 ~m (insertManyIfNewUnit m₂ l).1.1 := by
  simp_to_model [Equiv, Const.insertManyIfNewUnit]
    using List.insertListIfNewUnit_perm_of_perm_first h.1

theorem alter_equiv_congr (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} (f : Option β → Option β) : (alter m₁ k f).1 ~m (alter m₂ k f).1 := by
  simp_to_model [Equiv, Const.alter] using List.Const.alterKey_of_perm _ h.1

theorem modify_equiv_congr (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) (h : m₁.1 ~m m₂.1)
    {k : α} (f : β → β) : (modify m₁ k f).1 ~m (modify m₂ k f).1 := by
  simp_to_model [Equiv, Const.modify] using List.Const.modifyKey_of_perm _ h.1

theorem equiv_of_forall_getKey_eq_of_forall_get?_eq (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) :
    (∀ k hk hk', m₁.getKey k hk = m₂.getKey k hk') → (∀ k, get? m₁ k = get? m₂ k) → m₁.1 ~m m₂.1 := by
  simp_to_model [getKey, Const.get?, contains, Equiv] using List.getKey_getValue?_ext

@[deprecated equiv_of_forall_getKey_eq_of_forall_get?_eq (since := "2025-04-25")]
theorem equiv_of_forall_getKey?_eq_of_forall_get?_eq (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) :
    (∀ k, m₁.getKey? k = m₂.getKey? k) → (∀ k, get? m₁ k = get? m₂ k) → m₁.1 ~m m₂.1 := by
  simp_to_model [getKey?, Const.get?, Equiv] using List.getKey?_getValue?_ext

theorem equiv_of_forall_get?_eq {α : Type u} [BEq α] [Hashable α] [LawfulBEq α]
    {m₁ m₂ : Raw₀ α fun _ => β} (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) :
    (∀ k, get? m₁ k = get? m₂ k) → m₁.1 ~m m₂.1 := by
  simpa only [Const.get?_eq_get?, h₁, h₂] using Raw₀.equiv_of_forall_get?_eq m₁ m₂ h₁ h₂

theorem equiv_of_forall_getKey?_unit_eq {m₁ m₂ : Raw₀ α fun _ => Unit}
    (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) : (∀ k, m₁.getKey? k = m₂.getKey? k) → m₁.1 ~m m₂.1 := by
  simp_to_model [getKey?, Equiv] using List.getKey?_ext

theorem equiv_of_forall_contains_unit_eq {α : Type u} [BEq α] [Hashable α] [LawfulBEq α]
    {m₁ m₂ : Raw₀ α fun _ => Unit} (h₁ : m₁.1.WF) (h₂ : m₂.1.WF) :
    (∀ k, m₁.contains k = m₂.contains k) → m₁.1 ~m m₂.1 := by
  simp_to_model [contains, Equiv] using List.containsKey_ext

end Const

end Equiv

section filterMap

section raw

variable {α : Type u} {β : α → Type v} {γ : α → Type w} (m : Raw₀ α β)

theorem toList_filterMap {f : (a : α) → β a → Option (γ a)} :
    (m.filterMap f).1.toList.Perm
      (m.1.toList.filterMap (fun p => (f p.1 p.2).map (fun x => ⟨p.1, x⟩))) := by
  simp_to_model [filterMap, toList, Equiv] using List.Perm.rfl

end raw

variable {γ : α → Type w}

theorem isEmpty_filterMap_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} (h : m.1.WF) :
    (m.filterMap f).1.isEmpty = true ↔
      ∀ (k : α) (h : m.contains k = true), f k (m.get k h) = none := by
  simp_to_model [filterMap, isEmpty, contains, get] using List.isEmpty_filterMap_eq_true

theorem isEmpty_filterMap_eq_false_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} (h : m.1.WF) :
    (m.filterMap f).1.isEmpty = false ↔
      ∃ (k : α) (h : m.contains k = true), (f k (m.get k h)).isSome := by
  simp_to_model [filterMap, isEmpty, contains, get] using List.isEmpty_filterMap_eq_false

theorem contains_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) :
    (m.filterMap f).contains k = (m.get? k).any (f k · |>.isSome) := by
  simp_to_model [filterMap, contains, get?] using List.containsKey_filterMap

theorem contains_of_contains_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) :
    (m.filterMap f).contains k = true → m.contains k = true := by
  simp_to_model [filterMap, contains] using containsKey_of_containsKey_filterMap

theorem size_filterMap_le_size [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} (h : m.1.WF) :
    (m.filterMap f).1.size ≤ m.1.size := by
  simp_to_model [filterMap, size] using List.length_filterMap_le

theorem size_filterMap_eq_size_iff [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} (h : m.1.WF) :
    (m.filterMap f).1.size = m.1.size ↔ ∀ (a : α) (h : m.contains a), (f a (m.get a h)).isSome := by
  simp_to_model [filterMap, size, contains, get] using List.length_filterMap_eq_length_iff

theorem get?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) :
    (m.filterMap f).get? k = (m.get? k).bind (f k) := by
  simp_to_model [filterMap, get?] using List.getValueCast?_filterMap

theorem isSome_apply_of_contains_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) :
    ∀ (h' : (m.filterMap f).contains k = true),
      (f k (m.get k (contains_of_contains_filterMap m h h'))).isSome := by
  simp_to_model [filterMap, contains, get] using List.isSome_apply_of_containsKey_filterMap

theorem get_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) {h'} :
    (m.filterMap f).get k h' =
      (f k (m.get k (contains_of_contains_filterMap m h h'))).get
        (isSome_apply_of_contains_filterMap m h h') := by
  simp_to_model [filterMap, get] using List.getValueCast_filterMap

theorem get!_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} [Inhabited (γ k)] (h : m.1.WF) :
    (m.filterMap f).get! k = ((m.get? k).bind (f k)).get! := by
  simp_to_model [filterMap, get!, get?] using List.getValueCast!_filterMap

theorem getD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} {fallback : γ k} (h : m.1.WF) :
    (m.filterMap f).getD k fallback = ((m.get? k).bind (f k)).getD fallback := by
  simp_to_model [filterMap, getD, get?] using List.getValueCastD_filterMap

theorem getKey?_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (contains_of_getKey?_eq_some m h h'))).isSome) := by
  simp_to_model [filterMap, getKey?, get] using List.getKey?_filterMap

theorem getKey_filterMap [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) {h'}:
    (m.filterMap f).getKey k h' = m.getKey k (contains_of_contains_filterMap m h h') := by
  simp_to_model [filterMap, getKey] using List.getKey_filterMap

theorem getKey!_filterMap [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Option (γ a)} {k : α} (h : m.1.WF) :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (contains_of_getKey?_eq_some m h h'))).isSome)).get! := by
  simp_to_model [filterMap, getKey!, getKey?, get] using List.getKey!_filterMap

theorem getKeyD_filterMap [LawfulBEq α]
    {f : (a : α) → β a → Option (γ a)} {k fallback : α} (h : m.1.WF) :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (m.get x (contains_of_getKey?_eq_some m h h'))).isSome)).getD fallback := by
  simp_to_model [filterMap, getKeyD, getKey?, get] using List.getKeyD_filterMap

namespace Const

variable {β : Type v} {γ : Type w} (m : Raw₀ α (fun _ => β))

theorem isEmpty_filterMap_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.1.WF) :
    (m.filterMap f).1.isEmpty = true ↔
      ∀ (k : α) (h : m.contains k = true), f (m.getKey k h) (Const.get m k h) = none := by
  simp_to_model [filterMap, isEmpty, contains, getKey, Const.get] using List.Const.isEmpty_filterMap_eq_true

theorem isEmpty_filterMap_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.1.WF) :
    (m.filterMap f).1.isEmpty = false ↔
      ∃ (k : α) (h : m.contains k = true), (f (m.getKey k h) (Const.get m k h)).isSome := by
  simp_to_model [filterMap, isEmpty, contains, getKey, Const.get] using List.Const.isEmpty_filterMap_eq_false

theorem contains_filterMap_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) :
    (m.filterMap f).contains k = true ↔ ∃ (h' : m.contains k = true),
      (f (m.getKey k h') (Const.get m k h')).isSome := by
  simp_to_model [filterMap, contains, getKey, Const.get] using List.Const.containsKey_filterMap_iff

theorem size_filterMap_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} (h : m.1.WF) :
    (m.filterMap f).1.size = m.1.size ↔ ∀ (a : α) (h : m.contains a),
      (f (m.getKey a h) (Const.get m a h)).isSome := by
  simp_to_model [filterMap, size, getKey, contains, Const.get] using List.Const.length_filterMap_eq_length_iff

theorem get?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) :
    Const.get? (m.filterMap f) k = (Const.get? m k).pbind (fun x h' =>
      f (m.getKey k ((contains_eq_isSome_get? m h).trans (Option.isSome_of_eq_some h'))) x) := by
  simp_to_model [filterMap, getKey, Const.get?] using List.Const.getValue?_filterMap

theorem get?_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} (h : m.1.WF) :
    m.getKey? k = some k' → Const.get? (m.filterMap f) k = (Const.get? m k).bind
      fun x => f k' x := by
  simp_to_model [filterMap, getKey?, Const.get?]
    using List.Const.getValue?_filterMap_of_getKey?_eq_some

theorem isSome_apply_of_contains_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) :
    ∀ (h' : (m.filterMap f).contains k = true),
      (f (m.getKey k (contains_of_contains_filterMap m h h'))
        (Const.get m k (contains_of_contains_filterMap m h h'))).isSome := by
  simp_to_model [filterMap, getKey, Const.get, contains] using List.Const.isSome_apply_of_containsKey_filterMap

theorem get_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) {h'} :
    Const.get (m.filterMap f) k h' =
      (f (m.getKey k (contains_of_contains_filterMap m h h'))
        (Const.get m k (contains_of_contains_filterMap m h h'))).get
          (isSome_apply_of_contains_filterMap m h h') := by
  simp_to_model [filterMap, getKey, Const.get] using List.getValue_filterMap

theorem get!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) :
    Const.get! (m.filterMap f) k =
      ((Const.get? m k).pbind (fun x h' =>
      f (m.getKey k ((contains_eq_isSome_get? m h).trans (Option.isSome_of_eq_some h'))) x)).get! := by
  simp_to_model [filterMap, Const.get!, getKey, Const.get?] using List.Const.getValue!_filterMap

theorem get!_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : m.1.WF) :
    m.getKey? k = some k' → Const.get! (m.filterMap f) k = ((Const.get? m k).bind
      fun x => f k' x).get! := by
  simp_to_model [filterMap, getKey?, Const.get?, Const.get!]
    using List.Const.getValue!_filterMap_of_getKey?_eq_some

theorem getD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} {fallback : γ} (h : m.1.WF) :
    Const.getD (m.filterMap f) k fallback =
      ((Const.get? m k).pbind (fun x h' =>
      f (m.getKey k ((contains_eq_isSome_get? m h).trans (Option.isSome_of_eq_some h'))) x)).getD fallback := by
  simp_to_model [filterMap, Const.getD, getKey, Const.get?] using List.Const.getValueD_filterMap

theorem getD_filterMap_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.1.WF) :
    m.getKey? k = some k' → Const.getD (m.filterMap f) k fallback = ((Const.get? m k).bind
      fun x => f k' x).getD fallback := by
  simp_to_model [filterMap, getKey?, Const.get?, Const.getD]
    using List.Const.getValueD_filterMap_of_getKey?_eq_some

theorem toList_filterMap {α : Type u} (m : Raw₀ α fun _ => β)
    {f : α → β → Option γ} :
    (Raw.Const.toList (m.filterMap f).1).Perm
      ((Raw.Const.toList m.1).filterMap (fun p => (f p.1 p.2).map (fun x => ⟨p.1, x⟩))) := by
  simp_to_model [Const.toList, filterMap]
  simp only [List.map_filterMap, List.filterMap_map, Function.comp_def, Option.map_map]
  rfl

theorem getKey?_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) :
    (m.filterMap f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (contains_of_getKey?_eq_some m h h'))).isSome) := by
  simp_to_model [filterMap, Const.get, getKey?] using List.Const.getKey?_filterMap

theorem getKey!_filterMap [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Option γ} {k : α} (h : m.1.WF) :
    (m.filterMap f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (contains_of_getKey?_eq_some m h h'))).isSome)).get! := by
  simp_to_model [filterMap, Const.get, getKey?, getKey!] using List.Const.getKey!_filterMap

theorem getKeyD_filterMap [EquivBEq α] [LawfulHashable α]
    {f : α → β → Option γ} {k fallback : α} (h : m.1.WF) :
    (m.filterMap f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (contains_of_getKey?_eq_some m h h'))).isSome)).getD fallback := by
  simp_to_model [filterMap, Const.get, getKey?, getKeyD] using List.Const.getKeyD_filterMap

end Const

end filterMap

section filter

section raw

variable {α : Type u} {β : α → Type v} (m : Raw₀ α β)

theorem filterMap_equiv_filter {f : (a : α) → β a → Bool} :
    (m.filterMap (fun k => Option.guard (fun v => f k v))).1.Equiv (m.filter f).1 := by
  rw [filterMap_eq_filter]
  exact ⟨.rfl⟩

theorem toList_filter
    {f : (a : α) → β a → Bool} :
    (m.filter f).1.toList.Perm (m.1.toList.filter (fun p => f p.1 p.2)) := by
  simp_to_model [filter, toList, Equiv] using List.Perm.rfl

theorem keys_filter_key {f : α → Bool} :
    (m.filter fun k _ => f k).1.keys.Perm (m.1.keys.filter f) := by
  simp_to_model [keys, filter]
  simp only [List.keys_eq_map, List.filter_map, Function.comp_def, List.Perm.rfl]

end raw

theorem isEmpty_filter_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} (h : m.1.WF) :
    (m.filter f).1.isEmpty = true ↔
      ∀ (k : α) (h : m.contains k = true), f k (m.get k h) = false := by
  simp_to_model [filter, contains, get, isEmpty] using List.isEmpty_filter_eq_true

theorem isEmpty_filter_eq_false_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} (h : m.1.WF) :
    (m.filter f).1.isEmpty = false ↔
      ∃ (k : α) (h : m.contains k = true), f k (m.get k h) = true := by
  simp_to_model [filter, contains, get, isEmpty] using List.isEmpty_filter_eq_false

theorem isEmpty_filter_key_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.1.WF) :
    (m.filter (fun a _ => f a)).1.isEmpty ↔
      ∀ (k : α) (h : m.contains k), f (m.getKey k h) = false := by
  simp_to_model [filter, contains, getKey, isEmpty] using List.isEmpty_filter_key_iff

theorem isEmpty_filter_key_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.1.WF) :
    (m.filter (fun a _ => f a)).1.isEmpty = false ↔
      ∃ (k : α) (h : m.contains k = true), f (m.getKey k h) := by
  rw [← Bool.not_eq_true, isEmpty_filter_key_iff m h]
  simp only [Classical.not_forall, Bool.not_eq_false]

theorem contains_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).contains k = (m.get? k).any (f k) := by
  simp_to_model [filter, contains, get?] using List.containsKey_filter

theorem contains_filter_key_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} (h : m.1.WF) :
    (m.filter (fun a _ => f a)).contains k ↔ ∃ h : m.contains k, f (m.getKey k h) := by
  simp_to_model [filter, contains, getKey] using List.containsKey_filter_key

theorem contains_of_contains_filter [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).contains k = true → m.contains k = true := by
  simp_to_model [filter, contains] using containsKey_of_containsKey_filter

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} (h : m.1.WF) :
    (m.filter f).1.size ≤ m.1.size := by
  simp_to_model [filter, size] using List.length_filter_le

theorem size_filter_eq_size_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} (h : m.1.WF) :
    (m.filter f).1.size = m.1.size ↔ ∀ (a : α) (h : m.contains a), (f a (m.get a h)) = true := by
  simp_to_model [filter, size, contains, get] using Internal.List.length_filter_eq_length_iff

theorem filter_equiv_self_iff [LawfulBEq α]
    {f : (a : α) → β a → Bool} (h : m.1.WF) :
    (m.filter f).1.Equiv m.1 ↔ ∀ (a : α) (h : m.contains a), (f a (m.get a h)) = true := by
  simp_to_model [filter, Equiv, contains, get] using List.perm_filter_self_iff_forall_containsKey

theorem filter_key_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → Bool} (h : m.1.WF) :
    (m.filter fun k _ => f k).1.Equiv m.1 ↔ ∀ (a : α) (h : m.contains a), f (m.getKey a h) = true := by
  simp_to_model [filter, Equiv, contains, getKey] using List.perm_filter_key_self_iff_forall_containsKey

theorem size_filter_key_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} (h : m.1.WF) :
    (m.filter fun k _ => f k).1.size = m.1.size ↔ ∀ (k : α) (h : m.contains k), f (m.getKey k h) := by
  simp_to_model [filter, size, contains, getKey] using List.length_filter_key_eq_length_iff

theorem get?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).get? k = (m.get? k).filter (f k) := by
  simp_to_model [filter, get?] using List.getValueCast?_filter

theorem get_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) {h'} :
    (m.filter f).get k h' =
      m.get k (contains_of_contains_filter m h h') := by
  simp_to_model [filter, get] using List.getValueCast_filter

theorem get!_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} [Inhabited (β k)] (h : m.1.WF) :
    (m.filter f).get! k = ((m.get? k).filter (f k)).get! := by
  simp_to_model [filter, get!, get?] using List.getValueCast!_filter

theorem getD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} {fallback : β k} (h : m.1.WF) :
    (m.filter f).getD k fallback = ((m.get? k).filter (f k)).getD fallback := by
  simp_to_model [filter, getD, get?] using List.getValueCastD_filter

theorem keys_filter [LawfulBEq α] {f : (a : α) → β a → Bool} (h : m.1.WF) :
    (m.filter f).1.keys.Perm
      (m.1.keys.attach.filter (fun ⟨x, h'⟩ => f x (m.get x (contains_of_mem_keys m h h')))).unattach := by
  simp_to_model [keys, filter, Equiv, get]
  rw [List.attach_congr Raw.keys_eq_keys_toListModel]
  rw [List.keys_filter (Raw.WF.out h).distinct]
  simp only [List.filter_map, Function.comp_def, List.unattach, List.map_map]
  rfl

theorem getKey?_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (contains_of_getKey?_eq_some m h h'))) := by
  simp_to_model [filter, getKey?, get] using List.getKey?_filter

theorem getKey?_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k : α} (h : m.1.WF) :
    (m.filter fun k _ => f k).getKey? k = (m.getKey? k).filter f := by
  simp_to_model [filter, getKey?, get] using List.getKey?_filter_key

theorem getKey_filter [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) {h'}:
    (m.filter f).getKey k h' = m.getKey k (contains_of_contains_filter m h h') := by
  simp_to_model [filter, getKey] using List.getKey_filter

theorem getKey!_filter [LawfulBEq α] [Inhabited α]
    {f : (a : α) → β a → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (contains_of_getKey?_eq_some m h h')))).get! := by
  simp_to_model [filter, getKey?, get, getKey!] using List.getKey!_filter

theorem getKey!_filter_key [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → Bool} {k : α} (h : m.1.WF) :
    (m.filter fun k _ => f k).getKey! k = ((m.getKey? k).filter f).get! := by
  simp_to_model [filter, getKey?, get, getKey!] using List.getKey!_filter_key

theorem getKeyD_filter [LawfulBEq α]
    {f : (a : α) → β a → Bool} {k fallback : α} (h : m.1.WF) :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      f x (m.get x (contains_of_getKey?_eq_some m h h')))).getD fallback := by
  simp_to_model [filter, getKey?, get, getKeyD] using List.getKeyD_filter

theorem getKeyD_filter_key [EquivBEq α] [LawfulHashable α]
    {f : α → Bool} {k fallback : α} (h : m.1.WF) :
    (m.filter fun k _ => f k).getKeyD k fallback = ((m.getKey? k).filter f).getD fallback := by
  simp_to_model [filter, getKey?, get, getKeyD] using List.getKeyD_filter_key

namespace Const

variable {β : Type v} {γ : Type w} (m : Raw₀ α (fun _ => β))

theorem isEmpty_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.1.WF) :
    (m.filter f).1.isEmpty = true ↔
      ∀ (k : α) (h : m.contains k = true), f (m.getKey k h) (Const.get m k h) = false := by
  simp_to_model [filter, isEmpty, contains, getKey, Const.get] using List.Const.isEmpty_filter_eq_true

theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.1.WF) :
    (m.filter f).1.isEmpty = false ↔
      ∃ (k : α) (h : m.contains k = true), (f (m.getKey k h) (Const.get m k h)) = true := by
  simp_to_model [filter, isEmpty, contains, getKey, Const.get] using List.Const.isEmpty_filter_eq_false

theorem contains_filter_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).contains k = true ↔ ∃ (h' : m.contains k = true),
      f (m.getKey k h') (Const.get m k h') := by
  simp_to_model [filter, contains, getKey, Const.get] using List.Const.containsKey_filter_iff

theorem size_filter_le_size [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.1.WF) :
    (m.filter f).1.size ≤  m.1.size := by
  simp_to_model [filter, size] using List.length_filter_le

theorem size_filter_eq_size_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.1.WF) :
    (m.filter f).1.size = m.1.size ↔ ∀ (a : α) (h : m.contains a),
      f (m.getKey a h) (Const.get m a h) := by
  simp_to_model [filter, size, contains, getKey, Const.get] using List.Const.length_filter_eq_length_iff

theorem filter_equiv_self_iff [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} (h : m.1.WF) :
    (m.filter f).1.Equiv m.1 ↔ ∀ (a : α) (h : m.contains a),
      f (m.getKey a h) (Const.get m a h) := by
  simp_to_model [filter, Equiv, contains, getKey, Const.get] using
    List.Const.perm_filter_self_iff_forall_containsKey

theorem get?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.1.WF) :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k ((contains_eq_isSome_get? m h).trans (Option.isSome_of_eq_some h'))) x) := by
  simp_to_model [filter, Const.get?, getKey] using List.Const.getValue?_filter

theorem get?_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} (h : m.1.WF) :
    m.getKey? k = some k' →
      Const.get? (m.filter f) k = (Const.get? m k).filter (fun x => f k' x) := by
  simp_to_model [filter, Const.get?, getKey?] using List.Const.getValue?_filter_of_getKey?_eq_some

theorem get_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.1.WF) {h'} :
    Const.get (m.filter f) k h' = Const.get m k (contains_of_contains_filter m h h') := by
  simp_to_model [filter, Const.get] using List.getValue_filter

theorem get!_filter [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k : α} (h : m.1.WF) :
    Const.get! (m.filter f) k =
      ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k ((contains_eq_isSome_get? m h).trans (Option.isSome_of_eq_some h'))) x)).get! := by
  simp_to_model [filter, Const.get!, getKey, Const.get?] using List.Const.getValue!_filter

theorem get!_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited β]
    {f : α → β → Bool} {k k' : α} (h : m.1.WF) :
    m.getKey? k = some k' →
      Const.get! (m.filter f) k = ((Const.get? m k).filter (fun x => f k' x)).get! := by
  simp_to_model [filter, Const.get?, getKey?, Const.get!]
    using List.Const.getValue!_filter_of_getKey?_eq_some

theorem getD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} {fallback : β} (h : m.1.WF) :
    Const.getD (m.filter f) k fallback = ((Const.get? m k).pfilter (fun x h' =>
      f (m.getKey k ((contains_eq_isSome_get? m h).trans (Option.isSome_of_eq_some h'))) x)).getD fallback := by
  simp_to_model [filter, Const.getD, getKey, Const.get?] using List.Const.getValueD_filter

theorem getD_filter_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k k' : α} {fallback : β} (h : m.1.WF) :
    m.getKey? k = some k' →
      Const.getD (m.filter f) k fallback =
        ((Const.get? m k).filter (fun x => f k' x)).getD fallback := by
  simp_to_model [filter, Const.get?, getKey?, Const.getD]
    using List.Const.getValueD_filter_of_getKey?_eq_some

theorem toList_filter {α : Type u} (m : Raw₀ α fun _ => β) {f : α → β → Bool} :
    (Raw.Const.toList (m.filter f).1).Perm
      ((Raw.Const.toList m.1).filter (fun p => f p.1 p.2)) := by
  simp_to_model [filter, Const.toList]
  simp only [List.filter_map, Function.comp_def]
  rfl

theorem keys_filter [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} (h : m.1.WF):
    (m.filter f).1.keys.Perm
      (m.1.keys.attach.filter (fun ⟨x, h'⟩ => f x (get m x (contains_of_mem_keys m h h')))).unattach := by
  simp_to_model [keys, filter, Equiv, Const.get]
  rw [List.attach_congr Raw.keys_eq_keys_toListModel]
  rw [List.Const.keys_filter (Raw.WF.out h).distinct]
  simp only [List.filter_map, Function.comp_def, List.unattach, List.map_map]
  rfl

theorem getKey?_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).getKey? k =
    (m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (contains_of_getKey?_eq_some m h h')))) := by
  simp_to_model [filter, getKey?, Const.get] using List.Const.getKey?_filter

theorem getKey!_filter [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : α → β → Bool} {k : α} (h : m.1.WF) :
    (m.filter f).getKey! k =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (contains_of_getKey?_eq_some m h h'))))).get! := by
  simp_to_model [filter, getKey!, getKey?, Const.get] using List.Const.getKey!_filter

theorem getKeyD_filter [EquivBEq α] [LawfulHashable α]
    {f : α → β → Bool} {k fallback : α} (h : m.1.WF) :
    (m.filter f).getKeyD k fallback =
    ((m.getKey? k).pfilter (fun x h' =>
      (f x (Const.get m x (contains_of_getKey?_eq_some m h h'))))).getD fallback := by
  simp_to_model [filter, getKeyD, getKey?, Const.get] using List.Const.getKeyD_filter

end Const

end filter

section map

section raw

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : α → Type w'} (m : Raw₀ α β)

theorem map_id_equiv : (m.map fun _ v => v).1.Equiv m.1 := by
  simp_to_model [map, Equiv] using List.Perm.of_eq (List.map_id _)

theorem map_map_equiv {f : (a : α) → β a → γ a} {g : (a : α) → γ a → δ a} :
    ((m.map f).map g).1.Equiv (m.map fun k v => g k (f k v)) := by
  simp_to_model [map, Equiv, Const.toList] using List.Perm.of_eq (List.map_map)

theorem toList_map {f : (a : α) → β a → γ a} :
    (m.map f).1.toList.Perm (m.1.toList.map (fun p => ⟨p.1, f p.1 p.2⟩)) := by
  simp_to_model [map, toList, Equiv] using List.Perm.rfl

theorem keys_map {f : (a : α) → β a → γ a} : (m.map f).1.keys.Perm m.1.keys := by
  simp_to_model [keys, map, Equiv]
  rw [List.keys_map]

end raw

variable {γ : α → Type w}

theorem filterMap_equiv_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} (h : m.1.WF) :
    (m.filterMap (fun k v => Option.some (f k v))).1.Equiv (m.map f) := by
  rw [filterMap_eq_map m f h]
  exact ⟨.rfl⟩

theorem isEmpty_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} (h : m.1.WF) :
    (m.map f).1.isEmpty = m.1.isEmpty := by
  simp_to_model [map, isEmpty] using List.isEmpty_map

theorem contains_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) :
    (m.map f).contains k = m.contains k := by
  simp_to_model [map, contains] using List.containsKey_map

theorem contains_of_contains_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) :
    (m.map f).contains k = true → m.contains k = true := by
  simp [contains_map m h]

theorem size_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} (h : m.1.WF) :
    (m.map f).1.size = m.1.size := by
  simp_to_model [map, size] using List.length_map

theorem get?_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) :
    (m.map f).get? k = (m.get? k).map (f k) := by
  simp_to_model [map, get?] using List.getValueCast?_map

theorem get_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) {h'} :
    (m.map f).get k h' =
      f k (m.get k (contains_of_contains_map m h h')) := by
  simp_to_model [map, get] using List.getValueCast_map

theorem get!_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} [Inhabited (γ k)] (h : m.1.WF) :
    (m.map f).get! k = ((m.get? k).map (f k)).get! := by
  simp_to_model [map, get?, get!] using List.getValueCast!_map

theorem getD_map [LawfulBEq α]
    {f : (a : α) → β a → γ a} {k : α} {fallback : γ k} (h : m.1.WF) :
    (m.map f).getD k fallback = ((m.get? k).map (f k)).getD fallback := by
  simp_to_model [map, getD, get?] using List.getValueCastD_map

theorem getKey?_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) :
    (m.map f).getKey? k = m.getKey? k := by
  simp_to_model [map, getKey?] using List.getKey?_map

theorem getKey_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) {h'}:
    (m.map f).getKey k h' = m.getKey k (contains_of_contains_map m h h') := by
  simp_to_model [map, getKey] using List.getKey_map

theorem getKey!_map [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {f : (a : α) → β a → γ a} {k : α} (h : m.1.WF) :
    (m.map f).getKey! k = m.getKey! k := by
  simp_to_model [map, getKey!] using List.getKey!_map

theorem getKeyD_map [EquivBEq α] [LawfulHashable α]
    {f : (a : α) → β a → γ a} {k fallback : α} (h : m.1.WF) :
    (m.map f).getKeyD k fallback = m.getKeyD k fallback := by
  simp_to_model [map, getKeyD] using List.getKeyD_map

namespace Const

variable {β : Type v} {γ : Type w} (m : Raw₀ α (fun _ => β))

/-- Variant of `get?_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem get?_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.1.WF) :
    Const.get? (m.map f) k = (Const.get? m k).pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => (contains_eq_isSome_get? m h).trans (Option.isSome_of_mem h')) := by
  simp_to_model [map, Const.get?, contains, getKey] using Const.getValue?_map

theorem get?_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.1.WF) :
    Const.get? (m.map f) k = (Const.get? m k).map (f k) := by
  simp [get?_map' m h, getKey_eq m h]

theorem get?_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} (h : m.1.WF) :
    m.getKey? k = some k' → Const.get? (m.map f) k = (Const.get? m k).map (f k') := by
  simp_to_model [map, Const.get?, getKey?] using Const.getValue?_map_of_getKey?_eq_some

/-- Variant of `get_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem get_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.1.WF) {h'} :
    Const.get (m.map f) k h' =
      (f (m.getKey k (contains_of_contains_map m h h'))
        (Const.get m k (contains_of_contains_map m h h'))) := by
  simp_to_model [map, getKey, Const.get, contains] using List.getValue_map

theorem get_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} (h : m.1.WF) {h'} :
    Const.get (m.map f) k h' = f k (Const.get m k (contains_of_contains_map m h h')) := by
  simp [get_map' m h, getKey_eq m h]

/-- Variant of `get!_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem get!_map' [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} (h : m.1.WF) :
    Const.get! (m.map f) k =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => (contains_eq_isSome_get? m h).trans (Option.isSome_of_mem h'))).get! := by
  simp_to_model [map, getKey, Const.get!, Const.get?, contains] using List.Const.getValue!_map

theorem get!_map [LawfulBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k : α} (h : m.1.WF) :
    Const.get! (m.map f) k = ((Const.get? m k).map (f k)).get! := by
  simp [get!_map' m h, getKey_eq m h]

theorem get!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.1.WF) :
    m.getKey? k = some k' → Const.get! (m.map f) k = ((Const.get? m k).map (f k')).get! := by
  simp_to_model [map, Const.get!, Const.get?, getKey?] using Const.getValue!_map_of_getKey?_eq_some

/-- Variant of `getD_map` that holds with `EquivBEq` (i.e. without `LawfulBEq`). -/
theorem getD_map' [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} (h : m.1.WF) :
    Const.getD (m.map f) k fallback =
      ((get? m k).pmap (fun v h => f (m.getKey k h) v)
        (fun _ h' => (contains_eq_isSome_get? m h).trans (Option.isSome_of_mem h'))).getD fallback := by
  simp_to_model [map, getKey, Const.getD, Const.get?, contains] using List.Const.getValueD_map

theorem getD_map [LawfulBEq α] [LawfulHashable α]
    {f : α → β → γ} {k : α} {fallback : γ} (h : m.1.WF) :
    Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k)).getD fallback := by
  simp [getD_map' m h, getKey_eq m h]

theorem getD_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.1.WF) :
    m.getKey? k = some k' → Const.getD (m.map f) k fallback = ((Const.get? m k).map (f k')).getD fallback := by
  simp_to_model [map, Const.getD, Const.get?, getKey?] using Const.getValueD_map_of_getKey?_eq_some

theorem toList_map {α : Type u} (m : Raw₀ α fun _ => β)
    {f : α → β → γ} :
    (Raw.Const.toList (m.map f).1).Perm
      ((Raw.Const.toList m.1).map (fun p => (p.1, f p.1 p.2))) := by
  simp_to_model [map, Const.toList]
  simp only [List.map_map, Function.comp_def]
  rfl

end Const

end map

end Raw₀

end Std.DHashMap.Internal
