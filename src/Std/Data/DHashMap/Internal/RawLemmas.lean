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

open Std.DHashMap.Internal.List

universe u v

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
    | apply Raw₀.wfImp_insert | apply Raw₀.wfImp_insertIfNew | apply Raw₀.wfImp_erase
    | apply Raw.WF.out | assumption | apply Raw₀.wfImp_empty | apply Raw.WFImp.distinct
    | apply Raw.WF.empty₀))

/-- Internal implementation detail of the hash map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``contains_eq_containsKey, ``Raw.isEmpty_eq_isEmpty, ``Raw.size_eq_length,
    ``get?_eq_getValueCast?, ``Const.get?_eq_getValue?, ``get_eq_getValueCast,
    ``Const.get_eq_getValue, ``get!_eq_getValueCast!, ``getD_eq_getValueCastD,
    ``Const.get!_eq_getValue!, ``Const.getD_eq_getValueD, ``getKey?_eq_getKey?,
    ``getKey_eq_getKey, ``getKeyD_eq_getKeyD, ``getKey!_eq_getKey!,
    ``Raw.length_keys_eq_length_keys, ``Raw.isEmpty_keys_eq_isEmpty_keys,
    ``Raw.contains_keys_eq_contains_keys, ``Raw.mem_keys_iff_contains_keys,
    ``Raw.pairwise_keys_iff_pairwise_keys]

private def modifyNames : Array Name :=
  #[``toListModel_insert, ``toListModel_erase, ``toListModel_insertIfNew]

private def congrNames : MacroM (Array (TSyntax `term)) := do
  return #[← `(_root_.List.Perm.isEmpty_eq), ← `(containsKey_of_perm),
    ← `(_root_.List.Perm.length_eq), ← `(getValueCast?_of_perm _),
    ← `(getValue?_of_perm _), ← `(getValue_of_perm _), ← `(getValueCast_of_perm _),
    ← `(getValueCast!_of_perm _), ← `(getValueCastD_of_perm _), ← `(getValue!_of_perm _),
    ← `(getValueD_of_perm _), ← `(getKey?_of_perm _), ← `(getKey_of_perm _), ← `(getKeyD_of_perm _),
    ← `(getKey!_of_perm _)]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_model" ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[using $using?]?) => do
  let mut congrModify : Array (TSyntax `term) := #[]
  for congr in (← congrNames) do
    for modify in modifyNames do
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
  simp_to_model using List.isEmpty_insertEntry

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
  simp_to_model using List.containsKey_insertEntry

theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} : (m.insert k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntry

theorem contains_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).contains k := by
  simp_to_model using List.containsKey_insertEntry_self

theorem size_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.size = if m.contains k then m.1.size else m.1.size + 1 := by
  simp_to_model using List.length_insertEntry

theorem size_le_size_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    m.1.size ≤ (m.insert k v).1.size := by
  simp_to_model using List.length_le_length_insertEntry

theorem size_insert_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).1.size ≤ m.1.size + 1 := by
  simp_to_model using List.length_insertEntry_le

@[simp]
theorem erase_empty {k : α} {c : Nat} : (empty c : Raw₀ α β).erase k = empty c := by
  simp [erase, empty]

theorem isEmpty_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.isEmpty = (m.1.isEmpty || (m.1.size == 1 && m.contains k)) := by
  simp_to_model using List.isEmpty_eraseKey

theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) := by
  simp_to_model using List.containsKey_eraseKey

theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).contains a → m.contains a := by
  simp_to_model using List.containsKey_of_containsKey_eraseKey

theorem size_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.size = if m.contains k then m.1.size - 1 else m.1.size := by
  simp_to_model using List.length_eraseKey

theorem size_erase_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).1.size ≤ m.1.size := by
  simp_to_model using List.length_eraseKey_le

theorem size_le_size_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    m.1.size ≤ (m.erase k).1.size + 1 := by
  simp_to_model using List.length_le_length_eraseKey

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
  simp_to_model using List.getValueCast?_insertEntry

theorem get?_insert_self [LawfulBEq α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).get? k = some v := by
  simp_to_model using List.getValueCast?_insertEntry_self

theorem contains_eq_isSome_get? [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a = (m.get? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValueCast?

theorem get?_eq_none [LawfulBEq α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.get? a = none := by
  simp_to_model using List.getValueCast?_eq_none

theorem get?_erase [LawfulBEq α] (h : m.1.WF) {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a := by
  simp_to_model using List.getValueCast?_eraseKey

theorem get?_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} : (m.erase k).get? k = none := by
  simp_to_model using List.getValueCast?_eraseKey_self

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
  simp_to_model using List.getValue?_insertEntry

theorem get?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β} :
    get? (m.insert k v) k = some v := by
  simp_to_model using List.getValue?_insertEntry_self

theorem contains_eq_isSome_get? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = (get? m a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getValue?

theorem get?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = false → get? m a = none := by
  simp_to_model using List.getValue?_eq_none.2

theorem get?_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    Const.get? (m.erase k) a = if k == a then none else get? m a := by
  simp_to_model using List.getValue?_eraseKey

theorem get?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    get? (m.erase k) k = none := by
  simp_to_model using List.getValue?_eraseKey_self

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
  simp_to_model using List.getValueCast_insertEntry

theorem get_insert_self [LawfulBEq α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).get k (contains_insert_self _ h) = v := by
  simp_to_model using List.getValueCast_insertEntry_self

@[simp]
theorem get_erase [LawfulBEq α] (h : m.1.WF) {k a : α} {h'} :
    (m.erase k).get a h' = m.get a (contains_of_contains_erase _ h h') := by
  simp_to_model using List.getValueCast_eraseKey

theorem get?_eq_some_get [LawfulBEq α] (h : m.1.WF) {a : α} {h} : m.get? a = some (m.get a h) := by
  simp_to_model using List.getValueCast?_eq_some_getValueCast

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} {h₁} :
    get (m.insert k v) a h₁ =
      if h₂ : k == a then v
      else get m a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model using List.getValue_insertEntry

theorem get_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β} :
    get (m.insert k v) k (contains_insert_self _ h) = v := by
  simp_to_model using List.getValue_insertEntry_self

@[simp]
theorem get_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {h'} :
    get (m.erase k) a h' = get m a (contains_of_contains_erase _ h h') := by
  simp_to_model using List.getValue_eraseKey

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
  simp_to_model using List.getValueCast!_insertEntry

theorem get!_insert_self [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] {b : β a} :
    (m.insert a b).get! a = b := by
  simp_to_model using List.getValueCast!_insertEntry_self

theorem get!_eq_default [LawfulBEq α] (h : m.1.WF) {a : α} [Inhabited (β a)] :
    m.contains a = false → m.get! a = default := by
  simp_to_model using List.getValueCast!_eq_default

theorem get!_erase [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] :
    (m.erase k).get! a = if k == a then default else m.get! a := by
  simp_to_model using List.getValueCast!_eraseKey

theorem get!_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} [Inhabited (β k)] :
    (m.erase k).get! k = default := by
  simp_to_model using List.getValueCast!_eraseKey_self

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
  simp_to_model using List.getValue!_insertEntry

theorem get!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k : α}
    {v : β} : get! (m.insert k v) k = v := by
  simp_to_model using List.getValue!_insertEntry_self

theorem get!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {a : α} :
    m.contains a = false → get! m a = default := by
  simp_to_model using List.getValue!_eq_default

theorem get!_erase [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α} :
    get! (m.erase k) a = if k == a then default else get! m a := by
  simp_to_model using List.getValue!_eraseKey

theorem get!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k : α} :
    get! (m.erase k) k = default := by
  simp_to_model using List.getValue!_eraseKey_self

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
  simp_to_model using List.getValueCastD_insertEntry

theorem getD_insert_self [LawfulBEq α] (h : m.1.WF) {a : α} {fallback b : β a} :
    (m.insert a b).getD a fallback = b := by
  simp_to_model using List.getValueCastD_insertEntry_self

theorem getD_eq_fallback [LawfulBEq α] (h : m.1.WF) {a : α} {fallback : β a} :
    m.contains a = false → m.getD a fallback = fallback := by
  simp_to_model using List.getValueCastD_eq_fallback

theorem getD_erase [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} :
    (m.erase k).getD a fallback = if k == a then fallback else m.getD a fallback := by
  simp_to_model using List.getValueCastD_eraseKey

theorem getD_erase_self [LawfulBEq α] (h : m.1.WF) {k : α} {fallback : β k} :
    (m.erase k).getD k fallback = fallback := by
  simp_to_model using List.getValueCastD_eraseKey_self

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
  simp_to_model using List.getValueD_insertEntry

theorem getD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {fallback v : β} :
    getD (m.insert k v) k fallback = v := by
  simp_to_model using List.getValueD_insertEntry_self

theorem getD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {fallback : β} :
    m.contains a = false → getD m a fallback = fallback := by
  simp_to_model using List.getValueD_eq_fallback

theorem getD_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback : β} :
    getD (m.erase k) a fallback = if k == a then fallback else getD m a fallback := by
  simp_to_model using List.getValueD_eraseKey

theorem getD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {fallback : β} :
    getD (m.erase k) k fallback = fallback := by
  simp_to_model using List.getValueD_eraseKey_self

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
  simp_to_model using List.getKey?_insertEntry

theorem getKey?_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).getKey? k = some k := by
  simp_to_model using List.getKey?_insertEntry_self

theorem contains_eq_isSome_getKey? [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = (m.getKey? a).isSome := by
  simp_to_model using List.containsKey_eq_isSome_getKey?

theorem getKey?_eq_none [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.getKey? a = none := by
  simp_to_model using List.getKey?_eq_none

theorem getKey?_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
    (m.erase k).getKey? a = if k == a then none else m.getKey? a := by
  simp_to_model using List.getKey?_eraseKey

theorem getKey?_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    (m.erase k).getKey? k = none := by
  simp_to_model using List.getKey?_eraseKey_self

theorem getKey_insert [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insert k v).getKey a h₁ =
      if h₂ : k == a then
        k
      else
        m.getKey a (contains_of_contains_insert _ h h₁ (Bool.eq_false_iff.2 h₂)) := by
  simp_to_model using List.getKey_insertEntry

theorem getKey_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insert k v).getKey k (contains_insert_self _ h) = k := by
  simp_to_model using List.getKey_insertEntry_self

@[simp]
theorem getKey_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {h'} :
    (m.erase k).getKey a h' = m.getKey a (contains_of_contains_erase _ h h') := by
  simp_to_model using List.getKey_eraseKey

theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a : α} {h} :
    m.getKey? a = some (m.getKey a h) := by
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
  simp_to_model using List.getKey!_insertEntry

theorem getKey!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α}
    {b : β a} : (m.insert a b).getKey! a = a := by
  simp_to_model using List.getKey!_insertEntry_self

theorem getKey!_eq_default [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {a : α} :
    m.contains a = false → m.getKey! a = default := by
  simp_to_model using List.getKey!_eq_default

theorem getKey!_erase [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α} :
    (m.erase k).getKey! a = if k == a then default else m.getKey! a := by
  simp_to_model using List.getKey!_eraseKey

theorem getKey!_erase_self [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k : α} :
    (m.erase k).getKey! k = default := by
  simp_to_model using List.getKey!_eraseKey_self

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
  simp_to_model using List.getKeyD_insertEntry

theorem getKeyD_insert_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α}
    {b : β a} :
    (m.insert a b).getKeyD a fallback = a := by
  simp_to_model using List.getKeyD_insertEntry_self

theorem getKeyD_eq_fallback [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {a fallback : α} :
    m.contains a = false → m.getKeyD a fallback = fallback := by
  simp_to_model using List.getKeyD_eq_fallback

theorem getKeyD_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α} :
    (m.erase k).getKeyD a fallback = if k == a then fallback else m.getKeyD a fallback := by
  simp_to_model using List.getKeyD_eraseKey

theorem getKeyD_erase_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k fallback : α} :
    (m.erase k).getKeyD k fallback = fallback := by
  simp_to_model using List.getKeyD_eraseKey_self

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
  simp_to_model using List.isEmpty_insertEntryIfNew

theorem contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).contains a = (k == a || m.contains a) := by
  simp_to_model using List.containsKey_insertEntryIfNew

theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).contains k := by
  simp_to_model using List.containsKey_insertEntryIfNew_self

theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} : (m.insertIfNew k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew

/-- This is a restatement of `contains_insertIfNew` that is written to exactly match the proof
obligation in the statement of `get_insertIfNew`. -/
theorem contains_of_contains_insertIfNew' [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).contains a → ¬((k == a) ∧ m.contains k = false) → m.contains a := by
  simp_to_model using List.containsKey_of_containsKey_insertEntryIfNew'

theorem size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.size = if m.contains k then m.1.size else m.1.size + 1 := by
  simp_to_model using List.length_insertEntryIfNew

theorem size_le_size_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    m.1.size ≤ (m.insertIfNew k v).1.size := by
  simp_to_model using List.length_le_length_insertEntryIfNew

theorem size_insertIfNew_le [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} {v : β k} :
    (m.insertIfNew k v).1.size ≤ m.1.size + 1 := by
  simp_to_model using List.length_insertEntryIfNew_le

theorem get?_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).get? a =
      if h : k == a ∧ m.contains k = false then some (cast (congrArg β (eq_of_beq h.1)) v)
      else m.get? a := by
  simp_to_model using List.getValueCast?_insertEntryIfNew

theorem get_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).get a h₁ =
      if h₂ : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.get a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model using List.getValueCast_insertEntryIfNew

theorem get!_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (m.insertIfNew k v).get! a =
      if h : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h.1)) v
      else m.get! a := by
  simp_to_model using List.getValueCast!_insertEntryIfNew

theorem getD_insertIfNew [LawfulBEq α] (h : m.1.WF) {k a : α} {fallback : β a} {v : β k} :
    (m.insertIfNew k v).getD a fallback =
      if h : k == a ∧ m.contains k = false then cast (congrArg β (eq_of_beq h.1)) v
      else m.getD a fallback := by
  simp_to_model using List.getValueCastD_insertEntryIfNew

namespace Const

variable {β : Type v} (m : Raw₀ α (fun _ => β)) (h : m.1.WF)

theorem get?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} :
    get? (m.insertIfNew k v) a = if k == a ∧ m.contains k = false then some v else get? m a := by
  simp_to_model using List.getValue?_insertEntryIfNew

theorem get_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β} {h₁} :
    get (m.insertIfNew k v) a h₁ =
      if h₂ : k == a ∧ m.contains k = false then v
      else get m a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model using List.getValue_insertEntryIfNew

theorem get!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited β] (h : m.1.WF) {k a : α}
    {v : β} :
    get! (m.insertIfNew k v) a = if k == a ∧ m.contains k = false then v else get! m a := by
  simp_to_model using List.getValue!_insertEntryIfNew

theorem getD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {fallback v : β} :
    getD (m.insertIfNew k v) a fallback =
      if k == a ∧ m.contains k = false then v else getD m a fallback := by
  simp_to_model using List.getValueD_insertEntryIfNew

end Const

theorem getKey?_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).getKey? a =
      if k == a ∧ m.contains k = false then some k else m.getKey? a := by
  simp_to_model using List.getKey?_insertEntryIfNew

theorem getKey_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} {v : β k} {h₁} :
    (m.insertIfNew k v).getKey a h₁ =
      if h₂ : k == a ∧ m.contains k = false then k
      else m.getKey a (contains_of_contains_insertIfNew' _ h h₁ h₂) := by
  simp_to_model using List.getKey_insertEntryIfNew

theorem getKey!_insertIfNew [EquivBEq α] [LawfulHashable α] [Inhabited α] (h : m.1.WF) {k a : α}
    {v : β k} :
    (m.insertIfNew k v).getKey! a =
      if k == a ∧ m.contains k = false then k else m.getKey! a := by
  simp_to_model using List.getKey!_insertEntryIfNew

theorem getKeyD_insertIfNew [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a fallback : α}
    {v : β k} :
    (m.insertIfNew k v).getKeyD a fallback =
      if k == a ∧ m.contains k = false then k else m.getKeyD a fallback := by
  simp_to_model using List.getKeyD_insertEntryIfNew

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
theorem isEmpty_keys [EquivBEq α] [LawfulHashable α] (h: m.1.WF):
    m.1.keys.isEmpty = m.1.isEmpty:= by
  simp_to_model using List.isEmpty_keys_eq_isEmpty

@[simp]
theorem contains_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    m.1.keys.contains k = m.contains k := by
  simp_to_model using List.containsKey_eq_keys_contains.symm

@[simp]
theorem mem_keys [LawfulBEq α] [LawfulHashable α] (h : m.1.WF) {k : α} :
    k ∈ m.1.keys ↔ m.contains k := by
  simp_to_model 
  rw [List.containsKey_eq_keys_contains]

theorem distinct_keys [EquivBEq α] [LawfulHashable α] (h : m.1.WF) :
    m.1.keys.Pairwise (fun a b => (a == b) = false) := by
  simp_to_model using (Raw.WF.out h).distinct.distinct

end Raw₀

end Std.DHashMap.Internal
