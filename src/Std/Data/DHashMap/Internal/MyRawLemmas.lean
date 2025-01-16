/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Internal.WF
import Std.Data.DHashMap.Internal.RawLemmas

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

namespace Std.DHashMap.Internal.Raw₀

variable [BEq α] [Hashable α]
variable (m : Raw₀ α β)

open Lean

@[simp]
theorem isEmpty_modify [LawfulBEq α] (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model using List.isEmpty_modifyKey

section Alter

-- theorem constAlter_eq_alter [LawfulBEq α] {β : Type v} (m : Raw₀ α (fun _ => β)) (a : α)
--     (f : Option β → Option β) : Const.alter m a f = m.alter a f := by
--   simp_to_model using List.constAlterKey_eq_alterKey

-- theorem alter_empty [LawfulBEq α] {k : α} {f : Option (β k) → Option (β k)} :
--     empty.alter k f =
--     match f none with
--     | none => empty
--     | some v => empty.insert k v := by
--   simp_to_model using List.alterKey_nil

@[simp]
theorem isEmpty_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (m.get? k)).isNone) := by
  simp_to_model using List.isEmpty_alterKey

theorem contains_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' := by
  simp_to_model using List.containsKey_alterKey

theorem size_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.size =
    if m.contains k && (f (m.get? k)).isNone then
      m.1.size - 1
    else if !m.contains k && (f (m.get? k)).isSome then
      m.1.size + 1
    else
      m.1.size := by
  simp_to_model using List.length_alterKey'

theorem size_alter_eq_add_one [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    (h₁ : m.contains k = false) (h₂: (f (m.get? k)).isSome) :
    (m.alter k f).1.size = m.1.size + 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_sub_one [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    (h₁ : m.contains k) (h₂: (f (m.get? k)).isNone) :
    (m.alter k f).1.size = m.1.size - 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    (h₁ : m.contains k = false) (h₂: (f (m.get? k)).isNone) :
    (m.alter k f).1.size = m.1.size := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self' [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    (h₁ : m.contains k) (h₂: (f (m.get? k)).isSome) :
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
    (m.alter k f).get? k' = if h : k == k' then
      cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (m.get? k))
    else
      m.get? k' := by
  simp_to_model using List.getValueCast?_alterKey

theorem get_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)}
    (hc : (m.alter k f).contains k') :
    (m.alter k f).get k' hc =
    if heq : k == k' then
      haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, if_pos heq] at hc
      cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get <| h'
    else
      haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
      m.get k' h' := by
  simp_to_model using List.getValueCast_alterKey

theorem get_alter_self [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    {hc : (m.alter k f).contains k} :
    haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, beq_self_eq_true] at hc
    (m.alter k f).get k hc = (f (m.get? k)).get h' := by
  simp_to_model using List.getValueCast_alterKey_self

theorem get!_alter [LawfulBEq α] {k k' : α} (h : m.1.WF) [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).get! k' =
    if heq : k == k' then
      haveI : Inhabited (β k) := ⟨cast (congrArg β <| eq_of_beq heq).symm default⟩
      cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get!
    else
      m.get! k' := by
  simp_to_model using List.getValueCast!_alterKey

theorem getD_alter [LawfulBEq α] {k k' : α} {v : β k'} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k' v =
    if heq : k == k' then
      f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD v
    else
      m.getD k' v := by
  simp_to_model using List.getValueCastD_alterKey

theorem getD_alter_self [LawfulBEq α] {k : α} {v : β k} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k v = (f (m.get? k)).getD v := by
  simp only [getD_alter, h, beq_self_eq_true, reduceDIte, cast_eq_id, Option.map_id_fun, id_eq]

theorem getKey?_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k' =
    if k == k' then
      if (f (m.get? k)).isSome then some k else none
    else
      m.getKey? k' := by
  simp_to_model using List.getKey?_alterKey

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} : (m.alter k f).getKey! k' =
    if k == k' then
      if (f (m.get? k)).isSome then k else panic ""
    else
      m.getKey! k' := by
  simp_to_model using List.getKey!_alterKey

theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF)
    {f : Option (β k) → Option (β k)} (hc : (m.alter k f).contains k') :
    (m.alter k f).getKey k' hc =
    if heq : k == k' then
      k
    else
      haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
      m.getKey k' h' := by
  have := getKey?_alter (m := m) (k := k) (k' := k') (f := f) h
  rw [getKey?_eq_some_getKey _ h.alter₀ (h' := hc)] at this
  split
  · next heq =>
    cases eq_of_beq heq
    apply Option.some_inj.mp
    simp_all
  · next heq =>
    apply Option.some_inj.mp
    simp_all only [Bool.false_eq_true, ite_false]
    rw [getKey?_eq_some_getKey m h]

theorem getKeyD_alter [LawfulBEq α] {k k' d : α} (h : m.1.WF) {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKeyD k' d =
    if k == k' then
      if (f (m.get? k)).isSome then k else d
    else
      m.getKeyD k' d := by
  simp only [getKeyD_eq_getD_getKey?, h.alter₀, h, getKey?_alter, beq_iff_eq, Function.comp_apply]
  split
  · next heq =>
    cases eq_of_beq heq
    split <;> rfl
  · rfl

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => β))

-- theorem alter_empty {k : α} {f : Option β → Option β} :
--     Const.alter empty k f =
--     match f none with
--     | none => empty
--     | some v => empty.insert k v := by
--   simp_to_model using List.Const.alterKey_nil

@[simp]
theorem isEmpty_alter (h : m.1.WF)  {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty ↔ (m.erase k).1.isEmpty ∧ f (Const.get? m k) = none := by
  simp_to_model using List.Const.isEmpty_alterKey

theorem contains_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).contains k' =
    if k == k' then
      (f (Const.get? m k)).isSome
    else
      m.contains k' := by
  simp_to_model using List.Const.containsKey_alterKey

theorem size_alter (h : m.1.WF) {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.size =
    if m.contains k && (f (Const.get? m k)).isNone then
      m.1.size - 1
    else if !m.contains k && (f (Const.get? m k)).isSome then
      m.1.size + 1
    else
      m.1.size := by
  simp_to_model using List.Const.length_alterKey'

theorem size_alter_eq_add_one (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k = false) (h₂: (f (Const.get? m k)).isSome) :
    (Const.alter m k f).1.size = m.1.size + 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_sub_one (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k) (h₂: (f (Const.get? m k)).isNone) :
    (Const.alter m k f).1.size = m.1.size - 1 := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k = false) (h₂: (f (Const.get? m k)).isNone) :
    (Const.alter m k f).1.size = m.1.size := by
  simp [size_alter, h, h₁, h₂]

theorem size_alter_eq_self' (h : m.1.WF) {k : α} {f : Option β → Option β}
    (h₁ : m.contains k) (h₂: (f (Const.get? m k)).isSome) :
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
    Const.get? (Const.alter m k f) k' = if k == k' then
      f (Const.get? m k)
    else
      Const.get? m k' := by
  simp_to_model using List.Const.getValue?_alterKey

theorem get_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β}
    (hc : (Const.alter m k f).contains k') :
    Const.get (Const.alter m k f) k' hc =
    if heq : k == k' then
      haveI h' : (f (Const.get? m k)).isSome := by rwa [contains_alter _ h, if_pos heq] at hc
      (f (Const.get? m k)).get <| h'
    else
      haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
      Const.get m k' h' := by
  simp_to_model using List.Const.getValue_alterKey

theorem get_alter_self (h : m.1.WF) {k : α} {f : Option β → Option β}
    {hc : (Const.alter m k f).contains k} :
    haveI h' : (f (Const.get? m k)).isSome := by rwa [contains_alter _ h, BEq.refl] at hc
    Const.get (Const.alter m k f) k hc = (f (Const.get? m k)).get h' := by
  simp_to_model using List.Const.getValue_alterKey_self

theorem cast_eq_id {α : Type u} : cast (rfl : α = α) = id := by rfl

theorem get!_alter {k k' : α} (h : m.1.WF) [Inhabited β] {f : Option β → Option β} :
    Const.get! (Const.alter m k f) k' =
    if k == k' then
      (f (Const.get? m k)).get!
    else
      Const.get! m k' := by
  simp_to_model using List.Const.getValue!_alterKey

theorem getD_alter {k k' : α} {v : β} (h : m.1.WF) {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k' v =
    if k == k' then
      f (Const.get? m k) |>.getD v
    else
      Const.getD m k' v := by
  simp_to_model using List.Const.getValueD_alterKey

theorem getD_alter_self {k : α} {v : β} (h : m.1.WF) {f : Option β → Option β} :
    Const.getD (Const.alter m k f) k v = (f (Const.get? m k)).getD v := by
  simp only [h, getD_alter, BEq.refl, reduceIte]

theorem getKey?_alter (h : m.1.WF) {k k' : α} {f : Option β → Option β} :
    (Const.alter m k f).getKey? k' =
    if k == k' then
      if (f (Const.get? m k)).isSome then some k else none
    else
      m.getKey? k' := by
  simp_to_model using List.Const.getKey?_alterKey

theorem getKey!_alter [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option β → Option β} :
    (Const.alter m k f).getKey! k' =
    if k == k' then
      if (f (Const.get? m k)).isSome then k else panic ""
    else
      m.getKey! k' := by
  simp_to_model using List.Const.getKey!_alterKey

theorem getKey_alter [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option β → Option β}
    (hc : (Const.alter m k f).contains k') :
    (Const.alter m k f).getKey k' hc =
    if heq : k == k' then
      k
    else
      haveI h' : m.contains k' := by rwa [contains_alter _ h, if_neg heq] at hc
      m.getKey k' h' := by
  simp_to_model using List.Const.getKey_alterKey

theorem getKeyD_alter {k k' d : α} (h : m.1.WF) {f : Option β → Option β} :
    (Const.alter m k f).getKeyD k' d =
    if k == k' then
      if (f (Const.get? m k)).isSome then k else d
    else
      m.getKeyD k' d := by
  simp_to_model using List.Const.getKeyD_alterKey

end Const

end Alter

section Modify

variable [LawfulBEq α]

-- theorem constModify_eq_modify {β : Type v} (m : Raw₀ α (fun _ => β)) (a : α)
--     (f : β → β) : Const.modify m a f = m.modify a f := by
--   simp_to_model using List.constModifyKey_eq_modifyKey

-- @[simp]
-- theorem modify_empty [LawfulBEq α] {k : α} {f : β k → β k} : empty.modify k f = empty := by
--   simp_to_model using List.modifyKey_nil

-- theorem modify_of_not_mem [LawfulBEq α] {k : α} {f g : β k → β k} (h : m.contains k = false) :
--     m.modify k f = m := by
--   simp_to_model using List.modifyKey_of_not_mem

theorem contains_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).contains k' = m.contains k' := by
  simp_to_model using List.containsKey_modifyKey

theorem size_modify (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).1.size = m.1.size := by
  simp_to_model using List.length_modifyKey

theorem get?_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).get? k' = if h : k == k' then
      (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((m.get? k).map f))
    else
      m.get? k' := by
  simp_to_model using List.getValueCast?_modifyKey

@[simp]
theorem get?_modify_self (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).get? k = (m.get? k).map f := by
  simp_to_model using List.getValueCast?_modifyKey_self

theorem get_modify (h : m.1.WF) {k k' : α} {f : β k → β k}
    (hc : (m.modify k f).contains k') :
    (m.modify k f).get k' hc =
    if heq : k == k' then
      haveI h' : m.contains k := by rwa [contains_modify _ h, ← eq_of_beq heq] at hc
      cast (congrArg β (eq_of_beq heq)) <| f (m.get k h')
    else
      haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
      m.get k' h' := by
  simp_to_model using List.getValueCast_modifyKey

@[simp]
theorem get_modify_self (h : m.1.WF) {k : α} {f : β k → β k} {hc : (m.modify k f).contains k} :
    haveI h' : m.contains k := by rwa [contains_modify _ h] at hc
    (m.modify k f).get k hc = f (m.get k h') := by
  simp_to_model using List.getValueCast_modifyKey_self

theorem get!_modify (h : m.1.WF) {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (m.modify k f).get! k' =
    if heq : k == k' then
      haveI : Inhabited (β k) := ⟨cast (congrArg β <| eq_of_beq heq).symm default⟩
      -- not correct if f does not preserve default: ... f (m.get! k)
      -- possible alternative: write ... (m.getD k (cast ⋯ default))
      m.get? k |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
    else
      m.get! k' := by
  simp_to_model using List.getValueCast!_modifyKey

@[simp]
theorem get!_modify_self (h : m.1.WF) {k : α} [Inhabited (β k)] {f : β k → β k} :
    (m.modify k f).get! k = ((m.get? k).map f).get! := by
  simp_to_model using List.getValueCast!_modifyKey_self

theorem getD_modify (h : m.1.WF) {k k' : α} {v : β k'} {f : β k → β k} :
    (m.modify k f).getD k' v =
    if heq : k == k' then
      m.get? k |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD v
    else
      m.getD k' v := by
  simp_to_model using List.getValueCastD_modifyKey

@[simp]
theorem getD_modify_self (h : m.1.WF) {k : α} {v : β k} {f : β k → β k} :
    (m.modify k f).getD k v = ((m.get? k).map f).getD v := by
  simp_to_model using List.getValueCastD_modifyKey_self

theorem getKey?_modify (h : m.1.WF) {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey? k' =
    if k == k' then
      if m.contains k then some k else none
    else
      m.getKey? k' := by
  simp_to_model using List.getKey?_modifyKey

theorem getKey?_modify_self (h : m.1.WF) {k : α} {f : β k → β k} :
    (m.modify k f).getKey? k = if m.contains k then some k else none := by
  simp_to_model using List.getKey?_modifyKey_self

theorem getKey!_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β k → β k} :
    (m.modify k f).getKey! k' =
    if k == k' then
      if m.contains k then k else panic ""
    else
      m.getKey! k' := by
  simp_to_model using List.getKey!_modifyKey

theorem getKey!_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β k → β k} :
    (m.modify k f).getKey! k = if m.contains k then k else panic "" := by
  simp_to_model using List.getKey!_modifyKey_self

theorem getKey_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β k → β k}
    (hc : (m.modify k f).contains k') :
    (m.modify k f).getKey k' hc =
    if heq : k == k' then
      k
    else
      haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
      m.getKey k' h' := by
  simp_to_model using List.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β k → β k}
    (hc : (m.modify k f).contains k) : (m.modify k f).getKey k hc = k := by
  simp_to_model using List.getKey_modifyKey_self

theorem getKeyD_modify (h : m.1.WF) {k k' d : α} {f : β k → β k} :
    (m.modify k f).getKeyD k' d =
    if k == k' then
      if m.contains k then k else d
    else
      m.getKeyD k' d := by
  simp_to_model using List.getKeyD_modifyKey

theorem getKeyD_modify_self (h : m.1.WF) [Inhabited α] {k d : α} {f : β k → β k} :
    (m.modify k f).getKeyD k d = if m.contains k then k else d := by
  simp_to_model using List.getKeyD_modifyKey_self

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α] (m : Raw₀ α (fun _ => β))
omit [LawfulBEq α]

-- @[simp]
-- theorem modify_empty [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} :
--     Const.modify empty k f = empty := by
--   simp_to_model using List.Const.modify_empty

-- theorem modify_of_not_mem [EquivBEq α] [LawfulHashable α] {k : α} {f g : β → β} (h : m.contains k = false) :
--     Const.modify m k f = m := by
--   simp_to_model using List.Const.modify_of_not_mem

@[simp]
theorem isEmpty_modify (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model using List.Const.isEmpty_modifyKey

theorem contains_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    (Const.modify m k f).contains k' = m.contains k' := by
  simp_to_model using List.Const.containsKey_modifyKey

theorem size_modify (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.size = m.1.size := by
  simp_to_model using List.Const.length_modifyKey

theorem get?_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    Const.get? (Const.modify m k f) k' = if k == k' then
      (Const.get? m k).map f
    else
      Const.get? m k' := by
  simp_to_model using List.Const.getValue?_modifyKey

@[simp]
theorem get?_modify_self (h : m.1.WF) {k : α} {f : β → β} :
    Const.get? (Const.modify m k f) k = (Const.get? m k).map f := by
  simp_to_model using List.Const.getValue?_modifyKey_self

theorem get_modify (h : m.1.WF) {k k' : α} {f : β → β}
    (hc : (Const.modify m k f).contains k') :
    Const.get (Const.modify m k f) k' hc =
    if heq : k == k' then
      haveI h' : m.contains k := by rwa [contains_modify _ h, ← contains_congr _ h heq] at hc
      f (Const.get m k h')
    else
      haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
      Const.get m k' h' := by
  simp_to_model using List.Const.getValue_modifyKey

@[simp]
theorem get_modify_self (h : m.1.WF) {k : α} {f : β → β} {hc : (Const.modify m k f).contains k} :
    haveI h' : m.contains k := by rwa [contains_modify _ h] at hc
    Const.get (Const.modify m k f) k hc = f (Const.get m k h') := by
  simp_to_model using List.Const.getValue_modifyKey_self

theorem get!_modify (h : m.1.WF) {k k' : α} [hi : Inhabited β] {f : β → β} :
    Const.get! (Const.modify m k f) k' =
    if k == k' then
      Const.get? m k |>.map f |>.get!
    else
      Const.get! m k' := by
  simp_to_model using List.Const.getValue!_modifyKey

@[simp]
theorem get!_modify_self (h : m.1.WF) {k : α} [Inhabited (β)] {f : β → β} :
    Const.get! (Const.modify m k f) k = ((Const.get? m k).map f).get! := by
  simp_to_model using List.Const.getValue!_modifyKey_self

theorem getD_modify (h : m.1.WF) {k k' : α} {v : β} {f : β → β} :
    Const.getD (Const.modify m k f) k' v =
    if k == k' then
      Const.get? m k |>.map f |>.getD v
    else
      Const.getD m k' v := by
  simp_to_model using List.Const.getValueD_modifyKey

@[simp]
theorem getD_modify_self (h : m.1.WF) {k : α} {v : β} {f : β → β} :
    Const.getD (Const.modify m k f) k v = ((Const.get? m k).map f).getD v := by
  simp_to_model using List.Const.getValueD_modifyKey_self

theorem getKey?_modify (h : m.1.WF) {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey? k' =
    if k == k' then
      if m.contains k then some k else none
    else
      m.getKey? k' := by
  simp_to_model using List.Const.getKey?_modifyKey

theorem getKey?_modify_self (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).getKey? k = if m.contains k then some k else none := by
  simp_to_model using List.Const.getKey?_modifyKey_self

theorem getKey!_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β → β} :
    (Const.modify m k f).getKey! k' =
    if k == k' then
      if m.contains k then k else panic ""
    else
      m.getKey! k' := by
  simp_to_model using List.Const.getKey!_modifyKey

theorem getKey!_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β → β} :
    (Const.modify m k f).getKey! k = if m.contains k then k else panic "" := by
  simp_to_model using List.Const.getKey!_modifyKey_self

theorem getKey_modify (h : m.1.WF) [Inhabited α] {k k' : α} {f : β → β}
    (hc : (Const.modify m k f).contains k') :
    (Const.modify m k f).getKey k' hc =
    if heq : k == k' then
      k
    else
      haveI h' : m.contains k' := by rwa [contains_modify _ h] at hc
      m.getKey k' h' := by
  simp_to_model using List.Const.getKey_modifyKey

@[simp]
theorem getKey_modify_self (h : m.1.WF) [Inhabited α] {k : α} {f : β → β}
    (hc : (Const.modify m k f).contains k) : (Const.modify m k f).getKey k hc = k := by
  simp_to_model using List.Const.getKey_modifyKey_self

theorem getKeyD_modify (h : m.1.WF) {k k' d : α} {f : β → β} :
    (Const.modify m k f).getKeyD k' d =
    if k == k' then
      if m.contains k then k else d
    else
      m.getKeyD k' d := by
  simp_to_model using List.Const.getKeyD_modifyKey

theorem getKeyD_modify_self (h : m.1.WF) [Inhabited α] {k d : α} {f : β → β} :
    (Const.modify m k f).getKeyD k d = if m.contains k then k else d := by
  simp_to_model using List.Const.getKeyD_modifyKey_self

end Const

end Modify
