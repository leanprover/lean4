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

@[simp]
theorem isEmpty_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (m.get? k)).isNone) := by
  simp_to_model using List.isEmpty_alterKey

theorem contains_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' := by
  simp_to_model using List.containsKey_alterKey

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
  have := get?_alter m (k' := k') (f := f) h
  rw [get?_eq_some_get _ h.alter₀ (h' := hc)] at this
  · split
    · next heq =>
      cases eq_of_beq heq
      apply Option.some_inj.mp
      simp_all
    · next heq =>
      apply Option.some_inj.mp
      simp_all only [Bool.false_eq_true, Function.comp_apply, dite_false]
      rw [get?_eq_some_get m h]

theorem get_alter_self [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)}
    {hc : (m.alter k f).contains k} :
    haveI h' : (f (m.get? k)).isSome := by rwa [contains_alter _ h, beq_self_eq_true] at hc
    (m.alter k f).get k hc = (f (m.get? k)).get h' := by
  rw [get_alter _ h]
  simp only [beq_self_eq_true, reduceDIte, cast_eq]

theorem cast_eq_id {α : Type u} : cast (rfl : α = α) = id := by rfl

theorem get!_alter [LawfulBEq α] {k k' : α} (h : m.1.WF) [Inhabited (β k')] {f : Option (β k) → Option (β k)} :
    (m.alter k f).get! k' =
    if heq : k == k' then
      haveI : Inhabited (β k) := ⟨cast (congrArg β <| eq_of_beq heq).symm default⟩
      cast (congrArg β (eq_of_beq heq)) <| (f (m.get? k)).get!
    else
      m.get! k' := by
  simp only [get!_eq_get!_get?, h.alter₀, h, get?_alter, beq_iff_eq, Function.comp_apply]
  split
  · next heq =>
    cases eq_of_beq heq
    simp only [cast_eq]
  · rfl

theorem getD_alter [LawfulBEq α] {k k' : α} {v : β k'} (h : m.1.WF) {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k' v =
    if heq : k == k' then
      f (m.get? k) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD v
    else
      m.getD k' v := by
  simp only [getD_eq_getD_get?, h.alter₀, h, get?_alter, beq_iff_eq, Function.comp_apply]
  split
  · next heq =>
    cases eq_of_beq heq
    simp only [cast_eq_id, Option.map_id]
  · rfl

theorem getD_alter_self [LawfulBEq α] {k : α} {v : β k} (h : m.1.WF) {f : Option (β k) → Option (β k)} :
    (m.alter k f).getD k v = (f (m.get? k)).getD v := by
  simp only [getD_alter, h, beq_self_eq_true, reduceDIte, cast_eq_id, Option.map_id_fun, id_eq]

theorem getKey?_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey? k' =
    if k == k' then
      if (f (m.get? k)).isSome then some k else none
    else
      m.getKey? k' := by
  simp_to_model using List.getKey?_alterKey

theorem getKey!_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option (β k) → Option (β k)} :
    (m.alter k f).getKey! k' =
    if k == k' then
      if (f (m.get? k)).isSome then k else panic ""
    else
      m.getKey! k' := by
  simp [getKey!_eq_get!_getKey?, getKey?_alter, h, h.alter₀]
  split
  · next heq =>
    cases eq_of_beq heq
    split <;> rfl
  · next heq =>
    rfl

theorem getKey_alter [LawfulBEq α] [Inhabited α] {k k' : α} (h : m.1.WF) {f : Option (β k) → Option (β k)}
    (hc : (m.alter k f).contains k') :
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

variable {β : Type v} [EquivBEq α] [LawfulHashable α]

@[simp]
theorem isEmpty_modify (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.isEmpty = m.1.isEmpty := by
  simp_to_model using List.Const.isEmpty_modifyKey

@[simp]
theorem isEmpty_alter (m : Raw₀ α (fun _ => β)) (h : m.1.WF)  {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty ↔ (m.erase k).1.isEmpty ∧ f (Const.get? m k) = none := by
  simp_to_model using List.Const.isEmpty_alterKey

end Const
