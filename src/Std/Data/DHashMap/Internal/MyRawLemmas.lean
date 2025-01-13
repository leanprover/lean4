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
    (m.modify k f).1.isEmpty ↔ m.1.isEmpty := by
  simp_to_model using List.isEmpty_modifyKey

@[simp]
theorem isEmpty_alter [LawfulBEq α] (h : m.1.WF) {k : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).1.isEmpty = ((m.erase k).1.isEmpty && (f (m.get? k)).isNone) := by
  simp_to_model using List.isEmpty_alterKey

theorem contains_alter [LawfulBEq α] (h : m.1.WF) {k k' : α} {f : Option (β k) → Option (β k)} :
    (m.alter k f).contains k' = if k == k' then (f (m.get? k)).isSome else m.contains k' := by
  simp_to_model using List.containsKey_alterKey

namespace Const

variable {β : Type v} [EquivBEq α] [LawfulHashable α]

@[simp]
theorem isEmpty_modify (m : Raw₀ α (fun _ => β)) (h : m.1.WF) {k : α} {f : β → β} :
    (Const.modify m k f).1.isEmpty ↔ m.1.isEmpty := by
  simp_to_model using List.Const.isEmpty_modifyKey

@[simp]
theorem isEmpty_alter (m : Raw₀ α (fun _ => β)) (h : m.1.WF)  {k : α} {f : Option β → Option β} :
    (Const.alter m k f).1.isEmpty ↔ (m.erase k).1.isEmpty ∧ f (Const.get? m k) = none := by
  simp_to_model using List.Const.isEmpty_alterKey

end Const
