/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.Impl.Operations

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

namespace Std.DTreeMap.Internal

namespace Impl

/-- Flattens a tree into a list of key-value pairs. This function is defined for verification
purposes and should not be executed because it is very inefficient. -/
def toListModel : Impl α β → List ((a : α) × β a)
  | .leaf => []
  | .inner _ k v l r => l.toListModel ++ ⟨k, v⟩ :: r.toListModel

/-- The tree map property. -/
def Ordered [Ord α] (t : Impl α β) : Prop :=
  t.toListModel.Pairwise (fun a b => compare a.1 b.1 = .lt)

/-- Well-formedness of tree maps. -/
inductive WF [Ord α] : Impl α β → Prop where
  /-- This is the actual well-formedness invariant: the tree must be a balanced BST. -/
  | wf {t} : Balanced t → (∀ [TransOrd α], Ordered t) → WF t
  /-- The empty tree is well-formed. Later shown to be subsumed by `.wf`. -/
  | empty : WF .empty
  /-- `insert` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | insert {t h k v} : WF t → WF (t.insert k v h).impl
  /-- `erase` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | erase {t h k} : WF t → WF (t.erase k h).impl
  /-- `containsThenInsert` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | containsThenInsert {t h k v} : WF t → WF (t.containsThenInsert k v h).2.impl

/-- A well-formed tree is balanced. This is needed here already because we need to know that the
tree is balanced to call the optimized modification functions. -/
theorem WF.balanced [Ord α] {t : Impl α β} (h : WF t) : t.Balanced := by
  cases h <;> try apply TreeB.balanced_impl
  case wf htb hto => exact htb
  case empty => exact balanced_empty

end Impl

end Std.DTreeMap.Internal

-- open Lean

-- run_meta do
--   let env ← getEnv
--   let mut arr : Array (Nat × Name × MessageData) := #[]
--   let mut unknown : Array Name := #[]
--   let mut totalSize : Nat := 0
--   for (name, info) in env.constants do
--     if (`Std.DTreeMap.Internal.Impl).isPrefixOf name then
--       if let some e := info.value? then
--         let numObjs ← e.numObjs
--         arr := arr.push (numObjs, (name, m!"{info.type}"))
--         totalSize := totalSize + numObjs
--       else
--         unknown := unknown.push name
--   arr := arr.qsort (fun a b => a.1 > b.1)
--   logInfo m!"total size: {totalSize}"
--   for (a, (b, c)) in arr do
--     logInfo m!"({a}, {b}, {c})"
