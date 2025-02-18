/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.Operations

/-!
# Well-formedness predicate on size-bounded trees

This file defines the well-formedness predicate `WF` on the internal size-bounded tree data
structure `Impl` and proves well-formedness for those operations that aren't per definition.

A central consequence of well-formedness, balancedness, is shown for all well-formed trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

namespace Std.DTreeMap.Internal

namespace Impl

/-- Well-formedness of tree maps. -/
inductive WF [Ord α] : {β : α → Type v} → Impl α β → Prop where
  /-- This is the actual well-formedness invariant: the tree must be a balanced BST. -/
  | wf {t} : Balanced t → (∀ [TransOrd α], Ordered t) → WF t
  /-- The empty tree is well-formed. Later shown to be subsumed by `.wf`. -/
  | empty : WF .empty
  /-- `insert` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | insert {t h k v} : WF t → WF (t.insert k v h).impl
  /-- `insertIfNew` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | insertIfNew {t h k v} : WF t → WF (t.insertIfNew k v h).impl
  /-- `erase` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | erase {t h k} : WF t → WF (t.erase k h).impl
  /-- `containsThenInsert` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | containsThenInsert {t h k v} : WF t → WF (t.containsThenInsert k v h).2.impl
  /-- `containsThenInsertIfNew` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | containsThenInsertIfNew {t h k v} : WF t → WF (t.containsThenInsertIfNew k v h).2.impl
  /-- `filter` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | filter {t h f} : WF t → WF (t.filter f h).impl
  /-- `mergeWith` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | mergeWith {t₁ t₂ f h} [LawfulEqOrd α] : WF t₁ → WF (t₁.mergeWith f t₂ h).impl
  /-- `mergeWith` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | constMergeWith {t₁ t₂ f h} : WF t₁ → WF (Impl.Const.mergeWith f t₁ t₂ h).impl

/--
A well-formed tree is balanced. This is needed here already because we need to know that the
tree is balanced to call the optimized modification functions.
-/
theorem WF.balanced [Ord α] {t : Impl α β} (h : WF t) : t.Balanced := by
  cases h <;> (try apply SizedBalancedTree.balanced_impl) <;> try apply BalancedTree.balanced_impl
  case wf htb hto => exact htb
  case empty => exact balanced_empty

theorem WF.eraseMany [Ord α] {ρ} [ForIn Id ρ α] {t : Impl α β} {l : ρ} {h} (hwf : WF t) :
    WF (t.eraseMany l h).val :=
  (t.eraseMany l h).2 hwf fun _ _ _ hwf' => hwf'.erase

theorem WF.insertMany [Ord α] {ρ} [ForIn Id ρ ((a : α) × β a)] {t : Impl α β} {l : ρ} {h} (hwf : WF t) :
    WF (t.insertMany l h).val :=
  (t.insertMany l h).2 hwf fun _ _ _ _ hwf' => hwf'.insert

theorem WF.constInsertMany [Ord α] {β : Type v} {ρ} [ForIn Id ρ (α × β)] {t : Impl α (fun _ => β)}
    {l : ρ} {h} (hwf : WF t) : WF (Impl.Const.insertMany t l h).val :=
  (Impl.Const.insertMany t l h).2 hwf fun _ _ _ _ hwf' => hwf'.insert

theorem WF.constInsertManyIfNewUnit [Ord α] {ρ} [ForIn Id ρ α] {t : Impl α (fun _ => Unit)} {l : ρ}
    {h} (hwf : WF t) : WF (Impl.Const.insertManyIfNewUnit t l h).val :=
  (Impl.Const.insertManyIfNewUnit t l h).2 hwf fun _ _ _ hwf' => hwf'.insertIfNew

end Impl

end Std.DTreeMap.Internal
