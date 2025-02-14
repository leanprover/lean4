/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.HashMap.Basic
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Internal lemmas about the tree map

This file contains internal lemmas about `Std.DTreeMap.Internal.Impl`. Users of the tree map should
not rely on the contents of this file.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.Internal.List
open Std.Internal

universe u v

namespace Std.DTreeMap.Internal.Impl

variable {α : Type u} {β : α → Type v} {instOrd : Ord α} {t : Impl α β}

/-- Internal implementation detail of the tree map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply WF.ordered | apply WF.balanced | apply WF.insert | apply WF.insert!
    | apply WF.insertIfNew | apply WF.insertIfNew!
    | apply WF.erase | apply WF.erase!
    | apply Ordered.distinctKeys
    | assumption
    ))

/-- Internal implementation detail of the tree map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``isEmpty_eq_isEmpty, ``contains_eq_containsKey, ``size_eq_length]

private def modifyMap : Std.HashMap Name Name :=
  .ofList
    [⟨`insert, ``toListModel_insert⟩,
     ⟨`insert!, ``toListModel_insert!⟩,
     ⟨`insertIfNew, ``toListModel_insertIfNew⟩,
     ⟨`insertIfNew!, ``toListModel_insertIfNew!⟩,
     ⟨`erase, ``toListModel_erase⟩,
     ⟨`erase!, ``toListModel_erase!⟩]

private def congrNames : MacroM (Array (TSyntax `term)) := do
  return #[← `(_root_.List.Perm.isEmpty_eq), ← `(containsKey_of_perm),
    ← `(_root_.List.Perm.length_eq), ← `(getValueCast?_of_perm _),
    ← `(getValue?_of_perm _), ← `(getValue_of_perm _), ← `(getValueCast_of_perm _),
    ← `(getValueCast!_of_perm _), ← `(getValueCastD_of_perm _), ← `(getValue!_of_perm _),
    ← `(getValueD_of_perm _), ← `(getKey?_of_perm _), ← `(getKey_of_perm _), ← `(getKeyD_of_perm _),
    ← `(getKey!_of_perm _)]

/-- Internal implementation detail of the tree map -/
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

attribute [local instance] beqOfOrd
attribute [local instance] equivBEq_of_transOrd

theorem isEmpty_empty : isEmpty (empty : Impl α β) := by
  simp [Impl.isEmpty_eq_isEmpty]

theorem isEmpty_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.isEmpty = false := by
  simp_to_model [insert] using List.isEmpty_insertEntry

theorem isEmpty_insert! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert! k v).isEmpty = false := by
  simp_to_model [insert!] using List.isEmpty_insertEntry

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Iff.rfl

theorem contains_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : compare k k' = .eq) :
    t.contains k = t.contains k' := by
  rw [← beq_iff_eq (b := Ordering.eq), ← beq_eq] at hab
  simp_to_model using List.containsKey_congr

theorem mem_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : compare k k' = .eq) :
    k ∈ t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_congr h hab]

theorem isEmpty_insertIfNew [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v h.balanced).impl.isEmpty = false := by
  simp_to_model [insertIfNew] using List.isEmpty_insertEntryIfNew

theorem isEmpty_insertIfNew! [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew! k v).isEmpty = false := by
  simp_to_model [insertIfNew!] using List.isEmpty_insertEntryIfNew

end Std.DTreeMap.Internal.Impl
