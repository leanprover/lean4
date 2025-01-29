/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.WF

/-!
# API lemmas for `DTreeMap.Impl`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.Internal.List
open Std.Internal

universe u v

namespace Std.DTreeMap.Internal.Impl

variable {α : Type u} {β : α → Type v} {_ : Ord α} {t : Impl α β}

/-- Internal implementation detail of the hash map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply WF.ordered | apply WF.balanced | apply WF.insert | apply WF.insertSlow
    | apply WF.erase
    | apply Ordered.distinctKeys
    | assumption
    ))

/-- Internal implementation detail of the hash map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``apply_isEmpty, ``apply_contains, ``apply_size]

private def modifyNames : Array Name :=
  #[``toListModel_insert, ``toListModel_insertSlow, ``toListModel_erase, ``toListModel_eraseSlow]

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

attribute [local instance] beqOfOrd
attribute [local instance] equivBEq_of_transOrd

theorem isEmpty_empty : isEmpty (empty : Impl α β) := by
  simp [Impl.apply_isEmpty]

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Iff.rfl

theorem contains_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : k == k') :
    t.contains k = t.contains k' := by
  simp_to_model using List.containsKey_congr

theorem mem_congr [TransOrd α] (h : t.WF) {k k' : α} (hab : k == k') : k ∈ t ↔ k' ∈ t := by
  simp [mem_iff_contains, contains_congr h hab]

theorem contains_empty {k : α} : (empty : Impl α β).contains k = false := by
  simp [contains, empty]

theorem mem_empty {k : α} : k ∉ (empty : Impl α β) := by
  simp [mem_iff_contains, contains_empty]

theorem isEmpty_insert [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v h.balanced).impl.isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntry

theorem isEmpty_insertSlow [TransOrd α] (h : t.WF) {k : α} {v : β k} :
    (t.insertSlow k v).isEmpty = false := by
  simp_to_model using List.isEmpty_insertEntry

theorem contains_insert [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v h.balanced).impl.contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model using List.containsKey_insertEntry

theorem contains_insertSlow [TransOrd α] (h : t.WF) {k a : α} {v : β k} :
    (t.insertSlow k v).contains a = (compare k a == .eq || t.contains a) := by
  simp_to_model using List.containsKey_insertEntry

theorem isEmpty_erase [TransOrd α] (h : t.WF) {k : α} :
    (t.erase k h.balanced).impl.isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model using List.isEmpty_eraseKey

theorem isEmpty_eraseSlow [TransOrd α] (h : t.WF) {k : α} :
    (t.eraseSlow k).isEmpty = (t.isEmpty || (t.size = 1 && t.contains k)) := by
  simp_to_model using List.isEmpty_eraseKey

-- theorem contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
--     (m.erase k).contains a = (!(k == a) && m.contains a) := by
--   simp_to_model using List.containsKey_eraseKey

-- theorem contains_of_contains_erase [EquivBEq α] [LawfulHashable α] (h : m.1.WF) {k a : α} :
--     (m.erase k).contains a → m.contains a := by
--   simp_to_model using List.containsKey_of_containsKey_eraseKey

end Std.DTreeMap.Internal.Impl

/-- Used as instance by the dependents of this file -/
theorem TransOrd.ofTransCmp {α : Type u} {cmp : α → α → Ordering} [TransCmp cmp] :
    letI _ : Ord α := ⟨cmp⟩; TransOrd α :=
  let _ : Ord α := ⟨cmp⟩
  have _ : OrientedOrd α := ⟨⟩
  ⟨TransCmp.le_trans⟩
