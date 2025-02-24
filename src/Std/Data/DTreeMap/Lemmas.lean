/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.Lemmas
import Std.Data.DTreeMap.Basic

/-!
# Dependent tree map lemmas

This file contains lemmas about `Std.Data.DTreeMap`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

open Std.DTreeMap.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.DTreeMap

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap α β cmp}

private theorem ext {t t' : DTreeMap α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : DTreeMap α β cmp).isEmpty :=
  Impl.isEmpty_empty

@[simp]
theorem isEmpty_insert [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).isEmpty = false :=
  Impl.isEmpty_insert t.wf

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr t.wf hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr t.wf hab

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew t.wf

@[simp]
theorem contains_emptyc {k : α} : (∅ : DTreeMap α β cmp).contains k = false :=
  Impl.contains_empty

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : DTreeMap α β cmp) :=
  Impl.not_mem_empty

theorem contains_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → t.contains a = false :=
  Impl.contains_of_isEmpty t.wf

theorem not_mem_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → a ∉ t :=
  Impl.not_mem_of_isEmpty t.wf

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  Impl.isEmpty_eq_false_iff_exists_contains_eq_true t.wf

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  Impl.isEmpty_eq_false_iff_exists_mem t.wf

theorem isEmpty_iff_forall_contains [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  Impl.isEmpty_iff_forall_contains t.wf

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  Impl.isEmpty_iff_forall_not_mem t.wf

@[simp]
theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : DTreeMap α β cmp).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [TransCmp cmp] {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insert t.wf

@[simp]
theorem mem_insert [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insert t.wf

theorem contains_insert_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).contains k :=
  Impl.contains_insert_self t.wf

theorem mem_insert_self [TransCmp cmp] {k : α} {v : β k} :
    k ∈ t.insert k v :=
  Impl.mem_insert_self t.wf

theorem contains_of_contains_insert [TransCmp cmp] {k a : α} {v : β k} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insert t.wf

theorem mem_of_mem_insert [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.mem_of_mem_insert t.wf

@[simp]
theorem size_emptyc : (∅ : DTreeMap α β cmp).size = 0 :=
  Impl.size_empty

theorem isEmpty_eq_size_eq_zero :
    t.isEmpty = (t.size == 0) :=
  Impl.isEmpty_eq_size_eq_zero t.wf

theorem size_insert [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  Impl.size_insert t.wf

theorem size_le_size_insert [TransCmp cmp] {k : α} {v : β k} :
    t.size ≤ (t.insert k v).size :=
  Impl.size_le_size_insert t.wf

theorem size_insert_le [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).size ≤ t.size + 1 :=
  Impl.size_insert_le t.wf

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : DTreeMap α β cmp).erase k = empty :=
  ext <| Impl.erase_empty (instOrd := ⟨cmp⟩) (k := k)

@[simp]
theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  Impl.isEmpty_erase t.wf

@[simp]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  Impl.contains_erase t.wf

@[simp]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  Impl.mem_erase t.wf

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  Impl.contains_of_contains_erase t.wf

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  Impl.mem_of_mem_erase t.wf

theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  Impl.size_erase t.wf

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  Impl.size_erase_le t.wf

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  Impl.size_le_size_erase t.wf

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsert k v).1 = t.contains k :=
  Impl.containsThenInsert_fst t.wf

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| Impl.containsThenInsert_snd t.wf

@[simp]
theorem containsThenInsertIfNew_fst [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  Impl.containsThenInsertIfNew_fst t.wf

@[simp]
theorem containsThenInsertIfNew_snd [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| Impl.containsThenInsertIfNew_snd t.wf

@[simp]
theorem contains_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insertIfNew t.wf

@[simp]
theorem mem_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insertIfNew t.wf

theorem contains_insertIfNew_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).contains k :=
  Impl.contains_insertIfNew_self t.wf

theorem mem_insertIfNew_self [TransCmp cmp] {k : α} {v : β k} :
    k ∈ t.insertIfNew k v :=
  Impl.mem_insertIfNew_self t.wf

theorem contains_of_contains_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insertIfNew t.wf

theorem mem_of_mem_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.contains_of_contains_insertIfNew t.wf

theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  Impl.size_insertIfNew t.wf

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  Impl.size_le_size_insertIfNew t.wf

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  Impl.size_insertIfNew_le t.wf

end Std.DTreeMap
