/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
module

prelude
import Std.Data.DTreeMap.Raw.Lemmas
public import Std.Data.TreeMap.Raw.AdditionalOperations

@[expose] public section

/-!
# Tree map lemmas

This file contains lemmas about `Std.Data.TreeMap.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
These proofs can be obtained from `Std.Data.TreeMap.Raw.WF`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.TreeMap.Raw

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} {cmp : α → α → Ordering} {t : TreeMap.Raw α β cmp}

private theorem ext {t t' : Raw α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyc : (∅ : TreeMap.Raw α β cmp).isEmpty :=
  DTreeMap.Raw.isEmpty_emptyc

@[simp, grind =]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).isEmpty = false :=
  DTreeMap.Raw.isEmpty_insert h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DTreeMap.Raw.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {k : α} : t.contains k ↔ k ∈ t :=
  DTreeMap.Raw.contains_iff_mem

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  DTreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  DTreeMap.Raw.mem_congr h hab

@[simp, grind =]
theorem contains_emptyc {k : α} : (∅ : Raw α β cmp).contains k = false :=
  DTreeMap.Raw.contains_emptyc

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : Raw α β cmp) :=
  DTreeMap.Raw.not_mem_emptyc

theorem contains_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → t.contains a = false :=
  DTreeMap.Raw.contains_of_isEmpty h

theorem not_mem_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → a ∉ t :=
  DTreeMap.Raw.not_mem_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  DTreeMap.Raw.isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  DTreeMap.Raw.isEmpty_eq_false_iff_exists_mem h

theorem isEmpty_eq_false_of_contains [TransCmp cmp] (h : t.WF) {a : α} (hc : t.contains a = true) :
    t.isEmpty = false :=
  DTreeMap.Raw.isEmpty_eq_false_of_contains h hc

theorem isEmpty_iff_forall_contains [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  DTreeMap.Raw.isEmpty_iff_forall_contains h

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  DTreeMap.Raw.isEmpty_iff_forall_not_mem h

@[simp]
theorem insert_eq_insert {p : α × β} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : α × β} :
    Singleton.singleton p = (∅ : Raw α β cmp).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.Raw.contains_insert h

@[simp, grind =]
theorem mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  DTreeMap.Raw.mem_insert h

theorem contains_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).contains k :=
  DTreeMap.Raw.contains_insert_self h

theorem mem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    k ∈ t.insert k v :=
  DTreeMap.Raw.mem_insert_self h

theorem contains_of_contains_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  DTreeMap.Raw.contains_of_contains_insert h

theorem mem_of_mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  DTreeMap.Raw.mem_of_mem_insert h

@[simp, grind =]
theorem size_emptyc : (∅ : Raw α β cmp).size = 0 :=
  DTreeMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  DTreeMap.Raw.isEmpty_eq_size_eq_zero h.out

@[grind =] theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  DTreeMap.Raw.size_insert h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    t.size ≤ (t.insert k v).size :=
  DTreeMap.Raw.size_le_size_insert h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).size ≤ t.size + 1 :=
  DTreeMap.Raw.size_insert_le h

@[simp, grind =]
theorem erase_emptyc {k : α} :
    (∅ : Raw α β cmp).erase k = ∅ :=
  ext <| DTreeMap.Raw.erase_emptyc

@[simp, grind =]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  DTreeMap.Raw.isEmpty_erase h

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransCmp cmp] (h : t.WF) (k : α) :
    t.isEmpty = ((t.erase k).isEmpty && !(t.contains k)) :=
  DTreeMap.Raw.isEmpty_eq_isEmpty_erase_and_not_contains h k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransCmp cmp] (h : t.WF) {k : α}
    (he : (t.erase k).isEmpty = false) :
    t.isEmpty = false :=
  DTreeMap.Raw.isEmpty_eq_false_of_isEmpty_erase_eq_false h he

@[simp, grind =]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  DTreeMap.Raw.contains_erase h

@[simp, grind =]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  DTreeMap.Raw.mem_erase h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  DTreeMap.Raw.contains_of_contains_erase h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  DTreeMap.Raw.mem_of_mem_erase h

@[grind =] theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  DTreeMap.Raw.size_erase h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  DTreeMap.Raw.size_erase_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  DTreeMap.Raw.size_le_size_erase h

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsert k v).1 = t.contains k :=
  DTreeMap.Raw.containsThenInsert_fst h

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| DTreeMap.Raw.containsThenInsert_snd h

@[simp, grind =]
theorem containsThenInsertIfNew_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  DTreeMap.Raw.containsThenInsertIfNew_fst h

@[simp, grind =]
theorem containsThenInsertIfNew_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.Raw.containsThenInsertIfNew_snd h

@[simp, grind =] theorem get_eq_getElem {a : α} {h} : get t a h = t[a]'h := rfl
@[simp, grind =] theorem get?_eq_getElem? {a : α} : get? t a = t[a]? := rfl
@[simp, grind =] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! t a = t[a]! := rfl

@[simp, grind =]
theorem getElem?_emptyc [TransCmp cmp] {a : α} :
    (∅ : Raw α β cmp)[a]? = none :=
  DTreeMap.Raw.Const.get?_emptyc (cmp := cmp) (a := a)

theorem getElem?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t[a]? = none :=
  DTreeMap.Raw.Const.get?_of_isEmpty h

@[grind =] theorem getElem?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    (t.insert k v)[a]? = if cmp k a = .eq then some v else t[a]? :=
  DTreeMap.Raw.Const.get?_insert h

@[simp]
theorem getElem?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v)[k]? = some v :=
  DTreeMap.Raw.Const.get?_insert_self h

theorem contains_eq_isSome_getElem? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = t[a]?.isSome :=
  DTreeMap.Raw.Const.contains_eq_isSome_get? h

@[simp]
theorem isSome_getElem?_eq_contains [TransCmp cmp] (h : t.WF) {a : α} :
    t[a]?.isSome = t.contains a :=
  (contains_eq_isSome_getElem? h).symm

theorem mem_iff_isSome_getElem? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ t[a]?.isSome :=
  DTreeMap.Raw.Const.mem_iff_isSome_get? h

@[simp]
theorem isSome_getElem?_iff_mem [TransCmp cmp] (h : t.WF) {a : α} :
    t[a]?.isSome ↔ a ∈ t :=
  (mem_iff_isSome_getElem? h).symm

theorem getElem?_eq_some_iff [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    t[k]? = some v ↔ ∃ h, t[k] = v :=
  DTreeMap.Raw.Const.get?_eq_some_iff h

theorem getElem?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t[a]? = none :=
  DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false h

theorem getElem?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t[a]? = none :=
  DTreeMap.Raw.Const.get?_eq_none h

@[grind =] theorem getElem?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k)[a]? = if cmp k a = .eq then none else t[a]? :=
  DTreeMap.Raw.Const.get?_erase h

@[simp]
theorem getElem?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k)[k]? = none :=
  DTreeMap.Raw.Const.get?_erase_self h

theorem getElem?_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    t[a]? = t[b]? :=
  DTreeMap.Raw.Const.get?_congr h hab

@[grind =] theorem getElem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insert k v)[a]'h₁ =
      if h₂ : cmp k a = .eq then v
      else t[a]'(mem_of_mem_insert h h₁ h₂) :=
  DTreeMap.Raw.Const.get_insert h

theorem toList_insert_perm [BEq α] [TransCmp cmp] [LawfulBEqCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).toList.Perm (⟨k, v⟩ :: t.toList.filter (¬k == ·.1)) :=
  DTreeMap.Raw.Const.toList_insert_perm h

theorem keys_insertIfNew_perm {t : Raw α Unit cmp} [BEq α] [TransCmp cmp] [LawfulBEqCmp cmp] (h : t.WF) {k : α} :
    (t.insertIfNew k ()).keys.Perm (if k ∈ t then t.keys else k :: t.keys) :=
  DTreeMap.Raw.keys_insertIfNew_perm h

@[simp]
theorem getElem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v)[k]'(mem_insert_self h) = v :=
  DTreeMap.Raw.Const.get_insert_self h

@[simp, grind =]
theorem getElem_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k)[a]'h' = t[a]'(mem_of_mem_erase h h') :=
  DTreeMap.Raw.Const.get_erase h

theorem getElem?_eq_some_getElem [TransCmp cmp] (h : t.WF) {a : α} (h') :
    t[a]? = some (t[a]'h') :=
  DTreeMap.Raw.Const.get?_eq_some_get h h'

theorem getElem_eq_get_getElem? [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t[a] = t[a]?.get ((mem_iff_isSome_getElem? h).mp h') :=
  DTreeMap.Raw.Const.get_eq_get_get? h

@[grind =] theorem get_getElem? [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t[a]?.get h' = t[a]'((mem_iff_isSome_getElem? h).mpr h') :=
  DTreeMap.Raw.Const.get_get? h

theorem getElem_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((mem_congr h hab).mp h') :=
  DTreeMap.Raw.Const.get_congr h hab

@[simp, grind =]
theorem getElem!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    (∅ : Raw α β cmp)[a]! = default :=
  DTreeMap.Raw.Const.get!_emptyc (cmp := cmp) (a := a)

theorem getElem!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → t[a]! = default :=
  DTreeMap.Raw.Const.get!_of_isEmpty h

@[grind =] theorem getElem!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    (t.insert k v)[a]! = if cmp k a = .eq then v else t[a]! :=
  DTreeMap.Raw.Const.get!_insert h

@[simp]
theorem getElem!_insert_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α}
    {v : β} : (t.insert k v)[k]! = v :=
  DTreeMap.Raw.Const.get!_insert_self h

theorem getElem!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → t[a]! = default :=
  DTreeMap.Raw.Const.get!_eq_default_of_contains_eq_false h

theorem getElem!_eq_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → t[a]! = default :=
  DTreeMap.Raw.Const.get!_eq_default h

@[grind =] theorem getElem!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
    (t.erase k)[a]! = if cmp k a = .eq then default else t[a]! :=
  DTreeMap.Raw.Const.get!_erase h

@[simp]
theorem getElem!_erase_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} :
    (t.erase k)[k]! = default :=
  DTreeMap.Raw.Const.get!_erase_self h

theorem getElem?_eq_some_getElem!_of_contains [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → t[a]? = some t[a]! :=
  DTreeMap.Raw.Const.get?_eq_some_get! h

theorem getElem?_eq_some_getElem! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → t[a]? = some t[a]! :=
  DTreeMap.Raw.Const.get?_eq_some_get! h

theorem getElem!_eq_get!_getElem? [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t[a]! = t[a]?.get! :=
  DTreeMap.Raw.Const.get!_eq_get!_get? h

theorem getElem_eq_getElem! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} {h'} :
    t[a]'h' = t[a]! :=
  DTreeMap.Raw.Const.get_eq_get! h

theorem getElem!_congr [TransCmp cmp] [Inhabited β] (h : t.WF) {a b : α}
    (hab : cmp a b = .eq) : t[a]! = t[b]! :=
  DTreeMap.Raw.Const.get!_congr h hab

@[simp, grind =]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  DTreeMap.Raw.Const.getD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_of_isEmpty h

@[grind =] theorem getD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  DTreeMap.Raw.Const.getD_insert h

@[simp]
theorem getD_insert_self [TransCmp cmp] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  DTreeMap.Raw.Const.getD_insert_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_eq_fallback h

@[grind =] theorem getD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  DTreeMap.Raw.Const.getD_erase h

@[simp]
theorem getD_erase_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  DTreeMap.Raw.Const.getD_erase_self h

theorem getElem?_eq_some_getD_of_contains [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → t[a]? = some (getD t a fallback) :=
  DTreeMap.Raw.Const.get?_eq_some_getD_of_contains h

theorem getElem?_eq_some_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → t[a]? = some (getD t a fallback) :=
  DTreeMap.Raw.Const.get?_eq_some_getD h

theorem getD_eq_getD_getElem? [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t[a]?.getD fallback :=
  DTreeMap.Raw.Const.getD_eq_getD_get? h

theorem getElem_eq_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} {h'} :
    t[a]'h' = getD t a fallback :=
  DTreeMap.Raw.Const.get_eq_getD h

theorem getElem!_eq_getD_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t[a]! = getD t a default :=
  DTreeMap.Raw.Const.get!_eq_getD_default h

theorem getD_congr [TransCmp cmp] (h : t.WF) {a b : α} {fallback : β}
    (hab : cmp a b = .eq) : getD t a fallback = getD t b fallback :=
  DTreeMap.Raw.Const.getD_congr h hab

@[simp, grind =]
theorem getKey?_emptyc {a : α} : (∅ : Raw α β cmp).getKey? a = none :=
  DTreeMap.Raw.getKey?_emptyc

theorem getKey?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  DTreeMap.Raw.getKey?_of_isEmpty h

@[grind =] theorem getKey?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  DTreeMap.Raw.getKey?_insert h

@[simp]
theorem getKey?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).getKey? k = some k :=
  DTreeMap.Raw.getKey?_insert_self h

theorem contains_eq_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  DTreeMap.Raw.contains_eq_isSome_getKey? h

@[simp, grind =]
theorem isSome_getKey?_eq_contains [TransCmp cmp] (h : t.WF) {a : α} :
    (t.getKey? a).isSome = t.contains a :=
  (contains_eq_isSome_getKey? h).symm

theorem mem_iff_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  DTreeMap.Raw.mem_iff_isSome_getKey? h

@[simp]
theorem isSome_getKey?_iff_mem [TransCmp cmp] (h : t.WF) {a : α} :
    (t.getKey? a).isSome ↔ a ∈ t :=
  (mem_iff_isSome_getKey? h).symm

theorem mem_of_getKey?_eq_some [TransCmp cmp] (h : t.WF) {a a' : α} :
    t.getKey? a = some a' → a' ∈ t :=
  DTreeMap.Raw.mem_of_getKey?_eq_some h

theorem getKey?_eq_some_iff [TransCmp cmp] (h : t.WF) {k k' : α} :
    getKey? t k = some k' ↔ ∃ h, getKey t k h = k' :=
  DTreeMap.Raw.getKey?_eq_some_iff h

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none :=
  DTreeMap.Raw.getKey?_eq_none_of_contains_eq_false h

theorem getKey?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  DTreeMap.Raw.getKey?_eq_none h

@[grind =] theorem getKey?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  DTreeMap.Raw.getKey?_erase h

@[simp]
theorem getKey?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).getKey? k = none :=
  DTreeMap.Raw.getKey?_erase_self h

theorem compare_getKey?_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.getKey? k).all (cmp · k = .eq) :=
  DTreeMap.Raw.compare_getKey?_self h

theorem getKey?_congr [TransCmp cmp] (h : t.WF) {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey? k = t.getKey? k' :=
  DTreeMap.Raw.getKey?_congr h h'

theorem getKey?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    (h' : t.contains k) :
    t.getKey? k = some k :=
  DTreeMap.Raw.getKey?_eq_some_of_contains h h'

theorem getKey?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    t.getKey? k = some k :=
  DTreeMap.Raw.getKey?_eq_some_of_contains h h'

@[grind =] theorem getKey_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h h₁ h₂) :=
  DTreeMap.Raw.getKey_insert h

@[simp]
theorem getKey_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).getKey k (mem_insert_self h) = k :=
  DTreeMap.Raw.getKey_insert_self h

@[simp, grind =]
theorem getKey_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h h') :=
  DTreeMap.Raw.getKey_erase h

theorem getKey?_eq_some_getKey [TransCmp cmp] (h : t.WF) {a : α} (h') :
    t.getKey? a = some (t.getKey a h') :=
  DTreeMap.Raw.getKey?_eq_some_getKey h h'

theorem getKey_eq_get_getKey? [TransCmp cmp] (h : t.WF) {a : α} {h' : a ∈ t} :
    t.getKey a h' = (t.getKey? a).get ((mem_iff_isSome_getKey? h).mp h') :=
  DTreeMap.Raw.getKey_eq_get_getKey? h.out

@[simp, grind =]
theorem get_getKey? [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    (t.getKey? a).get h' = t.getKey a ((mem_iff_isSome_getKey? h).mpr h') :=
  DTreeMap.Raw.get_getKey? h.out

theorem compare_getKey_self [TransCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    cmp (t.getKey k h') k = .eq :=
  DTreeMap.Raw.compare_getKey_self h h'

theorem getKey_congr [TransCmp cmp] (h : t.WF) {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h h').mp h₁) :=
  DTreeMap.Raw.getKey_congr h h' h₁

@[simp, grind =]
theorem getKey_eq [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    t.getKey k h' = k :=
  DTreeMap.Raw.getKey_eq h h'

@[simp, grind =]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : Raw α β cmp).getKey! a = default :=
  DTreeMap.Raw.getKey!_emptyc

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  DTreeMap.Raw.getKey!_of_isEmpty h

@[grind =] theorem getKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
    {v : β} : (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  DTreeMap.Raw.getKey!_insert h

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α}
    {b : β} : (t.insert a b).getKey! a = a :=
  DTreeMap.Raw.getKey!_insert_self h

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey! a = default :=
  DTreeMap.Raw.getKey!_eq_default_of_contains_eq_false h

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  DTreeMap.Raw.getKey!_eq_default h

@[grind =] theorem getKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  DTreeMap.Raw.getKey!_erase h

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k).getKey! k = default :=
  DTreeMap.Raw.getKey!_erase_self h

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  DTreeMap.Raw.getKey?_eq_some_getKey!_of_contains h

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  DTreeMap.Raw.getKey?_eq_some_getKey! h

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  DTreeMap.Raw.getKey!_eq_get!_getKey? h

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {h'} :
    t.getKey a h' = t.getKey! a :=
  DTreeMap.Raw.getKey_eq_getKey! h

theorem getKey!_congr [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey! k = t.getKey! k' :=
  DTreeMap.Raw.getKey!_congr h h'

theorem getKey!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    (h' : t.contains k) :
    t.getKey! k = k :=
  DTreeMap.Raw.getKey!_eq_of_contains h h'

theorem getKey!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    (h' : k ∈ t) :
    t.getKey! k = k :=
  DTreeMap.Raw.getKey!_eq_of_mem h h'

@[simp, grind =]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : Raw α β cmp).getKeyD a fallback = fallback :=
  DTreeMap.Raw.getKeyD_emptyc

theorem getKeyD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  DTreeMap.Raw.getKeyD_of_isEmpty h

@[grind =] theorem getKeyD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} {v : β} :
    (t.insert k v).getKeyD a fallback =
      if cmp k a = .eq then k else t.getKeyD a fallback :=
  DTreeMap.Raw.getKeyD_insert h

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] (h : t.WF) {a fallback : α} {b : β} :
    (t.insert a b).getKeyD a fallback = a :=
  DTreeMap.Raw.getKeyD_insert_self h

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  DTreeMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_eq_fallback [TransCmp cmp] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  DTreeMap.Raw.getKeyD_eq_fallback h

@[grind =] theorem getKeyD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  DTreeMap.Raw.getKeyD_erase h

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] (h : t.WF) {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  DTreeMap.Raw.getKeyD_erase_self h

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  DTreeMap.Raw.getKey?_eq_some_getKeyD_of_contains h

theorem getKey?_eq_some_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} :
  a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  DTreeMap.Raw.getKey?_eq_some_getKeyD h

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  DTreeMap.Raw.getKeyD_eq_getD_getKey? h

theorem getKey_eq_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} {h'} :
    t.getKey a h' = t.getKeyD a fallback :=
  DTreeMap.Raw.getKey_eq_getKeyD h

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = t.getKeyD a default :=
  DTreeMap.Raw.getKey!_eq_getKeyD_default h

theorem getKeyD_congr [TransCmp cmp] (h : t.WF) {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getKeyD k fallback = t.getKeyD k' fallback :=
  DTreeMap.Raw.getKeyD_congr h h'

theorem getKeyD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k fallback : α}
    (h' : t.contains k) :
    t.getKeyD k fallback = k :=
  DTreeMap.Raw.getKeyD_eq_of_contains h h'

theorem getKeyD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k fallback : α} (h' : k ∈ t) :
    t.getKeyD k fallback = k :=
  DTreeMap.Raw.getKeyD_eq_of_contains h h'

@[simp, grind =]
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).isEmpty = false :=
  DTreeMap.Raw.isEmpty_insertIfNew h

@[simp, grind =]
theorem contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.Raw.contains_insertIfNew h

@[simp, grind =]
theorem mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  DTreeMap.Raw.mem_insertIfNew h

theorem contains_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).contains k :=
  DTreeMap.Raw.contains_insertIfNew_self h

theorem mem_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    k ∈ t.insertIfNew k v :=
  DTreeMap.Raw.mem_insertIfNew_self h

theorem contains_of_contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  DTreeMap.Raw.contains_of_contains_insertIfNew h

theorem mem_of_mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  DTreeMap.Raw.contains_of_contains_insertIfNew h

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] (h : t.WF) {k a : α}
    {v : β} :
    a ∈ (t.insertIfNew k v) → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  DTreeMap.Raw.mem_of_mem_insertIfNew' h

@[grind =] theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.Raw.size_insertIfNew h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  DTreeMap.Raw.size_le_size_insertIfNew h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  DTreeMap.Raw.size_insertIfNew_le h

@[grind =] theorem getElem?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v)[a]? =
      if cmp k a = .eq ∧ ¬ k ∈ t then
        some v
      else
        t[a]? :=
  DTreeMap.Raw.Const.get?_insertIfNew h

@[grind =] theorem getElem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v)[a]'h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        v
      else
        t[a]'(mem_of_mem_insertIfNew' h h₁ h₂) :=
  DTreeMap.Raw.Const.get_insertIfNew h

@[grind =] theorem getElem!_insertIfNew [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v)[a]! = if cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]! :=
  DTreeMap.Raw.Const.get!_insertIfNew h

@[grind =] theorem getD_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  DTreeMap.Raw.Const.getD_insertIfNew h

@[grind =] theorem getKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  DTreeMap.Raw.getKey?_insertIfNew h

@[grind =] theorem getKey_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  DTreeMap.Raw.getKey_insertIfNew h

@[grind =] theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
    {v : β} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  DTreeMap.Raw.getKey!_insertIfNew h

@[grind =] theorem getKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k a fallback : α}
    {v : β} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  DTreeMap.Raw.getKeyD_insertIfNew h

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = t[k]? :=
  DTreeMap.Raw.Const.getThenInsertIfNew?_fst h

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.Raw.Const.getThenInsertIfNew?_snd h

@[simp, grind =]
theorem length_keys [TransCmp cmp] (h : t.WF) :
    t.keys.length = t.size :=
  DTreeMap.Raw.length_keys h

@[simp, grind =]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty :=
  DTreeMap.Raw.isEmpty_keys

@[simp, grind =]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    t.keys.contains k = t.contains k :=
  DTreeMap.Raw.contains_keys h

@[simp, grind =]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  DTreeMap.Raw.mem_keys h

theorem mem_of_mem_keys [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.keys → k ∈ t :=
  DTreeMap.Raw.mem_of_mem_keys h

theorem distinct_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.Raw.distinct_keys h

theorem nodup_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Nodup :=
  (t.distinct_keys h).imp Std.ReflCmp.ne_of_cmp_ne_eq

theorem ordered_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Pairwise (fun a b => cmp a b = .lt) :=
  DTreeMap.Raw.ordered_keys h

@[simp, grind _=_]
theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  DTreeMap.Raw.Const.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList (h : t.WF) :
    (toList t).length = t.size :=
  DTreeMap.Raw.Const.length_toList h

@[simp, grind =]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  DTreeMap.Raw.Const.isEmpty_toList

@[simp, grind =]
theorem mem_toList_iff_getElem?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t[k]? = some v :=
  DTreeMap.Raw.Const.mem_toList_iff_get?_eq_some h

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ t[k]? = some v :=
  DTreeMap.Raw.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some h

theorem getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] (h : t.WF) {k : α}
    {v : β} :
    t[k]? = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  DTreeMap.Raw.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList h

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some [TransCmp cmp] (h : t.WF)
    {k k' : α} {v : β} :
    t.toList.find? (cmp ·.1 k == .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ t[k]? = some v :=
  DTreeMap.Raw.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some h

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] (h : t.WF) {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  DTreeMap.Raw.Const.find?_toList_eq_none_iff_contains_eq_false h

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] (h : t.WF) {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  DTreeMap.Raw.Const.find?_toList_eq_none_iff_not_mem h

theorem distinct_keys_toList [TransCmp cmp] (h : t.WF) :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  DTreeMap.Raw.Const.distinct_keys_toList h

theorem ordered_keys_toList [TransCmp cmp] (h : t.WF) :
    (toList t).Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  DTreeMap.Raw.Const.ordered_keys_toList h

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init :=
  DTreeMap.Raw.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init :=
  DTreeMap.Raw.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : α → β → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init :=
  DTreeMap.Raw.Const.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList {f : α → β → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init :=
  DTreeMap.Raw.Const.foldr_eq_foldr_toList

@[simp, grind =]
theorem forM_eq_forM [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    ForM.forM t f = t.toList.forM f :=
  DTreeMap.Raw.Const.forMUncurried_eq_forM_toList (f := f)

@[simp, grind =]
theorem forIn_eq_forIn [Monad m] [LawfulMonad m] {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init (fun a d => f a.1 a.2 d) := rfl

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α × β → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  DTreeMap.Raw.Const.forInUncurried_eq_forIn_toList

theorem foldlM_eq_foldlM_keys [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init :=
  DTreeMap.Raw.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init :=
  DTreeMap.Raw.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init :=
  DTreeMap.Raw.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init :=
  DTreeMap.Raw.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t (fun a => f a.1) = t.keys.forM f :=
  DTreeMap.Raw.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m] [LawfulMonad m]
    {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init (fun a d => f a.1 d) = ForIn.forIn t.keys init f :=
  DTreeMap.Raw.forIn_eq_forIn_keys

end monadic

@[simp, grind =]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton {k : α} {v : β} :
    t.insertMany [⟨k, v⟩] = t.insert k v :=
  rfl

@[grind _=_] theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    t.insertMany (⟨k, v⟩ :: l) = (t.insert k v).insertMany l :=
  ext <| DTreeMap.Raw.Const.insertMany_cons

@[grind _=_] theorem insertMany_append {l₁ l₂ : List (α × β)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  DTreeMap.Raw.Const.contains_insertMany_list h

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Prod.fst).contains k :=
  DTreeMap.Raw.Const.mem_insertMany_list h

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ t.insertMany l → (l.map Prod.fst).contains k = false → k ∈ t :=
  DTreeMap.Raw.Const.mem_of_mem_insertMany_list h

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k :=
  DTreeMap.Raw.Const.getKey?_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKey? k' = some k :=
  DTreeMap.Raw.Const.getKey?_insertMany_list_of_mem h k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  DTreeMap.Raw.Const.getKey_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k :=
  DTreeMap.Raw.Const.getKey_insertMany_list_of_mem h k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k :=
  DTreeMap.Raw.Const.getKey!_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKey! k' = k :=
  DTreeMap.Raw.Const.getKey!_insertMany_list_of_mem h k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback :=
  DTreeMap.Raw.Const.getKeyD_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKeyD k' fallback = k :=
  DTreeMap.Raw.Const.getKeyD_insertMany_list_of_mem h k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length :=
  DTreeMap.Raw.Const.size_insertMany_list h distinct

theorem size_le_size_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    t.size ≤ (t.insertMany l).size :=
  DTreeMap.Raw.Const.size_le_size_insertMany_list h

grind_pattern size_le_size_insertMany_list => (t.insertMany l).size

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  DTreeMap.Raw.Const.size_insertMany_list_le h

grind_pattern size_insertMany_list_le => (t.insertMany l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  DTreeMap.Raw.Const.isEmpty_insertMany_list h

theorem getElem?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l)[k]? = t[k]? :=
  DTreeMap.Raw.Const.get?_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getElem?_insertMany_list_of_mem [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l)[k']? = some v :=
  DTreeMap.Raw.Const.get?_insertMany_list_of_mem h k_eq distinct mem

@[grind =] theorem getElem?_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α} :
    (insertMany t l)[k]? =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).or t[k]? :=
  DTreeMap.Raw.Const.get?_insertMany_list h

theorem getElem_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α}
    (contains : (l.map Prod.fst).contains k = false)
    {h'} :
    (t.insertMany l)[k]'h' =
    t.get k (mem_of_mem_insertMany_list h h' contains) :=
  DTreeMap.Raw.Const.get_insertMany_list_of_contains_eq_false h contains

theorem getElem_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l)[k']'h' = v :=
  DTreeMap.Raw.Const.get_insertMany_list_of_mem h k_eq distinct mem

theorem getElem_insertMany_list [TransCmp cmp] [BEq α] [PartialEquivBEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α} {h'} :
    (insertMany t l)[k]'h' =
      match w : l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none) with
      | some v => v
      | none => t[k]'(mem_of_mem_insertMany_list h h' (by simpa [LawfulBEqCmp.compare_eq_iff_beq, BEq.comm] using w)) :=
  DTreeMap.Raw.Const.get_insertMany_list h

theorem getElem!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l)[k]! = t.get! k :=
  DTreeMap.Raw.Const.get!_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getElem!_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l)[k']! = v :=
  DTreeMap.Raw.Const.get!_insertMany_list_of_mem h k_eq distinct mem

theorem getElem!_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited β]
    (h : t.WF) {l : List (α × β)} {k : α} :
    (insertMany t l)[k]! =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).getD t[k]! :=
  DTreeMap.Raw.Const.get!_insertMany_list h

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback :=
  DTreeMap.Raw.Const.getD_insertMany_list_of_contains_eq_false h contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = v :=
  DTreeMap.Raw.Const.getD_insertMany_list_of_mem h k_eq distinct mem

theorem getD_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α} {fallback : β} :
    (insertMany t l).getD k fallback =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).getD (t.getD k fallback) :=
  DTreeMap.Raw.Const.getD_insertMany_list h

section Unit

variable {t : Raw α Unit cmp}

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit t [] = t :=
  rfl

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit t [k] = t.insertIfNew k () :=
  rfl

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    insertManyIfNewUnit t (k :: l) = insertManyIfNewUnit (t.insertIfNew k ()) l :=
  ext <| DTreeMap.Raw.Const.insertManyIfNewUnit_cons

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) :=
  DTreeMap.Raw.Const.contains_insertManyIfNewUnit_list h

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k :=
  DTreeMap.Raw.Const.mem_insertManyIfNewUnit_list h

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t :=
  DTreeMap.Raw.Const.mem_of_mem_insertManyIfNewUnit_list h contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit t l) k = none :=
  DTreeMap.Raw.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit t l) k' = some k :=
  DTreeMap.Raw.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} (mem : k ∈ t) :
    getKey? (insertManyIfNewUnit t l) k = getKey? t k :=
  DTreeMap.Raw.Const.getKey?_insertManyIfNewUnit_list_of_mem h mem

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains :=
  DTreeMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_mem h contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} (not_mem : ¬ k ∈ t)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey (insertManyIfNewUnit t l) k' h' = k :=
  DTreeMap.Raw.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] (h : t.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit t l) k = default :=
  DTreeMap.Raw.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit t l) k' = k :=
  DTreeMap.Raw.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k : α} (mem : k ∈ t):
    getKey! (insertManyIfNewUnit t l) k = getKey! t k :=
  DTreeMap.Raw.Const.getKey!_insertManyIfNewUnit_list_of_mem h mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit t l) k fallback = fallback :=
  DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit t l) k' fallback = k :=
  DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k fallback : α} (mem : k ∈ t) :
    getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback :=
  DTreeMap.Raw.Const.getKeyD_insertManyIfNewUnit_list_of_mem h mem

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length :=
  DTreeMap.Raw.Const.size_insertManyIfNewUnit_list h distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp] (h : t.WF)
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size :=
  DTreeMap.Raw.Const.size_le_size_insertManyIfNewUnit_list h

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp] (h : t.WF)
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length :=
  DTreeMap.Raw.Const.size_insertManyIfNewUnit_list_le h

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] (h : t.WF) {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  DTreeMap.Raw.Const.isEmpty_insertManyIfNewUnit_list h

@[simp]
theorem getElem?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l)[k]? = if k ∈ t ∨ l.contains k then some () else none :=
  DTreeMap.Raw.Const.get?_insertManyIfNewUnit_list h

@[simp]
theorem getElem_insertManyIfNewUnit_list {l : List α} {k : α} {h'} :
    (insertManyIfNewUnit t l)[k]'h' = () :=
  rfl

@[simp]
theorem getElem!_insertManyIfNewUnit_list {l : List α} {k : α} :
    (insertManyIfNewUnit t l)[k]! = () :=
  rfl

@[simp]
theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit t l) k fallback = () :=
  rfl

end Unit

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List (α × β)) cmp = ∅ := by
  rfl

@[simp, grind =]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] cmp = (∅ : Raw α β cmp).insert k v := by
  rfl

@[grind _=_] theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : Raw α β cmp).insert k v) tl :=
  ext DTreeMap.Raw.Const.ofList_cons

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l cmp = insertMany (∅ : Raw α β cmp) l :=
  ext DTreeMap.Raw.Const.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  DTreeMap.Raw.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Prod.fst).contains k :=
  DTreeMap.Raw.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp)[k]? = none :=
  DTreeMap.Raw.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp)[k']? = some v :=
  DTreeMap.Raw.Const.get?_ofList_of_mem k_eq distinct mem

theorem getElem_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l cmp)[k']'h = v :=
  DTreeMap.Raw.Const.get_ofList_of_mem k_eq distinct mem

theorem getElem!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp)[k]! = default :=
  DTreeMap.Raw.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp)[k']! = v :=
  DTreeMap.Raw.Const.get!_ofList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  DTreeMap.Raw.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l cmp) k' fallback = v :=
  DTreeMap.Raw.Const.getD_ofList_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  DTreeMap.Raw.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey? k' = some k :=
  DTreeMap.Raw.Const.getKey?_ofList_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  DTreeMap.Raw.Const.getKey_ofList_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  DTreeMap.Raw.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey! k' = k :=
  DTreeMap.Raw.Const.getKey!_ofList_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  DTreeMap.Raw.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  DTreeMap.Raw.Const.getKeyD_ofList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  DTreeMap.Raw.Const.size_ofList distinct

theorem size_ofList_le [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).size ≤ l.length :=
  DTreeMap.Raw.Const.size_ofList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp, grind =]
theorem isEmpty_ofList [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  DTreeMap.Raw.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) cmp =
      (∅ : Raw α Unit cmp) :=
  rfl

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] cmp = (∅ : Raw α Unit cmp).insertIfNew k () :=
  rfl

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) cmp =
      insertManyIfNewUnit ((∅ : Raw α Unit cmp).insertIfNew hd ()) tl :=
  ext DTreeMap.Raw.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp).contains k = l.contains k :=
  DTreeMap.Raw.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ unitOfList l cmp ↔ l.contains k := by
  simp [← contains_iff_mem]

theorem getKey?_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l cmp) k = none :=
  DTreeMap.Raw.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (unitOfList l cmp) k' = some k :=
  DTreeMap.Raw.Const.getKey?_unitOfList_of_mem k_eq distinct mem

theorem getKey_unitOfList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l cmp) k' h' = k :=
  DTreeMap.Raw.Const.getKey_unitOfList_of_mem k_eq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l cmp) k = default :=
  DTreeMap.Raw.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKey! (unitOfList l cmp) k' = k :=
  DTreeMap.Raw.Const.getKey!_unitOfList_of_mem k_eq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l cmp) k fallback = fallback :=
  DTreeMap.Raw.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKeyD (unitOfList l cmp) k' fallback = k :=
  DTreeMap.Raw.Const.getKeyD_unitOfList_of_mem k_eq distinct mem

theorem size_unitOfList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (unitOfList l cmp).size = l.length :=
  DTreeMap.Raw.Const.size_unitOfList distinct

theorem size_unitOfList_le [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).size ≤ l.length :=
  DTreeMap.Raw.Const.size_unitOfList_le

@[simp]
theorem isEmpty_unitOfList [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).isEmpty = l.isEmpty :=
  DTreeMap.Raw.Const.isEmpty_unitOfList

@[simp]
theorem getElem?_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp)[k]? = if l.contains k then some () else none :=
  DTreeMap.Raw.Const.get?_unitOfList

@[simp]
theorem getElem_unitOfList {l : List α} {k : α} {h} :
    (unitOfList l cmp)[k]'h = () :=
  DTreeMap.Raw.Const.get_unitOfList

@[simp]
theorem getElem!_unitOfList {l : List α} {k : α} :
    (unitOfList l cmp)[k]! = () :=
  DTreeMap.Raw.Const.get!_unitOfList

@[simp]
theorem getD_unitOfList {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l cmp) k fallback = () :=
  DTreeMap.Raw.Const.getD_unitOfList

section Union

variable (t₁ t₂ : Raw α β cmp)

variable {t₁ t₂}

@[simp]
theorem union_eq : t₁.union t₂ = t₁ ∪ t₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    (t₁ ∪ t₂).contains k = (t₁.contains k || t₂.contains k) :=
  DTreeMap.Raw.contains_union h₁ h₂

/- mem -/
theorem mem_union_of_left [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    k ∈ t₁ → k ∈ t₁ ∪ t₂ :=
  DTreeMap.Raw.mem_union_of_left h₁ h₂

theorem mem_union_of_right [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    k ∈ t₂ → k ∈ t₁ ∪ t₂ :=
  DTreeMap.Raw.mem_union_of_right h₁ h₂

@[simp]
theorem mem_union_iff [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    k ∈ t₁ ∪ t₂ ↔ k ∈ t₁ ∨ k ∈ t₂ :=
  DTreeMap.Raw.mem_union_iff h₁ h₂

theorem mem_of_mem_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₂ → k ∈ t₁ :=
  DTreeMap.Raw.mem_of_mem_union_of_not_mem_right h₁ h₂

theorem mem_of_mem_union_of_not_mem_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₁ → k ∈ t₂ :=
  DTreeMap.Raw.mem_of_mem_union_of_not_mem_left h₁ h₂

/- Equiv -/
theorem Equiv.union_left {t₃ : Raw α β cmp} [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (equiv : t₁.Equiv t₂) :
    (t₁ ∪ t₃).Equiv (t₂ ∪ t₃) :=
  ⟨DTreeMap.Raw.Equiv.union_left h₁ h₂ h₃ equiv.1⟩

theorem Equiv.union_right {t₃ : Raw α β cmp} [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (equiv : t₂.Equiv t₃) :
    (t₁ ∪ t₂).Equiv (t₁ ∪ t₃) :=
  ⟨DTreeMap.Raw.Equiv.union_right h₁ h₂ h₃ equiv.1⟩

theorem Equiv.union_congr {t₃ t₄ : Raw α β cmp} [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (h₄ : t₄.WF)
    (equiv₁ : t₁.Equiv t₃) (equiv₂ : t₂.Equiv t₄) :
    (t₁ ∪ t₂).Equiv (t₃ ∪ t₄) :=
  ⟨DTreeMap.Raw.Equiv.union_congr h₁ h₂ h₃ h₄ equiv₁.1 equiv₂.1⟩

theorem union_insert_right_equiv_insert_union [TransCmp cmp] {p : (_ : α) × β}
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ ∪ (t₂.insert p.fst p.snd)).Equiv ((t₁ ∪ t₂).insert p.fst p.snd) :=
  ⟨DTreeMap.Raw.union_insert_right_equiv_insert_union h₁ h₂⟩

/- getElem? -/
theorem getElem?_union [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} :
    (t₁ ∪ t₂)[k]? = (t₂[k]?).or (t₁[k]?) :=
  DTreeMap.Raw.Const.get?_union h₁ h₂

theorem getElem?_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂)[k]? = t₂[k]? :=
  DTreeMap.Raw.Const.get?_union_of_not_mem_left h₁ h₂ not_mem

theorem getElem?_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂)[k]? = t₁[k]? :=
  DTreeMap.Raw.Const.get?_union_of_not_mem_right h₁ h₂ not_mem

/- get? -/
@[deprecated getElem?_union (since := "2025-12-10")]
theorem get?_union [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} :
    (t₁ ∪ t₂).get? k = (t₂.get? k).or (t₁.get? k) :=
  DTreeMap.Raw.Const.get?_union h₁ h₂

@[deprecated getElem?_union_of_not_mem_left (since := "2025-12-10")]
theorem get?_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get? k = t₂.get? k :=
  DTreeMap.Raw.Const.get?_union_of_not_mem_left h₁ h₂ not_mem

@[deprecated getElem?_union_of_not_mem_right (since := "2025-12-10")]
theorem get?_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).get? k = t₁.get? k :=
  DTreeMap.Raw.Const.get?_union_of_not_mem_right h₁ h₂ not_mem

/- getElem -/
theorem getElem_union_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)[k]'(mem_union_of_right h₁ h₂ mem) = t₂[k]'mem :=
  DTreeMap.Raw.Const.get_union_of_mem_right h₁ h₂ mem

theorem getElem_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂)[k]'h' = t₂[k]'(mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  DTreeMap.Raw.Const.get_union_of_not_mem_left h₁ h₂ not_mem

theorem getElem_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂)[k]'h' = t₁[k]'(mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  DTreeMap.Raw.Const.get_union_of_not_mem_right h₁ h₂ not_mem

/- get -/
@[deprecated getElem_union_of_mem_right (since := "2025-12-10")]
theorem get_union_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).get k (mem_union_of_right h₁ h₂ mem) = t₂.get k mem :=
  DTreeMap.Raw.Const.get_union_of_mem_right h₁ h₂ mem

@[deprecated getElem_union_of_not_mem_left (since := "2025-12-10")]
theorem get_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).get k h' = t₂.get k (mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  DTreeMap.Raw.Const.get_union_of_not_mem_left h₁ h₂ not_mem

@[deprecated getElem_union_of_not_mem_right (since := "2025-12-10")]
theorem get_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂).get k h' = t₁.get k (mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  DTreeMap.Raw.Const.get_union_of_not_mem_right h₁ h₂ not_mem

/- getD -/
theorem getD_union [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k (t₁.getD k fallback) :=
  DTreeMap.Raw.Const.getD_union h₁ h₂

theorem getD_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k fallback :=
  DTreeMap.Raw.Const.getD_union_of_not_mem_left h₁ h₂ not_mem

theorem getD_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback :=
  DTreeMap.Raw.Const.getD_union_of_not_mem_right h₁ h₂ not_mem

/- getElem! -/
theorem getElem!_union [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} [Inhabited β] :
    (t₁ ∪ t₂)[k]! = t₂.getD k (t₁[k]!) :=
  DTreeMap.Raw.Const.get!_union h₁ h₂

theorem getElem!_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} [Inhabited β] (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂)[k]! = t₂[k]! :=
  DTreeMap.Raw.Const.get!_union_of_not_mem_left h₁ h₂ not_mem

theorem getElem!_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} [Inhabited β] (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂)[k]! = t₁[k]! :=
  DTreeMap.Raw.Const.get!_union_of_not_mem_right h₁ h₂ not_mem

/- get! -/
@[deprecated getElem!_union (since := "2025-12-10")]
theorem get!_union [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} [Inhabited β] :
    (t₁ ∪ t₂).get! k = t₂.getD k (t₁.get! k) :=
  DTreeMap.Raw.Const.get!_union h₁ h₂

@[deprecated getElem!_union_of_not_mem_left (since := "2025-12-10")]
theorem get!_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} [Inhabited β] (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get! k = t₂.get! k :=
  DTreeMap.Raw.Const.get!_union_of_not_mem_left h₁ h₂ not_mem

@[deprecated getElem!_union_of_not_mem_right (since := "2025-12-10")]
theorem get!_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} [Inhabited β] (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂).get! k = t₁.get! k :=
  DTreeMap.Raw.Const.get!_union_of_not_mem_right h₁ h₂ not_mem

/- getKey? -/
theorem getKey?_union [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} :
    (t₁ ∪ t₂).getKey? k = (t₂.getKey? k).or (t₁.getKey? k) :=
  DTreeMap.Raw.getKey?_union h₁ h₂

theorem getKey?_union_of_not_mem_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKey? k = t₂.getKey? k :=
  DTreeMap.Raw.getKey?_union_of_not_mem_left h₁ h₂ not_mem

theorem getKey?_union_of_not_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKey? k = t₁.getKey? k :=
  DTreeMap.Raw.getKey?_union_of_not_mem_right h₁ h₂ not_mem

/- getKey -/
theorem getKey_union_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).getKey k (mem_union_of_right h₁ h₂ mem) = t₂.getKey k mem :=
  DTreeMap.Raw.getKey_union_of_mem_right h₁ h₂ mem

theorem getKey_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).getKey k h' = t₂.getKey k (mem_of_mem_union_of_not_mem_left h₁ h₂ h' not_mem) :=
  DTreeMap.Raw.getKey_union_of_not_mem_left h₁ h₂ not_mem

theorem getKey_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂).getKey k h' = t₁.getKey k (mem_of_mem_union_of_not_mem_right h₁ h₂ h' not_mem) :=
  DTreeMap.Raw.getKey_union_of_not_mem_right h₁ h₂ not_mem

/- getKeyD -/
theorem getKeyD_union [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} :
    (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k (t₁.getKeyD k fallback) :=
  DTreeMap.Raw.getKeyD_union h₁ h₂

theorem getKeyD_union_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k fallback :=
  DTreeMap.Raw.getKeyD_union_of_not_mem_left h₁ h₂ mem

theorem getKeyD_union_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKeyD k fallback = t₁.getKeyD k fallback :=
   DTreeMap.Raw.getKeyD_union_of_not_mem_right h₁ h₂ mem

/- getKey! -/
theorem getKey!_union [TransCmp cmp] [Inhabited α]
    (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    (t₁ ∪ t₂).getKey! k = t₂.getKeyD k (t₁.getKey! k) :=
  DTreeMap.Raw.getKey!_union h₁ h₂

theorem getKey!_union_of_not_mem_left [Inhabited α]
    [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α}
    (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKey! k = t₂.getKey! k :=
  DTreeMap.Raw.getKey!_union_of_not_mem_left h₁ h₂ not_mem

theorem getKey!_union_of_not_mem_right [Inhabited α]
    [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α}
    (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKey! k = t₁.getKey! k :=
  DTreeMap.Raw.getKey!_union_of_not_mem_right h₁ h₂ not_mem

/- size -/
theorem size_union_of_not_mem [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) : (∀ (a : α), a ∈ t₁ → ¬a ∈ t₂) →
    (t₁ ∪ t₂).size = t₁.size + t₂.size :=
  DTreeMap.Raw.size_union_of_not_mem h₁ h₂

theorem size_left_le_size_union [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) : t₁.size ≤ (t₁ ∪ t₂).size :=
  DTreeMap.Raw.size_left_le_size_union h₁ h₂

theorem size_right_le_size_union [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) : t₂.size ≤ (t₁ ∪ t₂).size :=
  DTreeMap.Raw.size_right_le_size_union h₁ h₂

theorem size_union_le_size_add_size [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ ∪ t₂).size ≤ t₁.size + t₂.size :=
  DTreeMap.Raw.size_union_le_size_add_size h₁ h₂

/- isEmpty -/
@[simp]
theorem isEmpty_union [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ ∪ t₂).isEmpty = (t₁.isEmpty && t₂.isEmpty) :=
  DTreeMap.Raw.isEmpty_union h₁ h₂

end Union

section Inter

variable {t₁ t₂ : Raw α β cmp}

@[simp]
theorem inter_eq : t₁.inter t₂ = t₁ ∩ t₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂).contains k = (t₁.contains k && t₂.contains k) :=
  DTreeMap.Raw.contains_inter h₁ h₂

/- mem -/
@[simp]
theorem mem_inter_iff [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ :=
  DTreeMap.Raw.mem_inter_iff h₁ h₂

theorem not_mem_inter_of_not_mem_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ ∩ t₂ :=
  DTreeMap.Raw.not_mem_inter_of_not_mem_left h₁ h₂ not_mem

theorem not_mem_inter_of_not_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α}
    (not_mem : k ∉ t₂) :
    k ∉ t₁ ∩ t₂ :=
  DTreeMap.Raw.not_mem_inter_of_not_mem_right h₁ h₂ not_mem

/- Equiv -/

theorem Equiv.inter_left [TransCmp cmp] {t₃ : Raw α β cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (equiv : t₁ ~m t₂) :
    (t₁ ∩ t₃).Equiv (t₂ ∩ t₃) :=
  ⟨DTreeMap.Raw.Equiv.inter_left h₁ h₂ h₃ equiv.1⟩

theorem Equiv.inter_right [TransCmp cmp] {t₃ : Raw α β cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (equiv : t₂ ~m t₃) :
    (t₁ ∩ t₂).Equiv (t₁ ∩ t₃) :=
  ⟨DTreeMap.Raw.Equiv.inter_right h₁ h₂ h₃ equiv.1⟩

theorem Equiv.inter_congr [TransCmp cmp] {t₃ t₄ : Raw α β cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (h₄ : t₄.WF)
    (equiv₁ : t₁ ~m t₃) (equiv₂ : t₂ ~m t₄) :
    (t₁ ∩ t₂).Equiv (t₃ ∩ t₄) :=
  ⟨DTreeMap.Raw.Equiv.inter_congr h₁ h₂ h₃ h₄ equiv₁.1 equiv₂.1⟩

/- getElem? -/
theorem getElem?_inter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂)[k]? = if k ∈ t₂ then t₁[k]? else none :=
  DTreeMap.Raw.Const.get?_inter h₁ h₂

theorem getElem?_inter_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂)[k]? = t₁[k]? :=
  DTreeMap.Raw.Const.get?_inter_of_mem_right h₁ h₂ mem

theorem getElem?_inter_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂)[k]? = none :=
  DTreeMap.Raw.Const.get?_inter_of_not_mem_left h₁ h₂ not_mem

theorem getElem?_inter_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂)[k]? = none :=
  DTreeMap.Raw.Const.get?_inter_of_not_mem_right h₁ h₂ not_mem

/- get? -/
@[deprecated getElem?_inter (since := "2025-12-10")]
theorem get?_inter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂).get? k = if k ∈ t₂ then t₁.get? k else none :=
  DTreeMap.Raw.Const.get?_inter h₁ h₂

@[deprecated getElem?_inter_of_mem_right (since := "2025-12-10")]
theorem get?_inter_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get? k = t₁.get? k :=
  DTreeMap.Raw.Const.get?_inter_of_mem_right h₁ h₂ mem

@[deprecated getElem?_inter_of_not_mem_left (since := "2025-12-10")]
theorem get?_inter_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get? k = none :=
  DTreeMap.Raw.Const.get?_inter_of_not_mem_left h₁ h₂ not_mem

@[deprecated getElem?_inter_of_not_mem_right (since := "2025-12-10")]
theorem get?_inter_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get? k = none :=
  DTreeMap.Raw.Const.get?_inter_of_not_mem_right h₁ h₂ not_mem

/- getElem -/
@[simp]
theorem getElem_inter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂)[k]'h_mem = t₁[k]'((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  DTreeMap.Raw.Const.get_inter h₁ h₂

/- get -/
@[deprecated getElem_inter (since := "2025-12-10")]
theorem get_inter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).get k h_mem = t₁.get k ((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  DTreeMap.Raw.Const.get_inter h₁ h₂

/- getD -/
theorem getD_inter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} :
    (t₁ ∩ t₂).getD k fallback =
    if k ∈ t₂ then t₁.getD k fallback else fallback :=
  DTreeMap.Raw.Const.getD_inter h₁ h₂

theorem getD_inter_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getD k fallback = t₁.getD k fallback :=
  DTreeMap.Raw.Const.getD_inter_of_mem_right h₁ h₂ mem

theorem getD_inter_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  DTreeMap.Raw.Const.getD_inter_of_not_mem_right h₁ h₂ not_mem

theorem getD_inter_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  DTreeMap.Raw.Const.getD_inter_of_not_mem_left h₁ h₂ not_mem

/- getElem! -/
theorem getElem!_inter [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂)[k]! = if k ∈ t₂ then t₁[k]! else default :=
  DTreeMap.Raw.Const.get!_inter h₁ h₂

theorem getElem!_inter_of_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂)[k]! = t₁[k]! :=
  DTreeMap.Raw.Const.get!_inter_of_mem_right h₁ h₂ mem

theorem getElem!_inter_of_not_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂)[k]! = default :=
  DTreeMap.Raw.Const.get!_inter_of_not_mem_right h₁ h₂ not_mem

theorem getElem!_inter_of_not_mem_left [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂)[k]! = default :=
  DTreeMap.Raw.Const.get!_inter_of_not_mem_left h₁ h₂ not_mem

/- get! -/
@[deprecated getElem!_inter (since := "2025-12-10")]
theorem get!_inter [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂).get! k = if k ∈ t₂ then t₁.get! k else default :=
  DTreeMap.Raw.Const.get!_inter h₁ h₂

@[deprecated getElem!_inter_of_mem_right (since := "2025-12-10")]
theorem get!_inter_of_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get! k = t₁.get! k :=
  DTreeMap.Raw.Const.get!_inter_of_mem_right h₁ h₂ mem

@[deprecated getElem!_inter_of_not_mem_right (since := "2025-12-10")]
theorem get!_inter_of_not_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get! k = default :=
  DTreeMap.Raw.Const.get!_inter_of_not_mem_right h₁ h₂ not_mem

@[deprecated getElem!_inter_of_not_mem_left (since := "2025-12-10")]
theorem get!_inter_of_not_mem_left [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get! k = default :=
  DTreeMap.Raw.Const.get!_inter_of_not_mem_left h₁ h₂ not_mem

/- getKey? -/
theorem getKey?_inter [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂).getKey? k =
    if k ∈ t₂ then t₁.getKey? k else none :=
  DTreeMap.Raw.getKey?_inter h₁ h₂

theorem getKey?_inter_of_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getKey? k = t₁.getKey? k :=
  DTreeMap.Raw.getKey?_inter_of_mem_right h₁ h₂ mem

theorem getKey?_inter_of_not_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getKey? k = none :=
  DTreeMap.Raw.getKey?_inter_of_not_mem_right h₁ h₂ not_mem

theorem getKey?_inter_of_not_mem_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getKey? k = none :=
  DTreeMap.Raw.getKey?_inter_of_not_mem_left h₁ h₂ not_mem

/- getKey -/
@[simp]
theorem getKey_inter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).getKey k h_mem =
    t₁.getKey k ((mem_inter_iff h₁ h₂).1 h_mem).1 :=
  DTreeMap.Raw.getKey_inter h₁ h₂

/- getKeyD -/
theorem getKeyD_inter [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} :
    (t₁ ∩ t₂).getKeyD k fallback =
    if k ∈ t₂ then t₁.getKeyD k fallback else fallback :=
  DTreeMap.Raw.getKeyD_inter h₁ h₂

theorem getKeyD_inter_of_mem_right [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getKeyD k fallback = t₁.getKeyD k fallback :=
  DTreeMap.Raw.getKeyD_inter_of_mem_right h₁ h₂ mem

theorem getKeyD_inter_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getKeyD k fallback = fallback :=
  DTreeMap.Raw.getKeyD_inter_of_not_mem_right h₁ h₂ not_mem

theorem getKeyD_inter_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getKeyD k fallback = fallback :=
  DTreeMap.Raw.getKeyD_inter_of_not_mem_left h₁ h₂ not_mem

/- getKey! -/
theorem getKey!_inter [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    (t₁ ∩ t₂).getKey! k =
    if k ∈ t₂ then t₁.getKey! k else default :=
  DTreeMap.Raw.getKey!_inter h₁ h₂

theorem getKey!_inter_of_mem_right [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getKey! k = t₁.getKey! k :=
  DTreeMap.Raw.getKey!_inter_of_mem_right h₁ h₂ mem

theorem getKey!_inter_of_not_mem_right [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getKey! k = default :=
  DTreeMap.Raw.getKey!_inter_of_not_mem_right h₁ h₂ not_mem

theorem getKey!_inter_of_not_mem_left [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getKey! k = default :=
  DTreeMap.Raw.getKey!_inter_of_not_mem_left h₁ h₂ not_mem

/- size -/
theorem size_inter_le_size_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ ∩ t₂).size ≤ t₁.size :=
  DTreeMap.Raw.size_inter_le_size_left h₁ h₂

theorem size_inter_le_size_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ ∩ t₂).size ≤ t₂.size :=
  DTreeMap.Raw.size_inter_le_size_right h₁ h₂

theorem size_inter_eq_size_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ (a : α), a ∈ t₁ → a ∈ t₂) :
    (t₁ ∩ t₂).size = t₁.size :=
  DTreeMap.Raw.size_inter_eq_size_left h₁ h₂ h

theorem size_inter_eq_size_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ (a : α), a ∈ t₂ → a ∈ t₁) :
    (t₁ ∩ t₂).size = t₂.size :=
  DTreeMap.Raw.size_inter_eq_size_right h₁ h₂ h

theorem size_add_size_eq_size_union_add_size_inter [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁.size + t₂.size = (t₁ ∪ t₂).size + (t₁ ∩ t₂).size :=
  DTreeMap.Raw.size_add_size_eq_size_union_add_size_inter h₁ h₂

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  DTreeMap.Raw.isEmpty_inter_left h₁ h₂ h

@[simp]
theorem isEmpty_inter_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₂.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  DTreeMap.Raw.isEmpty_inter_right h₁ h₂ h

theorem isEmpty_inter_iff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ ∩ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∉ t₂ :=
  DTreeMap.Raw.isEmpty_inter_iff h₁ h₂

end Inter

section
variable {β : Type v} {m₁ m₂ : Raw α β cmp}

theorem Const.Equiv.beq [TransCmp cmp] [BEq β] [ReflBEq β] (h₁ : m₁.WF) (h₂ : m₂.WF) (h : m₁ ~m m₂) : m₁ == m₂ :=
  DTreeMap.Raw.Const.Equiv.beq h₁ h₂ h.1

theorem Const.equiv_of_beq [TransCmp cmp] [LawfulEqCmp cmp] [BEq β] [LawfulBEq β] (h₁ : m₁.WF) (h₂ : m₂.WF) (k : m₁ == m₂) : m₁ ~m m₂ :=
  ⟨DTreeMap.Raw.Const.equiv_of_beq h₁.1 h₂.1 k⟩

theorem Const.Equiv.beq_congr [TransCmp cmp] [BEq β] {m₃ m₄ : Raw α β cmp} (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) (h₄ : m₄.WF) (w₁ : m₁ ~m m₃) (w₂ : m₂ ~m m₄) : (m₁ == m₂) = (m₃ == m₄) :=
  DTreeMap.Raw.Const.Equiv.beq_congr h₁ h₂ h₃ h₄ w₁.1 w₂.1

end

section Diff

variable {t₁ t₂ : Raw α β cmp}

@[simp]
theorem diff_eq : t₁.diff t₂ = t₁ \ t₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂).contains k = (t₁.contains k && !t₂.contains k) :=
  DTreeMap.Raw.contains_diff h₁ h₂

/- mem -/
@[simp]
theorem mem_diff_iff [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    k ∈ t₁ \ t₂ ↔ k ∈ t₁ ∧ k ∉ t₂ :=
  DTreeMap.Raw.mem_diff_iff h₁ h₂

theorem not_mem_diff_of_not_mem_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ \ t₂ :=
  DTreeMap.Raw.not_mem_diff_of_not_mem_left h₁ h₂ not_mem

theorem not_mem_diff_of_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α}
    (mem : k ∈ t₂) :
    k ∉ t₁ \ t₂ :=
  DTreeMap.Raw.not_mem_diff_of_mem_right h₁ h₂ mem

/- Equiv -/

theorem Equiv.diff_left [TransCmp cmp] {t₃ : Raw α β cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (equiv : t₁ ~m t₂) :
    (t₁ \ t₃).Equiv (t₂ \ t₃) :=
  ⟨DTreeMap.Raw.Equiv.diff_left h₁ h₂ h₃ equiv.1⟩

theorem Equiv.diff_right [TransCmp cmp] {t₃ : Raw α β cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (equiv : t₂ ~m t₃) :
    (t₁ \ t₂).Equiv (t₁ \ t₃) :=
  ⟨DTreeMap.Raw.Equiv.diff_right h₁ h₂ h₃ equiv.1⟩

theorem Equiv.diff_congr [TransCmp cmp] {t₃ t₄ : Raw α β cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h₃ : t₃.WF) (h₄ : t₄.WF)
    (equiv₁ : t₁ ~m t₃) (equiv₂ : t₂ ~m t₄) :
    (t₁ \ t₂).Equiv (t₃ \ t₄) :=
  ⟨DTreeMap.Raw.Equiv.diff_congr h₁ h₂ h₃ h₄ equiv₁.1 equiv₂.1⟩

/- getElem? -/
theorem getElem?_diff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂)[k]? = if k ∈ t₂ then none else t₁[k]? :=
  DTreeMap.Raw.Const.get?_diff h₁ h₂

theorem getElem?_diff_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂)[k]? = t₁[k]? :=
  DTreeMap.Raw.Const.get?_diff_of_not_mem_right h₁ h₂ not_mem

theorem getElem?_diff_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂)[k]? = none :=
  DTreeMap.Raw.Const.get?_diff_of_not_mem_left h₁ h₂ not_mem

theorem getElem?_diff_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂)[k]? = none :=
  DTreeMap.Raw.Const.get?_diff_of_mem_right h₁ h₂ mem

/- get? -/
@[deprecated getElem?_diff (since := "2025-12-10")]
theorem get?_diff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂).get? k = if k ∈ t₂ then none else t₁.get? k :=
  DTreeMap.Raw.Const.get?_diff h₁ h₂

@[deprecated getElem?_diff_of_not_mem_right (since := "2025-12-10")]
theorem get?_diff_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get? k = t₁.get? k :=
  DTreeMap.Raw.Const.get?_diff_of_not_mem_right h₁ h₂ not_mem

@[deprecated getElem?_diff_of_not_mem_left (since := "2025-12-10")]
theorem get?_diff_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get? k = none :=
  DTreeMap.Raw.Const.get?_diff_of_not_mem_left h₁ h₂ not_mem

@[deprecated getElem?_diff_of_mem_right (since := "2025-12-10")]
theorem get?_diff_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get? k = none :=
  DTreeMap.Raw.Const.get?_diff_of_mem_right h₁ h₂ mem

/- getElem -/
theorem getElem_diff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂)[k]'h_mem = t₁[k]'((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  DTreeMap.Raw.Const.get_diff h₁ h₂

/- get -/
@[deprecated getElem_diff (since := "2025-12-10")]
theorem get_diff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).get k h_mem = t₁.get k ((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  DTreeMap.Raw.Const.get_diff h₁ h₂

/- getD -/
theorem getD_diff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} :
    (t₁ \ t₂).getD k fallback =
    if k ∈ t₂ then fallback else t₁.getD k fallback :=
  DTreeMap.Raw.Const.getD_diff h₁ h₂

theorem getD_diff_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getD k fallback = t₁.getD k fallback :=
  DTreeMap.Raw.Const.getD_diff_of_not_mem_right h₁ h₂ not_mem

theorem getD_diff_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (mem : k ∈ t₂) :
    (t₁ \ t₂).getD k fallback = fallback :=
  DTreeMap.Raw.Const.getD_diff_of_mem_right h₁ h₂ mem

theorem getD_diff_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {fallback : β} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getD k fallback = fallback :=
  DTreeMap.Raw.Const.getD_diff_of_not_mem_left h₁ h₂ not_mem

/- getElem! -/
theorem getElem!_diff [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂)[k]! = if k ∈ t₂ then default else t₁[k]! :=
  DTreeMap.Raw.Const.get!_diff h₁ h₂

theorem getElem!_diff_of_not_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂)[k]! = t₁[k]! :=
  DTreeMap.Raw.Const.get!_diff_of_not_mem_right h₁ h₂ not_mem

theorem getElem!_diff_of_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂)[k]! = default :=
  DTreeMap.Raw.Const.get!_diff_of_mem_right h₁ h₂ mem

theorem getElem!_diff_of_not_mem_left [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂)[k]! = default :=
  DTreeMap.Raw.Const.get!_diff_of_not_mem_left h₁ h₂ not_mem

/- get! -/
@[deprecated getElem!_diff (since := "2025-12-10")]
theorem get!_diff [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂).get! k = if k ∈ t₂ then default else t₁.get! k :=
  DTreeMap.Raw.Const.get!_diff h₁ h₂

@[deprecated getElem!_diff_of_not_mem_right (since := "2025-12-10")]
theorem get!_diff_of_not_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get! k = t₁.get! k :=
  DTreeMap.Raw.Const.get!_diff_of_not_mem_right h₁ h₂ not_mem

@[deprecated getElem!_diff_of_mem_right (since := "2025-12-10")]
theorem get!_diff_of_mem_right [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get! k = default :=
  DTreeMap.Raw.Const.get!_diff_of_mem_right h₁ h₂ mem

@[deprecated getElem!_diff_of_not_mem_left (since := "2025-12-10")]
theorem get!_diff_of_not_mem_left [TransCmp cmp] [Inhabited β] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get! k = default :=
  DTreeMap.Raw.Const.get!_diff_of_not_mem_left h₁ h₂ not_mem

/- getKey? -/
theorem getKey?_diff [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂).getKey? k =
    if k ∈ t₂ then none else t₁.getKey? k :=
  DTreeMap.Raw.getKey?_diff h₁ h₂

theorem getKey?_diff_of_not_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getKey? k = t₁.getKey? k :=
  DTreeMap.Raw.getKey?_diff_of_not_mem_right h₁ h₂ not_mem

theorem getKey?_diff_of_not_mem_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getKey? k = none :=
  DTreeMap.Raw.getKey?_diff_of_not_mem_left h₁ h₂ not_mem

theorem getKey?_diff_of_mem_right [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getKey? k = none :=
  DTreeMap.Raw.getKey?_diff_of_mem_right h₁ h₂ mem

/- getKey -/
theorem getKey_diff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).getKey k h_mem =
    t₁.getKey k ((mem_diff_iff h₁ h₂).1 h_mem).1 :=
  DTreeMap.Raw.getKey_diff h₁ h₂

/- getKeyD -/
theorem getKeyD_diff [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} :
    (t₁ \ t₂).getKeyD k fallback =
    if k ∈ t₂ then fallback else t₁.getKeyD k fallback :=
  DTreeMap.Raw.getKeyD_diff h₁ h₂

theorem getKeyD_diff_of_not_mem_right [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getKeyD k fallback = t₁.getKeyD k fallback :=
  DTreeMap.Raw.getKeyD_diff_of_not_mem_right h₁ h₂ not_mem

theorem getKeyD_diff_of_mem_right [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getKeyD k fallback = fallback :=
  DTreeMap.Raw.getKeyD_diff_of_mem_right h₁ h₂ mem

theorem getKeyD_diff_of_not_mem_left [TransCmp cmp] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getKeyD k fallback = fallback :=
  DTreeMap.Raw.getKeyD_diff_of_not_mem_left h₁ h₂ not_mem

/- getKey! -/
theorem getKey!_diff [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} :
    (t₁ \ t₂).getKey! k =
    if k ∈ t₂ then default else t₁.getKey! k :=
  DTreeMap.Raw.getKey!_diff h₁ h₂

theorem getKey!_diff_of_not_mem_right [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getKey! k = t₁.getKey! k :=
  DTreeMap.Raw.getKey!_diff_of_not_mem_right h₁ h₂ not_mem

theorem getKey!_diff_of_mem_right [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getKey! k = default :=
  DTreeMap.Raw.getKey!_diff_of_mem_right h₁ h₂ mem

theorem getKey!_diff_of_not_mem_left [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF)
    (h₂ : t₂.WF) {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getKey! k = default :=
  DTreeMap.Raw.getKey!_diff_of_not_mem_left h₁ h₂ not_mem

/- size -/
theorem size_diff_le_size_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ \ t₂).size ≤ t₁.size :=
  DTreeMap.Raw.size_diff_le_size_left h₁ h₂

theorem size_diff_eq_size_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ (a : α), a ∈ t₁ → a ∉ t₂) :
    (t₁ \ t₂).size = t₁.size :=
  DTreeMap.Raw.size_diff_eq_size_left h₁ h₂ h

theorem size_diff_add_size_inter_eq_size_left [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ \ t₂).size + (t₁ ∩ t₂).size = t₁.size :=
  DTreeMap.Raw.size_diff_add_size_inter_eq_size_left h₁ h₂

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁.isEmpty) :
    (t₁ \ t₂).isEmpty = true :=
  DTreeMap.Raw.isEmpty_diff_left h₁ h₂ h

theorem isEmpty_diff_iff [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    (t₁ \ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∈ t₂ :=
  DTreeMap.Raw.isEmpty_diff_iff h₁ h₂

end Diff

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α}
    {f : Option β → Option β} :
    (alter t k f).isEmpty = ((t.erase k).isEmpty && (f t[k]?).isNone) :=
   DTreeMap.Raw.Const.isEmpty_alter_eq_isEmpty_erase h

@[simp, grind =]
theorem isEmpty_alter [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f t[k]?).isNone) :=
  DTreeMap.Raw.Const.isEmpty_alter h

@[grind =] theorem contains_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f).contains k' =
      if cmp k k' = .eq then (f t[k]?).isSome else t.contains k' :=
  DTreeMap.Raw.Const.contains_alter h

@[grind =] theorem mem_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    k' ∈ alter t k f ↔
      if cmp k k' = .eq then (f t[k]?).isSome = true else k' ∈ t :=
  DTreeMap.Raw.Const.mem_alter h

theorem mem_alter_of_compare_eq [TransCmp cmp] (h : t.WF) {k k': α} {f : Option β → Option β}
    (he : cmp k k' = .eq) :
    k' ∈ alter t k f ↔ (f t[k]?).isSome :=
  DTreeMap.Raw.Const.mem_alter_of_compare_eq h he

@[simp]
theorem contains_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).contains k = (f t[k]?).isSome :=
  DTreeMap.Raw.Const.contains_alter_self h

@[simp]
theorem mem_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    k ∈ alter t k f ↔ (f t[k]?).isSome :=
  DTreeMap.Raw.Const.mem_alter_self h

theorem contains_alter_of_not_compare_eq [TransCmp cmp] (h : t.WF) {k k' : α}
    {f : Option β → Option β} (he : ¬ cmp k k' = .eq) :
    (alter t k f).contains k' = t.contains k' :=
  DTreeMap.Raw.Const.contains_alter_of_not_compare_eq h he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β}
    (he : ¬ cmp k k' = .eq) :
    k' ∈ alter t k f ↔ k' ∈ t :=
  DTreeMap.Raw.Const.mem_alter_of_not_compare_eq h he

@[grind =]
theorem size_alter [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).size =
      if k ∈ t ∧ (f t[k]?).isNone then
        t.size - 1
      else if k ∉ t ∧ (f t[k]?).isSome then
        t.size + 1
      else
        t.size :=
  DTreeMap.Raw.Const.size_alter h

theorem size_alter_eq_add_one [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f t[k]?).isSome) :
    (alter t k f).size = t.size + 1 :=
  DTreeMap.Raw.Const.size_alter_eq_add_one h h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f t[k]?).isNone) :
    (alter t k f).size = t.size - 1 :=
  DTreeMap.Raw.Const.size_alter_eq_sub_one h h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f t[k]?).isNone) :
    (alter t k f).size = t.size :=
  DTreeMap.Raw.Const.size_alter_eq_self_of_not_mem h h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f t[k]?).isSome) :
    (alter t k f).size = t.size :=
  DTreeMap.Raw.Const.size_alter_eq_self_of_mem h h₁ h₂

theorem size_alter_le_size [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).size ≤ t.size + 1 :=
  DTreeMap.Raw.Const.size_alter_le_size h

theorem size_le_size_alter [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter t k f).size :=
  DTreeMap.Raw.Const.size_le_size_alter h

@[grind =]
theorem getElem?_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f)[k']? =
      if cmp k k' = .eq then
        f t[k]?
      else
        t[k']? :=
  DTreeMap.Raw.Const.get?_alter h

@[simp]
theorem getElem?_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f)[k]? = f t[k]? :=
  DTreeMap.Raw.Const.get?_alter_self h

@[grind =]
theorem getElem_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter t k f)} :
    (alter t k f)[k']'hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f t[k]?).isSome := mem_alter_of_compare_eq h heq |>.mp hc
        f t[k]? |>.get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        t[k']'h' :=
  DTreeMap.Raw.Const.get_alter h

@[simp]
theorem getElem_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    haveI h' : (f t[k]?).isSome := mem_alter_self h |>.mp hc
    (alter t k f)[k]'hc = (f t[k]?).get h' :=
  DTreeMap.Raw.Const.get_alter_self h

@[grind =]
theorem getElem!_alter [TransCmp cmp] (h : t.WF) {k k' : α} [Inhabited β] {f : Option β → Option β} :
    (alter t k f)[k']! =
      if cmp k k' = .eq then
        f t[k]? |>.get!
      else
        t[k']! :=
  DTreeMap.Raw.Const.get!_alter h

@[simp]
theorem getElem!_alter_self [TransCmp cmp] (h : t.WF) {k : α} [Inhabited β] {f : Option β → Option β} :
    (alter t k f)[k]! = (f t[k]?).get! :=
  DTreeMap.Raw.Const.get!_alter_self h

@[grind =]
theorem getD_alter [TransCmp cmp] (h : t.WF) {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter t k f) k' fallback =
      if cmp k k' = .eq then
        f t[k]? |>.getD fallback
      else
        getD t k' fallback :=
  DTreeMap.Raw.Const.getD_alter h

@[simp]
theorem getD_alter_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter t k f) k fallback = (f t[k]?).getD fallback :=
  DTreeMap.Raw.Const.getD_alter_self h

@[grind =]
theorem getKey?_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey? k' =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then some k else none
      else
        t.getKey? k' :=
  DTreeMap.Raw.Const.getKey?_alter h

theorem getKey?_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).getKey? k = if (f t[k]?).isSome then some k else none :=
  DTreeMap.Raw.Const.getKey?_alter_self h

@[grind =]
theorem getKey!_alter [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey! k' =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then k else default
      else
        t.getKey! k' :=
  DTreeMap.Raw.Const.getKey!_alter h

theorem getKey!_alter_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    {f : Option β → Option β} :
    (alter t k f).getKey! k = if (f t[k]?).isSome then k else default :=
  DTreeMap.Raw.Const.getKey!_alter_self h

@[grind =]
theorem getKey_alter [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter t k f} :
    (alter t k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' :=
  DTreeMap.Raw.Const.getKey_alter h

@[simp]
theorem getKey_alter_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    (alter t k f).getKey k hc = k :=
  DTreeMap.Raw.Const.getKey_alter_self h

@[grind =]
theorem getKeyD_alter [TransCmp cmp] (h : t.WF) {k k' fallback : α} {f : Option β → Option β} :
    (alter t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  DTreeMap.Raw.Const.getKeyD_alter h

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter t k f).getKeyD k fallback = if (f t[k]?).isSome then k else fallback :=
  DTreeMap.Raw.Const.getKeyD_alter_self h

end Alter

section Modify

@[simp, grind =]
theorem isEmpty_modify [TransCmp cmp] (h : t.WF) {k : α} {f : β → β} :
    (modify t k f).isEmpty = t.isEmpty :=
  DTreeMap.Raw.Const.isEmpty_modify h

@[grind =]
theorem contains_modify [TransCmp cmp] (h : t.WF) {k k' : α} {f : β → β} :
    (modify t k f).contains k' = t.contains k' :=
  DTreeMap.Raw.Const.contains_modify h

@[grind =]
theorem mem_modify [TransCmp cmp] (h : t.WF) {k k' : α} {f : β → β} :
    k' ∈ modify t k f ↔ k' ∈ t :=
  DTreeMap.Raw.Const.mem_modify h

@[grind =]
theorem size_modify [TransCmp cmp] (h : t.WF) {k : α} {f : β → β} :
    (modify t k f).size = t.size :=
  DTreeMap.Raw.Const.size_modify h

@[grind =]
theorem getElem?_modify [TransCmp cmp] (h : t.WF) {k k' : α} {f : β → β} :
    (modify t k f)[k']? =
      if cmp k k' = .eq then
        t[k]?.map f
      else
        t[k']? :=
  DTreeMap.Raw.Const.get?_modify h

@[simp]
theorem getElem?_modify_self [TransCmp cmp] (h : t.WF) {k : α} {f : β → β} :
    (modify t k f)[k]? = t[k]?.map f :=
  DTreeMap.Raw.Const.get?_modify_self h

@[grind =]
theorem getElem_modify [TransCmp cmp] (h : t.WF) {k k' : α} {f : β → β} {hc : k' ∈ modify t k f} :
    (modify t k f)[k']'hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        f (t[k]'h')
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        t[k']'h' :=
  DTreeMap.Raw.Const.get_modify h

@[simp]
theorem getElem_modify_self [TransCmp cmp] (h : t.WF) {k : α} {f : β → β} {hc : k ∈ modify t k f} :
    haveI h' : k ∈ t := mem_modify h |>.mp hc
    (modify t k f)[k]'hc = f (t[k]'h') :=
  DTreeMap.Raw.Const.get_modify_self h

@[grind =]
theorem getElem!_modify [TransCmp cmp] (h : t.WF) {k k' : α} [hi : Inhabited β] {f : β → β} :
    (modify t k f)[k']! =
      if cmp k k' = .eq then
        t[k]? |>.map f |>.get!
      else
        t[k']! :=
  DTreeMap.Raw.Const.get!_modify h

@[simp]
theorem getElem!_modify_self [TransCmp cmp] (h : t.WF) {k : α} [Inhabited β] {f : β → β} :
    (modify t k f)[k]! = (t[k]?.map f).get! :=
  DTreeMap.Raw.Const.get!_modify_self h

@[grind =]
theorem getD_modify [TransCmp cmp] (h : t.WF) {k k' : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k' fallback =
      if cmp k k' = .eq then
        t[k]?.map f |>.getD fallback
      else
        getD t k' fallback :=
  DTreeMap.Raw.Const.getD_modify h

@[simp]
theorem getD_modify_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k fallback = (t[k]?.map f).getD fallback :=
  DTreeMap.Raw.Const.getD_modify_self h

@[grind =]
theorem getKey?_modify [TransCmp cmp] (h : t.WF) {k k' : α} {f : β → β} :
    (modify t k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  DTreeMap.Raw.Const.getKey?_modify h

theorem getKey?_modify_self [TransCmp cmp] (h : t.WF) {k : α} {f : β → β} :
    (modify t k f).getKey? k = if k ∈ t then some k else none :=
  DTreeMap.Raw.Const.getKey?_modify_self h

@[grind =]
theorem getKey!_modify [TransCmp cmp] (h : t.WF) [Inhabited α] {k k' : α} {f : β → β} :
    (modify t k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  DTreeMap.Raw.Const.getKey!_modify h

theorem getKey!_modify_self [TransCmp cmp] (h : t.WF) [Inhabited α] {k : α} {f : β → β} :
    (modify t k f).getKey! k = if k ∈ t then k else default :=
  DTreeMap.Raw.Const.getKey!_modify_self h

@[grind =]
theorem getKey_modify [TransCmp cmp] (h : t.WF) [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify t k f} :
    (modify t k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        t.getKey k' h' :=
  DTreeMap.Raw.Const.getKey_modify h

@[simp]
theorem getKey_modify_self [TransCmp cmp] (h : t.WF) [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify t k f} : (modify t k f).getKey k hc = k :=
  DTreeMap.Raw.Const.getKey_modify_self h

@[grind =]
theorem getKeyD_modify [TransCmp cmp] (h : t.WF) {k k' fallback : α} {f : β → β} :
    (modify t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  DTreeMap.Raw.Const.getKeyD_modify h

theorem getKeyD_modify_self [TransCmp cmp] (h : t.WF) [Inhabited α] {k fallback : α} {f : β → β} :
    (modify t k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  DTreeMap.Raw.Const.getKeyD_modify_self h

end Modify

section Min

@[simp, grind =]
theorem minKey?_emptyc :
    (empty : Raw α β cmp).minKey? = none :=
  DTreeMap.Raw.minKey?_emptyc

theorem minKey?_of_isEmpty [TransCmp cmp] (h : t.WF) :
    (he : t.isEmpty) → t.minKey? = none :=
  DTreeMap.Raw.minKey?_of_isEmpty h

@[simp, grind =]
theorem minKey?_eq_none_iff [TransCmp cmp] (h : t.WF) :
    t.minKey? = none ↔ t.isEmpty :=
  DTreeMap.Raw.minKey?_eq_none_iff h

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF) {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.Raw.minKey?_eq_some_iff_getKey?_eq_self_and_forall h

theorem minKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.Raw.minKey?_eq_some_iff_mem_and_forall h

@[simp, grind =]
theorem isNone_minKey?_eq_isEmpty [TransCmp cmp] (h : t.WF) :
    t.minKey?.isNone = t.isEmpty :=
  DTreeMap.Raw.isNone_minKey?_eq_isEmpty h

@[simp, grind =]
theorem isSome_minKey?_eq_not_isEmpty [TransCmp cmp] (h : t.WF) :
    t.minKey?.isSome = !t.isEmpty :=
  DTreeMap.Raw.isSome_minKey?_eq_not_isEmpty h

theorem isSome_minKey?_iff_isEmpty_eq_false [TransCmp cmp] (h : t.WF) :
    t.minKey?.isSome ↔ t.isEmpty = false :=
  DTreeMap.Raw.isSome_minKey?_iff_isEmpty_eq_false h

@[grind =]
theorem minKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  DTreeMap.Raw.minKey?_insert h

theorem minKey?_insert_of_isEmpty [TransCmp cmp] (h : t.WF) {k v} (he : t.isEmpty) :
    (t.insert k v).minKey? = some k :=
  DTreeMap.Raw.minKey?_insert_of_isEmpty h he

theorem minKey!_insert_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} (he : t.isEmpty) :
    (t.insert k v).minKey! = k :=
  DTreeMap.Raw.minKey!_insert_of_isEmpty h he

theorem minKeyD_insert_of_isEmpty [TransCmp cmp] (h : t.WF) {k v} (he : t.isEmpty) {fallback : α} :
    (t.insert k v).minKeyD fallback = k :=
  DTreeMap.Raw.minKeyD_insert_of_isEmpty h he

theorem minKey?_insertIfNew_of_isEmpty [TransCmp cmp] (h : t.WF) {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey? = some k :=
  DTreeMap.Raw.minKey?_insertIfNew_of_isEmpty h he

theorem minKey!_insertIfNew_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey! = k :=
  DTreeMap.Raw.minKey!_insertIfNew_of_isEmpty h he

theorem minKeyD_insertIfNew_of_isEmpty [TransCmp cmp] (h : t.WF) {k v} (he : t.isEmpty) {fallback : α} :
    (t.insertIfNew k v).minKeyD fallback = k :=
  DTreeMap.Raw.minKeyD_insertIfNew_of_isEmpty h he

@[grind =]
theorem isSome_minKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).minKey?.isSome :=
  DTreeMap.Raw.isSome_minKey?_insert h

theorem minKey?_insert_le_minKey? [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v |>.minKey? |>.get <| isSome_minKey?_insert h) = kmi) →
    cmp kmi km |>.isLE :=
  DTreeMap.Raw.minKey?_insert_le_minKey? h

theorem minKey?_insert_le_self [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insert k v |>.minKey?.get <| isSome_minKey?_insert h) = kmi) →
    cmp kmi k |>.isLE :=
  DTreeMap.Raw.minKey?_insert_le_self h

theorem contains_minKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) →
    t.contains km :=
  DTreeMap.Raw.contains_minKey? h

theorem isSome_minKey?_of_contains [TransCmp cmp] (h : t.WF) {k} :
    (hc : t.contains k) → t.minKey?.isSome :=
  DTreeMap.Raw.isSome_minKey?_of_contains h

theorem isSome_minKey?_of_mem [TransCmp cmp] (h : t.WF) {k} :
    k ∈ t → t.minKey?.isSome :=
  DTreeMap.Raw.isSome_minKey?_of_mem h

theorem minKey?_le_of_contains [TransCmp cmp] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains h hc) = km) →
    cmp km k |>.isLE :=
  DTreeMap.Raw.minKey?_le_of_contains h

theorem minKey?_le_of_mem [TransCmp cmp] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem h hc) = km) →
    cmp km k |>.isLE :=
  DTreeMap.Raw.minKey?_le_of_mem h

theorem le_minKey? [TransCmp cmp] {k} (h : t.WF) :
    (∀ k', t.minKey? = some k' → (cmp k k').isLE) ↔
      (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.Raw.le_minKey? h

theorem getKey?_minKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km :=
  DTreeMap.Raw.getKey?_minKey? h

theorem getKey_minKey? [TransCmp cmp] (h : t.WF) {km hc} :
    (hkm : t.minKey?.get (isSome_minKey?_of_contains h hc) = km) → t.getKey km hc = km :=
  DTreeMap.Raw.getKey_minKey? h

theorem getKey!_minKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) → t.getKey! km = km :=
  DTreeMap.Raw.getKey!_minKey? h

theorem getKeyD_minKey? [TransCmp cmp] (h : t.WF) {km fallback} :
    (hkm : t.minKey? = some km) → t.getKeyD km fallback = km :=
  DTreeMap.Raw.getKeyD_minKey? h

@[simp]
theorem minKey?_bind_getKey? [TransCmp cmp] (h : t.WF) :
    t.minKey?.bind t.getKey? = t.minKey? :=
  DTreeMap.Raw.minKey?_bind_getKey? h

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransCmp cmp] (h : t.WF) {k} :
    (t.erase k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq :=
  DTreeMap.Raw.minKey?_erase_eq_iff_not_compare_eq_minKey? h

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransCmp cmp] (h : t.WF) {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.minKey?) = t.minKey? :=
  DTreeMap.Raw.minKey?_erase_eq_of_not_compare_eq_minKey? h

theorem isSome_minKey?_of_isSome_minKey?_erase [TransCmp cmp] (h : t.WF) {k} :
    (hs : t.erase k |>.minKey?.isSome) →
    t.minKey?.isSome :=
  DTreeMap.Raw.isSome_minKey?_of_isSome_minKey?_erase h

theorem minKey?_le_minKey?_erase [TransCmp cmp] (h : t.WF) {k km kme} :
    (hkme : (t.erase k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase h <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  DTreeMap.Raw.minKey?_le_minKey?_erase h

@[grind =]
theorem minKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  DTreeMap.Raw.minKey?_insertIfNew h

@[grind =]
theorem isSome_minKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).minKey?.isSome :=
  DTreeMap.Raw.isSome_minKey?_insertIfNew h

theorem minKey?_insertIfNew_le_minKey? [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.minKey? |>.get <| isSome_minKey?_insertIfNew h) = kmi) →
    cmp kmi km |>.isLE :=
  DTreeMap.Raw.minKey?_insertIfNew_le_minKey? h

theorem minKey?_insertIfNew_le_self [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.minKey?.get <| isSome_minKey?_insertIfNew h) = kmi) →
    cmp kmi k |>.isLE :=
  DTreeMap.Raw.minKey?_insertIfNew_le_self h

@[grind =_]
theorem minKey?_eq_head?_keys [TransCmp cmp] (h : t.WF) :
    t.minKey? = t.keys.head? :=
  DTreeMap.Raw.minKey?_eq_head?_keys h

@[grind =]
theorem minKey?_modify [TransCmp cmp] (h : t.WF) {k f} :
    (t.modify k f).minKey? = t.minKey?.map fun km => if cmp km k = .eq then k else km :=
  DTreeMap.Raw.Const.minKey?_modify h

@[simp] theorem min?_keys [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp]
    (h : t.WF) :
    t.keys.min? = t.minKey? :=
  DTreeMap.Raw.min?_keys h

@[simp] theorem head?_keys [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp]
    (h : t.WF) :
    t.keys.head? = t.minKey? :=
  DTreeMap.Raw.head?_keys h

@[simp, grind =]
theorem minKey?_modify_eq_minKey? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f} :
    (t.modify k f).minKey? = t.minKey? :=
  DTreeMap.Raw.Const.minKey?_modify_eq_minKey? h

theorem isSome_minKey?_modify [TransCmp cmp] {k f} (h : t.WF) :
    (t.modify k f).minKey?.isSome = !t.isEmpty :=
  DTreeMap.Raw.Const.isSome_minKey?_modify h

theorem isSome_minKey?_modify_eq_isSome [TransCmp cmp] (h : t.WF) {k f} :
    (t.modify k f).minKey?.isSome = t.minKey?.isSome :=
  DTreeMap.Raw.Const.isSome_minKey?_modify_eq_isSome h

theorem compare_minKey?_modify_eq [TransCmp cmp] (h : t.WF) {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (t.modify k f |>.minKey? |>.get <|
        (isSome_minKey?_modify_eq_isSome h).trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  DTreeMap.Raw.Const.compare_minKey?_modify_eq h

theorem minKey?_alter_eq_self [TransCmp cmp] (h : t.WF) {k f} :
    (t.alter k f).minKey? = some k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Raw.Const.minKey?_alter_eq_self h

theorem minKey?_eq_some_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.minKey? = some t.minKey! :=
  DTreeMap.Raw.minKey?_eq_some_minKey! h he

theorem minKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty) :
    t.minKey! = default :=
  DTreeMap.Raw.minKey!_eq_default h he

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKey!_eq_iff_getKey?_eq_self_and_forall h he

theorem minKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKey!_eq_iff_mem_and_forall h he

@[grind =]
theorem minKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insert k v).minKey! =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  DTreeMap.Raw.minKey!_insert h

theorem minKey!_insert_le_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false)
    {k v} :
    cmp (t.insert k v).minKey! t.minKey! |>.isLE :=
  DTreeMap.Raw.minKey!_insert_le_minKey! h he

theorem minKey!_insert_le_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp (t.insert k v).minKey! k |>.isLE :=
  DTreeMap.Raw.minKey!_insert_le_self h

theorem contains_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.contains t.minKey! :=
  DTreeMap.Raw.contains_minKey! h he

theorem minKey!_mem [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.minKey! ∈ t :=
  DTreeMap.Raw.minKey!_mem h he

theorem minKey!_le_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : t.contains k) :
    cmp t.minKey! k |>.isLE :=
  DTreeMap.Raw.minKey!_le_of_contains h hc

theorem minKey!_le_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : k ∈ t) :
    cmp t.minKey! k |>.isLE :=
  DTreeMap.Raw.minKey!_le_of_mem h hc

theorem le_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {k} :
    (cmp k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.Raw.le_minKey! h he

theorem getKey?_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey? t.minKey! = some t.minKey! :=
  DTreeMap.Raw.getKey?_minKey! h he

theorem getKey_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {hc} :
    t.getKey t.minKey! hc = t.minKey! :=
  DTreeMap.Raw.getKey_minKey! h

theorem getKey!_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey! t.minKey! = t.minKey! :=
  DTreeMap.Raw.getKey!_minKey! h he

theorem getKeyD_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.minKey! fallback = t.minKey! :=
  DTreeMap.Raw.getKeyD_minKey! h he

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.minKey! = .eq) :
    (t.erase k).minKey! = t.minKey! :=
  DTreeMap.Raw.minKey!_erase_eq_of_not_compare_minKey!_eq h he heq

theorem minKey!_le_minKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) :
    cmp t.minKey! (t.erase k).minKey! |>.isLE :=
  DTreeMap.Raw.minKey!_le_minKey!_erase h he

@[grind =] theorem minKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insertIfNew k v).minKey! =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.Raw.minKey!_insertIfNew h

theorem minKey!_insertIfNew_le_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {k v} :
    cmp (t.insertIfNew k v).minKey! t.minKey! |>.isLE :=
  DTreeMap.Raw.minKey!_insertIfNew_le_minKey! h he

theorem minKey!_insertIfNew_le_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp (t.insertIfNew k v).minKey! k |>.isLE :=
  DTreeMap.Raw.minKey!_insertIfNew_le_self h

@[grind =_] theorem minKey!_eq_head!_keys [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.minKey! = t.keys.head! :=
  DTreeMap.Raw.minKey!_eq_head!_keys h

theorem minKey!_modify [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f).minKey! = if cmp t.minKey! k = .eq then k else t.minKey! :=
  DTreeMap.Raw.Const.minKey!_modify h he

@[simp]
theorem minKey!_modify_eq_minKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    (modify t k f).minKey! = t.minKey! :=
  DTreeMap.Raw.Const.minKey!_modify_eq_minKey! h

theorem compare_minKey!_modify_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    cmp (modify t k f).minKey! t.minKey! = .eq :=
  DTreeMap.Raw.Const.compare_minKey!_modify_eq h

@[simp]
theorem ordCompare_minKey!_modify_eq [Ord α] [TransOrd α] {t : Raw α β} [Inhabited α] (h : t.WF) {k f} :
    compare (modify t k f).minKey! t.minKey! = .eq :=
  compare_minKey!_modify_eq h

theorem minKey!_alter_eq_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f).minKey! = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Raw.Const.minKey!_alter_eq_self h he

theorem minKey?_eq_some_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.minKey? = some (t.minKeyD fallback) :=
  DTreeMap.Raw.minKey?_eq_some_minKeyD h he

theorem minKeyD_eq_fallback [TransCmp cmp] (h : t.WF) (he : t.isEmpty) {fallback} :
    t.minKeyD fallback = fallback :=
  DTreeMap.Raw.minKeyD_eq_fallback h he

theorem minKey!_eq_minKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.minKey! = t.minKeyD default :=
  DTreeMap.Raw.minKey!_eq_minKeyD_default h

theorem minKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.minKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKeyD_eq_iff_getKey?_eq_self_and_forall h he

theorem minKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.minKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKeyD_eq_iff_mem_and_forall h he

@[grind =]
theorem minKeyD_insert [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insert k v |>.minKeyD fallback) =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  DTreeMap.Raw.minKeyD_insert h

theorem minKeyD_insert_le_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false)
    {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  DTreeMap.Raw.minKeyD_insert_le_minKeyD h he

theorem minKeyD_insert_le_self [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_insert_le_self h

theorem contains_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.contains (t.minKeyD fallback) :=
  DTreeMap.Raw.contains_minKeyD h he

theorem minKeyD_mem [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.minKeyD fallback ∈ t :=
  DTreeMap.Raw.minKeyD_mem h he

theorem minKeyD_le_of_contains [TransCmp cmp] (h : t.WF) {k} (hc : t.contains k) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_le_of_contains h hc

theorem minKeyD_le_of_mem [TransCmp cmp] (h : t.WF) {k} (hc : k ∈ t) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_le_of_mem h hc

theorem le_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {k fallback} :
    (cmp k (t.minKeyD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.Raw.le_minKeyD h he

theorem getKey?_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey? (t.minKeyD fallback) = some (t.minKeyD fallback) :=
  DTreeMap.Raw.getKey?_minKeyD h he

theorem getKey_minKeyD [TransCmp cmp] (h : t.WF) {fallback hc} :
    t.getKey (t.minKeyD fallback) hc = t.minKeyD fallback :=
  DTreeMap.Raw.getKey_minKeyD h

theorem getKey!_minKeyD [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey! (t.minKeyD fallback) = t.minKeyD fallback :=
  DTreeMap.Raw.getKey!_minKeyD h he

theorem getKeyD_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback fallback'} :
    t.getKeyD (t.minKeyD fallback) fallback' = t.minKeyD fallback :=
  DTreeMap.Raw.getKeyD_minKeyD h he

theorem minKeyD_erase_eq_of_not_compare_minKeyD_eq [TransCmp cmp] (h : t.WF) {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.minKeyD fallback) = .eq) :
    (t.erase k |>.minKeyD fallback) = t.minKeyD fallback :=
  DTreeMap.Raw.minKeyD_erase_eq_of_not_compare_minKeyD_eq h he heq

theorem minKeyD_le_minKeyD_erase [TransCmp cmp] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.minKeyD fallback) (t.erase k |>.minKeyD fallback) |>.isLE :=
  DTreeMap.Raw.minKeyD_le_minKeyD_erase h he

@[grind =]
theorem minKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insertIfNew k v |>.minKeyD fallback) =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.Raw.minKeyD_insertIfNew h

theorem minKeyD_insertIfNew_le_minKeyD [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  DTreeMap.Raw.minKeyD_insertIfNew_le_minKeyD h he

theorem minKeyD_insertIfNew_le_self [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_insertIfNew_le_self h

theorem minKeyD_eq_headD_keys [TransCmp cmp] (h : t.WF) {fallback} :
    t.minKeyD fallback = t.keys.headD fallback :=
  DTreeMap.Raw.minKeyD_eq_headD_keys h

theorem minKeyD_modify [TransCmp cmp] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) {fallback} :
    (modify t k f |>.minKeyD fallback) =
      if cmp (t.minKeyD fallback) k = .eq then k else (t.minKeyD fallback) :=
  DTreeMap.Raw.Const.minKeyD_modify h he

@[simp, grind =]
theorem minKeyD_modify_eq_minKeyD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f fallback} :
    (modify t k f |>.minKeyD fallback) = t.minKeyD fallback :=
  DTreeMap.Raw.Const.minKeyD_modify_eq_minKeyD h

theorem compare_minKeyD_modify_eq [TransCmp cmp] (h : t.WF) {k f fallback} :
    cmp (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  DTreeMap.Raw.Const.compare_minKeyD_modify_eq h

@[simp]
theorem ordCompare_minKeyD_modify_eq [Ord α] [TransOrd α] {t : Raw α β} (h : t.WF) {k f fallback} :
    compare (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  compare_minKeyD_modify_eq h

theorem minKeyD_alter_eq_self [TransCmp cmp] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) {fallback} :
    (alter t k f |>.minKeyD fallback) = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Raw.Const.minKeyD_alter_eq_self h he

end Min

section Max

@[simp, grind =]
theorem maxKey?_emptyc :
    (empty : Raw α β cmp).maxKey? = none :=
  DTreeMap.Raw.maxKey?_emptyc

theorem maxKey?_of_isEmpty [TransCmp cmp] (h : t.WF) :
    (he : t.isEmpty) → t.maxKey? = none :=
  DTreeMap.Raw.maxKey?_of_isEmpty h

@[simp, grind =]
theorem maxKey?_eq_none_iff [TransCmp cmp] (h : t.WF) :
    t.maxKey? = none ↔ t.isEmpty :=
  DTreeMap.Raw.maxKey?_eq_none_iff h

theorem maxKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF) {km} :
    t.maxKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.Raw.maxKey?_eq_some_iff_getKey?_eq_self_and_forall h

theorem maxKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {km} :
    t.maxKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.Raw.maxKey?_eq_some_iff_mem_and_forall h

@[simp, grind =]
theorem isNone_maxKey?_eq_isEmpty [TransCmp cmp] (h : t.WF) :
    t.maxKey?.isNone = t.isEmpty :=
  DTreeMap.Raw.isNone_maxKey?_eq_isEmpty h

@[simp, grind = ]
theorem isSome_maxKey?_eq_not_isEmpty [TransCmp cmp] (h : t.WF) :
    t.maxKey?.isSome = !t.isEmpty :=
  DTreeMap.Raw.isSome_maxKey?_eq_not_isEmpty h

theorem isSome_maxKey?_iff_isEmpty_eq_false [TransCmp cmp] (h : t.WF) :
    t.maxKey?.isSome ↔ t.isEmpty = false :=
  DTreeMap.Raw.isSome_maxKey?_iff_isEmpty_eq_false h

@[grind =]
theorem maxKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  DTreeMap.Raw.maxKey?_insert h

@[grind =]
theorem isSome_maxKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).maxKey?.isSome :=
  DTreeMap.Raw.isSome_maxKey?_insert h

theorem maxKey?_le_maxKey?_insert [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insert k v |>.maxKey? |>.get <| isSome_maxKey?_insert h) = kmi) →
    cmp km kmi |>.isLE :=
  DTreeMap.Raw.maxKey?_le_maxKey?_insert h

theorem self_le_maxKey?_insert [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insert k v |>.maxKey?.get <| isSome_maxKey?_insert h) = kmi) →
    cmp k kmi |>.isLE :=
  DTreeMap.Raw.self_le_maxKey?_insert h

theorem contains_maxKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) →
    t.contains km :=
  DTreeMap.Raw.contains_maxKey? h

theorem isSome_maxKey?_of_contains [TransCmp cmp] (h : t.WF) {k} :
    (hc : t.contains k) → t.maxKey?.isSome :=
  DTreeMap.Raw.isSome_maxKey?_of_contains h

theorem isSome_maxKey?_of_mem [TransCmp cmp] (h : t.WF) {k} :
    k ∈ t → t.maxKey?.isSome :=
  DTreeMap.Raw.isSome_maxKey?_of_mem h

theorem le_maxKey?_of_contains [TransCmp cmp] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_contains h hc) = km) →
    cmp k km |>.isLE :=
  DTreeMap.Raw.le_maxKey?_of_contains h

theorem le_maxKey?_of_mem [TransCmp cmp] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_mem h hc) = km) →
    cmp k km |>.isLE :=
  DTreeMap.Raw.le_maxKey?_of_mem h

theorem maxKey?_le [TransCmp cmp] {k} (h : t.WF) :
    (∀ k', t.maxKey? = some k' → (cmp k' k).isLE) ↔
      (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.Raw.maxKey?_le h

theorem getKey?_maxKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) → t.getKey? km = some km :=
  DTreeMap.Raw.getKey?_maxKey? h

theorem getKey_maxKey? [TransCmp cmp] (h : t.WF) {km hc} :
    (hkm : t.maxKey?.get (isSome_maxKey?_of_contains h hc) = km) → t.getKey km hc = km :=
  DTreeMap.Raw.getKey_maxKey? h

theorem getKey!_maxKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) → t.getKey! km = km :=
  DTreeMap.Raw.getKey!_maxKey? h

theorem getKeyD_maxKey? [TransCmp cmp] (h : t.WF) {km fallback} :
    (hkm : t.maxKey? = some km) → t.getKeyD km fallback = km :=
  DTreeMap.Raw.getKeyD_maxKey? h

@[simp]
theorem maxKey?_bind_getKey? [TransCmp cmp] (h : t.WF) :
    t.maxKey?.bind t.getKey? = t.maxKey? :=
  DTreeMap.Raw.maxKey?_bind_getKey? h

theorem maxKey?_erase_eq_iff_not_compare_eq_maxKey? [TransCmp cmp] (h : t.WF) {k} :
    (t.erase k |>.maxKey?) = t.maxKey? ↔
      ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq :=
  DTreeMap.Raw.maxKey?_erase_eq_iff_not_compare_eq_maxKey? h

theorem maxKey?_erase_eq_of_not_compare_eq_maxKey? [TransCmp cmp] (h : t.WF) {k} :
    (hc : ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.maxKey?) = t.maxKey? :=
  DTreeMap.Raw.maxKey?_erase_eq_of_not_compare_eq_maxKey? h

theorem isSome_maxKey?_of_isSome_maxKey?_erase [TransCmp cmp] (h : t.WF) {k} :
    (hs : t.erase k |>.maxKey?.isSome) →
    t.maxKey?.isSome :=
  DTreeMap.Raw.isSome_maxKey?_of_isSome_maxKey?_erase h

theorem maxKey?_erase_le_maxKey? [TransCmp cmp] (h : t.WF) {k km kme} :
    (hkme : (t.erase k |>.maxKey?) = some kme) →
    (hkm : (t.maxKey?.get <|
      isSome_maxKey?_of_isSome_maxKey?_erase h <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  DTreeMap.Raw.maxKey?_erase_le_maxKey? h

@[grind =]
theorem maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  DTreeMap.Raw.maxKey?_insertIfNew h

@[grind =]
theorem isSome_maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).maxKey?.isSome :=
  DTreeMap.Raw.isSome_maxKey?_insertIfNew h

theorem maxKey?_le_maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.maxKey? |>.get <| isSome_maxKey?_insertIfNew h) = kmi) →
    cmp km kmi |>.isLE :=
  DTreeMap.Raw.maxKey?_le_maxKey?_insertIfNew h

theorem self_le_maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.maxKey?.get <| isSome_maxKey?_insertIfNew h) = kmi) →
    cmp k kmi |>.isLE :=
  DTreeMap.Raw.self_le_maxKey?_insertIfNew h

@[grind =_] theorem maxKey?_eq_getLast?_keys [TransCmp cmp] (h : t.WF) :
    t.maxKey? = t.keys.getLast? :=
  DTreeMap.Raw.maxKey?_eq_getLast?_keys h

theorem maxKey?_modify [TransCmp cmp] (h : t.WF) {k f} :
    (t.modify k f).maxKey? = t.maxKey?.map fun km => if cmp km k = .eq then k else km :=
  DTreeMap.Raw.Const.maxKey?_modify h

@[simp, grind =]
theorem maxKey?_modify_eq_maxKey? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f} :
    (t.modify k f).maxKey? = t.maxKey? :=
  DTreeMap.Raw.Const.maxKey?_modify_eq_maxKey? h

theorem isSome_maxKey?_modify [TransCmp cmp] {k f} (h : t.WF) :
    (t.modify k f).maxKey?.isSome = !t.isEmpty :=
  DTreeMap.Raw.Const.isSome_maxKey?_modify h

theorem isSome_maxKey?_modify_eq_isSome [TransCmp cmp] (h : t.WF) {k f} :
    (t.modify k f).maxKey?.isSome = t.maxKey?.isSome :=
  DTreeMap.Raw.Const.isSome_maxKey?_modify_eq_isSome h

theorem compare_maxKey?_modify_eq [TransCmp cmp] (h : t.WF) {k f km kmm} :
    (hkm : t.maxKey? = some km) →
    (hkmm : (t.modify k f |>.maxKey? |>.get <|
        (isSome_maxKey?_modify_eq_isSome h).trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  DTreeMap.Raw.Const.compare_maxKey?_modify_eq h

theorem maxKey?_alter_eq_self [TransCmp cmp] (h : t.WF) {k f} :
    (t.alter k f).maxKey? = some k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Raw.Const.maxKey?_alter_eq_self h

theorem maxKey?_eq_some_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.maxKey? = some t.maxKey! :=
  DTreeMap.Raw.maxKey?_eq_some_maxKey! h he

theorem maxKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty) :
    t.maxKey! = default :=
  DTreeMap.Raw.maxKey!_eq_default h he

theorem maxKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.maxKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKey!_eq_iff_getKey?_eq_self_and_forall h he

theorem maxKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.maxKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKey!_eq_iff_mem_and_forall h he

@[grind =]
theorem maxKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insert k v).maxKey! =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  DTreeMap.Raw.maxKey!_insert h

theorem maxKey!_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false)
    {k v} :
    cmp t.maxKey! (t.insert k v).maxKey! |>.isLE :=
  DTreeMap.Raw.maxKey!_le_maxKey!_insert h he

theorem self_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp k (t.insert k v).maxKey! |>.isLE :=
  DTreeMap.Raw.self_le_maxKey!_insert h

theorem contains_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.contains t.maxKey! :=
  DTreeMap.Raw.contains_maxKey! h he

theorem maxKey!_mem [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.maxKey! ∈ t :=
  DTreeMap.Raw.maxKey!_mem h he

theorem le_maxKey!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : t.contains k) :
    cmp k t.maxKey! |>.isLE :=
  DTreeMap.Raw.le_maxKey!_of_contains h hc

theorem le_maxKey!_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : k ∈ t) :
    cmp k t.maxKey! |>.isLE :=
  DTreeMap.Raw.le_maxKey!_of_mem h hc

theorem maxKey!_le [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {k} :
    (cmp t.maxKey! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.Raw.maxKey!_le h he

theorem getKey?_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey? t.maxKey! = some t.maxKey! :=
  DTreeMap.Raw.getKey?_maxKey! h he

theorem getKey_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {hc} :
    t.getKey t.maxKey! hc = t.maxKey! :=
  DTreeMap.Raw.getKey_maxKey! h

theorem getKey!_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey! t.maxKey! = t.maxKey! :=
  DTreeMap.Raw.getKey!_maxKey! h he

theorem getKeyD_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.maxKey! fallback = t.maxKey! :=
  DTreeMap.Raw.getKeyD_maxKey! h he

theorem maxKey!_erase_eq_of_not_compare_maxKey!_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.maxKey! = .eq) :
    (t.erase k).maxKey! = t.maxKey! :=
  DTreeMap.Raw.maxKey!_erase_eq_of_not_compare_maxKey!_eq h he heq

theorem maxKey!_erase_le_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) :
    cmp (t.erase k).maxKey! t.maxKey! |>.isLE :=
  DTreeMap.Raw.maxKey!_erase_le_maxKey! h he

@[grind =]
theorem maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insertIfNew k v).maxKey! =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.Raw.maxKey!_insertIfNew h

theorem maxKey!_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {k v} :
    cmp t.maxKey! (t.insertIfNew k v).maxKey! |>.isLE :=
  DTreeMap.Raw.maxKey!_le_maxKey!_insertIfNew h he

theorem self_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp k (t.insertIfNew k v).maxKey! |>.isLE :=
  DTreeMap.Raw.self_le_maxKey!_insertIfNew h

@[grind =_]
theorem maxKey!_eq_getLast!_keys [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.maxKey! = t.keys.getLast! :=
  DTreeMap.Raw.maxKey!_eq_getLast!_keys h

theorem maxKey!_modify [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f).maxKey! = if cmp t.maxKey! k = .eq then k else t.maxKey! :=
  DTreeMap.Raw.Const.maxKey!_modify h he

@[simp]
theorem maxKey!_modify_eq_maxKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    (modify t k f).maxKey! = t.maxKey! :=
  DTreeMap.Raw.Const.maxKey!_modify_eq_maxKey! h

theorem compare_maxKey!_modify_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    cmp (modify t k f).maxKey! t.maxKey! = .eq :=
  DTreeMap.Raw.Const.compare_maxKey!_modify_eq h

@[simp]
theorem ordCompare_maxKey!_modify_eq [Ord α] [TransOrd α] {t : Raw α β} [Inhabited α] (h : t.WF) {k f} :
    compare (modify t k f).maxKey! t.maxKey! = .eq :=
  compare_maxKey!_modify_eq h

theorem maxKey!_alter_eq_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f).maxKey! = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Raw.Const.maxKey!_alter_eq_self h he

theorem maxKey?_eq_some_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.maxKey? = some (t.maxKeyD fallback) :=
  DTreeMap.Raw.maxKey?_eq_some_maxKeyD h he

theorem maxKeyD_eq_fallback [TransCmp cmp] (h : t.WF) (he : t.isEmpty) {fallback} :
    t.maxKeyD fallback = fallback :=
  DTreeMap.Raw.maxKeyD_eq_fallback h he

theorem maxKey!_eq_maxKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.maxKey! = t.maxKeyD default :=
  DTreeMap.Raw.maxKey!_eq_maxKeyD_default h

theorem maxKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.maxKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKeyD_eq_iff_getKey?_eq_self_and_forall h he

theorem maxKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKeyD_eq_iff_mem_and_forall h he

@[grind =]
theorem maxKeyD_insert [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insert k v |>.maxKeyD fallback) =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  DTreeMap.Raw.maxKeyD_insert h

theorem maxKeyD_le_maxKeyD_insert [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false)
    {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.maxKeyD_le_maxKeyD_insert h he

theorem self_le_maxKeyD_insert [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp k (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.self_le_maxKeyD_insert h

theorem contains_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.contains (t.maxKeyD fallback) :=
  DTreeMap.Raw.contains_maxKeyD h he

theorem maxKeyD_mem [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.maxKeyD fallback ∈ t :=
  DTreeMap.Raw.maxKeyD_mem h he

theorem le_maxKeyD_of_contains [TransCmp cmp] (h : t.WF) {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.le_maxKeyD_of_contains h hc

theorem le_maxKeyD_of_mem [TransCmp cmp] (h : t.WF) {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.le_maxKeyD_of_mem h hc

theorem maxKeyD_le [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {k fallback} :
    (cmp (t.maxKeyD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.Raw.maxKeyD_le h he

theorem getKey?_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey? (t.maxKeyD fallback) = some (t.maxKeyD fallback) :=
  DTreeMap.Raw.getKey?_maxKeyD h he

theorem getKey_maxKeyD [TransCmp cmp] (h : t.WF) {fallback hc} :
    t.getKey (t.maxKeyD fallback) hc = t.maxKeyD fallback :=
  DTreeMap.Raw.getKey_maxKeyD h

theorem getKey!_maxKeyD [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey! (t.maxKeyD fallback) = t.maxKeyD fallback :=
  DTreeMap.Raw.getKey!_maxKeyD h he

theorem getKeyD_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback fallback'} :
    t.getKeyD (t.maxKeyD fallback) fallback' = t.maxKeyD fallback :=
  DTreeMap.Raw.getKeyD_maxKeyD h he

theorem maxKeyD_erase_eq_of_not_compare_maxKeyD_eq [TransCmp cmp] (h : t.WF) {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.maxKeyD fallback) = .eq) :
    (t.erase k |>.maxKeyD fallback) = t.maxKeyD fallback :=
  DTreeMap.Raw.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq h he heq

theorem maxKeyD_erase_le_maxKeyD [TransCmp cmp] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.erase k |>.maxKeyD fallback) (t.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.maxKeyD_erase_le_maxKeyD h he

@[grind =]
theorem maxKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insertIfNew k v |>.maxKeyD fallback) =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.Raw.maxKeyD_insertIfNew h

theorem maxKeyD_le_maxKeyD_insertIfNew [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.maxKeyD_le_maxKeyD_insertIfNew h he

theorem self_le_maxKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp k (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.Raw.self_le_maxKeyD_insertIfNew h

theorem maxKeyD_eq_getLastD_keys [TransCmp cmp] (h : t.WF) {fallback} :
    t.maxKeyD fallback = t.keys.getLastD fallback :=
  DTreeMap.Raw.maxKeyD_eq_getLastD_keys h

theorem maxKeyD_modify [TransCmp cmp] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) {fallback} :
    (modify t k f |>.maxKeyD fallback) =
      if cmp (t.maxKeyD fallback) k = .eq then k else (t.maxKeyD fallback) :=
  DTreeMap.Raw.Const.maxKeyD_modify h he

@[simp, grind =]
theorem maxKeyD_modify_eq_maxKeyD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f fallback} :
    (modify t k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  DTreeMap.Raw.Const.maxKeyD_modify_eq_maxKeyD h

theorem compare_maxKeyD_modify_eq [TransCmp cmp] (h : t.WF) {k f fallback} :
    cmp (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  DTreeMap.Raw.Const.compare_maxKeyD_modify_eq h

@[simp]
theorem ordCompare_maxKeyD_modify_eq [Ord α] [TransOrd α] {t : Raw α β} (h : t.WF) {k f fallback} :
    compare (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  compare_maxKeyD_modify_eq h

theorem maxKeyD_alter_eq_self [TransCmp cmp] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) {fallback} :
    (alter t k f |>.maxKeyD fallback) = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Raw.Const.maxKeyD_alter_eq_self h he

end Max

namespace Equiv

variable {t₁ t₂ t₃ t₄ : Raw α β cmp} {δ : Type w} {m : Type w → Type w'}

@[refl, simp] theorem rfl : Equiv t t := ⟨.rfl⟩

@[symm] theorem symm : Equiv t₁ t₂ → Equiv t₂ t₁
  | ⟨h⟩ => ⟨h.symm⟩

theorem trans : Equiv t₁ t₂ → Equiv t₂ t₃ → Equiv t₁ t₃
  | ⟨h⟩, ⟨h'⟩ => ⟨h.trans h'⟩

instance instTrans : @Trans (Raw α β cmp) _ _ Equiv Equiv Equiv := ⟨trans⟩

theorem comm : t₁ ~m t₂ ↔ t₂ ~m t₁ := ⟨symm, symm⟩
theorem congr_left (h : t₁ ~m t₂) : t₁ ~m t₃ ↔ t₂ ~m t₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : t₁ ~m t₂) : t₃ ~m t₁ ↔ t₃ ~m t₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

-- congruence lemmas

theorem isEmpty_eq (h : t₁ ~m t₂) : t₁.isEmpty = t₂.isEmpty :=
  h.1.isEmpty_eq

theorem contains_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.contains k = t₂.contains k :=
  h.1.contains_eq h₁.1 h₂.1

theorem mem_iff [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    k ∈ t₁ ↔ k ∈ t₂ :=
  h.1.mem_iff h₁.1 h₂.1

theorem size_eq (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.size = t₂.size :=
  h.1.size_eq h₁.1 h₂.1

theorem getElem?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁[k]? = t₂[k]? :=
  h.1.constGet?_eq h₁.1 h₂.1

theorem getElem_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁[k] = t₂[k]'((h.mem_iff h₁ h₂).mp hk) :=
  h.1.constGet_eq h₁.1 h₂.1

theorem getElem!_eq [TransCmp cmp] [Inhabited β] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁[k]! = t₂[k]! :=
  h.1.constGet!_eq h₁.1 h₂.1

theorem getD_eq [TransCmp cmp] {k : α} {fallback : β} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getD k fallback = t₂.getD k fallback :=
  h.1.constGetD_eq h₁.1 h₂.1

theorem getKey?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKey? k = t₂.getKey? k :=
  h.1.getKey?_eq h₁.1 h₂.1

theorem getKey_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKey k hk = t₂.getKey k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.getKey_eq h₁.1 h₂.1

theorem getKey!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKey! k = t₂.getKey! k :=
  h.1.getKey!_eq h₁.1 h₂.1

theorem getKeyD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyD k fallback = t₂.getKeyD k fallback :=
  h.1.getKeyD_eq h₁.1 h₂.1

theorem toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.toList = t₂.toList :=
  h.1.constToList_eq h₁.1 h₂.1

theorem toArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.toArray = t₂.toArray :=
  h.1.constToArray_eq h₁.1 h₂.1

theorem keys_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.keys = t₂.keys :=
  h.1.keys_eq h₁.1 h₂.1

theorem keysArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.keysArray = t₂.keysArray :=
  h.1.keysArray_eq h₁.1 h₂.1

theorem foldlM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → β → m δ}
    {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.foldlM f init = t₂.foldlM f init :=
  h.1.foldlM_eq h₁.1 h₂.1

theorem foldl_eq [TransCmp cmp] {f : δ → α → β → δ} {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) :
    t₁.foldl f init = t₂.foldl f init :=
  h.1.foldl_eq h₁.1 h₂.1

theorem foldrM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → β → δ → m δ}
    {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.foldrM f init = t₂.foldrM f init :=
  h.1.foldrM_eq h₁.1 h₂.1

theorem foldr_eq [TransCmp cmp] {f : α → β → δ → δ} {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) :
    t₁.foldr f init = t₂.foldr f init :=
  h.1.foldr_eq h₁.1 h₂.1

theorem forIn_eq [TransCmp cmp] [Monad m] [LawfulMonad m]
    {b : δ} {f : α × β → δ → m (ForInStep δ)} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    ForIn.forIn t₁ b f = ForIn.forIn t₂ b f :=
  h.1.forIn_eq h₁.1 h₂.1 (f := fun ⟨a, b⟩ => f ⟨a, b⟩)

theorem forM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α × β → m PUnit}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    ForM.forM t₁ f = ForM.forM t₂ f :=
  h.1.forM_eq h₁.1 h₂.1 (f := fun x : (_ : α) × β => f (x.1, x.2))

theorem any_eq [TransCmp cmp] {p : α → β → Bool} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.any p = t₂.any p :=
  h.1.any_eq h₁.1 h₂.1

theorem all_eq [TransCmp cmp] {p : α → β → Bool} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.all p = t₂.all p :=
  h.1.all_eq h₁.1 h₂.1

theorem minKey?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minKey? = t₂.minKey? :=
  h.1.minKey?_eq h₁.1 h₂.1

theorem minKey!_eq [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minKey! = t₂.minKey! :=
  h.1.minKey!_eq h₁.1 h₂.1

theorem minKeyD_eq [TransCmp cmp] {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minKeyD fallback = t₂.minKeyD fallback :=
  h.1.minKeyD_eq h₁.1 h₂.1

theorem maxKey?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxKey? = t₂.maxKey? :=
  h.1.maxKey?_eq h₁.1 h₂.1

theorem maxKey!_eq [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxKey! = t₂.maxKey! :=
  h.1.maxKey!_eq h₁.1 h₂.1

theorem maxKeyD_eq [TransCmp cmp] {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxKeyD fallback = t₂.maxKeyD fallback :=
  h.1.maxKeyD_eq h₁.1 h₂.1

theorem minEntry?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minEntry? = t₂.minEntry? :=
  h.1.constMinEntry?_eq h₁.1 h₂.1

theorem minEntry!_eq [TransCmp cmp] [Inhabited (α × β)] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.minEntry! = t₂.minEntry! :=
  h.1.constMinEntry!_eq h₁.1 h₂.1

theorem minEntryD_eq [TransCmp cmp] {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.minEntryD fallback = t₂.minEntryD fallback :=
  h.1.constMinEntryD_eq h₁.1 h₂.1

theorem maxEntry?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxEntry? = t₂.maxEntry? :=
  h.1.constMaxEntry?_eq h₁.1 h₂.1

theorem maxEntry!_eq [TransCmp cmp] [Inhabited (α × β)] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.maxEntry! = t₂.maxEntry! :=
  h.1.constMaxEntry!_eq h₁.1 h₂.1

theorem maxEntryD_eq [TransCmp cmp] {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.maxEntryD fallback = t₂.maxEntryD fallback :=
  h.1.constMaxEntryD_eq h₁.1 h₂.1

theorem entryAtIdx?_eq [TransCmp cmp] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.entryAtIdx? i = t₂.entryAtIdx? i :=
  h.1.constEntryAtIdx?_eq h₁.1 h₂.1

theorem entryAtIdx!_eq [TransCmp cmp] [Inhabited (α × β)] {i : Nat} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.entryAtIdx! i = t₂.entryAtIdx! i :=
  h.1.constEntryAtIdx!_eq h₁.1 h₂.1

theorem entryAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α × β} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.entryAtIdxD i fallback = t₂.entryAtIdxD i fallback :=
  h.1.constEntryAtIdxD_eq h₁.1 h₂.1

theorem keyAtIdx?_eq [TransCmp cmp] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.keyAtIdx? i = t₂.keyAtIdx? i :=
  h.1.keyAtIdx?_eq h₁.1 h₂.1

theorem keyAtIdx!_eq [TransCmp cmp] [Inhabited α] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.keyAtIdx! i = t₂.keyAtIdx! i :=
  h.1.keyAtIdx!_eq h₁.1 h₂.1

theorem keyAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.keyAtIdxD i fallback = t₂.keyAtIdxD i fallback :=
  h.1.keyAtIdxD_eq h₁.1 h₂.1

theorem getEntryGE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryGE? k = t₂.getEntryGE? k :=
  h.1.constGetEntryGE?_eq h₁.1 h₂.1

theorem getEntryGE!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryGE! k = t₂.getEntryGE! k :=
  h.1.constGetEntryGE!_eq h₁.1 h₂.1

theorem getEntryGED_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryGED k fallback = t₂.getEntryGED k fallback :=
  h.1.constGetEntryGED_eq h₁.1 h₂.1

theorem getEntryGT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryGT? k = t₂.getEntryGT? k :=
  h.1.constGetEntryGT?_eq h₁.1 h₂.1

theorem getEntryGT!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryGT! k = t₂.getEntryGT! k :=
  h.1.constGetEntryGT!_eq h₁.1 h₂.1

theorem getEntryGTD_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryGTD k fallback = t₂.getEntryGTD k fallback :=
  h.1.constGetEntryGTD_eq h₁.1 h₂.1

theorem getEntryLE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryLE? k = t₂.getEntryLE? k :=
  h.1.constGetEntryLE?_eq h₁.1 h₂.1

theorem getEntryLE!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryLE! k = t₂.getEntryLE! k :=
  h.1.constGetEntryLE!_eq h₁.1 h₂.1

theorem getEntryLED_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryLED k fallback = t₂.getEntryLED k fallback :=
  h.1.constGetEntryLED_eq h₁.1 h₂.1

theorem getEntryLT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryLT? k = t₂.getEntryLT? k :=
  h.1.constGetEntryLT?_eq h₁.1 h₂.1

theorem getEntryLT!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryLT! k = t₂.getEntryLT! k :=
  h.1.constGetEntryLT!_eq h₁.1 h₂.1

theorem getEntryLTD_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryLTD k fallback = t₂.getEntryLTD k fallback :=
  h.1.constGetEntryLTD_eq h₁.1 h₂.1

theorem getKeyGE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGE? k = t₂.getKeyGE? k :=
  h.1.getKeyGE?_eq h₁.1 h₂.1

theorem getKeyGE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGE! k = t₂.getKeyGE! k :=
  h.1.getKeyGE!_eq h₁.1 h₂.1

theorem getKeyGED_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGED k fallback = t₂.getKeyGED k fallback :=
  h.1.getKeyGED_eq h₁.1 h₂.1

theorem getKeyGT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGT? k = t₂.getKeyGT? k :=
  h.1.getKeyGT?_eq h₁.1 h₂.1

theorem getKeyGT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGT! k = t₂.getKeyGT! k :=
  h.1.getKeyGT!_eq h₁.1 h₂.1

theorem getKeyGTD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGTD k fallback = t₂.getKeyGTD k fallback :=
  h.1.getKeyGTD_eq h₁.1 h₂.1

theorem getKeyLE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLE? k = t₂.getKeyLE? k :=
  h.1.getKeyLE?_eq h₁.1 h₂.1

theorem getKeyLE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLE! k = t₂.getKeyLE! k :=
  h.1.getKeyLE!_eq h₁.1 h₂.1

theorem getKeyLED_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLED k fallback = t₂.getKeyLED k fallback :=
  h.1.getKeyLED_eq h₁.1 h₂.1

theorem getKeyLT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLT? k = t₂.getKeyLT? k :=
  h.1.getKeyLT?_eq h₁.1 h₂.1

theorem getKeyLT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLT! k = t₂.getKeyLT! k :=
  h.1.getKeyLT!_eq h₁.1 h₂.1

theorem getKeyLTD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLTD k fallback = t₂.getKeyLTD k fallback :=
  h.1.getKeyLTD_eq h₁.1 h₂.1

theorem insert [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (v : β) : t₁.insert k v ~m t₂.insert k v :=
  ⟨h.1.insert h₁.1 h₂.1 k v⟩

theorem erase [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) : t₁.erase k ~m t₂.erase k :=
  ⟨h.1.erase h₁.1 h₂.1 k⟩

theorem insertIfNew [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (v : β) : t₁.insertIfNew k v ~m t₂.insertIfNew k v :=
  ⟨h.1.insertIfNew h₁.1 h₂.1 k v⟩

theorem alter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (f : Option β → Option β) :
    t₁.alter k f ~m t₂.alter k f :=
  ⟨h.1.constAlter h₁.1 h₂.1 k f⟩

theorem modify [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (f : β → β) : t₁.modify k f ~m t₂.modify k f :=
  ⟨h.1.constModify h₁.1 h₂.1 k f⟩

theorem filter (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (f : α → β → Bool) :
    t₁.filter f ~m t₂.filter f :=
  ⟨h.1.filter h₁.1 h₂.1 f⟩

theorem map (h : t₁ ~m t₂) (f : α → β → γ) : t₁.map f ~m t₂.map f :=
  ⟨h.1.map f⟩

theorem filterMap (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (f : α → β → Option γ) :
    t₁.filterMap f ~m t₂.filterMap f :=
  ⟨h.1.filterMap h₁.1 h₂.1 f⟩

theorem insertMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (l : List (α × β)) : t₁.insertMany l ~m t₂.insertMany l :=
  ⟨h.1.constInsertMany_list h₁.1 h₂.1 l⟩

theorem insertManyIfNewUnit_list [TransCmp cmp] {t₁ t₂ : Raw α Unit cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (l : List α) :
    t₁.insertManyIfNewUnit l ~m t₂.insertManyIfNewUnit l :=
  ⟨h.1.constInsertManyIfNewUnit_list h₁.1 h₂.1 l⟩

theorem eraseMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (l : List α) :
    t₁.eraseMany l ~m t₂.eraseMany l :=
  ⟨h.1.eraseMany_list h₁.1 h₂.1 l⟩

theorem mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h₃ : t₃.WF) (h₄ : t₄.WF)
    (f : α → β → β → β)
    (h : t₁ ~m t₂) (h' : t₃ ~m t₄) :
    t₁.mergeWith f t₃ ~m t₂.mergeWith f t₄ :=
  ⟨h.1.constMergeWith h₁.1 h₂.1 h₃.1 h₄.1 f h'.1⟩

theorem values_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.values = t₂.values :=
  h.1.values_eq h₁.1 h₂.1

theorem valuesArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.valuesArray = t₂.valuesArray :=
  h.1.valuesArray_eq h₁.1 h₂.1

-- extensionalities

theorem of_forall_getKey_eq_of_forall_getElem?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (hk : ∀ k hk hk', t₁.getKey k hk = t₂.getKey k hk')
    (hv : ∀ k : α, t₁[k]? = t₂[k]?) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey_eq_of_forall_constGet?_eq h₁.1 h₂.1 hk hv⟩

theorem of_forall_getElem?_eq [TransCmp cmp] [LawfulEqCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k : α, t₁[k]? = t₂[k]?) : t₁ ~m t₂ :=
  ⟨.of_forall_constGet?_eq h₁.1 h₂.1 h⟩

theorem of_forall_getKey?_unit_eq [TransCmp cmp] {t₁ t₂ : Raw α Unit cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : ∀ k, t₁.getKey? k = t₂.getKey? k) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey?_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_contains_unit_eq [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : Raw α Unit cmp} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ ~m t₂ :=
  ⟨.of_forall_contains_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_mem_unit_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : Raw α Unit cmp} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ ~m t₂ :=
  ⟨.of_forall_mem_unit_iff h₁.1 h₂.1 h⟩

end Equiv

section Equiv

variable {t₁ t₂ : Raw α β cmp}

private theorem equiv_iff : t₁ ~m t₂ ↔ t₁.1.Equiv t₂.1 :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem equiv_empty_iff_isEmpty : t ~m empty ↔ t.isEmpty :=
  equiv_iff.trans DTreeMap.Raw.equiv_empty_iff_isEmpty

theorem empty_equiv_iff_isEmpty : empty ~m t ↔ t.isEmpty :=
  equiv_iff.trans DTreeMap.Raw.empty_equiv_iff_isEmpty

theorem equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList :=
  equiv_iff.trans DTreeMap.Raw.Const.equiv_iff_toList_perm

theorem Equiv.of_toList_perm (h : t₁.toList.Perm t₂.toList) : t₁ ~m t₂ :=
  ⟨.of_constToList_perm h⟩

theorem equiv_iff_toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁ ~m t₂ ↔ t₁.toList = t₂.toList :=
  equiv_iff.trans (DTreeMap.Raw.Const.equiv_iff_toList_eq h₁.1 h₂.1)

theorem equiv_iff_keys_unit_perm {t₁ t₂ : Raw α Unit cmp} :
    t₁ ~m t₂ ↔ t₁.keys.Perm t₂.keys :=
  equiv_iff.trans DTreeMap.Raw.Const.equiv_iff_keys_unit_perm

theorem equiv_iff_keys_unit_eq {t₁ t₂ : Raw α Unit cmp} [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁ ~m t₂ ↔ t₁.keys = t₂.keys :=
  equiv_iff.trans (DTreeMap.Raw.Const.equiv_iff_keys_unit_eq h₁.1 h₂.1)

theorem Equiv.of_keys_unit_perm {t₁ t₂ : Raw α Unit cmp} : t₁.keys.Perm t₂.keys → t₁ ~m t₂ :=
  equiv_iff_keys_unit_perm.mpr

end Equiv

section filterMap

theorem toList_filterMap {f : α → β → Option γ} (h : t.WF) :
    (t.filterMap f).toList =
      (t.toList.filterMap (fun p => (f p.1 p.2).map (fun x => ⟨p.1, x⟩))) :=
  DTreeMap.Raw.Const.toList_filterMap h

@[grind =]
theorem isEmpty_filterMap_iff [TransCmp cmp]
    {f : α → β → Option γ} (h : t.WF) :
    (t.filterMap f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ t), f (t.getKey k h) (t[k]'h) = none :=
  DTreeMap.Raw.Const.isEmpty_filterMap_iff h.out

theorem isEmpty_filterMap_eq_false_iff [TransCmp cmp]
    {f : α → β → Option γ} (h : t.WF) :
    (t.filterMap f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ t), (f (t.getKey k h) (t[k]'h)).isSome :=
  DTreeMap.Raw.Const.isEmpty_filterMap_eq_false_iff h.out

-- TODO: `contains_filterMap` is missing

@[grind =]
theorem mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    k ∈ (t.filterMap f) ↔ ∃ (g : k ∈ t),
      (f (t.getKey k g) (t[k]'g)).isSome :=
  DTreeMap.Raw.Const.mem_filterMap h.out

theorem mem_of_mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} (h : t.WF) (h' : k ∈ (t.filterMap f)) :
    k ∈ t :=
  DTreeMap.Raw.mem_of_mem_filterMap h.out h'

theorem size_filterMap_le_size [TransCmp cmp]
    {f : α → β → Option γ} (h : t.WF) :
    (t.filterMap f).size ≤ t.size :=
  DTreeMap.Raw.size_filterMap_le_size h.out

grind_pattern size_filterMap_le_size => (t.filterMap f).size
theorem size_filterMap_eq_size_iff [TransCmp cmp]
    {f : α → β → Option γ} (h : t.WF) :
    (t.filterMap f).size = t.size ↔ ∀ (a : α) (h : a ∈ t),
      (f (t.getKey a h) (t[a]'h)).isSome :=
  DTreeMap.Raw.Const.size_filterMap_eq_size_iff h.out

@[simp]
theorem getElem?_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    (t.filterMap f)[k]? = t[k]?.pbind (fun x h' =>
      f (t.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x) :=
  DTreeMap.Raw.Const.get?_filterMap h.out

/-- Simpler variant of `getElem?_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem?_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    (t.filterMap f)[k]? = t[k]?.bind fun x => f k x := by
  simp [getElem?_filterMap, h]

theorem getElem?_filterMap_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Option γ} {k k' : α} (h : t.WF) :
    t.getKey? k = some k' → (t.filterMap f)[k]? = t[k]?.bind
      fun x => f k' x :=
  DTreeMap.Raw.Const.get?_filterMap_of_getKey?_eq_some h.out

theorem isSome_apply_of_mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    ∀ (h' : k ∈ t.filterMap f),
      (f (t.getKey k (mem_of_mem_filterMap h h'))
        (t[k]'(mem_of_mem_filterMap h h'))).isSome :=
  DTreeMap.Raw.Const.isSome_apply_of_mem_filterMap h.out

@[simp]
theorem getElem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {g} (h : t.WF) :
    (t.filterMap f)[k]'g =
      (f (t.getKey k (mem_of_mem_filterMap h g))
        (t[k]'(mem_of_mem_filterMap h g))).get
          (isSome_apply_of_mem_filterMap h g) :=
  DTreeMap.Raw.Const.get_filterMap h.out (h':= g)

/-- Simpler variant of `getElem_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} {g} (h : t.WF) :
    (t.filterMap f)[k]'g =
      (f k (t[k]'(mem_of_mem_filterMap h g))).get (by simpa [h] using isSome_apply_of_mem_filterMap h g) := by
  simp [getElem_filterMap, h]

theorem getElem!_filterMap [TransCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    (t.filterMap f)[k]! =
      (t[k]?.pbind (fun x h' =>
      f (t.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h')))
          x)).get! :=
  DTreeMap.Raw.Const.get!_filterMap h.out

/-- Simpler variant of `getElem!_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem!_filterMap' [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    (t.filterMap f)[k]! = (t[k]?.bind (f k)).get! := by
  simp [getElem!_filterMap, h]

theorem getElem!_filterMap_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : t.WF) :
    t.getKey? k = some k' → (t.filterMap f)[k]! = (t[k]?.bind
      fun x => f k' x).get! :=
  DTreeMap.Raw.Const.get!_filterMap_of_getKey?_eq_some h.out

theorem getD_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {fallback : γ} (h : t.WF) :
    getD (t.filterMap f) k fallback =
      (t[k]?.pbind (fun x h' =>
      f (t.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  DTreeMap.Raw.Const.getD_filterMap h.out

/-- Simpler variant of `getD_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getD_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} {fallback : γ} (h : t.WF) :
    getD (t.filterMap f) k fallback = (t[k]?.bind (f k)).getD fallback := by
  simp [getD_filterMap, h]

theorem getD_filterMap_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : t.WF) :
    t.getKey? k = some k' → getD (t.filterMap f) k fallback = (t[k]?.bind
      fun x => f k' x).getD fallback :=
  DTreeMap.Raw.Const.getD_filterMap_of_getKey?_eq_some h.out

@[grind =]
theorem getKey?_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    (t.filterMap f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h h'))).isSome) :=
  DTreeMap.Raw.Const.getKey?_filterMap h.out

@[simp]
theorem getKey_filterMap [TransCmp cmp]
    {f : (a : α) → β → Option γ} {k : α} {h'} (h : t.WF) :
    (t.filterMap f).getKey k h' = t.getKey k (mem_of_mem_filterMap h h') :=
  DTreeMap.Raw.getKey_filterMap h.out

@[grind =]
theorem getKey!_filterMap [TransCmp cmp] [Inhabited α]
    {f : α → β → Option γ} {k : α} (h : t.WF) :
    (t.filterMap f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h h'))).isSome)).get! :=
  DTreeMap.Raw.Const.getKey!_filterMap h.out

@[grind =]
theorem getKeyD_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k fallback : α} (h : t.WF) :
    (t.filterMap f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h h'))).isSome)).getD fallback :=
  DTreeMap.Raw.Const.getKeyD_filterMap h.out

end filterMap

section filter

theorem filterMap_equiv_filter {f : α → β → Bool} (h : t.WF) :
    (t.filterMap (fun k => Option.guard (fun v => f k v))) ~m (t.filter f) :=
  ⟨DTreeMap.Raw.filterMap_equiv_filter h.out⟩

theorem toList_filter
    {f : (a : α) → β → Bool} (h : t.WF) :
    (t.filter f).toList = t.toList.filter (fun p => f p.1 p.2) :=
  DTreeMap.Raw.Const.toList_filter h.out

theorem keys_filter_key {f : α → Bool} (h : t.WF) :
    (t.filter fun k _ => f k).keys = t.keys.filter f :=
  DTreeMap.Raw.keys_filter_key h.out

@[grind =]
theorem isEmpty_filter_iff [TransCmp cmp]
    {f : α → β → Bool} (h : t.WF) :
    (t.filter f).isEmpty = true ↔
      ∀ (k : α) (h : k ∈ t), f (t.getKey k h) (t[k]' h) = false :=
  DTreeMap.Raw.Const.isEmpty_filter_iff h.out

theorem isEmpty_filter_eq_false_iff [TransCmp cmp]
    {f : α → β → Bool} (h : t.WF) :
    (t.filter f).isEmpty = false ↔
      ∃ (k : α) (h : k ∈ t), f (t.getKey k h) (t[k]'h) :=
  DTreeMap.Raw.Const.isEmpty_filter_eq_false_iff h.out

-- TODO: `contains_filter` is missing

@[grind =]
theorem mem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    k ∈ t.filter f ↔ ∃ (h' : k ∈ t),
      f (t.getKey k h') (t[k]' h') :=
  DTreeMap.Raw.Const.mem_filter h.out

theorem mem_of_mem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    k ∈ t.filter f → k ∈ t :=
  DTreeMap.Raw.mem_of_mem_filter h.out

theorem size_filter_le_size [TransCmp cmp]
    {f : α → β → Bool} (h : t.WF) :
    (t.filter f).size ≤ t.size :=
  DTreeMap.Raw.size_filter_le_size h.out

grind_pattern size_filter_le_size => (t.filter f).size

theorem size_filter_eq_size_iff [TransCmp cmp]
    {f : α → β → Bool} (h : t.WF) :
    (t.filter f).size = t.size ↔ ∀ (a : α) (h : a ∈ t),
      f (t.getKey a h) t[a] :=
  DTreeMap.Raw.Const.size_filter_eq_size_iff h.out

theorem filter_equiv_self_iff [TransCmp cmp]
    {f : α → β → Bool} (h : t.WF) :
    (t.filter f) ~m t ↔ ∀ (a : α) (h : a ∈ t),
      f (t.getKey a h) t[a] :=
  ⟨fun h' => (DTreeMap.Raw.Const.filter_equiv_self_iff h.out).mp h'.1,
    fun h' => ⟨(DTreeMap.Raw.Const.filter_equiv_self_iff h.out).mpr h'⟩⟩

@[simp]
theorem getElem?_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    (t.filter f)[k]? = t[k]?.pfilter (fun x h' =>
      f (t.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x) :=
  DTreeMap.Raw.Const.get?_filter h.out

/-- Simpler variant of `getElem?_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem?_filter' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    (t.filter f)[k]? = t[k]?.filter (f k) := by
  simp [getElem?_filter, h]

theorem getElem?_filter_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Bool} {k k' : α} (h : t.WF) :
    t.getKey? k = some k' →
      (t.filter f)[k]? = t[k]?.filter (f k') :=
  DTreeMap.Raw.Const.get?_filter_of_getKey?_eq_some h.out

@[simp, grind =]
theorem getElem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {h'} (h : t.WF) :
    (t.filter f)[k]' h' = t[k]' (mem_of_mem_filter h h') :=
  DTreeMap.Raw.Const.get_filter h.out (h' := h')

theorem getElem!_filter [TransCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    (t.filter f)[k]! =
      (t[k]?.pfilter (fun x h' =>
      f (t.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  DTreeMap.Raw.Const.get!_filter h.out

/-- Simpler variant of `getElem!_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem!_filter' [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    (t.filter f)[k]! = (t[k]?.filter (f k)).get! := by
  simp [getElem!_filter, h]

theorem getElem!_filter_of_getKey?_eq_some [TransCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k k' : α} (h : t.WF) :
    t.getKey? k = some k' →
      (t.filter f)[k]! = (t[k]?.filter (fun x => f k' x)).get! :=
  DTreeMap.Raw.Const.get!_filter_of_getKey?_eq_some h.out

theorem getD_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {fallback : β} (h : t.WF) :
    getD (t.filter f) k fallback = (t[k]?.pfilter (fun x h' =>
      f (t.getKey k ((mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  DTreeMap.Raw.Const.getD_filter h.out

/-- Simpler variant of `getD_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getD_filter' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Bool} {k : α} {fallback : β} (h : t.WF) :
    getD (t.filter f) k fallback = (t[k]?.filter (f k)).getD fallback := by
  simp [getD_filter, h]

theorem getD_filter_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Bool} {k k' : α} {fallback : β} (h : t.WF) :
    t.getKey? k = some k' →
      getD (t.filter f) k fallback =
        (t[k]?.filter (fun x => f k' x)).getD fallback :=
  DTreeMap.Raw.Const.getD_filter_of_getKey?_eq_some h.out

theorem keys_filter [TransCmp cmp] {f : α → β → Bool} (h : t.WF) :
    (t.filter f).keys =
      (t.keys.attach.filter (fun ⟨x, h'⟩ => f x (t[x]' (mem_of_mem_keys h h')))).unattach :=
  DTreeMap.Raw.Const.keys_filter h.out

@[grind =]
theorem getKey?_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    (t.filter f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]' (mem_of_getKey?_eq_some h h')))) :=
  DTreeMap.Raw.Const.getKey?_filter h.out

theorem getKey?_filter_key [TransCmp cmp]
    {f : α → Bool} {k : α} (h : t.WF) :
    (t.filter fun k _ => f k).getKey? k = (t.getKey? k).filter f :=
  DTreeMap.Raw.getKey?_filter_key h.out

@[simp, grind =]
theorem getKey_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} (h : t.WF) {h'} :
    (t.filter f).getKey k h' = t.getKey k (mem_of_mem_filter h h') :=
  DTreeMap.Raw.getKey_filter h.out

@[grind =]
theorem getKey!_filter [TransCmp cmp] [Inhabited α]
    {f : α → β → Bool} {k : α} (h : t.WF) :
    (t.filter f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]' (mem_of_getKey?_eq_some h h'))))).get! :=
  DTreeMap.Raw.Const.getKey!_filter h.out

theorem getKey!_filter_key [TransCmp cmp] [Inhabited α]
    {f : α → Bool} {k : α} (h : t.WF) :
    (t.filter fun k _ => f k).getKey! k = ((t.getKey? k).filter f).get! :=
  DTreeMap.Raw.getKey!_filter_key h.out

@[grind =]
theorem getKeyD_filter [TransCmp cmp]
    {f : α → β → Bool} {k fallback : α} (h : t.WF) :
    (t.filter f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]' (mem_of_getKey?_eq_some h h'))))).getD fallback :=
  DTreeMap.Raw.Const.getKeyD_filter h.out

theorem getKeyD_filter_key [TransCmp cmp]
    {f : α → Bool} {k fallback : α} (h : t.WF) :
    (t.filter fun k _ => f k).getKeyD k fallback = ((t.getKey? k).filter f).getD fallback :=
  DTreeMap.Raw.getKeyD_filter_key h.out

end filter

section map

theorem map_id_equiv : (t.map fun _ v => v) ~m t :=
  ⟨DTreeMap.Raw.map_id_equiv⟩

theorem map_map_equiv {f : α → β → γ} {g : α → γ → δ} :
    ((t.map f).map g) ~m (t.map fun k v => g k (f k v)) :=
  ⟨DTreeMap.Raw.map_map_equiv⟩

theorem toList_map {f : (a : α) → β → γ} :
    (t.map f).toList = t.toList.map (fun p => ⟨p.1, f p.1 p.2⟩) :=
  DTreeMap.Raw.Const.toList_map

theorem keys_map {f : α → β → γ} : (t.map f).keys = t.keys :=
  DTreeMap.Raw.keys_map

theorem filterMap_equiv_map [TransCmp cmp]
    {f : α → β → γ} (h : t.WF) :
    (t.filterMap (fun k v => Option.some (f k v))) ~m (t.map f) :=
  ⟨DTreeMap.Raw.filterMap_equiv_map h.out⟩

@[simp, grind =]
theorem isEmpty_map [TransCmp cmp] {f : α → β → γ} :
    (t.map f).isEmpty = t.isEmpty :=
  DTreeMap.Raw.isEmpty_map

@[simp, grind =]
theorem contains_map [TransCmp cmp]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f).contains k = t.contains k :=
  DTreeMap.Raw.contains_map h.out

theorem contains_of_contains_map [TransCmp cmp]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f).contains k = true → t.contains k = true :=
  DTreeMap.Raw.contains_of_contains_map h.out

@[simp, grind =]
theorem mem_map [TransCmp cmp]
    {f : (a : α) → β → γ} {k : α} (h : t.WF) :
    k ∈ (t.map f) ↔ k ∈ t :=
  DTreeMap.Raw.mem_map h.out

theorem mem_of_mem_map [TransCmp cmp]
    {f : α → β → γ} {k : α} (h : t.WF) :
    k ∈ (t.map f) → k ∈ t :=
  DTreeMap.Raw.mem_of_mem_map h.out

@[simp, grind =]
theorem size_map [TransCmp cmp] {f : α → β → γ} :
    (t.map f).size = t.size :=
  DTreeMap.Raw.size_map

@[simp, grind =]
theorem getKey?_map [TransCmp cmp]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f).getKey? k = t.getKey? k :=
  DTreeMap.Raw.getKey?_map h.out

@[simp, grind =]
theorem getKey_map [TransCmp cmp]
    {f : α → β → γ} {k : α} {h'} (h : t.WF) :
    (t.map f).getKey k h' = t.getKey k (mem_of_mem_map h h') :=
  DTreeMap.Raw.getKey_map h.out

@[simp, grind =]
theorem getKey!_map [TransCmp cmp] [Inhabited α]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f).getKey! k = t.getKey! k :=
  DTreeMap.Raw.getKey!_map h.out

@[simp, grind =]
theorem getKeyD_map [TransCmp cmp]
    {f : α → β → γ} {k fallback : α} (h : t.WF) :
    (t.map f).getKeyD k fallback = t.getKeyD k fallback :=
  DTreeMap.Raw.getKeyD_map h.out

@[simp, grind =]
theorem getElem?_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f)[k]? = t[k]?.map (f k) :=
  DTreeMap.Raw.Const.get?_map h.out

/-- Variant of `getElem?_map` that holds without `LawfulEqCmp`. -/
@[simp (low)]
theorem getElem?_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f)[k]? = t[k]?.pmap (fun v h' => f (t.getKey k h') v)
      (fun _ h' => (mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h')) :=
  DTreeMap.Raw.Const.get?_map' h.out

theorem getElem?_map_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → γ} {k k' : α} (h : t.WF) (h' : t.getKey? k = some k') :
    (t.map f)[k]? = t[k]?.map (f k') :=
  DTreeMap.Raw.Const.get?_map_of_getKey?_eq_some h.out h'

@[simp, grind =]
theorem getElem_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} {h'} (h : t.WF) :
    (t.map f)[k]' h' =
      (f k (t[k]' (mem_of_mem_map h h'))) :=
  DTreeMap.Raw.Const.get_map h.out (h':= h')

/-- Variant of `getElem_map` that holds without `LawfulEqCmp`. -/
@[simp (low)]
theorem getElem_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} {h'} (h : t.WF) :
    (t.map f)[k]' h' =
      (f (t.getKey k (mem_of_mem_map h h'))
        (t[k]' (mem_of_mem_map h h'))) :=
  DTreeMap.Raw.Const.get_map' h.out (h':= h')

@[grind =]
theorem getElem!_map [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f)[k]! =
      (t[k]?.map (f k)).get! :=
  DTreeMap.Raw.Const.get!_map h.out

/-- Variant of `getElem!_map` that holds without `LawfulEqCmp`. -/
theorem getElem!_map' [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k : α} (h : t.WF) :
    (t.map f)[k]! =
      ((t[k]?).pmap (fun v h => f (t.getKey k h) v)
        (fun _ h' => (mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))).get! :=
  DTreeMap.Raw.Const.get!_map' h.out

theorem getElem!_map_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : t.WF) (h' : t.getKey? k = some k') :
    (t.map f)[k]! = (t[k]?.map (f k')).get! :=
  DTreeMap.Raw.Const.get!_map_of_getKey?_eq_some h.out h'

@[grind =]
theorem getD_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} {fallback : γ} (h : t.WF) :
    (t.map f).getD k fallback =
      (t[k]?.map (f k)).getD fallback :=
  DTreeMap.Raw.Const.getD_map h.out

/-- Variant of `getD_map` that holds without `LawfulEqCmp`. -/
theorem getD_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} {fallback : γ} (h : t.WF) :
    getD (t.map f) k fallback =
      (t[k]?.pmap (fun v h => f (t.getKey k h) v)
        (fun _ h' => (mem_iff_isSome_getElem? h).mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  DTreeMap.Raw.Const.getD_map' h.out

theorem getD_map_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : t.WF) (h' : t.getKey? k = some k') :
    (t.map f).getD k fallback = (t[k]?.map (f k')).getD fallback :=
  DTreeMap.Raw.Const.getD_map_of_getKey?_eq_some h.out h'

end map

end Std.TreeMap.Raw
