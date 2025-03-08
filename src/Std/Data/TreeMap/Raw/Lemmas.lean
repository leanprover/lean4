/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.Basic

/-!
# Tree map lemmas

This file contains lemmas about `Std.Data.TreeMap.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
These proofs can be obtained from `Std.Data.TreeMap.Raw.WF`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

namespace Std.TreeMap.Raw

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap.Raw α β cmp}

private theorem ext {t t' : Raw α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : TreeMap.Raw α β cmp).isEmpty :=
  DTreeMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).isEmpty = false :=
  DTreeMap.Raw.isEmpty_insert h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DTreeMap.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  DTreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  DTreeMap.Raw.mem_congr h hab

@[simp]
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

@[simp]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.Raw.contains_insert h

@[simp]
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

@[simp]
theorem size_emptyc : (∅ : Raw α β cmp).size = 0 :=
  DTreeMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  DTreeMap.Raw.isEmpty_eq_size_eq_zero h.out

theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  DTreeMap.Raw.size_insert h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    t.size ≤ (t.insert k v).size :=
  DTreeMap.Raw.size_le_size_insert h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).size ≤ t.size + 1 :=
  DTreeMap.Raw.size_insert_le h

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : Raw α β cmp).erase k = ∅ :=
  ext <| DTreeMap.Raw.erase_emptyc

@[simp]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  DTreeMap.Raw.isEmpty_erase h

@[simp]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  DTreeMap.Raw.contains_erase h

@[simp]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  DTreeMap.Raw.mem_erase h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  DTreeMap.Raw.contains_of_contains_erase h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  DTreeMap.Raw.mem_of_mem_erase h

theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  DTreeMap.Raw.size_erase h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  DTreeMap.Raw.size_erase_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  DTreeMap.Raw.size_le_size_erase h

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsert k v).1 = t.contains k :=
  DTreeMap.Raw.containsThenInsert_fst h

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| DTreeMap.Raw.containsThenInsert_snd h

@[simp]
theorem containsThenInsertIfNew_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  DTreeMap.Raw.containsThenInsertIfNew_fst h

@[simp]
theorem containsThenInsertIfNew_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.Raw.containsThenInsertIfNew_snd h

@[simp] theorem get_eq_getElem {a : α} {h} : get t a h = t[a]'h := rfl
@[simp] theorem get?_eq_getElem? {a : α} : get? t a = t[a]? := rfl
@[simp] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! t a = t[a]! := rfl

@[simp]
theorem getElem?_emptyc [TransCmp cmp] {a : α} :
    (∅ : Raw α β cmp)[a]? = none :=
  DTreeMap.Raw.Const.get?_emptyc (cmp := cmp) (a := a)

theorem getElem?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t[a]? = none :=
  DTreeMap.Raw.Const.get?_of_isEmpty h

theorem getElem?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    (t.insert k v)[a]? = if cmp k a = .eq then some v else t[a]? :=
  DTreeMap.Raw.Const.get?_insert h

@[simp]
theorem getElem?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v)[k]? = some v :=
  DTreeMap.Raw.Const.get?_insert_self h

theorem contains_eq_isSome_getElem? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = t[a]?.isSome :=
  DTreeMap.Raw.Const.contains_eq_isSome_get? h

theorem mem_iff_isSome_getElem? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ t[a]?.isSome :=
  DTreeMap.Raw.Const.mem_iff_isSome_get? h

theorem getElem?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t[a]? = none :=
  DTreeMap.Raw.Const.get?_eq_none_of_contains_eq_false h

theorem getElem?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t[a]? = none :=
  DTreeMap.Raw.Const.get?_eq_none h

theorem getElem?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k)[a]? = if cmp k a = .eq then none else t[a]? :=
  DTreeMap.Raw.Const.get?_erase h

@[simp]
theorem getElem?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k)[k]? = none :=
  DTreeMap.Raw.Const.get?_erase_self h

theorem getElem?_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    t[a]? = t[b]? :=
  DTreeMap.Raw.Const.get?_congr h hab

theorem getElem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insert k v)[a]'h₁ =
      if h₂ : cmp k a = .eq then v
      else t[a]'(mem_of_mem_insert h h₁ h₂) :=
  DTreeMap.Raw.Const.get_insert h

@[simp]
theorem getElem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v)[k]'(mem_insert_self h) = v :=
  DTreeMap.Raw.Const.get_insert_self h

@[simp]
theorem getElem_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k)[a]'h' = t[a]'(mem_of_mem_erase h h') :=
  DTreeMap.Raw.Const.get_erase h

theorem getElem?_eq_some_getElem [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t[a]? = some (t[a]'h') :=
  DTreeMap.Raw.Const.get?_eq_some_get h

theorem getElem_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((mem_congr h hab).mp h') :=
  DTreeMap.Raw.Const.get_congr h hab

@[simp]
theorem getElem!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    (∅ : Raw α β cmp)[a]! = default :=
  DTreeMap.Raw.Const.get!_emptyc (cmp := cmp) (a := a)

theorem getElem!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → t[a]! = default :=
  DTreeMap.Raw.Const.get!_of_isEmpty h

theorem getElem!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
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

theorem getElem!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
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

theorem getElem!_eq_getElem!_getElem? [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t[a]! = t[a]?.get! :=
  DTreeMap.Raw.Const.get!_eq_get!_get? h

theorem getElem_eq_getElem! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} {h'} :
    t[a]'h' = t[a]! :=
  DTreeMap.Raw.Const.get_eq_get! h

theorem getElem!_congr [TransCmp cmp] [Inhabited β] (h : t.WF) {a b : α}
    (hab : cmp a b = .eq) : t[a]! = t[b]! :=
  DTreeMap.Raw.Const.get!_congr h hab

@[simp]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  DTreeMap.Raw.Const.getD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
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

theorem getD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
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
    t.contains a = true → get? t a = some (getD t a fallback) :=
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

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : Raw α β cmp).getKey? a = none :=
  DTreeMap.Raw.getKey?_emptyc

theorem getKey?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  DTreeMap.Raw.getKey?_of_isEmpty h

theorem getKey?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  DTreeMap.Raw.getKey?_insert h

@[simp]
theorem getKey?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).getKey? k = some k :=
  DTreeMap.Raw.getKey?_insert_self h

theorem contains_eq_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  DTreeMap.Raw.contains_eq_isSome_getKey? h

theorem mem_iff_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  DTreeMap.Raw.mem_iff_isSome_getKey? h

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none :=
  DTreeMap.Raw.getKey?_eq_none_of_contains_eq_false h

theorem getKey?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  DTreeMap.Raw.getKey?_eq_none h

theorem getKey?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  DTreeMap.Raw.getKey?_erase h

@[simp]
theorem getKey?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).getKey? k = none :=
  DTreeMap.Raw.getKey?_erase_self h

theorem getKey_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h h₁ h₂) :=
  DTreeMap.Raw.getKey_insert h

@[simp]
theorem getKey_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insert k v).getKey k (mem_insert_self h) = k :=
  DTreeMap.Raw.getKey_insert_self h

@[simp]
theorem getKey_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h h') :=
  DTreeMap.Raw.getKey_erase h

theorem getKey?_eq_some_getKey [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  DTreeMap.Raw.getKey?_eq_some_getKey h

@[simp]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : Raw α β cmp).getKey! a = default :=
  DTreeMap.Raw.getKey!_emptyc

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  DTreeMap.Raw.getKey!_of_isEmpty h

theorem getKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
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

theorem getKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
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

@[simp]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : Raw α β cmp).getKeyD a fallback = fallback :=
  DTreeMap.Raw.getKeyD_emptyc

theorem getKeyD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  DTreeMap.Raw.getKeyD_of_isEmpty h

theorem getKeyD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} {v : β} :
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

theorem getKeyD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
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

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).isEmpty = false :=
  DTreeMap.Raw.isEmpty_insertIfNew h

@[simp]
theorem contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.Raw.contains_insertIfNew h

@[simp]
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

theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.Raw.size_insertIfNew h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  DTreeMap.Raw.size_le_size_insertIfNew h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  DTreeMap.Raw.size_insertIfNew_le h

theorem getElem?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v)[a]? =
      if cmp k a = .eq ∧ ¬ k ∈ t then
        some v
      else
        t[a]? :=
  DTreeMap.Raw.Const.get?_insertIfNew h

theorem getElem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v)[a]'h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        v
      else
        t[a]'(mem_of_mem_insertIfNew' h h₁ h₂) :=
  DTreeMap.Raw.Const.get_insertIfNew h

theorem getElem!_insertIfNew [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v)[a]! = if cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]! :=
  DTreeMap.Raw.Const.get!_insertIfNew h

theorem getD_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  DTreeMap.Raw.Const.getD_insertIfNew h

theorem getKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  DTreeMap.Raw.getKey?_insertIfNew h

theorem getKey_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  DTreeMap.Raw.getKey_insertIfNew h

theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
    {v : β} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  DTreeMap.Raw.getKey!_insertIfNew h

theorem getKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k a fallback : α}
    {v : β} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  DTreeMap.Raw.getKeyD_insertIfNew h

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  DTreeMap.Raw.Const.getThenInsertIfNew?_fst h

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.Raw.Const.getThenInsertIfNew?_snd h

@[simp]
theorem length_keys [TransCmp cmp] (h : t.WF) :
    t.keys.length = t.size :=
  DTreeMap.Raw.length_keys h

@[simp]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty :=
  DTreeMap.Raw.isEmpty_keys

@[simp]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    t.keys.contains k = t.contains k :=
  DTreeMap.Raw.contains_keys h

@[simp]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  DTreeMap.Raw.mem_keys h

theorem distinct_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.Raw.distinct_keys h

@[simp]
theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  DTreeMap.Raw.Const.map_fst_toList_eq_keys

@[simp]
theorem length_toList (h : t.WF) :
    (toList t).length = t.size :=
  DTreeMap.Raw.Const.length_toList h

@[simp]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  DTreeMap.Raw.Const.isEmpty_toList

@[simp]
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

section monadic

variable {δ : Type w} {m : Type w → Type w}

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

@[simp]
theorem forM_eq_forM [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    ForM.forM t f = t.toList.forM f :=
  DTreeMap.Raw.Const.forMUncurried_eq_forM_toList (f := f)

@[simp]
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

@[simp]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp]
theorem insertMany_list_singleton {k : α} {v : β} :
    t.insertMany [⟨k, v⟩] = t.insert k v :=
  rfl

theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    t.insertMany (⟨k, v⟩ :: l) = (t.insert k v).insertMany l :=
  ext <| DTreeMap.Raw.Const.insertMany_cons

@[simp]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  DTreeMap.Raw.Const.contains_insertMany_list h

@[simp]
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

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  DTreeMap.Raw.Const.size_insertMany_list_le h

@[simp]
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

@[simp]
theorem ofList_nil :
    ofList ([] : List (α × β)) cmp = ∅ := by
  rfl

@[simp]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] cmp = (∅ : Raw α β cmp).insert k v := by
  rfl

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : Raw α β cmp).insert k v) tl :=
  ext DTreeMap.Raw.Const.ofList_cons

@[simp]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  DTreeMap.Raw.Const.contains_ofList

@[simp]
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
  simp [mem_iff_contains]

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

end Std.TreeMap.Raw
