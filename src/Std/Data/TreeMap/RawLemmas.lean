/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.RawLemmas
import Std.Data.TreeMap.Raw

/-!
# Tree map lemmas

This file contains lemmas about `Std.Data.TreeMap.Raw`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

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
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).isEmpty = false :=
  DTreeMap.Raw.isEmpty_insertIfNew h

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
    (empty : Raw α β cmp).erase k = empty :=
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

theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.Raw.size_insertIfNew h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  DTreeMap.Raw.size_le_size_insertIfNew h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  DTreeMap.Raw.size_insertIfNew_le h

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
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (contains_of_contains_insert h h₁ h₂) :=
  DTreeMap.Raw.Const.get_insert h

@[simp]
theorem getElem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v) k (contains_insert_self h) = v :=
  DTreeMap.Raw.Const.get_insert_self h

@[simp]
theorem getElem_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    get (t.erase k) a h' = t[a]'(contains_of_contains_erase h h') :=
  DTreeMap.Raw.Const.get_erase h

theorem getElem?_eq_some_getElem [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t[a]? = some (t[a]'h') :=
  DTreeMap.Raw.Const.get?_eq_some_get h

theorem getElem_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((contains_congr h hab).symm.trans h') :=
  DTreeMap.Raw.Const.get_congr h hab

@[simp]
theorem getElem!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : Raw α β cmp) a = default :=
  DTreeMap.Raw.Const.get!_emptyc

theorem getElem!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → t[a]! = default :=
  DTreeMap.Raw.Const.get!_of_isEmpty h

theorem getElem!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else t[a]! :=
  DTreeMap.Raw.Const.get!_insert h

@[simp]
theorem getElem!_insert_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α}
    {v : β} : get! (t.insert k v) k = v :=
  DTreeMap.Raw.Const.get!_insert_self h

theorem getElem!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → t[a]! = default :=
  DTreeMap.Raw.Const.get!_eq_default_of_contains_eq_false h

theorem getElem!_eq_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → t[a]! = default :=
  DTreeMap.Raw.Const.get!_eq_default h

theorem getElem!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else t[a]! :=
  DTreeMap.Raw.Const.get!_erase h

@[simp]
theorem getElem!_erase_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k) k = default :=
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
theorem getElemD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  DTreeMap.Raw.Const.getD_emptyc

theorem getElemD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_of_isEmpty h

theorem getElemD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  DTreeMap.Raw.Const.getD_insert h

@[simp]
theorem getElemD_insert_self [TransCmp cmp] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  DTreeMap.Raw.Const.getD_insert_self h

theorem getElemD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_eq_fallback_of_contains_eq_false h

theorem getElemD_eq_fallback [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  DTreeMap.Raw.Const.getD_eq_fallback h

theorem getElemD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  DTreeMap.Raw.Const.getD_erase h

@[simp]
theorem getElemD_erase_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  DTreeMap.Raw.Const.getD_erase_self h

theorem getElem?_eq_some_getElemD_of_contains [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  DTreeMap.Raw.Const.get?_eq_some_getD_of_contains h

theorem getElem?_eq_some_getElemD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → t[a]? = some (getD t a fallback) :=
  DTreeMap.Raw.Const.get?_eq_some_getD h

theorem getElemD_eq_getElemD_getElem? [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t[a]?.getD fallback :=
  DTreeMap.Raw.Const.getD_eq_getD_get? h

theorem getElem_eq_getElemD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} {h'} :
    t[a]'h' = getD t a fallback :=
  DTreeMap.Raw.Const.get_eq_getD h

theorem getElem!_eq_getElemD_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t[a]! = getD t a default :=
  DTreeMap.Raw.Const.get!_eq_getD_default h

theorem getElemD_congr [TransCmp cmp] (h : t.WF) {a b : α} {fallback : β}
    (hab : cmp a b = .eq) : getD t a fallback = getD t b fallback :=
  DTreeMap.Raw.Const.getD_congr h hab

end Std.TreeMap.Raw
