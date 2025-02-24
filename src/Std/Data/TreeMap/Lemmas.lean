/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Lemmas
import Std.Data.TreeMap.Basic

/-!
# Tree map lemmas

This file contains lemmas about `Std.Data.TreeMap`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

private theorem ext {t t' : TreeMap α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : TreeMap α β cmp).isEmpty :=
  DTreeMap.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).isEmpty = false :=
  DTreeMap.isEmpty_insert

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DTreeMap.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  DTreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  DTreeMap.mem_congr hab

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).isEmpty = false :=
  DTreeMap.isEmpty_insertIfNew

@[simp]
theorem contains_emptyc {k : α} : (∅ : TreeMap α β cmp).contains k = false :=
  DTreeMap.contains_emptyc

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : TreeMap α β cmp) :=
  DTreeMap.not_mem_emptyc

theorem contains_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → t.contains a = false :=
  DTreeMap.contains_of_isEmpty

theorem not_mem_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty → a ∉ t :=
  DTreeMap.not_mem_of_isEmpty

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  DTreeMap.isEmpty_eq_false_iff_exists_contains_eq_true

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  DTreeMap.isEmpty_eq_false_iff_exists_mem

theorem isEmpty_iff_forall_contains [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  DTreeMap.isEmpty_iff_forall_contains

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  DTreeMap.isEmpty_iff_forall_not_mem

@[simp]
theorem insert_eq_insert {p : α × β} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : α × β} :
    Singleton.singleton p = (∅ : TreeMap α β cmp).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [h : TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.contains_insert

@[simp]
theorem mem_insert [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  DTreeMap.mem_insert

theorem contains_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).contains k :=
  DTreeMap.contains_insert_self

theorem mem_insert_self [TransCmp cmp] {k : α} {v : β} :
    k ∈ t.insert k v :=
  DTreeMap.mem_insert_self

theorem contains_of_contains_insert [TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  DTreeMap.contains_of_contains_insert

theorem mem_of_mem_insert [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  DTreeMap.mem_of_mem_insert

@[simp]
theorem size_emptyc : (∅ : TreeMap α β cmp).size = 0 :=
  DTreeMap.size_emptyc

theorem isEmpty_eq_size_eq_zero :
    t.isEmpty = (t.size == 0) :=
  DTreeMap.isEmpty_eq_size_eq_zero

theorem size_insert [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  DTreeMap.size_insert

theorem size_le_size_insert [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insert k v).size :=
  DTreeMap.size_le_size_insert

theorem size_insert_le [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).size ≤ t.size + 1 :=
  DTreeMap.size_insert_le

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : TreeMap α β cmp).erase k = empty :=
  ext <| DTreeMap.erase_emptyc

@[simp]
theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  DTreeMap.isEmpty_erase

@[simp]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  DTreeMap.contains_erase

@[simp]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  DTreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  DTreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  DTreeMap.mem_of_mem_erase

theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  DTreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  DTreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  DTreeMap.size_le_size_erase

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsert k v).1 = t.contains k :=
  DTreeMap.containsThenInsert_fst

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| DTreeMap.containsThenInsert_snd

@[simp]
theorem containsThenInsertIfNew_fst [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  DTreeMap.containsThenInsertIfNew_fst

@[simp]
theorem containsThenInsertIfNew_snd [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.containsThenInsertIfNew_snd

@[simp]
theorem contains_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.contains_insertIfNew

@[simp]
theorem mem_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  DTreeMap.mem_insertIfNew

@[simp]
theorem contains_insertIfNew_self [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).contains k :=
  DTreeMap.contains_insertIfNew_self

@[simp]
theorem mem_insertIfNew_self [TransCmp cmp] {k : α} {v : β} :
    k ∈ t.insertIfNew k v :=
  DTreeMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  DTreeMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  DTreeMap.contains_of_contains_insertIfNew

theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.size_insertIfNew

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  DTreeMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  DTreeMap.size_insertIfNew_le

@[simp] theorem get_eq_getElem {a : α} {h} : get t a h = t[a]'h := rfl
@[simp] theorem get?_eq_getElem? {a : α} : get? t a = t[a]? := rfl
@[simp] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! t a = t[a]! := rfl

@[simp]
theorem getElem?_emptyc [TransCmp cmp] {a : α} :
    (∅ : TreeMap α β cmp)[a]? = none :=
  DTreeMap.Const.get?_emptyc (cmp := cmp) (a := a)

theorem getElem?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t[a]? = none :=
  DTreeMap.Const.get?_of_isEmpty

theorem getElem?_insert [TransCmp cmp] {a k : α} {v : β} :
    (t.insert k v)[a]? = if cmp k a = .eq then some v else t[a]? :=
  DTreeMap.Const.get?_insert

@[simp]
theorem getElem?_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v)[k]? = some v :=
  DTreeMap.Const.get?_insert_self

theorem contains_eq_isSome_getElem? [TransCmp cmp] {a : α} :
    t.contains a = t[a]?.isSome :=
  DTreeMap.Const.contains_eq_isSome_get?

theorem mem_iff_isSome_getElem? [TransCmp cmp] {a : α} :
    a ∈ t ↔ t[a]?.isSome :=
  DTreeMap.Const.mem_iff_isSome_get?

theorem getElem?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t[a]? = none :=
  DTreeMap.Const.get?_eq_none_of_contains_eq_false

theorem getElem?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t[a]? = none :=
  DTreeMap.Const.get?_eq_none

theorem getElem?_erase [TransCmp cmp] {k a : α} :
    (t.erase k)[a]? = if cmp k a = .eq then none else t[a]? :=
  DTreeMap.Const.get?_erase

@[simp]
theorem getElem?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k)[k]? = none :=
  DTreeMap.Const.get?_erase_self

theorem getElem?_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) :
    t[a]? = t[b]? :=
  DTreeMap.Const.get?_congr hab

theorem getElem_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insert k v)[a]'h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (contains_of_contains_insert h₁ h₂) :=
  DTreeMap.Const.get_insert

@[simp]
theorem getElem_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v)[k]'(contains_insert_self) = v :=
  DTreeMap.Const.get_insert_self

@[simp]
theorem getElem_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k)[a]'h' = t[a]'(contains_of_contains_erase h') :=
  DTreeMap.Const.get_erase

theorem getElem?_eq_some_getElem [TransCmp cmp] {a : α} {h} :
    t[a]? = some (t[a]'h) :=
  DTreeMap.Const.get?_eq_some_get

theorem getElem_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((contains_congr hab).symm.trans h') :=
  DTreeMap.Const.get_congr hab

@[simp]
theorem getElem!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    (∅ : TreeMap α β cmp)[a]! = default :=
  DTreeMap.Const.get!_emptyc (cmp := cmp) (a := a)

theorem getElem!_of_isEmpty [TransCmp cmp] [Inhabited β] {a : α} :
    t.isEmpty = true → t[a]! = default :=
  DTreeMap.Const.get!_of_isEmpty

theorem getElem!_insert [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    (t.insert k v)[a]! = if cmp k a = .eq then v else t[a]! :=
  DTreeMap.Const.get!_insert

@[simp]
theorem getElem!_insert_self [TransCmp cmp] [Inhabited β] {k : α}
    {v : β} : (t.insert k v)[k]! = v :=
  DTreeMap.Const.get!_insert_self

theorem getElem!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = false → t[a]! = default :=
  DTreeMap.Const.get!_eq_default_of_contains_eq_false

theorem getElem!_eq_default [TransCmp cmp] [Inhabited β] {a : α} :
    ¬ a ∈ t → t[a]! = default :=
  DTreeMap.Const.get!_eq_default

theorem getElem!_erase [TransCmp cmp] [Inhabited β] {k a : α} :
    (t.erase k)[a]! = if cmp k a = .eq then default else t[a]! :=
  DTreeMap.Const.get!_erase

@[simp]
theorem getElem!_erase_self [TransCmp cmp] [Inhabited β] {k : α} :
    (t.erase k)[k]! = default :=
  DTreeMap.Const.get!_erase_self

theorem getElem?_eq_some_getElem!_of_contains [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = true → t[a]? = some t[a]! :=
  DTreeMap.Const.get?_eq_some_get!

theorem getElem?_eq_some_getElem! [TransCmp cmp] [Inhabited β] {a : α} :
    a ∈ t → t[a]? = some t[a]! :=
  DTreeMap.Const.get?_eq_some_get!

theorem getElem!_eq_getElem!_getElem? [TransCmp cmp] [Inhabited β] {a : α} :
    t[a]! = t[a]?.get! :=
  DTreeMap.Const.get!_eq_get!_get?

theorem getElem_eq_getElem! [TransCmp cmp] [Inhabited β] {a : α} {h} :
    t[a]'h = t[a]! :=
  DTreeMap.Const.get_eq_get!

theorem getElem!_congr [TransCmp cmp] [Inhabited β] {a b : α}
    (hab : cmp a b = .eq) : t[a]! = t[b]! :=
  DTreeMap.Const.get!_congr hab

@[simp]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : TreeMap α β cmp) a fallback = fallback :=
  DTreeMap.Const.getD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  DTreeMap.Const.getD_of_isEmpty

theorem getD_insert [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  DTreeMap.Const.getD_insert

@[simp]
theorem getD_insert_self [TransCmp cmp] {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  DTreeMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  DTreeMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  DTreeMap.Const.getD_eq_fallback

theorem getD_erase [TransCmp cmp] {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  DTreeMap.Const.getD_erase

@[simp]
theorem getD_erase_self [TransCmp cmp] {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  DTreeMap.Const.getD_erase_self

theorem getElem?_eq_some_getD_of_contains [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  DTreeMap.Const.get?_eq_some_getD_of_contains

theorem getElem?_eq_some_getD [TransCmp cmp] {a : α} {fallback : β} :
    a ∈ t → t[a]? = some (getD t a fallback) :=
  DTreeMap.Const.get?_eq_some_getD

theorem getD_eq_getD_getElem? [TransCmp cmp] {a : α} {fallback : β} :
    getD t a fallback = t[a]?.getD fallback :=
  DTreeMap.Const.getD_eq_getD_get?

theorem getElem_eq_getD [TransCmp cmp] {a : α} {fallback : β} {h} :
    t[a]'h = getD t a fallback :=
  DTreeMap.Const.get_eq_getD

theorem getElem!_eq_getD_default [TransCmp cmp] [Inhabited β] {a : α} :
    t[a]! = getD t a default :=
  DTreeMap.Const.get!_eq_getD_default

theorem getD_congr [TransCmp cmp] {a b : α} {fallback : β}
    (hab : cmp a b = .eq) : getD t a fallback = getD t b fallback :=
  DTreeMap.Const.getD_congr hab

end Std.TreeMap
