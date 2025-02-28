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
    (∅ : TreeMap α β cmp).erase k = ∅ :=
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
      else get t a (mem_of_mem_insert h₁ h₂) :=
  DTreeMap.Const.get_insert

@[simp]
theorem getElem_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v)[k]'mem_insert_self = v :=
  DTreeMap.Const.get_insert_self

@[simp]
theorem getElem_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k)[a]'h' = t[a]'(mem_of_mem_erase h') :=
  DTreeMap.Const.get_erase

theorem getElem?_eq_some_getElem [TransCmp cmp] {a : α} {h} :
    t[a]? = some (t[a]'h) :=
  DTreeMap.Const.get?_eq_some_get

theorem getElem_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((mem_congr hab).mp h') :=
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

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : TreeMap α β cmp).getKey? a = none :=
  DTreeMap.getKey?_emptyc

theorem getKey?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  DTreeMap.getKey?_of_isEmpty

theorem getKey?_insert [TransCmp cmp] {a k : α} {v : β} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  DTreeMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).getKey? k = some k :=
  DTreeMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [TransCmp cmp] {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  DTreeMap.contains_eq_isSome_getKey?

theorem mem_iff_isSome_getKey? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  DTreeMap.mem_iff_isSome_getKey?

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.getKey? a = none :=
  DTreeMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  DTreeMap.getKey?_eq_none

theorem getKey?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  DTreeMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).getKey? k = none :=
  DTreeMap.getKey?_erase_self

theorem getKey_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h₁ h₂) :=
  DTreeMap.getKey_insert

@[simp]
theorem getKey_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).getKey k mem_insert_self = k :=
  DTreeMap.getKey_insert_self

@[simp]
theorem getKey_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h') :=
  DTreeMap.getKey_erase

theorem getKey?_eq_some_getKey [TransCmp cmp] {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  DTreeMap.getKey?_eq_some_getKey

@[simp]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : TreeMap α β cmp).getKey! a = default :=
  DTreeMap.getKey!_emptyc

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  DTreeMap.getKey!_of_isEmpty

theorem getKey!_insert [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β} : (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  DTreeMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] {a : α}
    {b : β} : (t.insert a b).getKey! a = a :=
  DTreeMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.getKey! a = default :=
  DTreeMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  DTreeMap.getKey!_eq_default

theorem getKey!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  DTreeMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] {k : α} :
    (t.erase k).getKey! k = default :=
  DTreeMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  DTreeMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  DTreeMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  DTreeMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] {a : α} {h} :
    t.getKey a h = t.getKey! a :=
  DTreeMap.getKey_eq_getKey!

@[simp]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : TreeMap α β cmp).getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_emptyc

theorem getKeyD_of_isEmpty [TransCmp cmp] {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_of_isEmpty

theorem getKeyD_insert [TransCmp cmp] {k a fallback : α} {v : β} :
    (t.insert k v).getKeyD a fallback = if cmp k a = .eq then k else t.getKeyD a fallback :=
  DTreeMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] {a fallback : α} {b : β} :
    (t.insert a b).getKeyD a fallback = a :=
  DTreeMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_eq_fallback

theorem getKeyD_erase [TransCmp cmp] {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  DTreeMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  DTreeMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  DTreeMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [TransCmp cmp] {a fallback : α} :
  a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  DTreeMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  DTreeMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [TransCmp cmp] {a fallback : α} {h} :
    t.getKey a h = t.getKeyD a fallback :=
  DTreeMap.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = t.getKeyD a default :=
  DTreeMap.getKey!_eq_getKeyD_default

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).isEmpty = false :=
  DTreeMap.isEmpty_insertIfNew

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

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] {k a : α} {v : β} :
    a ∈ (t.insertIfNew k v) → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  DTreeMap.mem_of_mem_insertIfNew'

theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.size_insertIfNew

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  DTreeMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  DTreeMap.size_insertIfNew_le

theorem getElem?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]? =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else t[a]? :=
  DTreeMap.Const.get?_insertIfNew

theorem getElem_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v)[a]'h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]'(mem_of_mem_insertIfNew' h₁ h₂) :=
  DTreeMap.Const.get_insertIfNew

theorem getElem!_insertIfNew [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]! = if cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]! :=
  DTreeMap.Const.get!_insertIfNew

theorem getD_insertIfNew [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  DTreeMap.Const.getD_insertIfNew

theorem getKey?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  DTreeMap.getKey?_insertIfNew

theorem getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂) :=
  DTreeMap.getKey_insertIfNew

theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  DTreeMap.getKey!_insertIfNew

theorem getKeyD_insertIfNew [TransCmp cmp] {k a fallback : α}
    {v : β} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  DTreeMap.getKeyD_insertIfNew

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  DTreeMap.Const.getThenInsertIfNew?_fst

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.Const.getThenInsertIfNew?_snd

@[simp]
theorem length_keys [TransCmp cmp] :
    t.keys.length = t.size :=
  DTreeMap.length_keys

@[simp]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty  :=
  DTreeMap.isEmpty_keys

@[simp]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  DTreeMap.contains_keys

@[simp]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  DTreeMap.mem_keys

theorem distinct_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.distinct_keys

@[simp]
theorem map_prod_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  DTreeMap.Const.map_prod_fst_toList_eq_keys

@[simp]
theorem length_toList :
    (toList t).length = t.size :=
  DTreeMap.Const.length_toList

@[simp]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  DTreeMap.Const.isEmpty_toList

@[simp]
theorem mem_toList_iff_getElem?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t[k]? = some v :=
  DTreeMap.Const.mem_toList_iff_get?_eq_some

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some [TransCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ t[k]? = some v :=
  DTreeMap.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some

theorem getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] {k : α} {v : β} :
    t[k]? = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  DTreeMap.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some [TransCmp cmp] {k k' : α}
    {v : β} :
    t.toList.find? (fun a => cmp a.1 k = .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ t[k]? = some v :=
  DTreeMap.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  DTreeMap.Const.find?_toList_eq_none_iff_contains_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  DTreeMap.Const.find?_toList_eq_none_iff_not_mem

theorem distinct_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  DTreeMap.Const.distinct_keys_toList

end Std.TreeMap
