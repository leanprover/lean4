/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Lemmas
import Std.Data.TreeMap.Basic
import Std.Data.TreeMap.AdditionalOperations

/-!
# Tree map lemmas

This file contains lemmas about `Std.Data.TreeMap`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {γ : Type w} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

private theorem ext {t t' : TreeMap α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyc : (∅ : TreeMap α β cmp).isEmpty :=
  DTreeMap.isEmpty_emptyc

@[simp, grind =]
theorem isEmpty_insert [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).isEmpty = false :=
  DTreeMap.isEmpty_insert

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DTreeMap.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {k : α} : t.contains k ↔ k ∈ t :=
  DTreeMap.contains_iff_mem

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  DTreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  DTreeMap.mem_congr hab

@[simp, grind =]
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

theorem isEmpty_eq_false_of_contains [TransCmp cmp] {a : α} (hc : t.contains a = true) :
    t.isEmpty = false :=
  DTreeMap.isEmpty_eq_false_of_contains hc

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

@[simp, grind =]
theorem contains_insert [h : TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.contains_insert

@[simp, grind =]
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

@[simp, grind =]
theorem size_emptyc : (∅ : TreeMap α β cmp).size = 0 :=
  DTreeMap.size_emptyc

theorem isEmpty_eq_size_eq_zero :
    t.isEmpty = (t.size == 0) :=
  DTreeMap.isEmpty_eq_size_eq_zero

@[grind =] theorem size_insert [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  DTreeMap.size_insert

theorem size_le_size_insert [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insert k v).size :=
  DTreeMap.size_le_size_insert

theorem size_insert_le [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).size ≤ t.size + 1 :=
  DTreeMap.size_insert_le

@[simp, grind =]
theorem erase_emptyc {k : α} :
    (∅ : TreeMap α β cmp).erase k = ∅ :=
  ext <| DTreeMap.erase_emptyc

@[simp, grind =]
theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  DTreeMap.isEmpty_erase

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransCmp cmp] (k : α) :
    t.isEmpty = ((t.erase k).isEmpty && !(t.contains k)) :=
  DTreeMap.isEmpty_eq_isEmpty_erase_and_not_contains k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransCmp cmp] {k : α}
    (he : (t.erase k).isEmpty = false) :
    t.isEmpty = false :=
  DTreeMap.isEmpty_eq_false_of_isEmpty_erase_eq_false he

@[simp, grind =]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  DTreeMap.contains_erase

@[simp, grind =]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  DTreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  DTreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  DTreeMap.mem_of_mem_erase

@[grind =] theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  DTreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  DTreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  DTreeMap.size_le_size_erase

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsert k v).1 = t.contains k :=
  DTreeMap.containsThenInsert_fst

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| DTreeMap.containsThenInsert_snd

@[simp, grind =]
theorem containsThenInsertIfNew_fst [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  DTreeMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsertIfNew_snd [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.containsThenInsertIfNew_snd

@[simp, grind =] theorem get_eq_getElem {a : α} {h} : get t a h = t[a]'h := rfl
@[simp, grind =] theorem get?_eq_getElem? {a : α} : get? t a = t[a]? := rfl
@[simp, grind =] theorem get!_eq_getElem! [Inhabited β] {a : α} : get! t a = t[a]! := rfl

@[simp, grind =]
theorem getElem?_emptyc [TransCmp cmp] {a : α} :
    (∅ : TreeMap α β cmp)[a]? = none :=
  DTreeMap.Const.get?_emptyc (cmp := cmp) (a := a)

theorem getElem?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t[a]? = none :=
  DTreeMap.Const.get?_of_isEmpty

@[grind =]
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

@[simp]
theorem isSome_getElem?_eq_contains [TransCmp cmp] {a : α} :
    t[a]?.isSome = t.contains a :=
  contains_eq_isSome_getElem?.symm

theorem mem_iff_isSome_getElem? [TransCmp cmp] {a : α} :
    a ∈ t ↔ t[a]?.isSome :=
  DTreeMap.Const.mem_iff_isSome_get?

@[simp]
theorem isSome_getElem?_iff_mem [TransCmp cmp] {a : α} :
    t[a]?.isSome ↔ a ∈ t :=
  mem_iff_isSome_getElem?.symm

theorem getElem?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t[a]? = none :=
  DTreeMap.Const.get?_eq_none_of_contains_eq_false

theorem getElem?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t[a]? = none :=
  DTreeMap.Const.get?_eq_none

@[grind =] theorem getElem?_erase [TransCmp cmp] {k a : α} :
    (t.erase k)[a]? = if cmp k a = .eq then none else t[a]? :=
  DTreeMap.Const.get?_erase

@[simp]
theorem getElem?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k)[k]? = none :=
  DTreeMap.Const.get?_erase_self

theorem getElem?_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) :
    t[a]? = t[b]? :=
  DTreeMap.Const.get?_congr hab

@[grind =] theorem getElem_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insert k v)[a]'h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (mem_of_mem_insert h₁ h₂) :=
  DTreeMap.Const.get_insert

@[simp]
theorem getElem_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v)[k]'mem_insert_self = v :=
  DTreeMap.Const.get_insert_self

@[simp, grind =]
theorem getElem_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k)[a]'h' = t[a]'(mem_of_mem_erase h') :=
  DTreeMap.Const.get_erase

theorem getElem?_eq_some_getElem [TransCmp cmp] {a : α} {h} :
    t[a]? = some (t[a]'h) :=
  DTreeMap.Const.get?_eq_some_get

theorem getElem_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((mem_congr hab).mp h') :=
  DTreeMap.Const.get_congr hab

@[simp, grind =]
theorem getElem!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    (∅ : TreeMap α β cmp)[a]! = default :=
  DTreeMap.Const.get!_emptyc (cmp := cmp) (a := a)

theorem getElem!_of_isEmpty [TransCmp cmp] [Inhabited β] {a : α} :
    t.isEmpty = true → t[a]! = default :=
  DTreeMap.Const.get!_of_isEmpty

@[grind =] theorem getElem!_insert [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
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

@[grind =] theorem getElem!_erase [TransCmp cmp] [Inhabited β] {k a : α} :
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

theorem getElem!_eq_get!_getElem? [TransCmp cmp] [Inhabited β] {a : α} :
    t[a]! = t[a]?.get! :=
  DTreeMap.Const.get!_eq_get!_get?

@[deprecated getElem!_eq_get!_getElem? (since := "2025-03-19")]
theorem getElem!_eq_getElem!_getElem? [TransCmp cmp] [Inhabited β] {a : α} :
    t[a]! = t[a]?.get! :=
  DTreeMap.Const.get!_eq_get!_get?

theorem getElem_eq_getElem! [TransCmp cmp] [Inhabited β] {a : α} {h} :
    t[a]'h = t[a]! :=
  DTreeMap.Const.get_eq_get!

theorem getElem!_congr [TransCmp cmp] [Inhabited β] {a b : α}
    (hab : cmp a b = .eq) : t[a]! = t[b]! :=
  DTreeMap.Const.get!_congr hab

@[simp, grind =]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : TreeMap α β cmp) a fallback = fallback :=
  DTreeMap.Const.getD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  DTreeMap.Const.getD_of_isEmpty

@[grind =] theorem getD_insert [TransCmp cmp] {k a : α} {fallback v : β} :
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

@[grind =] theorem getD_erase [TransCmp cmp] {k a : α} {fallback : β} :
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

@[simp, grind =]
theorem getKey?_emptyc {a : α} : (∅ : TreeMap α β cmp).getKey? a = none :=
  DTreeMap.getKey?_emptyc

theorem getKey?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  DTreeMap.getKey?_of_isEmpty

@[grind =] theorem getKey?_insert [TransCmp cmp] {a k : α} {v : β} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  DTreeMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).getKey? k = some k :=
  DTreeMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [TransCmp cmp] {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  DTreeMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_getKey?_eq_contains [TransCmp cmp] {a : α} :
    (t.getKey? a).isSome = t.contains a :=
  contains_eq_isSome_getKey?.symm

theorem mem_iff_isSome_getKey? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  DTreeMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [TransCmp cmp] {a : α} :
    (t.getKey? a).isSome ↔ a ∈ t :=
  mem_iff_isSome_getKey?.symm

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.getKey? a = none :=
  DTreeMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  DTreeMap.getKey?_eq_none

@[grind =] theorem getKey?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  DTreeMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).getKey? k = none :=
  DTreeMap.getKey?_erase_self

theorem compare_getKey?_self [TransCmp cmp] {k : α} :
    (t.getKey? k).all (cmp · k = .eq) :=
  DTreeMap.compare_getKey?_self

theorem getKey?_congr [TransCmp cmp] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey? k = t.getKey? k' :=
  DTreeMap.getKey?_congr h'

theorem getKey?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h' : t.contains k) :
    t.getKey? k = some k :=
  DTreeMap.getKey?_eq_some_of_contains h'

theorem getKey?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.getKey? k = some k :=
  DTreeMap.getKey?_eq_some_of_contains h'

@[grind =] theorem getKey_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h₁ h₂) :=
  DTreeMap.getKey_insert

@[simp]
theorem getKey_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).getKey k mem_insert_self = k :=
  DTreeMap.getKey_insert_self

@[simp, grind =]
theorem getKey_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h') :=
  DTreeMap.getKey_erase

theorem getKey?_eq_some_getKey [TransCmp cmp] {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  DTreeMap.getKey?_eq_some_getKey

theorem compare_getKey_self [TransCmp cmp] {k : α} (h' : k ∈ t) :
    cmp (t.getKey k h') k = .eq :=
  DTreeMap.compare_getKey_self h'

theorem getKey_congr [TransCmp cmp] {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h').mp h₁) :=
  DTreeMap.getKey_congr h' h₁

@[simp, grind =]
theorem getKey_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.getKey k h' = k :=
  DTreeMap.getKey_eq h'

@[simp, grind =]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : TreeMap α β cmp).getKey! a = default :=
  DTreeMap.getKey!_emptyc

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  DTreeMap.getKey!_of_isEmpty

@[grind =] theorem getKey!_insert [TransCmp cmp] [Inhabited α] {k a : α}
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

@[grind =] theorem getKey!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
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

theorem getKey!_congr [TransCmp cmp] [Inhabited α] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey! k = t.getKey! k' :=
  DTreeMap.getKey!_congr h'

theorem getKey!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    (h' : t.contains k) :
    t.getKey! k = k :=
  DTreeMap.getKey!_eq_of_contains h'

theorem getKey!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α} (h' : k ∈ t) :
    t.getKey! k = k :=
  DTreeMap.getKey!_eq_of_mem h'

@[simp, grind =]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : TreeMap α β cmp).getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_emptyc

theorem getKeyD_of_isEmpty [TransCmp cmp] {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_of_isEmpty

@[grind =] theorem getKeyD_insert [TransCmp cmp] {k a fallback : α} {v : β} :
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

@[grind =] theorem getKeyD_erase [TransCmp cmp] {k a fallback : α} :
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

theorem getKeyD_congr [TransCmp cmp] {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getKeyD k fallback = t.getKeyD k' fallback :=
  DTreeMap.getKeyD_congr h'

theorem getKeyD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α}
    (h' : t.contains k) :
    t.getKeyD k fallback = k :=
  DTreeMap.getKeyD_eq_of_contains h'

theorem getKeyD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : k ∈ t) :
    t.getKeyD k fallback = k :=
  DTreeMap.getKeyD_eq_of_contains h'

@[simp, grind =]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).isEmpty = false :=
  DTreeMap.isEmpty_insertIfNew

@[simp, grind =]
theorem contains_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  DTreeMap.contains_insertIfNew

@[simp, grind =]
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

@[grind =] theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  DTreeMap.size_insertIfNew

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  DTreeMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  DTreeMap.size_insertIfNew_le

@[grind =] theorem getElem?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]? =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else t[a]? :=
  DTreeMap.Const.get?_insertIfNew

@[grind =] theorem getElem_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v)[a]'h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]'(mem_of_mem_insertIfNew' h₁ h₂) :=
  DTreeMap.Const.get_insertIfNew

@[grind =] theorem getElem!_insertIfNew [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]! = if cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]! :=
  DTreeMap.Const.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  DTreeMap.Const.getD_insertIfNew

@[grind =] theorem getKey?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  DTreeMap.getKey?_insertIfNew

@[grind =] theorem getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂) :=
  DTreeMap.getKey_insertIfNew

@[grind =] theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  DTreeMap.getKey!_insertIfNew

@[grind =] theorem getKeyD_insertIfNew [TransCmp cmp] {k a fallback : α}
    {v : β} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  DTreeMap.getKeyD_insertIfNew

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  DTreeMap.Const.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| DTreeMap.Const.getThenInsertIfNew?_snd

instance [TransCmp cmp] : LawfulGetElem (TreeMap α β cmp) α β (fun m a => a ∈ m) where
  getElem?_def m a _ := by
    split
    · exact getElem?_eq_some_getElem
    · exact getElem?_eq_none ‹_›
  getElem!_def m a := by
    rw [getElem!_eq_get!_getElem?]
    split <;> simp_all

theorem getElem?_eq_some_iff [TransCmp cmp] {k : α} {v : β} :
    t[k]? = some v ↔ ∃ h : k ∈ t, t[k] = v :=
  _root_.getElem?_eq_some_iff

@[simp, grind =]
theorem length_keys [TransCmp cmp] :
    t.keys.length = t.size :=
  DTreeMap.length_keys

@[simp, grind =]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty :=
  DTreeMap.isEmpty_keys

@[simp, grind =]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  DTreeMap.contains_keys

@[simp, grind =]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  DTreeMap.mem_keys

theorem distinct_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.distinct_keys

theorem ordered_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => cmp a b = .lt) :=
  DTreeMap.ordered_keys

@[simp, grind _=_]
theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  DTreeMap.Const.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList :
    (toList t).length = t.size :=
  DTreeMap.Const.length_toList

@[simp, grind =]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  DTreeMap.Const.isEmpty_toList

@[simp, grind =]
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
    t.toList.find? (cmp ·.1 k == .eq) = some ⟨k', v⟩ ↔
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

theorem ordered_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  DTreeMap.Const.ordered_keys_toList

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init :=
  DTreeMap.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init :=
  DTreeMap.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : α → β → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init :=
  DTreeMap.Const.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList {f : α → β → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init :=
  DTreeMap.Const.foldr_eq_foldr_toList

@[simp, grind =]
theorem forM_eq_forM [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    ForM.forM t f = ForM.forM t.toList f :=
  DTreeMap.Const.forMUncurried_eq_forM_toList (f := f)

@[simp, grind =]
theorem forIn_eq_forIn [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init (fun a d => f a.1 a.2 d) := rfl

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α × β → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  DTreeMap.Const.forInUncurried_eq_forIn_toList

theorem foldlM_eq_foldlM_keys [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init :=
  DTreeMap.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init :=
  DTreeMap.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init :=
  DTreeMap.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init :=
  DTreeMap.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t (fun a => f a.1) = t.keys.forM f :=
  DTreeMap.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init (fun a d => f a.1 d) = ForIn.forIn t.keys init f :=
  DTreeMap.forIn_eq_forIn_keys

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
  ext <| DTreeMap.Const.insertMany_cons

@[grind _=_] theorem insertMany_append {l₁ l₂ : List (α × β)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  DTreeMap.Const.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Prod.fst).contains k :=
  DTreeMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    k ∈ t.insertMany l → (l.map Prod.fst).contains k = false → k ∈ t :=
  DTreeMap.Const.mem_of_mem_insertMany_list

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k :=
  DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKey? k' = some k :=
  DTreeMap.Const.getKey?_insertMany_list_of_mem k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h' contains_eq_false) :=
  DTreeMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k :=
  DTreeMap.Const.getKey_insertMany_list_of_mem k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k :=
  DTreeMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKey! k' = k :=
  DTreeMap.Const.getKey!_insertMany_list_of_mem k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback :=
  DTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKeyD k' fallback = k :=
  DTreeMap.Const.getKeyD_insertMany_list_of_mem k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length :=
  DTreeMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    t.size ≤ (t.insertMany l).size :=
  DTreeMap.Const.size_le_size_insertMany_list

grind_pattern size_le_size_insertMany_list => (t.insertMany l).size

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List (α × β)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  DTreeMap.Const.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (t.insertMany l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  DTreeMap.Const.isEmpty_insertMany_list

theorem getElem?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l)[k]? = t[k]? :=
  DTreeMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem?_insertMany_list_of_mem [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l)[k']? = some v :=
  DTreeMap.Const.get?_insertMany_list_of_mem k_eq distinct mem

@[grind =] theorem getElem?_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    (t.insertMany l)[k]? =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).or (t[k]?) :=
  DTreeMap.Const.get?_insertMany_list

theorem getElem_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains : (l.map Prod.fst).contains k = false)
    {h'} :
    (t.insertMany l)[k]'h' =
    t.get k (mem_of_mem_insertMany_list h' contains) :=
  DTreeMap.Const.get_insertMany_list_of_contains_eq_false contains

theorem getElem_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l)[k']'h' = v :=
  DTreeMap.Const.get_insertMany_list_of_mem k_eq distinct mem

theorem getElem!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l)[k]! = t.get! k :=
  DTreeMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem!_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l)[k']! = v :=
  DTreeMap.Const.get!_insertMany_list_of_mem k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback :=
  DTreeMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = v :=
  DTreeMap.Const.getD_insertMany_list_of_mem k_eq distinct mem

section Unit

variable {t : TreeMap α Unit cmp}

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
  ext <| DTreeMap.Const.insertManyIfNewUnit_cons

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) :=
  DTreeMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k :=
  DTreeMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t :=
  DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit t l) k = none :=
  DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit t l) k' = some k :=
  DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} (mem : k ∈ t) :
    getKey? (insertManyIfNewUnit t l) k = getKey? t k :=
  DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains :=
  DTreeMap.Const.getKey_insertManyIfNewUnit_list_of_mem contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} (not_mem : ¬ k ∈ t)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey (insertManyIfNewUnit t l) k' h' = k :=
  DTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit t l) k = default :=
  DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit t l) k' = k :=
  DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ t) :
    getKey! (insertManyIfNewUnit t l) k = getKey! t k :=
  DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit t l) k fallback = fallback :=
  DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit t l) k' fallback = k :=
  DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k fallback : α} (mem : k ∈ t) :
    getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback :=
  DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length :=
  DTreeMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp]
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size :=
  DTreeMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp]
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length :=
  DTreeMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  DTreeMap.Const.isEmpty_insertManyIfNewUnit_list

@[simp]
theorem getElem?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l)[k]? = if k ∈ t ∨ l.contains k then some () else none :=
  DTreeMap.Const.get?_insertManyIfNewUnit_list

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
    ofList [⟨k, v⟩] cmp = (∅ : TreeMap α β cmp).insert k v := by
  rfl

@[grind _=_] theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : TreeMap α β cmp).insert k v) tl :=
  ext DTreeMap.Const.ofList_cons

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l cmp = insertMany (∅ : TreeMap α β cmp) l := rfl

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  DTreeMap.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Prod.fst).contains k :=
  DTreeMap.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp)[k]? = none :=
  DTreeMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp)[k']? = some v :=
  DTreeMap.Const.get?_ofList_of_mem k_eq distinct mem

theorem getElem_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l cmp)[k']'h = v :=
  DTreeMap.Const.get_ofList_of_mem k_eq distinct mem

theorem getElem!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp)[k]! = default :=
  DTreeMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp)[k']! = v :=
  DTreeMap.Const.get!_ofList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  DTreeMap.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l cmp) k' fallback = v :=
  DTreeMap.Const.getD_ofList_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  DTreeMap.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey? k' = some k :=
  DTreeMap.Const.getKey?_ofList_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  DTreeMap.Const.getKey_ofList_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  DTreeMap.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey! k' = k :=
  DTreeMap.Const.getKey!_ofList_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  DTreeMap.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  DTreeMap.Const.getKeyD_ofList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  DTreeMap.Const.size_ofList distinct

theorem size_ofList_le [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).size ≤ l.length :=
  DTreeMap.Const.size_ofList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp, grind =]
theorem isEmpty_ofList [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  DTreeMap.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) cmp =
      (∅ : TreeMap α Unit cmp) :=
  rfl

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] cmp = (∅ : TreeMap α Unit cmp).insertIfNew k () :=
  rfl

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) cmp =
      insertManyIfNewUnit ((∅ : TreeMap α Unit cmp).insertIfNew hd ()) tl :=
  ext DTreeMap.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp).contains k = l.contains k :=
  DTreeMap.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ unitOfList l cmp ↔ l.contains k := by
  simp [← contains_iff_mem]

theorem getKey?_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l cmp) k = none :=
  DTreeMap.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (unitOfList l cmp) k' = some k :=
  DTreeMap.Const.getKey?_unitOfList_of_mem k_eq distinct mem

theorem getKey_unitOfList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l cmp) k' h' = k :=
  DTreeMap.Const.getKey_unitOfList_of_mem k_eq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l cmp) k = default :=
  DTreeMap.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKey! (unitOfList l cmp) k' = k :=
  DTreeMap.Const.getKey!_unitOfList_of_mem k_eq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l cmp) k fallback = fallback :=
  DTreeMap.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKeyD (unitOfList l cmp) k' fallback = k :=
  DTreeMap.Const.getKeyD_unitOfList_of_mem k_eq distinct mem

theorem size_unitOfList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (unitOfList l cmp).size = l.length :=
  DTreeMap.Const.size_unitOfList distinct

theorem size_unitOfList_le [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).size ≤ l.length :=
  DTreeMap.Const.size_unitOfList_le

@[simp]
theorem isEmpty_unitOfList [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).isEmpty = l.isEmpty :=
  DTreeMap.Const.isEmpty_unitOfList

@[simp]
theorem getElem?_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp)[k]? = if l.contains k then some () else none :=
  DTreeMap.Const.get?_unitOfList

@[simp]
theorem getElem_unitOfList {l : List α} {k : α} {h} :
    (unitOfList l cmp)[k]'h = () :=
  DTreeMap.Const.get_unitOfList

@[simp]
theorem getElem!_unitOfList {l : List α} {k : α} :
    (unitOfList l cmp)[k]! = () :=
  DTreeMap.Const.get!_unitOfList

@[simp]
theorem getD_unitOfList {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l cmp) k fallback = () :=
  DTreeMap.Const.getD_unitOfList

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [TransCmp cmp] {k : α}
    {f : Option β → Option β} :
    (alter t k f).isEmpty = ((t.erase k).isEmpty && (f t[k]?).isNone) :=
   DTreeMap.Const.isEmpty_alter_eq_isEmpty_erase

@[simp, grind =]
theorem isEmpty_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f t[k]?).isNone) :=
  DTreeMap.Const.isEmpty_alter

@[grind =]
theorem contains_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).contains k' =
      if cmp k k' = .eq then (f t[k]?).isSome else t.contains k' :=
  DTreeMap.Const.contains_alter

@[grind =]
theorem mem_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    k' ∈ alter t k f ↔
      if cmp k k' = .eq then (f t[k]?).isSome = true else k' ∈ t :=
  DTreeMap.Const.mem_alter

theorem mem_alter_of_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : cmp k k' = .eq) :
    k' ∈ alter t k f ↔ (f t[k]?).isSome :=
  DTreeMap.Const.mem_alter_of_compare_eq he

@[simp]
theorem contains_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).contains k = (f t[k]?).isSome :=
  DTreeMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    k ∈ alter t k f ↔ (f t[k]?).isSome :=
  DTreeMap.Const.mem_alter_self

theorem contains_alter_of_not_compare_eq [TransCmp cmp] {k k' : α}
    {f : Option β → Option β} (he : ¬ cmp k k' = .eq) :
    (alter t k f).contains k' = t.contains k' :=
  DTreeMap.Const.contains_alter_of_not_compare_eq he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : ¬ cmp k k' = .eq) :
    k' ∈ alter t k f ↔ k' ∈ t :=
  DTreeMap.Const.mem_alter_of_not_compare_eq he

@[grind =]
theorem size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size =
      if k ∈ t ∧ (f t[k]?).isNone then
        t.size - 1
      else if k ∉ t ∧ (f t[k]?).isSome then
        t.size + 1
      else
        t.size :=
  DTreeMap.Const.size_alter

theorem size_alter_eq_add_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f t[k]?).isSome) :
    (alter t k f).size = t.size + 1 :=
  DTreeMap.Const.size_alter_eq_add_one h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f t[k]?).isNone) :
    (alter t k f).size = t.size - 1 :=
  DTreeMap.Const.size_alter_eq_sub_one h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f t[k]?).isNone) :
    (alter t k f).size = t.size :=
  DTreeMap.Const.size_alter_eq_self_of_not_mem h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f t[k]?).isSome) :
    (alter t k f).size = t.size :=
  DTreeMap.Const.size_alter_eq_self_of_mem h₁ h₂

theorem size_alter_le_size [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size ≤ t.size + 1 :=
  DTreeMap.Const.size_alter_le_size

theorem size_le_size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter t k f).size :=
  DTreeMap.Const.size_le_size_alter

@[grind =]
theorem getElem?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f)[k']? =
      if cmp k k' = .eq then
        f t[k]?
      else
        t[k']? :=
  DTreeMap.Const.get?_alter

@[simp]
theorem getElem?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f)[k]? = f t[k]? :=
  DTreeMap.Const.get?_alter_self

@[grind =]
theorem getElem_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter t k f)} :
    (alter t k f)[k']'hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f t[k]?).isSome := mem_alter_of_compare_eq heq |>.mp hc
        f t[k]? |>.get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t[k']'h' :=
  DTreeMap.Const.get_alter

@[simp]
theorem getElem_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    haveI h' : (f t[k]?).isSome := mem_alter_self.mp hc
    (alter t k f)[k]'hc = (f t[k]?).get h' :=
  DTreeMap.Const.get_alter_self

@[grind =]
theorem getElem!_alter [TransCmp cmp] {k k' : α} [Inhabited β] {f : Option β → Option β} :
    (alter t k f)[k']! =
      if cmp k k' = .eq then
        f t[k]? |>.get!
      else
        t[k']! :=
  DTreeMap.Const.get!_alter

@[simp]
theorem getElem!_alter_self [TransCmp cmp] {k : α} [Inhabited β] {f : Option β → Option β} :
    (alter t k f)[k]! = (f t[k]?).get! :=
  DTreeMap.Const.get!_alter_self

@[grind =]
theorem getD_alter [TransCmp cmp] {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter t k f) k' fallback =
      if cmp k k' = .eq then
        f t[k]? |>.getD fallback
      else
        getD t k' fallback :=
  DTreeMap.Const.getD_alter

@[simp]
theorem getD_alter_self [TransCmp cmp] {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter t k f) k fallback = (f t[k]?).getD fallback :=
  DTreeMap.Const.getD_alter_self

@[grind =]
theorem getKey?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey? k' =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then some k else none
      else
        t.getKey? k' :=
  DTreeMap.Const.getKey?_alter

theorem getKey?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).getKey? k = if (f t[k]?).isSome then some k else none :=
  DTreeMap.Const.getKey?_alter_self

@[grind =]
theorem getKey!_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey! k' =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then k else default
      else
        t.getKey! k' :=
  DTreeMap.Const.getKey!_alter

theorem getKey!_alter_self [TransCmp cmp] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (alter t k f).getKey! k = if (f t[k]?).isSome then k else default :=
  DTreeMap.Const.getKey!_alter_self

@[grind =]
theorem getKey_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter t k f} :
    (alter t k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t.getKey k' h' :=
  DTreeMap.Const.getKey_alter

@[simp]
theorem getKey_alter_self [TransCmp cmp] [Inhabited α] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    (alter t k f).getKey k hc = k :=
  DTreeMap.Const.getKey_alter_self

@[grind =]
theorem getKeyD_alter [TransCmp cmp] {k k' fallback : α} {f : Option β → Option β} :
    (alter t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  DTreeMap.Const.getKeyD_alter

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [Inhabited α] {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter t k f).getKeyD k fallback = if (f t[k]?).isSome then k else fallback :=
  DTreeMap.Const.getKeyD_alter_self

end Alter

section Modify

@[simp, grind =]
theorem isEmpty_modify [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f).isEmpty = t.isEmpty :=
  DTreeMap.Const.isEmpty_modify

@[grind =]
theorem contains_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    (modify t k f).contains k' = t.contains k' :=
  DTreeMap.Const.contains_modify

@[grind =]
theorem mem_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    k' ∈ modify t k f ↔ k' ∈ t :=
  DTreeMap.Const.mem_modify

@[grind =]
theorem size_modify [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f).size = t.size :=
  DTreeMap.Const.size_modify

@[grind =]
theorem getElem?_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    (modify t k f)[k']? =
      if cmp k k' = .eq then
        t[k]?.map f
      else
        t[k']? :=
  DTreeMap.Const.get?_modify

@[simp]
theorem getElem?_modify_self [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f)[k]? = t[k]?.map f :=
  DTreeMap.Const.get?_modify_self

@[grind =]
theorem getElem_modify [TransCmp cmp] {k k' : α} {f : β → β} {hc : k' ∈ modify t k f} :
    (modify t k f)[k']'hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr heq |>.mpr <| mem_modify.mp hc
        f (t[k]'h')
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t[k']'h' :=
  DTreeMap.Const.get_modify

@[simp]
theorem getElem_modify_self [TransCmp cmp] {k : α} {f : β → β} {hc : k ∈ modify t k f} :
    haveI h' : k ∈ t := mem_modify.mp hc
    (modify t k f)[k]'hc = f (t[k]'h') :=
  DTreeMap.Const.get_modify_self

@[grind =]
theorem getElem!_modify [TransCmp cmp] {k k' : α} [hi : Inhabited β] {f : β → β} :
    (modify t k f)[k']! =
      if cmp k k' = .eq then
        t[k]? |>.map f |>.get!
      else
        t[k']! :=
  DTreeMap.Const.get!_modify

@[simp]
theorem getElem!_modify_self [TransCmp cmp] {k : α} [Inhabited β] {f : β → β} :
    (modify t k f)[k]! = (t[k]?.map f).get! :=
  DTreeMap.Const.get!_modify_self

@[grind =]
theorem getD_modify [TransCmp cmp] {k k' : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k' fallback =
      if cmp k k' = .eq then
        t[k]?.map f |>.getD fallback
      else
        getD t k' fallback :=
  DTreeMap.Const.getD_modify

@[simp]
theorem getD_modify_self [TransCmp cmp] {k : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k fallback = (t[k]?.map f).getD fallback :=
  DTreeMap.Const.getD_modify_self

@[grind =]
theorem getKey?_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    (modify t k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  DTreeMap.Const.getKey?_modify

theorem getKey?_modify_self [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f).getKey? k = if k ∈ t then some k else none :=
  DTreeMap.Const.getKey?_modify_self

@[grind =]
theorem getKey!_modify [TransCmp cmp] [Inhabited α] {k k' : α} {f : β → β} :
    (modify t k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  DTreeMap.Const.getKey!_modify

theorem getKey!_modify_self [TransCmp cmp] [Inhabited α] {k : α} {f : β → β} :
    (modify t k f).getKey! k = if k ∈ t then k else default :=
  DTreeMap.Const.getKey!_modify_self

@[grind =]
theorem getKey_modify [TransCmp cmp] [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify t k f} :
    (modify t k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.getKey k' h' :=
  DTreeMap.Const.getKey_modify

@[simp]
theorem getKey_modify_self [TransCmp cmp] [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify t k f} : (modify t k f).getKey k hc = k :=
  DTreeMap.Const.getKey_modify_self

@[grind =]
theorem getKeyD_modify [TransCmp cmp] {k k' fallback : α} {f : β → β} :
    (modify t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  DTreeMap.Const.getKeyD_modify

theorem getKeyD_modify_self [TransCmp cmp] [Inhabited α] {k fallback : α} {f : β → β} :
    (modify t k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  DTreeMap.Const.getKeyD_modify_self

end Modify

section Min

@[simp, grind =]
theorem minKey?_emptyc :
    (∅ : TreeMap α β cmp).minKey? = none :=
  DTreeMap.minKey?_emptyc

theorem minKey?_of_isEmpty [TransCmp cmp] :
    (he : t.isEmpty) → t.minKey? = none :=
  DTreeMap.minKey?_of_isEmpty

@[simp, grind =]
theorem minKey?_eq_none_iff [TransCmp cmp] :
    t.minKey? = none ↔ t.isEmpty :=
  DTreeMap.minKey?_eq_none_iff

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.minKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem minKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.minKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_minKey?_eq_isEmpty [TransCmp cmp] :
    t.minKey?.isNone = t.isEmpty :=
  DTreeMap.isNone_minKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_minKey?_eq_not_isEmpty [TransCmp cmp] :
    t.minKey?.isSome = !t.isEmpty :=
  DTreeMap.isSome_minKey?_eq_not_isEmpty

theorem isSome_minKey?_iff_isEmpty_eq_false [TransCmp cmp] :
    t.minKey?.isSome ↔ t.isEmpty = false :=
  DTreeMap.isSome_minKey?_iff_isEmpty_eq_false

@[grind =] theorem minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  DTreeMap.minKey?_insert

@[grind =] theorem isSome_minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey?.isSome :=
  DTreeMap.isSome_minKey?_insert

theorem minKey?_insert_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v |>.minKey? |>.get isSome_minKey?_insert) = kmi) →
    cmp kmi km |>.isLE :=
  DTreeMap.minKey?_insert_le_minKey?

theorem minKey?_insert_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.minKey?.get isSome_minKey?_insert) = kmi) →
    cmp kmi k |>.isLE :=
  DTreeMap.minKey?_insert_le_self

theorem contains_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) →
    t.contains km :=
  DTreeMap.contains_minKey?

theorem isSome_minKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.minKey?.isSome :=
  DTreeMap.isSome_minKey?_of_contains

theorem isSome_minKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.minKey?.isSome :=
  DTreeMap.isSome_minKey?_of_mem

theorem minKey?_le_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains hc) = km) →
    cmp km k |>.isLE :=
  DTreeMap.minKey?_le_of_contains

theorem minKey?_le_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem hc) = km) →
    cmp km k |>.isLE :=
  DTreeMap.minKey?_le_of_mem

theorem le_minKey? [TransCmp cmp] {k} :
    (∀ k', t.minKey? = some k' → (cmp k k').isLE) ↔
      (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.le_minKey?

theorem getKey?_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km :=
  DTreeMap.getKey?_minKey?

theorem getKey_minKey? [TransCmp cmp] {km hc} :
    (hkm : t.minKey?.get (isSome_minKey?_of_contains hc) = km) → t.getKey km hc = km :=
  DTreeMap.getKey_minKey?

theorem getKey!_minKey? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.minKey? = some km) → t.getKey! km = km :=
  DTreeMap.getKey!_minKey?

theorem getKeyD_minKey? [TransCmp cmp] {km fallback} :
    (hkm : t.minKey? = some km) → t.getKeyD km fallback = km :=
  DTreeMap.getKeyD_minKey?

@[simp]
theorem minKey?_bind_getKey? [TransCmp cmp] :
    t.minKey?.bind t.getKey? = t.minKey? :=
  DTreeMap.minKey?_bind_getKey?

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (t.erase k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq :=
  DTreeMap.minKey?_erase_eq_iff_not_compare_eq_minKey?

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.minKey?) = t.minKey? :=
  DTreeMap.minKey?_erase_eq_of_not_compare_eq_minKey?

theorem isSome_minKey?_of_isSome_minKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.minKey?.isSome) →
    t.minKey?.isSome :=
  DTreeMap.isSome_minKey?_of_isSome_minKey?_erase

theorem minKey?_le_minKey?_erase [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  DTreeMap.minKey?_le_minKey?_erase

@[grind =] theorem minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  DTreeMap.minKey?_insertIfNew

@[grind =] theorem isSome_minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey?.isSome :=
  DTreeMap.isSome_minKey?_insertIfNew

theorem minKey?_insertIfNew_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.minKey? |>.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi km |>.isLE :=
  DTreeMap.minKey?_insertIfNew_le_minKey?

theorem minKey?_insertIfNew_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.minKey?.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi k |>.isLE :=
  DTreeMap.minKey?_insertIfNew_le_self

@[grind =_] theorem minKey?_eq_head?_keys [TransCmp cmp] :
    t.minKey? = t.keys.head? :=
  DTreeMap.minKey?_eq_head?_keys

theorem minKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).minKey? = t.minKey?.map fun km => if cmp km k = .eq then k else km :=
  DTreeMap.Const.minKey?_modify

@[simp, grind =]
theorem minKey?_modify_eq_minKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).minKey? = t.minKey? :=
  DTreeMap.Const.minKey?_modify_eq_minKey?

@[grind =] theorem isSome_minKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).minKey?.isSome = !t.isEmpty :=
  DTreeMap.Const.isSome_minKey?_modify

theorem isSome_minKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (t.modify k f).minKey?.isSome = t.minKey?.isSome :=
  DTreeMap.Const.isSome_minKey?_modify_eq_isSome

theorem compare_minKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (t.modify k f |>.minKey? |>.get <|
        isSome_minKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  DTreeMap.Const.compare_minKey?_modify_eq

theorem minKey?_alter_eq_self [TransCmp cmp] {k f} :
    (t.alter k f).minKey? = some k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Const.minKey?_alter_eq_self

theorem minKey_eq_get_minKey? [TransCmp cmp] {he} :
    t.minKey he = t.minKey?.get (isSome_minKey?_iff_isEmpty_eq_false.mpr he) :=
  DTreeMap.minKey_eq_get_minKey?

theorem minKey?_eq_some_minKey [TransCmp cmp] {he} :
    t.minKey? = some (t.minKey he) :=
  DTreeMap.minKey?_eq_some_minKey

theorem minKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.minKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.minKey_eq_iff_getKey?_eq_self_and_forall

theorem minKey_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.minKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.minKey_eq_iff_mem_and_forall

@[grind =] theorem minKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey isEmpty_insert =
      t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k' :=
  DTreeMap.minKey_insert

theorem minKey_insert_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insert k v |>.minKey isEmpty_insert) (t.minKey he) |>.isLE :=
  DTreeMap.minKey_insert_le_minKey

theorem minKey_insert_le_self [TransCmp cmp] {k v} :
    cmp (t.insert k v |>.minKey isEmpty_insert) k |>.isLE :=
  DTreeMap.minKey_insert_le_self

@[grind =] theorem contains_minKey [TransCmp cmp] {he} :
    t.contains (t.minKey he) :=
  DTreeMap.contains_minKey

@[grind] theorem minKey_mem [TransCmp cmp] {he} :
    t.minKey he ∈ t :=
  DTreeMap.minKey_mem

theorem minKey_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp (t.minKey <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) k |>.isLE :=
  DTreeMap.minKey_le_of_contains hc

theorem minKey_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp (t.minKey <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) k |>.isLE :=
  DTreeMap.minKey_le_of_mem hc

theorem le_minKey [TransCmp cmp] {k he} :
    (cmp k (t.minKey he)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.le_minKey

@[simp, grind =]
theorem getKey?_minKey [TransCmp cmp] {he} :
    t.getKey? (t.minKey he) = some (t.minKey he) :=
  DTreeMap.getKey?_minKey

@[simp, grind =]
theorem getKey_minKey [TransCmp cmp] {he hc} :
    t.getKey (t.minKey he) hc = t.minKey he :=
  DTreeMap.getKey_minKey

@[simp, grind =]
theorem getKey!_minKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.minKey he) = t.minKey he :=
  DTreeMap.getKey!_minKey

@[simp, grind =]
theorem getKeyD_minKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.minKey he) fallback = t.minKey he :=
  DTreeMap.getKeyD_minKey

@[simp]
theorem minKey_erase_eq_iff_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (t.erase k |>.minKey he) =
        t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he) ↔
      ¬ cmp k (t.minKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) = .eq :=
  DTreeMap.minKey_erase_eq_iff_not_compare_eq_minKey

theorem minKey_erase_eq_of_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he)) = .eq) →
    (t.erase k |>.minKey he) =
      t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he) :=
  DTreeMap.minKey_erase_eq_of_not_compare_eq_minKey

theorem minKey_le_minKey_erase [TransCmp cmp] {k he} :
    cmp (t.minKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false he)
      (t.erase k |>.minKey he) |>.isLE :=
  DTreeMap.minKey_le_minKey_erase

@[grind =] theorem minKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey isEmpty_insertIfNew =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.minKey_insertIfNew

theorem minKey_insertIfNew_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insertIfNew k v |>.minKey isEmpty_insertIfNew)
      (t.minKey he) |>.isLE :=
  DTreeMap.minKey_insertIfNew_le_minKey (t := t.inner) (he := he)

theorem minKey_insertIfNew_le_self [TransCmp cmp] {k v} :
    cmp (t.insertIfNew k v |>.minKey <| isEmpty_insertIfNew) k |>.isLE :=
  DTreeMap.minKey_insertIfNew_le_self

@[grind =_] theorem minKey_eq_head_keys [TransCmp cmp] {he} :
    t.minKey he = t.keys.head (List.isEmpty_eq_false_iff.mp <| isEmpty_keys ▸ he) :=
  DTreeMap.minKey_eq_head_keys

theorem minKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).minKey he =
      if cmp (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) k = .eq then
        k
      else
        (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) :=
  DTreeMap.Const.minKey_modify

@[simp, grind =]
theorem minKey_modify_eq_minKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).minKey he = t.minKey (cast (congrArg (· = false) isEmpty_modify) he) :=
  DTreeMap.Const.minKey_modify_eq_minKey

theorem compare_minKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.minKey he)
      (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) = .eq :=
  DTreeMap.Const.compare_minKey_modify_eq

@[simp]
theorem ordCompare_minKey_modify_eq [Ord α] [TransOrd α] {t : TreeMap α β} {k f he} :
    compare (modify t k f |>.minKey he)
      (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) = .eq :=
  compare_minKey_modify_eq

theorem minKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).minKey he = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Const.minKey_alter_eq_self

theorem minKey?_eq_some_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.minKey? = some t.minKey! :=
  DTreeMap.minKey?_eq_some_minKey! he

theorem minKey_eq_minKey! [TransCmp cmp] [Inhabited α] {he : t.isEmpty = false} :
    t.minKey he = t.minKey! :=
  DTreeMap.minKey_eq_minKey!

theorem minKey!_eq_default [TransCmp cmp] [Inhabited α] (he : t.isEmpty) :
    t.minKey! = default :=
  DTreeMap.minKey!_eq_default he

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall he

theorem minKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.minKey!_eq_iff_mem_and_forall he

@[grind =]
theorem minKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v).minKey! =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  DTreeMap.minKey!_insert

theorem minKey!_insert_le_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k v} :
    cmp (t.insert k v).minKey! t.minKey! |>.isLE :=
  DTreeMap.minKey!_insert_le_minKey! he

theorem minKey!_insert_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insert k v).minKey! k |>.isLE :=
  DTreeMap.minKey!_insert_le_self

theorem contains_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.contains t.minKey! :=
  DTreeMap.contains_minKey! he

theorem minKey!_mem [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.minKey! ∈ t :=
  DTreeMap.minKey!_mem he

theorem minKey!_le_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp t.minKey! k |>.isLE :=
  DTreeMap.minKey!_le_of_contains hc

theorem minKey!_le_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp t.minKey! k |>.isLE :=
  DTreeMap.minKey!_le_of_mem hc

theorem le_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    (cmp k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.le_minKey! he

theorem getKey?_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.getKey? t.minKey! = some t.minKey! :=
  DTreeMap.getKey?_minKey! he

@[grind =] theorem getKey_minKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey! :=
  DTreeMap.getKey_minKey!

@[simp, grind =]
theorem getKey_minKey!_eq_minKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey (isEmpty_eq_false_of_contains hc) :=
  DTreeMap.getKey_minKey!_eq_minKey

theorem getKey!_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.getKey! t.minKey! = t.minKey! :=
  DTreeMap.getKey!_minKey! he

theorem getKeyD_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.minKey! fallback = t.minKey! :=
  DTreeMap.getKeyD_minKey! he

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.minKey! = .eq) :
    (t.erase k).minKey! = t.minKey! :=
  DTreeMap.minKey!_erase_eq_of_not_compare_minKey!_eq he heq

theorem minKey!_le_minKey!_erase [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) :
    cmp t.minKey! (t.erase k).minKey! |>.isLE :=
  DTreeMap.minKey!_le_minKey!_erase he

@[grind =]
theorem minKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v).minKey! =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.minKey!_insertIfNew

theorem minKey!_insertIfNew_le_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k v} :
    cmp (t.insertIfNew k v).minKey! t.minKey! |>.isLE :=
  DTreeMap.minKey!_insertIfNew_le_minKey! he

theorem minKey!_insertIfNew_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insertIfNew k v).minKey! k |>.isLE :=
  DTreeMap.minKey!_insertIfNew_le_self

@[grind =_]
theorem minKey!_eq_head!_keys [TransCmp cmp] [Inhabited α] :
    t.minKey! = t.keys.head! :=
  DTreeMap.minKey!_eq_head!_keys

theorem minKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f).minKey! = if cmp t.minKey! k = .eq then k else t.minKey! :=
  DTreeMap.Const.minKey!_modify he

@[simp]
theorem minKey!_modify_eq_minKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f).minKey! = t.minKey! :=
  DTreeMap.Const.minKey!_modify_eq_minKey!

theorem compare_minKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f).minKey! t.minKey! = .eq :=
  DTreeMap.Const.compare_minKey!_modify_eq

@[simp]
theorem ordCompare_minKey!_modify_eq [Ord α] [TransOrd α] {t : TreeMap α β} [Inhabited α] {k f} :
    compare (modify t k f).minKey! t.minKey! = .eq :=
  compare_minKey!_modify_eq

theorem minKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f).minKey! = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Const.minKey!_alter_eq_self he

theorem minKey?_eq_some_minKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.minKey? = some (t.minKeyD fallback) :=
  DTreeMap.minKey?_eq_some_minKeyD he

theorem minKeyD_eq_fallback [TransCmp cmp] (he : t.isEmpty) {fallback} :
    t.minKeyD fallback = fallback :=
  DTreeMap.minKeyD_eq_fallback he

theorem minKey!_eq_minKeyD_default [TransCmp cmp] [Inhabited α] :
    t.minKey! = t.minKeyD default :=
  DTreeMap.minKey!_eq_minKeyD_default

theorem minKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.minKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall he

theorem minKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.minKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.minKeyD_eq_iff_mem_and_forall he

@[grind =]
theorem minKeyD_insert [TransCmp cmp] {k v fallback} :
    (t.insert k v |>.minKeyD fallback) =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  DTreeMap.minKeyD_insert

theorem minKeyD_insert_le_minKeyD [TransCmp cmp] (he : t.isEmpty = false)
    {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  DTreeMap.minKeyD_insert_le_minKeyD he

theorem minKeyD_insert_le_self [TransCmp cmp] {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) k |>.isLE :=
  DTreeMap.minKeyD_insert_le_self

theorem contains_minKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.contains (t.minKeyD fallback) :=
  DTreeMap.contains_minKeyD he

theorem minKeyD_mem [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.minKeyD fallback ∈ t :=
  DTreeMap.minKeyD_mem he

theorem minKeyD_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  DTreeMap.minKeyD_le_of_contains hc

theorem minKeyD_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  DTreeMap.minKeyD_le_of_mem hc

theorem le_minKeyD [TransCmp cmp] (he : t.isEmpty = false) {k fallback} :
    (cmp k (t.minKeyD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.le_minKeyD he

theorem getKey?_minKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.getKey? (t.minKeyD fallback) = some (t.minKeyD fallback) :=
  DTreeMap.getKey?_minKeyD he

@[grind =] theorem getKey_minKeyD [TransCmp cmp] {fallback hc} :
    t.getKey (t.minKeyD fallback) hc = t.minKeyD fallback :=
  DTreeMap.getKey_minKeyD

theorem getKey!_minKeyD [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getKey! (t.minKeyD fallback) = t.minKeyD fallback :=
  DTreeMap.getKey!_minKeyD he

theorem getKeyD_minKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback fallback'} :
    t.getKeyD (t.minKeyD fallback) fallback' = t.minKeyD fallback :=
  DTreeMap.getKeyD_minKeyD he

theorem minKeyD_erase_eq_of_not_compare_minKeyD_eq [TransCmp cmp] {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.minKeyD fallback) = .eq) :
    (t.erase k |>.minKeyD fallback) = t.minKeyD fallback :=
  DTreeMap.minKeyD_erase_eq_of_not_compare_minKeyD_eq he heq

theorem minKeyD_le_minKeyD_erase [TransCmp cmp] {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.minKeyD fallback) (t.erase k |>.minKeyD fallback) |>.isLE :=
  DTreeMap.minKeyD_le_minKeyD_erase he

@[grind =]
theorem minKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    (t.insertIfNew k v |>.minKeyD fallback) =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.minKeyD_insertIfNew

theorem minKeyD_insertIfNew_le_minKeyD [TransCmp cmp]
    (he : t.isEmpty = false) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  DTreeMap.minKeyD_insertIfNew_le_minKeyD he

theorem minKeyD_insertIfNew_le_self [TransCmp cmp] {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) k |>.isLE :=
  DTreeMap.minKeyD_insertIfNew_le_self

theorem minKeyD_eq_headD_keys [TransCmp cmp] {fallback} :
    t.minKeyD fallback = t.keys.headD fallback :=
  DTreeMap.minKeyD_eq_headD_keys

theorem minKeyD_modify [TransCmp cmp] {k f}
    (he : (modify t k f).isEmpty = false) {fallback} :
    (modify t k f |>.minKeyD fallback) =
      if cmp (t.minKeyD fallback) k = .eq then k else (t.minKeyD fallback) :=
  DTreeMap.Const.minKeyD_modify he

@[simp, grind =]
theorem minKeyD_modify_eq_minKeyD [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (modify t k f |>.minKeyD fallback) = t.minKeyD fallback :=
  DTreeMap.Const.minKeyD_modify_eq_minKeyD

theorem compare_minKeyD_modify_eq [TransCmp cmp] {k f fallback} :
    cmp (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  DTreeMap.Const.compare_minKeyD_modify_eq

@[simp]
theorem ordCompare_minKeyD_modify_eq [Ord α] [TransOrd α] {t : TreeMap α β} {k f fallback} :
    compare (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  compare_minKeyD_modify_eq

theorem minKeyD_alter_eq_self [TransCmp cmp] {k f}
    (he : (alter t k f).isEmpty = false) {fallback} :
    (alter t k f |>.minKeyD fallback) = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  DTreeMap.Const.minKeyD_alter_eq_self he

end Min

section Max

@[simp, grind =]
theorem maxKey?_emptyc :
    (∅ : TreeMap α β cmp).maxKey? = none :=
  DTreeMap.maxKey?_emptyc

theorem maxKey?_of_isEmpty [TransCmp cmp] :
    (he : t.isEmpty) → t.maxKey? = none :=
  DTreeMap.maxKey?_of_isEmpty

@[simp, grind =]
theorem maxKey?_eq_none_iff [TransCmp cmp] :
    t.maxKey? = none ↔ t.isEmpty :=
  DTreeMap.maxKey?_eq_none_iff

theorem maxKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.maxKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem maxKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.maxKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.maxKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_maxKey?_eq_isEmpty [TransCmp cmp] :
    t.maxKey?.isNone = t.isEmpty :=
  DTreeMap.isNone_maxKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_maxKey?_eq_not_isEmpty [TransCmp cmp] :
    t.maxKey?.isSome = !t.isEmpty :=
  DTreeMap.isSome_maxKey?_eq_not_isEmpty

theorem isSome_maxKey?_iff_isEmpty_eq_false [TransCmp cmp] :
    t.maxKey?.isSome ↔ t.isEmpty = false :=
  DTreeMap.isSome_maxKey?_iff_isEmpty_eq_false

@[grind =]
theorem maxKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  DTreeMap.maxKey?_insert

@[grind =]
theorem isSome_maxKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey?.isSome :=
  DTreeMap.isSome_maxKey?_insert

theorem maxKey?_le_maxKey?_insert [TransCmp cmp] {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insert k v |>.maxKey? |>.get isSome_maxKey?_insert) = kmi) →
    cmp km kmi |>.isLE :=
  DTreeMap.maxKey?_le_maxKey?_insert

theorem self_le_maxKey?_insert [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.maxKey?.get isSome_maxKey?_insert) = kmi) →
    cmp k kmi |>.isLE :=
  DTreeMap.self_le_maxKey?_insert

theorem contains_maxKey? [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) →
    t.contains km :=
  DTreeMap.contains_maxKey?

theorem isSome_maxKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.maxKey?.isSome :=
  DTreeMap.isSome_maxKey?_of_contains

theorem isSome_maxKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.maxKey?.isSome :=
  DTreeMap.isSome_maxKey?_of_mem

theorem le_maxKey?_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_contains hc) = km) →
    cmp k km |>.isLE :=
  DTreeMap.le_maxKey?_of_contains

theorem le_maxKey?_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_mem hc) = km) →
    cmp k km |>.isLE :=
  DTreeMap.le_maxKey?_of_mem

theorem maxKey?_le [TransCmp cmp] {k} :
    (∀ k', t.maxKey? = some k' → (cmp k' k).isLE) ↔
      (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.maxKey?_le

theorem getKey?_maxKey? [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) → t.getKey? km = some km :=
  DTreeMap.getKey?_maxKey?

theorem getKey_maxKey? [TransCmp cmp] {km hc} :
    (hkm : t.maxKey?.get (isSome_maxKey?_of_contains hc) = km) → t.getKey km hc = km :=
  DTreeMap.getKey_maxKey?

theorem getKey!_maxKey? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.maxKey? = some km) → t.getKey! km = km :=
  DTreeMap.getKey!_maxKey?

theorem getKeyD_maxKey? [TransCmp cmp] {km fallback} :
    (hkm : t.maxKey? = some km) → t.getKeyD km fallback = km :=
  DTreeMap.getKeyD_maxKey?

@[simp]
theorem maxKey?_bind_getKey? [TransCmp cmp] :
    t.maxKey?.bind t.getKey? = t.maxKey? :=
  DTreeMap.maxKey?_bind_getKey?

theorem maxKey?_erase_eq_iff_not_compare_eq_maxKey? [TransCmp cmp] {k} :
    (t.erase k |>.maxKey?) = t.maxKey? ↔
      ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq :=
  DTreeMap.maxKey?_erase_eq_iff_not_compare_eq_maxKey?

theorem maxKey?_erase_eq_of_not_compare_eq_maxKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.maxKey?) = t.maxKey? :=
  DTreeMap.maxKey?_erase_eq_of_not_compare_eq_maxKey?

theorem isSome_maxKey?_of_isSome_maxKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.maxKey?.isSome) →
    t.maxKey?.isSome :=
  DTreeMap.isSome_maxKey?_of_isSome_maxKey?_erase

theorem maxKey?_erase_le_maxKey? [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.maxKey?) = some kme) →
    (hkm : (t.maxKey?.get <|
      isSome_maxKey?_of_isSome_maxKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  DTreeMap.maxKey?_erase_le_maxKey?

@[grind =] theorem maxKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  DTreeMap.maxKey?_insertIfNew

@[grind =] theorem isSome_maxKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey?.isSome :=
  DTreeMap.isSome_maxKey?_insertIfNew

theorem maxKey?_le_maxKey?_insertIfNew [TransCmp cmp] {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.maxKey? |>.get isSome_maxKey?_insertIfNew) = kmi) →
    cmp km kmi |>.isLE :=
  DTreeMap.maxKey?_le_maxKey?_insertIfNew

theorem self_le_maxKey?_insertIfNew [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.maxKey?.get isSome_maxKey?_insertIfNew) = kmi) →
    cmp k kmi |>.isLE :=
  DTreeMap.self_le_maxKey?_insertIfNew

@[grind =_] theorem maxKey?_eq_getLast?_keys [TransCmp cmp] :
    t.maxKey? = t.keys.getLast? :=
  DTreeMap.maxKey?_eq_getLast?_keys

@[grind =] theorem maxKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).maxKey? = t.maxKey?.map fun km => if cmp km k = .eq then k else km :=
  DTreeMap.Const.maxKey?_modify

@[simp, grind =]
theorem maxKey?_modify_eq_maxKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).maxKey? = t.maxKey? :=
  DTreeMap.Const.maxKey?_modify_eq_maxKey?

theorem isSome_maxKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).maxKey?.isSome = !t.isEmpty :=
  DTreeMap.Const.isSome_maxKey?_modify

theorem isSome_maxKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (t.modify k f).maxKey?.isSome = t.maxKey?.isSome :=
  DTreeMap.Const.isSome_maxKey?_modify_eq_isSome

theorem compare_maxKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.maxKey? = some km) →
    (hkmm : (t.modify k f |>.maxKey? |>.get <|
        isSome_maxKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  DTreeMap.Const.compare_maxKey?_modify_eq

theorem maxKey?_alter_eq_self [TransCmp cmp] {k f} :
    (t.alter k f).maxKey? = some k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Const.maxKey?_alter_eq_self

theorem maxKey_eq_get_maxKey? [TransCmp cmp] {he} :
    t.maxKey he = t.maxKey?.get (isSome_maxKey?_iff_isEmpty_eq_false.mpr he) :=
  DTreeMap.maxKey_eq_get_maxKey?

theorem maxKey?_eq_some_maxKey [TransCmp cmp] {he} :
    t.maxKey? = some (t.maxKey he) :=
  DTreeMap.maxKey?_eq_some_maxKey

theorem maxKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.maxKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall

theorem maxKey_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.maxKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.maxKey_eq_iff_mem_and_forall

@[grind =] theorem maxKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey isEmpty_insert =
      t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k' :=
  DTreeMap.maxKey_insert

theorem maxKey_le_maxKey_insert [TransCmp cmp] {k v he} :
    cmp (t.maxKey he) (t.insert k v |>.maxKey isEmpty_insert) |>.isLE :=
  DTreeMap.maxKey_le_maxKey_insert

theorem self_le_maxKey_insert [TransCmp cmp] {k v} :
    cmp k (t.insert k v |>.maxKey isEmpty_insert) |>.isLE :=
  DTreeMap.self_le_maxKey_insert

@[grind =] theorem contains_maxKey [TransCmp cmp] {he} :
    t.contains (t.maxKey he) :=
  DTreeMap.contains_maxKey

@[grind] theorem maxKey_mem [TransCmp cmp] {he} :
    t.maxKey he ∈ t :=
  DTreeMap.maxKey_mem

theorem le_maxKey_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp k (t.maxKey <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) |>.isLE :=
  DTreeMap.le_maxKey_of_contains hc

theorem le_maxKey_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp k (t.maxKey <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) |>.isLE :=
  DTreeMap.le_maxKey_of_mem hc

theorem maxKey_le [TransCmp cmp] {k he} :
    (cmp (t.maxKey he) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.maxKey_le

@[simp, grind =]
theorem getKey?_maxKey [TransCmp cmp] {he} :
    t.getKey? (t.maxKey he) = some (t.maxKey he) :=
  DTreeMap.getKey?_maxKey

@[simp, grind =]
theorem getKey_maxKey [TransCmp cmp] {he hc} :
    t.getKey (t.maxKey he) hc = t.maxKey he :=
  DTreeMap.getKey_maxKey

@[simp, grind =]
theorem getKey!_maxKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.maxKey he) = t.maxKey he :=
  DTreeMap.getKey!_maxKey

@[simp, grind =]
theorem getKeyD_maxKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.maxKey he) fallback = t.maxKey he :=
  DTreeMap.getKeyD_maxKey

@[simp]
theorem maxKey_erase_eq_iff_not_compare_eq_maxKey [TransCmp cmp] {k he} :
    (t.erase k |>.maxKey he) =
        t.maxKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he) ↔
      ¬ cmp k (t.maxKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) = .eq :=
  DTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey

theorem maxKey_erase_eq_of_not_compare_eq_maxKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.maxKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he)) = .eq) →
    (t.erase k |>.maxKey he) =
      t.maxKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he) :=
  DTreeMap.maxKey_erase_eq_of_not_compare_eq_maxKey

theorem maxKey_erase_le_maxKey [TransCmp cmp] {k he} :
    cmp (t.erase k |>.maxKey he)
      (t.maxKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) |>.isLE :=
  DTreeMap.maxKey_erase_le_maxKey

@[grind =] theorem maxKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey isEmpty_insertIfNew =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.maxKey_insertIfNew

theorem maxKey_le_maxKey_insertIfNew [TransCmp cmp] {k v he} :
    cmp (t.maxKey he)
      (t.insertIfNew k v |>.maxKey isEmpty_insertIfNew) |>.isLE :=
  DTreeMap.maxKey_le_maxKey_insertIfNew (t := t.inner) (he := he)

theorem self_le_maxKey_insertIfNew [TransCmp cmp] {k v} :
    cmp k (t.insertIfNew k v |>.maxKey <| isEmpty_insertIfNew) |>.isLE :=
  DTreeMap.self_le_maxKey_insertIfNew

@[grind =_] theorem maxKey_eq_getLast_keys [TransCmp cmp] {he} :
    t.maxKey he = t.keys.getLast (List.isEmpty_eq_false_iff.mp <| isEmpty_keys ▸ he) :=
  DTreeMap.maxKey_eq_getLast_keys

theorem maxKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).maxKey he =
      if cmp (t.maxKey <| cast (congrArg (· = false) isEmpty_modify) he) k = .eq then
        k
      else
        (t.maxKey <| cast (congrArg (· = false) isEmpty_modify) he) :=
  DTreeMap.Const.maxKey_modify

@[simp, grind =]
theorem maxKey_modify_eq_maxKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).maxKey he = t.maxKey (cast (congrArg (· = false) isEmpty_modify) he) :=
  DTreeMap.Const.maxKey_modify_eq_maxKey

theorem compare_maxKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.maxKey he)
      (t.maxKey <| cast (congrArg (· = false) isEmpty_modify) he) = .eq :=
  DTreeMap.Const.compare_maxKey_modify_eq

@[simp]
theorem ordCompare_maxKey_modify_eq [Ord α] [TransOrd α] {t : TreeMap α β} {k f he} :
    compare (modify t k f |>.maxKey he)
      (t.maxKey <| cast (congrArg (· = false) isEmpty_modify) he) = .eq :=
  compare_maxKey_modify_eq

theorem maxKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).maxKey he = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Const.maxKey_alter_eq_self

theorem maxKey?_eq_some_maxKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.maxKey? = some t.maxKey! :=
  DTreeMap.maxKey?_eq_some_maxKey! he

theorem maxKey_eq_maxKey! [TransCmp cmp] [Inhabited α] {he : t.isEmpty = false} :
    t.maxKey he = t.maxKey! :=
  DTreeMap.maxKey_eq_maxKey!

theorem maxKey!_eq_default [TransCmp cmp] [Inhabited α] (he : t.isEmpty) :
    t.maxKey! = default :=
  DTreeMap.maxKey!_eq_default he

theorem maxKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.maxKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall he

theorem maxKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.maxKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.maxKey!_eq_iff_mem_and_forall he

@[grind =]
theorem maxKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v).maxKey! =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  DTreeMap.maxKey!_insert

theorem maxKey!_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k v} :
    cmp t.maxKey! (t.insert k v).maxKey! |>.isLE :=
  DTreeMap.maxKey!_le_maxKey!_insert he

theorem self_le_maxKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    cmp k (t.insert k v).maxKey! |>.isLE :=
  DTreeMap.self_le_maxKey!_insert

theorem contains_maxKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.contains t.maxKey! :=
  DTreeMap.contains_maxKey! he

theorem maxKey!_mem [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.maxKey! ∈ t :=
  DTreeMap.maxKey!_mem he

theorem le_maxKey!_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp k t.maxKey! |>.isLE :=
  DTreeMap.le_maxKey!_of_contains hc

theorem le_maxKey!_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp k t.maxKey! |>.isLE :=
  DTreeMap.le_maxKey!_of_mem hc

theorem maxKey!_le [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    (cmp t.maxKey! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.maxKey!_le he

theorem getKey?_maxKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.getKey? t.maxKey! = some t.maxKey! :=
  DTreeMap.getKey?_maxKey! he

@[grind =] theorem getKey_maxKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.maxKey! hc = t.maxKey! :=
  DTreeMap.getKey_maxKey!

@[simp, grind =]
theorem getKey_maxKey!_eq_maxKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.maxKey! hc = t.maxKey (isEmpty_eq_false_of_contains hc) :=
  DTreeMap.getKey_maxKey!_eq_maxKey

theorem getKey!_maxKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.getKey! t.maxKey! = t.maxKey! :=
  DTreeMap.getKey!_maxKey! he

theorem getKeyD_maxKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.maxKey! fallback = t.maxKey! :=
  DTreeMap.getKeyD_maxKey! he

theorem maxKey!_erase_eq_of_not_compare_maxKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.maxKey! = .eq) :
    (t.erase k).maxKey! = t.maxKey! :=
  DTreeMap.maxKey!_erase_eq_of_not_compare_maxKey!_eq he heq

theorem maxKey!_erase_le_maxKey! [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) :
    cmp (t.erase k).maxKey! t.maxKey! |>.isLE :=
  DTreeMap.maxKey!_erase_le_maxKey! he

@[grind =]
theorem maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v).maxKey! =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.maxKey!_insertIfNew

theorem maxKey!_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k v} :
    cmp t.maxKey! (t.insertIfNew k v).maxKey! |>.isLE :=
  DTreeMap.maxKey!_le_maxKey!_insertIfNew he

theorem self_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    cmp k (t.insertIfNew k v).maxKey! |>.isLE :=
  DTreeMap.self_le_maxKey!_insertIfNew

@[grind =_]
theorem maxKey!_eq_getLast!_keys [TransCmp cmp] [Inhabited α] :
    t.maxKey! = t.keys.getLast! :=
  DTreeMap.maxKey!_eq_getLast!_keys

theorem maxKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f).maxKey! = if cmp t.maxKey! k = .eq then k else t.maxKey! :=
  DTreeMap.Const.maxKey!_modify he

@[simp]
theorem maxKey!_modify_eq_maxKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f).maxKey! = t.maxKey! :=
  DTreeMap.Const.maxKey!_modify_eq_maxKey!

theorem compare_maxKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f).maxKey! t.maxKey! = .eq :=
  DTreeMap.Const.compare_maxKey!_modify_eq

@[simp]
theorem ordCompare_maxKey!_modify_eq [Ord α] [TransOrd α] {t : TreeMap α β} [Inhabited α] {k f} :
    compare (modify t k f).maxKey! t.maxKey! = .eq :=
  compare_maxKey!_modify_eq

theorem maxKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f).maxKey! = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Const.maxKey!_alter_eq_self he

theorem maxKey?_eq_some_maxKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.maxKey? = some (t.maxKeyD fallback) :=
  DTreeMap.maxKey?_eq_some_maxKeyD he

theorem maxKeyD_eq_fallback [TransCmp cmp] (he : t.isEmpty) {fallback} :
    t.maxKeyD fallback = fallback :=
  DTreeMap.maxKeyD_eq_fallback he

theorem maxKey!_eq_maxKeyD_default [TransCmp cmp] [Inhabited α] :
    t.maxKey! = t.maxKeyD default :=
  DTreeMap.maxKey!_eq_maxKeyD_default

theorem maxKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.maxKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.maxKeyD_eq_iff_getKey?_eq_self_and_forall he

theorem maxKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t.isEmpty = false) {km fallback} :
    t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.maxKeyD_eq_iff_mem_and_forall he

@[grind =]
theorem maxKeyD_insert [TransCmp cmp] {k v fallback} :
    (t.insert k v |>.maxKeyD fallback) =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  DTreeMap.maxKeyD_insert

theorem maxKeyD_le_maxKeyD_insert [TransCmp cmp] (he : t.isEmpty = false)
    {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.maxKeyD_le_maxKeyD_insert he

theorem self_le_maxKeyD_insert [TransCmp cmp] {k v fallback} :
    cmp k (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.self_le_maxKeyD_insert

theorem contains_maxKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.contains (t.maxKeyD fallback) :=
  DTreeMap.contains_maxKeyD he

theorem maxKeyD_mem [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.maxKeyD fallback ∈ t :=
  DTreeMap.maxKeyD_mem he

theorem le_maxKeyD_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  DTreeMap.le_maxKeyD_of_contains hc

theorem le_maxKeyD_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  DTreeMap.le_maxKeyD_of_mem hc

theorem maxKeyD_le [TransCmp cmp] (he : t.isEmpty = false) {k fallback} :
    (cmp (t.maxKeyD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.maxKeyD_le he

theorem getKey?_maxKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback} :
    t.getKey? (t.maxKeyD fallback) = some (t.maxKeyD fallback) :=
  DTreeMap.getKey?_maxKeyD he

@[grind =] theorem getKey_maxKeyD [TransCmp cmp] {fallback hc} :
    t.getKey (t.maxKeyD fallback) hc = t.maxKeyD fallback :=
  DTreeMap.getKey_maxKeyD

theorem getKey!_maxKeyD [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getKey! (t.maxKeyD fallback) = t.maxKeyD fallback :=
  DTreeMap.getKey!_maxKeyD he

theorem getKeyD_maxKeyD [TransCmp cmp] (he : t.isEmpty = false) {fallback fallback'} :
    t.getKeyD (t.maxKeyD fallback) fallback' = t.maxKeyD fallback :=
  DTreeMap.getKeyD_maxKeyD he

theorem maxKeyD_erase_eq_of_not_compare_maxKeyD_eq [TransCmp cmp] {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.maxKeyD fallback) = .eq) :
    (t.erase k |>.maxKeyD fallback) = t.maxKeyD fallback :=
  DTreeMap.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq he heq

theorem maxKeyD_erase_le_maxKeyD [TransCmp cmp] {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.erase k |>.maxKeyD fallback) (t.maxKeyD fallback) |>.isLE :=
  DTreeMap.maxKeyD_erase_le_maxKeyD he

@[grind =]
theorem maxKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    (t.insertIfNew k v |>.maxKeyD fallback) =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.maxKeyD_insertIfNew

theorem maxKeyD_le_maxKeyD_insertIfNew [TransCmp cmp]
    (he : t.isEmpty = false) {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.maxKeyD_le_maxKeyD_insertIfNew he

theorem self_le_maxKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    cmp k (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  DTreeMap.self_le_maxKeyD_insertIfNew

theorem maxKeyD_eq_getLastD_keys [TransCmp cmp] {fallback} :
    t.maxKeyD fallback = t.keys.getLastD fallback :=
  DTreeMap.maxKeyD_eq_getLastD_keys

theorem maxKeyD_modify [TransCmp cmp] {k f}
    (he : (modify t k f).isEmpty = false) {fallback} :
    (modify t k f |>.maxKeyD fallback) =
      if cmp (t.maxKeyD fallback) k = .eq then k else (t.maxKeyD fallback) :=
  DTreeMap.Const.maxKeyD_modify he

@[simp, grind =]
theorem maxKeyD_modify_eq_maxKeyD [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (modify t k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  DTreeMap.Const.maxKeyD_modify_eq_maxKeyD

theorem compare_maxKeyD_modify_eq [TransCmp cmp] {k f fallback} :
    cmp (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  DTreeMap.Const.compare_maxKeyD_modify_eq

@[simp]
theorem ordCompare_maxKeyD_modify_eq [Ord α] [TransOrd α] {t : TreeMap α β} {k f fallback} :
    compare (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  compare_maxKeyD_modify_eq

theorem maxKeyD_alter_eq_self [TransCmp cmp] {k f}
    (he : (alter t k f).isEmpty = false) {fallback} :
    (alter t k f |>.maxKeyD fallback) = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  DTreeMap.Const.maxKeyD_alter_eq_self he

end Max

namespace Equiv

variable {t₁ t₂ t₃ t₄ : TreeMap α β cmp} {δ : Type w} {m : Type w → Type w'}

@[refl, simp] theorem rfl : Equiv t t := ⟨.rfl⟩

@[symm] theorem symm : Equiv t₁ t₂ → Equiv t₂ t₁
  | ⟨h⟩ => ⟨h.symm⟩

theorem trans : Equiv t₁ t₂ → Equiv t₂ t₃ → Equiv t₁ t₃
  | ⟨h⟩, ⟨h'⟩ => ⟨h.trans h'⟩

instance instTrans : @Trans (TreeMap α β cmp) _ _ Equiv Equiv Equiv := ⟨trans⟩

theorem comm : t₁ ~m t₂ ↔ t₂ ~m t₁ := ⟨symm, symm⟩
theorem congr_left (h : t₁ ~m t₂) : t₁ ~m t₃ ↔ t₂ ~m t₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : t₁ ~m t₂) : t₃ ~m t₁ ↔ t₃ ~m t₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

-- congruence lemmas

theorem isEmpty_eq (h : t₁ ~m t₂) : t₁.isEmpty = t₂.isEmpty :=
  h.1.isEmpty_eq

theorem contains_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.contains k = t₂.contains k :=
  h.1.contains_eq

theorem mem_iff [TransCmp cmp] (h : t₁ ~m t₂) {k : α} :
    k ∈ t₁ ↔ k ∈ t₂ :=
  h.1.mem_iff

theorem size_eq (h : t₁ ~m t₂) : t₁.size = t₂.size :=
  h.1.size_eq

theorem getElem?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) : t₁[k]? = t₂[k]? :=
  h.1.constGet?_eq

theorem getElem_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h : t₁ ~m t₂) :
    t₁[k] = t₂[k]'(h.mem_iff.mp hk) :=
  h.1.constGet_eq

theorem getElem!_eq [TransCmp cmp] [Inhabited β] {k : α} (h : t₁ ~m t₂) :
    t₁[k]! = t₂[k]! :=
  h.1.constGet!_eq

theorem getD_eq [TransCmp cmp] {k : α} {fallback : β} (h : t₁ ~m t₂) :
    t₁.getD k fallback = t₂.getD k fallback :=
  h.1.constGetD_eq

theorem getKey?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getKey? k = t₂.getKey? k :=
  h.1.getKey?_eq

theorem getKey_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h : t₁ ~m t₂) :
    t₁.getKey k hk = t₂.getKey k (h.mem_iff.mp hk) :=
  h.1.getKey_eq

theorem getKey!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getKey! k = t₂.getKey! k :=
  h.1.getKey!_eq

theorem getKeyD_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getKeyD k fallback = t₂.getKeyD k fallback :=
  h.1.getKeyD_eq

theorem toList_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.toList = t₂.toList :=
  h.1.constToList_eq

theorem toArray_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.toArray = t₂.toArray :=
  h.1.constToArray_eq

theorem keys_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.keys = t₂.keys :=
  h.1.keys_eq

theorem keysArray_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.keysArray = t₂.keysArray :=
  h.1.keysArray_eq

theorem foldlM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → β → m δ} {init : δ}
    (h : t₁ ~m t₂) :
    t₁.foldlM f init = t₂.foldlM f init :=
  h.1.foldlM_eq

theorem foldl_eq [TransCmp cmp] {f : δ → α → β → δ} {init : δ} (h : t₁ ~m t₂) :
    t₁.foldl f init = t₂.foldl f init :=
  h.1.foldl_eq

theorem foldrM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → β → δ → m δ} {init : δ}
    (h : t₁ ~m t₂) :
    t₁.foldrM f init = t₂.foldrM f init :=
  h.1.foldrM_eq

theorem foldr_eq [TransCmp cmp] {f : α → β → δ → δ} {init : δ} (h : t₁ ~m t₂) :
    t₁.foldr f init = t₂.foldr f init :=
  h.1.foldr_eq

theorem forIn_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {b : δ} {f : α × β → δ → m (ForInStep δ)}
    (h : t₁ ~m t₂) : ForIn.forIn t₁ b f = ForIn.forIn t₂ b f :=
  h.1.forIn_eq (f := fun ⟨a, b⟩ => f ⟨a, b⟩)

theorem forM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α × β → m PUnit} (h : t₁ ~m t₂) :
    ForM.forM t₁ f = ForM.forM t₂ f :=
  h.1.forM_eq (f := fun x : (_ : α) × β => f (x.1, x.2))

theorem any_eq [TransCmp cmp] {p : α → β → Bool} (h : t₁ ~m t₂) : t₁.any p = t₂.any p :=
  h.1.any_eq

theorem all_eq [TransCmp cmp] {p : α → β → Bool} (h : t₁ ~m t₂) : t₁.all p = t₂.all p :=
  h.1.all_eq

theorem minKey?_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.minKey? = t₂.minKey? :=
  h.1.minKey?_eq

theorem minKey_eq [TransCmp cmp] {h' : t₁.isEmpty = false} (h : t₁ ~m t₂) :
    t₁.minKey h' = t₂.minKey (h.isEmpty_eq.symm.trans h') :=
  h.1.minKey_eq

theorem minKey!_eq [TransCmp cmp] [Inhabited α] (h : t₁ ~m t₂) :
    t₁.minKey! = t₂.minKey! :=
  h.1.minKey!_eq

theorem minKeyD_eq [TransCmp cmp] {fallback : α} (h : t₁ ~m t₂) :
    t₁.minKeyD fallback = t₂.minKeyD fallback :=
  h.1.minKeyD_eq

theorem maxKey?_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.maxKey? = t₂.maxKey? :=
  h.1.maxKey?_eq

theorem maxKey_eq [TransCmp cmp] {h' : t₁.isEmpty = false} (h : t₁ ~m t₂) :
    t₁.maxKey h' = t₂.maxKey (h.isEmpty_eq.symm.trans h') :=
  h.1.maxKey_eq

theorem maxKey!_eq [TransCmp cmp] [Inhabited α] (h : t₁ ~m t₂) :
    t₁.maxKey! = t₂.maxKey! :=
  h.1.maxKey!_eq

theorem maxKeyD_eq [TransCmp cmp] {fallback : α} (h : t₁ ~m t₂) :
    t₁.maxKeyD fallback = t₂.maxKeyD fallback :=
  h.1.maxKeyD_eq

theorem minEntry?_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.minEntry? = t₂.minEntry? :=
  h.1.constMinEntry?_eq

theorem minEntry_eq [TransCmp cmp] {he : t₁.isEmpty = false} (h : t₁ ~m t₂) :
    t₁.minEntry he = t₂.minEntry (h.isEmpty_eq.symm.trans he) :=
  h.1.constMinEntry_eq

theorem minEntry!_eq [TransCmp cmp] [Inhabited (α × β)] (h : t₁ ~m t₂) :
    t₁.minEntry! = t₂.minEntry! :=
  h.1.constMinEntry!_eq

theorem minEntryD_eq [TransCmp cmp] {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.minEntryD fallback = t₂.minEntryD fallback :=
  h.1.constMinEntryD_eq

theorem maxEntry?_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.maxEntry? = t₂.maxEntry? :=
  h.1.constMaxEntry?_eq

theorem maxEntry_eq [TransCmp cmp] {he : t₁.isEmpty = false} (h : t₁ ~m t₂) :
    t₁.maxEntry he = t₂.maxEntry (h.isEmpty_eq.symm.trans he) :=
  h.1.constMaxEntry_eq

theorem maxEntry!_eq [TransCmp cmp] [Inhabited (α × β)] (h : t₁ ~m t₂) :
    t₁.maxEntry! = t₂.maxEntry! :=
  h.1.constMaxEntry!_eq

theorem maxEntryD_eq [TransCmp cmp] {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.maxEntryD fallback = t₂.maxEntryD fallback :=
  h.1.constMaxEntryD_eq

theorem entryAtIdx?_eq [TransCmp cmp] {i : Nat} (h : t₁ ~m t₂) :
    t₁.entryAtIdx? i = t₂.entryAtIdx? i :=
  h.1.constEntryAtIdx?_eq

theorem entryAtIdx_eq [TransCmp cmp] {i : Nat} {h' : i < t₁.size} (h : t₁ ~m t₂) :
    t₁.entryAtIdx i h' = t₂.entryAtIdx i (h.size_eq ▸ h') :=
  h.1.constEntryAtIdx_eq

theorem entryAtIdx!_eq [TransCmp cmp] [Inhabited (α × β)] {i : Nat} (h : t₁ ~m t₂) :
    t₁.entryAtIdx! i = t₂.entryAtIdx! i :=
  h.1.constEntryAtIdx!_eq

theorem entryAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.entryAtIdxD i fallback = t₂.entryAtIdxD i fallback :=
  h.1.constEntryAtIdxD_eq

theorem keyAtIdx?_eq [TransCmp cmp] {i : Nat} (h : t₁ ~m t₂) :
    t₁.keyAtIdx? i = t₂.keyAtIdx? i :=
  h.1.keyAtIdx?_eq

theorem keyAtIdx_eq [TransCmp cmp] {i : Nat} {h' : i < t₁.size} (h : t₁ ~m t₂) :
    t₁.keyAtIdx i h' = t₂.keyAtIdx i (h.size_eq ▸ h') :=
  h.1.keyAtIdx_eq

theorem keyAtIdx!_eq [TransCmp cmp] [Inhabited α] {i : Nat} (h : t₁ ~m t₂) :
    t₁.keyAtIdx! i = t₂.keyAtIdx! i :=
  h.1.keyAtIdx!_eq

theorem keyAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α} (h : t₁ ~m t₂) :
    t₁.keyAtIdxD i fallback = t₂.keyAtIdxD i fallback :=
  h.1.keyAtIdxD_eq

theorem getEntryGE?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryGE? k = t₂.getEntryGE? k :=
  h.1.constGetEntryGE?_eq

theorem getEntryGE_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getEntryGE k h' = t₂.getEntryGE k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.constGetEntryGE_eq

theorem getEntryGE!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryGE! k = t₂.getEntryGE! k :=
  h.1.constGetEntryGE!_eq

theorem getEntryGED_eq [TransCmp cmp] {k : α} {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.getEntryGED k fallback = t₂.getEntryGED k fallback :=
  h.1.constGetEntryGED_eq

theorem getEntryGT?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryGT? k = t₂.getEntryGT? k :=
  h.1.constGetEntryGT?_eq

theorem getEntryGT_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getEntryGT k h' = t₂.getEntryGT k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.constGetEntryGT_eq

theorem getEntryGT!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryGT! k = t₂.getEntryGT! k :=
  h.1.constGetEntryGT!_eq

theorem getEntryGTD_eq [TransCmp cmp] {k : α} {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.getEntryGTD k fallback = t₂.getEntryGTD k fallback :=
  h.1.constGetEntryGTD_eq

theorem getEntryLE?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryLE? k = t₂.getEntryLE? k :=
  h.1.constGetEntryLE?_eq

theorem getEntryLE_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getEntryLE k h' = t₂.getEntryLE k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.constGetEntryLE_eq

theorem getEntryLE!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryLE! k = t₂.getEntryLE! k :=
  h.1.constGetEntryLE!_eq

theorem getEntryLED_eq [TransCmp cmp] {k : α} {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.getEntryLED k fallback = t₂.getEntryLED k fallback :=
  h.1.constGetEntryLED_eq

theorem getEntryLT?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryLT? k = t₂.getEntryLT? k :=
  h.1.constGetEntryLT?_eq

theorem getEntryLT_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getEntryLT k h' = t₂.getEntryLT k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.constGetEntryLT_eq

theorem getEntryLT!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h : t₁ ~m t₂) :
    t₁.getEntryLT! k = t₂.getEntryLT! k :=
  h.1.constGetEntryLT!_eq

theorem getEntryLTD_eq [TransCmp cmp] {k : α} {fallback : α × β} (h : t₁ ~m t₂) :
    t₁.getEntryLTD k fallback = t₂.getEntryLTD k fallback :=
  h.1.constGetEntryLTD_eq

theorem getKeyGE?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyGE? k = t₂.getKeyGE? k :=
  h.1.getKeyGE?_eq

theorem getKeyGE_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getKeyGE k h' = t₂.getKeyGE k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyGE_eq

theorem getKeyGE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyGE! k = t₂.getKeyGE! k :=
  h.1.getKeyGE!_eq

theorem getKeyGED_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getKeyGED k fallback = t₂.getKeyGED k fallback :=
  h.1.getKeyGED_eq

theorem getKeyGT?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyGT? k = t₂.getKeyGT? k :=
  h.1.getKeyGT?_eq

theorem getKeyGT_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getKeyGT k h' = t₂.getKeyGT k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyGT_eq

theorem getKeyGT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyGT! k = t₂.getKeyGT! k :=
  h.1.getKeyGT!_eq

theorem getKeyGTD_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getKeyGTD k fallback = t₂.getKeyGTD k fallback :=
  h.1.getKeyGTD_eq

theorem getKeyLE?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyLE? k = t₂.getKeyLE? k :=
  h.1.getKeyLE?_eq

theorem getKeyLE_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getKeyLE k h' = t₂.getKeyLE k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyLE_eq

theorem getKeyLE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyLE! k = t₂.getKeyLE! k :=
  h.1.getKeyLE!_eq

theorem getKeyLED_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getKeyLED k fallback = t₂.getKeyLED k fallback :=
  h.1.getKeyLED_eq

theorem getKeyLT?_eq [TransCmp cmp] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyLT? k = t₂.getKeyLT? k :=
  h.1.getKeyLT?_eq

theorem getKeyLT_eq [TransCmp cmp] {k : α} {h'} (h : t₁ ~m t₂) :
    t₁.getKeyLT k h' = t₂.getKeyLT k (h'.imp fun _ ⟨h₁, h₂⟩ => ⟨h.mem_iff.mp h₁, h₂⟩) :=
  h.1.getKeyLT_eq

theorem getKeyLT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h : t₁ ~m t₂) :
    t₁.getKeyLT! k = t₂.getKeyLT! k :=
  h.1.getKeyLT!_eq

theorem getKeyLTD_eq [TransCmp cmp] {k fallback : α} (h : t₁ ~m t₂) :
    t₁.getKeyLTD k fallback = t₂.getKeyLTD k fallback :=
  h.1.getKeyLTD_eq

theorem insert [TransCmp cmp] (h : t₁ ~m t₂) (k : α) (v : β) : t₁.insert k v ~m t₂.insert k v :=
  ⟨h.1.insert k v⟩

theorem erase [TransCmp cmp] (h : t₁ ~m t₂) (k : α) : t₁.erase k ~m t₂.erase k :=
  ⟨h.1.erase k⟩

theorem insertIfNew [TransCmp cmp] (h : t₁ ~m t₂) (k : α) (v : β) :
    t₁.insertIfNew k v ~m t₂.insertIfNew k v :=
  ⟨h.1.insertIfNew k v⟩

theorem alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t₁ ~m t₂)
    (k : α) (f : Option β → Option β) : t₁.alter k f ~m t₂.alter k f :=
  ⟨h.1.constAlter k f⟩

theorem modify [TransCmp cmp] [LawfulEqCmp cmp] (h : t₁ ~m t₂)
    (k : α) (f : β → β) : t₁.modify k f ~m t₂.modify k f :=
  ⟨h.1.constModify k f⟩

theorem filter (h : t₁ ~m t₂) (f : α → β → Bool) : t₁.filter f ~m t₂.filter f :=
  ⟨h.1.filter f⟩

theorem map (h : t₁ ~m t₂) (f : α → β → γ) : t₁.map f ~m t₂.map f :=
  ⟨h.1.map f⟩

theorem filterMap (h : t₁ ~m t₂) (f : α → β → Option γ) : t₁.filterMap f ~m t₂.filterMap f :=
  ⟨h.1.filterMap f⟩

theorem insertMany_list [TransCmp cmp] (h : t₁ ~m t₂) (l : List (α × β)) :
    t₁.insertMany l ~m t₂.insertMany l :=
  ⟨h.1.constInsertMany_list l⟩

theorem insertManyIfNewUnit_list [TransCmp cmp] {t₁ t₂ : TreeMap α Unit cmp}
    (h : t₁ ~m t₂) (l : List α) :
    t₁.insertManyIfNewUnit l ~m t₂.insertManyIfNewUnit l :=
  ⟨h.1.constInsertManyIfNewUnit_list l⟩

theorem eraseMany_list [TransCmp cmp] (h : t₁ ~m t₂) (l : List α) :
    t₁.eraseMany l ~m t₂.eraseMany l :=
  ⟨h.1.eraseMany_list l⟩

theorem mergeWith [TransCmp cmp] [LawfulEqCmp cmp] (f : α → β → β → β)
    (h : t₁ ~m t₂) (h' : t₃ ~m t₄) : t₁.mergeWith f t₃ ~m t₂.mergeWith f t₄ :=
  ⟨h.1.constMergeWith f h'.1⟩

theorem values_eq [TransCmp cmp] (h : t₁ ~m t₂) : t₁.values = t₂.values :=
  h.1.values_eq

theorem valuesArray_eq [TransCmp cmp] (h : t₁ ~m t₂) :
    t₁.valuesArray = t₂.valuesArray :=
  h.1.valuesArray_eq

-- extensionalities

theorem of_forall_getKey_eq_of_forall_constGet?_eq [TransCmp cmp]
    (hk : ∀ k hk hk', t₁.getKey k hk = t₂.getKey k hk')
    (hv : ∀ k : α, t₁[k]? = t₂[k]?) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey_eq_of_forall_constGet?_eq hk hv⟩

theorem of_forall_constGet?_eq [TransCmp cmp] [LawfulEqCmp cmp]
    (h : ∀ k : α, t₁[k]? = t₂[k]?) : t₁ ~m t₂ :=
  ⟨.of_forall_constGet?_eq h⟩

theorem of_forall_getKey?_unit_eq [TransCmp cmp] {t₁ t₂ : TreeMap α Unit cmp}
    (h : ∀ k, t₁.getKey? k = t₂.getKey? k) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey?_unit_eq h⟩

theorem of_forall_contains_unit_eq [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : TreeMap α Unit cmp}
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ ~m t₂ :=
  ⟨.of_forall_contains_unit_eq h⟩

theorem of_forall_mem_unit_iff [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : TreeMap α Unit cmp}
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ ~m t₂ :=
  ⟨.of_forall_mem_unit_iff h⟩

end Equiv

section Equiv

variable {t₁ t₂ : TreeMap α β cmp}

private theorem equiv_iff_equiv : t₁ ~m t₂ ↔ t₁.1.Equiv t₂.1 :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem equiv_empty_iff_isEmpty : t ~m empty ↔ t.isEmpty :=
  equiv_iff_equiv.trans DTreeMap.equiv_empty_iff_isEmpty

theorem empty_equiv_iff_isEmpty : empty ~m t ↔ t.isEmpty :=
  Equiv.comm.trans equiv_empty_iff_isEmpty

theorem equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList :=
  equiv_iff_equiv.trans DTreeMap.Const.equiv_iff_toList_perm

theorem Equiv.of_toList_perm (h : t₁.toList.Perm t₂.toList) : t₁ ~m t₂ :=
  ⟨.of_constToList_perm h⟩

theorem equiv_iff_toList_eq [TransCmp cmp] :
    t₁ ~m t₂ ↔ t₁.toList = t₂.toList :=
  equiv_iff_equiv.trans DTreeMap.Const.equiv_iff_toList_eq

theorem equiv_iff_keys_unit_perm {t₁ t₂ : TreeMap α Unit cmp} :
    t₁ ~m t₂ ↔ t₁.keys.Perm t₂.keys :=
  equiv_iff_equiv.trans DTreeMap.Const.equiv_iff_keys_unit_perm

theorem equiv_iff_keys_unit_eq [TransCmp cmp] {t₁ t₂ : TreeMap α Unit cmp} :
    t₁ ~m t₂ ↔ t₁.keys = t₂.keys :=
  equiv_iff_equiv.trans DTreeMap.Const.equiv_iff_keys_unit_eq

theorem Equiv.of_keys_unit_perm {t₁ t₂ : TreeMap α Unit cmp} : t₁.keys.Perm t₂.keys → t₁ ~m t₂ :=
  equiv_iff_keys_unit_perm.mpr

end Equiv

end Std.TreeMap
