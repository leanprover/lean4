/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Markus Himmel, Paul Reichert
-/
module

prelude
public import Std.Data.ExtDTreeMap.Lemmas
public import Std.Data.ExtTreeMap.Basic

@[expose] public section

/-!
# Extensional tree map lemmas

This file contains lemmas about `Std.ExtTreeMap`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.ExtTreeMap

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} {cmp : α → α → Ordering} {t : ExtTreeMap α β cmp}

private theorem ext {t t' : ExtTreeMap α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

private theorem ext_iff {t t' : ExtTreeMap α β cmp} : t = t' ↔ t.inner = t'.inner :=
  ⟨fun h => h ▸ rfl, ext⟩

@[simp]
theorem isEmpty_iff {t : ExtTreeMap α β cmp} [TransCmp cmp] : t.isEmpty ↔ t = ∅ :=
  ExtDTreeMap.isEmpty_iff.trans ext_iff.symm

@[simp]
theorem isEmpty_eq_false_iff {t : ExtTreeMap α β cmp} [TransCmp cmp] : t.isEmpty = false ↔ ¬t = ∅ :=
  (Bool.not_eq_true _).symm.to_iff.trans (not_congr isEmpty_iff)

@[simp, grind =]
theorem isEmpty_empty : (∅ : ExtTreeMap α β cmp).isEmpty :=
  rfl

@[simp]
theorem empty_eq : ∅ = t ↔ t = ∅ := eq_comm

@[simp]
theorem insert_ne_empty [TransCmp cmp] {k : α} {v : β} :
    t.insert k v ≠ ∅ :=
  mt ext_iff.mp ExtDTreeMap.insert_ne_empty

theorem mem_iff_contains [TransCmp cmp] {k : α} : k ∈ t ↔ t.contains k :=
  ExtDTreeMap.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem [TransCmp cmp] {k : α} : t.contains k ↔ k ∈ t :=
  ExtDTreeMap.contains_iff_mem

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  ExtDTreeMap.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  ExtDTreeMap.mem_congr hab

@[simp, grind =]
theorem contains_empty [TransCmp cmp] {k : α} : (∅ : ExtTreeMap α β cmp).contains k = false :=
  ExtDTreeMap.contains_empty

@[simp]
theorem not_mem_empty [TransCmp cmp] {k : α} : k ∉ (∅ : ExtTreeMap α β cmp) :=
  ExtDTreeMap.not_mem_empty

theorem eq_empty_iff_forall_contains [TransCmp cmp] : t = ∅ ↔ ∀ a, t.contains a = false :=
  ext_iff.trans ExtDTreeMap.eq_empty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem [TransCmp cmp] : t = ∅ ↔ ∀ a, ¬a ∈ t :=
  ext_iff.trans ExtDTreeMap.eq_empty_iff_forall_not_mem

theorem ne_empty_of_mem [TransCmp cmp] {a : α} (h : a ∈ t) : t ≠ ∅ :=
  (not_congr eq_empty_iff_forall_not_mem).mpr fun h' => h' a h

@[simp]
theorem insert_eq_insert [TransCmp cmp] {p : α × β} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert [TransCmp cmp] {p : α × β} :
    Singleton.singleton p = (∅ : ExtTreeMap α β cmp).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [h : TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  ExtDTreeMap.contains_insert

@[simp, grind =]
theorem mem_insert [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  ExtDTreeMap.mem_insert

theorem contains_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).contains k :=
  ExtDTreeMap.contains_insert_self

theorem mem_insert_self [TransCmp cmp] {k : α} {v : β} :
    k ∈ t.insert k v :=
  ExtDTreeMap.mem_insert_self

theorem contains_of_contains_insert [TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  ExtDTreeMap.contains_of_contains_insert

theorem mem_of_mem_insert [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  ExtDTreeMap.mem_of_mem_insert

@[simp, grind =]
theorem size_empty : (∅ : ExtTreeMap α β cmp).size = 0 :=
  ExtDTreeMap.size_empty

theorem isEmpty_eq_size_beq_zero : t.isEmpty = (t.size == 0) :=
  ExtDTreeMap.isEmpty_eq_size_beq_zero

theorem eq_empty_iff_size_eq_zero [TransCmp cmp] : t = ∅ ↔ t.size = 0 :=
  ext_iff.trans ExtDTreeMap.eq_empty_iff_size_eq_zero

@[grind =] theorem size_insert [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  ExtDTreeMap.size_insert

theorem size_le_size_insert [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insert k v).size :=
  ExtDTreeMap.size_le_size_insert

theorem size_insert_le [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).size ≤ t.size + 1 :=
  ExtDTreeMap.size_insert_le

@[simp, grind =]
theorem erase_empty [TransCmp cmp] {k : α} : (∅ : ExtTreeMap α β cmp).erase k = ∅ :=
  ext <| ExtDTreeMap.erase_empty

@[simp]
theorem erase_eq_empty_iff [TransCmp cmp] {k : α} :
    t.erase k = ∅ ↔ t = ∅ ∨ (t.size = 1 ∧ k ∈ t) := by
  simpa only [ext_iff] using ExtDTreeMap.erase_eq_empty_iff

theorem eq_empty_iff_erase_eq_empty_and_not_mem [TransCmp cmp] (k : α) :
    t = ∅ ↔ t.erase k = ∅ ∧ ¬k ∈ t := by
  simpa only [ext_iff] using ExtDTreeMap.eq_empty_iff_erase_eq_empty_and_not_mem k

theorem ne_empty_of_erase_ne_empty [TransCmp cmp] {k : α} (h : t.erase k ≠ ∅) : t ≠ ∅ := by
  simp_all

@[simp, grind =]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  ExtDTreeMap.contains_erase

@[simp, grind =]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  ExtDTreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  ExtDTreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  ExtDTreeMap.mem_of_mem_erase

@[grind =] theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  ExtDTreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  ExtDTreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  ExtDTreeMap.size_le_size_erase

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsert k v).1 = t.contains k :=
  ExtDTreeMap.containsThenInsert_fst

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| ExtDTreeMap.containsThenInsert_snd

@[simp, grind =]
theorem containsThenInsertIfNew_fst [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  ExtDTreeMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsertIfNew_snd [TransCmp cmp] {k : α} {v : β} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| ExtDTreeMap.containsThenInsertIfNew_snd

@[simp, grind =] theorem get_eq_getElem [TransCmp cmp] {a : α} {h} : get t a h = t[a]'h := rfl
@[simp, grind =] theorem get?_eq_getElem? [TransCmp cmp] {a : α} : get? t a = t[a]? := rfl
@[simp, grind =] theorem get!_eq_getElem! [TransCmp cmp] [Inhabited β] {a : α} : get! t a = t[a]! := rfl

@[simp, grind =]
theorem getElem?_empty [TransCmp cmp] {a : α} :
    (∅ : ExtTreeMap α β cmp)[a]? = none :=
  ExtDTreeMap.Const.get?_empty (cmp := cmp) (a := a)

@[grind =]
theorem getElem?_insert [TransCmp cmp] {a k : α} {v : β} :
    (t.insert k v)[a]? = if cmp k a = .eq then some v else t[a]? :=
  ExtDTreeMap.Const.get?_insert

@[simp]
theorem getElem?_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v)[k]? = some v :=
  ExtDTreeMap.Const.get?_insert_self

theorem contains_eq_isSome_getElem? [TransCmp cmp] {a : α} :
    t.contains a = t[a]?.isSome :=
  ExtDTreeMap.Const.contains_eq_isSome_get?

@[simp]
theorem isSome_getElem?_eq_contains [TransCmp cmp] {a : α} :
    t[a]?.isSome = t.contains a :=
  contains_eq_isSome_getElem?.symm

theorem mem_iff_isSome_getElem? [TransCmp cmp] {a : α} :
    a ∈ t ↔ t[a]?.isSome :=
  ExtDTreeMap.Const.mem_iff_isSome_get?

@[simp]
theorem isSome_getElem?_iff_mem [TransCmp cmp] {a : α} :
    t[a]?.isSome ↔ a ∈ t :=
  mem_iff_isSome_getElem?.symm

theorem getElem?_eq_some_iff [TransCmp cmp] {k : α} {v : β} :
    t[k]? = some v ↔ ∃ h, t[k] = v :=
  ExtDTreeMap.Const.get?_eq_some_iff

theorem getElem?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t[a]? = none :=
  ExtDTreeMap.Const.get?_eq_none_of_contains_eq_false

theorem getElem?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t[a]? = none :=
  ExtDTreeMap.Const.get?_eq_none

@[grind =] theorem getElem?_erase [TransCmp cmp] {k a : α} :
    (t.erase k)[a]? = if cmp k a = .eq then none else t[a]? :=
  ExtDTreeMap.Const.get?_erase

@[simp]
theorem getElem?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k)[k]? = none :=
  ExtDTreeMap.Const.get?_erase_self

theorem getElem?_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) :
    t[a]? = t[b]? :=
  ExtDTreeMap.Const.get?_congr hab

@[grind =] theorem getElem_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insert k v)[a]'h₁ =
      if h₂ : cmp k a = .eq then v
      else t[a]'(mem_of_mem_insert h₁ h₂) :=
  ExtDTreeMap.Const.get_insert (h₁ := h₁)

@[simp]
theorem getElem_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v)[k]'mem_insert_self = v :=
  ExtDTreeMap.Const.get_insert_self

@[simp, grind =]
theorem getElem_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k)[a]'h' = t[a]'(mem_of_mem_erase h') :=
  ExtDTreeMap.Const.get_erase (h' := h')

theorem getElem?_eq_some_getElem [TransCmp cmp] {a : α} (h) :
    t[a]? = some (t[a]'h) :=
  ExtDTreeMap.Const.get?_eq_some_get h

theorem getElem_eq_get_getElem? [TransCmp cmp] {a : α} {h} :
    t[a] = t[a]?.get (mem_iff_isSome_getElem?.mp h) :=
  ExtDTreeMap.Const.get_eq_get_get? (h := h)

@[grind =] theorem get_getElem? [TransCmp cmp] {a : α} {h} :
    t[a]?.get h = t[a]'(mem_iff_isSome_getElem?.mpr h) :=
  ExtDTreeMap.Const.get_get?

theorem getElem_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) {h'} :
    t[a]'h' = t[b]'((mem_congr hab).mp h') :=
  ExtDTreeMap.Const.get_congr hab (h' := h')

@[simp, grind =]
theorem getElem!_empty [TransCmp cmp] [Inhabited β] {a : α} :
    (∅ : ExtTreeMap α β cmp)[a]! = default :=
  ExtDTreeMap.Const.get!_empty (cmp := cmp) (a := a)

@[grind =] theorem getElem!_insert [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    (t.insert k v)[a]! = if cmp k a = .eq then v else t[a]! :=
  ExtDTreeMap.Const.get!_insert

@[simp]
theorem getElem!_insert_self [TransCmp cmp] [Inhabited β] {k : α}
    {v : β} : (t.insert k v)[k]! = v :=
  ExtDTreeMap.Const.get!_insert_self

theorem getElem!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = false → t[a]! = default :=
  ExtDTreeMap.Const.get!_eq_default_of_contains_eq_false

theorem getElem!_eq_default [TransCmp cmp] [Inhabited β] {a : α} :
    ¬ a ∈ t → t[a]! = default :=
  ExtDTreeMap.Const.get!_eq_default

@[grind =] theorem getElem!_erase [TransCmp cmp] [Inhabited β] {k a : α} :
    (t.erase k)[a]! = if cmp k a = .eq then default else t[a]! :=
  ExtDTreeMap.Const.get!_erase

@[simp]
theorem getElem!_erase_self [TransCmp cmp] [Inhabited β] {k : α} :
    (t.erase k)[k]! = default :=
  ExtDTreeMap.Const.get!_erase_self

theorem getElem?_eq_some_getElem!_of_contains [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = true → t[a]? = some t[a]! :=
  ExtDTreeMap.Const.get?_eq_some_get!

theorem getElem?_eq_some_getElem! [TransCmp cmp] [Inhabited β] {a : α} :
    a ∈ t → t[a]? = some t[a]! :=
  ExtDTreeMap.Const.get?_eq_some_get!

theorem getElem!_eq_get!_getElem? [TransCmp cmp] [Inhabited β] {a : α} :
    t[a]! = t[a]?.get! :=
  ExtDTreeMap.Const.get!_eq_get!_get?

theorem getElem_eq_getElem! [TransCmp cmp] [Inhabited β] {a : α} {h} :
    t[a]'h = t[a]! :=
  ExtDTreeMap.Const.get_eq_get! (h := h)

theorem getElem!_congr [TransCmp cmp] [Inhabited β] {a b : α}
    (hab : cmp a b = .eq) : t[a]! = t[b]! :=
  ExtDTreeMap.Const.get!_congr hab

@[simp, grind =]
theorem getD_empty [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : ExtTreeMap α β cmp) a fallback = fallback :=
  ExtDTreeMap.Const.getD_empty

@[grind =] theorem getD_insert [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  ExtDTreeMap.Const.getD_insert

@[simp]
theorem getD_insert_self [TransCmp cmp] {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  ExtDTreeMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  ExtDTreeMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  ExtDTreeMap.Const.getD_eq_fallback

@[grind =] theorem getD_erase [TransCmp cmp] {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  ExtDTreeMap.Const.getD_erase

@[simp]
theorem getD_erase_self [TransCmp cmp] {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  ExtDTreeMap.Const.getD_erase_self

theorem getElem?_eq_some_getD_of_contains [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = true → t[a]? = some (getD t a fallback) :=
  ExtDTreeMap.Const.get?_eq_some_getD_of_contains

theorem getElem?_eq_some_getD [TransCmp cmp] {a : α} {fallback : β} :
    a ∈ t → t[a]? = some (getD t a fallback) :=
  ExtDTreeMap.Const.get?_eq_some_getD

theorem getD_eq_getD_getElem? [TransCmp cmp] {a : α} {fallback : β} :
    getD t a fallback = t[a]?.getD fallback :=
  ExtDTreeMap.Const.getD_eq_getD_get?

theorem getElem_eq_getD [TransCmp cmp] {a : α} (fallback : β) {h} :
    t[a]'h = getD t a fallback :=
  ExtDTreeMap.Const.get_eq_getD (h := h)

theorem getElem!_eq_getD_default [TransCmp cmp] [Inhabited β] {a : α} :
    t[a]! = getD t a default :=
  ExtDTreeMap.Const.get!_eq_getD_default

theorem getD_congr [TransCmp cmp] {a b : α} {fallback : β}
    (hab : cmp a b = .eq) : getD t a fallback = getD t b fallback :=
  ExtDTreeMap.Const.getD_congr hab

@[simp, grind =]
theorem getKey?_empty [TransCmp cmp] {a : α} : (∅ : ExtTreeMap α β cmp).getKey? a = none :=
  ExtDTreeMap.getKey?_empty

@[grind =] theorem getKey?_insert [TransCmp cmp] {a k : α} {v : β} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  ExtDTreeMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).getKey? k = some k :=
  ExtDTreeMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [TransCmp cmp] {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  ExtDTreeMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_getKey?_eq_contains [TransCmp cmp] {a : α} :
    (t.getKey? a).isSome = t.contains a :=
  contains_eq_isSome_getKey?.symm

theorem mem_iff_isSome_getKey? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  ExtDTreeMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [TransCmp cmp] {a : α} :
    (t.getKey? a).isSome ↔ a ∈ t :=
  mem_iff_isSome_getKey?.symm

theorem mem_of_getKey?_eq_some [TransCmp cmp] {k k' : α} :
    t.getKey? k = some k' → k' ∈ t :=
  ExtDTreeMap.mem_of_getKey?_eq_some

theorem getKey?_eq_some_iff [TransCmp cmp] {k k' : α} :
    getKey? t k = some k' ↔ ∃ h, getKey t k h = k' :=
  ExtDTreeMap.getKey?_eq_some_iff

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.getKey? a = none :=
  ExtDTreeMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  ExtDTreeMap.getKey?_eq_none

@[grind =] theorem getKey?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  ExtDTreeMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).getKey? k = none :=
  ExtDTreeMap.getKey?_erase_self

theorem compare_getKey?_self [TransCmp cmp] {k : α} :
    (t.getKey? k).all (cmp · k = .eq) :=
  ExtDTreeMap.compare_getKey?_self

theorem getKey?_congr [TransCmp cmp] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey? k = t.getKey? k' :=
  ExtDTreeMap.getKey?_congr h'

theorem getKey?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h' : t.contains k) :
    t.getKey? k = some k :=
  ExtDTreeMap.getKey?_eq_some_of_contains h'

theorem getKey?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.getKey? k = some k :=
  ExtDTreeMap.getKey?_eq_some_of_contains h'

@[grind =] theorem getKey_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h₁ h₂) :=
  ExtDTreeMap.getKey_insert

@[simp]
theorem getKey_insert_self [TransCmp cmp] {k : α} {v : β} :
    (t.insert k v).getKey k mem_insert_self = k :=
  ExtDTreeMap.getKey_insert_self

@[simp, grind =]
theorem getKey_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h') :=
  ExtDTreeMap.getKey_erase

theorem getKey?_eq_some_getKey [TransCmp cmp] {a : α} (h') :
    t.getKey? a = some (t.getKey a h') :=
  ExtDTreeMap.getKey?_eq_some_getKey h'

theorem getKey_eq_get_getKey? [TransCmp cmp] {a : α} {h} :
    t.getKey a h = (t.getKey? a).get (mem_iff_isSome_getKey?.mp h) :=
  ExtDTreeMap.getKey_eq_get_getKey?

@[simp, grind =]
theorem get_getKey? [TransCmp cmp] {a : α} {h} :
    (t.getKey? a).get h = t.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  ExtDTreeMap.get_getKey?

theorem compare_getKey_self [TransCmp cmp] {k : α} (h' : k ∈ t) :
    cmp (t.getKey k h') k = .eq :=
  ExtDTreeMap.compare_getKey_self h'

theorem getKey_congr [TransCmp cmp] {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h').mp h₁) :=
  ExtDTreeMap.getKey_congr h' h₁

@[simp, grind =]
theorem getKey_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.getKey k h' = k :=
  ExtDTreeMap.getKey_eq h'

@[simp, grind =]
theorem getKey!_empty [TransCmp cmp] {a : α} [Inhabited α] :
    (∅ : ExtTreeMap α β cmp).getKey! a = default :=
  ExtDTreeMap.getKey!_empty

@[grind =] theorem getKey!_insert [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β} : (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  ExtDTreeMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] {a : α}
    {b : β} : (t.insert a b).getKey! a = a :=
  ExtDTreeMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.getKey! a = default :=
  ExtDTreeMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  ExtDTreeMap.getKey!_eq_default

@[grind =] theorem getKey!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  ExtDTreeMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] {k : α} :
    (t.erase k).getKey! k = default :=
  ExtDTreeMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  ExtDTreeMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  ExtDTreeMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  ExtDTreeMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] {a : α} {h} :
    t.getKey a h = t.getKey! a :=
  ExtDTreeMap.getKey_eq_getKey!

theorem getKey!_congr [TransCmp cmp] [Inhabited α] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey! k = t.getKey! k' :=
  ExtDTreeMap.getKey!_congr h'

theorem getKey!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    (h' : t.contains k) :
    t.getKey! k = k :=
  ExtDTreeMap.getKey!_eq_of_contains h'

theorem getKey!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α} (h' : k ∈ t) :
    t.getKey! k = k :=
  ExtDTreeMap.getKey!_eq_of_mem h'

@[simp, grind =]
theorem getKeyD_empty [TransCmp cmp] {a : α} {fallback : α} :
    (∅ : ExtTreeMap α β cmp).getKeyD a fallback = fallback :=
  ExtDTreeMap.getKeyD_empty

@[grind =] theorem getKeyD_insert [TransCmp cmp] {k a fallback : α} {v : β} :
    (t.insert k v).getKeyD a fallback = if cmp k a = .eq then k else t.getKeyD a fallback :=
  ExtDTreeMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] {a fallback : α} {b : β} :
    (t.insert a b).getKeyD a fallback = a :=
  ExtDTreeMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  ExtDTreeMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  ExtDTreeMap.getKeyD_eq_fallback

@[grind =] theorem getKeyD_erase [TransCmp cmp] {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  ExtDTreeMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  ExtDTreeMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  ExtDTreeMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [TransCmp cmp] {a fallback : α} :
  a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  ExtDTreeMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  ExtDTreeMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [TransCmp cmp] {a fallback : α} {h} :
    t.getKey a h = t.getKeyD a fallback :=
  ExtDTreeMap.getKey_eq_getKeyD

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = t.getKeyD a default :=
  ExtDTreeMap.getKey!_eq_getKeyD_default

theorem getKeyD_congr [TransCmp cmp] {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getKeyD k fallback = t.getKeyD k' fallback :=
  ExtDTreeMap.getKeyD_congr h'

theorem getKeyD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α}
    (h' : t.contains k) :
    t.getKeyD k fallback = k :=
  ExtDTreeMap.getKeyD_eq_of_contains h'

theorem getKeyD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : k ∈ t) :
    t.getKeyD k fallback = k :=
  ExtDTreeMap.getKeyD_eq_of_contains h'

@[simp]
theorem insertIfNew_ne_empty [TransCmp cmp] {k : α} {v : β} :
    ¬t.insertIfNew k v = ∅ :=
  mt ext_iff.mp ExtDTreeMap.insertIfNew_ne_empty

@[simp, grind =]
theorem contains_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  ExtDTreeMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  ExtDTreeMap.mem_insertIfNew

@[simp]
theorem contains_insertIfNew_self [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).contains k :=
  ExtDTreeMap.contains_insertIfNew_self

@[simp]
theorem mem_insertIfNew_self [TransCmp cmp] {k : α} {v : β} :
    k ∈ t.insertIfNew k v :=
  ExtDTreeMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  ExtDTreeMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  ExtDTreeMap.contains_of_contains_insertIfNew

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] {k a : α} {v : β} :
    a ∈ (t.insertIfNew k v) → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  ExtDTreeMap.mem_of_mem_insertIfNew'

@[grind =] theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  ExtDTreeMap.size_insertIfNew

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β} :
    t.size ≤ (t.insertIfNew k v).size :=
  ExtDTreeMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  ExtDTreeMap.size_insertIfNew_le

@[grind =] theorem getElem?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]? =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else t[a]? :=
  ExtDTreeMap.Const.get?_insertIfNew

@[grind =] theorem getElem_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v)[a]'h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]'(mem_of_mem_insertIfNew' h₁ h₂) :=
  ExtDTreeMap.Const.get_insertIfNew (h₁ := h₁)

@[grind =] theorem getElem!_insertIfNew [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]! = if cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]! :=
  ExtDTreeMap.Const.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  ExtDTreeMap.Const.getD_insertIfNew

@[grind =] theorem getKey?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  ExtDTreeMap.getKey?_insertIfNew

@[grind =] theorem getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂) :=
  ExtDTreeMap.getKey_insertIfNew

@[grind =] theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  ExtDTreeMap.getKey!_insertIfNew

@[grind =] theorem getKeyD_insertIfNew [TransCmp cmp] {k a fallback : α}
    {v : β} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  ExtDTreeMap.getKeyD_insertIfNew

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = t[k]? :=
  ExtDTreeMap.Const.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| ExtDTreeMap.Const.getThenInsertIfNew?_snd

instance [TransCmp cmp] : LawfulGetElem (ExtTreeMap α β cmp) α β (fun m a => a ∈ m) where
  getElem?_def m a _ := by
    split
    · exact getElem?_eq_some_getElem _
    · exact getElem?_eq_none ‹_›
  getElem!_def m a := by
    rw [getElem!_eq_get!_getElem?]
    split <;> simp_all

@[simp, grind =]
theorem length_keys [TransCmp cmp] :
    t.keys.length = t.size :=
  ExtDTreeMap.length_keys

@[simp, grind =]
theorem isEmpty_keys [TransCmp cmp] : t.keys.isEmpty = t.isEmpty :=
  ExtDTreeMap.isEmpty_keys

@[simp]
theorem keys_eq_nil_iff [TransCmp cmp] : t.keys = [] ↔ t = ∅ :=
  ExtDTreeMap.keys_eq_nil_iff.trans ext_iff.symm

@[simp, grind =]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  ExtDTreeMap.contains_keys

@[simp, grind =]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  ExtDTreeMap.mem_keys

theorem mem_of_mem_keys [TransCmp cmp] {k : α} :
    k ∈ t.keys → k ∈ t :=
  ExtDTreeMap.mem_of_mem_keys

theorem distinct_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  ExtDTreeMap.distinct_keys

theorem nodup_keys [TransCmp cmp] :
    t.keys.Nodup :=
  t.distinct_keys.imp Std.ReflCmp.ne_of_cmp_ne_eq

theorem ordered_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => cmp a b = .lt) :=
  ExtDTreeMap.ordered_keys

@[simp, grind _=_]
theorem map_fst_toList_eq_keys [TransCmp cmp] :
    (toList t).map Prod.fst = t.keys :=
  ExtDTreeMap.Const.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList [TransCmp cmp] :
    (toList t).length = t.size :=
  ExtDTreeMap.Const.length_toList

@[simp]
theorem isEmpty_toList [TransCmp cmp] :
    t.toList.isEmpty = t.isEmpty :=
  ExtDTreeMap.Const.isEmpty_toList

@[simp]
theorem toList_eq_nil_iff [TransCmp cmp] :
    t.toList = [] ↔ t = ∅ :=
  ExtDTreeMap.Const.toList_eq_nil_iff.trans ext_iff.symm

@[simp, grind =]
theorem mem_toList_iff_getElem?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t[k]? = some v :=
  ExtDTreeMap.Const.mem_toList_iff_get?_eq_some

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some [TransCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ t[k]? = some v :=
  ExtDTreeMap.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some

theorem getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] {k : α} {v : β} :
    t[k]? = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  ExtDTreeMap.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some [TransCmp cmp] {k k' : α}
    {v : β} :
    t.toList.find? (cmp ·.1 k == .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ t[k]? = some v :=
  ExtDTreeMap.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  ExtDTreeMap.Const.find?_toList_eq_none_iff_contains_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  ExtDTreeMap.Const.find?_toList_eq_none_iff_not_mem

theorem distinct_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  ExtDTreeMap.Const.distinct_keys_toList

theorem ordered_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  ExtDTreeMap.Const.ordered_keys_toList

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init :=
  ExtDTreeMap.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList [TransCmp cmp] {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init :=
  ExtDTreeMap.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → β → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init :=
  ExtDTreeMap.Const.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList [TransCmp cmp] {f : α → β → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init :=
  ExtDTreeMap.Const.foldr_eq_foldr_toList

@[simp, grind =]
theorem forM_eq_forM [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    ForM.forM t f = ForM.forM t.toList f :=
  ExtDTreeMap.Const.forMUncurried_eq_forM_toList (f := f)

@[simp, grind =]
theorem forIn_eq_forIn [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init (fun a d => f a.1 a.2 d) := rfl

theorem forIn_eq_forIn_toList [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α × β → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  ExtDTreeMap.Const.forInUncurried_eq_forIn_toList

theorem foldlM_eq_foldlM_keys [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init :=
  ExtDTreeMap.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys [TransCmp cmp] {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init :=
  ExtDTreeMap.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init :=
  ExtDTreeMap.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys [TransCmp cmp] {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init :=
  ExtDTreeMap.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t (fun a => f a.1) = t.keys.forM f :=
  ExtDTreeMap.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init (fun a d => f a.1 d) = ForIn.forIn t.keys init f :=
  ExtDTreeMap.forIn_eq_forIn_keys

end monadic

@[simp, grind =]
theorem insertMany_nil [TransCmp cmp] :
    t.insertMany [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton [TransCmp cmp] {k : α} {v : β} :
    t.insertMany [⟨k, v⟩] = t.insert k v :=
  rfl

@[grind _=_] theorem insertMany_cons [TransCmp cmp] {l : List (α × β)} {k : α} {v : β} :
    t.insertMany (⟨k, v⟩ :: l) = (t.insert k v).insertMany l :=
  ext <| ExtDTreeMap.Const.insertMany_cons

@[grind _=_] theorem insertMany_append [TransCmp cmp] {l₁ l₂ : List (α × β)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  ExtDTreeMap.Const.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Prod.fst).contains k :=
  ExtDTreeMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    k ∈ t.insertMany l → (l.map Prod.fst).contains k = false → k ∈ t :=
  ExtDTreeMap.Const.mem_of_mem_insertMany_list

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k :=
  ExtDTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKey? k' = some k :=
  ExtDTreeMap.Const.getKey?_insertMany_list_of_mem k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h' contains_eq_false) :=
  ExtDTreeMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k :=
  ExtDTreeMap.Const.getKey_insertMany_list_of_mem k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k :=
  ExtDTreeMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKey! k' = k :=
  ExtDTreeMap.Const.getKey!_insertMany_list_of_mem k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback :=
  ExtDTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (t.insertMany l).getKeyD k' fallback = k :=
  ExtDTreeMap.Const.getKeyD_insertMany_list_of_mem k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length :=
  ExtDTreeMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    t.size ≤ (t.insertMany l).size :=
  ExtDTreeMap.Const.size_le_size_insertMany_list

grind_pattern size_le_size_insertMany_list => (t.insertMany l).size

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List (α × β)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  ExtDTreeMap.Const.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (t.insertMany l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  ExtDTreeMap.Const.isEmpty_insertMany_list

theorem insertMany_list_eq_empty_iff [TransCmp cmp] {l : List (α × β)} :
    t.insertMany l = ∅ ↔ t = ∅ ∧ l = [] := by
  simpa only [ext_iff] using ExtDTreeMap.Const.insertMany_list_eq_empty_iff

theorem getElem?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l)[k]? = t[k]? :=
  ExtDTreeMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem?_insertMany_list_of_mem [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l)[k']? = some v :=
  ExtDTreeMap.Const.get?_insertMany_list_of_mem k_eq distinct mem

@[grind =] theorem getElem?_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    (t.insertMany l)[k]? =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).or (t[k]?) :=
  ExtDTreeMap.Const.get?_insertMany_list

theorem getElem_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains : (l.map Prod.fst).contains k = false)
    {h'} :
    (t.insertMany l)[k]'h' =
    t[k]'(mem_of_mem_insertMany_list h' contains) :=
  ExtDTreeMap.Const.get_insertMany_list_of_contains_eq_false contains (h' := h')

theorem getElem_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l)[(k')]'h' = v :=
  ExtDTreeMap.Const.get_insertMany_list_of_mem k_eq distinct mem (h' := h')

theorem getElem!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l)[k]! = t[k]! :=
  ExtDTreeMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getElem!_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l)[k']! = v :=
  ExtDTreeMap.Const.get!_insertMany_list_of_mem k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback :=
  ExtDTreeMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = v :=
  ExtDTreeMap.Const.getD_insertMany_list_of_mem k_eq distinct mem

section Unit

variable {t : ExtTreeMap α Unit cmp}

@[simp]
theorem insertManyIfNewUnit_nil [TransCmp cmp] :
    insertManyIfNewUnit t [] = t :=
  rfl

@[simp]
theorem insertManyIfNewUnit_list_singleton [TransCmp cmp] {k : α} :
    insertManyIfNewUnit t [k] = t.insertIfNew k () :=
  rfl

theorem insertManyIfNewUnit_cons [TransCmp cmp] {l : List α} {k : α} :
    insertManyIfNewUnit t (k :: l) = insertManyIfNewUnit (t.insertIfNew k ()) l :=
  ext <| ExtDTreeMap.Const.insertManyIfNewUnit_cons

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) :=
  ExtDTreeMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k :=
  ExtDTreeMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t :=
  ExtDTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKey? (insertManyIfNewUnit t l) k = none :=
  ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (insertManyIfNewUnit t l) k' = some k :=
  ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} (mem : k ∈ t) :
    getKey? (insertManyIfNewUnit t l) k = getKey? t k :=
  ExtDTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_mem mem

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains :=
  ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_mem contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} (not_mem : ¬ k ∈ t)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey (insertManyIfNewUnit t l) k' h' = k :=
  ExtDTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit t l) k = default :=
  ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit t l) k' = k :=
  ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k : α} (mem : k ∈ t) :
    getKey! (insertManyIfNewUnit t l) k = getKey! t k :=
  ExtDTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_mem mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getKeyD (insertManyIfNewUnit t l) k fallback = fallback :=
  ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit t l) k' fallback = k :=
  ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq not_mem distinct mem

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k fallback : α} (mem : k ∈ t) :
    getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback :=
  ExtDTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem mem

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length :=
  ExtDTreeMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp]
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size :=
  ExtDTreeMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp]
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length :=
  ExtDTreeMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  ExtDTreeMap.Const.isEmpty_insertManyIfNewUnit_list

@[simp]
theorem insertManyIfNewUnit_list_eq_empty_iff [TransCmp cmp] {l : List α} :
    insertManyIfNewUnit t l = ∅ ↔ t = ∅ ∧ l = [] := by
  simpa only [ext_iff] using ExtDTreeMap.Const.insertManyIfNewUnit_list_eq_empty_iff

@[simp]
theorem getElem?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l)[k]? = if k ∈ t ∨ l.contains k then some () else none :=
  ExtDTreeMap.Const.get?_insertManyIfNewUnit_list

@[simp]
theorem getElem_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} {k : α} {h'} :
    (insertManyIfNewUnit t l)[k]'h' = () :=
  rfl

@[simp]
theorem getElem!_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} {k : α} :
    (insertManyIfNewUnit t l)[k]! = () :=
  rfl

@[simp]
theorem getD_insertManyIfNewUnit_list [TransCmp cmp]
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit t l) k fallback = () :=
  rfl

end Unit

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List (α × β)) cmp = ∅ := by
  rfl

@[simp, grind =]
theorem ofList_singleton [TransCmp cmp] {k : α} {v : β} :
    ofList [⟨k, v⟩] cmp = (∅ : ExtTreeMap α β cmp).insert k v := by
  rfl

@[grind _=_] theorem ofList_cons [TransCmp cmp] {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : ExtTreeMap α β cmp).insert k v) tl :=
  ext ExtDTreeMap.Const.ofList_cons

theorem ofList_eq_insertMany_empty [TransCmp cmp] {l : List (α × β)} :
    ofList l cmp = insertMany (∅ : ExtTreeMap α β cmp) l :=
  ext ExtDTreeMap.Const.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  ExtDTreeMap.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Prod.fst).contains k :=
  ExtDTreeMap.Const.mem_ofList

theorem getElem?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp)[k]? = none :=
  ExtDTreeMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem getElem?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp)[k']? = some v :=
  ExtDTreeMap.Const.get?_ofList_of_mem k_eq distinct mem

theorem getElem_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l cmp)[(k')]'h = v :=
  ExtDTreeMap.Const.get_ofList_of_mem k_eq distinct mem (h := h)

theorem getElem!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp)[k]! = default :=
  ExtDTreeMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem getElem!_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp)[k']! = v :=
  ExtDTreeMap.Const.get!_ofList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  ExtDTreeMap.Const.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l cmp) k' fallback = v :=
  ExtDTreeMap.Const.getD_ofList_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  ExtDTreeMap.Const.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey? k' = some k :=
  ExtDTreeMap.Const.getKey?_ofList_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  ExtDTreeMap.Const.getKey_ofList_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  ExtDTreeMap.Const.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey! k' = k :=
  ExtDTreeMap.Const.getKey!_ofList_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  ExtDTreeMap.Const.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  ExtDTreeMap.Const.getKeyD_ofList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  ExtDTreeMap.Const.size_ofList distinct

theorem size_ofList_le [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).size ≤ l.length :=
  ExtDTreeMap.Const.size_ofList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp]
theorem ofList_eq_empty_iff [TransCmp cmp] {l : List (α × β)} :
    ofList l cmp = ∅ ↔ l = [] :=
  ext_iff.trans ExtDTreeMap.Const.ofList_eq_empty_iff

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) cmp =
      (∅ : ExtTreeMap α Unit cmp) :=
  rfl

@[simp]
theorem unitOfList_singleton [TransCmp cmp] {k : α} :
    unitOfList [k] cmp = (∅ : ExtTreeMap α Unit cmp).insertIfNew k () :=
  rfl

theorem unitOfList_cons [TransCmp cmp] {hd : α} {tl : List α} :
    unitOfList (hd :: tl) cmp =
      insertManyIfNewUnit ((∅ : ExtTreeMap α Unit cmp).insertIfNew hd ()) tl :=
  ext ExtDTreeMap.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp).contains k = l.contains k :=
  ExtDTreeMap.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ unitOfList l cmp ↔ l.contains k := by
  simp [mem_iff_contains]

theorem getKey?_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l cmp) k = none :=
  ExtDTreeMap.Const.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (unitOfList l cmp) k' = some k :=
  ExtDTreeMap.Const.getKey?_unitOfList_of_mem k_eq distinct mem

theorem getKey_unitOfList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l cmp) k' h' = k :=
  ExtDTreeMap.Const.getKey_unitOfList_of_mem k_eq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l cmp) k = default :=
  ExtDTreeMap.Const.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKey! (unitOfList l cmp) k' = k :=
  ExtDTreeMap.Const.getKey!_unitOfList_of_mem k_eq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l cmp) k fallback = fallback :=
  ExtDTreeMap.Const.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKeyD (unitOfList l cmp) k' fallback = k :=
  ExtDTreeMap.Const.getKeyD_unitOfList_of_mem k_eq distinct mem

theorem size_unitOfList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (unitOfList l cmp).size = l.length :=
  ExtDTreeMap.Const.size_unitOfList distinct

theorem size_unitOfList_le [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).size ≤ l.length :=
  ExtDTreeMap.Const.size_unitOfList_le

@[simp]
theorem unitOfList_eq_empty_iff [TransCmp cmp] {l : List α} :
    unitOfList l cmp = ∅ ↔ l = [] :=
  ext_iff.trans ExtDTreeMap.Const.unitOfList_eq_empty_iff

@[simp]
theorem getElem?_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp)[k]? = if l.contains k then some () else none :=
  ExtDTreeMap.Const.get?_unitOfList

@[simp]
theorem getElem_unitOfList [TransCmp cmp] {l : List α} {k : α} {h} :
    (unitOfList l cmp)[k]'h = () :=
  rfl

@[simp]
theorem getElem!_unitOfList [TransCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp)[k]! = () :=
  rfl

@[simp]
theorem getD_unitOfList [TransCmp cmp] {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l cmp) k fallback = () :=
  rfl

section Union

variable {t₁ t₂ : ExtTreeMap α β cmp}

@[simp]
theorem union_eq [TransCmp cmp] : t₁.union t₂ = t₁ ∪ t₂ := by
  simp only [Union.union]

/- contains -/
@[simp]
theorem contains_union [TransCmp cmp]
    {k : α} :
    (t₁ ∪ t₂).contains k = (t₁.contains k || t₂.contains k) :=
  ExtDTreeMap.contains_union

/- mem -/
theorem mem_union_of_left [TransCmp cmp] {k : α} :
    k ∈ t₁ → k ∈ t₁ ∪ t₂ :=
  ExtDTreeMap.mem_union_of_left

theorem mem_union_of_right [TransCmp cmp] {k : α} :
    k ∈ t₂ → k ∈ t₁ ∪ t₂ :=
   ExtDTreeMap.mem_union_of_right

@[simp]
theorem mem_union_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ ↔ k ∈ t₁ ∨ k ∈ t₂ :=
  ExtDTreeMap.mem_union_iff

theorem mem_of_mem_union_of_not_mem_right [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₂ → k ∈ t₁ :=
  ExtDTreeMap.mem_of_mem_union_of_not_mem_right

theorem mem_of_mem_union_of_not_mem_left [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₁ → k ∈ t₂ :=
  ExtDTreeMap.mem_of_mem_union_of_not_mem_left

theorem union_insert_right_eq_insert_union [TransCmp cmp] {p : (_ : α) × β} :
    (t₁ ∪ (t₂.insert p.fst p.snd)) = ((t₁ ∪ t₂).insert p.fst p.snd) := by
  simp only [Union.union]
  simp only [union, insert, ExtDTreeMap.union_eq, mk.injEq]
  exact ExtDTreeMap.union_insert_right_eq_insert_union

/- getElem? -/
theorem getElem?_union [TransCmp cmp] {k : α} :
    (t₁ ∪ t₂)[k]? = (t₂[k]?).or (t₁[k]?) :=
  ExtDTreeMap.Const.get?_union

theorem getElem?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂)[k]? = t₂[k]? :=
  ExtDTreeMap.Const.get?_union_of_not_mem_left not_mem

theorem getElem?_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂)[k]? = t₁[k]? :=
  ExtDTreeMap.Const.get?_union_of_not_mem_right not_mem

/- get? -/
@[deprecated getElem?_union (since := "2025-12-10")]
theorem get?_union [TransCmp cmp] {k : α} :
    (t₁ ∪ t₂).get? k = (t₂.get? k).or (t₁.get? k) :=
  ExtDTreeMap.Const.get?_union

@[deprecated getElem?_union_of_not_mem_left (since := "2025-12-10")]
theorem get?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get? k = t₂.get? k :=
  ExtDTreeMap.Const.get?_union_of_not_mem_left not_mem

@[deprecated getElem?_union_of_not_mem_right (since := "2025-12-10")]
theorem get?_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).get? k = t₁.get? k :=
  ExtDTreeMap.Const.get?_union_of_not_mem_right not_mem

/- getElem -/
theorem getElem_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)[k]'(mem_union_of_right mem) = t₂[k]'mem :=
  ExtDTreeMap.Const.get_union_of_mem_right mem

theorem getElem_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂)[k]'h' = t₂[k]'(mem_of_mem_union_of_not_mem_left h' not_mem) :=
  ExtDTreeMap.Const.get_union_of_not_mem_left not_mem (h' := h')

/- get -/
@[deprecated getElem_union_of_mem_right (since := "2025-12-10")]
theorem get_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).get k (mem_union_of_right mem) = t₂.get k mem :=
  ExtDTreeMap.Const.get_union_of_mem_right mem

@[deprecated getElem_union_of_not_mem_left (since := "2025-12-10")]
theorem get_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).get k h' = t₂.get k (mem_of_mem_union_of_not_mem_left h' not_mem) :=
  ExtDTreeMap.Const.get_union_of_not_mem_left not_mem

/- getD -/
theorem getD_union [TransCmp cmp] {k : α} {fallback : β} :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k (t₁.getD k fallback) :=
  ExtDTreeMap.Const.getD_union

theorem getD_union_of_not_mem_left [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k fallback :=
  ExtDTreeMap.Const.getD_union_of_not_mem_left not_mem

theorem getD_union_of_not_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback :=
  ExtDTreeMap.Const.getD_union_of_not_mem_right not_mem

/- getElem! -/
theorem getElem!_union [TransCmp cmp] {k : α} [Inhabited β] :
    (t₁ ∪ t₂)[k]! = t₂.getD k (t₁[k]!) :=
  ExtDTreeMap.Const.get!_union

theorem getElem!_union_of_not_mem_left [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂)[k]! = t₂[k]! :=
  ExtDTreeMap.Const.get!_union_of_not_mem_left not_mem

theorem getElem!_union_of_not_mem_right [TransCmp cmp] {k : α} [Inhabited β] (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂)[k]! = t₁[k]! :=
  ExtDTreeMap.Const.get!_union_of_not_mem_right not_mem

/- get! -/
@[deprecated getElem!_union (since := "2025-12-10")]
theorem get!_union [TransCmp cmp] {k : α} [Inhabited β] :
    (t₁ ∪ t₂).get! k = t₂.getD k (t₁.get! k) :=
  ExtDTreeMap.Const.get!_union

@[deprecated getElem!_union_of_not_mem_left (since := "2025-12-10")]
theorem get!_union_of_not_mem_left [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get! k = t₂.get! k :=
  ExtDTreeMap.Const.get!_union_of_not_mem_left not_mem

@[deprecated getElem!_union_of_not_mem_right (since := "2025-12-10")]
theorem get!_union_of_not_mem_right [TransCmp cmp] {k : α} [Inhabited β] (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂).get! k = t₁.get! k :=
  ExtDTreeMap.Const.get!_union_of_not_mem_right not_mem

/- getKey? -/
theorem getKey?_union [TransCmp cmp] {k : α} :
    (t₁ ∪ t₂).getKey? k = (t₂.getKey? k).or (t₁.getKey? k) :=
  ExtDTreeMap.getKey?_union

theorem getKey?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKey? k = t₂.getKey? k :=
  ExtDTreeMap.getKey?_union_of_not_mem_left not_mem

/- getKey -/
theorem getKey_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).getKey k (mem_union_of_right mem) = t₂.getKey k mem :=
  ExtDTreeMap.getKey_union_of_mem_right mem

theorem getKey_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).getKey k h' = t₂.getKey k (mem_of_mem_union_of_not_mem_left h' not_mem) :=
  ExtDTreeMap.getKey_union_of_not_mem_left not_mem

theorem getKey_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂).getKey k h' = t₁.getKey k (mem_of_mem_union_of_not_mem_right h' not_mem) :=
  ExtDTreeMap.getKey_union_of_not_mem_right not_mem

/- getKeyD -/
theorem getKeyD_union [TransCmp cmp] {k fallback : α} :
    (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k (t₁.getKeyD k fallback) :=
  ExtDTreeMap.getKeyD_union

theorem getKeyD_union_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k fallback :=
  ExtDTreeMap.getKeyD_union_of_not_mem_left not_mem

theorem getKeyD_union_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKeyD k fallback = t₁.getKeyD k fallback :=
  ExtDTreeMap.getKeyD_union_of_not_mem_right not_mem

/- getKey! -/
theorem getKey!_union [TransCmp cmp] [Inhabited α] {k : α} : (t₁ ∪ t₂).getKey! k = t₂.getKeyD k (t₁.getKey! k) :=
  ExtDTreeMap.getKey!_union

theorem getKey!_union_of_not_mem_left [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKey! k = t₂.getKey! k :=
  ExtDTreeMap.getKey!_union_of_not_mem_left not_mem

theorem getKey!_union_of_not_mem_right [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKey! k = t₁.getKey! k :=
  ExtDTreeMap.getKey!_union_of_not_mem_right not_mem

/- size -/
theorem size_union_of_not_mem [TransCmp cmp] :
    (∀ (a : α), a ∈ t₁ → ¬a ∈ t₂) →
    (t₁ ∪ t₂).size = t₁.size + t₂.size :=
  ExtDTreeMap.size_union_of_not_mem

theorem size_left_le_size_union [TransCmp cmp] : t₁.size ≤ (t₁ ∪ t₂).size :=
  ExtDTreeMap.size_left_le_size_union

theorem size_right_le_size_union [TransCmp cmp] :
    t₂.size ≤ (t₁ ∪ t₂).size :=
  ExtDTreeMap.size_right_le_size_union

theorem size_union_le_size_add_size [TransCmp cmp] :
    (t₁ ∪ t₂).size ≤ t₁.size + t₂.size :=
  ExtDTreeMap.size_union_le_size_add_size

/- isEmpty -/
@[simp]
theorem isEmpty_union [TransCmp cmp] :
    (t₁ ∪ t₂).isEmpty = (t₁.isEmpty && t₂.isEmpty) :=
  ExtDTreeMap.isEmpty_union

end Union

section Inter

variable {t₁ t₂ : ExtTreeMap α β cmp}

@[simp]
theorem inter_eq [TransCmp cmp] : t₁.inter t₂ = t₁ ∩ t₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).contains k = (t₁.contains k && t₂.contains k) :=
  ExtDTreeMap.contains_inter

/- mem -/
@[simp]
theorem mem_inter_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ :=
  ExtDTreeMap.mem_inter_iff

theorem not_mem_inter_of_not_mem_left [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ ∩ t₂ :=
  ExtDTreeMap.not_mem_inter_of_not_mem_left not_mem

theorem not_mem_inter_of_not_mem_right [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₂) :
    k ∉ t₁ ∩ t₂ :=
  ExtDTreeMap.not_mem_inter_of_not_mem_right not_mem

/- getElem? -/
theorem getElem?_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂)[k]? = if k ∈ t₂ then t₁[k]? else none :=
  ExtDTreeMap.Const.get?_inter

theorem getElem?_inter_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂)[k]? = t₁[k]? :=
  ExtDTreeMap.Const.get?_inter_of_mem_right mem

theorem getElem?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂)[k]? = none :=
  ExtDTreeMap.Const.get?_inter_of_not_mem_left not_mem

theorem getElem?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂)[k]? = none :=
  ExtDTreeMap.Const.get?_inter_of_not_mem_right not_mem

/- get? -/
@[deprecated getElem?_inter (since := "2025-12-10")]
theorem get?_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).get? k = if k ∈ t₂ then t₁.get? k else none :=
  ExtDTreeMap.Const.get?_inter

@[deprecated getElem?_inter_of_mem_right (since := "2025-12-10")]
theorem get?_inter_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get? k = t₁.get? k :=
  ExtDTreeMap.Const.get?_inter_of_mem_right mem

@[deprecated getElem?_inter_of_not_mem_left (since := "2025-12-10")]
theorem get?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get? k = none :=
  ExtDTreeMap.Const.get?_inter_of_not_mem_left not_mem

@[deprecated getElem?_inter_of_not_mem_right (since := "2025-12-10")]
theorem get?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get? k = none :=
  ExtDTreeMap.Const.get?_inter_of_not_mem_right not_mem

/- getElem -/
@[simp]
theorem getElem_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂)[k]'h_mem = t₁[k]'(mem_inter_iff.1 h_mem).1 :=
  ExtDTreeMap.Const.get_inter (h_mem := h_mem)

/- get -/
@[deprecated getElem_inter (since := "2025-12-10")]
theorem get_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).get k h_mem = t₁.get k (mem_inter_iff.1 h_mem).1 :=
  ExtDTreeMap.Const.get_inter

/- getD -/
theorem getD_inter [TransCmp cmp] {k : α} {fallback : β} :
    (t₁ ∩ t₂).getD k fallback =
    if k ∈ t₂ then t₁.getD k fallback else fallback :=
  ExtDTreeMap.Const.getD_inter

theorem getD_inter_of_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getD k fallback = t₁.getD k fallback :=
  ExtDTreeMap.Const.getD_inter_of_mem_right mem

theorem getD_inter_of_not_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  ExtDTreeMap.Const.getD_inter_of_not_mem_right not_mem

theorem getD_inter_of_not_mem_left [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getD k fallback = fallback :=
  ExtDTreeMap.Const.getD_inter_of_not_mem_left not_mem

/- getElem! -/
theorem getElem!_inter [TransCmp cmp] {k : α} [Inhabited β] :
    (t₁ ∩ t₂)[k]! = if k ∈ t₂ then t₁[k]! else default :=
  ExtDTreeMap.Const.get!_inter

theorem getElem!_inter_of_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (mem : k ∈ t₂) :
    (t₁ ∩ t₂)[k]! = t₁[k]! :=
  ExtDTreeMap.Const.get!_inter_of_mem_right mem

theorem getElem!_inter_of_not_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂)[k]! = default :=
  ExtDTreeMap.Const.get!_inter_of_not_mem_right not_mem

theorem getElem!_inter_of_not_mem_left [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂)[k]! = default :=
  ExtDTreeMap.Const.get!_inter_of_not_mem_left not_mem

/- get! -/
@[deprecated getElem!_inter (since := "2025-12-10")]
theorem get!_inter [TransCmp cmp] {k : α} [Inhabited β] :
    (t₁ ∩ t₂).get! k = if k ∈ t₂ then t₁.get! k else default :=
  ExtDTreeMap.Const.get!_inter

@[deprecated getElem!_inter_of_mem_right (since := "2025-12-10")]
theorem get!_inter_of_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (mem : k ∈ t₂) :
    (t₁ ∩ t₂).get! k = t₁.get! k :=
  ExtDTreeMap.Const.get!_inter_of_mem_right mem

@[deprecated getElem!_inter_of_not_mem_right (since := "2025-12-10")]
theorem get!_inter_of_not_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).get! k = default :=
  ExtDTreeMap.Const.get!_inter_of_not_mem_right not_mem

@[deprecated getElem!_inter_of_not_mem_left (since := "2025-12-10")]
theorem get!_inter_of_not_mem_left [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).get! k = default :=
  ExtDTreeMap.Const.get!_inter_of_not_mem_left not_mem

/- getKey? -/
theorem getKey?_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).getKey? k =
    if k ∈ t₂ then t₁.getKey? k else none :=
  ExtDTreeMap.getKey?_inter

theorem getKey?_inter_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getKey? k = t₁.getKey? k :=
  ExtDTreeMap.getKey?_inter_of_mem_right mem

theorem getKey?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getKey? k = none :=
  ExtDTreeMap.getKey?_inter_of_not_mem_right not_mem

theorem getKey?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getKey? k = none :=
  ExtDTreeMap.getKey?_inter_of_not_mem_left not_mem

/- getKey -/
@[simp]
theorem getKey_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).getKey k h_mem =
    t₁.getKey k (mem_inter_iff.1 h_mem).1 :=
  ExtDTreeMap.getKey_inter

/- getKeyD -/
theorem getKeyD_inter [TransCmp cmp] {k fallback : α} :
    (t₁ ∩ t₂).getKeyD k fallback =
    if k ∈ t₂ then t₁.getKeyD k fallback else fallback :=
  ExtDTreeMap.getKeyD_inter

theorem getKeyD_inter_of_mem_right [TransCmp cmp]
    {k fallback : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getKeyD k fallback = t₁.getKeyD k fallback :=
  ExtDTreeMap.getKeyD_inter_of_mem_right mem

theorem getKeyD_inter_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getKeyD k fallback = fallback :=
  ExtDTreeMap.getKeyD_inter_of_not_mem_right not_mem

theorem getKeyD_inter_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getKeyD k fallback = fallback :=
  ExtDTreeMap.getKeyD_inter_of_not_mem_left not_mem

/- getKey! -/
theorem getKey!_inter [TransCmp cmp] [Inhabited α] {k : α} :
    (t₁ ∩ t₂).getKey! k =
    if k ∈ t₂ then t₁.getKey! k else default :=
  ExtDTreeMap.getKey!_inter

theorem getKey!_inter_of_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∩ t₂).getKey! k = t₁.getKey! k :=
  ExtDTreeMap.getKey!_inter_of_mem_right mem

theorem getKey!_inter_of_not_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ ∩ t₂).getKey! k = default :=
  ExtDTreeMap.getKey!_inter_of_not_mem_right not_mem

theorem getKey!_inter_of_not_mem_left [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ ∩ t₂).getKey! k = default :=
  ExtDTreeMap.getKey!_inter_of_not_mem_left not_mem

/- size -/
theorem size_inter_le_size_left [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₁.size :=
  ExtDTreeMap.size_inter_le_size_left

theorem size_inter_le_size_right [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₂.size :=
  ExtDTreeMap.size_inter_le_size_right

theorem size_inter_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∈ t₂) :
    (t₁ ∩ t₂).size = t₁.size :=
  ExtDTreeMap.size_inter_eq_size_left h

theorem size_inter_eq_size_right [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₂ → a ∈ t₁) :
    (t₁ ∩ t₂).size = t₂.size :=
  ExtDTreeMap.size_inter_eq_size_right h

theorem size_add_size_eq_size_union_add_size_inter [TransCmp cmp] :
    t₁.size + t₂.size = (t₁ ∪ t₂).size + (t₁ ∩ t₂).size :=
  ExtDTreeMap.size_add_size_eq_size_union_add_size_inter

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  ExtDTreeMap.isEmpty_inter_left h

@[simp]
theorem isEmpty_inter_right [TransCmp cmp] (h : t₂.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true :=
  ExtDTreeMap.isEmpty_inter_right h

theorem isEmpty_inter_iff [TransCmp cmp] :
    (t₁ ∩ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∉ t₂ :=
  ExtDTreeMap.isEmpty_inter_iff

end Inter

section Diff

variable {t₁ t₂ : ExtTreeMap α β cmp}

@[simp]
theorem diff_eq [TransCmp cmp] : t₁.diff t₂ = t₁ \ t₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).contains k = (t₁.contains k && !t₂.contains k) :=
  ExtDTreeMap.contains_diff

/- mem -/
@[simp]
theorem mem_diff_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ \ t₂ ↔ k ∈ t₁ ∧ k ∉ t₂ :=
  ExtDTreeMap.mem_diff_iff

theorem not_mem_diff_of_not_mem_left [TransCmp cmp] {k : α}
    (not_mem : k ∉ t₁) :
    k ∉ t₁ \ t₂ :=
  ExtDTreeMap.not_mem_diff_of_not_mem_left not_mem

theorem not_mem_diff_of_mem_right [TransCmp cmp] {k : α}
    (mem : k ∈ t₂) :
    k ∉ t₁ \ t₂ :=
  ExtDTreeMap.not_mem_diff_of_mem_right mem

/- getElem? -/
theorem getElem?_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂)[k]? = if k ∈ t₂ then none else t₁[k]? :=
  ExtDTreeMap.Const.get?_diff

theorem getElem?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂)[k]? = t₁[k]? :=
  ExtDTreeMap.Const.get?_diff_of_not_mem_right not_mem

theorem getElem?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂)[k]? = none :=
  ExtDTreeMap.Const.get?_diff_of_not_mem_left not_mem

theorem getElem?_diff_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂)[k]? = none :=
  ExtDTreeMap.Const.get?_diff_of_mem_right mem

/- get? -/
@[deprecated getElem?_diff (since := "2025-12-10")]
theorem get?_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).get? k = if k ∈ t₂ then none else t₁.get? k :=
  ExtDTreeMap.Const.get?_diff

@[deprecated getElem?_diff_of_not_mem_right (since := "2025-12-10")]
theorem get?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get? k = t₁.get? k :=
  ExtDTreeMap.Const.get?_diff_of_not_mem_right not_mem

@[deprecated getElem?_diff_of_not_mem_left (since := "2025-12-10")]
theorem get?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get? k = none :=
  ExtDTreeMap.Const.get?_diff_of_not_mem_left not_mem

@[deprecated getElem?_diff_of_mem_right (since := "2025-12-10")]
theorem get?_diff_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).get? k = none :=
  ExtDTreeMap.Const.get?_diff_of_mem_right mem

/- getElem -/
theorem getElem_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂)[k]'h_mem = t₁[k]'(mem_diff_iff.1 h_mem).1 :=
  ExtDTreeMap.Const.get_diff (h_mem := h_mem)

/- get -/
@[deprecated getElem_diff (since := "2025-12-10")]
theorem get_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).get k h_mem = t₁.get k (mem_diff_iff.1 h_mem).1 :=
  ExtDTreeMap.Const.get_diff

/- getD -/
theorem getD_diff [TransCmp cmp] {k : α} {fallback : β} :
    (t₁ \ t₂).getD k fallback =
    if k ∈ t₂ then fallback else t₁.getD k fallback :=
  ExtDTreeMap.Const.getD_diff

theorem getD_diff_of_not_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getD k fallback = t₁.getD k fallback :=
  ExtDTreeMap.Const.getD_diff_of_not_mem_right not_mem

theorem getD_diff_of_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (mem : k ∈ t₂) :
    (t₁ \ t₂).getD k fallback = fallback :=
  ExtDTreeMap.Const.getD_diff_of_mem_right mem

theorem getD_diff_of_not_mem_left [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getD k fallback = fallback :=
  ExtDTreeMap.Const.getD_diff_of_not_mem_left not_mem

/- getElem! -/
theorem getElem!_diff [TransCmp cmp] {k : α} [Inhabited β] :
    (t₁ \ t₂)[k]! = if k ∈ t₂ then default else t₁[k]! :=
  ExtDTreeMap.Const.get!_diff

theorem getElem!_diff_of_not_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₂) :
    (t₁ \ t₂)[k]! = t₁[k]! :=
  ExtDTreeMap.Const.get!_diff_of_not_mem_right not_mem

theorem getElem!_diff_of_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (mem : k ∈ t₂) :
    (t₁ \ t₂)[k]! = default :=
  ExtDTreeMap.Const.get!_diff_of_mem_right mem

theorem getElem!_diff_of_not_mem_left [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₁) :
    (t₁ \ t₂)[k]! = default :=
  ExtDTreeMap.Const.get!_diff_of_not_mem_left not_mem

/- get! -/
@[deprecated getElem!_diff (since := "2025-12-10")]
theorem get!_diff [TransCmp cmp] {k : α} [Inhabited β] :
    (t₁ \ t₂).get! k = if k ∈ t₂ then default else t₁.get! k :=
  ExtDTreeMap.Const.get!_diff

@[deprecated getElem!_diff_of_not_mem_right (since := "2025-12-10")]
theorem get!_diff_of_not_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₂) :
    (t₁ \ t₂).get! k = t₁.get! k :=
  ExtDTreeMap.Const.get!_diff_of_not_mem_right not_mem

@[deprecated getElem!_diff_of_mem_right (since := "2025-12-10")]
theorem get!_diff_of_mem_right [TransCmp cmp]
    {k : α} [Inhabited β] (mem : k ∈ t₂) :
    (t₁ \ t₂).get! k = default :=
  ExtDTreeMap.Const.get!_diff_of_mem_right mem

@[deprecated getElem!_diff_of_not_mem_left (since := "2025-12-10")]
theorem get!_diff_of_not_mem_left [TransCmp cmp]
    {k : α} [Inhabited β] (not_mem : k ∉ t₁) :
    (t₁ \ t₂).get! k = default :=
  ExtDTreeMap.Const.get!_diff_of_not_mem_left not_mem

/- getKey? -/
theorem getKey?_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).getKey? k =
    if k ∈ t₂ then none else t₁.getKey? k :=
  ExtDTreeMap.getKey?_diff

theorem getKey?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getKey? k = t₁.getKey? k :=
  ExtDTreeMap.getKey?_diff_of_not_mem_right not_mem

theorem getKey?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getKey? k = none :=
  ExtDTreeMap.getKey?_diff_of_not_mem_left not_mem

theorem getKey?_diff_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getKey? k = none :=
  ExtDTreeMap.getKey?_diff_of_mem_right mem

/- getKey -/
theorem getKey_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).getKey k h_mem =
    t₁.getKey k (mem_diff_iff.1 h_mem).1 :=
  ExtDTreeMap.getKey_diff

/- getKeyD -/
theorem getKeyD_diff [TransCmp cmp] {k fallback : α} :
    (t₁ \ t₂).getKeyD k fallback =
    if k ∈ t₂ then fallback else t₁.getKeyD k fallback :=
  ExtDTreeMap.getKeyD_diff

theorem getKeyD_diff_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getKeyD k fallback = t₁.getKeyD k fallback :=
  ExtDTreeMap.getKeyD_diff_of_not_mem_right not_mem

theorem getKeyD_diff_of_mem_right [TransCmp cmp]
    {k fallback : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getKeyD k fallback = fallback :=
  ExtDTreeMap.getKeyD_diff_of_mem_right mem

theorem getKeyD_diff_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getKeyD k fallback = fallback :=
  ExtDTreeMap.getKeyD_diff_of_not_mem_left not_mem

/- getKey! -/
theorem getKey!_diff [TransCmp cmp] [Inhabited α] {k : α} :
    (t₁ \ t₂).getKey! k =
    if k ∈ t₂ then default else t₁.getKey! k :=
  ExtDTreeMap.getKey!_diff

theorem getKey!_diff_of_not_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₂) :
    (t₁ \ t₂).getKey! k = t₁.getKey! k :=
  ExtDTreeMap.getKey!_diff_of_not_mem_right not_mem

theorem getKey!_diff_of_mem_right [TransCmp cmp] [Inhabited α]
    {k : α} (mem : k ∈ t₂) :
    (t₁ \ t₂).getKey! k = default :=
  ExtDTreeMap.getKey!_diff_of_mem_right mem

theorem getKey!_diff_of_not_mem_left [TransCmp cmp] [Inhabited α]
    {k : α} (not_mem : k ∉ t₁) :
    (t₁ \ t₂).getKey! k = default :=
  ExtDTreeMap.getKey!_diff_of_not_mem_left not_mem

/- size -/
theorem size_diff_le_size_left [TransCmp cmp] :
    (t₁ \ t₂).size ≤ t₁.size :=
  ExtDTreeMap.size_diff_le_size_left

theorem size_diff_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∉ t₂) :
    (t₁ \ t₂).size = t₁.size :=
  ExtDTreeMap.size_diff_eq_size_left h

theorem size_diff_add_size_inter_eq_size_left [TransCmp cmp] :
    (t₁ \ t₂).size + (t₁ ∩ t₂).size = t₁.size :=
  ExtDTreeMap.size_diff_add_size_inter_eq_size_left

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ \ t₂).isEmpty = true :=
  ExtDTreeMap.isEmpty_diff_left h

theorem isEmpty_diff_iff [TransCmp cmp] :
    (t₁ \ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∈ t₂ :=
  ExtDTreeMap.isEmpty_diff_iff

end Diff

section Alter

theorem alter_eq_empty_iff_erase_eq_empty [TransCmp cmp] {k : α}
    {f : Option β → Option β} :
    alter t k f = ∅ ↔ t.erase k = ∅ ∧ f t[k]? = none := by
  simpa only [ext_iff] using ExtDTreeMap.Const.alter_eq_empty_iff_erase_eq_empty

@[simp]
theorem alter_eq_empty_iff [TransCmp cmp] {k : α} {f : Option β → Option β} :
    alter t k f = ∅ ↔ (t = ∅ ∨ (t.size = 1 ∧ k ∈ t)) ∧ (f t[k]?) = none := by
  simpa only [ext_iff] using ExtDTreeMap.Const.alter_eq_empty_iff

@[grind =]
theorem contains_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).contains k' =
      if cmp k k' = .eq then (f t[k]?).isSome else t.contains k' :=
  ExtDTreeMap.Const.contains_alter

@[grind =]
theorem mem_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    k' ∈ alter t k f ↔
      if cmp k k' = .eq then (f t[k]?).isSome = true else k' ∈ t :=
  ExtDTreeMap.Const.mem_alter

theorem mem_alter_of_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : cmp k k' = .eq) :
    k' ∈ alter t k f ↔ (f t[k]?).isSome :=
  ExtDTreeMap.Const.mem_alter_of_compare_eq he

@[simp]
theorem contains_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).contains k = (f t[k]?).isSome :=
  ExtDTreeMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    k ∈ alter t k f ↔ (f t[k]?).isSome :=
  ExtDTreeMap.Const.mem_alter_self

theorem contains_alter_of_not_compare_eq [TransCmp cmp] {k k' : α}
    {f : Option β → Option β} (he : ¬ cmp k k' = .eq) :
    (alter t k f).contains k' = t.contains k' :=
  ExtDTreeMap.Const.contains_alter_of_not_compare_eq he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : ¬ cmp k k' = .eq) :
    k' ∈ alter t k f ↔ k' ∈ t :=
  ExtDTreeMap.Const.mem_alter_of_not_compare_eq he

@[grind =]
theorem size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size =
      if k ∈ t ∧ (f t[k]?).isNone then
        t.size - 1
      else if k ∉ t ∧ (f t[k]?).isSome then
        t.size + 1
      else
        t.size :=
  ExtDTreeMap.Const.size_alter

theorem size_alter_eq_add_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f t[k]?).isSome) :
    (alter t k f).size = t.size + 1 :=
  ExtDTreeMap.Const.size_alter_eq_add_one h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f t[k]?).isNone) :
    (alter t k f).size = t.size - 1 :=
  ExtDTreeMap.Const.size_alter_eq_sub_one h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f t[k]?).isNone) :
    (alter t k f).size = t.size :=
  ExtDTreeMap.Const.size_alter_eq_self_of_not_mem h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f t[k]?).isSome) :
    (alter t k f).size = t.size :=
  ExtDTreeMap.Const.size_alter_eq_self_of_mem h₁ h₂

theorem size_alter_le_size [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size ≤ t.size + 1 :=
  ExtDTreeMap.Const.size_alter_le_size

theorem size_le_size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter t k f).size :=
  ExtDTreeMap.Const.size_le_size_alter

@[grind =]
theorem getElem?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f)[k']? =
      if cmp k k' = .eq then
        f t[k]?
      else
        t[k']? :=
  ExtDTreeMap.Const.get?_alter

@[simp]
theorem getElem?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f)[k]? = f t[k]? :=
  ExtDTreeMap.Const.get?_alter_self

@[grind =]
theorem getElem_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter t k f)} :
    (alter t k f)[(k')]'hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f t[k]?).isSome := mem_alter_of_compare_eq heq |>.mp hc
        f t[k]? |>.get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t[(k')]'h' :=
  ExtDTreeMap.Const.get_alter (hc := hc)

@[simp]
theorem getElem_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    haveI h' : (f t[k]?).isSome := mem_alter_self.mp hc
    (alter t k f)[k]'hc = (f t[k]?).get h' :=
  ExtDTreeMap.Const.get_alter_self (hc := hc)

@[grind =]
theorem getElem!_alter [TransCmp cmp] {k k' : α} [Inhabited β] {f : Option β → Option β} :
    (alter t k f)[k']! =
      if cmp k k' = .eq then
        f t[k]? |>.get!
      else
        t[k']! :=
  ExtDTreeMap.Const.get!_alter

@[simp]
theorem getElem!_alter_self [TransCmp cmp] {k : α} [Inhabited β] {f : Option β → Option β} :
    (alter t k f)[k]! = (f t[k]?).get! :=
  ExtDTreeMap.Const.get!_alter_self

@[grind =]
theorem getD_alter [TransCmp cmp] {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter t k f) k' fallback =
      if cmp k k' = .eq then
        f t[k]? |>.getD fallback
      else
        getD t k' fallback :=
  ExtDTreeMap.Const.getD_alter

@[simp]
theorem getD_alter_self [TransCmp cmp] {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter t k f) k fallback = (f t[k]?).getD fallback :=
  ExtDTreeMap.Const.getD_alter_self

@[grind =]
theorem getKey?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey? k' =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then some k else none
      else
        t.getKey? k' :=
  ExtDTreeMap.Const.getKey?_alter

theorem getKey?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).getKey? k = if (f t[k]?).isSome then some k else none :=
  ExtDTreeMap.Const.getKey?_alter_self

@[grind =]
theorem getKey!_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey! k' =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then k else default
      else
        t.getKey! k' :=
  ExtDTreeMap.Const.getKey!_alter

theorem getKey!_alter_self [TransCmp cmp] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (alter t k f).getKey! k = if (f t[k]?).isSome then k else default :=
  ExtDTreeMap.Const.getKey!_alter_self

@[grind =]
theorem getKey_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter t k f} :
    (alter t k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t.getKey k' h' :=
  ExtDTreeMap.Const.getKey_alter

@[simp]
theorem getKey_alter_self [TransCmp cmp] [Inhabited α] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    (alter t k f).getKey k hc = k :=
  ExtDTreeMap.Const.getKey_alter_self

@[grind =]
theorem getKeyD_alter [TransCmp cmp] {k k' fallback : α} {f : Option β → Option β} :
    (alter t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f t[k]?).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  ExtDTreeMap.Const.getKeyD_alter

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [Inhabited α] {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter t k f).getKeyD k fallback = if (f t[k]?).isSome then k else fallback :=
  ExtDTreeMap.Const.getKeyD_alter_self

end Alter

section Modify

@[simp]
theorem modify_eq_empty_iff [TransCmp cmp] {k : α} {f : β → β} :
    t.modify k f = ∅ ↔ t = ∅ := by
  simpa only [ext_iff] using ExtDTreeMap.Const.modify_eq_empty_iff

@[grind =]
theorem contains_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    (modify t k f).contains k' = t.contains k' :=
  ExtDTreeMap.Const.contains_modify

@[grind =]
theorem mem_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    k' ∈ modify t k f ↔ k' ∈ t :=
  ExtDTreeMap.Const.mem_modify

@[grind =]
theorem size_modify [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f).size = t.size :=
  ExtDTreeMap.Const.size_modify

@[grind =]
theorem getElem?_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    (modify t k f)[k']? =
      if cmp k k' = .eq then
        t[k]?.map f
      else
        t[k']? :=
  ExtDTreeMap.Const.get?_modify

@[simp]
theorem getElem?_modify_self [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f)[k]? = t[k]?.map f :=
  ExtDTreeMap.Const.get?_modify_self

@[grind =]
theorem getElem_modify [TransCmp cmp] {k k' : α} {f : β → β} {hc : k' ∈ modify t k f} :
    (modify t k f)[(k')]'hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr heq |>.mpr <| mem_modify.mp hc
        f (t[k]'h')
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t[(k')]'h' :=
  ExtDTreeMap.Const.get_modify (hc := hc)

@[simp]
theorem getElem_modify_self [TransCmp cmp] {k : α} {f : β → β} {hc : k ∈ modify t k f} :
    haveI h' : k ∈ t := mem_modify.mp hc
    (modify t k f)[k]'hc = f (t[k]'h') :=
  ExtDTreeMap.Const.get_modify_self (hc := hc)

@[grind =]
theorem getElem!_modify [TransCmp cmp] {k k' : α} [hi : Inhabited β] {f : β → β} :
    (modify t k f)[k']! =
      if cmp k k' = .eq then
        t[k]? |>.map f |>.get!
      else
        t[k']! :=
  ExtDTreeMap.Const.get!_modify

@[simp]
theorem getElem!_modify_self [TransCmp cmp] {k : α} [Inhabited β] {f : β → β} :
    (modify t k f)[k]! = (t[k]?.map f).get! :=
  ExtDTreeMap.Const.get!_modify_self

@[grind =]
theorem getD_modify [TransCmp cmp] {k k' : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k' fallback =
      if cmp k k' = .eq then
        t[k]?.map f |>.getD fallback
      else
        getD t k' fallback :=
  ExtDTreeMap.Const.getD_modify

@[simp]
theorem getD_modify_self [TransCmp cmp] {k : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k fallback = (t[k]?.map f).getD fallback :=
  ExtDTreeMap.Const.getD_modify_self

@[grind =]
theorem getKey?_modify [TransCmp cmp] {k k' : α} {f : β → β} :
    (modify t k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  ExtDTreeMap.Const.getKey?_modify

theorem getKey?_modify_self [TransCmp cmp] {k : α} {f : β → β} :
    (modify t k f).getKey? k = if k ∈ t then some k else none :=
  ExtDTreeMap.Const.getKey?_modify_self

@[grind =]
theorem getKey!_modify [TransCmp cmp] [Inhabited α] {k k' : α} {f : β → β} :
    (modify t k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  ExtDTreeMap.Const.getKey!_modify

theorem getKey!_modify_self [TransCmp cmp] [Inhabited α] {k : α} {f : β → β} :
    (modify t k f).getKey! k = if k ∈ t then k else default :=
  ExtDTreeMap.Const.getKey!_modify_self

@[grind =]
theorem getKey_modify [TransCmp cmp] [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify t k f} :
    (modify t k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.getKey k' h' :=
  ExtDTreeMap.Const.getKey_modify

@[simp]
theorem getKey_modify_self [TransCmp cmp] [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify t k f} : (modify t k f).getKey k hc = k :=
  ExtDTreeMap.Const.getKey_modify_self

@[grind =]
theorem getKeyD_modify [TransCmp cmp] {k k' fallback : α} {f : β → β} :
    (modify t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  ExtDTreeMap.Const.getKeyD_modify

theorem getKeyD_modify_self [TransCmp cmp] [Inhabited α] {k fallback : α} {f : β → β} :
    (modify t k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  ExtDTreeMap.Const.getKeyD_modify_self

end Modify

section Min

@[simp, grind =]
theorem minKey?_empty [TransCmp cmp] : (∅ : ExtTreeMap α β cmp).minKey? = none :=
  ExtDTreeMap.minKey?_empty

@[simp, grind =]
theorem minKey?_eq_none_iff [TransCmp cmp] :
    t.minKey? = none ↔ t = ∅ :=
  ExtDTreeMap.minKey?_eq_none_iff.trans ext_iff.symm

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtDTreeMap.minKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem minKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtDTreeMap.minKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_minKey?_eq_isEmpty [TransCmp cmp] :
    t.minKey?.isNone = t.isEmpty :=
  ExtDTreeMap.isNone_minKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_minKey?_eq_not_isEmpty [TransCmp cmp] :
    t.minKey?.isSome = !t.isEmpty :=
  ExtDTreeMap.isSome_minKey?_eq_not_isEmpty

theorem isSome_minKey?_iff_ne_empty [TransCmp cmp] :
    t.minKey?.isSome ↔ t ≠ ∅ :=
  ExtDTreeMap.isSome_minKey?_iff_ne_empty.trans (not_congr ext_iff).symm

@[grind =] theorem minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  ExtDTreeMap.minKey?_insert

@[grind =] theorem isSome_minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey?.isSome :=
  ExtDTreeMap.isSome_minKey?_insert

theorem minKey_insert_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insert k v).minKey insert_ne_empty = k :=
  ExtDTreeMap.minKey_insert_of_isEmpty he

theorem minKey?_insert_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insert k v).minKey? = some k :=
  ExtDTreeMap.minKey?_insert_of_isEmpty he

theorem minKey!_insert_of_isEmpty [TransCmp cmp] [Inhabited α] {k v} (he : t.isEmpty) :
    (t.insert k v).minKey! = k :=
  ExtDTreeMap.minKey!_insert_of_isEmpty he

theorem minKeyD_insert_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) {fallback : α} :
    (t.insert k v).minKeyD fallback = k :=
  ExtDTreeMap.minKeyD_insert_of_isEmpty he

theorem minKey_insertIfNew_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey insertIfNew_ne_empty = k :=
  ExtDTreeMap.minKey_insertIfNew_of_isEmpty he

theorem minKey?_insertIfNew_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey? = some k :=
  ExtDTreeMap.minKey?_insertIfNew_of_isEmpty he

theorem minKey!_insertIfNew_of_isEmpty [TransCmp cmp] [Inhabited α] {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey! = k :=
  ExtDTreeMap.minKey!_insertIfNew_of_isEmpty he

theorem minKeyD_insertIfNew_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) {fallback : α} :
    (t.insertIfNew k v).minKeyD fallback = k :=
  ExtDTreeMap.minKeyD_insertIfNew_of_isEmpty he

theorem minKey?_insert_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v |>.minKey? |>.get isSome_minKey?_insert) = kmi) →
    cmp kmi km |>.isLE :=
  ExtDTreeMap.minKey?_insert_le_minKey?

theorem minKey?_insert_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.minKey?.get isSome_minKey?_insert) = kmi) →
    cmp kmi k |>.isLE :=
  ExtDTreeMap.minKey?_insert_le_self

theorem contains_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) → t.contains km :=
  ExtDTreeMap.contains_minKey?

theorem minKey?_mem [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) → km ∈ t :=
  ExtDTreeMap.minKey?_mem

@[simp] theorem min?_keys [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.keys.min? = t.minKey? :=
  ExtDTreeMap.min?_keys

@[simp] theorem head?_keys [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.keys.head? = t.minKey? :=
  ExtDTreeMap.head?_keys

theorem isSome_minKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.minKey?.isSome :=
  ExtDTreeMap.isSome_minKey?_of_contains

theorem isSome_minKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.minKey?.isSome :=
  ExtDTreeMap.isSome_minKey?_of_mem

theorem minKey?_le_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains hc) = km) →
    cmp km k |>.isLE :=
  ExtDTreeMap.minKey?_le_of_contains

theorem minKey?_le_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem hc) = km) →
    cmp km k |>.isLE :=
  ExtDTreeMap.minKey?_le_of_mem

theorem le_minKey? [TransCmp cmp] {k} :
    (∀ k', t.minKey? = some k' → (cmp k k').isLE) ↔
      (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtDTreeMap.le_minKey?

theorem getKey?_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km :=
  ExtDTreeMap.getKey?_minKey?

theorem getKey_minKey? [TransCmp cmp] {km hc} :
    (hkm : t.minKey?.get (isSome_minKey?_of_contains hc) = km) → t.getKey km hc = km :=
  ExtDTreeMap.getKey_minKey?

theorem getKey!_minKey? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.minKey? = some km) → t.getKey! km = km :=
  ExtDTreeMap.getKey!_minKey?

theorem getKeyD_minKey? [TransCmp cmp] {km fallback} :
    (hkm : t.minKey? = some km) → t.getKeyD km fallback = km :=
  ExtDTreeMap.getKeyD_minKey?

@[simp]
theorem minKey?_bind_getKey? [TransCmp cmp] :
    t.minKey?.bind t.getKey? = t.minKey? :=
  ExtDTreeMap.minKey?_bind_getKey?

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (t.erase k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq :=
  ExtDTreeMap.minKey?_erase_eq_iff_not_compare_eq_minKey?

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.minKey?) = t.minKey? :=
  ExtDTreeMap.minKey?_erase_eq_of_not_compare_eq_minKey?

theorem isSome_minKey?_of_isSome_minKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.minKey?.isSome) →
    t.minKey?.isSome :=
  ExtDTreeMap.isSome_minKey?_of_isSome_minKey?_erase

theorem minKey?_le_minKey?_erase [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  ExtDTreeMap.minKey?_le_minKey?_erase

@[grind =] theorem minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  ExtDTreeMap.minKey?_insertIfNew

@[grind =] theorem isSome_minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey?.isSome :=
  ExtDTreeMap.isSome_minKey?_insertIfNew

theorem minKey?_insertIfNew_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.minKey? |>.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi km |>.isLE :=
  ExtDTreeMap.minKey?_insertIfNew_le_minKey?

theorem minKey?_insertIfNew_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.minKey?.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi k |>.isLE :=
  ExtDTreeMap.minKey?_insertIfNew_le_self

@[grind =_] theorem minKey?_eq_head?_keys [TransCmp cmp] :
    t.minKey? = t.keys.head? :=
  ExtDTreeMap.minKey?_eq_head?_keys

theorem minKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).minKey? = t.minKey?.map fun km => if cmp km k = .eq then k else km :=
  ExtDTreeMap.Const.minKey?_modify

@[simp, grind =]
theorem minKey?_modify_eq_minKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).minKey? = t.minKey? :=
  ExtDTreeMap.Const.minKey?_modify_eq_minKey?

@[grind =] theorem isSome_minKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).minKey?.isSome = !t.isEmpty :=
  ExtDTreeMap.Const.isSome_minKey?_modify

theorem isSome_minKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (t.modify k f).minKey?.isSome = t.minKey?.isSome :=
  ExtDTreeMap.Const.isSome_minKey?_modify_eq_isSome

theorem compare_minKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (t.modify k f |>.minKey? |>.get <|
        isSome_minKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  ExtDTreeMap.Const.compare_minKey?_modify_eq

theorem minKey?_alter_eq_self [TransCmp cmp] {k f} :
    (t.alter k f).minKey? = some k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  ExtDTreeMap.Const.minKey?_alter_eq_self

theorem minKey_eq_get_minKey? [TransCmp cmp] {he} :
    t.minKey he = t.minKey?.get (isSome_minKey?_iff_ne_empty.mpr he) :=
  ExtDTreeMap.minKey_eq_get_minKey?

theorem minKey?_eq_some_minKey [TransCmp cmp] (he) :
    t.minKey? = some (t.minKey he) :=
  ExtDTreeMap.minKey?_eq_some_minKey (mt ext he)

theorem minKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.minKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtDTreeMap.minKey_eq_iff_getKey?_eq_self_and_forall

theorem minKey_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.minKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  ExtDTreeMap.minKey_eq_iff_mem_and_forall

@[grind =] theorem minKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey insert_ne_empty =
      t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k' :=
  ExtDTreeMap.minKey_insert

theorem minKey_insert_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insert k v |>.minKey insert_ne_empty) (t.minKey he) |>.isLE :=
  ExtDTreeMap.minKey_insert_le_minKey

theorem minKey_insert_le_self [TransCmp cmp] {k v} :
    cmp (t.insert k v |>.minKey insert_ne_empty) k |>.isLE :=
  ExtDTreeMap.minKey_insert_le_self

@[grind =] theorem contains_minKey [TransCmp cmp] {he} :
    t.contains (t.minKey he) :=
  ExtDTreeMap.contains_minKey

theorem minKey_mem [TransCmp cmp] {he} :
    t.minKey he ∈ t :=
  ExtDTreeMap.minKey_mem

grind_pattern minKey_mem => t.minKey he ∈ t

theorem minKey_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp (t.minKey (ne_empty_of_mem hc)) k |>.isLE :=
  ExtDTreeMap.minKey_le_of_contains hc

theorem minKey_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp (t.minKey (ne_empty_of_mem hc)) k |>.isLE :=
  ExtDTreeMap.minKey_le_of_mem hc

theorem le_minKey [TransCmp cmp] {k he} :
    (cmp k (t.minKey he)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtDTreeMap.le_minKey

@[simp, grind =]
theorem getKey?_minKey [TransCmp cmp] {he} :
    t.getKey? (t.minKey he) = some (t.minKey he) :=
  ExtDTreeMap.getKey?_minKey

@[simp, grind =]
theorem getKey_minKey [TransCmp cmp] {he hc} :
    t.getKey (t.minKey he) hc = t.minKey he :=
  ExtDTreeMap.getKey_minKey

@[simp, grind =]
theorem getKey!_minKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.minKey he) = t.minKey he :=
  ExtDTreeMap.getKey!_minKey

@[simp, grind =]
theorem getKeyD_minKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.minKey he) fallback = t.minKey he :=
  ExtDTreeMap.getKeyD_minKey

@[simp]
theorem minKey_erase_eq_iff_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (t.erase k |>.minKey he) =
        t.minKey (ne_empty_of_erase_ne_empty he) ↔
      ¬ cmp k (t.minKey <| ne_empty_of_erase_ne_empty he) = .eq :=
  ExtDTreeMap.minKey_erase_eq_iff_not_compare_eq_minKey

theorem minKey_erase_eq_of_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.minKey (ne_empty_of_erase_ne_empty he)) = .eq) →
    (t.erase k |>.minKey he) =
      t.minKey (ne_empty_of_erase_ne_empty he) :=
  ExtDTreeMap.minKey_erase_eq_of_not_compare_eq_minKey

theorem minKey_le_minKey_erase [TransCmp cmp] {k he} :
    cmp (t.minKey <| ne_empty_of_erase_ne_empty he)
      (t.erase k |>.minKey he) |>.isLE :=
  ExtDTreeMap.minKey_le_minKey_erase

@[grind =] theorem minKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey insertIfNew_ne_empty =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  ExtDTreeMap.minKey_insertIfNew

theorem minKey_insertIfNew_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insertIfNew k v |>.minKey insertIfNew_ne_empty)
      (t.minKey he) |>.isLE :=
  ExtDTreeMap.minKey_insertIfNew_le_minKey (t := t.inner) (he := mt ext he)

theorem minKey_insertIfNew_le_self [TransCmp cmp] {k v} :
    cmp (t.insertIfNew k v |>.minKey <| insertIfNew_ne_empty) k |>.isLE :=
  ExtDTreeMap.minKey_insertIfNew_le_self

@[grind =_] theorem minKey_eq_head_keys [TransCmp cmp] {he} :
    t.minKey he = t.keys.head (mt keys_eq_nil_iff.mp he) :=
  ExtDTreeMap.minKey_eq_head_keys

theorem minKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).minKey he =
      if cmp (t.minKey (mt modify_eq_empty_iff.mpr he)) k = .eq then
        k
      else
        (t.minKey (mt modify_eq_empty_iff.mpr he)) :=
  ExtDTreeMap.Const.minKey_modify

@[simp, grind =]
theorem minKey_modify_eq_minKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).minKey he = t.minKey (mt modify_eq_empty_iff.mpr he) :=
  ExtDTreeMap.Const.minKey_modify_eq_minKey

theorem compare_minKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.minKey he)
      (t.minKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  ExtDTreeMap.Const.compare_minKey_modify_eq

@[simp]
theorem ordCompare_minKey_modify_eq [Ord α] [TransOrd α] {t : ExtTreeMap α β} {k f he} :
    compare (modify t k f |>.minKey he)
      (t.minKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  compare_minKey_modify_eq

theorem minKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).minKey he = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  ExtDTreeMap.Const.minKey_alter_eq_self

theorem minKey?_eq_some_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.minKey? = some t.minKey! :=
  ExtDTreeMap.minKey?_eq_some_minKey! (mt ext he)

theorem minKey_eq_minKey! [TransCmp cmp] [Inhabited α] {he : t ≠ ∅} :
    t.minKey he = t.minKey! :=
  ExtDTreeMap.minKey_eq_minKey!

theorem minKey!_empty [TransCmp cmp] [Inhabited α] : (∅ : ExtTreeMap α β cmp).minKey! = default :=
  ExtDTreeMap.minKey!_empty

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtDTreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem minKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtDTreeMap.minKey!_eq_iff_mem_and_forall (mt ext he)

@[grind =]
theorem minKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v).minKey! =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  ExtDTreeMap.minKey!_insert

theorem minKey!_insert_le_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp (t.insert k v).minKey! t.minKey! |>.isLE :=
  ExtDTreeMap.minKey!_insert_le_minKey! (mt ext he)

theorem minKey!_insert_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insert k v).minKey! k |>.isLE :=
  ExtDTreeMap.minKey!_insert_le_self

theorem contains_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.contains t.minKey! :=
  ExtDTreeMap.contains_minKey! (mt ext he)

theorem minKey!_mem [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.minKey! ∈ t :=
  ExtDTreeMap.minKey!_mem (mt ext he)

theorem minKey!_le_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp t.minKey! k |>.isLE :=
  ExtDTreeMap.minKey!_le_of_contains hc

theorem minKey!_le_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp t.minKey! k |>.isLE :=
  ExtDTreeMap.minKey!_le_of_mem hc

theorem le_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    (cmp k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtDTreeMap.le_minKey! (mt ext he)

theorem getKey?_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey? t.minKey! = some t.minKey! :=
  ExtDTreeMap.getKey?_minKey! (mt ext he)

@[grind =] theorem getKey_minKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey! :=
  ExtDTreeMap.getKey_minKey!

@[simp, grind =]
theorem getKey_minKey!_eq_minKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey (ne_empty_of_mem hc) :=
  ExtDTreeMap.getKey_minKey!_eq_minKey

theorem getKey!_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey! t.minKey! = t.minKey! :=
  ExtDTreeMap.getKey!_minKey! (mt ext he)

theorem getKeyD_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKeyD t.minKey! fallback = t.minKey! :=
  ExtDTreeMap.getKeyD_minKey! (mt ext he)

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k t.minKey! = .eq) :
    (t.erase k).minKey! = t.minKey! :=
  ExtDTreeMap.minKey!_erase_eq_of_not_compare_minKey!_eq (mt ext he) heq

theorem minKey!_le_minKey!_erase [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) :
    cmp t.minKey! (t.erase k).minKey! |>.isLE :=
  ExtDTreeMap.minKey!_le_minKey!_erase (mt ext he)

@[grind =]
theorem minKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v).minKey! =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  ExtDTreeMap.minKey!_insertIfNew

theorem minKey!_insertIfNew_le_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp (t.insertIfNew k v).minKey! t.minKey! |>.isLE :=
  ExtDTreeMap.minKey!_insertIfNew_le_minKey! (mt ext he)

theorem minKey!_insertIfNew_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insertIfNew k v).minKey! k |>.isLE :=
  ExtDTreeMap.minKey!_insertIfNew_le_self

@[grind =_]
theorem minKey!_eq_head!_keys [TransCmp cmp] [Inhabited α] :
    t.minKey! = t.keys.head! :=
  ExtDTreeMap.minKey!_eq_head!_keys

theorem minKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : modify t k f ≠ ∅) :
    (modify t k f).minKey! = if cmp t.minKey! k = .eq then k else t.minKey! :=
  ExtDTreeMap.Const.minKey!_modify (mt ext he)

@[simp]
theorem minKey!_modify_eq_minKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f).minKey! = t.minKey! :=
  ExtDTreeMap.Const.minKey!_modify_eq_minKey!

theorem compare_minKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f).minKey! t.minKey! = .eq :=
  ExtDTreeMap.Const.compare_minKey!_modify_eq

@[simp]
theorem ordCompare_minKey!_modify_eq [Ord α] [TransOrd α] {t : ExtTreeMap α β} [Inhabited α] {k f} :
    compare (modify t k f).minKey! t.minKey! = .eq :=
  compare_minKey!_modify_eq

theorem minKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : alter t k f ≠ ∅) :
    (alter t k f).minKey! = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  ExtDTreeMap.Const.minKey!_alter_eq_self (mt ext he)

theorem minKey?_eq_some_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.minKey? = some (t.minKeyD fallback) :=
  ExtDTreeMap.minKey?_eq_some_minKeyD (mt ext he)

theorem minKeyD_empty [TransCmp cmp] {fallback} : (∅ : ExtTreeMap α β cmp).minKeyD fallback = fallback :=
  ExtDTreeMap.minKeyD_empty

theorem minKey!_eq_minKeyD_default [TransCmp cmp] [Inhabited α] :
    t.minKey! = t.minKeyD default :=
  ExtDTreeMap.minKey!_eq_minKeyD_default

theorem minKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.minKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtDTreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem minKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.minKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  ExtDTreeMap.minKeyD_eq_iff_mem_and_forall (mt ext he)

@[grind =]
theorem minKeyD_insert [TransCmp cmp] {k v fallback} :
    (t.insert k v |>.minKeyD fallback) =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  ExtDTreeMap.minKeyD_insert

theorem minKeyD_insert_le_minKeyD [TransCmp cmp] (he : t ≠ ∅)
    {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  ExtDTreeMap.minKeyD_insert_le_minKeyD (mt ext he)

theorem minKeyD_insert_le_self [TransCmp cmp] {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) k |>.isLE :=
  ExtDTreeMap.minKeyD_insert_le_self

theorem contains_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.contains (t.minKeyD fallback) :=
  ExtDTreeMap.contains_minKeyD (mt ext he)

theorem minKeyD_mem [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.minKeyD fallback ∈ t :=
  ExtDTreeMap.minKeyD_mem (mt ext he)

theorem minKeyD_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  ExtDTreeMap.minKeyD_le_of_contains hc

theorem minKeyD_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  ExtDTreeMap.minKeyD_le_of_mem hc

theorem le_minKeyD [TransCmp cmp] (he : t ≠ ∅) {k fallback} :
    (cmp k (t.minKeyD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  ExtDTreeMap.le_minKeyD (mt ext he)

theorem getKey?_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.getKey? (t.minKeyD fallback) = some (t.minKeyD fallback) :=
  ExtDTreeMap.getKey?_minKeyD (mt ext he)

@[grind =] theorem getKey_minKeyD [TransCmp cmp] {fallback hc} :
    t.getKey (t.minKeyD fallback) hc = t.minKeyD fallback :=
  ExtDTreeMap.getKey_minKeyD

theorem getKey!_minKeyD [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKey! (t.minKeyD fallback) = t.minKeyD fallback :=
  ExtDTreeMap.getKey!_minKeyD (mt ext he)

theorem getKeyD_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback fallback'} :
    t.getKeyD (t.minKeyD fallback) fallback' = t.minKeyD fallback :=
  ExtDTreeMap.getKeyD_minKeyD (mt ext he)

theorem minKeyD_erase_eq_of_not_compare_minKeyD_eq [TransCmp cmp] {k fallback}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k (t.minKeyD fallback) = .eq) :
    (t.erase k |>.minKeyD fallback) = t.minKeyD fallback :=
  ExtDTreeMap.minKeyD_erase_eq_of_not_compare_minKeyD_eq (mt ext he) heq

theorem minKeyD_le_minKeyD_erase [TransCmp cmp] {k}
    (he : t.erase k ≠ ∅) {fallback} :
    cmp (t.minKeyD fallback) (t.erase k |>.minKeyD fallback) |>.isLE :=
  ExtDTreeMap.minKeyD_le_minKeyD_erase (mt ext he)

@[grind =]
theorem minKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    (t.insertIfNew k v |>.minKeyD fallback) =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  ExtDTreeMap.minKeyD_insertIfNew

theorem minKeyD_insertIfNew_le_minKeyD [TransCmp cmp]
    (he : t ≠ ∅) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  ExtDTreeMap.minKeyD_insertIfNew_le_minKeyD (mt ext he)

theorem minKeyD_insertIfNew_le_self [TransCmp cmp] {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) k |>.isLE :=
  ExtDTreeMap.minKeyD_insertIfNew_le_self

theorem minKeyD_eq_headD_keys [TransCmp cmp] {fallback} :
    t.minKeyD fallback = t.keys.headD fallback :=
  ExtDTreeMap.minKeyD_eq_headD_keys

theorem minKeyD_modify [TransCmp cmp] {k f}
    (he : modify t k f ≠ ∅) {fallback} :
    (modify t k f |>.minKeyD fallback) =
      if cmp (t.minKeyD fallback) k = .eq then k else (t.minKeyD fallback) :=
  ExtDTreeMap.Const.minKeyD_modify (mt ext he)

@[simp, grind =]
theorem minKeyD_modify_eq_minKeyD [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (modify t k f |>.minKeyD fallback) = t.minKeyD fallback :=
  ExtDTreeMap.Const.minKeyD_modify_eq_minKeyD

theorem compare_minKeyD_modify_eq [TransCmp cmp] {k f fallback} :
    cmp (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  ExtDTreeMap.Const.compare_minKeyD_modify_eq

@[simp]
theorem ordCompare_minKeyD_modify_eq [Ord α] [TransOrd α] {t : ExtTreeMap α β} {k f fallback} :
    compare (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  compare_minKeyD_modify_eq

theorem minKeyD_alter_eq_self [TransCmp cmp] {k f}
    (he : alter t k f ≠ ∅) {fallback} :
    (alter t k f |>.minKeyD fallback) = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  ExtDTreeMap.Const.minKeyD_alter_eq_self (mt ext he)

end Min

section Max

@[simp, grind =]
theorem maxKey?_empty [TransCmp cmp] : (∅ : ExtTreeMap α β cmp).maxKey? = none :=
  ExtDTreeMap.maxKey?_empty

@[simp, grind =]
theorem maxKey?_eq_none_iff [TransCmp cmp] :
    t.maxKey? = none ↔ t = ∅ :=
  ExtDTreeMap.maxKey?_eq_none_iff.trans ext_iff.symm

theorem maxKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.maxKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtDTreeMap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem maxKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.maxKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtDTreeMap.maxKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_maxKey?_eq_isEmpty [TransCmp cmp] :
    t.maxKey?.isNone = t.isEmpty :=
  ExtDTreeMap.isNone_maxKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_maxKey?_eq_not_isEmpty [TransCmp cmp] :
    t.maxKey?.isSome = !t.isEmpty :=
  ExtDTreeMap.isSome_maxKey?_eq_not_isEmpty

theorem isSome_maxKey?_iff_ne_empty [TransCmp cmp] :
    t.maxKey?.isSome ↔ t ≠ ∅ :=
  ExtDTreeMap.isSome_maxKey?_iff_ne_empty.trans (not_congr ext_iff).symm

@[grind =]
theorem maxKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  ExtDTreeMap.maxKey?_insert

@[grind =]
theorem isSome_maxKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey?.isSome :=
  ExtDTreeMap.isSome_maxKey?_insert

theorem maxKey?_le_maxKey?_insert [TransCmp cmp] {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insert k v |>.maxKey? |>.get isSome_maxKey?_insert) = kmi) →
    cmp km kmi |>.isLE :=
  ExtDTreeMap.maxKey?_le_maxKey?_insert

theorem self_le_maxKey?_insert [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.maxKey?.get isSome_maxKey?_insert) = kmi) →
    cmp k kmi |>.isLE :=
  ExtDTreeMap.self_le_maxKey?_insert

theorem contains_maxKey? [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) → t.contains km :=
  ExtDTreeMap.contains_maxKey?

theorem maxKey?_mem [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) → km ∈ t :=
  ExtDTreeMap.maxKey?_mem

theorem isSome_maxKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.maxKey?.isSome :=
  ExtDTreeMap.isSome_maxKey?_of_contains

theorem isSome_maxKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.maxKey?.isSome :=
  ExtDTreeMap.isSome_maxKey?_of_mem

theorem le_maxKey?_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_contains hc) = km) →
    cmp k km |>.isLE :=
  ExtDTreeMap.le_maxKey?_of_contains

theorem le_maxKey?_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_mem hc) = km) →
    cmp k km |>.isLE :=
  ExtDTreeMap.le_maxKey?_of_mem

theorem maxKey?_le [TransCmp cmp] {k} :
    (∀ k', t.maxKey? = some k' → (cmp k' k).isLE) ↔
      (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtDTreeMap.maxKey?_le

theorem getKey?_maxKey? [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) → t.getKey? km = some km :=
  ExtDTreeMap.getKey?_maxKey?

theorem getKey_maxKey? [TransCmp cmp] {km hc} :
    (hkm : t.maxKey?.get (isSome_maxKey?_of_contains hc) = km) → t.getKey km hc = km :=
  ExtDTreeMap.getKey_maxKey?

theorem getKey!_maxKey? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.maxKey? = some km) → t.getKey! km = km :=
  ExtDTreeMap.getKey!_maxKey?

theorem getKeyD_maxKey? [TransCmp cmp] {km fallback} :
    (hkm : t.maxKey? = some km) → t.getKeyD km fallback = km :=
  ExtDTreeMap.getKeyD_maxKey?

@[simp]
theorem maxKey?_bind_getKey? [TransCmp cmp] :
    t.maxKey?.bind t.getKey? = t.maxKey? :=
  ExtDTreeMap.maxKey?_bind_getKey?

theorem maxKey?_erase_eq_iff_not_compare_eq_maxKey? [TransCmp cmp] {k} :
    (t.erase k |>.maxKey?) = t.maxKey? ↔
      ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq :=
  ExtDTreeMap.maxKey?_erase_eq_iff_not_compare_eq_maxKey?

theorem maxKey?_erase_eq_of_not_compare_eq_maxKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.maxKey?) = t.maxKey? :=
  ExtDTreeMap.maxKey?_erase_eq_of_not_compare_eq_maxKey?

theorem isSome_maxKey?_of_isSome_maxKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.maxKey?.isSome) →
    t.maxKey?.isSome :=
  ExtDTreeMap.isSome_maxKey?_of_isSome_maxKey?_erase

theorem maxKey?_erase_le_maxKey? [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.maxKey?) = some kme) →
    (hkm : (t.maxKey?.get <|
      isSome_maxKey?_of_isSome_maxKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  ExtDTreeMap.maxKey?_erase_le_maxKey?

@[grind =] theorem maxKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  ExtDTreeMap.maxKey?_insertIfNew

@[grind =] theorem isSome_maxKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey?.isSome :=
  ExtDTreeMap.isSome_maxKey?_insertIfNew

theorem maxKey?_le_maxKey?_insertIfNew [TransCmp cmp] {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.maxKey? |>.get isSome_maxKey?_insertIfNew) = kmi) →
    cmp km kmi |>.isLE :=
  ExtDTreeMap.maxKey?_le_maxKey?_insertIfNew

theorem self_le_maxKey?_insertIfNew [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.maxKey?.get isSome_maxKey?_insertIfNew) = kmi) →
    cmp k kmi |>.isLE :=
  ExtDTreeMap.self_le_maxKey?_insertIfNew

@[grind =_] theorem maxKey?_eq_getLast?_keys [TransCmp cmp] :
    t.maxKey? = t.keys.getLast? :=
  ExtDTreeMap.maxKey?_eq_getLast?_keys

@[grind =] theorem maxKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).maxKey? = t.maxKey?.map fun km => if cmp km k = .eq then k else km :=
  ExtDTreeMap.Const.maxKey?_modify

@[simp, grind =]
theorem maxKey?_modify_eq_maxKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).maxKey? = t.maxKey? :=
  ExtDTreeMap.Const.maxKey?_modify_eq_maxKey?

theorem isSome_maxKey?_modify [TransCmp cmp] {k f} :
    (t.modify k f).maxKey?.isSome = !t.isEmpty :=
  ExtDTreeMap.Const.isSome_maxKey?_modify

theorem isSome_maxKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (t.modify k f).maxKey?.isSome = t.maxKey?.isSome :=
  ExtDTreeMap.Const.isSome_maxKey?_modify_eq_isSome

theorem compare_maxKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.maxKey? = some km) →
    (hkmm : (t.modify k f |>.maxKey? |>.get <|
        isSome_maxKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  ExtDTreeMap.Const.compare_maxKey?_modify_eq

theorem maxKey?_alter_eq_self [TransCmp cmp] {k f} :
    (t.alter k f).maxKey? = some k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  ExtDTreeMap.Const.maxKey?_alter_eq_self

theorem maxKey_eq_get_maxKey? [TransCmp cmp] {he} :
    t.maxKey he = t.maxKey?.get (isSome_maxKey?_iff_ne_empty.mpr he) :=
  ExtDTreeMap.maxKey_eq_get_maxKey?

theorem maxKey?_eq_some_maxKey [TransCmp cmp] (he) :
    t.maxKey? = some (t.maxKey he) :=
  ExtDTreeMap.maxKey?_eq_some_maxKey (mt ext he)

theorem maxKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.maxKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtDTreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall

theorem maxKey_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.maxKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  ExtDTreeMap.maxKey_eq_iff_mem_and_forall

@[grind =] theorem maxKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey insert_ne_empty =
      t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k' :=
  ExtDTreeMap.maxKey_insert

theorem maxKey_le_maxKey_insert [TransCmp cmp] {k v he} :
    cmp (t.maxKey he) (t.insert k v |>.maxKey insert_ne_empty) |>.isLE :=
  ExtDTreeMap.maxKey_le_maxKey_insert

theorem self_le_maxKey_insert [TransCmp cmp] {k v} :
    cmp k (t.insert k v |>.maxKey insert_ne_empty) |>.isLE :=
  ExtDTreeMap.self_le_maxKey_insert

@[grind =] theorem contains_maxKey [TransCmp cmp] {he} :
    t.contains (t.maxKey he) :=
  ExtDTreeMap.contains_maxKey

theorem maxKey_mem [TransCmp cmp] {he} :
    t.maxKey he ∈ t :=
  ExtDTreeMap.maxKey_mem

grind_pattern maxKey_mem => t.maxKey he ∈ t

theorem le_maxKey_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp k (t.maxKey (ne_empty_of_mem hc)) |>.isLE :=
  ExtDTreeMap.le_maxKey_of_contains hc

theorem le_maxKey_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp k (t.maxKey (ne_empty_of_mem hc)) |>.isLE :=
  ExtDTreeMap.le_maxKey_of_mem hc

theorem maxKey_le [TransCmp cmp] {k he} :
    (cmp (t.maxKey he) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtDTreeMap.maxKey_le

@[simp, grind =]
theorem getKey?_maxKey [TransCmp cmp] {he} :
    t.getKey? (t.maxKey he) = some (t.maxKey he) :=
  ExtDTreeMap.getKey?_maxKey

@[simp, grind =]
theorem getKey_maxKey [TransCmp cmp] {he hc} :
    t.getKey (t.maxKey he) hc = t.maxKey he :=
  ExtDTreeMap.getKey_maxKey

@[simp, grind =]
theorem getKey!_maxKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.maxKey he) = t.maxKey he :=
  ExtDTreeMap.getKey!_maxKey

@[simp, grind =]
theorem getKeyD_maxKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.maxKey he) fallback = t.maxKey he :=
  ExtDTreeMap.getKeyD_maxKey

@[simp]
theorem maxKey_erase_eq_iff_not_compare_eq_maxKey [TransCmp cmp] {k he} :
    (t.erase k |>.maxKey he) =
        t.maxKey (ne_empty_of_erase_ne_empty he) ↔
      ¬ cmp k (t.maxKey <| ne_empty_of_erase_ne_empty he) = .eq :=
  ExtDTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey

theorem maxKey_erase_eq_of_not_compare_eq_maxKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.maxKey (ne_empty_of_erase_ne_empty he)) = .eq) →
    (t.erase k |>.maxKey he) =
      t.maxKey (ne_empty_of_erase_ne_empty he) :=
  ExtDTreeMap.maxKey_erase_eq_of_not_compare_eq_maxKey

theorem maxKey_erase_le_maxKey [TransCmp cmp] {k he} :
    cmp (t.erase k |>.maxKey he)
      (t.maxKey <| ne_empty_of_erase_ne_empty he) |>.isLE :=
  ExtDTreeMap.maxKey_erase_le_maxKey

@[grind =] theorem maxKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey insertIfNew_ne_empty =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  ExtDTreeMap.maxKey_insertIfNew

theorem maxKey_le_maxKey_insertIfNew [TransCmp cmp] {k v he} :
    cmp (t.maxKey he)
      (t.insertIfNew k v |>.maxKey insertIfNew_ne_empty) |>.isLE :=
  ExtDTreeMap.maxKey_le_maxKey_insertIfNew (t := t.inner) (he := mt ext he)

theorem self_le_maxKey_insertIfNew [TransCmp cmp] {k v} :
    cmp k (t.insertIfNew k v |>.maxKey <| insertIfNew_ne_empty) |>.isLE :=
  ExtDTreeMap.self_le_maxKey_insertIfNew

@[grind =_] theorem maxKey_eq_getLast_keys [TransCmp cmp] {he} :
    t.maxKey he = t.keys.getLast (mt keys_eq_nil_iff.mp he) :=
  ExtDTreeMap.maxKey_eq_getLast_keys

theorem maxKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).maxKey he =
      if cmp (t.maxKey (mt modify_eq_empty_iff.mpr he)) k = .eq then
        k
      else
        (t.maxKey (mt modify_eq_empty_iff.mpr he)) :=
  ExtDTreeMap.Const.maxKey_modify

@[simp, grind =]
theorem maxKey_modify_eq_maxKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).maxKey he = t.maxKey (mt modify_eq_empty_iff.mpr he) :=
  ExtDTreeMap.Const.maxKey_modify_eq_maxKey

theorem compare_maxKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.maxKey he)
      (t.maxKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  ExtDTreeMap.Const.compare_maxKey_modify_eq

@[simp]
theorem ordCompare_maxKey_modify_eq [Ord α] [TransOrd α] {t : ExtTreeMap α β} {k f he} :
    compare (modify t k f |>.maxKey he)
      (t.maxKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  compare_maxKey_modify_eq

theorem maxKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).maxKey he = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  ExtDTreeMap.Const.maxKey_alter_eq_self

theorem maxKey?_eq_some_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.maxKey? = some t.maxKey! :=
  ExtDTreeMap.maxKey?_eq_some_maxKey! (mt ext he)

theorem maxKey_eq_maxKey! [TransCmp cmp] [Inhabited α] {he : t ≠ ∅} :
    t.maxKey he = t.maxKey! :=
  ExtDTreeMap.maxKey_eq_maxKey!

theorem maxKey!_empty [TransCmp cmp] [Inhabited α] : (∅ : ExtTreeMap α β cmp).maxKey! = default :=
  ExtDTreeMap.maxKey!_empty

theorem maxKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.maxKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtDTreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem maxKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.maxKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtDTreeMap.maxKey!_eq_iff_mem_and_forall (mt ext he)

@[grind =]
theorem maxKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v).maxKey! =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  ExtDTreeMap.maxKey!_insert

theorem maxKey!_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp t.maxKey! (t.insert k v).maxKey! |>.isLE :=
  ExtDTreeMap.maxKey!_le_maxKey!_insert (mt ext he)

theorem self_le_maxKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    cmp k (t.insert k v).maxKey! |>.isLE :=
  ExtDTreeMap.self_le_maxKey!_insert

theorem contains_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.contains t.maxKey! :=
  ExtDTreeMap.contains_maxKey! (mt ext he)

theorem maxKey!_mem [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.maxKey! ∈ t :=
  ExtDTreeMap.maxKey!_mem (mt ext he)

theorem le_maxKey!_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp k t.maxKey! |>.isLE :=
  ExtDTreeMap.le_maxKey!_of_contains hc

theorem le_maxKey!_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp k t.maxKey! |>.isLE :=
  ExtDTreeMap.le_maxKey!_of_mem hc

theorem maxKey!_le [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    (cmp t.maxKey! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtDTreeMap.maxKey!_le (mt ext he)

theorem getKey?_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey? t.maxKey! = some t.maxKey! :=
  ExtDTreeMap.getKey?_maxKey! (mt ext he)

@[grind =] theorem getKey_maxKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.maxKey! hc = t.maxKey! :=
  ExtDTreeMap.getKey_maxKey!

@[simp, grind =]
theorem getKey_maxKey!_eq_maxKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.maxKey! hc = t.maxKey (ne_empty_of_mem hc) :=
  ExtDTreeMap.getKey_maxKey!_eq_maxKey

theorem getKey!_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey! t.maxKey! = t.maxKey! :=
  ExtDTreeMap.getKey!_maxKey! (mt ext he)

theorem getKeyD_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKeyD t.maxKey! fallback = t.maxKey! :=
  ExtDTreeMap.getKeyD_maxKey! (mt ext he)

theorem maxKey!_erase_eq_of_not_compare_maxKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k t.maxKey! = .eq) :
    (t.erase k).maxKey! = t.maxKey! :=
  ExtDTreeMap.maxKey!_erase_eq_of_not_compare_maxKey!_eq (mt ext he) heq

theorem maxKey!_erase_le_maxKey! [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) :
    cmp (t.erase k).maxKey! t.maxKey! |>.isLE :=
  ExtDTreeMap.maxKey!_erase_le_maxKey! (mt ext he)

@[grind =]
theorem maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v).maxKey! =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  ExtDTreeMap.maxKey!_insertIfNew

theorem maxKey!_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp t.maxKey! (t.insertIfNew k v).maxKey! |>.isLE :=
  ExtDTreeMap.maxKey!_le_maxKey!_insertIfNew (mt ext he)

theorem self_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    cmp k (t.insertIfNew k v).maxKey! |>.isLE :=
  ExtDTreeMap.self_le_maxKey!_insertIfNew

@[grind =_]
theorem maxKey!_eq_getLast!_keys [TransCmp cmp] [Inhabited α] :
    t.maxKey! = t.keys.getLast! :=
  ExtDTreeMap.maxKey!_eq_getLast!_keys

theorem maxKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : modify t k f ≠ ∅) :
    (modify t k f).maxKey! = if cmp t.maxKey! k = .eq then k else t.maxKey! :=
  ExtDTreeMap.Const.maxKey!_modify (mt ext he)

@[simp]
theorem maxKey!_modify_eq_maxKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f).maxKey! = t.maxKey! :=
  ExtDTreeMap.Const.maxKey!_modify_eq_maxKey!

theorem compare_maxKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f).maxKey! t.maxKey! = .eq :=
  ExtDTreeMap.Const.compare_maxKey!_modify_eq

@[simp]
theorem ordCompare_maxKey!_modify_eq [Ord α] [TransOrd α] {t : ExtTreeMap α β} [Inhabited α] {k f} :
    compare (modify t k f).maxKey! t.maxKey! = .eq :=
  compare_maxKey!_modify_eq

theorem maxKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : alter t k f ≠ ∅) :
    (alter t k f).maxKey! = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  ExtDTreeMap.Const.maxKey!_alter_eq_self (mt ext he)

theorem maxKey?_eq_some_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.maxKey? = some (t.maxKeyD fallback) :=
  ExtDTreeMap.maxKey?_eq_some_maxKeyD (mt ext he)

theorem maxKeyD_empty [TransCmp cmp] {fallback} : (∅ : ExtTreeMap α β cmp).maxKeyD fallback = fallback :=
  ExtDTreeMap.maxKeyD_empty

theorem maxKey!_eq_maxKeyD_default [TransCmp cmp] [Inhabited α] :
    t.maxKey! = t.maxKeyD default :=
  ExtDTreeMap.maxKey!_eq_maxKeyD_default

theorem maxKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.maxKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtDTreeMap.maxKeyD_eq_iff_getKey?_eq_self_and_forall (mt ext he)

theorem maxKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  ExtDTreeMap.maxKeyD_eq_iff_mem_and_forall (mt ext he)

@[grind =]
theorem maxKeyD_insert [TransCmp cmp] {k v fallback} :
    (t.insert k v |>.maxKeyD fallback) =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  ExtDTreeMap.maxKeyD_insert

theorem maxKeyD_le_maxKeyD_insert [TransCmp cmp] (he : t ≠ ∅)
    {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.maxKeyD_le_maxKeyD_insert (mt ext he)

theorem self_le_maxKeyD_insert [TransCmp cmp] {k v fallback} :
    cmp k (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.self_le_maxKeyD_insert

theorem contains_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.contains (t.maxKeyD fallback) :=
  ExtDTreeMap.contains_maxKeyD (mt ext he)

theorem maxKeyD_mem [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.maxKeyD fallback ∈ t :=
  ExtDTreeMap.maxKeyD_mem (mt ext he)

theorem le_maxKeyD_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.le_maxKeyD_of_contains hc

theorem le_maxKeyD_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.le_maxKeyD_of_mem hc

theorem maxKeyD_le [TransCmp cmp] (he : t ≠ ∅) {k fallback} :
    (cmp (t.maxKeyD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  ExtDTreeMap.maxKeyD_le (mt ext he)

theorem getKey?_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.getKey? (t.maxKeyD fallback) = some (t.maxKeyD fallback) :=
  ExtDTreeMap.getKey?_maxKeyD (mt ext he)

@[grind =] theorem getKey_maxKeyD [TransCmp cmp] {fallback hc} :
    t.getKey (t.maxKeyD fallback) hc = t.maxKeyD fallback :=
  ExtDTreeMap.getKey_maxKeyD

theorem getKey!_maxKeyD [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKey! (t.maxKeyD fallback) = t.maxKeyD fallback :=
  ExtDTreeMap.getKey!_maxKeyD (mt ext he)

theorem getKeyD_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback fallback'} :
    t.getKeyD (t.maxKeyD fallback) fallback' = t.maxKeyD fallback :=
  ExtDTreeMap.getKeyD_maxKeyD (mt ext he)

theorem maxKeyD_erase_eq_of_not_compare_maxKeyD_eq [TransCmp cmp] {k fallback}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k (t.maxKeyD fallback) = .eq) :
    (t.erase k |>.maxKeyD fallback) = t.maxKeyD fallback :=
  ExtDTreeMap.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq (mt ext he) heq

theorem maxKeyD_erase_le_maxKeyD [TransCmp cmp] {k}
    (he : t.erase k ≠ ∅) {fallback} :
    cmp (t.erase k |>.maxKeyD fallback) (t.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.maxKeyD_erase_le_maxKeyD (mt ext he)

@[grind =]
theorem maxKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    (t.insertIfNew k v |>.maxKeyD fallback) =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  ExtDTreeMap.maxKeyD_insertIfNew

theorem maxKeyD_le_maxKeyD_insertIfNew [TransCmp cmp]
    (he : t ≠ ∅) {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.maxKeyD_le_maxKeyD_insertIfNew (mt ext he)

theorem self_le_maxKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    cmp k (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  ExtDTreeMap.self_le_maxKeyD_insertIfNew

theorem maxKeyD_eq_getLastD_keys [TransCmp cmp] {fallback} :
    t.maxKeyD fallback = t.keys.getLastD fallback :=
  ExtDTreeMap.maxKeyD_eq_getLastD_keys

theorem maxKeyD_modify [TransCmp cmp] {k f}
    (he : modify t k f ≠ ∅) {fallback} :
    (modify t k f |>.maxKeyD fallback) =
      if cmp (t.maxKeyD fallback) k = .eq then k else (t.maxKeyD fallback) :=
  ExtDTreeMap.Const.maxKeyD_modify (mt ext he)

@[simp, grind =]
theorem maxKeyD_modify_eq_maxKeyD [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (modify t k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  ExtDTreeMap.Const.maxKeyD_modify_eq_maxKeyD

theorem compare_maxKeyD_modify_eq [TransCmp cmp] {k f fallback} :
    cmp (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  ExtDTreeMap.Const.compare_maxKeyD_modify_eq

@[simp]
theorem ordCompare_maxKeyD_modify_eq [Ord α] [TransOrd α] {t : ExtTreeMap α β} {k f fallback} :
    compare (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  compare_maxKeyD_modify_eq

theorem maxKeyD_alter_eq_self [TransCmp cmp] {k f}
    (he : alter t k f ≠ ∅) {fallback} :
    (alter t k f |>.maxKeyD fallback) = k ↔
      (f t[k]?).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  ExtDTreeMap.Const.maxKeyD_alter_eq_self (mt ext he)

end Max

section Ext

variable {t₁ t₂ : ExtTreeMap α β cmp}

@[ext 900, grind ext]
theorem ext_getKey_getElem? [TransCmp cmp] {t₁ t₂ : ExtTreeMap α β cmp}
    (hk : ∀ k hk hk', t₁.getKey k hk = t₂.getKey k hk')
    (hv : ∀ k : α, t₁[k]? = t₂[k]?) : t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_getKey_get? hk hv)

@[ext]
theorem ext_getElem? [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : ExtTreeMap α β cmp}
    (h : ∀ k : α, t₁[k]? = t₂[k]?) : t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_get? h)

theorem ext_getKey?_unit [TransCmp cmp] {t₁ t₂ : ExtTreeMap α Unit cmp}
    (h : ∀ k, t₁.getKey? k = t₂.getKey? k) : t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_getKey?_unit h)

theorem ext_contains_unit [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : ExtTreeMap α Unit cmp}
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_contains_unit h)

theorem ext_mem_unit [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : ExtTreeMap α Unit cmp}
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_mem_unit h)

theorem toList_inj [TransCmp cmp] {t₁ t₂ : ExtTreeMap α β cmp} :
    t₁.toList = t₂.toList ↔ t₁ = t₂ :=
  ExtDTreeMap.Const.toList_inj.trans ext_iff.symm

theorem ext_toList [TransCmp cmp] (h : t₁.toList.Perm t₂.toList) : t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_toList h)

theorem ext_keys_unit [TransCmp cmp] {t₁ t₂ : ExtTreeMap α Unit cmp} (h : t₁.keys.Perm t₂.keys) :
    t₁ = t₂ :=
  ext (ExtDTreeMap.Const.ext_keys_unit h)

end Ext

section filterMap

variable {t : ExtTreeMap α β cmp}

@[simp, grind =]
theorem toList_filterMap [TransCmp cmp] {f : (a : α) → β → Option γ} :
    (t.filterMap f).toList =
      t.toList.filterMap (fun p => (f p.1 p.2).map (fun x => (p.1, x))) :=
  ExtDTreeMap.Const.toList_filterMap

theorem filterMap_eq_empty_iff [TransCmp cmp] {f : α → β → Option γ} :
    t.filterMap f = ∅ ↔ ∀ k h, f (t.getKey k h) (t[k]'h) = none :=
  ext_iff.trans ExtDTreeMap.Const.filterMap_eq_empty_iff

-- TODO: `contains_filterMap` is missing

@[grind =]
theorem mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    k ∈ t.filterMap f ↔ ∃ h, (f (t.getKey k h) t[k]).isSome :=
  ExtDTreeMap.Const.mem_filterMap

theorem contains_of_contains_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f).contains k = true → t.contains k = true :=
  ExtDTreeMap.contains_of_contains_filterMap

theorem mem_of_mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    k ∈ t.filterMap f → k ∈ t :=
  ExtDTreeMap.mem_of_mem_filterMap

theorem size_filterMap_le_size [TransCmp cmp]
    {f : α → β → Option γ} :
    (t.filterMap f).size ≤ t.size :=
  ExtDTreeMap.size_filterMap_le_size

grind_pattern size_filterMap_le_size => (t.filterMap f).size

theorem size_filterMap_eq_size_iff [TransCmp cmp]
    {f : α → β → Option γ} :
    (t.filterMap f).size = t.size ↔ ∀ k h, (f (t.getKey k h) t[k]).isSome :=
  ExtDTreeMap.Const.size_filterMap_eq_size_iff

@[simp]
theorem getElem?_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f)[k]? = t[k]?.pbind (fun x h' =>
      f (t.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x) :=
  ExtDTreeMap.Const.get?_filterMap

/-- Simpler variant of `getElem?_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem?_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f)[k]? = t[k]?.bind fun x => f k x := by
  simp [getElem?_filterMap]

theorem getElem?_filterMap_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Option γ} {k k' : α} (h : t.getKey? k = some k') :
    (t.filterMap f)[k]? = t[k]?.bind (f k') :=
  ExtDTreeMap.Const.get?_filterMap_of_getKey?_eq_some h

theorem isSome_apply_of_mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ t.filterMap f),
      (f (t.getKey k (mem_of_mem_filterMap h))
        (t[k]'(mem_of_mem_filterMap h))).isSome :=
  ExtDTreeMap.Const.isSome_apply_of_mem_filterMap

@[simp]
theorem getElem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {h} :
    (t.filterMap f)[k]'h =
      (f (t.getKey k (mem_of_mem_filterMap h))
        (t[k]'(mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  ExtDTreeMap.Const.get_filterMap (h := h)

/-- Simpler variant of `getElem_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} {h} :
    (t.filterMap f)[k]'h =
      (f k (t[k]'(mem_of_mem_filterMap h))).get (by simpa using isSome_apply_of_mem_filterMap h) := by
  simp [getElem_filterMap]

theorem getElem!_filterMap [TransCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f)[k]! =
      (t[k]?.pbind (fun x h' =>
        f (t.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  ExtDTreeMap.Const.get!_filterMap

/-- Simpler variant of `getElem!_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem!_filterMap' [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f)[k]! = (t[k]?.bind (f k)).get! := by
  simp [getElem!_filterMap]

theorem getElem!_filterMap_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : t.getKey? k = some k') :
    (t.filterMap f)[k]! = (t[k]?.bind (f k')).get! :=
  ExtDTreeMap.Const.get!_filterMap_of_getKey?_eq_some h

theorem getD_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    (t.filterMap f).getD k fallback =
      (t[k]?.pbind (fun x h' =>
      f (t.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  ExtDTreeMap.Const.getD_filterMap

/-- Simpler variant of `getD_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getD_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    (t.filterMap f).getD k fallback = (t[k]?.bind (f k)).getD fallback := by
  simp [getD_filterMap]

theorem getD_filterMap_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : t.getKey? k = some k') :
    (t.filterMap f).getD k fallback = (t[k]?.bind (f k')).getD fallback :=
  ExtDTreeMap.Const.getD_filterMap_of_getKey?_eq_some h

@[grind =]
theorem getKey?_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h'))).isSome) :=
  ExtDTreeMap.Const.getKey?_filterMap

@[simp, grind =]
theorem getKey_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {h'} :
    (t.filterMap f).getKey k h' = t.getKey k (mem_of_mem_filterMap h') :=
  ExtDTreeMap.getKey_filterMap

@[grind =]
theorem getKey!_filterMap [TransCmp cmp] [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h'))).isSome)).get! :=
  ExtDTreeMap.Const.getKey!_filterMap

@[grind =]
theorem getKeyD_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k fallback : α} :
    (t.filterMap f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  ExtDTreeMap.Const.getKeyD_filterMap

end filterMap

section filter

variable {t : ExtTreeMap α β cmp}

theorem filterMap_equiv_filter {f : α → β → Bool} :
    t.filterMap (fun k => Option.guard (fun v => f k v)) = t.filter f :=
  ext ExtDTreeMap.filterMap_eq_filter

@[simp, grind =]
theorem toList_filter [TransCmp cmp] {f : α → β → Bool} :
    (t.filter f).toList = t.toList.filter (fun p => f p.1 p.2) :=
  ExtDTreeMap.Const.toList_filter

theorem keys_filter_key [TransCmp cmp] {f : α → Bool} :
    (t.filter fun k _ => f k).keys = t.keys.filter f :=
  ExtDTreeMap.keys_filter_key

theorem filter_eq_empty_iff [TransCmp cmp] {f : α → β → Bool} :
    t.filter f = ∅ ↔ ∀ k h, f (t.getKey k h) (t[k]'h) = false :=
  ext_iff.trans ExtDTreeMap.Const.filter_eq_empty_iff

-- TODO: `contains_filter` is missing

@[grind =]
theorem mem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    k ∈ t.filter f ↔ ∃ (h' : k ∈ t), f (t.getKey k h') t[k] :=
  ExtDTreeMap.Const.mem_filter

theorem contains_of_contains_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    (t.filter f).contains k = true → t.contains k = true :=
  ExtDTreeMap.contains_of_contains_filter

theorem mem_of_mem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    k ∈ t.filter f → k ∈ t :=
  ExtDTreeMap.mem_of_mem_filter

theorem size_filter_le_size [TransCmp cmp]
    {f : α → β → Bool} :
    (t.filter f).size ≤ t.size :=
  ExtDTreeMap.size_filter_le_size

grind_pattern size_filter_le_size => (t.filter f).size

theorem size_filter_eq_size_iff [TransCmp cmp]
    {f : α → β → Bool} :
    (t.filter f).size = t.size ↔ ∀ k h, f (t.getKey k h) (t[k]'h) :=
  ExtDTreeMap.Const.size_filter_eq_size_iff

theorem filter_eq_self_iff [TransCmp cmp]
    {f : α → β → Bool} :
    t.filter f = t ↔ ∀ k h, f (t.getKey k h) (t[k]'h) :=
  ext_iff.trans ExtDTreeMap.Const.filter_eq_self_iff

@[simp]
theorem getElem?_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    (t.filter f)[k]? = t[k]?.pfilter (fun x h' =>
      f (t.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x) :=
  ExtDTreeMap.Const.get?_filter

/-- Simpler variant of `getElem?_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem?_filter' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Bool} {k : α} :
    (t.filter f)[k]? = t[k]?.filter (f k) := by
  simp [getElem?_filter]

theorem getElem?_filter_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Bool} {k k' : α} :
    t.getKey? k = some k' →
      (t.filter f)[k]? = t[k]?.filter (fun x => f k' x) :=
  ExtDTreeMap.Const.get?_filter_of_getKey?_eq_some

@[simp, grind =]
theorem getElem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {h'} :
    (t.filter f)[k]'(h') = t[k]'(mem_of_mem_filter h') :=
  ExtDTreeMap.Const.get_filter (h' := h')

theorem getElem!_filter [TransCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    (t.filter f)[k]! =
      (t[k]?.pfilter (fun x h' =>
      f (t.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  ExtDTreeMap.Const.get!_filter

/-- Simpler variant of `getElem!_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getElem!_filter' [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    (t.filter f)[k]! = (t[k]?.filter (f k)).get! := by
  simp [getElem!_filter]

theorem getElem!_filter_of_getKey?_eq_some [TransCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k k' : α} :
    t.getKey? k = some k' →
      (t.filter f)[k]! = (t[k]?.filter (f k')).get! :=
  ExtDTreeMap.Const.get!_filter_of_getKey?_eq_some

theorem getD_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {fallback : β} :
    (t.filter f).getD k fallback = (t[k]?.pfilter (fun x h' =>
      f (t.getKey k (mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  ExtDTreeMap.Const.getD_filter

/-- Simpler variant of `getD_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getD_filter' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Bool} {k : α} {fallback : β} :
    (t.filter f).getD k fallback = (t[k]?.filter (f k)).getD fallback := by
  simp [getD_filter]

theorem getD_filter_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Bool} {k k' : α} {fallback : β} :
    t.getKey? k = some k' →
      (t.filter f).getD k fallback =
        (t[k]?.filter (fun x => f k' x)).getD fallback :=
  ExtDTreeMap.Const.getD_filter_of_getKey?_eq_some

theorem keys_filter [TransCmp cmp] {f : α → β → Bool} :
    (t.filter f).keys =
      (t.keys.attach.filter (fun ⟨x, h'⟩ => f x (t[x]'(mem_of_mem_keys h')))).unattach :=
  ExtDTreeMap.Const.keys_filter

@[grind =]
theorem getKey?_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    (t.filter f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h')))) :=
  ExtDTreeMap.Const.getKey?_filter

theorem getKey?_filter_key [TransCmp cmp]
    {f : α → Bool} {k : α} :
    (t.filter fun k _ => f k).getKey? k = (t.getKey? k).filter f :=
  ExtDTreeMap.getKey?_filter_key

@[simp, grind =]
theorem getKey_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {h'} :
    (t.filter f).getKey k h' = t.getKey k (mem_of_mem_filter h') :=
  ExtDTreeMap.getKey_filter

@[grind =]
theorem getKey!_filter [TransCmp cmp] [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (t.filter f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h'))))).get! :=
  ExtDTreeMap.Const.getKey!_filter

theorem getKey!_filter_key [TransCmp cmp] [Inhabited α]
    {f : α → Bool} {k : α} :
    (t.filter fun k _ => f k).getKey! k = ((t.getKey? k).filter f).get! :=
  ExtDTreeMap.getKey!_filter_key

@[grind =]
theorem getKeyD_filter [TransCmp cmp]
    {f : α → β → Bool} {k fallback : α} :
    (t.filter f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t[x]'(mem_of_getKey?_eq_some h'))))).getD fallback :=
  ExtDTreeMap.Const.getKeyD_filter

theorem getKeyD_filter_key [TransCmp cmp]
    {f : α → Bool} {k fallback : α} :
    (t.filter fun k _ => f k).getKeyD k fallback = ((t.getKey? k).filter f).getD fallback :=
  ExtDTreeMap.getKeyD_filter_key

end filter

section map

variable {t : ExtTreeMap α β cmp}

@[simp]
theorem map_id : t.map (fun _ v => v) = t :=
  ext ExtDTreeMap.map_id

@[simp, grind =]
theorem map_map {f : α → β → γ} {g : α → γ → δ} :
    (t.map f).map g = t.map fun k v => g k (f k v) :=
  ext ExtDTreeMap.map_map

@[simp, grind =]
theorem toList_map [TransCmp cmp] {f : α → β → γ} :
    (t.map f).toList = t.toList.map (fun p => (p.1, f p.1 p.2)) :=
  ExtDTreeMap.Const.toList_map

@[simp, grind =]
theorem keys_map [TransCmp cmp] {f : α → β → γ} : (t.map f).keys = t.keys :=
  ExtDTreeMap.keys_map

theorem filterMap_eq_map [TransCmp cmp]
    {f : α → β → γ} :
    t.filterMap (fun k v => some (f k v)) = t.map f :=
  ext ExtDTreeMap.filterMap_eq_map

@[simp]
theorem map_eq_empty_iff [TransCmp cmp] {f : α → β → γ} :
    t.map f = ∅ ↔ t = ∅ := by
  simpa only [ext_iff] using ExtDTreeMap.map_eq_empty_iff

@[simp, grind =]
theorem contains_map [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    (t.map f).contains k = t.contains k :=
  ExtDTreeMap.contains_map

theorem contains_of_contains_map [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    (t.map f).contains k = true → t.contains k = true :=
  ExtDTreeMap.contains_of_contains_map

@[simp, grind =]
theorem mem_map [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    k ∈ t.map f ↔ k ∈ t := by
  simp only [mem_iff_contains, contains_map]

theorem mem_of_mem_map [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    k ∈ t.map f → k ∈ t :=
  ExtDTreeMap.contains_of_contains_map

@[simp, grind =]
theorem size_map [TransCmp cmp]
    {f : α → β → γ} :
    (t.map f).size = t.size :=
  ExtDTreeMap.size_map

@[simp, grind =]
theorem getElem?_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} :
    (t.map f)[k]? = t[k]?.map (f k) :=
  ExtDTreeMap.Const.get?_map

/-- Variant of `getElem?_map` that holds without `LawfulEqCmp`. -/
@[simp (low)]
theorem getElem?_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    (t.map f)[k]? = t[k]?.pmap (fun v h' => f (t.getKey k h') v)
      (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h')) :=
  ExtDTreeMap.Const.get?_map'

theorem getElem?_map_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → γ} {k k' : α} (h : t.getKey? k = some k') :
    (t.map f)[k]? = t[k]?.map (f k') :=
  ExtDTreeMap.Const.get?_map_of_getKey?_eq_some h

@[simp, grind =]
theorem getElem_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} {h'} :
    (t.map f)[k]'(h') =
      f k (t[k]'(mem_of_mem_map h')) :=
  ExtDTreeMap.Const.get_map (h' := h')

/-- Variant of `getElem_map` that holds without `LawfulEqCmp`. -/
@[simp (low)]
theorem getElem_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} {h'} :
    (t.map f)[k]'(h') =
      f (t.getKey k (mem_of_mem_map h')) (t[k]'(mem_of_mem_map h')) :=
  ExtDTreeMap.Const.get_map' (h' := h')

@[grind =]
theorem getElem!_map [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    (t.map f)[k]! =
      (t[k]?.map (f k)).get! :=
  ExtDTreeMap.Const.get!_map

/-- Variant of `getElem!_map` that holds without `LawfulEqCmp`. -/
theorem getElem!_map' [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    (t.map f)[k]! =
      (t[k]?.pmap (fun v h => f (t.getKey k h) v)
        (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_mem h'))).get! :=
  ExtDTreeMap.Const.get!_map'

theorem getElem!_map_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : t.getKey? k = some k') :
    (t.map f)[k]! = (t[k]?.map (f k')).get! :=
  ExtDTreeMap.Const.get!_map_of_getKey?_eq_some h

@[grind =]
theorem getD_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} {fallback : γ} :
    (t.map f).getD k fallback =
      (t[k]?.map (f k)).getD fallback :=
  ExtDTreeMap.Const.getD_map

/-- Variant of `getD_map` that holds without `LawfulEqCmp`. -/
theorem getD_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} {fallback : γ} :
    (t.map f).getD k fallback =
      (t[k]?.pmap (fun v h => f (t.getKey k h) v)
        (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  ExtDTreeMap.Const.getD_map'

theorem getD_map_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : t.getKey? k = some k') :
    (t.map f).getD k fallback = (t[k]?.map (f k')).getD fallback :=
  ExtDTreeMap.Const.getD_map_of_getKey?_eq_some h

@[simp, grind =]
theorem getKey?_map [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    (t.map f).getKey? k = t.getKey? k :=
  ExtDTreeMap.getKey?_map

@[simp, grind =]
theorem getKey_map [TransCmp cmp]
    {f : α → β → γ} {k : α} {h'} :
    (t.map f).getKey k h' = t.getKey k (mem_of_mem_map h') :=
  ExtDTreeMap.getKey_map

@[simp, grind =]
theorem getKey!_map [TransCmp cmp] [Inhabited α]
    {f : α → β → γ} {k : α} :
    (t.map f).getKey! k = t.getKey! k :=
  ExtDTreeMap.getKey!_map

@[simp, grind =]
theorem getKeyD_map [TransCmp cmp]
    {f : α → β → γ} {k fallback : α} :
    (t.map f).getKeyD k fallback = t.getKeyD k fallback :=
  ExtDTreeMap.getKeyD_map

end map

end Std.ExtTreeMap
