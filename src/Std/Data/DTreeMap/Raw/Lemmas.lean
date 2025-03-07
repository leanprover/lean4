/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.Lemmas
import Std.Data.DTreeMap.Raw.Basic

/-!
# Dependent tree map lemmas

This file contains lemmas about `Std.Data.DTreeMap.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp` and a proof that the involved maps are well-formed.
These proofs can be obtained from `Std.Data.DTreeMap.Raw.WF`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v w

namespace Std.DTreeMap.Raw

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap.Raw α β cmp}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

private theorem ext {t t' : Raw α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : DTreeMap.Raw α β cmp).isEmpty :=
  Impl.isEmpty_empty

@[simp]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).isEmpty = false :=
  Impl.isEmpty_insert! h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr h hab

@[simp]
theorem contains_emptyc {k : α} : (∅ : Raw α β cmp).contains k = false :=
  Impl.contains_empty

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : Raw α β cmp) :=
  Impl.not_mem_empty

theorem contains_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → t.contains a = false :=
  Impl.contains_of_isEmpty h

theorem not_mem_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → a ∉ t :=
  Impl.not_mem_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  Impl.isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  Impl.isEmpty_eq_false_iff_exists_mem h

theorem isEmpty_iff_forall_contains [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  Impl.isEmpty_iff_forall_contains h

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  Impl.isEmpty_iff_forall_not_mem h

@[simp]
theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : Raw α β cmp).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insert! h

@[simp]
theorem mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insert! h

theorem contains_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).contains k :=
  Impl.contains_insert!_self h

theorem mem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insert k v :=
  Impl.mem_insert!_self h

theorem contains_of_contains_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insert! h

theorem mem_of_mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.mem_of_mem_insert! h

@[simp]
theorem size_emptyc : (∅ : Raw α β cmp).size = 0 :=
  Impl.size_empty

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  Impl.isEmpty_eq_size_eq_zero h.out

theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  Impl.size_insert! h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v).size :=
  Impl.size_le_size_insert! h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size ≤ t.size + 1 :=
  Impl.size_insert!_le h

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : Raw α β cmp).erase k = ∅ :=
  ext <| Impl.erase!_empty (instOrd := ⟨cmp⟩) (k := k)

@[simp]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  Impl.isEmpty_erase! h

@[simp]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  Impl.contains_erase! h

@[simp]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  Impl.mem_erase! h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  Impl.contains_of_contains_erase! h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  Impl.mem_of_mem_erase! h

theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  Impl.size_erase! h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  Impl.size_erase!_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  Impl.size_le_size_erase! h

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).1 = t.contains k :=
  Impl.containsThenInsert!_fst h

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| Impl.containsThenInsert!_snd h

@[simp]
theorem containsThenInsertIfNew_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  Impl.containsThenInsertIfNew!_fst h

@[simp]
theorem containsThenInsertIfNew_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| Impl.containsThenInsertIfNew!_snd h

@[simp]
theorem get?_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (∅ : DTreeMap α β cmp).get? a = none :=
  Impl.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none :=
  Impl.get?_of_isEmpty h

theorem get?_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).get? a =
      if h : cmp k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a :=
  Impl.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get? k = some v :=
  Impl.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome :=
  Impl.contains_eq_isSome_get? h

theorem mem_iff_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  Impl.mem_iff_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none :=
  Impl.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  Impl.get?_eq_none h

theorem get?_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  Impl.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).get? k = none :=
  Impl.get?_erase!_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem get?_emptyc [TransCmp cmp] {a : α} :
    get? (∅ : Raw α β cmp) a = none :=
  Impl.Const.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → get? t a = none :=
  Impl.Const.get?_of_isEmpty h

theorem get?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert k v) a =
      if cmp k a = .eq then some v else get? t a :=
  Impl.Const.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get? (t.insert k v) k = some v :=
  Impl.Const.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (get? t a).isSome :=
  Impl.Const.contains_eq_isSome_get? h

theorem mem_iff_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (get? t a).isSome :=
  Impl.Const.mem_iff_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → get? t a = none :=
  Impl.Const.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → get? t a = none :=
  Impl.Const.get?_eq_none h

theorem get?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    get? (t.erase k) a = if cmp k a = .eq then none else get? t a :=
  Impl.Const.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    get? (t.erase k) k = none :=
  Impl.Const.get?_erase!_self h

theorem get?_eq_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} : get? t a = t.get? a :=
  Impl.Const.get?_eq_get? h

theorem get?_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get? t a = get? t b :=
  Impl.Const.get?_congr h hab

end Const

theorem get_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).get a h₁ =
      if h₂ : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (mem_of_mem_insert h h₁ h₂) :=
  Impl.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get k (mem_insert_self h) = v :=
  Impl.get_insert!_self h

@[simp]
theorem get_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h h') :=
  Impl.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  Impl.get?_eq_some_get h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem get_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (mem_of_mem_insert h h₁ h₂) :=
  Impl.Const.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v) k (mem_insert_self h) = v :=
  Impl.Const.get_insert!_self h

@[simp]
theorem get_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    get (t.erase k) a h' = get t a (mem_of_mem_erase h h') :=
  Impl.Const.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    get? t a = some (get t a h') :=
  Impl.Const.get?_eq_some_get h

theorem get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    get t a h' = t.get a h' :=
  Impl.Const.get_eq_get h

theorem get_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    get t a h' = get t b ((mem_congr h hab).mp h') :=
  Impl.Const.get_congr h hab

end Const

@[simp]
theorem get!_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default :=
  Impl.get!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)]
    {v : β k} : (t.insert k v).get! a =
      if h : cmp k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a :=
  Impl.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)]
    {b : β a} : (t.insert a b).get! a = b :=
  Impl.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default :=
  Impl.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default :=
  Impl.get!_eq_default h

theorem get!_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  Impl.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase k).get! k = default :=
  Impl.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = true → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get!_of_contains h

theorem get?_eq_some_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! :=
  Impl.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] {h'} :
    t.get a h' = t.get! a :=
  Impl.get_eq_get! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem get!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.Const.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → get! t a = default :=
  Impl.Const.get!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else get! t a :=
  Impl.Const.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} {v : β} :
    get! (t.insert k v) k = v :=
  Impl.Const.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → get! t a = default :=
  Impl.Const.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → get! t a = default :=
  Impl.Const.get!_eq_default h

theorem get!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else get! t a :=
  Impl.Const.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k) k = default :=
  Impl.Const.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = (get? t a).get! :=
  Impl.Const.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} {h'} :
    get t a h' = get! t a :=
  Impl.Const.get_eq_get! h

theorem get!_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = t.get! a :=
  Impl.Const.get!_eq_get! h

theorem get!_congr [TransCmp cmp] [Inhabited β] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get! t a = get! t b :=
  Impl.Const.get!_congr h hab

end Const

@[simp]
theorem getD_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    (∅ : DTreeMap α β cmp).getD a fallback = fallback :=
  Impl.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  Impl.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v).getD a fallback =
      if h : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback :=
  Impl.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert a b).getD a fallback = b :=
  Impl.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = false → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback h

theorem getD_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase k).getD a fallback = if cmp k a = .eq then fallback else t.getD a fallback :=
  Impl.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase k).getD k fallback = fallback :=
  Impl.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    {fallback : β a} : t.contains a = true → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback :=
  Impl.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} {h'} :
    t.get a h' = t.getD a fallback :=
  Impl.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default :=
  Impl.get!_eq_getD_default h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  Impl.Const.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  Impl.Const.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  Impl.Const.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  Impl.Const.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback h

theorem getD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  Impl.Const.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  Impl.Const.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback :=
  Impl.Const.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} {h'} :
    get t a h' = getD t a fallback :=
  Impl.Const.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = getD t a default :=
  Impl.Const.get!_eq_getD_default h

theorem getD_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback :=
  Impl.Const.getD_eq_getD h

theorem getD_congr [TransCmp cmp] (h : t.WF) {a b : α} {fallback : β} (hab : cmp a b = .eq) :
    getD t a fallback = getD t b fallback :=
  Impl.Const.getD_congr h hab

end Const

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : DTreeMap α β cmp).getKey? a = none :=
  Impl.getKey?_empty

theorem getKey?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  Impl.getKey?_of_isEmpty h

theorem getKey?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  Impl.getKey?_insert! h

@[simp]
theorem getKey?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).getKey? k = some k :=
  Impl.getKey?_insert!_self h

theorem contains_eq_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  Impl.contains_eq_isSome_getKey? h

theorem mem_iff_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  Impl.mem_iff_isSome_getKey? h

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none :=
  Impl.getKey?_eq_none_of_contains_eq_false h

theorem getKey?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  Impl.getKey?_eq_none h

theorem getKey?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  Impl.getKey?_erase! h

@[simp]
theorem getKey?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).getKey? k = none :=
  Impl.getKey?_erase!_self h

theorem getKey_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then
        k
      else
        t.getKey a (mem_of_mem_insert h h₁ h₂) :=
  Impl.getKey_insert! h

@[simp]
theorem getKey_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).getKey k (mem_insert_self h) = k :=
  Impl.getKey_insert!_self h

@[simp]
theorem getKey_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h h') :=
  Impl.getKey_erase! h

theorem getKey?_eq_some_getKey [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  Impl.getKey?_eq_some_getKey h

@[simp]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : DTreeMap α β cmp).getKey! a = default :=
  Impl.getKey!_empty

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  Impl.getKey!_of_isEmpty h

theorem getKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  Impl.getKey!_insert! h

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {b : β a} :
    (t.insert a b).getKey! a = a :=
  Impl.getKey!_insert!_self h

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey! a = default :=
  Impl.getKey!_eq_default_of_contains_eq_false h

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  Impl.getKey!_eq_default h

theorem getKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  Impl.getKey!_erase! h

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k).getKey! k = default :=
  Impl.getKey!_erase!_self h

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey!_of_contains h

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey! h

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  Impl.getKey!_eq_get!_getKey? h

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {h'} :
    t.getKey a h' = t.getKey! a :=
  Impl.getKey_eq_getKey! h

@[simp]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : DTreeMap α β cmp).getKeyD a fallback = fallback :=
  Impl.getKeyD_empty

theorem getKeyD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_of_isEmpty h

theorem getKeyD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert k v).getKeyD a fallback = if cmp k a = .eq then k else t.getKeyD a fallback :=
  Impl.getKeyD_insert! h

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] (h : t.WF) {a fallback : α} {b : β a} :
    (t.insert a b).getKeyD a fallback = a :=
  Impl.getKeyD_insert!_self h

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_eq_fallback [TransCmp cmp] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback h

theorem getKeyD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  Impl.getKeyD_erase! h

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] (h : t.WF) {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  Impl.getKeyD_erase!_self h

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD_of_contains h

theorem getKey?_eq_some_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} :
    a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD h

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  Impl.getKeyD_eq_getD_getKey? h

theorem getKey_eq_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} {h'} :
    t.getKey a h' = t.getKeyD a fallback :=
  Impl.getKey_eq_getKeyD h

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = t.getKeyD a default :=
  Impl.getKey!_eq_getKeyD_default h

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew! h

@[simp]
theorem contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insertIfNew! h

@[simp]
theorem mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insertIfNew! h

theorem contains_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).contains k :=
  Impl.contains_insertIfNew!_self h

theorem mem_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNew k v :=
  Impl.mem_insertIfNew!_self h

theorem contains_of_contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insertIfNew! h

theorem mem_of_mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.contains_of_contains_insertIfNew! h

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  Impl.mem_of_mem_insertIfNew!' h

theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  Impl.size_insertIfNew! h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  Impl.size_le_size_insertIfNew! h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  Impl.size_insertIfNew!_le h

theorem get?_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).get? a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a :=
  Impl.get?_insertIfNew! h

theorem get_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.get_insertIfNew! h

theorem get!_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v).get! a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a :=
  Impl.get!_insertIfNew! h

theorem getD_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v).getD a fallback =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback :=
  Impl.getD_insertIfNew! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem get?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else get? t a :=
  Impl.Const.get?_insertIfNew! h

theorem get_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v) a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.Const.get_insertIfNew! h

theorem get!_insertIfNew [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else get! t a :=
  Impl.Const.get!_insertIfNew! h

theorem getD_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  Impl.Const.getD_insertIfNew! h

end Const

theorem getKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  Impl.getKey?_insertIfNew! h

theorem getKey_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.getKey_insertIfNew! h

theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  Impl.getKey!_insertIfNew! h

theorem getKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  Impl.getKeyD_insertIfNew! h

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] [LawfulEqCmp cmp] (_ : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).1 = t.get? k :=
  Impl.getThenInsertIfNew?!_fst

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).2 = t.insertIfNew k v :=
  ext <| Impl.getThenInsertIfNew?!_snd h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] (_ : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  Impl.Const.getThenInsertIfNew?!_fst

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| Impl.Const.getThenInsertIfNew?!_snd h

end Const

@[simp]
theorem length_keys [TransCmp cmp] (h : t.WF) :
    t.keys.length = t.size :=
  Impl.length_keys h.out

@[simp]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty :=
  Impl.isEmpty_keys

@[simp]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] (h : t.WF) [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  Impl.contains_keys h

@[simp]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  Impl.mem_keys h

theorem distinct_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  Impl.distinct_keys h.out

@[simp]
theorem map_fst_toList_eq_keys :
    t.toList.map Sigma.fst = t.keys :=
  Impl.map_fst_toList_eq_keys

@[simp]
theorem length_toList [TransCmp cmp] (h : t.WF) :
    t.toList.length = t.size :=
  Impl.length_toList h.out

@[simp]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  Impl.isEmpty_toList

@[simp]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    ⟨k, v⟩ ∈ t.toList ↔ t.get? k = some v :=
  Impl.mem_toList_iff_get?_eq_some h.out

theorem find?_toList_eq_some_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {v : β k} : t.toList.find? (cmp ·.1 k == .eq) = some ⟨k, v⟩ ↔ t.get? k = some v :=
  Impl.find?_toList_eq_some_iff_get?_eq_some h.out

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] (h : t.WF) {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  Impl.find?_toList_eq_none_iff_contains_eq_false h.out

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] (h : t.WF) {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false h

theorem distinct_keys_toList [TransCmp cmp] (h : t.WF) :
    t.toList.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  Impl.distinct_keys_toList h.out

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  Impl.Const.map_fst_toList_eq_keys

@[simp]
theorem length_toList (h : t.WF) :
    (toList t).length = t.size :=
  Impl.Const.length_toList h.out

@[simp]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  Impl.Const.isEmpty_toList

@[simp]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β} :
    (k, v) ∈ toList t ↔ get? t k = some v :=
  Impl.Const.mem_toList_iff_get?_eq_some h

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ get? t k = some v :=
  Impl.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some h

theorem get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get? t k = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  Impl.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList h

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] (h : t.WF)
    {k k' : α} {v : β} :
    (toList t).find? (fun a => cmp a.1 k = .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ get? t k = some v :=
  Impl.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some h.out

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] (h : t.WF) {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  Impl.Const.find?_toList_eq_none_iff_contains_eq_false h.out

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] (h : t.WF) {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  Impl.Const.find?_toList_eq_none_iff_not_mem h.out

theorem distinct_keys_toList [TransCmp cmp] (h : t.WF) :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  Impl.Const.distinct_keys_toList h.out

end Const

section monadic

variable {δ : Type w} {m : Type w → Type w}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → (a : α) → β a → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init :=
  Impl.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init :=
  Impl.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : (a : α) → β a → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init :=
  Impl.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList {f : (a : α) → β a → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init :=
  Impl.foldr_eq_foldr_toList

@[simp]
theorem forM_eq_forM [Monad m] [LawfulMonad m] {f : (a : α) → β a → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : (a : α) × β a → m PUnit} :
    ForM.forM t f = ForM.forM t.toList f :=
  Impl.forM_eq_forM_toList

@[simp]
theorem forIn_eq_forIn [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init (fun a b => f a.1 a.2 b) := rfl

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : (a : α) × β a → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  Impl.forIn_eq_forIn_toList (f := f)

theorem foldlM_eq_foldlM_keys [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init :=
  Impl.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init :=
  Impl.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init :=
  Impl.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init :=
  Impl.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t (fun a => f a.1) = t.keys.forM f :=
  Impl.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m] [LawfulMonad m]
    {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init (fun a d => f a.1 d) = ForIn.forIn t.keys init f :=
  Impl.forIn_eq_forIn_keys

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = (Const.toList t).foldlM (fun a b => f a b.1 b.2) init :=
  Impl.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = (Const.toList t).foldl (fun a b => f a b.1 b.2) init :=
  Impl.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : α → β → δ → m δ} {init : δ} :
    t.foldrM f init = (Const.toList t).foldrM (fun a b => f a.1 a.2 b) init :=
  Impl.Const.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList {f : α → β → δ → δ} {init : δ} :
    t.foldr f init = (Const.toList t).foldr (fun a b => f a.1 a.2 b) init :=
  Impl.Const.foldr_eq_foldr_toList

theorem forM_eq_forMUncurried [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = forMUncurried (fun a => f a.1 a.2) t := rfl

theorem forMUncurried_eq_forM_toList [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    forMUncurried f t = (Const.toList t).forM f :=
  Impl.Const.forM_eq_forM_toList

/--
Deprecated, use `forMUncurried_eq_forM_toList` together with `forM_eq_forMUncurried` instead.
-/
@[deprecated forMUncurried_eq_forM_toList (since := "2025-03-02")]
theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = (Const.toList t).forM (fun a => f a.1 a.2) :=
  Impl.Const.forM_eq_forM_toList

theorem forIn_eq_forInUncurried [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = forInUncurried (fun a b => f a.1 a.2 b) init t := rfl

theorem forInUncurried_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α × β → δ → m (ForInStep δ)} {init : δ} :
    forInUncurried f init t = ForIn.forIn (Const.toList t) init f :=
  Impl.Const.forIn_eq_forIn_toList

/--
Deprecated, use `forInUncurried_eq_forIn_toList` together with `forIn_eq_forInUncurried` instead.
-/
@[deprecated forInUncurried_eq_forIn_toList (since := "2025-03-02")]
theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn (Const.toList t) init (fun a b => f a.1 a.2 b) :=
  Impl.Const.forIn_eq_forIn_toList

end Const

end monadic

@[simp]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp]
theorem insertMany_list_singleton {k : α} {v : β k} :
    t.insertMany [⟨k, v⟩] = t.insert k v :=
  rfl

theorem insertMany_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    t.insertMany (⟨k, v⟩ :: l) = (t.insert k v).insertMany l :=
  ext <| Impl.insertMany!_cons

@[simp]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Sigma.fst).contains k) :=
  Impl.contains_insertMany!_list h

@[simp]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Sigma.fst).contains k :=
  Impl.mem_insertMany!_list h

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l → (l.map Sigma.fst).contains k = false → k ∈ t :=
  Impl.mem_of_mem_insertMany!_list h

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get? k = t.get? k :=
  Impl.get?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get? k' = some (cast (by congr; apply compare_eq_iff_eq.mp k_eq) v) :=
  Impl.get?_insertMany!_list_of_mem h k_eq distinct mem

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).get k h' =
    t.get k (mem_of_mem_insertMany_list h h' contains) :=
  Impl.get_insertMany!_list_of_contains_eq_false h contains

theorem get_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l).get k' h' = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.get_insertMany!_list_of_mem h k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get! k = t.get! k :=
  Impl.get!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get! k' = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.get!_insertMany!_list_of_mem h k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback :=
  Impl.getD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.getD_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k :=
  Impl.getKey?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey? k' = some k :=
  Impl.getKey?_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  Impl.getKey_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k :=
  Impl.getKey_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k :=
  Impl.getKey!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey! k' = k :=
  Impl.getKey!_insertMany!_list_of_mem h k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback :=
  Impl.getKeyD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKeyD k' fallback = k :=
  Impl.getKeyD_insertMany!_list_of_mem h k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Sigma.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length :=
  Impl.size_insertMany!_list h distinct

theorem size_le_size_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} :
    t.size ≤ (t.insertMany l).size :=
  Impl.size_le_size_insertMany!_list h

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  Impl.size_insertMany!_list_le h

@[simp]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.isEmpty_insertMany!_list h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem insertMany_nil :
    insertMany t [] = t :=
  rfl

@[simp]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany t [⟨k, v⟩] = t.insert k v :=
  rfl

theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    Const.insertMany t ((k, v) :: l) = Const.insertMany (t.insert k v) l :=
  ext <| Impl.Const.insertMany!_cons

@[simp]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (Const.insertMany t l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  Impl.Const.contains_insertMany!_list h

@[simp]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ Const.insertMany t l ↔ k ∈ t ∨ (l.map Prod.fst).contains k :=
  Impl.Const.mem_insertMany!_list h

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ( α × β )} {k : α} :
    k ∈ insertMany t l → (l.map Prod.fst).contains k = false → k ∈ t :=
  Impl.Const.mem_of_mem_insertMany!_list h

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey? k = t.getKey? k :=
  Impl.Const.getKey?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey? k' = some k :=
  Impl.Const.getKey?_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany t l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  Impl.Const.getKey_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany t l).getKey k' h' = k :=
  Impl.Const.getKey_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey! k = t.getKey! k :=
  Impl.Const.getKey!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey! k' = k :=
  Impl.Const.getKey!_insertMany!_list_of_mem h k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKeyD k fallback = t.getKeyD k fallback :=
  Impl.Const.getKeyD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKeyD k' fallback = k :=
  Impl.Const.getKeyD_insertMany!_list_of_mem h k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (insertMany t l).size = t.size + l.length :=
  Impl.Const.size_insertMany!_list h distinct

theorem size_le_size_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    t.size ≤ (insertMany t l).size :=
  Impl.Const.size_le_size_insertMany!_list h

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (insertMany t l).size ≤ t.size + l.length :=
  Impl.Const.size_insertMany!_list_le h

@[simp]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.Const.isEmpty_insertMany!_list h

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany t l) k = get? t k :=
  Impl.Const.get?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany t l) k' = v :=
  Impl.Const.get?_insertMany!_list_of_mem h k_eq distinct mem

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany t l) k h' = get t k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  Impl.Const.get_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    get (insertMany t l) k' h' = v :=
  Impl.Const.get_insertMany!_list_of_mem h k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited β] (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany t l) k = get! t k :=
  Impl.Const.get!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [Inhabited β] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany t l) k' = v :=
  Impl.Const.get!_insertMany!_list_of_mem h k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany t l) k fallback = getD t k fallback :=
  Impl.Const.getD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany t l) k' fallback = v :=
  Impl.Const.getD_insertMany!_list_of_mem h k_eq distinct mem

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
  ext <| Impl.Const.insertManyIfNewUnit!_cons

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) :=
  Impl.Const.contains_insertManyIfNewUnit!_list h

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k :=
  Impl.Const.mem_insertManyIfNewUnit!_list h

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t :=
  Impl.Const.mem_of_mem_insertManyIfNewUnit!_list h contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false → getKey? (insertManyIfNewUnit t l) k = none :=
  Impl.Const.getKey?_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false h

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey? (insertManyIfNewUnit t l) k' = some k :=
  Impl.Const.getKey?_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey? (insertManyIfNewUnit t l) k = getKey? t k :=
  Impl.Const.getKey?_insertManyIfNewUnit!_list_of_mem h

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains :=
  Impl.Const.getKey_insertManyIfNewUnit!_list_of_mem h contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey (insertManyIfNewUnit t l) k' h' = k :=
  Impl.Const.getKey_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false →
      getKey! (insertManyIfNewUnit t l) k = default :=
  Impl.Const.getKey!_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false h

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey! (insertManyIfNewUnit t l) k' = k :=
  Impl.Const.getKey!_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey! (insertManyIfNewUnit t l) k = getKey! t k :=
  Impl.Const.getKey!_insertManyIfNewUnit!_list_of_mem h

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k fallback : α} :
    ¬ k ∈ t → l.contains k = false → getKeyD (insertManyIfNewUnit t l) k fallback = fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false h

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKeyD (insertManyIfNewUnit t l) k' fallback = k :=
  Impl.Const.getKeyD_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k fallback : α} :
    k ∈ t → getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit!_list_of_mem h

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length :=
  Impl.Const.size_insertManyIfNewUnit!_list h distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp] (h : t.WF)
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size :=
  Impl.Const.size_le_size_insertManyIfNewUnit!_list h

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp] (h : t.WF)
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length :=
  Impl.Const.size_insertManyIfNewUnit!_list_le h

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] (h : t.WF) {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.Const.isEmpty_insertManyIfNewUnit!_list h

@[simp]
theorem get?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit t l) k =
      if k ∈ t ∨ l.contains k then some () else none :=
  Impl.Const.get?_insertManyIfNewUnit!_list h

@[simp]
theorem get_insertManyIfNewUnit_list {l : List α} {k : α} {h'} :
    get (insertManyIfNewUnit t l) k h' = () :=
  rfl

@[simp]
theorem get!_insertManyIfNewUnit_list {l : List α} {k : α} :
    get! (insertManyIfNewUnit t l) k = () :=
  rfl

@[simp]
theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit t l) k fallback = () :=
  rfl

end Const

@[simp]
theorem ofList_nil :
    ofList ([] : List ((a : α) × (β a))) cmp = ∅ :=
  rfl

@[simp]
theorem ofList_singleton {k : α} {v : β k} :
    ofList [⟨k, v⟩] cmp = (∅ : Raw α β cmp).insert k v :=
  rfl

theorem ofList_cons {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) cmp = ((∅ : Raw α β cmp).insert k v).insertMany tl :=
  ext Impl.insertMany_empty_list_cons_eq_insertMany!

@[simp]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l cmp).contains k = (l.map Sigma.fst).contains k := by
  simp [ofList, contains, Impl.ofList]
  exact Impl.contains_insertMany_empty_list (instOrd := ⟨cmp⟩) (k := k) (l := l)

@[simp]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Sigma.fst).contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).get? k = none :=
  Impl.get?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).get? k' = some (cast (by congr; apply compare_eq_iff_eq.mp k_eq) v) :=
  Impl.get?_insertMany_empty_list_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l cmp).get k' h = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.get_insertMany_empty_list_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).get! k = default :=
  Impl.get!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).get! k' = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.get!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getD k fallback = fallback :=
  Impl.getD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).getD k' fallback = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.getD_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  Impl.getKey?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKey? k' = some k :=
  Impl.getKey?_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  Impl.getKey_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [Inhabited α] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  Impl.getKey!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKey! k' = k :=
  Impl.getKey!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  Impl.getKeyD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  Impl.getKeyD_insertMany_empty_list_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  Impl.size_insertMany_empty_list distinct

theorem size_ofList_le [TransCmp cmp] {l : List ((a : α) × β a)} :
    (ofList l cmp).1.size ≤ l.length :=
  Impl.size_insertMany_empty_list_le

@[simp]
theorem isEmpty_ofList [TransCmp cmp] {l : List ((a : α) × β a)} :
    (ofList l cmp).1.isEmpty = l.isEmpty :=
  Impl.isEmpty_insertMany_empty_list

namespace Const

variable {β : Type v}

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
  ext <| Impl.Const.insertMany_empty_list_cons_eq_insertMany!

@[simp]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  Impl.Const.contains_insertMany_empty_list

@[simp]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Prod.fst).contains k := by
  simp [mem_iff_contains]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l cmp) k = none :=
  Impl.Const.get?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l cmp) k' = some v :=
  Impl.Const.get?_insertMany_empty_list_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l cmp) k' h = v :=
  Impl.Const.get_insertMany_empty_list_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l cmp) k = default :=
  Impl.Const.get!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l cmp) k' = v :=
  Impl.Const.get!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  Impl.Const.getD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l cmp) k' fallback = v :=
  Impl.Const.getD_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  Impl.Const.getKey?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey? k' = some k :=
  Impl.Const.getKey?_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  Impl.Const.getKey_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  Impl.Const.getKey!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey! k' = k :=
  Impl.Const.getKey!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  Impl.Const.getKeyD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  Impl.Const.getKeyD_insertMany_empty_list_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  Impl.Const.size_insertMany_empty_list distinct

theorem size_ofList_le [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).size ≤ l.length :=
  Impl.Const.size_insertMany_empty_list_le

theorem isEmpty_ofList [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  Impl.Const.isEmpty_insertMany_empty_list

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
  ext Impl.Const.insertManyIfNewUnit_empty_list_cons_eq_insertManyIfNewUnit!

@[simp]
theorem contains_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp).contains k = l.contains k :=
  Impl.Const.contains_insertManyIfNewUnit_empty_list

@[simp]
theorem mem_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ unitOfList l cmp ↔ l.contains k := by
  simp [mem_iff_contains]

theorem getKey?_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l cmp) k = none :=
  Impl.Const.getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (unitOfList l cmp) k' = some k :=
  Impl.Const.getKey?_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem getKey_unitOfList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l cmp) k' h' = k :=
  Impl.Const.getKey_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l cmp) k = default :=
  Impl.Const.getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKey! (unitOfList l cmp) k' = k :=
  Impl.Const.getKey!_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l cmp) k fallback = fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKeyD (unitOfList l cmp) k' fallback = k :=
  Impl.Const.getKeyD_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem size_unitOfList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (unitOfList l cmp).size = l.length :=
  Impl.Const.size_insertManyIfNewUnit_empty_list distinct

theorem size_unitOfList_le [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).size ≤ l.length :=
  Impl.Const.size_insertManyIfNewUnit_empty_list_le

@[simp]
theorem isEmpty_unitOfList [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).isEmpty = l.isEmpty :=
  Impl.Const.isEmpty_insertManyIfNewUnit_empty_list

@[simp]
theorem get?_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    get? (unitOfList l cmp) k = if l.contains k then some () else none :=
  Impl.Const.get?_insertManyIfNewUnit_empty_list

@[simp]
theorem get_unitOfList {l : List α} {k : α} {h} :
    get (unitOfList l cmp) k h = () :=
  Impl.Const.get_insertManyIfNewUnit_empty_list

@[simp]
theorem get!_unitOfList {l : List α} {k : α} :
    get! (unitOfList l cmp) k = () :=
  Impl.Const.get!_insertManyIfNewUnit_empty_list

@[simp]
theorem getD_unitOfList {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l cmp) k fallback = () :=
  Impl.Const.getD_insertManyIfNewUnit_empty_list

end Const

end Std.DTreeMap.Raw
