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

universe u v w

namespace Std.DTreeMap

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap α β cmp}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

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

theorem isEmpty_eq_false_of_contains [TransCmp cmp] {a : α} (hc : t.contains a = true) :
    t.isEmpty = false :=
  Impl.isEmpty_eq_false_of_contains t.wf hc

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
    (∅ : DTreeMap α β cmp).erase k = ∅ :=
  ext <| Impl.erase_empty (instOrd := ⟨cmp⟩) (k := k)

@[simp]
theorem isEmpty_erase [TransCmp cmp] {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  Impl.isEmpty_erase t.wf

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransCmp cmp] (k : α) :
    t.isEmpty = ((t.erase k).isEmpty && !(t.contains k)) :=
  Impl.isEmpty_eq_isEmpty_erase_and_not_contains t.wf k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransCmp cmp] {k : α}
    (he : (t.erase k).isEmpty = false) :
    t.isEmpty = false :=
  Impl.isEmpty_eq_false_of_isEmpty_erase_eq_false t.wf he

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
theorem get?_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (∅ : DTreeMap α β cmp).get? a = none :=
  Impl.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    t.isEmpty = true → t.get? a = none :=
  Impl.get?_of_isEmpty t.wf

theorem get?_insert [TransCmp cmp] [LawfulEqCmp cmp] {a k : α} {v : β k} :
    (t.insert k v).get? a =
      if h : cmp k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a :=
  Impl.get?_insert t.wf

@[simp]
theorem get?_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.insert k v).get? k = some v :=
  Impl.get?_insert_self t.wf

theorem contains_eq_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    t.contains a = (t.get? a).isSome :=
  Impl.contains_eq_isSome_get? t.wf

theorem mem_iff_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  Impl.mem_iff_isSome_get? t.wf

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    t.contains a = false → t.get? a = none :=
  Impl.get?_eq_none_of_contains_eq_false t.wf

theorem get?_eq_none [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  Impl.get?_eq_none t.wf

theorem get?_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  Impl.get?_erase t.wf

@[simp]
theorem get?_erase_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} :
    (t.erase k).get? k = none :=
  Impl.get?_erase_self t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

@[simp]
theorem get?_emptyc [TransCmp cmp] {a : α} :
    get? (∅ : DTreeMap α β cmp) a = none :=
  Impl.Const.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → get? t a = none :=
  Impl.Const.get?_of_isEmpty t.wf

theorem get?_insert [TransCmp cmp] {a k : α} {v : β} :
    get? (t.insert k v) a =
      if cmp k a = .eq then some v else get? t a :=
  Impl.Const.get?_insert t.wf

@[simp]
theorem get?_insert_self [TransCmp cmp] {k : α} {v : β} :
    get? (t.insert k v) k = some v :=
  Impl.Const.get?_insert_self t.wf

theorem contains_eq_isSome_get? [TransCmp cmp] {a : α} :
    t.contains a = (get? t a).isSome :=
  Impl.Const.contains_eq_isSome_get? t.wf

theorem mem_iff_isSome_get? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (get? t a).isSome :=
  Impl.Const.mem_iff_isSome_get? t.wf

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → get? t a = none :=
  Impl.Const.get?_eq_none_of_contains_eq_false t.wf

theorem get?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → get? t a = none :=
  Impl.Const.get?_eq_none t.wf

theorem get?_erase [TransCmp cmp] {k a : α} :
    get? (t.erase k) a = if cmp k a = .eq then none else get? t a :=
  Impl.Const.get?_erase t.wf

@[simp]
theorem get?_erase_self [TransCmp cmp] {k : α} :
    get? (t.erase k) k = none :=
  Impl.Const.get?_erase_self t.wf

theorem get?_eq_get? [LawfulEqCmp cmp] [TransCmp cmp] {a : α} : get? t a = t.get? a :=
  Impl.Const.get?_eq_get? t.wf

theorem get?_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) :
    get? t a = get? t b :=
  Impl.Const.get?_congr t.wf hab

end Const

theorem get_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insert k v).get a h₁ =
      if h₂ : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (mem_of_mem_insert h₁ h₂) :=
  Impl.get_insert t.wf

@[simp]
theorem get_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.insert k v).get k mem_insert_self = v :=
  Impl.get_insert_self t.wf

@[simp]
theorem get_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h') :=
  Impl.get_erase t.wf

theorem get?_eq_some_get [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  Impl.get?_eq_some_get t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

theorem get_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (mem_of_mem_insert h₁ h₂) :=
  Impl.Const.get_insert t.wf

@[simp]
theorem get_insert_self [TransCmp cmp] {k : α} {v : β} :
    get (t.insert k v) k mem_insert_self = v :=
  Impl.Const.get_insert_self t.wf

@[simp]
theorem get_erase [TransCmp cmp] {k a : α} {h'} :
    get (t.erase k) a h' = get t a (mem_of_mem_erase h') :=
  Impl.Const.get_erase t.wf

theorem get?_eq_some_get [TransCmp cmp] {a : α} {h} :
    get? t a = some (get t a h) :=
  Impl.Const.get?_eq_some_get t.wf

theorem get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {h} : get t a h = t.get a h :=
  Impl.Const.get_eq_get t.wf

theorem get_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) {h'} :
    get t a h' = get t b ((mem_congr hab).mp h') :=
  Impl.Const.get_congr t.wf hab

end Const

@[simp]
theorem get!_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    get! (∅ : DTreeMap α β cmp) a = default :=
  Impl.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default :=
  Impl.get!_of_isEmpty t.wf

theorem get!_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insert k v).get! a =
      if h : cmp k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a :=
  Impl.get!_insert t.wf

@[simp]
theorem get!_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] {b : β a} :
    (t.insert a b).get! a = b :=
  Impl.get!_insert_self t.wf

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default :=
  Impl.get!_eq_default_of_contains_eq_false t.wf

theorem get!_eq_default [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default :=
  Impl.get!_eq_default t.wf

theorem get!_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} [Inhabited (β a)] :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  Impl.get!_erase t.wf

@[simp]
theorem get!_erase_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} [Inhabited (β k)] :
    (t.erase k).get! k = default :=
  Impl.get!_erase_self t.wf

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.contains a = true → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get!_of_contains t.wf

theorem get?_eq_some_get! [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get! t.wf

theorem get!_eq_get!_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! :=
  Impl.get!_eq_get!_get? t.wf

theorem get_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] {h} :
    t.get a h = t.get! a :=
  Impl.get_eq_get! t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

@[simp]
theorem get!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : DTreeMap α β cmp) a = default :=
  Impl.Const.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited β] {a : α} :
    t.isEmpty = true → get! t a = default :=
  Impl.Const.get!_of_isEmpty t.wf

theorem get!_insert [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else get! t a :=
  Impl.Const.get!_insert t.wf

@[simp]
theorem get!_insert_self [TransCmp cmp] [Inhabited β] {k : α} {v : β} : get! (t.insert k v) k = v :=
  Impl.Const.get!_insert_self t.wf

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = false → get! t a = default :=
  Impl.Const.get!_eq_default_of_contains_eq_false t.wf

theorem get!_eq_default [TransCmp cmp] [Inhabited β] {a : α} :
    ¬ a ∈ t → get! t a = default :=
  Impl.Const.get!_eq_default t.wf

theorem get!_erase [TransCmp cmp] [Inhabited β] {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else get! t a :=
  Impl.Const.get!_erase t.wf

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited β] {k : α} :
    get! (t.erase k) k = default :=
  Impl.Const.get!_erase_self t.wf

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = true → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! t.wf

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited β] {a : α} :
    a ∈ t → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! t.wf

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited β] {a : α} :
    get! t a = (get? t a).get! :=
  Impl.Const.get!_eq_get!_get? t.wf

theorem get_eq_get! [TransCmp cmp] [Inhabited β] {a : α} {h} :
    get t a h = get! t a :=
  Impl.Const.get_eq_get! t.wf

theorem get!_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β] {a : α} :
    get! t a = t.get! a :=
  Impl.Const.get!_eq_get! t.wf

theorem get!_congr [TransCmp cmp] [Inhabited β] {a b : α} (hab : cmp a b = .eq) :
    get! t a = get! t b :=
  Impl.Const.get!_congr t.wf hab

end Const

@[simp]
theorem getD_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    (∅ : DTreeMap α β cmp).getD a fallback = fallback :=
  Impl.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  Impl.getD_of_isEmpty t.wf

theorem getD_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v).getD a fallback =
      if h : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback :=
  Impl.getD_insert t.wf

@[simp]
theorem getD_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback b : β a} :
    (t.insert a b).getD a fallback = b :=
  Impl.getD_insert_self t.wf

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] {a : α}
    {fallback : β a} : t.contains a = false → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback_of_contains_eq_false t.wf

theorem getD_eq_fallback [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback t.wf

theorem getD_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {fallback : β a} :
    (t.erase k).getD a fallback = if cmp k a = .eq then fallback else t.getD a fallback :=
  Impl.getD_erase t.wf

@[simp]
theorem getD_erase_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {fallback : β k} :
    (t.erase k).getD k fallback = fallback :=
  Impl.getD_erase_self t.wf

theorem get?_eq_some_getD_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    t.contains a = true → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD_of_contains t.wf

theorem get?_eq_some_getD [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD t.wf

theorem getD_eq_getD_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback :=
  Impl.getD_eq_getD_get? t.wf

theorem get_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} {h} :
    t.get a h = t.getD a fallback :=
  Impl.get_eq_getD t.wf

theorem get!_eq_getD_default [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default :=
  Impl.get!_eq_getD_default t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

@[simp]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : DTreeMap α β cmp) a fallback = fallback :=
  Impl.Const.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  Impl.Const.getD_of_isEmpty t.wf

theorem getD_insert [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  Impl.Const.getD_insert t.wf

@[simp]
theorem getD_insert_self [TransCmp cmp] {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  Impl.Const.getD_insert_self t.wf

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback_of_contains_eq_false t.wf

theorem getD_eq_fallback [TransCmp cmp] {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback t.wf

theorem getD_erase [TransCmp cmp] {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  Impl.Const.getD_erase t.wf

@[simp]
theorem getD_erase_self [TransCmp cmp] {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  Impl.Const.getD_erase_self t.wf

theorem get?_eq_some_getD_of_contains [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD_of_contains t.wf

theorem get?_eq_some_getD [TransCmp cmp] {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD t.wf

theorem getD_eq_getD_get? [TransCmp cmp] {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback :=
  Impl.Const.getD_eq_getD_get? t.wf

theorem get_eq_getD [TransCmp cmp] {a : α} {fallback : β} {h} :
    get t a h = getD t a fallback :=
  Impl.Const.get_eq_getD t.wf

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited β] {a : α} :
    get! t a = getD t a default :=
  Impl.Const.get!_eq_getD_default t.wf

theorem getD_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback :=
  Impl.Const.getD_eq_getD t.wf

theorem getD_congr [TransCmp cmp] {a b : α} {fallback : β} (hab : cmp a b = .eq) :
    getD t a fallback = getD t b fallback :=
  Impl.Const.getD_congr t.wf hab

end Const

@[simp]
theorem getKey?_emptyc {a : α} : (∅ : DTreeMap α β cmp).getKey? a = none :=
  Impl.getKey?_empty

theorem getKey?_of_isEmpty [TransCmp cmp] {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  Impl.getKey?_of_isEmpty t.wf

theorem getKey?_insert [TransCmp cmp] {a k : α} {v : β k} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  Impl.getKey?_insert t.wf

@[simp]
theorem getKey?_insert_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).getKey? k = some k :=
  Impl.getKey?_insert_self t.wf

theorem contains_eq_isSome_getKey? [TransCmp cmp] {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  Impl.contains_eq_isSome_getKey? t.wf

theorem mem_iff_isSome_getKey? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  Impl.mem_iff_isSome_getKey? t.wf

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.getKey? a = none :=
  Impl.getKey?_eq_none_of_contains_eq_false t.wf

theorem getKey?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  Impl.getKey?_eq_none t.wf

theorem getKey?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  Impl.getKey?_erase t.wf

@[simp]
theorem getKey?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).getKey? k = none :=
  Impl.getKey?_erase_self t.wf

theorem compare_getKey?_self [TransCmp cmp] {k : α} :
    (t.getKey? k).all (cmp · k = .eq) :=
  Impl.compare_getKey?_self t.wf

theorem getKey?_congr [TransCmp cmp] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey? k = t.getKey? k' :=
  Impl.getKey?_congr t.wf h'

theorem getKey?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : t.contains k) :
    t.getKey? k = some k :=
  Impl.getKey?_eq_some_of_contains t.wf h'

theorem getKey?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.getKey? k = some k :=
  Impl.getKey?_eq_some_of_contains t.wf h'

theorem getKey_insert [TransCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then
        k
      else
        t.getKey a (mem_of_mem_insert h₁ h₂) :=
  Impl.getKey_insert t.wf

@[simp]
theorem getKey_insert_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).getKey k mem_insert_self = k :=
  Impl.getKey_insert_self t.wf

@[simp]
theorem getKey_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h') :=
  Impl.getKey_erase t.wf

theorem getKey?_eq_some_getKey [TransCmp cmp] {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  Impl.getKey?_eq_some_getKey t.wf

theorem compare_getKey_self [TransCmp cmp] {k : α} (h' : k ∈ t) :
    cmp (t.getKey k h') k = .eq :=
  Impl.compare_getKey_self t.wf h'

theorem getKey_congr [TransCmp cmp] {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h').mp h₁) :=
  Impl.getKey_congr t.wf h' h₁

@[simp]
theorem getKey_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    (h' : k ∈ t) : t.getKey k h' = k :=
  Impl.getKey_eq t.wf h'

@[simp]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : DTreeMap α β cmp).getKey! a = default :=
  Impl.getKey!_empty

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  Impl.getKey!_of_isEmpty t.wf

theorem getKey!_insert [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β k} : (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  Impl.getKey!_insert t.wf

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] {a : α}
    {b : β a} : (t.insert a b).getKey! a = a :=
  Impl.getKey!_insert_self t.wf

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.getKey! a = default :=
  Impl.getKey!_eq_default_of_contains_eq_false t.wf

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  Impl.getKey!_eq_default t.wf

theorem getKey!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  Impl.getKey!_erase t.wf

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] {k : α} :
    (t.erase k).getKey! k = default :=
  Impl.getKey!_erase_self t.wf

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey!_of_contains t.wf

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey! t.wf

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  Impl.getKey!_eq_get!_getKey? t.wf

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] {a : α} {h} :
    t.getKey a h = t.getKey! a :=
  Impl.getKey_eq_getKey! t.wf

theorem getKey!_congr [TransCmp cmp] [Inhabited α] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey! k = t.getKey! k' :=
  Impl.getKey!_congr t.wf h'

theorem getKey!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    (h' : t.contains k) :
    t.getKey! k = k :=
  Impl.getKey!_eq_of_contains t.wf h'

theorem getKey!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    {k : α} (h' : k ∈ t) :
    t.getKey! k = k :=
  Impl.getKey!_eq_of_mem t.wf h'

@[simp]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : DTreeMap α β cmp).getKeyD a fallback = fallback :=
  Impl.getKeyD_empty

theorem getKeyD_of_isEmpty [TransCmp cmp] {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_of_isEmpty t.wf

theorem getKeyD_insert [TransCmp cmp] {k a fallback : α} {v : β k} :
    (t.insert k v).getKeyD a fallback =
      if cmp k a = .eq then k else t.getKeyD a fallback :=
  Impl.getKeyD_insert t.wf

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] {a fallback : α} {b : β a} :
    (t.insert a b).getKeyD a fallback = a :=
  Impl.getKeyD_insert_self t.wf

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback_of_contains_eq_false t.wf

theorem getKeyD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback t.wf

theorem getKeyD_erase [TransCmp cmp] {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  Impl.getKeyD_erase t.wf

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  Impl.getKeyD_erase_self t.wf

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD_of_contains t.wf

theorem getKey?_eq_some_getKeyD [TransCmp cmp] {a fallback : α} :
  a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD t.wf

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  Impl.getKeyD_eq_getD_getKey? t.wf

theorem getKey_eq_getKeyD [TransCmp cmp] {a fallback : α} {h} :
    t.getKey a h = t.getKeyD a fallback :=
  Impl.getKey_eq_getKeyD t.wf

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = t.getKeyD a default :=
  Impl.getKey!_eq_getKeyD_default t.wf

theorem getKeyD_congr [TransCmp cmp] {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getKeyD k fallback = t.getKeyD k' fallback :=
  Impl.getKeyD_congr t.wf h'

theorem getKeyD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α}
    (h' : t.contains k) :
    t.getKeyD k fallback = k :=
  Impl.getKeyD_eq_of_contains t.wf h'

theorem getKeyD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : k ∈ t) :
    t.getKeyD k fallback = k :=
  Impl.getKeyD_eq_of_contains t.wf h'

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew t.wf

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

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v) → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  Impl.mem_of_mem_insertIfNew' t.wf

theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  Impl.size_insertIfNew t.wf

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  Impl.size_le_size_insertIfNew t.wf

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  Impl.size_insertIfNew_le t.wf

theorem get?_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).get? a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a :=
  Impl.get?_insertIfNew t.wf

theorem get_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h₁ h₂) :=
  Impl.get_insertIfNew t.wf

theorem get!_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v).get! a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a :=
  Impl.get!_insertIfNew t.wf

theorem getD_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v).getD a fallback =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback :=
  Impl.getD_insertIfNew t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

theorem get?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    get? (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else get? t a :=
  Impl.Const.get?_insertIfNew t.wf

theorem get_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v) a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then v else get t a (mem_of_mem_insertIfNew' h₁ h₂) :=
  Impl.Const.get_insertIfNew t.wf

theorem get!_insertIfNew [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    get! (t.insertIfNew k v) a = if cmp k a = .eq ∧ ¬ k ∈ t then v else get! t a :=
  Impl.Const.get!_insertIfNew t.wf

theorem getD_insertIfNew [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  Impl.Const.getD_insertIfNew t.wf

end Const

theorem getKey?_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  Impl.getKey?_insertIfNew t.wf

theorem getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂) :=
  Impl.getKey_insertIfNew t.wf

theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  Impl.getKey!_insertIfNew t.wf

theorem getKeyD_insertIfNew [TransCmp cmp] {k a fallback : α} {v : β k} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  Impl.getKeyD_insertIfNew t.wf

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).1 = t.get? k :=
  Impl.getThenInsertIfNew?_fst t.wf

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).2 = t.insertIfNew k v :=
  ext <| Impl.getThenInsertIfNew?_snd t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

@[simp]
theorem getThenInsertIfNew?_fst [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  Impl.Const.getThenInsertIfNew?_fst t.wf

@[simp]
theorem getThenInsertIfNew?_snd [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| Impl.Const.getThenInsertIfNew?_snd t.wf

end Const

@[simp]
theorem length_keys [TransCmp cmp] :
    t.keys.length = t.size :=
  Impl.length_keys t.wf

@[simp]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty :=
  Impl.isEmpty_keys

@[simp]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  Impl.contains_keys t.wf

@[simp]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  Impl.mem_keys t.wf

theorem distinct_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  Impl.distinct_keys t.wf

@[simp]
theorem map_fst_toList_eq_keys :
    t.toList.map Sigma.fst = t.keys :=
  Impl.map_fst_toList_eq_keys

@[simp]
theorem length_toList [TransCmp cmp] :
    t.toList.length = t.size :=
  Impl.length_toList t.wf

@[simp]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  Impl.isEmpty_toList

@[simp]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    ⟨k, v⟩ ∈ t.toList ↔ t.get? k = some v :=
  Impl.mem_toList_iff_get?_eq_some t.wf

theorem find?_toList_eq_some_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    t.toList.find? (cmp ·.1 k == .eq) = some ⟨k, v⟩ ↔ t.get? k = some v :=
  Impl.find?_toList_eq_some_iff_get?_eq_some t.wf

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  Impl.find?_toList_eq_none_iff_contains_eq_false t.wf

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false

theorem distinct_keys_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  Impl.distinct_keys_toList t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

@[simp]
theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  Impl.Const.map_fst_toList_eq_keys

@[simp]
theorem length_toList :
    (toList t).length = t.size :=
  Impl.Const.length_toList t.wf

@[simp]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  Impl.Const.isEmpty_toList

@[simp]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ get? t k = some v :=
  Impl.Const.mem_toList_iff_get?_eq_some t.wf

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ get? t k = some v :=
  Impl.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some t.wf

theorem get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] {k : α} {v : β} :
    get? t k = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  Impl.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList t.wf

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] {k k' : α} {v : β} :
    (toList t).find? (cmp ·.1 k == .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ get? t k = some v :=
  Impl.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some t.wf

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  Impl.Const.find?_toList_eq_none_iff_contains_eq_false t.wf

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  Impl.Const.find?_toList_eq_none_iff_not_mem t.wf

theorem distinct_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  Impl.Const.distinct_keys_toList t.wf

end Const

section monadic

variable {δ : Type w} {m : Type w → Type w}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β a → m δ} {init : δ} :
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

theorem foldrM_eq_foldrM_keys [Monad m] [LawfulMonad m]
    {f : α → δ → m δ} {init : δ} :
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

variable {β : Type v} {t : DTreeMap α β cmp}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m]
    {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = (Const.toList t).foldlM (fun a b => f a b.1 b.2) init :=
  Impl.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = (Const.toList t).foldl (fun a b => f a b.1 b.2) init :=
  Impl.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m]
    {f : α → β → δ → m δ} {init : δ} :
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
  ext <| Impl.insertMany_cons t.wf

@[simp]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Sigma.fst).contains k) :=
  Impl.contains_insertMany_list t.wf

@[simp]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Sigma.fst).contains k :=
  Impl.mem_insertMany_list t.wf

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l → (l.map Sigma.fst).contains k = false → k ∈ t :=
  Impl.mem_of_mem_insertMany_list t.wf

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get? k = t.get? k :=
  Impl.get?_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get? k' = some (cast (by congr; apply compare_eq_iff_eq.mp k_eq) v) :=
  Impl.get?_insertMany_list_of_mem t.wf k_eq distinct mem

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).get k h' =
    t.get k (mem_of_mem_insertMany_list h' contains) :=
  Impl.get_insertMany_list_of_contains_eq_false t.wf contains

theorem get_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l).get k' h' = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.get_insertMany_list_of_mem t.wf k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get! k = t.get! k :=
  Impl.get!_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get! k' = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.get!_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback :=
  Impl.getD_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = cast (by congr; apply compare_eq_iff_eq.mp k_eq) v :=
  Impl.getD_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k :=
  Impl.getKey?_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey? k' = some k :=
  Impl.getKey?_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h' contains_eq_false) :=
  Impl.getKey_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k :=
  Impl.getKey_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k :=
  Impl.getKey!_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey! k' = k :=
  Impl.getKey!_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback :=
  Impl.getKeyD_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKeyD k' fallback = k :=
  Impl.getKeyD_insertMany_list_of_mem t.wf k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Sigma.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length :=
  Impl.size_insertMany_list t.wf distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List ((a : α) × β a)} :
    t.size ≤ (t.insertMany l).size :=
  Impl.size_le_size_insertMany_list t.wf

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List ((a : α) × β a)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  Impl.size_insertMany_list_le t.wf

@[simp]
theorem isEmpty_insertMany_list [TransCmp cmp]
    {l : List ((a : α) × β a)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.isEmpty_insertMany_list t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

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
  ext <| Impl.Const.insertMany_cons t.wf

@[simp]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    (Const.insertMany t l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  Impl.Const.contains_insertMany_list t.wf

@[simp]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    k ∈ Const.insertMany t l ↔ k ∈ t ∨ (l.map Prod.fst).contains k :=
  Impl.Const.mem_insertMany_list t.wf

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ( α × β )} {k : α} :
    k ∈ insertMany t l → (l.map Prod.fst).contains k = false → k ∈ t :=
  Impl.Const.mem_of_mem_insertMany_list t.wf

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey? k = t.getKey? k :=
  Impl.Const.getKey?_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey? k' = some k :=
  Impl.Const.getKey?_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany t l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h' contains_eq_false) :=
  Impl.Const.getKey_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany t l).getKey k' h' = k :=
  Impl.Const.getKey_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey! k = t.getKey! k :=
  Impl.Const.getKey!_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey! k' = k :=
  Impl.Const.getKey!_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKeyD k fallback = t.getKeyD k fallback :=
  Impl.Const.getKeyD_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKeyD k' fallback = k :=
  Impl.Const.getKeyD_insertMany_list_of_mem t.wf k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (insertMany t l).size = t.size + l.length :=
  Impl.Const.size_insertMany_list t.wf distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    t.size ≤ (insertMany t l).size :=
  Impl.Const.size_le_size_insertMany_list t.wf

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List (α × β)} :
    (insertMany t l).size ≤ t.size + l.length :=
  Impl.Const.size_insertMany_list_le t.wf

@[simp]
theorem isEmpty_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.Const.isEmpty_insertMany_list t.wf

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany t l) k = get? t k :=
  Impl.Const.get?_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany t l) k' = v :=
  Impl.Const.get?_insertMany_list_of_mem t.wf k_eq distinct mem

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany t l) k h' = get t k (mem_of_mem_insertMany_list h' contains_eq_false) :=
  Impl.Const.get_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem get_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    get (insertMany t l) k' h' = v :=
  Impl.Const.get_insertMany_list_of_mem t.wf k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany t l) k = get! t k :=
  Impl.Const.get!_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany t l) k' = v :=
  Impl.Const.get!_insertMany_list_of_mem t.wf k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany t l) k fallback = getD t k fallback :=
  Impl.Const.getD_insertMany_list_of_contains_eq_false t.wf contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany t l) k' fallback = v :=
  Impl.Const.getD_insertMany_list_of_mem t.wf k_eq distinct mem

variable {t : DTreeMap α Unit cmp}

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
  ext <| Impl.Const.insertManyIfNewUnit_cons t.wf

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) :=
  Impl.Const.contains_insertManyIfNewUnit_list t.wf

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k :=
  Impl.Const.mem_insertManyIfNewUnit_list t.wf

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t :=
  Impl.Const.mem_of_mem_insertManyIfNewUnit_list t.wf contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false → getKey? (insertManyIfNewUnit t l) k = none :=
  Impl.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false t.wf

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey? (insertManyIfNewUnit t l) k' = some k :=
  Impl.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem t.wf k_eq

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} :
    k ∈ t → getKey? (insertManyIfNewUnit t l) k = getKey? t k :=
  Impl.Const.getKey?_insertManyIfNewUnit_list_of_mem t.wf

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains :=
  Impl.Const.getKey_insertManyIfNewUnit_list_of_mem t.wf contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey (insertManyIfNewUnit t l) k' h' = k :=
  Impl.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem t.wf k_eq

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false →
      getKey! (insertManyIfNewUnit t l) k = default :=
  Impl.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false t.wf

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey! (insertManyIfNewUnit t l) k' = k :=
  Impl.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem t.wf k_eq

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k : α} :
    k ∈ t → getKey! (insertManyIfNewUnit t l) k = getKey! t k :=
  Impl.Const.getKey!_insertManyIfNewUnit_list_of_mem t.wf

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k fallback : α} :
    ¬ k ∈ t → l.contains k = false → getKeyD (insertManyIfNewUnit t l) k fallback = fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false t.wf

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKeyD (insertManyIfNewUnit t l) k' fallback = k :=
  Impl.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem t.wf k_eq

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k fallback : α} :
    k ∈ t → getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit_list_of_mem t.wf

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length :=
  Impl.Const.size_insertManyIfNewUnit_list t.wf distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp]
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size :=
  Impl.Const.size_le_size_insertManyIfNewUnit_list t.wf

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp]
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length :=
  Impl.Const.size_insertManyIfNewUnit_list_le t.wf

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.Const.isEmpty_insertManyIfNewUnit_list t.wf

@[simp]
theorem get?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit t l) k =
      if k ∈ t ∨ l.contains k then some () else none :=
  Impl.Const.get?_insertManyIfNewUnit_list t.wf

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
    ofList [⟨k, v⟩] cmp = (∅ : DTreeMap α β cmp).insert k v :=
  rfl

theorem ofList_cons {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) cmp = ((∅ : DTreeMap α β cmp).insert k v).insertMany tl :=
  ext <| Impl.insertMany_empty_list_cons

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
    ofList [⟨k, v⟩] cmp = (∅ : DTreeMap α β cmp).insert k v := by
  rfl

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : DTreeMap α β cmp).insert k v) tl :=
  ext Impl.Const.insertMany_empty_list_cons

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
      (∅ : DTreeMap α Unit cmp) :=
  rfl

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] cmp = (∅ : DTreeMap α Unit cmp).insertIfNew k () :=
  rfl

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) cmp =
      insertManyIfNewUnit ((∅ : DTreeMap α Unit cmp).insertIfNew hd ()) tl :=
  ext Impl.Const.insertManyIfNewUnit_empty_list_cons

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

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).isEmpty = ((t.erase k).isEmpty && (f (t.get? k)).isNone) :=
  Impl.isEmpty_alter_eq_isEmpty_erase t.wf

@[simp]
theorem isEmpty_alter [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (t.get? k)).isNone) :=
  Impl.isEmpty_alter t.wf

theorem contains_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).contains k' =
      if cmp k k' = .eq then (f (t.get? k)).isSome else t.contains k' :=
  Impl.contains_alter t.wf

theorem mem_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    k' ∈ t.alter k f ↔
      if cmp k k' = .eq then (f (t.get? k)).isSome = true else k' ∈ t :=
  Impl.mem_alter t.wf

theorem mem_alter_of_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] {k k': α}
    {f : Option (β k) → Option (β k)}
    (he : cmp k k' = .eq) :
    k' ∈ t.alter k f ↔ (f (t.get? k)).isSome :=
  Impl.mem_alter_of_compare_eq t.wf he

@[simp]
theorem contains_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).contains k = (f (t.get? k)).isSome :=
  Impl.contains_alter_self t.wf

@[simp]
theorem mem_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    k ∈ t.alter k f ↔ (f (t.get? k)).isSome :=
  Impl.mem_alter_self t.wf

theorem contains_alter_of_not_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ cmp k k' = .eq) :
    (t.alter k f).contains k' = t.contains k' :=
  Impl.contains_alter_of_not_compare_eq t.wf he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ cmp k k' = .eq) :
    k' ∈ t.alter k f ↔ k' ∈ t :=
  Impl.mem_alter_of_not_compare_eq t.wf he

theorem size_alter [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).size =
      if k ∈ t ∧ (f (t.get? k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (t.get? k)).isSome then
        t.size + 1
      else
        t.size :=
  Impl.size_alter t.wf

theorem size_alter_eq_add_one [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∉ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f).size = t.size + 1 :=
  Impl.size_alter_eq_add_one t.wf h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f).size = t.size - 1 :=
  Impl.size_alter_eq_sub_one t.wf h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : ¬ k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f).size = t.size :=
  Impl.size_alter_eq_self_of_not_mem t.wf h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f).size = t.size :=
  Impl.size_alter_eq_self_of_mem t.wf h₁ h₂

theorem size_alter_le_size [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).size ≤ t.size + 1 :=
  Impl.size_alter_le_size t.wf

theorem size_le_size_alter [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    t.size - 1 ≤ (t.alter k f).size :=
  Impl.size_le_size_alter t.wf

theorem get?_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get? k' =
      if h : cmp k k' = .eq then
        cast (congrArg (Option ∘ β) (compare_eq_iff_eq.mp h)) (f (t.get? k))
      else
        t.get? k' :=
  Impl.get?_alter t.wf

@[simp]
theorem get?_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get? k = f (t.get? k) := by
  simp [get?_alter]

theorem get_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ (t.alter k f)} :
    (t.alter k f).get k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f (t.get? k)).isSome := mem_alter_of_compare_eq heq |>.mp hc
        cast (congrArg β (compare_eq_iff_eq.mp heq)) <| (f (t.get? k)).get <| h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t.get k' h' :=
  Impl.get_alter t.wf

@[simp]
theorem get_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter k f} :
    haveI h' : (f (t.get? k)).isSome := mem_alter_self.mp hc
    (t.alter k f).get k hc = (f (t.get? k)).get h' :=
  Impl.get_alter_self t.wf

theorem get!_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α} [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get! k' =
      if heq : cmp k k' = .eq then
        (f (t.get? k)).map (cast (congrArg β (compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' :=
  Impl.get!_alter t.wf

@[simp]
theorem get!_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} [Inhabited (β k)]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get! k = (f (t.get? k)).get! :=
  Impl.get!_alter_self t.wf

theorem getD_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α} {fallback : β k'}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getD k' fallback =
      if heq : cmp k k' = .eq then
        f (t.get? k) |>.map (cast (congrArg β <| compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback :=
  Impl.getD_alter t.wf

@[simp]
theorem getD_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {fallback : β k}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getD k fallback = (f (t.get? k)).getD fallback :=
  Impl.getD_alter_self t.wf

theorem getKey?_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey? k' =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then some k else none
      else
        t.getKey? k' :=
  Impl.getKey?_alter t.wf

theorem getKey?_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey? k = if (f (t.get? k)).isSome then some k else none :=
  Impl.getKey?_alter_self t.wf

theorem getKey!_alter [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k k' : α}
    {f : Option (β k) → Option (β k)} : (t.alter k f).getKey! k' =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then k else default
      else
        t.getKey! k' :=
  Impl.getKey!_alter t.wf

theorem getKey!_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey! k = if (f (t.get? k)).isSome then k else default :=
  Impl.getKey!_alter_self t.wf

theorem getKey_alter [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ t.alter k f} :
    (t.alter k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t.getKey k' h' :=
  Impl.getKey_alter t.wf

@[simp]
theorem getKey_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter k f} :
    (t.alter k f).getKey k hc = k :=
  Impl.getKey_alter_self t.wf

theorem getKeyD_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' fallback : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.getKeyD_alter t.wf

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    {fallback : α} {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKeyD k fallback = if (f (t.get? k)).isSome then k else fallback :=
  Impl.getKeyD_alter_self t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

theorem isEmpty_alter_eq_isEmpty_erase [TransCmp cmp] {k : α}
    {f : Option β → Option β} :
    (alter t k f).isEmpty = ((t.erase k).isEmpty && (f (get? t k)).isNone) :=
   Impl.Const.isEmpty_alter_eq_isEmpty_erase t.wf

@[simp]
theorem isEmpty_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (get? t k)).isNone) :=
  Impl.Const.isEmpty_alter t.wf

theorem contains_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).contains k' =
      if cmp k k' = .eq then (f (get? t k)).isSome else t.contains k' :=
  Impl.Const.contains_alter t.wf

theorem mem_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    k' ∈ alter t k f ↔
      if cmp k k' = .eq then (f (get? t k)).isSome = true else k' ∈ t :=
  Impl.Const.mem_alter t.wf

theorem mem_alter_of_compare_eq [TransCmp cmp] {k k': α} {f : Option β → Option β}
    (he : cmp k k' = .eq) :
    k' ∈ alter t k f ↔ (f (get? t k)).isSome :=
  Impl.Const.mem_alter_of_compare_eq t.wf he

@[simp]
theorem contains_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).contains k = (f (get? t k)).isSome :=
  Impl.Const.contains_alter_self t.wf

@[simp]
theorem mem_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    k ∈ alter t k f ↔ (f (get? t k)).isSome :=
  Impl.Const.mem_alter_self t.wf

theorem contains_alter_of_not_compare_eq [TransCmp cmp] {k k' : α}
    {f : Option β → Option β} (he : ¬ cmp k k' = .eq) :
    (alter t k f).contains k' = t.contains k' :=
  Impl.Const.contains_alter_of_not_compare_eq t.wf he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : ¬ cmp k k' = .eq) :
    k' ∈ alter t k f ↔ k' ∈ t :=
  Impl.Const.mem_alter_of_not_compare_eq t.wf he

theorem size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size =
      if k ∈ t ∧ (f (get? t k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (get? t k)).isSome then
        t.size + 1
      else
        t.size :=
  Impl.Const.size_alter t.wf

theorem size_alter_eq_add_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f (get? t k)).isSome) :
    (alter t k f).size = t.size + 1 :=
  Impl.Const.size_alter_eq_add_one t.wf h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter t k f).size = t.size - 1 :=
  Impl.Const.size_alter_eq_sub_one t.wf h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter t k f).size = t.size :=
  Impl.Const.size_alter_eq_self_of_not_mem t.wf h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isSome) :
    (alter t k f).size = t.size :=
  Impl.Const.size_alter_eq_self_of_mem t.wf h₁ h₂

theorem size_alter_le_size [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size ≤ t.size + 1 :=
  Impl.Const.size_alter_le_size t.wf

theorem size_le_size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter t k f).size :=
  Impl.Const.size_le_size_alter t.wf

theorem get?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    get? (alter t k f) k' =
      if cmp k k' = .eq then
        f (get? t k)
      else
        get? t k' :=
  Impl.Const.get?_alter t.wf

@[simp]
theorem get?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    get? (alter t k f) k = f (get? t k) :=
  Impl.Const.get?_alter_self t.wf

theorem get_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter t k f)} :
    get (alter t k f) k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f (get? t k)).isSome := mem_alter_of_compare_eq heq |>.mp hc
        (f (get? t k)).get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        get t k' h' :=
  Impl.Const.get_alter t.wf

@[simp]
theorem get_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    haveI h' : (f (get? t k)).isSome := mem_alter_self.mp hc
    get (alter t k f) k hc = (f (get? t k)).get h' :=
  Impl.Const.get_alter_self t.wf

theorem get!_alter [TransCmp cmp] {k k' : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter t k f) k' =
      if cmp k k' = .eq then
        (f (get? t k)).get!
      else
        get! t k' :=
  Impl.Const.get!_alter t.wf

@[simp]
theorem get!_alter_self [TransCmp cmp] {k : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter t k f) k = (f (get? t k)).get! :=
  Impl.Const.get!_alter_self t.wf

theorem getD_alter [TransCmp cmp] {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter t k f) k' fallback =
      if cmp k k' = .eq then
        f (get? t k) |>.getD fallback
      else
        getD t k' fallback :=
  Impl.Const.getD_alter t.wf

@[simp]
theorem getD_alter_self [TransCmp cmp] {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter t k f) k fallback = (f (get? t k)).getD fallback :=
  Impl.Const.getD_alter_self t.wf

theorem getKey?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey? k' =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then some k else none
      else
        t.getKey? k' :=
  Impl.Const.getKey?_alter t.wf

theorem getKey?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).getKey? k = if (f (get? t k)).isSome then some k else none :=
  Impl.Const.getKey?_alter_self t.wf

theorem getKey!_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey! k' =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then k else default
      else
        t.getKey! k' :=
  Impl.Const.getKey!_alter t.wf

theorem getKey!_alter_self [TransCmp cmp] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (alter t k f).getKey! k = if (f (get? t k)).isSome then k else default :=
  Impl.Const.getKey!_alter_self t.wf

theorem getKey_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter t k f} :
    (alter t k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : t.contains k' := mem_alter_of_not_compare_eq heq |>.mp hc
        t.getKey k' h' :=
  Impl.Const.getKey_alter t.wf

@[simp]
theorem getKey_alter_self [TransCmp cmp] [Inhabited α] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    (alter t k f).getKey k hc = k :=
  Impl.Const.getKey_alter_self t.wf

theorem getKeyD_alter [TransCmp cmp] {k k' fallback : α} {f : Option β → Option β} :
    (alter t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.Const.getKeyD_alter t.wf

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [Inhabited α] {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter t k f).getKeyD k fallback = if (f (get? t k)).isSome then k else fallback :=
  Impl.Const.getKeyD_alter_self t.wf

end Const

end Alter

section Modify

variable [TransCmp cmp]

section Dependent

variable [LawfulEqCmp cmp]

@[simp]
theorem isEmpty_modify {k : α} {f : β k → β k} :
    (t.modify k f).isEmpty = t.isEmpty :=
  Impl.isEmpty_modify t.wf

theorem contains_modify {k k' : α} {f : β k → β k} :
    (t.modify k f).contains k' = t.contains k' :=
  Impl.contains_modify t.wf

theorem mem_modify {k k' : α} {f : β k → β k} :
    k' ∈ t.modify k f ↔ k' ∈ t :=
  Impl.mem_modify t.wf

theorem size_modify {k : α} {f : β k → β k} :
    (t.modify k f).size = t.size :=
  Impl.size_modify t.wf

theorem get?_modify {k k' : α} {f : β k → β k} :
    (t.modify k f).get? k' =
      if h : cmp k k' = .eq then
        (cast (congrArg (Option ∘ β) (compare_eq_iff_eq.mp h)) ((t.get? k).map f))
      else
        t.get? k' :=
  Impl.get?_modify t.wf

@[simp]
theorem get?_modify_self {k : α} {f : β k → β k} :
    (t.modify k f).get? k = (t.get? k).map f :=
  Impl.get?_modify_self t.wf

theorem get_modify {k k' : α} {f : β k → β k} {hc : k' ∈ t.modify k f} :
    (t.modify k f).get k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr heq |>.mpr <| mem_modify.mp hc
        cast (congrArg β (compare_eq_iff_eq.mp heq)) <| f (t.get k h')
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.get k' h' :=
  Impl.get_modify t.wf

@[simp]
theorem get_modify_self {k : α} {f : β k → β k} {hc : k ∈ t.modify k f} :
    haveI h' : k ∈ t := mem_modify.mp hc
    (t.modify k f).get k hc = f (t.get k h') :=
  Impl.get_modify_self t.wf

theorem get!_modify {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (t.modify k f).get! k' =
      if heq : cmp k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β (compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' :=
  Impl.get!_modify t.wf

@[simp]
theorem get!_modify_self {k : α} [Inhabited (β k)] {f : β k → β k} :
    (t.modify k f).get! k = ((t.get? k).map f).get! :=
  Impl.get!_modify_self t.wf

theorem getD_modify {k k' : α} {fallback : β k'} {f : β k → β k} :
    (t.modify k f).getD k' fallback =
      if heq : cmp k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β <| compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback :=
  Impl.getD_modify t.wf

@[simp]
theorem getD_modify_self {k : α} {fallback : β k} {f : β k → β k} :
    (t.modify k f).getD k fallback = ((t.get? k).map f).getD fallback :=
  Impl.getD_modify_self t.wf

theorem getKey?_modify {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  Impl.getKey?_modify t.wf

theorem getKey?_modify_self {k : α} {f : β k → β k} :
    (t.modify k f).getKey? k = if k ∈ t then some k else none :=
  Impl.getKey?_modify_self t.wf

theorem getKey!_modify [Inhabited α] {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  Impl.getKey!_modify t.wf

theorem getKey!_modify_self [Inhabited α] {k : α} {f : β k → β k} :
    (t.modify k f).getKey! k = if k ∈ t then k else default :=
  Impl.getKey!_modify_self t.wf

theorem getKey_modify [Inhabited α] {k k' : α} {f : β k → β k}
    {hc : k' ∈ t.modify k f} :
    (t.modify k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.getKey k' h' :=
  Impl.getKey_modify t.wf

@[simp]
theorem getKey_modify_self [Inhabited α] {k : α} {f : β k → β k}
    {hc : k ∈ t.modify k f} : (t.modify k f).getKey k hc = k :=
  Impl.getKey_modify_self t.wf

theorem getKeyD_modify {k k' fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.getKeyD_modify t.wf

theorem getKeyD_modify_self [Inhabited α] {k fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  Impl.getKeyD_modify_self t.wf

end Dependent

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

@[simp]
theorem isEmpty_modify {k : α} {f : β → β} :
    (modify t k f).isEmpty = t.isEmpty :=
  Impl.Const.isEmpty_modify t.wf

theorem contains_modify {k k' : α} {f : β → β} :
    (modify t k f).contains k' = t.contains k' :=
  Impl.Const.contains_modify t.wf

theorem mem_modify {k k' : α} {f : β → β} :
    k' ∈ modify t k f ↔ k' ∈ t :=
  Impl.Const.mem_modify t.wf

theorem size_modify {k : α} {f : β → β} :
    (modify t k f).size = t.size :=
  Impl.Const.size_modify t.wf

theorem get?_modify {k k' : α} {f : β → β} :
    get? (modify t k f) k' =
      if cmp k k' = .eq then
        (get? t k).map f
      else
        get? t k' :=
  Impl.Const.get?_modify t.wf

@[simp]
theorem get?_modify_self {k : α} {f : β → β} :
    get? (modify t k f) k = (get? t k).map f :=
  Impl.Const.get?_modify_self t.wf

theorem get_modify {k k' : α} {f : β → β} {hc : k' ∈ modify t k f} :
    get (modify t k f) k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr heq |>.mpr <| mem_modify.mp hc
        f (get t k h')
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        get t k' h' :=
  Impl.Const.get_modify t.wf

@[simp]
theorem get_modify_self {k : α} {f : β → β} {hc : k ∈ modify t k f} :
    haveI h' : k ∈ t := mem_modify.mp hc
    get (modify t k f) k hc = f (get t k h') :=
  Impl.Const.get_modify_self t.wf

theorem get!_modify {k k' : α} [hi : Inhabited β] {f : β → β} :
    get! (modify t k f) k' =
      if cmp k k' = .eq then
        get? t k |>.map f |>.get!
      else
        get! t k' :=
  Impl.Const.get!_modify t.wf

@[simp]
theorem get!_modify_self {k : α} [Inhabited β] {f : β → β} :
    get! (modify t k f) k = ((get? t k).map f).get! :=
  Impl.Const.get!_modify_self t.wf

theorem getD_modify {k k' : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k' fallback =
      if cmp k k' = .eq then
        get? t k |>.map f |>.getD fallback
      else
        getD t k' fallback :=
  Impl.Const.getD_modify t.wf

@[simp]
theorem getD_modify_self {k : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k fallback = ((get? t k).map f).getD fallback :=
  Impl.Const.getD_modify_self t.wf

theorem getKey?_modify {k k' : α} {f : β → β} :
    (modify t k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  Impl.Const.getKey?_modify t.wf

theorem getKey?_modify_self {k : α} {f : β → β} :
    (modify t k f).getKey? k = if k ∈ t then some k else none :=
  Impl.Const.getKey?_modify_self t.wf

theorem getKey!_modify [Inhabited α] {k k' : α} {f : β → β} :
    (modify t k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  Impl.Const.getKey!_modify t.wf

theorem getKey!_modify_self [Inhabited α] {k : α} {f : β → β} :
    (modify t k f).getKey! k = if k ∈ t then k else default :=
  Impl.Const.getKey!_modify_self t.wf

theorem getKey_modify [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify t k f} :
    (modify t k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.getKey k' h' :=
  Impl.Const.getKey_modify t.wf

@[simp]
theorem getKey_modify_self [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify t k f} : (modify t k f).getKey k hc = k :=
  Impl.Const.getKey_modify_self t.wf

theorem getKeyD_modify {k k' fallback : α} {f : β → β} :
    (modify t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.Const.getKeyD_modify t.wf

theorem getKeyD_modify_self [Inhabited α] {k fallback : α} {f : β → β} :
    (modify t k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  Impl.Const.getKeyD_modify_self t.wf

end Const

end Modify

section Min

@[simp]
theorem minKey?_emptyc :
    (∅ : DTreeMap α β cmp).minKey? = none :=
  Impl.minKey?_empty

theorem minKey?_of_isEmpty [TransCmp cmp] :
    (he : t.isEmpty) → t.minKey? = none :=
  Impl.minKey?_of_isEmpty t.wf

@[simp]
theorem minKey?_eq_none_iff [TransCmp cmp] :
    t.minKey? = none ↔ t.isEmpty :=
  Impl.minKey?_eq_none_iff t.wf

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  Impl.minKey?_eq_some_iff_getKey?_eq_self_and_forall t.wf

theorem minKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  Impl.minKey?_eq_some_iff_mem_and_forall t.wf

@[simp]
theorem isNone_minKey?_eq_isEmpty [TransCmp cmp] :
    t.minKey?.isNone = t.isEmpty :=
  Impl.isNone_minKey?_eq_isEmpty t.wf

@[simp]
theorem isSome_minKey?_eq_not_isEmpty [TransCmp cmp] :
    t.minKey?.isSome = !t.isEmpty :=
  Impl.isSome_minKey?_eq_not_isEmpty t.wf

theorem isSome_minKey?_iff_isEmpty_eq_false [TransCmp cmp] :
    t.minKey?.isSome ↔ t.isEmpty = false :=
  Impl.isSome_minKey?_iff_isEmpty_eq_false t.wf

theorem minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k'|>.isLE then k else k') :=
  Impl.minKey?_insert t.wf

theorem isSome_minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey?.isSome :=
  Impl.isSome_minKey?_insert t.wf

theorem minKey?_insert_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v |>.minKey? |>.get isSome_minKey?_insert) = kmi) →
    cmp kmi km |>.isLE :=
  Impl.minKey?_insert_le_minKey? t.wf

theorem minKey?_insert_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.minKey?.get isSome_minKey?_insert) = kmi) →
    cmp kmi k |>.isLE :=
  Impl.minKey?_insert_le_self t.wf

theorem contains_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) →
    t.contains km :=
  Impl.contains_minKey? t.wf

theorem minKey?_mem [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) →
    km ∈ t:=
  Impl.minKey?_mem t.wf

theorem isSome_minKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.minKey?.isSome :=
  Impl.isSome_minKey?_of_contains t.wf

theorem isSome_minKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.minKey?.isSome :=
  Impl.isSome_minKey?_of_mem t.wf

theorem minKey?_le_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains hc) = km) →
    cmp km k |>.isLE :=
  Impl.minKey?_le_of_contains t.wf

theorem minKey?_le_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem hc) = km) →
    cmp km k |>.isLE :=
  Impl.minKey?_le_of_mem t.wf

theorem le_minKey? [TransCmp cmp] {k} :
    (∀ k', t.minKey? = some k' → (cmp k k').isLE) ↔
      (∀ k', k' ∈ t → (cmp k k').isLE) :=
  Impl.le_minKey? t.wf

theorem getKey?_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km :=
  Impl.getKey?_minKey? t.wf

@[simp]
theorem minKey?_bind_getKey? [TransCmp cmp] :
    t.minKey?.bind t.getKey? = t.minKey? :=
  Impl.minKey?_bind_getKey? t.wf

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (t.erase k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq :=
  Impl.minKey?_erase_eq_iff_not_compare_eq_minKey? t.wf

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.minKey?) = t.minKey? :=
  Impl.minKey?_erase_eq_of_not_compare_eq_minKey? t.wf

theorem isSome_minKey?_of_isSome_minKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.minKey?.isSome) →
    t.minKey?.isSome :=
  Impl.isSome_minKey?_of_isSome_minKey?_erase t.wf

theorem minKey?_le_minKey?_erase [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  Impl.minKey?_le_minKey?_erase t.wf

theorem minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey? =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  Impl.minKey?_insertIfNew t.wf

theorem isSome_minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey?.isSome :=
  Impl.isSome_minKey?_insertIfNew t.wf

theorem minKey?_insertIfNew_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.minKey? |>.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi km |>.isLE :=
  Impl.minKey?_insertIfNew_le_minKey? t.wf

theorem minKey?_insertIfNew_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.minKey?.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi k |>.isLE :=
  Impl.minKey?_insertIfNew_le_self t.wf

@[simp]
theorem minKey?_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).minKey? = t.minKey? :=
  Impl.minKey?_modify t.wf

theorem minKey?_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.alter k f).minKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.minKey?_alter_eq_self t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

theorem minKey?_modify [TransCmp cmp] {k f} :
    (Const.modify t k f).minKey? = t.minKey?.map fun km => if cmp km k = .eq then k else km :=
  Impl.Const.minKey?_modify t.wf

@[simp]
theorem minKey?_modify_eq_minKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (Const.modify t k f).minKey? = t.minKey? :=
  Impl.Const.minKey?_modify_eq_minKey? t.wf

theorem isSome_minKey?_modify [TransCmp cmp] {k f} :
    (Const.modify t k f).minKey?.isSome = !t.isEmpty :=
  Impl.Const.isSome_minKey?_modify t.wf

theorem isSome_minKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (Const.modify t k f).minKey?.isSome = t.minKey?.isSome :=
  Impl.Const.isSome_minKey?_modify_eq_isSome t.wf

theorem compare_minKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (Const.modify t k f |>.minKey? |>.get <|
        isSome_minKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  Impl.Const.compare_minKey?_modify_eq t.wf

theorem minKey?_alter_eq_self [TransCmp cmp] {k f} :
    (Const.alter t k f).minKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.Const.minKey?_alter_eq_self t.wf

end Const

theorem minKey_eq_get_minKey? [TransCmp cmp] {he} :
    t.minKey he = t.minKey?.get (isSome_minKey?_iff_isEmpty_eq_false.mpr he) :=
  Impl.minKey_eq_get_minKey? t.wf

theorem minKey?_eq_some_minKey [TransCmp cmp] {he} :
    t.minKey? = some (t.minKey he) :=
  Impl.minKey?_eq_some_minKey t.wf

theorem minKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.minKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  Impl.minKey_eq_iff_getKey?_eq_self_and_forall t.wf

theorem minKey_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.minKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  Impl.minKey_eq_some_iff_mem_and_forall t.wf

theorem minKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey isEmpty_insert =
      t.minKey?.elim k fun k' => if cmp k k'|>.isLE then k else k' :=
  Impl.minKey_insert t.wf

theorem minKey_insert_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insert k v |>.minKey isEmpty_insert) (t.minKey he) |>.isLE :=
  Impl.minKey_insert_le_minKey t.wf

theorem minKey_insert_le_self [TransCmp cmp] {k v} :
    cmp (t.insert k v |>.minKey isEmpty_insert) k |>.isLE :=
  Impl.minKey_insert_le_self t.wf

theorem contains_minKey [TransCmp cmp] {he} :
    t.contains (t.minKey he) :=
  Impl.contains_minKey t.wf

theorem minKey_mem [TransCmp cmp] {he} :
    t.minKey he ∈ t :=
  Impl.minKey_mem t.wf

theorem minKey_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp (t.minKey <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) k |>.isLE :=
  Impl.minKey_le_of_contains t.wf hc

theorem minKey_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp (t.minKey <| isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨k, hc⟩) k |>.isLE :=
  Impl.minKey_le_of_mem t.wf hc

theorem le_minKey [TransCmp cmp] {k he} :
    (cmp k (t.minKey he)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  Impl.le_minKey t.wf

@[simp]
theorem getKey?_minKey [TransCmp cmp] {he} :
    t.getKey? (t.minKey he) = some (t.minKey he) :=
  Impl.getKey?_minKey t.wf

@[simp]
theorem getKey_minKey [TransCmp cmp] {he hc} :
    t.getKey (t.minKey he) hc = t.minKey he :=
  Impl.getKey_minKey t.wf

@[simp]
theorem getKey!_minKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.minKey he) = t.minKey he :=
  Impl.getKey!_minKey t.wf

@[simp]
theorem getKeyD_minKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.minKey he) fallback = t.minKey he :=
  Impl.getKeyD_minKey t.wf

@[simp]
theorem minKey_erase_eq_iff_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (t.erase k |>.minKey he) =
        t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he) ↔
      ¬ cmp k (t.minKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false he) = .eq :=
  Impl.minKey_erase_eq_iff_not_compare_eq_minKey t.wf

theorem minKey_erase_eq_of_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he)) = .eq) →
    (t.erase k |>.minKey he) =
      t.minKey (isEmpty_eq_false_of_isEmpty_erase_eq_false he) :=
  Impl.minKey_erase_eq_of_not_compare_eq_minKey t.wf

theorem minKey_le_minKey_erase [TransCmp cmp] {k he} :
    cmp (t.minKey <| isEmpty_eq_false_of_isEmpty_erase_eq_false he)
      (t.erase k |>.minKey he) |>.isLE :=
  Impl.minKey_le_minKey_erase t.wf

theorem minKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey isEmpty_insertIfNew =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  Impl.minKey_insertIfNew t.wf

theorem minKey_insertIfNew_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insertIfNew k v |>.minKey isEmpty_insertIfNew)
      (t.minKey he) |>.isLE :=
  Impl.minKey_insertIfNew_le_minKey t.wf

theorem minKey_insertIfNew_le_self [TransCmp cmp] {k v} :
    cmp (t.insertIfNew k v |>.minKey <| isEmpty_insertIfNew) k |>.isLE :=
  Impl.minKey_insertIfNew_le_self t.wf

@[simp]
theorem minKey_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (t.modify k f).minKey he = t.minKey (cast (congrArg (· = false) isEmpty_modify) he) :=
  Impl.minKey_modify t.wf

theorem minKey_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (t.alter k f).minKey he = k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.minKey_alter_eq_self t.wf

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

theorem minKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).minKey he =
      if cmp (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) k = .eq then
        k
      else
        (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) :=
  Impl.Const.minKey_modify t.wf

@[simp]
theorem minKey_modify_eq_minKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).minKey he = t.minKey (cast (congrArg (· = false) isEmpty_modify) he) :=
  Impl.Const.minKey_modify_eq_minKey t.wf

@[simp]
theorem compare_minKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.minKey he)
      (t.minKey <| cast (congrArg (· = false) isEmpty_modify) he) = .eq :=
  Impl.Const.compare_minKey_modify_eq t.wf

theorem minKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).minKey he = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.Const.minKey_alter_eq_self t.wf

end Const

theorem minKey?_eq_some_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.minKey? = some t.minKey! :=
  Impl.minKey?_eq_some_minKey! t.wf he

theorem minKey!_eq_default [TransCmp cmp] [Inhabited α] (he : t.isEmpty) :
    t.minKey! = default :=
  Impl.minKey!_eq_default t.wf he

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  Impl.minKey!_eq_iff_getKey?_eq_self_and_forall t.wf he

theorem minKey!_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  Impl.minKey!_eq_some_iff_mem_and_forall t.wf he

theorem minKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v |>.minKey!) =
      (t.minKey?.elim k fun k' => if cmp k k'|>.isLE then k else k') :=
  Impl.minKey!_insert t.wf

theorem minKey!_insert_le_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k v} :
    cmp (t.insert k v |>.minKey!) t.minKey! |>.isLE :=
  Impl.minKey!_insert_le_minKey! t.wf he

theorem minKey!_insert_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insert k v |>.minKey!) k |>.isLE :=
  Impl.minKey!_insert_le_self t.wf

theorem contains_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.contains t.minKey! :=
  Impl.contains_minKey! t.wf he

theorem minKey!_mem [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.minKey! ∈ t :=
  Impl.minKey!_mem t.wf he

theorem minKey!_le_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp t.minKey! k |>.isLE :=
  Impl.minKey!_le_of_contains t.wf hc

theorem minKey!_le_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp t.minKey! k |>.isLE :=
  Impl.minKey!_le_of_mem t.wf hc

theorem le_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k} :
    (cmp k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  Impl.le_minKey! t.wf he

theorem getKey?_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.getKey? t.minKey! = some t.minKey! :=
  Impl.getKey?_minKey! t.wf he

theorem getKey_minKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey! :=
  Impl.getKey_minKey! t.wf

@[simp]
theorem getKey_minKey!_eq_minKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey (isEmpty_eq_false_of_contains hc) :=
  Impl.getKey_minKey!_eq_minKey t.wf

theorem getKey!_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) :
    t.getKey! t.minKey! = t.minKey! :=
  Impl.getKey!_minKey! t.wf he

theorem getKeyD_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.minKey! fallback = t.minKey! :=
  Impl.getKeyD_minKey! t.wf he

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.minKey! = .eq) :
    (t.erase k |>.minKey!) = t.minKey! :=
  Impl.minKey!_erase_eq_of_not_compare_minKey!_eq t.wf he heq

theorem minKey!_le_minKey!_erase [TransCmp cmp] [Inhabited α] {k}
    (he : (t.erase k).isEmpty = false) :
    cmp t.minKey! (t.erase k |>.minKey!) |>.isLE :=
  Impl.minKey!_le_minKey!_erase t.wf he

theorem minKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v |>.minKey!) =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  Impl.minKey!_insertIfNew t.wf

theorem minKey!_insertIfNew_le_minKey! [TransCmp cmp] [Inhabited α] (he : t.isEmpty = false) {k v} :
    cmp (t.insertIfNew k v |>.minKey!) t.minKey! |>.isLE :=
  Impl.minKey!_insertIfNew_le_minKey! t.wf he

theorem minKey!_insertIfNew_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insertIfNew k v |>.minKey!) k |>.isLE :=
  Impl.minKey!_insertIfNew_le_self t.wf

@[simp]
theorem minKey!_modify [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (t.modify k f |>.minKey!) = t.minKey! :=
  Impl.minKey!_modify t.wf

theorem minKey!_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f}
    (he : (t.alter k f).isEmpty = false) :
    (t.alter k f |>.minKey!) = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.minKey!_alter_eq_self t.wf he

namespace Const

variable {β : Type v} {t : DTreeMap α β cmp}

theorem minKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f |> minKey!) = if cmp t.minKey! k = .eq then k else t.minKey! :=
  Impl.Const.minKey!_modify t.wf he

@[simp]
theorem minKey!_modify_eq_minKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f |>.minKey!) = t.minKey! :=
  Impl.Const.minKey!_modify_eq_minKey! t.wf

@[simp]
theorem compare_minKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f |> minKey!) t.minKey! = .eq :=
  Impl.Const.compare_minKey!_modify_eq t.wf (instOrd := ⟨cmp⟩)

theorem minKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f |>.minKey!) = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.Const.minKey!_alter_eq_self t.wf he

end Const

end Min

end Std.DTreeMap
