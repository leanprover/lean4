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
    t.keys.isEmpty = t.isEmpty  :=
  Impl.isEmpty_keys

@[simp]
theorem contains_keys [BEq α] [LawfulBEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  by exact Impl.contains_keys t.wf

@[simp]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  Impl.mem_keys t.wf

theorem distinct_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  Impl.distinct_keys t.wf

@[simp]
theorem map_sigma_fst_toList_eq_keys :
    t.toList.map Sigma.fst = t.keys :=
  Impl.map_sigma_fst_toList_eq_keys

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

theorem find?_toList_eq_some_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k}
    : t.toList.find? (cmp ·.1 k == .eq) = some ⟨k, v⟩ ↔ t.get? k = some v :=
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
theorem map_prod_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  Impl.Const.map_prod_fst_toList_eq_keys

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

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] {k k' : α} {v : β}
    : (toList t).find? (fun a => cmp a.1 k = .eq) = some ⟨k', v⟩ ↔
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

end Std.DTreeMap
