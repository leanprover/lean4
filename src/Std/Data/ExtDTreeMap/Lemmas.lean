/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Std.Data.ExtDTreeMap.Basic

@[expose] public section

/-!
# Extensional dependent tree map lemmas

This file contains lemmas about `Std.ExtDTreeMap`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

attribute [local instance] Std.DTreeMap.isSetoid

universe u v w w'

namespace Std.ExtDTreeMap

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {cmp : α → α → Ordering} {t : ExtDTreeMap α β cmp}
local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

@[simp, grind =]
theorem isEmpty_empty : (∅ : ExtDTreeMap α β cmp).isEmpty :=
  rfl

@[simp]
theorem empty_eq : ∅ = t ↔ t = ∅ := eq_comm

@[simp]
theorem insert_ne_empty [TransCmp cmp] {k : α} {v : β k} :
    t.insert k v ≠ ∅ :=
  t.inductionOn fun _ => isEmpty_eq_false_iff.mp DTreeMap.isEmpty_insert

theorem mem_iff_contains [TransCmp cmp] {k : α} : k ∈ t ↔ t.contains k :=
  Iff.rfl

@[simp, grind _=_]
theorem contains_iff_mem [TransCmp cmp] {k : α} : t.contains k ↔ k ∈ t :=
  Iff.rfl

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  t.inductionOn (fun _ hab => DTreeMap.contains_congr hab) hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  t.inductionOn (fun _ hab => DTreeMap.mem_congr hab) hab

@[simp, grind =]
theorem contains_empty [TransCmp cmp] {k : α} : (∅ : ExtDTreeMap α β cmp).contains k = false :=
  rfl

@[simp]
theorem not_mem_empty [TransCmp cmp] {k : α} : k ∉ (∅ : ExtDTreeMap α β cmp) :=
  Bool.false_ne_true

theorem eq_empty_iff_forall_contains [TransCmp cmp] : t = ∅ ↔ ∀ a, t.contains a = false :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.isEmpty_iff_forall_contains

theorem eq_empty_iff_forall_not_mem [TransCmp cmp] : t = ∅ ↔ ∀ a, ¬a ∈ t :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.isEmpty_iff_forall_not_mem

theorem ne_empty_of_mem [TransCmp cmp] {a : α} (h : a ∈ t) : t ≠ ∅ :=
  (not_congr eq_empty_iff_forall_not_mem).mpr fun h' => h' a h

@[simp]
theorem insert_eq_insert [TransCmp cmp] {p : (a : α) × β a} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert [TransCmp cmp] {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : ExtDTreeMap α β cmp).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [TransCmp cmp] {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  t.inductionOn fun _ => DTreeMap.contains_insert

@[simp, grind =]
theorem mem_insert [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_insert

theorem contains_insert_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).contains k :=
  t.inductionOn fun _ => DTreeMap.contains_insert_self

theorem mem_insert_self [TransCmp cmp] {k : α} {v : β k} :
    k ∈ t.insert k v :=
  t.inductionOn fun _ => DTreeMap.mem_insert_self

theorem contains_of_contains_insert [TransCmp cmp] {k a : α} {v : β k} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_insert

theorem mem_of_mem_insert [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_of_mem_insert

@[simp, grind =]
theorem size_empty : (∅ : ExtDTreeMap α β cmp).size = 0 :=
  rfl

theorem isEmpty_eq_size_beq_zero : t.isEmpty = (t.size == 0) :=
  t.inductionOn fun _ => DTreeMap.isEmpty_eq_size_eq_zero

theorem eq_empty_iff_size_eq_zero [TransCmp cmp] : t = ∅ ↔ t.size = 0 := by
  cases t with | mk t
  simpa only [← isEmpty_iff, ← decide_eq_decide, Bool.decide_eq_true] using isEmpty_eq_size_beq_zero

@[grind =] theorem size_insert [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  t.inductionOn fun _ => DTreeMap.size_insert

theorem size_le_size_insert [TransCmp cmp] {k : α} {v : β k} :
    t.size ≤ (t.insert k v).size :=
  t.inductionOn fun _ => DTreeMap.size_le_size_insert

theorem size_insert_le [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).size ≤ t.size + 1 :=
  t.inductionOn fun _ => DTreeMap.size_insert_le

@[simp, grind =]
theorem erase_empty [TransCmp cmp] {k : α} : (∅ : ExtDTreeMap α β cmp).erase k = ∅ :=
  rfl

@[simp]
theorem erase_eq_empty_iff [TransCmp cmp] {k : α} :
    t.erase k = ∅ ↔ t = ∅ ∨ (t.size = 1 ∧ k ∈ t) := by
  cases t with | mk t
  simp only [← isEmpty_iff, ← decide_eq_decide, Bool.decide_eq_true, Bool.decide_or,
    Bool.decide_and, mem_iff_contains]
  exact DTreeMap.isEmpty_erase

theorem eq_empty_iff_erase_eq_empty_and_not_mem [TransCmp cmp] (k : α) :
    t = ∅ ↔ t.erase k = ∅ ∧ ¬k ∈ t := by
  cases t with | mk t
  simp only [← isEmpty_iff, mem_iff_contains, ← decide_eq_decide, Bool.decide_eq_true,
    Bool.decide_and, decide_not]
  exact DTreeMap.isEmpty_eq_isEmpty_erase_and_not_contains k

theorem ne_empty_of_erase_ne_empty [TransCmp cmp] {k : α} (h : t.erase k ≠ ∅) : t ≠ ∅ := by
  simp_all

@[simp, grind =]
theorem contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  t.inductionOn fun _ => DTreeMap.contains_erase

@[simp, grind =]
theorem mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_erase

theorem contains_of_contains_erase [TransCmp cmp] {k a : α} :
    (t.erase k).contains a → t.contains a :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_erase

theorem mem_of_mem_erase [TransCmp cmp] {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_of_mem_erase

@[grind =] theorem size_erase [TransCmp cmp] {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  t.inductionOn fun _ => DTreeMap.size_erase

theorem size_erase_le [TransCmp cmp] {k : α} :
    (t.erase k).size ≤ t.size :=
  t.inductionOn fun _ => DTreeMap.size_erase_le

theorem size_le_size_erase [TransCmp cmp] {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  t.inductionOn fun _ => DTreeMap.size_le_size_erase

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsert k v).1 = t.contains k :=
  t.inductionOn fun _ => DTreeMap.containsThenInsert_fst

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  t.inductionOn fun _ => congrArg mk DTreeMap.containsThenInsert_snd

@[simp, grind =]
theorem containsThenInsertIfNew_fst [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  t.inductionOn fun _ => DTreeMap.containsThenInsertIfNew_fst

@[simp, grind =]
theorem containsThenInsertIfNew_snd [TransCmp cmp] {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  t.inductionOn fun _ => congrArg mk DTreeMap.containsThenInsertIfNew_snd

@[simp, grind =]
theorem get?_empty [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (∅ : ExtDTreeMap α β cmp).get? a = none :=
  DTreeMap.get?_emptyc

@[grind =] theorem get?_insert [TransCmp cmp] [LawfulEqCmp cmp] {a k : α} {v : β k} :
    (t.insert k v).get? a =
      if h : cmp k a = .eq then some (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h)) v) else t.get? a :=
  t.inductionOn fun _ => DTreeMap.get?_insert

@[simp]
theorem get?_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.insert k v).get? k = some v :=
  t.inductionOn fun _ => DTreeMap.get?_insert_self

theorem contains_eq_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    t.contains a = (t.get? a).isSome :=
  t.inductionOn fun _ => DTreeMap.contains_eq_isSome_get?

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (t.get? a).isSome = t.contains a :=
  t.inductionOn fun _ => DTreeMap.isSome_get?_eq_contains

theorem mem_iff_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  t.inductionOn fun _ => DTreeMap.mem_iff_isSome_get?

@[simp]
theorem isSome_get?_iff_mem [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (t.get? a).isSome ↔ a ∈ t :=
  t.inductionOn fun _ => DTreeMap.isSome_get?_iff_mem

theorem get?_eq_some_iff [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    t.get? k = some v ↔ ∃ h, t.get k h = v :=
  t.inductionOn fun _ => DTreeMap.get?_eq_some_iff

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    t.contains a = false → t.get? a = none :=
  t.inductionOn fun _ => DTreeMap.get?_eq_none_of_contains_eq_false

theorem get?_eq_none [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  t.inductionOn fun _ => DTreeMap.get?_eq_none

@[grind =] theorem get?_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  t.inductionOn fun _ => DTreeMap.get?_erase

@[simp]
theorem get?_erase_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} :
    (t.erase k).get? k = none :=
  t.inductionOn fun _ => DTreeMap.get?_erase_self

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp, grind =]
theorem get?_empty [TransCmp cmp] {a : α} :
    get? (∅ : ExtDTreeMap α β cmp) a = none :=
  DTreeMap.Const.get?_emptyc

@[grind =] theorem get?_insert [TransCmp cmp] {a k : α} {v : β} :
    get? (t.insert k v) a =
      if cmp k a = .eq then some v else get? t a :=
  t.inductionOn fun _ => DTreeMap.Const.get?_insert

@[simp]
theorem get?_insert_self [TransCmp cmp] {k : α} {v : β} :
    get? (t.insert k v) k = some v :=
  t.inductionOn fun _ => DTreeMap.Const.get?_insert_self

theorem contains_eq_isSome_get? [TransCmp cmp] {a : α} :
    t.contains a = (get? t a).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.contains_eq_isSome_get?

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] {a : α} :
    (get? t a).isSome = t.contains a :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_get?_eq_contains

theorem mem_iff_isSome_get? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (get? t a).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.mem_iff_isSome_get?

theorem get?_eq_some_iff [TransCmp cmp] {k : α} {v : β} :
    get? t k = some v ↔ ∃ h, get t k h = v :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_some_iff

@[simp]
theorem isSome_get?_iff_mem [TransCmp cmp] {a : α} :
    (get? t a).isSome ↔ a ∈ t :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_get?_iff_mem

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → get? t a = none :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_none_of_contains_eq_false

theorem get?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → get? t a = none :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_none

@[grind =] theorem get?_erase [TransCmp cmp] {k a : α} :
    get? (t.erase k) a = if cmp k a = .eq then none else get? t a :=
  t.inductionOn fun _ => DTreeMap.Const.get?_erase

@[simp]
theorem get?_erase_self [TransCmp cmp] {k : α} :
    get? (t.erase k) k = none :=
  t.inductionOn fun _ => DTreeMap.Const.get?_erase_self

theorem get?_eq_get? [LawfulEqCmp cmp] [TransCmp cmp] {a : α} : get? t a = t.get? a :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_get?

theorem get?_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) :
    get? t a = get? t b :=
  t.inductionOn (fun _ hab => DTreeMap.Const.get?_congr hab) hab

end Const

@[grind =] theorem get_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insert k v).get a h₁ =
      if h₂ : cmp k a = .eq then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (mem_of_mem_insert h₁ h₂) :=
  t.inductionOn (fun _ _ => DTreeMap.get_insert) h₁

@[simp]
theorem get_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.insert k v).get k mem_insert_self = v :=
  t.inductionOn fun _ => DTreeMap.get_insert_self

@[simp, grind =]
theorem get_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h') :=
  t.inductionOn (fun _ _ => DTreeMap.get_erase) h'

theorem get?_eq_some_get [TransCmp cmp] [LawfulEqCmp cmp] {a : α} (h') :
    t.get? a = some (t.get a h') :=
  t.inductionOn (fun _ => DTreeMap.get?_eq_some_get) h'

theorem get_eq_get_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {h} :
    t.get a h = (t.get? a).get (mem_iff_isSome_get?.mp h) :=
  t.inductionOn (fun _ _ => DTreeMap.get_eq_get_get?) h

@[grind =] theorem get_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {h} :
    (t.get? a).get h = t.get a (mem_iff_isSome_get?.mpr h) :=
  t.inductionOn (fun _ _ => DTreeMap.get_get?) h

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem get_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (mem_of_mem_insert h₁ h₂) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_insert) h₁

@[simp]
theorem get_insert_self [TransCmp cmp] {k : α} {v : β} :
    get (t.insert k v) k mem_insert_self = v :=
  t.inductionOn fun _ => DTreeMap.Const.get_insert_self

@[simp, grind =]
theorem get_erase [TransCmp cmp] {k a : α} {h'} :
    get (t.erase k) a h' = get t a (mem_of_mem_erase h') :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_erase) h'

theorem get?_eq_some_get [TransCmp cmp] {a : α} (h) :
    get? t a = some (get t a h) :=
  t.inductionOn (fun _ => DTreeMap.Const.get?_eq_some_get) h

theorem get_eq_get_get? [TransCmp cmp] {a : α} {h} :
    get t a h = (get? t a).get (mem_iff_isSome_get?.mp h) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_eq_get_get?) h

@[grind =] theorem get_get? [TransCmp cmp] {a : α} {h} :
    (get? t a).get h = get t a (mem_iff_isSome_get?.mpr h) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_get?) h

theorem get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {h} : get t a h = t.get a h :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_eq_get) h

theorem get_congr [TransCmp cmp] {a b : α} (hab : cmp a b = .eq) {h'} :
    get t a h' = get t b ((mem_congr hab).mp h') :=
  t.inductionOn (fun _ hab _ => DTreeMap.Const.get_congr hab) hab h'

end Const

@[simp, grind =]
theorem get!_empty [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    get! (∅ : ExtDTreeMap α β cmp) a = default :=
  DTreeMap.get!_emptyc

@[grind =] theorem get!_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insert k v).get! a =
      if h : cmp k a = .eq then cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h)) v else t.get! a :=
  t.inductionOn fun _ => DTreeMap.get!_insert

@[simp]
theorem get!_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] {b : β a} :
    (t.insert a b).get! a = b :=
  t.inductionOn fun _ => DTreeMap.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default :=
  t.inductionOn fun _ => DTreeMap.get!_eq_default_of_contains_eq_false

theorem get!_eq_default [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default :=
  t.inductionOn fun _ => DTreeMap.get!_eq_default

@[grind =] theorem get!_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} [Inhabited (β a)] :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  t.inductionOn fun _ => DTreeMap.get!_erase

@[simp]
theorem get!_erase_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} [Inhabited (β k)] :
    (t.erase k).get! k = default :=
  t.inductionOn fun _ => DTreeMap.get!_erase_self

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.contains a = true → t.get? a = some (t.get! a) :=
  t.inductionOn fun _ => DTreeMap.get?_eq_some_get!_of_contains

theorem get?_eq_some_get! [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) :=
  t.inductionOn fun _ => DTreeMap.get?_eq_some_get!

theorem get!_eq_get!_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! :=
  t.inductionOn fun _ => DTreeMap.get!_eq_get!_get?

theorem get_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] {h} :
    t.get a h = t.get! a :=
  t.inductionOn (fun _ _ => DTreeMap.get_eq_get!) h

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp, grind =]
theorem get!_empty [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : ExtDTreeMap α β cmp) a = default :=
  DTreeMap.Const.get!_emptyc

@[grind =] theorem get!_insert [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else get! t a :=
  t.inductionOn fun _ => DTreeMap.Const.get!_insert

@[simp]
theorem get!_insert_self [TransCmp cmp] [Inhabited β] {k : α} {v : β} : get! (t.insert k v) k = v :=
  t.inductionOn fun _ => DTreeMap.Const.get!_insert_self

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = false → get! t a = default :=
  t.inductionOn fun _ => DTreeMap.Const.get!_eq_default_of_contains_eq_false

theorem get!_eq_default [TransCmp cmp] [Inhabited β] {a : α} :
    ¬ a ∈ t → get! t a = default :=
  t.inductionOn fun _ => DTreeMap.Const.get!_eq_default

@[grind =] theorem get!_erase [TransCmp cmp] [Inhabited β] {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else get! t a :=
  t.inductionOn fun _ => DTreeMap.Const.get!_erase

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited β] {k : α} :
    get! (t.erase k) k = default :=
  t.inductionOn fun _ => DTreeMap.Const.get!_erase_self

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited β] {a : α} :
    t.contains a = true → get? t a = some (get! t a) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_some_get!_of_contains

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited β] {a : α} :
    a ∈ t → get? t a = some (get! t a) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_some_get!

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited β] {a : α} :
    get! t a = (get? t a).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_eq_get!_get?

theorem get_eq_get! [TransCmp cmp] [Inhabited β] {a : α} {h} :
    get t a h = get! t a :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_eq_get!) h

theorem get!_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β] {a : α} :
    get! t a = t.get! a :=
  t.inductionOn fun _ => DTreeMap.Const.get!_eq_get!

theorem get!_congr [TransCmp cmp] [Inhabited β] {a b : α} (hab : cmp a b = .eq) :
    get! t a = get! t b :=
  t.inductionOn (fun _ hab => DTreeMap.Const.get!_congr hab) hab

end Const

@[simp, grind =]
theorem getD_empty [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    (∅ : ExtDTreeMap α β cmp).getD a fallback = fallback :=
  DTreeMap.getD_emptyc

@[grind =] theorem getD_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v).getD a fallback =
      if h : cmp k a = .eq then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h)) v
      else t.getD a fallback :=
  t.inductionOn fun _ => DTreeMap.getD_insert

@[simp]
theorem getD_insert_self [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback b : β a} :
    (t.insert a b).getD a fallback = b :=
  t.inductionOn fun _ => DTreeMap.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] {a : α}
    {fallback : β a} : t.contains a = false → t.getD a fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.getD_eq_fallback

@[grind =] theorem getD_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {fallback : β a} :
    (t.erase k).getD a fallback = if cmp k a = .eq then fallback else t.getD a fallback :=
  t.inductionOn fun _ => DTreeMap.getD_erase

@[simp]
theorem getD_erase_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {fallback : β k} :
    (t.erase k).getD k fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.getD_erase_self

theorem get?_eq_some_getD_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    t.contains a = true → t.get? a = some (t.getD a fallback) :=
  t.inductionOn fun _ => DTreeMap.get?_eq_some_getD_of_contains

theorem get?_eq_some_getD [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  t.inductionOn fun _ => DTreeMap.get?_eq_some_getD

theorem getD_eq_getD_get? [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getD_eq_getD_get?

theorem get_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} {h} :
    t.get a h = t.getD a fallback :=
  t.inductionOn (fun _ _ => DTreeMap.get_eq_getD) h

theorem get!_eq_getD_default [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default :=
  t.inductionOn fun _ => DTreeMap.get!_eq_getD_default

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp, grind =]
theorem getD_empty [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : ExtDTreeMap α β cmp) a fallback = fallback :=
  DTreeMap.Const.getD_emptyc

@[grind =] theorem getD_insert [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_insert

@[simp]
theorem getD_insert_self [TransCmp cmp] {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  t.inductionOn fun _ => DTreeMap.Const.getD_insert_self

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_eq_fallback_of_contains_eq_false

theorem getD_eq_fallback [TransCmp cmp] {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_eq_fallback

@[grind =] theorem getD_erase [TransCmp cmp] {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_erase

@[simp]
theorem getD_erase_self [TransCmp cmp] {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_erase_self

theorem get?_eq_some_getD_of_contains [TransCmp cmp] {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_some_getD_of_contains

theorem get?_eq_some_getD [TransCmp cmp] {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_some_getD

theorem getD_eq_getD_get? [TransCmp cmp] {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_eq_getD_get?

theorem get_eq_getD [TransCmp cmp] {a : α} {fallback : β} {h} :
    get t a h = getD t a fallback :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_eq_getD) h

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited β] {a : α} :
    get! t a = getD t a default :=
  t.inductionOn fun _ => DTreeMap.Const.get!_eq_getD_default

theorem getD_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_eq_getD

theorem getD_congr [TransCmp cmp] {a b : α} {fallback : β} (hab : cmp a b = .eq) :
    getD t a fallback = getD t b fallback :=
  t.inductionOn (fun _ hab => DTreeMap.Const.getD_congr hab) hab

end Const

@[simp, grind =]
theorem getKey?_empty [TransCmp cmp] {a : α} : (∅ : ExtDTreeMap α β cmp).getKey? a = none :=
  DTreeMap.getKey?_emptyc

@[grind =] theorem getKey?_insert [TransCmp cmp] {a k : α} {v : β k} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  t.inductionOn fun _ => DTreeMap.getKey?_insert

@[simp]
theorem getKey?_insert_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).getKey? k = some k :=
  t.inductionOn fun _ => DTreeMap.getKey?_insert_self

theorem contains_eq_isSome_getKey? [TransCmp cmp] {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  t.inductionOn fun _ => DTreeMap.contains_eq_isSome_getKey?

@[simp, grind =]
theorem isSome_getKey?_eq_contains [TransCmp cmp] {a : α} :
    (t.getKey? a).isSome = t.contains a :=
  t.inductionOn fun _ => DTreeMap.isSome_getKey?_eq_contains

theorem mem_iff_isSome_getKey? [TransCmp cmp] {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  t.inductionOn fun _ => DTreeMap.mem_iff_isSome_getKey?

@[simp]
theorem isSome_getKey?_iff_mem [TransCmp cmp] {a : α} :
    (t.getKey? a).isSome ↔ a ∈ t :=
  t.inductionOn fun _ => DTreeMap.isSome_getKey?_iff_mem

theorem mem_of_getKey?_eq_some [TransCmp cmp] {k k' : α} :
    t.getKey? k = some k' → k' ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_of_getKey?_eq_some

theorem getKey?_eq_some_iff [TransCmp cmp] {k k' : α} :
    getKey? t k = some k' ↔ ∃ h, getKey t k h = k' :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_some_iff

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] {a : α} :
    t.contains a = false → t.getKey? a = none :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_none_of_contains_eq_false

theorem getKey?_eq_none [TransCmp cmp] {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_none

@[grind =] theorem getKey?_erase [TransCmp cmp] {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  t.inductionOn fun _ => DTreeMap.getKey?_erase

@[simp]
theorem getKey?_erase_self [TransCmp cmp] {k : α} :
    (t.erase k).getKey? k = none :=
  t.inductionOn fun _ => DTreeMap.getKey?_erase_self

theorem compare_getKey?_self [TransCmp cmp] {k : α} :
    (t.getKey? k).all (cmp · k = .eq) :=
  t.inductionOn fun _ => DTreeMap.compare_getKey?_self

theorem getKey?_congr [TransCmp cmp] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey? k = t.getKey? k' :=
  t.inductionOn (fun _ h' => DTreeMap.getKey?_congr h') h'

theorem getKey?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : t.contains k) :
    t.getKey? k = some k :=
  t.inductionOn (fun _ h' => DTreeMap.getKey?_eq_some_of_contains h') h'

theorem getKey?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h' : k ∈ t) :
    t.getKey? k = some k :=
  t.inductionOn (fun _ h' => DTreeMap.getKey?_eq_some h') h'

@[grind =] theorem getKey_insert [TransCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then
        k
      else
        t.getKey a (mem_of_mem_insert h₁ h₂) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_insert) h₁

@[simp]
theorem getKey_insert_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insert k v).getKey k mem_insert_self = k :=
  t.inductionOn fun _ => DTreeMap.getKey_insert_self

@[simp, grind =]
theorem getKey_erase [TransCmp cmp] {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h') :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_erase) h'

theorem getKey?_eq_some_getKey [TransCmp cmp] {a : α} (h') :
    t.getKey? a = some (t.getKey a h') :=
  t.inductionOn (fun _ => DTreeMap.getKey?_eq_some_getKey) h'

theorem getKey_eq_get_getKey? [TransCmp cmp] {a : α} {h} :
    t.getKey a h = (t.getKey? a).get (mem_iff_isSome_getKey?.mp h) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_eq_get_getKey?) h

@[simp, grind =]
theorem get_getKey? [TransCmp cmp] {a : α} {h} :
    (t.getKey? a).get h = t.getKey a (mem_iff_isSome_getKey?.mpr h) :=
  t.inductionOn (fun _ _ => DTreeMap.get_getKey?) h

theorem compare_getKey_self [TransCmp cmp] {k : α} (h' : k ∈ t) :
    cmp (t.getKey k h') k = .eq :=
  t.inductionOn (fun _ h' => DTreeMap.compare_getKey_self h') h'

theorem getKey_congr [TransCmp cmp] {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h').mp h₁) :=
  t.inductionOn (fun _ h' h₁ => DTreeMap.getKey_congr h' h₁) h' h₁

@[simp, grind =]
theorem getKey_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    (h' : k ∈ t) : t.getKey k h' = k :=
  t.inductionOn (fun _ h' => DTreeMap.getKey_eq h') h'

@[simp, grind =]
theorem getKey!_empty [TransCmp cmp] {a : α} [Inhabited α] :
    (∅ : ExtDTreeMap α β cmp).getKey! a = default :=
  DTreeMap.getKey!_emptyc

@[grind =] theorem getKey!_insert [TransCmp cmp] [Inhabited α] {k a : α}
    {v : β k} : (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  t.inductionOn fun _ => DTreeMap.getKey!_insert

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] {a : α}
    {b : β a} : (t.insert a b).getKey! a = a :=
  t.inductionOn fun _ => DTreeMap.getKey!_insert_self

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = false → t.getKey! a = default :=
  t.inductionOn fun _ => DTreeMap.getKey!_eq_default_of_contains_eq_false

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  t.inductionOn fun _ => DTreeMap.getKey!_eq_default

@[grind =] theorem getKey!_erase [TransCmp cmp] [Inhabited α] {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  t.inductionOn fun _ => DTreeMap.getKey!_erase

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] {k : α} :
    (t.erase k).getKey! k = default :=
  t.inductionOn fun _ => DTreeMap.getKey!_erase_self

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_some_getKey!_of_contains

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_some_getKey!

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  t.inductionOn fun _ => DTreeMap.getKey!_eq_get!_getKey?

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] {a : α} {h} :
    t.getKey a h = t.getKey! a :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_eq_getKey!) h

theorem getKey!_congr [TransCmp cmp] [Inhabited α] {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey! k = t.getKey! k' :=
  t.inductionOn (fun _ h' => DTreeMap.getKey!_congr h') h'

theorem getKey!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    (h' : t.contains k) :
    t.getKey! k = k :=
  t.inductionOn (fun _ h' => DTreeMap.getKey!_eq_of_contains h') h'

theorem getKey!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    {k : α} (h' : k ∈ t) :
    t.getKey! k = k :=
  t.inductionOn (fun _ h' => DTreeMap.getKey!_eq_of_mem h') h'

@[simp, grind =]
theorem getKeyD_empty [TransCmp cmp] {a : α} {fallback : α} :
    (∅ : ExtDTreeMap α β cmp).getKeyD a fallback = fallback :=
  DTreeMap.getKeyD_emptyc

@[grind =] theorem getKeyD_insert [TransCmp cmp] {k a fallback : α} {v : β k} :
    (t.insert k v).getKeyD a fallback =
      if cmp k a = .eq then k else t.getKeyD a fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_insert

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] {a fallback : α} {b : β a} :
    (t.insert a b).getKeyD a fallback = a :=
  t.inductionOn fun _ => DTreeMap.getKeyD_insert_self

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_eq_fallback_of_contains_eq_false

theorem getKeyD_eq_fallback [TransCmp cmp] {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_eq_fallback

@[grind =] theorem getKeyD_erase [TransCmp cmp] {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_erase

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_erase_self

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_some_getKeyD_of_contains

theorem getKey?_eq_some_getKeyD [TransCmp cmp] {a fallback : α} :
  a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  t.inductionOn fun _ => DTreeMap.getKey?_eq_some_getKeyD

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_eq_getD_getKey?

theorem getKey_eq_getKeyD [TransCmp cmp] {a fallback : α} {h} :
    t.getKey a h = t.getKeyD a fallback :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_eq_getKeyD) h

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] {a : α} :
    t.getKey! a = t.getKeyD a default :=
  t.inductionOn fun _ => DTreeMap.getKey!_eq_getKeyD_default

theorem getKeyD_congr [TransCmp cmp] {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getKeyD k fallback = t.getKeyD k' fallback :=
  t.inductionOn (fun _ h' => DTreeMap.getKeyD_congr h') h'

theorem getKeyD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α}
    (h' : t.contains k) :
    t.getKeyD k fallback = k :=
  t.inductionOn (fun _ h' => DTreeMap.getKeyD_eq_of_contains h') h'

theorem getKeyD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k fallback : α} (h' : k ∈ t) :
    t.getKeyD k fallback = k :=
  t.inductionOn (fun _ h' => DTreeMap.getKeyD_eq_of_mem h') h'

@[simp]
theorem insertIfNew_ne_empty [TransCmp cmp] {k : α} {v : β k} :
    t.insertIfNew k v ≠ ∅ := by
  cases t with | mk t
  simpa only [← isEmpty_iff, ne_eq, Bool.not_eq_true] using DTreeMap.isEmpty_insertIfNew

@[simp, grind =]
theorem contains_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  t.inductionOn fun _ => DTreeMap.contains_insertIfNew

@[simp, grind =]
theorem mem_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_insertIfNew

theorem contains_insertIfNew_self [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).contains k :=
  t.inductionOn fun _ => DTreeMap.contains_insertIfNew_self

theorem mem_insertIfNew_self [TransCmp cmp] {k : α} {v : β k} :
    k ∈ t.insertIfNew k v :=
  t.inductionOn fun _ => DTreeMap.mem_insertIfNew_self

theorem contains_of_contains_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_insertIfNew

theorem mem_of_mem_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_of_mem_insertIfNew

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] {k a : α} {v : β k} :
    a ∈ (t.insertIfNew k v) → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_of_mem_insertIfNew'

@[grind =] theorem size_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  t.inductionOn fun _ => DTreeMap.size_insertIfNew

theorem size_le_size_insertIfNew [TransCmp cmp] {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  t.inductionOn fun _ => DTreeMap.size_le_size_insertIfNew

theorem size_insertIfNew_le [TransCmp cmp] {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  t.inductionOn fun _ => DTreeMap.size_insertIfNew_le

@[grind =] theorem get?_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).get? a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a :=
  t.inductionOn fun _ => DTreeMap.get?_insertIfNew

@[grind =] theorem get_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h₁ h₂) :=
  t.inductionOn (fun _ _ => DTreeMap.get_insertIfNew) h₁

@[grind =] theorem get!_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v).get! a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a :=
  t.inductionOn fun _ => DTreeMap.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v).getD a fallback =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback :=
  t.inductionOn fun _ => DTreeMap.getD_insertIfNew

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem get?_insertIfNew [TransCmp cmp] {k a : α} {v : β} :
    get? (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else get? t a :=
  t.inductionOn fun _ => DTreeMap.Const.get?_insertIfNew

@[grind =] theorem get_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v) a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then v else get t a (mem_of_mem_insertIfNew' h₁ h₂) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_insertIfNew) h₁

@[grind =] theorem get!_insertIfNew [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    get! (t.insertIfNew k v) a = if cmp k a = .eq ∧ ¬ k ∈ t then v else get! t a :=
  t.inductionOn fun _ => DTreeMap.Const.get!_insertIfNew

@[grind =] theorem getD_insertIfNew [TransCmp cmp] {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_insertIfNew

end Const

@[grind =] theorem getKey?_insertIfNew [TransCmp cmp] {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  t.inductionOn fun _ => DTreeMap.getKey?_insertIfNew

@[grind =] theorem getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_insertIfNew) h₁

@[grind =] theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  t.inductionOn fun _ => DTreeMap.getKey!_insertIfNew

@[grind =] theorem getKeyD_insertIfNew [TransCmp cmp] {k a fallback : α} {v : β k} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_insertIfNew

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).1 = t.get? k :=
  t.inductionOn fun _ => DTreeMap.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).2 = t.insertIfNew k v :=
  t.inductionOn fun _ => congrArg mk DTreeMap.getThenInsertIfNew?_snd

theorem mem_of_get_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} {w} (_ : t.get k w = v) : k ∈ t := w

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  t.inductionOn fun _ => DTreeMap.Const.getThenInsertIfNew?_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  t.inductionOn fun _ => congrArg mk DTreeMap.Const.getThenInsertIfNew?_snd

end Const

@[simp, grind =]
theorem length_keys [TransCmp cmp] :
    t.keys.length = t.size :=
  t.inductionOn fun _ => DTreeMap.length_keys

@[simp, grind =]
theorem isEmpty_keys [TransCmp cmp] :
    t.keys.isEmpty = t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.isEmpty_keys

@[simp]
theorem keys_eq_nil_iff [TransCmp cmp] :
    t.keys = [] ↔ t = ∅ := by
  simp only [← List.isEmpty_iff, isEmpty_keys, isEmpty_iff]

@[simp, grind =]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  t.inductionOn fun _ => DTreeMap.contains_keys

@[simp, grind =]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_keys

theorem mem_of_mem_keys [TransCmp cmp] {k : α} (h : k ∈ t.keys) : k ∈ t :=
  t.inductionOn (fun _ => DTreeMap.mem_of_mem_keys) h

theorem distinct_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  t.inductionOn fun _ => DTreeMap.distinct_keys

theorem nodup_keys [TransCmp cmp] :
    t.keys.Nodup :=
  t.distinct_keys.imp Std.ReflCmp.ne_of_cmp_ne_eq

theorem ordered_keys [TransCmp cmp] :
    t.keys.Pairwise (fun a b => cmp a b = .lt) :=
  t.inductionOn fun _ => DTreeMap.ordered_keys

@[simp, grind _=_]
theorem map_fst_toList_eq_keys [TransCmp cmp] :
    t.toList.map Sigma.fst = t.keys :=
  t.inductionOn fun _ => DTreeMap.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList [TransCmp cmp] :
    t.toList.length = t.size :=
  t.inductionOn fun _ => DTreeMap.length_toList

@[simp, grind =]
theorem isEmpty_toList [TransCmp cmp] :
    t.toList.isEmpty = t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.isEmpty_toList

@[simp]
theorem toList_eq_nil_iff [TransCmp cmp] :
    t.toList = [] ↔ t = ∅ := by
  simp only [← List.isEmpty_iff, isEmpty_toList, isEmpty_iff]

@[simp, grind =]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    ⟨k, v⟩ ∈ t.toList ↔ t.get? k = some v :=
  t.inductionOn fun _ => DTreeMap.mem_toList_iff_get?_eq_some

theorem find?_toList_eq_some_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β k} :
    t.toList.find? (cmp ·.1 k == .eq) = some ⟨k, v⟩ ↔ t.get? k = some v :=
  t.inductionOn fun _ => DTreeMap.find?_toList_eq_some_iff_get?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  t.inductionOn fun _ => DTreeMap.find?_toList_eq_none_iff_contains_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  t.inductionOn fun _ => DTreeMap.find?_toList_eq_none_iff_not_mem

theorem distinct_keys_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  t.inductionOn fun _ => DTreeMap.distinct_keys_toList

theorem ordered_keys_toList [TransCmp cmp] :
    t.toList.Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  t.inductionOn fun _ => DTreeMap.ordered_keys_toList

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp, grind _=_]
theorem map_fst_toList_eq_keys [TransCmp cmp] :
    (toList t).map Prod.fst = t.keys :=
  t.inductionOn fun _ => DTreeMap.Const.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList [TransCmp cmp] :
    (toList t).length = t.size :=
  t.inductionOn fun _ => DTreeMap.Const.length_toList

@[simp, grind =]
theorem isEmpty_toList [TransCmp cmp] :
    (toList t).isEmpty = t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.Const.isEmpty_toList

@[simp]
theorem toList_eq_nil_iff [TransCmp cmp] :
    toList t = [] ↔ t = ∅ := by
  simp only [← List.isEmpty_iff, isEmpty_toList, isEmpty_iff]

@[simp, grind =]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ get? t k = some v :=
  t.inductionOn fun _ => DTreeMap.Const.mem_toList_iff_get?_eq_some

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ get? t k = some v :=
  t.inductionOn fun _ => DTreeMap.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some

theorem get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] {k : α} {v : β} :
    get? t k = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  t.inductionOn fun _ => DTreeMap.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] {k k' : α} {v : β} :
    (toList t).find? (cmp ·.1 k == .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ get? t k = some v :=
  t.inductionOn fun _ => DTreeMap.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  t.inductionOn fun _ => DTreeMap.Const.find?_toList_eq_none_iff_contains_eq_false

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  t.inductionOn fun _ => DTreeMap.Const.find?_toList_eq_none_iff_not_mem

theorem distinct_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  t.inductionOn fun _ => DTreeMap.Const.distinct_keys_toList

theorem ordered_keys_toList [TransCmp cmp] :
    (toList t).Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  t.inductionOn fun _ => DTreeMap.Const.ordered_keys_toList

end Const

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β a → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init :=
  t.inductionOn fun _ => DTreeMap.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList [TransCmp cmp] {f : δ → (a : α) → β a → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init :=
  t.inductionOn fun _ => DTreeMap.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : (a : α) → β a → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init :=
  t.inductionOn fun _ => DTreeMap.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList [TransCmp cmp] {f : (a : α) → β a → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init :=
  t.inductionOn fun _ => DTreeMap.foldr_eq_foldr_toList

@[simp, grind =]
theorem forM_eq_forM [TransCmp cmp] [Monad m] [LawfulMonad m] {f : (a : α) → β a → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : (a : α) × β a → m PUnit} :
    ForM.forM t f = ForM.forM t.toList f :=
  t.inductionOn fun _ => DTreeMap.forM_eq_forM_toList

@[simp, grind =]
theorem forIn_eq_forIn [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init (fun a b => f a.1 a.2 b) := rfl

theorem forIn_eq_forIn_toList [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : (a : α) × β a → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  t.inductionOn fun _ => DTreeMap.forIn_eq_forIn_toList

theorem foldlM_eq_foldlM_keys [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init :=
  t.inductionOn fun _ => DTreeMap.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys [TransCmp cmp] {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init :=
  t.inductionOn fun _ => DTreeMap.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init :=
  t.inductionOn fun _ => DTreeMap.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys [TransCmp cmp] {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init :=
  t.inductionOn fun _ => DTreeMap.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t (fun a => f a.1) = t.keys.forM f :=
  t.inductionOn fun _ => DTreeMap.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init (fun a d => f a.1 d) = ForIn.forIn t.keys init f :=
  t.inductionOn fun _ => DTreeMap.forIn_eq_forIn_keys

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

theorem foldlM_eq_foldlM_toList [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = (Const.toList t).foldlM (fun a b => f a b.1 b.2) init :=
  t.inductionOn fun _ => DTreeMap.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList [TransCmp cmp] {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = (Const.toList t).foldl (fun a b => f a b.1 b.2) init :=
  t.inductionOn fun _ => DTreeMap.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α → β → δ → m δ} {init : δ} :
    t.foldrM f init = (Const.toList t).foldrM (fun a b => f a.1 a.2 b) init :=
  t.inductionOn fun _ => DTreeMap.Const.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList [TransCmp cmp] {f : α → β → δ → δ} {init : δ} :
    t.foldr f init = (Const.toList t).foldr (fun a b => f a.1 a.2 b) init :=
  t.inductionOn fun _ => DTreeMap.Const.foldr_eq_foldr_toList

theorem forM_eq_forMUncurried [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = forMUncurried (fun a => f a.1 a.2) t :=
  rfl

theorem forMUncurried_eq_forM_toList [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    forMUncurried f t = (Const.toList t).forM f :=
  t.inductionOn fun _ => DTreeMap.Const.forMUncurried_eq_forM_toList

theorem forIn_eq_forInUncurried [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = forInUncurried (fun a b => f a.1 a.2 b) init t :=
  rfl

theorem forInUncurried_eq_forIn_toList [TransCmp cmp] [Monad m] [LawfulMonad m]
    {f : α × β → δ → m (ForInStep δ)} {init : δ} :
    forInUncurried f init t = ForIn.forIn (Const.toList t) init f :=
  t.inductionOn fun _ => DTreeMap.Const.forInUncurried_eq_forIn_toList

end Const

end monadic

@[simp, grind =]
theorem insertMany_nil [TransCmp cmp] : t.insertMany [] = t := rfl

@[simp, grind =]
theorem insertMany_list_singleton [TransCmp cmp] {k : α} {v : β k} :
    t.insertMany [⟨k, v⟩] = t.insert k v := rfl

@[grind _=_]
theorem insertMany_cons [TransCmp cmp] {l : List ((a : α) × β a)} {p : (a : α) × β a} :
    t.insertMany (p :: l) = (t.insert p.1 p.2).insertMany l := by
  rcases p with ⟨k, v⟩
  unfold insertMany
  simp only [bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons, Id.run_pure]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insert a.1 a.2) (t.insert k v) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

@[grind _=_]
theorem insertMany_append [TransCmp cmp] {l₁ l₂ : List ((a : α) × β a)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

private theorem insertMany_list_mk [TransCmp cmp]
    {t : DTreeMap α β cmp} {l : List ((a : α) × β a)} :
    (ExtDTreeMap.insertMany (mk t) l : ExtDTreeMap α β cmp) =
      mk (t.insertMany l) := by
  simp only [mk, Quotient.mk]
  induction l generalizing t with
  | nil => rfl
  | cons x l ih =>
    rcases x with ⟨k, v⟩
    simp only [insertMany_cons, insert, mk, Quotient.mk, ih, DTreeMap.insertMany_cons]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Sigma.fst).contains k) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Sigma.fst).contains k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.mem_insertMany_list

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l → (l.map Sigma.fst).contains k = false → k ∈ t := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.mem_of_mem_insertMany_list

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get? k = t.get? k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get? k' = some (cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v) := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.get?_insertMany_list_of_mem k_eq distinct mem

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).get k h' =
    t.get k (mem_of_mem_insertMany_list h' contains) := by
  refine t.inductionOn (fun _ _ => ?_) h'
  simp only [insertMany_list_mk]
  exact DTreeMap.get_insertMany_list_of_contains_eq_false contains

theorem get_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l).get k' h' = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v := by
  refine t.inductionOn (fun _ distinct mem _ => ?_) distinct mem h'
  simp only [insertMany_list_mk]
  exact DTreeMap.get_insertMany_list_of_mem k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get! k = t.get! k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get! k' = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.get!_insertMany_list_of_mem k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.getD_insertMany_list_of_mem k_eq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey? k' = some k := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.getKey?_insertMany_list_of_mem k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h' contains_eq_false) := by
  refine t.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h'
  simp only [insertMany_list_mk]
  exact DTreeMap.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k := by
  refine t.inductionOn (fun _ distinct mem _ => ?_) distinct mem h'
  simp only [insertMany_list_mk]
  exact DTreeMap.getKey_insertMany_list_of_mem k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey! k' = k := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.getKey!_insertMany_list_of_mem k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKeyD k' fallback = k := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.getKeyD_insertMany_list_of_mem k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Sigma.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length := by
  refine t.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertMany_list_mk]
  exact DTreeMap.size_insertMany_list distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List ((a : α) × β a)} :
    t.size ≤ (t.insertMany l).size := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.size_le_size_insertMany_list

grind_pattern size_le_size_insertMany_list => (t.insertMany l).size

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List ((a : α) × β a)} :
    (t.insertMany l).size ≤ t.size + l.length := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (t.insertMany l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] {l : List ((a : α) × β a)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.isEmpty_insertMany_list

@[simp]
theorem insertMany_list_eq_empty_iff [TransCmp cmp] {l : List ((a : α) × β a)} :
    t.insertMany l = ∅ ↔ t = ∅ ∧ l = [] := by
  simp only [← isEmpty_iff, isEmpty_insertMany_list, Bool.and_eq_true, List.isEmpty_iff]

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp, grind =]
theorem insertMany_nil [TransCmp cmp] : insertMany t [] = t := rfl

@[simp, grind =]
theorem insertMany_list_singleton [TransCmp cmp] {k : α} {v : β} :
    insertMany t [⟨k, v⟩] = t.insert k v := rfl

@[grind _=_]
theorem insertMany_cons [TransCmp cmp] {l : List (α × β)} {p : α × β} :
    Const.insertMany t (p :: l) = Const.insertMany (t.insert p.1 p.2) l := by
  rcases p with ⟨k, v⟩
  unfold insertMany
  simp only [bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons, Id.run_pure]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insert a.1 a.2) (t.insert k v) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

@[grind _=_]
theorem insertMany_append [TransCmp cmp] {l₁ l₂ : List (α × β)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

private theorem insertMany_list_mk [TransCmp cmp]
    {t : DTreeMap α β cmp} {l : List (α × β)} :
    (Const.insertMany (mk t) l : ExtDTreeMap α β cmp) =
      mk (DTreeMap.Const.insertMany t l) := by
  simp only [mk]
  induction l generalizing t with
  | nil => rfl
  | cons x l ih =>
    rcases x with ⟨k, v⟩
    simp only [Quotient.mk, insertMany_cons, insert, ih, DTreeMap.Const.insertMany_cons]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    (Const.insertMany t l).contains k = (t.contains k || (l.map Prod.fst).contains k) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.contains_insertMany_list

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    k ∈ Const.insertMany t l ↔ k ∈ t ∨ (l.map Prod.fst).contains k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.mem_insertMany_list

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ( α × β )} {k : α} :
    k ∈ insertMany t l → (l.map Prod.fst).contains k = false → k ∈ t := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.mem_of_mem_insertMany_list

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey? k = t.getKey? k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKey?_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey? k' = some k := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKey?_insertMany_list_of_mem k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany t l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h' contains_eq_false) := by
  refine t.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h'
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKey_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany t l).getKey k' h' = k := by
  refine t.inductionOn (fun _ distinct mem _ => ?_) distinct mem h'
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKey_insertMany_list_of_mem k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey! k = t.getKey! k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKey!_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey! k' = k := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKey!_insertMany_list_of_mem k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKeyD k fallback = t.getKeyD k fallback := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKeyD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKeyD k' fallback = k := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getKeyD_insertMany_list_of_mem k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (insertMany t l).size = t.size + l.length := by
  refine t.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.size_insertMany_list distinct

theorem size_le_size_insertMany_list [TransCmp cmp]
    {l : List (α × β)} :
    t.size ≤ (insertMany t l).size := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.size_le_size_insertMany_list

grind_pattern size_le_size_insertMany_list => (insertMany t l).size

theorem size_insertMany_list_le [TransCmp cmp]
    {l : List (α × β)} :
    (insertMany t l).size ≤ t.size + l.length := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.size_insertMany_list_le

grind_pattern size_insertMany_list_le => (insertMany t l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] {l : List (α × β)} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.isEmpty_insertMany_list

@[simp]
theorem insertMany_list_eq_empty_iff [TransCmp cmp] {l : List (α × β)} :
    insertMany t l = ∅ ↔ t = ∅ ∧ l = [] := by
  simp only [← isEmpty_iff, isEmpty_insertMany_list, Bool.and_eq_true, List.isEmpty_iff]

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany t l) k = get? t k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get?_insertMany_list_of_contains_eq_false contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany t l) k' = some v := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get?_insertMany_list_of_mem k_eq distinct mem

theorem get?_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} :
    get? (insertMany t l) k =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).or (get? t k) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get?_insertMany_list

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany t l) k h' = get t k (mem_of_mem_insertMany_list h' contains_eq_false) := by
  refine t.inductionOn (fun _ contains_eq_false _ => ?_) contains_eq_false h'
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get_insertMany_list_of_contains_eq_false contains_eq_false

theorem get_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    get (insertMany t l) k' h' = v := by
  refine t.inductionOn (fun _ distinct mem _ => ?_) distinct mem h'
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get_insertMany_list_of_mem k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited β] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany t l) k = get! t k := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get!_insertMany_list_of_contains_eq_false contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [Inhabited β]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany t l) k' = v := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.get!_insertMany_list_of_mem k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany t l) k fallback = getD t k fallback := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getD_insertMany_list_of_contains_eq_false contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany t l) k' fallback = v := by
  refine t.inductionOn (fun _ distinct mem => ?_) distinct mem
  simp only [insertMany_list_mk]
  exact DTreeMap.Const.getD_insertMany_list_of_mem k_eq distinct mem

variable {t : ExtDTreeMap α Unit cmp}

@[simp]
theorem insertManyIfNewUnit_nil [TransCmp cmp] : insertManyIfNewUnit t [] = t := rfl

@[simp]
theorem insertManyIfNewUnit_list_singleton [TransCmp cmp] {k : α} :
    insertManyIfNewUnit t [k] = t.insertIfNew k () := rfl

theorem insertManyIfNewUnit_cons [TransCmp cmp] {l : List α} {k : α} :
    insertManyIfNewUnit t (k :: l) = insertManyIfNewUnit (t.insertIfNew k ()) l := by
  unfold insertManyIfNewUnit
  simp only [bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons, Id.run_pure]
  refine Eq.trans ?_ (Eq.symm ?_ : l.foldl (fun b a => b.insertIfNew a ()) (t.insertIfNew k ()) = _)
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm
  exact (List.foldl_hom (f := Subtype.val) fun x y => rfl).symm

private theorem insertManyIfNewUnit_list_mk [TransCmp cmp] {t : DTreeMap α Unit cmp} {l : List α} :
    (Const.insertManyIfNewUnit (mk t) l : ExtDTreeMap α Unit cmp) =
      mk (DTreeMap.Const.insertManyIfNewUnit t l) := by
  simp only [mk]
  induction l generalizing t with
  | nil => rfl
  | cons x l ih =>
    simp only [Quotient.mk, insertManyIfNewUnit_cons, insertIfNew, ih,
      DTreeMap.Const.insertManyIfNewUnit_cons]

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.contains_insertManyIfNewUnit_list

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.mem_insertManyIfNewUnit_list

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t := by
  refine t.inductionOn (fun _ contains_eq_false => ?_) contains_eq_false
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.mem_of_mem_insertManyIfNewUnit_list contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false → getKey? (insertManyIfNewUnit t l) k = none := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey? (insertManyIfNewUnit t l) k' = some k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} :
    k ∈ t → getKey? (insertManyIfNewUnit t l) k = getKey? t k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey?_insertManyIfNewUnit_list_of_mem

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains := by
  refine t.inductionOn (fun _ _ => ?_) h' contains
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey_insertManyIfNewUnit_list_of_mem

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey (insertManyIfNewUnit t l) k' h' = k := by
  refine t.inductionOn (fun _ _ => ?_) h'
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false →
      getKey! (insertManyIfNewUnit t l) k = default := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey! (insertManyIfNewUnit t l) k' = k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k : α} :
    k ∈ t → getKey! (insertManyIfNewUnit t l) k = getKey! t k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKey!_insertManyIfNewUnit_list_of_mem

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k fallback : α} :
    ¬ k ∈ t → l.contains k = false → getKeyD (insertManyIfNewUnit t l) k fallback = fallback := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKeyD (insertManyIfNewUnit t l) k' fallback = k := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem k_eq

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    {l : List α} {k fallback : α} :
    k ∈ t → getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.getKeyD_insertManyIfNewUnit_list_of_mem

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length := by
  refine t.inductionOn (fun _ distinct => ?_) distinct
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.size_insertManyIfNewUnit_list distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp]
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.size_le_size_insertManyIfNewUnit_list

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp]
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.size_insertManyIfNewUnit_list_le

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.isEmpty_insertManyIfNewUnit_list

@[simp]
theorem insertManyIfNewUnit_list_eq_empty_iff [TransCmp cmp] {l : List α} :
    insertManyIfNewUnit t l = ∅ ↔ t = ∅ ∧ l = [] := by
  simp only [← isEmpty_iff, isEmpty_insertManyIfNewUnit_list, Bool.and_eq_true, List.isEmpty_iff]

@[simp]
theorem get?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit t l) k =
      if k ∈ t ∨ l.contains k then some () else none := by
  refine t.inductionOn fun _ => ?_
  simp only [insertManyIfNewUnit_list_mk]
  exact DTreeMap.Const.get?_insertManyIfNewUnit_list

@[simp]
theorem get_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} {k : α} {h'} :
    get (insertManyIfNewUnit t l) k h' = () :=
  rfl

@[simp]
theorem get!_insertManyIfNewUnit_list [TransCmp cmp] {l : List α} {k : α} :
    get! (insertManyIfNewUnit t l) k = () :=
  rfl

@[simp]
theorem getD_insertManyIfNewUnit_list [TransCmp cmp]
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit t l) k fallback = () :=
  rfl

end Const

@[simp, grind =]
theorem ofList_nil : ofList ([] : List ((a : α) × β a)) cmp = ∅ := rfl

@[simp, grind =]
theorem ofList_singleton [TransCmp cmp] {k : α} {v : β k} :
    ofList [⟨k, v⟩] cmp = (∅ : ExtDTreeMap α β cmp).insert k v :=
  rfl

@[grind _=_] theorem ofList_cons [TransCmp cmp] {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) cmp = ((∅ : ExtDTreeMap α β cmp).insert k v).insertMany tl := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DTreeMap.ofList_cons

theorem ofList_eq_insertMany_empty [TransCmp cmp] {l : List ((a : α) × (β a))} :
    ofList l cmp = insertMany (∅ : ExtDTreeMap α β cmp) l := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DTreeMap.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l cmp).contains k = (l.map Sigma.fst).contains k :=
  DTreeMap.contains_ofList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Sigma.fst).contains k :=
  DTreeMap.mem_ofList

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).get? k = none :=
  DTreeMap.get?_ofList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).get? k' = some (cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v) :=
  DTreeMap.get?_ofList_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l cmp).get k' h = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  DTreeMap.get_ofList_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).get! k = default :=
  DTreeMap.get!_ofList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).get! k' = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  DTreeMap.get!_ofList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getD k fallback = fallback :=
  DTreeMap.getD_ofList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).getD k' fallback = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  DTreeMap.getD_ofList_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  DTreeMap.getKey?_ofList_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKey? k' = some k :=
  DTreeMap.getKey?_ofList_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  DTreeMap.getKey_ofList_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [Inhabited α] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  DTreeMap.getKey!_ofList_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKey! k' = k :=
  DTreeMap.getKey!_ofList_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  DTreeMap.getKeyD_ofList_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  DTreeMap.getKeyD_ofList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  DTreeMap.size_ofList distinct

theorem size_ofList_le [TransCmp cmp] {l : List ((a : α) × β a)} :
    (ofList l cmp).size ≤ l.length :=
  DTreeMap.size_ofList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp]
theorem ofList_eq_empty_iff [TransCmp cmp] {l : List ((a : α) × β a)} :
    ofList l cmp = ∅ ↔ l = [] := by
  simpa [← isEmpty_iff, ← List.isEmpty_iff] using DTreeMap.isEmpty_ofList

namespace Const

variable {β : Type v}

@[simp, grind =]
theorem ofList_nil : ofList ([] : List (α × β)) cmp = ∅ := rfl

@[simp, grind =]
theorem ofList_singleton [TransCmp cmp] {k : α} {v : β} :
    ofList [⟨k, v⟩] cmp = (∅ : ExtDTreeMap α β cmp).insert k v :=
  rfl

@[grind _=_] theorem ofList_cons [TransCmp cmp] {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : ExtDTreeMap α β cmp).insert k v) tl := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DTreeMap.Const.ofList_cons

theorem ofList_eq_insertMany_empty [TransCmp cmp] {l : List (α × β)} :
    ofList l cmp = insertMany (∅ : ExtDTreeMap α β cmp) l := by
  conv => rhs; apply insertMany_list_mk
  exact congrArg mk DTreeMap.Const.ofList_eq_insertMany_empty

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  DTreeMap.Const.contains_ofList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Prod.fst).contains k :=
  DTreeMap.Const.mem_ofList

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l cmp) k = none :=
  DTreeMap.Const.get?_ofList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l cmp) k' = some v :=
  DTreeMap.Const.get?_ofList_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l cmp) k' h = v :=
  DTreeMap.Const.get_ofList_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l cmp) k = default :=
  DTreeMap.Const.get!_ofList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l cmp) k' = v :=
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

@[simp]
theorem ofList_eq_empty_iff [TransCmp cmp] {l : List (α × β)} :
    ofList l cmp = ∅ ↔ l = [] := by
  simpa only [← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe] using DTreeMap.Const.isEmpty_ofList

@[simp]
theorem unitOfList_nil : unitOfList ([] : List α) cmp = (∅ : ExtDTreeMap α Unit cmp) := rfl

@[simp]
theorem unitOfList_singleton [TransCmp cmp] {k : α} :
    unitOfList [k] cmp = (∅ : ExtDTreeMap α Unit cmp).insertIfNew k () :=
  rfl

theorem unitOfList_cons [TransCmp cmp] {hd : α} {tl : List α} :
    unitOfList (hd :: tl) cmp =
      insertManyIfNewUnit ((∅ : ExtDTreeMap α Unit cmp).insertIfNew hd ()) tl := by
  conv => rhs; apply insertManyIfNewUnit_list_mk
  exact congrArg mk DTreeMap.Const.unitOfList_cons

@[simp]
theorem contains_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp).contains k = l.contains k :=
  DTreeMap.Const.contains_unitOfList

@[simp]
theorem mem_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ unitOfList l cmp ↔ l.contains k :=
  DTreeMap.Const.mem_unitOfList

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
theorem unitOfList_eq_empty_iff [TransCmp cmp] {l : List α} :
    unitOfList l cmp = ∅ ↔ l = [] := by
  simpa only [← isEmpty_iff, ← List.isEmpty_iff, Bool.coe_iff_coe] using DTreeMap.Const.isEmpty_unitOfList

@[simp]
theorem get?_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    get? (unitOfList l cmp) k = if l.contains k then some () else none :=
  DTreeMap.Const.get?_unitOfList

@[simp]
theorem get_unitOfList [TransCmp cmp] {l : List α} {k : α} {h} :
    get (unitOfList l cmp) k h = () :=
  rfl

@[simp]
theorem get!_unitOfList [TransCmp cmp] {l : List α} {k : α} :
    get! (unitOfList l cmp) k = () :=
  rfl

@[simp]
theorem getD_unitOfList [TransCmp cmp] {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l cmp) k fallback = () :=
  rfl

end Const

section Union

variable {t₁ t₂ : ExtDTreeMap α β cmp}

@[simp]
theorem union_eq [TransCmp cmp] : t₁.union t₂ = t₁ ∪ t₂ := by
  simp only [Union.union]

private theorem union_mk [TransCmp cmp]
    {t₁ t₂ : DTreeMap α β cmp} :
    (ExtDTreeMap.union (mk t₁) (mk t₂) : ExtDTreeMap α β cmp) = mk (t₁ ∪ t₂) := by congr

/- contains -/
@[simp]
theorem contains_union [TransCmp cmp]
    {k : α} :
    (t₁ ∪ t₂).contains k = (t₁.contains k || t₂.contains k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.contains_union

/- mem -/
theorem mem_union_of_left [TransCmp cmp] {k : α} :
    k ∈ t₁ → k ∈ t₁ ∪ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_union_of_left

theorem mem_union_of_right [TransCmp cmp] {k : α} :
    k ∈ t₂ → k ∈ t₁ ∪ t₂ :=
   t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_union_of_right

@[simp]
theorem mem_union_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ ↔ k ∈ t₁ ∨ k ∈ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_union_iff

theorem mem_of_mem_union_of_not_mem_right [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₂ → k ∈ t₁ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_of_mem_union_of_not_mem_right

theorem mem_of_mem_union_of_not_mem_left [TransCmp cmp] {k : α} :
    k ∈ t₁ ∪ t₂ → ¬k ∈ t₁ → k ∈ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_of_mem_union_of_not_mem_left

theorem union_insert_right_eq_insert_union [TransCmp cmp] {p : (a : α) × β a} :
    (t₁ ∪ (t₂.insert p.fst p.snd)) = ((t₁ ∪ t₂).insert p.fst p.snd) :=
  t₁.inductionOn₂ t₂ fun _ _ => sound DTreeMap.union_insert_right_equiv_insert_union

/- get? -/
theorem get?_union [TransCmp cmp] [LawfulEqCmp cmp] {k : α} :
    (t₁ ∪ t₂).get? k = (t₂.get? k).or (t₁.get? k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.get?_union

theorem get?_union_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get? k = t₂.get? k := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply @DTreeMap.get?_union_of_not_mem_left
      exact not_mem

theorem get?_union_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).get? k = t₁.get? k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_union_of_not_mem_right h

/- get -/
theorem get_union_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).get k (mem_union_of_right mem) = t₂.get k mem := by
  revert mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get_union_of_mem_right h

theorem get_union_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).get k h' = t₂.get k (mem_of_mem_union_of_not_mem_left h' not_mem) := by
  revert not_mem h'
  exact t₁.inductionOn₂ t₂ fun _ _ not_mem _ => DTreeMap.get_union_of_not_mem_left not_mem

/- getD -/
theorem getD_union [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {fallback : β k} :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k (t₁.getD k fallback) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getD_union

theorem getD_union_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getD k fallback = t₂.getD k fallback := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ not_mem => DTreeMap.getD_union_of_not_mem_left not_mem

theorem getD_union_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂).getD k fallback = t₁.getD k fallback := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ not_mem => DTreeMap.getD_union_of_not_mem_right not_mem

/- get! -/
theorem get!_union [TransCmp cmp] [LawfulEqCmp cmp] {k : α} [Inhabited (β k)] :
    (t₁ ∪ t₂).get! k = t₂.getD k (t₁.get! k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.get!_union

theorem get!_union_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).get! k = t₂.get! k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_union_of_not_mem_left h

theorem get!_union_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (not_mem : ¬k ∈ t₂)  :
    (t₁ ∪ t₂).get! k = t₁.get! k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_union_of_not_mem_right h

/- getKey? -/
theorem getKey?_union [TransCmp cmp] {k : α} :
    (t₁ ∪ t₂).getKey? k = (t₂.getKey? k).or (t₁.getKey? k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey?_union

theorem getKey?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKey? k = t₂.getKey? k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_union_of_not_mem_left h

/- getKey -/
theorem getKey_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂).getKey k (mem_union_of_right mem) = t₂.getKey k mem := by
  revert mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey_union_of_mem_right h

theorem getKey_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    (t₁ ∪ t₂).getKey k h' = t₂.getKey k (mem_of_mem_union_of_not_mem_left h' not_mem) := by
  revert not_mem h'
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey_union_of_not_mem_left h

theorem getKey_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    (t₁ ∪ t₂).getKey k h' = t₁.getKey k (mem_of_mem_union_of_not_mem_right h' not_mem) := by
  revert not_mem h'
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey_union_of_not_mem_right h

/- getKeyD -/
theorem getKeyD_union [TransCmp cmp] {k fallback : α} :
    (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k (t₁.getKeyD k fallback) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKeyD_union

theorem getKeyD_union_of_not_mem_left [TransCmp cmp]
    {k fallback : α} (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKeyD k fallback = t₂.getKeyD k fallback := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_union_of_not_mem_left h

theorem getKeyD_union_of_not_mem_right [TransCmp cmp]
    {k fallback : α} (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKeyD k fallback = t₁.getKeyD k fallback := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_union_of_not_mem_right h

/- getKey! -/
theorem getKey!_union [TransCmp cmp] [Inhabited α] {k : α} : (t₁ ∪ t₂).getKey! k = t₂.getKeyD k (t₁.getKey! k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey!_union

theorem getKey!_union_of_not_mem_left [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₁) :
    (t₁ ∪ t₂).getKey! k = t₂.getKey! k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_union_of_not_mem_left h

theorem getKey!_union_of_not_mem_right [Inhabited α]
    [TransCmp cmp] {k : α}
    (not_mem : ¬k ∈ t₂) :
    (t₁ ∪ t₂).getKey! k = t₁.getKey! k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey!_union_of_not_mem_right

/- size -/
theorem size_union_of_not_mem [TransCmp cmp] :
    (∀ (a : α), a ∈ t₁ → ¬a ∈ t₂) →
    (t₁ ∪ t₂).size = t₁.size + t₂.size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_union_of_not_mem

theorem size_left_le_size_union [TransCmp cmp] : t₁.size ≤ (t₁ ∪ t₂).size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_left_le_size_union

theorem size_right_le_size_union [TransCmp cmp] :
    t₂.size ≤ (t₁ ∪ t₂).size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_right_le_size_union

theorem size_union_le_size_add_size [TransCmp cmp] :
    (t₁ ∪ t₂).size ≤ t₁.size + t₂.size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_union_le_size_add_size

/- isEmpty -/
@[simp]
theorem isEmpty_union [TransCmp cmp] :
    (t₁ ∪ t₂).isEmpty = (t₁.isEmpty && t₂.isEmpty) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.isEmpty_union

end Union

namespace Const

variable {β : Type v} {t₁ t₂ : ExtDTreeMap α (fun _ => β) cmp}

/- get? -/
theorem get?_union [TransCmp cmp] {k : α} :
    Const.get? (t₁.union t₂) k = (Const.get? t₂ k).or (Const.get? t₁ k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.get?_union

theorem get?_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) :
    Const.get? (t₁.union t₂) k = Const.get? t₂ k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_union_of_not_mem_left h

theorem get?_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) :
    Const.get? (t₁.union t₂) k = Const.get? t₁ k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_union_of_not_mem_right h

/- get -/
theorem get_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : t₂.contains k) :
    Const.get (t₁.union t₂) k (mem_union_of_right mem) = Const.get t₂ k mem := by
  revert mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get_union_of_mem_right h

theorem get_union_of_not_mem_left [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₁) {h'} :
    Const.get (t₁.union t₂) k h' = Const.get t₂ k (mem_of_mem_union_of_not_mem_left h' not_mem) := by
  revert not_mem h'
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get_union_of_not_mem_left h

theorem get_union_of_not_mem_right [TransCmp cmp]
    {k : α} (not_mem : ¬k ∈ t₂) {h'} :
    Const.get (t₁.union t₂) k h' = Const.get t₁ k (mem_of_mem_union_of_not_mem_right h' not_mem) := by
  revert not_mem h'
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get_union_of_not_mem_right h

/- getD -/
theorem getD_union [TransCmp cmp] {k : α} {fallback : β} :
    Const.getD (t₁.union t₂) k fallback = Const.getD t₂ k (Const.getD t₁ k fallback) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.getD_union

theorem getD_union_of_not_mem_left [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : ¬k ∈ t₁) :
    Const.getD (t₁.union t₂) k fallback = Const.getD t₂ k fallback := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_union_of_not_mem_left h

theorem getD_union_of_not_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (not_mem : ¬k ∈ t₂) :
    Const.getD (t₁.union t₂) k fallback = Const.getD t₁ k fallback := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_union_of_not_mem_right h

/- get! -/
theorem get!_union [TransCmp cmp] [Inhabited β] {k : α} :
    Const.get! (t₁.union t₂) k = Const.getD t₂ k (Const.get! t₁ k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.get!_union

theorem get!_union_of_not_mem_left [TransCmp cmp] [Inhabited β]
    {k : α} (not_mem : ¬k ∈ t₁) :
    Const.get! (t₁.union t₂) k = Const.get! t₂ k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_union_of_not_mem_left h

theorem get!_union_of_not_mem_right [TransCmp cmp] [Inhabited β]
    {k : α} (not_mem : ¬k ∈ t₂) :
    Const.get! (t₁.union t₂) k = Const.get! t₁ k := by
  revert not_mem
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_union_of_not_mem_right h

end Const

section Inter

variable {t₁ t₂ : ExtDTreeMap α β cmp}

@[simp]
theorem inter_eq [TransCmp cmp] : t₁.inter t₂ = t₁ ∩ t₂ := by
  simp only [Inter.inter]

/- contains -/
@[simp]
theorem contains_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).contains k = (t₁.contains k && t₂.contains k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.contains_inter

/- mem -/
@[simp]
theorem mem_inter_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ ∩ t₂ ↔ k ∈ t₁ ∧ k ∈ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_inter_iff

theorem not_mem_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    ¬k ∈ t₁ ∩ t₂ := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.not_mem_inter_of_not_mem_left h

theorem not_mem_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    ¬k ∈ t₁ ∩ t₂ := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.not_mem_inter_of_not_mem_right h

/- get? -/
theorem get?_inter [TransCmp cmp] [LawfulEqCmp cmp] {k : α} :
    (t₁ ∩ t₂).get? k =
    if k ∈ t₂ then t₁.get? k else none :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.get?_inter

theorem get?_inter_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h : k ∈ t₂) :
    (t₁ ∩ t₂).get? k = t₁.get? k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_inter_of_mem_right h

theorem get?_inter_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    (t₁ ∩ t₂).get? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_inter_of_not_mem_left h

theorem get?_inter_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    (t₁ ∩ t₂).get? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_inter_of_not_mem_right h

/- get -/
@[simp]
theorem get_inter [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).get k h_mem =
    t₁.get k (mem_inter_iff.1 h_mem).1 := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply DTreeMap.get_inter

/- getD -/
theorem getD_inter [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} :
    (t₁ ∩ t₂).getD k fallback =
    if k ∈ t₂ then t₁.getD k fallback else fallback :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getD_inter

theorem getD_inter_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (h : k ∈ t₂) :
    (t₁ ∩ t₂).getD k fallback = t₁.getD k fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getD_inter_of_mem_right h

theorem getD_inter_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (h : ¬k ∈ t₂) :
    (t₁ ∩ t₂).getD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getD_inter_of_not_mem_right h

theorem getD_inter_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (h : ¬k ∈ t₁) :
    (t₁ ∩ t₂).getD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getD_inter_of_not_mem_left h

/- get! -/
theorem get!_inter [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] :
    (t₁ ∩ t₂).get! k =
    if k ∈ t₂ then t₁.get! k else default :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.get!_inter

theorem get!_inter_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (h : k ∈ t₂) :
    (t₁ ∩ t₂).get! k = t₁.get! k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_inter_of_mem_right h

theorem get!_inter_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (h : ¬k ∈ t₂) :
    (t₁ ∩ t₂).get! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_inter_of_not_mem_right h

theorem get!_inter_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (h : ¬k ∈ t₁) :
    (t₁ ∩ t₂).get! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_inter_of_not_mem_left h

/- getKey? -/
theorem getKey?_inter [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).getKey? k =
    if k ∈ t₂ then t₁.getKey? k else none :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey?_inter

theorem getKey?_inter_of_mem_right [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    (t₁ ∩ t₂).getKey? k = t₁.getKey? k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_inter_of_mem_right h

theorem getKey?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    (t₁ ∩ t₂).getKey? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_inter_of_not_mem_right h

theorem getKey?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    (t₁ ∩ t₂).getKey? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_inter_of_not_mem_left h

/- getKey -/
@[simp]
theorem getKey_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    (t₁ ∩ t₂).getKey k h_mem =
    t₁.getKey k (mem_inter_iff.1 h_mem).1 := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply DTreeMap.getKey_inter

/- getKeyD -/
theorem getKeyD_inter [TransCmp cmp] {k fallback : α} :
    (t₁ ∩ t₂).getKeyD k fallback =
    if k ∈ t₂ then t₁.getKeyD k fallback else fallback :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKeyD_inter

theorem getKeyD_inter_of_mem_right [TransCmp cmp] {k fallback : α} (h : k ∈ t₂) :
    (t₁ ∩ t₂).getKeyD k fallback = t₁.getKeyD k fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_inter_of_mem_right h

theorem getKeyD_inter_of_not_mem_right [TransCmp cmp] {k fallback : α} (h : ¬k ∈ t₂) :
    (t₁ ∩ t₂).getKeyD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_inter_of_not_mem_right h

theorem getKeyD_inter_of_not_mem_left [TransCmp cmp] {k fallback : α} (h : ¬k ∈ t₁) :
    (t₁ ∩ t₂).getKeyD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_inter_of_not_mem_left h

/- getKey! -/
theorem getKey!_inter [Inhabited α] [TransCmp cmp] {k : α} :
    (t₁ ∩ t₂).getKey! k =
    if k ∈ t₂ then t₁.getKey! k else default :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey!_inter

theorem getKey!_inter_of_mem_right [Inhabited α] [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    (t₁ ∩ t₂).getKey! k = t₁.getKey! k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_inter_of_mem_right h

theorem getKey!_inter_of_not_mem_right [Inhabited α] [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    (t₁ ∩ t₂).getKey! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_inter_of_not_mem_right h

theorem getKey!_inter_of_not_mem_left [Inhabited α] [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    (t₁ ∩ t₂).getKey! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_inter_of_not_mem_left h

/- size -/
theorem size_inter_le_size_left [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₁.size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_inter_le_size_left

theorem size_inter_le_size_right [TransCmp cmp] :
    (t₁ ∩ t₂).size ≤ t₂.size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_inter_le_size_right

theorem size_inter_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∈ t₂) :
    (t₁ ∩ t₂).size = t₁.size := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.size_inter_eq_size_left h

theorem size_inter_eq_size_right [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₂ → a ∈ t₁) :
    (t₁ ∩ t₂).size = t₂.size := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.size_inter_eq_size_right h

theorem size_add_size_eq_size_union_add_size_inter [TransCmp cmp] :
    t₁.size + t₂.size = (t₁ ∪ t₂).size + (t₁ ∩ t₂).size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_add_size_eq_size_union_add_size_inter

/- isEmpty -/
@[simp]
theorem isEmpty_inter_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.isEmpty_inter_left h

@[simp]
theorem isEmpty_inter_right [TransCmp cmp] (h : t₂.isEmpty) :
    (t₁ ∩ t₂).isEmpty = true := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.isEmpty_inter_right h

theorem isEmpty_inter_iff [TransCmp cmp] :
    (t₁ ∩ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → ¬k ∈ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.isEmpty_inter_iff

end Inter

namespace Const

variable {β : Type v} {t₁ t₂ : ExtDTreeMap α (fun _ => β) cmp}

/- get? -/
theorem get?_inter [TransCmp cmp] {k : α} :
    Const.get? (t₁ ∩ t₂) k =
    if k ∈ t₂ then Const.get? t₁ k else none :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.get?_inter

theorem get?_inter_of_mem_right [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    Const.get? (t₁ ∩ t₂) k = Const.get? t₁ k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_inter_of_mem_right h

theorem get?_inter_of_not_mem_left [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    Const.get? (t₁ ∩ t₂) k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_inter_of_not_mem_left h

theorem get?_inter_of_not_mem_right [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    Const.get? (t₁ ∩ t₂) k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_inter_of_not_mem_right h

/- get -/
@[simp]
theorem get_inter [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ ∩ t₂} :
    Const.get (t₁ ∩ t₂) k h_mem =
    Const.get t₁ k (mem_inter_iff.1 h_mem).1 := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply DTreeMap.Const.get_inter

/- getD -/
theorem getD_inter [TransCmp cmp]
    {k : α} {fallback : β} :
    Const.getD (t₁ ∩ t₂) k fallback =
    if k ∈ t₂ then Const.getD t₁ k fallback else fallback :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.getD_inter

theorem getD_inter_of_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (h : k ∈ t₂) :
    Const.getD (t₁ ∩ t₂) k fallback = Const.getD t₁ k fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_inter_of_mem_right h

theorem getD_inter_of_not_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (h : ¬k ∈ t₂) :
    Const.getD (t₁ ∩ t₂) k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_inter_of_not_mem_right h

theorem getD_inter_of_not_mem_left [TransCmp cmp]
    {k : α} {fallback : β} (h : ¬k ∈ t₁) :
    Const.getD (t₁ ∩ t₂) k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_inter_of_not_mem_left h

/- get! -/
theorem get!_inter [TransCmp cmp] [Inhabited β]
    {k : α} :
    Const.get! (t₁ ∩ t₂) k =
    if k ∈ t₂ then Const.get! t₁ k else default :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.get!_inter

theorem get!_inter_of_mem_right [TransCmp cmp] [Inhabited β]
    {k : α} (h : k ∈ t₂) :
    Const.get! (t₁ ∩ t₂) k = Const.get! t₁ k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_inter_of_mem_right h

theorem get!_inter_of_not_mem_right [TransCmp cmp] [Inhabited β]
    {k : α} (h : ¬k ∈ t₂) :
    Const.get! (t₁ ∩ t₂) k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_inter_of_not_mem_right h

theorem get!_inter_of_not_mem_left [TransCmp cmp] [Inhabited β]
    {k : α} (h : ¬k ∈ t₁) :
    Const.get! (t₁ ∩ t₂) k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_inter_of_not_mem_left h

end Const

section Diff

variable {t₁ t₂ : ExtDTreeMap α β cmp}

@[simp]
theorem diff_eq [TransCmp cmp] : t₁.diff t₂ = t₁ \ t₂ := by
  simp only [SDiff.sdiff]

/- contains -/
@[simp]
theorem contains_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).contains k = (t₁.contains k && !t₂.contains k) :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.contains_diff

/- mem -/
@[simp]
theorem mem_diff_iff [TransCmp cmp] {k : α} :
    k ∈ t₁ \ t₂ ↔ k ∈ t₁ ∧ k ∉ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.mem_diff_iff

theorem not_mem_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    ¬k ∈ t₁ \ t₂ := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.not_mem_diff_of_not_mem_left h

theorem not_mem_diff_of_mem_right [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    ¬k ∈ t₁ \ t₂ := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.not_mem_diff_of_mem_right h

/- get? -/
theorem get?_diff [TransCmp cmp] [LawfulEqCmp cmp] {k : α} :
    (t₁ \ t₂).get? k =
    if k ∈ t₂ then none else t₁.get? k :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.get?_diff

theorem get?_diff_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    (t₁ \ t₂).get? k = t₁.get? k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_diff_of_not_mem_right h

theorem get?_diff_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    (t₁ \ t₂).get? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_diff_of_not_mem_left h

theorem get?_diff_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} (h : k ∈ t₂) :
    (t₁ \ t₂).get? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get?_diff_of_mem_right h

/- get -/
theorem get_diff [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).get k h_mem =
    t₁.get k (mem_diff_iff.1 h_mem).1 := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply DTreeMap.get_diff

/- getD -/
theorem getD_diff [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} :
    (t₁ \ t₂).getD k fallback =
    if k ∈ t₂ then fallback else t₁.getD k fallback :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getD_diff

theorem getD_diff_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (h : ¬k ∈ t₂) :
    (t₁ \ t₂).getD k fallback = t₁.getD k fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getD_diff_of_not_mem_right h

theorem getD_diff_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (h : k ∈ t₂) :
    (t₁ \ t₂).getD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getD_diff_of_mem_right h

theorem getD_diff_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} {fallback : β k} (h : ¬k ∈ t₁) :
    (t₁ \ t₂).getD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getD_diff_of_not_mem_left h

/- get! -/
theorem get!_diff [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] :
    (t₁ \ t₂).get! k =
    if k ∈ t₂ then default else t₁.get! k :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.get!_diff

theorem get!_diff_of_not_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (h : ¬k ∈ t₂) :
    (t₁ \ t₂).get! k = t₁.get! k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_diff_of_not_mem_right h

theorem get!_diff_of_mem_right [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (h : k ∈ t₂) :
    (t₁ \ t₂).get! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_diff_of_mem_right h

theorem get!_diff_of_not_mem_left [TransCmp cmp] [LawfulEqCmp cmp]
    {k : α} [Inhabited (β k)] (h : ¬k ∈ t₁) :
    (t₁ \ t₂).get! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.get!_diff_of_not_mem_left h

/- getKey? -/
theorem getKey?_diff [TransCmp cmp] {k : α} :
    (t₁ \ t₂).getKey? k =
    if k ∈ t₂ then none else t₁.getKey? k :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey?_diff

theorem getKey?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    (t₁ \ t₂).getKey? k = t₁.getKey? k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_diff_of_not_mem_right h

theorem getKey?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    (t₁ \ t₂).getKey? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_diff_of_not_mem_left h

theorem getKey?_diff_of_mem_right [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    (t₁ \ t₂).getKey? k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey?_diff_of_mem_right h

/- getKey -/
theorem getKey_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    (t₁ \ t₂).getKey k h_mem =
    t₁.getKey k (mem_diff_iff.1 h_mem).1 := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply DTreeMap.getKey_diff

/- getKeyD -/
theorem getKeyD_diff [TransCmp cmp] {k fallback : α} :
    (t₁ \ t₂).getKeyD k fallback =
    if k ∈ t₂ then fallback else t₁.getKeyD k fallback :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKeyD_diff

theorem getKeyD_diff_of_not_mem_right [TransCmp cmp] {k fallback : α} (h : ¬k ∈ t₂) :
    (t₁ \ t₂).getKeyD k fallback = t₁.getKeyD k fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_diff_of_not_mem_right h

theorem getKeyD_diff_of_mem_right [TransCmp cmp] {k fallback : α} (h : k ∈ t₂) :
    (t₁ \ t₂).getKeyD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_diff_of_mem_right h

theorem getKeyD_diff_of_not_mem_left [TransCmp cmp] {k fallback : α} (h : ¬k ∈ t₁) :
    (t₁ \ t₂).getKeyD k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKeyD_diff_of_not_mem_left h

/- getKey! -/
theorem getKey!_diff [Inhabited α] [TransCmp cmp] {k : α} :
    (t₁ \ t₂).getKey! k =
    if k ∈ t₂ then default else t₁.getKey! k :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.getKey!_diff

theorem getKey!_diff_of_not_mem_right [Inhabited α] [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    (t₁ \ t₂).getKey! k = t₁.getKey! k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_diff_of_not_mem_right h

theorem getKey!_diff_of_mem_right [Inhabited α] [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    (t₁ \ t₂).getKey! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_diff_of_mem_right h

theorem getKey!_diff_of_not_mem_left [Inhabited α] [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    (t₁ \ t₂).getKey! k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.getKey!_diff_of_not_mem_left h

/- size -/
theorem size_diff_le_size_left [TransCmp cmp] :
    (t₁ \ t₂).size ≤ t₁.size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_diff_le_size_left

theorem size_diff_eq_size_left [TransCmp cmp]
    (h : ∀ (a : α), a ∈ t₁ → a ∉ t₂) :
    (t₁ \ t₂).size = t₁.size := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.size_diff_eq_size_left h

theorem size_diff_add_size_inter_eq_size_left [TransCmp cmp] :
    (t₁ \ t₂).size + (t₁ ∩ t₂).size = t₁.size :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.size_diff_add_size_inter_eq_size_left

/- isEmpty -/
@[simp]
theorem isEmpty_diff_left [TransCmp cmp] (h : t₁.isEmpty) :
    (t₁ \ t₂).isEmpty = true := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.isEmpty_diff_left h

theorem isEmpty_diff_iff [TransCmp cmp] :
    (t₁ \ t₂).isEmpty ↔ ∀ k, k ∈ t₁ → k ∈ t₂ :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.isEmpty_diff_iff

end Diff

namespace Const

variable {β : Type v} {t₁ t₂ : ExtDTreeMap α (fun _ => β) cmp}

/- get? -/
theorem get?_diff [TransCmp cmp] {k : α} :
    Const.get? (t₁ \ t₂) k =
    if k ∈ t₂ then none else Const.get? t₁ k :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.get?_diff

theorem get?_diff_of_not_mem_right [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₂) :
    Const.get? (t₁ \ t₂) k = Const.get? t₁ k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_diff_of_not_mem_right h

theorem get?_diff_of_not_mem_left [TransCmp cmp]
    {k : α} (h : ¬k ∈ t₁) :
    Const.get? (t₁ \ t₂) k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_diff_of_not_mem_left h

theorem get?_diff_of_mem_right [TransCmp cmp]
    {k : α} (h : k ∈ t₂) :
    Const.get? (t₁ \ t₂) k = none := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get?_diff_of_mem_right h

/- get -/
theorem get_diff [TransCmp cmp]
    {k : α} {h_mem : k ∈ t₁ \ t₂} :
    Const.get (t₁ \ t₂) k h_mem =
    Const.get t₁ k (mem_diff_iff.1 h_mem).1 := by
  induction t₁ with
  | mk a =>
    induction t₂ with
    | mk b =>
      apply DTreeMap.Const.get_diff

/- getD -/
theorem getD_diff [TransCmp cmp]
    {k : α} {fallback : β} :
    Const.getD (t₁ \ t₂) k fallback =
    if k ∈ t₂ then fallback else Const.getD t₁ k fallback :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.getD_diff

theorem getD_diff_of_not_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (h : ¬k ∈ t₂) :
    Const.getD (t₁ \ t₂) k fallback = Const.getD t₁ k fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_diff_of_not_mem_right h

theorem getD_diff_of_mem_right [TransCmp cmp]
    {k : α} {fallback : β} (h : k ∈ t₂) :
    Const.getD (t₁ \ t₂) k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_diff_of_mem_right h

theorem getD_diff_of_not_mem_left [TransCmp cmp]
    {k : α} {fallback : β} (h : ¬k ∈ t₁) :
    Const.getD (t₁ \ t₂) k fallback = fallback := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.getD_diff_of_not_mem_left h

/- get! -/
theorem get!_diff [TransCmp cmp] [Inhabited β]
    {k : α} :
    Const.get! (t₁ \ t₂) k =
    if k ∈ t₂ then default else Const.get! t₁ k :=
  t₁.inductionOn₂ t₂ fun _ _ => DTreeMap.Const.get!_diff

theorem get!_diff_of_not_mem_right [TransCmp cmp] [Inhabited β]
    {k : α} (h : ¬k ∈ t₂) :
    Const.get! (t₁ \ t₂) k = Const.get! t₁ k := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_diff_of_not_mem_right h

theorem get!_diff_of_mem_right [TransCmp cmp] [Inhabited β]
    {k : α} (h : k ∈ t₂) :
    Const.get! (t₁ \ t₂) k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_diff_of_mem_right h

theorem get!_diff_of_not_mem_left [TransCmp cmp] [Inhabited β]
    {k : α} (h : ¬k ∈ t₁) :
    Const.get! (t₁ \ t₂) k = default := by
  revert h
  exact t₁.inductionOn₂ t₂ fun _ _ h => DTreeMap.Const.get!_diff_of_not_mem_left h

end Const

section Alter

theorem alter_eq_empty_iff_erase_eq_empty [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    t.alter k f = ∅ ↔ t.erase k = ∅ ∧ f (t.get? k) = none := by
  cases t with | mk t
  simpa only [← isEmpty_iff, ← Option.isNone_iff_eq_none, ← Bool.and_eq_true, Bool.coe_iff_coe] using
    DTreeMap.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem alter_eq_empty_iff [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    t.alter k f = ∅ ↔ (t = ∅ ∨ (t.size = 1 ∧ k ∈ t)) ∧ f (t.get? k) = none := by
  rw [alter_eq_empty_iff_erase_eq_empty, erase_eq_empty_iff]

@[grind =]
theorem contains_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).contains k' =
      if cmp k k' = .eq then (f (t.get? k)).isSome else t.contains k' :=
  t.inductionOn fun _ => DTreeMap.contains_alter

@[grind =]
theorem mem_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    k' ∈ t.alter k f ↔
      if cmp k k' = .eq then (f (t.get? k)).isSome = true else k' ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_alter

theorem mem_alter_of_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)}
    (he : cmp k k' = .eq) :
    k' ∈ t.alter k f ↔ (f (t.get? k)).isSome :=
  t.inductionOn (fun _ he => DTreeMap.mem_alter_of_compare_eq he) he

@[simp]
theorem contains_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).contains k = (f (t.get? k)).isSome :=
  t.inductionOn fun _ => DTreeMap.contains_alter_self

@[simp]
theorem mem_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    k ∈ t.alter k f ↔ (f (t.get? k)).isSome :=
  t.inductionOn fun _ => DTreeMap.mem_alter_self

theorem contains_alter_of_not_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ cmp k k' = .eq) :
    (t.alter k f).contains k' = t.contains k' :=
  t.inductionOn (fun _ he => DTreeMap.contains_alter_of_not_compare_eq he) he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ cmp k k' = .eq) :
    k' ∈ t.alter k f ↔ k' ∈ t :=
  t.inductionOn (fun _ he => DTreeMap.mem_alter_of_not_compare_eq he) he

@[grind =]
theorem size_alter [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).size =
      if k ∈ t ∧ (f (t.get? k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (t.get? k)).isSome then
        t.size + 1
      else
        t.size :=
  t.inductionOn fun _ => DTreeMap.size_alter

theorem size_alter_eq_add_one [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∉ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f).size = t.size + 1 :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.size_alter_eq_add_one h₁ h₂) h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f).size = t.size - 1 :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.size_alter_eq_sub_one h₁ h₂) h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : ¬ k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f).size = t.size :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.size_alter_eq_self_of_not_mem h₁ h₂) h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f).size = t.size :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.size_alter_eq_self_of_mem h₁ h₂) h₁ h₂

theorem size_alter_le_size [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).size ≤ t.size + 1 :=
  t.inductionOn fun _ => DTreeMap.size_alter_le_size

theorem size_le_size_alter [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    t.size - 1 ≤ (t.alter k f).size :=
  t.inductionOn fun _ => DTreeMap.size_le_size_alter

@[grind =]
theorem get?_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get? k' =
      if h : cmp k k' = .eq then
        cast (congrArg (Option ∘ β) (LawfulEqCmp.compare_eq_iff_eq.mp h)) (f (t.get? k))
      else
        t.get? k' :=
  t.inductionOn fun _ => DTreeMap.get?_alter

@[simp]
theorem get?_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get? k = f (t.get? k) :=
  t.inductionOn fun _ => DTreeMap.get?_alter_self

@[grind =]
theorem get_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ (t.alter k f)} :
    (t.alter k f).get k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f (t.get? k)).isSome := mem_alter_of_compare_eq heq |>.mp hc
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq)) <| (f (t.get? k)).get <| h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        t.get k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.get_alter) hc

@[simp]
theorem get_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter k f} :
    haveI h' : (f (t.get? k)).isSome := mem_alter_self.mp hc
    (t.alter k f).get k hc = (f (t.get? k)).get h' :=
  t.inductionOn (fun _ _ => DTreeMap.get_alter_self) hc

@[grind =]
theorem get!_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α} [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get! k' =
      if heq : cmp k k' = .eq then
        (f (t.get? k)).map (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' :=
  t.inductionOn fun _ => DTreeMap.get!_alter

@[simp]
theorem get!_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} [Inhabited (β k)]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get! k = (f (t.get? k)).get! :=
  t.inductionOn fun _ => DTreeMap.get!_alter_self

@[grind =]
theorem getD_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α} {fallback : β k'}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getD k' fallback =
      if heq : cmp k k' = .eq then
        f (t.get? k) |>.map (cast (congrArg β <| LawfulEqCmp.compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback :=
  t.inductionOn fun _ => DTreeMap.getD_alter

@[simp]
theorem getD_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {fallback : β k}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getD k fallback = (f (t.get? k)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getD_alter_self

@[grind =]
theorem getKey?_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey? k' =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then some k else none
      else
        t.getKey? k' :=
  t.inductionOn fun _ => DTreeMap.getKey?_alter

theorem getKey?_alter_self [TransCmp cmp] [LawfulEqCmp cmp] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey? k = if (f (t.get? k)).isSome then some k else none :=
  t.inductionOn fun _ => DTreeMap.getKey?_alter_self

@[grind =]
theorem getKey!_alter [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k k' : α}
    {f : Option (β k) → Option (β k)} : (t.alter k f).getKey! k' =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then k else default
      else
        t.getKey! k' :=
  t.inductionOn fun _ => DTreeMap.getKey!_alter

theorem getKey!_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey! k = if (f (t.get? k)).isSome then k else default :=
  t.inductionOn fun _ => DTreeMap.getKey!_alter_self

@[simp]
theorem getKey_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter k f} :
    (t.alter k f).getKey k hc = k :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_alter_self) hc

@[grind =]
theorem getKeyD_alter [TransCmp cmp] [LawfulEqCmp cmp] {k k' fallback : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_alter

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k : α}
    {fallback : α} {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKeyD k fallback = if (f (t.get? k)).isSome then k else fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_alter_self

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

theorem alter_eq_empty_iff_erase_eq_empty [TransCmp cmp] {k : α}
    {f : Option β → Option β} :
    alter t k f = ∅ ↔ t.erase k = ∅ ∧ f (get? t k) = none := by
  cases t with | mk t
  simpa only [← isEmpty_iff, ← Option.isNone_iff_eq_none, ← Bool.and_eq_true, Bool.coe_iff_coe] using
    DTreeMap.Const.isEmpty_alter_eq_isEmpty_erase

@[simp]
theorem alter_eq_empty_iff [TransCmp cmp] {k : α} {f : Option β → Option β} :
    alter t k f = ∅ ↔ (t = ∅ ∨ (t.size = 1 ∧ k ∈ t)) ∧ (f (get? t k)) = none := by
  rw [alter_eq_empty_iff_erase_eq_empty, erase_eq_empty_iff]

@[grind =]
theorem contains_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).contains k' =
      if cmp k k' = .eq then (f (get? t k)).isSome else t.contains k' :=
  t.inductionOn fun _ => DTreeMap.Const.contains_alter

@[grind =]
theorem mem_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    k' ∈ alter t k f ↔
      if cmp k k' = .eq then (f (get? t k)).isSome = true else k' ∈ t :=
  t.inductionOn fun _ => DTreeMap.Const.mem_alter

theorem mem_alter_of_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : cmp k k' = .eq) :
    k' ∈ alter t k f ↔ (f (get? t k)).isSome :=
  t.inductionOn (fun _ he => DTreeMap.Const.mem_alter_of_compare_eq he) he

@[simp]
theorem contains_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).contains k = (f (get? t k)).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.contains_alter_self

@[simp]
theorem mem_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    k ∈ alter t k f ↔ (f (get? t k)).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.mem_alter_self

theorem contains_alter_of_not_compare_eq [TransCmp cmp] {k k' : α}
    {f : Option β → Option β} (he : ¬ cmp k k' = .eq) :
    (alter t k f).contains k' = t.contains k' :=
  t.inductionOn (fun _ he => DTreeMap.Const.contains_alter_of_not_compare_eq he) he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    (he : ¬ cmp k k' = .eq) :
    k' ∈ alter t k f ↔ k' ∈ t :=
  t.inductionOn (fun _ he => DTreeMap.Const.mem_alter_of_not_compare_eq he) he

@[grind =]
theorem size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size =
      if k ∈ t ∧ (f (get? t k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (get? t k)).isSome then
        t.size + 1
      else
        t.size :=
  t.inductionOn fun _ => DTreeMap.Const.size_alter

theorem size_alter_eq_add_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f (get? t k)).isSome) :
    (alter t k f).size = t.size + 1 :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.Const.size_alter_eq_add_one h₁ h₂) h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter t k f).size = t.size - 1 :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.Const.size_alter_eq_sub_one h₁ h₂) h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter t k f).size = t.size :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.Const.size_alter_eq_self_of_not_mem h₁ h₂) h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isSome) :
    (alter t k f).size = t.size :=
  t.inductionOn (fun _ h₁ h₂ => DTreeMap.Const.size_alter_eq_self_of_mem h₁ h₂) h₁ h₂

theorem size_alter_le_size [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).size ≤ t.size + 1 :=
  t.inductionOn fun _ => DTreeMap.Const.size_alter_le_size

theorem size_le_size_alter [TransCmp cmp] {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter t k f).size :=
  t.inductionOn fun _ => DTreeMap.Const.size_le_size_alter

@[grind =]
theorem get?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    get? (alter t k f) k' =
      if cmp k k' = .eq then
        f (get? t k)
      else
        get? t k' :=
  t.inductionOn fun _ => DTreeMap.Const.get?_alter

@[simp]
theorem get?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    get? (alter t k f) k = f (get? t k) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_alter_self

@[grind =]
theorem get_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter t k f)} :
    get (alter t k f) k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f (get? t k)).isSome := mem_alter_of_compare_eq heq |>.mp hc
        (f (get? t k)).get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq heq |>.mp hc
        get t k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_alter) hc

@[simp]
theorem get_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    haveI h' : (f (get? t k)).isSome := mem_alter_self.mp hc
    get (alter t k f) k hc = (f (get? t k)).get h' :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_alter_self) hc

@[grind =]
theorem get!_alter [TransCmp cmp] {k k' : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter t k f) k' =
      if cmp k k' = .eq then
        (f (get? t k)).get!
      else
        get! t k' :=
  t.inductionOn fun _ => DTreeMap.Const.get!_alter

@[simp]
theorem get!_alter_self [TransCmp cmp] {k : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter t k f) k = (f (get? t k)).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_alter_self

@[grind =]
theorem getD_alter [TransCmp cmp] {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter t k f) k' fallback =
      if cmp k k' = .eq then
        f (get? t k) |>.getD fallback
      else
        getD t k' fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_alter

@[simp]
theorem getD_alter_self [TransCmp cmp] {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter t k f) k fallback = (f (get? t k)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_alter_self

@[grind =]
theorem getKey?_alter [TransCmp cmp] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey? k' =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then some k else none
      else
        t.getKey? k' :=
  t.inductionOn fun _ => DTreeMap.Const.getKey?_alter

theorem getKey?_alter_self [TransCmp cmp] {k : α} {f : Option β → Option β} :
    (alter t k f).getKey? k = if (f (get? t k)).isSome then some k else none :=
  t.inductionOn fun _ => DTreeMap.Const.getKey?_alter_self

@[grind =]
theorem getKey!_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey! k' =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then k else default
      else
        t.getKey! k' :=
  t.inductionOn fun _ => DTreeMap.Const.getKey!_alter

theorem getKey!_alter_self [TransCmp cmp] [Inhabited α] {k : α}
    {f : Option β → Option β} :
    (alter t k f).getKey! k = if (f (get? t k)).isSome then k else default :=
  t.inductionOn fun _ => DTreeMap.Const.getKey!_alter_self

@[grind =]
theorem getKey_alter [TransCmp cmp] [Inhabited α] {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter t k f} :
    (alter t k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : t.contains k' := mem_alter_of_not_compare_eq heq |>.mp hc
        t.getKey k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.Const.getKey_alter) hc

@[simp]
theorem getKey_alter_self [TransCmp cmp] [Inhabited α] {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    (alter t k f).getKey k hc = k :=
  t.inductionOn (fun _ _ => DTreeMap.Const.getKey_alter_self) hc

@[grind =]
theorem getKeyD_alter [TransCmp cmp] {k k' fallback : α} {f : Option β → Option β} :
    (alter t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getKeyD_alter

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [Inhabited α] {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter t k f).getKeyD k fallback = if (f (get? t k)).isSome then k else fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getKeyD_alter_self

end Const

end Alter

section Modify

variable [TransCmp cmp]

section Dependent

variable [LawfulEqCmp cmp]

@[simp]
theorem modify_eq_empty_iff {k : α} {f : β k → β k} :
    t.modify k f = ∅ ↔ t = ∅ := by
  cases t with | mk t
  simpa only [← isEmpty_iff, Bool.coe_iff_coe] using DTreeMap.isEmpty_modify

@[grind =]
theorem contains_modify {k k' : α} {f : β k → β k} :
    (t.modify k f).contains k' = t.contains k' :=
  t.inductionOn fun _ => DTreeMap.contains_modify

@[grind =]
theorem mem_modify {k k' : α} {f : β k → β k} :
    k' ∈ t.modify k f ↔ k' ∈ t :=
  t.inductionOn fun _ => DTreeMap.mem_modify

@[grind =]
theorem size_modify {k : α} {f : β k → β k} :
    (t.modify k f).size = t.size :=
  t.inductionOn fun _ => DTreeMap.size_modify

@[grind =]
theorem get?_modify {k k' : α} {f : β k → β k} :
    (t.modify k f).get? k' =
      if h : cmp k k' = .eq then
        (cast (congrArg (Option ∘ β) (LawfulEqCmp.compare_eq_iff_eq.mp h)) ((t.get? k).map f))
      else
        t.get? k' :=
  t.inductionOn fun _ => DTreeMap.get?_modify

@[simp]
theorem get?_modify_self {k : α} {f : β k → β k} :
    (t.modify k f).get? k = (t.get? k).map f :=
  t.inductionOn fun _ => DTreeMap.get?_modify_self

@[grind =]
theorem get_modify {k k' : α} {f : β k → β k} {hc : k' ∈ t.modify k f} :
    (t.modify k f).get k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr heq |>.mpr <| mem_modify.mp hc
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq)) <| f (t.get k h')
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.get k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.get_modify) hc

@[simp]
theorem get_modify_self {k : α} {f : β k → β k} {hc : k ∈ t.modify k f} :
    haveI h' : k ∈ t := mem_modify.mp hc
    (t.modify k f).get k hc = f (t.get k h') :=
  t.inductionOn (fun _ _ => DTreeMap.get_modify_self) hc

@[grind =]
theorem get!_modify {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (t.modify k f).get! k' =
      if heq : cmp k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' :=
  t.inductionOn fun _ => DTreeMap.get!_modify

@[simp]
theorem get!_modify_self {k : α} [Inhabited (β k)] {f : β k → β k} :
    (t.modify k f).get! k = ((t.get? k).map f).get! :=
  t.inductionOn fun _ => DTreeMap.get!_modify_self

@[grind =]
theorem getD_modify {k k' : α} {fallback : β k'} {f : β k → β k} :
    (t.modify k f).getD k' fallback =
      if heq : cmp k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β <| LawfulEqCmp.compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback :=
  t.inductionOn fun _ => DTreeMap.getD_modify

@[simp]
theorem getD_modify_self {k : α} {fallback : β k} {f : β k → β k} :
    (t.modify k f).getD k fallback = ((t.get? k).map f).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getD_modify_self

@[grind =]
theorem getKey?_modify {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  t.inductionOn fun _ => DTreeMap.getKey?_modify

theorem getKey?_modify_self {k : α} {f : β k → β k} :
    (t.modify k f).getKey? k = if k ∈ t then some k else none :=
  t.inductionOn fun _ => DTreeMap.getKey?_modify_self

@[grind =]
theorem getKey!_modify [Inhabited α] {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  t.inductionOn fun _ => DTreeMap.getKey!_modify

theorem getKey!_modify_self [Inhabited α] {k : α} {f : β k → β k} :
    (t.modify k f).getKey! k = if k ∈ t then k else default :=
  t.inductionOn fun _ => DTreeMap.getKey!_modify_self

@[grind =]
theorem getKey_modify [Inhabited α] {k k' : α} {f : β k → β k}
    {hc : k' ∈ t.modify k f} :
    (t.modify k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.getKey k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_modify) hc

@[simp]
theorem getKey_modify_self [Inhabited α] {k : α} {f : β k → β k}
    {hc : k ∈ t.modify k f} : (t.modify k f).getKey k hc = k :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_modify_self) hc

@[grind =]
theorem getKeyD_modify {k k' fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_modify

theorem getKeyD_modify_self [Inhabited α] {k fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_modify_self

end Dependent

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[simp]
theorem modify_eq_empty_iff {k : α} {f : β → β} :
    modify t k f = ∅ ↔ t = ∅ := by
  cases t with | mk t
  simpa only [← isEmpty_iff, Bool.coe_iff_coe] using DTreeMap.Const.isEmpty_modify

@[grind =]
theorem contains_modify {k k' : α} {f : β → β} :
    (modify t k f).contains k' = t.contains k' :=
  t.inductionOn fun _ => DTreeMap.Const.contains_modify

@[grind =]
theorem mem_modify {k k' : α} {f : β → β} :
    k' ∈ modify t k f ↔ k' ∈ t :=
  t.inductionOn fun _ => DTreeMap.Const.mem_modify

@[grind =]
theorem size_modify {k : α} {f : β → β} :
    (modify t k f).size = t.size :=
  t.inductionOn fun _ => DTreeMap.Const.size_modify

@[grind =]
theorem get?_modify {k k' : α} {f : β → β} :
    get? (modify t k f) k' =
      if cmp k k' = .eq then
        (get? t k).map f
      else
        get? t k' :=
  t.inductionOn fun _ => DTreeMap.Const.get?_modify

@[simp]
theorem get?_modify_self {k : α} {f : β → β} :
    get? (modify t k f) k = (get? t k).map f :=
  t.inductionOn fun _ => DTreeMap.Const.get?_modify_self

@[grind =]
theorem get_modify {k k' : α} {f : β → β} {hc : k' ∈ modify t k f} :
    get (modify t k f) k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr heq |>.mpr <| mem_modify.mp hc
        f (get t k h')
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        get t k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_modify) hc

@[simp]
theorem get_modify_self {k : α} {f : β → β} {hc : k ∈ modify t k f} :
    haveI h' : k ∈ t := mem_modify.mp hc
    get (modify t k f) k hc = f (get t k h') :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_modify_self) hc

@[grind =]
theorem get!_modify {k k' : α} [hi : Inhabited β] {f : β → β} :
    get! (modify t k f) k' =
      if cmp k k' = .eq then
        get? t k |>.map f |>.get!
      else
        get! t k' :=
  t.inductionOn fun _ => DTreeMap.Const.get!_modify

@[simp]
theorem get!_modify_self {k : α} [Inhabited β] {f : β → β} :
    get! (modify t k f) k = ((get? t k).map f).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_modify_self

@[grind =]
theorem getD_modify {k k' : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k' fallback =
      if cmp k k' = .eq then
        get? t k |>.map f |>.getD fallback
      else
        getD t k' fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_modify

@[simp]
theorem getD_modify_self {k : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k fallback = ((get? t k).map f).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_modify_self

@[grind =]
theorem getKey?_modify {k k' : α} {f : β → β} :
    (modify t k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  t.inductionOn fun _ => DTreeMap.Const.getKey?_modify

theorem getKey?_modify_self {k : α} {f : β → β} :
    (modify t k f).getKey? k = if k ∈ t then some k else none :=
  t.inductionOn fun _ => DTreeMap.Const.getKey?_modify_self

@[grind =]
theorem getKey!_modify [Inhabited α] {k k' : α} {f : β → β} :
    (modify t k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  t.inductionOn fun _ => DTreeMap.Const.getKey!_modify

theorem getKey!_modify_self [Inhabited α] {k : α} {f : β → β} :
    (modify t k f).getKey! k = if k ∈ t then k else default :=
  t.inductionOn fun _ => DTreeMap.Const.getKey!_modify_self

@[grind =]
theorem getKey_modify [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify t k f} :
    (modify t k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify.mp hc
        t.getKey k' h' :=
  t.inductionOn (fun _ _ => DTreeMap.Const.getKey_modify) hc

@[simp]
theorem getKey_modify_self [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify t k f} : (modify t k f).getKey k hc = k :=
  t.inductionOn (fun _ _ => DTreeMap.Const.getKey_modify_self) hc

@[grind =]
theorem getKeyD_modify {k k' fallback : α} {f : β → β} :
    (modify t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getKeyD_modify

theorem getKeyD_modify_self [Inhabited α] {k fallback : α} {f : β → β} :
    (modify t k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getKeyD_modify_self

end Const

end Modify

section Min

@[simp, grind =]
theorem minKey?_empty [TransCmp cmp] :
    (∅ : ExtDTreeMap α β cmp).minKey? = none :=
  DTreeMap.minKey?_emptyc

@[simp, grind =]
theorem minKey?_eq_none_iff [TransCmp cmp] :
    t.minKey? = none ↔ t = ∅ :=
  Iff.symm <| isEmpty_iff.symm.trans <| Iff.symm <| t.inductionOn fun _ => DTreeMap.minKey?_eq_none_iff

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem minKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_minKey?_eq_isEmpty [TransCmp cmp] :
    t.minKey?.isNone = t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.isNone_minKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_minKey?_eq_not_isEmpty [TransCmp cmp] :
    t.minKey?.isSome = !t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.isSome_minKey?_eq_not_isEmpty

theorem isSome_minKey?_iff_ne_empty [TransCmp cmp] :
    t.minKey?.isSome ↔ ¬t = ∅ := by
  simp

@[grind =] theorem minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  t.inductionOn fun _ => DTreeMap.minKey?_insert

@[grind =] theorem isSome_minKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_minKey?_insert

theorem minKey_insert_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insert k v).minKey insert_ne_empty = k := by
  induction t
  case mk a =>
    exact DTreeMap.minKey_insert_of_isEmpty he

theorem minKey?_insert_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insert k v).minKey? = some k :=
  t.inductionOn (fun _ he => DTreeMap.minKey?_insert_of_isEmpty he) he

theorem minKey!_insert_of_isEmpty [TransCmp cmp] [Inhabited α] {k v} (he : t.isEmpty) :
    (t.insert k v).minKey! = k :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_insert_of_isEmpty he) he

theorem minKeyD_insert_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) {fallback : α} :
    (t.insert k v).minKeyD fallback = k :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_insert_of_isEmpty he) he

theorem minKey_insertIfNew_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey insertIfNew_ne_empty = k := by
  induction t
  case mk a =>
    exact DTreeMap.minKey_insertIfNew_of_isEmpty he

theorem minKey?_insertIfNew_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey? = some k :=
  t.inductionOn (fun _ he => DTreeMap.minKey?_insertIfNew_of_isEmpty he) he

theorem minKey!_insertIfNew_of_isEmpty [TransCmp cmp] [Inhabited α] {k v} (he : t.isEmpty) :
    (t.insertIfNew k v).minKey! = k :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_insertIfNew_of_isEmpty he) he

theorem minKeyD_insertIfNew_of_isEmpty [TransCmp cmp] {k v} (he : t.isEmpty) {fallback : α} :
    (t.insertIfNew k v).minKeyD fallback = k := t.inductionOn
    (fun _ he => DTreeMap.minKeyD_insertIfNew_of_isEmpty he) he

theorem minKey?_insert_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v |>.minKey? |>.get isSome_minKey?_insert) = kmi) →
    cmp kmi km |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_insert_le_minKey?

theorem minKey?_insert_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.minKey?.get isSome_minKey?_insert) = kmi) →
    cmp kmi k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_insert_le_self

theorem contains_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) →
    t.contains km :=
  t.inductionOn fun _ => DTreeMap.contains_minKey?

theorem minKey?_mem [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) →
    km ∈ t :=
  t.inductionOn fun _ => DTreeMap.minKey?_mem

@[simp] theorem min?_keys [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.keys.min? = t.minKey? :=
  t.inductionOn fun _ => DTreeMap.min?_keys

@[simp] theorem head?_keys [TransCmp cmp] [Min α]
    [LE α] [LawfulOrderCmp cmp] [LawfulOrderMin α]
    [LawfulOrderLeftLeaningMin α] [LawfulEqCmp cmp] :
    t.keys.head? = t.minKey? :=
  t.inductionOn fun _ => DTreeMap.head?_keys

theorem isSome_minKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.minKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_minKey?_of_contains

theorem isSome_minKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.minKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_minKey?_of_mem

theorem minKey?_le_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains hc) = km) →
    cmp km k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_le_of_contains

theorem minKey?_le_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem hc) = km) →
    cmp km k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_le_of_mem

theorem le_minKey? [TransCmp cmp] {k} :
    (∀ k', t.minKey? = some k' → (cmp k k').isLE) ↔
      (∀ k', k' ∈ t → (cmp k k').isLE) :=
  t.inductionOn fun _ => DTreeMap.le_minKey?

theorem getKey?_minKey? [TransCmp cmp] {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km :=
  t.inductionOn fun _ => DTreeMap.getKey?_minKey?

theorem getKey_minKey? [TransCmp cmp] {km hc} :
    (hkm : t.minKey?.get (isSome_minKey?_of_contains hc) = km) → t.getKey km hc = km :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_minKey?) hc

theorem getKey!_minKey? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.minKey? = some km) → t.getKey! km = km :=
  t.inductionOn fun _ => DTreeMap.getKey!_minKey?

theorem getKeyD_minKey? [TransCmp cmp] {km fallback} :
    (hkm : t.minKey? = some km) → t.getKeyD km fallback = km :=
  t.inductionOn fun _ => DTreeMap.getKeyD_minKey?

@[simp]
theorem minKey?_bind_getKey? [TransCmp cmp] :
    t.minKey?.bind t.getKey? = t.minKey? :=
  t.inductionOn fun _ => DTreeMap.minKey?_bind_getKey?

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (t.erase k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq :=
  t.inductionOn fun _ => DTreeMap.minKey?_erase_eq_iff_not_compare_eq_minKey?

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.minKey?) = t.minKey? :=
  t.inductionOn fun _ => DTreeMap.minKey?_erase_eq_of_not_compare_eq_minKey?

theorem isSome_minKey?_of_isSome_minKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.minKey?.isSome) →
    t.minKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_minKey?_of_isSome_minKey?_erase

theorem minKey?_le_minKey?_erase [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_le_minKey?_erase

@[grind =] theorem minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  t.inductionOn fun _ => DTreeMap.minKey?_insertIfNew

@[grind =] theorem isSome_minKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_minKey?_insertIfNew

theorem minKey?_insertIfNew_le_minKey? [TransCmp cmp] {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.minKey? |>.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi km |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_insertIfNew_le_minKey?

theorem minKey?_insertIfNew_le_self [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.minKey?.get isSome_minKey?_insertIfNew) = kmi) →
    cmp kmi k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_insertIfNew_le_self

@[grind =_] theorem minKey?_eq_head?_keys [TransCmp cmp] :
    t.minKey? = t.keys.head? :=
  t.inductionOn fun _ => DTreeMap.minKey?_eq_head?_keys

@[simp, grind =]
theorem minKey?_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).minKey? = t.minKey? :=
  t.inductionOn fun _ => DTreeMap.minKey?_modify

theorem minKey?_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.alter k f).minKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn fun _ => DTreeMap.minKey?_alter_eq_self

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem minKey?_modify [TransCmp cmp] {k f} :
    (Const.modify t k f).minKey? = t.minKey?.map fun km => if cmp km k = .eq then k else km :=
  t.inductionOn fun _ => DTreeMap.Const.minKey?_modify

@[simp]
theorem minKey?_modify_eq_minKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (Const.modify t k f).minKey? = t.minKey? :=
  t.inductionOn fun _ => DTreeMap.Const.minKey?_modify_eq_minKey?

@[grind =] theorem isSome_minKey?_modify [TransCmp cmp] {k f} :
    (Const.modify t k f).minKey?.isSome = !t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_minKey?_modify

theorem isSome_minKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (Const.modify t k f).minKey?.isSome = t.minKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_minKey?_modify_eq_isSome

theorem compare_minKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (Const.modify t k f |>.minKey? |>.get <|
        isSome_minKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.compare_minKey?_modify_eq

theorem minKey?_alter_eq_self [TransCmp cmp] {k f} :
    (Const.alter t k f).minKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn fun _ => DTreeMap.Const.minKey?_alter_eq_self

end Const

theorem minKey_eq_get_minKey? [TransCmp cmp] {he} :
    t.minKey he = t.minKey?.get (isSome_minKey?_iff_ne_empty.mpr he) :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_eq_get_minKey?) he

theorem minKey?_eq_some_minKey [TransCmp cmp] (he) :
    t.minKey? = some (t.minKey he) :=
  t.inductionOn (fun _ _ => DTreeMap.minKey?_eq_some_minKey) he

theorem minKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.minKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  t.inductionOn (fun _ _ _ => DTreeMap.minKey_eq_iff_getKey?_eq_self_and_forall) he km

theorem minKey_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.minKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  t.inductionOn (fun _ _ _ => DTreeMap.minKey_eq_iff_mem_and_forall) he km

@[grind =] theorem minKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).minKey insert_ne_empty =
      t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k' :=
  t.inductionOn fun _ => DTreeMap.minKey_insert

theorem minKey_insert_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insert k v |>.minKey insert_ne_empty) (t.minKey he) |>.isLE :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_insert_le_minKey) he

theorem minKey_insert_le_self [TransCmp cmp] {k v} :
    cmp (t.insert k v |>.minKey insert_ne_empty) k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey_insert_le_self

@[grind =] theorem contains_minKey [TransCmp cmp] {he} :
    t.contains (t.minKey he) :=
  t.inductionOn (fun _ _ => DTreeMap.contains_minKey) he

theorem minKey_mem [TransCmp cmp] {he} :
    t.minKey he ∈ t :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_mem) he

grind_pattern minKey_mem => t.minKey he ∈ t

theorem minKey_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp (t.minKey (ne_empty_of_mem hc)) k |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.minKey_le_of_contains hc) hc

theorem minKey_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp (t.minKey (ne_empty_of_mem hc)) k |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.minKey_le_of_mem hc) hc

theorem le_minKey [TransCmp cmp] {k he} :
    (cmp k (t.minKey he)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  t.inductionOn (fun _ _ => DTreeMap.le_minKey) he

@[simp, grind =]
theorem getKey?_minKey [TransCmp cmp] {he} :
    t.getKey? (t.minKey he) = some (t.minKey he) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey?_minKey) he

@[simp, grind =]
theorem getKey_minKey [TransCmp cmp] {he hc} :
    t.getKey (t.minKey he) hc = t.minKey he :=
  t.inductionOn (fun _ _ _ => DTreeMap.getKey_minKey) he hc

@[simp, grind =]
theorem getKey!_minKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.minKey he) = t.minKey he :=
  t.inductionOn (fun _ _ => DTreeMap.getKey!_minKey) he

@[simp, grind =]
theorem getKeyD_minKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.minKey he) fallback = t.minKey he :=
  t.inductionOn (fun _ _ _ => DTreeMap.getKeyD_minKey) he fallback

@[simp]
theorem minKey_erase_eq_iff_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (t.erase k |>.minKey he) =
        t.minKey (ne_empty_of_erase_ne_empty he) ↔
      ¬ cmp k (t.minKey <| ne_empty_of_erase_ne_empty he) = .eq :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_erase_eq_iff_not_compare_eq_minKey) he

theorem minKey_erase_eq_of_not_compare_eq_minKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.minKey (ne_empty_of_erase_ne_empty he)) = .eq) →
    (t.erase k |>.minKey he) =
      t.minKey (ne_empty_of_erase_ne_empty he) :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_erase_eq_of_not_compare_eq_minKey) he

theorem minKey_le_minKey_erase [TransCmp cmp] {k he} :
    cmp (t.minKey <| ne_empty_of_erase_ne_empty he)
      (t.erase k |>.minKey he) |>.isLE :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_le_minKey_erase) he

@[grind =] theorem minKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).minKey insertIfNew_ne_empty =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  t.inductionOn fun _ => DTreeMap.minKey_insertIfNew

theorem minKey_insertIfNew_le_minKey [TransCmp cmp] {k v he} :
    cmp (t.insertIfNew k v |>.minKey insertIfNew_ne_empty)
      (t.minKey he) |>.isLE :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_insertIfNew_le_minKey) he

theorem minKey_insertIfNew_le_self [TransCmp cmp] {k v} :
    cmp (t.insertIfNew k v |>.minKey <| insertIfNew_ne_empty) k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey_insertIfNew_le_self

@[grind =_] theorem minKey_eq_head_keys [TransCmp cmp] {he} :
    t.minKey he = t.keys.head (mt keys_eq_nil_iff.mp he) :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_eq_head_keys) he

@[simp, grind =]
theorem minKey_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (t.modify k f).minKey he = t.minKey (mt modify_eq_empty_iff.mpr he) :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_modify) he

theorem minKey_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (t.alter k f).minKey he = k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_alter_eq_self) he

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem minKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).minKey he =
      if cmp (t.minKey (mt modify_eq_empty_iff.mpr he)) k = .eq then
        k
      else
        (t.minKey (mt modify_eq_empty_iff.mpr he)) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.minKey_modify) he

@[simp]
theorem minKey_modify_eq_minKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).minKey he = t.minKey (mt modify_eq_empty_iff.mpr he) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.minKey_modify_eq_minKey) he

theorem compare_minKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.minKey he)
      (t.minKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  t.inductionOn (fun _ _ => DTreeMap.Const.compare_minKey_modify_eq) he

@[simp]
theorem ordCompare_minKey_modify_eq [Ord α] [TransOrd α] {t : ExtDTreeMap α β} {k f he} :
    compare (modify t k f |>.minKey he)
      (t.minKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  t.inductionOn (fun _ _ => DTreeMap.Const.ordCompare_minKey_modify_eq) he

theorem minKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).minKey he = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn (fun _ _ => DTreeMap.Const.minKey_alter_eq_self) he

end Const

theorem minKey_eq_minKey! [TransCmp cmp] [Inhabited α] {he : t ≠ ∅} :
    t.minKey he = t.minKey! :=
  t.inductionOn (fun _ _ => DTreeMap.minKey_eq_minKey!) he

theorem minKey?_eq_some_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.minKey? = some t.minKey! := by
  rw [minKey?_eq_some_minKey he, minKey_eq_minKey!]

@[simp]
theorem minKey!_empty [TransCmp cmp] [Inhabited α] : (∅ : ExtDTreeMap α β cmp).minKey! = default :=
  DTreeMap.minKey!_eq_default rfl

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_eq_iff_getKey?_eq_self_and_forall (isEmpty_eq_false_iff.mpr he)) he

theorem minKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_eq_iff_mem_and_forall (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem minKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v).minKey! =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  t.inductionOn fun _ => DTreeMap.minKey!_insert

theorem minKey!_insert_le_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp (t.insert k v).minKey! t.minKey! |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_insert_le_minKey! (isEmpty_eq_false_iff.mpr he)) he

theorem minKey!_insert_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insert k v).minKey! k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey!_insert_le_self

theorem contains_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.contains t.minKey! :=
  t.inductionOn (fun _ he => DTreeMap.contains_minKey! (isEmpty_eq_false_iff.mpr he)) he

theorem minKey!_mem [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.minKey! ∈ t :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_mem (isEmpty_eq_false_iff.mpr he)) he

theorem minKey!_le_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp t.minKey! k |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.minKey!_le_of_contains hc) hc

theorem minKey!_le_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp t.minKey! k |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.minKey!_le_of_mem hc) hc

theorem le_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    (cmp k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  t.inductionOn (fun _ he => DTreeMap.le_minKey! (isEmpty_eq_false_iff.mpr he)) he

theorem getKey?_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey? t.minKey! = some t.minKey! :=
  t.inductionOn (fun _ he => DTreeMap.getKey?_minKey! (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem getKey_minKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey! :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_minKey!) hc

@[simp, grind =]
theorem getKey_minKey!_eq_minKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.minKey! hc = t.minKey (ne_empty_of_mem hc) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_minKey!_eq_minKey) hc

theorem getKey!_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey! t.minKey! = t.minKey! :=
  t.inductionOn (fun _ he => DTreeMap.getKey!_minKey! (isEmpty_eq_false_iff.mpr he)) he

theorem getKeyD_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKeyD t.minKey! fallback = t.minKey! :=
  t.inductionOn (fun _ he => DTreeMap.getKeyD_minKey! (isEmpty_eq_false_iff.mpr he)) he

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k t.minKey! = .eq) :
    (t.erase k).minKey! = t.minKey! :=
  t.inductionOn (fun _ he heq => DTreeMap.minKey!_erase_eq_of_not_compare_minKey!_eq (isEmpty_eq_false_iff.mpr he) heq) he heq

theorem minKey!_le_minKey!_erase [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) :
    cmp t.minKey! (t.erase k).minKey! |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_le_minKey!_erase (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem minKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v).minKey! =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  t.inductionOn fun _ => DTreeMap.minKey!_insertIfNew

theorem minKey!_insertIfNew_le_minKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp (t.insertIfNew k v).minKey! t.minKey! |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_insertIfNew_le_minKey! (isEmpty_eq_false_iff.mpr he)) he

theorem minKey!_insertIfNew_le_self [TransCmp cmp] [Inhabited α] {k v} :
    cmp (t.insertIfNew k v).minKey! k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKey!_insertIfNew_le_self

@[grind =_] theorem minKey!_eq_head!_keys [TransCmp cmp] [Inhabited α] :
    t.minKey! = t.keys.head! :=
  t.inductionOn fun _ => DTreeMap.minKey!_eq_head!_keys

@[simp]
theorem minKey!_modify [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (t.modify k f).minKey! = t.minKey! :=
  t.inductionOn fun _ => DTreeMap.minKey!_modify

theorem minKey!_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f}
    (he : t.alter k f ≠ ∅) :
    (t.alter k f).minKey! = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKey!_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem minKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : modify t k f ≠ ∅) :
    (modify t k f).minKey! = if cmp t.minKey! k = .eq then k else t.minKey! :=
  t.inductionOn (fun _ he => DTreeMap.Const.minKey!_modify (isEmpty_eq_false_iff.mpr he)) he

@[simp]
theorem minKey!_modify_eq_minKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f).minKey! = t.minKey! :=
  t.inductionOn fun _ => DTreeMap.Const.minKey!_modify_eq_minKey!

theorem compare_minKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f).minKey! t.minKey! = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.compare_minKey!_modify_eq

@[simp]
theorem ordCompare_minKey!_modify_eq [Ord α] [TransOrd α] {t : ExtDTreeMap α β} [Inhabited α] {k f} :
    compare (modify t k f).minKey! t.minKey! = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.ordCompare_minKey!_modify_eq

theorem minKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : alter t k f ≠ ∅) :
    (alter t k f).minKey! = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn (fun _ he => DTreeMap.Const.minKey!_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

end Const

theorem minKey?_eq_some_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.minKey? = some (t.minKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.minKey?_eq_some_minKeyD (isEmpty_eq_false_iff.mpr he)) he

@[simp]
theorem minKeyD_empty [TransCmp cmp] {fallback : α} :
    (∅ : ExtDTreeMap α β cmp).minKeyD fallback = fallback :=
  DTreeMap.minKeyD_eq_fallback rfl

theorem minKey!_eq_minKeyD_default [TransCmp cmp] [Inhabited α] :
    t.minKey! = t.minKeyD default :=
  t.inductionOn fun _ => DTreeMap.minKey!_eq_minKeyD_default

theorem minKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.minKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_eq_iff_getKey?_eq_self_and_forall (isEmpty_eq_false_iff.mpr he)) he

theorem minKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.minKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_eq_iff_mem_and_forall (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem minKeyD_insert [TransCmp cmp] {k v fallback} :
    (t.insert k v |>.minKeyD fallback) =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  t.inductionOn fun _ => DTreeMap.minKeyD_insert

theorem minKeyD_insert_le_minKeyD [TransCmp cmp] (he : t ≠ ∅)
    {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_insert_le_minKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem minKeyD_insert_le_self [TransCmp cmp] {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKeyD_insert_le_self

theorem contains_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.contains (t.minKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.contains_minKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem minKeyD_mem [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.minKeyD fallback ∈ t :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_mem (isEmpty_eq_false_iff.mpr he)) he

theorem minKeyD_le_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.minKeyD_le_of_contains hc) hc

theorem minKeyD_le_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.minKeyD_le_of_mem hc) hc

theorem le_minKeyD [TransCmp cmp] (he : t ≠ ∅) {k fallback} :
    (cmp k (t.minKeyD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  t.inductionOn (fun _ he => DTreeMap.le_minKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem getKey?_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.getKey? (t.minKeyD fallback) = some (t.minKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.getKey?_minKeyD (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem getKey_minKeyD [TransCmp cmp] {fallback hc} :
    t.getKey (t.minKeyD fallback) hc = t.minKeyD fallback :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_minKeyD) hc

theorem getKey!_minKeyD [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKey! (t.minKeyD fallback) = t.minKeyD fallback :=
  t.inductionOn (fun _ he => DTreeMap.getKey!_minKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem getKeyD_minKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback fallback'} :
    t.getKeyD (t.minKeyD fallback) fallback' = t.minKeyD fallback :=
  t.inductionOn (fun _ he => DTreeMap.getKeyD_minKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem minKeyD_erase_eq_of_not_compare_minKeyD_eq [TransCmp cmp] {k fallback}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k (t.minKeyD fallback) = .eq) :
    (t.erase k |>.minKeyD fallback) = t.minKeyD fallback :=
  t.inductionOn (fun _ he heq => DTreeMap.minKeyD_erase_eq_of_not_compare_minKeyD_eq (isEmpty_eq_false_iff.mpr he) heq) he heq

theorem minKeyD_le_minKeyD_erase [TransCmp cmp] {k}
    (he : t.erase k ≠ ∅) {fallback} :
    cmp (t.minKeyD fallback) (t.erase k |>.minKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_le_minKeyD_erase (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem minKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    (t.insertIfNew k v |>.minKeyD fallback) =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  t.inductionOn fun _ => DTreeMap.minKeyD_insertIfNew

theorem minKeyD_insertIfNew_le_minKeyD [TransCmp cmp]
    (he : t ≠ ∅) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_insertIfNew_le_minKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem minKeyD_insertIfNew_le_self [TransCmp cmp] {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) k |>.isLE :=
  t.inductionOn fun _ => DTreeMap.minKeyD_insertIfNew_le_self

theorem minKeyD_eq_headD_keys [TransCmp cmp] {fallback} :
    t.minKeyD fallback = t.keys.headD fallback :=
  t.inductionOn fun _ => DTreeMap.minKeyD_eq_headD_keys

@[simp, grind =]
theorem minKeyD_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (t.modify k f |>.minKeyD fallback) = t.minKeyD fallback :=
  t.inductionOn fun _ => DTreeMap.minKeyD_modify

theorem minKeyD_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f}
    (he : t.alter k f ≠ ∅) {fallback} :
    (t.alter k f |>.minKeyD fallback) = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn (fun _ he => DTreeMap.minKeyD_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem minKeyD_modify [TransCmp cmp] {k f}
    (he : modify t k f ≠ ∅) {fallback} :
    (modify t k f |>.minKeyD fallback) =
      if cmp (t.minKeyD fallback) k = .eq then k else (t.minKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.Const.minKeyD_modify (isEmpty_eq_false_iff.mpr he)) he

@[simp, grind =]
theorem minKeyD_modify_eq_minKeyD [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (modify t k f |>.minKeyD fallback) = t.minKeyD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.minKeyD_modify_eq_minKeyD

theorem compare_minKeyD_modify_eq [TransCmp cmp] {k f fallback} :
    cmp (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.compare_minKeyD_modify_eq

@[simp]
theorem ordCompare_minKeyD_modify_eq [Ord α] [TransOrd α] {t : ExtDTreeMap α β} {k f fallback} :
    compare (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.ordCompare_minKeyD_modify_eq

theorem minKeyD_alter_eq_self [TransCmp cmp] {k f}
    (he : alter t k f ≠ ∅) {fallback} :
    (alter t k f |>.minKeyD fallback) = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  t.inductionOn (fun _ he => DTreeMap.Const.minKeyD_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

end Const

end Min

section Max

@[simp, grind =]
theorem maxKey?_empty [TransCmp cmp] : (∅ : ExtDTreeMap α β cmp).maxKey? = none :=
  DTreeMap.maxKey?_emptyc

@[simp, grind =]
theorem maxKey?_eq_none_iff [TransCmp cmp] : t.maxKey? = none ↔ t = ∅ :=
  Iff.symm <| isEmpty_iff.symm.trans <| Iff.symm <| t.inductionOn fun _ => DTreeMap.maxKey?_eq_none_iff

theorem maxKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] {km} :
    t.maxKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  t.inductionOn fun _ => DTreeMap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall

theorem maxKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {km} :
    t.maxKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  t.inductionOn fun _ => DTreeMap.maxKey?_eq_some_iff_mem_and_forall

@[simp, grind =]
theorem isNone_maxKey?_eq_isEmpty [TransCmp cmp] :
    t.maxKey?.isNone = t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.isNone_maxKey?_eq_isEmpty

@[simp, grind =]
theorem isSome_maxKey?_eq_not_isEmpty [TransCmp cmp] :
    t.maxKey?.isSome = !t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.isSome_maxKey?_eq_not_isEmpty

theorem isSome_maxKey?_iff_ne_empty [TransCmp cmp] :
    t.maxKey?.isSome ↔ t ≠ ∅ := by
  simp

@[grind =] theorem maxKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k|>.isLE then k else k') :=
  t.inductionOn fun _ => DTreeMap.maxKey?_insert

@[grind =] theorem isSome_maxKey?_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_maxKey?_insert

theorem maxKey?_le_maxKey?_insert [TransCmp cmp] {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insert k v |>.maxKey? |>.get isSome_maxKey?_insert) = kmi) →
    cmp km kmi |>.isLE :=
  t.inductionOn fun _ => DTreeMap.maxKey?_le_maxKey?_insert

theorem self_le_maxKey?_insert [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insert k v |>.maxKey?.get isSome_maxKey?_insert) = kmi) →
    cmp k kmi |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKey?_insert

theorem contains_maxKey? [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) →
    t.contains km :=
  t.inductionOn fun _ => DTreeMap.contains_maxKey?

theorem maxKey?_mem [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) → km ∈ t :=
  t.inductionOn fun _ => DTreeMap.maxKey?_mem

theorem isSome_maxKey?_of_contains [TransCmp cmp] {k} :
    (hc : t.contains k) → t.maxKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_maxKey?_of_contains

theorem isSome_maxKey?_of_mem [TransCmp cmp] {k} :
    k ∈ t → t.maxKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_maxKey?_of_mem

theorem le_maxKey?_of_contains [TransCmp cmp] {k km} :
    (hc : t.contains k) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_contains hc) = km) →
    cmp k km |>.isLE :=
  t.inductionOn fun _ => DTreeMap.le_maxKey?_of_contains

theorem le_maxKey?_of_mem [TransCmp cmp] {k km} :
    (hc : k ∈ t) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_mem hc) = km) →
    cmp k km |>.isLE :=
  t.inductionOn fun _ => DTreeMap.le_maxKey?_of_mem

theorem maxKey?_le [TransCmp cmp] {k} :
    (∀ k', t.maxKey? = some k' → (cmp k' k).isLE) ↔
      (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  t.inductionOn fun _ => DTreeMap.maxKey?_le

theorem getKey?_maxKey? [TransCmp cmp] {km} :
    (hkm : t.maxKey? = some km) → t.getKey? km = some km :=
  t.inductionOn fun _ => DTreeMap.getKey?_maxKey?

theorem getKey_maxKey? [TransCmp cmp] {km hc} :
    (hkm : t.maxKey?.get (isSome_maxKey?_of_contains hc) = km) → t.getKey km hc = km :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_maxKey?) hc

theorem getKey!_maxKey? [TransCmp cmp] [Inhabited α] {km} :
    (hkm : t.maxKey? = some km) → t.getKey! km = km :=
  t.inductionOn fun _ => DTreeMap.getKey!_maxKey?

theorem getKeyD_maxKey? [TransCmp cmp] {km fallback} :
    (hkm : t.maxKey? = some km) → t.getKeyD km fallback = km :=
  t.inductionOn fun _ => DTreeMap.getKeyD_maxKey?

@[simp]
theorem maxKey?_bind_getKey? [TransCmp cmp] :
    t.maxKey?.bind t.getKey? = t.maxKey? :=
  t.inductionOn fun _ => DTreeMap.maxKey?_bind_getKey?

theorem maxKey?_erase_eq_iff_not_compare_eq_maxKey? [TransCmp cmp] {k} :
    (t.erase k |>.maxKey?) = t.maxKey? ↔
      ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq :=
  t.inductionOn fun _ => DTreeMap.maxKey?_erase_eq_iff_not_compare_eq_maxKey?

theorem maxKey?_erase_eq_of_not_compare_eq_maxKey? [TransCmp cmp] {k} :
    (hc : ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.maxKey?) = t.maxKey? :=
  t.inductionOn fun _ => DTreeMap.maxKey?_erase_eq_of_not_compare_eq_maxKey?

theorem isSome_maxKey?_of_isSome_maxKey?_erase [TransCmp cmp] {k} :
    (hs : t.erase k |>.maxKey?.isSome) →
    t.maxKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_maxKey?_of_isSome_maxKey?_erase

theorem maxKey?_erase_le_maxKey? [TransCmp cmp] {k km kme} :
    (hkme : (t.erase k |>.maxKey?) = some kme) →
    (hkm : (t.maxKey?.get <|
      isSome_maxKey?_of_isSome_maxKey?_erase <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  t.inductionOn fun _ => DTreeMap.maxKey?_erase_le_maxKey?

@[grind =] theorem maxKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  t.inductionOn fun _ => DTreeMap.maxKey?_insertIfNew

@[grind =] theorem isSome_maxKey?_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_maxKey?_insertIfNew

theorem maxKey?_le_maxKey?_insertIfNew [TransCmp cmp] {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.maxKey? |>.get isSome_maxKey?_insertIfNew) = kmi) →
    cmp km kmi |>.isLE :=
  t.inductionOn fun _ => DTreeMap.maxKey?_le_maxKey?_insertIfNew

theorem self_le_maxKey?_insertIfNew [TransCmp cmp] {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.maxKey?.get isSome_maxKey?_insertIfNew) = kmi) →
    cmp k kmi |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKey?_insertIfNew

@[grind =_] theorem maxKey?_eq_getLast?_keys [TransCmp cmp] :
    t.maxKey? = t.keys.getLast? :=
  t.inductionOn fun _ => DTreeMap.maxKey?_eq_getLast?_keys

@[simp, grind =]
theorem maxKey?_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.modify k f).maxKey? = t.maxKey? :=
  t.inductionOn fun _ => DTreeMap.maxKey?_modify

theorem maxKey?_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (t.alter k f).maxKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn fun _ => DTreeMap.maxKey?_alter_eq_self

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

@[grind =] theorem maxKey?_modify [TransCmp cmp] {k f} :
    (Const.modify t k f).maxKey? = t.maxKey?.map fun km => if cmp km k = .eq then k else km :=
  t.inductionOn fun _ => DTreeMap.Const.maxKey?_modify

@[simp, grind =]
theorem maxKey?_modify_eq_maxKey? [TransCmp cmp] [LawfulEqCmp cmp] {k f} :
    (Const.modify t k f).maxKey? = t.maxKey? :=
  t.inductionOn fun _ => DTreeMap.Const.maxKey?_modify_eq_maxKey?

@[grind =] theorem isSome_maxKey?_modify [TransCmp cmp] {k f} :
    (Const.modify t k f).maxKey?.isSome = !t.isEmpty :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_maxKey?_modify

theorem isSome_maxKey?_modify_eq_isSome [TransCmp cmp] {k f} :
    (Const.modify t k f).maxKey?.isSome = t.maxKey?.isSome :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_maxKey?_modify_eq_isSome

theorem compare_maxKey?_modify_eq [TransCmp cmp] {k f km kmm} :
    (hkm : t.maxKey? = some km) →
    (hkmm : (Const.modify t k f |>.maxKey? |>.get <|
        isSome_maxKey?_modify_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.compare_maxKey?_modify_eq

theorem maxKey?_alter_eq_self [TransCmp cmp] {k f} :
    (Const.alter t k f).maxKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn fun _ => DTreeMap.Const.maxKey?_alter_eq_self

end Const

theorem maxKey_eq_get_maxKey? [TransCmp cmp] {he} :
    t.maxKey he = t.maxKey?.get (isSome_maxKey?_iff_ne_empty.mpr he) :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_eq_get_maxKey?) he

theorem maxKey?_eq_some_maxKey [TransCmp cmp] (he) :
    t.maxKey? = some (t.maxKey he) :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey?_eq_some_maxKey) he

theorem maxKey_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {he km} :
    t.maxKey he = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  t.inductionOn (fun _ _ _ => DTreeMap.maxKey_eq_iff_getKey?_eq_self_and_forall) he km

theorem maxKey_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {he km} :
    t.maxKey he = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  t.inductionOn (fun _ _ _ => DTreeMap.maxKey_eq_iff_mem_and_forall) he km

@[grind =] theorem maxKey_insert [TransCmp cmp] {k v} :
    (t.insert k v).maxKey insert_ne_empty =
      t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k' :=
  t.inductionOn fun _ => DTreeMap.maxKey_insert

theorem maxKey_le_maxKey_insert [TransCmp cmp] {k v he} :
    cmp (t.maxKey he) (t.insert k v |>.maxKey insert_ne_empty) |>.isLE :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_le_maxKey_insert) he

theorem self_le_maxKey_insert [TransCmp cmp] {k v} :
    cmp k (t.insert k v |>.maxKey insert_ne_empty) |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKey_insert

@[grind =] theorem contains_maxKey [TransCmp cmp] {he} :
    t.contains (t.maxKey he) :=
  t.inductionOn (fun _ _ => DTreeMap.contains_maxKey) he

theorem maxKey_mem [TransCmp cmp] {he} :
    t.maxKey he ∈ t :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_mem) he

grind_pattern maxKey_mem => t.maxKey he ∈ t

theorem le_maxKey_of_contains [TransCmp cmp] {k} (hc : t.contains k) :
    cmp k (t.maxKey (ne_empty_of_mem hc)) |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.le_maxKey_of_contains hc) hc

theorem le_maxKey_of_mem [TransCmp cmp] {k} (hc : k ∈ t) :
    cmp k (t.maxKey (ne_empty_of_mem hc)) |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.le_maxKey_of_mem hc) hc

theorem maxKey_le [TransCmp cmp] {k he} :
    (cmp (t.maxKey he) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_le) he

@[simp, grind =]
theorem getKey?_maxKey [TransCmp cmp] {he} :
    t.getKey? (t.maxKey he) = some (t.maxKey he) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey?_maxKey) he

@[simp, grind =]
theorem getKey_maxKey [TransCmp cmp] {he hc} :
    t.getKey (t.maxKey he) hc = t.maxKey he :=
  t.inductionOn (fun _ _ _ => DTreeMap.getKey_maxKey) he hc

@[simp, grind =]
theorem getKey!_maxKey [TransCmp cmp] [Inhabited α] {he} :
    t.getKey! (t.maxKey he) = t.maxKey he :=
  t.inductionOn (fun _ _ => DTreeMap.getKey!_maxKey) he

@[simp, grind =]
theorem getKeyD_maxKey [TransCmp cmp] {he fallback} :
    t.getKeyD (t.maxKey he) fallback = t.maxKey he :=
  t.inductionOn (fun _ _ _ => DTreeMap.getKeyD_maxKey) he fallback

@[simp]
theorem maxKey_erase_eq_iff_not_compare_eq_maxKey [TransCmp cmp] {k he} :
    (t.erase k |>.maxKey he) =
        t.maxKey (ne_empty_of_erase_ne_empty he) ↔
      ¬ cmp k (t.maxKey <| ne_empty_of_erase_ne_empty he) = .eq :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_erase_eq_iff_not_compare_eq_maxKey) he

theorem maxKey_erase_eq_of_not_compare_eq_maxKey [TransCmp cmp] {k he} :
    (hc : ¬ cmp k (t.maxKey (ne_empty_of_erase_ne_empty he)) = .eq) →
    (t.erase k |>.maxKey he) =
      t.maxKey (ne_empty_of_erase_ne_empty he) :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_erase_eq_of_not_compare_eq_maxKey) he

theorem maxKey_erase_le_maxKey [TransCmp cmp] {k he} :
    cmp (t.erase k |>.maxKey he)
      (t.maxKey <| ne_empty_of_erase_ne_empty he) |>.isLE :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_erase_le_maxKey) he

@[grind =] theorem maxKey_insertIfNew [TransCmp cmp] {k v} :
    (t.insertIfNew k v).maxKey insertIfNew_ne_empty =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  t.inductionOn fun _ => DTreeMap.maxKey_insertIfNew

theorem maxKey_le_maxKey_insertIfNew [TransCmp cmp] {k v he} :
    cmp (t.maxKey he)
      (t.insertIfNew k v |>.maxKey insertIfNew_ne_empty) |>.isLE :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_le_maxKey_insertIfNew) he

theorem self_le_maxKey_insertIfNew [TransCmp cmp] {k v} :
    cmp k (t.insertIfNew k v |>.maxKey <| insertIfNew_ne_empty) |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKey_insertIfNew

@[grind =_] theorem maxKey_eq_getLast_keys [TransCmp cmp] {he} :
    t.maxKey he = t.keys.getLast (mt keys_eq_nil_iff.mp he) :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_eq_getLast_keys) he

@[simp]
theorem maxKey_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (t.modify k f).maxKey he = t.maxKey (mt modify_eq_empty_iff.mpr he) :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_modify) he

theorem maxKey_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (t.alter k f).maxKey he = k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_alter_eq_self) he

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

theorem maxKey_modify [TransCmp cmp] {k f he} :
    (modify t k f).maxKey he =
      if cmp (t.maxKey (mt modify_eq_empty_iff.mpr he)) k = .eq then
        k
      else
        (t.maxKey (mt modify_eq_empty_iff.mpr he)) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.maxKey_modify) he

@[simp, grind =]
theorem maxKey_modify_eq_maxKey [TransCmp cmp] [LawfulEqCmp cmp] {k f he} :
    (modify t k f).maxKey he = t.maxKey (mt modify_eq_empty_iff.mpr he) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.maxKey_modify_eq_maxKey) he

theorem compare_maxKey_modify_eq [TransCmp cmp] {k f he} :
    cmp (modify t k f |>.maxKey he)
      (t.maxKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  t.inductionOn (fun _ _ => DTreeMap.Const.compare_maxKey_modify_eq) he

@[simp]
theorem ordCompare_maxKey_modify_eq [Ord α] [TransOrd α] {t : ExtDTreeMap α β} {k f he} :
    compare (modify t k f |>.maxKey he)
      (t.maxKey (mt modify_eq_empty_iff.mpr he)) = .eq :=
  t.inductionOn (fun _ _ => DTreeMap.Const.ordCompare_maxKey_modify_eq) he

theorem maxKey_alter_eq_self [TransCmp cmp] {k f he} :
    (alter t k f).maxKey he = k ↔
      (f (get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn (fun _ _ => DTreeMap.Const.maxKey_alter_eq_self) he

end Const

theorem maxKey_eq_maxKey! [TransCmp cmp] [Inhabited α] {he : t ≠ ∅} :
    t.maxKey he = t.maxKey! :=
  t.inductionOn (fun _ _ => DTreeMap.maxKey_eq_maxKey!) he

theorem maxKey?_eq_some_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.maxKey? = some t.maxKey! := by
  rw [maxKey?_eq_some_maxKey he, maxKey_eq_maxKey!]

@[simp]
theorem maxKey!_empty [TransCmp cmp] [Inhabited α] : (∅ : ExtDTreeMap α β cmp).maxKey! = default :=
  DTreeMap.maxKey!_eq_default rfl

theorem maxKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.maxKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_eq_iff_getKey?_eq_self_and_forall (isEmpty_eq_false_iff.mpr he)) he

theorem maxKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    (he : t ≠ ∅) {km} :
    t.maxKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_eq_iff_mem_and_forall (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem maxKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    (t.insert k v).maxKey! =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  t.inductionOn fun _ => DTreeMap.maxKey!_insert

theorem maxKey!_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp t.maxKey! (t.insert k v).maxKey! |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_le_maxKey!_insert (isEmpty_eq_false_iff.mpr he)) he

theorem self_le_maxKey!_insert [TransCmp cmp] [Inhabited α] {k v} :
    cmp k (t.insert k v).maxKey! |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKey!_insert

theorem contains_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.contains t.maxKey! :=
  t.inductionOn (fun _ he => DTreeMap.contains_maxKey! (isEmpty_eq_false_iff.mpr he)) he

theorem maxKey!_mem [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.maxKey! ∈ t :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_mem (isEmpty_eq_false_iff.mpr he)) he

theorem le_maxKey!_of_contains [TransCmp cmp] [Inhabited α] {k} (hc : t.contains k) :
    cmp k t.maxKey! |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.le_maxKey!_of_contains hc) hc

theorem le_maxKey!_of_mem [TransCmp cmp] [Inhabited α] {k} (hc : k ∈ t) :
    cmp k t.maxKey! |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.le_maxKey!_of_mem hc) hc

theorem maxKey!_le [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k} :
    (cmp t.maxKey! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_le (isEmpty_eq_false_iff.mpr he)) he

theorem getKey?_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey? t.maxKey! = some t.maxKey! :=
  t.inductionOn (fun _ he => DTreeMap.getKey?_maxKey! (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem getKey_maxKey! [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.maxKey! hc = t.maxKey! :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_maxKey!) hc

@[simp, grind =]
theorem getKey_maxKey!_eq_maxKey [TransCmp cmp] [Inhabited α] {hc} :
    t.getKey t.maxKey! hc = t.maxKey (ne_empty_of_mem hc) :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_maxKey!_eq_maxKey) hc

theorem getKey!_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) :
    t.getKey! t.maxKey! = t.maxKey! :=
  t.inductionOn (fun _ he => DTreeMap.getKey!_maxKey! (isEmpty_eq_false_iff.mpr he)) he

theorem getKeyD_maxKey! [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKeyD t.maxKey! fallback = t.maxKey! :=
  t.inductionOn (fun _ he => DTreeMap.getKeyD_maxKey! (isEmpty_eq_false_iff.mpr he)) he

theorem maxKey!_erase_eq_of_not_compare_maxKey!_eq [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k t.maxKey! = .eq) :
    (t.erase k).maxKey! = t.maxKey! :=
  t.inductionOn (fun _ he heq => DTreeMap.maxKey!_erase_eq_of_not_compare_maxKey!_eq (isEmpty_eq_false_iff.mpr he) heq) he heq

theorem maxKey!_erase_le_maxKey! [TransCmp cmp] [Inhabited α] {k}
    (he : t.erase k ≠ ∅) :
    cmp (t.erase k).maxKey! t.maxKey! |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_erase_le_maxKey! (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    (t.insertIfNew k v).maxKey! =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  t.inductionOn fun _ => DTreeMap.maxKey!_insertIfNew

theorem maxKey!_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {k v} :
    cmp t.maxKey! (t.insertIfNew k v).maxKey! |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_le_maxKey!_insertIfNew (isEmpty_eq_false_iff.mpr he)) he

theorem self_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] {k v} :
    cmp k (t.insertIfNew k v).maxKey! |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKey!_insertIfNew

@[grind =_]
theorem maxKey!_eq_getLast!_keys [TransCmp cmp] [Inhabited α] :
    t.maxKey! = t.keys.getLast! :=
  t.inductionOn fun _ => DTreeMap.maxKey!_eq_getLast!_keys

@[simp]
theorem maxKey!_modify [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (t.modify k f).maxKey! = t.maxKey! :=
  t.inductionOn fun _ => DTreeMap.maxKey!_modify

theorem maxKey!_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f}
    (he : t.alter k f ≠ ∅) :
    (t.alter k f).maxKey! = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKey!_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

theorem maxKey!_modify [TransCmp cmp] [Inhabited α] {k f}
    (he : modify t k f ≠ ∅) :
    (modify t k f).maxKey! = if cmp t.maxKey! k = .eq then k else t.maxKey! :=
  t.inductionOn (fun _ he => DTreeMap.Const.maxKey!_modify (isEmpty_eq_false_iff.mpr he)) he

@[simp]
theorem maxKey!_modify_eq_maxKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] {k f} :
    (modify t k f).maxKey! = t.maxKey! :=
  t.inductionOn fun _ => DTreeMap.Const.maxKey!_modify_eq_maxKey!

theorem compare_maxKey!_modify_eq [TransCmp cmp] [Inhabited α] {k f} :
    cmp (modify t k f).maxKey! t.maxKey! = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.compare_maxKey!_modify_eq

@[simp]
theorem ordCompare_maxKey!_modify_eq [Ord α] [TransOrd α] {t : ExtDTreeMap α β} [Inhabited α] {k f} :
    compare (modify t k f).maxKey! t.maxKey! = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.ordCompare_maxKey!_modify_eq

theorem maxKey!_alter_eq_self [TransCmp cmp] [Inhabited α] {k f}
    (he : alter t k f ≠ ∅) :
    (alter t k f).maxKey! = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.Const.maxKey!_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

end Const

theorem maxKey?_eq_some_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.maxKey? = some (t.maxKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.maxKey?_eq_some_maxKeyD (isEmpty_eq_false_iff.mpr he)) he

@[simp]
theorem maxKeyD_empty [TransCmp cmp] {fallback} :
    (∅ : ExtDTreeMap α β cmp).maxKeyD fallback = fallback :=
  DTreeMap.maxKeyD_eq_fallback rfl

theorem maxKey!_eq_maxKeyD_default [TransCmp cmp] [Inhabited α] :
    t.maxKey! = t.maxKeyD default :=
  t.inductionOn fun _ => DTreeMap.maxKey!_eq_maxKeyD_default

theorem maxKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.maxKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_eq_iff_getKey?_eq_self_and_forall (isEmpty_eq_false_iff.mpr he)) he

theorem maxKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp]
    (he : t ≠ ∅) {km fallback} :
    t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_eq_iff_mem_and_forall (isEmpty_eq_false_iff.mpr he)) he

@[grind =]
theorem maxKeyD_insert [TransCmp cmp] {k v fallback} :
    (t.insert k v |>.maxKeyD fallback) =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  t.inductionOn fun _ => DTreeMap.maxKeyD_insert

theorem maxKeyD_le_maxKeyD_insert [TransCmp cmp] (he : t ≠ ∅)
    {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_le_maxKeyD_insert (isEmpty_eq_false_iff.mpr he)) he

theorem self_le_maxKeyD_insert [TransCmp cmp] {k v fallback} :
    cmp k (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKeyD_insert

theorem contains_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.contains (t.maxKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.contains_maxKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem maxKeyD_mem [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.maxKeyD fallback ∈ t :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_mem (isEmpty_eq_false_iff.mpr he)) he

theorem le_maxKeyD_of_contains [TransCmp cmp] {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.le_maxKeyD_of_contains hc) hc

theorem le_maxKeyD_of_mem [TransCmp cmp] {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ hc => DTreeMap.le_maxKeyD_of_mem hc) hc

theorem maxKeyD_le [TransCmp cmp] (he : t ≠ ∅) {k fallback} :
    (cmp (t.maxKeyD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_le (isEmpty_eq_false_iff.mpr he)) he

theorem getKey?_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback} :
    t.getKey? (t.maxKeyD fallback) = some (t.maxKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.getKey?_maxKeyD (isEmpty_eq_false_iff.mpr he)) he

@[grind =] theorem getKey_maxKeyD [TransCmp cmp] {fallback hc} :
    t.getKey (t.maxKeyD fallback) hc = t.maxKeyD fallback :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_maxKeyD) hc

theorem getKey!_maxKeyD [TransCmp cmp] [Inhabited α] (he : t ≠ ∅) {fallback} :
    t.getKey! (t.maxKeyD fallback) = t.maxKeyD fallback :=
  t.inductionOn (fun _ he => DTreeMap.getKey!_maxKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem getKeyD_maxKeyD [TransCmp cmp] (he : t ≠ ∅) {fallback fallback'} :
    t.getKeyD (t.maxKeyD fallback) fallback' = t.maxKeyD fallback :=
  t.inductionOn (fun _ he => DTreeMap.getKeyD_maxKeyD (isEmpty_eq_false_iff.mpr he)) he

theorem maxKeyD_erase_eq_of_not_compare_maxKeyD_eq [TransCmp cmp] {k fallback}
    (he : t.erase k ≠ ∅) (heq : ¬ cmp k (t.maxKeyD fallback) = .eq) :
    (t.erase k |>.maxKeyD fallback) = t.maxKeyD fallback :=
  t.inductionOn (fun _ he heq => DTreeMap.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq (isEmpty_eq_false_iff.mpr he) heq) he heq

theorem maxKeyD_erase_le_maxKeyD [TransCmp cmp] {k}
    (he : t.erase k ≠ ∅) {fallback} :
    cmp (t.erase k |>.maxKeyD fallback) (t.maxKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_erase_le_maxKeyD (isEmpty_eq_false_iff.mpr he)) he

@[grind =]
theorem maxKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    (t.insertIfNew k v |>.maxKeyD fallback) =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  t.inductionOn fun _ => DTreeMap.maxKeyD_insertIfNew

theorem maxKeyD_le_maxKeyD_insertIfNew [TransCmp cmp]
    (he : t ≠ ∅) {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_le_maxKeyD_insertIfNew (isEmpty_eq_false_iff.mpr he)) he

theorem self_le_maxKeyD_insertIfNew [TransCmp cmp] {k v fallback} :
    cmp k (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  t.inductionOn fun _ => DTreeMap.self_le_maxKeyD_insertIfNew

theorem maxKeyD_eq_getLastD_keys [TransCmp cmp] {fallback} :
    t.maxKeyD fallback = t.keys.getLastD fallback :=
  t.inductionOn fun _ => DTreeMap.maxKeyD_eq_getLastD_keys

@[simp]
theorem maxKeyD_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (t.modify k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  t.inductionOn fun _ => DTreeMap.maxKeyD_modify

theorem maxKeyD_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] {k f}
    (he : t.alter k f ≠ ∅) {fallback} :
    (t.alter k f |>.maxKeyD fallback) = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.maxKeyD_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

namespace Const

variable {β : Type v} {t : ExtDTreeMap α β cmp}

theorem maxKeyD_modify [TransCmp cmp] {k f}
    (he : modify t k f ≠ ∅) {fallback} :
    (modify t k f |>.maxKeyD fallback) =
      if cmp (t.maxKeyD fallback) k = .eq then k else (t.maxKeyD fallback) :=
  t.inductionOn (fun _ he => DTreeMap.Const.maxKeyD_modify (isEmpty_eq_false_iff.mpr he)) he

@[simp, grind =]
theorem maxKeyD_modify_eq_maxKeyD [TransCmp cmp] [LawfulEqCmp cmp] {k f fallback} :
    (modify t k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.maxKeyD_modify_eq_maxKeyD

theorem compare_maxKeyD_modify_eq [TransCmp cmp] {k f fallback} :
    cmp (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.compare_maxKeyD_modify_eq

@[simp]
theorem ordCompare_maxKeyD_modify_eq [Ord α] [TransOrd α] {t : ExtDTreeMap α β} {k f fallback} :
    compare (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  t.inductionOn fun _ => DTreeMap.Const.ordCompare_maxKeyD_modify_eq

theorem maxKeyD_alter_eq_self [TransCmp cmp] {k f}
    (he : alter t k f ≠ ∅) {fallback} :
    (alter t k f |>.maxKeyD fallback) = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  t.inductionOn (fun _ he => DTreeMap.Const.maxKeyD_alter_eq_self (isEmpty_eq_false_iff.mpr he)) he

end Const

end Max

section Ext

variable {t₁ t₂ : ExtDTreeMap α β cmp}

@[ext, grind ext]
theorem ext_get? [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : ExtDTreeMap α β cmp}
    (h : ∀ k, t₁.get? k = t₂.get? k) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_forall_get?_eq h)) h

theorem toList_inj [TransCmp cmp] {t₁ t₂ : ExtDTreeMap α β cmp} :
    t₁.toList = t₂.toList ↔ t₁ = t₂ := by
  constructor
  · intro h
    cases t₁; cases t₂
    exact sound (.of_toList_perm (.of_eq h))
  · rintro rfl; rfl

theorem ext_toList [TransCmp cmp] (h : t₁.toList.Perm t₂.toList) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_toList_perm h)) h

namespace Const

variable {β : Type v} {t₁ t₂ : ExtDTreeMap α β cmp}

theorem ext_getKey_get? [TransCmp cmp]
    (hk : ∀ k hk hk', t₁.getKey k hk = t₂.getKey k hk')
    (hv : ∀ k, Const.get? t₁ k = Const.get? t₂ k) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ hk hv => sound <|
    .of_forall_getKey_eq_of_forall_constGet?_eq hk hv) hk hv

theorem ext_get? [TransCmp cmp] [LawfulEqCmp cmp]
    (h : ∀ k, Const.get? t₁ k = Const.get? t₂ k) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_forall_constGet?_eq h)) h

theorem ext_getKey?_unit [TransCmp cmp] {t₁ t₂ : ExtDTreeMap α Unit cmp}
    (h : ∀ k, t₁.getKey? k = t₂.getKey? k) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_forall_getKey?_unit_eq h)) h

theorem ext_contains_unit [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : ExtDTreeMap α Unit cmp}
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_forall_contains_unit_eq h)) h

theorem ext_mem_unit [TransCmp cmp] [LawfulEqCmp cmp] {t₁ t₂ : ExtDTreeMap α Unit cmp}
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_forall_mem_unit_iff h)) h

theorem toList_inj [TransCmp cmp] {t₁ t₂ : ExtDTreeMap α β cmp} :
    Const.toList t₁ = Const.toList t₂ ↔ t₁ = t₂ := by
  constructor
  · intro h
    cases t₁; cases t₂
    exact sound (.of_constToList_perm (.of_eq h))
  · rintro rfl; rfl

theorem ext_toList [TransCmp cmp] (h : (Const.toList t₁).Perm (Const.toList t₂)) : t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_constToList_perm h)) h

theorem ext_keys_unit [TransCmp cmp] {t₁ t₂ : ExtDTreeMap α Unit cmp} (h : t₁.keys.Perm t₂.keys) :
    t₁ = t₂ :=
  t₁.inductionOn₂ t₂ (fun _ _ h => sound (.of_keys_unit_perm h)) h

end Const

end Ext

section filterMap

variable {γ : α → Type w}

@[simp, grind =]
theorem toList_filterMap [TransCmp cmp] {f : (a : α) → β a → Option (γ a)} :
    (t.filterMap f).toList =
      t.toList.filterMap (fun p => (f p.1 p.2).map (fun x => ⟨p.1, x⟩)) :=
  t.inductionOn fun _ => DTreeMap.toList_filterMap

theorem filterMap_eq_empty_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} :
    t.filterMap f = ∅ ↔ ∀ k h, f k (t.get k h) = none :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.isEmpty_filterMap_iff

@[grind =]
theorem contains_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (t.filterMap f).contains k = (t.get? k).any (f k · |>.isSome) :=
  t.inductionOn fun _ => DTreeMap.contains_filterMap

@[grind =]
theorem mem_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ t.filterMap f ↔ ∃ h, (f k (t.get k h)).isSome := by
  simp only [mem_iff_contains, contains_filterMap, Option.any_eq_true_iff_get,
    ← contains_eq_isSome_get?, get_get?]

theorem contains_of_contains_filterMap [TransCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (t.filterMap f).contains k = true → t.contains k = true :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_filterMap

theorem mem_of_mem_filterMap [TransCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    k ∈ t.filterMap f → k ∈ t :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_filterMap

theorem size_filterMap_le_size [TransCmp cmp]
    {f : (a : α) → β a → Option (γ a)} :
    (t.filterMap f).size ≤ t.size :=
  t.inductionOn fun _ => DTreeMap.size_filterMap_le_size

grind_pattern size_filterMap_le_size => (t.filterMap f).size

theorem size_filterMap_eq_size_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} :
    (t.filterMap f).size = t.size ↔ ∀ (a : α) (h : a ∈ t), (f a (t.get a h)).isSome :=
  t.inductionOn fun _ => DTreeMap.size_filterMap_eq_size_iff

@[simp, grind =]
theorem get?_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (t.filterMap f).get? k = (t.get? k).bind (f k) :=
  t.inductionOn fun _ => DTreeMap.get?_filterMap

theorem isSome_apply_of_mem_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    ∀ (h' : k ∈ t.filterMap f),
      (f k (t.get k (mem_of_mem_filterMap h'))).isSome :=
  t.inductionOn fun _ => DTreeMap.isSome_apply_of_mem_filterMap

@[simp, grind =]
theorem get_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (t.filterMap f).get k h' =
      (f k (t.get k (mem_of_mem_filterMap h'))).get
        (isSome_apply_of_mem_filterMap h') :=
  t.inductionOn (fun _ _ => DTreeMap.get_filterMap) h'

@[simp, grind =]
theorem get!_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} [Inhabited (γ k)] :
    (t.filterMap f).get! k = ((t.get? k).bind (f k)).get! :=
  t.inductionOn fun _ => DTreeMap.get!_filterMap

@[simp, grind =]
theorem getD_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} {fallback : γ k} :
    (t.filterMap f).getD k fallback = ((t.get? k).bind (f k)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getD_filterMap

@[grind =]
theorem getKey?_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (t.filterMap f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (t.get x (mem_of_getKey?_eq_some h'))).isSome) :=
  t.inductionOn fun _ => DTreeMap.getKey?_filterMap

@[simp, grind =]
theorem getKey_filterMap [TransCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k : α} {h'} :
    (t.filterMap f).getKey k h' = t.getKey k (mem_of_mem_filterMap h') :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_filterMap) h'

@[grind =]
theorem getKey!_filterMap [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    {f : (a : α) → β a → Option (γ a)} {k : α} :
    (t.filterMap f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t.get x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  t.inductionOn fun _ => DTreeMap.getKey!_filterMap

@[grind =]
theorem getKeyD_filterMap [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Option (γ a)} {k fallback : α} :
    (t.filterMap f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (t.get x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_filterMap

namespace Const

variable {β : Type v} {γ : Type w} {t : ExtDTreeMap α (fun _ => β) cmp}

theorem filterMap_eq_empty_iff [TransCmp cmp] {f : α → β → Option γ} :
    t.filterMap f = ∅ ↔ ∀ k h, f (t.getKey k h) (get t k h) = none :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.Const.isEmpty_filterMap_iff

-- TODO: `contains_filterMap` is missing

@[grind =]
theorem mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    k ∈ t.filterMap f ↔ ∃ h, (f (t.getKey k h) (Const.get t k h)).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.mem_filterMap

-- TODO: `size_filterMap_le_size` is missing

theorem size_filterMap_eq_size_iff [TransCmp cmp]
    {f : α → β → Option γ} :
    (t.filterMap f).size = t.size ↔ ∀ k h, (f (t.getKey k h) (Const.get t k h)).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.size_filterMap_eq_size_iff

@[simp]
theorem get?_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    Const.get? (t.filterMap f) k = (Const.get? t k).pbind (fun x h' =>
      f (t.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_filterMap

/-- Simpler variant of `get?_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem get?_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} :
    Const.get? (t.filterMap f) k = (Const.get? t k).bind fun x => f k x := by
  simp [get?_filterMap]

theorem get?_filterMap_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Option γ} {k k' : α} (h : t.getKey? k = some k') :
    Const.get? (t.filterMap f) k = (Const.get? t k).bind (f k') :=
  t.inductionOn (fun _ => DTreeMap.Const.get?_filterMap_of_getKey?_eq_some) h

theorem isSome_apply_of_mem_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    ∀ (h : k ∈ t.filterMap f),
      (f (t.getKey k (mem_of_mem_filterMap h))
        (Const.get t k (mem_of_mem_filterMap h))).isSome :=
  t.inductionOn fun _ => DTreeMap.Const.isSome_apply_of_mem_filterMap

@[simp]
theorem get_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (t.filterMap f) k h =
      (f (t.getKey k (mem_of_mem_filterMap h))
        (Const.get t k (mem_of_mem_filterMap h))).get
          (isSome_apply_of_mem_filterMap h) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_filterMap) h

/-- Simpler variant of `get_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem get_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} {h} :
    Const.get (t.filterMap f) k h =
      (f k (Const.get t k (mem_of_mem_filterMap h))).get (by simpa using isSome_apply_of_mem_filterMap h) := by
  simp [get_filterMap]

theorem get!_filterMap [TransCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (t.filterMap f) k =
      ((Const.get? t k).pbind (fun x h' =>
        f (t.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_filterMap

/-- Simpler variant of `get!_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem get!_filterMap' [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k : α} :
    Const.get! (t.filterMap f) k = ((Const.get? t k).bind (f k) ).get!:= by
  simp [get!_filterMap]

theorem get!_filterMap_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → Option γ} {k k' : α} (h : t.getKey? k = some k') :
    Const.get! (t.filterMap f) k = ((Const.get? t k).bind (f k')).get! :=
  t.inductionOn (fun _ => DTreeMap.Const.get!_filterMap_of_getKey?_eq_some) h

theorem getD_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (t.filterMap f) k fallback =
      ((Const.get? t k).pbind (fun x h' =>
      f (t.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_filterMap

/-- Simpler variant of `getD_filterMap` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getD_filterMap' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Option γ} {k : α} {fallback : γ} :
    Const.getD (t.filterMap f) k fallback = ((Const.get? t k).bind (f k)).getD fallback := by
  simp [getD_filterMap]

theorem getD_filterMap_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : t.getKey? k = some k') :
    Const.getD (t.filterMap f) k fallback = ((Const.get? t k).bind (f k')).getD fallback :=
  t.inductionOn (fun _ => DTreeMap.Const.getD_filterMap_of_getKey?_eq_some) h

theorem toList_filterMap [TransCmp cmp] {f : α → β → Option γ} :
    Const.toList (t.filterMap fun k v => f k v) =
      (Const.toList t).filterMap (fun p => (f p.1 p.2).map (fun x => (p.1, x))) :=
  t.inductionOn fun _ => DTreeMap.Const.toList_filterMap

@[grind =]
theorem getKey?_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (Const.get t x (mem_of_getKey?_eq_some h'))).isSome) :=
  t.inductionOn fun _ => DTreeMap.Const.getKey?_filterMap

@[grind =]
theorem getKey!_filterMap [TransCmp cmp] [Inhabited α]
    {f : α → β → Option γ} {k : α} :
    (t.filterMap f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (Const.get t x (mem_of_getKey?_eq_some h'))).isSome)).get! :=
  t.inductionOn fun _ => DTreeMap.Const.getKey!_filterMap

@[grind =]
theorem getKeyD_filterMap [TransCmp cmp]
    {f : α → β → Option γ} {k fallback : α} :
    (t.filterMap f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (Const.get t x (mem_of_getKey?_eq_some h'))).isSome)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getKeyD_filterMap

end Const

end filterMap

section filter

theorem filterMap_eq_filter {f : (a : α) → β a → Bool} :
    t.filterMap (fun k => Option.guard (fun v => f k v)) = t.filter f :=
  t.inductionOn fun _ => sound DTreeMap.filterMap_equiv_filter

@[simp, grind =]
theorem toList_filter [TransCmp cmp] {f : (a : α) → β a → Bool} :
    (t.filter f).toList = t.toList.filter (fun p => f p.1 p.2) :=
  t.inductionOn fun _ => DTreeMap.toList_filter

theorem keys_filter_key [TransCmp cmp] {f : α → Bool} :
    (t.filter fun k _ => f k).keys = t.keys.filter f :=
  t.inductionOn fun _ => DTreeMap.keys_filter_key

theorem filter_eq_empty_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} :
    t.filter f = ∅ ↔ ∀ k h, f k (t.get k h) = false :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.isEmpty_filter_iff

theorem filter_key_eq_empty_iff [TransCmp cmp] {f : α → Bool} :
    t.filter (fun a _ => f a) = ∅ ↔ ∀ k h, f (t.getKey k h) = false :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.isEmpty_filter_key_iff

@[grind =]
theorem contains_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} :
    (t.filter f).contains k = (t.get? k).any (f k) :=
  t.inductionOn fun _ => DTreeMap.contains_filter

@[grind =]
theorem mem_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} :
    k ∈ t.filter f ↔ ∃ h, f k (t.get k h) := by
  simp only [mem_iff_contains, contains_filter, Option.any_eq_true_iff_get,
    ← contains_eq_isSome_get?, get_get?]

theorem mem_filter_key [TransCmp cmp]
    {f : α → Bool} {k : α} :
    k ∈ t.filter (fun a _ => f a) ↔ ∃ h, f (t.getKey k h) :=
  t.inductionOn fun _ => DTreeMap.mem_filter_key

theorem contains_of_contains_filter [TransCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} :
    (t.filter f).contains k = true → t.contains k = true :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_filter

theorem mem_of_mem_filter [TransCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} :
    k ∈ (t.filter f) → k ∈ t :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_filter

theorem size_filter_le_size [TransCmp cmp]
    {f : (a : α) → β a → Bool} :
    (t.filter f).size ≤ t.size :=
  t.inductionOn fun _ => DTreeMap.size_filter_le_size

grind_pattern size_filter_le_size => (t.filter f).size

theorem size_filter_eq_size_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} :
    (t.filter f).size = t.size ↔ ∀ k h, f k (t.get k h) :=
  t.inductionOn fun _ => DTreeMap.size_filter_eq_size_iff

theorem filter_eq_self_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} :
    t.filter f = t ↔ ∀ k h, f k (t.get k h) :=
  t.inductionOn fun _ => Iff.trans ⟨exact, sound⟩ DTreeMap.filter_equiv_self_iff

theorem filter_key_equiv_self_iff [TransCmp cmp]
    {f : (a : α) → Bool} :
    t.filter (fun k _ => f k) = t ↔ ∀ k h, f (t.getKey k h) :=
  t.inductionOn fun _ => Iff.trans ⟨exact, sound⟩ DTreeMap.filter_key_equiv_self_iff

theorem size_filter_key_eq_size_iff [TransCmp cmp]
    {f : α → Bool} :
    (t.filter fun k _ => f k).size = t.size ↔ ∀ (k : α) (h : k ∈ t), f (t.getKey k h) :=
  t.inductionOn fun _ => DTreeMap.size_filter_key_eq_size_iff

@[simp, grind =]
theorem get?_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} :
    (t.filter f).get? k = (t.get? k).filter (f k) :=
  t.inductionOn fun _ => DTreeMap.get?_filter

@[simp, grind =]
theorem get_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (t.filter f).get k h' = t.get k (mem_of_mem_filter h') :=
  t.inductionOn (fun _ _ => DTreeMap.get_filter) h'

@[grind =]
theorem get!_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} [Inhabited (β k)] :
    (t.filter f).get! k = ((t.get? k).filter (f k)).get! :=
  t.inductionOn fun _ => DTreeMap.get!_filter

@[grind =]
theorem getD_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} {fallback : β k} :
    (t.filter f).getD k fallback = ((t.get? k).filter (f k)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getD_filter

theorem keys_filter [TransCmp cmp] [LawfulEqCmp cmp] {f : (a : α) → β a → Bool} :
    (t.filter f).keys =
      (t.keys.attach.filter (fun ⟨x, h'⟩ => f x (t.get x (mem_of_mem_keys h')))).unattach :=
  t.inductionOn fun _ => DTreeMap.keys_filter

@[grind =]
theorem getKey?_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} :
    (t.filter f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      f x (t.get x (mem_of_getKey?_eq_some h'))) :=
  t.inductionOn fun _ => DTreeMap.getKey?_filter

theorem getKey?_filter_key [TransCmp cmp]
    {f : α → Bool} {k : α} :
    (t.filter fun k _ => f k).getKey? k = (t.getKey? k).filter f :=
  t.inductionOn fun _ => DTreeMap.getKey?_filter_key

@[simp, grind =]
theorem getKey_filter [TransCmp cmp]
    {f : (a : α) → β a → Bool} {k : α} {h'} :
    (t.filter f).getKey k h' = t.getKey k (mem_of_mem_filter h') :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_filter) h'

@[grind =]
theorem getKey!_filter [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α]
    {f : (a : α) → β a → Bool} {k : α} :
    (t.filter f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      f x (t.get x (mem_of_getKey?_eq_some h')))).get! :=
  t.inductionOn fun _ => DTreeMap.getKey!_filter

theorem getKey!_filter_key [TransCmp cmp] [Inhabited α]
    {f : α → Bool} {k : α} :
    (t.filter fun k _ => f k).getKey! k = ((t.getKey? k).filter f).get! :=
  t.inductionOn fun _ => DTreeMap.getKey!_filter_key

@[grind =]
theorem getKeyD_filter [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → Bool} {k fallback : α} :
    (t.filter f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      f x (t.get x (mem_of_getKey?_eq_some h')))).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_filter

theorem getKeyD_filter_key [TransCmp cmp]
    {f : α → Bool} {k fallback : α} :
    (t.filter fun k _ => f k).getKeyD k fallback = ((t.getKey? k).filter f).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_filter_key

namespace Const

variable {β : Type v} {γ : Type w} {t : ExtDTreeMap α (fun _ => β) cmp}

theorem filter_eq_empty_iff [TransCmp cmp] {f : α → β → Bool} :
    t.filter f = ∅ ↔ ∀ k h, f (t.getKey k h) (Const.get t k h) = false :=
  isEmpty_iff.symm.trans <| t.inductionOn fun _ => DTreeMap.Const.isEmpty_filter_iff

-- TODO: `contains_filter` is missing

@[grind =]
theorem mem_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    k ∈ t.filter f ↔ ∃ (h' : k ∈ t),
      f (t.getKey k h') (Const.get t k h') :=
  t.inductionOn fun _ => DTreeMap.Const.mem_filter

theorem size_filter_le_size [TransCmp cmp]
    {f : α → β → Bool} :
    (t.filter f).size ≤ t.size :=
  t.inductionOn fun _ => DTreeMap.Const.size_filter_le_size

grind_pattern size_filter_le_size => (t.filter f).size

theorem size_filter_eq_size_iff [TransCmp cmp]
    {f : α → β → Bool} :
    (t.filter f).size = t.size ↔ ∀ (a : α) (h : a ∈ t),
      f (t.getKey a h) (Const.get t a h) :=
  t.inductionOn fun _ => DTreeMap.Const.size_filter_eq_size_iff

theorem filter_eq_self_iff [TransCmp cmp]
    {f : α → β → Bool} :
    t.filter f = t ↔ ∀ k h, f (t.getKey k h) (Const.get t k h) :=
  t.inductionOn fun _ => Iff.trans ⟨exact, sound⟩ DTreeMap.Const.filter_equiv_self_iff

theorem get?_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    Const.get? (t.filter f) k = (Const.get? t k).pfilter (fun x h' =>
      f (t.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_filter

/-- Simpler variant of `get?_filter` when `LawfulEqCmp` is available. -/
@[simp, grind =]
theorem get?_filter' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Bool} {k : α} :
    Const.get? (t.filter f) k = (Const.get? t k).filter (f k) := by
  simp [get?_filter]

theorem get?_filter_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Bool} {k k' : α} :
    t.getKey? k = some k' →
      Const.get? (t.filter f) k = (Const.get? t k).filter (fun x => f k' x) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_filter_of_getKey?_eq_some

@[simp, grind =]
theorem get_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {h'} :
    Const.get (t.filter f) k h' = Const.get t k (mem_of_mem_filter h') :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_filter) h'

theorem get!_filter [TransCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    Const.get! (t.filter f) k =
      ((Const.get? t k).pfilter (fun x h' =>
      f (t.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_filter

/-- Simpler variant of `get!_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem get!_filter' [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k : α} :
    Const.get! (t.filter f) k = ((Const.get? t k).filter (f k)).get! := by
  simp [get!_filter]

theorem get!_filter_of_getKey?_eq_some [TransCmp cmp] [Inhabited β]
    {f : α → β → Bool} {k k' : α} :
    t.getKey? k = some k' →
      Const.get! (t.filter f) k = ((Const.get? t k).filter (fun x => f k' x)).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_filter_of_getKey?_eq_some

theorem getD_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} {fallback : β} :
    Const.getD (t.filter f) k fallback = ((Const.get? t k).pfilter (fun x h' =>
      f (t.getKey k (mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))) x)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_filter

/-- Simpler variant of `getD_filter` when `LawfulEqCmp` is available. -/
@[grind =]
theorem getD_filter' [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → Bool} {k : α} {fallback : β} :
    Const.getD (t.filter f) k fallback = ((Const.get? t k).filter (f k)).getD fallback := by
  simp [getD_filter]

theorem getD_filter_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → Bool} {k k' : α} {fallback : β} :
    t.getKey? k = some k' →
      Const.getD (t.filter f) k fallback =
        ((Const.get? t k).filter (fun x => f k' x)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_filter_of_getKey?_eq_some

@[simp, grind =]
theorem toList_filter [TransCmp cmp] {f : α → β → Bool} :
    toList (t.filter f) =
      (toList t).filter (fun p => f p.1 p.2) :=
  t.inductionOn fun _ => DTreeMap.Const.toList_filter

theorem keys_filter [TransCmp cmp] {f : α → β → Bool} :
    (t.filter f).keys =
      (t.keys.attach.filter (fun ⟨x, h'⟩ => f x (get t x (mem_of_mem_keys h')))).unattach :=
  t.inductionOn fun _ => DTreeMap.Const.keys_filter

@[grind =]
theorem getKey?_filter [TransCmp cmp]
    {f : α → β → Bool} {k : α} :
    (t.filter f).getKey? k =
    (t.getKey? k).pfilter (fun x h' =>
      (f x (Const.get t x (mem_of_getKey?_eq_some h')))) :=
  t.inductionOn fun _ => DTreeMap.Const.getKey?_filter

@[grind =]
theorem getKey!_filter [TransCmp cmp] [Inhabited α]
    {f : α → β → Bool} {k : α} :
    (t.filter f).getKey! k =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (Const.get t x (mem_of_getKey?_eq_some h'))))).get! :=
  t.inductionOn fun _ => DTreeMap.Const.getKey!_filter

@[grind =]
theorem getKeyD_filter [TransCmp cmp]
    {f : α → β → Bool} {k fallback : α} :
    (t.filter f).getKeyD k fallback =
    ((t.getKey? k).pfilter (fun x h' =>
      (f x (Const.get t x (mem_of_getKey?_eq_some h'))))).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getKeyD_filter

end Const

end filter

section map

variable {γ : α → Type w} {δ : α → Type w'}

@[simp]
theorem map_id : t.map (fun _ v => v) = t :=
  t.inductionOn fun _ => sound DTreeMap.map_id_equiv

@[simp, grind =]
theorem map_map {f : (a : α) → β a → γ a} {g : (a : α) → γ a → δ a} :
    (t.map f).map g = t.map fun k v => g k (f k v) :=
  t.inductionOn fun _ => sound DTreeMap.map_map_equiv

@[simp, grind =]
theorem toList_map [TransCmp cmp] {f : (a : α) → β a → γ a} :
    (t.map f).toList = t.toList.map (fun p => ⟨p.1, f p.1 p.2⟩) :=
  t.inductionOn fun _ => DTreeMap.toList_map

@[simp, grind =]
theorem keys_map [TransCmp cmp] {f : (a : α) → β a → γ a} : (t.map f).keys = t.keys :=
  t.inductionOn fun _ => DTreeMap.keys_map

theorem filterMap_eq_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} :
    (t.filterMap (fun k v => some (f k v))) = t.map f :=
  t.inductionOn fun _ => sound DTreeMap.filterMap_equiv_map

@[simp]
theorem map_eq_empty_iff [TransCmp cmp] {f : (a : α) → β a → γ a} :
    t.map f = ∅ ↔ t = ∅ := by
  simp only [← isEmpty_iff, Bool.coe_iff_coe]
  exact t.inductionOn fun _ => DTreeMap.isEmpty_map

@[grind =]
theorem contains_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} :
    (t.map f).contains k = t.contains k :=
  t.inductionOn fun _ => DTreeMap.contains_map

theorem contains_of_contains_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} :
    (t.map f).contains k = true → t.contains k = true :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_map

@[simp, grind =]
theorem mem_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ t.map f ↔ k ∈ t := by
  simp only [mem_iff_contains, contains_map]

theorem mem_of_mem_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} :
    k ∈ t.map f → k ∈ t :=
  t.inductionOn fun _ => DTreeMap.contains_of_contains_map

@[simp, grind =]
theorem size_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} :
    (t.map f).size = t.size :=
  t.inductionOn fun _ => DTreeMap.size_map

@[simp, grind =]
theorem get?_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} :
    (t.map f).get? k = (t.get? k).map (f k) :=
  t.inductionOn fun _ => DTreeMap.get?_map

@[simp, grind =]
theorem get_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (t.map f).get k h' = f k (t.get k (mem_of_mem_map h')) :=
  t.inductionOn (fun _ _ => DTreeMap.get_map) h'

@[grind =]
theorem get!_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} [Inhabited (γ k)] :
    (t.map f).get! k = ((t.get? k).map (f k)).get! :=
  t.inductionOn fun _ => DTreeMap.get!_map

@[grind =]
theorem getD_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} {fallback : γ k} :
    (t.map f).getD k fallback = ((t.get? k).map (f k)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.getD_map

@[simp, grind =]
theorem getKey?_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} :
    (t.map f).getKey? k = t.getKey? k :=
  t.inductionOn fun _ => DTreeMap.getKey?_map

@[simp, grind =]
theorem getKey_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k : α} {h'} :
    (t.map f).getKey k h' = t.getKey k (mem_of_mem_map h') :=
  t.inductionOn (fun _ _ => DTreeMap.getKey_map) h'

@[simp, grind =]
theorem getKey!_map [TransCmp cmp] [Inhabited α]
    {f : (a : α) → β a → γ a} {k : α} :
    (t.map f).getKey! k = t.getKey! k :=
  t.inductionOn fun _ => DTreeMap.getKey!_map

@[simp, grind =]
theorem getKeyD_map [TransCmp cmp]
    {f : (a : α) → β a → γ a} {k fallback : α} :
    (t.map f).getKeyD k fallback = t.getKeyD k fallback :=
  t.inductionOn fun _ => DTreeMap.getKeyD_map

namespace Const

variable {β : Type v} {γ : Type w} {t : ExtDTreeMap α (fun _ => β) cmp}

@[simp, grind =]
theorem get?_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} :
    Const.get? (t.map f) k = (Const.get? t k).map (f k) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_map

/-- Variant of `get?_map` that holds without `LawfulEqCmp`. -/
@[simp (low)]
theorem get?_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} :
    Const.get? (t.map f) k = (Const.get? t k).pmap (fun v h' => f (t.getKey k h') v)
      (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h')) :=
  t.inductionOn fun _ => DTreeMap.Const.get?_map'

theorem get?_map_of_getKey?_eq_some [TransCmp cmp]
    {f : α → β → γ} {k k' : α} (h : t.getKey? k = some k') :
    Const.get? (t.map f) k = (Const.get? t k).map (f k') :=
  t.inductionOn (fun _ => DTreeMap.Const.get?_map_of_getKey?_eq_some) h

@[simp, grind =]
theorem get_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} {h'} :
    Const.get (t.map f) k h' = f k (Const.get t k (mem_of_mem_map h')) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_map) h'

/-- Variant of `get_map` that holds without `LawfulEqCmp`. -/
@[simp (low)]
theorem get_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} {h'} :
    Const.get (t.map f) k h' =
      f (t.getKey k (mem_of_mem_map h')) (Const.get t k (mem_of_mem_map h')) :=
  t.inductionOn (fun _ _ => DTreeMap.Const.get_map') h'

@[grind =]
theorem get!_map [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (t.map f) k = ((Const.get? t k).map (f k)).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_map

/-- Variant of `get!_map` that holds without `LawfulEqCmp`. -/
theorem get!_map' [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k : α} :
    Const.get! (t.map f) k =
      ((get? t k).pmap (fun v h => f (t.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_mem h'))).get! :=
  t.inductionOn fun _ => DTreeMap.Const.get!_map'

theorem get!_map_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : t.getKey? k = some k') :
    Const.get! (t.map f) k = ((Const.get? t k).map (f k')).get! :=
  t.inductionOn (fun _ => DTreeMap.Const.get!_map_of_getKey?_eq_some) h

@[grind =]
theorem getD_map [TransCmp cmp] [LawfulEqCmp cmp]
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (t.map f) k fallback = ((Const.get? t k).map (f k)).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_map

/-- Variant of `getD_map` that holds without `LawfulEqCmp`. -/
theorem getD_map' [TransCmp cmp]
    {f : α → β → γ} {k : α} {fallback : γ} :
    Const.getD (t.map f) k fallback =
      ((get? t k).pmap (fun v h => f (t.getKey k h) v)
        (fun _ h' => mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some h'))).getD fallback :=
  t.inductionOn fun _ => DTreeMap.Const.getD_map'

theorem getD_map_of_getKey?_eq_some [TransCmp cmp] [Inhabited γ]
    {f : α → β → γ} {k k' : α} {fallback : γ} (h : t.getKey? k = some k') :
    Const.getD (t.map f) k fallback = ((Const.get? t k).map (f k')).getD fallback :=
  t.inductionOn (fun _ => DTreeMap.Const.getD_map_of_getKey?_eq_some) h

@[simp, grind =]
theorem toList_map [TransCmp cmp] {f : α → β → γ} :
    Const.toList (t.map f) =
      (Const.toList t).map (fun p => (p.1, f p.1 p.2)) :=
  t.inductionOn fun _ => DTreeMap.Const.toList_map

end Const

end map

end Std.ExtDTreeMap
