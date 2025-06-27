/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeSet.Raw.Basic

/-!
# Tree set lemmas

This file contains lemmas about `Std.Data.TreeSet.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
These proofs can be obtained from `Std.Data.TreeSet.Raw.WF`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.TreeSet.Raw

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeSet.Raw α cmp}

private theorem ext {t t' : Raw α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyc : (∅ : Raw α cmp).isEmpty :=
  TreeMap.Raw.isEmpty_emptyc

@[simp, grind =]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).isEmpty = false :=
  TreeMap.Raw.isEmpty_insertIfNew h

@[grind =]
theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.Raw.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {k : α} : t.contains k ↔ k ∈ t :=
  TreeMap.Raw.contains_iff_mem

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  TreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.Raw.mem_congr h hab

@[simp, grind =]
theorem contains_emptyc {k : α} : (∅ : Raw α cmp).contains k = false :=
  TreeMap.Raw.contains_emptyc

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : Raw α cmp) :=
  TreeMap.Raw.not_mem_emptyc

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

theorem isEmpty_eq_false_of_contains [TransCmp cmp] (h : t.WF) {a : α} (hc : t.contains a = true) :
    t.isEmpty = false :=
  TreeMap.Raw.isEmpty_eq_false_of_contains h hc

theorem isEmpty_iff_forall_contains [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  DTreeMap.Raw.isEmpty_iff_forall_contains h

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  DTreeMap.Raw.isEmpty_iff_forall_not_mem h

@[simp]
theorem insert_eq_insert {p : α} : Insert.insert p t = t.insert p :=
  rfl

@[simp]
theorem singleton_eq_insert {p : α} :
    Singleton.singleton p = (∅ : Raw α cmp).insert p :=
  rfl

@[simp, grind =]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.Raw.contains_insertIfNew h

@[simp, grind =]
theorem mem_insert [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.insert k ↔ cmp k a = .eq ∨ a ∈ t :=
  TreeMap.Raw.mem_insertIfNew h

theorem contains_insert_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).contains k :=
  TreeMap.Raw.contains_insertIfNew_self h

theorem mem_insert_self [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.insert k :=
  TreeMap.Raw.mem_insertIfNew_self h

theorem contains_of_contains_insert [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).contains a → cmp k a ≠ .eq → t.contains a :=
  TreeMap.Raw.contains_of_contains_insertIfNew h

theorem mem_of_mem_insert [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.insert k → cmp k a ≠ .eq → a ∈ t :=
  TreeMap.Raw.mem_of_mem_insertIfNew h

/-- This is a restatement of `mem_of_mem_insert` that is written to exactly match the
proof obligation in the statement of `get_insert`. -/
theorem mem_of_mem_insert' [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.insert k → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  TreeMap.Raw.mem_of_mem_insertIfNew' h

@[simp, grind =]
theorem size_emptyc : (∅ : Raw α cmp).size = 0 :=
  TreeMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  TreeMap.Raw.isEmpty_eq_size_eq_zero h.out

@[grind =] theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  TreeMap.Raw.size_insertIfNew h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.insert k).size :=
  TreeMap.Raw.size_le_size_insertIfNew h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  TreeMap.Raw.size_insertIfNew_le h

@[simp, grind =]
theorem erase_emptyc {k : α} :
    (∅ : Raw α cmp).erase k = ∅ :=
  ext <| TreeMap.Raw.erase_emptyc

@[simp, grind =]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  TreeMap.Raw.isEmpty_erase h

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransCmp cmp] (h : t.WF) (k : α) :
    t.isEmpty = ((t.erase k).isEmpty && !(t.contains k)) :=
  TreeMap.Raw.isEmpty_eq_isEmpty_erase_and_not_contains h k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransCmp cmp] (h : t.WF) {k : α}
    (he : (t.erase k).isEmpty = false) :
    t.isEmpty = false :=
  TreeMap.Raw.isEmpty_eq_false_of_isEmpty_erase_eq_false h he

@[simp, grind =]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  TreeMap.Raw.contains_erase h

@[simp, grind =]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  TreeMap.Raw.mem_erase h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.Raw.contains_of_contains_erase h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  TreeMap.Raw.mem_of_mem_erase h

@[grind =] theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  TreeMap.Raw.size_erase h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  TreeMap.Raw.size_erase_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  TreeMap.Raw.size_le_size_erase h

@[simp, grind =]
theorem get?_emptyc {a : α} : (∅ : TreeSet α cmp).get? a = none :=
  TreeMap.Raw.getKey?_emptyc

theorem get?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none :=
  TreeMap.Raw.getKey?_of_isEmpty h

@[grind =] theorem get?_insert [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).get? a = if cmp k a = .eq ∧ ¬k ∈ t then some k else t.get? a :=
  TreeMap.Raw.getKey?_insertIfNew h

theorem contains_eq_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome :=
  TreeMap.Raw.contains_eq_isSome_getKey? h

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] (h : t.WF) {a : α} :
    (t.get? a).isSome = t.contains a :=
  (contains_eq_isSome_get? h).symm

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none :=
  TreeMap.Raw.getKey?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  TreeMap.Raw.getKey?_eq_none h

@[grind =] theorem get?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  TreeMap.Raw.getKey?_erase h

@[simp]
theorem get?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).get? k = none :=
  TreeMap.Raw.getKey?_erase_self h

theorem get?_beq [TransCmp cmp] (h : t.WF) {k : α} :
    (t.get? k).all (cmp · k = .eq) :=
  TreeMap.Raw.compare_getKey?_self h

theorem get?_congr [TransCmp cmp] (h : t.WF) {k k' : α} (h' : cmp k k' = .eq) :
    t.get? k = t.get? k' :=
  TreeMap.Raw.getKey?_congr h h'

theorem get?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    (h' : t.contains k) :
    t.get? k = some k :=
  TreeMap.Raw.getKey?_eq_some_of_contains h h'

theorem get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    t.get? k = some k :=
  TreeMap.Raw.getKey?_eq_some_of_contains h h'

@[grind =] theorem get_insert [TransCmp cmp] (h : t.WF) {k a : α} {h₁} :
    (t.insert k).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.get a (mem_of_mem_insert' h h₁ h₂) :=
  TreeMap.Raw.getKey_insertIfNew h

@[simp, grind =]
theorem get_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h h') :=
  TreeMap.Raw.getKey_erase h

theorem get?_eq_some_get [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  TreeMap.Raw.getKey?_eq_some_getKey h

theorem get_beq [TransCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    cmp (t.get k h') k = .eq :=
  TreeMap.Raw.compare_getKey_self h h'

theorem get_congr [TransCmp cmp] (h : t.WF) {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq) (h₁ : k₁ ∈ t) :
    t.get k₁ h₁ = t.get k₂ ((mem_congr h h').mp h₁) :=
  TreeMap.Raw.getKey_congr h h' h₁

@[simp, grind =]
theorem get_eq [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) : t.get k h' = k :=
  TreeMap.Raw.getKey_eq h h'

@[simp, grind =]
theorem get!_emptyc {a : α} [Inhabited α] :
    (∅ : TreeSet α cmp).get! a = default :=
  TreeMap.Raw.getKey!_emptyc

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get! a = default :=
  TreeMap.Raw.getKey!_of_isEmpty h

@[grind =] theorem get!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.insert k).get! a = if cmp k a = .eq ∧ ¬ k ∈ t then k else t.get! a :=
  TreeMap.Raw.getKey!_insertIfNew h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.get! a = default :=
  TreeMap.Raw.getKey!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get! a = default :=
  TreeMap.Raw.getKey!_eq_default h

@[grind =] theorem get!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  TreeMap.Raw.getKey!_erase h

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k).get! k = default :=
  TreeMap.Raw.getKey!_erase_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.get? a = some (t.get! a) :=
  TreeMap.Raw.getKey?_eq_some_getKey!_of_contains h

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.get? a = some (t.get! a) :=
  TreeMap.Raw.getKey?_eq_some_getKey! h

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.get! a = (t.get? a).get! :=
  TreeMap.Raw.getKey!_eq_get!_getKey? h

theorem get_eq_get! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {h'} :
    t.get a h' = t.get! a :=
  TreeMap.Raw.getKey_eq_getKey! h

theorem get!_congr [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} (h' : cmp k k' = .eq) :
    t.get! k = t.get! k' :=
  TreeMap.Raw.getKey!_congr h h'

theorem get!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    (h' : t.contains k) :
    t.get! k = k :=
  TreeMap.Raw.getKey!_eq_of_contains h h'

theorem get!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    (h' : k ∈ t) :
    t.get! k = k :=
  TreeMap.Raw.getKey!_eq_of_mem h h'

@[simp, grind =]
theorem getD_emptyc {a : α} {fallback : α} :
    (∅ : TreeSet α cmp).getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_of_isEmpty h

@[grind =] theorem getD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.insert k).getD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getD a fallback :=
  TreeMap.Raw.getKeyD_insertIfNew h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_eq_fallback h

@[grind =] theorem getD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.erase k).getD a fallback =
      if cmp k a = .eq then fallback else t.getD a fallback :=
  TreeMap.Raw.getKeyD_erase h

@[simp]
theorem getD_erase_self [TransCmp cmp] (h : t.WF) {k fallback : α} :
    (t.erase k).getD k fallback = fallback :=
  TreeMap.Raw.getKeyD_erase_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.get? a = some (t.getD a fallback) :=
  TreeMap.Raw.getKey?_eq_some_getKeyD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] (h : t.WF) {a fallback : α} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  TreeMap.Raw.getKey?_eq_some_getKeyD h

theorem getD_eq_getD_get? [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.getD a fallback = (t.get? a).getD fallback :=
  TreeMap.Raw.getKeyD_eq_getD_getKey? h

theorem get_eq_getD [TransCmp cmp] (h : t.WF) {a fallback : α} {h'} :
    t.get a h' = t.getD a fallback :=
  TreeMap.Raw.getKey_eq_getKeyD h

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.get! a = t.getD a default :=
  TreeMap.Raw.getKey!_eq_getKeyD_default h

theorem getD_congr [TransCmp cmp] (h : t.WF) {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getD k fallback = t.getD k' fallback :=
  TreeMap.Raw.getKeyD_congr h h'

theorem getD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k fallback : α}
    (h' : t.contains k) :
    t.getD k fallback = k :=
  TreeMap.Raw.getKeyD_eq_of_contains h h'

theorem getD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k fallback : α} (h' : k ∈ t) :
    t.getD k fallback = k :=
  TreeMap.Raw.getKeyD_eq_of_contains h h'

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  TreeMap.Raw.containsThenInsertIfNew_fst h

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| TreeMap.Raw.containsThenInsertIfNew_snd h

@[simp, grind =]
theorem length_toList [TransCmp cmp] (h : t.WF) :
    t.toList.length = t.size :=
  DTreeMap.Raw.length_keys h

@[simp, grind =]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  DTreeMap.Raw.isEmpty_keys

@[simp, grind =]
theorem contains_toList [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    t.toList.contains k = t.contains k :=
  DTreeMap.Raw.contains_keys h

@[simp, grind =]
theorem mem_toList [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.toList ↔ k ∈ t :=
  DTreeMap.Raw.mem_keys h

theorem distinct_toList [TransCmp cmp] (h : t.WF) :
    t.toList.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.Raw.distinct_keys h

theorem ordered_toList [TransCmp cmp] (h : t.WF) :
    t.toList.Pairwise (fun a b => cmp a b = .lt) :=
  DTreeMap.Raw.ordered_keys h

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m]
    {f : δ → α → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM f init :=
  TreeMap.Raw.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_toList {f : δ → α → δ} {init : δ} :
    t.foldl f init = t.toList.foldl f init :=
  TreeMap.Raw.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m]
    {f : α → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM f init :=
  TreeMap.Raw.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_toList {f : α → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr f init :=
  TreeMap.Raw.foldr_eq_foldr_keys

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t f = t.toList.forM f :=
  TreeMap.Raw.forM_eq_forM_keys

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  TreeMap.Raw.forIn_eq_forIn_keys

end monadic

@[simp, grind =]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton {k : α} :
    t.insertMany [k] = t.insert k :=
  rfl

@[grind _=_] theorem insertMany_cons {l : List α} {k : α} :
    t.insertMany (k :: l) = (t.insert k).insertMany l :=
  ext TreeMap.Raw.insertManyIfNewUnit_cons

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List α} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    (t.insertMany l).contains k = (t.contains k || l.contains k) :=
  TreeMap.Raw.contains_insertManyIfNewUnit_list h

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    k ∈ insertMany t l ↔ k ∈ t ∨ l.contains k :=
  TreeMap.Raw.mem_insertManyIfNewUnit_list h

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertMany t l → k ∈ t :=
  TreeMap.Raw.mem_of_mem_insertManyIfNewUnit_list h contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    get? (insertMany t l) k = none :=
  TreeMap.Raw.getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h not_mem contains_eq_false

theorem get?_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get? (insertMany t l) k' = some k :=
  TreeMap.Raw.getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem get?_insertMany_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} (mem : k ∈ t) :
    get? (insertMany t l) k = get? t k :=
  TreeMap.Raw.getKey?_insertManyIfNewUnit_list_of_mem h mem

theorem get_insertMany_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} {h'} (contains : k ∈ t) :
    get (insertMany t l) k h' = get t k contains :=
  TreeMap.Raw.getKey_insertManyIfNewUnit_list_of_mem h contains

theorem get_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} (not_mem : ¬ k ∈ t)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get (insertMany t l) k' h' = k :=
  TreeMap.Raw.getKey_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] (h : t.WF) {l : List α} {k : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    get! (insertMany t l) k = default :=
  TreeMap.Raw.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h not_mem contains_eq_false

theorem get!_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get! (insertMany t l) k' = k :=
  TreeMap.Raw.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem get!_insertMany_list_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k : α} (mem : k ∈ t):
    get! (insertMany t l) k = get! t k :=
  TreeMap.Raw.getKey!_insertManyIfNewUnit_list_of_mem h mem

theorem getD_insertMany_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k fallback : α}
    (not_mem : ¬ k ∈ t) (contains_eq_false : l.contains k = false) :
    getD (insertMany t l) k fallback = fallback :=
  TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    h not_mem contains_eq_false

theorem getD_insertMany_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (not_mem : ¬ k ∈ t) (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getD (insertMany t l) k' fallback = k :=
  TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem h k_eq not_mem distinct mem

theorem getD_insertMany_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k fallback : α} (mem : k ∈ t) :
    getD (insertMany t l) k fallback = getD t k fallback :=
  TreeMap.Raw.getKeyD_insertManyIfNewUnit_list_of_mem h mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertMany t l).size = t.size + l.length :=
  TreeMap.Raw.size_insertManyIfNewUnit_list h distinct

theorem size_le_size_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List α} :
    t.size ≤ (insertMany t l).size :=
  TreeMap.Raw.size_le_size_insertManyIfNewUnit_list h

grind_pattern size_le_size_insertMany_list => (insertMany t l).size

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List α} :
    (insertMany t l).size ≤ t.size + l.length :=
  TreeMap.Raw.size_insertManyIfNewUnit_list_le h

grind_pattern size_insertMany_list_le => (insertMany t l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF) {l : List α} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  TreeMap.Raw.isEmpty_insertManyIfNewUnit_list h

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List α) cmp =
      (∅ : Raw α cmp) :=
  rfl

@[simp, grind =]
theorem ofList_singleton {k : α} :
    ofList [k] cmp = (∅ : Raw α cmp).insert k :=
  rfl

@[grind _=_]
theorem ofList_cons {hd : α} {tl : List α} :
    ofList (hd :: tl) cmp =
      insertMany ((∅ : Raw α cmp).insert hd) tl :=
  ext TreeMap.Raw.unitOfList_cons

theorem ofList_eq_insertMany_empty {l : List α} :
    ofList l cmp = insertMany (∅ : Raw α cmp) l :=
  match l with
  | [] => by simp
  | hd :: tl => by simp [ofList_cons, insertMany_cons]

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (ofList l cmp).contains k = l.contains k :=
  TreeMap.Raw.contains_unitOfList

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ ofList l cmp ↔ l.contains k := by
  simp [← contains_iff_mem]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get? (ofList l cmp) k = none :=
  TreeMap.Raw.getKey?_unitOfList_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    get? (ofList l cmp) k' = some k :=
  TreeMap.Raw.getKey?_unitOfList_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    get (ofList l cmp) k' h' = k :=
  TreeMap.Raw.getKey_unitOfList_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    get! (ofList l cmp) k = default :=
  TreeMap.Raw.getKey!_unitOfList_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    get! (ofList l cmp) k' = k :=
  TreeMap.Raw.getKey!_unitOfList_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  TreeMap.Raw.getKeyD_unitOfList_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getD (ofList l cmp) k' fallback = k :=
  TreeMap.Raw.getKeyD_unitOfList_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (ofList l cmp).size = l.length :=
  TreeMap.Raw.size_unitOfList distinct

theorem size_ofList_le [TransCmp cmp] {l : List α} :
    (ofList l cmp).size ≤ l.length :=
  TreeMap.Raw.size_unitOfList_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp, grind =]
theorem isEmpty_ofList [TransCmp cmp] {l : List α} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  TreeMap.Raw.isEmpty_unitOfList

section Min

@[simp, grind =]
theorem min?_emptyc :
    (empty : Raw α cmp).min? = none :=
  TreeMap.Raw.minKey?_emptyc

theorem min?_of_isEmpty [TransCmp cmp] (h : t.WF) :
    (he : t.isEmpty) → t.min? = none :=
  TreeMap.Raw.minKey?_of_isEmpty h

@[simp, grind =]
theorem min?_eq_none_iff [TransCmp cmp] (h : t.WF) :
    t.min? = none ↔ t.isEmpty :=
  TreeMap.Raw.minKey?_eq_none_iff h

theorem min?_eq_some_iff_get?_eq_self_and_forall [TransCmp cmp] (h : t.WF) {km} :
    t.min? = some km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.Raw.minKey?_eq_some_iff_getKey?_eq_self_and_forall h

theorem min?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {km} :
    t.min? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  DTreeMap.Raw.minKey?_eq_some_iff_mem_and_forall h

@[simp, grind =]
theorem isNone_min?_eq_isEmpty [TransCmp cmp] (h : t.WF) :
    t.min?.isNone = t.isEmpty :=
  TreeMap.Raw.isNone_minKey?_eq_isEmpty h

@[simp, grind =]
theorem isSome_min?_eq_not_isEmpty [TransCmp cmp] (h : t.WF) :
    t.min?.isSome = !t.isEmpty :=
  TreeMap.Raw.isSome_minKey?_eq_not_isEmpty h

theorem isSome_min?_iff_isEmpty_eq_false [TransCmp cmp] (h : t.WF) :
    t.min?.isSome ↔ t.isEmpty = false :=
  TreeMap.Raw.isSome_minKey?_iff_isEmpty_eq_false h

@[grind =]
theorem min?_insert [TransCmp cmp] (h : t.WF) {k} :
    (t.insert k).min? =
      some (t.min?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  TreeMap.Raw.minKey?_insertIfNew h

theorem isSome_min?_insert [TransCmp cmp] (h : t.WF) {k} :
    (t.insert k).min?.isSome :=
  TreeMap.Raw.isSome_minKey?_insertIfNew h

theorem min?_insert_le_min? [TransCmp cmp] (h : t.WF) {k km kmi} :
    (hkm : t.min? = some km) →
    (hkmi : (t.insert k |>.min? |>.get <| isSome_min?_insert h) = kmi) →
    cmp kmi km |>.isLE :=
  TreeMap.Raw.minKey?_insertIfNew_le_minKey? h

theorem min?_insert_le_self [TransCmp cmp] (h : t.WF) {k kmi} :
    (hkmi : (t.insert k |>.min?.get <| isSome_min?_insert h) = kmi) →
    cmp kmi k |>.isLE :=
  TreeMap.Raw.minKey?_insertIfNew_le_self h

theorem contains_min? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.min? = some km) →
    t.contains km :=
  TreeMap.Raw.contains_minKey? h

theorem isSome_min?_of_contains [TransCmp cmp] (h : t.WF) {k} :
    (hc : t.contains k) → t.min?.isSome :=
  TreeMap.Raw.isSome_minKey?_of_contains h

theorem isSome_min?_of_mem [TransCmp cmp] (h : t.WF) {k} :
    k ∈ t → t.min?.isSome :=
  TreeMap.Raw.isSome_minKey?_of_mem h

theorem min?_le_of_contains [TransCmp cmp] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.min?.get <| isSome_min?_of_contains h hc) = km) →
    cmp km k |>.isLE :=
  TreeMap.Raw.minKey?_le_of_contains h

theorem min?_le_of_mem [TransCmp cmp] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.min?.get <| isSome_min?_of_mem h hc) = km) →
    cmp km k |>.isLE :=
  TreeMap.Raw.minKey?_le_of_mem h

theorem le_min? [TransCmp cmp] {k} (h : t.WF) :
    (∀ k', t.min? = some k' → (cmp k k').isLE) ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  TreeMap.Raw.le_minKey? h

theorem get?_min? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.min? = some km) → t.get? km = some km :=
  TreeMap.Raw.getKey?_minKey? h

theorem get_min? [TransCmp cmp] (h : t.WF) {km hc} :
    (hkm : t.min?.get (isSome_min?_of_contains h hc) = km) → t.get km hc = km :=
  TreeMap.Raw.getKey_minKey? h

theorem get!_min? [TransCmp cmp] [Inhabited α] (h : t.WF) {km} :
    (hkm : t.min? = some km) → t.get! km = km :=
  TreeMap.Raw.getKey!_minKey? h

theorem getD_min? [TransCmp cmp] (h : t.WF) {km fallback} :
    (hkm : t.min? = some km) → t.getD km fallback = km :=
  TreeMap.Raw.getKeyD_minKey? h

@[simp]
theorem min?_bind_get? [TransCmp cmp] (h : t.WF) :
    t.min?.bind t.get? = t.min? :=
  TreeMap.Raw.minKey?_bind_getKey? h

theorem min?_erase_eq_iff_not_compare_eq_min? [TransCmp cmp] (h : t.WF) {k} :
    (t.erase k |>.min?) = t.min? ↔
      ∀ {km}, t.min? = some km → ¬ cmp k km = .eq :=
  TreeMap.Raw.minKey?_erase_eq_iff_not_compare_eq_minKey? h

theorem min?_erase_eq_of_not_compare_eq_min? [TransCmp cmp] (h : t.WF) {k} :
    (hc : ∀ {km}, t.min? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.min?) = t.min? :=
  TreeMap.Raw.minKey?_erase_eq_of_not_compare_eq_minKey? h

theorem isSome_min?_of_isSome_min?_erase [TransCmp cmp] (h : t.WF) {k} :
    (hs : t.erase k |>.min?.isSome) →
    t.min?.isSome :=
  TreeMap.Raw.isSome_minKey?_of_isSome_minKey?_erase h

theorem min?_le_min?_erase [TransCmp cmp] (h : t.WF) {k km kme} :
    (hkme : (t.erase k |>.min?) = some kme) →
    (hkm : (t.min?.get <|
      isSome_min?_of_isSome_min?_erase h <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  TreeMap.Raw.minKey?_le_minKey?_erase h

@[grind =_]
theorem min?_eq_head?_toList [TransCmp cmp] (h : t.WF) :
    t.min? = t.toList.head? :=
  TreeMap.Raw.minKey?_eq_head?_keys h

theorem min?_eq_some_min! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.min? = some t.min! :=
  DTreeMap.Raw.minKey?_eq_some_minKey! h he

theorem min!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty) :
    t.min! = default :=
  DTreeMap.Raw.minKey!_eq_default h he

theorem min!_eq_iff_get?_eq_self_and_forall [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.min! = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKey!_eq_iff_getKey?_eq_self_and_forall h he

theorem min!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.min! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKey!_eq_iff_mem_and_forall h he

@[grind =] theorem min!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k} :
    (t.insert k |>.min!) =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.Raw.minKey!_insertIfNew h

theorem min!_insert_le_min! [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {k} :
    cmp (t.insert k |>.min!) t.min! |>.isLE :=
  DTreeMap.Raw.minKey!_insertIfNew_le_minKey! h he

theorem min!_insert_le_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k} :
    cmp (t.insert k |>.min!) k |>.isLE :=
  DTreeMap.Raw.minKey!_insertIfNew_le_self h

@[grind =] theorem contains_min! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.contains t.min! :=
  DTreeMap.Raw.contains_minKey! h he

@[grind] theorem min!_mem [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.min! ∈ t :=
  DTreeMap.Raw.minKey!_mem h he

theorem min!_le_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : t.contains k) :
    cmp t.min! k |>.isLE :=
  DTreeMap.Raw.minKey!_le_of_contains h hc

theorem min!_le_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : k ∈ t) :
    cmp t.min! k |>.isLE :=
  DTreeMap.Raw.minKey!_le_of_mem h hc

theorem le_min! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {k} :
    (cmp k t.min!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.Raw.le_minKey! h he

theorem get?_min! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.get? t.min! = some t.min! :=
  DTreeMap.Raw.getKey?_minKey! h he

theorem get_min! [TransCmp cmp] [Inhabited α] (h : t.WF) {hc} :
    t.get t.min! hc = t.min! :=
  DTreeMap.Raw.getKey_minKey! h

theorem get!_min! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.get! t.min! = t.min! :=
  DTreeMap.Raw.getKey!_minKey! h he

theorem getD_min! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getD t.min! fallback = t.min! :=
  DTreeMap.Raw.getKeyD_minKey! h he

theorem min!_erase_eq_of_not_compare_min!_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.min! = .eq) :
    (t.erase k |>.min!) = t.min! :=
  DTreeMap.Raw.minKey!_erase_eq_of_not_compare_minKey!_eq h he heq

theorem min!_le_min!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) :
    cmp t.min! (t.erase k |>.min!) |>.isLE :=
  DTreeMap.Raw.minKey!_le_minKey!_erase h he

@[grind =_]
theorem min!_eq_head!_toList [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.min! = t.toList.head! :=
  TreeMap.Raw.minKey!_eq_head!_keys h

theorem min?_eq_some_minD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.min? = some (t.minD fallback) :=
  DTreeMap.Raw.minKey?_eq_some_minKeyD h he

theorem minD_eq_fallback [TransCmp cmp] (h : t.WF) (he : t.isEmpty) {fallback} :
    t.minD fallback = fallback :=
  DTreeMap.Raw.minKeyD_eq_fallback h he

theorem min!_eq_minD_default [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.min! = t.minD default :=
  DTreeMap.Raw.minKey!_eq_minKeyD_default h

theorem minD_eq_iff_get?_eq_self_and_forall [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.minD fallback = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKeyD_eq_iff_getKey?_eq_self_and_forall h he

theorem minD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.minD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  DTreeMap.Raw.minKeyD_eq_iff_mem_and_forall h he

@[grind =] theorem minD_insert [TransCmp cmp] (h : t.WF) {k fallback} :
    (t.insert k |>.minD fallback) =
      t.min?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  DTreeMap.Raw.minKeyD_insertIfNew h

theorem minD_insert_le_minD [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {k fallback} :
    cmp (t.insert k |>.minD fallback) (t.minD fallback) |>.isLE :=
  DTreeMap.Raw.minKeyD_insertIfNew_le_minKeyD h he

theorem minD_insert_le_self [TransCmp cmp] (h : t.WF) {k fallback} :
    cmp (t.insert k |>.minD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_insertIfNew_le_self h

@[grind =] theorem contains_minD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.contains (t.minD fallback) :=
  DTreeMap.Raw.contains_minKeyD h he

@[grind] theorem minD_mem [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.minD fallback ∈ t :=
  DTreeMap.Raw.minKeyD_mem h he

theorem minD_le_of_contains [TransCmp cmp] (h : t.WF) {k} (hc : t.contains k) {fallback} :
    cmp (t.minD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_le_of_contains h hc

theorem minD_le_of_mem [TransCmp cmp] (h : t.WF) {k} (hc : k ∈ t) {fallback} :
    cmp (t.minD fallback) k |>.isLE :=
  DTreeMap.Raw.minKeyD_le_of_mem h hc

theorem le_minD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {k fallback} :
    (cmp k (t.minD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  DTreeMap.Raw.le_minKeyD h he

theorem get?_minD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.get? (t.minD fallback) = some (t.minD fallback) :=
  DTreeMap.Raw.getKey?_minKeyD h he

theorem get_minD [TransCmp cmp] (h : t.WF) {fallback hc} :
    t.get (t.minD fallback) hc = t.minD fallback :=
  DTreeMap.Raw.getKey_minKeyD h

theorem get!_minD [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.get! (t.minD fallback) = t.minD fallback :=
  DTreeMap.Raw.getKey!_minKeyD h he

theorem getD_minD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback fallback'} :
    t.getD (t.minD fallback) fallback' = t.minD fallback :=
  DTreeMap.Raw.getKeyD_minKeyD h he

theorem minD_erase_eq_of_not_compare_minD_eq [TransCmp cmp] (h : t.WF) {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.minD fallback) = .eq) :
    (t.erase k |>.minD fallback) = t.minD fallback :=
  DTreeMap.Raw.minKeyD_erase_eq_of_not_compare_minKeyD_eq h he heq

theorem minD_le_minD_erase [TransCmp cmp] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.minD fallback) (t.erase k |>.minD fallback) |>.isLE :=
  DTreeMap.Raw.minKeyD_le_minKeyD_erase h he

@[grind =_]
theorem minD_eq_headD_toList [TransCmp cmp] (h : t.WF) {fallback} :
    t.minD fallback = t.toList.headD fallback :=
  TreeMap.Raw.minKeyD_eq_headD_keys h

end Min

section Max

@[simp, grind =]
theorem max?_emptyc :
    (empty : Raw α cmp).max? = none :=
  TreeMap.Raw.maxKey?_emptyc

theorem max?_of_isEmpty [TransCmp cmp] (h : t.WF) :
    (he : t.isEmpty) → t.max? = none :=
  TreeMap.Raw.maxKey?_of_isEmpty h

@[simp, grind =]
theorem max?_eq_none_iff [TransCmp cmp] (h : t.WF) :
    t.max? = none ↔ t.isEmpty :=
  TreeMap.Raw.maxKey?_eq_none_iff h

theorem max?_eq_some_iff_get?_eq_self_and_forall [TransCmp cmp] (h : t.WF) {km} :
    t.max? = some km ↔ t.get? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.Raw.maxKey?_eq_some_iff_getKey?_eq_self_and_forall h

theorem max?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {km} :
    t.max? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  DTreeMap.Raw.maxKey?_eq_some_iff_mem_and_forall h

@[simp, grind =]
theorem isNone_max?_eq_isEmpty [TransCmp cmp] (h : t.WF) :
    t.max?.isNone = t.isEmpty :=
  TreeMap.Raw.isNone_maxKey?_eq_isEmpty h

@[simp, grind =]
theorem isSome_max?_eq_not_isEmpty [TransCmp cmp] (h : t.WF) :
    t.max?.isSome = !t.isEmpty :=
  TreeMap.Raw.isSome_maxKey?_eq_not_isEmpty h

theorem isSome_max?_iff_isEmpty_eq_false [TransCmp cmp] (h : t.WF) :
    t.max?.isSome ↔ t.isEmpty = false :=
  TreeMap.Raw.isSome_maxKey?_iff_isEmpty_eq_false h

@[grind =]
theorem max?_insert [TransCmp cmp] (h : t.WF) {k} :
    (t.insert k).max? =
      some (t.max?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  TreeMap.Raw.maxKey?_insertIfNew h

theorem isSome_max?_insert [TransCmp cmp] (h : t.WF) {k} :
    (t.insert k).max?.isSome :=
  TreeMap.Raw.isSome_maxKey?_insertIfNew h

theorem max?_le_max?_insert [TransCmp cmp] (h : t.WF) {k km kmi} :
    (hkm : t.max? = some km) →
    (hkmi : (t.insert k |>.max? |>.get <| isSome_max?_insert h) = kmi) →
    cmp km kmi |>.isLE :=
  TreeMap.Raw.maxKey?_le_maxKey?_insertIfNew h

theorem self_le_max?_insert [TransCmp cmp] (h : t.WF) {k kmi} :
    (hkmi : (t.insert k |>.max?.get <| isSome_max?_insert h) = kmi) →
    cmp k kmi |>.isLE :=
  TreeMap.Raw.self_le_maxKey?_insertIfNew h

theorem contains_max? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.max? = some km) →
    t.contains km :=
  TreeMap.Raw.contains_maxKey? h

theorem isSome_max?_of_contains [TransCmp cmp] (h : t.WF) {k} :
    (hc : t.contains k) → t.max?.isSome :=
  TreeMap.Raw.isSome_maxKey?_of_contains h

theorem isSome_max?_of_mem [TransCmp cmp] (h : t.WF) {k} :
    k ∈ t → t.max?.isSome :=
  TreeMap.Raw.isSome_maxKey?_of_mem h

theorem le_max?_of_contains [TransCmp cmp] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.max?.get <| isSome_max?_of_contains h hc) = km) →
    cmp k km |>.isLE :=
  TreeMap.Raw.le_maxKey?_of_contains h

theorem le_max?_of_mem [TransCmp cmp] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.max?.get <| isSome_max?_of_mem h hc) = km) →
    cmp k km |>.isLE :=
  TreeMap.Raw.le_maxKey?_of_mem h

theorem max?_le [TransCmp cmp] {k} (h : t.WF) :
    (∀ k', t.max? = some k' → (cmp k' k).isLE) ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  TreeMap.Raw.maxKey?_le h

theorem get?_max? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.max? = some km) → t.get? km = some km :=
  TreeMap.Raw.getKey?_maxKey? h

theorem get_max? [TransCmp cmp] (h : t.WF) {km hc} :
    (hkm : t.max?.get (isSome_max?_of_contains h hc) = km) → t.get km hc = km :=
  TreeMap.Raw.getKey_maxKey? h

theorem get!_max? [TransCmp cmp] [Inhabited α] (h : t.WF) {km} :
    (hkm : t.max? = some km) → t.get! km = km :=
  TreeMap.Raw.getKey!_maxKey? h

theorem getD_max? [TransCmp cmp] (h : t.WF) {km fallback} :
    (hkm : t.max? = some km) → t.getD km fallback = km :=
  TreeMap.Raw.getKeyD_maxKey? h

@[simp]
theorem max?_bind_get? [TransCmp cmp] (h : t.WF) :
    t.max?.bind t.get? = t.max? :=
  TreeMap.Raw.maxKey?_bind_getKey? h

theorem max?_erase_eq_iff_not_compare_eq_max? [TransCmp cmp] (h : t.WF) {k} :
    (t.erase k |>.max?) = t.max? ↔
      ∀ {km}, t.max? = some km → ¬ cmp k km = .eq :=
  TreeMap.Raw.maxKey?_erase_eq_iff_not_compare_eq_maxKey? h

theorem max?_erase_eq_of_not_compare_eq_max? [TransCmp cmp] (h : t.WF) {k} :
    (hc : ∀ {km}, t.max? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.max?) = t.max? :=
  TreeMap.Raw.maxKey?_erase_eq_of_not_compare_eq_maxKey? h

theorem isSome_max?_of_isSome_max?_erase [TransCmp cmp] (h : t.WF) {k} :
    (hs : t.erase k |>.max?.isSome) →
    t.max?.isSome :=
  TreeMap.Raw.isSome_maxKey?_of_isSome_maxKey?_erase h

theorem max?_erase_le_max? [TransCmp cmp] (h : t.WF) {k km kme} :
    (hkme : (t.erase k |>.max?) = some kme) →
    (hkm : (t.max?.get <|
      isSome_max?_of_isSome_max?_erase h <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  TreeMap.Raw.maxKey?_erase_le_maxKey? h

@[grind =_] theorem max?_eq_getLast?_toList [TransCmp cmp] (h : t.WF) :
    t.max? = t.toList.getLast? :=
  TreeMap.Raw.maxKey?_eq_getLast?_keys h

@[deprecated max?_eq_getLast?_toList (since := "2025-05-23")]
theorem max?_eq_head?_toList [TransCmp cmp] (h : t.WF) :
    t.max? = t.toList.getLast? :=
  TreeMap.Raw.maxKey?_eq_getLast?_keys h

theorem max?_eq_some_max! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.max? = some t.max! :=
  DTreeMap.Raw.maxKey?_eq_some_maxKey! h he

theorem max!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty) :
    t.max! = default :=
  DTreeMap.Raw.maxKey!_eq_default h he

theorem max!_eq_iff_get?_eq_self_and_forall [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.max! = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKey!_eq_iff_getKey?_eq_self_and_forall h he

theorem max!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.max! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKey!_eq_iff_mem_and_forall h he

@[grind =] theorem max!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k} :
    (t.insert k |>.max!) =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.Raw.maxKey!_insertIfNew h

theorem max!_le_max!_insert [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {k} :
    cmp t.max! (t.insert k |>.max!) |>.isLE :=
  DTreeMap.Raw.maxKey!_le_maxKey!_insertIfNew h he

theorem self_le_max!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k} :
    cmp k (t.insert k |>.max!) |>.isLE :=
  DTreeMap.Raw.self_le_maxKey!_insertIfNew h

@[grind =] theorem contains_max! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.contains t.max! :=
  DTreeMap.Raw.contains_maxKey! h he

@[grind] theorem max!_mem [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.max! ∈ t :=
  DTreeMap.Raw.maxKey!_mem h he

theorem le_max!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : t.contains k) :
    cmp k t.max! |>.isLE :=
  DTreeMap.Raw.le_maxKey!_of_contains h hc

theorem le_max!_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : k ∈ t) :
    cmp k t.max! |>.isLE :=
  DTreeMap.Raw.le_maxKey!_of_mem h hc

theorem max!_le [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {k} :
    (cmp t.max! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.Raw.maxKey!_le h he

theorem get?_max! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.get? t.max! = some t.max! :=
  DTreeMap.Raw.getKey?_maxKey! h he

theorem get_max! [TransCmp cmp] [Inhabited α] (h : t.WF) {hc} :
    t.get t.max! hc = t.max! :=
  DTreeMap.Raw.getKey_maxKey! h

theorem get!_max! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.get! t.max! = t.max! :=
  DTreeMap.Raw.getKey!_maxKey! h he

theorem getD_max! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getD t.max! fallback = t.max! :=
  DTreeMap.Raw.getKeyD_maxKey! h he

theorem max!_erase_eq_of_not_compare_max!_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.max! = .eq) :
    (t.erase k |>.max!) = t.max! :=
  DTreeMap.Raw.maxKey!_erase_eq_of_not_compare_maxKey!_eq h he heq

theorem max!_erase_le_max! [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) :
    cmp (t.erase k |>.max!) t.max! |>.isLE :=
  DTreeMap.Raw.maxKey!_erase_le_maxKey! h he

@[grind =_]
theorem max!_eq_getLast!_toList [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.max! = t.toList.getLast! :=
  TreeMap.Raw.maxKey!_eq_getLast!_keys h

theorem max?_eq_some_maxD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.max? = some (t.maxD fallback) :=
  DTreeMap.Raw.maxKey?_eq_some_maxKeyD h he

theorem maxD_eq_fallback [TransCmp cmp] (h : t.WF) (he : t.isEmpty) {fallback} :
    t.maxD fallback = fallback :=
  DTreeMap.Raw.maxKeyD_eq_fallback h he

theorem max!_eq_maxD_default [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.max! = t.maxD default :=
  DTreeMap.Raw.maxKey!_eq_maxKeyD_default h

theorem maxD_eq_iff_get?_eq_self_and_forall [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.maxD fallback = km ↔ t.get? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKeyD_eq_iff_getKey?_eq_self_and_forall h he

theorem maxD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.maxD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  DTreeMap.Raw.maxKeyD_eq_iff_mem_and_forall h he

@[grind =] theorem maxD_insert [TransCmp cmp] (h : t.WF) {k fallback} :
    (t.insert k |>.maxD fallback) =
      t.max?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  DTreeMap.Raw.maxKeyD_insertIfNew h

theorem maxD_le_maxD_insert [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {k fallback} :
    cmp (t.maxD fallback) (t.insert k |>.maxD fallback) |>.isLE :=
  DTreeMap.Raw.maxKeyD_le_maxKeyD_insertIfNew h he

theorem self_le_maxD_insert [TransCmp cmp] (h : t.WF) {k fallback} :
    cmp k (t.insert k |>.maxD fallback) |>.isLE :=
  DTreeMap.Raw.self_le_maxKeyD_insertIfNew h

@[grind =] theorem contains_maxD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.contains (t.maxD fallback) :=
  DTreeMap.Raw.contains_maxKeyD h he

@[grind] theorem maxD_mem [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.maxD fallback ∈ t :=
  DTreeMap.Raw.maxKeyD_mem h he

theorem le_maxD_of_contains [TransCmp cmp] (h : t.WF) {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxD fallback) |>.isLE :=
  DTreeMap.Raw.le_maxKeyD_of_contains h hc

theorem le_maxD_of_mem [TransCmp cmp] (h : t.WF) {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxD fallback) |>.isLE :=
  DTreeMap.Raw.le_maxKeyD_of_mem h hc

theorem maxD_le [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {k fallback} :
    (cmp (t.maxD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  DTreeMap.Raw.maxKeyD_le h he

theorem get?_maxD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.get? (t.maxD fallback) = some (t.maxD fallback) :=
  DTreeMap.Raw.getKey?_maxKeyD h he

theorem get_maxD [TransCmp cmp] (h : t.WF) {fallback hc} :
    t.get (t.maxD fallback) hc = t.maxD fallback :=
  DTreeMap.Raw.getKey_maxKeyD h

theorem get!_maxD [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.get! (t.maxD fallback) = t.maxD fallback :=
  DTreeMap.Raw.getKey!_maxKeyD h he

theorem getD_maxD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback fallback'} :
    t.getD (t.maxD fallback) fallback' = t.maxD fallback :=
  DTreeMap.Raw.getKeyD_maxKeyD h he

theorem maxD_erase_eq_of_not_compare_maxD_eq [TransCmp cmp] (h : t.WF) {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.maxD fallback) = .eq) :
    (t.erase k |>.maxD fallback) = t.maxD fallback :=
  DTreeMap.Raw.maxKeyD_erase_eq_of_not_compare_maxKeyD_eq h he heq

theorem maxD_erase_le_maxD [TransCmp cmp] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.erase k |>.maxD fallback) (t.maxD fallback) |>.isLE :=
  DTreeMap.Raw.maxKeyD_erase_le_maxKeyD h he

@[grind =_]
theorem maxD_eq_getLastD_toList [TransCmp cmp] (h : t.WF) {fallback} :
    t.maxD fallback = t.toList.getLastD fallback :=
  TreeMap.Raw.maxKeyD_eq_getLastD_keys h

end Max

namespace Equiv

variable {t₁ t₂ t₃ t₄ : Raw α cmp} {δ : Type w} {m : Type w → Type w'}

@[refl, simp] theorem rfl : Equiv t t := ⟨.rfl⟩

@[symm] theorem symm : Equiv t₁ t₂ → Equiv t₂ t₁
  | ⟨h⟩ => ⟨h.symm⟩

theorem trans : Equiv t₁ t₂ → Equiv t₂ t₃ → Equiv t₁ t₃
  | ⟨h⟩, ⟨h'⟩ => ⟨h.trans h'⟩

instance instTrans : @Trans (Raw α cmp) _ _ Equiv Equiv Equiv := ⟨trans⟩

theorem comm : t₁ ~m t₂ ↔ t₂ ~m t₁ := ⟨symm, symm⟩
theorem congr_left (h : t₁ ~m t₂) : t₁ ~m t₃ ↔ t₂ ~m t₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : t₁ ~m t₂) : t₃ ~m t₁ ↔ t₃ ~m t₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

-- congruence lemmas

theorem isEmpty_eq (h : t₁ ~m t₂) : t₁.isEmpty = t₂.isEmpty :=
  h.1.isEmpty_eq

theorem contains_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.contains k = t₂.contains k :=
  h.1.contains_eq h₁.1 h₂.1

theorem mem_iff [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    k ∈ t₁ ↔ k ∈ t₂ :=
  h.1.mem_iff h₁.1 h₂.1

theorem size_eq (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.size = t₂.size :=
  h.1.size_eq h₁.1 h₂.1

theorem get?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.get? k = t₂.get? k :=
  h.1.getKey?_eq h₁.1 h₂.1

theorem getKey_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.get k hk = t₂.get k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.getKey_eq h₁.1 h₂.1

theorem getKey!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.get! k = t₂.get! k :=
  h.1.getKey!_eq h₁.1 h₂.1

theorem getKeyD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getD k fallback = t₂.getD k fallback :=
  h.1.getKeyD_eq h₁.1 h₂.1

theorem toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.toList = t₂.toList :=
  h.1.keys_eq h₁.1 h₂.1

theorem toArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.toArray = t₂.toArray :=
  h.1.keysArray_eq h₁.1 h₂.1

theorem foldlM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → α → m δ}
    {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.foldlM f init = t₂.foldlM f init :=
  h.1.foldlM_eq h₁.1 h₂.1

theorem foldl_eq [TransCmp cmp] {f : δ → α → δ} {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) :
    t₁.foldl f init = t₂.foldl f init :=
  h.1.foldl_eq h₁.1 h₂.1

theorem foldrM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → δ → m δ}
    {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.foldrM f init = t₂.foldrM f init :=
  h.1.foldrM_eq h₁.1 h₂.1

theorem foldr_eq [TransCmp cmp] {f : α → δ → δ} {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) :
    t₁.foldr f init = t₂.foldr f init :=
  h.1.foldr_eq h₁.1 h₂.1

theorem forIn_eq [TransCmp cmp] [Monad m] [LawfulMonad m]
    {b : δ} {f : α → δ → m (ForInStep δ)} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    ForIn.forIn t₁ b f = ForIn.forIn t₂ b f :=
  h.1.forIn_eq h₁.1 h₂.1 (f := fun x => f x.1)

theorem forM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : α → m PUnit}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    ForM.forM t₁ f = ForM.forM t₂ f :=
  h.1.forM_eq h₁.1 h₂.1 (f := fun x => f x.1)

theorem any_eq [TransCmp cmp] {p : α → Bool} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.any p = t₂.any p :=
  h.1.any_eq h₁.1 h₂.1

theorem all_eq [TransCmp cmp] {p : α → Bool} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.all p = t₂.all p :=
  h.1.all_eq h₁.1 h₂.1

theorem min?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.min? = t₂.min? :=
  h.1.minKey?_eq h₁.1 h₂.1

theorem min!_eq [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.min! = t₂.min! :=
  h.1.minKey!_eq h₁.1 h₂.1

theorem minD_eq [TransCmp cmp] {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minD fallback = t₂.minD fallback :=
  h.1.minKeyD_eq h₁.1 h₂.1

theorem max?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.max? = t₂.max? :=
  h.1.maxKey?_eq h₁.1 h₂.1

theorem max!_eq [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.max! = t₂.max! :=
  h.1.maxKey!_eq h₁.1 h₂.1

theorem maxD_eq [TransCmp cmp] {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxD fallback = t₂.maxD fallback :=
  h.1.maxKeyD_eq h₁.1 h₂.1

theorem atIdx?_eq [TransCmp cmp] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.atIdx? i = t₂.atIdx? i :=
  h.1.keyAtIdx?_eq h₁.1 h₂.1

theorem atIdx!_eq [TransCmp cmp] [Inhabited α] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.atIdx! i = t₂.atIdx! i :=
  h.1.keyAtIdx!_eq h₁.1 h₂.1

theorem atIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.atIdxD i fallback = t₂.atIdxD i fallback :=
  h.1.keyAtIdxD_eq h₁.1 h₂.1

theorem getGE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getGE? k = t₂.getGE? k :=
  h.1.getKeyGE?_eq h₁.1 h₂.1

theorem getGE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getGE! k = t₂.getGE! k :=
  h.1.getKeyGE!_eq h₁.1 h₂.1

theorem getGED_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getGED k fallback = t₂.getGED k fallback :=
  h.1.getKeyGED_eq h₁.1 h₂.1

theorem getGT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getGT? k = t₂.getGT? k :=
  h.1.getKeyGT?_eq h₁.1 h₂.1

theorem getGT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getGT! k = t₂.getGT! k :=
  h.1.getKeyGT!_eq h₁.1 h₂.1

theorem getGTD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getGTD k fallback = t₂.getGTD k fallback :=
  h.1.getKeyGTD_eq h₁.1 h₂.1

theorem getLE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getLE? k = t₂.getLE? k :=
  h.1.getKeyLE?_eq h₁.1 h₂.1

theorem getLE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getLE! k = t₂.getLE! k :=
  h.1.getKeyLE!_eq h₁.1 h₂.1

theorem getLED_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getLED k fallback = t₂.getLED k fallback :=
  h.1.getKeyLED_eq h₁.1 h₂.1

theorem getLT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getLT? k = t₂.getLT? k :=
  h.1.getKeyLT?_eq h₁.1 h₂.1

theorem getLT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getLT! k = t₂.getLT! k :=
  h.1.getKeyLT!_eq h₁.1 h₂.1

theorem getLTD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getLTD k fallback = t₂.getLTD k fallback :=
  h.1.getKeyLTD_eq h₁.1 h₂.1

theorem insert [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (k : α) :
    t₁.insert k ~m t₂.insert k :=
  ⟨h.1.insertIfNew h₁.1 h₂.1 k ()⟩

theorem erase [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (k : α) :
    t₁.erase k ~m t₂.erase k :=
  ⟨h.1.erase h₁.1 h₂.1 k⟩

theorem filter (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (f : α → Bool) :
    t₁.filter f ~m t₂.filter f :=
  ⟨h.1.filter h₁.1 h₂.1 _⟩

theorem insertMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (l : List α) : t₁.insertMany l ~m t₂.insertMany l :=
  ⟨h.1.insertManyIfNewUnit_list h₁.1 h₂.1 l⟩

theorem eraseMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (l : List α) :
    t₁.eraseMany l ~m t₂.eraseMany l :=
  ⟨h.1.eraseMany_list h₁.1 h₂.1 l⟩

theorem merge [TransCmp cmp] [LawfulEqCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h₃ : t₃.WF) (h₄ : t₄.WF)
    (h : t₁ ~m t₂) (h' : t₃ ~m t₄) :
    t₁.merge t₃ ~m t₂.merge t₄ :=
  ⟨h.1.mergeWith h₁.1 h₂.1 h₃.1 h₄.1 _ h'.1⟩

-- extensionalities

theorem of_forall_get?_eq [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : ∀ k, t₁.get? k = t₂.get? k) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey?_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_contains_eq [TransCmp cmp] [LawfulEqCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ ~m t₂ :=
  ⟨.of_forall_contains_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_mem_iff [TransCmp cmp] [LawfulEqCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ ~m t₂ :=
  ⟨.of_forall_mem_unit_iff h₁.1 h₂.1 h⟩

end Equiv

section Equiv

variable {t₁ t₂ : Raw α cmp}

private theorem equiv_iff : t₁ ~m t₂ ↔ t₁.1.Equiv t₂.1 :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem equiv_empty_iff_isEmpty : t ~m empty ↔ t.isEmpty :=
  equiv_iff.trans TreeMap.Raw.equiv_empty_iff_isEmpty

theorem empty_equiv_iff_isEmpty : empty ~m t ↔ t.isEmpty :=
  equiv_iff.trans TreeMap.Raw.empty_equiv_iff_isEmpty

theorem equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList :=
  equiv_iff.trans TreeMap.Raw.equiv_iff_keys_unit_perm

theorem Equiv.of_toList_perm (h : t₁.toList.Perm t₂.toList) : t₁ ~m t₂ :=
  ⟨.of_keys_unit_perm h⟩

theorem equiv_iff_toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁ ~m t₂ ↔ t₁.toList = t₂.toList :=
  equiv_iff.trans (TreeMap.Raw.equiv_iff_keys_unit_eq h₁.1 h₂.1)

end Equiv

end Std.TreeSet.Raw
