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

universe u v w

namespace Std.TreeSet.Raw

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeSet.Raw α cmp}

private theorem ext {t t' : Raw α cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : Raw α cmp).isEmpty :=
  TreeMap.Raw.isEmpty_emptyc

@[simp]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).isEmpty = false :=
  TreeMap.Raw.isEmpty_insertIfNew h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  TreeMap.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  TreeMap.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  TreeMap.Raw.mem_congr h hab

@[simp]
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

@[simp]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  TreeMap.Raw.contains_insertIfNew h

@[simp]
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

@[simp]
theorem size_emptyc : (∅ : Raw α cmp).size = 0 :=
  TreeMap.Raw.size_emptyc

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  TreeMap.Raw.isEmpty_eq_size_eq_zero h.out

theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).size = if t.contains k then t.size else t.size + 1 :=
  TreeMap.Raw.size_insertIfNew h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.insert k).size :=
  TreeMap.Raw.size_le_size_insertIfNew h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.insert k).size ≤ t.size + 1 :=
  TreeMap.Raw.size_insertIfNew_le h

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : Raw α cmp).erase k = ∅ :=
  ext <| TreeMap.Raw.erase_emptyc

@[simp]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  TreeMap.Raw.isEmpty_erase h

@[simp]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  TreeMap.Raw.contains_erase h

@[simp]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  TreeMap.Raw.mem_erase h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  TreeMap.Raw.contains_of_contains_erase h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  TreeMap.Raw.mem_of_mem_erase h

theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  TreeMap.Raw.size_erase h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  TreeMap.Raw.size_erase_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  TreeMap.Raw.size_le_size_erase h

@[simp]
theorem get?_emptyc {a : α} : (∅ : TreeSet α cmp).get? a = none :=
  TreeMap.Raw.getKey?_emptyc

theorem get?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none :=
  TreeMap.Raw.getKey?_of_isEmpty h

theorem get?_insert [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).get? a = if cmp k a = .eq ∧ ¬k ∈ t then some k else t.get? a :=
  TreeMap.Raw.getKey?_insertIfNew h

theorem contains_eq_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome :=
  TreeMap.Raw.contains_eq_isSome_getKey? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none :=
  TreeMap.Raw.getKey?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  TreeMap.Raw.getKey?_eq_none h

theorem get?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  TreeMap.Raw.getKey?_erase h

@[simp]
theorem get?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).get? k = none :=
  TreeMap.Raw.getKey?_erase_self h

theorem get_insert [TransCmp cmp] (h : t.WF) {k a : α} {h₁} :
    (t.insert k).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.get a (mem_of_mem_insert' h h₁ h₂) :=
  TreeMap.Raw.getKey_insertIfNew h

@[simp]
theorem get_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h h') :=
  TreeMap.Raw.getKey_erase h

theorem get?_eq_some_get [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  TreeMap.Raw.getKey?_eq_some_getKey h

@[simp]
theorem get!_emptyc {a : α} [Inhabited α] :
    (∅ : TreeSet α cmp).get! a = default :=
  TreeMap.Raw.getKey!_emptyc

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get! a = default :=
  TreeMap.Raw.getKey!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.insert k).get! a = if cmp k a = .eq ∧ ¬ k ∈ t then k else t.get! a :=
  TreeMap.Raw.getKey!_insertIfNew h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.get! a = default :=
  TreeMap.Raw.getKey!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get! a = default :=
  TreeMap.Raw.getKey!_eq_default h

theorem get!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
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

@[simp]
theorem getD_emptyc {a : α} {fallback : α} :
    (∅ : TreeSet α cmp).getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_emptyc

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_of_isEmpty h

theorem getD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.insert k).getD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getD a fallback :=
  TreeMap.Raw.getKeyD_insertIfNew h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  TreeMap.Raw.getKeyD_eq_fallback h

theorem getD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
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

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} :
    (t.containsThenInsert k).1 = t.contains k :=
  TreeMap.Raw.containsThenInsertIfNew_fst h

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} :
    (t.containsThenInsert k).2 = t.insert k :=
  ext <| TreeMap.Raw.containsThenInsertIfNew_snd h

@[simp]
theorem length_toList [TransCmp cmp] (h : t.WF) :
    t.toList.length = t.size :=
  DTreeMap.Raw.length_keys h

@[simp]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  DTreeMap.Raw.isEmpty_keys

@[simp]
theorem contains_toList [BEq α] [LawfulBEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    t.toList.contains k = t.contains k :=
  DTreeMap.Raw.contains_keys h

@[simp]
theorem mem_toList [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.toList ↔ k ∈ t :=
  DTreeMap.Raw.mem_keys h

theorem distinct_toList [TransCmp cmp] (h : t.WF) :
    t.toList.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  DTreeMap.Raw.distinct_keys h

section monadic

variable {δ : Type w} {m : Type w → Type w}

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

@[simp]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp]
theorem insertMany_list_singleton {k : α} :
    t.insertMany [k] = t.insert k :=
  rfl

theorem insertMany_cons {l : List α} {k : α} :
    t.insertMany (k :: l) = (t.insert k).insertMany l :=
  ext TreeMap.Raw.insertManyIfNewUnit_cons

@[simp]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    (t.insertMany l).contains k = (t.contains k || l.contains k) :=
  TreeMap.Raw.contains_insertManyIfNewUnit_list h

@[simp]
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

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List α} :
    (insertMany t l).size ≤ t.size + l.length :=
  TreeMap.Raw.size_insertManyIfNewUnit_list_le h

@[simp]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF) {l : List α} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  TreeMap.Raw.isEmpty_insertManyIfNewUnit_list h

@[simp]
theorem ofList_nil :
    ofList ([] : List α) cmp =
      (∅ : Raw α cmp) :=
  rfl

@[simp]
theorem ofList_singleton {k : α} :
    ofList [k] cmp = (∅ : Raw α cmp).insert k :=
  rfl

theorem ofList_cons {hd : α} {tl : List α} :
    ofList (hd :: tl) cmp =
      insertMany ((∅ : Raw α cmp).insert hd) tl :=
  ext TreeMap.Raw.unitOfList_cons

@[simp]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (ofList l cmp).contains k = l.contains k :=
  TreeMap.Raw.contains_unitOfList

@[simp]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ ofList l cmp ↔ l.contains k := by
  simp [mem_iff_contains]

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

@[simp]
theorem isEmpty_ofList [TransCmp cmp] {l : List α} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  TreeMap.Raw.isEmpty_unitOfList

end Std.TreeSet.Raw
