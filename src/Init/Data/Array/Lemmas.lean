/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Init.Data.Nat.Lemmas
import Init.Data.List.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Modify
import Init.Data.List.Nat.Basic
import Init.Data.List.Monadic
import Init.Data.List.OfFn
import Init.Data.Array.Mem
import Init.Data.Array.DecidableEq
import Init.Data.Array.Lex.Basic
import Init.Data.Range.Lemmas
import Init.TacticsExtra
import Init.Data.List.ToArray

/-!
## Theorems about `Array`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/-! ## Preliminaries -/

/-! ### toList -/

@[simp] theorem toList_inj {xs ys : Array α} : xs.toList = ys.toList ↔ xs = ys := by
  cases xs; cases ys; simp

@[simp] theorem toList_eq_nil_iff (xs : Array α) : xs.toList = [] ↔ xs = #[] := by
  cases xs <;> simp

@[simp] theorem mem_toList_iff (a : α) (xs : Array α) : a ∈ xs.toList ↔ a ∈ xs := by
  cases xs <;> simp

@[simp] theorem length_toList {xs : Array α} : xs.toList.length = xs.size := rfl

theorem eq_toArray : xs = List.toArray as ↔ xs.toList = as := by
  cases xs
  simp

theorem toArray_eq : List.toArray as = xs ↔ as = xs.toList := by
  cases xs
  simp

/-! ### empty -/

@[simp] theorem empty_eq {xs : Array α} : #[] = xs ↔ xs = #[] := by
  cases xs <;> simp

theorem size_empty : (#[] : Array α).size = 0 := rfl

@[simp] theorem mkEmpty_eq (α n) : @mkEmpty α n = #[] := rfl

/-! ### size -/

theorem eq_empty_of_size_eq_zero (h : xs.size = 0) : xs = #[] := by
  cases xs
  simp_all

theorem ne_empty_of_size_eq_add_one (h : xs.size = n + 1) : xs ≠ #[] := by
  cases xs
  simpa using List.ne_nil_of_length_eq_add_one h

theorem ne_empty_of_size_pos (h : 0 < xs.size) : xs ≠ #[] := by
  cases xs
  simpa using List.ne_nil_of_length_pos h

theorem size_eq_zero_iff : xs.size = 0 ↔ xs = #[] :=
  ⟨eq_empty_of_size_eq_zero, fun h => h ▸ rfl⟩

@[deprecated size_eq_zero_iff (since := "2025-02-24")]
abbrev size_eq_zero := @size_eq_zero_iff

theorem eq_empty_iff_size_eq_zero : xs = #[] ↔ xs.size = 0 :=
  size_eq_zero_iff.symm

theorem size_pos_of_mem {a : α} {xs : Array α} (h : a ∈ xs) : 0 < xs.size := by
  cases xs
  simp only [mem_toArray] at h
  simpa using List.length_pos_of_mem h

theorem exists_mem_of_size_pos {xs : Array α} (h : 0 < xs.size) : ∃ a, a ∈ xs := by
  cases xs
  simpa using List.exists_mem_of_length_pos h

theorem size_pos_iff_exists_mem {xs : Array α} : 0 < xs.size ↔ ∃ a, a ∈ xs :=
  ⟨exists_mem_of_size_pos, fun ⟨_, h⟩ => size_pos_of_mem h⟩

theorem exists_mem_of_size_eq_add_one {xs : Array α} (h : xs.size = n + 1) : ∃ a, a ∈ xs := by
  cases xs
  simpa using List.exists_mem_of_length_eq_add_one h

theorem size_pos_iff {xs : Array α} : 0 < xs.size ↔ xs ≠ #[] :=
  Nat.pos_iff_ne_zero.trans (not_congr size_eq_zero_iff)

@[deprecated size_pos_iff (since := "2025-02-24")]
abbrev size_pos := @size_pos_iff

theorem size_eq_one_iff {xs : Array α} : xs.size = 1 ↔ ∃ a, xs = #[a] := by
  cases xs
  simpa using List.length_eq_one_iff

@[deprecated size_eq_one_iff (since := "2025-02-24")]
abbrev size_eq_one := @size_eq_one_iff

/-! ### push -/

@[simp] theorem push_ne_empty {a : α} {xs : Array α} : xs.push a ≠ #[] := by
  cases xs
  simp

@[simp] theorem push_ne_self {a : α} {xs : Array α} : xs.push a ≠ xs := by
  cases xs
  simp

@[simp] theorem ne_push_self {a : α} {xs : Array α} : xs ≠ xs.push a := by
  rw [ne_eq, eq_comm]
  simp

theorem back_eq_of_push_eq {a b : α} {xs ys : Array α} (h : xs.push a = ys.push b) : a = b := by
  cases xs
  cases ys
  simp only [List.push_toArray, mk.injEq] at h
  replace h := List.append_inj_right' h (by simp)
  simpa using h

theorem pop_eq_of_push_eq {a b : α} {xs ys : Array α} (h : xs.push a = ys.push b) : xs = ys := by
  cases xs
  cases ys
  simp at h
  replace h := List.append_inj_left' h (by simp)
  simp [h]

theorem push_inj_left {a : α} {xs ys : Array α} : xs.push a = ys.push a ↔ xs = ys :=
  ⟨pop_eq_of_push_eq, fun h => by simp [h]⟩

theorem push_inj_right {a b : α} {xs : Array α} : xs.push a = xs.push b ↔ a = b :=
  ⟨back_eq_of_push_eq, fun h => by simp [h]⟩

theorem push_eq_push {a b : α} {xs ys : Array α} : xs.push a = ys.push b ↔ a = b ∧ xs = ys := by
  constructor
  · intro h
    exact ⟨back_eq_of_push_eq h, pop_eq_of_push_eq h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem push_eq_append_singleton (as : Array α) (x) : as.push x = as ++ #[x] := rfl

theorem exists_push_of_ne_empty {xs : Array α} (h : xs ≠ #[]) :
    ∃ (ys : Array α) (a : α), xs = ys.push a := by
  rcases xs with ⟨xs⟩
  simp only [ne_eq, mk.injEq] at h
  exact ⟨(xs.take (xs.length - 1)).toArray, xs.getLast h, by simp⟩

theorem ne_empty_iff_exists_push {xs : Array α} :
    xs ≠ #[] ↔ ∃ (ys : Array α) (a : α), xs = ys.push a :=
  ⟨exists_push_of_ne_empty, fun ⟨_, _, eq⟩ => eq.symm ▸ push_ne_empty⟩

theorem exists_push_of_size_pos {xs : Array α} (h : 0 < xs.size) :
    ∃ (ys : Array α) (a : α), xs = ys.push a := by
  replace h : xs ≠ #[] := size_pos_iff.mp h
  exact exists_push_of_ne_empty h

theorem size_pos_iff_exists_push {xs : Array α} :
    0 < xs.size ↔ ∃ (ys : Array α) (a : α), xs = ys.push a :=
  ⟨exists_push_of_size_pos, fun ⟨_, _, eq⟩ => by simp [eq]⟩

theorem exists_push_of_size_eq_add_one {xs : Array α} (h : xs.size = n + 1) :
    ∃ (ys : Array α) (a : α), xs = ys.push a :=
  exists_push_of_size_pos (by simp [h])

theorem singleton_inj : #[a] = #[b] ↔ a = b := by
  simp

/-! ### mkArray -/

@[simp] theorem size_mkArray (n : Nat) (v : α) : (mkArray n v).size = n :=
  List.length_replicate ..

@[simp] theorem toList_mkArray : (mkArray n a).toList = List.replicate n a := by
  simp only [mkArray]

@[simp] theorem mkArray_zero : mkArray 0 a = #[] := rfl

theorem mkArray_succ : mkArray (n + 1) a = (mkArray n a).push a := by
  apply toList_inj.1
  simp [List.replicate_succ']

@[simp] theorem getElem_mkArray (n : Nat) (v : α) (h : i < (mkArray n v).size) :
    (mkArray n v)[i] = v := by simp [← getElem_toList]

theorem getElem?_mkArray (n : Nat) (v : α) (i : Nat) :
    (mkArray n v)[i]? = if i < n then some v else none := by
  simp [getElem?_def]

/-! ## L[i] and L[i]? -/

@[simp] theorem getElem?_eq_none_iff {xs : Array α} : xs[i]? = none ↔ xs.size ≤ i := by
  by_cases h : i < xs.size
  · simp [getElem?_pos, h]
  · rw [getElem?_neg xs i h]
    simp_all

@[simp] theorem none_eq_getElem?_iff {xs : Array α} {i : Nat} : none = xs[i]? ↔ xs.size ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none {xs : Array α} (h : xs.size ≤ i) : xs[i]? = none := by
  simp [getElem?_eq_none_iff, h]

@[simp] theorem getElem?_eq_getElem {xs : Array α} {i : Nat} (h : i < xs.size) : xs[i]? = some xs[i] :=
  getElem?_pos ..

theorem getElem?_eq_some_iff {xs : Array α} : xs[i]? = some b ↔ ∃ h : i < xs.size, xs[i] = b := by
  simp [getElem?_def]

theorem some_eq_getElem?_iff {xs : Array α} : some b = xs[i]? ↔ ∃ h : i < xs.size, xs[i] = b := by
  rw [eq_comm, getElem?_eq_some_iff]

@[simp] theorem some_getElem_eq_getElem?_iff (xs : Array α) (i : Nat) (h : i < xs.size) :
    (some xs[i] = xs[i]?) ↔ True := by
  simp [h]

@[simp] theorem getElem?_eq_some_getElem_iff (xs : Array α) (i : Nat) (h : i < xs.size) :
    (xs[i]? = some xs[i]) ↔ True := by
  simp [h]

theorem getElem_eq_iff {xs : Array α} {i : Nat} {h : i < xs.size} : xs[i] = x ↔ xs[i]? = some x := by
  simp only [getElem?_eq_some_iff]
  exact ⟨fun w => ⟨h, w⟩, fun h => h.2⟩

theorem getElem_eq_getElem?_get (xs : Array α) (i : Nat) (h : i < xs.size) :
    xs[i] = xs[i]?.get (by simp [getElem?_eq_getElem, h]) := by
  simp [getElem_eq_iff]

theorem getD_getElem? (xs : Array α) (i : Nat) (d : α) :
    xs[i]?.getD d = if p : i < xs.size then xs[i]'p else d := by
  if h : i < xs.size then
    simp [h, getElem?_def]
  else
    have p : i ≥ xs.size := Nat.le_of_not_gt h
    simp [getElem?_eq_none p, h]

@[simp] theorem getElem?_empty {i : Nat} : (#[] : Array α)[i]? = none := rfl

theorem getElem_push_lt (xs : Array α) (x : α) (i : Nat) (h : i < xs.size) :
    have : i < (xs.push x).size := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (xs.push x)[i] = xs[i] := by
  simp only [push, ← getElem_toList, List.concat_eq_append, List.getElem_append_left, h]

@[simp] theorem getElem_push_eq (xs : Array α) (x : α) : (xs.push x)[xs.size] = x := by
  simp only [push, ← getElem_toList, List.concat_eq_append]
  rw [List.getElem_append_right] <;> simp [← getElem_toList, Nat.zero_lt_one]

theorem getElem_push (xs : Array α) (x : α) (i : Nat) (h : i < (xs.push x).size) :
    (xs.push x)[i] = if h : i < xs.size then xs[i] else x := by
  by_cases h' : i < xs.size
  · simp [getElem_push_lt, h']
  · simp at h
    simp [getElem_push_lt, Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h')]

theorem getElem?_push {xs : Array α} {x} : (xs.push x)[i]? = if i = xs.size then some x else xs[i]? := by
  simp [getElem?_def, getElem_push]
  (repeat' split) <;> first | rfl | omega

@[simp] theorem getElem?_push_size {xs : Array α} {x} : (xs.push x)[xs.size]? = some x := by
  simp [getElem?_push]

@[simp] theorem getElem_singleton (a : α) (h : i < 1) : #[a][i] = a :=
  match i, h with
  | 0, _ => rfl

theorem getElem?_singleton (a : α) (i : Nat) : #[a][i]? = if i = 0 then some a else none := by
  simp [List.getElem?_singleton]

theorem ext_getElem? {xs ys : Array α} (h : ∀ i : Nat, xs[i]? = ys[i]?) : xs = ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simpa using List.ext_getElem? (by simpa using h)

/-! ### mem -/

theorem not_mem_empty (a : α) : ¬ a ∈ #[] := by simp

@[simp] theorem mem_push {xs : Array α} {x y : α} : x ∈ xs.push y ↔ x ∈ xs ∨ x = y := by
  simp only [mem_def]
  simp

theorem mem_push_self {xs : Array α} {x : α} : x ∈ xs.push x :=
  mem_push.2 (Or.inr rfl)

theorem eq_push_append_of_mem {xs : Array α} {x : α} (h : x ∈ xs) :
    ∃ (as bs : Array α), xs = as.push x ++ bs ∧ x ∉ as:= by
  rcases xs with ⟨xs⟩
  obtain ⟨as, bs, h, w⟩ := List.eq_append_cons_of_mem (mem_def.1 h)
  simp only at h
  obtain rfl := h
  exact ⟨as.toArray, bs.toArray, by simp, by simpa using w⟩

theorem mem_push_of_mem {xs : Array α} {x : α} (y : α) (h : x ∈ xs) : x ∈ xs.push y :=
  mem_push.2 (Or.inl h)

theorem exists_mem_of_ne_empty (xs : Array α) (h : xs ≠ #[]) : ∃ x, x ∈ xs := by
  simpa using List.exists_mem_of_ne_nil xs.toList (by simpa using h)

theorem eq_empty_iff_forall_not_mem {xs : Array α} : xs = #[] ↔ ∀ a, a ∉ xs := by
  cases xs
  simp [List.eq_nil_iff_forall_not_mem]

@[simp] theorem mem_dite_empty_left {x : α} [Decidable p] {xs : ¬ p → Array α} :
    (x ∈ if h : p then #[] else xs h) ↔ ∃ h : ¬ p, x ∈ xs h := by
  split <;> simp_all

@[simp] theorem mem_dite_empty_right {x : α} [Decidable p] {xs : p → Array α} :
    (x ∈ if h : p then xs h else #[]) ↔ ∃ h : p, x ∈ xs h := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_left {x : α} [Decidable p] {xs : Array α} :
    (x ∈ if p then #[] else xs) ↔ ¬ p ∧ x ∈ xs := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_right {x : α} [Decidable p] {xs : Array α} :
    (x ∈ if p then xs else #[]) ↔ p ∧ x ∈ xs := by
  split <;> simp_all

theorem eq_of_mem_singleton (h : a ∈ #[b]) : a = b := by
  simpa using h

@[simp] theorem mem_singleton {a b : α} : a ∈ #[b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem forall_mem_push {p : α → Prop} {xs : Array α} {a : α} :
    (∀ x, x ∈ xs.push a → p x) ↔ p a ∧ ∀ x, x ∈ xs → p x := by
  cases xs
  simp [or_comm, forall_eq_or_imp]

theorem forall_mem_ne {a : α} {xs : Array α} : (∀ a' : α, a' ∈ xs → ¬a = a') ↔ a ∉ xs :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem forall_mem_ne' {a : α} {xs : Array α} : (∀ a' : α, a' ∈ xs → ¬a' = a) ↔ a ∉ xs :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem exists_mem_empty (p : α → Prop) : ¬ (∃ x, ∃ _ : x ∈ #[], p x) := nofun

theorem forall_mem_empty (p : α → Prop) : ∀ (x) (_ : x ∈ #[]), p x := nofun

theorem exists_mem_push {p : α → Prop} {a : α} {xs : Array α} :
    (∃ x, ∃ _ : x ∈ xs.push a, p x) ↔ p a ∨ ∃ x, ∃ _ : x ∈ xs, p x := by
  simp only [mem_push, exists_prop]
  constructor
  · rintro ⟨x, (h | rfl), h'⟩
    · exact .inr ⟨x, h, h'⟩
    · exact .inl h'
  · rintro (h | ⟨x, h, h'⟩)
    · exact ⟨a, by simp, h⟩
    · exact ⟨x, .inl h, h'⟩

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ (x) (_ : x ∈ #[a]), p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]

theorem mem_empty_iff (a : α) : a ∈ (#[] : Array α) ↔ False := by simp

theorem mem_singleton_self (a : α) : a ∈ #[a] := by simp

theorem mem_of_mem_push_of_mem {a b : α} {xs : Array α} : a ∈ xs.push b → b ∈ xs → a ∈ xs := by
  cases xs
  simp only [List.push_toArray, mem_toArray, List.mem_append, List.mem_singleton]
  rintro (h | rfl)
  · intro _
    exact h
  · exact id

theorem eq_or_ne_mem_of_mem {a b : α} {xs : Array α} (h' : a ∈ xs.push b) :
    a = b ∨ (a ≠ b ∧ a ∈ xs) := by
  if h : a = b then
    exact .inl h
  else
    simp only [mem_push, h, or_false] at h'
    exact .inr ⟨h, h'⟩

theorem ne_empty_of_mem {a : α} {xs : Array α} (h : a ∈ xs) : xs ≠ #[] := by
  cases xs
  simp [List.ne_nil_of_mem (by simpa using h)]

theorem mem_of_ne_of_mem {a y : α} {xs : Array α} (h₁ : a ≠ y) (h₂ : a ∈ xs.push y) : a ∈ xs := by
  simpa [h₁] using h₂

theorem ne_of_not_mem_push {a b : α} {xs : Array α} (h : a ∉ xs.push b) : a ≠ b := by
  simp only [mem_push, not_or] at h
  exact h.2

theorem not_mem_of_not_mem_push {a b : α} {xs : Array α} (h : a ∉ xs.push b) : a ∉ xs := by
  simp only [mem_push, not_or] at h
  exact h.1

theorem not_mem_push_of_ne_of_not_mem {a y : α} {xs : Array α} : a ≠ y → a ∉ xs → a ∉ xs.push y :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_push {a y : α} {xs : Array α} : a ∉ xs.push y → a ≠ y ∧ a ∉ xs := by
  simp +contextual

theorem getElem_of_mem {a} {xs : Array α} (h : a ∈ xs) : ∃ (i : Nat) (h : i < xs.size), xs[i]'h = a := by
  cases xs
  simp [List.getElem_of_mem (by simpa using h)]

theorem getElem?_of_mem {a} {xs : Array α} (h : a ∈ xs) : ∃ i : Nat, xs[i]? = some a :=
  let ⟨n, _, e⟩ := getElem_of_mem h; ⟨n, e ▸ getElem?_eq_getElem _⟩

theorem mem_of_getElem {xs : Array α} {i : Nat} {h} {a : α} (e : xs[i] = a) : a ∈ xs := by
  subst e
  simp

theorem mem_of_getElem? {xs : Array α} {i : Nat} {a : α} (e : xs[i]? = some a) : a ∈ xs :=
  let ⟨_, e⟩ := getElem?_eq_some_iff.1 e; e ▸ getElem_mem ..

theorem mem_iff_getElem {a} {xs : Array α} : a ∈ xs ↔ ∃ (i : Nat) (h : i < xs.size), xs[i]'h = a :=
  ⟨getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_getElem? {a} {xs : Array α} : a ∈ xs ↔ ∃ i : Nat, xs[i]? = some a := by
  simp [getElem?_eq_some_iff, mem_iff_getElem]

theorem forall_getElem {xs : Array α} {p : α → Prop} :
    (∀ (i : Nat) h, p (xs[i]'h)) ↔ ∀ a, a ∈ xs → p a := by
  cases xs; simp [List.forall_getElem]

/-! ### isEmpty -/

@[simp] theorem isEmpty_toList {xs : Array α} : xs.toList.isEmpty = xs.isEmpty := by
  rcases xs with ⟨_ | _⟩ <;> simp

theorem isEmpty_eq_false_iff_exists_mem {xs : Array α} :
    xs.isEmpty = false ↔ ∃ x, x ∈ xs := by
  cases xs
  simpa using List.isEmpty_eq_false_iff_exists_mem

@[simp] theorem isEmpty_iff {xs : Array α} : xs.isEmpty ↔ xs = #[] := by
  cases xs <;> simp

@[deprecated isEmpty_iff (since := "2025-02-17")]
abbrev isEmpty_eq_true := @isEmpty_iff

@[simp] theorem isEmpty_eq_false_iff {xs : Array α} : xs.isEmpty = false ↔ xs ≠ #[] := by
  cases xs <;> simp

@[deprecated isEmpty_eq_false_iff (since := "2025-02-17")]
abbrev isEmpty_eq_false := @isEmpty_eq_false_iff

theorem isEmpty_iff_size_eq_zero {xs : Array α} : xs.isEmpty ↔ xs.size = 0 := by
  rw [isEmpty_iff, size_eq_zero_iff]

/-! ### Decidability of bounded quantifiers -/

instance {xs : Array α} {p : α → Prop} [DecidablePred p] :
    Decidable (∀ x, x ∈ xs → p x) :=
  decidable_of_iff (∀ (i : Nat) h, p (xs[i]'h)) (by
    simp only [mem_iff_getElem, forall_exists_index]
    exact
      ⟨by rintro w _ i h rfl; exact w i h, fun w i h => w _ i h rfl⟩)

instance {xs : Array α} {p : α → Prop} [DecidablePred p] :
    Decidable (∃ x, x ∈ xs ∧ p x) :=
  decidable_of_iff (∃ (i : Nat), ∃ (h : i < xs.size), p (xs[i]'h)) (by
    simp [mem_iff_getElem]
    exact
      ⟨by rintro ⟨i, h, w⟩; exact ⟨_, ⟨i, h, rfl⟩, w⟩, fun ⟨_, ⟨i, h, rfl⟩, w⟩ => ⟨i, h, w⟩⟩)

/-! ### any / all -/

theorem anyM_eq_anyM_loop [Monad m] (p : α → m Bool) (as : Array α) (start stop) :
    anyM p as start stop = anyM.loop p as (min stop as.size) (Nat.min_le_right ..) start := by
  simp only [anyM, Nat.min_def]; split <;> rfl

theorem anyM_stop_le_start [Monad m] (p : α → m Bool) (as : Array α) (start stop)
    (h : min stop as.size ≤ start) : anyM p as start stop = pure false := by
  rw [anyM_eq_anyM_loop, anyM.loop, dif_neg (Nat.not_lt.2 h)]

theorem anyM_loop_cons [Monad m] (p : α → m Bool) (a : α) (as : List α) (stop start : Nat)
    (h : stop + 1 ≤ (a :: as).length) :
    anyM.loop p ⟨a :: as⟩ (stop + 1) h (start + 1) =
      anyM.loop p ⟨as⟩ stop (by simpa using h) start := by
  rw [anyM.loop]
  conv => rhs; rw [anyM.loop]
  split <;> rename_i h'
  · simp only [Nat.add_lt_add_iff_right] at h'
    rw [dif_pos h', anyM_loop_cons]
    simp
  · rw [dif_neg]
    omega

@[simp] theorem anyM_toList [Monad m] (p : α → m Bool) (as : Array α) :
    as.toList.anyM p = as.anyM p :=
  match as with
  | ⟨[]⟩  => rfl
  | ⟨a :: as⟩ => by
    simp only [List.anyM, anyM, List.size_toArray, List.length_cons, Nat.le_refl, ↓reduceDIte]
    rw [anyM.loop, dif_pos (by omega)]
    congr 1
    funext b
    split
    · simp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [anyM_loop_cons]
      simpa [anyM] using anyM_toList p ⟨as⟩

-- Auxiliary for `any_iff_exists`.
theorem anyM_loop_iff_exists {p : α → Bool} {as : Array α} {start stop} (h : stop ≤ as.size) :
    anyM.loop (m := Id) p as stop h start = true ↔
      ∃ (i : Nat) (_ : i < as.size), start ≤ i ∧ i < stop ∧ p as[i] = true := by
  unfold anyM.loop
  split <;> rename_i h₁
  · dsimp
    split <;> rename_i h₂
    · simp only [true_iff]
      refine ⟨start, by omega, by omega, by omega, h₂⟩
    · rw [anyM_loop_iff_exists]
      constructor
      · rintro ⟨i, hi, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; omega
        exact ⟨i, by omega, by omega, lt, h⟩
      · rintro ⟨i, hi, ge, lt, h⟩
        have : start ≠ i := by rintro rfl; erw [h] at h₂; simp_all
        exact ⟨i, by omega, by omega, lt, h⟩
  · simp
    omega
termination_by stop - start

-- This could also be proved from `SatisfiesM_anyM_iff_exists` in `Batteries.Data.Array.Init.Monadic`
theorem any_iff_exists {p : α → Bool} {as : Array α} {start stop} :
    as.any p start stop ↔ ∃ (i : Nat) (_ : i < as.size), start ≤ i ∧ i < stop ∧ p as[i] := by
  dsimp [any, anyM, Id.run]
  split
  · rw [anyM_loop_iff_exists]
  · rw [anyM_loop_iff_exists]
    constructor
    · rintro ⟨i, hi, ge, _, h⟩
      exact ⟨i, by omega, by omega, by omega, h⟩
    · rintro ⟨i, hi, ge, _, h⟩
      exact ⟨i, by omega, by omega, by omega, h⟩

@[simp] theorem any_eq_true {p : α → Bool} {as : Array α} :
    as.any p = true ↔ ∃ (i : Nat) (_ : i < as.size), p as[i] := by
  simp [any_iff_exists]

@[simp] theorem any_eq_false {p : α → Bool} {as : Array α} :
    as.any p = false ↔ ∀ (i : Nat) (_ : i < as.size), ¬p as[i] := by
  rw [Bool.eq_false_iff, Ne, any_eq_true]
  simp

@[simp] theorem any_toList {p : α → Bool} (as : Array α) : as.toList.any p = as.any p := by
  rw [Bool.eq_iff_iff, any_eq_true, List.any_eq_true]
  simp only [List.mem_iff_getElem, getElem_toList]
  exact ⟨fun ⟨_, ⟨i, w, rfl⟩, h⟩ => ⟨i, w, h⟩, fun ⟨i, w, h⟩ => ⟨_, ⟨i, w, rfl⟩, h⟩⟩

theorem allM_eq_not_anyM_not [Monad m] [LawfulMonad m] (p : α → m Bool) (as : Array α) :
    allM p as = (! ·) <$> anyM ((! ·) <$> p ·) as := by
  dsimp [allM, anyM]
  simp

@[simp] theorem allM_toList [Monad m] [LawfulMonad m] (p : α → m Bool) (as : Array α) :
    as.toList.allM p = as.allM p := by
  rw [allM_eq_not_anyM_not]
  rw [← anyM_toList]
  rw [List.allM_eq_not_anyM_not]

theorem all_eq_not_any_not (p : α → Bool) (as : Array α) (start stop) :
    as.all p start stop = !(as.any (!p ·) start stop) := by
  dsimp [all, allM]
  rfl

theorem all_iff_forall {p : α → Bool} {as : Array α} {start stop} :
    as.all p start stop ↔ ∀ (i : Nat) (_ : i < as.size), start ≤ i ∧ i < stop → p as[i] := by
  rw [all_eq_not_any_not]
  suffices ¬(as.any (!p ·) start stop = true) ↔
      ∀ (i : Nat) (_ : i < as.size), start ≤ i ∧ i < stop → p as[i] by
    simp_all
  simp only [any_iff_exists, Bool.not_eq_eq_eq_not, Bool.not_true, not_exists, not_and,
    Bool.not_eq_false, and_imp]

@[simp] theorem all_eq_true {p : α → Bool} {as : Array α} :
    as.all p = true ↔ ∀ (i : Nat) (_ : i < as.size), p as[i] := by
  simp [all_iff_forall]

@[simp] theorem all_eq_false {p : α → Bool} {as : Array α} :
    as.all p = false ↔ ∃ (i : Nat) (_ : i < as.size), ¬p as[i] := by
  rw [Bool.eq_false_iff, Ne, all_eq_true]
  simp

@[simp] theorem all_toList {p : α → Bool} (as : Array α) : as.toList.all p = as.all p := by
  rw [Bool.eq_iff_iff, all_eq_true, List.all_eq_true]
  simp only [List.mem_iff_getElem, getElem_toList]
  constructor
  · intro w i h
    exact w as[i] ⟨i, h, getElem_toList h⟩
  · rintro w x ⟨i, h, rfl⟩
    exact w i h

theorem all_eq_true_iff_forall_mem {xs : Array α} : xs.all p ↔ ∀ x, x ∈ xs → p x := by
  simp only [← all_toList, List.all_eq_true, mem_def]

/-- Variant of `anyM_toArray` with a side condition on `stop`. -/
@[simp] theorem _root_.List.anyM_toArray' [Monad m] [LawfulMonad m] (p : α → m Bool) (l : List α)
    (h : stop = l.toArray.size) :
    l.toArray.anyM p 0 stop = l.anyM p := by
  subst h
  rw [← anyM_toList]

/-- Variant of `any_toArray` with a side condition on `stop`. -/
@[simp] theorem _root_.List.any_toArray' (p : α → Bool) (l : List α) (h : stop = l.toArray.size) :
    l.toArray.any p 0 stop = l.any p := by
  subst h
  rw [any_toList]

/-- Variant of `allM_toArray` with a side condition on `stop`. -/
@[simp] theorem _root_.List.allM_toArray' [Monad m] [LawfulMonad m] (p : α → m Bool) (l : List α)
    (h : stop = l.toArray.size) :
    l.toArray.allM p 0 stop = l.allM p := by
  subst h
  rw [← allM_toList]

/-- Variant of `all_toArray` with a side condition on `stop`. -/
@[simp] theorem _root_.List.all_toArray' (p : α → Bool) (l : List α) (h : stop = l.toArray.size) :
    l.toArray.all p 0 stop = l.all p := by
  subst h
  rw [all_toList]

theorem _root_.List.anyM_toArray [Monad m] [LawfulMonad m] (p : α → m Bool) (l : List α) :
    l.toArray.anyM p = l.anyM p := by
  rw [← anyM_toList]

theorem _root_.List.any_toArray (p : α → Bool) (l : List α) : l.toArray.any p = l.any p := by
  rw [any_toList]

theorem _root_.List.allM_toArray [Monad m] [LawfulMonad m] (p : α → m Bool) (l : List α) :
    l.toArray.allM p = l.allM p := by
  rw [← allM_toList]

theorem _root_.List.all_toArray (p : α → Bool) (l : List α) : l.toArray.all p = l.all p := by
  rw [all_toList]

/-- Variant of `any_eq_true` in terms of membership rather than an array index. -/
theorem any_eq_true' {p : α → Bool} {as : Array α} :
    as.any p = true ↔ (∃ x, x ∈ as ∧ p x) := by
  cases as
  simp

/-- Variant of `any_eq_false` in terms of membership rather than an array index. -/
theorem any_eq_false' {p : α → Bool} {as : Array α} :
    as.any p = false ↔ ∀ x, x ∈ as → ¬p x := by
  rw [Bool.eq_false_iff, Ne, any_eq_true']
  simp

/-- Variant of `all_eq_true` in terms of membership rather than an array index. -/
theorem all_eq_true' {p : α → Bool} {as : Array α} :
    as.all p = true ↔ (∀ x, x ∈ as → p x) := by
  cases as
  simp

/-- Variant of `all_eq_false` in terms of membership rather than an array index. -/
theorem all_eq_false' {p : α → Bool} {as : Array α} :
    as.all p = false ↔ ∃ x, x ∈ as ∧ ¬p x := by
  rw [Bool.eq_false_iff, Ne, all_eq_true']
  simp

theorem any_eq {xs : Array α} {p : α → Bool} : xs.any p = decide (∃ i : Nat, ∃ h, p (xs[i]'h)) := by
  by_cases h : xs.any p
  · simp_all [any_eq_true]
  · simp_all [any_eq_false]

/-- Variant of `any_eq` in terms of membership rather than an array index. -/
theorem any_eq' {xs : Array α} {p : α → Bool} : xs.any p = decide (∃ x, x ∈ xs ∧ p x) := by
  by_cases h : xs.any p
  · simp_all [any_eq_true', -any_eq_true]
  · simp only [Bool.not_eq_true] at h
    simp only [h]
    simp only [any_eq_false'] at h
    simpa using h

theorem all_eq {xs : Array α} {p : α → Bool} : xs.all p = decide (∀ i, (_ : i < xs.size) → p xs[i]) := by
  by_cases h : xs.all p
  · simp_all [all_eq_true]
  · simp only [Bool.not_eq_true] at h
    simp only [h]
    simp only [all_eq_false] at h
    simpa using h

/-- Variant of `all_eq` in terms of membership rather than an array index. -/
theorem all_eq' {xs : Array α} {p : α → Bool} : xs.all p = decide (∀ x, x ∈ xs → p x) := by
  by_cases h : xs.all p
  · simp_all [all_eq_true', -all_eq_true]
  · simp only [Bool.not_eq_true] at h
    simp only [h]
    simp only [all_eq_false'] at h
    simpa using h

theorem decide_exists_mem {xs : Array α} {p : α → Prop} [DecidablePred p] :
    decide (∃ x, x ∈ xs ∧ p x) = xs.any p := by
  simp [any_eq']

theorem decide_forall_mem {xs : Array α} {p : α → Prop} [DecidablePred p] :
    decide (∀ x, x ∈ xs → p x) = xs.all p := by
  simp [all_eq']

@[simp] theorem _root_.List.contains_toArray [BEq α] {l : List α} {a : α} :
    l.toArray.contains a = l.contains a := by
  simp [Array.contains, List.any_beq]

theorem _root_.List.elem_toArray [BEq α] {l : List α} {a : α} :
    Array.elem a l.toArray = List.elem a l := by
  simp [Array.elem]

theorem any_beq [BEq α] {xs : Array α} {a : α} : (xs.any fun x => a == x) = xs.contains a := by
  cases xs
  simp [List.any_beq]

/-- Variant of `any_beq` with `==` reversed. -/
theorem any_beq' [BEq α] [PartialEquivBEq α] {xs : Array α} :
    (xs.any fun x => x == a) = xs.contains a := by
  simp only [BEq.comm, any_beq]

theorem all_bne [BEq α] {xs : Array α} : (xs.all fun x => a != x) = !xs.contains a := by
  cases xs
  simp [List.all_bne]

/-- Variant of `all_bne` with `!=` reversed. -/
theorem all_bne' [BEq α] [PartialEquivBEq α] {xs : Array α} :
    (xs.all fun x => x != a) = !xs.contains a := by
  simp only [bne_comm, all_bne]

theorem mem_of_contains_eq_true [BEq α] [LawfulBEq α] {a : α} {as : Array α} : as.contains a = true → a ∈ as := by
  cases as
  simp

@[deprecated mem_of_contains_eq_true (since := "2024-12-12")]
abbrev mem_of_elem_eq_true := @mem_of_contains_eq_true

theorem contains_eq_true_of_mem [BEq α] [LawfulBEq α] {a : α} {as : Array α} (h : a ∈ as) : as.contains a = true := by
  cases as
  simpa using h

@[deprecated contains_eq_true_of_mem (since := "2024-12-12")]
abbrev elem_eq_true_of_mem := @contains_eq_true_of_mem

instance [BEq α] [LawfulBEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_contains_eq_true contains_eq_true_of_mem)

@[simp] theorem elem_eq_contains [BEq α] {a : α} {xs : Array α} :
    elem a xs = xs.contains a := by
  simp [elem]

theorem elem_iff [BEq α] [LawfulBEq α] {a : α} {xs : Array α} :
    elem a xs = true ↔ a ∈ xs := ⟨mem_of_contains_eq_true, contains_eq_true_of_mem⟩

theorem contains_iff [BEq α] [LawfulBEq α] {a : α} {xs : Array α} :
    xs.contains a = true ↔ a ∈ xs := ⟨mem_of_contains_eq_true, contains_eq_true_of_mem⟩

theorem elem_eq_mem [BEq α] [LawfulBEq α] (a : α) (xs : Array α) :
    elem a xs = decide (a ∈ xs) := by rw [Bool.eq_iff_iff, elem_iff, decide_eq_true_iff]

@[simp] theorem contains_eq_mem [BEq α] [LawfulBEq α] (a : α) (xs : Array α) :
    xs.contains a = decide (a ∈ xs) := by rw [← elem_eq_contains, elem_eq_mem]

/-- Variant of `any_push` with a side condition on `stop`. -/
@[simp] theorem any_push' [BEq α] {xs : Array α} {a : α} {p : α → Bool} (h : stop = xs.size + 1) :
    (xs.push a).any p 0 stop = (xs.any p || p a) := by
  cases xs
  rw [List.push_toArray]
  simp [h]

theorem any_push [BEq α] {xs : Array α} {a : α} {p : α → Bool} :
    (xs.push a).any p = (xs.any p || p a) :=
  any_push' (by simp)

/-- Variant of `all_push` with a side condition on `stop`. -/
@[simp] theorem all_push' [BEq α] {xs : Array α} {a : α} {p : α → Bool} (h : stop = xs.size + 1) :
    (xs.push a).all p 0 stop = (xs.all p && p a) := by
  cases xs
  rw [List.push_toArray]
  simp [h]

theorem all_push [BEq α] {xs : Array α} {a : α} {p : α → Bool} :
    (xs.push a).all p = (xs.all p && p a) :=
  all_push' (by simp)

@[simp] theorem contains_push [BEq α] {xs : Array α} {a : α} {b : α} :
    (xs.push a).contains b = (xs.contains b || b == a) := by
  simp [contains]

/-! ### set -/

@[simp] theorem getElem_set_self (xs : Array α) (i : Nat) (h : i < xs.size) (v : α) {j : Nat}
      (eq : i = j) (p : j < (xs.set i v).size) :
    (xs.set i v)[j]'p = v := by
  cases xs
  simp
  simp [set, ← getElem_toList, ←eq]

@[deprecated getElem_set_self (since := "2024-12-11")]
abbrev getElem_set_eq := @getElem_set_self

@[simp] theorem getElem?_set_self (xs : Array α) (i : Nat) (h : i < xs.size) (v : α) :
    (xs.set i v)[i]? = v := by simp [getElem?_eq_getElem, h]

@[deprecated getElem?_set_self (since := "2024-12-11")]
abbrev getElem?_set_eq := @getElem?_set_self

@[simp] theorem getElem_set_ne (xs : Array α) (i : Nat) (h' : i < xs.size) (v : α) {j : Nat}
    (pj : j < (xs.set i v).size) (h : i ≠ j) :
    (xs.set i v)[j]'pj = xs[j]'(size_set xs i v _ ▸ pj) := by
  simp only [set, ← getElem_toList, List.getElem_set_ne h]

@[simp] theorem getElem?_set_ne (xs : Array α) (i : Nat) (h : i < xs.size) {j : Nat} (v : α)
    (ne : i ≠ j) : (xs.set i v)[j]? = xs[j]? := by
  by_cases h : j < xs.size <;> simp [getElem?_eq_getElem, getElem?_eq_none, Nat.ge_of_not_lt, ne, h]

theorem getElem_set (xs : Array α) (i : Nat) (h' : i < xs.size) (v : α) (j : Nat)
    (h : j < (xs.set i v).size) :
    (xs.set i v)[j]'h = if i = j then v else xs[j]'(size_set xs i v _ ▸ h) := by
  by_cases p : i = j <;> simp [p]

theorem getElem?_set (xs : Array α) (i : Nat) (h : i < xs.size) (v : α) (j : Nat) :
    (xs.set i v)[j]? = if i = j then some v else xs[j]? := by
  split <;> simp_all

@[simp] theorem set_getElem_self {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs.set i xs[i] = xs := by
  cases xs
  simp

@[simp] theorem set_eq_empty_iff {xs : Array α} (n : Nat) (a : α) (h) :
     xs.set n a = #[] ↔ xs = #[] := by
  cases xs <;> cases n <;> simp [set]

theorem set_comm (a b : α)
    {i j : Nat} (xs : Array α) {hi : i < xs.size} {hj : j < (xs.set i a).size} (h : i ≠ j) :
    (xs.set i a).set j b = (xs.set j b (by simpa using hj)).set i a (by simpa using hi) := by
  cases xs
  simp [List.set_comm _ _ _ h]

@[simp]
theorem set_set (a b : α) (xs : Array α) (i : Nat) (h : i < xs.size) :
    (xs.set i a).set i b (by simpa using h) = xs.set i b := by
  cases xs
  simp

theorem mem_set (xs : Array α) (i : Nat) (h : i < xs.size) (a : α) :
    a ∈ xs.set i a := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using h), by simp⟩

theorem mem_or_eq_of_mem_set
    {xs : Array α} {i : Nat} {a b : α} {w : i < xs.size} (h : a ∈ xs.set i b) : a ∈ xs ∨ a = b := by
  cases xs
  simpa using List.mem_or_eq_of_mem_set (by simpa using h)

/-! ### setIfInBounds -/

@[simp] theorem set!_eq_setIfInBounds : @set! = @setIfInBounds := rfl

@[deprecated set!_eq_setIfInBounds (since := "2024-12-12")]
abbrev set!_is_setIfInBounds := @set!_eq_setIfInBounds

@[simp] theorem size_setIfInBounds (xs : Array α) (i : Nat) (a : α) :
    (xs.setIfInBounds i a).size = xs.size := by
  if h : i < xs.size  then
    simp [setIfInBounds, h]
  else
    simp [setIfInBounds, h]

theorem getElem_setIfInBounds (xs : Array α) (i : Nat) (a : α) (j : Nat)
    (hj : j < (xs.setIfInBounds i a).size) :
    (xs.setIfInBounds i a)[j]'hj = if i = j then a else xs[j]'(by simpa using hj) := by
  simp only [setIfInBounds]
  split
  · simp [getElem_set]
  · simp only [size_setIfInBounds] at hj
    rw [if_neg]
    omega

@[simp] theorem getElem_setIfInBounds_self (xs : Array α) {i : Nat} (a : α) (h : _) :
    (xs.setIfInBounds i a)[i]'h = a := by
  simp at h
  simp only [setIfInBounds, h, ↓reduceDIte, getElem_set_self]

@[deprecated getElem_setIfInBounds_self (since := "2024-12-11")]
abbrev getElem_setIfInBounds_eq := @getElem_setIfInBounds_self

@[simp] theorem getElem_setIfInBounds_ne (xs : Array α) {i : Nat} (a : α) {j : Nat}
    (hj : j < (xs.setIfInBounds i a).size) (h : i ≠ j) :
    (xs.setIfInBounds i a)[j]'hj = xs[j]'(by simpa using hj) := by
  simp [getElem_setIfInBounds, h]

theorem getElem?_setIfInBounds {xs : Array α} {i j : Nat} {a : α}  :
    (xs.setIfInBounds i a)[j]? = if i = j then if i < xs.size then some a else none else xs[j]? := by
  cases xs
  simp [List.getElem?_set]

theorem getElem?_setIfInBounds_self (xs : Array α) {i : Nat} (a : α) :
    (xs.setIfInBounds i a)[i]? = if i < xs.size then some a else none := by
  simp [getElem?_setIfInBounds]

@[simp]
theorem getElem?_setIfInBounds_self_of_lt (xs : Array α) {i : Nat} (a : α) (h : i < xs.size) :
    (xs.setIfInBounds i a)[i]? = some a := by
  simp [getElem?_setIfInBounds, h]

@[deprecated getElem?_setIfInBounds_self (since := "2024-12-11")]
abbrev getElem?_setIfInBounds_eq := @getElem?_setIfInBounds_self

@[simp] theorem getElem?_setIfInBounds_ne {xs : Array α} {i j : Nat} (h : i ≠ j) {a : α}  :
    (xs.setIfInBounds i a)[j]? = xs[j]? := by
  simp [getElem?_setIfInBounds, h]

theorem setIfInBounds_eq_of_size_le {xs : Array α} {i : Nat} (h : xs.size ≤ i) {a : α} :
    xs.setIfInBounds i a = xs := by
  cases xs
  simp [List.set_eq_of_length_le (by simpa using h)]

@[simp] theorem setIfInBounds_eq_empty_iff {xs : Array α} (i : Nat) (a : α) :
    xs.setIfInBounds i a = #[] ↔ xs = #[] := by
  cases xs <;> cases i <;> simp

theorem setIfInBounds_comm (a b : α)
    {i j : Nat} (xs : Array α) (h : i ≠ j) :
    (xs.setIfInBounds i a).setIfInBounds j b = (xs.setIfInBounds j b).setIfInBounds i a := by
  cases xs
  simp [List.set_comm _ _ _ h]

@[simp]
theorem setIfInBounds_setIfInBounds (a b : α) (xs : Array α) (i : Nat) :
    (xs.setIfInBounds i a).setIfInBounds i b = xs.setIfInBounds i b := by
  cases xs
  simp

theorem mem_setIfInBounds (xs : Array α) (i : Nat) (h : i < xs.size) (a : α) :
    a ∈ xs.setIfInBounds i a := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using h), by simp⟩

theorem mem_or_eq_of_mem_setIfInBounds
    {xs : Array α} {i : Nat} {a b : α} (h : a ∈ xs.setIfInBounds i b) : a ∈ xs ∨ a = b := by
  cases xs
  simpa using List.mem_or_eq_of_mem_set (by simpa using h)

/-- Simplifies a normal form from `get!` -/
@[simp] theorem getD_get?_setIfInBounds (xs : Array α) (i : Nat) (v d : α) :
    (xs.setIfInBounds i v)[i]?.getD d = if i < xs.size then v else d := by
  by_cases h : i < xs.size <;>
    simp [setIfInBounds, Nat.not_lt_of_le, h,  getD_getElem?]

@[simp] theorem toList_setIfInBounds (xs : Array α) (i x) :
    (xs.setIfInBounds i x).toList = xs.toList.set i x := by
  simp only [setIfInBounds]
  split <;> rename_i h
  · simp
  · simp [List.set_eq_of_length_le (by simpa using h)]

/-! ### BEq -/

@[simp] theorem beq_empty_iff [BEq α] {xs : Array α} : (xs == #[]) = xs.isEmpty := by
  cases xs
  simp

@[simp] theorem empty_beq_iff [BEq α] {xs : Array α} : (#[] == xs) = xs.isEmpty := by
  cases xs
  simp

@[simp] theorem push_beq_push [BEq α] {a b : α} {xs ys : Array α} :
    (xs.push a == ys.push b) = (xs == ys && a == b) := by
  cases xs
  cases ys
  simp

theorem size_eq_of_beq [BEq α] {xs ys : Array α} (h : xs == ys) : xs.size = ys.size := by
  cases xs
  cases ys
  simp [List.length_eq_of_beq (by simpa using h)]

@[simp] theorem mkArray_beq_mkArray [BEq α] {a b : α} {n : Nat} :
    (mkArray n a == mkArray n b) = (n == 0 || a == b) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mkArray_succ, mkArray_succ, push_beq_push, mkArray_beq_mkArray]
    rw [Bool.eq_iff_iff]
    simp +contextual

private theorem beq_of_beq_singleton [BEq α] {a b : α} : #[a] == #[b] → a == b := by
  intro h
  have : isEqv #[a] #[b] BEq.beq = true := h
  simp [isEqv, isEqvAux] at this
  assumption

@[simp] theorem reflBEq_iff [BEq α] : ReflBEq (Array α) ↔ ReflBEq α := by
  constructor
  · intro h
    constructor
    intro a
    apply beq_of_beq_singleton
    simp
  · intro h
    constructor
    apply Array.isEqv_self_beq

@[simp] theorem lawfulBEq_iff [BEq α] : LawfulBEq (Array α) ↔ LawfulBEq α := by
  constructor
  · intro h
    constructor
    · intro a b h
      apply singleton_inj.1
      apply eq_of_beq
      simpa [instBEq, isEqv, isEqvAux]
    · intro a
      apply beq_of_beq_singleton
      simp
  · intro h
    constructor
    · intro xs ys h
      obtain ⟨hs, hi⟩ := isEqv_iff_rel.mp h
      ext i h₁ h₂
      · exact hs
      · simpa using hi _ h₁
    · intro xs
      apply Array.isEqv_self_beq

/-! ### isEqv -/

@[simp] theorem isEqv_eq [DecidableEq α] {xs ys : Array α} : xs.isEqv ys (· == ·) = (xs = ys) := by
  cases xs
  cases ys
  simp

/-! ### back -/

theorem back_eq_getElem (xs : Array α) (h : 0 < xs.size) : xs.back = xs[xs.size - 1] := by
  cases xs
  simp [List.getLast_eq_getElem]

theorem back?_eq_getElem? (xs : Array α) : xs.back? = xs[xs.size - 1]? := by
  cases xs
  simp [List.getLast?_eq_getElem?]

@[simp] theorem back_mem {xs : Array α} (h : 0 < xs.size) : xs.back h ∈ xs := by
  cases xs
  simp

/-! ### map -/

theorem mapM_eq_foldlM [Monad m] [LawfulMonad m] (f : α → m β) (xs : Array α) :
    xs.mapM f = xs.foldlM (fun bs a => bs.push <$> f a) #[] := by
  rw [mapM, aux, ← foldlM_toList]; rfl
where
  aux (i bs) :
      mapM.map f xs i bs = (xs.toList.drop i).foldlM (fun bs a => bs.push <$> f a) bs := by
    unfold mapM.map; split
    · rw [← List.getElem_cons_drop_succ_eq_drop ‹_›]
      simp only [aux (i + 1), map_eq_pure_bind, length_toList, List.foldlM_cons, bind_assoc,
        pure_bind]
      rfl
    · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; rfl
  termination_by xs.size - i
  decreasing_by decreasing_trivial_pre_omega

@[simp] theorem toList_map (f : α → β) (xs : Array α) : (xs.map f).toList = xs.toList.map f := by
  rw [map, mapM_eq_foldlM]
  apply congrArg toList (foldl_toList (fun bs a => push bs (f a)) #[] xs).symm |>.trans
  have H (l xs) : List.foldl (fun bs a => push bs (f a)) xs l = ⟨xs.toList ++ l.map f⟩ := by
    induction l generalizing xs <;> simp [*]
  simp [H]

@[simp] theorem _root_.List.map_toArray (f : α → β) (l : List α) :
    l.toArray.map f = (l.map f).toArray := by
  apply ext'
  simp

@[simp] theorem size_map (f : α → β) (xs : Array α) : (xs.map f).size = xs.size := by
  simp only [← length_toList]
  simp

@[simp] theorem getElem_map (f : α → β) (xs : Array α) (i : Nat) (hi : i < (xs.map f).size) :
    (xs.map f)[i] = f (xs[i]'(by simpa using hi)) := by
  cases xs
  simp

@[simp] theorem getElem?_map (f : α → β) (xs : Array α) (i : Nat) :
    (xs.map f)[i]? = xs[i]?.map f := by
  simp [getElem?_def]

@[simp] theorem mapM_empty [Monad m] (f : α → m β) : mapM f #[] = pure #[] := by
  rw [mapM, mapM.map]; rfl

@[simp] theorem map_empty (f : α → β) : map f #[] = #[] := mapM_empty f

@[simp] theorem map_push {f : α → β} {as : Array α} {x : α} :
    (as.push x).map f = (as.map f).push (f x) := by
  ext
  · simp
  · simp only [getElem_map, getElem_push, size_map]
    split <;> rfl

@[simp] theorem map_id_fun : map (id : α → α) = id := by
  funext xs
  induction xs <;> simp_all

/-- `map_id_fun'` differs from `map_id_fun` by representing the identity function as a lambda, rather than `id`. -/
@[simp] theorem map_id_fun' : map (fun (a : α) => a) = id := map_id_fun

-- This is not a `@[simp]` lemma because `map_id_fun` will apply.
theorem map_id (xs : Array α) : map (id : α → α) xs = xs := by
  cases xs <;> simp_all

/-- `map_id'` differs from `map_id` by representing the identity function as a lambda, rather than `id`. -/
-- This is not a `@[simp]` lemma because `map_id_fun'` will apply.
theorem map_id' (xs : Array α) : map (fun (a : α) => a) xs = xs := map_id xs

/-- Variant of `map_id`, with a side condition that the function is pointwise the identity. -/
theorem map_id'' {f : α → α} (h : ∀ x, f x = x) (xs : Array α) : map f xs = xs := by
  simp [show f = id from funext h]

theorem map_singleton (f : α → β) (a : α) : map f #[a] = #[f a] := rfl

-- We use a lower priority here as there are more specific lemmas in downstream libraries
-- which should be able to fire first.
@[simp 500] theorem mem_map {f : α → β} {xs : Array α} : b ∈ xs.map f ↔ ∃ a, a ∈ xs ∧ f a = b := by
  simp only [mem_def, toList_map, List.mem_map]

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem forall_mem_map {f : α → β} {xs : Array α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ xs.map f), P i) ↔ ∀ (j) (_ : j ∈ xs), P (f j) := by
  simp

@[simp] theorem map_eq_empty_iff {f : α → β} {xs : Array α} : map f xs = #[] ↔ xs = #[] := by
  cases xs
  simp

theorem eq_empty_of_map_eq_empty {f : α → β} {xs : Array α} (h : map f xs = #[]) : xs = #[] :=
  map_eq_empty_iff.mp h

@[simp] theorem map_inj_left {f g : α → β} : map f xs = map g xs ↔ ∀ a ∈ xs, f a = g a := by
  cases xs <;> simp_all

theorem map_inj_right {f : α → β} (w : ∀ x y, f x = f y → x = y) : map f xs = map f ys ↔ xs = ys := by
  cases xs
  cases ys
  simp [List.map_inj_right w]

theorem map_congr_left (h : ∀ a ∈ xs, f a = g a) : map f xs = map g xs :=
  map_inj_left.2 h

theorem map_inj : map f = map g ↔ f = g := by
  constructor
  · intro h; ext a; replace h := congrFun h #[a]; simpa using h
  · intro h; subst h; rfl

theorem map_eq_push_iff {f : α → β} {xs : Array α} {ys : Array β} {b : β} :
    map f xs = ys.push b ↔ ∃ zs a, xs = zs.push a ∧ map f zs = ys ∧ f a = b := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.map_toArray, List.push_toArray, mk.injEq, List.map_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, h⟩
    simp only [List.map_eq_singleton_iff] at h
    obtain ⟨a, rfl, rfl⟩ := h
    refine ⟨l₁.toArray, a, by simp⟩
  · rintro ⟨⟨l₁⟩, a, h₁, h₂, rfl⟩
    refine ⟨l₁, [a], by simp_all⟩

@[simp] theorem map_eq_singleton_iff {f : α → β} {xs : Array α} {b : β} :
    map f xs = #[b] ↔ ∃ a, xs = #[a] ∧ f a = b := by
  cases xs
  simp

theorem map_eq_map_iff {f g : α → β} {xs : Array α} :
    map f xs = map g xs ↔ ∀ a ∈ xs, f a = g a := by
  cases xs <;> simp_all

theorem map_eq_iff {f : α → β} {xs : Array α} {ys : Array β} :
    map f xs = ys ↔ ∀ i : Nat, ys[i]? = xs[i]?.map f := by
  cases xs
  cases ys
  simp [List.map_eq_iff]

theorem map_eq_foldl (f : α → β) (xs : Array α) :
    map f xs = foldl (fun bs a => bs.push (f a)) #[] xs := by
  simpa using mapM_eq_foldlM (m := Id) f xs

@[simp] theorem map_set {f : α → β} {xs : Array α} {i : Nat} {h : i < xs.size} {a : α} :
    (xs.set i a).map f = (xs.map f).set i (f a) (by simpa using h) := by
  cases xs
  simp

@[simp] theorem map_setIfInBounds {f : α → β} {xs : Array α} {i : Nat} {a : α} :
    (xs.setIfInBounds i a).map f = (xs.map f).setIfInBounds i (f a) := by
  cases xs
  simp

@[simp] theorem map_pop {f : α → β} {xs : Array α} : xs.pop.map f = (xs.map f).pop := by
  cases xs
  simp

@[simp] theorem back?_map {f : α → β} {xs : Array α} : (xs.map f).back? = xs.back?.map f := by
  cases xs
  simp

@[simp] theorem map_map {f : α → β} {g : β → γ} {as : Array α} :
    (as.map f).map g = as.map (g ∘ f) := by
  cases as; simp

theorem mapM_eq_mapM_toList [Monad m] [LawfulMonad m] (f : α → m β) (xs : Array α) :
    xs.mapM f = List.toArray <$> (xs.toList.mapM f) := by
  rw [mapM_eq_foldlM, ← foldlM_toList, ← List.foldrM_reverse]
  conv => rhs; rw [← List.reverse_reverse xs.toList]
  induction xs.toList.reverse with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem toList_mapM [Monad m] [LawfulMonad m] (f : α → m β) (xs : Array α) :
    toList <$> xs.mapM f = xs.toList.mapM f := by
  simp [mapM_eq_mapM_toList]

@[deprecated "Use `mapM_eq_foldlM` instead" (since := "2025-01-08")]
theorem mapM_map_eq_foldl (as : Array α) (f : α → β) (i) :
    mapM.map (m := Id) f as i b = as.foldl (start := i) (fun acc a => acc.push (f a)) b := by
  unfold mapM.map
  split <;> rename_i h
  · simp only [Id.bind_eq]
    dsimp [foldl, Id.run, foldlM]
    rw [mapM_map_eq_foldl, dif_pos (by omega), foldlM.loop, dif_pos h]
    -- Calling `split` here gives a bad goal.
    have : size as - i = Nat.succ (size as - i - 1) := by omega
    rw [this]
    simp [foldl, foldlM, Id.run, Nat.sub_add_eq]
  · dsimp [foldl, Id.run, foldlM]
    rw [dif_pos (by omega), foldlM.loop, dif_neg h]
    rfl
termination_by as.size - i

/--
Use this as `induction ass using array₂_induction` on a hypothesis of the form `ass : Array (Array α)`.
The hypothesis `ass` will be replaced with a hypothesis `ass : List (List α)`,
and former appearances of `ass` in the goal will be replaced with `(ass.map List.toArray).toArray`.
-/
-- We can't use `@[cases_eliminator]` here as
-- `Lean.Meta.getCustomEliminator?` only looks at the top-level constant.
theorem array₂_induction (P : Array (Array α) → Prop) (of : ∀ (xss : List (List α)), P (xss.map List.toArray).toArray)
    (xss : Array (Array α)) : P xss := by
  specialize of (xss.toList.map toList)
  simpa [← toList_map, Function.comp_def, map_id] using of

/--
Use this as `induction ass using array₃_induction` on a hypothesis of the form `ass : Array (Array (Array α))`.
The hypothesis `ass` will be replaced with a hypothesis `ass : List (List (List α))`,
and former appearances of `ass` in the goal will be replaced with
`((ass.map (fun xs => xs.map List.toArray)).map List.toArray).toArray`.
-/
theorem array₃_induction (P : Array (Array (Array α)) → Prop)
    (of : ∀ (xss : List (List (List α))), P ((xss.map (fun xs => xs.map List.toArray)).map List.toArray).toArray)
    (xss : Array (Array (Array α))) : P xss := by
  specialize of ((xss.toList.map toList).map (fun as => as.map toList))
  simpa [← toList_map, Function.comp_def, map_id] using of

/-! ### filter -/

@[congr]
theorem filter_congr {xs ys : Array α} (h : xs = ys)
    {f : α → Bool} {g : α → Bool} (h' : f = g) {start stop start' stop' : Nat}
    (h₁ : start = start') (h₂ : stop = stop') :
    filter f xs start stop = filter g ys start' stop' := by
  congr

@[simp] theorem toList_filter' (p : α → Bool) (xs : Array α) (h : stop = xs.size) :
    (xs.filter p 0 stop).toList = xs.toList.filter p := by
  subst h
  dsimp only [filter]
  rw [← foldl_toList]
  generalize xs.toList = xs
  suffices ∀ as, (List.foldl (fun acc a => if p a = true then push acc a else acc) as xs).toList =
      as.toList ++ List.filter p xs by
    simpa using this #[]
  induction xs with simp
  | cons => split <;> simp [*]

theorem toList_filter (p : α → Bool) (xs : Array α) :
    (xs.filter p).toList = xs.toList.filter p := by
  simp

@[simp] theorem _root_.List.filter_toArray' (p : α → Bool) (l : List α) (h : stop = l.length) :
    l.toArray.filter p 0 stop = (l.filter p).toArray := by
  apply ext'
  simp [h]

theorem _root_.List.filter_toArray (p : α → Bool) (l : List α) :
    l.toArray.filter p = (l.filter p).toArray := by
  simp

@[simp] theorem filter_push_of_pos {p : α → Bool} {a : α} {xs : Array α}
    (h : p a) (w : stop = xs.size + 1):
    (xs.push a).filter p 0 stop = (xs.filter p).push a := by
  subst w
  rcases xs with ⟨xs⟩
  simp [h]

@[simp] theorem filter_push_of_neg {p : α → Bool} {a : α} {xs : Array α}
    (h : ¬p a) (w : stop = xs.size + 1) :
    (xs.push a).filter p 0 stop = xs.filter p := by
  subst w
  rcases xs with ⟨xs⟩
  simp [h]

theorem filter_push {p : α → Bool} {a : α} {xs : Array α} :
    (xs.push a).filter p = if p a then (xs.filter p).push a else xs.filter p := by
  split <;> simp [*]

theorem size_filter_le (p : α → Bool) (xs : Array α) :
    (xs.filter p).size ≤ xs.size := by
  rcases xs with ⟨xs⟩
  simpa using List.length_filter_le p xs

@[simp] theorem filter_eq_self {p : α → Bool} {xs : Array α} :
    filter p xs = xs ↔ ∀ a ∈ xs, p a := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem filter_size_eq_size {p : α → Bool} {xs : Array α} :
    (xs.filter p).size = xs.size ↔ ∀ a ∈ xs, p a := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem mem_filter {p : α → Bool} {xs : Array α} {a : α} :
    a ∈ xs.filter p ↔ a ∈ xs ∧ p a := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem filter_eq_empty_iff {p : α → Bool} {xs : Array α} :
    filter p xs = #[] ↔ ∀ a, a ∈ xs → ¬p a := by
  rcases xs with ⟨xs⟩
  simp

theorem forall_mem_filter {p : α → Bool} {xs : Array α} {P : α → Prop} :
    (∀ (i) (_ : i ∈ xs.filter p), P i) ↔ ∀ (j) (_ : j ∈ xs), p j → P j := by
  simp

@[simp] theorem filter_filter (q) (xs : Array α) :
    filter p (filter q xs) = filter (fun a => p a && q a) xs := by
  apply ext'
  simp only [toList_filter, List.filter_filter]

theorem foldl_filter (p : α → Bool) (f : β → α → β) (xs : Array α) (init : β) :
    (xs.filter p).foldl f init = xs.foldl (fun x y => if p y then f x y else x) init := by
  rcases xs with ⟨xs⟩
  rw [List.filter_toArray]
  simp [List.foldl_filter]

theorem foldr_filter (p : α → Bool) (f : α → β → β) (xs : Array α) (init : β) :
    (xs.filter p).foldr f init = xs.foldr (fun x y => if p x then f x y else y) init := by
  rcases xs with ⟨xs⟩
  rw [List.filter_toArray]
  simp [List.foldr_filter]

theorem filter_map (f : β → α) (xs : Array β) : filter p (map f xs) = map f (filter (p ∘ f) xs) := by
  rcases xs with ⟨xs⟩
  simp [List.filter_map]

theorem map_filter_eq_foldl (f : α → β) (p : α → Bool) (xs : Array α) :
    map f (filter p xs) = foldl (fun acc x => bif p x then acc.push (f x) else acc) #[] xs := by
  rcases xs with ⟨xs⟩
  apply ext'
  simp only [List.size_toArray, List.filter_toArray', List.map_toArray, List.foldl_toArray']
  rw [← List.reverse_reverse xs]
  generalize xs.reverse = xs
  simp only [List.filter_reverse, List.map_reverse, List.foldl_reverse]
  induction xs with
  | nil => rfl
  | cons x l ih =>
    simp only [List.filter_cons, List.foldr_cons]
    split <;> simp_all

@[simp] theorem filter_append {p : α → Bool} (xs ys : Array α) (w : stop = xs.size + ys.size) :
    filter p (xs ++ ys) 0 stop = filter p xs ++ filter p ys := by
  subst w
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp [List.filter_append]

theorem filter_eq_append_iff {p : α → Bool} :
    filter p xs = ys ++ zs ↔ ∃ as bs, xs = as ++ bs ∧ filter p as = ys ∧ filter p bs = zs := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  rcases zs with ⟨zs⟩
  simp only [List.size_toArray, List.filter_toArray', List.append_toArray, mk.injEq,
    List.filter_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    refine ⟨l₁.toArray, l₂.toArray, by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, h₁, h₂, h₃⟩
    refine ⟨l₁, l₂, by simp_all⟩

theorem filter_eq_push_iff {p : α → Bool} {xs ys : Array α} {a : α} :
    filter p xs = ys.push a ↔
      ∃ as bs, xs = as.push a ++ bs ∧ filter p as = ys ∧ p a ∧ (∀ x, x ∈ bs → ¬p x) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.size_toArray, List.filter_toArray', List.push_toArray, mk.injEq, Bool.not_eq_true]
  rw [← List.reverse_inj]
  simp only [← List.filter_reverse]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [List.filter_eq_cons_iff]
  constructor
  · rintro ⟨l₁, l₂, h₁, h₂, h₃, h₄⟩
    refine ⟨l₂.reverse.toArray, l₁.reverse.toArray, by simp_all⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, h₁, h₂, h₃, h₄⟩
    refine ⟨l₂.reverse, l₁.reverse, by simp_all⟩

theorem mem_of_mem_filter {a : α} {xs : Array α} (h : a ∈ filter p xs) : a ∈ xs :=
  (mem_filter.mp h).1

@[simp]
theorem size_filter_pos_iff {xs : Array α} {p : α → Bool} :
    0 < (filter p xs).size ↔ ∃ x ∈ xs, p x := by
  rcases xs with ⟨xs⟩
  simp

@[simp]
theorem size_filter_lt_size_iff_exists {xs : Array α} {p : α → Bool} :
    (filter p xs).size < xs.size ↔ ∃ x ∈ xs, ¬p x := by
  rcases xs with ⟨xs⟩
  simp

/-! ### filterMap -/

@[congr]
theorem filterMap_congr {as bs : Array α} (h : as = bs)
    {f : α → Option β} {g : α → Option β} (h' : f = g) {start stop start' stop' : Nat}
    (h₁ : start = start') (h₂ : stop = stop') :
    filterMap f as start stop = filterMap g bs start' stop' := by
  congr

@[simp] theorem toList_filterMap' (f : α → Option β) (xs : Array α) (w : stop = xs.size) :
    (xs.filterMap f 0 stop).toList = xs.toList.filterMap f := by
  subst w
  dsimp only [filterMap, filterMapM]
  rw [← foldlM_toList]
  generalize xs.toList = xs
  have this : ∀ as : Array β, (Id.run (List.foldlM (m := Id) ?_ as xs)).toList =
    as.toList ++ List.filterMap f xs := ?_
  exact this #[]
  induction xs
  · simp_all [Id.run]
  · simp_all [Id.run, List.filterMap_cons]
    split <;> simp_all

theorem toList_filterMap (f : α → Option β) (xs : Array α) :
    (xs.filterMap f).toList = xs.toList.filterMap f := by
  simp [toList_filterMap']


@[simp] theorem _root_.List.filterMap_toArray' (f : α → Option β) (l : List α) (h : stop = l.length) :
    l.toArray.filterMap f 0 stop = (l.filterMap f).toArray := by
  apply ext'
  simp [h]

theorem _root_.List.filterMap_toArray (f : α → Option β) (l : List α) :
    l.toArray.filterMap f = (l.filterMap f).toArray := by
  simp

@[simp] theorem filterMap_push_none {f : α → Option β} {a : α} {xs : Array α}
    (h : f a = none) (w : stop = xs.size + 1) :
    filterMap f (xs.push a) 0 stop = filterMap f xs := by
  subst w
  rcases xs with ⟨xs⟩
  simp [h]

@[simp] theorem filterMap_push_some {f : α → Option β} {a : α} {xs : Array α} {b : β}
    (h : f a = some b) (w : stop = xs.size + 1) :
    filterMap f (xs.push a) 0 stop = (filterMap f xs).push b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [h]

@[simp] theorem filterMap_eq_map (f : α → β) (w : stop = as.size) :
    filterMap (some ∘ f) as 0 stop = map f as := by
  subst w
  cases as
  simp

/-- Variant of `filterMap_eq_map` with `some ∘ f` expanded out to a lambda. -/
@[simp]
theorem filterMap_eq_map' (f : α → β) (w : stop = as.size) :
    filterMap (fun x => some (f x)) as 0 stop = map f as :=
  filterMap_eq_map f w

theorem filterMap_some_fun : filterMap (some : α → Option α) = id := by
  funext xs
  cases xs
  simp

@[simp] theorem filterMap_some (xs : Array α) : filterMap some xs = xs := by
  cases xs
  simp

theorem map_filterMap_some_eq_filterMap_isSome (f : α → Option β) (xs : Array α) :
    (xs.filterMap f).map some = (xs.map f).filter fun b => b.isSome := by
  cases xs
  simp [List.map_filterMap_some_eq_filter_map_isSome]

theorem size_filterMap_le (f : α → Option β) (xs : Array α) :
    (xs.filterMap f).size ≤ xs.size := by
  cases xs
  simp [List.length_filterMap_le]

@[simp] theorem filterMap_size_eq_size {xs : Array α} :
    (xs.filterMap f).size = xs.size ↔ ∀ a, a ∈ xs → (f a).isSome := by
  cases xs
  simp [List.filterMap_length_eq_length]

@[simp]
theorem filterMap_eq_filter (p : α → Bool) (w : stop = as.size) :
    filterMap (Option.guard (p ·)) as 0 stop = filter p as := by
  subst w
  cases as
  simp

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (xs : Array α) :
    filterMap g (filterMap f xs) = filterMap (fun x => (f x).bind g) xs := by
  cases xs
  simp [List.filterMap_filterMap]

theorem map_filterMap (f : α → Option β) (g : β → γ) (xs : Array α) :
    map g (filterMap f xs) = filterMap (fun x => (f x).map g) xs := by
  cases xs
  simp [List.map_filterMap]

@[simp] theorem filterMap_map (f : α → β) (g : β → Option γ) (xs : Array α) :
    filterMap g (map f xs) = filterMap (g ∘ f) xs := by
  cases xs
  simp [List.filterMap_map]

theorem filter_filterMap (f : α → Option β) (p : β → Bool) (xs : Array α) :
    filter p (filterMap f xs) = filterMap (fun x => (f x).filter p) xs := by
  cases xs
  simp [List.filter_filterMap]

theorem filterMap_filter (p : α → Bool) (f : α → Option β) (xs : Array α) :
    filterMap f (filter p xs) = filterMap (fun x => if p x then f x else none) xs := by
  cases xs
  simp [List.filterMap_filter]

@[simp] theorem mem_filterMap {f : α → Option β} {xs : Array α} {b : β} :
    b ∈ filterMap f xs ↔ ∃ a, a ∈ xs ∧ f a = some b := by
  simp only [mem_def, toList_filterMap, List.mem_filterMap]

theorem forall_mem_filterMap {f : α → Option β} {xs : Array α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ filterMap f xs), P i) ↔ ∀ (j) (_ : j ∈ xs) (b), f j = some b → P b := by
  simp only [mem_filterMap, forall_exists_index, and_imp]
  rw [forall_comm]
  apply forall_congr'
  intro a
  rw [forall_comm]

@[simp] theorem filterMap_append {α β : Type _} {xs ys : Array α} (f : α → Option β) (w : stop = xs.size + ys.size) :
    filterMap f (xs ++ ys) 0 stop = filterMap f xs ++ filterMap f ys := by
  subst w
  cases xs
  cases ys
  simp

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (xs : Array α) : map g (filterMap f xs) = xs := by simp only [map_filterMap, H, filterMap_some, id]

theorem forall_none_of_filterMap_eq_empty (h : filterMap f xs = #[]) : ∀ x ∈ xs, f x = none := by
  cases xs
  simpa using h

@[simp] theorem filterMap_eq_nil_iff {xs : Array α} : filterMap f xs = #[] ↔ ∀ a, a ∈ xs → f a = none := by
  cases xs
  simp

theorem filterMap_eq_push_iff {f : α → Option β} {xs : Array α} {ys : Array β} {b : β} :
    filterMap f xs = ys.push b ↔ ∃ as a bs,
      xs = as.push a ++ bs ∧ filterMap f as = ys ∧ f a = some b ∧ (∀ x, x ∈ bs → f x = none) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.size_toArray, List.filterMap_toArray', List.push_toArray, mk.injEq]
  rw [← List.reverse_inj]
  simp only [← List.filterMap_reverse]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [List.filterMap_eq_cons_iff]
  constructor
  · rintro ⟨l₁, a, l₂, h₁, h₂, h₃, h₄⟩
    refine ⟨l₂.reverse.toArray, a, l₁.reverse.toArray, by simp_all⟩
  · rintro ⟨⟨l₁⟩, a, ⟨l₂⟩, h₁, h₂, h₃, h₄⟩
    refine ⟨l₂.reverse, a, l₁.reverse, by simp_all⟩

@[simp]
theorem size_filterMap_pos_iff {xs : Array α} {f : α → Option β} :
    0 < (filterMap f xs).size ↔ ∃ (x : α) (_ : x ∈ xs) (b : β), f x = some b := by
  rcases xs with ⟨xs⟩
  simp

@[simp]
theorem size_filterMap_lt_size_iff_exists {xs : Array α} {f : α → Option β} :
    (filterMap f xs).size < xs.size ↔ ∃ (x : α) (_ : x ∈ xs), f x = none := by
  rcases xs with ⟨xs⟩
  simp

/-! ### singleton -/

@[simp] theorem singleton_def (v : α) : Array.singleton v = #[v] := rfl

/-! ### append -/

@[simp] theorem size_append (xs ys : Array α) : (xs ++ ys).size = xs.size + ys.size := by
  simp only [size, toList_append, List.length_append]

@[simp] theorem push_append {a : α} {xs ys : Array α} : (xs ++ ys).push a = xs ++ ys.push a := by
  cases xs
  cases ys
  simp

theorem append_push {xs ys : Array α} {a : α} : xs ++ ys.push a = (xs ++ ys).push a := by
  cases xs
  cases ys
  simp

theorem toArray_append {xs : List α} {ys : Array α} :
    xs.toArray ++ ys = (xs ++ ys.toList).toArray := by
  rcases ys with ⟨ys⟩
  simp

@[simp] theorem toArray_eq_append_iff {xs : List α} {as bs : Array α} :
    xs.toArray = as ++ bs ↔ xs = as.toList ++ bs.toList := by
  cases as
  cases bs
  simp

@[simp] theorem append_eq_toArray_iff {xs ys : Array α} {as : List α} :
    xs ++ ys = as.toArray ↔ xs.toList ++ ys.toList = as := by
  cases xs
  cases ys
  simp

theorem singleton_eq_toArray_singleton (a : α) : #[a] = [a].toArray := rfl

@[simp] theorem empty_append_fun : ((#[] : Array α) ++ ·) = id := by
  funext ⟨l⟩
  simp

@[simp] theorem mem_append {a : α} {xs ys : Array α} : a ∈ xs ++ ys ↔ a ∈ xs ∨ a ∈ ys := by
  simp only [mem_def, toList_append, List.mem_append]

theorem mem_append_left {a : α} {xs : Array α} (ys : Array α) (h : a ∈ xs) : a ∈ xs ++ ys :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (xs : Array α) {ys : Array α} (h : a ∈ ys) : a ∈ xs ++ ys :=
  mem_append.2 (Or.inr h)

theorem not_mem_append {a : α} {xs ys : Array α} (h₁ : a ∉ xs) (h₂ : a ∉ ys) : a ∉ xs ++ ys :=
  mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

/--
See also `eq_push_append_of_mem`, which proves a stronger version
in which the initial array must not contain the element.
-/
theorem append_of_mem {a : α} {xs : Array α} (h : a ∈ xs) : ∃ as bs : Array α, xs = as.push a ++ bs := by
  obtain ⟨xs', ys', w⟩ := List.append_of_mem (l := xs.toList) (by simpa using h)
  replace w := congrArg List.toArray w
  refine ⟨xs'.toArray, ys'.toArray, by simp_all⟩

theorem mem_iff_append {a : α} {xs : Array α} : a ∈ xs ↔ ∃ as bs : Array α, xs = as.push a ++ bs :=
  ⟨append_of_mem, fun ⟨as, bs, e⟩ => e ▸ by simp⟩

theorem forall_mem_append {p : α → Prop} {xs ys : Array α} :
    (∀ (x) (_ : x ∈ xs ++ ys), p x) ↔ (∀ (x) (_ : x ∈ xs), p x) ∧ (∀ (x) (_ : x ∈ ys), p x) := by
  simp only [mem_append, or_imp, forall_and]

theorem getElem_append {xs ys : Array α} (h : i < (xs ++ ys).size) :
    (xs ++ ys)[i] = if h' : i < xs.size then xs[i] else ys[i - xs.size]'(by simp at h; omega) := by
  cases xs; cases ys
  simp [List.getElem_append]

theorem getElem_append_left {xs ys : Array α} {h : i < (xs ++ ys).size} (hlt : i < xs.size) :
    (xs ++ ys)[i] = xs[i] := by
  simp only [← getElem_toList]
  have h' : i < (xs.toList ++ ys.toList).length := by rwa [← length_toList, toList_append] at h
  conv => rhs; rw [← List.getElem_append_left (bs := ys.toList) (h' := h')]
  apply List.get_of_eq; rw [toList_append]

theorem getElem_append_right {xs ys : Array α} {h : i < (xs ++ ys).size} (hle : xs.size ≤ i) :
    (xs ++ ys)[i] = ys[i - xs.size]'(Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) := by
  simp only [← getElem_toList]
  have h' : i < (xs.toList ++ ys.toList).length := by rwa [← length_toList, toList_append] at h
  conv => rhs; rw [← List.getElem_append_right (h₁ := hle) (h₂ := h')]
  apply List.get_of_eq; rw [toList_append]

theorem getElem?_append_left {xs ys : Array α} {i : Nat} (hn : i < xs.size) :
    (xs ++ ys)[i]? = xs[i]? := by
  have hn' : i < (xs ++ ys).size := Nat.lt_of_lt_of_le hn <|
    size_append .. ▸ Nat.le_add_right ..
  simp_all [getElem?_eq_getElem, getElem_append]

theorem getElem?_append_right {xs ys : Array α} {i : Nat} (h : xs.size ≤ i) :
    (xs ++ ys)[i]? = ys[i - xs.size]? := by
  cases xs
  cases ys
  simp at h
  simp [List.getElem?_append_right, h]

theorem getElem?_append {xs ys : Array α} {i : Nat} :
    (xs ++ ys)[i]? = if i < xs.size then xs[i]? else ys[i - xs.size]? := by
  split <;> rename_i h
  · exact getElem?_append_left h
  · exact getElem?_append_right (by simpa using h)

/-- Variant of `getElem_append_left` useful for rewriting from the small array to the big array. -/
theorem getElem_append_left' (ys : Array α) {xs : Array α} {i : Nat} (hi : i < xs.size) :
    xs[i] = (xs ++ ys)[i]'(by simpa using Nat.lt_add_right ys.size hi) := by
  rw [getElem_append_left] <;> simp

/-- Variant of `getElem_append_right` useful for rewriting from the small array to the big array. -/
theorem getElem_append_right' (xs : Array α) {ys : Array α} {i : Nat} (hi : i < ys.size) :
    ys[i] = (xs ++ ys)[i + xs.size]'(by simpa [Nat.add_comm] using Nat.add_lt_add_left hi _) := by
  rw [getElem_append_right] <;> simp [*, Nat.le_add_left]

theorem getElem_of_append {xs ys zs : Array α} (eq : xs = ys.push a ++ zs) (h : ys.size = i) :
    xs[i]'(eq ▸ h ▸ by simp +arith) = a := Option.some.inj <| by
  rw [← getElem?_eq_getElem, eq, getElem?_append_left (by simp; omega), ← h]
  simp

@[simp] theorem append_singleton {a : α} {as : Array α} : as ++ #[a] = as.push a := rfl

@[simp] theorem append_singleton_assoc {a : α} {xs ys : Array α} : xs ++ (#[a] ++ ys) = xs.push a ++ ys := by
  rw [← append_assoc, append_singleton]

theorem push_eq_append {a : α} {as : Array α} : as.push a = as ++ #[a] := rfl

theorem append_inj {xs₁ xs₂ ys₁ ys₂ : Array α} (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : xs₁.size = xs₂.size) :
    xs₁ = xs₂ ∧ ys₁ = ys₂ := by
  rcases xs₁ with ⟨s₁⟩
  rcases xs₂ with ⟨s₂⟩
  rcases ys₁ with ⟨t₁⟩
  rcases ys₂ with ⟨t₂⟩
  simpa using List.append_inj (by simpa using h) (by simpa using hl)

theorem append_inj_right {xs₁ xs₂ ys₁ ys₂ : Array α}
    (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : xs₁.size = xs₂.size) : ys₁ = ys₂ :=
  (append_inj h hl).right

theorem append_inj_left {xs₁ xs₂ ys₁ ys₂ : Array α}
    (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : xs₁.size = xs₂.size) : xs₁ = xs₂ :=
  (append_inj h hl).left

/-- Variant of `append_inj` instead requiring equality of the sizes of the second arrays. -/
theorem append_inj' {xs₁ xs₂ ys₁ ys₂ : Array α} (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : ys₁.size = ys₂.size) :
    xs₁ = xs₂ ∧ ys₁ = ys₂ :=
  append_inj h <| @Nat.add_right_cancel _ ys₁.size _ <| by
    let hap := congrArg size h; simp only [size_append, ← hl] at hap; exact hap

/-- Variant of `append_inj_right` instead requiring equality of the sizes of the second arrays. -/
theorem append_inj_right' {xs₁ xs₂ ys₁ ys₂ : Array α}
    (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : ys₁.size = ys₂.size) : ys₁ = ys₂ :=
  (append_inj' h hl).right

/-- Variant of `append_inj_left` instead requiring equality of the sizes of the second arrays. -/
theorem append_inj_left' {xs₁ xs₂ ys₁ ys₂ : Array α}
    (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : ys₁.size = ys₂.size) : xs₁ = xs₂ :=
  (append_inj' h hl).left

theorem append_right_inj {ys₁ ys₂ : Array α} (xs) : xs ++ ys₁ = xs ++ ys₂ ↔ ys₁ = ys₂ :=
  ⟨fun h => append_inj_right h rfl, congrArg _⟩

theorem append_left_inj {xs₁ xs₂ : Array α} (ys) : xs₁ ++ ys = xs₂ ++ ys ↔ xs₁ = xs₂ :=
  ⟨fun h => append_inj_left' h rfl, congrArg (· ++ _)⟩

@[simp] theorem append_left_eq_self {xs ys : Array α} : xs ++ ys = ys ↔ xs = #[] := by
  rw [← append_left_inj (xs₁ := xs), empty_append]

@[simp] theorem self_eq_append_left {xs ys : Array α} : ys = xs ++ ys ↔ xs = #[] := by
  rw [eq_comm, append_left_eq_self]

@[simp] theorem append_right_eq_self {xs ys : Array α} : xs ++ ys = xs ↔ ys = #[] := by
  rw [← append_right_inj (ys₁ := ys), append_empty]

@[simp] theorem self_eq_append_right {xs ys : Array α} : xs = xs ++ ys ↔ ys = #[] := by
  rw [eq_comm, append_right_eq_self]

@[simp] theorem append_eq_empty_iff {xs ys : Array α} : xs ++ ys = #[] ↔ xs = #[] ∧ ys = #[] := by
  cases xs <;> simp

@[simp] theorem empty_eq_append_iff {xs ys : Array α} : #[] = xs ++ ys ↔ xs = #[] ∧ ys = #[] := by
  rw [eq_comm, append_eq_empty_iff]

theorem append_ne_empty_of_left_ne_empty {xs ys : Array α} (h : xs ≠ #[]) : xs ++ ys ≠ #[] := by
  simp_all

theorem append_ne_empty_of_right_ne_empty {xs ys : Array α} (h : ys ≠ #[]) : xs ++ ys ≠ #[] := by
  simp_all

theorem append_eq_push_iff {xs ys zs : Array α} {x : α} :
    xs ++ ys = zs.push x ↔ (ys = #[] ∧ xs = zs.push x) ∨ (∃ ys', ys = ys'.push x ∧ zs = xs ++ ys') := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  rcases zs with ⟨zs⟩
  simp only [List.append_toArray, List.push_toArray, mk.injEq, List.append_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro (⟨as, rfl, rfl⟩ | ⟨bs, rfl, h⟩)
    · right; exact ⟨⟨as⟩, by simp⟩
    · rw [List.singleton_eq_append_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h
      · right; exact ⟨#[], by simp⟩
      · left; simp
  · rintro (⟨rfl, rfl⟩ | ⟨bs, h, rfl⟩)
    · right; exact ⟨[x], by simp⟩
    · left; refine ⟨bs.toList, ?_⟩
      replace h := congrArg Array.toList h
      simp_all

theorem push_eq_append_iff {xs ys zs : Array α} {x : α} :
    zs.push x = xs ++ ys ↔ (ys = #[] ∧ xs = zs.push x) ∨ (∃ ys', ys = ys'.push x ∧ zs = xs ++ ys') := by
  rw [eq_comm, append_eq_push_iff]

theorem append_eq_singleton_iff {xs ys : Array α} {x : α} :
    xs ++ ys = #[x] ↔ (xs = #[] ∧ ys = #[x]) ∨ (xs = #[x] ∧ ys = #[]) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, mk.injEq, List.append_eq_singleton_iff, toArray_eq_append_iff]

theorem singleton_eq_append_iff {xs ys : Array α} {x : α} :
    #[x] = xs ++ ys ↔ (xs = #[] ∧ ys = #[x]) ∨ (xs = #[x] ∧ ys = #[]) := by
  rw [eq_comm, append_eq_singleton_iff]

theorem append_eq_append_iff {ws xs ys zs : Array α} :
    ws ++ xs = ys ++ zs ↔ (∃ as, ys = ws ++ as ∧ xs = as ++ zs) ∨ ∃ cs, ws = ys ++ cs ∧ zs = cs ++ xs := by
  rcases ws with ⟨ws⟩
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  rcases zs with ⟨zs⟩
  simp only [List.append_toArray, mk.injEq, List.append_eq_append_iff, toArray_eq_append_iff]
  constructor
  · rintro (⟨as, rfl, rfl⟩ | ⟨cs, rfl, rfl⟩)
    · left; exact ⟨⟨as⟩, by simp⟩
    · right; exact ⟨⟨cs⟩, by simp⟩
  · rintro (⟨as, rfl, rfl⟩ | ⟨cs, rfl, rfl⟩)
    · left; exact ⟨as.toList, by simp⟩
    · right; exact ⟨cs.toList, by simp⟩

theorem set_append {xs ys : Array α} {i : Nat} {x : α} (h : i < (xs ++ ys).size) :
    (xs ++ ys).set i x =
      if h' : i < xs.size then
        xs.set i x ++ ys
      else
        xs ++ ys.set (i - xs.size) x (by simp at h; omega) := by
  rcases xs with ⟨s⟩
  rcases ys with ⟨t⟩
  simp only [List.append_toArray, List.set_toArray, List.set_append]
  split <;> simp

@[simp] theorem set_append_left {xs ys : Array α} {i : Nat} {x : α} (h : i < xs.size) :
    (xs ++ ys).set i x (by simp; omega) = xs.set i x ++ ys := by
  simp [set_append, h]

@[simp] theorem set_append_right {xs ys : Array α} {i : Nat} {x : α}
    (h' : i < (xs ++ ys).size) (h : xs.size ≤ i) :
    (xs ++ ys).set i x = xs ++ ys.set (i - xs.size) x (by simp at h'; omega) := by
  rw [set_append, dif_neg (by omega)]

theorem setIfInBounds_append {xs ys : Array α} {i : Nat} {x : α} :
    (xs ++ ys).setIfInBounds i x =
      if i < xs.size then
        xs.setIfInBounds i x ++ ys
      else
        xs ++ ys.setIfInBounds (i - xs.size) x := by
  rcases xs with ⟨s⟩
  rcases ys with ⟨t⟩
  simp only [List.append_toArray, List.setIfInBounds_toArray, List.set_append]
  split <;> simp

@[simp] theorem setIfInBounds_append_left {xs ys : Array α} {i : Nat} {x : α} (h : i < xs.size) :
    (xs ++ ys).setIfInBounds i x = xs.setIfInBounds i x ++ ys := by
  simp [setIfInBounds_append, h]

@[simp] theorem setIfInBounds_append_right {xs ys : Array α} {i : Nat} {x : α} (h : xs.size ≤ i) :
    (xs ++ ys).setIfInBounds i x = xs ++ ys.setIfInBounds (i - xs.size) x := by
  rw [setIfInBounds_append, if_neg (by omega)]

theorem filterMap_eq_append_iff {f : α → Option β} :
    filterMap f xs = ys ++ zs ↔ ∃ as bs, xs = as ++ bs ∧ filterMap f as = ys ∧ filterMap f bs = zs := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  rcases zs with ⟨zs⟩
  simp only [List.size_toArray, List.filterMap_toArray', List.append_toArray, mk.injEq,
    List.filterMap_eq_append_iff, toArray_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨⟨l₁⟩, ⟨l₂⟩, by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, rfl, h₁, h₂⟩
    exact ⟨l₁, l₂, by simp_all⟩

theorem append_eq_filterMap_iff {f : α → Option β} :
    xs ++ ys = filterMap f zs ↔
      ∃ as bs, zs = as ++ bs ∧ filterMap f as = xs ∧ filterMap f bs = ys := by
  rw [eq_comm, filterMap_eq_append_iff]

@[simp] theorem map_append (f : α → β) (xs ys : Array α) :
    map f (xs ++ ys) = map f xs ++ map f ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

theorem map_eq_append_iff {f : α → β} :
    map f xs = ys ++ zs ↔ ∃ as bs, xs = as ++ bs ∧ map f as = ys ∧ map f bs = zs := by
  simp only [← filterMap_eq_map, filterMap_eq_append_iff]

theorem append_eq_map_iff {f : α → β} :
    xs ++ ys = map f zs ↔ ∃ as bs, zs = as ++ bs ∧ map f as = xs ∧ map f bs = ys := by
  rw [eq_comm, map_eq_append_iff]

/-! ### flatten -/

@[simp] theorem flatten_empty : (#[] : Array (Array α)).flatten = #[] := by simp [flatten]; rfl

@[simp] theorem toList_flatten {xss : Array (Array α)} :
    xss.flatten.toList = (xss.toList.map toList).flatten := by
  dsimp [flatten]
  simp only [← foldl_toList]
  generalize xss.toList = l
  have : ∀ as : Array α, (List.foldl ?_ as l).toList = as.toList ++ ?_ := ?_
  exact this #[]
  induction l with
  | nil => simp
  | cons as => induction as.toList <;> simp [*]

@[simp] theorem flatten_map_toArray (L : List (List α)) :
    (L.toArray.map List.toArray).flatten = L.flatten.toArray := by
  apply ext'
  simp [Function.comp_def]

@[simp] theorem flatten_toArray_map (L : List (List α)) :
    (L.map List.toArray).toArray.flatten = L.flatten.toArray := by
  rw [← flatten_map_toArray]
  simp

-- We set this to lower priority so that `flatten_toArray_map` is applied first when relevant.
@[simp 500] theorem flatten_toArray (l : List (Array α)) :
    l.toArray.flatten = (l.map Array.toList).flatten.toArray := by
  apply ext'
  simp

@[simp] theorem size_flatten (xss : Array (Array α)) : xss.flatten.size = (xss.map size).sum := by
  cases xss using array₂_induction
  simp [Function.comp_def]

@[simp] theorem flatten_singleton (xs : Array α) : #[xs].flatten = xs := by simp [flatten]; rfl

theorem mem_flatten : ∀ {xss : Array (Array α)}, a ∈ xss.flatten ↔ ∃ xs, xs ∈ xss ∧ a ∈ xs := by
  simp only [mem_def, toList_flatten, List.mem_flatten, List.mem_map]
  intro xss
  constructor
  · rintro ⟨_, ⟨xs, m, rfl⟩, h⟩
    exact ⟨xs, m, h⟩
  · rintro ⟨xs, h₁, h₂⟩
    refine ⟨xs.toList, ⟨⟨xs, h₁, rfl⟩, h₂⟩⟩

@[simp] theorem flatten_eq_empty_iff {xss : Array (Array α)} : xss.flatten = #[] ↔ ∀ xs ∈ xss, xs = #[] := by
  induction xss using array₂_induction
  simp

@[simp] theorem empty_eq_flatten_iff {xss : Array (Array α)} : #[] = xss.flatten ↔ ∀ xs ∈ xss, xs = #[] := by
  rw [eq_comm, flatten_eq_empty_iff]

theorem flatten_ne_empty_iff {xss : Array (Array α)} : xss.flatten ≠ #[] ↔ ∃ xs, xs ∈ xss ∧ xs ≠ #[] := by
  simp

theorem exists_of_mem_flatten : x ∈ flatten xss → ∃ xs, xs ∈ xss ∧ x ∈ xs := mem_flatten.1

theorem mem_flatten_of_mem (ml : xs ∈ xss) (ma : a ∈ xs) : a ∈ flatten xss := mem_flatten.2 ⟨xs, ml, ma⟩

theorem forall_mem_flatten {p : α → Prop} {xss : Array (Array α)} :
    (∀ (x) (_ : x ∈ flatten xss), p x) ↔ ∀ (xs) (_ : xs ∈ xss) (x) (_ : x ∈ xs), p x := by
  simp only [mem_flatten, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatten_eq_flatMap {xss : Array (Array α)} : flatten xss = xss.flatMap id := by
  induction xss using array₂_induction
  rw [flatten_toArray_map, List.flatten_eq_flatMap]
  simp [List.flatMap_map]

@[simp] theorem map_flatten (f : α → β) (xss : Array (Array α)) :
    (flatten xss).map f = (map (map f) xss).flatten := by
  induction xss using array₂_induction with
  | of xss =>
    simp only [flatten_toArray_map, List.map_toArray, List.map_flatten, List.map_map,
      Function.comp_def]
    rw [← Function.comp_def, ← List.map_map, flatten_toArray_map]

@[simp] theorem filterMap_flatten (f : α → Option β) (xss : Array (Array α)) (w : stop = xss.flatten.size) :
    filterMap f (flatten xss) 0 stop = flatten (map (filterMap f) xss) := by
  subst w
  induction xss using array₂_induction
  simp only [flatten_toArray_map, List.size_toArray, List.length_flatten, List.filterMap_toArray',
    List.filterMap_flatten, List.map_toArray, List.map_map, Function.comp_def]
  rw [← Function.comp_def, ← List.map_map, flatten_toArray_map]

@[simp] theorem filter_flatten (p : α → Bool) (xss : Array (Array α)) (w : stop = xss.flatten.size) :
    filter p (flatten xss) 0 stop = flatten (map (filter p) xss) := by
  subst w
  induction xss using array₂_induction
  simp only [flatten_toArray_map, List.size_toArray, List.length_flatten, List.filter_toArray',
    List.filter_flatten, List.map_toArray, List.map_map, Function.comp_def]
  rw [← Function.comp_def, ← List.map_map, flatten_toArray_map]

theorem flatten_filter_not_isEmpty {xss : Array (Array α)} :
    flatten (xss.filter fun l => !l.isEmpty) = xss.flatten := by
  induction xss using array₂_induction
  simp [List.filter_map, Function.comp_def, List.flatten_filter_not_isEmpty]

theorem flatten_filter_ne_empty [DecidablePred fun xs : Array α => xs ≠ #[]] {xss : Array (Array α)} :
    flatten (xss.filter fun xs => xs ≠ #[]) = xss.flatten := by
  simp only [ne_eq, ← isEmpty_iff, Bool.not_eq_true, Bool.decide_eq_false,
    flatten_filter_not_isEmpty]

@[simp] theorem flatten_append (xss₁ xss₂ : Array (Array α)) :
    flatten (xss₁ ++ xss₂) = flatten xss₁ ++ flatten xss₂ := by
  induction xss₁ using array₂_induction
  induction xss₂ using array₂_induction
  simp [← List.map_append]

theorem flatten_push (xss : Array (Array α)) (xs : Array α) :
    flatten (xss.push xs) = flatten xss ++ xs := by
  induction xss using array₂_induction
  rcases xs with ⟨l⟩
  have this : [l.toArray] = [l].map List.toArray := by simp
  simp only [List.push_toArray, flatten_toArray_map, List.append_toArray]
  rw [this, ← List.map_append, flatten_toArray_map]
  simp

theorem flatten_flatten {xss : Array (Array (Array α))} : flatten (flatten xss) = flatten (map flatten xss) := by
  induction xss using array₃_induction with
  | of xss =>
    rw [flatten_toArray_map]
    have : (xss.map (fun xs => xs.map List.toArray)).flatten = xss.flatten.map List.toArray := by
      induction xss with
      | nil => simp
      | cons xs xss ih =>
        simp only [List.map_cons, List.flatten_cons, ih, List.map_append]
    rw [this, flatten_toArray_map, List.flatten_flatten, ← List.map_toArray, Array.map_map,
      ← List.map_toArray, map_map, Function.comp_def]
    simp only [Function.comp_apply, flatten_toArray_map]
    rw [List.map_toArray, ← Function.comp_def, ← List.map_map, flatten_toArray_map]

theorem flatten_eq_push_iff {xss : Array (Array α)} {ys : Array α} {y : α} :
    xss.flatten = ys.push y ↔
      ∃ (as : Array (Array α)) (bs : Array α) (cs : Array (Array α)),
        xss = as.push (bs.push y) ++ cs ∧ (∀ xs, xs ∈ cs → xs = #[]) ∧ ys = as.flatten ++ bs := by
  induction xss using array₂_induction with
  | of xs =>
    rcases ys with ⟨ys⟩
    rw [flatten_toArray_map, List.push_toArray, mk.injEq, List.flatten_eq_append_iff]
    constructor
    · rintro (⟨as, bs, rfl, rfl, h⟩ | ⟨as, bs, c, cs, ds, rfl, rfl, h⟩)
      · rw [List.singleton_eq_flatten_iff] at h
        obtain ⟨xs, ys, rfl, h₁, h₂⟩ := h
        exact ⟨((as ++ xs).map List.toArray).toArray, #[], (ys.map List.toArray).toArray, by simp,
          by simpa using h₂, by rw [flatten_toArray_map]; simpa⟩
      · rw [List.singleton_eq_append_iff] at h
        obtain (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) := h
        · simp at h₁
        · simp at h₁ h₂
          obtain ⟨rfl, rfl⟩ := h₁
          exact ⟨(as.map List.toArray).toArray, bs.toArray, (ds.map List.toArray).toArray, by simpa⟩
    · rintro ⟨as, bs, cs, h₁, h₂, h₃⟩
      replace h₁ := congrArg (List.map Array.toList) (congrArg Array.toList h₁)
      simp [Function.comp_def] at h₁
      subst h₁
      replace h₃ := congrArg Array.toList h₃
      simp at h₃
      subst h₃
      right
      exact ⟨(as.map Array.toList).toList, bs.toList, y, [], (cs.map Array.toList).toList, by simpa⟩

theorem push_eq_flatten_iff {xss : Array (Array α)} {ys : Array α} {y : α} :
    ys.push y = xss.flatten ↔
      ∃ (as : Array (Array α)) (bs : Array α) (cs : Array (Array α)),
        xss = as.push (bs.push y) ++ cs ∧ (∀ xs, xs ∈ cs → xs = #[]) ∧ ys = as.flatten ++ bs := by
  rw [eq_comm, flatten_eq_push_iff]

-- For now we omit `flatten_eq_append_iff`,
-- because it is not easily obtainable from `List.flatten_eq_append_iff`.
-- theorem flatten_eq_append_iff {xs : Array (Array α)} {ys zs : Array α} :
--     xs.flatten = ys ++ zs ↔
--       (∃ as bs, xs = as ++ bs ∧ ys = as.flatten ∧ zs = bs.flatten) ∨
--         ∃ (as : Array (Array α)) (bs : Array α) (c : α) (cs : Array α) (ds : Array (Array α)),
--           xs = as.push ((bs.push c ++ cs)) ++ ds ∧ ys = as.flatten ++ bs.push c ∧
--           zs = cs ++ ds.flatten := by sorry


/-- Two arrays of subarrays are equal iff their flattens coincide, as well as the sizes of the
subarrays. -/
theorem eq_iff_flatten_eq {xss₁ xss₂ : Array (Array α)} :
    xss₁ = xss₂ ↔ xss₁.flatten = xss₂.flatten ∧ map size xss₁ = map size xss₂ := by
  cases xss₁ using array₂_induction with
  | of L =>
    cases xss₂ using array₂_induction with
    | of L' =>
      simp [Function.comp_def, ← List.eq_iff_flatten_eq]
      rw [List.map_inj_right]
      simp +contextual

/-! ### flatMap -/

theorem flatMap_def (xs : Array α) (f : α → Array β) : xs.flatMap f = flatten (map f xs) := by
  rcases xs with ⟨l⟩
  simp [flatten_toArray, Function.comp_def, List.flatMap_def]

theorem flatMap_toList (xs : Array α) (f : α → List β) :
    xs.toList.flatMap f = (xs.flatMap (fun a => (f a).toArray)).toList := by
  rcases xs with ⟨l⟩
  simp

@[simp] theorem toList_flatMap (xs : Array α) (f : α → Array β) :
    (xs.flatMap f).toList = xs.toList.flatMap fun a => (f a).toList := by
  rcases xs with ⟨l⟩
  simp

@[simp] theorem flatMap_id (xss : Array (Array α)) : xss.flatMap id = xss.flatten := by simp [flatMap_def]

@[simp] theorem flatMap_id' (xss : Array (Array α)) : xss.flatMap (fun xs => xs) = xss.flatten := by simp [flatMap_def]

@[simp]
theorem size_flatMap (xs : Array α) (f : α → Array β) :
    (xs.flatMap f).size = sum (map (fun a => (f a).size) xs) := by
  rcases xs with ⟨l⟩
  simp [Function.comp_def]

@[simp] theorem mem_flatMap {f : α → Array β} {b} {xs : Array α} : b ∈ xs.flatMap f ↔ ∃ a, a ∈ xs ∧ b ∈ f a := by
  simp [flatMap_def, mem_flatten]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_flatMap {b : β} {xs : Array α} {f : α → Array β} :
    b ∈ xs.flatMap f → ∃ a, a ∈ xs ∧ b ∈ f a := mem_flatMap.1

theorem mem_flatMap_of_mem {b : β} {xs : Array α} {f : α → Array β} {a} (al : a ∈ xs) (h : b ∈ f a) :
    b ∈ xs.flatMap f := mem_flatMap.2 ⟨a, al, h⟩

@[simp]
theorem flatMap_eq_empty_iff {xs : Array α} {f : α → Array β} : xs.flatMap f = #[] ↔ ∀ x ∈ xs, f x = #[] := by
  rw [flatMap_def, flatten_eq_empty_iff]
  simp

theorem forall_mem_flatMap {p : β → Prop} {xs : Array α} {f : α → Array β} :
    (∀ (x) (_ : x ∈ xs.flatMap f), p x) ↔ ∀ (a) (_ : a ∈ xs) (b) (_ : b ∈ f a), p b := by
  simp only [mem_flatMap, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatMap_singleton (f : α → Array β) (x : α) : #[x].flatMap f = f x := by
  simp

@[simp] theorem flatMap_singleton' (xs : Array α) : (xs.flatMap fun x => #[x]) = xs := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem flatMap_append (xs ys : Array α) (f : α → Array β) :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

theorem flatMap_assoc {α β} (xs : Array α) (f : α → Array β) (g : β → Array γ) :
    (xs.flatMap f).flatMap g = xs.flatMap fun x => (f x).flatMap g := by
  rcases xs with ⟨xs⟩
  simp [List.flatMap_assoc, ← toList_flatMap]

theorem map_flatMap (f : β → γ) (g : α → Array β) (xs : Array α) :
    (xs.flatMap g).map f = xs.flatMap fun a => (g a).map f := by
  rcases xs with ⟨xs⟩
  simp [List.map_flatMap]

theorem flatMap_map (f : α → β) (g : β → Array γ) (xs : Array α) :
    (xs.map f).flatMap g = xs.flatMap (fun a => g (f a)) := by
  rcases xs with ⟨xs⟩
  simp [List.flatMap_map]

theorem map_eq_flatMap {α β} (f : α → β) (xs : Array α) : map f xs = xs.flatMap fun x => #[f x] := by
  simp only [← map_singleton]
  rw [← flatMap_singleton' xs, map_flatMap, flatMap_singleton']

theorem filterMap_flatMap {β γ} (xs : Array α) (g : α → Array β) (f : β → Option γ) :
    (xs.flatMap g).filterMap f = xs.flatMap fun a => (g a).filterMap f := by
  rcases xs with ⟨xs⟩
  simp [List.filterMap_flatMap]

theorem filter_flatMap (xs : Array α) (g : α → Array β) (f : β → Bool) :
    (xs.flatMap g).filter f = xs.flatMap fun a => (g a).filter f := by
  rcases xs with ⟨xs⟩
  simp [List.filter_flatMap]

theorem flatMap_eq_foldl (f : α → Array β) (xs : Array α) :
    xs.flatMap f = xs.foldl (fun acc a => acc ++ f a) #[] := by
  rcases xs with ⟨xs⟩
  simp only [List.flatMap_toArray, List.flatMap_eq_foldl, List.size_toArray, List.foldl_toArray']
  suffices ∀ l, (List.foldl (fun acc a => acc ++ (f a).toList) l xs).toArray =
      List.foldl (fun acc a => acc ++ f a) l.toArray xs by
    simpa using this []
  induction xs with
  | nil => simp
  | cons a l ih =>
    intro l'
    rw [List.foldl_cons, ih]
    simp [toArray_append]

/-! ### mkArray -/

@[simp] theorem mkArray_one : mkArray 1 a = #[a] := rfl

/-- Variant of `mkArray_succ` that prepends `a` at the beginning of the array. -/
theorem mkArray_succ' : mkArray (n + 1) a = #[a] ++ mkArray n a := by
  apply Array.ext'
  simp [List.replicate_succ]

@[simp] theorem mem_mkArray {a b : α} {n} : b ∈ mkArray n a ↔ n ≠ 0 ∧ b = a := by
  unfold mkArray
  simp only [mem_toArray, List.mem_replicate]

theorem eq_of_mem_mkArray {a b : α} {n} (h : b ∈ mkArray n a) : b = a := (mem_mkArray.1 h).2

theorem forall_mem_mkArray {p : α → Prop} {a : α} {n} :
    (∀ b, b ∈ mkArray n a → p b) ↔ n = 0 ∨ p a := by
  cases n <;> simp [mem_mkArray]

@[simp] theorem mkArray_succ_ne_empty (n : Nat) (a : α) : mkArray (n+1) a ≠ #[] := by
  simp [mkArray_succ]

@[simp] theorem mkArray_eq_empty_iff {n : Nat} (a : α) : mkArray n a = #[] ↔ n = 0 := by
  cases n <;> simp

@[simp] theorem getElem?_mkArray_of_lt {n : Nat} {i : Nat} (h : i < n) : (mkArray n a)[i]? = some a := by
  simp [getElem?_mkArray, h]

@[simp] theorem mkArray_inj : mkArray n a = mkArray m b ↔ n = m ∧ (n = 0 ∨ a = b) := by
  rw [← toList_inj]
  simp

theorem eq_mkArray_of_mem {a : α} {xs : Array α} (h : ∀ (b) (_ : b ∈ xs), b = a) : xs = mkArray xs.size a := by
  rw [← toList_inj]
  simpa using List.eq_replicate_of_mem (by simpa using h)

theorem eq_mkArray_iff {a : α} {n} {xs : Array α} :
    xs = mkArray n a ↔ xs.size = n ∧ ∀ (b) (_ : b ∈ xs), b = a := by
  rw [← toList_inj]
  simpa using List.eq_replicate_iff (l := xs.toList)

theorem map_eq_mkArray_iff {xs : Array α} {f : α → β} {b : β} :
    xs.map f = mkArray xs.size b ↔ ∀ x ∈ xs, f x = b := by
  simp [eq_mkArray_iff]

@[simp] theorem map_const (xs : Array α) (b : β) : map (Function.const α b) xs = mkArray xs.size b :=
  map_eq_mkArray_iff.mpr fun _ _ => rfl

@[simp] theorem map_const_fun (x : β) : map (Function.const α x) = (mkArray ·.size x) := by
  funext xs
  simp

/-- Variant of `map_const` using a lambda rather than `Function.const`. -/
-- This can not be a `@[simp]` lemma because it would fire on every `List.map`.
theorem map_const' (xs : Array α) (b : β) : map (fun _ => b) xs = mkArray xs.size b :=
  map_const xs b

@[simp] theorem set_mkArray_self : (mkArray n a).set i a h = mkArray n a := by
  apply Array.ext'
  simp

@[simp] theorem setIfInBounds_mkArray_self : (mkArray n a).setIfInBounds i a = mkArray n a := by
  apply Array.ext'
  simp

@[simp] theorem mkArray_append_mkArray : mkArray n a ++ mkArray m a = mkArray (n + m) a := by
  apply Array.ext'
  simp

theorem append_eq_mkArray_iff {xs ys : Array α} {a : α} :
    xs ++ ys = mkArray n a ↔
      xs.size + ys.size = n ∧ xs = mkArray xs.size a ∧ ys = mkArray ys.size a := by
  simp [← toList_inj, List.append_eq_replicate_iff]

theorem mkArray_eq_append_iff {xs ys : Array α} {a : α} :
    mkArray n a = xs ++ ys ↔
      xs.size + ys.size = n ∧ xs = mkArray xs.size a ∧ ys = mkArray ys.size a := by
  rw [eq_comm, append_eq_mkArray_iff]

@[simp] theorem map_mkArray : (mkArray n a).map f = mkArray n (f a) := by
  apply Array.ext'
  simp

theorem filter_mkArray (w : stop = n) :
    (mkArray n a).filter p 0 stop = if p a then mkArray n a else #[] := by
  apply Array.ext'
  simp only [w, toList_filter', toList_mkArray, List.filter_replicate]
  split <;> simp_all

@[simp] theorem filter_mkArray_of_pos (w : stop = n) (h : p a) :
    (mkArray n a).filter p 0 stop = mkArray n a := by
  simp [filter_mkArray, h, w]

@[simp] theorem filter_mkArray_of_neg (w : stop = n) (h : ¬ p a) :
    (mkArray n a).filter p 0 stop = #[] := by
  simp [filter_mkArray, h, w]

theorem filterMap_mkArray {f : α → Option β} (w : stop = n := by simp) :
    (mkArray n a).filterMap f 0 stop = match f a with | none => #[] | .some b => mkArray n b := by
  apply Array.ext'
  simp only [w, size_mkArray, toList_filterMap', toList_mkArray, List.filterMap_replicate]
  split <;> simp_all

-- This is not a useful `simp` lemma because `b` is unknown.
theorem filterMap_mkArray_of_some {f : α → Option β} (h : f a = some b) :
    (mkArray n a).filterMap f = mkArray n b := by
  simp [filterMap_mkArray, h]

@[simp] theorem filterMap_mkArray_of_isSome {f : α → Option β} (h : (f a).isSome) :
    (mkArray n a).filterMap f = mkArray n (Option.get _ h) := by
  match w : f a, h with
  | some b, _ => simp [filterMap_mkArray, h, w]

@[simp] theorem filterMap_mkArray_of_none {f : α → Option β} (h : f a = none) :
    (mkArray n a).filterMap f = #[] := by
  simp [filterMap_mkArray, h]

@[simp] theorem flatten_mkArray_empty : (mkArray n (#[] : Array α)).flatten = #[] := by
  rw [← toList_inj]
  simp

@[simp] theorem flatten_mkArray_singleton : (mkArray n #[a]).flatten = mkArray n a := by
  rw [← toList_inj]
  simp

@[simp] theorem flatten_mkArray_mkArray : (mkArray n (mkArray m a)).flatten = mkArray (n * m) a := by
  rw [← toList_inj]
  simp

theorem flatMap_mkArray {β} (f : α → Array β) : (mkArray n a).flatMap f = (mkArray n (f a)).flatten := by
  rw [← toList_inj]
  simp [flatMap_toList, List.flatMap_replicate]

@[simp] theorem isEmpty_mkArray : (mkArray n a).isEmpty = decide (n = 0) := by
  rw [← List.toArray_replicate, List.isEmpty_toArray]
  simp

@[simp] theorem sum_mkArray_nat (n : Nat) (a : Nat) : (mkArray n a).sum = n * a := by
  rw [← List.toArray_replicate, List.sum_toArray]
  simp

/-! ### Preliminaries about `swap` needed for `reverse`. -/

theorem getElem?_swap (xs : Array α) (i j : Nat) (hi hj) (k : Nat) : (xs.swap i j hi hj)[k]? =
    if j = k then some xs[i] else if i = k then some xs[j] else xs[k]? := by
  simp [swap_def, getElem?_set]

/-! ### reverse -/

@[simp] theorem size_reverse (xs : Array α) : xs.reverse.size = xs.size := by
  let rec go (as : Array α) (i j) : (reverse.loop as i j).size = as.size := by
    rw [reverse.loop]
    if h : i < j then
      simp [(go · (i+1) ⟨j-1, ·⟩), h]
    else simp [h]
    termination_by j - i
  simp only [reverse]; split <;> simp [go]

@[simp] theorem toList_reverse (xs : Array α) : xs.reverse.toList = xs.toList.reverse := by
  let rec go (as : Array α) (i j hj)
      (h : i + j + 1 = xs.size) (h₂ : as.size = xs.size)
      (H : ∀ k, as.toList[k]? = if i ≤ k ∧ k ≤ j then xs.toList[k]? else xs.toList.reverse[k]?)
      (k : Nat) : (reverse.loop as i ⟨j, hj⟩).toList[k]? = xs.toList.reverse[k]? := by
    rw [reverse.loop]; dsimp only; split <;> rename_i h₁
    · match j with | j+1 => ?_
      simp only [Nat.add_sub_cancel]
      rw [(go · (i+1) j)]
      · rwa [Nat.add_right_comm i]
      · simp [size_swap, h₂]
      · intro k
        rw [getElem?_toList, getElem?_swap]
        simp only [H, ← getElem_toList, ← List.getElem?_eq_getElem, Nat.le_of_lt h₁,
          ← getElem?_toList]
        split <;> rename_i h₂
        · simp only [← h₂, Nat.not_le.2 (Nat.lt_succ_self _), Nat.le_refl, and_false]
          exact (List.getElem?_reverse' (j+1) i (Eq.trans (by simp +arith) h)).symm
        split <;> rename_i h₃
        · simp only [← h₃, Nat.not_le.2 (Nat.lt_succ_self _), Nat.le_refl, false_and]
          exact (List.getElem?_reverse' i (j+1) (Eq.trans (by simp +arith) h)).symm
        simp only [Nat.succ_le, Nat.lt_iff_le_and_ne.trans (and_iff_left h₃),
          Nat.lt_succ.symm.trans (Nat.lt_iff_le_and_ne.trans (and_iff_left (Ne.symm h₂)))]
    · rw [H]; split <;> rename_i h₂
      · cases Nat.le_antisymm (Nat.not_lt.1 h₁) (Nat.le_trans h₂.1 h₂.2)
        cases Nat.le_antisymm h₂.1 h₂.2
        exact (List.getElem?_reverse' _ _ h).symm
      · rfl
    termination_by j - i
  simp only [reverse]
  split
  · match xs with | ⟨[]⟩ | ⟨[_]⟩ => rfl
  · have := Nat.sub_add_cancel (Nat.le_of_not_le ‹_›)
    refine List.ext_getElem? <| go _ _ _ _ (by simp [this]) rfl fun k => ?_
    split
    · rfl
    · rename_i h
      simp only [← show k < _ + 1 ↔ _ from Nat.lt_succ (n := xs.size - 1), this, Nat.zero_le,
        true_and, Nat.not_lt] at h
      rw [List.getElem?_eq_none_iff.2 ‹_›, List.getElem?_eq_none_iff.2 (xs.toList.length_reverse ▸ ‹_›)]

@[simp] theorem _root_.List.reverse_toArray (l : List α) : l.toArray.reverse = l.reverse.toArray := by
  apply ext'
  simp only [toList_reverse]

@[simp] theorem reverse_push (xs : Array α) (a : α) : (xs.push a).reverse = #[a] ++ xs.reverse := by
  cases xs
  simp

@[simp] theorem mem_reverse {x : α} {xs : Array α} : x ∈ xs.reverse ↔ x ∈ xs := by
  cases xs
  simp

@[simp] theorem getElem_reverse (xs : Array α) (i : Nat) (hi : i < xs.reverse.size) :
    (xs.reverse)[i] = xs[xs.size - 1 - i]'(by simp at hi; omega) := by
  cases xs
  simp

@[simp] theorem reverse_eq_empty_iff {xs : Array α} : xs.reverse = #[] ↔ xs = #[] := by
  cases xs
  simp

theorem reverse_ne_empty_iff {xs : Array α} : xs.reverse ≠ #[] ↔ xs ≠ #[] :=
  not_congr reverse_eq_empty_iff

@[simp] theorem isEmpty_reverse {xs : Array α} : xs.reverse.isEmpty = xs.isEmpty := by
  cases xs
  simp

/-- Variant of `getElem?_reverse` with a hypothesis giving the linear relation between the indices. -/
theorem getElem?_reverse' {xs : Array α} (i j) (h : i + j + 1 = xs.size) : xs.reverse[i]? = xs[j]? := by
  rcases xs with ⟨xs⟩
  simp at h
  simp only [List.reverse_toArray, List.getElem?_toArray]
  rw [List.getElem?_reverse' (l := xs) _ _ h]

@[simp]
theorem getElem?_reverse {xs : Array α} {i} (h : i < xs.size) :
    xs.reverse[i]? = xs[xs.size - 1 - i]? := by
  cases xs
  simp_all

@[simp] theorem reverse_reverse (xs : Array α) : xs.reverse.reverse = xs := by
  cases xs
  simp

theorem reverse_eq_iff {xs ys : Array α} : xs.reverse = ys ↔ xs = ys.reverse := by
  constructor <;> (rintro rfl; simp)

@[simp] theorem reverse_inj {xs ys : Array α} : xs.reverse = ys.reverse ↔ xs = ys := by
  simp [reverse_eq_iff]

@[simp] theorem reverse_eq_push_iff {xs : Array α} {ys : Array α} {a : α} :
    xs.reverse = ys.push a ↔ xs = #[a] ++ ys.reverse := by
  rw [reverse_eq_iff, reverse_push]

@[simp] theorem map_reverse (f : α → β) (xs : Array α) : xs.reverse.map f = (xs.map f).reverse := by
  cases xs <;> simp [*]

/-- Variant of `filter_reverse` with a hypothesis giving the stop condition. -/
@[simp] theorem filter_reverse' (p : α → Bool) (xs : Array α) (w : stop = xs.size) :
     (xs.reverse.filter p 0 stop) = (xs.filter p).reverse := by
  subst w
  cases xs
  simp

theorem filter_reverse (p : α → Bool) (xs : Array α) : (xs.reverse.filter p) = (xs.filter p).reverse := by
  cases xs
  simp

/-- Variant of `filterMap_reverse` with a hypothesis giving the stop condition. -/
@[simp] theorem filterMap_reverse' (f : α → Option β) (xs : Array α) (w : stop = xs.size) :
    (xs.reverse.filterMap f 0 stop) = (xs.filterMap f).reverse := by
  subst w
  cases xs
  simp

theorem filterMap_reverse (f : α → Option β) (xs : Array α) : (xs.reverse.filterMap f) = (xs.filterMap f).reverse := by
  cases xs
  simp

@[simp] theorem reverse_append (xs ys : Array α) : (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  cases xs
  cases ys
  simp

@[simp] theorem reverse_eq_append_iff {xs ys zs : Array α} :
    xs.reverse = ys ++ zs ↔ xs = zs.reverse ++ ys.reverse := by
  cases xs
  cases ys
  cases zs
  simp

/-- Reversing a flatten is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_flatten (xss : Array (Array α)) :
    xss.flatten.reverse = (xss.map reverse).reverse.flatten := by
  cases xss using array₂_induction
  simp [flatten_toArray, List.reverse_flatten, Function.comp_def]

/-- Flattening a reverse is the same as reversing all parts and reversing the flattened result. -/
theorem flatten_reverse (xss : Array (Array α)) :
    xss.reverse.flatten = (xss.map reverse).flatten.reverse := by
  cases xss using array₂_induction
  simp [flatten_toArray, List.flatten_reverse, Function.comp_def]

theorem reverse_flatMap {β} (xs : Array α) (f : α → Array β) :
    (xs.flatMap f).reverse = xs.reverse.flatMap (reverse ∘ f) := by
  cases xs
  simp [List.reverse_flatMap, Function.comp_def]

theorem flatMap_reverse {β} (xs : Array α) (f : α → Array β) :
    (xs.reverse.flatMap f) = (xs.flatMap (reverse ∘ f)).reverse := by
  cases xs
  simp [List.flatMap_reverse, Function.comp_def]

@[simp] theorem reverse_mkArray (n) (a : α) : reverse (mkArray n a) = mkArray n a := by
  rw [← toList_inj]
  simp

/-! ### extract -/

theorem extract_loop_zero (xs ys : Array α) (start : Nat) : extract.loop xs 0 start ys = ys := by
  rw [extract.loop]; split <;> rfl

theorem extract_loop_succ (xs ys : Array α) (size start : Nat) (h : start < xs.size) :
    extract.loop xs (size+1) start ys = extract.loop xs size (start+1) (ys.push xs[start]) := by
  rw [extract.loop, dif_pos h]; rfl

theorem extract_loop_of_ge (xs ys : Array α) (size start : Nat) (h : start ≥ xs.size) :
    extract.loop xs size start ys = ys := by
  rw [extract.loop, dif_neg (Nat.not_lt_of_ge h)]

theorem extract_loop_eq_aux (xs ys : Array α) (size start : Nat) :
    extract.loop xs size start ys = ys ++ extract.loop xs size start #[] := by
  induction size using Nat.recAux generalizing start ys with
  | zero => rw [extract_loop_zero, extract_loop_zero, append_empty]
  | succ size ih =>
    if h : start < xs.size then
      rw [extract_loop_succ (h := h), ih (ys.push _), push_eq_append_singleton]
      rw [extract_loop_succ (h := h), ih (#[].push _), push_eq_append_singleton, empty_append]
      rw [append_assoc]
    else
      rw [extract_loop_of_ge (h := Nat.le_of_not_lt h)]
      rw [extract_loop_of_ge (h := Nat.le_of_not_lt h)]
      rw [append_empty]

theorem extract_loop_eq (xs ys : Array α) (size start : Nat) (h : start + size ≤ xs.size) :
  extract.loop xs size start ys = ys ++ xs.extract start (start + size) := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [extract_loop_eq_aux, Nat.min_eq_left h, Nat.add_sub_cancel_left]

theorem size_extract_loop (xs ys : Array α) (size start : Nat) :
    (extract.loop xs size start ys).size = ys.size + min size (xs.size - start) := by
  induction size using Nat.recAux generalizing start ys with
  | zero => rw [extract_loop_zero, Nat.zero_min, Nat.add_zero]
  | succ size ih =>
    if h : start < xs.size then
      rw [extract_loop_succ (h:=h), ih, size_push, Nat.add_assoc, ←Nat.add_min_add_left,
        Nat.sub_succ, Nat.one_add, Nat.one_add, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
    else
      have h := Nat.le_of_not_gt h
      rw [extract_loop_of_ge (h:=h), Nat.sub_eq_zero_of_le h, Nat.min_zero, Nat.add_zero]

@[simp] theorem size_extract (xs : Array α) (start stop : Nat) :
    (xs.extract start stop).size = min stop xs.size - start := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [size_extract_loop, size_empty, Nat.zero_add, Nat.sub_min_sub_right, Nat.min_assoc,
    Nat.min_self]

theorem getElem_extract_loop_lt_aux (xs ys : Array α) (size start : Nat) (hlt : i < ys.size) :
    i < (extract.loop xs size start ys).size := by
  rw [size_extract_loop]
  apply Nat.lt_of_lt_of_le hlt
  exact Nat.le_add_right ..

theorem getElem_extract_loop_lt (xs ys : Array α) (size start : Nat) (hlt : i < ys.size)
    (h := getElem_extract_loop_lt_aux xs ys size start hlt) :
    (extract.loop xs size start ys)[i] = ys[i] := by
  apply Eq.trans _ (getElem_append_left (ys := extract.loop xs size start #[]) hlt)
  · rw [size_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)
  · congr; rw [extract_loop_eq_aux]

theorem getElem_extract_loop_ge_aux (xs ys : Array α) (size start : Nat) (hge : i ≥ ys.size)
    (h : i < (extract.loop xs size start ys).size) : start + i - ys.size < xs.size := by
  have h : i < ys.size + (xs.size - start) := by
      apply Nat.lt_of_lt_of_le h
      rw [size_extract_loop]
      apply Nat.add_le_add_left
      exact Nat.min_le_right ..
  rw [Nat.add_sub_assoc hge]
  apply Nat.add_lt_of_lt_sub'
  exact Nat.sub_lt_left_of_lt_add hge h

theorem getElem_extract_loop_ge (xs ys : Array α) (size start : Nat) (hge : i ≥ ys.size)
    (h : i < (extract.loop xs size start ys).size)
    (h' := getElem_extract_loop_ge_aux xs ys size start hge h) :
    (extract.loop xs size start ys)[i] = xs[start + i - ys.size] := by
  induction size using Nat.recAux generalizing start ys with
  | zero =>
    rw [size_extract_loop, Nat.zero_min, Nat.add_zero] at h
    omega
  | succ size ih =>
    have : start < xs.size := by
      apply Nat.lt_of_le_of_lt (Nat.le_add_right start (i - ys.size))
      rwa [← Nat.add_sub_assoc hge]
    have : i < (extract.loop xs size (start+1) (ys.push xs[start])).size := by
      rwa [← extract_loop_succ]
    have heq : (extract.loop xs (size+1) start ys)[i] =
        (extract.loop xs size (start+1) (ys.push xs[start]))[i] := by
      congr 1; rw [extract_loop_succ]
    rw [heq]
    if hi : ys.size = i then
      cases hi
      have h₁ : ys.size < (ys.push xs[start]).size := by rw [size_push]; exact Nat.lt_succ_self ..
      have h₂ : ys.size < (extract.loop xs size (start+1) (ys.push xs[start])).size := by
        rw [size_extract_loop]; apply Nat.lt_of_lt_of_le h₁; exact Nat.le_add_right ..
      have h : (extract.loop xs size (start + 1) (ys.push xs[start]))[ys.size] = xs[start] := by
        rw [getElem_extract_loop_lt xs (ys.push xs[start]) size (start+1) h₁ h₂, getElem_push_eq]
      rw [h]; congr; rw [Nat.add_sub_cancel]
    else
      have hge : ys.size + 1 ≤ i := Nat.lt_of_le_of_ne hge hi
      rw [ih (ys.push xs[start]) (start+1) ((size_push ..).symm ▸ hge)]
      congr 1; rw [size_push, Nat.add_right_comm, Nat.add_sub_add_right]

theorem getElem_extract_aux {xs : Array α} {start stop : Nat} (h : i < (xs.extract start stop).size) :
    start + i < xs.size := by
  rw [size_extract] at h; apply Nat.add_lt_of_lt_sub'; apply Nat.lt_of_lt_of_le h
  apply Nat.sub_le_sub_right; apply Nat.min_le_right

@[simp] theorem getElem_extract {xs : Array α} {start stop : Nat}
    (h : i < (xs.extract start stop).size) :
    (xs.extract start stop)[i] = xs[start + i]'(getElem_extract_aux h) :=
  show (extract.loop xs (min stop xs.size - start) start #[])[i]
    = xs[start + i]'(getElem_extract_aux h) by rw [getElem_extract_loop_ge]; rfl; exact Nat.zero_le _

theorem getElem?_extract {xs : Array α} {start stop : Nat} :
    (xs.extract start stop)[i]? = if i < min stop xs.size - start then xs[start + i]? else none := by
  simp only [getElem?_def, size_extract, getElem_extract]
  split
  · split
    · rfl
    · omega
  · rfl

@[congr] theorem extract_congr {xs ys : Array α}
    (w : xs = ys) (h : start = start') (h' : stop = stop') :
    xs.extract start stop = ys.extract start' stop' := by
  subst w h h'
  rfl

@[simp] theorem toList_extract (xs : Array α) (start stop : Nat) :
    (xs.extract start stop).toList = xs.toList.extract start stop := by
  apply List.ext_getElem
  · simp only [length_toList, size_extract, List.length_take, List.length_drop]
    omega
  · intros n h₁ h₂
    simp

@[simp] theorem extract_size (xs : Array α) : xs.extract 0 xs.size = xs := by
  apply ext
  · rw [size_extract, Nat.min_self, Nat.sub_zero]
  · intros; rw [getElem_extract]; congr; rw [Nat.zero_add]

@[deprecated extract_size (since := "2025-01-19")]
abbrev extract_all := @extract_size

theorem extract_empty_of_stop_le_start (xs : Array α) {start stop : Nat} (h : stop ≤ start) :
    xs.extract start stop = #[] := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.zero_min, extract_loop_zero]

theorem extract_empty_of_size_le_start (xs : Array α) {start stop : Nat} (h : xs.size ≤ start) :
    xs.extract start stop = #[] := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.min_zero, extract_loop_zero]

@[simp] theorem extract_empty (start stop : Nat) : (#[] : Array α).extract start stop = #[] :=
  extract_empty_of_size_le_start _ (Nat.zero_le _)

@[simp] theorem _root_.List.extract_toArray (l : List α) (start stop : Nat) :
    l.toArray.extract start stop = (l.extract start stop).toArray := by
  apply ext'
  simp

/-! ### foldlM and foldrM -/

theorem foldlM_start_stop {m} [Monad m] (xs : Array α) (f : β → α → m β) (b) (start stop : Nat) :
    xs.foldlM f b start stop = (xs.extract start stop).foldlM f b := by
  unfold foldlM
  simp only [Nat.sub_zero, size_extract, Nat.le_refl, ↓reduceDIte]
  suffices foldlM.loop f xs (min stop xs.size) (by omega) (min stop xs.size - start) start b =
      foldlM.loop f (xs.extract start stop) (min stop xs.size - start) (by simp) (min stop xs.size - start) 0 b by
    split
    · have : min stop xs.size = stop := by omega
      simp_all
    · have : min stop xs.size = xs.size := by omega
      simp_all
  revert b
  suffices ∀ (b : β) (i k) (w : i + k = min stop xs.size - start),
    foldlM.loop f xs (min stop xs.size) (by omega) i (start + k) b =
      foldlM.loop f (xs.extract start stop) (min stop xs.size - start) (by simp) i k b by
    intro b
    simpa using this b (min stop xs.size - start) 0 (by omega)
  intro b i k w
  induction i generalizing b k with
  | zero =>
    simp only [Nat.zero_add] at w
    subst k
    simp [foldlM.loop]
  | succ i ih =>
    unfold foldlM.loop
    rw [dif_pos (by omega), dif_pos (by omega)]
    split <;> rename_i h
    · rfl
    · simp at h
      subst h
      simp only [getElem_extract]
      congr
      funext b
      specialize ih b (k + 1) (by omega)
      simp [← Nat.add_assoc] at ih
      rw [ih]

theorem foldrM_start_stop {m} [Monad m] (xs : Array α) (f : α → β → m β) (b) (start stop : Nat) :
    xs.foldrM f b start stop = (xs.extract stop start).foldrM f b := by
  unfold foldrM
  simp only [size_extract, Nat.le_refl, ↓reduceDIte]
  suffices stop ≤ min start xs.size →
      foldrM.fold f xs stop (min start xs.size) (by omega) b =
        foldrM.fold f (xs.extract stop start) 0 (min start xs.size - stop) (by simp) b by
    split
    · split
      · rw [if_pos (by omega)]
        have h : min start xs.size = start := by omega
        specialize this (by omega)
        simp_all
      · rw [if_neg (by omega)]
    · split
      · rw [if_pos (by omega)]
        have h : min start xs.size = xs.size := by omega
        specialize this (by omega)
        simp_all
      · rw [if_neg (by omega)]
  revert b
  suffices ∀ (b : β) (i) (w : stop + i ≤ min start xs.size),
      foldrM.fold f xs stop (stop + i) (by omega) b =
        foldrM.fold f (xs.extract stop start) 0 i (by simp; omega) b by
    intro b w
    specialize this b (min start xs.size - stop)
    have h : stop + (min start xs.size - stop) = min start xs.size := by omega
    simp_all
  intro b i w
  induction i generalizing b with
  | zero =>
    unfold foldrM.fold
    simp
  | succ i ih =>
    unfold foldrM.fold
    simp only [beq_iff_eq, Nat.add_right_eq_self, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_eq,
      getElem_extract]
    congr
    funext b
    simp [ih b (by omega)]

@[congr] theorem foldlM_congr {m} [Monad m] {f g : β → α → m β} {b : β} {xs xs' : Array α}
    (w : xs = xs')
    (h : ∀ x y, f x y = g x y) (hstart : start = start') (hstop : stop = stop') :
    xs.foldlM f b start stop = xs'.foldlM g b start' stop' := by
  subst hstart hstop w
  rcases xs with ⟨xs⟩
  rw [foldlM_start_stop, List.extract_toArray]
  simp only [List.size_toArray, List.length_take, List.length_drop, List.foldlM_toArray']
  rw [foldlM_start_stop, List.extract_toArray]
  simp only [List.size_toArray, List.length_take, List.length_drop, List.foldlM_toArray']
  congr
  funext b a
  simp_all

@[congr] theorem foldrM_congr {m} [Monad m] {f g : α → β → m β} {b : β} {xs xs' : Array α}
    (w : xs = xs')
    (h : ∀ x y, f x y = g x y) (hstart : start = start') (hstop : stop = stop') :
    xs.foldrM f b start stop = xs'.foldrM g b start' stop' := by
  subst hstart hstop w
  rcases xs with ⟨xs⟩
  rw [foldrM_start_stop, List.extract_toArray]
  simp only [List.size_toArray, List.length_take, List.length_drop, List.foldrM_toArray']
  rw [foldrM_start_stop, List.extract_toArray]
  simp only [List.size_toArray, List.length_take, List.length_drop, List.foldrM_toArray']
  congr
  funext b a
  simp_all

/-- Variant of `foldlM_append` with a side condition for the `stop` argument. -/
@[simp] theorem foldlM_append' [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (xs xs' : Array α)
    (w : stop = xs.size + xs'.size) :
    (xs ++ xs').foldlM f b 0 stop = xs.foldlM f b >>= xs'.foldlM f := by
  subst w
  rcases xs with ⟨xs⟩
  rcases xs' with ⟨xs'⟩
  simp

theorem foldlM_append [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (xs xs' : Array α) :
    (xs ++ xs').foldlM f b = xs.foldlM f b >>= xs'.foldlM f := by
  simp

@[simp] theorem foldlM_loop_empty [Monad m] (f : β → α → m β) (init : β) (i j : Nat) :
    foldlM.loop f #[] s h i j init = pure init := by
  unfold foldlM.loop; split
  · split
    · rfl
    · simp at h
      omega
  · rfl

@[simp] theorem foldlM_empty [Monad m] (f : β → α → m β) (init : β) :
    foldlM f init #[] start stop = return init := by
  simp [foldlM]

@[simp] theorem foldrM_fold_empty [Monad m] (f : α → β → m β) (init : β) (i j : Nat) (h) :
    foldrM.fold f #[] i j h init = pure init := by
  unfold foldrM.fold
  split <;> rename_i h₁
  · rfl
  · split <;> rename_i h₂
    · rfl
    · simp at h₂

@[simp] theorem foldrM_empty [Monad m] (f : α → β → m β) (init : β) :
    foldrM f init #[] start stop = return init := by
  simp [foldrM]

/-- Variant of `foldlM_push` with a side condition for the `stop` argument. -/
@[simp] theorem foldlM_push' [Monad m] [LawfulMonad m] (xs : Array α) (a : α) (f : β → α → m β) (b)
    (w : stop = xs.size + 1) :
    (xs.push a).foldlM f b 0 stop = xs.foldlM f b >>= fun b => f b a := by
  subst w
  simp [← append_singleton]

theorem foldlM_push [Monad m] [LawfulMonad m] (xs : Array α) (a : α) (f : β → α → m β) (b) :
    (xs.push a).foldlM f b = xs.foldlM f b >>= fun b => f b a := by
  simp

theorem foldl_eq_foldlM (f : β → α → β) (b) (xs : Array α) :
    xs.foldl f b start stop = xs.foldlM (m := Id) f b start stop := by
  simp [foldl, Id.run]

theorem foldr_eq_foldrM (f : α → β → β) (b) (xs : Array α) :
    xs.foldr f b start stop = xs.foldrM (m := Id) f b start stop := by
  simp [foldr, Id.run]

@[simp] theorem id_run_foldlM (f : β → α → Id β) (b) (xs : Array α) :
    Id.run (xs.foldlM f b start stop) = xs.foldl f b start stop := (foldl_eq_foldlM f b xs).symm

@[simp] theorem id_run_foldrM (f : α → β → Id β) (b) (xs : Array α) :
    Id.run (xs.foldrM f b start stop) = xs.foldr f b start stop := (foldr_eq_foldrM f b xs).symm

/-- Variant of `foldlM_reverse` with a side condition for the `stop` argument. -/
@[simp] theorem foldlM_reverse' [Monad m] (xs : Array α) (f : β → α → m β) (b)
    (w : stop = xs.size) :
    xs.reverse.foldlM f b 0 stop = xs.foldrM (fun x y => f y x) b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.foldlM_reverse]

/-- Variant of `foldrM_reverse` with a side condition for the `start` argument. -/
@[simp] theorem foldrM_reverse' [Monad m] (xs : Array α) (f : α → β → m β) (b)
    (w : start = xs.size) :
    xs.reverse.foldrM f b start 0 = xs.foldlM (fun x y => f y x) b := by
  subst w
  rcases xs with ⟨xs⟩
  simp [List.foldrM_reverse]

theorem foldlM_reverse [Monad m] (xs : Array α) (f : β → α → m β) (b) :
    xs.reverse.foldlM f b = xs.foldrM (fun x y => f y x) b := by
  simp

theorem foldrM_reverse [Monad m] (xs : Array α) (f : α → β → m β) (b) :
    xs.reverse.foldrM f b = xs.foldlM (fun x y => f y x) b := by
  rcases xs with ⟨xs⟩
  simp

theorem foldrM_push [Monad m] (f : α → β → m β) (init : β) (xs : Array α) (a : α) :
    (xs.push a).foldrM f init = f a init >>= xs.foldrM f := by
  simp only [foldrM_eq_reverse_foldlM_toList, push_toList, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.foldlM_cons, List.foldlM_reverse]

/--
Variant of `foldrM_push` with `h : start = arr.size + 1`
rather than `(arr.push a).size` as the argument.
-/
@[simp] theorem foldrM_push' [Monad m] (f : α → β → m β) (init : β) (xs : Array α) (a : α)
    {start} (h : start = xs.size + 1) :
    (xs.push a).foldrM f init start = f a init >>= xs.foldrM f := by
  simp [← foldrM_push, h]

/-! ### foldl / foldr -/

-- This proof is the pure version of `Array.SatisfiesM_foldlM` in Batteries,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldl_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive i.1 b → motive (i.1 + 1) (f b as[i])) :
    motive as.size (as.foldl f init) := by
  let rec go {i j b} (h₁ : j ≤ as.size) (h₂ : as.size ≤ i + j) (H : motive j b) :
    (motive as.size) (foldlM.loop (m := Id) f as as.size (Nat.le_refl _) i j b) := by
    unfold foldlM.loop; split
    · next hj =>
      split
      · cases Nat.not_le_of_gt (by simp [hj]) h₂
      · exact go hj (by rwa [Nat.succ_add] at h₂) (hf ⟨j, hj⟩ b H)
    · next hj => exact Nat.le_antisymm h₁ (Nat.ge_of_not_lt hj) ▸ H
  simpa [foldl, foldlM] using go (Nat.zero_le _) (Nat.le_refl _) h0

-- This proof is the pure version of `Array.SatisfiesM_foldrM` in Batteries,
-- reproduced to avoid a dependency on `SatisfiesM`.
theorem foldr_induction
    {as : Array α} (motive : Nat → β → Prop) {init : β} (h0 : motive as.size init) {f : α → β → β}
    (hf : ∀ i : Fin as.size, ∀ b, motive (i.1 + 1) b → motive i.1 (f as[i] b)) :
    motive 0 (as.foldr f init) := by
  let rec go {i b} (hi : i ≤ as.size) (H : motive i b) :
    (motive 0) (foldrM.fold (m := Id) f as 0 i hi b) := by
    unfold foldrM.fold; simp; split
    · next hi => exact (hi ▸ H)
    · next hi =>
      split; {simp at hi}
      · next i hi' =>
        exact go _ (hf ⟨i, hi'⟩ b H)
  simp [foldr, foldrM]; split; {exact go _ h0}
  · next h => exact (Nat.eq_zero_of_not_pos h ▸ h0)

@[congr]
theorem foldl_congr {as bs : Array α} (h₀ : as = bs) {f g : β → α → β} (h₁ : f = g)
     {a b : β} (h₂ : a = b) {start start' stop stop' : Nat} (h₃ : start = start') (h₄ : stop = stop') :
    as.foldl f a start stop = bs.foldl g b start' stop' := by
  congr

@[congr]
theorem foldr_congr {as bs : Array α} (h₀ : as = bs) {f g : α → β → β} (h₁ : f = g)
     {a b : β} (h₂ : a = b) {start start' stop stop' : Nat} (h₃ : start = start') (h₄ : stop = stop') :
    as.foldr f a start stop = bs.foldr g b start' stop' := by
  congr

theorem foldr_push (f : α → β → β) (init : β) (xs : Array α) (a : α) :
    (xs.push a).foldr f init = xs.foldr f (f a init) := foldrM_push ..

/--
Variant of `foldr_push` with the `h : start = arr.size + 1`
rather than `(arr.push a).size` as the argument.
-/
@[simp] theorem foldr_push' (f : α → β → β) (init : β) (xs : Array α) (a : α) {start}
    (h : start = xs.size + 1) : (xs.push a).foldr f init start = xs.foldr f (f a init) :=
  foldrM_push' _ _ _ _ h

@[simp] theorem foldl_push_eq_append {as : Array α} {bs : Array β} {f : α → β} (w : stop = as.size) :
    as.foldl (fun acc a => acc.push (f a)) bs 0 stop = bs ++ as.map f := by
  subst w
  rcases as with ⟨as⟩
  rcases bs with ⟨bs⟩
  simp only [List.foldl_toArray']
  induction as generalizing bs <;> simp [*]

@[simp] theorem foldl_cons_eq_append {as : Array α} {bs : List β} {f : α → β} (w : stop = as.size) :
    as.foldl (fun acc a => (f a) :: acc) bs 0 stop = (as.map f).reverse.toList ++ bs := by
  subst w
  rcases as with ⟨as⟩
  simp

@[simp] theorem foldr_cons_eq_append {as : Array α} {bs : List β} {f : α → β} (w : start = as.size) :
    as.foldr (fun a acc => (f a) :: acc) bs start 0 = (as.map f).toList ++ bs := by
  subst w
  rcases as with ⟨as⟩
  simp

/-- Variant of `foldr_cons_eq_append` specialized to `f = id`. -/
@[simp] theorem foldr_cons_eq_append' {as : Array α} {bs : List α} (w : start = as.size) :
    as.foldr List.cons bs start 0 = as.toList ++ bs := by
  subst w
  rcases as with ⟨as⟩
  simp

@[simp] theorem foldr_append_eq_append (xs : Array α) (f : α → Array β) (ys : Array β) :
    xs.foldr (f · ++ ·) ys = (xs.map f).flatten ++ ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  induction xs <;> simp_all [Function.comp_def, flatten_toArray]

@[simp] theorem foldl_append_eq_append (xs : Array α) (f : α → Array β) (ys : Array β) :
    xs.foldl (· ++ f ·) ys = ys ++ (xs.map f).flatten := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  induction xs generalizing ys <;> simp_all [Function.comp_def, flatten_toArray]

@[simp] theorem foldr_flip_append_eq_append (xs : Array α) (f : α → Array β) (ys : Array β) :
    xs.foldr (fun x acc => acc ++ f x) ys = ys ++ (xs.map f).reverse.flatten := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  induction xs generalizing ys <;> simp_all [Function.comp_def, flatten_toArray]

@[simp] theorem foldl_flip_append_eq_append (xs : Array α) (f : α → Array β) (ys : Array β) :
    xs.foldl (fun acc y => f y ++ acc) ys = (xs.map f).reverse.flatten ++ ys:= by
  rcases xs with ⟨l⟩
  rcases ys with ⟨l'⟩
  induction l generalizing l' <;> simp_all [Function.comp_def, flatten_toArray]

theorem foldl_map' (f : β₁ → β₂) (g : α → β₂ → α) (xs : Array β₁) (init : α) (w : stop = xs.size) :
    (xs.map f).foldl g init 0 stop = xs.foldl (fun x y => g x (f y)) init := by
  subst w
  cases xs; simp [List.foldl_map]

theorem foldr_map' (f : α₁ → α₂) (g : α₂ → β → β) (xs : Array α₁) (init : β) (w : start = xs.size) :
    (xs.map f).foldr g init start 0 = xs.foldr (fun x y => g (f x) y) init := by
  subst w
  cases xs; simp [List.foldr_map]

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (xs : Array β₁) (init : α) :
    (xs.map f).foldl g init = xs.foldl (fun x y => g x (f y)) init := by
  cases xs; simp [List.foldl_map]

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (xs : Array α₁) (init : β) :
    (xs.map f).foldr g init = xs.foldr (fun x y => g (f x) y) init := by
  cases xs; simp [List.foldr_map]

theorem foldl_filterMap' (f : α → Option β) (g : γ → β → γ) (xs : Array α) (init : γ)
    (w : stop = (xs.filterMap f).size) :
    (xs.filterMap f).foldl g init 0 stop = xs.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  subst w
  cases xs
  simp [List.foldl_filterMap]
  rfl

theorem foldr_filterMap' (f : α → Option β) (g : β → γ → γ) (xs : Array α) (init : γ)
    (w : start = (xs.filterMap f).size) :
    (xs.filterMap f).foldr g init start 0 = xs.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  subst w
  cases xs
  simp [List.foldr_filterMap]
  rfl

theorem foldl_filterMap (f : α → Option β) (g : γ → β → γ) (xs : Array α) (init : γ) :
    (xs.filterMap f).foldl g init = xs.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  simp [foldl_filterMap']

theorem foldr_filterMap (f : α → Option β) (g : β → γ → γ) (xs : Array α) (init : γ) :
    (xs.filterMap f).foldr g init = xs.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  simp [foldr_filterMap']

theorem foldl_map_hom' (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (xs : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) (w : stop = xs.size) :
    (xs.map g).foldl f' (g a) 0 stop = g (xs.foldl f a) := by
  subst w
  cases xs
  simp
  rw [List.foldl_map_hom _ _ _ _ _ h]

theorem foldr_map_hom' (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (xs : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) (w : start = xs.size) :
    (xs.map g).foldr f' (g a) start 0 = g (xs.foldr f a) := by
  subst w
  cases xs
  simp
  rw [List.foldr_map_hom _ _ _ _ _ h]

theorem foldl_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (xs : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (xs.map g).foldl f' (g a) = g (xs.foldl f a) := by
  cases xs
  simp
  rw [List.foldl_map_hom _ _ _ _ _ h]

theorem foldr_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (xs : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (xs.map g).foldr f' (g a) = g (xs.foldr f a) := by
  cases xs
  simp
  rw [List.foldr_map_hom _ _ _ _ _ h]

/-- Variant of `foldrM_append` with a side condition for the `start` argument. -/
@[simp] theorem foldrM_append' [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (xs ys : Array α)
    (w : start = xs.size + ys.size) :
    (xs ++ ys).foldrM f b start 0 = ys.foldrM f b >>= xs.foldrM f := by
  subst w
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (xs ys : Array α) :
    (xs ++ ys).foldrM f b = ys.foldrM f b >>= xs.foldrM f := by
  simp

@[simp] theorem foldl_append' {β : Type _} (f : β → α → β) (b) (xs ys : Array α)
    (w : stop = xs.size + ys.size) :
    (xs ++ ys).foldl f b 0 stop = ys.foldl f (xs.foldl f b) := by
  subst w
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

@[simp] theorem foldr_append' (f : α → β → β) (b) (xs ys : Array α)
    (w : start = xs.size + ys.size) :
    (xs ++ ys).foldr f b start 0 = xs.foldr f (ys.foldr f b) := by
  subst w
  simp [foldr_eq_foldrM]

theorem foldl_append {β : Type _} (f : β → α → β) (b) (xs ys : Array α) :
    (xs ++ ys).foldl f b = ys.foldl f (xs.foldl f b) := by
  simp [foldl_eq_foldlM]

theorem foldr_append (f : α → β → β) (b) (xs ys : Array α) :
    (xs ++ ys).foldr f b = xs.foldr f (ys.foldr f b) := by
  simp [foldr_eq_foldrM]

@[simp] theorem foldl_flatten' (f : β → α → β) (b : β) (xss : Array (Array α))
    (w : stop = xss.flatten.size) :
    (flatten xss).foldl f b 0 stop = xss.foldl (fun b xs => xs.foldl f b) b := by
  subst w
  cases xss using array₂_induction
  simp [List.foldl_flatten, List.foldl_map]

@[simp] theorem foldr_flatten' (f : α → β → β) (b : β) (xss : Array (Array α))
    (w : start = xss.flatten.size) :
    (flatten xss).foldr f b start 0 = xss.foldr (fun xs b => xs.foldr f b) b := by
  subst w
  cases xss using array₂_induction
  simp [List.foldr_flatten, List.foldr_map]

theorem foldl_flatten (f : β → α → β) (b : β) (xss : Array (Array α)) :
    (flatten xss).foldl f b = xss.foldl (fun b xs => xs.foldl f b) b := by
  cases xss using array₂_induction
  simp [List.foldl_flatten, List.foldl_map]

theorem foldr_flatten (f : α → β → β) (b : β) (xss : Array (Array α)) :
    (flatten xss).foldr f b = xss.foldr (fun xs b => xs.foldr f b) b := by
  cases xss using array₂_induction
  simp [List.foldr_flatten, List.foldr_map]

/-- Variant of `foldl_reverse` with a side condition for the `stop` argument. -/
@[simp] theorem foldl_reverse' (xs : Array α) (f : β → α → β) (b) (w : stop = xs.size) :
    xs.reverse.foldl f b 0 stop = xs.foldr (fun x y => f y x) b := by
  simp [w, foldl_eq_foldlM, foldr_eq_foldrM]

/-- Variant of `foldr_reverse` with a side condition for the `start` argument. -/
@[simp] theorem foldr_reverse' (xs : Array α) (f : α → β → β) (b) (w : start = xs.size) :
    xs.reverse.foldr f b start 0 = xs.foldl (fun x y => f y x) b := by
  simp [w, foldl_eq_foldlM, foldr_eq_foldrM]

theorem foldl_reverse (xs : Array α) (f : β → α → β) (b) :
    xs.reverse.foldl f b = xs.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

theorem foldr_reverse (xs : Array α) (f : α → β → β) (b) :
    xs.reverse.foldr f b = xs.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

theorem foldl_eq_foldr_reverse (xs : Array α) (f : β → α → β) (b) :
    xs.foldl f b = xs.reverse.foldr (fun x y => f y x) b := by simp

theorem foldr_eq_foldl_reverse (xs : Array α) (f : α → β → β) (b) :
    xs.foldr f b = xs.reverse.foldl (fun x y => f y x) b := by simp

@[simp] theorem foldr_push_eq_append {as : Array α} {bs : Array β} {f : α → β} (w : start = as.size) :
    as.foldr (fun a xs => Array.push xs (f a)) bs start 0 = bs ++ (as.map f).reverse := by
  subst w
  rw [foldr_eq_foldl_reverse, foldl_push_eq_append rfl, map_reverse]

@[deprecated foldr_push_eq_append (since := "2025-02-09")] abbrev foldr_flip_push_eq_append := @foldr_push_eq_append

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {xs : Array α} {a₁ a₂} :
     xs.foldl op (op a₁ a₂) = op a₁ (xs.foldl op a₂) := by
  rcases xs with ⟨l⟩
  simp [List.foldl_assoc]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {xs : Array α} {a₁ a₂} :
    xs.foldr op (op a₁ a₂) = op (xs.foldr op a₁) a₂ := by
  rcases xs with ⟨l⟩
  simp [List.foldr_assoc]

theorem foldl_hom (f : α₁ → α₂) (g₁ : α₁ → β → α₁) (g₂ : α₂ → β → α₂) (xs : Array β) (init : α₁)
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : xs.foldl g₂ (f init) = f (xs.foldl g₁ init) := by
  cases xs
  simp
  rw [List.foldl_hom _ _ _ _ _ H]

theorem foldr_hom (f : β₁ → β₂) (g₁ : α → β₁ → β₁) (g₂ : α → β₂ → β₂) (xs : Array α) (init : β₁)
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : xs.foldr g₂ (f init) = f (xs.foldr g₁ init) := by
  cases xs
  simp
  rw [List.foldr_hom _ _ _ _ _ H]

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldl_rel {xs : Array α} {f g : β → α → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ xs → ∀ (c c' : β), r c c' → r (f c a) (g c' a)) :
    r (xs.foldl (fun acc a => f acc a) a) (xs.foldl (fun acc a => g acc a) b) := by
  rcases xs with ⟨xs⟩
  simpa using List.foldl_rel r h (by simpa using h')

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldr_rel {xs : Array α} {f g : α → β → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ xs → ∀ (c c' : β), r c c' → r (f a c) (g a c')) :
    r (xs.foldr (fun a acc => f a acc) a) (xs.foldr (fun a acc => g a acc) b) := by
  rcases xs with ⟨xs⟩
  simpa using List.foldr_rel r h (by simpa using h')

@[simp] theorem foldl_add_const (xs : Array α) (a b : Nat) :
    xs.foldl (fun x _ => x + a) b = b + a * xs.size := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem foldr_add_const (xs : Array α) (a b : Nat) :
    xs.foldr (fun _ x => x + a) b = b + a * xs.size := by
  rcases xs with ⟨xs⟩
  simp

/-! #### Further results about `back` and `back?` -/

@[simp] theorem back?_eq_none_iff {xs : Array α} : xs.back? = none ↔ xs = #[] := by
  simp only [back?_eq_getElem?, ← size_eq_zero_iff]
  simp only [_root_.getElem?_eq_none_iff]
  omega

theorem back?_eq_some_iff {xs : Array α} {a : α} :
    xs.back? = some a ↔ ∃ ys : Array α, xs = ys.push a := by
  rcases xs with ⟨xs⟩
  simp only [List.back?_toArray, List.getLast?_eq_some_iff, toArray_eq, push_toList]
  constructor
  · rintro ⟨ys, rfl⟩
    exact ⟨ys.toArray, by simp⟩
  · rintro ⟨ys, rfl⟩
    exact ⟨ys.toList, by simp⟩

@[simp] theorem back?_isSome : xs.back?.isSome ↔ xs ≠ #[] := by
  cases xs
  simp

theorem mem_of_back? {xs : Array α} {a : α} (h : xs.back? = some a) : a ∈ xs := by
  obtain ⟨ys, rfl⟩ := back?_eq_some_iff.1 h
  simp

@[simp] theorem back_append_of_size_pos {xs ys : Array α} {h₁} (h₂ : 0 < ys.size) :
    (xs ++ ys).back h₁ = ys.back h₂ := by
  rcases xs with ⟨l⟩
  rcases ys with ⟨l'⟩
  simp only [List.append_toArray, List.back_toArray]
  rw [List.getLast_append_of_ne_nil]

theorem back_append {xs : Array α} (h : 0 < (xs ++ ys).size) :
    (xs ++ ys).back h =
      if h' : ys.isEmpty then
        xs.back (by simp_all)
      else
        ys.back (by simp only [isEmpty_iff, eq_empty_iff_size_eq_zero] at h'; omega) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, List.back_toArray, List.getLast_append, List.isEmpty_iff,
    List.isEmpty_toArray]
  split
  · rw [dif_pos]
    simpa only [List.isEmpty_toArray]
  · rw [dif_neg]
    simpa only [List.isEmpty_toArray]

theorem back_append_right {xs ys : Array α} (h : 0 < ys.size) :
    (xs ++ ys).back (by simp; omega) = ys.back h := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, List.back_toArray]
  rw [List.getLast_append_right]

theorem back_append_left {xs ys : Array α} (w : 0 < (xs ++ ys).size) (h : ys.size = 0) :
    (xs ++ ys).back w = xs.back (by simp_all) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, List.back_toArray]
  rw [List.getLast_append_left]
  simpa using h

@[simp] theorem back?_append {xs ys : Array α} : (xs ++ ys).back? = ys.back?.or xs.back? := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [List.append_toArray, List.back?_toArray]
  rw [List.getLast?_append]

theorem back_filter_of_pos {p : α → Bool} {xs : Array α} (w : 0 < xs.size) (h : p (back xs w) = true) :
    (filter p xs).back (by simpa using ⟨_, by simp, h⟩) = xs.back w := by
  rcases xs with ⟨xs⟩
  simp only [List.back_toArray] at h
  simp only [List.size_toArray, List.filter_toArray', List.back_toArray]
  rw [List.getLast_filter_of_pos _ h]

theorem back_filterMap_of_eq_some {f : α → Option β} {xs : Array α} {w : 0 < xs.size} {b : β} (h : f (xs.back w) = some b) :
    (filterMap f xs).back (by simpa using ⟨_, by simp, b, h⟩) = some b := by
  rcases xs with ⟨xs⟩
  simp only [List.back_toArray] at h
  simp only [List.size_toArray, List.filterMap_toArray', List.back_toArray]
  rw [List.getLast_filterMap_of_eq_some h]

theorem back?_flatMap {xs : Array α} {f : α → Array β} :
    (xs.flatMap f).back? = xs.reverse.findSome? fun a => (f a).back? := by
  rcases xs with ⟨xs⟩
  simp [List.getLast?_flatMap]

theorem back?_flatten {xss : Array (Array α)} :
    (flatten xss).back? = xss.reverse.findSome? fun xs => xs.back? := by
  simp [← flatMap_id, back?_flatMap]

theorem back?_mkArray (a : α) (n : Nat) :
    (mkArray n a).back? = if n = 0 then none else some a := by
  rw [mkArray_eq_toArray_replicate]
  simp only [List.back?_toArray, List.getLast?_replicate]

@[simp] theorem back_mkArray (w : 0 < n) : (mkArray n a).back (by simpa using w) = a := by
  simp [back_eq_getElem]

/-! ## Additional operations -/

/-! ### leftpad -/

-- We unfold `leftpad` and `rightpad` for verification purposes.
attribute [simp] leftpad rightpad

theorem size_leftpad (n : Nat) (a : α) (xs : Array α) :
    (leftpad n a xs).size = max n xs.size := by simp; omega

theorem size_rightpad (n : Nat) (a : α) (xs : Array α) :
    (rightpad n a xs).size = max n xs.size := by simp; omega

/-! Content below this point has not yet been aligned with `List`. -/

/-! ### sum -/

theorem sum_eq_sum_toList [Add α] [Zero α] (as : Array α) : as.toList.sum = as.sum := by
  cases as
  simp [Array.sum, List.sum]

@[deprecated size_toArray (since := "2024-12-11")]
theorem size_mk (as : List α) : (Array.mk as).size = as.length := by simp [size]

/-- A more efficient version of `arr.toList.reverse`. -/
@[inline] def toListRev (xs : Array α) : List α := xs.foldl (fun l t => t :: l) []

@[simp] theorem toListRev_eq (xs : Array α) : xs.toListRev = xs.toList.reverse := by
  rw [toListRev, ← foldl_toList, ← List.foldr_reverse, List.foldr_cons_nil]

@[simp] theorem appendList_nil (xs : Array α) : xs ++ ([] : List α) = xs := Array.ext' (by simp)

@[simp] theorem appendList_cons (xs : Array α) (a : α) (l : List α) :
    xs ++ (a :: l) = xs.push a ++ l := Array.ext' (by simp)

theorem foldl_toList_eq_flatMap (l : List α) (acc : Array β)
    (F : Array β → α → Array β) (G : α → List β)
    (H : ∀ acc a, (F acc a).toList = acc.toList ++ G a) :
    (l.foldl F acc).toList = acc.toList ++ l.flatMap G := by
  induction l generalizing acc <;> simp [*, List.flatMap]

theorem foldl_toList_eq_map (l : List α) (acc : Array β) (G : α → β) :
    (l.foldl (fun acc a => acc.push (G a)) acc).toList = acc.toList ++ l.map G := by
  induction l generalizing acc <;> simp [*]

/-! # uset -/

attribute [simp] uset

theorem size_uset (xs : Array α) (v i h) : (uset xs i v h).size = xs.size := by simp

/-! # get -/

@[deprecated getElem?_eq_getElem (since := "2024-12-11")]
theorem getElem?_lt
    (xs : Array α) {i : Nat} (h : i < xs.size) : xs[i]? = some xs[i] := dif_pos h

@[deprecated getElem?_eq_none (since := "2024-12-11")]
theorem getElem?_ge
    (xs : Array α) {i : Nat} (h : i ≥ xs.size) : xs[i]? = none := dif_neg (Nat.not_lt_of_le h)

set_option linter.deprecated false in
@[deprecated "`get?` is deprecated" (since := "2025-02-12"), simp]
theorem get?_eq_getElem? (xs : Array α) (i : Nat) : xs.get? i = xs[i]? := rfl

@[deprecated getElem?_eq_none (since := "2024-12-11")]
theorem getElem?_len_le (xs : Array α) {i : Nat} (h : xs.size ≤ i) : xs[i]? = none := by
  simp [getElem?_eq_none, h]

@[deprecated getD_getElem? (since := "2024-12-11")] abbrev getD_get? := @getD_getElem?

@[simp] theorem getD_eq_getD_getElem? (xs : Array α) (i d) : xs.getD i d = xs[i]?.getD d := by
  simp only [getD]; split <;> simp [getD_getElem?, *]

@[deprecated getD_eq_getD_getElem? (since := "2025-02-12")] abbrev getD_eq_get? := @getD_eq_getD_getElem?

theorem getElem!_eq_getD [Inhabited α] (xs : Array α) : xs[i]! = xs.getD i default := by
  rfl

set_option linter.deprecated false in
@[deprecated getElem!_eq_getD (since := "2025-02-12")]
theorem get!_eq_getD [Inhabited α] (xs : Array α) : xs.get! n = xs.getD n default := rfl

set_option linter.deprecated false in
@[deprecated "Use `a[i]!` instead of `a.get! i`." (since := "2025-02-12")]
theorem get!_eq_getD_getElem? [Inhabited α] (xs : Array α) (i : Nat) :
    xs.get! i = xs[i]?.getD default := by
  by_cases p : i < xs.size <;>
  simp [get!, getElem!_eq_getD, getD_eq_getD_getElem?, getD_getElem?, p]

set_option linter.deprecated false in
@[deprecated get!_eq_getD_getElem? (since := "2025-02-12")] abbrev get!_eq_getElem? := @get!_eq_getD_getElem?

/-! # ofFn -/

@[simp] theorem size_ofFn_go {n} (f : Fin n → α) (i acc) :
    (ofFn.go f i acc).size = acc.size + (n - i) := by
  if hin : i < n then
    unfold ofFn.go
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    rw [dif_pos hin, size_ofFn_go f (i+1), size_push, Nat.add_assoc, this]
  else
    have : n - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hin)
    unfold ofFn.go
    simp [hin, this]
termination_by n - i

@[simp] theorem size_ofFn (f : Fin n → α) : (ofFn f).size = n := by simp [ofFn]

theorem getElem_ofFn_go (f : Fin n → α) (i) {acc k}
    (hki : k < n) (hin : i ≤ n) (hi : i = acc.size)
    (hacc : ∀ j, ∀ hj : j < acc.size, acc[j] = f ⟨j, Nat.lt_of_lt_of_le hj (hi ▸ hin)⟩) :
    haveI : acc.size + (n - acc.size) = n := Nat.add_sub_cancel' (hi ▸ hin)
    (ofFn.go f i acc)[k]'(by simp [*]) = f ⟨k, hki⟩ := by
  unfold ofFn.go
  if hin : i < n then
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    simp only [dif_pos hin]
    rw [getElem_ofFn_go f (i+1) _ hin (by simp [*]) (fun j hj => ?hacc)]
    cases (Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ (by simpa using hj)) with
    | inl hj => simp [getElem_push, hj, hacc j hj]
    | inr hj => simp [getElem_push, *]
  else
    simp [hin, hacc k (Nat.lt_of_lt_of_le hki (Nat.le_of_not_lt (hi ▸ hin)))]
termination_by n - i

@[simp] theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h) :
    (ofFn f)[i] = f ⟨i, size_ofFn f ▸ h⟩ :=
  getElem_ofFn_go _ _ _ (by simp) (by simp) nofun

theorem getElem?_ofFn (f : Fin n → α) (i : Nat) :
    (ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none := by
  simp [getElem?_def]

@[simp] theorem ofFn_zero (f : Fin 0 → α) : ofFn f = #[] := rfl

theorem ofFn_succ (f : Fin (n+1) → α) :
    ofFn f = (ofFn (fun (i : Fin n) => f i.castSucc)).push (f ⟨n, by omega⟩) := by
  ext i h₁ h₂
  · simp
  · simp [getElem_push]
    split <;> rename_i h₃
    · rfl
    · congr
      simp at h₁ h₂
      omega

/-! # mem -/

@[simp] theorem mem_toList {a : α} {xs : Array α} : a ∈ xs.toList ↔ a ∈ xs := mem_def.symm

theorem not_mem_nil (a : α) : ¬ a ∈ #[] := nofun

/-! # get lemmas -/

theorem lt_of_getElem {x : α} {xs : Array α} {i : Nat} {hidx : i < xs.size} (_ : xs[i] = x) :
    i < xs.size :=
  hidx

theorem getElem_fin_eq_getElem_toList (xs : Array α) (i : Fin xs.size) : xs[i] = xs.toList[i] := rfl

@[simp] theorem ugetElem_eq_getElem (xs : Array α) {i : USize} (h : i.toNat < xs.size) :
  xs[i] = xs[i.toNat] := rfl

theorem getElem?_size_le (xs : Array α) (i : Nat) (h : xs.size ≤ i) : xs[i]? = none := by
  simp [getElem?_neg, h]

@[deprecated getElem?_size_le (since := "2024-10-21")] abbrev get?_len_le := @getElem?_size_le

theorem getElem_mem_toList (xs : Array α) (i : Nat) (h : i < xs.size) : xs[i] ∈ xs.toList := by
  simp only [← getElem_toList, List.getElem_mem]

set_option linter.deprecated false in
@[deprecated "`Array.get?` is deprecated, use `a[i]?` instead." (since := "2025-02-12")]
theorem get?_eq_get?_toList (xs : Array α) (i : Nat) : xs.get? i = xs.toList.get? i := by
  simp [← getElem?_toList]

set_option linter.deprecated false in
@[deprecated get!_eq_getD_getElem? (since := "2025-02-12")] abbrev get!_eq_get? := @get!_eq_getD_getElem?

theorem back!_eq_back? [Inhabited α] (xs : Array α) : xs.back! = xs.back?.getD default := by
  simp [back!, back?, getElem!_def, Option.getD]; rfl

@[simp] theorem back?_push (xs : Array α) : (xs.push x).back? = some x := by
  simp [back?, ← getElem?_toList]

@[simp] theorem back!_push [Inhabited α] (xs : Array α) : (xs.push x).back! = x := by
  simp [back!_eq_back?]

@[deprecated mem_of_back? (since := "2024-10-21")] abbrev mem_of_back?_eq_some := @mem_of_back?

theorem getElem?_push_lt (xs : Array α) (x : α) (i : Nat) (h : i < xs.size) :
    (xs.push x)[i]? = some xs[i] := by
  rw [getElem?_pos, getElem_push_lt]

@[deprecated getElem?_push_lt (since := "2024-10-21")] abbrev get?_push_lt := @getElem?_push_lt

theorem getElem?_push_eq (xs : Array α) (x : α) : (xs.push x)[xs.size]? = some x := by
  rw [getElem?_pos, getElem_push_eq]

@[deprecated getElem?_push_eq (since := "2024-10-21")] abbrev get?_push_eq := @getElem?_push_eq

@[deprecated getElem?_push (since := "2024-10-21")] abbrev get?_push := @getElem?_push

@[simp] theorem getElem?_size {xs : Array α} : xs[xs.size]? = none := by
  simp only [getElem?_def, Nat.lt_irrefl, dite_false]

@[deprecated getElem?_size (since := "2024-10-21")] abbrev get?_size := @getElem?_size

@[deprecated getElem_set_self (since := "2025-01-17")]
theorem get_set_eq (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set i v h)[i]'(by simp [h]) = v := by
  simp only [set, ← getElem_toList, List.getElem_set_self]

theorem get?_set_eq (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set i v)[i]? = v := by simp [getElem?_pos, h]

@[simp] theorem get?_set_ne (xs : Array α) (i : Nat) (h' : i < xs.size) {j : Nat} (v : α)
    (h : i ≠ j) : (xs.set i v)[j]? = xs[j]? := by
  by_cases j < xs.size <;> simp [getElem?_pos, getElem?_neg, *]

theorem get?_set (xs : Array α) (i : Nat) (h : i < xs.size) (j : Nat) (v : α) :
    (xs.set i v)[j]? = if i = j then some v else xs[j]? := by
  if h : i = j then subst j; simp [*] else simp [*]

theorem get_set (xs : Array α) (i : Nat) (hi : i < xs.size) (j : Nat) (hj : j < xs.size) (v : α) :
    (xs.set i v)[j]'(by simp [*]) = if i = j then v else xs[j] := by
  if h : i = j then subst j; simp [*] else simp [*]

@[simp] theorem get_set_ne (xs : Array α) (i : Nat) (hi : i < xs.size) {j : Nat} (v : α) (hj : j < xs.size)
    (h : i ≠ j) : (xs.set i v)[j]'(by simp [*]) = xs[j] := by
  simp only [set, ← getElem_toList, List.getElem_set_ne h]

@[simp] theorem swapAt_def (xs : Array α) (i : Nat) (v : α) (hi) :
    xs.swapAt i v hi = (xs[i], xs.set i v) := rfl

theorem size_swapAt (xs : Array α) (i : Nat) (v : α) (hi) :
    (xs.swapAt i v hi).2.size = xs.size := by simp

@[simp]
theorem swapAt!_def (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) :
    xs.swapAt! i v = (xs[i], xs.set i v) := by simp [swapAt!, h]

@[simp] theorem size_swapAt! (xs : Array α) (i : Nat) (v : α) :
    (xs.swapAt! i v).2.size = xs.size := by
  simp only [swapAt!]
  split
  · simp
  · rfl

@[simp] theorem pop_empty : (#[] : Array α).pop = #[] := rfl

@[simp] theorem pop_push (xs : Array α) : (xs.push x).pop = xs := by simp [pop]

@[simp] theorem getElem_pop (xs : Array α) (i : Nat) (hi : i < xs.pop.size) :
    xs.pop[i] = xs[i]'(Nat.lt_of_lt_of_le (xs.size_pop ▸ hi) (Nat.sub_le _ _)) :=
  List.getElem_dropLast ..

theorem eq_push_pop_back!_of_size_ne_zero [Inhabited α] {xs : Array α} (h : xs.size ≠ 0) :
    xs = xs.pop.push xs.back! := by
  apply ext
  · simp [Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero h)]
  · intros i h h'
    if hlt : i < xs.pop.size then
      rw [getElem_push_lt (h:=hlt), getElem_pop]
    else
      have heq : i = xs.pop.size :=
        Nat.le_antisymm (size_pop .. ▸ Nat.le_pred_of_lt h) (Nat.le_of_not_gt hlt)
      cases heq
      rw [getElem_push_eq, back!]
      simp [← getElem!_pos]

theorem eq_push_of_size_ne_zero {xs : Array α} (h : xs.size ≠ 0) :
    ∃ (bs : Array α) (c : α), xs = bs.push c :=
  let _ : Inhabited α := ⟨xs[0]⟩
  ⟨xs.pop, xs.back!, eq_push_pop_back!_of_size_ne_zero h⟩

theorem size_eq_length_toList (xs : Array α) : xs.size = xs.toList.length := rfl

@[simp] theorem size_swapIfInBounds (xs : Array α) (i j) :
    (xs.swapIfInBounds i j).size = xs.size := by unfold swapIfInBounds; split <;> (try split) <;> simp [size_swap]

@[deprecated size_swapIfInBounds (since := "2024-11-24")] abbrev size_swap! := @size_swapIfInBounds

@[simp] theorem size_range {n : Nat} : (range n).size = n := by
  simp [range]

@[simp] theorem toList_range (n : Nat) : (range n).toList = List.range n := by
  apply List.ext_getElem <;> simp [range]

@[simp]
theorem getElem_range {n : Nat} {i : Nat} (h : i < (Array.range n).size) : (Array.range n)[i] = i := by
  simp [← getElem_toList]

theorem getElem?_range {n : Nat} {i : Nat} : (Array.range n)[i]? = if i < n then some i else none := by
  simp [getElem?_def, getElem_range]

@[simp] theorem size_range' {start size step} : (range' start size step).size = size := by
  simp [range']

@[simp] theorem toList_range' {start size step} :
     (range' start size step).toList = List.range' start size step := by
  apply List.ext_getElem <;> simp [range']

@[simp]
theorem getElem_range' {start size step : Nat} {i : Nat}
    (h : i < (Array.range' start size step).size) :
    (Array.range' start size step)[i] = start + step * i := by
  simp [← getElem_toList]

theorem getElem?_range' {start size step : Nat} {i : Nat} :
    (Array.range' start size step)[i]? = if i < size then some (start + step * i) else none := by
  simp [getElem?_def, getElem_range']

/-! ### shrink -/

@[simp] theorem size_shrink_loop (xs : Array α) (n : Nat) : (shrink.loop n xs).size = xs.size - n := by
  induction n generalizing xs with
  | zero => simp [shrink.loop]
  | succ n ih =>
    simp [shrink.loop, ih]
    omega

@[simp] theorem getElem_shrink_loop (xs : Array α) (n : Nat) (i : Nat) (h : i < (shrink.loop n xs).size) :
    (shrink.loop n xs)[i] = xs[i]'(by simp at h; omega) := by
  induction n generalizing xs i with
  | zero => simp [shrink.loop]
  | succ n ih =>
    simp [shrink.loop, ih]

@[simp] theorem size_shrink (xs : Array α) (i : Nat) : (xs.shrink i).size = min i xs.size := by
  simp [shrink]
  omega

@[simp] theorem getElem_shrink (xs : Array α) (i : Nat) (j : Nat) (h : j < (xs.shrink i).size) :
    (xs.shrink i)[j] = xs[j]'(by simp at h; omega) := by
  simp [shrink]

@[simp] theorem toList_shrink (xs : Array α) (i : Nat) : (xs.shrink i).toList = xs.toList.take i := by
  apply List.ext_getElem <;> simp

@[simp] theorem shrink_eq_take (xs : Array α) (i : Nat) : xs.shrink i = xs.take i := by
  ext <;> simp

/-! ### forIn -/

@[simp] theorem forIn_toList [Monad m] (xs : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn xs.toList b f = forIn xs b f := by
  cases xs
  simp

@[simp] theorem forIn'_toList [Monad m] (xs : Array α) (b : β) (f : (a : α) → a ∈ xs.toList → β → m (ForInStep β)) :
    forIn' xs.toList b f = forIn' xs b (fun a m b => f a (mem_toList.mpr m) b) := by
  cases xs
  simp

/-! ### map -/

@[deprecated "Use `toList_map` or `List.map_toArray` to characterize `Array.map`." (since := "2025-01-06")]
theorem map_induction (xs : Array α) (f : α → β) (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin xs.size → β → Prop) (hs : ∀ i, motive i.1 → p i (f xs[i]) ∧ motive (i+1)) :
    motive xs.size ∧
      ∃ eq : (xs.map f).size = xs.size, ∀ i h, p ⟨i, h⟩ ((xs.map f)[i]) := by
  have t := foldl_induction (as := xs) (β := Array β)
    (motive := fun i xs => motive i ∧ xs.size = i ∧ ∀ i h2, p i xs[i.1])
    (init := #[]) (f := fun acc a => acc.push (f a)) ?_ ?_
  obtain ⟨m, eq, w⟩ := t
  · refine ⟨m, by simp, ?_⟩
    intro i h
    simp only [eq] at w
    specialize w ⟨i, h⟩ h
    simpa using w
  · exact ⟨h0, rfl, nofun⟩
  · intro i bs ⟨m, ⟨eq, w⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (hs _ m).2
    · simp_all
    · intro j h
      simp at h ⊢
      by_cases h' : j < size bs
      · rw [getElem_push]
        simp_all
      · rw [getElem_push, dif_neg h']
        simp only [show j = i by omega]
        exact (hs _ m).1

set_option linter.deprecated false in
@[deprecated "Use `toList_map` or `List.map_toArray` to characterize `Array.map`." (since := "2025-01-06")]
theorem map_spec (xs : Array α) (f : α → β) (p : Fin xs.size → β → Prop)
    (hs : ∀ i, p i (f xs[i])) :
    ∃ eq : (xs.map f).size = xs.size, ∀ i h, p ⟨i, h⟩ ((xs.map f)[i]) := by
  simpa using map_induction xs f (fun _ => True) trivial p (by simp_all)

/-! ### modify -/

@[simp] theorem size_modify (xs : Array α) (i : Nat) (f : α → α) : (xs.modify i f).size = xs.size := by
  unfold modify modifyM Id.run
  split <;> simp

theorem getElem_modify {xs : Array α} {j i} (h : i < (xs.modify j f).size) :
    (xs.modify j f)[i] = if j = i then f (xs[i]'(by simpa using h)) else xs[i]'(by simpa using h) := by
  simp only [modify, modifyM, Id.run, Id.pure_eq]
  split
  · simp only [Id.bind_eq, get_set _ _ _ _ (by simpa using h)]; split <;> simp [*]
  · rw [if_neg (mt (by rintro rfl; exact h) (by simp_all))]

@[simp] theorem toList_modify (xs : Array α) (f : α → α) :
    (xs.modify i f).toList = xs.toList.modify f i := by
  apply List.ext_getElem
  · simp
  · simp [getElem_modify, List.getElem_modify]

theorem getElem_modify_self {xs : Array α} {i : Nat} (f : α → α) (h : i < (xs.modify i f).size) :
    (xs.modify i f)[i] = f (xs[i]'(by simpa using h)) := by
  simp [getElem_modify h]

theorem getElem_modify_of_ne {xs : Array α} {i : Nat} (h : i ≠ j)
    (f : α → α) (hj : j < (xs.modify i f).size) :
    (xs.modify i f)[j] = xs[j]'(by simpa using hj) := by
  simp [getElem_modify hj, h]

theorem getElem?_modify {xs : Array α} {i : Nat} {f : α → α} {j : Nat} :
    (xs.modify i f)[j]? = if i = j then xs[j]?.map f else xs[j]? := by
  simp only [getElem?_def, size_modify, getElem_modify, Option.map_dif]
  split <;> split <;> rfl

/-! ### contains -/

theorem contains_def [DecidableEq α] {a : α} {xs : Array α} : xs.contains a ↔ a ∈ xs := by
  rw [mem_def, contains, ← any_toList, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (xs : Array α) : Decidable (a ∈ xs) :=
  decidable_of_iff _ contains_def

/-! ### swap -/

@[simp] theorem getElem_swap_right (xs : Array α) {i j : Nat} {hi hj} :
    (xs.swap i j hi hj)[j]'(by simpa using hj) = xs[i] := by
  simp [swap_def, getElem_set]

@[simp] theorem getElem_swap_left (xs : Array α) {i j : Nat} {hi hj} :
    (xs.swap i j hi hj)[i]'(by simpa using hi) = xs[j] := by
  simp +contextual [swap_def, getElem_set]

@[simp] theorem getElem_swap_of_ne (xs : Array α) {i j : Nat} {hi hj} (hp : k < xs.size)
    (hi' : k ≠ i) (hj' : k ≠ j) : (xs.swap i j hi hj)[k]'(xs.size_swap .. |>.symm ▸ hp) = xs[k] := by
  simp [swap_def, getElem_set, hi'.symm, hj'.symm]

theorem getElem_swap' (xs : Array α) (i j : Nat) {hi hj} (k : Nat) (hk : k < xs.size) :
    (xs.swap i j hi hj)[k]'(by simp_all) = if k = i then xs[j] else if k = j then xs[i] else xs[k] := by
  split
  · simp_all only [getElem_swap_left]
  · split <;> simp_all

theorem getElem_swap (xs : Array α) (i j : Nat) {hi hj} (k : Nat) (hk : k < (xs.swap i j hi hj).size) :
    (xs.swap i j hi hj)[k] = if k = i then xs[j] else if k = j then xs[i] else xs[k]'(by simp_all) := by
  apply getElem_swap'

@[simp] theorem swap_swap (xs : Array α) {i j : Nat} (hi hj) :
    (xs.swap i j hi hj).swap i j ((xs.size_swap ..).symm ▸ hi) ((xs.size_swap ..).symm ▸ hj) = xs := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [getElem_swap]
    split
    · simp_all
    · split <;> simp_all

theorem swap_comm (xs : Array α) {i j : Nat} {hi hj} : xs.swap i j hi hj = xs.swap j i hj hi := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [getElem_swap]
    split
    · split <;> simp_all
    · split <;> simp_all

/-! ### eraseIdx -/

theorem eraseIdx_eq_eraseIdxIfInBounds {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs.eraseIdx i h = xs.eraseIdxIfInBounds i := by
  simp [eraseIdxIfInBounds, h]

/-! ### isPrefixOf -/

@[simp] theorem isPrefixOf_toList [BEq α] {xs ys : Array α} :
    xs.toList.isPrefixOf ys.toList = xs.isPrefixOf ys := by
  cases xs
  cases ys
  simp

/-! ### zipWith -/

@[simp] theorem toList_zipWith (f : α → β → γ) (xs : Array α) (ys : Array β) :
    (zipWith f xs ys).toList = List.zipWith f xs.toList ys.toList := by
  cases xs
  cases ys
  simp

@[simp] theorem toList_zip (xs : Array α) (ys : Array β) :
    (zip xs ys).toList = List.zip xs.toList ys.toList := by
  simp [zip, toList_zipWith, List.zip]

@[simp] theorem toList_zipWithAll (f : Option α → Option β → γ) (xs : Array α) (ys : Array β) :
    (zipWithAll f xs ys).toList = List.zipWithAll f xs.toList ys.toList := by
  cases xs
  cases ys
  simp

@[simp] theorem size_zipWith (xs : Array α) (ys : Array β) (f : α → β → γ) :
    (zipWith f xs ys).size = min xs.size ys.size := by
  rw [size_eq_length_toList, toList_zipWith, List.length_zipWith]

@[simp] theorem size_zip (xs : Array α) (ys : Array β) :
    (zip xs ys).size = min xs.size ys.size :=
  xs.size_zipWith ys Prod.mk

@[simp] theorem getElem_zipWith (xs : Array α) (ys : Array β) (f : α → β → γ) (i : Nat)
    (hi : i < (zipWith f xs ys).size) :
    (zipWith f xs ys)[i] = f (xs[i]'(by simp at hi; omega)) (ys[i]'(by simp at hi; omega)) := by
  cases xs
  cases ys
  simp

/-! ### findSomeM?, findM?, findSome?, find? -/

@[simp] theorem findSomeM?_toList [Monad m] [LawfulMonad m] (p : α → m (Option β)) (xs : Array α) :
    xs.toList.findSomeM? p = xs.findSomeM? p := by
  cases xs
  simp

@[simp] theorem findM?_toList [Monad m] [LawfulMonad m] (p : α → m Bool) (xs : Array α) :
    xs.toList.findM? p = xs.findM? p := by
  cases xs
  simp

@[simp] theorem findSome?_toList (p : α → Option β) (xs : Array α) :
    xs.toList.findSome? p = xs.findSome? p := by
  cases xs
  simp

@[simp] theorem find?_toList (p : α → Bool) (xs : Array α) :
    xs.toList.find? p = xs.find? p := by
  cases xs
  simp

@[simp] theorem finIdxOf?_toList [BEq α] (a : α) (xs : Array α) :
    xs.toList.finIdxOf? a = (xs.finIdxOf? a).map (Fin.cast (by simp)) := by
  cases xs
  simp

@[simp] theorem findFinIdx?_toList (p : α → Bool) (xs : Array α) :
    xs.toList.findFinIdx? p = (xs.findFinIdx? p).map (Fin.cast (by simp)) := by
  cases xs
  simp

end Array

open Array

namespace List

/-!
### More theorems about `List.toArray`, followed by an `Array` operation.

Our goal is to have `simp` "pull `List.toArray` outwards" as much as possible.
-/

theorem toListRev_toArray (l : List α) : l.toArray.toListRev = l.reverse := by simp

@[simp] theorem take_toArray (l : List α) (i : Nat) : l.toArray.take i = (l.take i).toArray := by
  apply Array.ext <;> simp

@[simp] theorem mapM_toArray [Monad m] [LawfulMonad m] (f : α → m β) (l : List α) :
    l.toArray.mapM f = List.toArray <$> l.mapM f := by
  simp only [← mapM'_eq_mapM, mapM_eq_foldlM]
  suffices ∀ xs : Array β,
      Array.foldlM (fun acc a => acc.push <$> f a) xs l.toArray = (xs ++ toArray ·) <$> mapM' f l by
    simpa using this #[]
  intro xs
  induction l generalizing xs with
  | nil => simp
  | cons a l ih =>
    simp only [foldlM_toArray] at ih
    rw [size_toArray, mapM'_cons, foldlM_toArray]
    simp [ih]

theorem uset_toArray (l : List α) (i : USize) (a : α) (h : i.toNat < l.toArray.size) :
    l.toArray.uset i a h = (l.set i.toNat a).toArray := by simp

@[simp] theorem modify_toArray (f : α → α) (l : List α) :
    l.toArray.modify i f = (l.modify f i).toArray := by
  apply ext'
  simp

@[simp] theorem flatten_toArray (L : List (List α)) :
    (L.toArray.map List.toArray).flatten = L.flatten.toArray := by
  apply ext'
  simp [Function.comp_def]

@[simp] theorem toArray_range (n : Nat) : (range n).toArray = Array.range n := by
  apply ext'
  simp

@[simp] theorem toArray_range' (start size step : Nat) :
    (range' start size step).toArray = Array.range' start size step := by
  apply ext'
  simp

@[simp] theorem toArray_ofFn (f : Fin n → α) : (ofFn f).toArray = Array.ofFn f := by
  ext <;> simp

end List

namespace Array

@[simp] theorem mapM_id {xs : Array α} {f : α → Id β} : xs.mapM f = xs.map f := by
  induction xs; simp_all

@[simp] theorem toList_ofFn (f : Fin n → α) : (Array.ofFn f).toList = List.ofFn f := by
  apply List.ext_getElem <;> simp

@[simp] theorem toList_takeWhile (p : α → Bool) (as : Array α) :
    (as.takeWhile p).toList = as.toList.takeWhile p := by
  induction as; simp

@[simp] theorem toList_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) :
    (xs.eraseIdx i h).toList = xs.toList.eraseIdx i := by
  induction xs
  simp

@[simp] theorem toList_eraseIdxIfInBounds (xs : Array α) (i : Nat) :
    (xs.eraseIdxIfInBounds i).toList = xs.toList.eraseIdx i := by
  induction xs
  simp

/-! ### flatten -/

@[simp] theorem flatten_toArray_map_toArray (xss : List (List α)) :
    (xss.map List.toArray).toArray.flatten = xss.flatten.toArray := by
  simp [flatten]
  suffices ∀ as, List.foldl (fun acc bs => acc ++ bs) as (List.map List.toArray xss) = as ++ xss.flatten.toArray by
    simpa using this #[]
  intro as
  induction xss generalizing as with
  | nil => simp
  | cons xs xss ih => simp [ih]

/-! ### findSomeRevM?, findRevM?, findSomeRev?, findRev? -/

@[simp] theorem findSomeRevM?_eq_findSomeM?_reverse
    [Monad m] [LawfulMonad m] (f : α → m (Option β)) (xs : Array α) :
    xs.findSomeRevM? f = xs.reverse.findSomeM? f := by
  cases xs
  rw [List.findSomeRevM?_toArray]
  simp

@[simp] theorem findRevM?_eq_findM?_reverse
    [Monad m] [LawfulMonad m] (f : α → m Bool) (xs : Array α) :
    xs.findRevM? f = xs.reverse.findM? f := by
  cases xs
  rw [List.findRevM?_toArray]
  simp

@[simp] theorem findSomeRev?_eq_findSome?_reverse (f : α → Option β) (xs : Array α) :
    xs.findSomeRev? f = xs.reverse.findSome? f := by
  cases xs
  simp [findSomeRev?, Id.run]

@[simp] theorem findRev?_eq_find?_reverse (f : α → Bool) (xs : Array α) :
    xs.findRev? f = xs.reverse.find? f := by
  cases xs
  simp [findRev?, Id.run]

/-! ### unzip -/

@[simp] theorem fst_unzip (xs : Array (α × β)) : (Array.unzip xs).fst = xs.map Prod.fst := by
  simp only [unzip]
  rcases xs with ⟨xs⟩
  simp only [List.foldl_toArray']
  rw [← List.foldl_hom (f := Prod.fst) (g₂ := fun bs x => bs.push x.1) (H := by simp), ← List.foldl_map]
  simp

@[simp] theorem snd_unzip (xs : Array (α × β)) : (Array.unzip xs).snd = xs.map Prod.snd := by
  simp only [unzip]
  rcases xs with ⟨xs⟩
  simp only [List.foldl_toArray']
  rw [← List.foldl_hom (f := Prod.snd) (g₂ := fun bs x => bs.push x.2) (H := by simp), ← List.foldl_map]
  simp

/-! ### take -/

@[simp] theorem take_size (xs : Array α) : xs.take xs.size = xs := by
  cases xs
  simp

/-! ### countP and count -/

@[simp] theorem _root_.List.countP_toArray (l : List α) : countP p l.toArray = l.countP p := by
  simp [countP]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, ih, List.countP_cons]
    split <;> simp_all

@[simp] theorem countP_toList (xs : Array α) : xs.toList.countP p = countP p xs := by
  cases xs
  simp

@[simp] theorem _root_.List.count_toArray [BEq α] (l : List α) (a : α) : count a l.toArray = l.count a := by
  simp [count, List.count_eq_countP]

@[simp] theorem count_toList [BEq α] (xs : Array α) (a : α) : xs.toList.count a = xs.count a := by
  cases xs
  simp

end Array

namespace List

@[simp] theorem unzip_toArray (as : List (α × β)) :
    as.toArray.unzip = Prod.map List.toArray List.toArray as.unzip := by
  ext1 <;> simp

@[simp] theorem firstM_toArray [Alternative m] (as : List α) (f : α → m β) :
    as.toArray.firstM f = as.firstM f := by
  unfold Array.firstM
  suffices ∀ i, i ≤ as.length → firstM.go f as.toArray (as.length - i) = firstM f (as.drop (as.length - i)) by
    specialize this as.length
    simpa
  intro i
  induction i with
  | zero => simp [firstM.go]
  | succ i ih =>
    unfold firstM.go
    split <;> rename_i h
    · rw [drop_eq_getElem_cons h]
      intro h'
      specialize ih (by omega)
      have : as.length - (i + 1) + 1 = as.length - i := by omega
      simp_all [ih]
    · simp only [size_toArray, Nat.not_lt] at h
      have : as.length = 0 := by omega
      simp_all

end List

namespace Array

theorem toList_fst_unzip (xs : Array (α × β)) :
    xs.unzip.1.toList = xs.toList.unzip.1 := by simp

theorem toList_snd_unzip (xs : Array (α × β)) :
    xs.unzip.2.toList = xs.toList.unzip.2 := by simp

@[simp] theorem flatMap_empty {β} (f : α → Array β) : (#[] : Array α).flatMap f = #[] := rfl

theorem flatMap_toArray_cons {β} (f : α → Array β) (a : α) (as : List α) :
    (a :: as).toArray.flatMap f = f a ++ as.toArray.flatMap f := by
  simp [flatMap]
  suffices ∀ cs, List.foldl (fun bs a => bs ++ f a) (f a ++ cs) as =
      f a ++ List.foldl (fun bs a => bs ++ f a) cs as by
    erw [empty_append] -- Why doesn't this work via `simp`?
    simpa using this #[]
  intro cs
  induction as generalizing cs <;> simp_all

@[simp] theorem flatMap_toArray {β} (f : α → Array β) (as : List α) :
    as.toArray.flatMap f = (as.flatMap (fun a => (f a).toList)).toArray := by
  induction as with
  | nil => simp
  | cons a as ih =>
    apply ext'
    simp [ih, flatMap_toArray_cons]

end Array

/-! ### Deprecations -/

namespace List

@[deprecated setIfInBounds_toArray (since := "2024-11-24")] abbrev setD_toArray := @setIfInBounds_toArray

end List

namespace Array

@[deprecated foldl_toList_eq_flatMap (since := "2024-10-16")]
abbrev foldl_toList_eq_bind := @foldl_toList_eq_flatMap

@[deprecated foldl_toList_eq_flatMap (since := "2024-10-16")]
abbrev foldl_data_eq_bind := @foldl_toList_eq_flatMap

@[deprecated getElem_mem (since := "2024-10-17")]
abbrev getElem?_mem := @getElem_mem

@[deprecated getElem_fin_eq_getElem_toList (since := "2024-10-17")]
abbrev getElem_fin_eq_toList_get := @getElem_fin_eq_getElem_toList

@[deprecated "Use reverse direction of `getElem?_toList`" (since := "2024-10-17")]
abbrev getElem?_eq_toList_getElem? := @getElem?_toList

@[deprecated getElem?_swap (since := "2024-10-17")] abbrev get?_swap := @getElem?_swap

@[deprecated getElem_push (since := "2024-10-21")] abbrev get_push := @getElem_push
@[deprecated getElem_push_lt (since := "2024-10-21")] abbrev get_push_lt := @getElem_push_lt
@[deprecated getElem_push_eq (since := "2024-10-21")] abbrev get_push_eq := @getElem_push_eq

@[deprecated back!_eq_back? (since := "2024-10-31")] abbrev back_eq_back? := @back!_eq_back?
@[deprecated back!_push (since := "2024-10-31")] abbrev back_push := @back!_push
@[deprecated eq_push_pop_back!_of_size_ne_zero (since := "2024-10-31")]
abbrev eq_push_pop_back_of_size_ne_zero := @eq_push_pop_back!_of_size_ne_zero

@[deprecated set!_is_setIfInBounds (since := "2024-11-24")] abbrev set_is_setIfInBounds := @set!_eq_setIfInBounds
@[deprecated size_setIfInBounds (since := "2024-11-24")] abbrev size_setD := @size_setIfInBounds
@[deprecated getElem_setIfInBounds_eq (since := "2024-11-24")] abbrev getElem_setD_eq := @getElem_setIfInBounds_self
@[deprecated getElem?_setIfInBounds_eq (since := "2024-11-24")] abbrev get?_setD_eq := @getElem?_setIfInBounds_self
@[deprecated getD_get?_setIfInBounds (since := "2024-11-24")] abbrev getD_setD := @getD_get?_setIfInBounds
@[deprecated getElem_setIfInBounds (since := "2024-11-24")] abbrev getElem_setD := @getElem_setIfInBounds

@[deprecated List.getElem_toArray (since := "2024-11-29")]
theorem getElem_mk {xs : List α} {i : Nat} (h : i < xs.length) : (Array.mk xs)[i] = xs[i] := rfl

@[deprecated Array.getElem_toList (since := "2024-12-08")]
theorem getElem_eq_getElem_toList {xs : Array α} (h : i < xs.size) : xs[i] = xs.toList[i] := rfl

@[deprecated Array.getElem?_toList (since := "2024-12-08")]
theorem getElem?_eq_getElem?_toList (xs : Array α) (i : Nat) : xs[i]? = xs.toList[i]? := by
  rw [getElem?_def]
  split <;> simp_all

@[deprecated LawfulGetElem.getElem?_def (since := "2024-12-08")]
theorem getElem?_eq {xs : Array α} {i : Nat} :
    xs[i]? = if h : i < xs.size then some xs[i] else none := by
  rw [getElem?_def]

end Array
