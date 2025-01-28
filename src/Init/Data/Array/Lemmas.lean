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

namespace Array

/-! ## Preliminaries -/

/-! ### toList -/

@[simp] theorem toList_inj {a b : Array α} : a.toList = b.toList ↔ a = b := by
  cases a; cases b; simp

@[simp] theorem toList_eq_nil_iff (l : Array α) : l.toList = [] ↔ l = #[] := by
  cases l <;> simp

@[simp] theorem mem_toList_iff (a : α) (l : Array α) : a ∈ l.toList ↔ a ∈ l := by
  cases l <;> simp

@[simp] theorem length_toList {l : Array α} : l.toList.length = l.size := rfl

theorem eq_toArray : v = List.toArray a ↔ v.toList = a := by
  cases v
  simp

theorem toArray_eq : List.toArray a = v ↔ a = v.toList := by
  cases v
  simp

/-! ### empty -/

@[simp] theorem empty_eq {xs : Array α} : #[] = xs ↔ xs = #[] := by
  cases xs <;> simp

theorem size_empty : (#[] : Array α).size = 0 := rfl

@[simp] theorem mkEmpty_eq (α n) : @mkEmpty α n = #[] := rfl

/-! ### size -/

theorem eq_empty_of_size_eq_zero (h : l.size = 0) : l = #[] := by
  cases l
  simp_all

theorem ne_empty_of_size_eq_add_one (h : l.size = n + 1) : l ≠ #[] := by
  cases l
  simpa using List.ne_nil_of_length_eq_add_one h

theorem ne_empty_of_size_pos (h : 0 < l.size) : l ≠ #[] := by
  cases l
  simpa using List.ne_nil_of_length_pos h

theorem size_eq_zero : l.size = 0 ↔ l = #[] :=
  ⟨eq_empty_of_size_eq_zero, fun h => h ▸ rfl⟩

theorem size_pos_of_mem {a : α} {l : Array α} (h : a ∈ l) : 0 < l.size := by
  cases l
  simp only [mem_toArray] at h
  simpa using List.length_pos_of_mem h

theorem exists_mem_of_size_pos {l : Array α} (h : 0 < l.size) : ∃ a, a ∈ l := by
  cases l
  simpa using List.exists_mem_of_length_pos h

theorem size_pos_iff_exists_mem {l : Array α} : 0 < l.size ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_size_pos, fun ⟨_, h⟩ => size_pos_of_mem h⟩

theorem exists_mem_of_size_eq_add_one {l : Array α} (h : l.size = n + 1) : ∃ a, a ∈ l := by
  cases l
  simpa using List.exists_mem_of_length_eq_add_one h

theorem size_pos {l : Array α} : 0 < l.size ↔ l ≠ #[] :=
  Nat.pos_iff_ne_zero.trans (not_congr size_eq_zero)

theorem size_eq_one {l : Array α} : l.size = 1 ↔ ∃ a, l = #[a] := by
  cases l
  simpa using List.length_eq_one

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
  replace h : xs ≠ #[] := size_pos.mp h
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

@[simp] theorem getElem?_eq_none_iff {a : Array α} : a[i]? = none ↔ a.size ≤ i := by
  by_cases h : i < a.size
  · simp [getElem?_pos, h]
  · rw [getElem?_neg a i h]
    simp_all

@[simp] theorem none_eq_getElem?_iff {a : Array α} {i : Nat} : none = a[i]? ↔ a.size ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none {a : Array α} (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_eq_none_iff, h]

@[simp] theorem getElem?_eq_getElem {a : Array α} {i : Nat} (h : i < a.size) : a[i]? = some a[i] :=
  getElem?_pos ..

theorem getElem?_eq_some_iff {a : Array α} : a[i]? = some b ↔ ∃ h : i < a.size, a[i] = b := by
  simp [getElem?_def]

theorem some_eq_getElem?_iff {a : Array α} : some b = a[i]? ↔ ∃ h : i < a.size, a[i] = b := by
  rw [eq_comm, getElem?_eq_some_iff]

@[simp] theorem some_getElem_eq_getElem?_iff (a : Array α) (i : Nat) (h : i < a.size) :
    (some a[i] = a[i]?) ↔ True := by
  simp [h]

@[simp] theorem getElem?_eq_some_getElem_iff (a : Array α) (i : Nat) (h : i < a.size) :
    (a[i]? = some a[i]) ↔ True := by
  simp [h]

theorem getElem_eq_iff {a : Array α} {i : Nat} {h : i < a.size} : a[i] = x ↔ a[i]? = some x := by
  simp only [getElem?_eq_some_iff]
  exact ⟨fun w => ⟨h, w⟩, fun h => h.2⟩

theorem getElem_eq_getElem?_get (a : Array α) (i : Nat) (h : i < a.size) :
    a[i] = a[i]?.get (by simp [getElem?_eq_getElem, h]) := by
  simp [getElem_eq_iff]

theorem getD_getElem? (a : Array α) (i : Nat) (d : α) :
    a[i]?.getD d = if p : i < a.size then a[i]'p else d := by
  if h : i < a.size then
    simp [h, getElem?_def]
  else
    have p : i ≥ a.size := Nat.le_of_not_gt h
    simp [getElem?_eq_none p, h]

@[simp] theorem getElem?_empty {i : Nat} : (#[] : Array α)[i]? = none := rfl

theorem getElem_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    have : i < (a.push x).size := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (a.push x)[i] = a[i] := by
  simp only [push, ← getElem_toList, List.concat_eq_append, List.getElem_append_left, h]

@[simp] theorem getElem_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, ← getElem_toList, List.concat_eq_append]
  rw [List.getElem_append_right] <;> simp [← getElem_toList, Nat.zero_lt_one]

theorem getElem_push (a : Array α) (x : α) (i : Nat) (h : i < (a.push x).size) :
    (a.push x)[i] = if h : i < a.size then a[i] else x := by
  by_cases h' : i < a.size
  · simp [getElem_push_lt, h']
  · simp at h
    simp [getElem_push_lt, Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h')]

theorem getElem?_push {a : Array α} {x} : (a.push x)[i]? = if i = a.size then some x else a[i]? := by
  simp [getElem?_def, getElem_push]
  (repeat' split) <;> first | rfl | omega

@[simp] theorem getElem?_push_size {a : Array α} {x} : (a.push x)[a.size]? = some x := by
  simp [getElem?_push]

@[simp] theorem getElem_singleton (a : α) (h : i < 1) : #[a][i] = a :=
  match i, h with
  | 0, _ => rfl

theorem getElem?_singleton (a : α) (i : Nat) : #[a][i]? = if i = 0 then some a else none := by
  simp [List.getElem?_singleton]

theorem ext_getElem? {l₁ l₂ : Array α} (h : ∀ i : Nat, l₁[i]? = l₂[i]?) : l₁ = l₂ := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simpa using List.ext_getElem? (by simpa using h)

/-! ### mem -/

theorem not_mem_empty (a : α) : ¬ a ∈ #[] := by simp

@[simp] theorem mem_push {a : Array α} {x y : α} : x ∈ a.push y ↔ x ∈ a ∨ x = y := by
  simp only [mem_def]
  simp

theorem mem_push_self {a : Array α} {x : α} : x ∈ a.push x :=
  mem_push.2 (Or.inr rfl)

theorem eq_push_append_of_mem {xs : Array α} {x : α} (h : x ∈ xs) :
    ∃ (as bs : Array α), xs = as.push x ++ bs ∧ x ∉ as:= by
  rcases xs with ⟨xs⟩
  obtain ⟨as, bs, h, w⟩ := List.eq_append_cons_of_mem (mem_def.1 h)
  simp only at h
  obtain rfl := h
  exact ⟨as.toArray, bs.toArray, by simp, by simpa using w⟩

theorem mem_push_of_mem {a : Array α} {x : α} (y : α) (h : x ∈ a) : x ∈ a.push y :=
  mem_push.2 (Or.inl h)

theorem exists_mem_of_ne_empty (l : Array α) (h : l ≠ #[]) : ∃ x, x ∈ l := by
  simpa using List.exists_mem_of_ne_nil l.toList (by simpa using h)

theorem eq_empty_iff_forall_not_mem {l : Array α} : l = #[] ↔ ∀ a, a ∉ l := by
  cases l
  simp [List.eq_nil_iff_forall_not_mem]

@[simp] theorem mem_dite_empty_left {x : α} [Decidable p] {l : ¬ p → Array α} :
    (x ∈ if h : p then #[] else l h) ↔ ∃ h : ¬ p, x ∈ l h := by
  split <;> simp_all

@[simp] theorem mem_dite_empty_right {x : α} [Decidable p] {l : p → Array α} :
    (x ∈ if h : p then l h else #[]) ↔ ∃ h : p, x ∈ l h := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_left {x : α} [Decidable p] {l : Array α} :
    (x ∈ if p then #[] else l) ↔ ¬ p ∧ x ∈ l := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_right {x : α} [Decidable p] {l : Array α} :
    (x ∈ if p then l else #[]) ↔ p ∧ x ∈ l := by
  split <;> simp_all

theorem eq_of_mem_singleton (h : a ∈ #[b]) : a = b := by
  simpa using h

@[simp] theorem mem_singleton {a b : α} : a ∈ #[b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem forall_mem_push {p : α → Prop} {xs : Array α} {a : α} :
    (∀ x, x ∈ xs.push a → p x) ↔ p a ∧ ∀ x, x ∈ xs → p x := by
  cases xs
  simp [or_comm, forall_eq_or_imp]

theorem forall_mem_ne {a : α} {l : Array α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem forall_mem_ne' {a : α} {l : Array α} : (∀ a' : α, a' ∈ l → ¬a' = a) ↔ a ∉ l :=
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

theorem mem_of_mem_push_of_mem {a b : α} {l : Array α} : a ∈ l.push b → b ∈ l → a ∈ l := by
  cases l
  simp only [List.push_toArray, mem_toArray, List.mem_append, List.mem_singleton]
  rintro (h | rfl)
  · intro _
    exact h
  · exact id

theorem eq_or_ne_mem_of_mem {a b : α} {l : Array α} (h' : a ∈ l.push b) :
    a = b ∨ (a ≠ b ∧ a ∈ l) := by
  if h : a = b then
    exact .inl h
  else
    simp only [mem_push, h, or_false] at h'
    exact .inr ⟨h, h'⟩

theorem ne_empty_of_mem {a : α} {l : Array α} (h : a ∈ l) : l ≠ #[] := by
  cases l
  simp [List.ne_nil_of_mem (by simpa using h)]

theorem mem_of_ne_of_mem {a y : α} {l : Array α} (h₁ : a ≠ y) (h₂ : a ∈ l.push y) : a ∈ l := by
  simpa [h₁] using h₂

theorem ne_of_not_mem_push {a b : α} {l : Array α} (h : a ∉ l.push b) : a ≠ b := by
  simp only [mem_push, not_or] at h
  exact h.2

theorem not_mem_of_not_mem_push {a b : α} {l : Array α} (h : a ∉ l.push b) : a ∉ l := by
  simp only [mem_push, not_or] at h
  exact h.1

theorem not_mem_push_of_ne_of_not_mem {a y : α} {l : Array α} : a ≠ y → a ∉ l → a ∉ l.push y :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_push {a y : α} {l : Array α} : a ∉ l.push y → a ≠ y ∧ a ∉ l := by
  simp +contextual

theorem getElem_of_mem {a} {l : Array α} (h : a ∈ l) : ∃ (i : Nat) (h : i < l.size), l[i]'h = a := by
  cases l
  simp [List.getElem_of_mem (by simpa using h)]

theorem getElem?_of_mem {a} {l : Array α} (h : a ∈ l) : ∃ i : Nat, l[i]? = some a :=
  let ⟨n, _, e⟩ := getElem_of_mem h; ⟨n, e ▸ getElem?_eq_getElem _⟩

theorem mem_of_getElem? {l : Array α} {i : Nat} {a : α} (e : l[i]? = some a) : a ∈ l :=
  let ⟨_, e⟩ := getElem?_eq_some_iff.1 e; e ▸ getElem_mem ..

theorem mem_iff_getElem {a} {l : Array α} : a ∈ l ↔ ∃ (i : Nat) (h : i < l.size), l[i]'h = a :=
  ⟨getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_getElem? {a} {l : Array α} : a ∈ l ↔ ∃ i : Nat, l[i]? = some a := by
  simp [getElem?_eq_some_iff, mem_iff_getElem]

theorem forall_getElem {l : Array α} {p : α → Prop} :
    (∀ (i : Nat) h, p (l[i]'h)) ↔ ∀ a, a ∈ l → p a := by
  cases l; simp [List.forall_getElem]

/-! ### isEmpty -/

@[simp] theorem isEmpty_toList {l : Array α} : l.toList.isEmpty = l.isEmpty := by
  rcases l with ⟨_ | _⟩ <;> simp

theorem isEmpty_iff {l : Array α} : l.isEmpty ↔ l = #[] := by
  cases l <;> simp

theorem isEmpty_eq_false_iff_exists_mem {xs : Array α} :
    xs.isEmpty = false ↔ ∃ x, x ∈ xs := by
  cases xs
  simpa using List.isEmpty_eq_false_iff_exists_mem

theorem isEmpty_iff_size_eq_zero {l : Array α} : l.isEmpty ↔ l.size = 0 := by
  rw [isEmpty_iff, size_eq_zero]

@[simp] theorem isEmpty_eq_true {l : Array α} : l.isEmpty ↔ l = #[] := by
  cases l <;> simp

@[simp] theorem isEmpty_eq_false {l : Array α} : l.isEmpty = false ↔ l ≠ #[] := by
  cases l <;> simp

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
    simp only [List.anyM, anyM, size_toArray, List.length_cons, Nat.le_refl, ↓reduceDIte]
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

theorem all_eq_true_iff_forall_mem {l : Array α} : l.all p ↔ ∀ x, x ∈ l → p x := by
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

@[simp] theorem elem_eq_contains [BEq α] {a : α} {l : Array α} :
    elem a l = l.contains a := by
  simp [elem]

theorem elem_iff [BEq α] [LawfulBEq α] {a : α} {as : Array α} :
    elem a as = true ↔ a ∈ as := ⟨mem_of_contains_eq_true, contains_eq_true_of_mem⟩

theorem contains_iff [BEq α] [LawfulBEq α] {a : α} {as : Array α} :
    as.contains a = true ↔ a ∈ as := ⟨mem_of_contains_eq_true, contains_eq_true_of_mem⟩

theorem elem_eq_mem [BEq α] [LawfulBEq α] (a : α) (as : Array α) :
    elem a as = decide (a ∈ as) := by rw [Bool.eq_iff_iff, elem_iff, decide_eq_true_iff]

@[simp] theorem contains_eq_mem [BEq α] [LawfulBEq α] (a : α) (as : Array α) :
    as.contains a = decide (a ∈ as) := by rw [← elem_eq_contains, elem_eq_mem]

/-- Variant of `any_push` with a side condition on `stop`. -/
@[simp] theorem any_push' [BEq α] {as : Array α} {a : α} {p : α → Bool} (h : stop = as.size + 1) :
    (as.push a).any p 0 stop = (as.any p || p a) := by
  cases as
  rw [List.push_toArray]
  simp [h]

theorem any_push [BEq α] {as : Array α} {a : α} {p : α → Bool} :
    (as.push a).any p = (as.any p || p a) :=
  any_push' (by simp)

/-- Variant of `all_push` with a side condition on `stop`. -/
@[simp] theorem all_push' [BEq α] {as : Array α} {a : α} {p : α → Bool} (h : stop = as.size + 1) :
    (as.push a).all p 0 stop = (as.all p && p a) := by
  cases as
  rw [List.push_toArray]
  simp [h]

theorem all_push [BEq α] {as : Array α} {a : α} {p : α → Bool} :
    (as.push a).all p = (as.all p && p a) :=
  all_push' (by simp)

@[simp] theorem contains_push [BEq α] {l : Array α} {a : α} {b : α} :
    (l.push a).contains b = (l.contains b || b == a) := by
  simp [contains]

/-! ### set -/

@[simp] theorem getElem_set_self (a : Array α) (i : Nat) (h : i < a.size) (v : α) {j : Nat}
      (eq : i = j) (p : j < (a.set i v).size) :
    (a.set i v)[j]'p = v := by
  cases a
  simp
  simp [set, ← getElem_toList, ←eq]

@[deprecated getElem_set_self (since := "2024-12-11")]
abbrev getElem_set_eq := @getElem_set_self

@[simp] theorem getElem?_set_self (a : Array α) (i : Nat) (h : i < a.size) (v : α) :
    (a.set i v)[i]? = v := by simp [getElem?_eq_getElem, h]

@[deprecated getElem?_set_self (since := "2024-12-11")]
abbrev getElem?_set_eq := @getElem?_set_self

@[simp] theorem getElem_set_ne (a : Array α) (i : Nat) (h' : i < a.size) (v : α) {j : Nat}
    (pj : j < (a.set i v).size) (h : i ≠ j) :
    (a.set i v)[j]'pj = a[j]'(size_set a i v _ ▸ pj) := by
  simp only [set, ← getElem_toList, List.getElem_set_ne h]

@[simp] theorem getElem?_set_ne (a : Array α) (i : Nat) (h : i < a.size) {j : Nat} (v : α)
    (ne : i ≠ j) : (a.set i v)[j]? = a[j]? := by
  by_cases h : j < a.size <;> simp [getElem?_eq_getElem, getElem?_eq_none, Nat.ge_of_not_lt, ne, h]

theorem getElem_set (a : Array α) (i : Nat) (h' : i < a.size) (v : α) (j : Nat)
    (h : j < (a.set i v).size) :
    (a.set i v)[j]'h = if i = j then v else a[j]'(size_set a i v _ ▸ h) := by
  by_cases p : i = j <;> simp [p]

theorem getElem?_set (a : Array α) (i : Nat) (h : i < a.size) (v : α) (j : Nat) :
    (a.set i v)[j]? = if i = j then some v else a[j]? := by
  split <;> simp_all

@[simp] theorem set_getElem_self {as : Array α} {i : Nat} (h : i < as.size) :
    as.set i as[i] = as := by
  cases as
  simp

@[simp] theorem set_eq_empty_iff {as : Array α} (n : Nat) (a : α) (h) :
     as.set n a = #[] ↔ as = #[] := by
  cases as <;> cases n <;> simp [set]

theorem set_comm (a b : α)
    {i j : Nat} (as : Array α) {hi : i < as.size} {hj : j < (as.set i a).size} (h : i ≠ j) :
    (as.set i a).set j b = (as.set j b (by simpa using hj)).set i a (by simpa using hi) := by
  cases as
  simp [List.set_comm _ _ _ h]

@[simp]
theorem set_set (a b : α) (as : Array α) (i : Nat) (h : i < as.size) :
    (as.set i a).set i b (by simpa using h) = as.set i b := by
  cases as
  simp

theorem mem_set (as : Array α) (i : Nat) (h : i < as.size) (a : α) :
    a ∈ as.set i a := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using h), by simp⟩

theorem mem_or_eq_of_mem_set
    {as : Array α} {i : Nat} {a b : α} {w : i < as.size} (h : a ∈ as.set i b) : a ∈ as ∨ a = b := by
  cases as
  simpa using List.mem_or_eq_of_mem_set (by simpa using h)

@[simp] theorem toList_set (a : Array α) (i x h) :
    (a.set i x).toList = a.toList.set i x := rfl

/-! ### setIfInBounds -/

@[simp] theorem set!_eq_setIfInBounds : @set! = @setIfInBounds := rfl

@[deprecated set!_eq_setIfInBounds (since := "2024-12-12")]
abbrev set!_is_setIfInBounds := @set!_eq_setIfInBounds

@[simp] theorem size_setIfInBounds (as : Array α) (index : Nat) (val : α) :
    (as.setIfInBounds index val).size = as.size := by
  if h : index < as.size  then
    simp [setIfInBounds, h]
  else
    simp [setIfInBounds, h]

theorem getElem_setIfInBounds (as : Array α) (i : Nat) (v : α) (j : Nat)
    (hj : j < (as.setIfInBounds i v).size) :
    (as.setIfInBounds i v)[j]'hj = if i = j then v else as[j]'(by simpa using hj) := by
  simp only [setIfInBounds]
  split
  · simp [getElem_set]
  · simp only [size_setIfInBounds] at hj
    rw [if_neg]
    omega

@[simp] theorem getElem_setIfInBounds_self (as : Array α) {i : Nat} (v : α) (h : _) :
    (as.setIfInBounds i v)[i]'h = v := by
  simp at h
  simp only [setIfInBounds, h, ↓reduceDIte, getElem_set_self]

@[deprecated getElem_setIfInBounds_self (since := "2024-12-11")]
abbrev getElem_setIfInBounds_eq := @getElem_setIfInBounds_self

@[simp] theorem getElem_setIfInBounds_ne (as : Array α) {i : Nat} (v : α) {j : Nat}
    (hj : j < (as.setIfInBounds i v).size) (h : i ≠ j) :
    (as.setIfInBounds i v)[j]'hj = as[j]'(by simpa using hj) := by
  simp [getElem_setIfInBounds, h]

theorem getElem?_setIfInBounds {as : Array α} {i j : Nat} {a : α}  :
    (as.setIfInBounds i a)[j]? = if i = j then if i < as.size then some a else none else as[j]? := by
  cases as
  simp [List.getElem?_set]

theorem getElem?_setIfInBounds_self (as : Array α) {i : Nat} (v : α) :
    (as.setIfInBounds i v)[i]? = if i < as.size then some v else none := by
  simp [getElem?_setIfInBounds]

@[simp]
theorem getElem?_setIfInBounds_self_of_lt (as : Array α) {i : Nat} (v : α) (h : i < as.size) :
    (as.setIfInBounds i v)[i]? = some v := by
  simp [getElem?_setIfInBounds, h]

@[deprecated getElem?_setIfInBounds_self (since := "2024-12-11")]
abbrev getElem?_setIfInBounds_eq := @getElem?_setIfInBounds_self

@[simp] theorem getElem?_setIfInBounds_ne {as : Array α} {i j : Nat} (h : i ≠ j) {a : α}  :
    (as.setIfInBounds i a)[j]? = as[j]? := by
  simp [getElem?_setIfInBounds, h]

theorem setIfInBounds_eq_of_size_le {l : Array α} {n : Nat} (h : l.size ≤ n) {a : α} :
    l.setIfInBounds n a = l := by
  cases l
  simp [List.set_eq_of_length_le (by simpa using h)]

@[simp] theorem setIfInBounds_eq_empty_iff {as : Array α} (n : Nat) (a : α) :
     as.setIfInBounds n a = #[] ↔ as = #[] := by
  cases as <;> cases n <;> simp

theorem setIfInBounds_comm (a b : α)
    {i j : Nat} (as : Array α) (h : i ≠ j) :
    (as.setIfInBounds i a).setIfInBounds j b = (as.setIfInBounds j b).setIfInBounds i a := by
  cases as
  simp [List.set_comm _ _ _ h]

@[simp]
theorem setIfInBounds_setIfInBounds (a b : α) (as : Array α) (i : Nat) :
    (as.setIfInBounds i a).setIfInBounds i b = as.setIfInBounds i b := by
  cases as
  simp

theorem mem_setIfInBounds (as : Array α) (i : Nat) (h : i < as.size) (a : α) :
    a ∈ as.setIfInBounds i a := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using h), by simp⟩

theorem mem_or_eq_of_mem_setIfInBounds
    {as : Array α} {i : Nat} {a b : α} (h : a ∈ as.setIfInBounds i b) : a ∈ as ∨ a = b := by
  cases as
  simpa using List.mem_or_eq_of_mem_set (by simpa using h)

/-- Simplifies a normal form from `get!` -/
@[simp] theorem getD_get?_setIfInBounds (a : Array α) (i : Nat) (v d : α) :
    (setIfInBounds a i v)[i]?.getD d = if i < a.size then v else d := by
  by_cases h : i < a.size <;>
    simp [setIfInBounds, Nat.not_lt_of_le, h,  getD_getElem?]

@[simp] theorem toList_setIfInBounds (a : Array α) (i x) :
    (a.setIfInBounds i x).toList = a.toList.set i x := by
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

@[simp] theorem push_beq_push [BEq α] {a b : α} {v : Array α} {w : Array α} :
    (v.push a == w.push b) = (v == w && a == b) := by
  cases v
  cases w
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
    · intro a b h
      obtain ⟨hs, hi⟩ := rel_of_isEqv h
      ext i h₁ h₂
      · exact hs
      · simpa using hi _ h₁
    · intro a
      apply Array.isEqv_self_beq

/-! ### isEqv -/

@[simp] theorem isEqv_eq [DecidableEq α] {l₁ l₂ : Array α} : l₁.isEqv l₂ (· == ·) = (l₁ = l₂) := by
  cases l₁
  cases l₂
  simp

/-! ### map -/

theorem mapM_eq_foldlM [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = arr.foldlM (fun bs a => bs.push <$> f a) #[] := by
  rw [mapM, aux, ← foldlM_toList]; rfl
where
  aux (i r) :
      mapM.map f arr i r = (arr.toList.drop i).foldlM (fun bs a => bs.push <$> f a) r := by
    unfold mapM.map; split
    · rw [← List.getElem_cons_drop_succ_eq_drop ‹_›]
      simp only [aux (i + 1), map_eq_pure_bind, length_toList, List.foldlM_cons, bind_assoc,
        pure_bind]
      rfl
    · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; rfl
  termination_by arr.size - i
  decreasing_by decreasing_trivial_pre_omega

@[simp] theorem toList_map (f : α → β) (arr : Array α) : (arr.map f).toList = arr.toList.map f := by
  rw [map, mapM_eq_foldlM]
  apply congrArg toList (foldl_toList (fun bs a => push bs (f a)) #[] arr).symm |>.trans
  have H (l arr) : List.foldl (fun bs a => push bs (f a)) arr l = ⟨arr.toList ++ l.map f⟩ := by
    induction l generalizing arr <;> simp [*]
  simp [H]

@[simp] theorem _root_.List.map_toArray (f : α → β) (l : List α) :
    l.toArray.map f = (l.map f).toArray := by
  apply ext'
  simp

@[simp] theorem size_map (f : α → β) (arr : Array α) : (arr.map f).size = arr.size := by
  simp only [← length_toList]
  simp

@[simp] theorem getElem_map (f : α → β) (a : Array α) (i : Nat) (hi : i < (a.map f).size) :
    (a.map f)[i] = f (a[i]'(by simpa using hi)) := by
  cases a
  simp

@[simp] theorem getElem?_map (f : α → β) (as : Array α) (i : Nat) :
    (as.map f)[i]? = as[i]?.map f := by
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
  funext l
  induction l <;> simp_all

/-- `map_id_fun'` differs from `map_id_fun` by representing the identity function as a lambda, rather than `id`. -/
@[simp] theorem map_id_fun' : map (fun (a : α) => a) = id := map_id_fun

-- This is not a `@[simp]` lemma because `map_id_fun` will apply.
theorem map_id (l : Array α) : map (id : α → α) l = l := by
  cases l <;> simp_all

/-- `map_id'` differs from `map_id` by representing the identity function as a lambda, rather than `id`. -/
-- This is not a `@[simp]` lemma because `map_id_fun'` will apply.
theorem map_id' (l : Array α) : map (fun (a : α) => a) l = l := map_id l

/-- Variant of `map_id`, with a side condition that the function is pointwise the identity. -/
theorem map_id'' {f : α → α} (h : ∀ x, f x = x) (l : Array α) : map f l = l := by
  simp [show f = id from funext h]

theorem map_singleton (f : α → β) (a : α) : map f #[a] = #[f a] := rfl

-- We use a lower priority here as there are more specific lemmas in downstream libraries
-- which should be able to fire first.
@[simp 500] theorem mem_map {f : α → β} {l : Array α} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  simp only [mem_def, toList_map, List.mem_map]

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem forall_mem_map {f : α → β} {l : Array α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ l.map f), P i) ↔ ∀ (j) (_ : j ∈ l), P (f j) := by
  simp

@[simp] theorem map_eq_empty_iff {f : α → β} {l : Array α} : map f l = #[] ↔ l = #[] := by
  cases l
  simp

theorem eq_empty_of_map_eq_empty {f : α → β} {l : Array α} (h : map f l = #[]) : l = #[] :=
  map_eq_empty_iff.mp h

@[simp] theorem map_inj_left {f g : α → β} : map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  cases l <;> simp_all

theorem map_inj_right {f : α → β} (w : ∀ x y, f x = f y → x = y) : map f l = map f l' ↔ l = l' := by
  cases l
  cases l'
  simp [List.map_inj_right w]

theorem map_congr_left (h : ∀ a ∈ l, f a = g a) : map f l = map g l :=
  map_inj_left.2 h

theorem map_inj : map f = map g ↔ f = g := by
  constructor
  · intro h; ext a; replace h := congrFun h #[a]; simpa using h
  · intro h; subst h; rfl

theorem map_eq_push_iff {f : α → β} {l : Array α} {l₂ : Array β} {b : β} :
    map f l = l₂.push b ↔ ∃ l₁ a, l = l₁.push a ∧ map f l₁ = l₂ ∧ f a = b := by
  rcases l with ⟨l⟩
  rcases l₂ with ⟨l₂⟩
  simp only [List.map_toArray, List.push_toArray, mk.injEq, List.map_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, h⟩
    simp only [List.map_eq_singleton_iff] at h
    obtain ⟨a, rfl, rfl⟩ := h
    refine ⟨l₁.toArray, a, by simp⟩
  · rintro ⟨⟨l₁⟩, a, h₁, h₂, rfl⟩
    refine ⟨l₁, [a], by simp_all⟩

@[simp] theorem map_eq_singleton_iff {f : α → β} {l : Array α} {b : β} :
    map f l = #[b] ↔ ∃ a, l = #[a] ∧ f a = b := by
  cases l
  simp

theorem map_eq_map_iff {f g : α → β} {l : Array α} :
    map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  cases l <;> simp_all

theorem map_eq_iff : map f l = l' ↔ ∀ i : Nat, l'[i]? = l[i]?.map f := by
  cases l
  cases l'
  simp [List.map_eq_iff]

theorem map_eq_foldl (f : α → β) (l : Array α) :
    map f l = foldl (fun bs a => bs.push (f a)) #[] l := by
  simpa using mapM_eq_foldlM (m := Id) f l

@[simp] theorem map_set {f : α → β} {l : Array α} {i : Nat} {h : i < l.size} {a : α} :
    (l.set i a).map f = (l.map f).set i (f a) (by simpa using h) := by
  cases l
  simp

@[simp] theorem map_setIfInBounds {f : α → β} {l : Array α} {i : Nat} {a : α} :
    (l.setIfInBounds i a).map f = (l.map f).setIfInBounds i (f a) := by
  cases l
  simp

@[simp] theorem map_pop {f : α → β} {l : Array α} : l.pop.map f = (l.map f).pop := by
  cases l
  simp

@[simp] theorem back?_map {f : α → β} {l : Array α} : (l.map f).back? = l.back?.map f := by
  cases l
  simp

@[simp] theorem map_map {f : α → β} {g : β → γ} {as : Array α} :
    (as.map f).map g = as.map (g ∘ f) := by
  cases as; simp

theorem mapM_eq_mapM_toList [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    arr.mapM f = List.toArray <$> (arr.toList.mapM f) := by
  rw [mapM_eq_foldlM, ← foldlM_toList, ← List.foldrM_reverse]
  conv => rhs; rw [← List.reverse_reverse arr.toList]
  induction arr.toList.reverse with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem toList_mapM [Monad m] [LawfulMonad m] (f : α → m β) (arr : Array α) :
    toList <$> arr.mapM f = arr.toList.mapM f := by
  simp [mapM_eq_mapM_toList]

@[deprecated "Use `mapM_eq_foldlM` instead" (since := "2025-01-08")]
theorem mapM_map_eq_foldl (as : Array α) (f : α → β) (i) :
    mapM.map (m := Id) f as i b = as.foldl (start := i) (fun r a => r.push (f a)) b := by
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
    (ass : Array (Array α)) : P ass := by
  specialize of (ass.toList.map toList)
  simpa [← toList_map, Function.comp_def, map_id] using of

/--
Use this as `induction ass using array₃_induction` on a hypothesis of the form `ass : Array (Array (Array α))`.
The hypothesis `ass` will be replaced with a hypothesis `ass : List (List (List α))`,
and former appearances of `ass` in the goal will be replaced with
`((ass.map (fun xs => xs.map List.toArray)).map List.toArray).toArray`.
-/
theorem array₃_induction (P : Array (Array (Array α)) → Prop)
    (of : ∀ (xss : List (List (List α))), P ((xss.map (fun xs => xs.map List.toArray)).map List.toArray).toArray)
    (ass : Array (Array (Array α))) : P ass := by
  specialize of ((ass.toList.map toList).map (fun as => as.map toList))
  simpa [← toList_map, Function.comp_def, map_id] using of

/-! ### filter -/

@[congr]
theorem filter_congr {as bs : Array α} (h : as = bs)
    {f : α → Bool} {g : α → Bool} (h' : f = g) {start stop start' stop' : Nat}
    (h₁ : start = start') (h₂ : stop = stop') :
    filter f as start stop = filter g bs start' stop' := by
  congr

@[simp] theorem toList_filter' (p : α → Bool) (l : Array α) (h : stop = l.size) :
    (l.filter p 0 stop).toList = l.toList.filter p := by
  subst h
  dsimp only [filter]
  rw [← foldl_toList]
  generalize l.toList = l
  suffices ∀ a, (List.foldl (fun r a => if p a = true then push r a else r) a l).toList =
      a.toList ++ List.filter p l by
    simpa using this #[]
  induction l with simp
  | cons => split <;> simp [*]

theorem toList_filter (p : α → Bool) (l : Array α) :
    (l.filter p).toList = l.toList.filter p := by
  simp

@[simp] theorem _root_.List.filter_toArray' (p : α → Bool) (l : List α) (h : stop = l.length) :
    l.toArray.filter p 0 stop = (l.filter p).toArray := by
  apply ext'
  simp [h]

theorem _root_.List.filter_toArray (p : α → Bool) (l : List α) :
    l.toArray.filter p = (l.filter p).toArray := by
  simp

@[simp] theorem filter_push_of_pos {p : α → Bool} {a : α} {l : Array α}
    (h : p a) (w : stop = l.size + 1):
    (l.push a).filter p 0 stop = (l.filter p).push a := by
  subst w
  rcases l with ⟨l⟩
  simp [h]

@[simp] theorem filter_push_of_neg {p : α → Bool} {a : α} {l : Array α}
    (h : ¬p a) (w : stop = l.size + 1) :
    (l.push a).filter p 0 stop = l.filter p := by
  subst w
  rcases l with ⟨l⟩
  simp [h]

theorem filter_push {p : α → Bool} {a : α} {l : Array α} :
    (l.push a).filter p = if p a then (l.filter p).push a else l.filter p := by
  split <;> simp [*]

theorem size_filter_le (p : α → Bool) (l : Array α) :
    (l.filter p).size ≤ l.size := by
  rcases l with ⟨l⟩
  simpa using List.length_filter_le p l

@[simp] theorem filter_eq_self {p : α → Bool} {l : Array α} :
    filter p l = l ↔ ∀ a ∈ l, p a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem filter_size_eq_size {p : α → Bool} {l : Array α} :
    (filter p l).size = l.size ↔ ∀ a ∈ l, p a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem mem_filter {p : α → Bool} {l : Array α} {a : α} :
    a ∈ filter p l ↔ a ∈ l ∧ p a := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem filter_eq_empty_iff {p : α → Bool} {l : Array α} :
    filter p l = #[] ↔ ∀ a, a ∈ l → ¬p a := by
  rcases l with ⟨l⟩
  simp

theorem forall_mem_filter {p : α → Bool} {l : Array α} {P : α → Prop} :
    (∀ (i) (_ : i ∈ l.filter p), P i) ↔ ∀ (j) (_ : j ∈ l), p j → P j := by
  simp

@[simp] theorem filter_filter (q) (l : Array α) :
    filter p (filter q l) = filter (fun a => p a && q a) l := by
  apply ext'
  simp only [toList_filter, List.filter_filter]

theorem foldl_filter (p : α → Bool) (f : β → α → β) (l : Array α) (init : β) :
    (l.filter p).foldl f init = l.foldl (fun x y => if p y then f x y else x) init := by
  rcases l with ⟨l⟩
  rw [List.filter_toArray]
  simp [List.foldl_filter]

theorem foldr_filter (p : α → Bool) (f : α → β → β) (l : Array α) (init : β) :
    (l.filter p).foldr f init = l.foldr (fun x y => if p x then f x y else y) init := by
  rcases l with ⟨l⟩
  rw [List.filter_toArray]
  simp [List.foldr_filter]

theorem filter_map (f : β → α) (l : Array β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  rcases l with ⟨l⟩
  simp [List.filter_map]

theorem map_filter_eq_foldl (f : α → β) (p : α → Bool) (l : Array α) :
    map f (filter p l) = foldl (fun y x => bif p x then y.push (f x) else y) #[] l := by
  rcases l with ⟨l⟩
  apply ext'
  simp only [size_toArray, List.filter_toArray', List.map_toArray, List.foldl_toArray']
  rw [← List.reverse_reverse l]
  generalize l.reverse = l
  simp only [List.filter_reverse, List.map_reverse, List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.filter_cons, List.foldr_cons]
    split <;> simp_all

@[simp] theorem filter_append {p : α → Bool} (l₁ l₂ : Array α) :
    filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂ := by
  rcases l₁ with ⟨l₁⟩
  rcases l₂ with ⟨l₂⟩
  simp [List.filter_append]

theorem filter_eq_append_iff {p : α → Bool} :
    filter p l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filter p l₁ = L₁ ∧ filter p l₂ = L₂ := by
  rcases l with ⟨l⟩
  rcases L₁ with ⟨L₁⟩
  rcases L₂ with ⟨L₂⟩
  simp only [size_toArray, List.filter_toArray', List.append_toArray, mk.injEq,
    List.filter_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    refine ⟨l₁.toArray, l₂.toArray, by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, h₁, h₂, h₃⟩
    refine ⟨l₁, l₂, by simp_all⟩

theorem filter_eq_push_iff {p : α → Bool} {l l' : Array α} {a : α} :
    filter p l = l'.push a ↔
      ∃ l₁ l₂, l = l₁.push a ++ l₂ ∧ filter p l₁ = l' ∧ p a ∧ (∀ x, x ∈ l₂ → ¬p x) := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp only [size_toArray, List.filter_toArray', List.push_toArray, mk.injEq, Bool.not_eq_true]
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

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  (mem_filter.mp h).1

/-! ### filterMap -/

@[congr]
theorem filterMap_congr {as bs : Array α} (h : as = bs)
    {f : α → Option β} {g : α → Option β} (h' : f = g) {start stop start' stop' : Nat}
    (h₁ : start = start') (h₂ : stop = stop') :
    filterMap f as start stop = filterMap g bs start' stop' := by
  congr

@[simp] theorem toList_filterMap' (f : α → Option β) (l : Array α) (w : stop = l.size) :
    (l.filterMap f 0 stop).toList = l.toList.filterMap f := by
  subst w
  dsimp only [filterMap, filterMapM]
  rw [← foldlM_toList]
  generalize l.toList = l
  have this : ∀ a : Array β, (Id.run (List.foldlM (m := Id) ?_ a l)).toList =
    a.toList ++ List.filterMap f l := ?_
  exact this #[]
  induction l
  · simp_all [Id.run]
  · simp_all [Id.run, List.filterMap_cons]
    split <;> simp_all

theorem toList_filterMap (f : α → Option β) (l : Array α) :
    (l.filterMap f).toList = l.toList.filterMap f := by
  simp [toList_filterMap']


@[simp] theorem _root_.List.filterMap_toArray' (f : α → Option β) (l : List α) (h : stop = l.length) :
    l.toArray.filterMap f 0 stop = (l.filterMap f).toArray := by
  apply ext'
  simp [h]

theorem _root_.List.filterMap_toArray (f : α → Option β) (l : List α) :
    l.toArray.filterMap f = (l.filterMap f).toArray := by
  simp

@[simp] theorem filterMap_push_none {f : α → Option β} {a : α} {l : Array α}
    (h : f a = none) (w : stop = l.size + 1) :
    filterMap f (l.push a) 0 stop = filterMap f l := by
  subst w
  rcases l with ⟨l⟩
  simp [h]

@[simp] theorem filterMap_push_some {f : α → Option β} {a : α} {l : Array α} {b : β}
    (h : f a = some b) (w : stop = l.size + 1) :
    filterMap f (l.push a) 0 stop = (filterMap f l).push b := by
  subst w
  rcases l with ⟨l⟩
  simp [h]

@[simp] theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f := by
  funext l
  cases l
  simp

theorem filterMap_some_fun : filterMap (some : α → Option α) = id := by
  funext l
  cases l
  simp

@[simp] theorem filterMap_some (l : Array α) : filterMap some l = l := by
  cases l
  simp

theorem map_filterMap_some_eq_filterMap_isSome (f : α → Option β) (l : Array α) :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome := by
  cases l
  simp [List.map_filterMap_some_eq_filter_map_isSome]

theorem size_filterMap_le (f : α → Option β) (l : Array α) :
    (filterMap f l).size ≤ l.size := by
  cases l
  simp [List.length_filterMap_le]

@[simp] theorem filterMap_size_eq_size {l} :
    (filterMap f l).size = l.size ↔ ∀ a, a ∈ l → (f a).isSome := by
  cases l
  simp [List.filterMap_length_eq_length]

@[simp]
theorem filterMap_eq_filter (p : α → Bool) :
    filterMap (Option.guard (p ·)) = filter p := by
  funext l
  cases l
  simp

theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (l : Array α) :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l := by
  cases l
  simp [List.filterMap_filterMap]

theorem map_filterMap (f : α → Option β) (g : β → γ) (l : Array α) :
    map g (filterMap f l) = filterMap (fun x => (f x).map g) l := by
  cases l
  simp [List.map_filterMap]

@[simp] theorem filterMap_map (f : α → β) (g : β → Option γ) (l : Array α) :
    filterMap g (map f l) = filterMap (g ∘ f) l := by
  cases l
  simp [List.filterMap_map]

theorem filter_filterMap (f : α → Option β) (p : β → Bool) (l : Array α) :
    filter p (filterMap f l) = filterMap (fun x => (f x).filter p) l := by
  cases l
  simp [List.filter_filterMap]

theorem filterMap_filter (p : α → Bool) (f : α → Option β) (l : Array α) :
    filterMap f (filter p l) = filterMap (fun x => if p x then f x else none) l := by
  cases l
  simp [List.filterMap_filter]

@[simp] theorem mem_filterMap {f : α → Option β} {l : Array α} {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b := by
  simp only [mem_def, toList_filterMap, List.mem_filterMap]

theorem forall_mem_filterMap {f : α → Option β} {l : Array α} {P : β → Prop} :
    (∀ (i) (_ : i ∈ filterMap f l), P i) ↔ ∀ (j) (_ : j ∈ l) (b), f j = some b → P b := by
  simp only [mem_filterMap, forall_exists_index, and_imp]
  rw [forall_comm]
  apply forall_congr'
  intro a
  rw [forall_comm]

@[simp] theorem filterMap_append {α β : Type _} (l l' : Array α) (f : α → Option β) :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' := by
  cases l
  cases l'
  simp

theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (l : Array α) : map g (filterMap f l) = l := by simp only [map_filterMap, H, filterMap_some, id]

theorem forall_none_of_filterMap_eq_empty (h : filterMap f xs = #[]) : ∀ x ∈ xs, f x = none := by
  cases xs
  simpa using h

@[simp] theorem filterMap_eq_nil_iff {l} : filterMap f l = #[] ↔ ∀ a, a ∈ l → f a = none := by
  cases l
  simp

theorem filterMap_eq_push_iff {f : α → Option β} {l : Array α} {l' : Array β} {b : β} :
    filterMap f l = l'.push b ↔ ∃ l₁ a l₂,
      l = l₁.push a ++ l₂ ∧ filterMap f l₁ = l' ∧ f a = some b ∧ (∀ x, x ∈ l₂ → f x = none) := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp only [size_toArray, List.filterMap_toArray', List.push_toArray, mk.injEq]
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

/-! ### singleton -/

@[simp] theorem singleton_def (v : α) : Array.singleton v = #[v] := rfl

/-! ### append -/

@[simp] theorem size_append (as bs : Array α) : (as ++ bs).size = as.size + bs.size := by
  simp only [size, toList_append, List.length_append]

@[simp] theorem append_push {as bs : Array α} {a : α} : as ++ bs.push a = (as ++ bs).push a := by
  cases as
  cases bs
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

@[simp] theorem append_eq_toArray_iff {as bs : Array α} {xs : List α} :
    as ++ bs = xs.toArray ↔ as.toList ++ bs.toList = xs := by
  cases as
  cases bs
  simp

theorem singleton_eq_toArray_singleton (a : α) : #[a] = [a].toArray := rfl

@[simp] theorem empty_append_fun : ((#[] : Array α) ++ ·) = id := by
  funext ⟨l⟩
  simp

@[simp] theorem mem_append {a : α} {s t : Array α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  simp only [mem_def, toList_append, List.mem_append]

theorem mem_append_left {a : α} {l₁ : Array α} (l₂ : Array α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (l₁ : Array α) {l₂ : Array α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  mem_append.2 (Or.inr h)

theorem not_mem_append {a : α} {s t : Array α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
  mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

/--
See also `eq_push_append_of_mem`, which proves a stronger version
in which the initial array must not contain the element.
-/
theorem append_of_mem {a : α} {l : Array α} (h : a ∈ l) : ∃ s t : Array α, l = s.push a ++ t := by
  obtain ⟨s, t, w⟩ := List.append_of_mem (l := l.toList) (by simpa using h)
  replace w := congrArg List.toArray w
  refine ⟨s.toArray, t.toArray, by simp_all⟩

theorem mem_iff_append {a : α} {l : Array α} : a ∈ l ↔ ∃ s t : Array α, l = s.push a ++ t :=
  ⟨append_of_mem, fun ⟨s, t, e⟩ => e ▸ by simp⟩

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : Array α} :
    (∀ (x) (_ : x ∈ l₁ ++ l₂), p x) ↔ (∀ (x) (_ : x ∈ l₁), p x) ∧ (∀ (x) (_ : x ∈ l₂), p x) := by
  simp only [mem_append, or_imp, forall_and]

theorem getElem_append {as bs : Array α} (h : i < (as ++ bs).size) :
    (as ++ bs)[i] = if h' : i < as.size then as[i] else bs[i - as.size]'(by simp at h; omega) := by
  cases as; cases bs
  simp [List.getElem_append]

theorem getElem_append_left {as bs : Array α} {h : i < (as ++ bs).size} (hlt : i < as.size) :
    (as ++ bs)[i] = as[i] := by
  simp only [← getElem_toList]
  have h' : i < (as.toList ++ bs.toList).length := by rwa [← length_toList, toList_append] at h
  conv => rhs; rw [← List.getElem_append_left (bs := bs.toList) (h' := h')]
  apply List.get_of_eq; rw [toList_append]

theorem getElem_append_right {as bs : Array α} {h : i < (as ++ bs).size} (hle : as.size ≤ i) :
    (as ++ bs)[i] = bs[i - as.size]'(Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) := by
  simp only [← getElem_toList]
  have h' : i < (as.toList ++ bs.toList).length := by rwa [← length_toList, toList_append] at h
  conv => rhs; rw [← List.getElem_append_right (h₁ := hle) (h₂ := h')]
  apply List.get_of_eq; rw [toList_append]

theorem getElem?_append_left {as bs : Array α} {i : Nat} (hn : i < as.size) :
    (as ++ bs)[i]? = as[i]? := by
  have hn' : i < (as ++ bs).size := Nat.lt_of_lt_of_le hn <|
    size_append .. ▸ Nat.le_add_right ..
  simp_all [getElem?_eq_getElem, getElem_append]

theorem getElem?_append_right {as bs : Array α} {i : Nat} (h : as.size ≤ i) :
    (as ++ bs)[i]? = bs[i - as.size]? := by
  cases as
  cases bs
  simp at h
  simp [List.getElem?_append_right, h]

theorem getElem?_append {as bs : Array α} {i : Nat} :
    (as ++ bs)[i]? = if i < as.size then as[i]? else bs[i - as.size]? := by
  split <;> rename_i h
  · exact getElem?_append_left h
  · exact getElem?_append_right (by simpa using h)

/-- Variant of `getElem_append_left` useful for rewriting from the small array to the big array. -/
theorem getElem_append_left' (l₂ : Array α) {l₁ : Array α} {i : Nat} (hi : i < l₁.size) :
    l₁[i] = (l₁ ++ l₂)[i]'(by simpa using Nat.lt_add_right l₂.size hi) := by
  rw [getElem_append_left] <;> simp

/-- Variant of `getElem_append_right` useful for rewriting from the small array to the big array. -/
theorem getElem_append_right' (l₁ : Array α) {l₂ : Array α} {i : Nat} (hi : i < l₂.size) :
    l₂[i] = (l₁ ++ l₂)[i + l₁.size]'(by simpa [Nat.add_comm] using Nat.add_lt_add_left hi _) := by
  rw [getElem_append_right] <;> simp [*, Nat.le_add_left]

theorem getElem_of_append {l l₁ l₂ : Array α} (eq : l = l₁.push a ++ l₂) (h : l₁.size = i) :
    l[i]'(eq ▸ h ▸ by simp_arith) = a := Option.some.inj <| by
  rw [← getElem?_eq_getElem, eq, getElem?_append_left (by simp; omega), ← h]
  simp

@[simp] theorem append_singleton {a : α} {as : Array α} : as ++ #[a] = as.push a := rfl

theorem push_eq_append {a : α} {as : Array α} : as.push a = as ++ #[a] := rfl

theorem append_inj {s₁ s₂ t₁ t₂ : Array α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : s₁.size = s₂.size) :
    s₁ = s₂ ∧ t₁ = t₂ := by
  rcases s₁ with ⟨s₁⟩
  rcases s₂ with ⟨s₂⟩
  rcases t₁ with ⟨t₁⟩
  rcases t₂ with ⟨t₂⟩
  simpa using List.append_inj (by simpa using h) (by simpa using hl)

theorem append_inj_right {s₁ s₂ t₁ t₂ : Array α}
    (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : s₁.size = s₂.size) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left {s₁ s₂ t₁ t₂ : Array α}
    (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : s₁.size = s₂.size) : s₁ = s₂ :=
  (append_inj h hl).left

/-- Variant of `append_inj` instead requiring equality of the sizes of the second arrays. -/
theorem append_inj' {s₁ s₂ t₁ t₂ : Array α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : t₁.size = t₂.size) :
    s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <| @Nat.add_right_cancel _ t₁.size _ <| by
    let hap := congrArg size h; simp only [size_append, ← hl] at hap; exact hap

/-- Variant of `append_inj_right` instead requiring equality of the sizes of the second arrays. -/
theorem append_inj_right' {s₁ s₂ t₁ t₂ : Array α}
    (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : t₁.size = t₂.size) : t₁ = t₂ :=
  (append_inj' h hl).right

/-- Variant of `append_inj_left` instead requiring equality of the sizes of the second arrays. -/
theorem append_inj_left' {s₁ s₂ t₁ t₂ : Array α}
    (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : t₁.size = t₂.size) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_right_inj {t₁ t₂ : Array α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => append_inj_right h rfl, congrArg _⟩

theorem append_left_inj {s₁ s₂ : Array α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  ⟨fun h => append_inj_left' h rfl, congrArg (· ++ _)⟩

@[simp] theorem append_left_eq_self {x y : Array α} : x ++ y = y ↔ x = #[] := by
  rw [← append_left_inj (s₁ := x), empty_append]

@[simp] theorem self_eq_append_left {x y : Array α} : y = x ++ y ↔ x = #[] := by
  rw [eq_comm, append_left_eq_self]

@[simp] theorem append_right_eq_self {x y : Array α} : x ++ y = x ↔ y = #[] := by
  rw [← append_right_inj (t₁ := y), append_empty]

@[simp] theorem self_eq_append_right {x y : Array α} : x = x ++ y ↔ y = #[] := by
  rw [eq_comm, append_right_eq_self]

@[simp] theorem append_eq_empty_iff : p ++ q = #[] ↔ p = #[] ∧ q = #[] := by
  cases p <;> simp

@[simp] theorem empty_eq_append_iff : #[] = a ++ b ↔ a = #[] ∧ b = #[] := by
  rw [eq_comm, append_eq_empty_iff]

theorem append_ne_empty_of_left_ne_empty {s : Array α} (h : s ≠ #[]) (t : Array α) :
    s ++ t ≠ #[] := by
  simp_all

theorem append_ne_empty_of_right_ne_empty (s : Array α) : t ≠ #[] → s ++ t ≠ #[] := by
  simp_all

theorem append_eq_push_iff {a b c : Array α} {x : α} :
    a ++ b = c.push x ↔ (b = #[] ∧ a = c.push x) ∨ (∃ b', b = b'.push x ∧ c = a ++ b') := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases c with ⟨c⟩
  simp only [List.append_toArray, List.push_toArray, mk.injEq, List.append_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro (⟨a', rfl, rfl⟩ | ⟨b', rfl, h⟩)
    · right; exact ⟨⟨a'⟩, by simp⟩
    · rw [List.singleton_eq_append_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h
      · right; exact ⟨#[], by simp⟩
      · left; simp
  · rintro (⟨rfl, rfl⟩ | ⟨b', h, rfl⟩)
    · right; exact ⟨[x], by simp⟩
    · left; refine ⟨b'.toList, ?_⟩
      replace h := congrArg Array.toList h
      simp_all

theorem push_eq_append_iff {a b c : Array α} {x : α} :
    c.push x = a ++ b ↔ (b = #[] ∧ a = c.push x) ∨ (∃ b', b = b'.push x ∧ c = a ++ b') := by
  rw [eq_comm, append_eq_push_iff]

theorem append_eq_singleton_iff {a b : Array α} {x : α} :
    a ++ b = #[x] ↔ (a = #[] ∧ b = #[x]) ∨ (a = #[x] ∧ b = #[]) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  simp only [List.append_toArray, mk.injEq, List.append_eq_singleton_iff, toArray_eq_append_iff]

theorem singleton_eq_append_iff {a b : Array α} {x : α} :
    #[x] = a ++ b ↔ (a = #[] ∧ b = #[x]) ∨ (a = #[x] ∧ b = #[]) := by
  rw [eq_comm, append_eq_singleton_iff]

theorem append_eq_append_iff {a b c d : Array α} :
    a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases c with ⟨c⟩
  rcases d with ⟨d⟩
  simp only [List.append_toArray, mk.injEq, List.append_eq_append_iff, toArray_eq_append_iff]
  constructor
  · rintro (⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩)
    · left; exact ⟨⟨a'⟩, by simp⟩
    · right; exact ⟨⟨c'⟩, by simp⟩
  · rintro (⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩)
    · left; exact ⟨a'.toList, by simp⟩
    · right; exact ⟨c'.toList, by simp⟩

theorem set_append {s t : Array α} {i : Nat} {x : α} (h : i < (s ++ t).size) :
    (s ++ t).set i x =
      if h' : i < s.size then
        s.set i x ++ t
      else
        s ++ t.set (i - s.size) x (by simp at h; omega) := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  simp only [List.append_toArray, List.set_toArray, List.set_append]
  split <;> simp

@[simp] theorem set_append_left {s t : Array α} {i : Nat} {x : α} (h : i < s.size) :
    (s ++ t).set i x (by simp; omega) = s.set i x ++ t := by
  simp [set_append, h]

@[simp] theorem set_append_right {s t : Array α} {i : Nat} {x : α}
    (h' : i < (s ++ t).size) (h : s.size ≤ i) :
    (s ++ t).set i x = s ++ t.set (i - s.size) x (by simp at h'; omega) := by
  rw [set_append, dif_neg (by omega)]

theorem setIfInBounds_append {s t : Array α} {i : Nat} {x : α} :
    (s ++ t).setIfInBounds i x =
      if i < s.size then
        s.setIfInBounds i x ++ t
      else
        s ++ t.setIfInBounds (i - s.size) x := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  simp only [List.append_toArray, List.setIfInBounds_toArray, List.set_append]
  split <;> simp

@[simp] theorem setIfInBounds_append_left {s t : Array α} {i : Nat} {x : α} (h : i < s.size) :
    (s ++ t).setIfInBounds i x = s.setIfInBounds i x ++ t := by
  simp [setIfInBounds_append, h]

@[simp] theorem setIfInBounds_append_right {s t : Array α} {i : Nat} {x : α} (h : s.size ≤ i) :
    (s ++ t).setIfInBounds i x = s ++ t.setIfInBounds (i - s.size) x := by
  rw [setIfInBounds_append, if_neg (by omega)]

theorem filterMap_eq_append_iff {f : α → Option β} :
    filterMap f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filterMap f l₁ = L₁ ∧ filterMap f l₂ = L₂ := by
  rcases l with ⟨l⟩
  rcases L₁ with ⟨L₁⟩
  rcases L₂ with ⟨L₂⟩
  simp only [size_toArray, List.filterMap_toArray', List.append_toArray, mk.injEq,
    List.filterMap_eq_append_iff, toArray_eq_append_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨⟨l₁⟩, ⟨l₂⟩, by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, rfl, h₁, h₂⟩
    exact ⟨l₁, l₂, by simp_all⟩

theorem append_eq_filterMap_iff {f : α → Option β} :
    L₁ ++ L₂ = filterMap f l ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filterMap f l₁ = L₁ ∧ filterMap f l₂ = L₂ := by
  rw [eq_comm, filterMap_eq_append_iff]

@[simp] theorem map_append (f : α → β) (l₁ l₂ : Array α) :
    map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  cases l₁
  cases l₂
  simp

theorem map_eq_append_iff {f : α → β} :
    map f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rw [← filterMap_eq_map, filterMap_eq_append_iff]

theorem append_eq_map_iff {f : α → β} :
    L₁ ++ L₂ = map f l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rw [eq_comm, map_eq_append_iff]

/-! ### flatten -/

@[simp] theorem flatten_empty : (#[] : Array (Array α)).flatten = #[] := by simp [flatten]; rfl

@[simp] theorem toList_flatten {l : Array (Array α)} :
    l.flatten.toList = (l.toList.map toList).flatten := by
  dsimp [flatten]
  simp only [← foldl_toList]
  generalize l.toList = l
  have : ∀ a : Array α, (List.foldl ?_ a l).toList = a.toList ++ ?_ := ?_
  exact this #[]
  induction l with
  | nil => simp
  | cons h => induction h.toList <;> simp [*]

@[simp] theorem flatten_map_toArray (l : List (List α)) :
    (l.toArray.map List.toArray).flatten = l.flatten.toArray := by
  apply ext'
  simp [Function.comp_def]

@[simp] theorem flatten_toArray_map (l : List (List α)) :
    (l.map List.toArray).toArray.flatten = l.flatten.toArray := by
  rw [← flatten_map_toArray]
  simp

theorem flatten_toArray (l : List (Array α)) :
    l.toArray.flatten = (l.map Array.toList).flatten.toArray := by
  apply ext'
  simp

@[simp] theorem size_flatten (L : Array (Array α)) : L.flatten.size = (L.map size).sum := by
  cases L using array₂_induction
  simp [Function.comp_def]

@[simp] theorem flatten_singleton (l : Array α) : #[l].flatten = l := by simp [flatten]; rfl

theorem mem_flatten : ∀ {L : Array (Array α)}, a ∈ L.flatten ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  simp only [mem_def, toList_flatten, List.mem_flatten, List.mem_map]
  intro l
  constructor
  · rintro ⟨_, ⟨s, m, rfl⟩, h⟩
    exact ⟨s, m, h⟩
  · rintro ⟨s, h₁, h₂⟩
    refine ⟨s.toList, ⟨⟨s, h₁, rfl⟩, h₂⟩⟩

@[simp] theorem flatten_eq_empty_iff {L : Array (Array α)} : L.flatten = #[] ↔ ∀ l ∈ L, l = #[] := by
  induction L using array₂_induction
  simp

@[simp] theorem empty_eq_flatten_iff {L : Array (Array α)} : #[] = L.flatten ↔ ∀ l ∈ L, l = #[] := by
  rw [eq_comm, flatten_eq_empty_iff]

theorem flatten_ne_empty_iff {xs : Array (Array α)} : xs.flatten ≠ #[] ↔ ∃ x, x ∈ xs ∧ x ≠ #[] := by
  simp

theorem exists_of_mem_flatten : a ∈ flatten L → ∃ l, l ∈ L ∧ a ∈ l := mem_flatten.1

theorem mem_flatten_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ flatten L := mem_flatten.2 ⟨l, lL, al⟩

theorem forall_mem_flatten {p : α → Prop} {L : Array (Array α)} :
    (∀ (x) (_ : x ∈ flatten L), p x) ↔ ∀ (l) (_ : l ∈ L) (x) (_ : x ∈ l), p x := by
  simp only [mem_flatten, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatten_eq_flatMap {L : Array (Array α)} : flatten L = L.flatMap id := by
  induction L using array₂_induction
  rw [flatten_toArray_map, List.flatten_eq_flatMap]
  simp [List.flatMap_map]

@[simp] theorem map_flatten (f : α → β) (L : Array (Array α)) :
    (flatten L).map f = (map (map f) L).flatten := by
  induction L using array₂_induction with
  | of xss =>
    simp only [flatten_toArray_map, List.map_toArray, List.map_flatten, List.map_map,
      Function.comp_def]
    rw [← Function.comp_def, ← List.map_map, flatten_toArray_map]

@[simp] theorem filterMap_flatten (f : α → Option β) (L : Array (Array α)) :
    filterMap f (flatten L) = flatten (map (filterMap f) L) := by
  induction L using array₂_induction
  simp only [flatten_toArray_map, size_toArray, List.length_flatten, List.filterMap_toArray',
    List.filterMap_flatten, List.map_toArray, List.map_map, Function.comp_def]
  rw [← Function.comp_def, ← List.map_map, flatten_toArray_map]

@[simp] theorem filter_flatten (p : α → Bool) (L : Array (Array α)) :
    filter p (flatten L) = flatten (map (filter p) L) := by
  induction L using array₂_induction
  simp only [flatten_toArray_map, size_toArray, List.length_flatten, List.filter_toArray',
    List.filter_flatten, List.map_toArray, List.map_map, Function.comp_def]
  rw [← Function.comp_def, ← List.map_map, flatten_toArray_map]

theorem flatten_filter_not_isEmpty {L : Array (Array α)} :
    flatten (L.filter fun l => !l.isEmpty) = L.flatten := by
  induction L using array₂_induction
  simp [List.filter_map, Function.comp_def, List.flatten_filter_not_isEmpty]

theorem flatten_filter_ne_empty [DecidablePred fun l : Array α => l ≠ #[]] {L : Array (Array α)} :
    flatten (L.filter fun l => l ≠ #[]) = L.flatten := by
  simp only [ne_eq, ← isEmpty_iff, Bool.not_eq_true, Bool.decide_eq_false,
    flatten_filter_not_isEmpty]

@[simp] theorem flatten_append (L₁ L₂ : Array (Array α)) :
    flatten (L₁ ++ L₂) = flatten L₁ ++ flatten L₂ := by
  induction L₁ using array₂_induction
  induction L₂ using array₂_induction
  simp [← List.map_append]

theorem flatten_push (L : Array (Array α)) (l : Array α) :
    flatten (L.push l) = flatten L ++ l := by
  induction L using array₂_induction
  rcases l with ⟨l⟩
  have this : [l.toArray] = [l].map List.toArray := by simp
  simp only [List.push_toArray, flatten_toArray_map, List.append_toArray]
  rw [this, ← List.map_append, flatten_toArray_map]
  simp

theorem flatten_flatten {L : Array (Array (Array α))} : flatten (flatten L) = flatten (map flatten L) := by
  induction L using array₃_induction with
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

theorem flatten_eq_push_iff {xs : Array (Array α)} {ys : Array α} {y : α} :
    xs.flatten = ys.push y ↔
      ∃ (as : Array (Array α)) (bs : Array α) (cs : Array (Array α)),
        xs = as.push (bs.push y) ++ cs ∧ (∀ l, l ∈ cs → l = #[]) ∧ ys = as.flatten ++ bs := by
  induction xs using array₂_induction with
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

theorem push_eq_flatten_iff {xs : Array (Array α)} {ys : Array α} {y : α} :
    ys.push y = xs.flatten ↔
      ∃ (as : Array (Array α)) (bs : Array α) (cs : Array (Array α)),
        xs = as.push (bs.push y) ++ cs ∧ (∀ l, l ∈ cs → l = #[]) ∧ ys = as.flatten ++ bs := by
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
theorem eq_iff_flatten_eq {L L' : Array (Array α)} :
    L = L' ↔ L.flatten = L'.flatten ∧ map size L = map size L' := by
  cases L using array₂_induction with
  | of L =>
    cases L' using array₂_induction with
    | of L' =>
      simp [Function.comp_def, ← List.eq_iff_flatten_eq]
      rw [List.map_inj_right]
      simp +contextual

/-! ### flatMap -/

theorem flatMap_def (l : Array α) (f : α → Array β) : l.flatMap f = flatten (map f l) := by
  rcases l with ⟨l⟩
  simp [flatten_toArray, Function.comp_def, List.flatMap_def]

theorem flatMap_toList (l : Array α) (f : α → List β) :
    l.toList.flatMap f = (l.flatMap (fun a => (f a).toArray)).toList := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem toList_flatMap (l : Array α) (f : α → Array β) :
    (l.flatMap f).toList = l.toList.flatMap fun a => (f a).toList := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem flatMap_id (l : Array (Array α)) : l.flatMap id = l.flatten := by simp [flatMap_def]

@[simp] theorem flatMap_id' (l : Array (Array α)) : l.flatMap (fun a => a) = l.flatten := by simp [flatMap_def]

@[simp]
theorem size_flatMap (l : Array α) (f : α → Array β) :
    (l.flatMap f).size = sum (map (fun a => (f a).size) l) := by
  rcases l with ⟨l⟩
  simp [Function.comp_def]

@[simp] theorem mem_flatMap {f : α → Array β} {b} {l : Array α} : b ∈ l.flatMap f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [flatMap_def, mem_flatten]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_flatMap {b : β} {l : Array α} {f : α → Array β} :
    b ∈ l.flatMap f → ∃ a, a ∈ l ∧ b ∈ f a := mem_flatMap.1

theorem mem_flatMap_of_mem {b : β} {l : Array α} {f : α → Array β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ l.flatMap f := mem_flatMap.2 ⟨a, al, h⟩

@[simp]
theorem flatMap_eq_empty_iff {l : Array α} {f : α → Array β} : l.flatMap f = #[] ↔ ∀ x ∈ l, f x = #[] := by
  rw [flatMap_def, flatten_eq_empty_iff]
  simp

theorem forall_mem_flatMap {p : β → Prop} {l : Array α} {f : α → Array β} :
    (∀ (x) (_ : x ∈ l.flatMap f), p x) ↔ ∀ (a) (_ : a ∈ l) (b) (_ : b ∈ f a), p b := by
  simp only [mem_flatMap, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatMap_singleton (f : α → Array β) (x : α) : #[x].flatMap f = f x := by
  simp

@[simp] theorem flatMap_singleton' (l : Array α) : (l.flatMap fun x => #[x]) = l := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem flatMap_append (xs ys : Array α) (f : α → Array β) :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp

theorem flatMap_assoc {α β} (l : Array α) (f : α → Array β) (g : β → Array γ) :
    (l.flatMap f).flatMap g = l.flatMap fun x => (f x).flatMap g := by
  rcases l with ⟨l⟩
  simp [List.flatMap_assoc, ← toList_flatMap]

theorem map_flatMap (f : β → γ) (g : α → Array β) (l : Array α) :
     (l.flatMap g).map f = l.flatMap fun a => (g a).map f := by
  rcases l with ⟨l⟩
  simp [List.map_flatMap]

theorem flatMap_map (f : α → β) (g : β → Array γ) (l : Array α) :
    (map f l).flatMap g = l.flatMap (fun a => g (f a)) := by
  rcases l with ⟨l⟩
  simp [List.flatMap_map]

theorem map_eq_flatMap {α β} (f : α → β) (l : Array α) : map f l = l.flatMap fun x => #[f x] := by
  simp only [← map_singleton]
  rw [← flatMap_singleton' l, map_flatMap, flatMap_singleton']

theorem filterMap_flatMap {β γ} (l : Array α) (g : α → Array β) (f : β → Option γ) :
    (l.flatMap g).filterMap f = l.flatMap fun a => (g a).filterMap f := by
  rcases l with ⟨l⟩
  simp [List.filterMap_flatMap]

theorem filter_flatMap (l : Array α) (g : α → Array β) (f : β → Bool) :
    (l.flatMap g).filter f = l.flatMap fun a => (g a).filter f := by
  rcases l with ⟨l⟩
  simp [List.filter_flatMap]

theorem flatMap_eq_foldl (f : α → Array β) (l : Array α) :
    l.flatMap f = l.foldl (fun acc a => acc ++ f a) #[] := by
  rcases l with ⟨l⟩
  simp only [List.flatMap_toArray, List.flatMap_eq_foldl, size_toArray, List.foldl_toArray']
  suffices ∀ l', (List.foldl (fun acc a => acc ++ (f a).toList) l' l).toArray =
      List.foldl (fun acc a => acc ++ f a) l'.toArray l by
    simpa using this []
  induction l with
  | nil => simp
  | cons a l ih =>
    intro l'
    simp [ih ((l' ++ (f a).toList)), toArray_append]

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

@[simp] theorem getElem?_mkArray_of_lt {n : Nat} {m : Nat} (h : m < n) : (mkArray n a)[m]? = some a := by
  simp [getElem?_mkArray, h]

@[simp] theorem mkArray_inj : mkArray n a = mkArray m b ↔ n = m ∧ (n = 0 ∨ a = b) := by
  rw [← toList_inj]
  simp

theorem eq_mkArray_of_mem {a : α} {l : Array α} (h : ∀ (b) (_ : b ∈ l), b = a) : l = mkArray l.size a := by
  rw [← toList_inj]
  simpa using List.eq_replicate_of_mem (by simpa using h)

theorem eq_mkArray_iff {a : α} {n} {l : Array α} :
    l = mkArray n a ↔ l.size = n ∧ ∀ (b) (_ : b ∈ l), b = a := by
  rw [← toList_inj]
  simpa using List.eq_replicate_iff (l := l.toList)

theorem map_eq_mkArray_iff {l : Array α} {f : α → β} {b : β} :
    l.map f = mkArray l.size b ↔ ∀ x ∈ l, f x = b := by
  simp [eq_mkArray_iff]

@[simp] theorem map_const (l : Array α) (b : β) : map (Function.const α b) l = mkArray l.size b :=
  map_eq_mkArray_iff.mpr fun _ _ => rfl

@[simp] theorem map_const_fun (x : β) : map (Function.const α x) = (mkArray ·.size x) := by
  funext l
  simp

/-- Variant of `map_const` using a lambda rather than `Function.const`. -/
-- This can not be a `@[simp]` lemma because it would fire on every `List.map`.
theorem map_const' (l : Array α) (b : β) : map (fun _ => b) l = mkArray l.size b :=
  map_const l b

@[simp] theorem set_mkArray_self : (mkArray n a).set i a h = mkArray n a := by
  apply Array.ext'
  simp

@[simp] theorem setIfInBounds_mkArray_self : (mkArray n a).setIfInBounds i a = mkArray n a := by
  apply Array.ext'
  simp

@[simp] theorem mkArray_append_mkArray : mkArray n a ++ mkArray m a = mkArray (n + m) a := by
  apply Array.ext'
  simp

theorem append_eq_mkArray_iff {l₁ l₂ : Array α} {a : α} :
    l₁ ++ l₂ = mkArray n a ↔
      l₁.size + l₂.size = n ∧ l₁ = mkArray l₁.size a ∧ l₂ = mkArray l₂.size a := by
  simp [← toList_inj, List.append_eq_replicate_iff]

theorem mkArray_eq_append_iff {l₁ l₂ : Array α} {a : α} :
    mkArray n a = l₁ ++ l₂ ↔
      l₁.size + l₂.size = n ∧ l₁ = mkArray l₁.size a ∧ l₂ = mkArray l₂.size a := by
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

theorem swap_def (a : Array α) (i j : Nat) (hi hj) :
    a.swap i j hi hj = (a.set i a[j]).set j a[i] (by simpa using hj) := by
  simp [swap]

theorem getElem?_swap (a : Array α) (i j : Nat) (hi hj) (k : Nat) : (a.swap i j hi hj)[k]? =
    if j = k then some a[i] else if i = k then some a[j] else a[k]? := by
  simp [swap_def, getElem?_set]

/-! ### reverse -/

@[simp] theorem size_reverse (a : Array α) : a.reverse.size = a.size := by
  let rec go (as : Array α) (i j) : (reverse.loop as i j).size = as.size := by
    rw [reverse.loop]
    if h : i < j then
      simp [(go · (i+1) ⟨j-1, ·⟩), h]
    else simp [h]
    termination_by j - i
  simp only [reverse]; split <;> simp [go]

@[simp] theorem toList_reverse (a : Array α) : a.reverse.toList = a.toList.reverse := by
  let rec go (as : Array α) (i j hj)
      (h : i + j + 1 = a.size) (h₂ : as.size = a.size)
      (H : ∀ k, as.toList[k]? = if i ≤ k ∧ k ≤ j then a.toList[k]? else a.toList.reverse[k]?)
      (k : Nat) : (reverse.loop as i ⟨j, hj⟩).toList[k]? = a.toList.reverse[k]? := by
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
          exact (List.getElem?_reverse' (j+1) i (Eq.trans (by simp_arith) h)).symm
        split <;> rename_i h₃
        · simp only [← h₃, Nat.not_le.2 (Nat.lt_succ_self _), Nat.le_refl, false_and]
          exact (List.getElem?_reverse' i (j+1) (Eq.trans (by simp_arith) h)).symm
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
  · match a with | ⟨[]⟩ | ⟨[_]⟩ => rfl
  · have := Nat.sub_add_cancel (Nat.le_of_not_le ‹_›)
    refine List.ext_getElem? <| go _ _ _ _ (by simp [this]) rfl fun k => ?_
    split
    · rfl
    · rename_i h
      simp only [← show k < _ + 1 ↔ _ from Nat.lt_succ (n := a.size - 1), this, Nat.zero_le,
        true_and, Nat.not_lt] at h
      rw [List.getElem?_eq_none_iff.2 ‹_›, List.getElem?_eq_none_iff.2 (a.toList.length_reverse ▸ ‹_›)]

@[simp] theorem _root_.List.reverse_toArray (l : List α) : l.toArray.reverse = l.reverse.toArray := by
  apply ext'
  simp only [toList_reverse]

@[simp] theorem reverse_push (as : Array α) (a : α) : (as.push a).reverse = #[a] ++ as.reverse := by
  cases as
  simp

@[simp] theorem mem_reverse {x : α} {as : Array α} : x ∈ as.reverse ↔ x ∈ as := by
  cases as
  simp

@[simp] theorem getElem_reverse (as : Array α) (i : Nat) (hi : i < as.reverse.size) :
    (as.reverse)[i] = as[as.size - 1 - i]'(by simp at hi; omega) := by
  cases as
  simp

@[simp] theorem reverse_eq_empty_iff {xs : Array α} : xs.reverse = #[] ↔ xs = #[] := by
  cases xs
  simp

theorem reverse_ne_empty_iff {xs : Array α} : xs.reverse ≠ #[] ↔ xs ≠ #[] :=
  not_congr reverse_eq_empty_iff

/-- Variant of `getElem?_reverse` with a hypothesis giving the linear relation between the indices. -/
theorem getElem?_reverse' {l : Array α} (i j) (h : i + j + 1 = l.size) : l.reverse[i]? = l[j]? := by
  rcases l with ⟨l⟩
  simp at h
  simp only [List.reverse_toArray, List.getElem?_toArray]
  rw [List.getElem?_reverse' (l := l) _ _ h]

@[simp]
theorem getElem?_reverse {l : Array α} {i} (h : i < l.size) :
    l.reverse[i]? = l[l.size - 1 - i]? := by
  cases l
  simp_all

@[simp] theorem reverse_reverse (as : Array α) : as.reverse.reverse = as := by
  cases as
  simp

theorem reverse_eq_iff {as bs : Array α} : as.reverse = bs ↔ as = bs.reverse := by
  constructor <;> (rintro rfl; simp)

@[simp] theorem reverse_inj {xs ys : Array α} : xs.reverse = ys.reverse ↔ xs = ys := by
  simp [reverse_eq_iff]

@[simp] theorem reverse_eq_push_iff {xs : Array α} {ys : Array α} {a : α} :
    xs.reverse = ys.push a ↔ xs = #[a] ++ ys.reverse := by
  rw [reverse_eq_iff, reverse_push]

@[simp] theorem map_reverse (f : α → β) (l : Array α) : l.reverse.map f = (l.map f).reverse := by
  cases l <;> simp [*]

@[simp] theorem filter_reverse (p : α → Bool) (l : Array α) : (l.reverse.filter p) = (l.filter p).reverse := by
  cases l
  simp

@[simp] theorem filterMap_reverse (f : α → Option β) (l : Array α) : (l.reverse.filterMap f) = (l.filterMap f).reverse := by
  cases l
  simp

@[simp] theorem reverse_append (as bs : Array α) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  cases as
  cases bs
  simp

@[simp] theorem reverse_eq_append_iff {xs ys zs : Array α} :
    xs.reverse = ys ++ zs ↔ xs = zs.reverse ++ ys.reverse := by
  cases xs
  cases ys
  cases zs
  simp

/-- Reversing a flatten is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_flatten (L : Array (Array α)) :
    L.flatten.reverse = (L.map reverse).reverse.flatten := by
  cases L using array₂_induction
  simp [flatten_toArray, List.reverse_flatten, Function.comp_def]

/-- Flattening a reverse is the same as reversing all parts and reversing the flattened result. -/
theorem flatten_reverse (L : Array (Array α)) :
    L.reverse.flatten = (L.map reverse).flatten.reverse := by
  cases L using array₂_induction
  simp [flatten_toArray, List.flatten_reverse, Function.comp_def]

theorem reverse_flatMap {β} (l : Array α) (f : α → Array β) :
    (l.flatMap f).reverse = l.reverse.flatMap (reverse ∘ f) := by
  cases l
  simp [List.reverse_flatMap, Function.comp_def]

theorem flatMap_reverse {β} (l : Array α) (f : α → Array β) :
    (l.reverse.flatMap f) = (l.flatMap (reverse ∘ f)).reverse := by
  cases l
  simp [List.flatMap_reverse, Function.comp_def]

@[simp] theorem reverse_mkArray (n) (a : α) : reverse (mkArray n a) = mkArray n a := by
  rw [← toList_inj]
  simp

/-! ### extract -/

theorem extract_loop_zero (as bs : Array α) (start : Nat) : extract.loop as 0 start bs = bs := by
  rw [extract.loop]; split <;> rfl

theorem extract_loop_succ (as bs : Array α) (size start : Nat) (h : start < as.size) :
    extract.loop as (size+1) start bs = extract.loop as size (start+1) (bs.push as[start]) := by
  rw [extract.loop, dif_pos h]; rfl

theorem extract_loop_of_ge (as bs : Array α) (size start : Nat) (h : start ≥ as.size) :
    extract.loop as size start bs = bs := by
  rw [extract.loop, dif_neg (Nat.not_lt_of_ge h)]

theorem extract_loop_eq_aux (as bs : Array α) (size start : Nat) :
    extract.loop as size start bs = bs ++ extract.loop as size start #[] := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, extract_loop_zero, append_empty]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih (bs.push _), push_eq_append_singleton]
      rw [extract_loop_succ (h:=h), ih (#[].push _), push_eq_append_singleton, empty_append]
      rw [append_assoc]
    else
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [append_empty]

theorem extract_loop_eq (as bs : Array α) (size start : Nat) (h : start + size ≤ as.size) :
  extract.loop as size start bs = bs ++ as.extract start (start + size) := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [extract_loop_eq_aux, Nat.min_eq_left h, Nat.add_sub_cancel_left]

theorem size_extract_loop (as bs : Array α) (size start : Nat) :
    (extract.loop as size start bs).size = bs.size + min size (as.size - start) := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, Nat.zero_min, Nat.add_zero]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih, size_push, Nat.add_assoc, ←Nat.add_min_add_left,
        Nat.sub_succ, Nat.one_add, Nat.one_add, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
    else
      have h := Nat.le_of_not_gt h
      rw [extract_loop_of_ge (h:=h), Nat.sub_eq_zero_of_le h, Nat.min_zero, Nat.add_zero]

@[simp] theorem size_extract (as : Array α) (start stop : Nat) :
    (as.extract start stop).size = min stop as.size - start := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [size_extract_loop, size_empty, Nat.zero_add, Nat.sub_min_sub_right, Nat.min_assoc,
    Nat.min_self]

theorem getElem_extract_loop_lt_aux (as bs : Array α) (size start : Nat) (hlt : i < bs.size) :
    i < (extract.loop as size start bs).size := by
  rw [size_extract_loop]
  apply Nat.lt_of_lt_of_le hlt
  exact Nat.le_add_right ..

theorem getElem_extract_loop_lt (as bs : Array α) (size start : Nat) (hlt : i < bs.size)
    (h := getElem_extract_loop_lt_aux as bs size start hlt) :
    (extract.loop as size start bs)[i] = bs[i] := by
  apply Eq.trans _ (getElem_append_left (bs:=extract.loop as size start #[]) hlt)
  · rw [size_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)
  · congr; rw [extract_loop_eq_aux]

theorem getElem_extract_loop_ge_aux (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size) : start + i - bs.size < as.size := by
  have h : i < bs.size + (as.size - start) := by
      apply Nat.lt_of_lt_of_le h
      rw [size_extract_loop]
      apply Nat.add_le_add_left
      exact Nat.min_le_right ..
  rw [Nat.add_sub_assoc hge]
  apply Nat.add_lt_of_lt_sub'
  exact Nat.sub_lt_left_of_lt_add hge h

theorem getElem_extract_loop_ge (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size)
    (h' := getElem_extract_loop_ge_aux as bs size start hge h) :
    (extract.loop as size start bs)[i] = as[start + i - bs.size] := by
  induction size using Nat.recAux generalizing start bs with
  | zero =>
    rw [size_extract_loop, Nat.zero_min, Nat.add_zero] at h
    omega
  | succ size ih =>
    have : start < as.size := by
      apply Nat.lt_of_le_of_lt (Nat.le_add_right start (i - bs.size))
      rwa [← Nat.add_sub_assoc hge]
    have : i < (extract.loop as size (start+1) (bs.push as[start])).size := by
      rwa [← extract_loop_succ]
    have heq : (extract.loop as (size+1) start bs)[i] =
        (extract.loop as size (start+1) (bs.push as[start]))[i] := by
      congr 1; rw [extract_loop_succ]
    rw [heq]
    if hi : bs.size = i then
      cases hi
      have h₁ : bs.size < (bs.push as[start]).size := by rw [size_push]; exact Nat.lt_succ_self ..
      have h₂ : bs.size < (extract.loop as size (start+1) (bs.push as[start])).size := by
        rw [size_extract_loop]; apply Nat.lt_of_lt_of_le h₁; exact Nat.le_add_right ..
      have h : (extract.loop as size (start + 1) (push bs as[start]))[bs.size] = as[start] := by
        rw [getElem_extract_loop_lt as (bs.push as[start]) size (start+1) h₁ h₂, getElem_push_eq]
      rw [h]; congr; rw [Nat.add_sub_cancel]
    else
      have hge : bs.size + 1 ≤ i := Nat.lt_of_le_of_ne hge hi
      rw [ih (bs.push as[start]) (start+1) ((size_push ..).symm ▸ hge)]
      congr 1; rw [size_push, Nat.add_right_comm, Nat.add_sub_add_right]

theorem getElem_extract_aux {as : Array α} {start stop : Nat} (h : i < (as.extract start stop).size) :
    start + i < as.size := by
  rw [size_extract] at h; apply Nat.add_lt_of_lt_sub'; apply Nat.lt_of_lt_of_le h
  apply Nat.sub_le_sub_right; apply Nat.min_le_right

@[simp] theorem getElem_extract {as : Array α} {start stop : Nat}
    (h : i < (as.extract start stop).size) :
    (as.extract start stop)[i] = as[start + i]'(getElem_extract_aux h) :=
  show (extract.loop as (min stop as.size - start) start #[])[i]
    = as[start + i]'(getElem_extract_aux h) by rw [getElem_extract_loop_ge]; rfl; exact Nat.zero_le _

theorem getElem?_extract {as : Array α} {start stop : Nat} :
    (as.extract start stop)[i]? = if i < min stop as.size - start then as[start + i]? else none := by
  simp only [getElem?_def, size_extract, getElem_extract]
  split
  · split
    · rfl
    · omega
  · rfl

@[simp] theorem toList_extract (as : Array α) (start stop : Nat) :
    (as.extract start stop).toList = (as.toList.drop start).take (stop - start) := by
  apply List.ext_getElem
  · simp only [length_toList, size_extract, List.length_take, List.length_drop]
    omega
  · intros n h₁ h₂
    simp

@[simp] theorem extract_size (as : Array α) : as.extract 0 as.size = as := by
  apply ext
  · rw [size_extract, Nat.min_self, Nat.sub_zero]
  · intros; rw [getElem_extract]; congr; rw [Nat.zero_add]

@[deprecated extract_size (since := "2025-01-19")]
abbrev extract_all := @extract_size

theorem extract_empty_of_stop_le_start (as : Array α) {start stop : Nat} (h : stop ≤ start) :
    as.extract start stop = #[] := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.zero_min, extract_loop_zero]

theorem extract_empty_of_size_le_start (as : Array α) {start stop : Nat} (h : as.size ≤ start) :
    as.extract start stop = #[] := by
  simp only [extract, Nat.sub_eq, mkEmpty_eq]
  rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.min_zero, extract_loop_zero]

@[simp] theorem extract_empty (start stop : Nat) : (#[] : Array α).extract start stop = #[] :=
  extract_empty_of_size_le_start _ (Nat.zero_le _)

@[simp] theorem _root_.List.extract_toArray (l : List α) (start stop : Nat) :
    l.toArray.extract start stop = ((l.drop start).take (stop - start)).toArray := by
  apply ext'
  simp

/-! ### foldlM and foldrM -/

theorem foldlM_start_stop {m} [Monad m] (l : Array α) (f : β → α → m β) (b) (start stop : Nat) :
    l.foldlM f b start stop = (l.extract start stop).foldlM f b := by
  unfold foldlM
  simp only [Nat.sub_zero, size_extract, Nat.le_refl, ↓reduceDIte]
  suffices foldlM.loop f l (min stop l.size) (by omega) (min stop l.size - start) start b =
      foldlM.loop f (l.extract start stop) (min stop l.size - start) (by simp) (min stop l.size - start) 0 b by
    split
    · have : min stop l.size = stop := by omega
      simp_all
    · have : min stop l.size = l.size := by omega
      simp_all
  revert b
  suffices ∀ (b : β) (i k) (w : i + k = min stop l.size - start),
    foldlM.loop f l (min stop l.size) (by omega) i (start + k) b =
      foldlM.loop f (l.extract start stop) (min stop l.size - start) (by simp) i k b by
    intro b
    simpa using this b (min stop l.size - start) 0 (by omega)
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

theorem foldrM_start_stop {m} [Monad m] (l : Array α) (f : α → β → m β) (b) (start stop : Nat) :
    l.foldrM f b start stop = (l.extract stop start).foldrM f b := by
  unfold foldrM
  simp only [size_extract, Nat.le_refl, ↓reduceDIte]
  suffices stop ≤ min start l.size →
      foldrM.fold f l stop (min start l.size) (by omega) b =
        foldrM.fold f (l.extract stop start) 0 (min start l.size - stop) (by simp) b by
    split
    · split
      · rw [if_pos (by omega)]
        have h : min start l.size = start := by omega
        specialize this (by omega)
        simp_all
      · rw [if_neg (by omega)]
    · split
      · rw [if_pos (by omega)]
        have h : min start l.size = l.size := by omega
        specialize this (by omega)
        simp_all
      · rw [if_neg (by omega)]
  revert b
  suffices ∀ (b : β) (i) (w : stop + i ≤ min start l.size),
      foldrM.fold f l stop (stop + i) (by omega) b =
        foldrM.fold f (l.extract stop start) 0 i (by simp; omega) b by
    intro b w
    specialize this b (min start l.size - stop)
    have h : stop + (min start l.size - stop) = min start l.size := by omega
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

@[congr] theorem foldlM_congr {m} [Monad m] {f g : β → α → m β} {b : β} {l l' : Array α}
    (w : l = l')
    (h : ∀ x y, f x y = g x y) (hstart : start = start') (hstop : stop = stop') :
    l.foldlM f b start stop = l'.foldlM g b start' stop' := by
  subst hstart hstop w
  rcases l with ⟨l⟩
  rw [foldlM_start_stop, List.extract_toArray]
  simp only [size_toArray, List.length_take, List.length_drop, List.foldlM_toArray']
  rw [foldlM_start_stop, List.extract_toArray]
  simp only [size_toArray, List.length_take, List.length_drop, List.foldlM_toArray']
  congr
  funext b a
  simp_all

@[congr] theorem foldrM_congr {m} [Monad m] {f g : α → β → m β} {b : β} {l l' : Array α}
    (w : l = l')
    (h : ∀ x y, f x y = g x y) (hstart : start = start') (hstop : stop = stop') :
    l.foldrM f b start stop = l'.foldrM g b start' stop' := by
  subst hstart hstop w
  rcases l with ⟨l⟩
  rw [foldrM_start_stop, List.extract_toArray]
  simp only [size_toArray, List.length_take, List.length_drop, List.foldrM_toArray']
  rw [foldrM_start_stop, List.extract_toArray]
  simp only [size_toArray, List.length_take, List.length_drop, List.foldrM_toArray']
  congr
  funext b a
  simp_all

/-- Variant of `foldlM_append` with a side condition for the `stop` argument. -/
@[simp] theorem foldlM_append' [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (l l' : Array α)
    (w : stop = l.size + l'.size) :
    (l ++ l').foldlM f b 0 stop = l.foldlM f b >>= l'.foldlM f := by
  subst w
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp

theorem foldlM_append [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (l l' : Array α) :
    (l ++ l').foldlM f b = l.foldlM f b >>= l'.foldlM f := by
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
@[simp] theorem foldlM_push' [Monad m] [LawfulMonad m] (l : Array α) (a : α) (f : β → α → m β) (b)
    (w : stop = l.size + 1) :
    (l.push a).foldlM f b 0 stop = l.foldlM f b >>= fun b => f b a := by
  subst w
  simp [← append_singleton]

theorem foldlM_push [Monad m] [LawfulMonad m] (l : Array α) (a : α) (f : β → α → m β) (b) :
    (l.push a).foldlM f b = l.foldlM f b >>= fun b => f b a := by
  simp

theorem foldl_eq_foldlM (f : β → α → β) (b) (l : Array α) :
    l.foldl f b start stop = l.foldlM (m := Id) f b start stop := by
  simp [foldl, Id.run]

theorem foldr_eq_foldrM (f : α → β → β) (b) (l : Array α) :
    l.foldr f b start stop = l.foldrM (m := Id) f b start stop := by
  simp [foldr, Id.run]

@[simp] theorem id_run_foldlM (f : β → α → Id β) (b) (l : Array α) :
    Id.run (l.foldlM f b start stop) = l.foldl f b start stop := (foldl_eq_foldlM f b l).symm

@[simp] theorem id_run_foldrM (f : α → β → Id β) (b) (l : Array α) :
    Id.run (l.foldrM f b start stop) = l.foldr f b start stop := (foldr_eq_foldrM f b l).symm

/-- Variant of `foldlM_reverse` with a side condition for the `stop` argument. -/
@[simp] theorem foldlM_reverse' [Monad m] (l : Array α) (f : β → α → m β) (b)
    (w : stop = l.size) :
    l.reverse.foldlM f b 0 stop = l.foldrM (fun x y => f y x) b := by
  subst w
  rcases l with ⟨l⟩
  simp [List.foldlM_reverse]

/-- Variant of `foldrM_reverse` with a side condition for the `start` argument. -/
@[simp] theorem foldrM_reverse' [Monad m] (l : Array α) (f : α → β → m β) (b)
    (w : start = l.size) :
    l.reverse.foldrM f b start 0 = l.foldlM (fun x y => f y x) b := by
  subst w
  rcases l with ⟨l⟩
  simp [List.foldrM_reverse]

theorem foldlM_reverse [Monad m] (l : Array α) (f : β → α → m β) (b) :
    l.reverse.foldlM f b = l.foldrM (fun x y => f y x) b := by
  simp

theorem foldrM_reverse [Monad m] (l : Array α) (f : α → β → m β) (b) :
    l.reverse.foldrM f b = l.foldlM (fun x y => f y x) b := by
  rcases l with ⟨l⟩
  simp

theorem foldrM_push [Monad m] (f : α → β → m β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldrM f init = f a init >>= arr.foldrM f := by
  simp only [foldrM_eq_reverse_foldlM_toList, push_toList, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.foldlM_cons, List.foldlM_reverse]

/--
Variant of `foldrM_push` with `h : start = arr.size + 1`
rather than `(arr.push a).size` as the argument.
-/
@[simp] theorem foldrM_push' [Monad m] (f : α → β → m β) (init : β) (arr : Array α) (a : α)
    {start} (h : start = arr.size + 1) :
    (arr.push a).foldrM f init start = f a init >>= arr.foldrM f := by
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

theorem foldr_push (f : α → β → β) (init : β) (arr : Array α) (a : α) :
    (arr.push a).foldr f init = arr.foldr f (f a init) := foldrM_push ..

/--
Variant of `foldr_push` with the `h : start = arr.size + 1`
rather than `(arr.push a).size` as the argument.
-/
@[simp] theorem foldr_push' (f : α → β → β) (init : β) (arr : Array α) (a : α) {start}
    (h : start = arr.size + 1) : (arr.push a).foldr f init start = arr.foldr f (f a init) :=
  foldrM_push' _ _ _ _ h

@[simp] theorem foldl_push_eq_append (l l' : Array α) : l.foldl push l' = l' ++ l := by
  cases l
  cases l'
  simp

@[simp] theorem foldr_flip_push_eq_append (l l' : Array α) :
    l.foldr (fun x y => push y x) l' = l' ++ l.reverse := by
  cases l
  cases l'
  simp

theorem foldl_map' (f : β₁ → β₂) (g : α → β₂ → α) (l : Array β₁) (init : α) (w : stop = l.size) :
    (l.map f).foldl g init 0 stop = l.foldl (fun x y => g x (f y)) init := by
  subst w
  cases l; simp [List.foldl_map]

theorem foldr_map' (f : α₁ → α₂) (g : α₂ → β → β) (l : Array α₁) (init : β) (w : start = l.size) :
    (l.map f).foldr g init start 0 = l.foldr (fun x y => g (f x) y) init := by
  subst w
  cases l; simp [List.foldr_map]

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (l : Array β₁) (init : α) :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  cases l; simp [List.foldl_map]

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (l : Array α₁) (init : β) :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  cases l; simp [List.foldr_map]

theorem foldl_filterMap' (f : α → Option β) (g : γ → β → γ) (l : Array α) (init : γ)
    (w : stop = (l.filterMap f).size) :
    (l.filterMap f).foldl g init 0 stop = l.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  subst w
  cases l
  simp [List.foldl_filterMap]
  rfl

theorem foldr_filterMap' (f : α → Option β) (g : β → γ → γ) (l : Array α) (init : γ)
    (w : start = (l.filterMap f).size) :
    (l.filterMap f).foldr g init start 0 = l.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  subst w
  cases l
  simp [List.foldr_filterMap]
  rfl

theorem foldl_filterMap (f : α → Option β) (g : γ → β → γ) (l : Array α) (init : γ) :
    (l.filterMap f).foldl g init = l.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  simp [foldl_filterMap']

theorem foldr_filterMap (f : α → Option β) (g : β → γ → γ) (l : Array α) (init : γ) :
    (l.filterMap f).foldr g init = l.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  simp [foldr_filterMap']

theorem foldl_map_hom' (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) (w : stop = l.size) :
    (l.map g).foldl f' (g a) 0 stop = g (l.foldl f a) := by
  subst w
  cases l
  simp
  rw [List.foldl_map_hom _ _ _ _ _ h]

theorem foldr_map_hom' (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) (w : start = l.size) :
    (l.map g).foldr f' (g a) start 0 = g (l.foldr f a) := by
  subst w
  cases l
  simp
  rw [List.foldr_map_hom _ _ _ _ _ h]

theorem foldl_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldl f' (g a) = g (l.foldl f a) := by
  cases l
  simp
  rw [List.foldl_map_hom _ _ _ _ _ h]

theorem foldr_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : Array α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldr f' (g a) = g (l.foldr f a) := by
  cases l
  simp
  rw [List.foldr_map_hom _ _ _ _ _ h]

/-- Variant of `foldrM_append` with a side condition for the `start` argument. -/
@[simp] theorem foldrM_append' [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l l' : Array α)
    (w : start = l.size + l'.size) :
    (l ++ l').foldrM f b start 0 = l'.foldrM f b >>= l.foldrM f := by
  subst w
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp

theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l l' : Array α) :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  simp

@[simp] theorem foldl_append' {β : Type _} (f : β → α → β) (b) (l l' : Array α)
    (w : stop = l.size + l'.size) :
    (l ++ l').foldl f b 0 stop = l'.foldl f (l.foldl f b) := by
  subst w
  simp [foldl_eq_foldlM]

@[simp] theorem foldr_append' (f : α → β → β) (b) (l l' : Array α)
    (w : start = l.size + l'.size) :
    (l ++ l').foldr f b start 0 = l.foldr f (l'.foldr f b) := by
  subst w
  simp [foldr_eq_foldrM]

theorem foldl_append {β : Type _} (f : β → α → β) (b) (l l' : Array α) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by
  simp [foldl_eq_foldlM]

theorem foldr_append (f : α → β → β) (b) (l l' : Array α) :
    (l ++ l').foldr f b = l.foldr f (l'.foldr f b) := by
  simp [foldr_eq_foldrM]

@[simp] theorem foldl_flatten' (f : β → α → β) (b : β) (L : Array (Array α))
    (w : stop = L.flatten.size) :
    (flatten L).foldl f b 0 stop = L.foldl (fun b l => l.foldl f b) b := by
  subst w
  cases L using array₂_induction
  simp [List.foldl_flatten, List.foldl_map]

@[simp] theorem foldr_flatten' (f : α → β → β) (b : β) (L : Array (Array α))
    (w : start = L.flatten.size) :
    (flatten L).foldr f b start 0 = L.foldr (fun l b => l.foldr f b) b := by
  subst w
  cases L using array₂_induction
  simp [List.foldr_flatten, List.foldr_map]

theorem foldl_flatten (f : β → α → β) (b : β) (L : Array (Array α)) :
    (flatten L).foldl f b = L.foldl (fun b l => l.foldl f b) b := by
  cases L using array₂_induction
  simp [List.foldl_flatten, List.foldl_map]

theorem foldr_flatten (f : α → β → β) (b : β) (L : Array (Array α)) :
    (flatten L).foldr f b = L.foldr (fun l b => l.foldr f b) b := by
  cases L using array₂_induction
  simp [List.foldr_flatten, List.foldr_map]

/-- Variant of `foldl_reverse` with a side condition for the `stop` argument. -/
@[simp] theorem foldl_reverse' (l : Array α) (f : β → α → β) (b) (w : stop = l.size) :
    l.reverse.foldl f b 0 stop = l.foldr (fun x y => f y x) b := by
  simp [w, foldl_eq_foldlM, foldr_eq_foldrM]

/-- Variant of `foldr_reverse` with a side condition for the `start` argument. -/
@[simp] theorem foldr_reverse' (l : Array α) (f : α → β → β) (b) (w : start = l.size) :
    l.reverse.foldr f b start 0 = l.foldl (fun x y => f y x) b := by
  simp [w, foldl_eq_foldlM, foldr_eq_foldrM]

theorem foldl_reverse (l : Array α) (f : β → α → β) (b) :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

theorem foldr_reverse (l : Array α) (f : α → β → β) (b) :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

theorem foldl_eq_foldr_reverse (l : Array α) (f : β → α → β) (b) :
    l.foldl f b = l.reverse.foldr (fun x y => f y x) b := by simp

theorem foldr_eq_foldl_reverse (l : Array α) (f : α → β → β) (b) :
    l.foldr f b = l.reverse.foldl (fun x y => f y x) b := by simp

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {l : Array α} {a₁ a₂} :
     l.foldl op (op a₁ a₂) = op a₁ (l.foldl op a₂) := by
  rcases l with ⟨l⟩
  simp [List.foldl_assoc]

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {l : Array α} {a₁ a₂} :
    l.foldr op (op a₁ a₂) = op (l.foldr op a₁) a₂ := by
  rcases l with ⟨l⟩
  simp [List.foldr_assoc]

theorem foldl_hom (f : α₁ → α₂) (g₁ : α₁ → β → α₁) (g₂ : α₂ → β → α₂) (l : Array β) (init : α₁)
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : l.foldl g₂ (f init) = f (l.foldl g₁ init) := by
  cases l
  simp
  rw [List.foldl_hom _ _ _ _ _ H]

theorem foldr_hom (f : β₁ → β₂) (g₁ : α → β₁ → β₁) (g₂ : α → β₂ → β₂) (l : Array α) (init : β₁)
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : l.foldr g₂ (f init) = f (l.foldr g₁ init) := by
  cases l
  simp
  rw [List.foldr_hom _ _ _ _ _ H]

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldl_rel {l : Array α} {f g : β → α → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f c a) (g c' a)) :
    r (l.foldl (fun acc a => f acc a) a) (l.foldl (fun acc a => g acc a) b) := by
  rcases l with ⟨l⟩
  simpa using List.foldl_rel r h (by simpa using h')

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldr_rel {l : Array α} {f g : α → β → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f a c) (g a c')) :
    r (l.foldr (fun a acc => f a acc) a) (l.foldr (fun a acc => g a acc) b) := by
  rcases l with ⟨l⟩
  simpa using List.foldr_rel r h (by simpa using h')

@[simp] theorem foldl_add_const (l : Array α) (a b : Nat) :
    l.foldl (fun x _ => x + a) b = b + a * l.size := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem foldr_add_const (l : Array α) (a b : Nat) :
    l.foldr (fun _ x => x + a) b = b + a * l.size := by
  rcases l with ⟨l⟩
  simp

/-! Content below this point has not yet been aligned with `List`. -/

/-! ### sum -/

theorem sum_eq_sum_toList [Add α] [Zero α] (as : Array α) : as.toList.sum = as.sum := by
  cases as
  simp [Array.sum, List.sum]

-- This is a duplicate of `List.toArray_toList`.
-- It's confusing to guess which namespace this theorem should live in,
-- so we provide both.
@[simp] theorem toArray_toList (a : Array α) : a.toList.toArray = a := rfl

@[deprecated size_toArray (since := "2024-12-11")]
theorem size_mk (as : List α) : (Array.mk as).size = as.length := by simp [size]

/-- A more efficient version of `arr.toList.reverse`. -/
@[inline] def toListRev (arr : Array α) : List α := arr.foldl (fun l t => t :: l) []

@[simp] theorem toListRev_eq (arr : Array α) : arr.toListRev = arr.toList.reverse := by
  rw [toListRev, ← foldl_toList, ← List.foldr_reverse, List.foldr_cons_nil]

@[simp] theorem appendList_nil (arr : Array α) : arr ++ ([] : List α) = arr := Array.ext' (by simp)

@[simp] theorem appendList_cons (arr : Array α) (a : α) (l : List α) :
    arr ++ (a :: l) = arr.push a ++ l := Array.ext' (by simp)

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

theorem size_uset (a : Array α) (v i h) : (uset a i v h).size = a.size := by simp

/-! # get -/

@[deprecated getElem?_eq_getElem (since := "2024-12-11")]
theorem getElem?_lt
    (a : Array α) {i : Nat} (h : i < a.size) : a[i]? = some a[i] := dif_pos h

@[deprecated getElem?_eq_none (since := "2024-12-11")]
theorem getElem?_ge
    (a : Array α) {i : Nat} (h : i ≥ a.size) : a[i]? = none := dif_neg (Nat.not_lt_of_le h)

@[simp] theorem get?_eq_getElem? (a : Array α) (i : Nat) : a.get? i = a[i]? := rfl

@[deprecated getElem?_eq_none (since := "2024-12-11")]
theorem getElem?_len_le (a : Array α) {i : Nat} (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_eq_none, h]

@[deprecated getD_getElem? (since := "2024-12-11")] abbrev getD_get? := @getD_getElem?

@[simp] theorem getD_eq_get? (a : Array α) (i d) : a.getD i d = (a[i]?).getD d := by
  simp only [getD, get_eq_getElem, get?_eq_getElem?]; split <;> simp [getD_getElem?, *]

theorem get!_eq_getD [Inhabited α] (a : Array α) : a.get! n = a.getD n default := rfl

theorem get!_eq_getElem? [Inhabited α] (a : Array α) (i : Nat) :
    a.get! i = (a.get? i).getD default := by
  by_cases p : i < a.size <;>
  simp only [get!_eq_getD, getD_eq_get?, getD_getElem?, p, get?_eq_getElem?]

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

@[simp] theorem mem_toList {a : α} {l : Array α} : a ∈ l.toList ↔ a ∈ l := mem_def.symm

theorem not_mem_nil (a : α) : ¬ a ∈ #[] := nofun

/-! # get lemmas -/

theorem lt_of_getElem {x : α} {a : Array α} {idx : Nat} {hidx : idx < a.size} (_ : a[idx] = x) :
    idx < a.size :=
  hidx

theorem getElem_fin_eq_getElem_toList (a : Array α) (i : Fin a.size) : a[i] = a.toList[i] := rfl

@[simp] theorem ugetElem_eq_getElem (a : Array α) {i : USize} (h : i.toNat < a.size) :
  a[i] = a[i.toNat] := rfl

theorem getElem?_size_le (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_neg, h]

@[deprecated getElem?_size_le (since := "2024-10-21")] abbrev get?_len_le := @getElem?_size_le

theorem getElem_mem_toList (a : Array α) (h : i < a.size) : a[i] ∈ a.toList := by
  simp only [← getElem_toList, List.getElem_mem]

theorem get?_eq_get?_toList (a : Array α) (i : Nat) : a.get? i = a.toList.get? i := by
  simp [← getElem?_toList]

theorem get!_eq_get? [Inhabited α] (a : Array α) : a.get! n = (a.get? n).getD default := by
  simp only [get!_eq_getElem?, get?_eq_getElem?]

theorem back!_eq_back? [Inhabited α] (a : Array α) : a.back! = a.back?.getD default := by
  simp [back!, back?, getElem!_def, Option.getD]; rfl

@[simp] theorem back?_push (a : Array α) : (a.push x).back? = some x := by
  simp [back?, ← getElem?_toList]

@[simp] theorem back!_push [Inhabited α] (a : Array α) : (a.push x).back! = x := by
  simp [back!_eq_back?]

theorem mem_of_back? {xs : Array α} {a : α} (h : xs.back? = some a) : a ∈ xs := by
  cases xs
  simpa using List.mem_of_getLast? (by simpa using h)

@[deprecated mem_of_back? (since := "2024-10-21")] abbrev mem_of_back?_eq_some := @mem_of_back?

theorem getElem?_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]? = some a[i] := by
  rw [getElem?_pos, getElem_push_lt]

@[deprecated getElem?_push_lt (since := "2024-10-21")] abbrev get?_push_lt := @getElem?_push_lt

theorem getElem?_push_eq (a : Array α) (x : α) : (a.push x)[a.size]? = some x := by
  rw [getElem?_pos, getElem_push_eq]

@[deprecated getElem?_push_eq (since := "2024-10-21")] abbrev get?_push_eq := @getElem?_push_eq

@[deprecated getElem?_push (since := "2024-10-21")] abbrev get?_push := @getElem?_push

@[simp] theorem getElem?_size {a : Array α} : a[a.size]? = none := by
  simp only [getElem?_def, Nat.lt_irrefl, dite_false]

@[deprecated getElem?_size (since := "2024-10-21")] abbrev get?_size := @getElem?_size

@[deprecated getElem_set_self (since := "2025-01-17")]
theorem get_set_eq (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (a.set i v h)[i]'(by simp [h]) = v := by
  simp only [set, ← getElem_toList, List.getElem_set_self]

theorem get?_set_eq (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (a.set i v)[i]? = v := by simp [getElem?_pos, h]

@[simp] theorem get?_set_ne (a : Array α) (i : Nat) (h' : i < a.size) {j : Nat} (v : α)
    (h : i ≠ j) : (a.set i v)[j]? = a[j]? := by
  by_cases j < a.size <;> simp [getElem?_pos, getElem?_neg, *]

theorem get?_set (a : Array α) (i : Nat) (h : i < a.size) (j : Nat) (v : α) :
    (a.set i v)[j]? = if i = j then some v else a[j]? := by
  if h : i = j then subst j; simp [*] else simp [*]

theorem get_set (a : Array α) (i : Nat) (hi : i < a.size) (j : Nat) (hj : j < a.size) (v : α) :
    (a.set i v)[j]'(by simp [*]) = if i = j then v else a[j] := by
  if h : i = j then subst j; simp [*] else simp [*]

@[simp] theorem get_set_ne (a : Array α) (i : Nat) (hi : i < a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  simp only [set, ← getElem_toList, List.getElem_set_ne h]

@[simp] theorem toList_swap (a : Array α) (i j : Nat) (hi hj) :
    (a.swap i j hi hj).toList = (a.toList.set i a[j]).set j a[i] := by simp [swap_def]

@[simp] theorem swapAt_def (a : Array α) (i : Nat) (v : α) (hi) :
    a.swapAt i v hi = (a[i], a.set i v) := rfl

theorem size_swapAt (a : Array α) (i : Nat) (v : α) (hi) :
    (a.swapAt i v hi).2.size = a.size := by simp

@[simp]
theorem swapAt!_def (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    a.swapAt! i v = (a[i], a.set i v) := by simp [swapAt!, h]

@[simp] theorem size_swapAt! (a : Array α) (i : Nat) (v : α) :
    (a.swapAt! i v).2.size = a.size := by
  simp only [swapAt!]
  split
  · simp
  · rfl

@[simp] theorem toList_pop (a : Array α) : a.pop.toList = a.toList.dropLast := by simp [pop]

@[simp] theorem pop_empty : (#[] : Array α).pop = #[] := rfl

@[simp] theorem pop_push (a : Array α) : (a.push x).pop = a := by simp [pop]

@[simp] theorem getElem_pop (a : Array α) (i : Nat) (hi : i < a.pop.size) :
    a.pop[i] = a[i]'(Nat.lt_of_lt_of_le (a.size_pop ▸ hi) (Nat.sub_le _ _)) :=
  List.getElem_dropLast ..

theorem eq_push_pop_back!_of_size_ne_zero [Inhabited α] {as : Array α} (h : as.size ≠ 0) :
    as = as.pop.push as.back! := by
  apply ext
  · simp [Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero h)]
  · intros i h h'
    if hlt : i < as.pop.size then
      rw [getElem_push_lt (h:=hlt), getElem_pop]
    else
      have heq : i = as.pop.size :=
        Nat.le_antisymm (size_pop .. ▸ Nat.le_pred_of_lt h) (Nat.le_of_not_gt hlt)
      cases heq
      rw [getElem_push_eq, back!]
      simp [← getElem!_pos]

theorem eq_push_of_size_ne_zero {as : Array α} (h : as.size ≠ 0) :
    ∃ (bs : Array α) (c : α), as = bs.push c :=
  let _ : Inhabited α := ⟨as[0]⟩
  ⟨as.pop, as.back!, eq_push_pop_back!_of_size_ne_zero h⟩

theorem size_eq_length_toList (as : Array α) : as.size = as.toList.length := rfl

@[simp] theorem size_swapIfInBounds (a : Array α) (i j) :
    (a.swapIfInBounds i j).size = a.size := by unfold swapIfInBounds; split <;> (try split) <;> simp [size_swap]

@[deprecated size_swapIfInBounds (since := "2024-11-24")] abbrev size_swap! := @size_swapIfInBounds

@[simp] theorem size_range {n : Nat} : (range n).size = n := by
  induction n <;> simp [range]

@[simp] theorem toList_range (n : Nat) : (range n).toList = List.range n := by
  apply List.ext_getElem <;> simp [range]

@[simp]
theorem getElem_range {n : Nat} {x : Nat} (h : x < (Array.range n).size) : (Array.range n)[x] = x := by
  simp [← getElem_toList]




/-! ### take -/

@[simp] theorem size_take_loop (a : Array α) (n : Nat) : (take.loop n a).size = a.size - n := by
  induction n generalizing a with
  | zero => simp [take.loop]
  | succ n ih =>
    simp [take.loop, ih]
    omega

@[simp] theorem getElem_take_loop (a : Array α) (n : Nat) (i : Nat) (h : i < (take.loop n a).size) :
    (take.loop n a)[i] = a[i]'(by simp at h; omega) := by
  induction n generalizing a i with
  | zero => simp [take.loop]
  | succ n ih =>
    simp [take.loop, ih]

@[simp] theorem size_take (a : Array α) (n : Nat) : (a.take n).size = min n a.size  := by
  simp [take]
  omega

@[simp] theorem getElem_take (a : Array α) (n : Nat) (i : Nat) (h : i < (a.take n).size) :
    (a.take n)[i] = a[i]'(by simp at h; omega) := by
  simp [take]

@[simp] theorem toList_take (a : Array α) (n : Nat) : (a.take n).toList = a.toList.take n := by
  apply List.ext_getElem <;> simp

/-! ### forIn -/

@[simp] theorem forIn_toList [Monad m] (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as.toList b f = forIn as b f := by
  cases as
  simp

@[simp] theorem forIn'_toList [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as.toList → β → m (ForInStep β)) :
    forIn' as.toList b f = forIn' as b (fun a m b => f a (mem_toList.mpr m) b) := by
  cases as
  simp

/-! ### map -/

@[deprecated "Use `toList_map` or `List.map_toArray` to characterize `Array.map`." (since := "2025-01-06")]
theorem map_induction (as : Array α) (f : α → β) (motive : Nat → Prop) (h0 : motive 0)
    (p : Fin as.size → β → Prop) (hs : ∀ i, motive i.1 → p i (f as[i]) ∧ motive (i+1)) :
    motive as.size ∧
      ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]) := by
  have t := foldl_induction (as := as) (β := Array β)
    (motive := fun i arr => motive i ∧ arr.size = i ∧ ∀ i h2, p i arr[i.1])
    (init := #[]) (f := fun r a => r.push (f a)) ?_ ?_
  obtain ⟨m, eq, w⟩ := t
  · refine ⟨m, by simpa [map_eq_foldl] using eq, ?_⟩
    intro i h
    simp only [eq] at w
    specialize w ⟨i, h⟩ h
    simpa [map_eq_foldl] using w
  · exact ⟨h0, rfl, nofun⟩
  · intro i b ⟨m, ⟨eq, w⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (hs _ m).2
    · simp_all
    · intro j h
      simp at h ⊢
      by_cases h' : j < size b
      · rw [getElem_push]
        simp_all
      · rw [getElem_push, dif_neg h']
        simp only [show j = i by omega]
        exact (hs _ m).1

set_option linter.deprecated false in
@[deprecated "Use `toList_map` or `List.map_toArray` to characterize `Array.map`." (since := "2025-01-06")]
theorem map_spec (as : Array α) (f : α → β) (p : Fin as.size → β → Prop)
    (hs : ∀ i, p i (f as[i])) :
    ∃ eq : (as.map f).size = as.size, ∀ i h, p ⟨i, h⟩ ((as.map f)[i]) := by
  simpa using map_induction as f (fun _ => True) trivial p (by simp_all)

/-! ### modify -/

@[simp] theorem size_modify (a : Array α) (i : Nat) (f : α → α) : (a.modify i f).size = a.size := by
  unfold modify modifyM Id.run
  split <;> simp

theorem getElem_modify {as : Array α} {x i} (h : i < (as.modify x f).size) :
    (as.modify x f)[i] = if x = i then f (as[i]'(by simpa using h)) else as[i]'(by simpa using h) := by
  simp only [modify, modifyM, get_eq_getElem, Id.run, Id.pure_eq]
  split
  · simp only [Id.bind_eq, get_set _ _ _ _ (by simpa using h)]; split <;> simp [*]
  · rw [if_neg (mt (by rintro rfl; exact h) (by simp_all))]

@[simp] theorem toList_modify (as : Array α) (f : α → α) :
    (as.modify x f).toList = as.toList.modify f x := by
  apply List.ext_getElem
  · simp
  · simp [getElem_modify, List.getElem_modify]

theorem getElem_modify_self {as : Array α} {i : Nat} (f : α → α) (h : i < (as.modify i f).size) :
    (as.modify i f)[i] = f (as[i]'(by simpa using h)) := by
  simp [getElem_modify h]

theorem getElem_modify_of_ne {as : Array α} {i : Nat} (h : i ≠ j)
    (f : α → α) (hj : j < (as.modify i f).size) :
    (as.modify i f)[j] = as[j]'(by simpa using hj) := by
  simp [getElem_modify hj, h]

theorem getElem?_modify {as : Array α} {i : Nat} {f : α → α} {j : Nat} :
    (as.modify i f)[j]? = if i = j then as[j]?.map f else as[j]? := by
  simp only [getElem?_def, size_modify, getElem_modify, Option.map_dif]
  split <;> split <;> rfl

/-! ### contains -/

theorem contains_def [DecidableEq α] {a : α} {as : Array α} : as.contains a ↔ a ∈ as := by
  rw [mem_def, contains, ← any_toList, List.any_eq_true]; simp [and_comm]

instance [DecidableEq α] (a : α) (as : Array α) : Decidable (a ∈ as) :=
  decidable_of_iff _ contains_def

/-! ### swap -/

@[simp] theorem getElem_swap_right (a : Array α) {i j : Nat} {hi hj} :
    (a.swap i j hi hj)[j]'(by simpa using hj) = a[i] := by
  simp [swap_def, getElem_set]

@[simp] theorem getElem_swap_left (a : Array α) {i j : Nat} {hi hj} :
    (a.swap i j hi hj)[i]'(by simpa using hi) = a[j] := by
  simp +contextual [swap_def, getElem_set]

@[simp] theorem getElem_swap_of_ne (a : Array α) {i j : Nat} {hi hj} (hp : p < a.size)
    (hi' : p ≠ i) (hj' : p ≠ j) : (a.swap i j hi hj)[p]'(a.size_swap .. |>.symm ▸ hp) = a[p] := by
  simp [swap_def, getElem_set, hi'.symm, hj'.symm]

theorem getElem_swap' (a : Array α) (i j : Nat) {hi hj} (k : Nat) (hk : k < a.size) :
    (a.swap i j hi hj)[k]'(by simp_all) = if k = i then a[j] else if k = j then a[i] else a[k] := by
  split
  · simp_all only [getElem_swap_left]
  · split <;> simp_all

theorem getElem_swap (a : Array α) (i j : Nat) {hi hj} (k : Nat) (hk : k < (a.swap i j).size) :
    (a.swap i j hi hj)[k] = if k = i then a[j] else if k = j then a[i] else a[k]'(by simp_all) := by
  apply getElem_swap'

@[simp] theorem swap_swap (a : Array α) {i j : Nat} (hi hj) :
    (a.swap i j hi hj).swap i j ((a.size_swap ..).symm ▸ hi) ((a.size_swap ..).symm ▸ hj) = a := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [getElem_swap]
    split
    · simp_all
    · split <;> simp_all

theorem swap_comm (a : Array α) {i j : Nat} {hi hj} : a.swap i j hi hj = a.swap j i hj hi := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [getElem_swap]
    split
    · split <;> simp_all
    · split <;> simp_all

/-! ### eraseIdx -/

theorem eraseIdx_eq_eraseIdxIfInBounds {a : Array α} {i : Nat} (h : i < a.size) :
    a.eraseIdx i h = a.eraseIdxIfInBounds i := by
  simp [eraseIdxIfInBounds, h]

/-! ### isPrefixOf -/

@[simp] theorem isPrefixOf_toList [BEq α] {as bs : Array α} :
    as.toList.isPrefixOf bs.toList = as.isPrefixOf bs := by
  cases as
  cases bs
  simp

/-! ### zipWith -/

@[simp] theorem toList_zipWith (f : α → β → γ) (as : Array α) (bs : Array β) :
    (Array.zipWith as bs f).toList = List.zipWith f as.toList bs.toList := by
  cases as
  cases bs
  simp

@[simp] theorem toList_zip (as : Array α) (bs : Array β) :
    (Array.zip as bs).toList = List.zip as.toList bs.toList := by
  simp [zip, toList_zipWith, List.zip]

@[simp] theorem toList_zipWithAll (f : Option α → Option β → γ) (as : Array α) (bs : Array β) :
    (Array.zipWithAll as bs f).toList = List.zipWithAll f as.toList bs.toList := by
  cases as
  cases bs
  simp

@[simp] theorem size_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size := by
  rw [size_eq_length_toList, toList_zipWith, List.length_zipWith]

@[simp] theorem size_zip (as : Array α) (bs : Array β) :
    (as.zip bs).size = min as.size bs.size :=
  as.size_zipWith bs Prod.mk

@[simp] theorem getElem_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) (i : Nat)
    (hi : i < (as.zipWith bs f).size) :
    (as.zipWith bs f)[i] = f (as[i]'(by simp at hi; omega)) (bs[i]'(by simp at hi; omega)) := by
  cases as
  cases bs
  simp

/-! ### findSomeM?, findM?, findSome?, find? -/

@[simp] theorem findSomeM?_toList [Monad m] [LawfulMonad m] (p : α → m (Option β)) (as : Array α) :
    as.toList.findSomeM? p = as.findSomeM? p := by
  cases as
  simp

@[simp] theorem findM?_toList [Monad m] [LawfulMonad m] (p : α → m Bool) (as : Array α) :
    as.toList.findM? p = as.findM? p := by
  cases as
  simp

@[simp] theorem findSome?_toList (p : α → Option β) (as : Array α) :
    as.toList.findSome? p = as.findSome? p := by
  cases as
  simp

@[simp] theorem find?_toList (p : α → Bool) (as : Array α) :
    as.toList.find? p = as.find? p := by
  cases as
  simp

end Array

open Array

namespace List

/-!
### More theorems about `List.toArray`, followed by an `Array` operation.

Our goal is to have `simp` "pull `List.toArray` outwards" as much as possible.
-/

theorem toListRev_toArray (l : List α) : l.toArray.toListRev = l.reverse := by simp

@[simp] theorem take_toArray (l : List α) (n : Nat) : l.toArray.take n = (l.take n).toArray := by
  apply Array.ext <;> simp

@[simp] theorem mapM_toArray [Monad m] [LawfulMonad m] (f : α → m β) (l : List α) :
    l.toArray.mapM f = List.toArray <$> l.mapM f := by
  simp only [← mapM'_eq_mapM, mapM_eq_foldlM]
  suffices ∀ init : Array β,
      foldlM (fun bs a => bs.push <$> f a) init l.toArray = (init ++ toArray ·) <$> mapM' f l by
    simpa using this #[]
  intro init
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [foldlM_toArray] at ih
    rw [size_toArray, mapM'_cons, foldlM_toArray]
    simp [ih]

theorem uset_toArray (l : List α) (i : USize) (a : α) (h : i.toNat < l.toArray.size) :
    l.toArray.uset i a h = (l.set i.toNat a).toArray := by simp

@[simp] theorem swap_toArray (l : List α) (i j : Nat) {hi hj}:
    l.toArray.swap i j hi hj = ((l.set i l[j]).set j l[i]).toArray := by
  apply ext'
  simp

@[simp] theorem modify_toArray (f : α → α) (l : List α) :
    l.toArray.modify i f = (l.modify f i).toArray := by
  apply ext'
  simp

@[simp] theorem flatten_toArray (l : List (List α)) :
    (l.toArray.map List.toArray).flatten = l.flatten.toArray := by
  apply ext'
  simp [Function.comp_def]

@[simp] theorem toArray_range (n : Nat) : (range n).toArray = Array.range n := by
  apply ext'
  simp

@[simp] theorem toArray_ofFn (f : Fin n → α) : (ofFn f).toArray = Array.ofFn f := by
  ext <;> simp

@[simp] theorem eraseIdx_toArray (l : List α) (i : Nat) (h : i < l.toArray.size) :
    l.toArray.eraseIdx i h = (l.eraseIdx i).toArray := by
  rw [Array.eraseIdx]
  split <;> rename_i h'
  · rw [eraseIdx_toArray]
    simp only [swap_toArray, Fin.getElem_fin, toList_toArray, mk.injEq]
    rw [eraseIdx_set_gt (by simp), eraseIdx_set_eq]
    simp
  · simp at h h'
    have t : i = l.length - 1 := by omega
    simp [t]
termination_by l.length - i
decreasing_by
  rename_i h
  simp at h
  simp
  omega

@[simp] theorem eraseIdxIfInBounds_toArray (l : List α) (i : Nat) :
    l.toArray.eraseIdxIfInBounds i = (l.eraseIdx i).toArray := by
  rw [Array.eraseIdxIfInBounds]
  split
  · simp
  · simp_all [eraseIdx_eq_self.2]

end List

namespace Array

@[simp] theorem mapM_id {l : Array α} {f : α → Id β} : l.mapM f = l.map f := by
  induction l; simp_all

@[simp] theorem toList_ofFn (f : Fin n → α) : (Array.ofFn f).toList = List.ofFn f := by
  apply List.ext_getElem <;> simp

@[simp] theorem toList_takeWhile (p : α → Bool) (as : Array α) :
    (as.takeWhile p).toList = as.toList.takeWhile p := by
  induction as; simp

@[simp] theorem toList_eraseIdx (as : Array α) (i : Nat) (h : i < as.size) :
    (as.eraseIdx i h).toList = as.toList.eraseIdx i := by
  induction as
  simp

@[simp] theorem toList_eraseIdxIfInBounds (as : Array α) (i : Nat) :
    (as.eraseIdxIfInBounds i).toList = as.toList.eraseIdx i := by
  induction as
  simp

/-! ### flatten -/

@[simp] theorem flatten_toArray_map_toArray (xss : List (List α)) :
    (xss.map List.toArray).toArray.flatten = xss.flatten.toArray := by
  simp [flatten]
  suffices ∀ as, List.foldl (fun r a => r ++ a) as (List.map List.toArray xss) = as ++ xss.flatten.toArray by
    simpa using this #[]
  intro as
  induction xss generalizing as with
  | nil => simp
  | cons xs xss ih => simp [ih]

/-! ### findSomeRevM?, findRevM?, findSomeRev?, findRev? -/

@[simp] theorem findSomeRevM?_eq_findSomeM?_reverse
    [Monad m] [LawfulMonad m] (f : α → m (Option β)) (as : Array α) :
    as.findSomeRevM? f = as.reverse.findSomeM? f := by
  cases as
  rw [List.findSomeRevM?_toArray]
  simp

@[simp] theorem findRevM?_eq_findM?_reverse
    [Monad m] [LawfulMonad m] (f : α → m Bool) (as : Array α) :
    as.findRevM? f = as.reverse.findM? f := by
  cases as
  rw [List.findRevM?_toArray]
  simp

@[simp] theorem findSomeRev?_eq_findSome?_reverse (f : α → Option β) (as : Array α) :
    as.findSomeRev? f = as.reverse.findSome? f := by
  cases as
  simp [findSomeRev?, Id.run]

@[simp] theorem findRev?_eq_find?_reverse (f : α → Bool) (as : Array α) :
    as.findRev? f = as.reverse.find? f := by
  cases as
  simp [findRev?, Id.run]

/-! ### unzip -/

@[simp] theorem fst_unzip (as : Array (α × β)) : (Array.unzip as).fst = as.map Prod.fst := by
  simp only [unzip]
  rcases as with ⟨as⟩
  simp only [List.foldl_toArray']
  rw [← List.foldl_hom (f := Prod.fst) (g₂ := fun bs x => bs.push x.1) (H := by simp), ← List.foldl_map]
  simp

@[simp] theorem snd_unzip (as : Array (α × β)) : (Array.unzip as).snd = as.map Prod.snd := by
  simp only [unzip]
  rcases as with ⟨as⟩
  simp only [List.foldl_toArray']
  rw [← List.foldl_hom (f := Prod.snd) (g₂ := fun bs x => bs.push x.2) (H := by simp), ← List.foldl_map]
  simp

/-! ### take -/

@[simp] theorem take_size (a : Array α) : a.take a.size = a := by
  cases a
  simp

/-! ### countP and count -/

@[simp] theorem _root_.List.countP_toArray (l : List α) : countP p l.toArray = l.countP p := by
  simp [countP]
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldr_cons, ih, List.countP_cons]
    split <;> simp_all

@[simp] theorem countP_toList (as : Array α) : as.toList.countP p = countP p as := by
  cases as
  simp

@[simp] theorem _root_.List.count_toArray [BEq α] (l : List α) (a : α) : count a l.toArray = l.count a := by
  simp [count, List.count_eq_countP]

@[simp] theorem count_toList [BEq α] (as : Array α) (a : α) : as.toList.count a = as.count a := by
  cases as
  simp

end Array

namespace List

@[simp] theorem unzip_toArray (as : List (α × β)) :
    as.toArray.unzip = Prod.map List.toArray List.toArray as.unzip := by
  ext1 <;> simp

end List

namespace Array

theorem toList_fst_unzip (as : Array (α × β)) :
    as.unzip.1.toList = as.toList.unzip.1 := by simp

theorem toList_snd_unzip (as : Array (α × β)) :
    as.unzip.2.toList = as.toList.unzip.2 := by simp

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

@[deprecated back!_toArray (since := "2024-10-31")] abbrev back_toArray := @back!_toArray

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

@[deprecated get?_eq_get?_toList (since := "2024-10-17")]
abbrev get?_eq_toList_get? := @get?_eq_get?_toList

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
theorem getElem_eq_getElem_toList {a : Array α} (h : i < a.size) : a[i] = a.toList[i] := rfl

@[deprecated Array.getElem?_toList (since := "2024-12-08")]
theorem getElem?_eq_getElem?_toList (a : Array α) (i : Nat) : a[i]? = a.toList[i]? := by
  rw [getElem?_def]
  split <;> simp_all

@[deprecated LawfulGetElem.getElem?_def (since := "2024-12-08")]
theorem getElem?_eq {a : Array α} {i : Nat} :
    a[i]? = if h : i < a.size then some a[i] else none := by
  rw [getElem?_def]

end Array
