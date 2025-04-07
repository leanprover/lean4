/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison, Jannis Limperg
-/
prelude
import Init.Data.List.Lemmas
import Init.Data.List.Sublist
import Init.Data.List.Range
import Init.Data.Fin.Lemmas

/-!
Lemmas about `List.findSome?`, `List.find?`, `List.findIdx`, `List.findIdx?`, `List.idxOf`,
and `List.lookup`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.


namespace List

open Nat

/-! ### findSome? -/

@[simp] theorem findSome?_cons_of_isSome {l} (h : (f a).isSome) : findSome? f (a :: l) = f a := by
  simp only [findSome?]
  split <;> simp_all

@[simp] theorem findSome?_cons_of_isNone {l} (h : (f a).isNone) : findSome? f (a :: l) = findSome? f l := by
  simp only [findSome?]
  split <;> simp_all

theorem exists_of_findSome?_eq_some {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all

@[simp] theorem findSome?_eq_none_iff : findSome? p l = none ↔ ∀ x ∈ l, p x = none := by
  induction l <;> simp [findSome?_cons]; split <;> simp [*]

@[deprecated findSome?_eq_none_iff (since := "2024-09-05")] abbrev findSome?_eq_none := @findSome?_eq_none_iff

@[simp] theorem findSome?_isSome_iff {f : α → Option β} {l : List α} :
    (l.findSome? f).isSome ↔ ∃ x, x ∈ l ∧ (f x).isSome := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [findSome?_cons]
    split <;> simp_all

theorem findSome?_eq_some_iff {f : α → Option β} {l : List α} {b : β} :
    l.findSome? f = some b ↔ ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ f a = some b ∧ ∀ x ∈ l₁, f x = none := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [findSome?_cons]
    split <;> rename_i b' h
    · simp only [Option.some.injEq, exists_and_right]
      constructor
      · rintro rfl
        exact ⟨[], p, ⟨l, rfl⟩, h, by simp⟩
      · rintro ⟨(⟨⟩ | ⟨p', l₁⟩), a, ⟨l₂, h₁⟩, h₂, h₃⟩
        · simp only [nil_append, cons.injEq] at h₁
          apply Option.some.inj
          simp [← h, ← h₂, h₁.1]
        · simp only [cons_append, cons.injEq] at h₁
          obtain ⟨rfl, rfl⟩ := h₁
          specialize h₃ p
          simp_all
    · rw [ih]
      constructor
      · rintro ⟨l₁, a, l₂, rfl, h₁, h₂⟩
        refine ⟨p :: l₁, a, l₂, rfl, h₁, ?_⟩
        intro a w
        simp at w
        rcases w with rfl | w
        · exact h
        · exact h₂ _ w
      · rintro ⟨l₁, a, l₂, h₁, h₂, h₃⟩
        rcases l₁ with (⟨⟩ | ⟨a', l₁⟩)
        · simp_all
        · simp only [cons_append, cons.injEq] at h₁
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h₁
          exact ⟨l₁, a, l₂, rfl, h₂, fun a' w => h₃ a' (mem_cons_of_mem p w)⟩

@[simp] theorem findSome?_guard {l : List α} : findSome? (Option.guard fun x => p x) l = find? p l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [guard, findSome?, find?]
    split <;> rename_i h
    · simp only [Option.guard_eq_some] at h
      obtain ⟨rfl, h⟩ := h
      simp [h]
    · simp only [Option.guard_eq_none] at h
      simp [ih, h]

theorem find?_eq_findSome?_guard {l : List α} : find? p l = findSome? (Option.guard fun x => p x) l :=
  findSome?_guard.symm

@[simp] theorem head?_filterMap {f : α → Option β} {l : List α} : (l.filterMap f).head? = l.findSome? f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [filterMap_cons, findSome?_cons]
    split <;> simp [*]

@[simp] theorem head_filterMap {f : α → Option β} {l : List α} (h) :
    (l.filterMap f).head h = (l.findSome? f).get (by simp_all [Option.isSome_iff_ne_none]) := by
  simp [head_eq_iff_head?_eq_some]

@[simp] theorem getLast?_filterMap {f : α → Option β} {l : List α} : (l.filterMap f).getLast? = l.reverse.findSome? f := by
  rw [getLast?_eq_head?_reverse]
  simp [← filterMap_reverse]

@[simp] theorem getLast_filterMap {f : α → Option β} {l : List α} (h) :
    (l.filterMap f).getLast h = (l.reverse.findSome? f).get (by simp_all [Option.isSome_iff_ne_none]) := by
  simp [getLast_eq_iff_getLast?_eq_some]

@[simp] theorem map_findSome? {f : α → Option β} {g : β → γ} {l : List α} :
    (l.findSome? f).map g = l.findSome? (Option.map g ∘ f) := by
  induction l <;> simp [findSome?_cons]; split <;> simp [*]

theorem findSome?_map {f : β → γ} {l : List β} : findSome? p (l.map f) = l.findSome? (p ∘ f) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, findSome?]
    split <;> simp_all

theorem findSome?_append {l₁ l₂ : List α} : (l₁ ++ l₂).findSome? f = (l₁.findSome? f).or (l₂.findSome? f) := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, findSome?]
    split <;> simp_all

theorem head_flatten {L : List (List α)} (h : ∃ l, l ∈ L ∧ l ≠ []) :
    (flatten L).head (by simpa using h) = (L.findSome? fun l => l.head?).get (by simpa using h) := by
  simp [head_eq_iff_head?_eq_some, head?_flatten]

theorem getLast_flatten {L : List (List α)} (h : ∃ l, l ∈ L ∧ l ≠ []) :
    (flatten L).getLast (by simpa using h) =
      (L.reverse.findSome? fun l => l.getLast?).get (by simpa using h) := by
  simp [getLast_eq_iff_getLast?_eq_some, getLast?_flatten]

theorem findSome?_replicate : findSome? f (replicate n a) = if n = 0 then none else f a := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [replicate_succ, findSome?_cons]
    split <;> simp_all

@[simp] theorem findSome?_replicate_of_pos (h : 0 < n) : findSome? f (replicate n a) = f a := by
  simp [findSome?_replicate, Nat.ne_of_gt h]

-- Argument is unused, but used to decide whether `simp` should unfold.
@[simp] theorem findSome?_replicate_of_isSome (_ : (f a).isSome) : findSome? f (replicate n a) = if n = 0 then none else f a := by
  simp [findSome?_replicate]

@[simp] theorem findSome?_replicate_of_isNone (h : (f a).isNone) : findSome? f (replicate n a) = none := by
  rw [Option.isNone_iff_eq_none] at h
  simp [findSome?_replicate, h]

theorem Sublist.findSome?_isSome {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    (l₁.findSome? f).isSome → (l₂.findSome? f).isSome := by
  induction h with
  | slnil => simp
  | cons a h ih
  | cons₂ a h ih =>
    simp only [findSome?]
    split
    · simp_all
    · exact ih

theorem Sublist.findSome?_eq_none {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    l₂.findSome? f = none → l₁.findSome? f = none := by
  simp only [List.findSome?_eq_none_iff, Bool.not_eq_true]
  exact fun w x m => w x (Sublist.mem m h)

theorem IsPrefix.findSome?_eq_some {l₁ l₂ : List α} {f : α → Option β} (h : l₁ <+: l₂) :
    List.findSome? f l₁ = some b → List.findSome? f l₂ = some b := by
  rw [IsPrefix] at h
  obtain ⟨t, rfl⟩ := h
  simp +contextual [findSome?_append]

theorem IsPrefix.findSome?_eq_none {l₁ l₂ : List α} {f : α → Option β} (h : l₁ <+: l₂) :
    List.findSome? f l₂ = none → List.findSome? f l₁ = none :=
  h.sublist.findSome?_eq_none
theorem IsSuffix.findSome?_eq_none {l₁ l₂ : List α} {f : α → Option β} (h : l₁ <:+ l₂) :
    List.findSome? f l₂ = none → List.findSome? f l₁ = none :=
  h.sublist.findSome?_eq_none
theorem IsInfix.findSome?_eq_none {l₁ l₂ : List α} {f : α → Option β} (h : l₁ <:+: l₂) :
    List.findSome? f l₂ = none → List.findSome? f l₁ = none :=
  h.sublist.findSome?_eq_none

/-! ### find? -/

@[simp] theorem find?_singleton {a : α} {p : α → Bool} : [a].find? p = if p a then some a else none := by
  simp only [find?]
  split <;> simp_all

@[simp] theorem find?_cons_of_pos {l} (h : p a) : find? p (a :: l) = some a := by
  simp [find?, h]

@[simp] theorem find?_cons_of_neg {l} (h : ¬p a) : find? p (a :: l) = find? p l := by
  simp [find?, h]

@[simp] theorem find?_eq_none : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  induction l <;> simp [find?_cons]; split <;> simp [*]

theorem find?_eq_some_iff_append :
    xs.find? p = some b ↔ p b ∧ ∃ as bs, xs = as ++ b :: bs ∧ ∀ a ∈ as, !p a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [find?_cons, exists_and_right]
    split <;> rename_i h
    · simp only [Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨h, [], ⟨xs, rfl⟩, by simp⟩
      · rintro ⟨-, ⟨as, ⟨⟨bs, h₁⟩, h₂⟩⟩⟩
        cases as with
        | nil => simp_all
        | cons a as =>
          specialize h₂ a mem_cons_self
          simp only [cons_append] at h₁
          obtain ⟨rfl, -⟩ := h₁
          simp_all
    · simp only [ih, Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, and_congr_right_iff]
      intro pb
      constructor
      · rintro ⟨as, ⟨⟨bs, rfl⟩, h₁⟩⟩
        refine ⟨x :: as, ⟨⟨bs, rfl⟩, ?_⟩⟩
        intro a m
        simp at m
        obtain (rfl|m) := m
        · exact h
        · exact h₁ a m
      · rintro ⟨as, ⟨bs, h₁⟩, h₂⟩
        cases as with
        | nil => simp_all
        | cons a as =>
          refine ⟨as, ⟨⟨bs, ?_⟩, fun a m => h₂ a (mem_cons_of_mem _ m)⟩⟩
          cases h₁
          simp

@[deprecated find?_eq_some_iff_append (since := "2024-11-06")]
abbrev find?_eq_some := @find?_eq_some_iff_append

@[simp]
theorem find?_cons_eq_some : (a :: xs).find? p = some b ↔ (p a ∧ a = b) ∨ (!p a ∧ xs.find? p = some b) := by
  rw [find?_cons]
  split <;> simp_all

@[simp] theorem find?_isSome {xs : List α} {p : α → Bool} : (xs.find? p).isSome ↔ ∃ x, x ∈ xs ∧ p x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [find?_cons, mem_cons, exists_eq_or_imp]
    split <;> simp_all

theorem find?_some : ∀ {l}, find? p l = some a → p a
  | b :: l, H => by
    by_cases h : p b <;> simp [find?, h] at H
    · exact H ▸ h
    · exact find?_some H

theorem mem_of_find?_eq_some : ∀ {l}, find? p l = some a → a ∈ l
  | b :: l, H => by
    by_cases h : p b <;> simp [find?, h] at H
    · exact H ▸ .head _
    · exact .tail _ (mem_of_find?_eq_some H)

theorem get_find?_mem {xs : List α} {p : α → Bool} (h) : (xs.find? p).get h ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [find?_cons]
    by_cases h : p x
    · simp [h]
    · simp only [h]
      right
      apply ih

@[simp] theorem find?_filter {xs : List α} {p : α → Bool} {q : α → Bool} :
    (xs.filter p).find? q = xs.find? (fun a => p a ∧ q a) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [filter_cons]
    split <;>
    · simp only [find?_cons]
      split <;> simp_all

@[simp] theorem head?_filter {p : α → Bool} {l : List α} : (l.filter p).head? = l.find? p := by
  rw [← filterMap_eq_filter, head?_filterMap, findSome?_guard]

@[simp] theorem head_filter {p : α → Bool} {l : List α} (h) :
    (l.filter p).head h = (l.find? p).get (by simp_all [Option.isSome_iff_ne_none]) := by
  simp [head_eq_iff_head?_eq_some]

@[simp] theorem getLast?_filter {p : α → Bool} {l : List α} : (l.filter p).getLast? = l.reverse.find? p := by
  rw [getLast?_eq_head?_reverse]
  simp [← filter_reverse]

@[simp] theorem getLast_filter {p : α → Bool} {l : List α} (h) :
    (l.filter p).getLast h = (l.reverse.find? p).get (by simp_all [Option.isSome_iff_ne_none]) := by
  simp [getLast_eq_iff_getLast?_eq_some]

@[simp] theorem find?_filterMap {xs : List α} {f : α → Option β} {p : β → Bool} :
    (xs.filterMap f).find? p = (xs.find? (fun a => (f a).any p)).bind f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [filterMap_cons]
    split <;>
    · simp only [find?_cons]
      split <;> simp_all

@[simp] theorem find?_map {f : β → α} {l : List β} : find? p (l.map f) = (l.find? (p ∘ f)).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, find?]
    by_cases h : p (f x) <;> simp [h, ih]

@[simp] theorem find?_append {l₁ l₂ : List α} : (l₁ ++ l₂).find? p = (l₁.find? p).or (l₂.find? p) := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, find?]
    by_cases h : p x <;> simp [h, ih]

@[simp] theorem find?_flatten {xss : List (List α)} {p : α → Bool} :
    xss.flatten.find? p = xss.findSome? (·.find? p) := by
  induction xss with
  | nil => simp
  | cons _ _ ih =>
    simp only [flatten_cons, find?_append, findSome?_cons, ih]
    split <;> simp [*]

theorem find?_flatten_eq_none_iff {xs : List (List α)} {p : α → Bool} :
    xs.flatten.find? p = none ↔ ∀ ys ∈ xs, ∀ x ∈ ys, !p x := by
  simp

@[deprecated find?_flatten_eq_none_iff (since := "2025-02-03")]
abbrev find?_flatten_eq_none := @find?_flatten_eq_none_iff

/--
If `find? p` returns `some a` from `xs.flatten`, then `p a` holds, and
some list in `xs` contains `a`, and no earlier element of that list satisfies `p`.
Moreover, no earlier list in `xs` has an element satisfying `p`.
-/
theorem find?_flatten_eq_some_iff {xs : List (List α)} {p : α → Bool} {a : α} :
    xs.flatten.find? p = some a ↔
      p a ∧ ∃ as ys zs bs, xs = as ++ (ys ++ a :: zs) :: bs ∧
        (∀ l ∈ as, ∀ x ∈ l, !p x) ∧ (∀ x ∈ ys, !p x) := by
  rw [find?_eq_some_iff_append]
  constructor
  · rintro ⟨h, ⟨ys, zs, h₁, h₂⟩⟩
    refine ⟨h, ?_⟩
    rw [flatten_eq_append_iff] at h₁
    obtain (⟨as, bs, rfl, rfl, h₁⟩ | ⟨as, bs, c, cs, ds, rfl, rfl, h₁⟩) := h₁
    · replace h₁ := h₁.symm
      rw [flatten_eq_cons_iff] at h₁
      obtain ⟨bs, cs, ds, rfl, h₁, rfl⟩ := h₁
      refine ⟨as ++ bs, [], cs, ds, by simp, ?_⟩
      simp
      rintro l (ma | mb) x m
      · simpa using h₂ x (by simpa using ⟨l, ma, m⟩)
      · specialize h₁ _ mb
        simp_all
    · simp [h₁]
      refine ⟨as, bs, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · simp_all
      · intro l ml a m
        simpa using h₂ a (by simpa using .inl ⟨l, ml, m⟩)
      · intro x m
        simpa using h₂ x (by simpa using .inr m)
  · rintro ⟨h, ⟨as, ys, zs, bs, rfl, h₁, h₂⟩⟩
    refine ⟨h, as.flatten ++ ys, zs ++ bs.flatten, by simp, ?_⟩
    intro a m
    simp at m
    obtain ⟨l, ml, m⟩ | m := m
    · exact h₁ l ml a m
    · exact h₂ a m

@[deprecated find?_flatten_eq_some_iff (since := "2025-02-03")]
abbrev find?_flatten_eq_some := @find?_flatten_eq_some_iff

@[simp] theorem find?_flatMap {xs : List α} {f : α → List β} {p : β → Bool} :
    (xs.flatMap f).find? p = xs.findSome? (fun x => (f x).find? p) := by
  simp [flatMap_def, findSome?_map]; rfl

@[deprecated find?_flatMap (since := "2024-10-16")] abbrev find?_bind := @find?_flatMap

theorem find?_flatMap_eq_none_iff {xs : List α} {f : α → List β} {p : β → Bool} :
    (xs.flatMap f).find? p = none ↔ ∀ x ∈ xs, ∀ y ∈ f x, !p y := by
  simp

@[deprecated find?_flatMap_eq_none_iff (since := "2024-10-16")]
abbrev find?_flatMap_eq_none := @find?_flatMap_eq_none_iff

@[deprecated find?_flatMap_eq_none (since := "2024-10-16")] abbrev find?_bind_eq_none := @find?_flatMap_eq_none_iff

theorem find?_replicate : find? p (replicate n a) = if n = 0 then none else if p a then some a else none := by
  cases n
  · simp
  · by_cases p a <;> simp_all [replicate_succ]

@[simp] theorem find?_replicate_of_length_pos (h : 0 < n) : find? p (replicate n a) = if p a then some a else none := by
  simp [find?_replicate, Nat.ne_of_gt h]

@[simp] theorem find?_replicate_of_pos (h : p a) : find? p (replicate n a) = if n = 0 then none else some a := by
  simp [find?_replicate, h]

@[simp] theorem find?_replicate_of_neg (h : ¬ p a) : find? p (replicate n a) = none := by
  simp [find?_replicate, h]

-- This isn't a `@[simp]` lemma since there is already a lemma for `l.find? p = none` for any `l`.
theorem find?_replicate_eq_none_iff {n : Nat} {a : α} {p : α → Bool} :
    (replicate n a).find? p = none ↔ n = 0 ∨ !p a := by
  simp [Classical.or_iff_not_imp_left]

@[deprecated find?_replicate_eq_none_iff (since := "2025-02-03")]
abbrev find?_replicate_eq_none := @find?_replicate_eq_none_iff

@[simp] theorem find?_replicate_eq_some_iff {n : Nat} {a b : α} {p : α → Bool} :
    (replicate n a).find? p = some b ↔ n ≠ 0 ∧ p a ∧ a = b := by
  cases n <;> simp

@[deprecated find?_replicate_eq_some_iff (since := "2025-02-03")]
abbrev find?_replicate_eq_some := @find?_replicate_eq_some_iff

@[simp] theorem get_find?_replicate {n : Nat} {a : α} {p : α → Bool} (h) : ((replicate n a).find? p).get h = a := by
  cases n with
  | zero => simp at h
  | succ n => simp

theorem Sublist.find?_isSome {l₁ l₂ : List α} (h : l₁ <+ l₂) : (l₁.find? p).isSome → (l₂.find? p).isSome := by
  induction h with
  | slnil => simp
  | cons a h ih
  | cons₂ a h ih =>
    simp only [find?]
    split
    · simp
    · simpa using ih

theorem Sublist.find?_eq_none {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₂.find? p = none → l₁.find? p = none := by
  simp only [List.find?_eq_none, Bool.not_eq_true]
  exact fun w x m => w x (Sublist.mem m h)

theorem IsPrefix.find?_eq_some {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <+: l₂) :
    List.find? p l₁ = some b → List.find? p l₂ = some b := by
  rw [IsPrefix] at h
  obtain ⟨t, rfl⟩ := h
  simp +contextual [find?_append]

theorem IsPrefix.find?_eq_none {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <+: l₂) :
    List.find? p l₂ = none → List.find? p l₁ = none :=
  h.sublist.find?_eq_none
theorem IsSuffix.find?_eq_none {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <:+ l₂) :
    List.find? p l₂ = none → List.find? p l₁ = none :=
  h.sublist.find?_eq_none
theorem IsInfix.find?_eq_none {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <:+: l₂) :
    List.find? p l₂ = none → List.find? p l₁ = none :=
  h.sublist.find?_eq_none

theorem find?_pmap {P : α → Prop} {f : (a : α) → P a → β} {xs : List α}
    (H : ∀ (a : α), a ∈ xs → P a) {p : β → Bool} :
    (xs.pmap f H).find? p = (xs.attach.find? (fun ⟨a, m⟩ => p (f a (H a m)))).map fun ⟨a, m⟩ => f a (H a m) := by
  simp only [pmap_eq_map_attach, find?_map]
  rfl

/-! ### findIdx? (preliminary lemmas) -/

@[local simp] private theorem findIdx?_go_nil {p : α → Bool} {i : Nat} :
    findIdx?.go p [] i = none := rfl

@[local simp] private theorem findIdx?_go_cons :
    findIdx?.go p (x :: xs) i = if p x then some i else findIdx?.go p xs (i + 1) := rfl

private theorem findIdx?_go_succ {p : α → Bool} {xs : List α} {i : Nat} :
    findIdx?.go p xs (i+1) = (findIdx?.go p xs i).map fun i => i + 1 := by
  induction xs generalizing i with simp
  | cons _ _ _ => split <;> simp_all

private theorem findIdx?_go_eq {p : α → Bool} {xs : List α} {i : Nat} :
    findIdx?.go p xs (i+1) = (findIdx?.go p xs 0).map fun k => k + (i + 1) := by
  induction xs generalizing i with
  | nil => simp
  | cons _ _ _ =>
    simp only [findIdx?_go_succ, findIdx?_go_cons, Nat.zero_add]
    split
    · simp_all
    · simp_all only [findIdx?_go_succ, Bool.not_eq_true, Option.map_map, Nat.zero_add]
      congr
      ext
      simp only [Nat.add_comm i, Function.comp_apply, Nat.add_assoc]

@[simp] theorem findIdx?_nil : ([] : List α).findIdx? p = none := rfl

@[simp] theorem findIdx?_cons :
    (x :: xs).findIdx? p = if p x then some 0 else (xs.findIdx? p).map fun i => i + 1 := by
  simp [findIdx?, findIdx?_go_eq]

/-! ### findIdx -/

theorem findIdx_cons {p : α → Bool} {b : α} {l : List α} :
    (b :: l).findIdx p = bif p b then 0 else (l.findIdx p) + 1 := by
  cases H : p b with
  | true => simp [H, findIdx, findIdx.go]
  | false => simp [H, findIdx, findIdx.go, findIdx_go_succ]
where
  findIdx_go_succ (p : α → Bool) (l : List α) (n : Nat) :
      List.findIdx.go p l (n + 1) = (findIdx.go p l n) + 1 := by
    cases l with
    | nil => unfold findIdx.go; exact Nat.succ_eq_add_one n
    | cons hd tl =>
      unfold findIdx.go
      cases p hd <;> simp only [cond_false, cond_true]
      exact findIdx_go_succ p tl (n + 1)

theorem findIdx_of_getElem?_eq_some {xs : List α} (w : xs[xs.findIdx p]? = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]

theorem findIdx_getElem {xs : List α} {w : xs.findIdx p < xs.length} :
    p xs[xs.findIdx p] :=
  xs.findIdx_of_getElem?_eq_some (getElem?_eq_getElem w)

theorem findIdx_lt_length_of_exists {xs : List α} (h : ∃ x ∈ xs, p x) :
    xs.findIdx p < xs.length := by
  induction xs with
  | nil => simp_all
  | cons x xs ih =>
    by_cases p x
    · simp_all only [forall_exists_index, and_imp, mem_cons, exists_eq_or_imp, true_or,
        findIdx_cons, cond_true, length_cons]
      apply Nat.succ_pos
    · simp_all [findIdx_cons, Nat.succ_lt_succ_iff]
      obtain ⟨x', m', h'⟩ := h
      exact ih x' m' h'

theorem findIdx_getElem?_eq_getElem_of_exists {xs : List α} (h : ∃ x ∈ xs, p x) :
    xs[xs.findIdx p]? = some (xs[xs.findIdx p]'(xs.findIdx_lt_length_of_exists h)) :=
  getElem?_eq_getElem (findIdx_lt_length_of_exists h)

@[simp]
theorem findIdx_eq_length {p : α → Bool} {xs : List α} :
    xs.findIdx p = xs.length ↔ ∀ x ∈ xs, p x = false := by
  induction xs with
  | nil => simp_all
  | cons x xs ih =>
    rw [findIdx_cons, length_cons]
    simp only [cond_eq_if]
    split <;> simp_all [Nat.succ.injEq]

theorem findIdx_eq_length_of_false {p : α → Bool} {xs : List α} (h : ∀ x ∈ xs, p x = false) :
    xs.findIdx p = xs.length := by
  rw [findIdx_eq_length]
  exact h

theorem findIdx_le_length {p : α → Bool} {xs : List α} : xs.findIdx p ≤ xs.length := by
  by_cases e : ∃ x ∈ xs, p x
  · exact Nat.le_of_lt (findIdx_lt_length_of_exists e)
  · simp at e
    exact Nat.le_of_eq (findIdx_eq_length.mpr e)

@[simp]
theorem findIdx_lt_length {p : α → Bool} {xs : List α} :
    xs.findIdx p < xs.length ↔ ∃ x ∈ xs, p x := by
  rw [← Decidable.not_iff_not, Nat.not_lt]
  have := @Nat.le_antisymm_iff (xs.findIdx p) xs.length
  simp only [findIdx_le_length, true_and] at this
  rw [← this, findIdx_eq_length, not_exists]
  simp only [Bool.not_eq_true, not_and]

/-- `p` does not hold for elements with indices less than `xs.findIdx p`. -/
theorem not_of_lt_findIdx {p : α → Bool} {xs : List α} {i : Nat} (h : i < xs.findIdx p) :
    p (xs[i]'(Nat.le_trans h findIdx_le_length)) = false := by
  revert i
  induction xs with
  | nil => intro i h; rw [findIdx_nil] at h; simp at h
  | cons x xs ih =>
    intro i h
    have ho := h
    rw [findIdx_cons] at h
    have npx : p x = false := by
      apply eq_false_of_ne_true
      intro y
      rw [y, cond_true] at h
      simp at h
    simp [npx, cond_false] at h
    cases i.eq_zero_or_pos with
    | inl e => simpa [e, Fin.zero_eta, get_cons_zero]
    | inr e =>
      have ipm := Nat.succ_pred_eq_of_pos e
      simp +singlePass only [← ipm, getElem_cons_succ]
      rw [← ipm, Nat.succ_lt_succ_iff] at h
      simpa using ih h

/-- If `¬ p xs[j]` for all `j < i`, then `i ≤ xs.findIdx p`. -/
theorem le_findIdx_of_not {p : α → Bool} {xs : List α} {i : Nat} (h : i < xs.length)
    (h2 : ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false) : i ≤ xs.findIdx p := by
  apply Decidable.byContradiction
  intro f
  simp only [Nat.not_le] at f
  exact absurd (@findIdx_getElem _ p xs (Nat.lt_trans f h)) (by simpa using h2 (xs.findIdx p) f)

/-- If `¬ p xs[j]` for all `j ≤ i`, then `i < xs.findIdx p`. -/
theorem lt_findIdx_of_not {p : α → Bool} {xs : List α} {i : Nat} (h : i < xs.length)
    (h2 : ∀ j (hji : j ≤ i), ¬p (xs[j]'(Nat.lt_of_le_of_lt hji h))) : i < xs.findIdx p := by
  apply Decidable.byContradiction
  intro f
  simp only [Nat.not_lt] at f
  exact absurd (@findIdx_getElem _ p xs (Nat.lt_of_le_of_lt f h)) (h2 (xs.findIdx p) f)

/-- `xs.findIdx p = i` iff `p xs[i]` and `¬ p xs [j]` for all `j < i`. -/
theorem findIdx_eq {p : α → Bool} {xs : List α} {i : Nat} (h : i < xs.length) :
    xs.findIdx p = i ↔ p xs[i] ∧ ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false := by
  refine ⟨fun f ↦ ⟨f ▸ (@findIdx_getElem _ p xs (f ▸ h)), fun _ hji ↦ not_of_lt_findIdx (f ▸ hji)⟩,
    fun ⟨_, h2⟩ ↦ ?_⟩
  apply Nat.le_antisymm _ (le_findIdx_of_not h h2)
  apply Decidable.byContradiction
  intro h3
  simp at h3
  simp_all [not_of_lt_findIdx h3]

theorem findIdx_append {p : α → Bool} {l₁ l₂ : List α} :
    (l₁ ++ l₂).findIdx p =
      if l₁.findIdx p < l₁.length then l₁.findIdx p else l₂.findIdx p + l₁.length := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx_cons, length_cons, cons_append]
    by_cases h : p x
    · simp [h]
    · simp only [h, ih, cond_eq_if, Bool.false_eq_true, ↓reduceIte, add_one_lt_add_one_iff]
      split <;> simp [Nat.add_assoc]

theorem IsPrefix.findIdx_le {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <+: l₂) :
    l₁.findIdx p ≤ l₂.findIdx p := by
  rw [IsPrefix] at h
  obtain ⟨t, rfl⟩ := h
  simp only [findIdx_append, findIdx_lt_length]
  split
  · exact Nat.le_refl ..
  · simp_all [findIdx_eq_length_of_false]

theorem IsPrefix.findIdx_eq_of_findIdx_lt_length {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <+: l₂)
    (lt : l₁.findIdx p < l₁.length) : l₂.findIdx p = l₁.findIdx p := by
  rw [IsPrefix] at h
  obtain ⟨t, rfl⟩ := h
  simp only [findIdx_append, findIdx_lt_length]
  split
  · rfl
  · simp_all

theorem findIdx_le_findIdx {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x → q x) : l.findIdx q ≤ l.findIdx p := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx_cons, cond_eq_if]
    split
    · simp
    · split
      · simp_all
      · simp only [Nat.add_le_add_iff_right]
        exact ih fun _ m w => h _ (mem_cons_of_mem x m) w

@[simp] theorem findIdx_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findIdx f = l.unattach.findIdx g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [ih, hf, findIdx_cons]

/-! ### findIdx? -/

@[simp]
theorem findIdx?_eq_none_iff {xs : List α} {p : α → Bool} :
    xs.findIdx? p = none ↔ ∀ x, x ∈ xs → p x = false := by
  induction xs with
  | nil => simp_all
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split <;> simp_all [cond_eq_if]

theorem findIdx?_isSome {xs : List α} {p : α → Bool} :
    (xs.findIdx? p).isSome = xs.any p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split <;> simp_all

theorem findIdx?_isNone {xs : List α} {p : α → Bool} :
    (xs.findIdx? p).isNone = xs.all (¬p ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split <;> simp_all

theorem findIdx?_eq_some_iff_findIdx_eq {xs : List α} {p : α → Bool} {i : Nat} :
    xs.findIdx? p = some i ↔ i < xs.length ∧ xs.findIdx p = i := by
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp only [findIdx?_cons, findIdx_cons]
    split
    · simp_all [cond_eq_if]
      rintro rfl
      exact zero_lt_succ xs.length
    · simp_all [cond_eq_if, and_assoc]
      constructor
      · rintro ⟨a, lt, rfl, rfl⟩
        simp_all [Nat.succ_lt_succ_iff]
      · rintro ⟨h, rfl⟩
        exact ⟨_, by simp_all [Nat.succ_lt_succ_iff], rfl, rfl⟩

theorem findIdx?_eq_some_of_exists {xs : List α} {p : α → Bool} (h : ∃ x, x ∈ xs ∧ p x) :
    xs.findIdx? p = some (xs.findIdx p) := by
  rw [findIdx?_eq_some_iff_findIdx_eq]
  exact ⟨findIdx_lt_length_of_exists h, rfl⟩

theorem findIdx?_eq_none_iff_findIdx_eq {xs : List α} {p : α → Bool} :
    xs.findIdx? p = none ↔ xs.findIdx p = xs.length := by
  simp

theorem findIdx?_eq_guard_findIdx_lt {xs : List α} {p : α → Bool} :
    xs.findIdx? p = Option.guard (fun i => i < xs.length) (xs.findIdx p) := by
  match h : xs.findIdx? p with
  | none =>
    simp only [findIdx?_eq_none_iff] at h
    simp [findIdx_eq_length_of_false h, Option.guard]
  | some i =>
    simp only [findIdx?_eq_some_iff_findIdx_eq] at h
    simp [h]

theorem findIdx?_eq_some_iff_getElem {xs : List α} {p : α → Bool} {i : Nat} :
    xs.findIdx? p = some i ↔
      ∃ h : i < xs.length, p xs[i] ∧ ∀ j (hji : j < i), ¬p (xs[j]'(Nat.lt_trans hji h)) := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons, Nat.zero_add]
    split
    · simp only [Option.some.injEq, Bool.not_eq_true, length_cons]
      cases i with
      | zero => simp_all
      | succ i =>
        simp only [Bool.not_eq_true, zero_ne_add_one, getElem_cons_succ, false_iff, not_exists,
          not_and, Classical.not_forall, Bool.not_eq_false]
        intros
        refine ⟨0, zero_lt_succ i, ‹_›⟩
    · simp only [Option.map_eq_some', ih, Bool.not_eq_true, length_cons]
      constructor
      · rintro ⟨a, ⟨⟨h, h₁, h₂⟩, rfl⟩⟩
        refine ⟨Nat.succ_lt_succ_iff.mpr h, by simpa, fun j hj => ?_⟩
        cases j with
        | zero => simp_all
        | succ j =>
          apply h₂
          simp_all [Nat.succ_lt_succ_iff]
      · rintro ⟨h, h₁, h₂⟩
        cases i with
        | zero => simp_all
        | succ i =>
          refine ⟨i, ⟨Nat.succ_lt_succ_iff.mp h, by simpa, fun j hj => ?_⟩, rfl⟩
          simpa using h₂ (j + 1) (Nat.succ_lt_succ_iff.mpr hj)

theorem of_findIdx?_eq_some {xs : List α} {p : α → Bool} (w : xs.findIdx? p = some i) :
    match xs[i]? with | some a => p a | none => false := by
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [findIdx?_cons, Nat.zero_add]
    split at w <;> cases i <;> simp_all [succ_inj']

@[deprecated of_findIdx?_eq_some (since := "2025-02-02")]
abbrev findIdx?_of_eq_some := @of_findIdx?_eq_some

theorem of_findIdx?_eq_none {xs : List α} {p : α → Bool} (w : xs.findIdx? p = none) :
    ∀ i : Nat, match xs[i]? with | some a => ¬ p a | none => true := by
  intro i
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [Bool.not_eq_true, findIdx?_cons, Nat.zero_add]
    cases i with
    | zero =>
      split at w <;> simp_all
    | succ i =>
      simp only [getElem?_cons_succ]
      apply ih
      split at w <;> simp_all

@[deprecated of_findIdx?_eq_none (since := "2025-02-02")]
abbrev findIdx?_of_eq_none := @of_findIdx?_eq_none

@[simp] theorem findIdx?_map {f : β → α} {l : List β} : findIdx? p (l.map f) = l.findIdx? (p ∘ f) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, findIdx?_cons]
    split <;> simp_all

@[simp] theorem findIdx?_append :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p).or ((ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with simp
  | cons _ _ _ => split <;> simp_all [Option.map_or', Option.map_map]; rfl

theorem findIdx?_flatten {l : List (List α)} {p : α → Bool} :
    l.flatten.findIdx? p =
      (l.findIdx? (·.any p)).map
        fun i => ((l.take i).map List.length).sum +
          (l[i]?.map fun xs => xs.findIdx p).getD 0 := by
  induction l with
  | nil => simp
  | cons xs l ih =>
    rw [flatten_cons, findIdx?_append, ih, findIdx?_cons]
    split <;> rename_i h
    · simp only [any_eq_true] at h
      rw [Option.or_of_isSome (by simp_all [findIdx?_isSome])]
      simp_all [findIdx?_eq_some_of_exists]
    · rw [Option.or_of_isNone (by simp_all [findIdx?_isNone])]
      simp [Function.comp_def, Nat.add_comm, Nat.add_assoc]

@[simp] theorem findIdx?_replicate :
    (replicate n a).findIdx? p = if 0 < n ∧ p a then some 0 else none := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [replicate, findIdx?_cons, Nat.zero_add, zero_lt_succ, true_and]
    split <;> simp_all

theorem findIdx?_eq_findSome?_zipIdx {xs : List α} {p : α → Bool} :
    xs.findIdx? p = xs.zipIdx.findSome? fun ⟨a, i⟩ => if p a then some i else none := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons, Nat.zero_add, zipIdx]
    split
    · simp_all
    · simp_all only [zipIdx_cons, ite_false, Option.isNone_none, findSome?_cons_of_isNone, reduceCtorEq]
      rw [← map_snd_add_zipIdx_eq_zipIdx (n := 1) (k := 0)]
      simp [Function.comp_def, findSome?_map]

theorem findIdx?_eq_fst_find?_zipIdx {xs : List α} {p : α → Bool} :
    xs.findIdx? p = (xs.zipIdx.find? fun ⟨x, _⟩ => p x).map (·.2) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons, Nat.zero_add, zipIdx_cons]
    split
    · simp_all
    · rw [ih, ← map_snd_add_zipIdx_eq_zipIdx (n := 1) (k := 0)]
      simp [Function.comp_def, *]

-- See also `findIdx_le_findIdx`.
theorem findIdx?_eq_none_of_findIdx?_eq_none {xs : List α} {p q : α → Bool} (w : ∀ x ∈ xs, p x → q x) :
    xs.findIdx? q = none → xs.findIdx? p = none := by
  simp only [findIdx?_eq_none_iff]
  intro h x m
  cases z : p x
  · rfl
  · exfalso
    specialize w x m z
    specialize h x m
    simp_all

theorem Sublist.findIdx?_isSome {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    (l₁.findIdx? p).isSome → (l₂.findIdx? p).isSome := by
  simp only [List.findIdx?_isSome, any_eq_true]
  rintro ⟨w, m, q⟩
  exact ⟨w, h.mem m, q⟩

theorem Sublist.findIdx?_eq_none {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    l₂.findIdx? p = none → l₁.findIdx? p = none := by
  simp only [findIdx?_eq_none_iff]
  exact fun w x m => w x (h.mem m)

theorem IsPrefix.findIdx?_eq_some {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <+: l₂) :
    List.findIdx? p l₁ = some i → List.findIdx? p l₂ = some i := by
  rw [IsPrefix] at h
  obtain ⟨t, rfl⟩ := h
  intro h
  simp [findIdx?_append, h]
theorem IsPrefix.findIdx?_eq_none {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <+: l₂) :
    List.findIdx? p l₂ = none → List.findIdx? p l₁ = none :=
  h.sublist.findIdx?_eq_none
theorem IsSuffix.findIdx?_eq_none {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <:+ l₂) :
    List.findIdx? p l₂ = none → List.findIdx? p l₁ = none :=
  h.sublist.findIdx?_eq_none
theorem IsInfix.findIdx?_eq_none {l₁ l₂ : List α} {p : α → Bool} (h : l₁ <:+: l₂) :
    List.findIdx? p l₂ = none → List.findIdx? p l₁ = none :=
  h.sublist.findIdx?_eq_none

theorem findIdx_eq_getD_findIdx? {xs : List α} {p : α → Bool} :
    xs.findIdx p = (xs.findIdx? p).getD xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx_cons, findIdx?_cons]
    split <;> simp_all [ih]

@[simp] theorem findIdx?_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findIdx? f = l.unattach.findIdx? g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [hf, findIdx?_cons]
    split <;> simp [ih, Function.comp_def]

/-! ### findFinIdx? -/

@[simp] theorem findFinIdx?_nil {p : α → Bool} : findFinIdx? p [] = none := rfl

theorem findIdx?_go_eq_map_findFinIdx?_go_val {xs : List α} {p : α → Bool} {i : Nat} {h} :
    List.findIdx?.go p xs i =
      (List.findFinIdx?.go p l xs i h).map (·.val) := by
  unfold findIdx?.go
  unfold findFinIdx?.go
  split
  · simp_all
  · simp only
    split
    · simp
    · rw [findIdx?_go_eq_map_findFinIdx?_go_val]

theorem findIdx?_eq_map_findFinIdx?_val {xs : List α} {p : α → Bool} :
    xs.findIdx? p = (xs.findFinIdx? p).map (·.val) := by
  simp [findIdx?, findFinIdx?]
  rw [findIdx?_go_eq_map_findFinIdx?_go_val]

theorem findFinIdx?_eq_pmap_findIdx? {xs : List α} {p : α → Bool} :
    xs.findFinIdx? p =
      (xs.findIdx? p).pmap
        (fun i m => by simp [findIdx?_eq_some_iff_getElem] at m; exact ⟨i, m.choose⟩)
        (fun i h => h) := by
  simp [findIdx?_eq_map_findFinIdx?_val, Option.pmap_map]

@[simp] theorem findFinIdx?_cons {p : α → Bool} {x : α} {xs : List α} :
    findFinIdx? p (x :: xs) = if p x then some 0 else (findFinIdx? p xs).map Fin.succ := by
  rw [← Option.map_inj_right (f := Fin.val) (fun a b => Fin.eq_of_val_eq)]
  rw [← findIdx?_eq_map_findFinIdx?_val]
  rw [findIdx?_cons]
  split
  · simp
  · rw [findIdx?_eq_map_findFinIdx?_val]
    simp [Function.comp_def]

@[simp] theorem findFinIdx?_eq_none_iff {l : List α} {p : α → Bool} :
    l.findFinIdx? p = none ↔ ∀ x ∈ l, ¬ p x := by
  simp [findFinIdx?_eq_pmap_findIdx?]

@[simp]
theorem findFinIdx?_eq_some_iff {xs : List α} {p : α → Bool} {i : Fin xs.length} :
    xs.findFinIdx? p = some i ↔
      p xs[i] ∧ ∀ j (hji : j < i), ¬p (xs[j]'(Nat.lt_trans hji i.2)) := by
  simp only [findFinIdx?_eq_pmap_findIdx?, Option.pmap_eq_some_iff, findIdx?_eq_some_iff_getElem,
    Bool.not_eq_true, Option.mem_def, exists_and_left, and_exists_self, Fin.getElem_fin]
  constructor
  · rintro ⟨a, ⟨h, w₁, w₂⟩, rfl⟩
    exact ⟨w₁, fun j hji => by simpa using w₂ j hji⟩
  · rintro ⟨h, w⟩
    exact ⟨i, ⟨i.2, h, fun j hji => w ⟨j, by omega⟩ hji⟩, rfl⟩

@[simp] theorem findFinIdx?_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findFinIdx? f = (l.unattach.findFinIdx? g).map (fun i => i.cast (by simp)) := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [hf, findFinIdx?_cons]
    split <;> simp [ih, Function.comp_def]


/-! ### idxOf

The verification API for `idxOf` is still incomplete.
The lemmas below should be made consistent with those for `findIdx` (and proved using them).
-/

theorem idxOf_cons [BEq α] :
    (x :: xs : List α).idxOf y = bif x == y then 0 else xs.idxOf y + 1 := by
  dsimp [idxOf]
  simp [findIdx_cons]

@[deprecated idxOf_cons (since := "2025-01-29")]
abbrev indexOf_cons := @idxOf_cons

@[simp] theorem idxOf_cons_self [BEq α] [ReflBEq α] {l : List α} : (a :: l).idxOf a = 0 := by
  simp [idxOf_cons]

@[deprecated idxOf_cons_self (since := "2025-01-29")]
abbrev indexOf_cons_self := @idxOf_cons_self

theorem idxOf_append [BEq α] [LawfulBEq α] {l₁ l₂ : List α} {a : α} :
    (l₁ ++ l₂).idxOf a = if a ∈ l₁ then l₁.idxOf a else l₂.idxOf a + l₁.length := by
  rw [idxOf, findIdx_append]
  split <;> rename_i h
  · rw [if_pos]
    simpa using h
  · rw [if_neg]
    simpa using h

@[deprecated idxOf_append (since := "2025-01-29")]
abbrev indexOf_append := @idxOf_append

theorem idxOf_eq_length [BEq α] [LawfulBEq α] {l : List α} (h : a ∉ l) : l.idxOf a = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [mem_cons, not_or] at h
    simp only [idxOf_cons, cond_eq_if, beq_iff_eq]
    split <;> simp_all

@[deprecated idxOf_eq_length (since := "2025-01-29")]
abbrev indexOf_eq_length := @idxOf_eq_length

theorem idxOf_lt_length [BEq α] [LawfulBEq α] {l : List α} (h : a ∈ l) : l.idxOf a < l.length := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [mem_cons] at h
    obtain rfl | h := h
    · simp
    · simp only [idxOf_cons, cond_eq_if, beq_iff_eq, length_cons]
      specialize ih h
      split
      · exact zero_lt_succ xs.length
      · exact Nat.add_lt_add_right ih 1

@[deprecated idxOf_lt_length (since := "2025-01-29")]
abbrev indexOf_lt_length := @idxOf_lt_length

/-! ### finIdxOf?

The verification API for `finIdxOf?` is still incomplete.
The lemmas below should be made consistent with those for `findFinIdx?` (and proved using them).
-/

theorem idxOf?_eq_map_finIdxOf?_val [BEq α] {xs : List α} {a : α} :
    xs.idxOf? a = (xs.finIdxOf? a).map (·.val) := by
  simp [idxOf?, finIdxOf?, findIdx?_eq_map_findFinIdx?_val]

@[simp] theorem finIdxOf?_nil [BEq α] : ([] : List α).finIdxOf? a = none := rfl

@[simp] theorem finIdxOf?_cons [BEq α] {a : α} {xs : List α} :
    (a :: xs).finIdxOf? b =
      if a == b then some ⟨0, by simp⟩ else (xs.finIdxOf? b).map (·.succ) := by
  simp [finIdxOf?]

@[simp] theorem finIdxOf?_eq_none_iff [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.finIdxOf? a = none ↔ a ∉ l := by
  simp only [finIdxOf?, findFinIdx?_eq_none_iff, beq_iff_eq]
  constructor
  · intro w m
    exact w a m rfl
  · rintro h a m rfl
    exact h m

@[simp] theorem finIdxOf?_eq_some_iff [BEq α] [LawfulBEq α] {l : List α} {a : α} {i : Fin l.length} :
    l.finIdxOf? a = some i ↔ l[i] = a ∧ ∀ j (_ : j < i), ¬l[j] = a := by
  simp only [finIdxOf?, findFinIdx?_eq_some_iff, beq_iff_eq]

/-! ### idxOf?

The verification API for `idxOf?` is still incomplete.
The lemmas below should be made consistent with those for `findIdx?` (and proved using them).
-/

@[simp] theorem idxOf?_nil [BEq α] : ([] : List α).idxOf? a = none := rfl

theorem idxOf?_cons [BEq α] {a : α} {xs : List α} {b : α} :
    (a :: xs).idxOf? b = if a == b then some 0 else (xs.idxOf? b).map (· + 1) := by
  simp [idxOf?]

@[simp] theorem idxOf?_eq_none_iff [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.idxOf? a = none ↔ a ∉ l := by
  simp only [idxOf?, findIdx?_eq_none_iff, beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro w h
    specialize w _ h
    simp at w
  · rintro w x h rfl
    contradiction

@[deprecated idxOf?_eq_none_iff (since := "2025-01-29")]
abbrev indexOf?_eq_none_iff := @idxOf?_eq_none_iff

/-! ### lookup -/

section lookup
variable [BEq α] [LawfulBEq α]

@[simp] theorem lookup_cons_self  {k : α} : ((k,b) :: es).lookup k = some b := by
  simp [lookup_cons]

theorem lookup_eq_findSome? {l : List (α × β)} {k : α} :
    l.lookup k = l.findSome? fun p => if k == p.1 then some p.2 else none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    match p with
    | (k', v) =>
      simp only [lookup_cons, findSome?_cons]
      split <;> simp_all

@[simp] theorem lookup_eq_none_iff {l : List (α × β)} {k : α} :
    l.lookup k = none ↔ ∀ p ∈ l, k != p.1 := by
  simp [lookup_eq_findSome?]

@[simp] theorem lookup_isSome_iff {l : List (α × β)} {k : α} :
    (l.lookup k).isSome ↔ ∃ p ∈ l, k == p.1 := by
  simp [lookup_eq_findSome?]

theorem lookup_eq_some_iff {l : List (α × β)} {k : α} {b : β} :
    l.lookup k = some b ↔ ∃ l₁ l₂, l = l₁ ++ (k, b) :: l₂ ∧ ∀ p ∈ l₁, k != p.1 := by
  simp only [lookup_eq_findSome?, findSome?_eq_some_iff]
  constructor
  · rintro ⟨l₁, a, l₂, rfl, h₁, h₂⟩
    simp only [beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simp at h₂
    exact ⟨l₁, l₂, rfl, by simpa using h₂⟩
  · rintro ⟨l₁, l₂, rfl, h⟩
    exact ⟨l₁, (k, b), l₂, rfl, by simp, by simpa using h⟩

theorem lookup_append {l₁ l₂ : List (α × β)} {k : α} :
    (l₁ ++ l₂).lookup k = (l₁.lookup k).or (l₂.lookup k) := by
  simp [lookup_eq_findSome?, findSome?_append]

theorem lookup_replicate {k : α} :
    (replicate n (a,b)).lookup k = if n = 0 then none else if k == a then some b else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, lookup_cons]
    split <;> simp_all

theorem lookup_replicate_of_pos {k : α} (h : 0 < n) :
    (replicate n (a, b)).lookup k = if k == a then some b else none := by
  simp [lookup_replicate, Nat.ne_of_gt h]

theorem lookup_replicate_self {a : α} :
    (replicate n (a, b)).lookup a = if n = 0 then none else some b := by
  simp [lookup_replicate]

@[simp] theorem lookup_replicate_self_of_pos {a : α} (h : 0 < n) :
    (replicate n (a, b)).lookup a = some b := by
  simp [lookup_replicate_self, Nat.ne_of_gt h]

@[simp] theorem lookup_replicate_ne {k : α} (h : !k == a) :
    (replicate n (a, b)).lookup k = none := by
  simp_all [lookup_replicate]

theorem Sublist.lookup_isSome {l₁ l₂ : List (α × β)} (h : l₁ <+ l₂) :
    (l₁.lookup k).isSome → (l₂.lookup k).isSome := by
  simp only [lookup_eq_findSome?]
  exact h.findSome?_isSome

theorem Sublist.lookup_eq_none {l₁ l₂ : List (α × β)} (h : l₁ <+ l₂) :
    l₂.lookup k = none → l₁.lookup k = none := by
  simp only [lookup_eq_findSome?]
  exact h.findSome?_eq_none

theorem IsPrefix.lookup_eq_some {l₁ l₂ : List (α × β)} (h : l₁ <+: l₂) :
    List.lookup k l₁ = some b → List.lookup k l₂ = some b := by
  simp only [lookup_eq_findSome?]
  exact h.findSome?_eq_some

theorem IsPrefix.lookup_eq_none {l₁ l₂ : List (α × β)} (h : l₁ <+: l₂) :
    List.lookup k l₂ = none → List.lookup k l₁ = none :=
  h.sublist.lookup_eq_none
theorem IsSuffix.lookup_eq_none {l₁ l₂ : List (α × β)} (h : l₁ <:+ l₂) :
    List.lookup k l₂ = none → List.lookup k l₁ = none :=
  h.sublist.lookup_eq_none
theorem IsInfix.lookup_eq_none {l₁ l₂ : List (α × β)} (h : l₁ <:+: l₂) :
    List.lookup k l₂ = none → List.lookup k l₁ = none :=
  h.sublist.lookup_eq_none

end lookup

/-! ### Deprecations -/

@[deprecated head_flatten (since := "2024-10-14")] abbrev head_join := @head_flatten
@[deprecated getLast_flatten (since := "2024-10-14")] abbrev getLast_join := @getLast_flatten
@[deprecated find?_flatten (since := "2024-10-14")] abbrev find?_join := @find?_flatten
@[deprecated find?_flatten_eq_none (since := "2024-10-14")] abbrev find?_join_eq_none := @find?_flatten_eq_none_iff
@[deprecated find?_flatten_eq_some (since := "2024-10-14")] abbrev find?_join_eq_some := @find?_flatten_eq_some_iff
@[deprecated findIdx?_flatten (since := "2024-10-14")] abbrev findIdx?_join := @findIdx?_flatten

end List
