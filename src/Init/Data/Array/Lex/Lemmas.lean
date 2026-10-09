/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/
module

prelude
import all Init.Data.Array.Lex.Basic
public import Init.Data.Array.Lex.Basic
import Init.Data.Range.Polymorphic.NatLemmas
public import Init.Data.BEq
public import Init.Data.Function
import Init.Data.Array.Bootstrap
import Init.Data.Array.DecidableEq
import Init.Data.Array.Lemmas
import Init.Data.Bool
import Init.Data.List.Lex
import Init.Data.Range.Polymorphic.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.ByCases
import Init.Data.List.Nat.Basic

public section

open Std

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/-! ### Lexicographic ordering -/

@[simp] theorem _root_.List.lt_toArray [LT α] {l₁ l₂ : List α} : l₁.toArray < l₂.toArray ↔ l₁ < l₂ := Iff.rfl
@[simp] theorem _root_.List.le_toArray [LT α] {l₁ l₂ : List α} : l₁.toArray ≤ l₂.toArray ↔ l₁ ≤ l₂ := Iff.rfl

@[simp] theorem lt_toList [LT α] {xs ys : Array α} : xs.toList < ys.toList ↔ xs < ys := Iff.rfl
@[simp] theorem le_toList [LT α] {xs ys : Array α} : xs.toList ≤ ys.toList ↔ xs ≤ ys := Iff.rfl

grind_pattern _root_.List.lt_toArray => l₁.toArray < l₂.toArray
grind_pattern _root_.List.le_toArray => l₁.toArray ≤ l₂.toArray
grind_pattern lt_toList => xs.toList < ys.toList
grind_pattern le_toList => xs.toList ≤ ys.toList

@[simp]
protected theorem not_lt [LT α] {xs ys : Array α} : ¬ xs < ys ↔ ys ≤ xs := Iff.rfl

@[deprecated Array.not_lt (since := "2025-10-26")]
protected theorem not_lt_iff_ge [LT α] {xs ys : Array α} : ¬ xs < ys ↔ ys ≤ xs := Iff.rfl

@[simp]
protected theorem not_le [LT α] {xs ys : Array α} :
    ¬ xs ≤ ys ↔ ys < xs :=
  Classical.not_not

@[deprecated Array.not_le (since := "2025-10-26")]
protected theorem not_le_iff_gt [LT α] {xs ys : Array α} :
    ¬ xs ≤ ys ↔ ys < xs :=
  Classical.not_not

@[simp] theorem lex_empty [BEq α] {lt : α → α → Bool} {xs : Array α} : xs.lex #[] lt = false := by
  simp [lex, lex.go]

@[simp, grind =] theorem _root_.List.lex_toArray [BEq α] {lt : α → α → Bool} {l₁ l₂ : List α} :
    l₁.toArray.lex l₂.toArray lt = l₁.lex l₂ lt := by
  rw [lex]
  suffices ∀ (i : Nat), (h₁ : i ≤ l₁.length) → (h₂ : i ≤ l₂.length) →
      (∀ j, (hj : j < i) → lt l₁[j] l₂[j] = false ∧ ((l₁[j] == l₂[j]) = true)) →
    lex.go l₁.toArray l₂.toArray lt i = l₁.lex l₂ lt from this 0 (by simp) (by simp) (by simp)
  intro i hi₁' hi₂' hi₁
  fun_induction lex.go with
  | case1 i hi₂ =>
    simp only [List.size_toArray] at hi₂
    obtain rfl : i = l₁.length := by omega
    rw [eq_comm, Bool.eq_iff_iff, List.lex_eq_true_iff_exists]
    simp only [List.size_toArray, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rintro (⟨-, h⟩|⟨j, ⟨hj₁, hj₂, hj₃, hj₄⟩⟩)
      · exact h
      · simp [(hi₁ j hj₁).1] at hj₄
    · intro hlt
      refine Or.inl ⟨?_, hlt⟩
      rw [List.isEqv_eq_true_iff_getElem]
      refine ⟨?_, fun i hi => ?_⟩
      · simp only [List.length_take]
        omega
      · simpa using (hi₁ i hi).2
  | case2 i hi₂ hi₃ =>
    simp only [List.size_toArray, Nat.not_le] at hi₂ hi₃
    obtain rfl : i = l₂.length := by omega
    rw [eq_comm, ← Bool.not_eq_true, List.lex_eq_true_iff_exists]
    simp only [not_or, not_and, Nat.not_lt, hi₁', implies_true, not_exists, Bool.not_eq_true,
      true_and]
    exact fun k hk₁ hk₂ hk₃ => (hi₁ k hk₂).1
  | case3 i hi₂ hi₃ hi₄ =>
    simp only [List.size_toArray, Nat.not_le] at hi₂ hi₃
    rw [eq_comm, List.lex_eq_true_iff_exists]
    exact Or.inr ⟨i, hi₂, hi₃, fun j hj => (hi₁ j hj).2, by simpa⟩
  | case4 i hi₂ hi₃ hi₄ hi₅ ih =>
    simp only [List.size_toArray, Nat.not_le] at hi₂ hi₃
    apply ih (by omega) (by omega) _
    intro j hj
    by_cases hj' : j < i
    · exact hi₁ _ hj'
    · obtain rfl : j = i := by omega
      exact ⟨by simpa using hi₄, by simpa⟩
  | case5 i hi₂ hi₃ hi₄ hi₅ =>
    simp only [List.size_toArray, Nat.not_le] at hi₂ hi₃
    rw [eq_comm, ← Bool.not_eq_true, List.lex_eq_true_iff_exists]
    simp only [not_or, not_and, Nat.not_lt, not_exists, Bool.not_eq_true]
    refine ⟨fun h => ?_, ?_⟩
    · rw [List.isEqv_eq_true_iff_getElem] at h
      rcases h with ⟨h, h'⟩
      have := h' i hi₂
      simp only [List.getElem_take] at this
      simp [this] at hi₅
    · intro j hj₁ hj₂ hj₃
      obtain (hji|rfl|hji) := Nat.lt_trichotomy i j
      · have := hj₃ _ hji
        simp [this] at hi₅
      · simpa using hi₄
      · exact (hi₁ j hji).1

theorem singleton_lex_singleton [BEq α] {lt : α → α → Bool} : #[a].lex #[b] lt = lt a b := by
  simp

@[simp, grind =] theorem lex_toList [BEq α] {lt : α → α → Bool} {xs ys : Array α} :
    xs.toList.lex ys.toList lt = xs.lex ys lt := by
  cases xs <;> cases ys <;> simp

instance [LT α] [LE α] [LawfulOrderLT α] [IsLinearOrder α] : IsLinearOrder (Array α) := by
  apply IsLinearOrder.of_le
  · constructor
    intro _ _ hab hba
    simpa using Std.le_antisymm (α := List α) hab hba
  · constructor; exact Std.le_trans (α := List α)
  · constructor; exact fun _ _ => Std.le_total (α := List α)

protected theorem lt_irrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] (xs : Array α) : ¬ xs < xs :=
  List.lt_irrefl xs.toList

instance ltIrrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Irrefl (α := Array α) (· < ·) where
  irrefl := Array.lt_irrefl

@[simp] theorem not_lt_empty [LT α] (xs : Array α) : ¬ xs < #[] := List.not_lt_nil xs.toList
@[simp] theorem empty_le [LT α] (xs : Array α) : #[] ≤ xs := List.nil_le xs.toList

@[simp] theorem le_empty [LT α] {xs : Array α} : xs ≤ #[] ↔ xs = #[] := by
  cases xs
  simp

@[simp] theorem empty_lt_push [LT α] (xs : Array α) (a : α) : #[] < xs.push a := by
  rcases xs with (_ | ⟨x, xs⟩) <;> simp

theorem empty_lt_iff [LT α] {xs : Array α} : #[] < xs ↔ xs ≠ #[] := by
  rw [← lt_toList, toList_empty, List.nil_lt_iff, ne_eq, ne_eq, toList_eq_nil_iff]

protected theorem le_refl [LT α] [i₀ : Std.Irrefl (· < · : α → α → Prop)] (xs : Array α) : xs ≤ xs :=
  List.le_refl xs.toList

instance [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Refl (· ≤ · : Array α → Array α → Prop) where
  refl := Array.le_refl

protected theorem lt_trans [LT α]
    [i₁ : Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
    {xs ys zs : Array α} (h₁ : xs < ys) (h₂ : ys < zs) : xs < zs :=
  List.lt_trans h₁ h₂

instance [LT α] [Trans (· < · : α → α → Prop) (· < ·) (· < ·)] :
    Trans (· < · : Array α → Array α → Prop) (· < ·) (· < ·) where
  trans h₁ h₂ := Array.lt_trans h₁ h₂

protected theorem lt_of_le_of_lt [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α]
    {xs ys zs : Array α} (h₁ : xs ≤ ys) (h₂ : ys < zs) : xs < zs :=
  Std.lt_of_le_of_lt (α := List α) h₁ h₂

protected theorem le_trans [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α]
    {xs ys zs : Array α} (h₁ : xs ≤ ys) (h₂ : ys ≤ zs) : xs ≤ zs :=
  fun h₃ => h₁ (Array.lt_of_le_of_lt h₂ h₃)

instance [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] :
    Trans (· ≤ · : Array α → Array α → Prop) (· ≤ ·) (· ≤ ·) where
  trans h₁ h₂ := Array.le_trans h₁ h₂

protected theorem lt_asymm [LT α]
    [i : Std.Asymm (· < · : α → α → Prop)]
    {xs ys : Array α} (h : xs < ys) : ¬ ys < xs := List.lt_asymm h

instance [LT α]
    [Std.Asymm (· < · : α → α → Prop)] :
    Std.Asymm (· < · : Array α → Array α → Prop) where
  asymm _ _ := Array.lt_asymm

protected theorem le_total [LT α]
    [i : Std.Asymm (· < · : α → α → Prop)] (xs ys : Array α) : xs ≤ ys ∨ ys ≤ xs :=
  List.le_total xs.toList ys.toList

protected theorem le_of_lt [LT α]
    [i : Std.Asymm (· < · : α → α → Prop)]
    {xs ys : Array α} (h : xs < ys) : xs ≤ ys :=
  List.le_of_lt h

protected theorem le_iff_lt_or_eq [LT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Trichotomous (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    {xs ys : Array α} : xs ≤ ys ↔ xs < ys ∨ xs = ys := by
  simpa using List.le_iff_lt_or_eq (l₁ := xs.toList) (l₂ := ys.toList)

protected theorem le_antisymm [LT α] [LE α] [IsLinearOrder α] [LawfulOrderLT α]
    {xs ys : Array α} : xs ≤ ys → ys ≤ xs → xs = ys := by
  simpa using List.le_antisymm (as := xs.toList) (bs := ys.toList)

instance [LT α] [Std.Asymm (· < · : α → α → Prop)] :
    Std.Total (· ≤ · : Array α → Array α → Prop) where
  total := Array.le_total

@[simp] theorem lex_eq_true_iff_lt [BEq α] [LawfulBEq α] [LT α] [DecidableLT α]
    {xs ys : Array α} : lex xs ys = true ↔ xs < ys := by
  cases xs
  cases ys
  simp

@[simp] theorem lex_eq_false_iff_ge [BEq α] [LawfulBEq α] [LT α] [DecidableLT α]
    {xs ys : Array α} : lex xs ys = false ↔ ys ≤ xs := by
  cases xs
  cases ys
  simp

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLT (Array α) :=
  fun xs ys => decidable_of_iff (lex xs ys = true) lex_eq_true_iff_lt

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLE (Array α) :=
  fun xs ys => decidable_of_iff (lex ys xs = false) lex_eq_false_iff_ge

/--
`l₁` is lexicographically less than `l₂` if either
- `l₁` is pairwise equivalent under `· == ·` to `l₂.take l₁.size`,
  and `l₁` is shorter than `l₂` or
- there exists an index `i` such that
  - for all `j < i`, `l₁[j] == l₂[j]` and
  - `l₁[i] < l₂[i]`
-/
theorem lex_eq_true_iff_exists [BEq α] (lt : α → α → Bool) :
    lex l₁ l₂ lt = true ↔
      (l₁.isEqv (l₂.take l₁.size) (· == ·) ∧ l₁.size < l₂.size) ∨
        (∃ (i : Nat) (h₁ : i < l₁.size) (h₂ : i < l₂.size),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) == l₂[j]'(Nat.lt_trans hj h₂)) ∧ lt l₁[i] l₂[i]) := by
  cases l₁
  cases l₂
  simp [List.lex_eq_true_iff_exists]

/--
`l₁` is *not* lexicographically less than `l₂`
(which you might think of as "`l₂` is lexicographically greater than or equal to `l₁`"") if either
- `l₁` is pairwise equivalent under `· == ·` to `l₂.take l₁.length` or
- there exists an index `i` such that
  - for all `j < i`, `l₁[j] == l₂[j]` and
  - `l₂[i] < l₁[i]`

This formulation requires that `==` and `lt` are compatible in the following senses:
- `==` is symmetric
  (we unnecessarily further assume it is transitive, to make use of the existing typeclasses)
- `lt` is irreflexive with respect to `==` (i.e. if `x == y` then `lt x y = false`
- `lt` is asymmetric  (i.e. `lt x y = true → lt y x = false`)
- `lt` is antisymmetric with respect to `==` (i.e. `lt x y = false → lt y x = false → x == y`)
-/
theorem lex_eq_false_iff_exists [BEq α] [PartialEquivBEq α] (lt : α → α → Bool)
    (lt_irrefl : ∀ x y, x == y → lt x y = false)
    (lt_asymm : ∀ x y, lt x y = true → lt y x = false)
    (lt_antisymm : ∀ x y, lt x y = false → lt y x = false → x == y) :
    lex l₁ l₂ lt = false ↔
      (l₂.isEqv (l₁.take l₂.size) (· == ·)) ∨
        (∃ (i : Nat) (h₁ : i < l₁.size) (h₂ : i < l₂.size),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) == l₂[j]'(Nat.lt_trans hj h₂)) ∧ lt l₂[i] l₁[i]) := by
  cases l₁
  cases l₂
  simp_all [List.lex_eq_false_iff_exists]

protected theorem lt_iff_exists [LT α] {xs ys : Array α} :
    xs < ys ↔
      (xs = ys.take xs.size ∧ xs.size < ys.size) ∨
        (∃ (i : Nat) (h₁ : i < xs.size) (h₂ : i < ys.size),
          (∀ j, (hj : j < i) →
            xs[j]'(Nat.lt_trans hj h₁) = ys[j]'(Nat.lt_trans hj h₂)) ∧ xs[i] < ys[i]) := by
  cases xs
  cases ys
  simp [List.lt_iff_exists]

protected theorem le_iff_exists [LT α]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Trichotomous (· < · : α → α → Prop)] {xs ys : Array α} :
    xs ≤ ys ↔
      (xs = ys.take xs.size) ∨
        (∃ (i : Nat) (h₁ : i < xs.size) (h₂ : i < ys.size),
          (∀ j, (hj : j < i) →
            xs[j]'(Nat.lt_trans hj h₁) = ys[j]'(Nat.lt_trans hj h₂)) ∧ xs[i] < ys[i]) := by
  cases xs
  cases ys
  simp [List.le_iff_exists]

theorem lt_of_getElem_zero [LT α] {xs ys : Array α} (h₁ : 0 < xs.size) (h₂ : 0 < ys.size)
    (h : xs[0]'h₁ < ys[0]'h₂) : xs < ys :=
  List.lt_of_getElem_zero (by simpa using h₁) (by simpa using h₂) (by simpa using h)

theorem append_left_lt [LT α] {xs ys zs : Array α} (h : ys < zs) :
    xs ++ ys < xs ++ zs := by
  cases xs
  cases ys
  cases zs
  simpa using List.append_left_lt h

theorem append_left_le [LT α]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Trichotomous (· < · : α → α → Prop)]
    {xs ys zs : Array α} (h : ys ≤ zs) :
    xs ++ ys ≤ xs ++ zs := by
  cases xs
  cases ys
  cases zs
  simpa using h

@[simp]
theorem append_left_lt_iff [LT α] [Std.Irrefl (· < · : α → α → Prop)] (xs : Array α)
    {ys zs : Array α} : xs ++ ys < xs ++ zs ↔ ys < zs := by
  simp only [← lt_toList, toList_append, List.append_left_lt_iff]

@[simp]
theorem append_left_le_iff [LT α] [Std.Irrefl (· < · : α → α → Prop)] (xs : Array α)
    {ys zs : Array α} : xs ++ ys ≤ xs ++ zs ↔ ys ≤ zs :=
  not_congr (append_left_lt_iff xs)

theorem le_append_left [LT α] [Std.Irrefl (· < · : α → α → Prop)]
    {xs ys : Array α} : xs ≤ xs ++ ys := by
  cases xs
  cases ys
  simpa using List.le_append_left

theorem append_lt_append_iff_of_size_eq [LT α] {xs₁ xs₂ ys₁ ys₂ : Array α}
    (h : xs₁.size = xs₂.size) :
    xs₁ ++ ys₁ < xs₂ ++ ys₂ ↔ xs₁ < xs₂ ∨ (xs₁ = xs₂ ∧ ys₁ < ys₂) := by
  rw [← lt_toList, toList_append, toList_append,
    List.append_lt_append_iff_of_length_eq (by simpa using h), lt_toList, lt_toList, toList_inj]

theorem append_le_append_iff_of_size_eq [LT α] [Std.Asymm (· < · : α → α → Prop)]
    [Std.Trichotomous (· < · : α → α → Prop)] {xs₁ xs₂ ys₁ ys₂ : Array α}
    (h : xs₁.size = xs₂.size) :
    xs₁ ++ ys₁ ≤ xs₂ ++ ys₂ ↔ xs₁ < xs₂ ∨ (xs₁ = xs₂ ∧ ys₁ ≤ ys₂) := by
  rw [← le_toList, toList_append, toList_append,
    List.append_le_append_iff_of_length_eq (by simpa using h), lt_toList, le_toList, toList_inj]

theorem append_right_lt_iff_of_size_eq [LT α] [Std.Irrefl (· < · : α → α → Prop)]
    {xs₁ xs₂ : Array α} (ys : Array α) (h : xs₁.size = xs₂.size) :
    xs₁ ++ ys < xs₂ ++ ys ↔ xs₁ < xs₂ := by
  rw [← lt_toList, toList_append, toList_append,
    List.append_right_lt_iff_of_length_eq _ (by simpa using h), lt_toList]

theorem append_right_le_iff_of_size_eq [LT α] [Std.Irrefl (· < · : α → α → Prop)]
    {xs₁ xs₂ : Array α} (ys : Array α) (h : xs₁.size = xs₂.size) :
    xs₁ ++ ys ≤ xs₂ ++ ys ↔ xs₁ ≤ xs₂ :=
  not_congr (append_right_lt_iff_of_size_eq ys h.symm)

protected theorem map_lt [LT α] [LT β]
    {xs ys : Array α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : xs < ys) :
    map f xs < map f ys := by
  cases xs
  cases ys
  simpa using List.map_lt w h

protected theorem map_le [LT α] [LT β]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Trichotomous (· < · : α → α → Prop)]
    [Std.Asymm (· < · : β → β → Prop)]
    [Std.Trichotomous (· < · : β → β → Prop)]
    {xs ys : Array α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : xs ≤ ys) :
    map f xs ≤ map f ys := by
  cases xs
  cases ys
  simpa using List.map_le w h

/-- See `map_lt_map_iff` for a variant with fewer proof obligations for `f` but with some mild
assumptions on the order on `α` and `β`. -/
theorem map_lt_map_iff_of_injective [LT α] [LT β] (f : α → β) (hf : ∀ a b, f a < f b ↔ a < b)
    (hfinj : Function.Injective f) {xs ys : Array α} :
    xs.map f < ys.map f ↔ xs < ys := by
  rw [← lt_toList, toList_map, toList_map, List.map_lt_map_iff_of_injective f hf hfinj, lt_toList]

/-- See `map_lt_map_iff_of_injective` for a variant which does not assume anything about the order
on `α` and `β`, but with more assumptions on `f`. -/
theorem map_lt_map_iff [LT α] [Std.Trichotomous (· < · : α → α → Prop)] [LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → β) (hf : ∀ a b, a < b → f a < f b)
    {xs ys : Array α} : xs.map f < ys.map f ↔ xs < ys := by
  rw [← lt_toList, toList_map, toList_map, List.map_lt_map_iff f hf, lt_toList]

theorem map_le_map_iff_of_injective [LT α] [LT β] (f : α → β) (hf : ∀ a b, f a < f b ↔ a < b)
    (hfinj : Function.Injective f) {xs ys : Array α} :
    xs.map f ≤ ys.map f ↔ xs ≤ ys :=
  not_congr (map_lt_map_iff_of_injective f hf hfinj)

theorem map_le_map_iff [LT α] [Std.Trichotomous (· < · : α → α → Prop)] [LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → β) (hf : ∀ a b, a < b → f a < f b)
    {xs ys : Array α} : xs.map f ≤ ys.map f ↔ xs ≤ ys :=
  not_congr (map_lt_map_iff f hf)

theorem flatMap_lt_flatMap_iff [LT α] [Std.Trichotomous (· < · : α → α → Prop)] [LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → Array β)
    (hf : ∀ a b, a < b → f a < f b)
    (hp : ∀ a b zs, f a ++ zs = f b → a = b)
    (hx : ∀ a, f a ≠ #[])
    {xs ys : Array α} :
    xs.flatMap f < ys.flatMap f ↔ xs < ys := by
  rw [← lt_toList, ← lt_toList, toList_flatMap, toList_flatMap]
  exact List.flatMap_lt_flatMap_iff (fun a => (f a).toList) (fun a b h => hf a b h)
    (fun a b ⟨l, hl⟩ => hp a b l.toArray (by simpa [← toList_inj] using hl))
    (fun a => by simpa using hx a)

theorem flatMap_le_flatMap_iff [LT α] [Std.Trichotomous (· < · : α → α → Prop)] [LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → Array β)
    (hf : ∀ a b, a < b → f a < f b)
    (hp : ∀ a b zs, f a ++ zs = f b → a = b)
    (hx : ∀ a, f a ≠ #[])
    {xs ys : Array α} :
    xs.flatMap f ≤ ys.flatMap f ↔ xs ≤ ys :=
  not_congr (flatMap_lt_flatMap_iff f hf hp hx)

end Array
