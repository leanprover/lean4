/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Lemmas
import Init.Data.List.Nat.TakeDrop

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/-! ### Lexicographic ordering -/

@[simp] theorem lex_lt [LT α] (l₁ l₂ : List α) : Lex (· < ·) l₁ l₂ ↔ l₁ < l₂ := Iff.rfl
@[simp] theorem not_lex_lt [LT α] (l₁ l₂ : List α) : ¬ Lex (· < ·) l₁ l₂ ↔ l₂ ≤ l₁ := Iff.rfl

protected theorem not_lt_iff_ge [LT α] (l₁ l₂ : List α) : ¬ l₁ < l₂ ↔ l₂ ≤ l₁ := Iff.rfl
protected theorem not_le_iff_gt [DecidableEq α] [LT α] [DecidableLT α] (l₁ l₂ : List α) :
    ¬ l₁ ≤ l₂ ↔ l₂ < l₁ :=
  Decidable.not_not

theorem lex_irrefl {r : α → α → Prop} (irrefl : ∀ x, ¬r x x) (l : List α) : ¬Lex r l l := by
  induction l with
  | nil => nofun
  | cons a l ih => intro
    | .rel h => exact irrefl _ h
    | .cons h => exact ih h

protected theorem lt_irrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] (l : List α) : ¬ l < l :=
  lex_irrefl Std.Irrefl.irrefl l

instance ltIrrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Irrefl (α := List α) (· < ·) where
  irrefl := List.lt_irrefl

@[simp] theorem not_lex_nil : ¬Lex r l [] := fun h => nomatch h

@[simp] theorem not_lt_nil [LT α] (l : List α) : ¬ l < [] := fun h => nomatch h
@[simp] theorem nil_le [LT α] (l : List α) : [] ≤ l := fun h => nomatch h

@[simp] theorem not_nil_lex_iff : ¬Lex r [] l ↔ l = [] := by
  constructor
  · rintro h
    match l, h with
    | [], h => rfl
    | a :: _, h => exact False.elim (h Lex.nil)
  · rintro rfl
    exact not_lex_nil

@[simp] theorem le_nil [LT α] (l : List α) : l ≤ [] ↔ l = [] := not_nil_lex_iff

-- This is named with a prime to avoid conflict with `lex [] (b :: bs) lt = true`.
-- Better naming for the `Lex` vs `lex` distinction would be welcome.
@[simp] theorem nil_lex_cons' : Lex r [] (a :: l) := Lex.nil

@[simp] theorem nil_lt_cons [LT α] (a : α) (l : List α) : [] < a :: l := Lex.nil

theorem cons_lex_cons_iff : Lex r (a :: l₁) (b :: l₂) ↔ r a b ∨ a = b ∧ Lex r l₁ l₂ :=
  ⟨fun | .rel h => .inl h | .cons h => .inr ⟨rfl, h⟩,
    fun | .inl h => Lex.rel h | .inr ⟨rfl, h⟩ => Lex.cons h⟩

theorem cons_lt_cons_iff [LT α] {a b} {l₁ l₂ : List α} :
    (a :: l₁) < (b :: l₂) ↔ a < b ∨ a = b ∧ l₁ < l₂ := by
  dsimp only [instLT, List.lt]
  simp [cons_lex_cons_iff]

@[simp] theorem cons_lt_cons_self [LT α] [i₀ : Std.Irrefl (· < · : α → α → Prop)] {l₁ l₂ : List α} :
    (a :: l₁) < (a :: l₂) ↔ l₁ < l₂ := by
  simp [cons_lt_cons_iff, i₀.irrefl]

theorem not_cons_lex_cons_iff [DecidableEq α] [DecidableRel r] {a b} {l₁ l₂ : List α} :
    ¬ Lex r (a :: l₁) (b :: l₂) ↔ (¬ r a b ∧ a ≠ b) ∨ (¬ r a b ∧ ¬ Lex r l₁ l₂) := by
  rw [cons_lex_cons_iff, not_or, Decidable.not_and_iff_or_not, and_or_left]

theorem cons_le_cons_iff [DecidableEq α] [LT α] [DecidableLT α]
    [i₀ : Std.Irrefl (· < · : α → α → Prop)]
    [i₁ : Std.Asymm (· < · : α → α → Prop)]
    [i₂ : Std.Antisymm (¬ · < · : α → α → Prop)]
    {a b} {l₁ l₂ : List α} :
    (a :: l₁) ≤ (b :: l₂) ↔ a < b ∨ a = b ∧ l₁ ≤ l₂ := by
  dsimp only [instLE, instLT, List.le, List.lt]
  simp only [not_cons_lex_cons_iff, ne_eq]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · left
      apply Decidable.byContradiction
      intro h₃
      apply h₂
      exact i₂.antisymm _ _ h₁ h₃
    · if h₃ : a < b then
        exact .inl h₃
      else
        right
        exact ⟨i₂.antisymm _ _ h₃ h₁, h₂⟩
  · rintro (h | ⟨h₁, h₂⟩)
    · left
      exact ⟨i₁.asymm _ _ h, fun w => i₀.irrefl _ (w ▸ h)⟩
    · right
      exact ⟨fun w => i₀.irrefl _ (h₁ ▸ w), h₂⟩

theorem not_lt_of_cons_le_cons [DecidableEq α] [LT α] [DecidableLT α]
    [i₀ : Std.Irrefl (· < · : α → α → Prop)]
    [i₁ : Std.Asymm (· < · : α → α → Prop)]
    [i₂ : Std.Antisymm (¬ · < · : α → α → Prop)]
    {a b : α} {l₁ l₂ : List α} (h : a :: l₁ ≤ b :: l₂) : ¬ b < a := by
  rw [cons_le_cons_iff] at h
  rcases h with h | ⟨rfl, h⟩
  · exact i₁.asymm _ _ h
  · exact i₀.irrefl _

theorem le_of_cons_le_cons [DecidableEq α] [LT α] [DecidableLT α]
    [i₀ : Std.Irrefl (· < · : α → α → Prop)]
    [i₁ : Std.Asymm (· < · : α → α → Prop)]
    [i₂ : Std.Antisymm (¬ · < · : α → α → Prop)]
    {a} {l₁ l₂ : List α} (h : a :: l₁ ≤ a :: l₂) : l₁ ≤ l₂ := by
  rw [cons_le_cons_iff] at h
  rcases h with h | ⟨_, h⟩
  · exact False.elim (i₀.irrefl _ h)
  · exact h

protected theorem le_refl [LT α] [i₀ : Std.Irrefl (· < · : α → α → Prop)] (l : List α) : l ≤ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro
    | .rel h => exact i₀.irrefl _ h
    | .cons h₃ => exact ih h₃

instance [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Refl (· ≤ · : List α → List α → Prop) where
  refl := List.le_refl

theorem lex_trans {r : α → α → Prop}
    (lt_trans : ∀ {x y z : α}, r x y → r y z → r x z)
    (h₁ : Lex r l₁ l₂) (h₂ : Lex r l₂ l₃) : Lex r l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => let _::_ := l₃; exact List.Lex.nil ..
  | @rel a l₁ b l₂ ab =>
    match h₂ with
    | .rel bc => exact List.Lex.rel (lt_trans ab bc)
    | .cons ih =>
      exact List.Lex.rel ab
  | @cons a l₁ l₂ h₁ ih2 =>
    match h₂ with
    | .rel bc =>
      exact List.Lex.rel bc
    | .cons ih =>
      exact List.Lex.cons (ih2 ih)

protected theorem lt_trans [LT α]
    [i₁ : Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
    {l₁ l₂ l₃ : List α} (h₁ : l₁ < l₂) (h₂ : l₂ < l₃) : l₁ < l₃ := by
  simp only [instLT, List.lt] at h₁ h₂ ⊢
  exact lex_trans (fun h₁ h₂ => i₁.trans h₁ h₂) h₁ h₂

instance [LT α] [Trans (· < · : α → α → Prop) (· < ·) (· < ·)] :
    Trans (· < · : List α → List α → Prop) (· < ·) (· < ·) where
  trans h₁ h₂ := List.lt_trans h₁ h₂

@[deprecated List.le_antisymm (since := "2024-12-13")]
protected abbrev lt_antisymm := @List.le_antisymm

protected theorem lt_of_le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i₀ : Std.Irrefl (· < · : α → α → Prop)]
    [i₁ : Std.Asymm (· < · : α → α → Prop)]
    [i₂ : Std.Antisymm (¬ · < · : α → α → Prop)]
    [i₃ : Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {l₁ l₂ l₃ : List α} (h₁ : l₁ ≤ l₂) (h₂ : l₂ < l₃) : l₁ < l₃ := by
  induction h₂ generalizing l₁ with
  | nil => simp_all
  | rel hab =>
    rename_i a xs
    cases l₁ with
    | nil => simp_all
    | cons c l₁ =>
      apply Lex.rel
      replace h₁ := not_lt_of_cons_le_cons h₁
      apply Decidable.byContradiction
      intro h₂
      have := i₃.trans h₁ h₂
      contradiction
  | cons w₃ ih =>
    rename_i a as bs
    cases l₁ with
    | nil => simp_all
    | cons c l₁ =>
      have w₄ := not_lt_of_cons_le_cons h₁
      by_cases w₅ : a = c
      · subst w₅
        exact Lex.cons (ih (le_of_cons_le_cons h₁))
      · exact Lex.rel (Decidable.byContradiction fun w₆ => w₅ (i₂.antisymm _ _ w₄ w₆))

protected theorem le_trans [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {l₁ l₂ l₃ : List α} (h₁ : l₁ ≤ l₂) (h₂ : l₂ ≤ l₃) : l₁ ≤ l₃ :=
  fun h₃ => h₁ (List.lt_of_le_of_lt h₂ h₃)

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)] :
    Trans (· ≤ · : List α → List α → Prop) (· ≤ ·) (· ≤ ·) where
  trans h₁ h₂ := List.le_trans h₁ h₂

theorem lex_asymm {r : α → α → Prop}
    (h : ∀ {x y : α}, r x y → ¬ r y x) : ∀ {l₁ l₂ : List α}, Lex r l₁ l₂ → ¬ Lex r l₂ l₁
  | nil, _, .nil => by simp
  | x :: l₁, y :: l₂, .rel h₁ =>
    fun
    | .rel h₂ => h h₁ h₂
    | .cons h₂ => h h₁ h₁
  | x :: l₁, _ :: l₂, .cons h₁ =>
    fun
    | .rel h₂ => h h₂ h₂
    | .cons h₂ => lex_asymm h h₁ h₂

protected theorem lt_asymm [LT α]
    [i : Std.Asymm (· < · : α → α → Prop)]
    {l₁ l₂ : List α} (h : l₁ < l₂) : ¬ l₂ < l₁ := lex_asymm (i.asymm _ _) h

instance [LT α] [Std.Asymm (· < · : α → α → Prop)] :
    Std.Asymm (· < · : List α → List α → Prop) where
  asymm _ _ := List.lt_asymm

theorem not_lex_total [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
    (h : ∀ x y : α, ¬ r x y ∨ ¬ r y x) (l₁ l₂ : List α) : ¬ Lex r l₁ l₂ ∨ ¬ Lex r l₂ l₁ := by
  rw [Decidable.or_iff_not_imp_left, Decidable.not_not]
  intro w₁ w₂
  match l₁, l₂, w₁, w₂ with
  | nil, _ :: _, .nil, w₂ => simp at w₂
  | x :: _, y :: _, .rel _, .rel _ =>
    obtain (_ | _) := h x y <;> contradiction
  | x :: _, _ :: _, .rel _, .cons _ =>
    obtain (_ | _) := h x x <;> contradiction
  | x :: _, _ :: _, .cons  _, .rel _ =>
    obtain (_ | _) := h x x <;> contradiction
  | _ :: l₁, _ :: l₂, .cons _, .cons _ =>
    obtain (_ | _) := not_lex_total h l₁ l₂ <;> contradiction

protected theorem le_total [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)] (l₁ l₂ : List α) : l₁ ≤ l₂ ∨ l₂ ≤ l₁ :=
  not_lex_total i.total l₂ l₁

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Total (¬ · < · : α → α → Prop)] :
    Std.Total (· ≤ · : List α → List α → Prop) where
  total := List.le_total

@[simp] protected theorem not_lt [LT α]
    {l₁ l₂ : List α} : ¬ l₁ < l₂ ↔ l₂ ≤ l₁ := Iff.rfl

@[simp] protected theorem not_le [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : List α} : ¬ l₂ ≤ l₁ ↔ l₁ < l₂ := Decidable.not_not

protected theorem le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)]
    {l₁ l₂ : List α} (h : l₁ < l₂) : l₁ ≤ l₂ := by
  obtain (h' | h') := List.le_total l₁ l₂
  · exact h'
  · exfalso
    exact h' h

protected theorem le_iff_lt_or_eq [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Total (¬ · < · : α → α → Prop)]
    {l₁ l₂ : List α} : l₁ ≤ l₂ ↔ l₁ < l₂ ∨ l₁ = l₂ := by
  constructor
  · intro h
    by_cases h' : l₂ ≤ l₁
    · right
      apply List.le_antisymm h h'
    · left
      exact Decidable.not_not.mp h'
  · rintro (h | rfl)
    · exact List.le_of_lt h
    · exact List.le_refl l₁

theorem lex_eq_decide_lex [DecidableEq α] (lt : α → α → Bool) :
    lex l₁ l₂ lt = decide (Lex (fun x y => lt x y) l₁ l₂) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp [lex]
    | cons b bs => simp [lex]
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp [lex]
    | cons b bs =>
      simp [lex, ih, cons_lex_cons_iff, Bool.beq_eq_decide_eq]

/-- Variant of `lex_eq_true_iff` using an arbitrary comparator. -/
@[simp] theorem lex_eq_true_iff_lex [DecidableEq α] (lt : α → α → Bool) :
    lex l₁ l₂ lt = true ↔ Lex (fun x y => lt x y) l₁ l₂ := by
  simp [lex_eq_decide_lex]

/-- Variant of `lex_eq_false_iff` using an arbitrary comparator. -/
@[simp] theorem lex_eq_false_iff_not_lex [DecidableEq α] (lt : α → α → Bool) :
    lex l₁ l₂ lt = false ↔ ¬ Lex (fun x y => lt x y) l₁ l₂ := by
  simp [Bool.eq_false_iff, lex_eq_true_iff_lex]

@[simp] theorem lex_eq_true_iff_lt [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : List α} : lex l₁ l₂ = true ↔ l₁ < l₂ := by
  simp only [lex_eq_true_iff_lex, decide_eq_true_eq]
  exact Iff.rfl

@[simp] theorem lex_eq_false_iff_ge [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : List α} : lex l₁ l₂ = false ↔ l₂ ≤ l₁ := by
  simp only [lex_eq_false_iff_not_lex, decide_eq_true_eq]
  exact Iff.rfl

attribute [local simp] Nat.add_one_lt_add_one_iff in
/--
`l₁` is lexicographically less than `l₂` if either
- `l₁` is pairwise equivalent under `· == ·` to `l₂.take l₁.length`,
  and `l₁` is shorter than `l₂` or
- there exists an index `i` such that
  - for all `j < i`, `l₁[j] == l₂[j]` and
  - `l₁[i] < l₂[i]`
-/
theorem lex_eq_true_iff_exists [BEq α] (lt : α → α → Bool) :
    lex l₁ l₂ lt = true ↔
      (l₁.isEqv (l₂.take l₁.length) (· == ·) ∧ l₁.length < l₂.length) ∨
        (∃ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) == l₂[j]'(Nat.lt_trans hj h₂)) ∧ lt l₁[i] l₂[i]) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp [lex]
    | cons b bs => simp [lex]
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp [lex]
    | cons b l₂ =>
      simp [cons_lex_cons, Bool.or_eq_true, Bool.and_eq_true, ih, isEqv, length_cons]
      constructor
      · rintro (hab | ⟨hab, ⟨h₁, h₂⟩ | ⟨i, h₁, h₂, w₁, w₂⟩⟩)
        · exact .inr ⟨0, by simp [hab]⟩
        · exact .inl ⟨⟨hab, h₁⟩, by simpa using h₂⟩
        · refine .inr ⟨i + 1, by simp [h₁],
            by simp [h₂], ?_, ?_⟩
          · intro j hj
            cases j with
            | zero => simp [hab]
            | succ j =>
              simp only [getElem_cons_succ]
              rw [w₁]
              simpa using hj
          · simpa using w₂
      · rintro (⟨⟨h₁, h₂⟩, h₃⟩ | ⟨i, h₁, h₂, w₁, w₂⟩)
        · exact .inr ⟨h₁, .inl ⟨h₂, by simpa using h₃⟩⟩
        · cases i with
          | zero =>
            left
            simpa using w₂
          | succ i =>
            right
            refine ⟨by simpa using w₁ 0 (by simp), ?_⟩
            right
            refine ⟨i, by simpa using h₁, by simpa using h₂, ?_, ?_⟩
            · intro j hj
              simpa using w₁ (j + 1) (by simpa)
            · simpa using w₂

attribute [local simp] Nat.add_one_lt_add_one_iff in
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
- `lt` is asymmmetric  (i.e. `lt x y = true → lt y x = false`)
- `lt` is antisymmetric with respect to `==` (i.e. `lt x y = false → lt y x = false → x == y`)
-/
theorem lex_eq_false_iff_exists [BEq α] [PartialEquivBEq α] (lt : α → α → Bool)
    (lt_irrefl : ∀ x y, x == y → lt x y = false)
    (lt_asymm : ∀ x y, lt x y = true → lt y x = false)
    (lt_antisymm : ∀ x y, lt x y = false → lt y x = false → x == y) :
    lex l₁ l₂ lt = false ↔
      (l₂.isEqv (l₁.take l₂.length) (· == ·)) ∨
        (∃ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) == l₂[j]'(Nat.lt_trans hj h₂)) ∧ lt l₂[i] l₁[i]) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp [lex]
    | cons b bs => simp [lex]
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp [lex]
    | cons b l₂ =>
      simp [cons_lex_cons, Bool.or_eq_false_iff, Bool.and_eq_false_imp, ih, isEqv,
        Bool.and_eq_true, length_cons]
      constructor
      · rintro ⟨hab, h⟩
        if eq : b == a then
          specialize h (BEq.symm eq)
          obtain (h | ⟨i, h₁, h₂, w₁, w₂⟩) := h
          · exact .inl ⟨eq, h⟩
          · refine .inr ⟨i + 1, by simpa using h₁, by simpa using h₂, ?_, ?_⟩
            · intro j hj
              cases j with
              | zero => simpa using BEq.symm eq
              | succ j =>
                simp only [getElem_cons_succ]
                rw [w₁]
                simpa using hj
            · simpa using w₂
        else
          right
          have hba : lt b a :=
            Decidable.byContradiction fun hba => eq (lt_antisymm _ _ (by simpa using hba) hab)
          exact ⟨0, by simp, by simp, by simpa⟩
      · rintro (⟨eq, h⟩ | ⟨i, h₁, h₂, w₁, w₂⟩)
        · exact ⟨lt_irrefl _ _ (BEq.symm eq), fun _ => .inl h⟩
        · cases i with
          | zero =>
            simp at w₂
            refine ⟨lt_asymm _ _ w₂, ?_⟩
            intro eq
            exfalso
            simp [lt_irrefl _ _ (BEq.symm eq)] at w₂
          | succ i =>
            refine ⟨lt_irrefl _ _ (by simpa using w₁ 0 (by simp)), ?_⟩
            refine fun _ => .inr ⟨i, by simpa using h₁, by simpa using h₂, ?_, ?_⟩
            · intro j hj
              simpa using w₁ (j + 1) (by simpa)
            · simpa using w₂

protected theorem lt_iff_exists [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : List α} :
    l₁ < l₂ ↔
      (l₁ = l₂.take l₁.length ∧ l₁.length < l₂.length) ∨
        (∃ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) = l₂[j]'(Nat.lt_trans hj h₂)) ∧ l₁[i] < l₂[i]) := by
  rw [← lex_eq_true_iff_lt, lex_eq_true_iff_exists]
  simp

protected theorem le_iff_exists [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)] {l₁ l₂ : List α} :
    l₁ ≤ l₂ ↔
      (l₁ = l₂.take l₁.length) ∨
        (∃ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) = l₂[j]'(Nat.lt_trans hj h₂)) ∧ l₁[i] < l₂[i]) := by
  rw [← lex_eq_false_iff_ge, lex_eq_false_iff_exists]
  · simp only [isEqv_eq, beq_iff_eq, decide_eq_true_eq]
    simp only [eq_comm]
    conv => lhs; simp +singlePass [exists_comm]
  · simpa using Std.Irrefl.irrefl
  · simpa using Std.Asymm.asymm
  · simpa using Std.Antisymm.antisymm

theorem append_left_lt [LT α] {l₁ l₂ l₃ : List α} (h : l₂ < l₃) :
    l₁ ++ l₂ < l₁ ++ l₃ := by
  induction l₁ with
  | nil => simp [h]
  | cons a l₁ ih => simp [cons_lt_cons_iff, ih]

theorem append_left_le [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    {l₁ l₂ l₃ : List α} (h : l₂ ≤ l₃) :
    l₁ ++ l₂ ≤ l₁ ++ l₃ := by
  induction l₁ with
  | nil => simp [h]
  | cons a l₁ ih => simp [cons_le_cons_iff, ih]

theorem le_append_left [LT α] [Std.Irrefl (· < · : α → α → Prop)]
    {l₁ l₂ : List α} : l₁ ≤ l₁ ++ l₂ := by
  intro h
  match l₁, h with
  | nil, h => simp at h
  | cons a l₁, h => exact le_append_left (by simpa using h)

theorem IsPrefix.le [LT α] [Std.Irrefl (· < · : α → α → Prop)]
    {l₁ l₂ : List α} (h : l₁ <+: l₂) : l₁ ≤ l₂ := by
  rcases h with ⟨_, rfl⟩
  apply le_append_left

protected theorem map_lt [LT α] [LT β]
    {l₁ l₂ : List α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ < l₂) :
    map f l₁ < map f l₂ := by
  match l₁, l₂, h with
  | nil, nil, h => simp at h
  | nil, cons b l₂, h => simp
  | cons a l₁, nil, h => simp at h
  | cons a l₁, cons _ l₂, .cons h =>
    simp [cons_lt_cons_iff, List.map_lt w (by simpa using h)]
  | cons a l₁, cons b l₂, .rel h =>
    simp [cons_lt_cons_iff, w, h]

protected theorem map_le [DecidableEq α] [LT α] [DecidableLT α] [DecidableEq β] [LT β] [DecidableLT β]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Irrefl (· < · : β → β → Prop)]
    [Std.Asymm (· < · : β → β → Prop)]
    [Std.Antisymm (¬ · < · : β → β → Prop)]
    {l₁ l₂ : List α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ ≤ l₂) :
    map f l₁ ≤ map f l₂ := by
  rw [List.le_iff_exists] at h ⊢
  obtain (h | ⟨i, h₁, h₂, w₁, w₂⟩) := h
  · left
    rw [h]
    simp
  · right
    refine ⟨i, by simpa using h₁, by simpa using h₂, ?_, ?_⟩
    · simp +contextual [w₁]
    · simpa using w _ _ w₂

end List
