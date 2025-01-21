/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Lex

namespace Array

/-! ### Lexicographic ordering -/

@[simp] theorem _root_.List.lt_toArray [LT α] (l₁ l₂ : List α) : l₁.toArray < l₂.toArray ↔ l₁ < l₂ := Iff.rfl
@[simp] theorem _root_.List.le_toArray [LT α] (l₁ l₂ : List α) : l₁.toArray ≤ l₂.toArray ↔ l₁ ≤ l₂ := Iff.rfl

@[simp] theorem lt_toList [LT α] (l₁ l₂ : Array α) : l₁.toList < l₂.toList ↔ l₁ < l₂ := Iff.rfl
@[simp] theorem le_toList [LT α] (l₁ l₂ : Array α) : l₁.toList ≤ l₂.toList ↔ l₁ ≤ l₂ := Iff.rfl

protected theorem not_lt_iff_ge [LT α] (l₁ l₂ : List α) : ¬ l₁ < l₂ ↔ l₂ ≤ l₁ := Iff.rfl
protected theorem not_le_iff_gt [DecidableEq α] [LT α] [DecidableLT α] (l₁ l₂ : List α) :
    ¬ l₁ ≤ l₂ ↔ l₂ < l₁ :=
  Decidable.not_not

@[simp] theorem lex_empty [BEq α] {lt : α → α → Bool} (l : Array α) : l.lex #[] lt = false := by
  simp [lex, Id.run]

@[simp] theorem singleton_lex_singleton [BEq α] {lt : α → α → Bool} : #[a].lex #[b] lt = lt a b := by
  simp only [lex, List.getElem_toArray, List.getElem_singleton]
  cases lt a b <;> cases a != b <;> simp [Id.run]

private theorem cons_lex_cons [BEq α] {lt : α → α → Bool} {a b : α} {xs ys : Array α} :
     (#[a] ++ xs).lex (#[b] ++ ys) lt =
       (lt a b || a == b && xs.lex ys lt) := by
  simp only [lex, Id.run]
  simp only [Std.Range.forIn'_eq_forIn'_range', size_append, size_toArray, List.length_singleton,
    Nat.add_comm 1]
  simp [Nat.add_min_add_right, List.range'_succ, getElem_append_left, List.range'_succ_left,
    getElem_append_right]
  cases lt a b
  · rw [bne]
    cases a == b <;> simp
  · simp

@[simp] theorem _root_.List.lex_toArray [BEq α] (lt : α → α → Bool) (l₁ l₂ : List α) :
    l₁.toArray.lex l₂.toArray lt = l₁.lex l₂ lt := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [lex, Id.run]
  | cons x l₁ ih =>
    cases l₂ with
    | nil => simp [lex, Id.run]
    | cons y l₂ =>
      rw [List.toArray_cons, List.toArray_cons y, cons_lex_cons, List.lex, ih]

@[simp] theorem lex_toList [BEq α] (lt : α → α → Bool) (l₁ l₂ : Array α) :
    l₁.toList.lex l₂.toList lt = l₁.lex l₂ lt := by
  cases l₁ <;> cases l₂ <;> simp

protected theorem lt_irrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] (l : Array α) : ¬ l < l :=
  List.lt_irrefl l.toList

instance ltIrrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Irrefl (α := Array α) (· < ·) where
  irrefl := Array.lt_irrefl

@[simp] theorem not_lt_empty [LT α] (l : Array α) : ¬ l < #[] := List.not_lt_nil l.toList
@[simp] theorem empty_le [LT α] (l : Array α) : #[] ≤ l := List.nil_le l.toList

@[simp] theorem le_empty [LT α] (l : Array α) : l ≤ #[] ↔ l = #[] := by
  cases l
  simp

@[simp] theorem empty_lt_push [LT α] (l : Array α) (a : α) : #[] < l.push a := by
  rcases l with (_ | ⟨x, l⟩) <;> simp

protected theorem le_refl [LT α] [i₀ : Std.Irrefl (· < · : α → α → Prop)] (l : Array α) : l ≤ l :=
  List.le_refl l.toList

instance [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Refl (· ≤ · : Array α → Array α → Prop) where
  refl := Array.le_refl

protected theorem lt_trans [LT α]
    [i₁ : Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
    {l₁ l₂ l₃ : Array α} (h₁ : l₁ < l₂) (h₂ : l₂ < l₃) : l₁ < l₃ :=
  List.lt_trans h₁ h₂

instance [LT α] [Trans (· < · : α → α → Prop) (· < ·) (· < ·)] :
    Trans (· < · : Array α → Array α → Prop) (· < ·) (· < ·) where
  trans h₁ h₂ := Array.lt_trans h₁ h₂

protected theorem lt_of_le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i₀ : Std.Irrefl (· < · : α → α → Prop)]
    [i₁ : Std.Asymm (· < · : α → α → Prop)]
    [i₂ : Std.Antisymm (¬ · < · : α → α → Prop)]
    [i₃ : Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {l₁ l₂ l₃ : Array α} (h₁ : l₁ ≤ l₂) (h₂ : l₂ < l₃) : l₁ < l₃ :=
  List.lt_of_le_of_lt h₁ h₂

protected theorem le_trans [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {l₁ l₂ l₃ : Array α} (h₁ : l₁ ≤ l₂) (h₂ : l₂ ≤ l₃) : l₁ ≤ l₃ :=
  fun h₃ => h₁ (Array.lt_of_le_of_lt h₂ h₃)

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)] :
    Trans (· ≤ · : Array α → Array α → Prop) (· ≤ ·) (· ≤ ·) where
  trans h₁ h₂ := Array.le_trans h₁ h₂

protected theorem lt_asymm [LT α]
    [i : Std.Asymm (· < · : α → α → Prop)]
    {l₁ l₂ : Array α} (h : l₁ < l₂) : ¬ l₂ < l₁ := List.lt_asymm h

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Asymm (· < · : α → α → Prop)] :
    Std.Asymm (· < · : Array α → Array α → Prop) where
  asymm _ _ := Array.lt_asymm

protected theorem le_total [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)] (l₁ l₂ : Array α) : l₁ ≤ l₂ ∨ l₂ ≤ l₁ :=
  List.le_total _ _

@[simp] protected theorem not_lt [LT α]
    {l₁ l₂ : Array α} : ¬ l₁ < l₂ ↔ l₂ ≤ l₁ := Iff.rfl

@[simp] protected theorem not_le [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : Array α} : ¬ l₂ ≤ l₁ ↔ l₁ < l₂ := Decidable.not_not

protected theorem le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)]
    {l₁ l₂ : Array α} (h : l₁ < l₂) : l₁ ≤ l₂ :=
  List.le_of_lt h

protected theorem le_iff_lt_or_eq [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Total (¬ · < · : α → α → Prop)]
    {l₁ l₂ : Array α} : l₁ ≤ l₂ ↔ l₁ < l₂ ∨ l₁ = l₂ := by
  simpa using List.le_iff_lt_or_eq (l₁ := l₁.toList) (l₂ := l₂.toList)

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Total (¬ · < · : α → α → Prop)] :
    Std.Total (· ≤ · : Array α → Array α → Prop) where
  total := Array.le_total

@[simp] theorem lex_eq_true_iff_lt [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : Array α} : lex l₁ l₂ = true ↔ l₁ < l₂ := by
  cases l₁
  cases l₂
  simp

@[simp] theorem lex_eq_false_iff_ge [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : Array α} : lex l₁ l₂ = false ↔ l₂ ≤ l₁ := by
  cases l₁
  cases l₂
  simp [List.not_lt_iff_ge]

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLT (Array α) :=
  fun l₁ l₂ => decidable_of_iff (lex l₁ l₂ = true) lex_eq_true_iff_lt

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLE (Array α) :=
  fun l₁ l₂ => decidable_of_iff (lex l₂ l₁ = false) lex_eq_false_iff_ge

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
- `lt` is asymmmetric  (i.e. `lt x y = true → lt y x = false`)
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

protected theorem lt_iff_exists [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : Array α} :
    l₁ < l₂ ↔
      (l₁ = l₂.take l₁.size ∧ l₁.size < l₂.size) ∨
        (∃ (i : Nat) (h₁ : i < l₁.size) (h₂ : i < l₂.size),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) = l₂[j]'(Nat.lt_trans hj h₂)) ∧ l₁[i] < l₂[i]) := by
  cases l₁
  cases l₂
  simp [List.lt_iff_exists]

protected theorem le_iff_exists [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)] {l₁ l₂ : Array α} :
    l₁ ≤ l₂ ↔
      (l₁ = l₂.take l₁.size) ∨
        (∃ (i : Nat) (h₁ : i < l₁.size) (h₂ : i < l₂.size),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) = l₂[j]'(Nat.lt_trans hj h₂)) ∧ l₁[i] < l₂[i]) := by
  cases l₁
  cases l₂
  simp [List.le_iff_exists]

theorem append_left_lt [LT α] {l₁ l₂ l₃ : Array α} (h : l₂ < l₃) :
    l₁ ++ l₂ < l₁ ++ l₃ := by
  cases l₁
  cases l₂
  cases l₃
  simpa using List.append_left_lt h

theorem append_left_le [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    {l₁ l₂ l₃ : Array α} (h : l₂ ≤ l₃) :
    l₁ ++ l₂ ≤ l₁ ++ l₃ := by
  cases l₁
  cases l₂
  cases l₃
  simpa using List.append_left_le h

theorem le_append_left [LT α] [Std.Irrefl (· < · : α → α → Prop)]
    {l₁ l₂ : Array α} : l₁ ≤ l₁ ++ l₂ := by
  cases l₁
  cases l₂
  simpa using List.le_append_left

protected theorem map_lt [LT α] [LT β]
    {l₁ l₂ : Array α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ < l₂) :
    map f l₁ < map f l₂ := by
  cases l₁
  cases l₂
  simpa using List.map_lt w h

protected theorem map_le [DecidableEq α] [LT α] [DecidableLT α] [DecidableEq β] [LT β] [DecidableLT β]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Irrefl (· < · : β → β → Prop)]
    [Std.Asymm (· < · : β → β → Prop)]
    [Std.Antisymm (¬ · < · : β → β → Prop)]
    {l₁ l₂ : Array α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ ≤ l₂) :
    map f l₁ ≤ map f l₂ := by
  cases l₁
  cases l₂
  simpa using List.map_le w h

end Array
