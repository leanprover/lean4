/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.Order.Lemmas
public import Init.Data.Order.Opposite

/-! ## Definitions -/

/--
Returns either `x` or `y`, the one with the smaller value under `f`.

If `f x ≤ f y`, it returns `x`, and otherwise returns `y`.
-/
public def minOn [LE β] [DecidableLE β] (f : α → β) (x y : α) :=
  if f x ≤ f y then x else y


/--
Returns either `x` or `y`, the one with the greater value under `f`.

If `f x ≤ f y`, it returns `x`, and otherwise returns `y`.
-/
public def maxOn [i : LE β] [DecidableLE β] (f : α → β) (x y : α) :=
  letI := i.opposite
  minOn f x y

/-! ## `minOn` Lemmas -/

public theorem minOn_eq_or [LE β] [DecidableLE β] {f : α → β} {x y : α} :
    minOn f x y = x ∨ minOn f x y = y := by
  rw [minOn]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp, grind =]
public theorem minOn_self [LE β] [DecidableLE β] {f : α → β} {x : α} :
    minOn f x x = x := by
  cases minOn_eq_or (f := f) (x := x) (y := x) <;> assumption

@[grind =]
public theorem minOn_eq_left [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : f x ≤ f y) :
    minOn f x y = x := by
  simp [minOn, h]

@[grind =]
public theorem minOn_eq_right [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : ¬ f x ≤ f y) :
    minOn f x y = y := by
  simp [minOn, h]

public theorem minOn_eq_right_of_lt
    [LE β] [DecidableLE β] [LT β] [Std.Total (α := β) (· ≤ ·)] [Std.LawfulOrderLT β]
    {f : α → β} {x y : α} (h : f y < f x) :
    minOn f x y = y := by
  apply minOn_eq_right
  simpa [Std.not_le] using h

@[grind =>]
public theorem apply_minOn_le_left [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f (minOn f x y) ≤ f x := by
  rw [minOn]
  split
  · apply Std.le_refl
  · exact Std.le_of_not_ge ‹_›

@[grind =>]
public theorem apply_minOn_le_right [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f (minOn f x y) ≤ f y := by
  rw [minOn]
  split
  · assumption
  · apply Std.le_refl

public theorem le_apply_minOn_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} {b : β} :
    b ≤ f (minOn f x y) ↔ b ≤ f x ∧ b ≤ f y := by
  apply Iff.intro
  · intro h
    exact ⟨Std.le_trans h apply_minOn_le_left, Std.le_trans h apply_minOn_le_right⟩
  · intro h
    cases minOn_eq_or (f := f) (x := x) (y := y) <;> simp_all

@[grind =]
public theorem minOn_assoc [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y z : α} : minOn f (minOn f x y) z = minOn f x (minOn f y z) := by
  open scoped Classical.Order in
  simp only [minOn]
  split
  · split
    · split
      · rfl
      · rfl
    · split
      · have : ¬ f x ≤ f z := by assumption
        have : f x ≤ f z := Std.le_trans ‹f x ≤ f y› ‹f y ≤ f z›
        contradiction
      · rfl
  · split
    · rfl
    · have : f z < f y := Std.not_le.mp ‹¬ f y ≤ f z›
      have : f y < f x := Std.not_le.mp ‹¬ f x ≤ f y›
      have : f z < f x := Std.lt_trans ‹_› ‹_›
      rw [if_neg]
      exact Std.not_le.mpr ‹_›

public instance [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} :
    Std.Associative (minOn f) where
  assoc := by apply minOn_assoc

public theorem min_apply [LE β] [DecidableLE β] [Min β] [Std.LawfulOrderLeftLeaningMin β]
    {f : α → β} {x y : α} : min (f x) (f y) = f (minOn f x y) := by
  rw [Std.min_eq_if, minOn]
  split <;> rfl

/-! ## `maxOn` Lemmas -/

public theorem maxOn_eq_or [LE β] [DecidableLE β] {f : α → β} {x y : α} :
    maxOn f x y = x ∨ maxOn f x y = y :=
  @minOn_eq_or ..

@[simp, grind =]
public theorem maxOn_self [LE β] [DecidableLE β] {f : α → β} {x : α} :
    maxOn f x x = x :=
  @minOn_self ..

@[grind =]
public theorem maxOn_eq_left [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : f y ≤ f x) :
    maxOn f x y = x :=
  @minOn_eq_left (h := h) ..

@[grind =]
public theorem maxOn_eq_right [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : ¬ f y ≤ f x) :
    maxOn f x y = y :=
  @minOn_eq_right (h := h) ..

public theorem maxOn_eq_right_of_lt
    [LE β] [DecidableLE β] [LT β] [Std.Total (α := β) (· ≤ ·)] [Std.LawfulOrderLT β]
    {f : α → β} {x y : α} (h : f x < f y) :
    maxOn f x y = y :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : LT β := (inferInstanceAs (LT β)).opposite
  minOn_eq_right_of_lt (h := h) ..

@[grind =>]
public theorem left_le_apply_maxOn [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f x ≤ f (maxOn f x y) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  apply_minOn_le_left (f := f)

@[grind =>]
public theorem right_le_apply_maxOn [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f y ≤ f (maxOn f x y) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  apply_minOn_le_right (f := f)

public theorem apply_maxOn_le_iff [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} {b : β} :
    f (maxOn f x y) ≤ b ↔ f x ≤ b ∧ f y ≤ b :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  le_apply_minOn_iff (f := f)

@[grind =]
public theorem maxOn_assoc [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y z : α} : maxOn f (maxOn f x y) z = maxOn f x (maxOn f y z) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  minOn_assoc (f := f)

public instance [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β} :
    Std.Associative (maxOn f) where
  assoc := by
    apply maxOn_assoc

public theorem max_apply [LE β] [DecidableLE β] [Max β] [Std.LawfulOrderLeftLeaningMax β]
    {f : α → β} {x y : α} : max (f x) (f y) = f (maxOn f x y) :=
  letI : LE β := (inferInstanceAs (LE β)).opposite
  letI : Min β := (inferInstanceAs (Max β)).oppositeMin
  min_apply (f := f)

public theorem apply_maxOn [LE β] [DecidableLE β] [Max β] [Std.LawfulOrderLeftLeaningMax β]
    {f : α → β} {x y : α} : f (maxOn f x y) = max (f x) (f y) :=
  max_apply.symm
