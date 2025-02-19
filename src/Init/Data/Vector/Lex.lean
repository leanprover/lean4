/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Array.Lex.Lemmas

namespace Vector


/-! ### Lexicographic ordering -/

@[simp] theorem lt_toArray [LT α] (l₁ l₂ : Vector α n) : l₁.toArray < l₂.toArray ↔ l₁ < l₂ := Iff.rfl
@[simp] theorem le_toArray [LT α] (l₁ l₂ : Vector α n) : l₁.toArray ≤ l₂.toArray ↔ l₁ ≤ l₂ := Iff.rfl

@[simp] theorem lt_toList [LT α] (l₁ l₂ : Vector α n) : l₁.toList < l₂.toList ↔ l₁ < l₂ := Iff.rfl
@[simp] theorem le_toList [LT α] (l₁ l₂ : Vector α n) : l₁.toList ≤ l₂.toList ↔ l₁ ≤ l₂ := Iff.rfl

protected theorem not_lt_iff_ge [LT α] (l₁ l₂ : Vector α n) : ¬ l₁ < l₂ ↔ l₂ ≤ l₁ := Iff.rfl
protected theorem not_le_iff_gt [DecidableEq α] [LT α] [DecidableLT α] (l₁ l₂ : Vector α n) :
    ¬ l₁ ≤ l₂ ↔ l₂ < l₁ :=
  Decidable.not_not

@[simp] theorem mk_lt_mk [LT α] :
    Vector.mk (α := α) (n := n) data₁ size₁ < Vector.mk data₂ size₂ ↔ data₁ < data₂ := Iff.rfl

@[simp] theorem mk_le_mk [LT α] :
    Vector.mk (α := α) (n := n) data₁ size₁ ≤ Vector.mk data₂ size₂ ↔ data₁ ≤ data₂ := Iff.rfl

@[simp] theorem mk_lex_mk [BEq α] (lt : α → α → Bool) {l₁ l₂ : Array α} {n₁ : l₁.size = n} {n₂ : l₂.size = n} :
    (Vector.mk l₁ n₁).lex (Vector.mk l₂ n₂) lt = l₁.lex l₂ lt := by
  simp [Vector.lex, Array.lex, n₁, n₂]
  rfl

@[simp] theorem lex_toArray [BEq α] (lt : α → α → Bool) (l₁ l₂ : Vector α n) :
    l₁.toArray.lex l₂.toArray lt = l₁.lex l₂ lt := by
  cases l₁
  cases l₂
  simp

@[simp] theorem lex_toList [BEq α] (lt : α → α → Bool) (l₁ l₂ : Vector α n) :
    l₁.toList.lex l₂.toList lt = l₁.lex l₂ lt := by
  rcases l₁ with ⟨⟨l₁⟩, n₁⟩
  rcases l₂ with ⟨⟨l₂⟩, n₂⟩
  simp

@[simp] theorem lex_empty
    [BEq α] {lt : α → α → Bool} (l₁ : Vector α 0) : l₁.lex #v[] lt = false := by
  cases l₁
  simp_all

@[simp] theorem singleton_lex_singleton [BEq α] {lt : α → α → Bool} : #v[a].lex #v[b] lt = lt a b := by
  simp only [lex, getElem_mk, List.getElem_toArray, List.getElem_singleton]
  cases lt a b <;> cases a != b <;> simp [Id.run]

protected theorem lt_irrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] (l : Vector α n) : ¬ l < l :=
  Array.lt_irrefl l.toArray

instance ltIrrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Irrefl (α := Vector α n) (· < ·) where
  irrefl := Vector.lt_irrefl

@[simp] theorem not_lt_empty [LT α] (l : Vector α 0) : ¬ l < #v[] := Array.not_lt_empty l.toArray
@[simp] theorem empty_le [LT α] (l : Vector α 0) : #v[] ≤ l := Array.empty_le l.toArray

@[simp] theorem le_empty [LT α] (l : Vector α 0) : l ≤ #v[] ↔ l = #v[] := by
  cases l
  simp

protected theorem le_refl [LT α] [i₀ : Std.Irrefl (· < · : α → α → Prop)] (l : Vector α n) : l ≤ l :=
  Array.le_refl l.toArray

instance [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Refl (· ≤ · : Vector α n → Vector α n → Prop) where
  refl := Vector.le_refl

protected theorem lt_trans [LT α]
    [i₁ : Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
    {l₁ l₂ l₃ : Vector α n} (h₁ : l₁ < l₂) (h₂ : l₂ < l₃) : l₁ < l₃ :=
  Array.lt_trans h₁ h₂

instance [LT α]
    [Trans (· < · : α → α → Prop) (· < ·) (· < ·)] :
    Trans (· < · : Vector α n → Vector α n → Prop) (· < ·) (· < ·) where
  trans h₁ h₂ := Vector.lt_trans h₁ h₂

protected theorem lt_of_le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i₀ : Std.Irrefl (· < · : α → α → Prop)]
    [i₁ : Std.Asymm (· < · : α → α → Prop)]
    [i₂ : Std.Antisymm (¬ · < · : α → α → Prop)]
    [i₃ : Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {l₁ l₂ l₃ : Vector α n} (h₁ : l₁ ≤ l₂) (h₂ : l₂ < l₃) : l₁ < l₃ :=
  Array.lt_of_le_of_lt h₁ h₂

protected theorem le_trans [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {l₁ l₂ l₃ : Vector α n} (h₁ : l₁ ≤ l₂) (h₂ : l₂ ≤ l₃) : l₁ ≤ l₃ :=
  fun h₃ => h₁ (Vector.lt_of_le_of_lt h₂ h₃)

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)] :
    Trans (· ≤ · : Vector α n → Vector α n → Prop) (· ≤ ·) (· ≤ ·) where
  trans h₁ h₂ := Vector.le_trans h₁ h₂

protected theorem lt_asymm [LT α]
    [i : Std.Asymm (· < · : α → α → Prop)]
    {l₁ l₂ : Vector α n} (h : l₁ < l₂) : ¬ l₂ < l₁ := Array.lt_asymm h

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Asymm (· < · : α → α → Prop)] :
    Std.Asymm (· < · : Vector α n → Vector α n → Prop) where
  asymm _ _ := Vector.lt_asymm

protected theorem le_total [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)] (l₁ l₂ : Vector α n) : l₁ ≤ l₂ ∨ l₂ ≤ l₁ :=
  Array.le_total _ _

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Total (¬ · < · : α → α → Prop)] :
    Std.Total (· ≤ · : Vector α n → Vector α n → Prop) where
  total := Vector.le_total

@[simp] protected theorem not_lt [LT α]
    {l₁ l₂ : Vector α n} : ¬ l₁ < l₂ ↔ l₂ ≤ l₁ := Iff.rfl

@[simp] protected theorem not_le [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : Vector α n} : ¬ l₂ ≤ l₁ ↔ l₁ < l₂ := Decidable.not_not

protected theorem le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)]
    {l₁ l₂ : Vector α n} (h : l₁ < l₂) : l₁ ≤ l₂ :=
  Array.le_of_lt h

protected theorem le_iff_lt_or_eq [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Total (¬ · < · : α → α → Prop)]
    {l₁ l₂ : Vector α n} : l₁ ≤ l₂ ↔ l₁ < l₂ ∨ l₁ = l₂ := by
  simpa using Array.le_iff_lt_or_eq (xs := l₁.toArray) (ys := l₂.toArray)

@[simp] theorem lex_eq_true_iff_lt [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : Vector α n} : lex l₁ l₂ = true ↔ l₁ < l₂ := by
  cases l₁
  cases l₂
  simp

@[simp] theorem lex_eq_false_iff_ge [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : Vector α n} : lex l₁ l₂ = false ↔ l₂ ≤ l₁ := by
  cases l₁
  cases l₂
  simp [Array.not_lt_iff_ge]

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLT (Vector α n) :=
  fun l₁ l₂ => decidable_of_iff (lex l₁ l₂ = true) lex_eq_true_iff_lt

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLE (Vector α n) :=
  fun l₁ l₂ => decidable_of_iff (lex l₂ l₁ = false) lex_eq_false_iff_ge

/--
`l₁` is lexicographically less than `l₂` if either
- `l₁` is pairwise equivalent under `· == ·` to `l₂.take l₁.size`,
  and `l₁` is shorter than `l₂` or
- there exists an index `i` such that
  - for all `j < i`, `l₁[j] == l₂[j]` and
  - `l₁[i] < l₂[i]`
-/
theorem lex_eq_true_iff_exists [BEq α] (lt : α → α → Bool) {l₁ l₂ : Vector α n} :
    lex l₁ l₂ lt = true ↔
      (∃ (i : Nat) (h : i < n), (∀ j, (hj : j < i) → l₁[j] == l₂[j]) ∧ lt l₁[i] l₂[i]) := by
  rcases l₁ with ⟨l₁, n₁⟩
  rcases l₂ with ⟨l₂, n₂⟩
  simp [Array.lex_eq_true_iff_exists, n₁, n₂]

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
    (lt_antisymm : ∀ x y, lt x y = false → lt y x = false → x == y)
    {l₁ l₂ : Vector α n} :
    lex l₁ l₂ lt = false ↔
      (l₂.isEqv l₁ (· == ·)) ∨
        (∃ (i : Nat) (h : i < n),(∀ j, (hj : j < i) → l₁[j] == l₂[j]) ∧ lt l₂[i] l₁[i]) := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, n₂⟩
  simp_all [Array.lex_eq_false_iff_exists, n₂]

protected theorem lt_iff_exists [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : Vector α n} :
    l₁ < l₂ ↔
      (∃ (i : Nat) (h : i < n), (∀ j, (hj : j < i) → l₁[j] = l₂[j]) ∧ l₁[i] < l₂[i]) := by
  cases l₁
  cases l₂
  simp_all [Array.lt_iff_exists]

protected theorem le_iff_exists [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)] {l₁ l₂ : Vector α n} :
    l₁ ≤ l₂ ↔
      (l₁ = l₂) ∨
        (∃ (i : Nat) (h : i < n), (∀ j, (hj : j < i) → l₁[j] = l₂[j]) ∧ l₁[i] < l₂[i]) := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, n₂⟩
  simp [Array.le_iff_exists, ← n₂]

theorem append_left_lt [LT α] {l₁ : Vector α n} {l₂ l₃ : Vector α m} (h : l₂ < l₃) :
    l₁ ++ l₂ < l₁ ++ l₃ := by
  simpa using Array.append_left_lt h

theorem append_left_le [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    {l₁ : Vector α n} {l₂ l₃ : Vector α m} (h : l₂ ≤ l₃) :
    l₁ ++ l₂ ≤ l₁ ++ l₃ := by
  simpa using Array.append_left_le h

protected theorem map_lt [LT α] [LT β]
    {l₁ l₂ : Vector α n} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ < l₂) :
    map f l₁ < map f l₂ := by
  simpa using Array.map_lt w h

protected theorem map_le [DecidableEq α] [LT α] [DecidableLT α] [DecidableEq β] [LT β] [DecidableLT β]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Irrefl (· < · : β → β → Prop)]
    [Std.Asymm (· < · : β → β → Prop)]
    [Std.Antisymm (¬ · < · : β → β → Prop)]
    {l₁ l₂ : Vector α n} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ ≤ l₂) :
    map f l₁ ≤ map f l₂ := by
  simpa using Array.map_le w h

end Vector
