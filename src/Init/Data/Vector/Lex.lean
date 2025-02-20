/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Array.Lex.Lemmas

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector


/-! ### Lexicographic ordering -/

@[simp] theorem lt_toArray [LT α] (xs ys : Vector α n) : xs.toArray < ys.toArray ↔ xs < ys := Iff.rfl
@[simp] theorem le_toArray [LT α] (xs ys : Vector α n) : xs.toArray ≤ ys.toArray ↔ xs ≤ ys := Iff.rfl

@[simp] theorem lt_toList [LT α] (xs ys : Vector α n) : xs.toList < ys.toList ↔ xs < ys := Iff.rfl
@[simp] theorem le_toList [LT α] (xs ys : Vector α n) : xs.toList ≤ ys.toList ↔ xs ≤ ys := Iff.rfl

protected theorem not_lt_iff_ge [LT α] (xs ys : Vector α n) : ¬ xs < ys ↔ ys ≤ xs := Iff.rfl
protected theorem not_le_iff_gt [DecidableEq α] [LT α] [DecidableLT α] (xs ys : Vector α n) :
    ¬ xs ≤ ys ↔ ys < xs :=
  Decidable.not_not

@[simp] theorem mk_lt_mk [LT α] :
    Vector.mk (α := α) (n := n) data₁ size₁ < Vector.mk data₂ size₂ ↔ data₁ < data₂ := Iff.rfl

@[simp] theorem mk_le_mk [LT α] :
    Vector.mk (α := α) (n := n) data₁ size₁ ≤ Vector.mk data₂ size₂ ↔ data₁ ≤ data₂ := Iff.rfl

@[simp] theorem mk_lex_mk [BEq α] (lt : α → α → Bool) {xs ys : Array α} {n₁ : xs.size = n} {n₂ : ys.size = n} :
    (Vector.mk xs n₁).lex (Vector.mk ys n₂) lt = xs.lex ys lt := by
  simp [Vector.lex, Array.lex, n₁, n₂]
  rfl

@[simp] theorem lex_toArray [BEq α] (lt : α → α → Bool) (xs ys : Vector α n) :
    xs.toArray.lex ys.toArray lt = xs.lex ys lt := by
  cases xs
  cases ys
  simp

@[simp] theorem lex_toList [BEq α] (lt : α → α → Bool) (xs ys : Vector α n) :
    xs.toList.lex ys.toList lt = xs.lex ys lt := by
  rcases xs with ⟨xs, n₁⟩
  rcases ys with ⟨ys, n₂⟩
  simp

@[simp] theorem lex_empty
    [BEq α] {lt : α → α → Bool} (xs : Vector α 0) : xs.lex #v[] lt = false := by
  cases xs
  simp_all

@[simp] theorem singleton_lex_singleton [BEq α] {lt : α → α → Bool} : #v[a].lex #v[b] lt = lt a b := by
  simp only [lex, getElem_mk, List.getElem_toArray, List.getElem_singleton]
  cases lt a b <;> cases a != b <;> simp [Id.run]

protected theorem lt_irrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] (xs : Vector α n) : ¬ xs < xs :=
  Array.lt_irrefl xs.toArray

instance ltIrrefl [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Irrefl (α := Vector α n) (· < ·) where
  irrefl := Vector.lt_irrefl

@[simp] theorem not_lt_empty [LT α] (xs : Vector α 0) : ¬ xs < #v[] := Array.not_lt_empty xs.toArray
@[simp] theorem empty_le [LT α] (xs : Vector α 0) : #v[] ≤ xs := Array.empty_le xs.toArray

@[simp] theorem le_empty [LT α] (xs : Vector α 0) : xs ≤ #v[] ↔ xs = #v[] := by
  cases xs
  simp

protected theorem le_refl [LT α] [i₀ : Std.Irrefl (· < · : α → α → Prop)] (xs : Vector α n) : xs ≤ xs :=
  Array.le_refl xs.toArray

instance [LT α] [Std.Irrefl (· < · : α → α → Prop)] : Std.Refl (· ≤ · : Vector α n → Vector α n → Prop) where
  refl := Vector.le_refl

protected theorem lt_trans [LT α]
    [i₁ : Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
    {xs ys zs : Vector α n} (h₁ : xs < ys) (h₂ : ys < zs) : xs < zs :=
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
    {xs ys zs : Vector α n} (h₁ : xs ≤ ys) (h₂ : ys < zs) : xs < zs :=
  Array.lt_of_le_of_lt h₁ h₂

protected theorem le_trans [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Trans (¬ · < · : α → α → Prop) (¬ · < ·) (¬ · < ·)]
    {xs ys zs : Vector α n} (h₁ : xs ≤ ys) (h₂ : ys ≤ zs) : xs ≤ zs :=
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
    {xs ys : Vector α n} (h : xs < ys) : ¬ ys < xs := Array.lt_asymm h

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Asymm (· < · : α → α → Prop)] :
    Std.Asymm (· < · : Vector α n → Vector α n → Prop) where
  asymm _ _ := Vector.lt_asymm

protected theorem le_total [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)] (xs ys : Vector α n) : xs ≤ ys ∨ ys ≤ xs :=
  Array.le_total _ _

instance [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Total (¬ · < · : α → α → Prop)] :
    Std.Total (· ≤ · : Vector α n → Vector α n → Prop) where
  total := Vector.le_total

@[simp] protected theorem not_lt [LT α]
    {xs ys : Vector α n} : ¬ xs < ys ↔ ys ≤ xs := Iff.rfl

@[simp] protected theorem not_le [DecidableEq α] [LT α] [DecidableLT α]
    {xs ys : Vector α n} : ¬ ys ≤ xs ↔ xs < ys := Decidable.not_not

protected theorem le_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Total (¬ · < · : α → α → Prop)]
    {xs ys : Vector α n} (h : xs < ys) : xs ≤ ys :=
  Array.le_of_lt h

protected theorem le_iff_lt_or_eq [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Total (¬ · < · : α → α → Prop)]
    {xs ys : Vector α n} : xs ≤ ys ↔ xs < ys ∨ xs = ys := by
  simpa using Array.le_iff_lt_or_eq (xs := xs.toArray) (ys := ys.toArray)

@[simp] theorem lex_eq_true_iff_lt [DecidableEq α] [LT α] [DecidableLT α]
    {xs ys : Vector α n} : lex xs ys = true ↔ xs < ys := by
  cases xs
  cases ys
  simp

@[simp] theorem lex_eq_false_iff_ge [DecidableEq α] [LT α] [DecidableLT α]
    {xs ys : Vector α n} : lex xs ys = false ↔ ys ≤ xs := by
  cases xs
  cases ys
  simp [Array.not_lt_iff_ge]

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLT (Vector α n) :=
  fun xs ys => decidable_of_iff (lex xs ys = true) lex_eq_true_iff_lt

instance [DecidableEq α] [LT α] [DecidableLT α] : DecidableLE (Vector α n) :=
  fun xs ys => decidable_of_iff (lex ys xs = false) lex_eq_false_iff_ge

/--
`xs` is lexicographically less than `ys` if
there exists an index `i` such that
- for all `j < i`, `l₁[j] == l₂[j]` and
- `l₁[i] < l₂[i]`
-/
theorem lex_eq_true_iff_exists [BEq α] (lt : α → α → Bool) {xs ys : Vector α n} :
    lex xs ys lt = true ↔
      (∃ (i : Nat) (h : i < n), (∀ j, (hj : j < i) → xs[j] == ys[j]) ∧ lt xs[i] ys[i]) := by
  rcases xs with ⟨xs, n₁⟩
  rcases ys with ⟨ys, n₂⟩
  simp [Array.lex_eq_true_iff_exists, n₁, n₂]

/--
`l₁` is *not* lexicographically less than `l₂`
(which you might think of as "`l₂` is lexicographically greater than or equal to `l₁`"") if either
- `l₁` is pairwise equivalent under `· == ·` to `l₂` or
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
    {xs ys : Vector α n} :
    lex xs ys lt = false ↔
      (ys.isEqv xs (· == ·)) ∨
        (∃ (i : Nat) (h : i < n),(∀ j, (hj : j < i) → xs[j] == ys[j]) ∧ lt ys[i] xs[i]) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, n₂⟩
  simp_all [Array.lex_eq_false_iff_exists, n₂]

protected theorem lt_iff_exists [DecidableEq α] [LT α] [DecidableLT α] {xs ys : Vector α n} :
    xs < ys ↔
      (∃ (i : Nat) (h : i < n), (∀ j, (hj : j < i) → xs[j] = ys[j]) ∧ xs[i] < ys[i]) := by
  cases xs
  cases ys
  simp_all [Array.lt_iff_exists]

protected theorem le_iff_exists [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)] {xs ys : Vector α n} :
    xs ≤ ys ↔
      (xs = ys) ∨
        (∃ (i : Nat) (h : i < n), (∀ j, (hj : j < i) → xs[j] = ys[j]) ∧ xs[i] < ys[i]) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, n₂⟩
  simp [Array.le_iff_exists, ← n₂]

theorem append_left_lt [LT α] {xs : Vector α n} {ys ys' : Vector α m} (h : ys < ys') :
    xs ++ ys < xs ++ ys' := by
  simpa using Array.append_left_lt h

theorem append_left_le [DecidableEq α] [LT α] [DecidableLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    {xs : Vector α n} {ys ys' : Vector α m} (h : ys ≤ ys') :
    xs ++ ys ≤ xs ++ ys' := by
  simpa using Array.append_left_le h

protected theorem map_lt [LT α] [LT β]
    {xs ys : Vector α n} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : xs < ys) :
    map f xs < map f ys := by
  simpa using Array.map_lt w h

protected theorem map_le [DecidableEq α] [LT α] [DecidableLT α] [DecidableEq β] [LT β] [DecidableLT β]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Irrefl (· < · : β → β → Prop)]
    [Std.Asymm (· < · : β → β → Prop)]
    [Std.Antisymm (¬ · < · : β → β → Prop)]
    {xs ys : Vector α n} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : xs ≤ ys) :
    map f xs ≤ map f ys := by
  simpa using Array.map_le w h

end Vector
