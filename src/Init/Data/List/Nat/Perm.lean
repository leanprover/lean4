/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Perm

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/-- Helper lemma for `set_set_perm`-/
private theorem set_set_perm' {as : List α} {i j : Nat} (h₁ : i < as.length) (h₂ : i + j < as.length)
    (hj : 0 < j) :
    (as.set i as[i + j]).set (i + j) as[i] ~ as := by
  have : as =
      as.take i ++ as[i] :: (as.take (i + j)).drop (i + 1) ++ as[i + j] :: as.drop (i + j + 1) := by
    simp only [getElem_cons_drop, append_assoc, cons_append]
    rw [← drop_append_of_le_length]
    · simp
    · simp; omega
  conv => lhs; congr; congr; rw [this]
  conv => rhs; rw [this]
  rw [set_append_left _ _ (by simp; omega)]
  rw [set_append_right _ _ (by simp; omega)]
  rw [set_append_right _ _ (by simp; omega)]
  simp only [length_append, length_take, length_set, length_cons, length_drop]
  rw [(show i - min i as.length = 0 by omega)]
  rw [(show i + j - (min i as.length + (min (i + j) as.length - (i + 1) + 1)) = 0 by omega)]
  simp only [set_cons_zero]
  simp only [append_assoc]
  apply Perm.append_left
  apply cons_append_cons_perm

theorem set_set_perm {as : List α} {i j : Nat} (h₁ : i < as.length) (h₂ : j < as.length) :
    (as.set i as[j]).set j as[i] ~ as := by
  if h₃ : i = j then
    simp [h₃]
  else
    if h₃ : i < j then
      let j' := j - i
      have t : j = i + j' := by omega
      generalize j' = j' at t
      subst t
      exact set_set_perm' _ _ (by omega)
    else
      rw [set_comm _ _ (by omega)]
      let i' := i - j
      have t : i = j + i' := by omega
      generalize i' = i' at t
      subst t
      apply set_set_perm' _ _ (by omega)

namespace Perm

/-- Variant of `List.Perm.take` specifying the the permutation is constant after `i` elementwise. -/
theorem take_of_getElem? {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat} (w : ∀ j, i ≤ j → l₁[j]? = l₂[j]?) :
    l₁.take i ~ l₂.take i := by
  refine h.take (Perm.of_eq ?_)
  ext1 j
  simpa using w (i + j) (by omega)

/-- Variant of `List.Perm.drop` specifying the the permutation is constant before `i` elementwise. -/
theorem drop_of_getElem? {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat} (w : ∀ j, j < i → l₁[j]? = l₂[j]?) :
    l₁.drop i ~ l₂.drop i := by
  refine h.drop (Perm.of_eq ?_)
  ext1
  simp only [getElem?_take]
  split <;> simp_all

end Perm

end List
