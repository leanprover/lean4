/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Ord.Basic
import Init.Omega
import Init.ByCases
import Init.Data.Array.Basic
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.WFTactics

public section

namespace Array

@[specialize]
protected def compareLex {α} (cmp : α → α → Ordering) (a₁ a₂ : Array α) : Ordering :=
  go 0
where go i :=
  if h₁ : a₁.size <= i then
    if a₂.size <= i then .eq else .lt
  else
    if h₂ : a₂.size <= i then
      .gt
    else match cmp a₁[i] a₂[i] with
      | .lt => .lt
      | .eq => go (i + 1)
      | .gt => .gt
termination_by a₁.size - i

instance {α} [Ord α] : Ord (Array α) where
  compare := Array.compareLex compare

protected theorem compare_eq_compareLex {α} [Ord α] :
    compare (α := Array α) = Array.compareLex compare := rfl

private theorem compareLex.go_succ {α} {cmp} {x₁ x₂} {a₁ a₂ : List α} {i} :
    compareLex.go cmp (x₁ :: a₁).toArray (x₂ :: a₂).toArray (i + 1) =
      compareLex.go cmp a₁.toArray a₂.toArray i := by
  induction i using Array.compareLex.go.induct cmp a₁.toArray a₂.toArray
  all_goals try
    conv => congr <;> rw [compareLex.go]
    simp
    repeat' split <;> (try simp_all; done)

protected theorem _root_.List.compareLex_eq_compareLex_toArray {α} {cmp} {l₁ l₂ : List α} :
    List.compareLex cmp l₁ l₂ = Array.compareLex cmp l₁.toArray l₂.toArray := by
  simp only [Array.compareLex]
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂
    · simp [Array.compareLex.go, List.compareLex_nil_nil]
    · simp [Array.compareLex.go, List.compareLex_nil_cons]
  | cons x xs ih =>
    cases l₂
    · simp [Array.compareLex.go, List.compareLex_cons_nil]
    · rw [Array.compareLex.go, List.compareLex_cons_cons]
      simp only [List.size_toArray, List.length_cons, Nat.le_zero_eq, Nat.add_one_ne_zero,
        ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero, Nat.zero_add]
      split <;> simp_all [compareLex.go_succ]

protected theorem _root_.List.compare_eq_compare_toArray {α} [Ord α] {l₁ l₂ : List α} :
    compare l₁ l₂ = compare l₁.toArray l₂.toArray :=
  List.compareLex_eq_compareLex_toArray

protected theorem compareLex_eq_compareLex_toList {α} {cmp} {a₁ a₂ : Array α} :
    Array.compareLex cmp a₁ a₂ = List.compareLex cmp a₁.toList a₂.toList := by
  rw [List.compareLex_eq_compareLex_toArray]

protected theorem compare_eq_compare_toList {α} [Ord α] {a₁ a₂ : Array α} :
    compare a₁ a₂ = compare a₁.toList a₂.toList :=
  Array.compareLex_eq_compareLex_toList

end Array
