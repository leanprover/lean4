/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Append
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.Append
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Access
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Consumers.Access
import Init.Data.Iterators.Lemmas.Basic
import Init.Omega

public section

namespace Std
open Std.Iterators Std.Iterators.Types

theorem Iter.append_eq_toIter_append_toIterM {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    it₁.append it₂ = (it₁.toIterM.append it₂.toIterM).toIter :=
  rfl

theorem Iter.Intermediate.appendSnd_eq_toIter_appendSnd_toIterM {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β]
    {it₂ : Iter (α := α₂) β} :
    Iter.Intermediate.appendSnd α₁ it₂ = (IterM.Intermediate.appendSnd α₁ it₂.toIterM).toIter :=
  rfl

theorem Iter.step_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    (it₁.append it₂).step =
      match it₁.step with
      | .yield it₁' out h => .yield (it₁'.append it₂) out (.fstYield h)
      | .skip it₁' h => .skip (it₁'.append it₂) (.fstSkip h)
      | .done h => .skip (Iter.Intermediate.appendSnd α₁ it₂) (.fstDone h) := by
  simp only [Iter.step, append_eq_toIter_append_toIterM, toIterM_toIter, IterM.step_append,
    Id.run_bind]
  cases it₁.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;>
    simp [Intermediate.appendSnd_eq_toIter_appendSnd_toIterM]

theorem Iter.Intermediate.step_appendSnd {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β]
    {it₂ : Iter (α := α₂) β} :
    (Iter.Intermediate.appendSnd α₁ it₂).step =
      match it₂.step with
      | .yield it₂' out h => .yield (Iter.Intermediate.appendSnd α₁ it₂') out (.sndYield h)
      | .skip it₂' h => .skip (Iter.Intermediate.appendSnd α₁ it₂') (.sndSkip h)
      | .done h => .done (.sndDone h) := by
  simp only [Iter.step, appendSnd, toIterM_toIter, IterM.Intermediate.step_appendSnd, Id.run_bind]
  cases it₂.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;> simp

@[cbv_eval, simp]
theorem Iter.toList_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    (it₁.append it₂).toList = it₁.toList ++ it₂.toList := by
  simp [append_eq_toIter_append_toIterM, toList_eq_toList_toIterM]

@[simp]
theorem Iter.toListRev_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    (it₁.append it₂).toListRev = it₂.toListRev ++ it₁.toListRev := by
  simp [append_eq_toIter_append_toIterM, toListRev_eq_toListRev_toIterM]

@[cbv_eval, simp]
theorem Iter.toArray_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} :
    (it₁.append it₂).toArray = it₁.toArray ++ it₂.toArray := by
  simp [append_eq_toIter_append_toIterM, toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.atIdxSlow?_appendSnd {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Productive α₁ Id] [Productive α₂ Id]
    {it₂ : Iter (α := α₂) β} {n : Nat} :
    (Iter.Intermediate.appendSnd α₁ it₂).atIdxSlow? n = it₂.atIdxSlow? n := by
  induction n, it₂ using Iter.atIdxSlow?.induct_unfolding with
  | yield_zero it it' out h h' =>
    simp only [atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Intermediate.step_appendSnd, h']
  | yield_succ it it' out h h' n ih =>
    simp only [atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Intermediate.step_appendSnd, h', ih]
  | skip_case n it it' h h' ih =>
    simp only [atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Intermediate.step_appendSnd, h', ih]
  | done_case n it h h' =>
    simp only [atIdxSlow?_eq_match (it := Iter.Intermediate.appendSnd α₁ it),
      Intermediate.step_appendSnd, h']

theorem Iter.atIdxSlow?_append_of_eq_some {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} {n : Nat} {b : β}
    (h : it₁.atIdxSlow? n = some b) :
    (it₁.append it₂).atIdxSlow? n = some b := by
  induction n, it₁ using Iter.atIdxSlow?.induct_unfolding generalizing it₂ with
  | yield_zero it it' out hp h' =>
    rw [atIdxSlow?_eq_match (it := it.append it₂)]
    cases h
    simp [step_append, h']
  | yield_succ it it' out hp h' n ih =>
    rw [atIdxSlow?_eq_match (it := it.append it₂)]
    simp [step_append, h', ih h]
  | skip_case n it it' hp h' ih =>
    rw [atIdxSlow?_eq_match (it := it.append it₂)]
    simp [step_append, h', ih h]
  | done_case n it hp h' =>
    cases h

theorem Iter.atIdxSlow?_append {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} {n : Nat} :
    (it₁.append it₂).atIdxSlow? n =
      if n < it₁.toList.length then it₁.atIdxSlow? n
      else it₂.atIdxSlow? (n - it₁.toList.length) := by
  induction n, it₁ using Iter.atIdxSlow?.induct_unfolding generalizing it₂ with
  | yield_zero it it' out h h' =>
    simp only [atIdxSlow?_eq_match (it := it.append it₂), step_append, h']
    rw [toList_eq_match_step (it := it)]
    simp [h']
  | yield_succ it it' out h h' n ih =>
    simp only [atIdxSlow?_eq_match (it := it.append it₂), step_append, h', ih]
    rw [toList_eq_match_step (it := it)]
    simp [h', Nat.succ_lt_succ_iff, Nat.succ_sub_succ]
  | skip_case n it it' h h' ih =>
    simp only [atIdxSlow?_eq_match (it := it.append it₂), step_append, h', ih]
    rw [toList_eq_match_step (it := it)]
    simp [h']
  | done_case n it h h' =>
    simp [atIdxSlow?_eq_match (it := it.append it₂), step_append, h',
      atIdxSlow?_appendSnd, toList_eq_match_step]

theorem Iter.atIdxSlow?_append_of_productive {α₁ α₂ β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β} {n k : Nat}
    (hk : it₁.atIdxSlow? k = none)
    (hmin : ∀ j, j < k → (it₁.atIdxSlow? j).isSome)
    (hle : k ≤ n) :
    (it₁.append it₂).atIdxSlow? n = it₂.atIdxSlow? (n - k) := by
  induction n, it₁ using Iter.atIdxSlow?.induct_unfolding generalizing k it₂ with
  | yield_zero it it' out hp h' =>
    exfalso
    have : k = 0 := by omega
    subst this
    rw [atIdxSlow?_eq_match (it := it)] at hk
    simp [h'] at hk
  | yield_succ it it' out hp h' n ih =>
    rw [atIdxSlow?_eq_match (it := it.append it₂)]
    simp only [step_append, h']
    match k with
    | 0 =>
      rw [atIdxSlow?_eq_match (it := it)] at hk
      simp [h'] at hk
    | k + 1 =>
      rw [atIdxSlow?_eq_match (it := it)] at hk
      simp [h'] at hk
      have hmin' : ∀ j, j < k → (it'.atIdxSlow? j).isSome := by
        intro j hj
        have h := hmin (j + 1) (by omega)
        rw [atIdxSlow?_eq_match (it := it)] at h
        simpa [h'] using h
      rw [ih hk hmin' (by omega)]
      congr 1
      omega
  | skip_case n it it' hp h' ih =>
    rw [atIdxSlow?_eq_match (it := it.append it₂)]
    simp only [step_append, h']
    rw [atIdxSlow?_eq_match (it := it)] at hk; simp [h'] at hk
    have hmin' : ∀ j, j < k → (it'.atIdxSlow? j).isSome := by
      intro j hj
      have h := hmin j hj
      rw [atIdxSlow?_eq_match (it := it)] at h
      simpa [h'] using h
    exact ih hk hmin' hle
  | done_case n it hp h' =>
    rw [atIdxSlow?_eq_match (it := it.append it₂)]
    simp only [step_append, h', atIdxSlow?_appendSnd]
    have hk0 : k = 0 := by
      false_or_by_contra
      have h := hmin 0 (by omega)
      rw [atIdxSlow?_eq_match (it := it)] at h
      simp [h'] at h
    simp [hk0]

end Std
