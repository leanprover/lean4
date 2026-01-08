/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.TakeWhile
public import Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile
public import Std.Data.Iterators.Lemmas.Consumers
public import Init.Data.Iterators.Lemmas.Consumers.Access

@[expose] public section

namespace Std
open Std.Iterators

theorem Iter.takeWhile_eq {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} :
    it.takeWhile P = (it.toIterM.takeWhile P).toIter :=
  rfl

theorem Iter.step_takeWhile {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} :
    (it.takeWhile P).step = (match it.step with
      | .yield it' out h => match hP : P out with
        | true => .yield (it'.takeWhile P) out (.yield h (by simpa))
        | false => .done (.rejected h (by simpa))
      | .skip it' h => .skip (it'.takeWhile P) (.skip h)
      | .done h => .done (.done h)) := by
  simp [Iter.takeWhile_eq, Iter.step, toIterM_toIter, IterM.step_takeWhile]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [IterM.Step.toPure_yield, PlausibleIterStep.yield, toIter_toIterM, toIterM_toIter]
    split <;> split <;> (try exfalso; simp_all; done) <;> simp_all
  · simp
  · simp

theorem Iter.val_step_takeWhile {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} :
    (it.takeWhile P).step.val = (match it.step.val with
      | .yield it' out => match P out with
        | true => .yield (it'.takeWhile P) out
        | false => .done
      | .skip it' => .skip (it'.takeWhile P)
      | .done => .done) := by
  simp [Iter.takeWhile_eq, Iter.step, toIterM_toIter, IterM.step_takeWhile]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [IterM.Step.toPure_yield, PlausibleIterStep.yield, toIter_toIterM, toIterM_toIter]
    split <;> split <;> (try exfalso; simp_all; done) <;> simp_all
  · simp
  · simp

theorem Iter.atIdxSlow?_takeWhile {α β}
    [Iterator α Id β] [Productive α Id] {l : Nat}
    {it : Iter (α := α) β} {P} :
    (it.takeWhile P).atIdxSlow? l = if ∀ k, k ≤ l → (it.atIdxSlow? k).any P then it.atIdxSlow? l else none := by
  fun_induction it.atIdxSlow? l
  case case1 it it' out h h' =>
    rw [atIdxSlow?_eq_match]
    simp only [val_step_takeWhile, h', Nat.le_zero_eq, forall_eq]
    rw [atIdxSlow?, h']
    simp only [Option.any_some]
    apply Eq.symm
    split
    · cases h' : P out
      · exfalso; simp_all
      · simp
    · cases h' : P out
      · simp
      · exfalso; simp_all
  case case2 it it' out h h' l ih =>
    rw [atIdxSlow?_eq_match]
    simp only [Nat.succ_eq_add_one, val_step_takeWhile, h']
    simp only [atIdxSlow?.eq_def (it := it), h']
    cases hP : P out
    · simp
      intro h
      specialize h 0 (Nat.zero_le _)
      simp at h
      exfalso; simp_all
    · simp [ih]
      split
      · rename_i h
        rw [if_pos]
        intro k hk
        split
        · exact hP
        · simp at hk
          exact h _ hk
      · rename_i hl
        rw [if_neg]
        intro hl'
        apply hl
        intro k hk
        exact hl' (k + 1) (Nat.succ_le_succ hk)
  case case3 l it it' h h' ih =>
    simp only [atIdxSlow?.eq_def (it := it.takeWhile P), step_takeWhile, h', ih]
    simp only [atIdxSlow?.eq_def (it := it), h']
  case case4 l it h h' =>
    simp only [atIdxSlow?.eq_def (it := it), atIdxSlow?.eq_def (it := it.takeWhile P), h',
      step_takeWhile]
    split <;> rfl

private theorem List.getElem?_takeWhile {l : List α} {P : α → Bool} {k} :
    (l.takeWhile P)[k]? = if ∀ k' : Nat, k' ≤ k → l[k']?.any P then l[k]? else none := by
  induction l generalizing k
  · simp
  · rename_i x xs ih
    rw [List.takeWhile_cons]
    split
    · cases k
      · simp [*]
      · simp [ih]
        split
        · rw [if_pos]
          intro k' hk'
          cases k'
          · simp [*]
          · simp_all
        · rename_i hP
          rw [if_neg]
          intro hP'
          apply hP
          intro k' hk'
          specialize hP' (k' + 1) (by omega)
          simp_all
    · simp
      intro h
      specialize h 0
      simp_all

@[simp]
theorem Iter.toList_takeWhile_of_finite {α β} [Iterator α Id β] {P}
    [Finite α Id]
    {it : Iter (α := α) β} :
    (it.takeWhile P).toList = it.toList.takeWhile P := by
  ext
  simp only [getElem?_toList_eq_atIdxSlow?, atIdxSlow?_takeWhile, List.getElem?_takeWhile]

@[simp]
theorem Iter.toListRev_takeWhile_of_finite {α β} [Iterator α Id β] {P}
    [Finite α Id]
    {it : Iter (α := α) β} :
    (it.takeWhile P).toListRev = (it.toList.takeWhile P).reverse := by
  rw [toListRev_eq, toList_takeWhile_of_finite]

@[simp]
theorem Iter.toArray_takeWhile_of_finite {α β} [Iterator α Id β] {P}
    [Finite α Id]
    {it : Iter (α := α) β} :
    (it.takeWhile P).toArray = it.toArray.takeWhile P := by
  rw [← toArray_toList, ← toArray_toList, List.takeWhile_toArray, toList_takeWhile_of_finite]

end Std
