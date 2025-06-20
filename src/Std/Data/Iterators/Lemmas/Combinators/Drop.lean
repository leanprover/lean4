/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Drop
import Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop
import Std.Data.Iterators.Lemmas.Combinators.Take
import Init.Data.Iterators.Lemmas.Consumers

namespace Std.Iterators

theorem Iter.drop_eq {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    it.drop n = (it.toIterM.drop n).toIter :=
  rfl

theorem Iter.step_drop {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    (it.drop n).step = (match it.step with
    | .yield it' out h =>
      match n with
      | 0 => .yield (it'.drop 0) out (.yield h rfl)
      | k + 1 => .skip (it'.drop k) (.drop h rfl)
    | .skip it' h => .skip (it'.drop n) (.skip h)
    | .done h => .done (.done h)) := by
  simp only [drop_eq, step, toIterM_toIter, IterM.step_drop, Id.run_bind]
  generalize it.toIterM.step.run = step
  obtain ⟨step, h⟩ := step
  cases step <;> cases n <;>
    simp [PlausibleIterStep.yield, PlausibleIterStep.skip, PlausibleIterStep.done]

theorem Iter.atIdxSlow?_drop {α β}
    [Iterator α Id β] [Productive α Id] {k l : Nat}
    {it : Iter (α := α) β} :
    (it.drop k).atIdxSlow? l = it.atIdxSlow? (l + k) := by
  induction k generalizing it <;> induction l generalizing it
  all_goals
    induction it using Iter.inductSkips with | step it ih =>
    rw [atIdxSlow?.eq_def, atIdxSlow?.eq_def, step_drop]
    cases it.step using PlausibleIterStep.casesOn <;> simp [*]

@[simp]
theorem Iter.toList_drop {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.drop n).toList = it.toList.drop n := by
  ext
  simp only [getElem?_toList_eq_atIdxSlow?, List.getElem?_drop, atIdxSlow?_drop]
  rw [Nat.add_comm]

@[simp]
theorem Iter.toListRev_drop {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.drop n).toListRev = (it.toList.reverse.take (it.toList.length - n)) := by
  rw [toListRev_eq, toList_drop, List.reverse_drop]

theorem List.drop_eq_extract {l : List α} {k : Nat} :
    l.drop k = l.extract k := by
  induction l generalizing k
  case nil => simp
  case cons _ _ ih =>
    match k with
    | 0 => simp
    | _ + 1 =>
      simp only [List.drop_succ_cons, List.length_cons, ih]
      simp only [List.extract_eq_drop_take, Nat.reduceSubDiff, List.drop_succ_cons]

@[simp]
theorem Iter.toArray_drop {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.drop n).toArray = it.toArray.extract n := by
  rw [← toArray_toList, ← toArray_toList, ← List.toArray_drop, toList_drop]

end Std.Iterators
