/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Access
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Access
import Init.Omega

namespace Std.Iter
open Std.Iterators

public theorem nextAtIdxSlow?_eq_match [Iterator α Id β] [Productive α Id]
    {n : Nat} {it : Iter (α := α) β} :
    it.nextAtIdxSlow? n =
      (match it.step with
      | .yield it' out hp =>
        match n with
        | 0 => .yield it' out (.zero_yield hp)
        | n + 1 =>
          let s := it'.nextAtIdxSlow? n
          ⟨s.val, .yield hp s.property⟩
      | .skip it' hp =>
        let s := it'.nextAtIdxSlow? n
        ⟨s.val, .skip hp s.property⟩
      | .done hp => .done (.done hp)) := by
  apply Subtype.ext
  simp only [nextAtIdxSlow?]
  rw [IterM.nextAtIdxSlow?_eq_match]
  simp only [bind_pure_comp, Id.run_bind, step]
  split
  · cases n <;> simp [*]
  · simp [*]
  · simp [*]

public theorem atIdxSlow?_eq_match [Iterator α Id β] [Productive α Id]
    {n : Nat} {it : Iter (α := α) β} :
    it.atIdxSlow? n =
      (match it.step.val with
      | .yield it' out =>
        match n with
        | 0 => some out
        | n + 1 => it'.atIdxSlow? n
      | .skip it' => it'.atIdxSlow? n
      | .done => none) := by
  induction n, it using Iter.atIdxSlow?.induct_unfolding <;> simp_all

public theorem lt_length_of_nextAtIdxSlow?_eq_yield [Iterator α Id β] [Finite α Id]
    [Productive α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {it it' : Iter (α := α) β} {i : Nat} {out : β}
    (h : (it.nextAtIdxSlow? i).val = .yield it' out) :
    i < it.length := by
  induction it using Iter.inductSteps generalizing i it' out with
  | step it ihy ihs =>
    rw [Std.Iter.length_eq_match_step]
    rw [nextAtIdxSlow?_eq_match] at h
    cases hstep : it.step using PlausibleIterStep.casesOn with
    | yield it'' out'' hp =>
      simp only [hstep] at h
      simp only
      cases i with
      | zero => omega
      | succ k =>
        simp only at h
        exact Nat.succ_lt_succ (ihy hp h)
    | skip it'' hp => exact ihs hp (by simpa [hstep] using h)
    | done hp => simp [hstep] at h

public theorem length_le_of_nextAtIdxSlow?_eq_done [Iterator α Id β] [Finite α Id]
    [Productive α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {i : Nat}
    (h : (it.nextAtIdxSlow? i).val = .done) :
    it.length ≤ i := by
  induction it using Iter.inductSteps generalizing i with
  | step it ihy ihs =>
    rw [Std.Iter.length_eq_match_step]
    rw [nextAtIdxSlow?_eq_match] at h
    cases hstep : it.step using PlausibleIterStep.casesOn with
    | yield it'' out'' hp =>
      simp only [hstep] at h
      simp only
      cases i with
      | zero => simp at h
      | succ k =>
        have := ihy hp (by simpa using h)
        omega
    | skip it'' hp =>
      simp only [hstep] at h
      simp only
      have := ihs hp h
      omega
    | done hp =>
      simp only
      omega

public theorem nextAtIdx?_eq_nextAtIdxSlow? [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {n : Nat} :
    it.nextAtIdx? n = it.nextAtIdxSlow? n := by
  simp [Iter.nextAtIdx?, Iter.nextAtIdxSlow?, IterM.nextAtIdx?_eq_nextAtIdxSlow?]

public theorem length_nextAtIdxSlow? [Iterator α Id β] [Finite α Id] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] {it : Iter (α := α) β} :
    (it.nextAtIdxSlow? n).val.successor.elim 0 Iter.length = it.length - n - 1 := by
  have := IterM.length_nextAtIdxSlow? (it := it.toIterM) (n := n)
  replace this := congrArg (fun x => ULift.down (Id.run x)) this
  simp only [Id.run_bind, Id.run_map] at this
  simp only [nextAtIdxSlow?, length, ← this]
  split at this
  · simpa [Option.elim, *]
  · exact IterM.not_isPlausibleNthOutputStep_skip.elim ‹_›
  · simp [Option.elim, *]

end Std.Iter
