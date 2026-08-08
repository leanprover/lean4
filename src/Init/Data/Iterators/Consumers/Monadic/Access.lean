/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.WFExtrinsicFix
import Init.RCases
import Init.Data.Iterators.Lemmas.Monadic.Basic

set_option linter.missingDocs true

public section

namespace Std
open Std.Iterators

/--
`it.IsPlausibleNthOutputStep n step` is the proposition that according to the
`IsPlausibleStep` relation, it is plausible that `step` returns the step in which the `n`-th value
of `it` is emitted, or `.done` if `it` can plausibly terminate before emitting `n` values.
-/
inductive IterM.IsPlausibleNthOutputStep {α β : Type w} {m : Type w → Type w'} [Iterator α m β] :
    Nat → IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop where
  /-- If `it` plausibly yields in its immediate next step, this step is a plausible `0`-th output step. -/
  | zero_yield {it : IterM (α := α) m β} : it.IsPlausibleStep (.yield it' out) →
      it.IsPlausibleNthOutputStep 0 (.yield it' out)
  /--
  If `it` plausibly terminates in its immediate next step (`.done`), then `.done` is a plausible
  `n`-th output step for arbitrary `n`.
  -/
  | done {it : IterM (α := α) m β} : it.IsPlausibleStep .done →
      it.IsPlausibleNthOutputStep n .done
  /--
  If `it` plausibly yields in its immediate next step, the successor iterator being `it'`, and
  if `step` is a plausible `n`-th output step of `it'`, then `step` is a plausible `n + 1`-th
  output step of `it`.
  -/
  | yield {it it' : IterM (α := α) m β} {out step} : it.IsPlausibleStep (.yield it' out) →
      it'.IsPlausibleNthOutputStep n step → it.IsPlausibleNthOutputStep (n + 1) step
  /--
  If `it` plausibly skips in its immediate next step, the successor iterator being `it'`, and
  if `step` is a plausible `n`-th output step of `it'`, then `step` is also a plausible `n`-th
  output step of `it`.
  -/
  | skip {it it' : IterM (α := α) m β} {step} : it.IsPlausibleStep (.skip it') →
      it'.IsPlausibleNthOutputStep n step → it.IsPlausibleNthOutputStep n step

theorem IterM.not_isPlausibleNthOutputStep_skip {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    {n : Nat} {it it' : IterM (α := α) m β} :
    ¬ it.IsPlausibleNthOutputStep n (.skip it') := by
  intro h
  generalize h' : IterStep.skip it' = step at h
  induction h
  · cases h'
  · cases h'
  · simp_all
  · simp_all

theorem IterM.isPlausibleNthOutputStep_trans_of_yield {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] {k n} {it it' : IterM (α := α) m β} {out step}
    (h : it.IsPlausibleNthOutputStep k (.yield it' out))
    (h' : it'.IsPlausibleNthOutputStep n step) :
    it.IsPlausibleNthOutputStep (n + k + 1) step := by
  generalize hs : (IterStep.yield it' out) = s at h
  induction h generalizing h' it' out
  case zero_yield =>
    cases hs
    exact .yield ‹_› h'
  case done => cases hs
  case yield ih =>
    cases hs
    refine .yield ‹_› ?_
    simp only [Nat.add_assoc] at ih
    exact ih h' rfl
  case skip ih =>
    cases hs
    refine .skip ‹_› ?_
    apply ih h' rfl

theorem IterM.isPlausibleNthOutputStep_trans_of_done {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] {k n} {it : IterM (α := α) m β}
    (h : it.IsPlausibleNthOutputStep k .done) (hle : k ≤ n) :
    it.IsPlausibleNthOutputStep n .done := by
  generalize hs : IterStep.done = s at h
  induction h generalizing n
  case zero_yield => cases hs
  case yield ih =>
    cases hs
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (Nat.ne_zero_of_lt (Nat.lt_of_add_one_le hle))
    exact .yield ‹_› (ih (Nat.le_of_add_le_add_right hle) rfl)
  case skip ih =>
    cases hs
    exact .skip ‹_› (ih hle rfl)
  case done =>
    cases hs
    exact .done ‹_›

theorem IterM.IsPlausibleNthOutputStep.unique [Iterator α Id β]
    [LawfulDeterministicIterator α Id] {it : IterM (α := α) Id β} {s s'}
    (hs : it.IsPlausibleNthOutputStep n s) (hs' : it.IsPlausibleNthOutputStep n s') :
    s = s' := by
  induction hs
  case zero_yield h =>
    match hs' with
    | .zero_yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h' := h'.eq_step
      rw [← h.eq_step] at h'
      cases h'
      all_goals simp
  case done h =>
    match hs' with
    | .zero_yield h' ..
    | .yield h' ..
    | .skip h' .. =>
      replace h := h.eq_step
      replace h' := h'.eq_step
      rw [← h] at h'
      cases h'
    | .done h' => simp
  case yield h _ ih =>
    match hs' with
    | .yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h' := h'.eq_step
      rw [← h.eq_step] at h'
      cases h'
      all_goals apply ih ‹_›
  case skip h _ ih =>
    match hs' with
    | .zero_yield h' ..
    | .yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h' := h'.eq_step
      rw [← h.eq_step] at h'
      cases h'
      all_goals apply ih ‹_›

/--
`IteratorAccess α m` provides efficient implementations for random access or iterators that support
it. `it.nextAtIdx? n` either returns the step in which the `n`th value of `it` is emitted
(necessarily of the form `.yield _ _`) or `.done` if `it` terminates before emitting the `n`th
value.

For monadic iterators, the monadic effects of this operation may differ from manually iterating
to the `n`-th value because `nextAtIdx?` can take shortcuts. By the signature, the return value
is guaranteed to plausible in the sense of `IterM.IsPlausibleNthOutputStep`.

This class is experimental and users of the iterator API should not explicitly depend on it.
-/
class IteratorAccess (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  /--
  `nextAtIdx? it n` either returns the step in which the `n`th value of `it` is emitted
  (necessarily of the form `.yield _ _`) or `.done` if `it` terminates before emitting the `n`th
  value.
  -/
  nextAtIdx? (it : IterM (α := α) m β) (n : Nat) :
    m (PlausibleIterStep (it.IsPlausibleNthOutputStep n))

/--
Returns the step in which `it` yields its `n`-th element, or `.done` if it terminates earlier.
In contrast to `step`, this function will always return either `.yield` or `.done` but never a
`.skip` step.

For monadic iterators, the monadic effects of this operation may differ from manually iterating
to the `n`-th value because `nextAtIdx?` can take shortcuts. By the signature, the return value
is guaranteed to plausible in the sense of `IterM.IsPlausibleNthOutputStep`.

This function is only available for iterators that explicitly support it by implementing
the `IteratorAccess` typeclass.
-/
@[always_inline, inline]
def IterM.nextAtIdx? [Iterator α m β] [IteratorAccess α m] (it : IterM (α := α) m β)
    (n : Nat) : m (PlausibleIterStep (it.IsPlausibleNthOutputStep n)) :=
  IteratorAccess.nextAtIdx? it n

/--
Slow version of `IterM.nextAtIdx?` that does not require an `IteratorAccess α m` instance.

Returns the step in which `it` yields its `n`-th element, or `.done` if it terminates earlier.
In contrast to `step`, this function will always return either `.yield` or `.done` but never a
`.skip` step.

This function terminates after finitely many steps.
-/
@[inline]
def IterM.atIdxSlow? [Monad m] [Iterator α m β] [Productive α m]
    (it' : IterM (α := α) m β)
    (n' : Nat) : m (Option β) := do
    match (← it'.step).inflate with
    | .yield it'' out _ =>
      match n' with
      | 0 => return some out
      | k + 1 => atIdxSlow? it'' k
    | .skip it'' _ => atIdxSlow? it'' n'
    | .done _ => return none
  termination_by (n', it'.finitelyManySkips)

/--
Slow version of `IterM.nextAtIdx?` that does not require an `IteratorAccess α m` instance.

Returns the step in which `it` yields its `n`-th element, or `.done` if it terminates earlier.
In contrast to `step`, this function will always return either `.yield` or `.done` but never a
`.skip` step.

This function terminates after finitely many steps.
-/
@[inline]
def IterM.nextAtIdxSlow? [Monad m] [Iterator α m β] [Productive α m]
    (it : IterM (α := α) m β)
    (n : Nat) : m (PlausibleIterStep (it.IsPlausibleNthOutputStep n)) :=
  go it n (fun s => id)
where
  go [Productive α m] it' n' (h : ∀ s, it'.IsPlausibleNthOutputStep n' s → it.IsPlausibleNthOutputStep n s) := do
    match (← it'.step).inflate with
    | .yield it'' out hp =>
      match n' with
      | 0 => return .yield it'' out (h _ (.zero_yield hp))
      | k + 1 => go it'' k (fun s hp' => h s (.yield hp hp'))
    | .skip it'' hp => go it'' n' (fun s hp' => h s (.skip hp hp'))
    | .done hp => return .done (h _ (.done hp))
  termination_by (n', it'.finitelyManySkips)

/--
Returns the `n`-th value emitted by `it`, or `none` if `it` terminates earlier.

For monadic iterators, the monadic effects of this operation may differ from manually iterating
to the `n`-th value because `atIdx?` can take shortcuts. By the signature, the return value
is guaranteed to plausible in the sense of `IterM.IsPlausibleNthOutputStep`.

This function is only available for iterators that explicitly support it by implementing
the `IteratorAccess` typeclass.
-/
@[always_inline, inline]
def IterM.atIdx? [Iterator α m β] [IteratorAccess α m] [Monad m] (it : IterM (α := α) m β)
    (n : Nat) : m (Option β) := do
  match (← IteratorAccess.nextAtIdx? it n).val with
  | .yield _ out => return some out
  | .skip _ => return none
  | .done => return none

end Std
