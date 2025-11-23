/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic

public section

namespace Std.Iterators

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

theorem IterM.not_isPlausibleNthOutputStep_yield {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    {n : Nat} {it it' : IterM (α := α) m β} :
    ¬ it.IsPlausibleNthOutputStep n (.skip it') := by
  intro h
  generalize h' : IterStep.skip it' = step at h
  induction h
  · cases h'
  · cases h'
  · simp_all
  · simp_all

/--
`IteratorAccess α m` provides efficient implementations for random access or iterators that support
it. `it.nextAtIdx? n` either returns the step in which the `n`-th value of `it` is emitted
(necessarily of the form `.yield _ _`) or `.done` if `it` terminates before emitting the `n`-th
value.

For monadic iterators, the monadic effects of this operation may differ from manually iterating
to the `n`-th value because `nextAtIdx?` can take shortcuts. By the signature, the return value
is guaranteed to plausible in the sense of `IterM.IsPlausibleNthOutputStep`.

This class is experimental and users of the iterator API should not explicitly depend on it.
-/
class IteratorAccess (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
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

end Std.Iterators
