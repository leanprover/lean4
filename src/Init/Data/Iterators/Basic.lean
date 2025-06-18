/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Core
import Init.Classical
import Init.Ext
import Init.NotationExtra
import Init.TacticsExtra

/-!
### Definition of iterators

This module defines iterators and what it means for an iterator to be finite and productive.
-/

namespace Std

namespace Iterators

/--
An iterator that sequentially emits values of type `β` in the monad `m`. It may be finite
or infinite.

See the root module `Std.Data.Iterators` for a more comprehensive overview over the iterator
framework.

See `Std.Data.Iterators.Producers` for ways to iterate over common data structures.
By convention, the monadic iterator associated with an object can be obtained via dot notation.
For example, `List.iterM IO` creates an iterator over a list in the monad `IO`.

See `Init.Data.Iterators.Consumers` for ways to use an iterator. For example, `it.toList` will
convert a provably finite iterator `it` into a list and `it.allowNontermination.toList` will
do so even if finiteness cannot be proved. It is also always possible to manually iterate using
`it.step`, relying on the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.

See `Iter` for a more convenient interface in case that no monadic effects are needed (`m = Id`).

Internally, `IterM m β` wraps an element of type `α` containing state information.
The type `α` determines the implementation of the iterator using a typeclass mechanism.
The concrete typeclass implementing the iterator is `Iterator α m β`.

When using combinators, `α` can become very complicated. It is an implicit parameter
of `α` so that the pretty printer will not print this large type by default. If a declaration
returns an iterator, the following will not work:

```lean
def x : IterM IO Nat := [1, 2, 3].iterM IO
```

Instead the declaration type needs to be completely omitted:

```lean
def x := [1, 2, 3].iterM IO

-- if you want to ensure that `x` is an iterator in `IO` emitting `Nat`
def x := ([1, 2, 3].iterM IO : IterM IO Nat)
```
-/
@[ext]
structure IterM {α : Type w} (m : Type w → Type w') (β : Type w) where
  /-- Internal implementation detail of the iterator. -/
  internalState : α

/--
An iterator that sequentially emits values of type `β`. It may be finite
or infinite.

See the root module `Std.Data.Iterators` for a more comprehensive overview over the iterator
framework.

See `Std.Data.Iterators.Producers` for ways to iterate over common data structures.
By convention, the monadic iterator associated with an object can be obtained via dot notation.
For example, `List.iterM IO` creates an iterator over a list in the monad `IO`.

See `Init.Data.Iterators.Consumers` for ways to use an iterator. For example, `it.toList` will
convert a provably finite iterator `it` into a list and `it.allowNontermination.toList` will
do so even if finiteness cannot be proved. It is also always possible to manually iterate using
`it.step`, relying on the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.

See `IterM` for iterators that operate in a monad.

Internally, `Iter β` wraps an element of type `α` containing state information.
The type `α` determines the implementation of the iterator using a typeclass mechanism.
The concrete typeclass implementing the iterator is `Iterator α m β`.

When using combinators, `α` can become very complicated. It is an implicit parameter
of `α` so that the pretty printer will not print this large type by default. If a declaration
returns an iterator, the following will not work:

```lean
def x : Iter Nat := [1, 2, 3].iter
```

Instead the declaration type needs to be completely omitted:

```lean
def x := [1, 2, 3].iter

-- if you want to ensure that `x` is an iterator emitting `Nat`
def x := ([1, 2, 3].iter : Iter Nat)
```
-/
structure Iter {α : Type w} (β : Type w) where
  /-- Internal implementation detail of the iterator. -/
  internalState : α

/--
Converts a pure iterator (`Iter β`) into a monadic iterator (`IterM Id β`) in the
identity monad `Id`.
-/
@[expose]
def Iter.toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) : IterM (α := α) Id β :=
  ⟨it.internalState⟩

/--
Converts a monadic iterator (`IterM Id β`) over `Id` into a pure iterator (`Iter β`).
-/
@[expose]
def IterM.toIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) : Iter (α := α) β :=
  ⟨it.internalState⟩

@[simp]
theorem Iter.toIter_toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) :
    it.toIterM.toIter = it :=
  rfl

@[simp]
theorem Iter.toIter_comp_toIterM {α : Type w} {β : Type w} :
    IterM.toIter ∘ Iter.toIterM (α := α) (β := β) = id :=
  rfl

@[simp]
theorem Iter.toIterM_toIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) :
    it.toIter.toIterM = it :=
  rfl

@[simp]
theorem Iter.toIterM_comp_toIter {α : Type w} {β : Type w} :
    Iter.toIterM ∘ IterM.toIter (α := α) (β := β) = id :=
  rfl

section IterStep

variable {α : Type u} {β : Type w}

/--
`IterStep α β` represents a step taken by an iterator (`Iter β` or `IterM m β`).
-/
inductive IterStep (α β) where
  /--
  `IterStep.yield it out` describes the situation that an iterator emits `out` and provides `it`
  as the succeeding iterator.
  -/
  | yield : (it : α) → (out : β) → IterStep α β
  /--
  `IterStep.skip it` describes the situation that an iterator does not emit anything in this
  iteration and provides `it'` as the succeeding iterator.

  Allowing `skip` steps is necessary to generate efficient code from a loop over an iterator.
  -/
  | skip : (it : α) → IterStep α β
  /--
  `IterStep.done` describes the situation that an iterator has finished and will neither emit
  more values nor cause any monadic effects. In this case, no succeeding iterator is provided.
  -/
  | done : IterStep α β

/--
Returns the succeeding iterator stored in an iterator step or `none` if the step is `.done`
and the iterator has finished.
-/
@[expose]
def IterStep.successor : IterStep α β → Option α
  | .yield it _ => some it
  | .skip it => some it
  | .done => none

/--
If present, applies `f` to the iterator of an `IterStep` and replaces the iterator
with the result of the application of `f`.
-/
@[always_inline, inline, expose]
def IterStep.mapIterator {α' : Type u'} (f : α → α') : IterStep α β → IterStep α' β
  | .yield it out => .yield (f it) out
  | .skip it => .skip (f it)
  | .done => .done

@[simp]
theorem IterStep.mapIterator_yield {α' : Type u'} {f : α → α'} {it : α} {out : β} :
    (IterStep.yield it out).mapIterator f = IterStep.yield (f it) out :=
  rfl

@[simp]
theorem IterStep.mapIterator_skip {α' : Type u'} {f : α → α'} {it : α} :
    (IterStep.skip it (β := β)).mapIterator f = IterStep.skip (f it) :=
  rfl

@[simp]
theorem IterStep.mapIterator_done {α' : Type u'} {f : α → α'} :
    (IterStep.done (α := α) (β := β)).mapIterator f = IterStep.done :=
  rfl

@[simp]
theorem IterStep.mapIterator_mapIterator {α' : Type u'} {α'' : Type u''}
    {f : α → α'} {g : α' → α''} {step : IterStep α β} :
    (step.mapIterator f).mapIterator g = step.mapIterator (g ∘ f) := by
  cases step <;> rfl

theorem IterStep.mapIterator_comp {α' : Type u'} {α'' : Type u''}
    {f : α → α'} {g : α' → α''} :
    IterStep.mapIterator (β := β) (g ∘ f) = mapIterator g ∘ mapIterator f := by
  apply funext
  exact fun _ => mapIterator_mapIterator.symm

@[simp]
theorem IterStep.mapIterator_id {step : IterStep α β} :
    step.mapIterator id = step := by
  cases step <;> rfl

/--
A variant of `IterStep` that bundles the step together with a proof that it is "plausible".
The plausibility predicate will later be chosen to assert that a state is a plausible successor
of another state. Having this proof bundled up with the step is important for termination proofs.

See `IterM.Step` and `Iter.Step` for the concrete choice of the plausibility predicate.
-/
@[expose]
def PlausibleIterStep (IsPlausibleStep : IterStep α β → Prop) := Subtype IsPlausibleStep

/--
Match pattern for the `yield` case. See also `IterStep.yield`.
-/
@[match_pattern, simp, expose]
def PlausibleIterStep.yield {IsPlausibleStep : IterStep α β → Prop}
    (it' : α) (out : β) (h : IsPlausibleStep (.yield it' out)) :
    PlausibleIterStep IsPlausibleStep :=
  ⟨.yield it' out, h⟩

/--
Match pattern for the `skip` case. See also `IterStep.skip`.
-/
@[match_pattern, simp, expose]
def PlausibleIterStep.skip {IsPlausibleStep : IterStep α β → Prop}
    (it' : α) (h : IsPlausibleStep (.skip it')) : PlausibleIterStep IsPlausibleStep :=
  ⟨.skip it', h⟩

/--
Match pattern for the `done` case. See also `IterStep.done`.
-/
@[match_pattern, simp, expose]
def PlausibleIterStep.done {IsPlausibleStep : IterStep α β → Prop}
    (h : IsPlausibleStep .done) : PlausibleIterStep IsPlausibleStep :=
  ⟨.done, h⟩

/--
A more convenient `cases` eliminator for `PlausibleIterStep`.
-/
@[elab_as_elim, cases_eliminator]
abbrev PlausibleIterStep.casesOn {IsPlausibleStep : IterStep α β → Prop}
    {motive : PlausibleIterStep IsPlausibleStep → Sort x} (s : PlausibleIterStep IsPlausibleStep)
    (yield : ∀ it' out h, motive ⟨.yield it' out, h⟩)
    (skip : ∀ it' h, motive ⟨.skip it', h⟩)
    (done : ∀ h, motive ⟨.done, h⟩) : motive s :=
  match s with
  | .yield it' out h => yield it' out h
  | .skip it' h => skip it' h
  | .done h => done h

end IterStep

/--
The typeclass providing the step function of an iterator in `Iter (α := α) β` or
`IterM (α := α) m β`.

In order to allow intrinsic termination proofs when iterating with the `step` function, the
step object is bundled with a proof that it is a "plausible" step for the given current iterator.
-/
class Iterator (α : Type w) (m : Type w → Type w') (β : outParam (Type w)) where
  IsPlausibleStep : IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop
  step : (it : IterM (α := α) m β) → m (PlausibleIterStep <| IsPlausibleStep it)

section Monadic

/--
Converts wraps the state of an iterator into an `IterM` object.
-/
@[always_inline, inline, expose]
def toIterM {α : Type w} (it : α) (m : Type w → Type w') (β : Type w) :
    IterM (α := α) m β :=
  ⟨it⟩

@[simp]
theorem toIterM_internalState {α m β} (it : IterM (α := α) m β) :
    toIterM it.internalState m β = it :=
  rfl

@[simp]
theorem internalState_toIterM {α m β} (it : α) :
    (toIterM it m β).internalState = it :=
  rfl

/--
Asserts that certain step is plausibly the successor of a given iterator. What "plausible" means
is up to the `Iterator` instance but it should be strong enough to allow termination proofs.
-/
@[expose]
abbrev IterM.IsPlausibleStep {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop :=
  Iterator.IsPlausibleStep (α := α) (m := m)

/--
The type of the step object returned by `IterM.step`, containing an `IterStep`
and a proof that this is a plausible step for the given iterator.
-/
@[expose]
abbrev IterM.Step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) :=
  PlausibleIterStep it.IsPlausibleStep

/--
Asserts that a certain output value could plausibly be emitted by the given iterator in its next
step.
-/
@[expose]
def IterM.IsPlausibleOutput {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) (out : β) : Prop :=
  ∃ it', it.IsPlausibleStep (.yield it' out)

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it`.
-/
@[expose]
def IterM.IsPlausibleSuccessorOf {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.IsPlausibleStep step

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it` while no value is emitted (see `IterStep.skip`).
-/
@[expose]
def IterM.IsPlausibleSkipSuccessorOf {α : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] (it' it : IterM (α := α) m β) : Prop :=
  it.IsPlausibleStep (.skip it')

/--
Makes a single step with the given iterator `it`, potentially emitting a value and providing a
succeeding iterator. If this function is used recursively, termination can sometimes be proved with
the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.
-/
@[always_inline, inline]
def IterM.step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) : m it.Step :=
  Iterator.step it

end Monadic

section Pure

/--
Asserts that certain step is plausibly the successor of a given iterator. What "plausible" means
is up to the `Iterator` instance but it should be strong enough to allow termination proofs.
-/
@[expose]
def Iter.IsPlausibleStep {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (step : IterStep (Iter (α := α) β) β) : Prop :=
  it.toIterM.IsPlausibleStep (step.mapIterator Iter.toIterM)

/--
Asserts that a certain iterator `it` could plausibly yield the value `out` after an arbitrary
number of steps.
-/
inductive IterM.IsPlausibleIndirectOutput {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    : IterM (α := α) m β → β → Prop where
  | direct {it : IterM (α := α) m β} {out : β} : it.IsPlausibleOutput out →
      it.IsPlausibleIndirectOutput out
  | indirect {it it' : IterM (α := α) m β} {out : β} : it'.IsPlausibleSuccessorOf it →
      it'.IsPlausibleIndirectOutput out → it.IsPlausibleIndirectOutput out

/--
The type of the step object returned by `Iter.step`, containing an `IterStep`
and a proof that this is a plausible step for the given iterator.
-/
@[expose]
def Iter.Step {α : Type w} {β : Type w} [Iterator α Id β] (it : Iter (α := α) β) :=
  PlausibleIterStep (Iter.IsPlausibleStep it)

/--
Converts an `Iter.Step` into an `IterM.Step`.
-/
@[always_inline, inline]
def Iter.Step.toMonadic {α : Type w} {β : Type w} [Iterator α Id β] {it : Iter (α := α) β}
    (step : it.Step) : it.toIterM.Step :=
  ⟨step.val.mapIterator Iter.toIterM, step.property⟩

/--
Converts an `IterM.Step` into an `Iter.Step`.
-/
@[always_inline, inline, expose]
def IterM.Step.toPure {α : Type w} {β : Type w} [Iterator α Id β] {it : IterM (α := α) Id β}
    (step : it.Step) : it.toIter.Step :=
  ⟨step.val.mapIterator IterM.toIter, (by simp [Iter.IsPlausibleStep, step.property])⟩

@[simp]
theorem IterM.Step.toPure_yield {α β : Type w} [Iterator α Id β] {it : IterM (α := α) Id β}
    {it' out h} : IterM.Step.toPure (⟨.yield it' out, h⟩ : it.Step) = .yield it'.toIter out h :=
  rfl

@[simp]
theorem IterM.Step.toPure_skip {α β : Type w} [Iterator α Id β] {it : IterM (α := α) Id β}
    {it' h} : IterM.Step.toPure (⟨.skip it', h⟩ : it.Step) = .skip it'.toIter h :=
  rfl

@[simp]
theorem IterM.Step.toPure_done {α β : Type w} [Iterator α Id β] {it : IterM (α := α) Id β}
    {h} : IterM.Step.toPure (⟨.done, h⟩ : it.Step) = .done h :=
  rfl

/--
Asserts that a certain output value could plausibly be emitted by the given iterator in its next
step.
-/
@[expose]
def Iter.IsPlausibleOutput {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (out : β) : Prop :=
  it.toIterM.IsPlausibleOutput out

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it`.
-/
@[expose]
def Iter.IsPlausibleSuccessorOf {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  it'.toIterM.IsPlausibleSuccessorOf it.toIterM

/--
Asserts that a certain iterator `it` could plausibly yield the value `out` after an arbitrary
number of steps.
-/
inductive Iter.IsPlausibleIndirectOutput {α β : Type w} [Iterator α Id β] :
    Iter (α := α) β → β → Prop where
  | direct {it : Iter (α := α) β} {out : β} : it.IsPlausibleOutput out →
      it.IsPlausibleIndirectOutput out
  | indirect {it it' : Iter (α := α) β} {out : β} : it'.IsPlausibleSuccessorOf it →
      it'.IsPlausibleIndirectOutput out → it.IsPlausibleIndirectOutput out

theorem Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM {α β : Type w}
    [Iterator α Id β] {it : Iter (α := α) β} {out : β} :
    it.IsPlausibleIndirectOutput out ↔ it.toIterM.IsPlausibleIndirectOutput out := by
  constructor
  · intro h
    induction h with
    | direct h =>
      exact .direct h
    | indirect h _ ih =>
      exact .indirect h ih
  · intro h
    rw [← Iter.toIter_toIterM (it := it)]
    generalize it.toIterM = it at ⊢ h
    induction h with
    | direct h =>
      exact .direct h
    | indirect h h' ih =>
      rename_i it it' out
      replace h : it'.toIter.IsPlausibleSuccessorOf it.toIter := h
      exact .indirect (α := α) h ih

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it` while no value is emitted (see `IterStep.skip`).
-/
def Iter.IsPlausibleSkipSuccessorOf {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  it'.toIterM.IsPlausibleSkipSuccessorOf it.toIterM

/--
Makes a single step with the given iterator `it`, potentially emitting a value and providing a
succeeding iterator. If this function is used recursively, termination can sometimes be proved with
the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.
-/
@[always_inline, inline, expose]
def Iter.step {α β : Type w} [Iterator α Id β] (it : Iter (α := α) β) : it.Step :=
  it.toIterM.step.run.toPure

end Pure

section Finite

/--
`Finite α m` asserts that `IterM (α := α) m` terminates after finitely many steps. Technically,
this means that the relation of plausible successors is well-founded.
Given this typeclass, termination proofs for well-founded recursion over an iterator `it` can use
`it.finitelyManySteps` as a termination measure.
-/
class Finite (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] : Prop where
  wf : WellFounded (IterM.IsPlausibleSuccessorOf (α := α) (m := m))

/--
This type is a wrapper around `IterM` so that it becomes a useful termination measure for
recursion over finite iterators. See also `IterM.finitelyManySteps` and `Iter.finitelyManySteps`.
-/
structure IterM.TerminationMeasures.Finite
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  it : IterM (α := α) m β

/--
The relation of plausible successors on `IterM.TerminationMeasures.Finite`. It is well-founded
if there is a `Finite` instance.
-/
@[expose]
def IterM.TerminationMeasures.Finite.Rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Finite α m → TerminationMeasures.Finite α m → Prop :=
  Relation.TransGen <| InvImage IterM.IsPlausibleSuccessorOf IterM.TerminationMeasures.Finite.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] : WellFoundedRelation (IterM.TerminationMeasures.Finite α m) where
  rel := IterM.TerminationMeasures.Finite.Rel
  wf := by exact (InvImage.wf _ Finite.wf).transGen

/--
Termination measure to be used in well-founded recursive functions recursing over a finite iterator
(see also `Finite`).
-/
@[expose]
def IterM.finitelyManySteps {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Finite α m :=
  ⟨it⟩

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySteps`.
-/
theorem IterM.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} {out : β} (h : it.IsPlausibleStep (.yield it' out)) :
    Rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

@[inherit_doc IterM.TerminationMeasures.Finite.rel_of_yield]
theorem IterM.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.IsPlausibleStep (.skip it')) :
    Rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
  | fail)

@[inherit_doc IterM.finitelyManySteps, expose]
def Iter.finitelyManySteps {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Finite α Id :=
  it.toIterM.finitelyManySteps

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySteps`.
-/
theorem Iter.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} {out : β} (h : it.IsPlausibleStep (.yield it' out)) :
    IterM.TerminationMeasures.Finite.Rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_yield h

@[inherit_doc Iter.TerminationMeasures.Finite.rel_of_yield]
theorem Iter.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.IsPlausibleStep (.skip it')) :
    IterM.TerminationMeasures.Finite.Rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›
  | fail)

theorem IterM.isPlausibleSuccessorOf_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it' it : IterM (α := α) m β} {out : β} (h : it.IsPlausibleStep (.yield it' out)) :
    it'.IsPlausibleSuccessorOf it :=
  ⟨_, rfl, h⟩

theorem IterM.isPlausibleSuccessorOf_of_skip
    {α m β} [Iterator α m β] {it it' : IterM (α := α) m β}
    (h : it.IsPlausibleStep (.skip it')) :
    it'.IsPlausibleSuccessorOf it :=
  ⟨_, rfl, h⟩

end Finite

section Productive

/--
`Productive α m` asserts that `IterM (α := α) m` terminates or emits a value after finitely many
skips. Technically, this means that the relation of plausible successors during skips is
well-founded.
Given this typeclass, termination proofs for well-founded recursion over an iterator `it` can use
`it.finitelyManySkips` as a termination measure.
-/
class Productive (α m) {β} [Iterator α m β] : Prop where
  wf : WellFounded (IterM.IsPlausibleSkipSuccessorOf (α := α) (m := m))

/--
This type is a wrapper around `IterM` so that it becomes a useful termination measure for
recursion over productive iterators. See also `IterM.finitelyManySkips` and `Iter.finitelyManySkips`.
-/
structure IterM.TerminationMeasures.Productive
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  it : IterM (α := α) m β

/--
The relation of plausible successors while skipping on `IterM.TerminationMeasures.Productive`.
It is well-founded if there is a `Productive` instance.
-/
@[expose]
def IterM.TerminationMeasures.Productive.Rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Productive α m → TerminationMeasures.Productive α m → Prop :=
  Relation.TransGen <| InvImage IterM.IsPlausibleSkipSuccessorOf IterM.TerminationMeasures.Productive.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] : WellFoundedRelation (IterM.TerminationMeasures.Productive α m) where
  rel := IterM.TerminationMeasures.Productive.Rel
  wf := by exact (InvImage.wf _ Productive.wf).transGen

/--
Termination measure to be used in well-founded recursive functions recursing over a productive
iterator (see also `Productive`).
-/
@[expose]
def IterM.finitelyManySkips {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Productive α m :=
  ⟨it⟩

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySkips`.
-/
theorem IterM.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.IsPlausibleStep (.skip it')) :
    Rel ⟨it'⟩ ⟨it⟩ :=
  .single h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
    | exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    | fail)

@[inherit_doc IterM.finitelyManySkips, expose]
def Iter.finitelyManySkips {α : Type w} {β : Type w} [Iterator α Id β] [Productive α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Productive α Id :=
  it.toIterM.finitelyManySkips

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `Iter.finitelyManySkips`.
-/
theorem Iter.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.IsPlausibleStep (.skip it')) :
    IterM.TerminationMeasures.Productive.Rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Productive.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
    | exact Iter.TerminationMeasures.Productive.rel_of_skip ‹_›
    | fail)

instance [Iterator α m β] [Finite α m] : Productive α m where
  wf := by
    apply Subrelation.wf (r := IterM.IsPlausibleSuccessorOf)
    · intro it' it h
      exact IterM.isPlausibleSuccessorOf_of_skip h
    · exact Finite.wf

end Productive

end Iterators

export Iterators (Iter IterM)

end Std
