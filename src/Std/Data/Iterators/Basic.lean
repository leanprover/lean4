/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Classical
import Init.NotationExtra
import Init.TacticsExtra

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

See `Std.Data.Iterators.Consumers` for ways to use an iterator. For example, `it.toList` will
convert a provably finite iterator `it` into a list and `it.allowNontermination.toList` will
do so even if finiteness cannot be proved. It is also always possible to manually iterate using
`it.step`, relying on the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.

See `Std.Data.Iterators.Combinators` for ways to compose iterators. For example, `it.map f` is
the iterator that applies a function `f` to every value emitted by `it`.

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
structure IterM {α : Type w} (m : Type w → Type w') (β : Type w) : Type w where
  inner : α

/--
An iterator that sequentially emits values of type `β`. It may be finite
or infinite.

See the root module `Std.Data.Iterators` for a more comprehensive overview over the iterator
framework.

See `Std.Data.Iterators.Producers` for ways to iterate over common data structures.
By convention, the monadic iterator associated with an object can be obtained via dot notation.
For example, `List.iterM IO` creates an iterator over a list in the monad `IO`.

See `Std.Data.Iterators.Consumers` for ways to use an iterator. For example, `it.toList` will
convert a provably finite iterator `it` into a list and `it.allowNontermination.toList` will
do so even if finiteness cannot be proved. It is also always possible to manually iterate using
`it.step`, relying on the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.

See `Std.Data.Iterators.Combinators` for ways to compose iterators. For example, `it.map f` is
the iterator that applies a function `f` to every value emitted by `it`.

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
structure Iter {α : Type w} (β : Type w) : Type w where
  inner : α

/--
Converts a pure iterator (`Iter β`) into a monadic iterator (`IterM Id β`) in the
identity monad `Id`.
-/
def Iter.toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) : IterM (α := α) Id β :=
  ⟨it.inner⟩

/--
Converts a monadic iterator (`IterM Id β`) over `Id` into a pure iterator (`Iter β`).
-/
def IterM.toPureIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) : Iter (α := α) β :=
  ⟨it.inner⟩

@[simp]
theorem Iter.toPureIter_toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) :
    it.toIterM.toPureIter = it :=
  rfl

@[simp]
theorem Iter.toIterM_toPureIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) :
    it.toPureIter.toIterM = it :=
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
def IterStep.successor : IterStep α β → Option α
  | .yield it _ => some it
  | .skip it => some it
  | .done => none

/--
Applies functions to the succeeding iterator and the emitted value stored in an `IterStep`.
-/
@[always_inline, inline]
def IterStep.map {α' : Type u'} {β' : Type v'} (f : α → α') (g : β → β') :
    IterStep α β → IterStep α' β'
  | .yield it out => .yield (f it) (g out)
  | .skip it => .skip (f it)
  | .done => .done

theorem IterStep.map_id {it : IterStep α β} :
    it.map id id = it := by
  simp only [map]
  cases it <;> simp

theorem IterStep.map_id' {it : IterStep α β} :
    it.map (·) (·) = it :=
  map_id

@[simp]
theorem IterStep.map_done {f : α → α'} {g : β → β'} :
  (.done : IterStep α β).map f g = .done := rfl

@[simp]
theorem IterStep.map_skip {f : α → α'} {g : β → β'} :
  (.skip it : IterStep α β).map f g = .skip (f it) := rfl

@[simp]
theorem IterStep.map_yield {f : α → α'} {g : β → β'} :
  (.yield it out : IterStep α β).map f g = .yield (f it) (g out) := rfl

theorem IterStep.map_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'}
    {α'' : Type u''} {β'' : Type v''} {f' : α' → α''} {g' : β' → β''} {it : IterStep α β} :
    (it.map f g).map f' g' = it.map (f · |> f') (g · |> g') := by
  simp only [map]
  cases it <;> simp

theorem IterStep.successor_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'} {step : IterStep α β} :
    (step.map f g).successor = step.successor.elim none (some <| f ·) := by
  cases step <;> rfl

/--
A variant of `IterStep` that bundles the step together with a proof that it is "plausible".
The plausibility predicate will later be chosen to assert that a state is a plausible successor
of another state. Having this proof bundled up with the step is important for termination proofs.

See `IterM.Step` and `Iter.Step` for the concrete choice of the plausibility predicate.
-/
def PlausibleIterStep (plausible_step : IterStep α β → Prop) := Subtype plausible_step

/--
Match pattern for the `yield` case. See also `IterStep.yield`.
-/
@[match_pattern]
def PlausibleIterStep.yield {plausible_step : IterStep α β → Prop}
    (it' : α) (out : β) (h : plausible_step (.yield it' out)) : PlausibleIterStep plausible_step :=
  ⟨.yield it' out, h⟩

/--
Match pattern for the `skip` case. See also `IterStep.skip`.
-/
@[match_pattern]
def PlausibleIterStep.skip {plausible_step : IterStep α β → Prop}
    (it' : α) (h : plausible_step (.skip it')) : PlausibleIterStep plausible_step :=
  ⟨.skip it', h⟩

/--
Match pattern for the `done` case. See also `IterStep.done`.
-/
@[match_pattern]
def PlausibleIterStep.done {plausible_step : IterStep α β → Prop}
    (h : plausible_step .done) : PlausibleIterStep plausible_step :=
  ⟨.done, h⟩

/--
Applies functions to the succeeding iterator and the emitted value stored in a `PlausibleIterStep`.
See also `IterStep.map`.
-/
@[always_inline, inline]
def PlausibleIterStep.map {plausible_step : IterStep α β → Prop}
    {α' : Type u'} {β' : Type v'} (f : α → α') (g : β → β') (new_plausible_step : IterStep α' β' → Prop)
    (h : ∀ step : IterStep α β, plausible_step step → new_plausible_step (step.map f g))
    (step : PlausibleIterStep plausible_step) : PlausibleIterStep new_plausible_step :=
  ⟨step.val.map f g, h _ step.property⟩

theorem PlausibleIterStep.map_id {plausible_step : IterStep α β → Prop}
    {it : PlausibleIterStep plausible_step} :
    it.map id id plausible_step (by simp [IterStep.map_id]) = it := by
  simp only [map, IterStep.map]
  cases it <;> dsimp only <;> split <;> simp

end IterStep

/--
The typeclass providing the step function of an iterator in `Iter (α := α) β` or
`IterM (α := α) m β`.

In order to allow intrinsic termination proofs when iterating with the `step` function, the
step object is bundled with a proof that it is a "plausible" step for the given current iterator.
-/
class Iterator (α : Type w) (m : Type w → Type w') (β : outParam (Type w)) where
  plausible_step : IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop
  step : (it : IterM (α := α) m β) → m (PlausibleIterStep <| plausible_step it)

section Monadic

/--
Converts wraps the state of an iterator into an `IterM` object.
-/
@[always_inline, inline]
def toIterM {α : Type w} (it : α) (m : Type w → Type w') (β : Type w) :
    IterM (α := α) m β :=
  ⟨it⟩

@[simp]
theorem toIterM_inner {α m β} (it : IterM (α := α) m β) :
    toIterM it.inner m β = it :=
  rfl

@[simp]
theorem inner_toIterM {α m β} (it : α) :
    (toIterM it m β).inner = it :=
  rfl

/--
Asserts that certain step is plausibly the successor of a given iterator. What "plausible" means
is up to the `Iterator` instance but it should be strong enough to allow termination proofs.
-/
abbrev IterM.plausible_step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop :=
  Iterator.plausible_step (α := α) (m := m)

/--
The type of the step object returned by `IterM.step`, containing an `IterStep`
and a proof that this is a plausible step for the given iterator.
-/
abbrev IterM.Step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) :=
  PlausibleIterStep it.plausible_step

/--
Asserts that a certain output value could plausibly be emitted by the given iterator in its next
step.
-/
def IterM.plausible_output {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) (out : β) : Prop :=
  ∃ it', it.plausible_step (.yield it' out)

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it`.
-/
def IterM.plausible_successor_of {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.plausible_step step

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it` while no value is emitted (see `IterStep.skip`).
-/
def IterM.plausible_skip_successor_of {α : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] (it' it : IterM (α := α) m β) : Prop :=
  it.plausible_step (.skip it')

/--
Makes a single step with the given iterator `it`, potentially emitting a value and providing a
succeeding iterator. If this function is used recursively, termination can sometimes be proved with
the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.
-/
def IterM.step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) : m it.Step :=
  Iterator.step it

end Monadic

section Pure

/--
Asserts that certain step is plausibly the successor of a given iterator. What "plausible" means
is up to the `Iterator` instance but it should be strong enough to allow termination proofs.
-/
def Iter.plausible_step {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (step : IterStep (Iter (α := α) β) β) : Prop :=
  it.toIterM.plausible_step (step.map Iter.toIterM id)

/--
The type of the step object returned by `Iter.step`, containing an `IterStep`
and a proof that this is a plausible step for the given iterator.
-/
def Iter.Step {α : Type w} {β : Type w} [Iterator α Id β] (it : Iter (α := α) β) :=
  PlausibleIterStep (Iter.plausible_step it)

/--
Asserts that a certain output value could plausibly be emitted by the given iterator in its next
step.
-/
def Iter.plausible_output {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (out : β) : Prop :=
  ∃ it', it.plausible_step (.yield it' out)

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it`.
-/
def Iter.plausible_successor_of {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.plausible_step step

/--
Asserts that a certain iterator `it'` could plausibly be the directly succeeding iterator of another
given iterator `it` while no value is emitted (see `IterStep.skip`).
-/
def Iter.plausible_skip_successor_of {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  it.plausible_step (.skip it')

/--
Makes a single step with the given iterator `it`, potentially emitting a value and providing a
succeeding iterator. If this function is used recursively, termination can sometimes be proved with
the termination measures `it.finitelyManySteps` and `it.finitelyManySkips`.
-/
@[always_inline, inline]
def Iter.step {α β : Type w} [Iterator α Id β] (it : Iter (α := α) β) : it.Step := by
  refine it.toIterM.step.run.map IterM.toPureIter id _ ?_
  intro step hp
  simp only [Iter.plausible_step, IterStep.map_map, id_eq, IterStep.map_id', toIterM_toPureIter, hp]

end Pure

section Finite

/--
`Finite α m` asserts that `IterM (α := α) m` terminates after finitely many steps. Technically,
this means that the relation of plausible successors is well-founded.
Given this typeclass, termination proofs for well-founded recursion over an iterator `it` can use
`it.finitelyManySteps` as a termination measure.
-/
class Finite (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] : Prop where
  wf : WellFounded (IterM.plausible_successor_of (α := α) (m := m))

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
def IterM.TerminationMeasures.Finite.rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Finite α m → TerminationMeasures.Finite α m → Prop :=
  Relation.TransGen <| InvImage IterM.plausible_successor_of IterM.TerminationMeasures.Finite.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] : WellFoundedRelation (IterM.TerminationMeasures.Finite α m) where
  rel := IterM.TerminationMeasures.Finite.rel
  wf := (InvImage.wf _ Finite.wf).transGen

/--
Termination measure to be used in well-founded recursive functions recursing over a finite iterator
(see also `Finite`).
-/
def IterM.finitelyManySteps {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Finite α m :=
  ⟨it⟩

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySteps`.
-/
theorem IterM.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} {out : β} (h : it.plausible_step (.yield it' out)) :
    rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

@[inherit_doc IterM.TerminationMeasures.Finite.rel_of_yield]
theorem IterM.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.plausible_step (.skip it')) :
    rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›)

@[inherit_doc IterM.finitelyManySteps]
def Iter.finitelyManySteps {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Finite α Id :=
  it.toIterM.finitelyManySteps

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySteps`.
-/
theorem Iter.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} {out : β} (h : it.plausible_step (.yield it' out)) :
    IterM.TerminationMeasures.Finite.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_yield h

@[inherit_doc Iter.TerminationMeasures.Finite.rel_of_yield]
theorem Iter.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.plausible_step (.skip it')) :
    IterM.TerminationMeasures.Finite.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›)

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
  wf : WellFounded (IterM.plausible_skip_successor_of (α := α) (m := m))

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
def IterM.TerminationMeasures.Productive.rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Productive α m → TerminationMeasures.Productive α m → Prop :=
  Relation.TransGen <| InvImage IterM.plausible_skip_successor_of IterM.TerminationMeasures.Productive.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] : WellFoundedRelation (IterM.TerminationMeasures.Productive α m) where
  rel := IterM.TerminationMeasures.Productive.rel
  wf := (InvImage.wf _ Productive.wf).transGen

/--
Termination measure to be used in well-founded recursive functions recursing over a productive
iterator (see also `Productive`).
-/
def IterM.finitelyManySkips {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Productive α m :=
  ⟨it⟩

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `IterM.finitelyManySkips`.
-/
theorem IterM.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.plausible_step (.skip it')) :
    rel ⟨it'⟩ ⟨it⟩ :=
  .single h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›)

@[inherit_doc IterM.finitelyManySkips]
def Iter.finitelyManySkips {α : Type w} {β : Type w} [Iterator α Id β] [Productive α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Productive α Id :=
  it.toIterM.finitelyManySkips

/--
This theorem is used by a `decreasing_trivial` extension. It powers automatic termination proofs
with `Iter.finitelyManySkips`.
-/
theorem Iter.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.plausible_step (.skip it')) :
    IterM.TerminationMeasures.Productive.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Productive.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact Iter.TerminationMeasures.Productive.rel_of_skip ‹_›)

end Productive

end Iterators

export Iterators (Iter IterM)

end Std
