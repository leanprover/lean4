/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.RCases
import Std.Data.Iterators.Basic
import Std.Data.Iterators.Consumers.Monadic.Partial

/-!
# Loop-based consumers

This module provides consumers that iterate over a given iterator, applying a certain user-supplied
function in every iteration. Concretely, the following operations are provided:

* `ForIn` instances
* `IterM.fold`, the analogue of `List.foldl`
* `IterM.foldM`, the analogue of `List.foldlM`
* `IterM.drain`, which iterates over the whole iterator and discards all emitted values. It can
  be used to apply the monadic effects of the iterator.

Some producers and combinators provide specialized implementations. These are captured by the
`IteratorLoop` and `IteratorLoopPartial` typeclasses. They should be implemented by all
types of iterators. A default implementation is provided. The typeclass `LawfulIteratorLoop`
asserts that an `IteratorLoop` instance equals the default implementation.
-/

namespace Std.Iterators

section Typeclasses

/--
Relation that needs to be well-formed in order for a loop over an iterator to terminate.
It is assumed that the `plausible_forInStep` predicate relates the input and output of the
stepper function.
-/
def IteratorLoop.rel (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop)
    (p' p : IterM (α := α) m β × γ) : Prop :=
  (∃ b, p.1.IsPlausibleStep (.yield p'.1 b) ∧ plausible_forInStep b p.2 (.yield p'.2)) ∨
    (p.1.IsPlausibleStep (.skip p'.1) ∧ p'.2 = p.2)

/--
Asserts that `IteratorLoop.rel` is well-founded.
-/
def IteratorLoop.WellFounded (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop) : Prop :=
    _root_.WellFounded (IteratorLoop.rel α m plausible_forInStep)

/--
`IteratorLoop α m` provides efficient implementations of loop-based consumers for `α`-based
iterators. The basis is a `ForIn`-style loop construct with the complication that it can be used
for infinite iterators, too -- given a proof that the given loop will nevertheless terminate.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorLoop (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type w → Type w'') where
  forIn : ∀ (_lift : (γ : Type w) → m γ → n γ) (γ : Type w),
      (plausible_forInStep : β → γ → ForInStep γ → Prop) →
      IteratorLoop.WellFounded α m plausible_forInStep →
      IterM (α := α) m β → γ →
      ((b : β) → (c : γ) → n (Subtype (plausible_forInStep b c))) → n γ

/--
`IteratorLoopPartial α m` provides efficient implementations of loop-based consumers for `α`-based
iterators. The basis is a partial, i.e. potentially nonterminating, `ForIn` instance.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorLoopPartial (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type w → Type w'') where
  forInPartial : ∀ (_lift : (γ : Type w) → m γ → n γ) {γ : Type w},
      IterM (α := α) m β → γ → ((b : β) → (c : γ) → n (ForInStep γ)) → n γ

end Typeclasses

private def IteratorLoop.WFRel {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {γ : Type x} {plausible_forInStep : β → γ → ForInStep γ → Prop}
    (_wf : WellFounded α m plausible_forInStep) :=
  IterM (α := α) m β × γ

private def IteratorLoop.WFRel.mk {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {γ : Type x} {plausible_forInStep : β → γ → ForInStep γ → Prop}
    (wf : WellFounded α m plausible_forInStep) (it : IterM (α := α) m β) (c : γ) :
    IteratorLoop.WFRel wf :=
  (it, c)

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {γ : Type x} {plausible_forInStep : β → γ → ForInStep γ → Prop}
    (wf : IteratorLoop.WellFounded α m plausible_forInStep) :
    WellFoundedRelation (IteratorLoop.WFRel wf) where
  rel := IteratorLoop.rel α m plausible_forInStep
  wf := wf

/--
This is the loop implementation of the default instance `IteratorLoop.defaultImplementation`.
-/
@[specialize]
def IterM.DefaultConsumers.forIn {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type w → Type w''} [Monad n]
    (lift : ∀ γ, m γ → n γ) (γ : Type w)
    (plausible_forInStep : β → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded α m plausible_forInStep)
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → (c : γ) → n (Subtype (plausible_forInStep b c))) : n γ :=
  haveI : WellFounded _ := wf
  letI : MonadLift m n := ⟨fun {γ} => lift γ⟩
  do
    match ← it.step with
    | .yield it' out _ =>
      match ← f out init with
      | ⟨.yield c, _⟩ => IterM.DefaultConsumers.forIn lift _ plausible_forInStep wf it' c f
      | ⟨.done c, _⟩ => return c
    | .skip it' _ => IterM.DefaultConsumers.forIn lift _ plausible_forInStep wf it' init f
    | .done _ => return init
termination_by IteratorLoop.WFRel.mk wf it init
decreasing_by
  · exact Or.inl ⟨out, ‹_›, ‹_›⟩
  · exact Or.inr ⟨‹_›, rfl⟩

/--
This is the default implementation of the `IteratorLoop` class.
It simply iterates through the iterator using `IterM.step`. For certain iterators, more efficient
implementations are possible and should be used instead.
-/
@[always_inline, inline]
def IteratorLoop.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [Iterator α m β] :
    IteratorLoop α m n where
  forIn lift := IterM.DefaultConsumers.forIn lift

/--
Asserts that a given `IteratorLoop` instance is equal to `IteratorLoop.defaultImplementation`.
(Even though equal, the given instance might be vastly more efficient.)
-/
class LawfulIteratorLoop (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    [Monad n] [Iterator α m β] [Finite α m] [i : IteratorLoop α m n] where
  lawful : i = .defaultImplementation

/--
This is the loop implementation of the default instance `IteratorLoopPartial.defaultImplementation`.
-/
@[specialize]
partial def IterM.DefaultConsumers.forInPartial {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type w → Type w''} [Monad n]
    (lift : ∀ γ, m γ → n γ) (γ : Type w)
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → (c : γ) → n (ForInStep γ)) : n γ :=
  letI : MonadLift m n := ⟨fun {γ} => lift γ⟩
  do
    match ← it.step with
    | .yield it' out _ =>
      match ← f out init with
      | .yield c => IterM.DefaultConsumers.forInPartial lift _ it' c f
      | .done c => return c
    | .skip it' _ => IterM.DefaultConsumers.forInPartial lift _ it' init f
    | .done _ => return init

/--
This is the default implementation of the `IteratorLoopPartial` class.
It simply iterates through the iterator using `IterM.step`. For certain iterators, more efficient
implementations are possible and should be used instead.
-/
@[always_inline, inline]
def IteratorLoopPartial.defaultImplementation {α : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoopPartial α m n where
  forInPartial lift := IterM.DefaultConsumers.forInPartial lift _

instance (α : Type w) (m : Type w → Type w') (n : Type w → Type w')
    [Monad m] [Monad n] [Iterator α m β] [Finite α m] :
    letI : IteratorLoop α m n := .defaultImplementation
    LawfulIteratorLoop α m n :=
  letI : IteratorLoop α m n := .defaultImplementation
  ⟨rfl⟩

theorem IteratorLoop.wellFounded_of_finite {m : Type w → Type w'}
    {α β γ : Type w} [Iterator α m β] [Finite α m] :
    WellFounded α m (γ := γ) fun _ _ _ => True := by
  apply Subrelation.wf
    (r := InvImage IterM.TerminationMeasures.Finite.Rel (fun p => p.1.finitelyManySteps))
  · intro p' p h
    apply Relation.TransGen.single
    obtain ⟨b, h, _⟩ | ⟨h, _⟩ := h
    · exact ⟨.yield p'.fst b, rfl, h⟩
    · exact ⟨.skip p'.fst, rfl, h⟩
  · apply InvImage.wf
    exact WellFoundedRelation.wf

/--
This `ForIn`-style loop construct traverses a finite iterator using an `IteratorLoop` instance.
-/
@[always_inline, inline]
def IteratorLoop.finiteForIn {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [Finite α m] [IteratorLoop α m n]
    (lift : ∀ γ, m γ → n γ) :
    ForIn n (IterM (α := α) m β) β where
  forIn {γ} [Monad n] it init f :=
    IteratorLoop.forIn (α := α) (m := m) lift γ (fun _ _ _ => True)
      wellFounded_of_finite
      it init ((⟨·, .intro⟩) <$> f · ·)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [Finite α m] [IteratorLoop α m n]
    [MonadLiftT m n] :
    ForIn n (IterM (α := α) m β) β := IteratorLoop.finiteForIn (fun _ => monadLift)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoopPartial α m n] [MonadLiftT m n] :
    ForIn n (IterM.Partial (α := α) m β) β where
  forIn it init f :=
    IteratorLoopPartial.forInPartial (α := α) (m := m) (fun _ => monadLift) it.it init f

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [Finite α m] [IteratorLoop α m n]
    [MonadLiftT m n] :
    ForM n (IterM (α := α) m β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [Finite α m] [IteratorLoopPartial α m n]
    [MonadLiftT m n] :
    ForM n (IterM.Partial (α := α) m β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

The monadic effects of `f` are interleaved with potential effects caused by the iterator's step
function. Therefore, it may *not* be equivalent to `(← it.toList).foldlM`.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.foldM` instead of `it.foldM`. However, it is not possible to formally
verify the behavior of the partial variant.
-/
@[always_inline, inline]
def IterM.foldM {m : Type w → Type w'} {n : Type w → Type w''} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [Finite α m] [IteratorLoop α m n]
    [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

The monadic effects of `f` are interleaved with potential effects caused by the iterator's step
function. Therefore, it may *not* be equivalent to `it.toList.foldlM`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.foldM` instead.
-/
@[always_inline, inline]
def IterM.Partial.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [IteratorLoopPartial α m n]
    [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM.Partial (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.fold` instead of `it.fold`. However, it is not possible to formally
verify the behavior of the partial variant.
-/
@[always_inline, inline]
def IterM.fold {m : Type w → Type w'} {α : Type w} {β : Type w} {γ : Type w} [Monad m]
    [Iterator α m β] [Finite α m] [IteratorLoop α m m]
    (f : γ → β → γ) (init : γ) (it : IterM (α := α) m β) : m γ :=
  ForIn.forIn (m := m) it init (fun x acc => pure (ForInStep.yield (f acc x)))

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.fold` instead.
-/
@[always_inline, inline]
def IterM.Partial.fold {m : Type w → Type w'} {α : Type w} {β : Type w} {γ : Type w}
    [Monad m] [Iterator α m β] [IteratorLoopPartial α m m]
    (f : γ → β → γ) (init : γ) (it : IterM.Partial (α := α) m β) : m γ :=
  ForIn.forIn (m := m) it init (fun x acc => pure (ForInStep.yield (f acc x)))

/--
Iterates over the whole iterator, applying the monadic effects of each step, discarding all
emitted values.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.drain` instead of `it.drain`. However, it is not possible to formally
verify the behavior of the partial variant.
-/
@[always_inline, inline]
def IterM.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] (it : IterM (α := α) m β) [IteratorLoop α m m] :
    m PUnit :=
  it.fold (γ := PUnit) (fun _ _ => .unit) .unit

/--
Iterates over the whole iterator, applying the monadic effects of each step, discarding all
emitted values.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.drain` instead.
-/
@[always_inline, inline]
def IterM.Partial.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorLoopPartial α m m] :
    m PUnit :=
  it.fold (γ := PUnit) (fun _ _ => .unit) .unit

end Std.Iterators
