/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Partial
public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
public import Init.Internal.ExtrinsicTermination

public section

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

open Std.Internal

section Typeclasses

/--
Relation that needs to be well-formed in order for a loop over an iterator to terminate.
It is assumed that the `plausible_forInStep` predicate relates the input and output of the
stepper function.
-/
@[expose]
def IteratorLoop.rel (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop)
    (p' p : IterM (α := α) m β × γ) : Prop :=
  (∃ b, p.1.IsPlausibleStep (.yield p'.1 b) ∧ plausible_forInStep b p.2 (.yield p'.2)) ∨
    (p.1.IsPlausibleStep (.skip p'.1) ∧ p'.2 = p.2)

/--
Asserts that `IteratorLoop.rel` is well-founded.
-/
@[expose]
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
@[ext]
class IteratorLoop (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type x → Type x') where
  forIn : ∀ (_liftBind : (γ : Type w) → (δ : Type x) → (γ → n δ) → m γ → n δ) (γ : Type x),
      (it : IterM (α := α) m β) → γ →
      ((b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (ForInStep γ)) → n γ

/--
`IteratorLoopPartial α m` provides efficient implementations of loop-based consumers for `α`-based
iterators. The basis is a partial, i.e. potentially nonterminating, `ForIn` instance.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorLoopPartial (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type x → Type x') where
  forInPartial : ∀ (_liftBind : (γ : Type w) → (δ : Type x) → (γ → n δ) → m γ → n δ) {γ : Type x},
      (it : IterM (α := α) m β) → γ →
      ((b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (ForInStep γ)) → n γ

/--
`IteratorSize α m` provides an implementation of the `IterM.size` function.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorSize (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  size : IterM (α := α) m β → m (ULift Nat)

/--
`IteratorSizePartial α m` provides an implementation of the `IterM.Partial.size` function that
can be used as `it.allowTermination.size`.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorSizePartial (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  size : IterM (α := α) m β → m (ULift Nat)

end Typeclasses

/-- Internal implementation detail of the iterator library. -/
structure IteratorLoop.WithWF (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (hwf : IteratorLoop.WellFounded α m PlausibleForInStep) where
  it : IterM (α := α) m β
  acc : γ

instance IteratorLoop.WithWF.instWellFoundedRelation
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (hwf : IteratorLoop.WellFounded α m PlausibleForInStep) :
    WellFoundedRelation (WithWF α m PlausibleForInStep hwf) where
  rel := InvImage (IteratorLoop.rel α m PlausibleForInStep) (fun x => (x.it, x.acc))
  wf := by exact InvImage.wf _ hwf

/--
This is the loop implementation of the default instance `IteratorLoop.defaultImplementation`.
-/
@[always_inline, expose]
def IterM.DefaultConsumers.forIn' {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) (γ : Type x)
    (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (ForInStep γ)) : n γ :=
  haveI : Nonempty γ := ⟨init⟩
  extrinsicFix₃ (C₃ := fun _ _ _ => n γ)
    (fun it acc (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b) recur => (lift _ _ · it.step) fun s => do
      match s.inflate with
      | .yield it' out h =>
        match ← f out (hP out <| .direct ⟨_, h⟩) acc with
        | .yield c => recur it' c (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h')
        | .done c => return c
      | .skip it' h => recur it' acc (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h')
      | .done _ => return acc) it init hP

/--
This is the loop implementation of the default instance `IteratorLoop.defaultImplementation`.
-/
@[specialize, expose]
def IterM.DefaultConsumers.forIn'.wf {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) (γ : Type x)
    (plausible_forInStep : β → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded α m plausible_forInStep)
    (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (plausible_forInStep b c))) : n γ :=
  haveI : WellFounded _ := wf
  (lift _ _ · it.step) fun s =>
    match s.inflate with
    | .yield it' out h => do
      match ← f out (hP _ <| .direct ⟨_, h⟩) init with
      | ⟨.yield c, _⟩ =>
        IterM.DefaultConsumers.forIn'.wf lift _ plausible_forInStep wf it' c P
          (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
      | ⟨.done c, _⟩ => return c
    | .skip it' h =>
      IterM.DefaultConsumers.forIn'.wf lift _ plausible_forInStep wf it' init P
          (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
    | .done _ => return init
termination_by IteratorLoop.WithWF.mk it init (hwf := wf)
decreasing_by
  · exact Or.inl ⟨out, ‹_›, ‹_›⟩
  · exact Or.inr ⟨‹_›, rfl⟩

/--
This is the default implementation of the `IteratorLoop` class.
It simply iterates through the iterator using `IterM.step`. For certain iterators, more efficient
implementations are possible and should be used instead.
-/
@[always_inline, expose]
def IteratorLoop.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type x → Type x'}
    [Monad n] [Iterator α m β] :
    IteratorLoop α m n where
  forIn lift γ it init := IterM.DefaultConsumers.forIn' lift γ it init _ (fun _ => id)

/--
Asserts that a given `IteratorLoop` instance is equal to `IteratorLoop.defaultImplementation`.
(Even though equal, the given instance might be vastly more efficient.)
-/
class LawfulIteratorLoop (α : Type w) (m : Type w → Type w') (n : Type x → Type x')
    [Monad m] [Monad n] [Iterator α m β] [i : IteratorLoop α m n] where
  lawful lift [LawfulMonadLiftBindFunction lift] γ it init
      (Pl : β → γ → ForInStep γ → Prop) (wf : IteratorLoop.WellFounded α m Pl)
      (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    i.forIn lift γ it init (Subtype.val <$> f · · ·) =
      IteratorLoop.defaultImplementation.forIn lift γ it init (Subtype.val <$> f · · ·)

/--
This is the loop implementation of the default instance `IteratorLoopPartial.defaultImplementation`.
-/
@[specialize]
partial def IterM.DefaultConsumers.forInPartial {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) (γ : Type x)
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (ForInStep γ)) : n γ :=
  (lift _ _ · it.step) fun s =>
      match s.inflate with
      | .yield it' out h => do
        match ← f out (.direct ⟨_, h⟩) init with
        | .yield c =>
          IterM.DefaultConsumers.forInPartial lift _ it' c
            fun out h' acc => f out (.indirect ⟨_, rfl, h⟩ h') acc
        | .done c => return c
      | .skip it' h =>
        IterM.DefaultConsumers.forInPartial lift _ it' init
          fun out h' acc => f out (.indirect ⟨_, rfl, h⟩ h') acc
      | .done _ => return init

/--
This is the default implementation of the `IteratorLoopPartial` class.
It simply iterates through the iterator using `IterM.step`. For certain iterators, more efficient
implementations are possible and should be used instead.
-/
@[always_inline, inline]
def IteratorLoopPartial.defaultImplementation {α : Type w} {m : Type w → Type w'}
    {n : Type x → Type x'} [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoopPartial α m n where
  forInPartial lift := IterM.DefaultConsumers.forInPartial lift _

instance (α : Type w) (m : Type w → Type w') (n : Type x → Type x')
    [Monad m] [Monad n] [Iterator α m β] [Finite α m] :
    letI : IteratorLoop α m n := .defaultImplementation
    LawfulIteratorLoop α m n := by
  letI : IteratorLoop α m n := .defaultImplementation
  constructor; simp

theorem IteratorLoop.wellFounded_of_finite {m : Type w → Type w'}
    {α β : Type w} {γ : Type x} [Iterator α m β] [Finite α m] :
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
This `ForIn'`-style loop construct traverses a finite iterator using an `IteratorLoop` instance.
-/
@[always_inline]
def IteratorLoop.finiteForIn' {m : Type w → Type w'} {n : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {γ} [Monad n] it init f :=
    IteratorLoop.forIn (α := α) (m := m) lift γ it init (fun out h acc => (f out h acc))

/--
A `ForIn'` instance for iterators. Its generic membership relation is not easy to use,
so this is not marked as `instance`. This way, more convenient instances can be built on top of it
or future library improvements will make it more comfortable.
-/
@[always_inline]
def IterM.instForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    [MonadLiftT m n] :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ :=
  IteratorLoop.finiteForIn' (fun _ _ f x => monadLift x >>= f)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n]
    [MonadLiftT m n] [Monad n] :
    ForIn n (IterM (α := α) m β) β :=
  haveI : ForIn' n (IterM (α := α) m β) β _ := IterM.instForIn'
  instForInOfForIn'

@[always_inline]
def IterM.Partial.instForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoopPartial α m n] [MonadLiftT m n] [Monad n] :
    ForIn' n (IterM.Partial (α := α) m β) β ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := IteratorLoopPartial.forInPartial (α := α) (m := m) (n := n)
      (fun _ _ f x => monadLift x >>= f) it.it init f

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoopPartial α m n] [MonadLiftT m n] [Monad n] :
    ForIn n (IterM.Partial (α := α) m β) β :=
  haveI : ForIn' n (IterM.Partial (α := α) m β) β _ := IterM.Partial.instForIn'
  instForInOfForIn'

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n]
    [MonadLiftT m n] :
    ForM n (IterM (α := α) m β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoopPartial α m n]
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
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [IteratorLoop α m n]
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
    [Iterator α m β] [IteratorLoop α m m]
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
    [Iterator α m β] (it : IterM (α := α) m β) [IteratorLoop α m m] :
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

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This function requires a {name}`Finite` instance proving that the iterator will finish after a
finite number of steps. If the iterator is not finite or such an instance is not available,
consider using {lit}`it.allowNontermination.anyM` instead of {lean}`it.anyM`. However, it is not
possible to formally verify the behavior of the partial variant.
-/
@[specialize]
def IterM.anyM {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m]
    (p : β → m (ULift Bool)) (it : IterM (α := α) m β) : m (ULift Bool) :=
  ForIn.forIn it (ULift.up false) (fun x _ => do
    if (← p x).down then
      return .done (.up true)
    else
      return .yield (.up false))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a {name}`Finite` instance, consider using {name}`IterM.anyM`
instead.
-/
@[specialize]
def IterM.Partial.anyM {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoopPartial α m m]
    (p : β → m (ULift Bool)) (it : IterM.Partial (α := α) m β) : m (ULift Bool) :=
  ForIn.forIn it (ULift.up false) (fun x _ => do
    if (← p x).down then
      return .done (.up true)
    else
      return .yield (.up false))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This function requires a {name}`Finite` instance proving that the iterator will finish after a
finite number of steps. If the iterator is not finite or such an instance is not available,
consider using {lit}`it.allowNontermination.any` instead of {lean}`it.any`. However, it is not
possible to formally verify the behavior of the partial variant.
-/
@[inline]
def IterM.any {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m]
    (p : β → Bool) (it : IterM (α := α) m β) : m (ULift Bool) := do
  it.anyM (fun x => pure (.up (p x)))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a {name}`Finite` instance, consider using {name}`IterM.any`
instead.
-/
@[inline]
def IterM.Partial.any {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoopPartial α m m]
    (p : β → Bool) (it : IterM.Partial (α := α) m β) : m (ULift Bool) := do
  it.anyM (fun x => pure (.up (p x)))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first mismatch. The elements in {name}`it` are
examined in order of iteration.

This function requires a {name}`Finite` instance proving that the iterator will finish after a
finite number of steps. If the iterator is not finite or such an instance is not available,
consider using {lit}`it.allowNontermination.allM` instead of {lean}`it.allM`. However, it is not
possible to formally verify the behavior of the partial variant.
-/
@[specialize]
def IterM.allM {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m]
    (p : β → m (ULift Bool)) (it : IterM (α := α) m β) : m (ULift Bool) := do
  ForIn.forIn it (ULift.up true) (fun x _ => do
    if (← p x).down then
      return .yield (.up true)
    else
      return .done (.up false))
set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first mismatch. The elements in {name}`it` are
examined in order of iteration.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a {name}`Finite` instance, consider using {name}`IterM.allM`
instead.
-/
@[specialize]
def IterM.Partial.allM {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoopPartial α m m]
    (p : β → m (ULift Bool)) (it : IterM.Partial (α := α) m β) : m (ULift Bool) := do
  ForIn.forIn it (ULift.up true) (fun x _ => do
    if (← p x).down then
      return .yield (.up true)
    else
      return .done (.up false))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first mismatch. The elements in {name}`it` are
examined in order of iteration.

This function requires a {name}`Finite` instance proving that the iterator will finish after a
finite number of steps. If the iterator is not finite or such an instance is not available,
consider using {lit}`it.allowNontermination.all` instead of {lean}`it.all`. However, it is not
possible to formally verify the behavior of the partial variant.
-/
@[inline]
def IterM.all {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m]
    (p : β → Bool) (it : IterM (α := α) m β) : m (ULift Bool) := do
  it.allM (fun x => pure (.up (p x)))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first mismatch. The elements in {name}`it` are
examined in order of iteration.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a {name}`Finite` instance, consider using {name}`IterM.all`
instead.
-/
@[inline]
def IterM.Partial.all {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoopPartial α m m]
    (p : β → Bool) (it : IterM.Partial (α := α) m β) : m (ULift Bool) := do
  it.allM (fun x => pure (.up (p x)))

/--
TODO!
-/
@[inline]
def IterM.findSomeM? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → m (Option γ)) :
    m (Option γ) :=
  ForIn.forIn it none (fun x _ => do
    match ← f x with
    | none => return .yield none
    | some fx => return .done (some fx))

@[inline]
def IterM.Partial.findSomeM? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoopPartial α m m] (it : IterM.Partial (α := α) m β) (f : β → m (Option γ)) :
    m (Option γ) :=
  ForIn.forIn it none (fun x _ => do
    match ← f x with
    | none => return .yield none
    | some fx => return .done (some fx))

@[inline]
def IterM.findSome? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → Option γ) :
    m (Option γ) :=
  it.findSomeM? (pure <| f ·)

@[inline]
def IterM.Partial.findSome? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoopPartial α m m] (it : IterM.Partial (α := α) m β) (f : β → Option γ) :
    m (Option γ) :=
  it.findSomeM? (pure <| f ·)

@[inline]
def IterM.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.findSomeM? (fun x => return if (← f x).down then some x else none)

@[inline]
def IterM.Partial.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoopPartial α m m] (it : IterM.Partial (α := α) m β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.findSomeM? (fun x => return if (← f x).down then some x else none)

@[inline]
def IterM.find? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → Bool) :
    m (Option β) :=
  it.findM? (pure <| .up <| f ·)

@[inline]
def IterM.Partial.find? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoopPartial α m m] (it : IterM.Partial (α := α) m β) (f : β → Bool) :
    m (Option β) :=
  it.findM? (pure <| .up <| f ·)

section Size

/--
This is the implementation of the default instance `IteratorSize.defaultImplementation`.
-/
@[always_inline, inline]
def IterM.DefaultConsumers.size {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [IteratorLoop α m m] (it : IterM (α := α) m β) :
    m (ULift Nat) :=
  it.fold (init := .up 0) fun acc _ => .up (acc.down + 1)

/--
This is the implementation of the default instance `IteratorSizePartial.defaultImplementation`.
-/
@[always_inline, inline]
def IterM.DefaultConsumers.sizePartial {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [IteratorLoopPartial α m m] (it : IterM (α := α) m β) :
    m (ULift Nat) :=
  it.allowNontermination.fold (init := .up 0) fun acc _ => .up (acc.down + 1)

/--
This is the default implementation of the `IteratorSize` class.
It simply iterates using `IteratorLoop` and counts the elements.
For certain iterators, more efficient implementations are possible and should be used instead.
-/
@[always_inline, inline]
def IteratorSize.defaultImplementation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] :
    IteratorSize α m where
  size := IterM.DefaultConsumers.size


/--
This is the default implementation of the `IteratorSizePartial` class.
It simply iterates using `IteratorLoopPartial` and counts the elements.
For certain iterators, more efficient implementations are possible and should be used instead.
-/
@[always_inline, inline]
instance IteratorSizePartial.defaultImplementation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoopPartial α m m] :
    IteratorSizePartial α m where
  size := IterM.DefaultConsumers.sizePartial

/--
Computes how many elements the iterator returns. In monadic situations, it is unclear which effects
are caused by calling `size`, and if the monad is nondeterministic, it is also unclear what the
returned value should be. The reference implementation, `IteratorSize.defaultImplementation`,
simply iterates over the whole iterator monadically, counting the number of emitted values.
An `IteratorSize` instance is considered lawful if it is equal to the reference implementation.

**Performance**:

Default performance is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline]
def IterM.size {α : Type} {m : Type → Type w'} {β : Type} [Iterator α m β] [Monad m]
    (it : IterM (α := α) m β) [IteratorSize α m] : m Nat :=
  ULift.down <$> IteratorSize.size it

/--
Computes how many elements the iterator emits.

With monadic iterators (`IterM`), it is unclear which effects
are caused by calling `size`, and if the monad is nondeterministic, it is also unclear what the
returned value should be. The reference implementation, `IteratorSize.defaultImplementation`,
simply iterates over the whole iterator monadically, counting the number of emitted values.
An `IteratorSize` instance is considered lawful if it is equal to the reference implementation.

This is the partial version of `size`. It does not require a proof of finiteness and might loop
forever. It is not possible to verify the behavior in Lean because it uses `partial`.

**Performance**:

Default performance is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline]
def IterM.Partial.size {α : Type} {m : Type → Type w'} {β : Type} [Iterator α m β] [Monad m]
    (it : IterM.Partial (α := α) m β) [IteratorSizePartial α m] : m Nat :=
  ULift.down <$> IteratorSizePartial.size it.it

end Size

end Std.Iterators
