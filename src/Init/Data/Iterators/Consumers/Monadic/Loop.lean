/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Partial
public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
public import Init.WFExtrinsicFix
public import Init.Data.Iterators.Consumers.Monadic.Total

set_option linter.missingDocs true

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
`IteratorLoop` type class. They should be implemented by all
types of iterators. A default implementation is provided. The typeclass `LawfulIteratorLoop`
asserts that an `IteratorLoop` instance equals the default implementation.
-/

namespace Std

open Std.Internal Std.Iterators

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
iterators. The basis is a `ForIn`-style loop construct.

Its behavior for well-founded loops is fully characterized by the `LawfulIteratorLoop` type class.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
@[ext]
class IteratorLoop (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type x → Type x') where
  /--
  Iteration over the iterator `it` in the manner expected by `for` loops.
  -/
  forIn : ∀ (_liftBind : (γ : Type w) → (δ : Type x) → (γ → n δ) → m γ → n δ) (γ : Type x),
      (plausible_forInStep : β → γ → ForInStep γ → Prop) →
      (it : IterM (α := α) m β) → γ →
      ((b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (plausible_forInStep b c))) →
      n γ

end Typeclasses

/-- Internal implementation detail of the iterator library. -/
structure IteratorLoop.WithWF (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (hwf : IteratorLoop.WellFounded α m PlausibleForInStep) where
  /-- Internal implementation detail of the iterator library. -/
  it : IterM (α := α) m β
  /-- Internal implementation detail of the iterator library. -/
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
@[always_inline, inline, expose]
def IterM.DefaultConsumers.forIn' {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type x → Type x'} [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) (γ : Type x)
    (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))) : n γ :=
  haveI : Nonempty γ := ⟨init⟩
  WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => n γ) (InvImage (IteratorLoop.rel α m PlausibleForInStep) (fun x => (x.1, x.2.1)))
    (fun it acc (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b) recur => (lift _ _ · it.step) fun s => do
      match s.inflate with
      | .yield it' out h =>
        match ← f out (hP out <| .direct ⟨_, h⟩) acc with
        | ⟨.yield c, h'⟩ => recur it' c (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') (Or.inl ⟨out, ‹_›, ‹_›⟩)
        | ⟨.done c, h⟩ => return c
      | .skip it' h => recur it' acc (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') (Or.inr ⟨‹_›, rfl⟩)
      | .done _ => return acc) it init hP

/--
This is the loop implementation of the default instance `IteratorLoop.defaultImplementation`.
-/
@[specialize, expose]
def IterM.DefaultConsumers.forIn'.wf {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β] {n : Type x → Type x'} [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) (γ : Type x)
    (PlausibleForInStep : β → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded α m PlausibleForInStep)
    (it : IterM (α := α) m β) (init : γ)
    (P : β → Prop) (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (PlausibleForInStep b c))) : n γ :=
  haveI : WellFounded _ := wf
  (lift _ _ · it.step) fun s =>
    match s.inflate with
    | .yield it' out h => do
      match ← f out (hP _ <| .direct ⟨_, h⟩) init with
      | ⟨.yield c, _⟩ =>
        IterM.DefaultConsumers.forIn'.wf lift _ PlausibleForInStep wf it' c P
          (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f
      | ⟨.done c, _⟩ => return c
    | .skip it' h =>
      IterM.DefaultConsumers.forIn'.wf lift _ PlausibleForInStep wf it' init P
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
@[always_inline, inline, expose]
def IteratorLoop.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type x → Type x'}
    [Monad n] [Iterator α m β] :
    IteratorLoop α m n where
  forIn lift γ Pl it init := IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id)

/--
Asserts that a given `IteratorLoop` instance is equal to `IteratorLoop.defaultImplementation`.
(Even though equal, the given instance might be vastly more efficient.)
-/
class LawfulIteratorLoop (α : Type w) (m : Type w → Type w') (n : Type x → Type x')
    [Monad m] [Monad n] [Iterator α m β] [i : IteratorLoop α m n] where
  /-- The implementation of `IteratorLoop.forIn` in `i` is equal to the default implementation. -/
  lawful lift [LawfulMonadLiftBindFunction lift] γ it init
      (Pl : β → γ → ForInStep γ → Prop) (wf : IteratorLoop.WellFounded α m Pl)
      (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) :
    i.forIn lift γ Pl it init f =
      IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

instance instLawfulIteratorLoopDefaultImplementation (α : Type w) (m : Type w → Type w')
    (n : Type x → Type x') [Monad m] [Monad n] [Iterator α m β] [Finite α m] :
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
@[always_inline, inline]
def IteratorLoop.finiteForIn' {m : Type w → Type w'} {n : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {γ} it init f :=
    IteratorLoop.forIn (α := α) (m := m) lift γ (fun _ _ _ => True) it init (return ⟨← f · · ·, trivial⟩)

/--
A `ForIn'` instance for iterators. Its generic membership relation is not easy to use,
so this is not marked as `instance`. This way, more convenient instances can be built on top of it
or future library improvements will make it more comfortable.
-/
@[always_inline, inline]
def IterM.instForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    [MonadLiftT m n] :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ :=
  IteratorLoop.finiteForIn' (fun _ _ f x => monadLift x >>= f)

instance IterM.instForInOfIteratorLoop {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n]
    [MonadLiftT m n] [Monad n] :
    ForIn n (IterM (α := α) m β) β :=
  haveI : ForIn' n (IterM (α := α) m β) β _ := IterM.instForIn'
  instForInOfForIn'

/-- Internal implementation detail of the iterator library. -/
@[always_inline, inline]
def IterM.Partial.instForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n] [Monad n] :
    ForIn' n (IterM.Partial (α := α) m β) β ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    haveI := @IterM.instForIn'; forIn' it.it init f

/-- Internal implementation detail of the iterator library. -/
@[always_inline, inline]
def IterM.Total.instForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n] [Monad n]
    [Finite α m] :
    ForIn' n (IterM.Total (α := α) m β) β ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := IterM.instForIn'.forIn' it.it init f

instance IterM.Partial.instForInOfIteratorLoop {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n] [Monad n] :
    ForIn n (IterM.Partial (α := α) m β) β :=
  haveI : ForIn' n (IterM.Partial (α := α) m β) β _ := IterM.Partial.instForIn'
  instForInOfForIn'

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n] [Monad n]
    [Finite α m] :
    ForIn n (IterM.Total (α := α) m β) β :=
  haveI : ForIn' n (IterM.Total (α := α) m β) β _ := IterM.Total.instForIn'
  instForInOfForIn'

instance IterM.instForMOfIteratorLoop {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n] [MonadLiftT m n] :
    ForM n (IterM (α := α) m β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance IterM.Partial.instForMOfItreratorLoop {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Monad n] [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n] :
    ForM n (IterM.Partial (α := α) m β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type w → Type w'} {n : Type w → Type w''} {α : Type w} {β : Type w} [Iterator α m β]
    [IteratorLoop α m n] [Monad n] [MonadLiftT m n] [Finite α m] :
    ForM n (IterM.Total (α := α) m β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

The monadic effects of `f` are interleaved with potential effects caused by the iterator's step
function. Therefore, it may *not* be equivalent to `(← it.toList).foldlM`.
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

This function is deprecated. Instead of `it.allowNontermination.foldM`, use `it.foldM`.
-/
@[always_inline, inline, deprecated IterM.foldM (since := "2025-12-04")]
def IterM.Partial.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM.Partial (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

The monadic effects of `f` are interleaved with potential effects caused by the iterator's step
function. Therefore, it may *not* be equivalent to `it.toList.foldlM`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.foldM`.
-/
@[always_inline, inline]
def IterM.Total.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [IteratorLoop α m n] [MonadLiftT m n]
    [Finite α m] (f : γ → β → n γ) (init : γ) (it : IterM.Total (α := α) m β) : n γ :=
  it.it.foldM (init := init) f

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.
-/
@[always_inline, inline]
def IterM.fold {m : Type w → Type w'} {α : Type w} {β : Type w} {γ : Type w} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] (f : γ → β → γ) (init : γ) (it : IterM (α := α) m β) :
    m γ :=
  ForIn.forIn (m := m) it init (fun x acc => pure (ForInStep.yield (f acc x)))

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This function is deprecated. Instead of `it.allowNontermination.fold`, use `it.fold`.
-/
@[always_inline, inline, deprecated IterM.Partial.fold (since := "2025-12-04")]
def IterM.Partial.fold {m : Type w → Type w'} {α : Type w} {β : Type w} {γ : Type w}
    [Monad m] [Iterator α m β] [IteratorLoop α m m] (f : γ → β → γ) (init : γ)
    (it : IterM.Partial (α := α) m β) : m γ :=
  ForIn.forIn (m := m) it init (fun x acc => pure (ForInStep.yield (f acc x)))

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.fold`.
-/
@[always_inline, inline]
def IterM.Total.fold {m : Type w → Type w'} {α : Type w} {β : Type w} {γ : Type w}
    [Monad m] [Iterator α m β] [IteratorLoop α m m] [Finite α m] (f : γ → β → γ) (init : γ)
    (it : IterM.Total (α := α) m β) : m γ :=
  it.it.fold (init := init) f

/--
Iterates over the whole iterator, applying the monadic effects of each step, discarding all
emitted values.
-/
@[always_inline, inline]
def IterM.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM (α := α) m β) [IteratorLoop α m m] :
    m PUnit :=
  it.fold (γ := PUnit) (fun _ _ => .unit) .unit

/--
Iterates over the whole iterator, applying the monadic effects of each step, discarding all
emitted values.

This function is deprecated. Instead of `it.allowNontermination.drain`, use `it.drain`.
-/
@[always_inline, inline, deprecated IterM.drain (since := "2025-12-04")]
def IterM.Partial.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorLoop α m m] : m PUnit :=
  it.it.fold (γ := PUnit) (fun _ _ => .unit) .unit

/--
Iterates over the whole iterator, applying the monadic effects of each step, discarding all
emitted values.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.drain`.
-/
@[always_inline, inline]
def IterM.Total.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) [IteratorLoop α m m] : m PUnit :=
  it.it.drain

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first match. The outputs of {name}`it` are
examined in order of iteration.
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

{lit}`O(|it|)`. Short-circuits upon encountering the first match. The outputs of {name}`it` are
examined in order of iteration.

This function is deprecated. Instead of {lit}`it.allowNontermination.anyM`, use {lit}`it.anyM`.
-/
@[always_inline, inline, deprecated IterM.anyM (since := "2025-12-04")]
def IterM.Partial.anyM {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] (p : β → m (ULift Bool))
    (it : IterM.Partial (α := α) m β) : m (ULift Bool) :=
  it.it.anyM p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first match. The outputs of {name}`it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.anyM`.
-/
@[always_inline, inline]
def IterM.Total.anyM {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] [Finite α m] (p : β → m (ULift Bool))
    (it : IterM.Total (α := α) m β) : m (ULift Bool) :=
  it.it.anyM p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first match. The outputs of {name}`it` are
examined in order of iteration.
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

{lit}`O(|it|)`. Short-circuits upon encountering the first match. The outputs of {name}`it` are
examined in order of iteration.

This function is deprecated. Instead of {lit}`it.allowNontermination.any`, use {lit}`it.any`.
-/
@[inline, deprecated IterM.any (since := "2025-12-04")]
def IterM.Partial.any {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (p : β → Bool) (it : IterM.Partial (α := α) m β) : m (ULift Bool) := do
  it.it.any p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first match. The outputs of {name}`it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.any`.
-/
@[inline]
def IterM.Total.any {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (p : β → Bool) (it : IterM.Total (α := α) m β) :
    m (ULift Bool) := do
  it.it.any p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first mismatch. The outputs of {name}`it` are
examined in order of iteration.
-/
@[specialize]
def IterM.allM {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [IteratorLoop α m m]
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

{lit}`O(|it|)`. Short-circuits upon encountering the first mismatch. The outputs of {name}`it` are
examined in order of iteration.

This function is deprecated. Instead of {lit}`it.allowNontermination.allM`, use {lit}`it.allM`.
-/
@[always_inline, inline, deprecated IterM.allM (since := "2025-12-04")]
def IterM.Partial.allM {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (p : β → m (ULift Bool)) (it : IterM.Partial (α := α) m β) :
    m (ULift Bool) := do
  it.it.allM p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the monadic predicate {name}`p` returns {lean}`ULift.up true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first mismatch. The outputs of {name}`it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.allM`.
-/
@[always_inline, inline]
def IterM.Total.allM {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (p : β → m (ULift Bool)) (it : IterM.Total (α := α) m β) :
    m (ULift Bool) := do
  it.it.allM p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first mismatch. The outputs of {name}`it` are
examined in order of iteration.

If the iterator is not finite, this function might run forever. The variant
{lit}`it.ensureTermination.toListRev` always terminates after finitely many steps.
-/
@[inline]
def IterM.all {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [IteratorLoop α m m]
    (p : β → Bool) (it : IterM (α := α) m β) : m (ULift Bool) := do
  it.allM (fun x => pure (.up (p x)))

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first mismatch. The outputs of {name}`it` are
examined in order of iteration.

This function is deprecated. Instead of {lit}`it.allowNontermination.allM`, use {lit}`it.allM`.
-/
@[inline, deprecated IterM.all (since := "2025-12-04")]
def IterM.Partial.all {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (p : β → Bool) (it : IterM.Partial (α := α) m β) : m (ULift Bool) := do
  it.it.all p

set_option doc.verso true in
/--
Returns {lean}`ULift.up true` if the pure predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|it|)`. Short-circuits upon encountering the first mismatch. The outputs of {name}`it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.all`.
-/
@[inline]
def IterM.Total.all {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (p : β → Bool) (it : IterM.Total (α := α) m β) :
    m (ULift Bool) := do
  it.it.all p

/--
Returns the first non-`none` result of applying the monadic function `f` to each output
of the iterator, in order. Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`. The outputs of `it` are
examined in order of iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.findSomeM?` always terminates after finitely many steps.

Example:
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[inline]
def IterM.findSomeM? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → m (Option γ)) :
    m (Option γ) :=
  ForIn.forIn it none (fun x _ => do
    match ← f x with
    | none => return .yield none
    | some fx => return .done (some fx))

/--
Returns the first non-`none` result of applying the monadic function `f` to each output
of the iterator, in order. Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`. The outputs of `it` are
examined in order of iteration.

This function is deprecated. Instead of `it.allowNontermination.findSomeM?`, use `it.findSomeM?`.

Example:
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[inline, deprecated IterM.findSomeM? (since := "2025-12-04")]
def IterM.Partial.findSomeM? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM.Partial (α := α) m β) (f : β → m (Option γ)) :
    m (Option γ) :=
  it.it.findSomeM? f

/--
Returns the first non-`none` result of applying the monadic function `f` to each output
of the iterator, in order. Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`. The outputs of `it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.findSomeM?`.

Example:
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[inline]
def IterM.Total.findSomeM? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (it : IterM.Total (α := α) m β) (f : β → m (Option γ)) :
    m (Option γ) :=
  it.it.findSomeM? f

/--
Returns the first non-`none` result of applying `f` to each output of the iterator, in order.
Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`.The outputs of `it` are examined in order of
iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.findSome?` always terminates after finitely many steps.

Examples:
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).findSome? (fun x => if x < 5 then some (10 * x) else none) = pure (some 10)`
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).findSome? (fun x => if x < 1 then some (10 * x) else none) = pure none`
-/
@[inline]
def IterM.findSome? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → Option γ) :
    m (Option γ) :=
  it.findSomeM? (pure <| f ·)

/--
Returns the first non-`none` result of applying `f` to each output of the iterator, in order.
Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`.The outputs of `it` are examined in order of
iteration.

This function is deprecated. Instead of `it.allowNontermination.findSome?`, use `it.findSome?`.

Examples:
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).allowNontermination.findSome? (fun x => if x < 5 then some (10 * x) else none) = pure (some 10)`
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).allowNontermination.findSome? (fun x => if x < 1 then some (10 * x) else none) = pure none`
-/
@[inline, deprecated IterM.findSome? (since := "2025-12-04")]
def IterM.Partial.findSome? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM.Partial (α := α) m β) (f : β → Option γ) :
    m (Option γ) :=
  it.it.findSome? f

/--
Returns the first non-`none` result of applying `f` to each output of the iterator, in order.
Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`.The outputs of `it` are examined in order of
iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.findSome?`.

Examples:
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).ensureTermination.findSome? (fun x => if x < 5 then some (10 * x) else none) = pure (some 10)`
 * `([7, 6, 5, 8, 1, 2, 6].iterM Id).ensureTermination.findSome? (fun x => if x < 1 then some (10 * x) else none) = pure none`
-/
@[inline]
def IterM.Total.findSome? {α β γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (it : IterM.Partial (α := α) m β) (f : β → Option γ) :
    m (Option γ) :=
  it.it.findSome? f

/--
Returns the first output of the iterator for which the monadic predicate `p` returns `true`, or
`none` if no such element is found.

`O(|it|)`. Short-circuits when `f` returns `true`. The outputs of `it` are examined in order of
iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.findM?` always terminates after finitely many steps.

Example:
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[inline]
def IterM.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.findSomeM? (fun x => return if (← f x).down then some x else none)

/--
Returns the first output of the iterator for which the monadic predicate `p` returns `true`, or
`none` if no such element is found.

`O(|it|)`. Short-circuits when `f` returns `true`. The outputs of `it` are examined in order of
iteration.

This function is deprecated. Instead of `it.allowNontermination.findM?`, use `it.findM?`.

Example:
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[inline, deprecated IterM.findM? (since := "2025-12-04")]
def IterM.Partial.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM.Partial (α := α) m β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.it.findM? f

/--
Returns the first output of the iterator for which the monadic predicate `p` returns `true`, or
`none` if no such element is found.

`O(|it|)`. Short-circuits when `f` returns `true`. The outputs of `it` are examined in order of
iteration.

This variant requires terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.findM?`.

Example:
```lean example
#eval ([7, 6, 5, 8, 1, 2, 6].iterM IO).findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[inline]
def IterM.Total.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (it : IterM.Total (α := α) m β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.it.findM? f

/--
Returns the first output of the iterator for which the predicate `p` returns `true`, or `none` if
no such output is found.

`O(|it|)`. Short-circuits upon encountering the first match. The elements in `it` are examined in
order of iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.find?` always terminates after finitely many steps.

Examples:
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).find? (· < 5) = pure (some 1)`
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).find? (· < 1) = pure none`
-/
@[inline]
def IterM.find? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (f : β → Bool) :
    m (Option β) :=
  it.findM? (pure <| .up <| f ·)

/--
Returns the first output of the iterator for which the predicate `p` returns `true`, or `none` if
no such output is found.

`O(|it|)`. Short-circuits upon encountering the first match. The elements in `it` are examined in
order of iteration.

This function is deprecated. Instead of `it.allowNontermination.find?`, use `it.find?`.

Examples:
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).allowNontermination.find? (· < 5) = pure (some 1)`
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).allowNontermination.find? (· < 1) = pure none`
-/
@[inline, deprecated IterM.find? (since := "2025-12-04")]
def IterM.Partial.find? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM.Partial (α := α) m β) (f : β → Bool) :
    m (Option β) :=
  it.it.find? f

/--
Returns the first output of the iterator for which the predicate `p` returns `true`, or `none` if
no such output is found.

`O(|it|)`. Short-circuits upon encountering the first match. The elements in `it` are examined in
order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.find?`.

Examples:
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).find? (· < 5) = pure (some 1)`
* `([7, 6, 5, 8, 1, 2, 6].iterM Id).find? (· < 1) = pure none`
-/
@[inline]
def IterM.Total.find? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] [Finite α m] (it : IterM.Total (α := α) m β) (f : β → Bool) :
    m (Option β) :=
  it.it.find? f

section Count

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline]
def IterM.count {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [IteratorLoop α m m] [Monad m] (it : IterM (α := α) m β) : m (ULift Nat) :=
  it.fold (init := .up 0) fun acc _ => .up (acc.down + 1)

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, deprecated IterM.count (since := "2025-10-29")]
def IterM.size {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [IteratorLoop α m m] [Monad m] (it : IterM (α := α) m β) : m (ULift Nat) :=
  it.count

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, deprecated IterM.count (since := "2025-12-04")]
def IterM.Partial.count {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [IteratorLoop α m m] [Monad m] (it : IterM.Partial (α := α) m β) : m (ULift Nat) :=
  it.it.fold (init := .up 0) fun acc _ => .up (acc.down + 1)

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, deprecated IterM.Partial.count (since := "2025-10-29")]
def IterM.Partial.size {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [IteratorLoop α m m] [Monad m] (it : IterM.Partial (α := α) m β) : m (ULift Nat) :=
  it.it.count

end Count

end Std
