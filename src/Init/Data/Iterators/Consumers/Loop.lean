/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.Iterators.Consumers.Partial

/-!
# Loop consumers

This module provides consumers that iterate over a given iterator, applying a certain user-supplied
function in every iteration. Concretely, the following operations are provided:

* `ForIn` instances
* `Iter.fold`, the analogue of `List.foldl`
* `Iter.foldM`, the analogue of `List.foldlM`

These operations are implemented using the `IteratorLoop` and `IteratorLoopPartial` typeclasses.
-/

namespace Std.Iterators

/--
A `ForIn'` instance for iterators. Its generic membership relation is not easy to use,
so this is not marked as `instance`. This way, more convenient instances can be built on top of it
or future library improvements will make it more comfortable.
-/
def Iter.instForIn' {α : Type w} {β : Type w} {n : Type w → Type w'} [Monad n]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] :
    ForIn' n (Iter (α := α) β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    IteratorLoop.finiteForIn' (fun δ (c : Id δ) => pure c.run) |>.forIn' it.toIterM init
        fun out h acc =>
          f out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc

instance (α : Type w) (β : Type w) (n : Type w → Type w') [Monad n]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] :
    ForIn n (Iter (α := α) β) β :=
  haveI : ForIn' n (Iter (α := α) β) β _ := Iter.instForIn'
  instForInOfForIn'

instance (α : Type w) (β : Type w) (n : Type w → Type w') [Monad n]
    [Iterator α Id β] [IteratorLoopPartial α Id n] :
    ForIn n (Iter.Partial (α := α) β) β where
  forIn it init f :=
    letI : MonadLift Id n := ⟨pure⟩
    ForIn.forIn it.it.toIterM.allowNontermination init f

instance {m : Type w → Type w'}
    {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m] :
    ForM m (Iter (α := α) β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type w → Type w'}
    {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id] [IteratorLoopPartial α Id m] :
    ForM m (Iter.Partial (α := α) β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldlM`.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.foldM` instead of `it.foldM`. However, it is not possible to formally
verify the behavior of the partial variant.
-/
@[always_inline, inline]
def Iter.foldM {m : Type w → Type w'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id m] (f : γ → β → m γ)
    (init : γ) (it : Iter (α := α) β) : m γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldlM`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.foldM` instead.
-/
@[always_inline, inline]
def Iter.Partial.foldM {m : Type w → Type w'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    [IteratorLoopPartial α Id m] (f : γ → β → m γ)
    (init : γ) (it : Iter.Partial (α := α) β) : m γ :=
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
def Iter.fold {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] (f : γ → β → γ)
    (init : γ) (it : Iter (α := α) β) : γ :=
  ForIn.forIn (m := Id) it init (fun x acc => ForInStep.yield (f acc x))

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.fold` instead.
-/
@[always_inline, inline]
def Iter.Partial.fold {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    [IteratorLoopPartial α Id Id] (f : γ → β → γ)
    (init : γ) (it : Iter.Partial (α := α) β) : γ :=
  ForIn.forIn (m := Id) it init (fun x acc => ForInStep.yield (f acc x))

@[always_inline, inline, inherit_doc IterM.size]
def Iter.size {α : Type w} {β : Type w} [Iterator α Id β] [IteratorSize α Id]
    (it : Iter (α := α) β) : Nat :=
  (IteratorSize.size it.toIterM).run.down

@[always_inline, inline, inherit_doc IterM.Partial.size]
def Iter.Partial.size {α : Type w} {β : Type w} [Iterator α Id β] [IteratorSizePartial α Id]
    (it : Iter (α := α) β) : Nat :=
  (IteratorSizePartial.size it.toIterM).run.down

end Std.Iterators
