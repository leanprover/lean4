/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Monadic.Loop

public section

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
@[always_inline, inline]
def Iter.instForIn' {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn' n (Iter (α := α) β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    IteratorLoop.finiteForIn' (fun _ _ f c => f c.run) |>.forIn' it.toIterM init
        fun out h acc =>
          f out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc

instance (α : Type w) (β : Type w) (n : Type x → Type x') [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn n (Iter (α := α) β) β :=
  haveI : ForIn' n (Iter (α := α) β) β _ := Iter.instForIn'
  instForInOfForIn'

@[always_inline, inline]
def Iter.Partial.instForIn' {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoopPartial α Id n] :
    ForIn' n (Iter.Partial (α := α) β) β ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    IteratorLoopPartial.forInPartial (α := α) (m := Id) (n := n) (fun _ _ f c => f c.run)
      it.it.toIterM init
      fun out h acc =>
        f out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc

instance (α : Type w) (β : Type w) (n : Type x → Type x') [Monad n]
    [Iterator α Id β] [IteratorLoopPartial α Id n] :
    ForIn n (Iter.Partial (α := α) β) β :=
  haveI : ForIn' n (Iter.Partial (α := α) β) β _ := Iter.Partial.instForIn'
  instForInOfForIn'

instance {m : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id m] :
    ForM m (Iter (α := α) β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoopPartial α Id m] :
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
def Iter.foldM {m : Type x → Type x'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
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
def Iter.Partial.foldM {m : Type x → Type x'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
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
def Iter.fold {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
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
def Iter.Partial.fold {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoopPartial α Id Id] (f : γ → β → γ)
    (init : γ) (it : Iter.Partial (α := α) β) : γ :=
  ForIn.forIn (m := Id) it init (fun x acc => ForInStep.yield (f acc x))

set_option doc.verso true in
/--
Returns {lean}`true` if the monadic predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.
-/
@[specialize]
def Iter.anyM {α β : Type w} {m : Type → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m]
    (p : β → m Bool) (it : Iter (α := α) β) : m Bool :=
  ForIn.forIn it false (fun x _ => do
    if ← p x then
      return .done true
    else
      return .yield false)

set_option doc.verso true in
/--
Returns {lean}`true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.
-/
@[inline]
def Iter.any {α β : Type w}
    [Iterator α Id β] [IteratorLoop α Id Id]
    (p : β → Bool) (it : Iter (α := α) β) : Bool :=
  (it.anyM (fun x => pure (f := Id) (p x))).run

set_option doc.verso true in
/--
Returns {lean}`true` if the monadic predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first mismatch. The elements in {name}`it` are
examined in order of iteration.
-/
@[specialize]
def Iter.allM {α β : Type w} {m : Type → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m]
    (p : β → m Bool) (it : Iter (α := α) β) : m Bool :=
  ForIn.forIn it true (fun x _ => do
    if ← p x then
      return .yield true
    else
      return .done false)

set_option doc.verso true in
/--
Returns {lean}`true` if the pure predicate {name}`p` returns {lean}`true` for
all elements emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first mismatch. The elements in {name}`it` are
examined in order of iteration.
-/
@[inline]
def Iter.all {α β : Type w}
    [Iterator α Id β] [IteratorLoop α Id Id]
    (p : β → Bool) (it : Iter (α := α) β) : Bool :=
  (it.allM (fun x => pure (f := Id) (p x))).run

@[inline]
def Iter.findSomeM? {α β : Type w} {γ : Type x} {m : Type x → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoop α Id m] (it : Iter (α := α) β) (f : β → m (Option γ)) :
    m (Option γ) :=
  ForIn.forIn it none (fun x _ => do
    match ← f x with
    | none => return .yield none
    | some fx => return .done (some fx))

@[inline]
def Iter.Partial.findSomeM? {α β : Type w} {γ : Type x} {m : Type x → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoopPartial α Id m] (it : Iter.Partial (α := α) β)
    (f : β → m (Option γ)) :
    m (Option γ) :=
  ForIn.forIn it none (fun x _ => do
    match ← f x with
    | none => return .yield none
    | some fx => return .done (some fx))

@[inline]
def Iter.findSome? {α β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] (it : Iter (α := α) β) (f : β → Option γ) :
    Option γ :=
  Id.run (it.findSomeM? (pure <| f ·))

@[inline]
def Iter.Partial.findSome? {α β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoopPartial α Id Id] (it : Iter.Partial (α := α) β) (f : β → Option γ) :
    Option γ :=
  Id.run (it.findSomeM? (pure <| f ·))

@[inline]
def Iter.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoop α Id m] (it : Iter (α := α) β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.findSomeM? (fun x => return if (← f x).down then some x else none)

@[inline]
def Iter.Partial.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoopPartial α Id m] (it : Iter.Partial (α := α) β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.findSomeM? (fun x => return if (← f x).down then some x else none)

@[inline]
def Iter.find? {α β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) (f : β → Bool) : Option β :=
  Id.run (it.findM? (pure <| .up <| f ·))

@[inline]
def Iter.Partial.find? {α β : Type w} [Iterator α Id β] [IteratorLoopPartial α Id Id]
    (it : Iter.Partial (α := α) β) (f : β → Bool) : Option β :=
  Id.run (it.findM? (pure <| .up <| f ·))

@[always_inline, inline, expose, inherit_doc IterM.size]
def Iter.size {α : Type w} {β : Type w} [Iterator α Id β] [IteratorSize α Id]
    (it : Iter (α := α) β) : Nat :=
  (IteratorSize.size it.toIterM).run.down

@[always_inline, inline, inherit_doc IterM.Partial.size]
def Iter.Partial.size {α : Type w} {β : Type w} [Iterator α Id β] [IteratorSizePartial α Id]
    (it : Iter (α := α) β) : Nat :=
  (IteratorSizePartial.size it.toIterM).run.down

/--
`LawfulIteratorSize α m` ensures that the `size` function of an iterator behaves as if it
iterated over the whole iterator, counting its elements and causing all the monadic side effects
of the iterations. This is a fairly strong condition for monadic iterators and it will be false
for many efficient implementations of `size` that compute the size without actually iterating.

This class is experimental and users of the iterator API should not explicitly depend on it.
-/
class LawfulIteratorSize (α : Type w) {β : Type w} [Iterator α Id β]
    [IteratorSize α Id] where
    size_eq_size_toArray {it : Iter (α := α) β} : it.size =
      haveI : IteratorCollect α Id Id := .defaultImplementation
      it.toArray.size

end Std.Iterators
