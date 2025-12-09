/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.FilterMap

public section

/-!

# `filterMap`, `filter` and `map` combinators

This file provides iterator combinators for filtering and mapping.

* `IterM.filterMap` either modifies or drops each value based on an option-valued mapping function.
* `IterM.filter` drops some elements based on a predicate.
* `IterM.map` modifies each value based on a mapping function

Several variants of these combinators are provided:

* `M` suffix: Instead of a pure function, these variants take a monadic function. Given a suitable
  `MonadLiftT` instance, they also allow lifting the iterator to another monad first and then
  applying the mapping function in this monad.
* `WithPostcondition` suffix: These variants take a monadic function where the return type in the
  monad is a subtype. This variant is in rare cases necessary for the intrinsic verification of an
  iterator, and particularly for specialized termination proofs. If possible, avoid this.
-/

namespace Std.Iterators

/--
If `it` is an iterator, then `it.filterMapM f` is another iterator that applies a monadic
function `f` to all values emitted by `it`. `f` is expected to return an `Option` inside the monad.
If `f` returns `none`, then nothing is emitted; if it returns `some x`, then `x` is emitted.

If `f` is pure, then the simpler variant `it.filterMap` can be used instead.

**Marble diagram (without monadic effects):**

```text
it                ---a --b--c --d-e--⊥
it.filterMapM     ---a'-----c'-------⊥
```

(given that `f a = pure (some a)'`, `f c = pure (some c')` and `f b = f d = d e = pure none`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite`

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided. For example, if `f` never returns `none`, then
this combinator will preserve productiveness. If `f` is an `ExceptT` monad and will always fail,
then `it.filterMapM` will be finite even if `it` isn't. In the first case, consider
using the `map`/`mapM`/`mapWithPostcondition` combinators instead, which provide more instances out
of the box.

If that does not help, the more general combinator `it.filterMapWithPostcondition f` makes it
possible to manually prove `Finite` and `Productive` instances depending on the concrete choice of `f`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f` and matches on the
returned `Option` value.
-/
@[always_inline, inline, expose]
def Iter.filterMapM {α β γ : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapM f : IterM m γ)

/--
If `it` is an iterator, then `it.filterM f` is another iterator that applies a monadic
predicate `f` to all values emitted by `it` and emits them only if they are accepted by `f`.

If `f` is pure, then the simpler variant `it.filter` can be used instead.

**Marble diagram (without monadic effects):**

```text
it             ---a--b--c--d-e--⊥
it.filterM     ---a-----c-------⊥
```

(given that `f a = f c = pure true` and `f b = f d = d e = pure false`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite`

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT` monad and
will always fail, then `it.filterWithPostcondition` will be finite -- and productive -- even if `it`
isn't.

In such situations, the more general combinator `it.filterWithPostcondition f` makes it possible to
manually prove `Finite` and `Productive` instances depending on the concrete choice of `f`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline, expose]
def Iter.filterM {α β : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → m (ULift Bool)) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterM f : IterM m β)

/--
If `it` is an iterator, then `it.mapM f` is another iterator that applies a monadic
function `f` to all values emitted by `it` and emits the result.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

If `f` is pure, then the simpler variant `it.map` can be used instead.

**Marble diagram (without monadic effects):**

```text
it          ---a --b --c --d -e ----⊥
it.mapM     ---a'--b'--c'--d'-e'----⊥
```

(given that `f a = pure a'`, `f b = pure b'` etc.)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT` monad and
will always fail, then `it.mapM` will be finite even if `it` isn't.

If that does not help, the more general combinator `it.mapWithPostcondition f` makes it possible to
manually prove `Finite` and `Productive` instances depending on the concrete choice of `f`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline, expose]
def Iter.mapM {α β γ : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → m γ) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapM f : IterM m γ)

@[always_inline, inline, inherit_doc IterM.filterMap, expose]
def Iter.filterMap {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    (f : β → Option γ) (it : Iter (α := α) β) :=
  ((it.toIterM.filterMap f).toIter : Iter γ)

@[always_inline, inline, inherit_doc IterM.filter, expose]
def Iter.filter {α : Type w} {β : Type w} [Iterator α Id β]
    (f : β → Bool) (it : Iter (α := α) β) :=
  ((it.toIterM.filter f).toIter : Iter β)

@[always_inline, inline, inherit_doc IterM.map, expose]
def Iter.map {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    (f : β → γ) (it : Iter (α := α) β) :=
  ((it.toIterM.map f).toIter : Iter γ)

end Std.Iterators
