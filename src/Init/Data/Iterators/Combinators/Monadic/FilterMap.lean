/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.PostconditionMonad
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.PropLemmas

public section

/-!

# Monadic `filterMap`, `filter` and `map` combinators

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

namespace Std

namespace Iterators.Types

/--
Internal state of the `filterMap` combinator. Do not depend on its internals.
-/
@[ext, unbox]
structure FilterMap (α : Type w) {β γ : Type w}
    (m : Type w → Type w') (n : Type w → Type w'') (lift : ⦃α : Type w⦄ → m α → n α)
    (f : β → PostconditionT n (Option γ)) where
  /-- Internal implementation detail of the iterator library. -/
  inner : IterM (α := α) m β

/--
Internal state of the `map` combinator. Do not depend on its internals.
-/
@[expose]
def Map (α : Type w) {β γ : Type w} (m : Type w → Type w') (n : Type w → Type w'')
    (lift : ⦃α : Type w⦄ → m α → n α) [Functor n]
    (f : β → PostconditionT n γ) :=
  FilterMap α m n lift (fun b => PostconditionT.map some (f b))

end Iterators.Types

open Std.Iterators Std.Iterators.Types

@[always_inline, inline, expose]
def IterM.InternalCombinators.filterMap {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} (lift : ⦃α : Type w⦄ → m α → n α)
    [Iterator α m β] (f : β → PostconditionT n (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMap α m n lift f) n γ :=
  ⟨⟨it⟩⟩

@[always_inline, inline, expose]
def IterM.InternalCombinators.map {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] (lift : ⦃α : Type w⦄ → m α → n α)
    [Iterator α m β] (f : β → PostconditionT n γ)
    (it : IterM (α := α) m β) : IterM (α := Map α m n lift f) n γ :=
  ⟨⟨it⟩⟩

/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `filterMap` and `filterMapM` are easier to use
and sufficient for most use cases.*

If `it` is an iterator, then `it.filterMapWithPostcondition f` is another iterator that applies a
monadic function `f` to all values emitted by `it`. `f` is expected to return an `Option` inside the
monad. If `f` returns `none`, then nothing is emitted; if it returns `some x`, then `x` is emitted.

`f` is expected to return `PostconditionT n (Option _)`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.filterMapWithPostcondition f` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**

```text
it                                ---a --b--c --d-e--⊥
it.filterMapWithPostcondition     ---a'-----c'-------⊥
```

(given that `f a = pure (some a)'`, `f c = pure (some c')` and `f b = f d = d e = pure none`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided. For example, if `f` never returns `none`, then
this combinator will preserve productiveness. If `f` is an `ExceptT` monad and will always fail,
then `it.filterMapWithPostcondition` will be finite even if `it` isn't. In the first case, consider
using the `map`/`mapM`/`mapWithPostcondition` combinators instead, which provide more instances out of
the box.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. If `f` always returns `some _`, a suitable
postcondition is `fun x => x.isSome`; if `f` always fails, a suitable postcondition might be
`fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f` and matches on the
returned `Option` value.
-/
@[inline, expose]
def IterM.filterMapWithPostcondition {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadLiftT m n] [Iterator α m β] (f : β → PostconditionT n (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMap α m n (fun ⦃_⦄ => monadLift) f) n γ :=
  IterM.InternalCombinators.filterMap (n := n) (fun ⦃_⦄ => monadLift) f it

namespace Iterators.Types

/--
`it.PlausibleStep step` is the proposition that `step` is a possible next step from the
`filterMap` iterator `it`. This is mostly internally relevant, except if one needs to manually
prove termination (`Finite` or `Productive` instances, for example) of a `filterMap` iterator.
-/
inductive FilterMap.PlausibleStep {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    [Iterator α m β] (it : IterM (α := FilterMap α m n lift f) n γ) :
    IterStep (IterM (α := FilterMap α m n lift f) n γ) γ → Prop where
  | yieldNone : ∀ {it' out},
      it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f out).Property none →
      PlausibleStep it (.skip (IterM.InternalCombinators.filterMap lift f it'))
  | yieldSome : ∀ {it' out out'}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f out).Property (some out') →
      PlausibleStep it (.yield (IterM.InternalCombinators.filterMap lift f it') out')
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip (IterM.InternalCombinators.filterMap lift f it'))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done

instance FilterMap.instIterator {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    [Iterator α m β] [Monad n] :
    Iterator (FilterMap α m n lift f) n γ where
  IsPlausibleStep := FilterMap.PlausibleStep (m := m) (n := n)
  step it :=
    letI : MonadLift m n := ⟨lift (α := _)⟩
    do
      match (← it.internalState.inner.step).inflate with
      | .yield it' out h => do
        match ← (f out).operation with
        | ⟨none, h'⟩ => pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (by exact .yieldNone h h')
        | ⟨some out', h'⟩ => pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (by exact .yieldSome h h')
      | .skip it' h => pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (by exact .skip h)
      | .done h => pure <| .deflate <| .done (.done h)

instance Map.instIterator {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n]
    [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n γ} :
    Iterator (Map α m n lift f) n γ :=
  inferInstanceAs <| Iterator (FilterMap α m n lift _) n γ

theorem Map.instIterator_eq_filterMapInstIterator {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n]
    [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n γ} :
    Map.instIterator (α := α) (β := β) (γ := γ) (m := m) (n := n) (lift := lift) (f := f) =
      FilterMap.instIterator :=
  rfl

private def FilterMap.instFinitenessRelation {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] :
    FinitenessRelation (FilterMap α m n lift f) n where
  Rel := InvImage IterM.IsPlausibleSuccessorOf (FilterMap.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldNone it' out h' h'' =>
      cases h
      exact IterM.isPlausibleSuccessorOf_of_yield h'
    case yieldSome it' out h' h'' =>
      cases h
      exact IterM.isPlausibleSuccessorOf_of_yield h'
    case skip it' h' =>
      cases h
      exact IterM.isPlausibleSuccessorOf_of_skip h'
    case done h' =>
      cases h

@[no_expose]
instance FilterMap.instFinite {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] : Finite (FilterMap α m n lift f) n :=
  Finite.of_finitenessRelation FilterMap.instFinitenessRelation

@[no_expose]
instance Map.instFinite {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n]
    [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n γ} [Finite α m] :
    Finite (Map α m n lift f) n :=
  Finite.of_finitenessRelation FilterMap.instFinitenessRelation

private def Map.instProductivenessRelation {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n γ} [Productive α m] :
    ProductivenessRelation (Map α m n lift f) n where
  Rel := InvImage IterM.IsPlausibleSkipSuccessorOf (FilterMap.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    cases h
    case yieldNone it' out h h' =>
      simp at h'
    case skip it' h =>
      exact h

@[no_expose]
instance Map.instProductive {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n γ} [Productive α m] :
    Productive (Map α m n lift f) n :=
  Productive.of_productivenessRelation Map.instProductivenessRelation

instance FilterMap.instIteratorLoop {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type x → Type x'}
    [Monad n] [Monad o] [Iterator α m β] {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n (Option γ)} :
    IteratorLoop (FilterMap α m n lift f) n o :=
  .defaultImplementation

instance Map.instIteratorLoop {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type x → Type x'} [Monad n] [Monad o] [Iterator α m β]
    {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n γ} :
    IteratorLoop (Map α m n lift f) n o :=
  .defaultImplementation

end Iterators.Types

/--
*Note: This is a very general combinator that requires an advanced understanding of monads, dependent
types and termination proofs. The variants `map` and `mapM` are easier to use and sufficient
for most use cases.*

If `it` is an iterator, then `it.mapWithPostcondition f` is another iterator that applies a monadic
function `f` to all values emitted by `it` and emits the result.

`f` is expected to return `PostconditionT n _`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.mapWithPostcondition f` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**

```text
it                          ---a --b --c --d -e ----⊥
it.mapWithPostcondition     ---a'--b'--c'--d'-e'----⊥
```

(given that `f a = pure a'`, `f b = pure b'` etc.)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT` monad and
will always fail, then `it.mapWithPostcondition` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.mapWithPostcondition {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [MonadLiftT m n] [Iterator α m β] (f : β → PostconditionT n γ)
    (it : IterM (α := α) m β) : IterM (α := Map α m n (fun ⦃_⦄ => monadLift) f) n γ :=
  InternalCombinators.map (fun {_} => monadLift) f it

/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `filter` and `filterM` are easier to use and
sufficient for most use cases.*

If `it` is an iterator, then `it.filterWithPostcondition f` is another iterator that applies a monadic
predicate `f` to all values emitted by `it` and emits them only if they are accepted by `f`.

`f` is expected to return `PostconditionT n (ULift Bool)`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.filterWithPostcondition f` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**

```text
it                             ---a--b--c--d-e--⊥
it.filterWithPostcondition     ---a-----c-------⊥
```

(given that `f a = f c = pure true` and `f b = f d = d e = pure false`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite`

For certain mapping functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided. For example, if `f` is an `ExceptT` monad and
will always fail, then `it.filterWithPostcondition` will be finite -- and productive -- even if `it`
isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.filterWithPostcondition {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [MonadLiftT m n] [Iterator α m β] (f : β → PostconditionT n (ULift Bool))
    (it : IterM (α := α) m β) :=
  (it.filterMapWithPostcondition
    (fun b => (f b).map (fun x => if x.down = true then some b else none)) : IterM n β)

/--
If `it` is an iterator, then `it.filterMapM f` is another iterator that applies a monadic
function `f` to all values emitted by `it`. `f` is expected to return an `Option` inside the monad.
If `f` returns `none`, then nothing is emitted; if it returns `some x`, then `x` is emitted.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

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
then `it.filterMapM` will be finite even if `it` isn't. In such cases, the termination proof needs
to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f` and matches on the
returned `Option` value.
-/
@[inline, expose]
def IterM.filterMapM {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Monad n] [MonadAttach n] [MonadLiftT m n]
    (f : β → n (Option γ)) (it : IterM (α := α) m β) :=
  (it.filterMapWithPostcondition (fun b => PostconditionT.attachLift (f b)) : IterM n γ)

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
will always fail, then `it.mapM` will be finite even if `it` isn't. In such cases, the termination
proof needs to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.mapM {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] (f : β → n γ) (it : IterM (α := α) m β) :=
  (it.mapWithPostcondition (fun b => PostconditionT.attachLift (f b)) : IterM n γ)

/--
If `it` is an iterator, then `it.filterM f` is another iterator that applies a monadic
predicate `f` to all values emitted by `it` and emits them only if they are accepted by `f`.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

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
isn't. In such cases, the termination proof needs to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] (f : β → n (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.filterMapWithPostcondition
    (fun b => (PostconditionT.attachLift (f b)).map (if ·.down = true then some b else none)) : IterM n β)

/--
If `it` is an iterator, then `it.filterMap f` is another iterator that applies a function `f` to all
values emitted by `it`. `f` is expected to return an `Option`. If it returns `none`, then nothing is
emitted; if it returns `some x`, then `x` is emitted.

In situations where `f` is monadic, use `filterMapM` instead.

**Marble diagram:**

```text
it               ---a --b--c --d-e--⊥
it.filterMap     ---a'-----c'-------⊥
```

(given that `f a = some a'`, `f c = c'` and `f b = f d = d e = none`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite`

For certain mapping functions `f`, the resulting iterator will be productive even though
no `Productive` instance is provided. For example, if `f` never returns `none`, then
this combinator will preserve productiveness. In such situations, the missing instance needs to
be proved manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f` and matches on the
returned `Option` value.
-/
@[inline, expose]
def IterM.filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Monad m] (f : β → Option γ) (it : IterM (α := α) m β) :=
  (it.filterMapWithPostcondition (fun b => pure (f b)) : IterM m γ)

/--
If `it` is an iterator, then `it.map f` is another iterator that applies a
function `f` to all values emitted by `it` and emits the result.

In situations where `f` is monadic, use `mapM` instead.

**Marble diagram:**

```text
it         ---a --b --c --d -e ----⊥
it.map     ---a'--b'--c'--d'-e'----⊥
```

(given that `f a = a'`, `f b = b'` etc.)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.map {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m] (f : β → γ)
    (it : IterM (α := α) m β) :=
  (it.mapWithPostcondition (fun b => pure (f b)) : IterM m γ)

/--
If `it` is an iterator, then `it.filter f` is another iterator that applies a
predicate `f` to all values emitted by `it` and emits them only if they are accepted by `f`.

In situations where `f` is monadic, use `filterM` instead.

**Marble diagram (without monadic effects):**

```text
it            ---a--b--c--d-e--⊥
it.filter     ---a-----c-------⊥
```

(given that `f a = f c = true` and `f b = f d = d e = false`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite`

For certain mapping functions `f`, the resulting iterator will be productive even though
no `Productive` instance is provided. For example, if `f` always returns `True`, the resulting
iterator will be productive as long as `it` is. In such situations, the missing instance needs to
be proved manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f` and matches on the
returned value.
-/
@[inline, expose]
def IterM.filter {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    (f : β → Bool) (it : IterM (α := α) m β) :=
  (it.filterMap (fun b => if f b then some b else none) : IterM m β)

end Std
