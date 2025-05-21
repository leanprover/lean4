/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Basic
import Std.Data.Iterators.Consumers.Collect
import Std.Data.Iterators.Consumers.Loop
import Std.Data.Iterators.PostConditionMonad
import Std.Data.Iterators.Internal.Termination

/-!
This file provides iterator combinators for filtering and mapping.

* `IterM.filterMap` either modifies or drops each value based on an option-valued mapping function.
* `IterM.filter` drops some elements based on a predicate.
* `IterM.map` modifies each value based on a mapping function

Several variants of these combinators are provided:

* `M` suffix: monadic mapping function
-/

namespace Std.Iterators

/--
Internal state of the `filterMap` combinator. Do not depend on its internals.
-/
@[ext, unbox]
structure FilterMap (α : Type w) {β γ : Type w}
    (m : Type w → Type w') (n : Type w → Type w'') (lift : {α : Type w} → m α → n α)
    (f : β → PostconditionT n (Option γ)) where
  inner : IterM (α := α) m β

/--
Internal state of the `filterMap` combinator. Do not depend on its internals.
-/
def Map (α : Type w) {β γ : Type w} (m : Type w → Type w') (n : Type w → Type w'')
    (lift : {α : Type w} → m α → n α) [Functor n]
    (f : β → PostconditionT n γ) :=
  FilterMap α m n lift (fun b => PostconditionT.map some (f b))

@[always_inline, inline]
def IterM.InternalCombinators.filterMap {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} (lift : {α : Type w} → m α → n α)
    [Iterator α m β] (f : β → PostconditionT n (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMap α m n lift f) n γ :=
  toIterM ⟨it⟩ n γ

/--
Given an iterator `it`, a monadic `Option`-valued mapping function `f` and a monad transformation `mf`,
`it.filterMapWithProof f mf` is an iterator that applies `f` to each output of `it`. If `f` returns `none`,
the output is dropped. If it returns `some x`, then the iterator yields `x`.

**Marble diagram (without monadic effects):**

```text
it                        ---a --b--c --d-e--⊥
it.filterMapWithProof     ---a'-----c'-------⊥
```

(given that `f a = some a'`, `f c = some c'` and `f b = f d = d e = none`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: not available

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` in addition to the cost of the monadic effects.
-/
@[inline]
def IterM.filterMapWithProof {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadLiftT m n] [Iterator α m β] (f : β → PostconditionT n (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMap α m n monadLift f) n γ :=
  IterM.InternalCombinators.filterMap monadLift f it

inductive FilterMap.PlausibleStep {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    {lift : {α : Type w} → m α → n α} {f : β → PostconditionT n (Option γ)} [Iterator α m β]
    (it : IterM (α := FilterMap α m n lift f) n γ) :
    IterStep (IterM (α := FilterMap α m n lift f) n γ) γ → Prop where
  | yieldNone : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f out).Property none → PlausibleStep it (.skip (IterM.InternalCombinators.filterMap lift f it'))
  | yieldSome : ∀ {it' out out'}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f out).Property (some out') → PlausibleStep it (.yield (IterM.InternalCombinators.filterMap lift f it') out')
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') → PlausibleStep it (.skip (IterM.InternalCombinators.filterMap lift f it'))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done

instance FilterMap.instIterator {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    {lift : {α : Type w} → m α → n α} {f : β → PostconditionT n (Option γ)}
    [Iterator α m β] [Monad n] :
    Iterator (FilterMap α m n lift f) n γ where
  IsPlausibleStep := FilterMap.PlausibleStep (m := m) (n := n)
  step it :=
    letI : MonadLift m n := ⟨lift⟩
    do
      match ← it.internalState.inner.step with
      | .yield it' out h => do
        match ← (f out).operation with
        | ⟨none, h'⟩ => pure <| .skip (it'.filterMapWithProof f) (.yieldNone h h')
        | ⟨some out', h'⟩ => pure <| .yield (it'.filterMapWithProof f) out' (.yieldSome h h')
      | .skip it' h => pure <| .skip (it'.filterMapWithProof f) (.skip h)
      | .done h => pure <| .done (.done h)

instance {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n] [Iterator α m β]
    {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} :
    Iterator (Map α m n lift f) n γ :=
  inferInstanceAs <| Iterator (FilterMap α m n lift _) n γ

private def FilterMap.instFinitenessRelation {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] :
    FinitenessRelation (FilterMap α m n lift f) n where
  rel := InvImage IterM.IsPlausibleSuccessorOf (FilterMap.inner ∘ IterM.internalState)
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

instance FilterMap.instFinite {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] : Finite (FilterMap α m n lift f) n :=
  Finite.of_finitenessRelation FilterMap.instFinitenessRelation

instance {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n] [Iterator α m β]
    {lift : {α : Type w} → m α → n α} {f : β → PostconditionT n γ} [Finite α m] :
    Finite (Map α m n lift f) n :=
  Finite.of_finitenessRelation FilterMap.instFinitenessRelation

private def Map.instProductivenessRelation {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} [Productive α m] :
    ProductivenessRelation (Map α m n lift f) n where
  rel := InvImage IterM.IsPlausibleSkipSuccessorOf (FilterMap.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    cases h
    case yieldNone it' out h h' =>
      simp at h'
    case skip it' h =>
      exact h

instance Map.instProductive {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} [Productive α m] :
    Productive (Map α m n lift f) n :=
  Productive.of_productivenessRelation Map.instProductivenessRelation

instance {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type x} [Monad n] [Monad o] [Iterator α m β]
    {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] :
    IteratorCollect (FilterMap α m n lift f) n o :=
  .defaultImplementation

instance {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type x} [Monad n] [Monad o] [Iterator α m β]
    {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] :
    IteratorCollectPartial (FilterMap α m n lift f) n o :=
  .defaultImplementation

-- TODO
instance FilterMap.instIteratorLoop {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad n] [Monad o] [Iterator α m β] {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] :
    IteratorLoop (FilterMap α m n lift f) n o :=
  .defaultImplementation

instance FilterMap.instIteratorLoopPartial {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad n] [Monad o] [Iterator α m β] {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n (Option γ)} [Finite α m] :
    IteratorLoopPartial (FilterMap α m n lift f) n o :=
  .defaultImplementation

/--
`map` operations allow for a more efficient implementation of `toArray`. For example,
`array.iter.map f |>.toArray happens in-place if possible.
-/
instance Map.instIteratorCollect {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type x} [Monad n] [Monad o] [Iterator α m β]
    {lift₁ : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} [Finite α m] [IteratorCollect α m o] :
    IteratorCollect (Map α m n lift₁ f) n o where
  toArrayMapped lift₂ _ g it :=
    IteratorCollect.toArrayMapped
      (lift := lift₂ ∘ lift₁)
      (fun x => do g (← lift₂ (f x).operation))
      it.internalState.inner (m := m)

instance Map.instIteratorCollectPartial {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type x} [Monad n] [Monad o] [Iterator α m β]
    {lift₁ : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} [IteratorCollectPartial α m o] :
    IteratorCollectPartial (Map α m n lift₁ f) n o where
  toArrayMappedPartial lift₂ _ g it :=
    IteratorCollectPartial.toArrayMappedPartial
      (lift := lift₂ ∘ lift₁)
      (fun x => do g (← lift₂ (f x).operation))
      it.internalState.inner (m := m)

instance Map.instIteratorLoop {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type x} [Monad n] [Monad o] [Iterator α m β]
    {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} :
    IteratorLoop (Map α m n lift f) n o :=
  .defaultImplementation

instance Map.instIteratorLoopPartial {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} {o : Type w → Type x} [Monad n] [Monad o] [Iterator α m β]
    {lift : {α : Type w} → m α → n α}
    {f : β → PostconditionT n γ} :
    IteratorLoopPartial (Map α m n lift f) n o :=
  .defaultImplementation

/--
Given an iterator `it`, a monadic mapping function `f` and a monad transformation `mf`,
`it.mapMH f mf` is an iterator that applies `f` to each output of `it`. If `f` returns `none`,
the output is dropped. If it returns `some x`, then the iterator yields `x`.

**Marble diagram (without monadic effects):**

```text
it                 ---a --b --c --d -e --⊥
it.mapMH           ---a'--b'--c'--d'-e'--⊥
```

(given that `f a = a'` and so on)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`. This requires us to wrap the FilterMap into a new type.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` in addition to the cost of the monadic effects.
-/
@[inline]
def IterM.mapWithProof {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [MonadLiftT m n] [Iterator α m β] (f : β → PostconditionT n γ)
    (it : IterM (α := α) m β) : IterM (α := Map α m n monadLift f) n γ :=
  toIterM ⟨it⟩ n γ

/--
Given an iterator `it`, a monadic predicate `p` and a monad transformation `mf`,
`it.filterMH p mf` is an iterator that applies `p` to each output of `it`. If `p` returns `false`,
the output is dropped. Otherwise, the iterator forwards the output of `it`.

**Marble diagram (without monadic effects):**

```text
it                 ---a--b--c--d-e--⊥
it.filterMH        ---a-----c-------⊥
```

(given that `f a = f c = true'` and `f b = f d = d e = false`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: not available

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` in addition to the cost of the monadic effects.
-/
@[inline]
def IterM.filterWithProof {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [MonadLiftT m n] [Iterator α m β] (f : β → PostconditionT n (ULift Bool))
    (it : IterM (α := α) m β) :=
  (it.filterMapWithProof
    (fun b => (f b).map (fun x => if x.down = true then some b else none)) : IterM n β)

@[inline]
def IterM.filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Monad m] (f : β → Option γ) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => pure (f b)) : IterM m γ)

@[inline]
def IterM.map {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m] (f : β → γ)
    (it : IterM (α := α) m β) :=
  (it.mapWithProof (fun b => pure (f b)) : IterM m γ)

@[inline]
def IterM.filter {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    (f : β → Bool) (it : IterM (α := α) m β) :=
  (it.filterMap (fun b => if f b then some b else none) : IterM m β)

@[inline]
def IterM.filterMapM {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Monad n] [MonadLiftT m n]
    (f : β → n (Option γ)) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => monadLift (f b)) : IterM n γ)

@[inline]
def IterM.mapM {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadLiftT m n] (f : β → n γ) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => some <$> monadLift (f b)) : IterM n γ)

@[inline]
def IterM.filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadLiftT m n] (f : β → n (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof
    (fun b => (PostconditionT.lift (f b)).map (if ·.down = true then some b else none)) : IterM n β)

end Std.Iterators
