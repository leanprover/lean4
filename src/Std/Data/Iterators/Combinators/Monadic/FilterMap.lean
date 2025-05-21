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
* `H` suffix: heterogeneous variant that allows switching the monad and the universes.
-/

namespace Std.Iterators

section FilterMap

/--
Internal state of the `filterMap` combinator. Do not depend on its internals.
-/
@[ext, unbox]
structure FilterMap (α : Type w) {β : Type w} {γ : Type w}
    {m : Type w → Type w'} (f : β → PostconditionT m (Option γ)) where
  inner : IterM (α := α) m β

variable {α : Type w} {m : Type w → Type w'} {β : Type w} {γ : Type w}
    [Monad m] [Iterator α m β] {f : β → PostconditionT m (Option γ)}

/--
Given an iterator `it`, a monadic `Option`-valued mapping function `f` and a monad transformation `mf`,
`it.filterMapWithProof f mf` is an iterator that applies `f` to each output of `it`. If `f` returns `none`,
the output is dropped. If it returns `some x`, then the iterator yields `x`.

**Marble diagram (without monadic effects):**

```text
it                 ---a --b--c --d-e--⊥
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
def IterM.filterMapWithProof [Monad m] [Iterator α m β] (f : β → PostconditionT m (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMap α f) m γ :=
  toIterM ⟨it⟩ m γ

def Map (α : Type w) {β : Type w} {γ : Type w} {m : Type w → Type w'} [Functor m]
    (f : β → PostconditionT m γ) :=
  FilterMap α (fun b => PostconditionT.map some (f b))

inductive FilterMap.PlausibleStep (it : IterM (α := FilterMap α f) m γ) :
    IterStep (IterM (α := FilterMap α f) m γ) γ → Prop where
  | yieldNone : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f out).Property none → PlausibleStep it (.skip (it'.filterMapWithProof f))
  | yieldSome : ∀ {it' out out'}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (f out).Property (some out') → PlausibleStep it (.yield (it'.filterMapWithProof f) out')
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') → PlausibleStep it (.skip (it'.filterMapWithProof f))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done

instance FilterMap.instIterator : Iterator (FilterMap α f) m γ where
  IsPlausibleStep := FilterMap.PlausibleStep
  step it := do
    match ← it.internalState.inner.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ => pure <| .skip (it'.filterMapWithProof f) (.yieldNone h h')
      | ⟨some out', h'⟩ => pure <| .yield (it'.filterMapWithProof f) out' (.yieldSome h h')
    | .skip it' h => pure <| .skip (it'.filterMapWithProof f) (.skip h)
    | .done h => pure <| .done (.done h)

instance {f : β → PostconditionT m γ} :
    Iterator (Map α f) m γ :=
  inferInstanceAs <| Iterator (FilterMap α _) m γ

private def FilterMap.instFinitenessRelation [Finite α m] : FinitenessRelation (FilterMap α f) m where
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

instance FilterMap.instFinite [Finite α m] : Finite (FilterMap α f) m :=
  Finite.of_finitenessRelation FilterMap.instFinitenessRelation

instance {f : β → PostconditionT m γ} [Finite α m] : Finite (Map α f) m :=
  Finite.of_finitenessRelation FilterMap.instFinitenessRelation

private def Map.instProductivenessRelation {f : β → PostconditionT m γ} [Productive α m] :
    ProductivenessRelation (Map α f) m where
  rel := InvImage IterM.IsPlausibleSkipSuccessorOf (FilterMap.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    cases h
    case yieldNone it' out h h' =>
      simp at h'
    case skip it' h =>
      exact h

instance Map.instProductive {f : β → PostconditionT m γ} [Productive α m] :
    Productive (Map α f) m :=
  Productive.of_productivenessRelation Map.instProductivenessRelation

instance {f : β → PostconditionT m (Option γ)} [Finite α m] :
    IteratorCollect (FilterMap α f) m :=
  .defaultImplementation

instance {f : β → PostconditionT m (Option γ)} :
    IteratorCollectPartial (FilterMap α f) m :=
  .defaultImplementation

instance FilterMap.instIteratorLoop [Monad m] [Monad n]
    [Iterator α m β] :
    IteratorLoop (FilterMap α f) m n :=
  .defaultImplementation

instance FilterMap.instIteratorLoopPartial [Monad m] [Monad n]
    [Iterator α m β] :
    IteratorLoopPartial (FilterMap α f) m n :=
  .defaultImplementation

/--
`map` operations allow for a more efficient implementation of `toArray`. For example,
`array.iter.map f |>.toArray happens in-place if possible.
-/
instance {f : β → PostconditionT m γ} [Finite α m] [IteratorCollect α m] :
    IteratorCollect (Map α f) m where
  toArrayMapped g it :=
    IteratorCollect.toArrayMapped
      (fun x => do g (← (f x).operation))
      it.internalState.inner

instance {f : β → PostconditionT m γ} [IteratorCollectPartial α m] :
    IteratorCollectPartial (Map α f) m where
  toArrayMappedPartial g it :=
    IteratorCollectPartial.toArrayMappedPartial
      (fun x => do g (← (f x).operation))
      it.internalState.inner

instance Map.instIteratorLoop {f : β → PostconditionT m γ}
    [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoop (Map α f) m n :=
  .defaultImplementation

instance Map.instIteratorLoopPartial {f : β → PostconditionT m γ}
    [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoopPartial (Map α f) m n :=
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
def IterM.mapWithProof [Monad m] [Iterator α m β] (f : β → PostconditionT m γ) (it : IterM (α := α) m β) :
    IterM (α := Map α f) m γ :=
  toIterM ⟨it⟩ m γ

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
def IterM.filterWithProof [Monad m] [Iterator α m β] (f : β → PostconditionT m (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof
    (fun b => (f b).map (fun x => if x.down = true then some b else none)) : IterM m β)

end FilterMap

section FilterMap

variable {α : Type w} {β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    {γ : Type w} {f : β → Option γ}

@[inline]
def IterM.filterMap (f : β → Option γ) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => pure (f b)) : IterM m γ)

@[inline]
def IterM.map (f : β → γ) (it : IterM (α := α) m β) :=
  (it.mapWithProof (fun b => pure (f b)) : IterM m γ)

@[inline]
def IterM.filter (f : β → Bool) (it : IterM (α := α) m β) :=
  (it.filterMap (fun b => if f b then some b else none) : IterM m β)

end FilterMap

section FilterMapM

variable {m : Type w → Type w'} {α : Type w} {β : Type w} {γ : Type w} {f : β → Option γ}

@[inline]
def IterM.filterMapM [Iterator α m β] [Monad m] (f : β → m (Option γ)) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => monadLift (f b)) : IterM m γ)

@[inline]
def IterM.mapM [Iterator α m β] [Monad m] (f : β → m γ) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => some <$> monadLift (f b)) : IterM m γ)

@[inline]
def IterM.filterM [Iterator α m β] [Monad m] (f : β → m (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof
    (fun b => (PostconditionT.lift (f b)).map (if ·.down = true then some b else none)) : IterM m β)

end FilterMapM

end Std.Iterators
