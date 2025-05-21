/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Basic
import Std.Data.Iterators.Consumers.Collect
import Std.Data.Iterators.Consumers.Loop

/-!
This file provides iterator combinators for filtering and mapping.

* `IterM.filterMap` either modifies or drops each value based on an option-valued mapping function.
* `IterM.filter` drops some elements based on a predicate.
* `IterM.map` modifies each value based on a mapping function

Several variants of these combinators are provided:

* `M` suffix: monadic mapping function
* `H` suffix: heterogeneous variant that allows switching the monad and the universes.
-/

section FilterMap

universe u' v' u v

@[ext, unbox]
structure FilterMap (α : Type w) {β : Type w} {γ : Type w}
    {m : Type w → Type w'} (f : β → HetT m (Option γ)) where
  inner : IterM (α := α) m β

variable {α : Type w} {m : Type w → Type w'} {β : Type w} {γ : Type w}
    [Monad m] [Iterator α m β] {f : β → HetT m (Option γ)}

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
def IterM.filterMapWithProof [Monad m] [Iterator α m β] (f : β → HetT m (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMap α f) m γ :=
  toIter ⟨it⟩ m γ

def Map (α : Type w) {β : Type w} {γ : Type w} {m : Type w → Type w'} [Functor m]
    (f : β → HetT m γ) :=
  FilterMap α (fun b => HetT.mapH some (f b))

inductive FilterMap.PlausibleStep (it : IterM (α := FilterMap α f) m γ) : (step : IterStep (IterM (α := FilterMap α f) m γ) γ) → Prop where
  | yieldNone : ∀ {it' out}, it.inner.inner.plausible_step (.yield it' out) →
      (f out).property none → PlausibleStep it (.skip (it'.filterMapWithProof f))
  | yieldSome : ∀ {it' out out'}, it.inner.inner.plausible_step (.yield it' out) →
      (f out).property (some out') → PlausibleStep it (.yield (it'.filterMapWithProof f) out')
  | skip : ∀ {it'}, it.inner.inner.plausible_step (.skip it') → PlausibleStep it (.skip (it'.filterMapWithProof f))
  | done : it.inner.inner.plausible_step .done → PlausibleStep it .done

instance FilterMap.instIterator : Iterator (FilterMap α f) m γ where
  plausible_step := FilterMap.PlausibleStep
  step it := do
    match ← it.inner.inner.step with
    | .yield it' out h => do
      match ← (f out).computation with
      | ⟨none, h'⟩ => pure <| .skip (it'.filterMapWithProof f) (.yieldNone h h')
      | ⟨some out', h'⟩ => pure <| .yield (it'.filterMapWithProof f) out' (.yieldSome h h')
    | .skip it' h => pure <| .skip (it'.filterMapWithProof f) (.skip h)
    | .done h => pure <| .done (.done h)

instance {f : β → HetT m γ} :
    Iterator (Map α f) m γ :=
  inferInstanceAs <| Iterator (FilterMap α _) m γ

instance FilterMap.instFinitenessRelation [Finite α m] : FinitenessRelation (FilterMap α f) m where
  rel := InvImage IterM.plausible_successor_of (FilterMap.inner ∘ IterM.inner)
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldNone it' out h' h'' =>
      cases h
      exact IterM.plausible_successor_of_yield h'
    case yieldSome it' out h' h'' =>
      cases h
      exact IterM.plausible_successor_of_yield h'
    case skip it' h' =>
      cases h
      exact IterM.plausible_successor_of_skip h'
    case done h' =>
      cases h

instance {f : β → HetT m γ} [Finite α m] :
    Finite (Map α f) m :=
  inferInstanceAs <| Finite (FilterMap α _) m

instance {f : β → HetT m γ} [Productive α m] :
    ProductivenessRelation (Map α f) m where
  rel := InvImage IterM.plausible_skip_successor_of (FilterMap.inner ∘ IterM.inner)
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    cases h
    case yieldNone it' out h h' =>
      simp at h'
    case skip it' h =>
      exact h

instance {f : β → HetT m (Option γ)} [Finite α m] :
    IteratorToArray (FilterMap α f) m :=
  .defaultImplementation

instance {f : β → HetT m (Option γ)} :
    IteratorToArrayPartial (FilterMap α f) m :=
  .defaultImplementation

instance FilterMap.instIteratorFor [Monad m] [Monad n]
    [Iterator α m β] :
    IteratorFor (FilterMap α f) m n :=
  .defaultImplementation

instance FilterMap.instIteratorForPartial [Monad m] [Monad n]
    [Iterator α m β] :
    IteratorForPartial (FilterMap α f) m n :=
  .defaultImplementation

/--
`map` operations allow for a more efficient implementation of `toArray`. For example,
`array.iter.map f |>.toArray happens in-place if possible.
-/
instance {f : β → HetT m γ} [IteratorToArray α m] :
    IteratorToArray (Map α f) m where
  toArrayMapped g it :=
    IteratorToArray.toArrayMapped
      (fun x => do g (← (f x).computation))
      it.inner.inner

instance {f : β → HetT m γ} [IteratorToArrayPartial α m] :
    IteratorToArrayPartial (Map α f) m where
  toArrayMappedPartial g it :=
    IteratorToArrayPartial.toArrayMappedPartial
      (fun x => do g (← (f x).computation))
      it.inner.inner

instance Map.instIteratorFor {f : β → HetT m γ}
    [Monad m] [Monad n] [Iterator α m β] :
    IteratorFor (Map α f) m n :=
  .defaultImplementation

instance Map.instIteratorForPartial {f : β → HetT m γ}
    [Monad m] [Monad n] [Iterator α m β] :
    IteratorForPartial (Map α f) m n :=
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
def IterM.mapWithProof [Monad m] [Iterator α m β] (f : β → HetT m γ) (it : IterM (α := α) m β) :
    IterM (α := Map α f) m γ :=
  toIter ⟨it⟩ m γ

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
def IterM.filterWithProof [Monad m] [Iterator α m β] (f : β → HetT m (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.filterMapWithProof (fun b => (f b).mapH (fun x => if x.down = true then some b else none)) : IterM m β)

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
  (it.filterMapWithProof (fun b => (HetT.lift (f b)).mapH (if ·.down = true then some b else none)) : IterM m β)

end FilterMapM
