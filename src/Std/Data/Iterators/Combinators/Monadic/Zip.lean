/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Option.Lemmas
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Loop
import Init.Data.Iterators.Internal.Termination

/-!

# Monadic `zip` combinator

This file provides an iterator combinator `IterM.zip` that combines two iterators into an iterator
of pairs.
-/

namespace Std.Internal.Option

/- TODO: move this to Init.Data.Option -/
namespace SomeLtNone

/--
Lifts an ordering relation to `Option`, such that `none` is the greatest element.

It can be understood as adding a distinguished greatest element, represented by `none`, to both `α`
and `β`.

Caution: Given `LT α`, `Option.SomeLtNone.lt LT.lt` differs from the `LT (Option α)` instance,
which is implemented by `Option.lt Lt.lt`.

Examples:
 * `Option.lt (fun n k : Nat => n < k) none none = False`
 * `Option.lt (fun n k : Nat => n < k) none (some 3) = False`
 * `Option.lt (fun n k : Nat => n < k) (some 3) none = True`
 * `Option.lt (fun n k : Nat => n < k) (some 4) (some 5) = True`
 * `Option.lt (fun n k : Nat => n < k) (some 4) (some 4) = False`
-/
def lt {α} (r : α → α → Prop) : Option α → Option α → Prop
  | none, _ => false
  | some _, none => true
  | some a', some a => r a' a

end SomeLtNone

/- TODO: Move these to Init.Data.Option.Lemmas in a separate PR -/
theorem wellFounded_lt {α} {rel : α → α → Prop} (h : WellFounded rel) :
    WellFounded (Option.lt rel) := by
  refine ⟨fun x => ?_⟩
  have hn : Acc (Option.lt rel) none := by
    refine Acc.intro none ?_
    intro y hyx
    cases y <;> cases hyx
  cases x
  · exact hn
  · rename_i x
    induction h.apply x
    rename_i x' h ih
    refine Acc.intro _ ?_
    intro y hyx'
    cases y
    · exact hn
    · exact ih _ hyx'

theorem SomeLtNone.wellFounded_lt {α} {r : α → α → Prop} (h : WellFounded r) :
    WellFounded (SomeLtNone.lt r) := by
  refine ⟨?_⟩
  intro x
  constructor
  intro x' hlt
  match x' with
  | none => contradiction
  | some x' =>
    clear hlt
    induction h.apply x'
    rename_i ih
    constructor
    intro x'' hlt'
    match x'' with
    | none => contradiction
    | some x'' => exact ih x'' hlt'

end Std.Internal.Option

namespace Std.Iterators
open Std.Internal

variable {m : Type w → Type w'}
  {α₁ : Type w} {β₁ : Type w} [Iterator α₁ m β₁]
  {α₂ : Type w} {β₂ : Type w} [Iterator α₂ m β₂]

/--
Internal state of the `zip` combinator. Do not depend on its internals.
-/
@[unbox]
structure Zip (α₁ : Type w) (m : Type w → Type w') {β₁ : Type w} [Iterator α₁ m β₁] (α₂ : Type w) (β₂ : Type w) where
  left : IterM (α := α₁) m β₁
  memoizedLeft : (Option { out : β₁ // ∃ it : IterM (α := α₁) m β₁, it.IsPlausibleOutput out })
  right : IterM (α := α₂) m β₂

/--
`it.PlausibleStep step` is the proposition that `step` is a possible next step from the
`zip` iterator `it`. This is mostly internally relevant, except if one needs to manually
prove termination (`Finite` or `Productive` instances, for example) of a `zip` iterator.
-/
inductive Zip.PlausibleStep (it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)) :
    IterStep (IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)) (β₁ × β₂) → Prop where
  | yieldLeft (hm : it.internalState.memoizedLeft = none) {it' out}
      (hp : it.internalState.left.IsPlausibleStep (.yield it' out)) :
      PlausibleStep it (.skip ⟨⟨it', (some ⟨out, _, _, hp⟩), it.internalState.right⟩⟩)
  | skipLeft (hm : it.internalState.memoizedLeft = none) {it'}
      (hp : it.internalState.left.IsPlausibleStep (.skip it')) :
      PlausibleStep it (.skip ⟨⟨it', none, it.internalState.right⟩⟩)
  | doneLeft (hm : it.internalState.memoizedLeft = none)
      (hp : it.internalState.left.IsPlausibleStep .done) :
      PlausibleStep it .done
  | yieldRight {out₁} (hm : it.internalState.memoizedLeft = some out₁) {it₂' out₂}
      (hp : it.internalState.right.IsPlausibleStep (.yield it₂' out₂)) :
      PlausibleStep it (.yield ⟨⟨it.internalState.left, none, it₂'⟩⟩ (out₁, out₂))
  | skipRight {out₁} (hm : it.internalState.memoizedLeft = some out₁) {it₂'}
      (hp : it.internalState.right.IsPlausibleStep (.skip it₂')) :
      PlausibleStep it (.skip ⟨⟨it.internalState.left, (some out₁), it₂'⟩⟩)
  | doneRight {out₁} (hm : it.internalState.memoizedLeft = some out₁)
      (hp : it.internalState.right.IsPlausibleStep .done) :
      PlausibleStep it .done

instance Zip.instIterator [Monad m] :
    Iterator (Zip α₁ m α₂ β₂) m (β₁ × β₂) where
  IsPlausibleStep := PlausibleStep
  step it :=
    match hm : it.internalState.memoizedLeft with
    | none => do
      match ← it.internalState.left.step with
      | .yield it₁' out hp =>
          pure <| .skip ⟨⟨it₁', (some ⟨out, _, _, hp⟩), it.internalState.right⟩⟩ (.yieldLeft hm hp)
      | .skip it₁' hp =>
          pure <| .skip ⟨⟨it₁', none, it.internalState.right⟩⟩ (.skipLeft hm hp)
      | .done hp =>
          pure <| .done (.doneLeft hm hp)
    | some out₁ => do
      match ← it.internalState.right.step with
      | .yield it₂' out₂ hp =>
          pure <| .yield ⟨⟨it.internalState.left, none, it₂'⟩⟩ (out₁, out₂) (.yieldRight hm hp)
      | .skip it₂' hp =>
          pure <| .skip ⟨⟨it.internalState.left, (some out₁), it₂'⟩⟩ (.skipRight hm hp)
      | .done hp =>
          pure <| .done (.doneRight hm hp)

/--
Given two iterators `left` and `right`, `left.zip right` is an iterator that yields pairs of
outputs of `left` and `right`. When one of them terminates,
the `zip` iterator will also terminate.

**Marble diagram:**

```text
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```

**Termination properties:**

* `Finite` instance: only if either `left` or `right` is finite and the other is productive
* `Productive` instance: only if `left` and `right` are productive

There are situations where `left.zip right` is finite (or productive) but none of the instances
above applies. For example, if the computation happens in an `Except` monad and `left` immediately
fails when calling `step`, then `left.zip right` will also do so. In such a case, the `Finite`
(or `Productive`) instance needs to be proved manually.

**Performance:**

This combinator incurs an additional O(1) cost with each step taken by `left` or `right`.

Right now, the compiler does not unbox the internal state, leading to worse performance than
possible.
-/
@[always_inline, inline]
def IterM.zip
    (left : IterM (α := α₁) m β₁) (right : IterM (α := α₂) m β₂) :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) :=
  toIterM ⟨left, none, right⟩ m _

variable (m) in
def Zip.Rel₁ [Finite α₁ m] [Productive α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      IterM.TerminationMeasures.Finite.Rel
      (Prod.Lex (Option.lt emptyRelation) IterM.TerminationMeasures.Productive.Rel))
    (fun it => (it.internalState.left.finitelyManySteps, (it.internalState.memoizedLeft, it.internalState.right.finitelyManySkips)))

theorem Zip.rel₁_of_left [Finite α₁ m] [Productive α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.internalState.left.finitelyManySteps.Rel it.internalState.left.finitelyManySteps) :
    Zip.Rel₁ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₁_of_memoizedLeft [Finite α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b' b} {right' right : IterM (α := α₂) m β₂}
    (h : Option.lt emptyRelation b' b) :
    Zip.Rel₁ m ⟨left, b', right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₁_of_right [Finite α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b b' : _} {it' it : IterM (α := α₂) m β₂}
    (h : b' = b)
    (h' : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Zip.Rel₁ m ⟨left, b', it'⟩ ⟨left, b, it⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

def Zip.instFinitenessRelation₁ [Monad m] [Finite α₁ m] [Productive α₂ m] :
    FinitenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.Rel₁ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply Option.wellFounded_lt
        exact emptyWf.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldLeft hm it' out hp =>
      cases h
      apply Zip.rel₁_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skipLeft hm it' hp =>
      cases h
      apply Zip.rel₁_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case doneLeft hm hp =>
      cases h
    case yieldRight out₁ hm it₂' out₂ hp =>
      cases h
      apply Zip.rel₁_of_memoizedLeft
      simp [Option.lt, hm]
    case skipRight out₁ hm it₂' hp =>
      cases h
      apply Zip.rel₁_of_right
      · simp_all
      · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case doneRight out₁ hm hp =>
      cases h

instance Zip.instFinite₁ [Monad m] [Finite α₁ m] [Productive α₂ m] :
    Finite (Zip α₁ m α₂ β₂) m :=
  Finite.of_finitenessRelation Zip.instFinitenessRelation₁

variable (m) in
def Zip.Rel₂ [Productive α₁ m] [Finite α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      IterM.TerminationMeasures.Finite.Rel
      (Prod.Lex (Option.SomeLtNone.lt emptyRelation) IterM.TerminationMeasures.Productive.Rel))
    (fun it => (it.internalState.right.finitelyManySteps, (it.internalState.memoizedLeft, it.internalState.left.finitelyManySkips)))

theorem Zip.rel₂_of_right [Productive α₁ m] [Finite α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.internalState.right.finitelyManySteps.Rel it.internalState.right.finitelyManySteps) : Zip.Rel₂ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₂_of_memoizedLeft [Productive α₁ m] [Finite α₂ m]
    {right : IterM (α := α₂) m β₂} {b' b} {left' left : IterM (α := α₁) m β₁}
    (h : Option.SomeLtNone.lt emptyRelation b' b) :
    Zip.Rel₂ m ⟨left, b', right⟩ ⟨left', b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₂_of_left [Productive α₁ m] [Finite α₂ m]
    {right : IterM (α := α₂) m β₂} {b b' : _} {it' it : IterM (α := α₁) m β₁}
    (h : b' = b)
    (h' : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Zip.Rel₂ m ⟨it', b', right⟩ ⟨it, b, right⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

def Zip.instFinitenessRelation₂ [Monad m] [Productive α₁ m] [Finite α₂ m] :
    FinitenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.Rel₂ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply Option.SomeLtNone.wellFounded_lt
        exact emptyWf.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldLeft hm it' out hp =>
      cases h
      apply Zip.rel₂_of_memoizedLeft
      simp_all [Option.SomeLtNone.lt]
    case skipLeft hm it' hp =>
      cases h
      apply Zip.rel₂_of_left
      · simp_all
      · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case doneLeft hm hp =>
      cases h
    case yieldRight out₁ hm it₂' out₂ hp =>
      cases h
      apply Zip.rel₂_of_right
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skipRight out₁ hm it₂' hp =>
      cases h
      apply Zip.rel₂_of_right
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case doneRight out₁ hm hp =>
      cases h

instance Zip.instFinite₂ [Monad m] [Productive α₁ m] [Finite α₂ m] :
    Finite (Zip α₁ m α₂ β₂) m :=
  Finite.of_finitenessRelation Zip.instFinitenessRelation₂

variable (m) in
def Zip.Rel₃ [Productive α₁ m] [Productive α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      (Option.SomeLtNone.lt emptyRelation)
      (Prod.Lex (IterM.TerminationMeasures.Productive.Rel) IterM.TerminationMeasures.Productive.Rel))
    (fun it => (it.internalState.memoizedLeft, (it.internalState.left.finitelyManySkips, it.internalState.right.finitelyManySkips)))

theorem Zip.rel₃_of_memoizedLeft [Productive α₁ m] [Productive α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : Option.SomeLtNone.lt emptyRelation it'.internalState.memoizedLeft it.internalState.memoizedLeft) :
    Zip.Rel₃ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₃_of_left [Productive α₁ m] [Productive α₂ m]
    {left' left : IterM (α := α₁) m β₁} {b} {right' right : IterM (α := α₂) m β₂}
    (h : left'.finitelyManySkips.Rel left.finitelyManySkips) :
    Zip.Rel₃ m ⟨left', b, right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₃_of_right [Productive α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b b' : _} {it' it : IterM (α := α₂) m β₂}
    (h : b' = b)
    (h' : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Zip.Rel₃ m ⟨left, b', it'⟩ ⟨left, b, it⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

def Zip.instProductivenessRelation [Monad m] [Productive α₁ m] [Productive α₂ m] :
    ProductivenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.Rel₃ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · apply Option.SomeLtNone.wellFounded_lt
      exact emptyWf.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · exact WellFoundedRelation.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    cases h
    case yieldLeft hm it' out hp =>
      apply Zip.rel₃_of_memoizedLeft
      simp [Option.SomeLtNone.lt, hm]
    case skipLeft hm it' hp =>
      obtain ⟨⟨left, memoizedLeft, right⟩⟩ := it
      simp only at hm
      rw [hm]
      apply Zip.rel₃_of_left
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case skipRight out₁ hm it₂' hp =>
      apply Zip.rel₃_of_right
      · simp_all
      · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›

instance Zip.instProductive [Monad m] [Productive α₁ m] [Productive α₂ m] :
    Productive (Zip α₁ m α₂ β₂) m :=
  Productive.of_productivenessRelation Zip.instProductivenessRelation

instance Zip.instIteratorCollect [Monad m] [Monad n] :
    IteratorCollect (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

instance Zip.instIteratorCollectPartial [Monad m] [Monad n] :
    IteratorCollectPartial (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

instance Zip.instIteratorLoop [Monad m] [Monad n] :
    IteratorLoop (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

instance Zip.instIteratorLoopPartial [Monad m] [Monad n] :
    IteratorLoopPartial (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

instance Zip.instIteratorSize [Monad m] [Finite (Zip α₁ m α₂ β₂) m] :
    IteratorSize (Zip α₁ m α₂ β₂) m :=
  .defaultImplementation

instance Zip.instIteratorSizePartial [Monad m] :
    IteratorSizePartial (Zip α₁ m α₂ β₂) m :=
  .defaultImplementation

end Std.Iterators
