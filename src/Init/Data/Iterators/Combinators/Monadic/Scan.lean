/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module

prelude
public import Init.Data.Iterators.PostconditionMonad
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.Bool

/-!

# `scan`, `scanM` and `scanWithPostcondition` combinators

This file provides iterator combinators for scanning with an accumulator.

* `IterM.scan` threads an accumulator through the iterator using a pure stepping function.
* `IterM.scanM` threads an accumulator using a monadic stepping function.
* `IterM.scanWithPostcondition` threads an accumulator using a monadic stepping function
  whose result is returned as a subtype.

Several variants of these combinators are provided:

* `M` suffix: Instead of a pure function, these variants take a monadic function. Given a suitable
  `MonadLiftT` instance, they also allow lifting the iterator to another monad first and then
  applying the stepping function in this monad.
* `WithPostcondition` suffix: These variants take a monadic stepping function where the return type in the
  monad is a subtype. This variant is in rare cases necessary for the intrinsic verification of an
  iterator, and particularly for specialized termination proofs. If possible, avoid this.
-/

public section
namespace Std
namespace Iterators.Types

/--
  Internal state for the ScanM combinator
-/
structure ScanM  {β γ : Type w} {n : Type w → Type w''}
     (α : Type w) (m : Type w → Type w') (f : γ → β → PostconditionT n γ)
     [MonadLiftT m n] where
  /-- Inner iterator -/
  inner : IterM (α := α) m β
  /-- Current accumulated value -/
  acc : γ
  /-- Whether we need to emit the accumulator (i.e. whether this is the first step)-/
  yieldAcc : Bool

/-- Internal implementation of the `scanM` combinator. See `IterM.scanM` for the public API. -/
@[expose]
public def IterM.InternalCombinators.scanM [MonadLiftT m n]
    (f : γ → β → PostconditionT n γ) (acc : γ) (yieldAcc : Bool) (it : IterM (α := α) m β) :
    IterM (α := ScanM α m f) n γ :=
  .mk ⟨it, acc, yieldAcc⟩

namespace ScanM
variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  {f : γ → β → PostconditionT n γ} [MonadLiftT m n] [Iterator α m β]

/--
`it.IsPlausibleStep` is the proposition that `step` is a possible next step from the `scanM`
iterator `it`. This is mostly an internal implementation detail used to prove termination.
-/
inductive IsPlausibleStep (it : IterM (α := ScanM α m f) n γ) :
    IterStep (IterM (α := ScanM α m f) n γ) γ → Prop where
  /-- When `yieldAcc` is true, the step yields the current accumulator and
      the successor iterator is identical except with `yieldAcc` set to false.
  -/
  | yieldAcc :
      it.internalState.yieldAcc = true →
      IsPlausibleStep it (.yield
        (IterM.InternalCombinators.scanM f it.internalState.acc false it.internalState.inner)
         it.internalState.acc)
  /-- When `yieldAcc` is false and the inner iterator yields `b` with successor `it'`,
      the step yields an `out` satisfying `(f acc b).Property out`, and the successor
      wraps `it'` with `out` as the new accumulator.
  -/
  | yieldNext : ∀ {it' b out},
      it.internalState.yieldAcc = false →
      it.internalState.inner.IsPlausibleStep (.yield it' b) →
      (f it.internalState.acc b).Property out →
      IsPlausibleStep it (.yield (IterM.InternalCombinators.scanM f out false it') out)
  /-- When `yieldAcc` is false and the inner iterator skips with successor `it'`,
      the step skips and the successor wraps `it'` with the same accumulator.
  -/
  | skip : ∀ {it'},
      it.internalState.yieldAcc = false →
      it.internalState.inner.IsPlausibleStep (.skip it') →
      IsPlausibleStep it
      (.skip (IterM.InternalCombinators.scanM f it.internalState.acc false it'))
  /-- When `yieldAcc` is false and the inner iterator is done, the step is done. -/
  | done :
      it.internalState.yieldAcc = false →
      it.internalState.inner.IsPlausibleStep .done →
      IsPlausibleStep it .done

instance instIterator [Monad n] : Iterator (ScanM α m f) n γ where
  IsPlausibleStep := ScanM.IsPlausibleStep
  step it := do
      if h : it.internalState.yieldAcc = true then
        pure <| .deflate <| .yield
          (IterM.InternalCombinators.scanM f it.internalState.acc false it.internalState.inner)
          it.internalState.acc
          (.yieldAcc h)
      else
        match (← it.internalState.inner.step).inflate with
        | .yield inner' b hp => do
          let ⟨newAcc, h_acc⟩ ← (f it.internalState.acc b).operation
          pure <| .deflate <| .yield
            (IterM.InternalCombinators.scanM f newAcc false inner')
            newAcc
            (.yieldNext (Bool.of_not_eq_true h) hp h_acc)
        | .skip inner' hp =>
          pure <| .deflate <| .skip
            (IterM.InternalCombinators.scanM f it.internalState.acc false inner')
            (.skip (Bool.of_not_eq_true h) hp)
        | .done hp =>
          pure <| .deflate <| .done (.done (Bool.of_not_eq_true h) hp)

private def FinRel [Finite α m] :
    IterM (α := ScanM α m f) n γ → IterM (α := ScanM α m f) n γ → Prop :=
  InvImage
    (Prod.Lex (· < ·) IterM.IsPlausibleSuccessorOf)
    (fun it => (it.internalState.yieldAcc, it.internalState.inner))

private theorem FinRel.of_yieldAcc [Finite α m] {it it' : IterM (α := ScanM α m f) n γ}
    (h' : it'.internalState.yieldAcc = false) (h : it.internalState.yieldAcc = true) :
    FinRel it' it := by
  apply Prod.Lex.left
  simp [*, LT.lt]

private theorem FinRel.of_inner [Finite α m] {it it' : IterM (α := ScanM α m f) n γ}
    (h : it'.internalState.yieldAcc = it.internalState.yieldAcc)
    (h' : it'.internalState.inner.IsPlausibleSuccessorOf it.internalState.inner) :
    FinRel it' it := by
  simp [FinRel, InvImage, Prod.Lex.right, *]

private def instFinitenessRelation [Monad n] [Finite α m] : FinitenessRelation (ScanM α m f) n where
  Rel := FinRel
  wf := by
    apply InvImage.wf
    refine ⟨fun _ => Prod.lexAccessible ?_ ?_ _⟩ <;> apply WellFounded.apply
    · exact Bool.lt_wfRel.wf
    · exact Finite.wf
  subrelation h := by
    obtain ⟨step, hstep, hplaus⟩ := h
    cases hplaus <;> cases hstep
    case yieldAcc hya => simp [FinRel.of_yieldAcc, IterM.InternalCombinators.scanM, hya]
    all_goals apply FinRel.of_inner <;> simp only [IterM.InternalCombinators.scanM, *]
    . exact IterM.isPlausibleSuccessorOf_of_yield ‹_›
    . exact IterM.isPlausibleSuccessorOf_of_skip ‹_›

instance instFinite [Monad n] [Finite α m] : Finite (ScanM α m f) n :=
  .of_finitenessRelation instFinitenessRelation

private def instProductivenessRelation [Monad n] [Productive α m] :
    ProductivenessRelation (ScanM α m f) n where
  Rel := InvImage IterM.IsPlausibleSkipSuccessorOf (ScanM.inner ∘ IterM.internalState)
  wf := InvImage.wf _ Productive.wf
  subrelation h := by cases h; assumption

instance instProductive [Monad n] [Productive α m] : Productive (ScanM α m f) n :=
  .of_productivenessRelation instProductivenessRelation

instance instIteratorLoop [Monad m] [Monad n] : IteratorLoop (ScanM α m f) n m :=
  .defaultImplementation

end ScanM
end Iterators.Types

open Std.Iterators.Types Std.Iterators
variable {m : Type w → Type w'} {α β γ : Type w}

/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `scan` and `scanM` are easier to use
and sufficient for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition f acc` is another iterator that applies a
monadic function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

`f` is expected to return `PostconditionT n γ`. The base iterator `it` being monadic in
`m`, `n` can be different from `m`, but `it.scanWithPostcondition f acc` expects a `MonadLiftT m n`
instance. The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**

```text
it                          ---a ---b ---c ---⊥
it.scanWithPostcondition    -i -a'-ab'-abc'---⊥
```

(given that `a' ← f i a'`, `ab' ← f a' b`, `abc' ← f ab' c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain stepping functions `f`, the resulting iterator will be finite even though
no `Finite` instance is provided. For example, if `f` is an `ExceptT` monad and will always fail,
then `it.scanWithPostcondition` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanWithPostcondition {n : Type w → Type w''} [MonadLiftT m n]
    (f : γ → β → PostconditionT n γ) (acc : γ) (it : IterM (α := α) m β) :=
  IterM.InternalCombinators.scanM (n := n) f acc true it

/--
If `it` is an iterator, then `it.scanM f acc` is another iterator that applies a monadic
function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

The base iterator `it` being monadic in `m`, `f` can return values in any monad `n` for which a
`MonadLiftT m n` instance is available.

If `f` is pure, then the simpler variant `it.scan` can be used instead.

**Marble diagram (without monadic effects):**

```text
it           ---a ---b ---c ---⊥
it.scanM     -i -a'-ab'-abc'---⊥
```

(given that `a' ← f i a`, `ab' ← f a' b`, `abc' ← f ab' c`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain stepping functions `f`, the resulting iterator will be finite even though
no `Finite` instance is provided. For example, if `f` is an `ExceptT` monad and will always fail,
then `it.scanM` will be finite even if `it` isn't. In such cases, the termination proof needs
to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scanM {n : Type w → Type w''} [MonadAttach n] [MonadLiftT m n]
    (f : γ → β → n γ) (acc : γ) (it : IterM (α := α) m β) :=
  it.scanWithPostcondition (PostconditionT.attachLift <| f · ·) acc

/--
If `it` is an iterator, then `it.scan f acc` is another iterator that applies a
function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

In situations where `f` is monadic, use `scanM` instead.

**Marble diagram:**

```text
it         ---a ---b ---c ---⊥
it.scan    -i -a'-ab'-abc'---⊥
```

(given that `f i a = a'`, `f a' b = ab'`, `f ab' c = abc'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline, expose]
def IterM.scan [Monad m] (f : γ → β → γ) (acc : γ) (it : IterM (α := α) m β) :=
  (it.scanWithPostcondition (pure <| f · ·) acc : IterM m γ)

end Std
