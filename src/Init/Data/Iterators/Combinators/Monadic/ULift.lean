/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Monadic

public section

namespace Std.Iterators

universe v u v' u'

section ULiftT

/-- `ULiftT.{v, u}` shrinks a monad on `Type max u v` to a monad on `Type u`. -/
def ULiftT (n : Type max u v → Type v') (α : Type u) := n (ULift.{v} α)

/-- Returns the underlying `n`-monadic representation of a `ULiftT n α` value. -/
@[always_inline, inline]
def ULiftT.run {n : Type max u v → Type v'} {α : Type u} (x : ULiftT n α) : n (ULift.{v} α) :=
  x

@[no_expose]
instance {n : Type max u v → Type v'} [Monad n] : Monad.{u} (ULiftT n) where
  pure a := pure (f := n) (ULift.up a)
  bind x f := bind (m := n) (x : n _) fun a => f a.down

@[no_expose]
instance {n : Type max u v → Type v'} [Monad n] [LawfulMonad n] : LawfulMonad.{u} (ULiftT n) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map := by simp [Functor.map]
  seqLeft_eq := by simp [Seq.seq, SeqLeft.seqLeft, Functor.map]
  seqRight_eq := by simp [Seq.seq, SeqRight.seqRight, Functor.map]
  pure_seq := by simp [Seq.seq, Pure.pure, Functor.map]
  bind_pure_comp := by simp [Bind.bind, Pure.pure, Functor.map]
  bind_map := by simp [Bind.bind, Functor.map, Seq.seq]
  pure_bind := by simp [Bind.bind, Pure.pure]
  bind_assoc := by simp [Bind.bind]

@[simp]
theorem ULiftT.run_pure {n : Type max u v → Type v'} [Monad n] {α : Type u} {a : α} :
    (pure a : ULiftT n α).run = pure (f := n) (ULift.up a) :=
  (rfl)

@[simp]
theorem ULiftT.run_bind {n : Type max u v → Type v'} [Monad n] {α β : Type u}
    {x : ULiftT n α} {f : α → ULiftT n β} :
    (x >>= f).run = x.run >>= (fun a => (f a.down).run) :=
  (rfl)

@[simp]
theorem ULiftT.run_map {n : Type max u v → Type v'} [Monad n] {α β : Type u}
    {x : ULiftT n α} {f : α → β} :
    (f <$> x).run = x.run >>= (fun a => pure <| .up (f a.down)) :=
  (rfl)

end ULiftT

/-- Internal state of the `uLift` iterator combinator. Do not depend on its internals. -/
@[unbox]
structure Types.ULiftIterator (α : Type u) (m : Type u → Type u') (n : Type max u v → Type v')
    (β : Type u) (lift : ∀ ⦃γ : Type u⦄, m γ → ULiftT n γ) : Type max u v where
  inner : IterM (α := α) m β

variable {α : Type u} {m : Type u → Type u'} {n : Type max u v → Type v'}
    {β : Type u} {lift : ∀ ⦃γ : Type u⦄, m γ → ULiftT n γ}

/--
Transforms a step of the base iterator into a step of the `uLift` iterator.
-/
@[always_inline, inline]
def Types.ULiftIterator.Monadic.modifyStep (step : IterStep (IterM (α := α) m β) β) :
    IterStep (IterM (α := ULiftIterator.{v} α m n β lift) n (ULift.{v} β)) (ULift.{v} β) :=
  match step with
  | .yield it' out => .yield ⟨⟨it'⟩⟩ (.up out)
  | .skip it' => .skip ⟨⟨it'⟩⟩
  | .done => .done

instance Types.ULiftIterator.instIterator [Iterator α m β] [Monad n] :
    Iterator (ULiftIterator α m n β lift) n (ULift β) where
  IsPlausibleStep it step :=
    ∃ step', it.internalState.inner.IsPlausibleStep step' ∧
      step = ULiftIterator.Monadic.modifyStep step'
  step it := do
    let step := (← (lift it.internalState.inner.step).run).down
    return ⟨Monadic.modifyStep step.val, ?hp⟩
  where finally
    case hp => exact ⟨step.val, step.property, rfl⟩

def Types.ULiftIterator.instFinitenessRelation [Iterator α m β] [Finite α m] [Monad n] :
    FinitenessRelation (ULiftIterator α m n β lift) n where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySteps)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by
    rcases h with ⟨_, hs, step, hp, rfl⟩
    cases step <;> cases hs
    · apply IterM.TerminationMeasures.Finite.rel_of_yield
      exact hp
    · apply IterM.TerminationMeasures.Finite.rel_of_skip
      exact hp

instance Types.ULiftIterator.instFinite [Iterator α m β] [Finite α m] [Monad n] :
    Finite (ULiftIterator α m n β lift) n :=
  .of_finitenessRelation instFinitenessRelation

def Types.ULiftIterator.instProductivenessRelation [Iterator α m β] [Productive α m] [Monad n] :
    ProductivenessRelation (ULiftIterator α m n β lift) n where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySkips)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := by
    rcases h with ⟨step, hp, hs⟩
    cases step <;> cases hs
    apply IterM.TerminationMeasures.Productive.rel_of_skip
    exact hp

instance Types.ULiftIterator.instProductive [Iterator α m β] [Productive α m] [Monad n] :
    Productive (ULiftIterator α m n β lift) n :=
  .of_productivenessRelation instProductivenessRelation

instance Types.ULiftIterator.instIteratorLoop {o} [Monad n] [Monad o] [Iterator α m β] :
    IteratorLoop (ULiftIterator α m n β lift) n o :=
  .defaultImplementation

instance Types.ULiftIterator.instIteratorLoopPartial {o} [Monad n] [Monad o] [Iterator α m β] :
    IteratorLoopPartial (ULiftIterator α m n β lift) n o :=
  .defaultImplementation

instance Types.ULiftIterator.instIteratorCollect {o} [Monad n] [Monad o] [Iterator α m β] :
    IteratorCollect (ULiftIterator α m n β lift) n o :=
  .defaultImplementation

instance Types.ULiftIterator.instIteratorCollectPartial {o} [Monad n] [Monad o] [Iterator α m β] :
    IteratorCollectPartial (ULiftIterator α m n β lift) n o :=
  .defaultImplementation

instance Types.ULiftIterator.instIteratorSize [Monad n] [Iterator α m β] [IteratorSize α m]
    [Finite (ULiftIterator α m n β lift) n] :
    IteratorSize (ULiftIterator α m n β lift) n :=
  .defaultImplementation

instance Types.ULiftIterator.instIteratorSizePartial [Monad n] [Iterator α m β] [IteratorSize α m] :
    IteratorSizePartial (ULiftIterator α m n β lift) n :=
  .defaultImplementation

/--
Transforms an `m`-monadic iterator with values in `β` into an `n`-monadic iterator with
values in `ULift β`. Requires a `MonadLift m (ULiftT n)` instance.

**Marble diagram:**

```
it            ---a    ----b    ---c    --d    ---⊥
it.uLift n    ---.up a----.up b---.up c--.up d---⊥
```

**Termination properties:**

* `Finite`: only if the original iterator is finite
* `Productive`: only if the original iterator is productive
-/
@[always_inline, inline, expose]
def IterM.uLift (it : IterM (α := α) m β) (n : Type max u v → Type v')
    [lift : MonadLiftT m (ULiftT n)] :
    IterM (α := Types.ULiftIterator α m n β (fun _ => lift.monadLift)) n (ULift β) :=
  ⟨⟨it⟩⟩

end Std.Iterators
