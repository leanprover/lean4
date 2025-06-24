module

prelude
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Internal.Termination
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Loop

namespace Std.Iterators

class LawfulIteratorMembership (α : Type w) (m : Type w → Type w') {β : Type w}
    [Iterator α m β] [Membership β (IterM (α := α) m β)] : Prop where
  mem_iff_isPlausibleIndirectOutput {it : IterM (α := α) m β} {out : β} :
    x ∈ it ↔ it.IsPlausibleIndirectOutput out

namespace Types

@[unbox]
structure Attach {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) where
  inner : IterM (α := α) m β
  is_descendant : inner.IsPlausibleIndirectSuccessorOf it

@[always_inline, inline]
def Attach.modifyStep {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    {baseIt : IterM (α := α) m β} (it : IterM (α := Attach baseIt) m { out : β // out ∈ baseIt })
    (step : it.internalState.inner.Step) :
    IterStep (IterM (α := Attach baseIt) m { out : β // out ∈ baseIt }) { out : β // out ∈ baseIt } :=
  match step with
  | .yield it' out h =>
    .yield ⟨it', .trans (.single ⟨_, rfl, h⟩) it.internalState.is_descendant⟩
      ⟨out, LawfulIteratorMembership.mem_iff_isPlausibleIndirectOutput.mpr (.trans it.internalState.is_descendant (.direct ⟨_, h⟩))⟩
  | .skip it' h =>
    .skip ⟨it', .trans (.single ⟨_, rfl, h⟩) it.internalState.is_descendant⟩
  | .done _ => .done

instance Attach.instIterator {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    {it : IterM (α := α) m β} :
    Iterator (Attach it) m { out : β // out ∈ it } where
  IsPlausibleStep it step := ∃ step', modifyStep it step' = step
  step it := (fun step => ⟨modifyStep it step, step, rfl⟩) <$> it.internalState.inner.step

def Attach.instFinitenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    [Finite α m] {it : IterM (α := α) m β} : FinitenessRelation (Attach it) m where
  rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySteps
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    obtain ⟨_, hs, step, h', rfl⟩ := h
    cases step using PlausibleIterStep.casesOn
    · simp only [IterStep.successor, modifyStep, Option.some.injEq] at hs
      simp only [← hs]
      exact ⟨_, rfl, ‹_›⟩
    · simp only [IterStep.successor, modifyStep, Option.some.injEq] at hs
      simp only [← hs]
      exact ⟨_, rfl, ‹_›⟩
    · simp [IterStep.successor, modifyStep, reduceCtorEq] at hs

instance Attach.instFinite {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    [Finite α m] {it : IterM (α := α) m β} : Finite (Attach it) m :=
  .of_finitenessRelation instFinitenessRelation

def Attach.instProductivenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    [Productive α m] {it : IterM (α := α) m β} : ProductivenessRelation (Attach it) m where
  rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySkips
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    simp_wf
    obtain ⟨step, hs⟩ := h
    cases step using PlausibleIterStep.casesOn
    · simp [IterStep.successor, modifyStep] at hs
    · simp only [modifyStep, IterStep.skip.injEq] at hs
      simp only [← hs]
      assumption
    · simp [modifyStep] at hs

instance Attach.instProductive {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    [Productive α m] {it : IterM (α := α) m β} : Productive (Attach it) m :=
  .of_productivenessRelation instProductivenessRelation

instance Attach.instIteratorCollect {α β : Type w} {m : Type w → Type w'} [Monad m] [Monad n]
    {it : IterM (α := α) m β} [Iterator α m β] [Membership β (IterM (α := α) m β)]
    [LawfulIteratorMembership α m] :
    IteratorCollect (Attach it) m n :=
  .defaultImplementation

instance Attach.instIteratorCollectPartial {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Monad n] {it : IterM (α := α) m β} [Iterator α m β] [Membership β (IterM (α := α) m β)]
    [LawfulIteratorMembership α m] :
    IteratorCollectPartial (Attach it) m n :=
  .defaultImplementation

instance Attach.instIteratorLoop {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Monad n] {it : IterM (α := α) m β} [Iterator α m β] [Membership β (IterM (α := α) m β)]
    [LawfulIteratorMembership α m] [MonadLiftT m n] :
    IteratorLoop (Attach it) m n :=
  .defaultImplementation

instance Attach.instIteratorLoopPartial {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Monad n] {it : IterM (α := α) m β} [Iterator α m β] [Membership β (IterM (α := α) m β)]
    [LawfulIteratorMembership α m] [MonadLiftT m n] :
    IteratorLoopPartial (Attach it) m n :=
  .defaultImplementation

instance {α β : Type w} {m : Type w → Type w'} [Monad m]
    {it : IterM (α := α) m β} [Iterator α m β] [Membership β (IterM (α := α) m β)]
    [LawfulIteratorMembership α m] [IteratorSize α m] :
    IteratorSize (Attach it) m where
  size it := IteratorSize.size it.internalState.inner

instance {α β : Type w} {m : Type w → Type w'} [Monad m]
    {it : IterM (α := α) m β} [Iterator α m β] [Membership β (IterM (α := α) m β)]
    [LawfulIteratorMembership α m] [IteratorSizePartial α m] :
    IteratorSizePartial (Attach it) m where
  size it := IteratorSizePartial.size it.internalState.inner

end Types

@[always_inline, inline]
def IterM.attach {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Membership β (IterM (α := α) m β)] [LawfulIteratorMembership α m]
    (it : IterM (α := α) m β) : IterM (α := Types.Attach it) m { out : β // out ∈ it } :=
  ⟨⟨it, .refl it⟩⟩

end Std.Iterators
