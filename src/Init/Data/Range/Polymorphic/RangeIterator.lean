/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Access
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Range.Polymorphic.PRange
public import Init.Data.List.Sublist

public section

/-!
# Range iterator

This module implements an iterator for ranges (`Std.PRange`).

This iterator is publicly available via `PRange.iter` after importing
`Std.Data.Iterators` and it internally powers many functions on ranges such as
`PRange.toList`.
-/

open Std.Iterators

namespace Std.PRange

/-- Internal state of the range iterators. Do not depend on its internals. -/
@[unbox]
structure RangeIterator (shape : BoundShape) (α : Type u) where
  next : Option α
  upperBound : Bound shape α

variable {α : Type u}

/--
The pure function mapping a range iterator of type `IterM` to the next step of the iterator.

This function is prefixed with `Monadic` in order to disambiguate it from the version for iterators
of type `Iter`.
-/
@[always_inline, inline]
def RangeIterator.Monadic.step {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    (it : IterM (α := RangeIterator su α) Id α) :
    IterStep (IterM (α := RangeIterator su α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
      .yield ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ a
    else
      .done

/--
The pure function mapping a range iterator of type `Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def RangeIterator.step {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    (it : Iter (α := RangeIterator su α) α) :
    IterStep (Iter (α := RangeIterator su α) α) α :=
  match it.internalState.next with
  | none => .done
  | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
      .yield ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ a
    else
      .done

theorem RangeIterator.step_eq_monadicStep {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} :
    RangeIterator.step it = (RangeIterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split
  · rfl
  · split <;> rfl

@[always_inline, inline]
instance {su} [UpwardEnumerable α] [SupportsUpperBound su α] :
    Iterator (RangeIterator su α) Id α where
  IsPlausibleStep it step := step = RangeIterator.Monadic.step it
  step it := pure ⟨RangeIterator.Monadic.step it, rfl⟩

theorem RangeIterator.Monadic.isPlausibleStep_iff {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = RangeIterator.Monadic.step it := by
  exact Iff.rfl

theorem RangeIterator.Monadic.step_eq_step {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} :
    it.step = pure ⟨RangeIterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [IterM.step, Iterator.step]

theorem RangeIterator.isPlausibleStep_iff {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} {step} :
    it.IsPlausibleStep step ↔ step = RangeIterator.step it := by
  simp only [Iter.IsPlausibleStep, Monadic.isPlausibleStep_iff, step_eq_monadicStep]
  constructor
  · intro h
    generalize hs : (step.mapIterator Iter.toIterM) = stepM at h
    cases h
    replace hs := congrArg (IterStep.mapIterator IterM.toIter) hs
    simpa using hs
  · rintro rfl
    simp only [IterStep.mapIterator_mapIterator, Iter.toIterM_comp_toIter, IterStep.mapIterator_id]

theorem RangeIterator.step_eq_step {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} :
    it.step = ⟨RangeIterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step, step_eq_monadicStep, Monadic.step_eq_step, IterM.Step.toPure]

instance RangeIterator.instIteratorCollect {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {n : Type u → Type w} [Monad n] : IteratorCollect (RangeIterator su α) Id n :=
  .defaultImplementation

instance RangeIterator.instIteratorCollectPartial {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    {n : Type u → Type w} [Monad n] : IteratorCollectPartial (RangeIterator su α) Id n :=
  .defaultImplementation

theorem RangeIterator.Monadic.isPlausibleOutput_next {su a}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} (h : it.internalState.next = some a)
    (hP : SupportsUpperBound.IsSatisfied it.internalState.upperBound a) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, RangeIterator.Monadic.step, h, hP]

theorem RangeIterator.Monadic.isPlausibleOutput_iff {su a}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a := by
  simp [IterM.IsPlausibleOutput, isPlausibleStep_iff, RangeIterator.Monadic.step]
  split
  · simp [*]
  · constructor
    · rintro ⟨it', hit'⟩
      split at hit' <;> simp_all
    · rename_i heq
      rintro ⟨heq', h'⟩
      simp only [heq', Option.some.injEq] at heq
      simp_all

theorem RangeIterator.isPlausibleOutput_next {su a}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} (h : it.internalState.next = some a)
    (hP : SupportsUpperBound.IsSatisfied it.internalState.upperBound a) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h, hP]

theorem RangeIterator.isPlausibleOutput_iff {su a}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem RangeIterator.Monadic.isPlausibleSuccessorOf_iff {su}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it' it : IterM (α := RangeIterator su α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp only [IterM.IsPlausibleSuccessorOf]
  constructor
  · rintro ⟨step, h, h'⟩
    cases h'
    simp only [RangeIterator.Monadic.step] at h
    split at h
    · cases h
    · split at h
      · simp only [IterStep.successor, Option.some.injEq] at h
        cases h
        exact ⟨_, ‹_›, ‹_›, rfl, rfl⟩
      · cases h
  · rintro ⟨a, h, hP, h'⟩
    refine ⟨.yield it' a, rfl, ?_⟩
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, step, h, hP, ↓reduceIte,
      IterStep.yield.injEq, and_true]
    simp [h'.1, ← h'.2]

theorem RangeIterator.isPlausibleSuccessorOf_iff {su}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it' it : Iter (α := RangeIterator su α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem RangeIterator.isSome_next_of_isPlausibleIndirectOutput {su}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} {out : α}
    (h : it.IsPlausibleIndirectOutput out) :
    it.internalState.next.isSome := by
  cases h
  case direct h =>
    rw [isPlausibleOutput_iff] at h
    simp [h]
  case indirect h _ =>
    rw [isPlausibleSuccessorOf_iff] at h
    obtain ⟨a, ha, _⟩ := h
    simp [ha]

private def List.Sublist.filter_mono {l : List α} {P Q : α → Bool} (h : ∀ a, P a → Q a) :
    List.Sublist (l.filter P) (l.filter Q) := by
  apply List.Sublist.trans (l₂ := (l.filter Q).filter P)
  · simp [Bool.and_eq_left_iff_imp.mpr (h _)]
  · apply List.filter_sublist

private def List.length_filter_strict_mono {l : List α} {P Q : α → Bool} {a : α}
    (h : ∀ a, P a → Q a) (ha : a ∈ l) (hPa : ¬ P a) (hQa : Q a) :
    (l.filter P).length < (l.filter Q).length := by
  have hsl : List.Sublist (l.filter P) (l.filter Q) := by
    apply List.Sublist.filter_mono
    exact h
  apply Nat.lt_of_le_of_ne
  · apply List.Sublist.length_le
    exact hsl
  · intro h
    apply hPa
    have heq := List.Sublist.eq_of_length hsl h
    have : a ∈ List.filter Q l := List.mem_filter.mpr ⟨ha, hQa⟩
    rw [← heq, List.mem_filter] at this
    exact this.2

private def RangeIterator.instFinitenessRelation [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] :
    FinitenessRelation (RangeIterator su α) Id where
  rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    match it with
    | ⟨⟨none, _⟩⟩ =>
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step] at hs₂
      simp [hs₂, IterStep.successor] at hs₁
    | ⟨⟨some init, bound⟩⟩ =>
      obtain ⟨n, hn⟩ := HasFiniteRanges.finite init bound
      induction n generalizing init with
      | zero =>
        simp [UpwardEnumerable.succMany?_zero] at hn
        constructor
        rintro it' ⟨step, hs₁, hs₂⟩
        simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step, hn] at hs₂
        simp [hs₂, IterStep.successor] at hs₁
      | succ n ih =>
        constructor
        rintro it' ⟨step, hs₁, hs₂⟩
        simp [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at hn
        match hs : UpwardEnumerable.succ? init with
        | none =>
          simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step, hs] at hs₂
          split at hs₂
          · rename_i h
            simp [hs₂, IterStep.successor] at hs₁
            cases hs₁
            constructor
            intro it' ⟨step, hs₁, hs₂⟩
            simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step] at hs₂
            simp [hs₂, IterStep.successor] at hs₁
          · simp [hs₂, IterStep.successor] at hs₁
        | some a =>
          simp [hs] at hn
          specialize ih _ hn
          simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step] at hs₂
          split at hs₂
          · simp [hs₂, IterStep.successor, hs] at hs₁
            cases hs₁
            exact ih
          · simp [hs₂, IterStep.successor] at hs₁
  subrelation := id

@[no_expose]
instance RangeIterator.instFinite {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] :
    Finite (RangeIterator su α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def RangeIterator.instProductivenessRelation [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] :
    ProductivenessRelation (RangeIterator su α) Id where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by
    exfalso
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep,
      Iterator.IsPlausibleStep, Monadic.step] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h

@[no_expose]
instance RangeIterator.instProductive {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] :
    Productive (RangeIterator su α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance RangeIterator.instIteratorAccess {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α] :
    IteratorAccess (RangeIterator su α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (UpwardEnumerable.succMany? n) with
    | none => .done
    | some next => if SupportsUpperBound.IsSatisfied it.internalState.upperBound next then
        .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
      else
        .done, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, UpwardEnumerable.succMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, UpwardEnumerable.succMany?_zero, Option.some.injEq] at heq
          cases heq
          split <;> rename_i heq''
          · apply IterM.IsPlausibleNthOutputStep.zero_yield
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', heq'']
          · apply IterM.IsPlausibleNthOutputStep.done
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', heq'']
      · rename_i n ih
        split <;> rename_i heq
        · cases heq' : it.internalState.next
          · apply IterM.IsPlausibleNthOutputStep.done
            simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq']
          · rename_i out
            simp only [heq', Option.bind_some, LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at heq
            specialize ih ⟨⟨UpwardEnumerable.succ? out, it.internalState.upperBound⟩⟩
            simp only [heq] at ih
            by_cases heq'' : SupportsUpperBound.IsSatisfied it.internalState.upperBound out
            · apply IterM.IsPlausibleNthOutputStep.yield
              · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq', heq'', ↓reduceIte,
                IterStep.yield.injEq]
                exact ⟨rfl, rfl⟩
              · exact ih
            · apply IterM.IsPlausibleNthOutputStep.done
              simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', heq'']
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          rename_i out
          simp only [heq', Option.bind_some] at heq
          have hle : UpwardEnumerable.LE out _ := ⟨n + 1, heq⟩
          simp only [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at heq
          specialize ih ⟨⟨UpwardEnumerable.succ? out, it.internalState.upperBound⟩⟩
          simp only [heq] at ih
          by_cases hout : SupportsUpperBound.IsSatisfied it.internalState.upperBound out
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout, ↓reduceIte,
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih
          · have := hout.imp (fun h => LawfulUpwardEnumerableUpperBound.isSatisfied_of_le _ _ _ h hle)
            simp only [this, ↓reduceIte]
            simp only [this, ↓reduceIte] at ih
            apply IterM.IsPlausibleNthOutputStep.done
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout])⟩

instance RangeIterator.instLawfulDeterministicIterator {su} [UpwardEnumerable α] [SupportsUpperBound su α] :
    LawfulDeterministicIterator (RangeIterator su α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem RangeIterator.Monadic.isPlausibleIndirectOutput_iff {su α}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (UpwardEnumerable.succMany? n ·) = some out ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [RangeIterator.Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulUpwardEnumerable.succMany?_zero]⟩
    case indirect h _ ih =>
      rw [RangeIterator.Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [RangeIterator.Monadic.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulUpwardEnumerable.succMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hle : UpwardEnumerable.LE a out := ⟨_, hn⟩
      rw [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at hn
      cases hn' : UpwardEnumerable.succ? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨some a', it.internalState.upperBound⟩) hn hu
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [RangeIterator.Monadic.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      apply LawfulUpwardEnumerableUpperBound.isSatisfied_of_le _ a out
      · exact hu
      · exact hle

theorem RangeIterator.isPlausibleIndirectOutput_iff {su α}
    [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (UpwardEnumerable.succMany? n ·) = some out ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound out := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/-!
## Efficient `IteratorLoop` instance
As long as the compiler cannot optimize away the `Option` in the internal state, we use a special
loop implementation.
-/

@[always_inline, inline]
instance RangeIterator.instIteratorLoop {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (RangeIterator su α) Id n where
  forIn _ γ Pl wf it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      if hu : SupportsUpperBound.IsSatisfied upperBound next then
        loop γ Pl wf upperBound next init (fun a ha₁ ha₂ c => f a ?hf c) next ?hle hu
      else
        return init
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[specialize]
    loop γ Pl wf (upperBound : Bound su α) least acc
        (f : (out : α) → UpwardEnumerable.LE least out → SupportsUpperBound.IsSatisfied upperBound out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s)))
        (next : α) (hl : UpwardEnumerable.LE least next) (hu : SupportsUpperBound.IsSatisfied upperBound next) : n γ := do
      match ← f next hl hu acc with
      | ⟨.yield acc', _⟩ =>
        match hs : UpwardEnumerable.succ? next with
        | some next' =>
          if hu : SupportsUpperBound.IsSatisfied upperBound next' then
            loop γ Pl wf upperBound least acc' f next' ?hle' hu
          else
            return acc'
        | none => return acc'
      | ⟨.done acc', _⟩ => return acc'
    termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
    decreasing_by
      simp [IteratorLoop.rel, RangeIterator.Monadic.isPlausibleStep_iff,
        RangeIterator.Monadic.step, *]
  finally
    case hf =>
      rw [RangeIterator.Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [UpwardEnumerable.succMany?_one, hs]

partial instance RepeatIterator.instIteratorLoopPartial {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {n : Type u → Type w} [Monad n] : IteratorLoopPartial (RangeIterator su α) Id n where
  forInPartial _ γ it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      if hu : SupportsUpperBound.IsSatisfied upperBound next then
        loop γ upperBound next init (fun a ha₁ ha₂ c => f a ?hf c) next ?hle hu
      else
        return init
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[specialize]
    loop γ (upperBound : Bound su α) least acc
        (f : (out : α) → UpwardEnumerable.LE least out → SupportsUpperBound.IsSatisfied upperBound out → (c : γ) → n (ForInStep γ))
        (next : α) (hl : UpwardEnumerable.LE least next) (hu : SupportsUpperBound.IsSatisfied upperBound next) : n γ := do
      match ← f next hl hu acc with
      | .yield acc' =>
        match hs : UpwardEnumerable.succ? next with
        | some next' =>
          if hu : SupportsUpperBound.IsSatisfied upperBound next' then
            loop γ upperBound least acc' f next' ?hle' hu
          else
            return acc'
        | none => return acc'
      | .done acc' => return acc'
  finally
    case hf =>
      rw [RangeIterator.Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [UpwardEnumerable.succMany?_one, hs]

theorem RangeIterator.instIteratorLoop.loop_eq {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] {γ : Type u}
    {lift} [Internal.LawfulMonadLiftBindFunction lift]
    {PlausibleForInStep} {upperBound} {next} {hl} {hu} {f} {acc} {wf} :
    loop (α := α) (su := su) (n := n) γ PlausibleForInStep wf upperBound least acc f next hl hu =
      (do
        match ← f next hl hu acc with
        | ⟨.yield c, _⟩ =>
          letI it' : IterM (α := RangeIterator su α) Id α := ⟨⟨UpwardEnumerable.succ? next, upperBound⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) lift γ
            PlausibleForInStep wf it' c it'.IsPlausibleIndirectOutput (fun _ => id)
            (fun b h c => f b
                (by
                  refine UpwardEnumerable.le_trans hl ?_
                  simp only [RangeIterator.Monadic.isPlausibleIndirectOutput_iff, it',
                    ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at h
                  exact ⟨h.choose + 1, h.choose_spec.1⟩)
                (by simp only [RangeIterator.Monadic.isPlausibleIndirectOutput_iff, it'] at h; exact h.choose_spec.2) c)
        | ⟨.done c, _⟩ => return c) := by
  rw [loop]
  apply bind_congr
  intro step
  split
  · split
    · split
      · simp only [*]
        rw [IterM.DefaultConsumers.forIn']
        simp only [Monadic.step_eq_step, Monadic.step, ↓reduceIte, *,
          Internal.LawfulMonadLiftBindFunction.liftBind_pure]
        rw [loop_eq (lift := lift)]
        apply bind_congr
        intro step
        split
        · apply IterM.DefaultConsumers.forIn'_eq_forIn'
          intros; rfl
        · simp
      · simp only [*]
        rw [IterM.DefaultConsumers.forIn']
        simp [Monadic.step_eq_step, Monadic.step, *,
          Internal.LawfulMonadLiftBindFunction.liftBind_pure]
    · simp only [*]
      rw [IterM.DefaultConsumers.forIn']
      simp [Monadic.step_eq_step, Monadic.step, Internal.LawfulMonadLiftBindFunction.liftBind_pure]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
decreasing_by
      simp [IteratorLoop.rel, RangeIterator.Monadic.isPlausibleStep_iff,
        RangeIterator.Monadic.step, *]

instance RangeIterator.instLawfulIteratorLoop {su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableUpperBound su α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (RangeIterator su α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction
    ext γ PlausibleForInStep hwf it init f
    simp only [IteratorLoop.forIn, IteratorLoop.defaultImplementation]
    rw [IterM.DefaultConsumers.forIn']
    simp only [RangeIterator.Monadic.step_eq_step, RangeIterator.Monadic.step]
    simp only [Internal.LawfulMonadLiftBindFunction.liftBind_pure]
    split
    · rename_i it f next upperBound f'
      simp
      split
      · simp only
        rw [instIteratorLoop.loop_eq (lift := lift)]
        apply bind_congr
        intro step
        split
        · apply IterM.DefaultConsumers.forIn'_eq_forIn'
          intro b c hPb hQb
          congr
        · simp
      · simp
    · simp

end Std.PRange.IteratorLoop
