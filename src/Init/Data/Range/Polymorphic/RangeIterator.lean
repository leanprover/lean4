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

set_option doc.verso true

public section

/-!
# Range iterator

This module implements an iterator for ranges (such as {name}`Std.Rcc`).

This iterator is publicly available via
{name (scope := "Std.Data.Iterators.Producers.Range")}`Std.Rcc.iter` (and identically named
functions in the sibling namespaces) after importing {lit}`Std.Data.Iterators`.

It powers many functions on ranges internally, such as
{name (scope := "Init.Data.Range.Polymorphic.Iterators")}`Rcc.toList`.
-/

open Std.Iterators

namespace Std
open PRange

namespace Rxc

variable {α : Type u} {lo hi a : α}

/-- Internal state of the range iterators. Do not depend on its internals. -/
@[unbox]
protected structure Iterator (α : Type u) where
  next : Option α
  upperBound : α

/--
The pure function mapping a range iterator of type {name}`IterM` to the next step of the iterator.

This function is prefixed with {lit}`Monadic` in order to disambiguate it from the version for
iterators of type {name}`Iter`.
-/
@[inline]
def Iterator.Monadic.step [UpwardEnumerable α] [LE α] [DecidableLE α]
    (it : IterM (α := Rxc.Iterator α) Id α) :
    IterStep (IterM (α := Rxc.Iterator α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some next =>
    if next ≤ it.internalState.upperBound then
      .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
    else
      .done

/--
The pure function mapping a range iterator of type {name}`Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def Iterator.step [UpwardEnumerable α] [LE α] [DecidableLE α]
    (it : Iter (α := Rxc.Iterator α) α) :
    IterStep (Iter (α := Rxc.Iterator α) α) α :=
  match it.internalState.next with
  | none => .done
  | some next => if next ≤ it.internalState.upperBound then
      .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
    else
      .done

theorem Iterator.step_eq_monadicStep [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    Iterator.step it = (Iterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split
  · rfl
  · split <;> rfl

@[always_inline, inline]
instance [UpwardEnumerable α] [LE α] [DecidableLE α] :
    Iterator (Rxc.Iterator α) Id α where
  IsPlausibleStep it step := step = Iterator.Monadic.step it
  step it := pure <| .deflate <| ⟨Iterator.Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleStep_iff [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rxc.Iterator α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.Monadic.step it := by
  exact Iff.rfl

theorem Iterator.Monadic.step_eq_step [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rxc.Iterator α) Id α} :
    it.step = pure (.deflate ⟨Iterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩) := by
  simp [IterM.step, Iterators.Iterator.step]

theorem Iterator.isPlausibleStep_iff [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rxc.Iterator α) α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.step it := by
  simp only [Iter.IsPlausibleStep, Monadic.isPlausibleStep_iff, step_eq_monadicStep]
  constructor
  · intro h
    generalize hs : (step.mapIterator Iter.toIterM) = stepM at h
    cases h
    replace hs := congrArg (IterStep.mapIterator IterM.toIter) hs
    simpa using hs
  · rintro rfl
    simp only [IterStep.mapIterator_mapIterator, Iter.toIterM_comp_toIter, IterStep.mapIterator_id]

theorem Iterator.step_eq_step [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    it.step = ⟨Iterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step, step_eq_monadicStep, Monadic.step_eq_step, IterM.Step.toPure]

instance Iterator.instIteratorCollect [UpwardEnumerable α] [LE α] [DecidableLE α]
    {n : Type u → Type w} [Monad n] : IteratorCollect (Rxc.Iterator α) Id n :=
  .defaultImplementation

instance Iterator.instIteratorCollectPartial [UpwardEnumerable α] [LE α] [DecidableLE α]
    {n : Type u → Type w} [Monad n] : IteratorCollectPartial (Rxc.Iterator α) Id n :=
  .defaultImplementation

theorem Iterator.Monadic.isPlausibleOutput_next {a}
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rxc.Iterator α) Id α} (h : it.internalState.next = some a)
    (hP : a ≤ it.internalState.upperBound) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, Monadic.step, h, hP]

theorem Iterator.Monadic.isPlausibleOutput_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rxc.Iterator α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        a ≤ it.internalState.upperBound := by
  simp [IterM.IsPlausibleOutput, isPlausibleStep_iff, Monadic.step]
  split
  · simp [*]
  · constructor
    · rintro ⟨it', hit'⟩
      split at hit' <;> simp_all
    · rename_i heq
      rintro ⟨heq', h'⟩
      simp only [heq', Option.some.injEq] at heq
      simp_all

theorem Iterator.isPlausibleOutput_next
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rxc.Iterator α) α} (h : it.internalState.next = some a)
    (hP : a ≤ it.internalState.upperBound) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h, hP]

theorem Iterator.isPlausibleOutput_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        a ≤ it.internalState.upperBound := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem Iterator.Monadic.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it' it : IterM (α := Rxc.Iterator α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        a ≤ it.internalState.upperBound ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp only [IterM.IsPlausibleSuccessorOf]
  constructor
  · rintro ⟨step, h, h'⟩
    cases h'
    simp only [Monadic.step] at h
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

theorem Iterator.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it' it : Iter (α := Rxc.Iterator α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        a ≤ it.internalState.upperBound ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem Iterator.isSome_next_of_isPlausibleIndirectOutput
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rxc.Iterator α) α} {out : α} (h : it.IsPlausibleIndirectOutput out) :
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

private def Iterator.instFinitenessRelation [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] :
    FinitenessRelation (Rxc.Iterator α) Id where
  rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    have hnone : ∀ bound, Acc (fun it' it : IterM (α := Rxc.Iterator α) Id α => it'.IsPlausibleSuccessorOf it)
        ⟨⟨none, bound⟩⟩ := by
      intro bound
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step] at hs₂
      simp [hs₂, IterStep.successor] at hs₁
    simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      Monadic.step, exists_eq_right] at hnone ⊢
    match it with
    | ⟨⟨none, _⟩⟩ => apply hnone
    | ⟨⟨some init, bound⟩⟩ =>
      obtain ⟨n, hn⟩ := Rxc.IsAlwaysFinite.finite init bound
      induction n generalizing init with
      | zero =>
        simp only [succMany?_zero, Option.elim_some] at hn
        constructor
        simp [hn, IterStep.successor]
      | succ n ih =>
        constructor
        rintro it'
        simp only [succMany?_add_one_eq_succ?_bind_succMany?] at hn
        match hs : succ? init with
        | none =>
          simp only [hs]
          intro h
          split at h
          · cases h
            apply hnone
          · cases h
        | some a =>
          intro h
          simp only [hs] at h hn
          specialize ih _ hn
          split at h
          · cases h
            exact ih
          · cases h
  subrelation := id

@[no_expose]
instance Iterator.instFinite [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [Rxc.IsAlwaysFinite α] :
    Finite (Rxc.Iterator α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def Iterator.instProductivenessRelation [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] :
    ProductivenessRelation (Rxc.Iterator α) Id where
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
instance Iterator.instProductive [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] :
    Productive (Rxc.Iterator α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance Iterator.instIteratorAccess [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] :
    IteratorAccess (Rxc.Iterator α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (UpwardEnumerable.succMany? n) with
    | none => .done
    | some next => if next ≤ it.internalState.upperBound then
        .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
      else
        .done, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, succMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, succMany?_zero, Option.some.injEq] at heq
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
            simp only [heq', Option.bind_some, succMany?_add_one_eq_succ?_bind_succMany?] at heq
            specialize ih ⟨⟨UpwardEnumerable.succ? out, it.internalState.upperBound⟩⟩
            simp only [heq] at ih
            by_cases heq'' : out ≤ it.internalState.upperBound
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
          simp only [succMany?_add_one_eq_succ?_bind_succMany?] at heq
          specialize ih ⟨⟨UpwardEnumerable.succ? out, it.internalState.upperBound⟩⟩
          simp only [heq] at ih
          by_cases hout : out ≤ it.internalState.upperBound
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout, ↓reduceIte,
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih
          · rename_i next
            haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
            have := hout.imp (fun h : next ≤ it.internalState.upperBound => by
              rw [← UpwardEnumerable.le_iff] at hle
              exact Trans.trans hle h)
            simp only [this, ↓reduceIte]
            simp only [this, ↓reduceIte] at ih
            apply IterM.IsPlausibleNthOutputStep.done
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout])⟩

instance Iterator.instLawfulDeterministicIterator [UpwardEnumerable α] [LE α] [DecidableLE α] :
    LawfulDeterministicIterator (Rxc.Iterator α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerable α]
    {it : IterM (α := Rxc.Iterator α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (succMany? n ·) = some out ∧
        out ≤ it.internalState.upperBound := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulUpwardEnumerable.succMany?_zero]⟩
    case indirect h _ ih =>
      rw [Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, succMany?_add_one_eq_succ?_bind_succMany?, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [Monadic.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulUpwardEnumerable.succMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hle : UpwardEnumerable.LE a out := ⟨_, hn⟩
      rw [succMany?_add_one_eq_succ?_bind_succMany?] at hn
      cases hn' : succ? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨some a', it.internalState.upperBound⟩) hn hu
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Monadic.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
      exact Trans.trans (α := α) (r := (· ≤ ·)) (UpwardEnumerable.le_iff.mpr hle) hu

theorem Iterator.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {it : Iter (α := Rxc.Iterator α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (succMany? n ·) = some out ∧
        out ≤ it.internalState.upperBound := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
@[always_inline, inline]
instance Iterator.instIteratorLoop [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (Rxc.Iterator α) Id n where
  forIn _ γ Pl wf it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      if hu : next ≤ upperBound then
        loop γ Pl wf upperBound next init (fun a ha₁ ha₂ c => f a ?hf c) next ?hle hu
      else
        return init
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[specialize]
    loop γ Pl wf (upperBound : α) least acc
        (f : (out : α) → UpwardEnumerable.LE least out → out ≤ upperBound → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s)))
        (next : α) (hl : UpwardEnumerable.LE least next) (hu : next ≤ upperBound) : n γ := do
      match ← f next hl hu acc with
      | ⟨.yield acc', _⟩ =>
        match hs : UpwardEnumerable.succ? next with
        | some next' =>
          if hu : next' ≤ upperBound then
            loop γ Pl wf upperBound least acc' f next' ?hle' hu
          else
            return acc'
        | none => return acc'
      | ⟨.done acc', _⟩ => return acc'
    termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
    decreasing_by
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff,
        Monadic.step, *]
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [succMany?_one, hs]

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
partial instance Iterator.instIteratorLoopPartial [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] : IteratorLoopPartial (Rxc.Iterator α) Id n where
  forInPartial _ γ it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      if hu : next ≤ upperBound then
        loop γ upperBound next init (fun a ha₁ ha₂ c => f a ?hf c) next ?hle hu
      else
        return init
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[specialize]
    loop γ (upperBound : α) least acc
        (f : (out : α) → UpwardEnumerable.LE least out → out ≤ upperBound → (c : γ) → n (ForInStep γ))
        (next : α) (hl : UpwardEnumerable.LE least next) (hu : next ≤ upperBound) : n γ := do
      match ← f next hl hu acc with
      | .yield acc' =>
        match hs : succ? next with
        | some next' =>
          if hu : next' ≤ upperBound then
            loop γ upperBound least acc' f next' ?hle' hu
          else
            return acc'
        | none => return acc'
      | .done acc' => return acc'
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [succMany?_one, hs]

theorem Iterator.instIteratorLoop.loop_eq [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] {γ : Type u}
    {lift} [Internal.LawfulMonadLiftBindFunction lift]
    {PlausibleForInStep} {upperBound} {next} {hl} {hu} {f} {acc} {wf} :
    loop (α := α) (n := n) γ PlausibleForInStep wf upperBound least acc f next hl hu =
      (do
        match ← f next hl hu acc with
        | ⟨.yield c, _⟩ =>
          letI it' : IterM (α := Rxc.Iterator α) Id α := ⟨⟨succ? next, upperBound⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) lift γ
            PlausibleForInStep wf it' c it'.IsPlausibleIndirectOutput (fun _ => id)
            (fun b h c => f b
                (by
                  refine UpwardEnumerable.le_trans hl ?_
                  simp only [Monadic.isPlausibleIndirectOutput_iff, it',
                    ← succMany?_add_one_eq_succ?_bind_succMany?] at h
                  exact ⟨h.choose + 1, h.choose_spec.1⟩)
                (by
                  simp only [Monadic.isPlausibleIndirectOutput_iff, it'] at h
                  exact h.choose_spec.2) c)
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
        rw [loop_eq (lift := lift), Shrink.inflate_deflate]
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
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulIteratorLoop [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (Rxc.Iterator α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction
    ext γ PlausibleForInStep hwf it init f
    simp only [IteratorLoop.forIn, IteratorLoop.defaultImplementation]
    rw [IterM.DefaultConsumers.forIn']
    simp only [Monadic.step_eq_step, Monadic.step]
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

end IteratorLoop

end Rxc

namespace Rxo

variable {α : Type u} {lo hi a : α}

/-- Internal state of the range iterators. Do not depend on its internals. -/
@[unbox]
protected structure Iterator (α : Type u) where
  next : Option α
  upperBound : α

/--
The pure function mapping a range iterator of type {name}`IterM` to the next step of the iterator.

This function is prefixed with {lit}`Monadic` in order to disambiguate it from the version for iterators
of type {name}`Iter`.
-/
@[inline]
def Iterator.Monadic.step [UpwardEnumerable α] [LT α] [DecidableLT α]
    (it : IterM (α := Rxo.Iterator α) Id α) :
    IterStep (IterM (α := Rxo.Iterator α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some next =>
    if next < it.internalState.upperBound then
      .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
    else
      .done

/--
The pure function mapping a range iterator of type {name}`Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def Iterator.step [UpwardEnumerable α] [LT α] [DecidableLT α]
    (it : Iter (α := Rxo.Iterator α) α) :
    IterStep (Iter (α := Rxo.Iterator α) α) α :=
  match it.internalState.next with
  | none => .done
  | some next => if next < it.internalState.upperBound then
      .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
    else
      .done

theorem Iterator.step_eq_monadicStep [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rxo.Iterator α) α} :
    Iterator.step it = (Iterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split
  · rfl
  · split <;> rfl

@[always_inline, inline]
instance [UpwardEnumerable α] [LT α] [DecidableLT α] :
    Iterator (Rxo.Iterator α) Id α where
  IsPlausibleStep it step := step = Iterator.Monadic.step it
  step it := pure (.deflate ⟨Iterator.Monadic.step it, rfl⟩)

theorem Iterator.Monadic.isPlausibleStep_iff [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rxo.Iterator α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.Monadic.step it := by
  exact Iff.rfl

theorem Iterator.Monadic.step_eq_step [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rxo.Iterator α) Id α} :
    it.step = pure (.deflate ⟨Iterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩) := by
  simp [IterM.step, Iterators.Iterator.step]

theorem Iterator.isPlausibleStep_iff [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rxo.Iterator α) α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.step it := by
  simp only [Iter.IsPlausibleStep, Monadic.isPlausibleStep_iff, step_eq_monadicStep]
  constructor
  · intro h
    generalize hs : (step.mapIterator Iter.toIterM) = stepM at h
    cases h
    replace hs := congrArg (IterStep.mapIterator IterM.toIter) hs
    simpa using hs
  · rintro rfl
    simp only [IterStep.mapIterator_mapIterator, Iter.toIterM_comp_toIter, IterStep.mapIterator_id]

theorem Iterator.step_eq_step [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rxo.Iterator α) α} :
    it.step = ⟨Iterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step, step_eq_monadicStep, Monadic.step_eq_step, IterM.Step.toPure]

instance Iterator.instIteratorCollect [UpwardEnumerable α] [LT α] [DecidableLT α]
    {n : Type u → Type w} [Monad n] : IteratorCollect (Rxo.Iterator α) Id n :=
  .defaultImplementation

instance Iterator.instIteratorCollectPartial [UpwardEnumerable α] [LT α] [DecidableLT α]
    {n : Type u → Type w} [Monad n] : IteratorCollectPartial (Rxo.Iterator α) Id n :=
  .defaultImplementation

theorem Iterator.Monadic.isPlausibleOutput_next {a}
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rxo.Iterator α) Id α} (h : it.internalState.next = some a)
    (hP : a < it.internalState.upperBound) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, Monadic.step, h, hP]

theorem Iterator.Monadic.isPlausibleOutput_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rxo.Iterator α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        a < it.internalState.upperBound := by
  simp [IterM.IsPlausibleOutput, isPlausibleStep_iff, Monadic.step]
  split
  · simp [*]
  · constructor
    · rintro ⟨it', hit'⟩
      split at hit' <;> simp_all
    · rename_i heq
      rintro ⟨heq', h'⟩
      simp only [heq', Option.some.injEq] at heq
      simp_all

theorem Iterator.isPlausibleOutput_next
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rxo.Iterator α) α} (h : it.internalState.next = some a)
    (hP : a < it.internalState.upperBound) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h, hP]

theorem Iterator.isPlausibleOutput_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rxo.Iterator α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        a < it.internalState.upperBound := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem Iterator.Monadic.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it' it : IterM (α := Rxo.Iterator α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        a < it.internalState.upperBound ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp only [IterM.IsPlausibleSuccessorOf]
  constructor
  · rintro ⟨step, h, h'⟩
    cases h'
    simp only [Monadic.step] at h
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

theorem Iterator.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it' it : Iter (α := Rxo.Iterator α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        a < it.internalState.upperBound ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem Iterator.isSome_next_of_isPlausibleIndirectOutput
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rxo.Iterator α) α} {out : α} (h : it.IsPlausibleIndirectOutput out) :
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

private def Iterator.instFinitenessRelation [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] :
    FinitenessRelation (Rxo.Iterator α) Id where
  rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    have hnone : ∀ bound, Acc (fun it' it : IterM (α := Rxo.Iterator α) Id α => it'.IsPlausibleSuccessorOf it)
        ⟨⟨none, bound⟩⟩ := by
      intro bound
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step] at hs₂
      simp [hs₂, IterStep.successor] at hs₁
    simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      Monadic.step, exists_eq_right] at hnone ⊢
    match it with
    | ⟨⟨none, _⟩⟩ => apply hnone
    | ⟨⟨some init, bound⟩⟩ =>
      obtain ⟨n, hn⟩ := Rxo.IsAlwaysFinite.finite init bound
      induction n generalizing init with
      | zero =>
        simp only [succMany?_zero, Option.elim_some] at hn
        constructor
        simp [hn, IterStep.successor]
      | succ n ih =>
        constructor
        rintro it'
        simp only [succMany?_add_one_eq_succ?_bind_succMany?] at hn
        match hs : succ? init with
        | none =>
          simp only [hs]
          intro h
          split at h
          · cases h
            apply hnone
          · cases h
        | some a =>
          intro h
          simp only [hs] at h hn
          specialize ih _ hn
          split at h
          · cases h
            exact ih
          · cases h
  subrelation := id

@[no_expose]
instance Iterator.instFinite [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [Rxo.IsAlwaysFinite α] :
    Finite (Rxo.Iterator α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def Iterator.instProductivenessRelation [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] :
    ProductivenessRelation (Rxo.Iterator α) Id where
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
instance Iterator.instProductive [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] :
    Productive (Rxo.Iterator α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance Iterator.instIteratorAccess [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] :
    IteratorAccess (Rxo.Iterator α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (UpwardEnumerable.succMany? n) with
    | none => .done
    | some next => if next < it.internalState.upperBound then
        .yield ⟨⟨UpwardEnumerable.succ? next, it.internalState.upperBound⟩⟩ next
      else
        .done, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, succMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, succMany?_zero, Option.some.injEq] at heq
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
            simp only [heq', Option.bind_some, succMany?_add_one_eq_succ?_bind_succMany?] at heq
            specialize ih ⟨⟨UpwardEnumerable.succ? out, it.internalState.upperBound⟩⟩
            simp only [heq] at ih
            by_cases heq'' : out < it.internalState.upperBound
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
          have hlt : UpwardEnumerable.LT out _ := ⟨n, heq⟩
          simp only [succMany?_add_one_eq_succ?_bind_succMany?] at heq
          specialize ih ⟨⟨UpwardEnumerable.succ? out, it.internalState.upperBound⟩⟩
          simp only [heq] at ih
          by_cases hout : out < it.internalState.upperBound
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout, ↓reduceIte,
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih
          · rename_i next
            haveI := UpwardEnumerable.instLTTransOfLawfulUpwardEnumerableLT (α := α)
            have := hout.imp (fun h : next < it.internalState.upperBound => by
              rw [← UpwardEnumerable.lt_iff] at hlt
              exact Trans.trans hlt h)
            simp only [this, ↓reduceIte]
            simp only [this, ↓reduceIte] at ih
            apply IterM.IsPlausibleNthOutputStep.done
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout])⟩

instance Iterator.instLawfulDeterministicIterator [UpwardEnumerable α] [LT α] [DecidableLT α] :
    LawfulDeterministicIterator (Rxo.Iterator α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerable α]
    {it : IterM (α := Rxo.Iterator α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (succMany? n ·) = some out ∧
        out < it.internalState.upperBound := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulUpwardEnumerable.succMany?_zero]⟩
    case indirect h _ ih =>
      rw [Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, succMany?_add_one_eq_succ?_bind_succMany?, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [Monadic.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulUpwardEnumerable.succMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hlt : UpwardEnumerable.LT a out := ⟨_, hn⟩
      rw [succMany?_add_one_eq_succ?_bind_succMany?] at hn
      cases hn' : succ? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨some a', it.internalState.upperBound⟩) hn hu
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Monadic.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      haveI := UpwardEnumerable.instLTTransOfLawfulUpwardEnumerableLT (α := α)
      exact Trans.trans (α := α) (UpwardEnumerable.lt_iff.mpr hlt) hu

theorem Iterator.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {it : Iter (α := Rxo.Iterator α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (succMany? n ·) = some out ∧
        out < it.internalState.upperBound := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
@[always_inline, inline]
instance Iterator.instIteratorLoop [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (Rxo.Iterator α) Id n where
  forIn _ γ Pl wf it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      if hu : next < upperBound then
        loop γ Pl wf upperBound next init (fun a ha₁ ha₂ c => f a ?hf c) next ?hle hu
      else
        return init
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[specialize]
    loop γ Pl wf (upperBound : α) least acc
        (f : (out : α) → UpwardEnumerable.LE least out → out < upperBound → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s)))
        (next : α) (hl : UpwardEnumerable.LE least next) (hu : next < upperBound) : n γ := do
      match ← f next hl hu acc with
      | ⟨.yield acc', _⟩ =>
        match hs : UpwardEnumerable.succ? next with
        | some next' =>
          if hu : next' < upperBound then
            loop γ Pl wf upperBound least acc' f next' ?hle' hu
          else
            return acc'
        | none => return acc'
      | ⟨.done acc', _⟩ => return acc'
    termination_by IteratorLoop.WithWF.mk ⟨⟨some next, upperBound⟩⟩ acc (hwf := wf)
    decreasing_by
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff,
        Monadic.step, *]
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [succMany?_one, hs]

/--
An efficient {name}`IteratorLoopPartial` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
partial instance Iterator.instIteratorLoopPartial [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] : IteratorLoopPartial (Rxo.Iterator α) Id n where
  forInPartial _ γ it init f :=
    match it with
    | ⟨⟨some next, upperBound⟩⟩ =>
      if hu : next < upperBound then
        loop γ upperBound next init (fun a ha₁ ha₂ c => f a ?hf c) next ?hle hu
      else
        return init
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[specialize]
    loop γ (upperBound : α) least acc
        (f : (out : α) → UpwardEnumerable.LE least out → out < upperBound → (c : γ) → n (ForInStep γ))
        (next : α) (hl : UpwardEnumerable.LE least next) (hu : next < upperBound) : n γ := do
      match ← f next hl hu acc with
      | .yield acc' =>
        match hs : succ? next with
        | some next' =>
          if hu : next' < upperBound then
            loop γ upperBound least acc' f next' ?hle' hu
          else
            return acc'
        | none => return acc'
      | .done acc' => return acc'
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [succMany?_one, hs]

theorem Iterator.instIteratorLoop.loop_eq [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] {γ : Type u}
    {lift} [Internal.LawfulMonadLiftBindFunction lift]
    {PlausibleForInStep} {upperBound} {next} {hl} {hu} {f} {acc} {wf} :
    loop (α := α) (n := n) γ PlausibleForInStep wf upperBound least acc f next hl hu =
      (do
        match ← f next hl hu acc with
        | ⟨.yield c, _⟩ =>
          letI it' : IterM (α := Rxo.Iterator α) Id α := ⟨⟨succ? next, upperBound⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) lift γ
            PlausibleForInStep wf it' c it'.IsPlausibleIndirectOutput (fun _ => id)
            (fun b h c => f b
                (by
                  refine UpwardEnumerable.le_trans hl ?_
                  simp only [Monadic.isPlausibleIndirectOutput_iff, it',
                    ← succMany?_add_one_eq_succ?_bind_succMany?] at h
                  exact ⟨h.choose + 1, h.choose_spec.1⟩)
                (by
                  simp only [Monadic.isPlausibleIndirectOutput_iff, it'] at h
                  exact h.choose_spec.2) c)
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
        rw [loop_eq (lift := lift), Shrink.inflate_deflate]
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
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulIteratorLoop [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (Rxo.Iterator α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction
    ext γ PlausibleForInStep hwf it init f
    simp only [IteratorLoop.forIn, IteratorLoop.defaultImplementation]
    rw [IterM.DefaultConsumers.forIn']
    simp only [Monadic.step_eq_step, Monadic.step]
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

end IteratorLoop

end Rxo

namespace Rxi

variable {α : Type u} {lo a : α}

/-- Internal state of the range iterators. Do not depend on its internals. -/
@[unbox]
protected structure Iterator (α : Type u) where
  next : Option α

/--
The pure function mapping a range iterator of type {name}`IterM` to the next step of the iterator.

This function is prefixed with {lit}`Monadic` in order to disambiguate it from the version for iterators
of type {name}`Iter`.
-/
@[inline]
def Iterator.Monadic.step [UpwardEnumerable α]
    (it : IterM (α := Rxi.Iterator α) Id α) :
    IterStep (IterM (α := Rxi.Iterator α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some next => .yield ⟨⟨UpwardEnumerable.succ? next⟩⟩ next

/--
The pure function mapping a range iterator of type {name}`Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def Iterator.step [UpwardEnumerable α]
    (it : Iter (α := Rxi.Iterator α) α) :
    IterStep (Iter (α := Rxi.Iterator α) α) α :=
  match it.internalState.next with
  | none => .done
  | some next => .yield ⟨⟨UpwardEnumerable.succ? next⟩⟩ next

theorem Iterator.step_eq_monadicStep [UpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    Iterator.step it = (Iterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split <;> rfl

@[always_inline, inline]
instance [UpwardEnumerable α] :
    Iterator (Rxi.Iterator α) Id α where
  IsPlausibleStep it step := step = Iterator.Monadic.step it
  step it := pure (.deflate ⟨Iterator.Monadic.step it, rfl⟩)

theorem Iterator.Monadic.isPlausibleStep_iff [UpwardEnumerable α]
    {it : IterM (α := Rxi.Iterator α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.Monadic.step it := by
  exact Iff.rfl

theorem Iterator.Monadic.step_eq_step [UpwardEnumerable α]
    {it : IterM (α := Rxi.Iterator α) Id α} :
    it.step = pure (.deflate ⟨Iterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩) := by
  simp [IterM.step, Iterators.Iterator.step]

theorem Iterator.isPlausibleStep_iff [UpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.step it := by
  simp only [Iter.IsPlausibleStep, Monadic.isPlausibleStep_iff, step_eq_monadicStep]
  constructor
  · intro h
    generalize hs : (step.mapIterator Iter.toIterM) = stepM at h
    cases h
    replace hs := congrArg (IterStep.mapIterator IterM.toIter) hs
    simpa using hs
  · rintro rfl
    simp only [IterStep.mapIterator_mapIterator, Iter.toIterM_comp_toIter, IterStep.mapIterator_id]

theorem Iterator.step_eq_step [UpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    it.step = ⟨Iterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step, step_eq_monadicStep, Monadic.step_eq_step, IterM.Step.toPure]

instance Iterator.instIteratorCollect [UpwardEnumerable α]
    {n : Type u → Type w} [Monad n] : IteratorCollect (Rxi.Iterator α) Id n :=
  .defaultImplementation

instance Iterator.instIteratorCollectPartial [UpwardEnumerable α]
    {n : Type u → Type w} [Monad n] : IteratorCollectPartial (Rxi.Iterator α) Id n :=
  .defaultImplementation

theorem Iterator.Monadic.isPlausibleOutput_next {a} [UpwardEnumerable α]
    {it : IterM (α := Rxi.Iterator α) Id α} (h : it.internalState.next = some a) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, Monadic.step, h]

theorem Iterator.Monadic.isPlausibleOutput_iff
    [UpwardEnumerable α]
    {it : IterM (α := Rxi.Iterator α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a := by
  simp [IterM.IsPlausibleOutput, isPlausibleStep_iff, Monadic.step]
  split
  · simp [*]
  · simp_all [eq_comm (a := a)]

theorem Iterator.isPlausibleOutput_next
    [UpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} (h : it.internalState.next = some a) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h]

theorem Iterator.isPlausibleOutput_iff
    [UpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem Iterator.Monadic.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α]
    {it' it : IterM (α := Rxi.Iterator α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        UpwardEnumerable.succ? a = it'.internalState.next := by
  simp only [IterM.IsPlausibleSuccessorOf]
  constructor
  · rintro ⟨step, h, h'⟩
    cases h'
    simp only [Monadic.step] at h
    split at h
    · cases h
    · cases h
      simp_all
  · rintro ⟨a, h, h'⟩
    refine ⟨.yield it' a, rfl, ?_⟩
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, step, h,
      IterStep.yield.injEq, and_true]
    simp [h']

theorem Iterator.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α]
    {it' it : Iter (α := Rxi.Iterator α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        UpwardEnumerable.succ? a = it'.internalState.next := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem Iterator.isSome_next_of_isPlausibleIndirectOutput
    [UpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} {out : α} (h : it.IsPlausibleIndirectOutput out) :
    it.internalState.next.isSome := by
  cases h
  case direct h =>
    rw [isPlausibleOutput_iff] at h
    simp [h]
  case indirect h _ =>
    rw [isPlausibleSuccessorOf_iff] at h
    obtain ⟨a, ha, _⟩ := h
    simp [ha]

private def Iterator.instFinitenessRelation [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] :
    FinitenessRelation (Rxi.Iterator α) Id where
  rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    have hnone : Acc (fun it' it : IterM (α := Rxi.Iterator α) Id α => it'.IsPlausibleSuccessorOf it)
        ⟨⟨none⟩⟩ := by
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step] at hs₂
      simp [hs₂, IterStep.successor] at hs₁
    simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      Monadic.step, exists_eq_right] at hnone ⊢
    match it with
    | ⟨⟨none⟩⟩ => apply hnone
    | ⟨⟨some init⟩⟩ =>
      obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init
      induction n generalizing init with
      | zero => simp [succMany?_zero] at hn
      | succ n ih =>
        constructor
        rintro it'
        simp only [succMany?_add_one_eq_succ?_bind_succMany?] at hn
        match hs : succ? init with
        | none =>
          simp only [hs]
          intro h
          cases h
          apply hnone
        | some a =>
          intro h
          simp only [hs] at h hn
          specialize ih _ hn
          cases h
          exact ih
  subrelation := id

@[no_expose]
instance Iterator.instFinite [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] :
    Finite (Rxi.Iterator α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def Iterator.instProductivenessRelation [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] :
    ProductivenessRelation (Rxi.Iterator α) Id where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by
    exfalso
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep,
      Iterator.IsPlausibleStep, Monadic.step] at h
    split at h <;> cases h

@[no_expose]
instance Iterator.instProductive [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] :
    Productive (Rxi.Iterator α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance Iterator.instIteratorAccess [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] :
    IteratorAccess (Rxi.Iterator α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (UpwardEnumerable.succMany? n) with
    | none => .done
    | some next =>
        .yield ⟨⟨UpwardEnumerable.succ? next⟩⟩ next, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, succMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, succMany?_zero, Option.some.injEq] at heq
          cases heq
          · apply IterM.IsPlausibleNthOutputStep.zero_yield
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq']
      · rename_i n ih
        split <;> rename_i heq
        · cases heq' : it.internalState.next
          · apply IterM.IsPlausibleNthOutputStep.done
            simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq']
          · rename_i out
            simp only [heq', Option.bind_some, succMany?_add_one_eq_succ?_bind_succMany?] at heq
            specialize ih ⟨⟨UpwardEnumerable.succ? out⟩⟩
            simp only [heq] at ih
            · apply IterM.IsPlausibleNthOutputStep.yield
              · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq',
                IterStep.yield.injEq]
                exact ⟨rfl, rfl⟩
              · exact ih
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          rename_i out
          simp only [heq', Option.bind_some] at heq
          have hlt : UpwardEnumerable.LT out _ := ⟨n, heq⟩
          simp only [succMany?_add_one_eq_succ?_bind_succMany?] at heq
          specialize ih ⟨⟨UpwardEnumerable.succ? out⟩⟩
          simp only [heq] at ih
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq',
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih)⟩

instance Iterator.instLawfulDeterministicIterator [UpwardEnumerable α] :
    LawfulDeterministicIterator (Rxi.Iterator α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {it : IterM (α := Rxi.Iterator α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (succMany? n ·) = some out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulUpwardEnumerable.succMany?_zero]⟩
    case indirect h _ ih =>
      rw [Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, succMany?_add_one_eq_succ?_bind_succMany?, hn, h]
  · rintro ⟨n, hn⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [Monadic.isPlausibleOutput_iff]
      simpa [LawfulUpwardEnumerable.succMany?_zero] using hn
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hlt : UpwardEnumerable.LT a out := ⟨_, hn⟩
      rw [succMany?_add_one_eq_succ?_bind_succMany?] at hn
      cases hn' : succ? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨⟨some a'⟩⟩) hn
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Monadic.isPlausibleSuccessorOf_iff]
      exact ⟨a, ‹_›, hn'⟩

theorem Iterator.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (succMany? n ·) = some out := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a
special loop implementation.
-/
@[always_inline, inline]
instance Iterator.instIteratorLoop [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (Rxi.Iterator α) Id n where
  forIn _ γ Pl wf it init f :=
    match it with
    | ⟨⟨some next⟩⟩ =>
        loop γ Pl wf next init (fun a ha c => f a ?hf c) next ?hle
    | ⟨⟨none⟩⟩ => return init
  where
    @[specialize]
    loop γ Pl wf least acc
        (f : (out : α) → UpwardEnumerable.LE least out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s)))
        (next : α) (hl : UpwardEnumerable.LE least next) : n γ := do
      match ← f next hl acc with
      | ⟨.yield acc', _⟩ =>
        match hs : UpwardEnumerable.succ? next with
        | some next' =>
            loop γ Pl wf least acc' f next' ?hle'
        | none => return acc'
      | ⟨.done acc', _⟩ => return acc'
    termination_by IteratorLoop.WithWF.mk ⟨⟨some next⟩⟩ acc (hwf := wf)
    decreasing_by
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff,
        Monadic.step, *]
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      exact ha
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [succMany?_one, hs]

/--
An efficient {name}`IteratorLoopPartial` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a
special loop implementation.
-/
partial instance Iterator.instIteratorLoopPartial [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {n : Type u → Type w} [Monad n] : IteratorLoopPartial (Rxi.Iterator α) Id n where
  forInPartial _ γ it init f :=
    match it with
    | ⟨⟨some next⟩⟩ => loop γ next init (fun a ha c => f a ?hf c) next ?hle
    | ⟨⟨none⟩⟩ => return init
  where
    @[specialize]
    loop γ least acc
        (f : (out : α) → UpwardEnumerable.LE least out → (c : γ) → n (ForInStep γ))
        (next : α) (hl : UpwardEnumerable.LE least next) : n γ := do
      match ← f next hl acc with
      | .yield acc' =>
        match hs : succ? next with
        | some next' =>
            loop γ least acc' f next' ?hle'
        | none => return acc'
      | .done acc' => return acc'
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      exact ha
    case hle =>
      exact UpwardEnumerable.le_refl _
    case hle' =>
      refine UpwardEnumerable.le_trans hl ⟨1, ?_⟩
      simp [succMany?_one, hs]

theorem Iterator.instIteratorLoop.loop_eq [UpwardEnumerable α]
    [LawfulUpwardEnumerable α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] {γ : Type u}
    {lift} [Internal.LawfulMonadLiftBindFunction lift]
    {PlausibleForInStep next hl f acc wf} :
    loop (α := α) (n := n) γ PlausibleForInStep wf least acc f next hl =
      (do
        match ← f next hl acc with
        | ⟨.yield c, _⟩ =>
          letI it' : IterM (α := Rxi.Iterator α) Id α := ⟨⟨succ? next⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) lift γ
            PlausibleForInStep wf it' c it'.IsPlausibleIndirectOutput (fun _ => id)
            (fun b h c => f b
                (by
                  refine UpwardEnumerable.le_trans hl ?_
                  simp only [Monadic.isPlausibleIndirectOutput_iff, it',
                    ← succMany?_add_one_eq_succ?_bind_succMany?] at h
                  exact ⟨h.choose + 1, h.choose_spec⟩)
                c)
        | ⟨.done c, _⟩ => return c) := by
  rw [loop]
  apply bind_congr
  intro step
  split
  · split
    · split
      · rename_i heq
        cases heq
        simp only [*]
        rw [IterM.DefaultConsumers.forIn']
        simp only [Monadic.step_eq_step, Monadic.step, *,
          Internal.LawfulMonadLiftBindFunction.liftBind_pure]
        rw [loop_eq (lift := lift), Shrink.inflate_deflate]
        apply bind_congr
        intro step
        split
        · apply IterM.DefaultConsumers.forIn'_eq_forIn'
          intros; rfl
        · simp
      · rename_i heq
        cases heq
    · simp only [*]
      rw [IterM.DefaultConsumers.forIn']
      simp [Monadic.step_eq_step, Monadic.step, Internal.LawfulMonadLiftBindFunction.liftBind_pure]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next⟩⟩ acc (hwf := wf)
decreasing_by
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulIteratorLoop [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (Rxi.Iterator α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction
    ext γ PlausibleForInStep hwf it init f
    simp only [IteratorLoop.forIn, IteratorLoop.defaultImplementation]
    rw [IterM.DefaultConsumers.forIn']
    simp only [Monadic.step_eq_step, Monadic.step]
    simp only [Internal.LawfulMonadLiftBindFunction.liftBind_pure]
    split
    · rename_i it f next upperBound f'
      rw [instIteratorLoop.loop_eq (lift := lift), Shrink.inflate_deflate]
      apply bind_congr
      intro step
      split
      · apply IterM.DefaultConsumers.forIn'_eq_forIn'
        intro b c hPb hQb
        congr
      · simp
    · simp

end IteratorLoop

end Rxi

end Std
