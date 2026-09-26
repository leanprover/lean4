/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Woosuk Kwak
-/
module

prelude
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
public import Init.Data.Range.Polymorphic.PRange
public import Init.Data.Iterators.Consumers.Monadic.Access
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.ByCases
import Init.Data.Bool
import Init.Data.List.Lemmas
import Init.Data.List.Sublist
import Init.Data.Option.Lemmas

set_option doc.verso true

public section

/-!
# Range reverse iterator

This module implements a reverse iterator for ranges (such as {name}`Std.Rcc`).

This iterator is publicly available via
{name (scope := "Std.Data.Iterators.Producers.Range")}`Std.Rcc.iterRev` (and identically named
functions in the sibling namespaces) after importing {lit}`Std.Data.Iterators`.
-/

open Std.Iterators

namespace Std
open PRange

namespace Rcx

variable {α : Type u} {lo hi a : α}

/-- Internal state of the range iterators. Do not depend on its internals. -/
@[unbox]
protected structure Iterator (α : Type u) where
  next : Option α
  lowerBound : α

/--
The pure function mapping a range iterator of type {name}`IterM` to the next step of the iterator.

This function is prefixed with {lit}`Monadic` in order to disambiguate it from the version for
iterators of type {name}`Iter`.
-/
@[inline]
def Iterator.Monadic.step [DownwardEnumerable α] [LE α] [DecidableLE α]
    (it : IterM (α := Rcx.Iterator α) Id α) :
    IterStep (IterM (α := Rcx.Iterator α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some next =>
    if it.internalState.lowerBound ≤ next then
      .yield ⟨⟨DownwardEnumerable.pred? next, it.internalState.lowerBound⟩⟩ next
    else
      .done

/--
The pure function mapping a range iterator of type {name}`Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def Iterator.step [DownwardEnumerable α] [LE α] [DecidableLE α]
    (it : Iter (α := Rcx.Iterator α) α) :
    IterStep (Iter (α := Rcx.Iterator α) α) α :=
  match it.internalState.next with
  | none => .done
  | some next => if it.internalState.lowerBound ≤ next then
      .yield ⟨⟨DownwardEnumerable.pred? next, it.internalState.lowerBound⟩⟩ next
    else
      .done

theorem Iterator.step_eq_monadicStep [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rcx.Iterator α) α} :
    Iterator.step it = (Iterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split
  · rfl
  · split <;> rfl

@[always_inline, inline]
instance [DownwardEnumerable α] [LE α] [DecidableLE α] :
    Iterator (Rcx.Iterator α) Id α where
  IsPlausibleStep it step := step = Iterator.Monadic.step it
  step it := pure <| .deflate <| ⟨Iterator.Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleStep_iff [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rcx.Iterator α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.Monadic.step it := by
  exact Iff.rfl

theorem Iterator.Monadic.step_eq_step [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rcx.Iterator α) Id α} :
    Std.Iterator.step it = pure (.deflate ⟨Iterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩) := by
  simp [Std.Iterator.step]

theorem Iterator.isPlausibleStep_iff [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rcx.Iterator α) α} {step} :
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

theorem Iterator.step_eq_step [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rcx.Iterator α) α} :
    it.step = ⟨Iterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [step_eq_monadicStep, IterM.Step.toPure, Iter.step_eq]

theorem Iterator.Monadic.isPlausibleOutput_next {a}
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rcx.Iterator α) Id α} (h : it.internalState.next = some a)
    (hP : a ≥ it.internalState.lowerBound) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, Monadic.step, h, hP]

theorem Iterator.Monadic.isPlausibleOutput_iff
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : IterM (α := Rcx.Iterator α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        it.internalState.lowerBound ≤ a := by
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
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rcx.Iterator α) α} (h : it.internalState.next = some a)
    (hP : it.internalState.lowerBound ≤ a) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h, hP]

theorem Iterator.isPlausibleOutput_iff
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rcx.Iterator α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        it.internalState.lowerBound ≤ a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem Iterator.Monadic.isPlausibleSuccessorOf_iff
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it' it : IterM (α := Rcx.Iterator α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        it.internalState.lowerBound ≤ a ∧
        DownwardEnumerable.pred? a = it'.internalState.next ∧
        it'.internalState.lowerBound = it.internalState.lowerBound := by
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
      IterStep.yield.injEq, and_true, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLE] -- TODO
    simp [h'.1, ← h'.2]

theorem Iterator.isPlausibleSuccessorOf_iff
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it' it : Iter (α := Rcx.Iterator α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        it.internalState.lowerBound ≤ a ∧
        DownwardEnumerable.pred? a = it'.internalState.next ∧
        it'.internalState.lowerBound = it.internalState.lowerBound := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem Iterator.isSome_next_of_isPlausibleIndirectOutput
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    {it : Iter (α := Rcx.Iterator α) α} {out : α} (h : it.IsPlausibleIndirectOutput out) :
    it.internalState.next.isSome := by
  cases h
  case direct h =>
    rw [isPlausibleOutput_iff] at h
    simp [h]
  case indirect h _ =>
    rw [isPlausibleSuccessorOf_iff] at h
    obtain ⟨a, ha, _⟩ := h
    simp [ha]

private def Iterator.instFinitenessRelation [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [Rcx.IsAlwaysFiniteRev α] :
    FinitenessRelation (Rcx.Iterator α) Id where
  Rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    have hnone : ∀ bound, Acc (fun it' it : IterM (α := Rcx.Iterator α) Id α => it'.IsPlausibleSuccessorOf it)
        ⟨⟨none, bound⟩⟩ := by
      intro bound
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLE] at hs₂ -- TODO
      simp [hs₂, IterStep.successor] at hs₁
    simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      Monadic.step, exists_eq_right, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLE] at hnone ⊢ -- TODO
    match it with
    | ⟨⟨none, _⟩⟩ => apply hnone
    | ⟨⟨some init, bound⟩⟩ =>
      obtain ⟨n, hn⟩ := Rcx.IsAlwaysFiniteRev.finite init bound
      induction n generalizing init with
      | zero =>
        simp only [predMany?_zero, Option.elim_some] at hn
        constructor
        simp [hn, IterStep.successor]
      | succ n ih =>
        constructor
        rintro it'
        simp only [predMany?_add_one_eq_pred?_bind_predMany?] at hn
        match hs : pred? init with
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

instance Iterator.instFinite [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [Rcx.IsAlwaysFiniteRev α] :
    Finite (Rcx.Iterator α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def Iterator.instProductivenessRelation [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] :
    ProductivenessRelation (Rcx.Iterator α) Id where
  Rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by
    exfalso
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep,
      Iterator.IsPlausibleStep, Monadic.step, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLE] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h

instance Iterator.instProductive [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] :
    Productive (Rcx.Iterator α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance Iterator.instIteratorAccess [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α] :
    IteratorAccess (Rcx.Iterator α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (DownwardEnumerable.predMany? n) with
    | none => .done
    | some next => if it.internalState.lowerBound ≤ next then
        .yield ⟨⟨DownwardEnumerable.pred? next, it.internalState.lowerBound⟩⟩ next
      else
        .done, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, predMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, predMany?_zero, Option.some.injEq] at heq
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
            simp only [heq', Option.bind_some, predMany?_add_one_eq_pred?_bind_predMany?] at heq
            specialize ih ⟨⟨DownwardEnumerable.pred? out, it.internalState.lowerBound⟩⟩
            simp only [heq] at ih
            by_cases heq'' : it.internalState.lowerBound ≤ out
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
          have hle : DownwardEnumerable.LE _ out := ⟨n + 1, heq⟩
          simp only [predMany?_add_one_eq_pred?_bind_predMany?] at heq
          specialize ih ⟨⟨DownwardEnumerable.pred? out, it.internalState.lowerBound⟩⟩
          simp only [heq] at ih
          by_cases hout : it.internalState.lowerBound ≤ out
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout, ↓reduceIte,
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih
          · rename_i next
            haveI := DownwardEnumerable.instLETransOfLawfulDownwardEnumerableLE (α := α)
            have := hout.imp (fun h : it.internalState.lowerBound ≤ next => by
              rw [← DownwardEnumerable.le_iff] at hle
              exact Trans.trans h hle)
            simp only [this, ↓reduceIte]
            simp only [this, ↓reduceIte] at ih
            apply IterM.IsPlausibleNthOutputStep.done
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout])⟩

instance Iterator.instLawfulDeterministicIterator [DownwardEnumerable α] [LE α] [DecidableLE α] :
    LawfulDeterministicIterator (Rcx.Iterator α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleIndirectOutput_iff
    [DownwardEnumerable α] [LE α] [DecidableLE α] [LawfulDownwardEnumerableLE α]
    [LawfulDownwardEnumerable α]
    {it : IterM (α := Rcx.Iterator α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (predMany? n ·) = some out ∧
        it.internalState.lowerBound ≤ out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulDownwardEnumerable.predMany?_zero]⟩
    case indirect h _ ih =>
      rw [Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, predMany?_add_one_eq_pred?_bind_predMany?, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [Monadic.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulDownwardEnumerable.predMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hle : DownwardEnumerable.LE out a := ⟨_, hn⟩
      rw [predMany?_add_one_eq_pred?_bind_predMany?] at hn
      cases hn' : pred? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨some a', it.internalState.lowerBound⟩) hn hu
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Monadic.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      haveI := DownwardEnumerable.instLETransOfLawfulDownwardEnumerableLE (α := α)
      exact Trans.trans (α := α) (r := (· ≤ ·)) hu (DownwardEnumerable.le_iff.mpr hle)

theorem Iterator.isPlausibleIndirectOutput_iff
    [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α]
    {it : Iter (α := Rcx.Iterator α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (predMany? n ·) = some out ∧
        it.internalState.lowerBound ≤ out := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
@[always_inline, inline]
instance Iterator.instIteratorLoop [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (Rcx.Iterator α) Id n where
  forIn _ γ Pl it init f :=
    match it with
    | ⟨⟨some next, lowerBound⟩⟩ =>
      loop γ Pl (· ≤ next) (fun a b hab hna => ?hle) lowerBound init next ?hle'' (fun a ha₁ ha₂ c => f a ?hf c)
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[always_inline, inline]
    loop γ (Pl : α → γ → ForInStep γ → Prop) (SmallEnough : α → Prop) (hl : ∀ a b : α, a ≤ b → SmallEnough b → SmallEnough a)
        (lowerBound : α) (acc : γ) (next : α) (h : SmallEnough next)
        (f : (out : α) → SmallEnough out → lowerBound ≤ out → (c : γ) → n (Subtype (Pl out c))) : n γ :=
      haveI : Nonempty γ := ⟨acc⟩
      WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => n γ) (InvImage (IteratorLoop.rel _ Id Pl) (fun x => (⟨Rcx.Iterator.mk (some x.1) lowerBound⟩, x.2.1)))
        (fun next acc (h : SmallEnough next) G => do
          if hu : lowerBound ≤ next then
            match ← f next h hu acc with
            | ⟨.yield acc', h'⟩ =>
              match hs : DownwardEnumerable.pred? next with
              | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
              | none => return acc'
            | ⟨.done acc', _⟩ => return acc'
          else
            return acc) next acc h
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      simp only [DownwardEnumerable.le_iff] at ha₁
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      simp only [DownwardEnumerable.le_iff] at hna hab ⊢
      exact DownwardEnumerable.le_trans hab hna
    case hle' =>
      simp only [DownwardEnumerable.le_iff]
      refine ⟨1, ?_⟩
      simpa [predMany?_one] using hs
    case hle'' =>
      exact DownwardEnumerable.le_iff.mpr (DownwardEnumerable.le_refl _)
    case decreasing =>
      simp_wf
      simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

private noncomputable def Iterator.instIteratorLoop.loop.wf [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] (γ : Type u)
    (Pl : α → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (Rcx.Iterator α) Id Pl)
    (SmallEnough : α → Prop) (hl : ∀ a b : α, a ≤ b → SmallEnough b → SmallEnough a)
    (lowerBound : α) (acc : γ) (next : α) (h : SmallEnough next)
    (f : (out : α) → SmallEnough out → lowerBound ≤ out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s))) :
    n γ := do
  if hu : lowerBound ≤ next then
    match ← f next h hu acc with
    | ⟨.yield acc', _⟩ =>
      match hs : DownwardEnumerable.pred? next with
      | some next' =>
        loop.wf γ Pl wf SmallEnough hl lowerBound acc' next' (hl _ _ ?hle h) f
      | none => return acc'
    | ⟨.done acc', _⟩ => return acc'
  else
    return acc
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, lowerBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]
where finally
  case hle =>
    simp only [DownwardEnumerable.le_iff]
    refine ⟨1, ?_⟩
    simpa [predMany?_one] using hs

private theorem Iterator.instIteratorLoop.loop_eq_wf [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α] [Monad n] [LawfulMonad n]
    {γ SmallEnough hl lowerBound} {next hn} {acc} (Pl wf f) :
    loop γ Pl SmallEnough hl lowerBound acc next hn f =
      loop.wf (α := α) (n := n) γ Pl wf SmallEnough hl lowerBound acc next hn f := by
  haveI : Nonempty γ := ⟨acc⟩
  rw [loop, WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · exact InvImage.wf _ wf
  · fun_induction loop.wf γ Pl wf SmallEnough hl lowerBound acc  next hn f
    · rw [WellFounded.fix_eq]
      simp only [↓reduceDIte, *]
      apply bind_congr; intro forInStep
      split
      · simp only
        split
        · simp_all
        · simp
      · simp
    · rw [WellFounded.fix_eq]
      simp_all

private theorem Iterator.instIteratorLoop.loopWf_eq [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] (γ : Type u)
    {lift} [instLawfulMonadLiftFunction : Std.Internal.LawfulMonadLiftBindFunction (m := Id) (n := n) lift]
    (Pl : α → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (Rcx.Iterator α) Id Pl)
    (SmallEnough : α → Prop) (hl : ∀ a b : α, a ≤ b → SmallEnough b → SmallEnough a)
    (lowerBound : α) (acc : γ) (next : α) (h : SmallEnough next)
    (f : (out : α) → SmallEnough out → lowerBound ≤ out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s))) :
    loop.wf γ Pl wf SmallEnough hl lowerBound acc next h f = (do
      if hu : lowerBound ≤ next then
        match ← f next h hu acc with
        | ⟨.yield acc', _⟩ =>
          letI it' : IterM (α := Rcx.Iterator α) Id α := ⟨⟨pred? next, lowerBound⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) (n := n) lift γ Pl it' acc'
            it'.IsPlausibleIndirectOutput (fun _ => id)
            fun next' h acc' => f next'
              (by
                refine hl next' next ?_ ‹_›
                simp only [it', Monadic.isPlausibleIndirectOutput_iff,
                  ← predMany?_add_one_eq_pred?_bind_predMany?] at h
                exact DownwardEnumerable.le_iff.mpr ⟨h.choose + 1, h.choose_spec.1⟩)
              (by
                simp only [it', Monadic.isPlausibleIndirectOutput_iff] at h
                exact h.choose_spec.2)
              acc'
        | ⟨.done acc', _⟩ => return acc'
      else return acc) := by
  haveI : Nonempty γ := ⟨acc⟩
  rw [loop.wf]
  congr 1; ext hu
  apply bind_congr; intro forInStep
  split
  · split
    · rw [loopWf_eq (lift := lift) _ Pl wf]
      rw [IterM.DefaultConsumers.forIn'_eq_match_step (lift := lift) Pl wf]; rotate_left
      · simp only [IterM.step_mk, Monadic.step_eq_step, Monadic.step,
          Shrink.inflate_deflate, instLawfulMonadLiftFunction.liftBind_pure, *]
        split
        · apply bind_congr; intro forInStep
          split
          · apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf <;> (intros; rfl)
          · simp
        · simp
    · rw [IterM.DefaultConsumers.forIn'_eq_match_step Pl wf]
      simp only [IterM.step_eq, instLawfulMonadLiftFunction.liftBind_pure, Shrink.inflate_deflate, *]
      -- Unfolding `Monadic.step` earlier would make some defeq checks fail on reducible transparency:
      -- `Iterator.IsPlausibleStep` is reducible and it reduces to `Monadic.step`, but `Monadic.step`
      -- is semireducible, and `simp` isn't able to unfold `Monadic.step` inside `Iterator.IsPlausibleStep`,
      -- since that one only appears in the type of a constant -- I think?
      simp [Monadic.step]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, lowerBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulIteratorLoop [DownwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (Rcx.Iterator α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction γ it init Pl wf f
    simp only [IteratorLoop.forIn, IterM.DefaultConsumers.forIn'_eq_wf Pl wf]
    rw [IterM.DefaultConsumers.forIn'.wf]
    split; rotate_left
    · simp only [IterM.step_eq,
      Internal.LawfulMonadLiftBindFunction.liftBind_pure (liftBind := lift), Shrink.inflate_deflate]
      simp [Monadic.step]
    rename_i next _
    rw [instIteratorLoop.loop_eq_wf Pl wf, instIteratorLoop.loopWf_eq (lift := lift)]
    simp only [IterM.step_mk, Monadic.step_eq_step, Monadic.step,
      instLawfulMonadLiftFunction.liftBind_pure, Shrink.inflate_deflate]
    split
    · apply bind_congr; intro forInStep
      split
      · simp only
        rw [← IterM.DefaultConsumers.forIn'_eq_wf Pl wf _]
        apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf <;> all_goals (intros; rfl)
      · simp
    · simp

end IteratorLoop

end Rcx

namespace Rox

variable {α : Type u} {lo hi a : α}

/-- Internal state of the range iterators. Do not depend on its internals. -/
@[unbox]
protected structure Iterator (α : Type u) where
  next : Option α
  lowerBound : α

/--
The pure function mapping a range iterator of type {name}`IterM` to the next step of the iterator.

This function is prefixed with {lit}`Monadic` in order to disambiguate it from the version for iterators
of type {name}`Iter`.
-/
@[inline, implicit_reducible]
def Iterator.Monadic.step [DownwardEnumerable α] [LT α] [DecidableLT α]
    (it : IterM (α := Rox.Iterator α) Id α) :
    IterStep (IterM (α := Rox.Iterator α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some next =>
    if it.internalState.lowerBound < next then
      .yield ⟨⟨DownwardEnumerable.pred? next, it.internalState.lowerBound⟩⟩ next
    else
      .done

/--
The pure function mapping a range iterator of type {name}`Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def Iterator.step [DownwardEnumerable α] [LT α] [DecidableLT α]
    (it : Iter (α := Rox.Iterator α) α) :
    IterStep (Iter (α := Rox.Iterator α) α) α :=
  match it.internalState.next with
  | none => .done
  | some next => if it.internalState.lowerBound < next then
      .yield ⟨⟨DownwardEnumerable.pred? next, it.internalState.lowerBound⟩⟩ next
    else
      .done

theorem Iterator.step_eq_monadicStep [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rox.Iterator α) α} :
    Iterator.step it = (Iterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split
  · rfl
  · split <;> rfl

@[always_inline, inline]
instance [DownwardEnumerable α] [LT α] [DecidableLT α] :
    Iterator (Rox.Iterator α) Id α where
  IsPlausibleStep it step := step = Iterator.Monadic.step it
  step it := pure (.deflate ⟨Iterator.Monadic.step it, rfl⟩)

theorem Iterator.Monadic.isPlausibleStep_iff [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rox.Iterator α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.Monadic.step it := by
  exact Iff.rfl

theorem Iterator.Monadic.step_eq_step [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rox.Iterator α) Id α} :
    Std.Iterator.step it = pure (.deflate ⟨Iterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩) := by
  simp [Std.Iterator.step]

theorem Iterator.isPlausibleStep_iff [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rox.Iterator α) α} {step} :
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

theorem Iterator.step_eq_step [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rox.Iterator α) α} :
    it.step = ⟨Iterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step_eq, step_eq_monadicStep, IterM.Step.toPure]

theorem Iterator.Monadic.isPlausibleOutput_next {a}
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rox.Iterator α) Id α} (h : it.internalState.next = some a)
    (hP : it.internalState.lowerBound < a) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, Monadic.step, h, hP]

theorem Iterator.Monadic.isPlausibleOutput_iff
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : IterM (α := Rox.Iterator α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        it.internalState.lowerBound < a := by
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
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rox.Iterator α) α} (h : it.internalState.next = some a)
    (hP : it.internalState.lowerBound < a) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h, hP]

theorem Iterator.isPlausibleOutput_iff
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rox.Iterator α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        it.internalState.lowerBound < a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem Iterator.Monadic.isPlausibleSuccessorOf_iff
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it' it : IterM (α := Rox.Iterator α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        it.internalState.lowerBound < a ∧
        DownwardEnumerable.pred? a = it'.internalState.next ∧
        it'.internalState.lowerBound = it.internalState.lowerBound := by
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
      IterStep.yield.injEq, and_true, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLT] -- TODO
    simp [h'.1, ← h'.2]

theorem Iterator.isPlausibleSuccessorOf_iff
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it' it : Iter (α := Rox.Iterator α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        it.internalState.lowerBound < a ∧
        DownwardEnumerable.pred? a = it'.internalState.next ∧
        it'.internalState.lowerBound = it.internalState.lowerBound := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem Iterator.isSome_next_of_isPlausibleIndirectOutput
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    {it : Iter (α := Rox.Iterator α) α} {out : α} (h : it.IsPlausibleIndirectOutput out) :
    it.internalState.next.isSome := by
  cases h
  case direct h =>
    rw [isPlausibleOutput_iff] at h
    simp [h]
  case indirect h _ =>
    rw [isPlausibleSuccessorOf_iff] at h
    obtain ⟨a, ha, _⟩ := h
    simp [ha]

private def Iterator.instFinitenessRelation [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [Rox.IsAlwaysFiniteRev α] :
    FinitenessRelation (Rox.Iterator α) Id where
  Rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    have hnone : ∀ bound, Acc (fun it' it : IterM (α := Rox.Iterator α) Id α => it'.IsPlausibleSuccessorOf it)
        ⟨⟨none, bound⟩⟩ := by
      intro bound
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLT] at hs₂ -- TODO
      simp [hs₂, IterStep.successor] at hs₁
    simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      Monadic.step, exists_eq_right, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLT] at hnone ⊢ -- TODO
    match it with
    | ⟨⟨none, _⟩⟩ => apply hnone
    | ⟨⟨some init, bound⟩⟩ =>
      obtain ⟨n, hn⟩ := Rox.IsAlwaysFiniteRev.finite init bound
      induction n generalizing init with
      | zero =>
        simp only [predMany?_zero, Option.elim_some] at hn
        constructor
        simp [hn, IterStep.successor]
      | succ n ih =>
        constructor
        rintro it'
        simp only [predMany?_add_one_eq_pred?_bind_predMany?] at hn
        match hs : pred? init with
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

instance Iterator.instFinite [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [Rox.IsAlwaysFiniteRev α] :
    Finite (Rox.Iterator α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def Iterator.instProductivenessRelation [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] :
    ProductivenessRelation (Rox.Iterator α) Id where
  Rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by
    exfalso
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep,
      Iterator.IsPlausibleStep, Monadic.step, instIteratorIteratorIdOfDownwardEnumerableOfDecidableLT] at h -- TODO
    split at h
    · cases h
    · split at h
      · cases h
      · cases h

instance Iterator.instProductive [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] :
    Productive (Rox.Iterator α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance Iterator.instIteratorAccess [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α] :
    IteratorAccess (Rox.Iterator α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (DownwardEnumerable.predMany? n) with
    | none => .done
    | some next => if it.internalState.lowerBound < next then
        .yield ⟨⟨DownwardEnumerable.pred? next, it.internalState.lowerBound⟩⟩ next
      else
        .done, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, predMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, predMany?_zero, Option.some.injEq] at heq
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
            simp only [heq', Option.bind_some, predMany?_add_one_eq_pred?_bind_predMany?] at heq
            specialize ih ⟨⟨DownwardEnumerable.pred? out, it.internalState.lowerBound⟩⟩
            simp only [heq] at ih
            by_cases heq'' : it.internalState.lowerBound < out
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
          have hlt : DownwardEnumerable.LT _ out := ⟨n, heq⟩
          simp only [predMany?_add_one_eq_pred?_bind_predMany?] at heq
          specialize ih ⟨⟨DownwardEnumerable.pred? out, it.internalState.lowerBound⟩⟩
          simp only [heq] at ih
          by_cases hout : it.internalState.lowerBound < out
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout, ↓reduceIte,
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih
          · rename_i next
            haveI := DownwardEnumerable.instLTTransOfLawfulDownwardEnumerableLT (α := α)
            have := hout.imp (fun h : it.internalState.lowerBound < next => by
              rw [← DownwardEnumerable.lt_iff] at hlt
              exact Trans.trans h hlt)
            simp only [this, ↓reduceIte]
            simp only [this, ↓reduceIte] at ih
            apply IterM.IsPlausibleNthOutputStep.done
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq', hout])⟩

instance Iterator.instLawfulDeterministicIterator [DownwardEnumerable α] [LT α] [DecidableLT α] :
    LawfulDeterministicIterator (Rox.Iterator α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleIndirectOutput_iff
    [DownwardEnumerable α] [LT α] [DecidableLT α] [LawfulDownwardEnumerableLT α]
    [LawfulDownwardEnumerable α]
    {it : IterM (α := Rox.Iterator α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (predMany? n ·) = some out ∧
        it.internalState.lowerBound < out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulDownwardEnumerable.predMany?_zero]⟩
    case indirect h _ ih =>
      rw [Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, predMany?_add_one_eq_pred?_bind_predMany?, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [Monadic.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulDownwardEnumerable.predMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hlt : DownwardEnumerable.LT out a := ⟨_, hn⟩
      rw [predMany?_add_one_eq_pred?_bind_predMany?] at hn
      cases hn' : pred? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨some a', it.internalState.lowerBound⟩) hn hu
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Monadic.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      haveI := DownwardEnumerable.instLTTransOfLawfulDownwardEnumerableLT (α := α)
      exact Trans.trans (α := α) hu (DownwardEnumerable.lt_iff.mpr hlt)

theorem Iterator.isPlausibleIndirectOutput_iff
    [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α]
    {it : Iter (α := Rox.Iterator α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (predMany? n ·) = some out ∧
        it.internalState.lowerBound < out := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
@[always_inline, inline]
instance Iterator.instIteratorLoop [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (Rox.Iterator α) Id n where
  forIn _ γ Pl it init f :=
    match it with
    | ⟨⟨some next, lowerBound⟩⟩ =>
      loop γ Pl (DownwardEnumerable.LE · next) (fun a b hab hna => ?hle) lowerBound init next ?hle'' (fun a ha₁ ha₂ c => f a ?hf c)
    | ⟨⟨none, _⟩⟩ => return init
  where
    @[always_inline, inline]
    loop γ (Pl : α → γ → ForInStep γ → Prop) (SmallEnough : α → Prop)
        (hl : ∀ a b : α, DownwardEnumerable.LE a b → SmallEnough b → SmallEnough a)
        (lowerBound : α) (acc : γ) (next : α) (h : SmallEnough next)
        (f : (out : α) → SmallEnough out → lowerBound < out → (c : γ) → n (Subtype (Pl out c))) : n γ :=
      haveI : Nonempty γ := ⟨acc⟩
      WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => n γ) (InvImage (IteratorLoop.rel _ Id Pl) (fun x => (⟨Rox.Iterator.mk (some x.1) lowerBound⟩, x.2.1)))
        (fun next acc (h : SmallEnough next) G => do
          if hu : lowerBound < next then
            match ← f next h hu acc with
            | ⟨.yield acc', h'⟩ =>
              match hs : DownwardEnumerable.pred? next with
              | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
              | none => return acc'
            | ⟨.done acc', _⟩ => return acc'
          else
            return acc) next acc h
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      obtain ⟨n, hn⟩ := ha₁
      exact ⟨n, hn, ha₂⟩
    case hle =>
      exact DownwardEnumerable.le_trans hab hna
    case hle' =>
      refine ⟨1, ?_⟩
      simpa [predMany?_one] using hs
    case hle'' =>
      exact DownwardEnumerable.le_refl _
    case decreasing =>
      simp_wf; simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

private noncomputable def Iterator.instIteratorLoop.loop.wf [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] (γ : Type u)
    (Pl : α → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (Rox.Iterator α) Id Pl)
    (SmallEnough : α → Prop) (hl : ∀ a b : α, DownwardEnumerable.LE a b → SmallEnough b → SmallEnough a)
    (lowerBound : α) (acc : γ) (next : α) (h : SmallEnough next)
    (f : (out : α) → SmallEnough out → lowerBound < out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s))) :
    n γ := do
  if hu : lowerBound < next then
    match ← f next h hu acc with
    | ⟨.yield acc', _⟩ =>
      match hs : DownwardEnumerable.pred? next with
      | some next' =>
        loop.wf γ Pl wf SmallEnough hl lowerBound acc' next' (hl _ _ ?hle h) f
      | none => return acc'
    | ⟨.done acc', _⟩ => return acc'
  else
    return acc
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, lowerBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]
where finally
  case hle =>
    refine ⟨1, ?_⟩
    simpa [predMany?_one] using hs

private theorem Iterator.instIteratorLoop.loop_eq_wf [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α] [Monad n] [LawfulMonad n]
    {γ SmallEnough hl lowerBound} {next hn} {acc} (Pl wf f) :
    loop γ Pl SmallEnough hl lowerBound acc next hn f =
      loop.wf (α := α) (n := n) γ Pl wf SmallEnough hl lowerBound acc next hn f := by
  haveI : Nonempty γ := ⟨acc⟩
  rw [loop, WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · exact InvImage.wf _ wf
  · fun_induction loop.wf γ Pl wf SmallEnough hl lowerBound acc next hn f
    · rw [WellFounded.fix_eq]
      simp only [↓reduceDIte, *]
      apply bind_congr; intro forInStep
      split
      · simp only
        split
        · simp_all
        · simp
      · simp
    · rw [WellFounded.fix_eq]
      simp_all

private theorem Iterator.instIteratorLoop.loopWf_eq [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] (γ : Type u)
    {lift} [instLawfulMonadLiftFunction : Std.Internal.LawfulMonadLiftBindFunction (m := Id) (n := n) lift]
    (Pl : α → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (Rox.Iterator α) Id Pl)
    (SmallEnough : α → Prop) (hl : ∀ a b : α, DownwardEnumerable.LE a b → SmallEnough b → SmallEnough a)
    (lowerBound : α) (acc : γ) (next : α) (h : SmallEnough next)
    (f : (out : α) → SmallEnough out → lowerBound < out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s))) :
    loop.wf γ Pl wf SmallEnough hl lowerBound acc next h f = (do
      if hu : lowerBound < next then
        match ← f next h hu acc with
        | ⟨.yield acc', _⟩ =>
          letI it' : IterM (α := Rox.Iterator α) Id α := ⟨⟨pred? next, lowerBound⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) (n := n) lift γ Pl it' acc'
            it'.IsPlausibleIndirectOutput (fun _ => id)
            fun next' h acc' => f next'
              (by
                refine hl next' next ?_ ‹_›
                simp only [it', Monadic.isPlausibleIndirectOutput_iff,
                  ← predMany?_add_one_eq_pred?_bind_predMany?] at h
                exact ⟨h.choose + 1, h.choose_spec.1⟩)
              (by
                simp only [it', Monadic.isPlausibleIndirectOutput_iff] at h
                exact h.choose_spec.2)
              acc'
        | ⟨.done acc', _⟩ => return acc'
      else return acc) := by
  haveI : Nonempty γ := ⟨acc⟩
  rw [loop.wf]
  congr 1; ext hu
  apply bind_congr; intro forInStep
  split
  · split
    · rw [loopWf_eq (lift := lift) _ Pl wf]
      rw [IterM.DefaultConsumers.forIn'_eq_match_step (lift := lift) Pl wf]; rotate_left
      · simp only [IterM.step_eq, Monadic.step,
          Shrink.inflate_deflate, instLawfulMonadLiftFunction.liftBind_pure, *]
        split
        · apply bind_congr; intro forInStep
          split
          · apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf <;> (intros; rfl)
          · simp
        · simp
    · rw [IterM.DefaultConsumers.forIn'_eq_match_step Pl wf]
      simp [IterM.step_eq, Monadic.step, instLawfulMonadLiftFunction.liftBind_pure, *]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next, lowerBound⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulIteratorLoop [DownwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulDownwardEnumerable α] [LawfulDownwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (Rox.Iterator α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction γ it init Pl wf f
    simp only [IteratorLoop.forIn, IterM.DefaultConsumers.forIn'_eq_wf Pl wf]
    rw [IterM.DefaultConsumers.forIn'.wf]
    split; rotate_left
    · simp [IterM.step_eq, Monadic.step, Internal.LawfulMonadLiftBindFunction.liftBind_pure (liftBind := lift)]
    rename_i next _
    rw [instIteratorLoop.loop_eq_wf Pl wf, instIteratorLoop.loopWf_eq (lift := lift)]
    simp only [IterM.step_eq, Monadic.step, instLawfulMonadLiftFunction.liftBind_pure,
      Shrink.inflate_deflate]
    split
    · apply bind_congr; intro forInStep
      split
      · simp only
        rw [← IterM.DefaultConsumers.forIn'_eq_wf Pl wf _]
        apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf <;> all_goals (intros; rfl)
      · simp
    · simp

end IteratorLoop

end Rox

namespace Rix

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
def Iterator.Monadic.step [DownwardEnumerable α]
    (it : IterM (α := Rix.Iterator α) Id α) :
    IterStep (IterM (α := Rix.Iterator α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some next => .yield ⟨⟨DownwardEnumerable.pred? next⟩⟩ next

/--
The pure function mapping a range iterator of type {name}`Iter` to the next step of the iterator.
-/
@[always_inline, inline]
def Iterator.step [DownwardEnumerable α]
    (it : Iter (α := Rix.Iterator α) α) :
    IterStep (Iter (α := Rix.Iterator α) α) α :=
  match it.internalState.next with
  | none => .done
  | some next => .yield ⟨⟨DownwardEnumerable.pred? next⟩⟩ next

theorem Iterator.step_eq_monadicStep [DownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} :
    Iterator.step it = (Iterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split <;> rfl

@[always_inline, inline]
instance [DownwardEnumerable α] :
    Iterator (Rix.Iterator α) Id α where
  IsPlausibleStep it step := step = Iterator.Monadic.step it
  step it := pure (.deflate ⟨Iterator.Monadic.step it, rfl⟩)

theorem Iterator.Monadic.isPlausibleStep_iff [DownwardEnumerable α]
    {it : IterM (α := Rix.Iterator α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = Iterator.Monadic.step it := by
  exact Iff.rfl

theorem Iterator.Monadic.step_eq_step [DownwardEnumerable α]
    {it : IterM (α := Rix.Iterator α) Id α} :
    it.step = pure (.deflate ⟨Iterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩) := by
  simp [IterM.step, Std.Iterator.step]

theorem Iterator.isPlausibleStep_iff [DownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} {step} :
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

theorem Iterator.step_eq_step [DownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} :
    it.step = ⟨Iterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step, step_eq_monadicStep, Monadic.step_eq_step, IterM.Step.toPure]

theorem Iterator.Monadic.isPlausibleOutput_next {a} [DownwardEnumerable α]
    {it : IterM (α := Rix.Iterator α) Id α} (h : it.internalState.next = some a) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, Monadic.step, h]

theorem Iterator.Monadic.isPlausibleOutput_iff
    [DownwardEnumerable α]
    {it : IterM (α := Rix.Iterator α) Id α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a := by
  simp [IterM.IsPlausibleOutput, isPlausibleStep_iff, Monadic.step]
  split
  · simp [*]
  · simp_all [eq_comm (a := a)]

theorem Iterator.isPlausibleOutput_next
    [DownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} (h : it.internalState.next = some a) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h]

theorem Iterator.isPlausibleOutput_iff
    [DownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem Iterator.Monadic.isPlausibleSuccessorOf_iff
    [DownwardEnumerable α]
    {it' it : IterM (α := Rix.Iterator α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        DownwardEnumerable.pred? a = it'.internalState.next := by
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
      IterStep.yield.injEq, and_true, instIteratorIteratorIdOfDownwardEnumerable] -- TODO
    simp [h']

theorem Iterator.isPlausibleSuccessorOf_iff
    [DownwardEnumerable α]
    {it' it : Iter (α := Rix.Iterator α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        DownwardEnumerable.pred? a = it'.internalState.next := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem Iterator.isSome_next_of_isPlausibleIndirectOutput
    [DownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} {out : α} (h : it.IsPlausibleIndirectOutput out) :
    it.internalState.next.isSome := by
  cases h
  case direct h =>
    rw [isPlausibleOutput_iff] at h
    simp [h]
  case indirect h _ =>
    rw [isPlausibleSuccessorOf_iff] at h
    obtain ⟨a, ha, _⟩ := h
    simp [ha]

private def Iterator.instFinitenessRelation [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [Rix.IsAlwaysFiniteRev α] :
    FinitenessRelation (Rix.Iterator α) Id where
  Rel it' it := it'.IsPlausibleSuccessorOf it
  wf := by
    constructor
    intro it
    have hnone : Acc (fun it' it : IterM (α := Rix.Iterator α) Id α => it'.IsPlausibleSuccessorOf it)
        ⟨⟨none⟩⟩ := by
      constructor
      intro it' ⟨step, hs₁, hs₂⟩
      simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Monadic.step, instIteratorIteratorIdOfDownwardEnumerable] at hs₂ -- TODO
      simp [hs₂, IterStep.successor] at hs₁
    simp only [IterM.IsPlausibleSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      Monadic.step, exists_eq_right, instIteratorIteratorIdOfDownwardEnumerable] at hnone ⊢ -- TODO
    match it with
    | ⟨⟨none⟩⟩ => apply hnone
    | ⟨⟨some init⟩⟩ =>
      obtain ⟨n, hn⟩ := Rix.IsAlwaysFiniteRev.finite init
      induction n generalizing init with
      | zero => simp [predMany?_zero] at hn
      | succ n ih =>
        constructor
        rintro it'
        simp only [predMany?_add_one_eq_pred?_bind_predMany?] at hn
        match hs : pred? init with
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

instance Iterator.instFinite [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [Rix.IsAlwaysFiniteRev α] :
    Finite (Rix.Iterator α) Id :=
  .of_finitenessRelation instFinitenessRelation

private def Iterator.instProductivenessRelation [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] :
    ProductivenessRelation (Rix.Iterator α) Id where
  Rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by
    exfalso
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep,
      Iterator.IsPlausibleStep, Monadic.step, instIteratorIteratorIdOfDownwardEnumerable] at h -- TODO
    split at h <;> cases h

instance Iterator.instProductive [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] :
    Productive (Rix.Iterator α) Id :=
  .of_productivenessRelation instProductivenessRelation

instance Iterator.instIteratorAccess [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] :
    IteratorAccess (Rix.Iterator α) Id where
  nextAtIdx? it n := ⟨match it.internalState.next.bind (DownwardEnumerable.predMany? n) with
    | none => .done
    | some next =>
        .yield ⟨⟨DownwardEnumerable.pred? next⟩⟩ next, (by
      induction n generalizing it
      · split <;> rename_i heq
        · apply IterM.IsPlausibleNthOutputStep.done
          simp only [Monadic.isPlausibleStep_iff, Monadic.step]
          simp only [Option.bind_eq_none_iff, predMany?_zero, reduceCtorEq,
            imp_false] at heq
          cases heq' : it.internalState.next
          · simp
          · rw [heq'] at heq
            exfalso
            exact heq _ rfl
        · cases heq' : it.internalState.next
          · simp [heq'] at heq
          simp only [heq', Option.bind_some, predMany?_zero, Option.some.injEq] at heq
          cases heq
          · apply IterM.IsPlausibleNthOutputStep.zero_yield
            simp [Monadic.isPlausibleStep_iff, Monadic.step, heq']
      · rename_i n ih
        split <;> rename_i heq
        · cases heq' : it.internalState.next
          · apply IterM.IsPlausibleNthOutputStep.done
            simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq']
          · rename_i out
            simp only [heq', Option.bind_some, predMany?_add_one_eq_pred?_bind_predMany?] at heq
            specialize ih ⟨⟨DownwardEnumerable.pred? out⟩⟩
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
          have hlt : DownwardEnumerable.LT _ out := ⟨n, heq⟩
          simp only [predMany?_add_one_eq_pred?_bind_predMany?] at heq
          specialize ih ⟨⟨DownwardEnumerable.pred? out⟩⟩
          simp only [heq] at ih
          · apply IterM.IsPlausibleNthOutputStep.yield
            · simp only [Monadic.isPlausibleStep_iff, Monadic.step, heq',
              IterStep.yield.injEq]
              exact ⟨rfl, rfl⟩
            · apply ih)⟩

instance Iterator.instLawfulDeterministicIterator [DownwardEnumerable α] :
    LawfulDeterministicIterator (Rix.Iterator α) Id where
  isPlausibleStep_eq_eq it := ⟨Monadic.step it, rfl⟩

theorem Iterator.Monadic.isPlausibleIndirectOutput_iff
    [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {it : IterM (α := Rix.Iterator α) Id α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (predMany? n ·) = some out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Monadic.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulDownwardEnumerable.predMany?_zero]⟩
    case indirect h _ ih =>
      rw [Monadic.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, predMany?_add_one_eq_pred?_bind_predMany?, hn, h]
  · rintro ⟨n, hn⟩
    induction n generalizing it
    case zero =>
      apply IterM.IsPlausibleIndirectOutput.direct
      rw [Monadic.isPlausibleOutput_iff]
      simpa [LawfulDownwardEnumerable.predMany?_zero] using hn
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp only [hn', Option.bind_some] at hn
      have hlt : DownwardEnumerable.LT out a := ⟨_, hn⟩
      rw [predMany?_add_one_eq_pred?_bind_predMany?] at hn
      cases hn' : pred? a
      · simp only [hn', Option.bind_none, reduceCtorEq] at hn
      rename_i a'
      simp only [hn', Option.bind_some] at hn
      specialize ih (it := ⟨⟨some a'⟩⟩) hn
      refine IterM.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Monadic.isPlausibleSuccessorOf_iff]
      exact ⟨a, ‹_›, hn'⟩

theorem Iterator.isPlausibleIndirectOutput_iff
    [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {it : Iter (α := Rix.Iterator α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (predMany? n ·) = some out := by
  simp only [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM,
    Monadic.isPlausibleIndirectOutput_iff, Iter.toIterM]

section IteratorLoop

/--
An efficient {name}`IteratorLoop` instance:
As long as the compiler cannot optimize away the {name}`Option` in the internal state, we use a special
loop implementation.
-/
@[always_inline, inline]
instance Iterator.instIteratorLoop [DownwardEnumerable α] [LawfulDownwardEnumerable α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (Rix.Iterator α) Id n where
  forIn _ γ Pl it init f :=
    match it with
    | ⟨⟨some next⟩⟩ =>
      loop γ Pl (DownwardEnumerable.LE · next) (fun a b hab hna => ?hle) init next ?hle'' (fun a ha c => f a ?hf c)
    | ⟨⟨none⟩⟩ => return init
  where
    @[always_inline, inline]
    loop γ (Pl : α → γ → ForInStep γ → Prop) (SmallEnough : α → Prop) (hl : ∀ a b : α, DownwardEnumerable.LE a b → SmallEnough b → SmallEnough a)
        (acc : γ) (next : α) (h : SmallEnough next)
        (f : (out : α) → SmallEnough out → (c : γ) → n (Subtype (Pl out c))) : n γ :=
      haveI : Nonempty γ := ⟨acc⟩
      WellFounded.extrinsicFix₃ (C₃ := fun _ _ _ => n γ) (InvImage (IteratorLoop.rel _ Id Pl) (fun x => (⟨Rix.Iterator.mk (some x.1)⟩, x.2.1)))
        (fun next acc (h : SmallEnough next) G => do
          match ← f next h acc with
          | ⟨.yield acc', h'⟩ =>
            match hs : DownwardEnumerable.pred? next with
            | some next' => G next' acc' (hl _ _ ?hle' h) ?decreasing
            | none => return acc'
          | ⟨.done acc', _⟩ => return acc') next acc h
  finally
    case hf =>
      rw [Monadic.isPlausibleIndirectOutput_iff]
      exact ha
    case hle =>
      exact DownwardEnumerable.le_trans hab hna
    case hle' =>
      refine ⟨1, ?_⟩
      simpa [predMany?_one] using hs
    case hle'' =>
      exact DownwardEnumerable.le_refl _
    case decreasing =>
      simp_wf; simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

private noncomputable def Iterator.instIteratorLoop.loop.wf [DownwardEnumerable α]
    [LawfulDownwardEnumerable α]
    {n : Type u → Type w} [Monad n] (γ : Type u)
    (Pl : α → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (Rix.Iterator α) Id Pl)
    (SmallEnough : α → Prop) (hl : ∀ a b : α, DownwardEnumerable.LE a b → SmallEnough b → SmallEnough a)
    (acc : γ) (next : α) (h : SmallEnough next)
    (f : (out : α) → SmallEnough out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s))) :
    n γ := do
    match ← f next h acc with
    | ⟨.yield acc', _⟩ =>
      match hs : DownwardEnumerable.pred? next with
      | some next' =>
        loop.wf γ Pl wf SmallEnough hl acc' next' (hl _ _ ?hle h) f
      | none => return acc'
    | ⟨.done acc', _⟩ => return acc'
termination_by IteratorLoop.WithWF.mk ⟨⟨some next⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]
where finally
  case hle =>
    refine ⟨1, ?_⟩
    simpa [predMany?_one] using hs

private theorem Iterator.instIteratorLoop.loop_eq_wf [DownwardEnumerable α]
    [LawfulDownwardEnumerable α] [Monad n] [LawfulMonad n]
    {γ SmallEnough hl} {next hn} {acc} (Pl wf f) :
    loop γ Pl SmallEnough hl acc next hn f =
      loop.wf (α := α) (n := n) γ Pl wf SmallEnough hl acc next hn f := by
  haveI : Nonempty γ := ⟨acc⟩
  rw [loop, WellFounded.extrinsicFix₃_eq_fix]; rotate_left
  · exact InvImage.wf _ wf
  · fun_induction loop.wf γ Pl wf SmallEnough hl acc next hn f
    · rw [WellFounded.fix_eq]
      apply bind_congr; intro forInStep
      split
      · simp only
        split
        · simp_all
        · simp
      · simp

private theorem Iterator.instIteratorLoop.loopWf_eq [DownwardEnumerable α]
    [LawfulDownwardEnumerable α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] (γ : Type u)
    {lift} [instLawfulMonadLiftFunction : Std.Internal.LawfulMonadLiftBindFunction (m := Id) (n := n) lift]
    (Pl : α → γ → ForInStep γ → Prop)
    (wf : IteratorLoop.WellFounded (Rix.Iterator α) Id Pl)
    (SmallEnough : α → Prop) (hl : ∀ a b : α, DownwardEnumerable.LE a b → SmallEnough b → SmallEnough a)
    (acc : γ) (next : α) (h : SmallEnough next)
    (f : (out : α) → SmallEnough out → (c : γ) → n (Subtype (fun s : ForInStep γ => Pl out c s))) :
    loop.wf γ Pl wf SmallEnough hl acc next h f = (do
        match ← f next h acc with
        | ⟨.yield acc', _⟩ =>
          letI it' : IterM (α := Rix.Iterator α) Id α := ⟨⟨pred? next⟩⟩
          IterM.DefaultConsumers.forIn' (m := Id) (n := n) lift γ Pl it' acc'
            it'.IsPlausibleIndirectOutput (fun _ => id)
            fun next' h acc' => f next'
              (by
                refine hl next' next ?_ ‹_›
                simp only [it', Monadic.isPlausibleIndirectOutput_iff,
                  ← predMany?_add_one_eq_pred?_bind_predMany?] at h
                exact ⟨h.choose + 1, h.choose_spec⟩)
              acc'
        | ⟨.done acc', _⟩ => return acc') := by
  haveI : Nonempty γ := ⟨acc⟩
  rw [loop.wf]
  apply bind_congr; intro forInStep
  split
  · split
    · rw [loopWf_eq (lift := lift) _ Pl wf]
      rw [IterM.DefaultConsumers.forIn'_eq_match_step (lift := lift) Pl wf]; rotate_left
      · simp only [Monadic.step_eq_step, Monadic.step,
          Shrink.inflate_deflate, instLawfulMonadLiftFunction.liftBind_pure, *]
        apply bind_congr; intro forInStep
        split
        · apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf <;> (intros; rfl)
        · simp
    · rw [IterM.DefaultConsumers.forIn'_eq_match_step Pl wf]
      simp [Monadic.step_eq_step, Monadic.step, instLawfulMonadLiftFunction.liftBind_pure, *]
  · simp
termination_by IteratorLoop.WithWF.mk ⟨⟨some next⟩⟩ acc (hwf := wf)
decreasing_by
  simp [IteratorLoop.rel, Monadic.isPlausibleStep_iff, Monadic.step, *]

instance Iterator.instLawfulIteratorLoop [DownwardEnumerable α]
    [LawfulDownwardEnumerable α]
    {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulIteratorLoop (Rix.Iterator α) Id n where
  lawful := by
    intro lift instLawfulMonadLiftFunction γ it init Pl wf f
    simp only [IteratorLoop.forIn, IterM.DefaultConsumers.forIn'_eq_wf Pl wf]
    rw [IterM.DefaultConsumers.forIn'.wf]
    split; rotate_left
    · simp [Monadic.step_eq_step, Monadic.step, Internal.LawfulMonadLiftBindFunction.liftBind_pure]
    rename_i next _
    rw [instIteratorLoop.loop_eq_wf Pl wf, instIteratorLoop.loopWf_eq (lift := lift)]
    simp only [Monadic.step_eq_step, Monadic.step, instLawfulMonadLiftFunction.liftBind_pure,
      Shrink.inflate_deflate]
    apply bind_congr; intro forInStep
    split
    · simp only
      rw [← IterM.DefaultConsumers.forIn'_eq_wf Pl wf _]
      apply IterM.DefaultConsumers.forIn'_eq_forIn' Pl wf <;> all_goals (intros; rfl)
    · simp

end IteratorLoop

end Rix

end Std
