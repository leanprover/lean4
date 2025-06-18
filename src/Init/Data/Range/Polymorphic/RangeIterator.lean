/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Internal.Termination
import Init.Data.Iterators.Consumers.Loop
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Range.Polymorphic.PRange
import Init.Data.List.Sublist

open Std.Iterators

namespace Std.Iterators.Types

@[unbox]
structure RangeIterator (shape : BoundShape) (α : Type u) where
  next : Option α
  upperBound : Bound shape α

variable {α : Type u}

@[always_inline, inline]
def RangeIterator.Monadic.step [UpwardEnumerable α] [SupportsUpperBound su α]
    (it : IterM (α := RangeIterator su α) Id α) :
    IterStep (IterM (α := RangeIterator su α) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
      .yield ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ a
    else
      .done

@[always_inline, inline]
def RangeIterator.step [UpwardEnumerable α] [SupportsUpperBound su α]
    (it : Iter (α := RangeIterator su α) α) :
    IterStep (Iter (α := RangeIterator su α) α) α :=
  match it.internalState.next with
  | none => .done
  | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
      .yield ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ a
    else
      .done

theorem RangeIterator.step_eq_monadicStep [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} :
    RangeIterator.step it = (RangeIterator.Monadic.step it.toIterM).mapIterator IterM.toIter := by
  simp only [step, Monadic.step, Iter.toIterM]
  split
  · rfl
  · split <;> rfl

@[always_inline, inline]
instance [UpwardEnumerable α] [SupportsUpperBound su α] :
    Iterator (RangeIterator su α) Id α where
  IsPlausibleStep it step := step = RangeIterator.Monadic.step it
  step it := pure ⟨RangeIterator.Monadic.step it, rfl⟩

theorem RangeIterator.Monadic.isPlausibleStep_iff [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} {step} :
    it.IsPlausibleStep step ↔ step = RangeIterator.Monadic.step it := by
  exact Iff.rfl

theorem RangeIterator.Monadic.step_eq_step [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} :
    it.step = pure ⟨RangeIterator.Monadic.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [IterM.step, Iterator.step]

theorem RangeIterator.isPlausibleStep_iff [UpwardEnumerable α] [SupportsUpperBound su α]
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

theorem RangeIterator.step_eq_step [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} :
    it.step = ⟨RangeIterator.step it, isPlausibleStep_iff.mpr rfl⟩ := by
  simp [Iter.step, step_eq_monadicStep, Monadic.step_eq_step, IterM.Step.toPure]

@[always_inline, inline]
instance RepeatIterator.instIteratorLoop [UpwardEnumerable α] [SupportsUpperBound su α]
    {n : Type u → Type w} [Monad n] :
    IteratorLoop (RangeIterator su α) Id n :=
  .defaultImplementation
  -- forIn lift γ plausible_forInStep wf it init f :=
  --   let rec @[specialize] loop (a : α) (c : γ) : n γ := do
  --     if P a then
  --       match ← f a sorry c with
  --       | ⟨.yield c', _⟩ => match (instSucc? a) with
  --         | none => pure c'
  --         | some a' => loop a' c'
  --       | ⟨.done c', _⟩ => pure c'
  --     else
  --       return init
  --   termination_by a
  --   decreasing_by all_goals sorry
  --   match it.internalState.next with
  --   | none => pure init
  --   | some a => loop a init

instance RepeatIterator.instIteratorLoopPartial [UpwardEnumerable α] [SupportsUpperBound su α]
    {n : Type u → Type w} [Monad n] : IteratorLoopPartial (RangeIterator su α) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorCollect [UpwardEnumerable α] [SupportsUpperBound su α]
    {n : Type u → Type w} [Monad n] : IteratorCollect (RangeIterator su α) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorCollectPartial [UpwardEnumerable α] [SupportsUpperBound su α]
    {n : Type u → Type w} [Monad n] : IteratorCollectPartial (RangeIterator su α) Id n :=
  .defaultImplementation

-- TODO: very specific performance optimizations if needed

-- abbrev test : ForIn Id (Iter (α := RangeIterator α instSucc? p) α) α :=
--   inferInstance

-- @[always_inline, inline]
-- def test' : ForIn Id.{u} (Iter (α := RangeIterator α instSucc? P) α) α where
--   forIn {γ _} it init f :=
--     let rec @[specialize] loop (a : α) (c : γ) : Id γ := do
--       if P a then
--         match ← f a c with
--         | .yield c' => match instSucc?.succ? a with
--           | none => pure c'
--           | some a' => loop a' c'
--         | .done c' => pure c'
--       else
--         pure c
--     termination_by a
--     decreasing_by all_goals sorry
--     match it.internalState.next with
--     | none => pure init
--     | some a => loop a init

-- @[csimp]
-- theorem aaa : @test = @test' := sorry

-- @[always_inline, inline]
-- instance test'' :
--     ForIn Id.{u} (Iter (α := RangeIterator α instSucc? p) α) α :=
--   test

theorem RangeIterator.Monadic.isPlausibleOutput_next
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : IterM (α := RangeIterator su α) Id α} (h : it.internalState.next = some a)
    (hP : SupportsUpperBound.IsSatisfied it.internalState.upperBound a) :
    it.IsPlausibleOutput a := by
  simp [IterM.IsPlausibleOutput, Monadic.isPlausibleStep_iff, RangeIterator.Monadic.step, h, hP]

theorem RangeIterator.Monadic.isPlausibleOutput_iff
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

theorem RangeIterator.isPlausibleOutput_next
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} (h : it.internalState.next = some a)
    (hP : SupportsUpperBound.IsSatisfied it.internalState.upperBound a) :
    it.IsPlausibleOutput a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM, h, hP]

theorem RangeIterator.isPlausibleOutput_iff
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it : Iter (α := RangeIterator su α) α} :
    it.IsPlausibleOutput a ↔
      it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a := by
  simp [Iter.IsPlausibleOutput, Monadic.isPlausibleOutput_iff, Iter.toIterM]

theorem RangeIterator.Monadic.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it' it : IterM (α := RangeIterator su α) Id α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp [IterM.IsPlausibleSuccessorOf]
  constructor
  · rintro ⟨step, h, h'⟩
    cases h'
    simp only [RangeIterator.Monadic.step] at h
    split at h
    · cases h
    · split at h
      · simp [IterStep.successor] at h
        cases h
        exact ⟨_, ‹_›, ‹_›, rfl, rfl⟩
      · cases h
  · rintro ⟨a, h, hP, h'⟩
    refine ⟨.yield it' a, rfl, ?_⟩
    simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, RangeIterator.Monadic.step, h, hP]
    simp [h'.1, ← h'.2]

theorem RangeIterator.isPlausibleSuccessorOf_iff
    [UpwardEnumerable α] [SupportsUpperBound su α]
    {it' it : Iter (α := RangeIterator su α) α} :
    it'.IsPlausibleSuccessorOf it ↔
      ∃ a, it.internalState.next = some a ∧
        SupportsUpperBound.IsSatisfied it.internalState.upperBound a ∧
        UpwardEnumerable.succ? a = it'.internalState.next ∧
        it'.internalState.upperBound = it.internalState.upperBound := by
  simp [Iter.IsPlausibleSuccessorOf, Monadic.isPlausibleSuccessorOf_iff, Iter.toIterM]

theorem RangeIterator.isSome_next_of_isPlausibleIndirectOutput
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

def RangeIterator.instFinitenessRelation [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] :
    FinitenessRelation (RangeIterator su α) Id where
  rel :=
    open Classical in
    InvImage WellFoundedRelation.rel
      (fun it => (HasFiniteRanges.mem_of_satisfiesUpperBound it.internalState.upperBound).choose
        |>.filter (∃ a, it.internalState.next = some a ∧ UpwardEnumerable.le a ·)
        |>.length)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    rw [Monadic.isPlausibleSuccessorOf_iff] at h
    obtain ⟨a, hn, hu, hn', hu'⟩ := h
    rw [hu']
    apply List.length_filter_strict_mono (a := a)
    · intro u h
      simp only [decide_eq_true_eq] at ⊢ h
      obtain ⟨a', ha', hle⟩ := h
      refine ⟨a, hn, UpwardEnumerable.le_trans ?_ hle⟩
      refine ⟨1, ?_⟩
      rw [ha'] at hn'
      rw [LawfulUpwardEnumerable.succMany?_succ, LawfulUpwardEnumerable.succMany?_zero,
        Option.bind_some, hn']
    · exact (HasFiniteRanges.mem_of_satisfiesUpperBound _).choose_spec _ hu
    · intro h
      simp only [decide_eq_true_eq] at h
      obtain ⟨x, hx, h⟩ := h
      rw [hx] at hn'
      have hlt : UpwardEnumerable.lt a x :=
        ⟨0, by simp [LawfulUpwardEnumerable.succMany?_succ, LawfulUpwardEnumerable.succMany?_zero, hn']⟩
      exact UpwardEnumerable.not_gt_of_le h hlt
    · simp only [decide_eq_true_eq]
      exact ⟨a, hn, UpwardEnumerable.le_refl _⟩

instance RangeIterator.instFinite [UpwardEnumerable α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] :
    Finite (RangeIterator su α) Id :=
  .of_finitenessRelation instFinitenessRelation

end Std.Iterators.Types
