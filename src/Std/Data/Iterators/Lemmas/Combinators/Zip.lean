/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Take
import Std.Data.Iterators.Combinators.Zip
import Init.Data.Iterators.Consumers.Access
import Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip
import Std.Data.Iterators.Lemmas.Combinators.Take
import Init.Data.Iterators.Lemmas.Consumers

namespace Std.Iterators

variable {α₁ α₂ β₁ β₂ : Type w} {m : Type w → Type w'}

/--
Constructs intermediate states of an iterator created with the combinator `Iter.zip`.
When `left.zip right` has already obtained a value from `left` but not yet from right,
it remembers `left`'s value in a field of its internal state. This intermediate state
cannot be created directly with `Iter.zip`.

`Intermediate.zip` is meant to be used only for verification purposes.
-/
noncomputable def Iter.Intermediate.zip [Iterator α₁ Id β₁]
    (it₁ : Iter (α := α₁) β₁)
    (memo : (Option { out : β₁ //
        ∃ it : Iter (α := α₁) β₁, it.toIterM.IsPlausibleOutput out }))
    (it₂ : Iter (α := α₂) β₂) :
    Iter (α := Zip α₁ Id α₂ β₂) (β₁ × β₂) :=
  (IterM.Intermediate.zip
    it₁.toIterM
    ((fun x => ⟨x.1, x.2.choose.toIterM, x.2.choose_spec⟩) <$> memo)
    it₂.toIterM).toIter

def Iter.Intermediate.zip_inj [Iterator α₁ Id β₁] :
    ∀ {it₁ it₁' : Iter (α := α₁) β₁} {memo memo'} {it₂ it₂' : Iter (α := α₂) β₂},
      zip it₁ memo it₂ = zip it₁' memo' it₂' ↔ it₁ = it₁' ∧ memo = memo' ∧ it₂ = it₂' := by
  intro it₁ it₁' memo memo' it₂ it₂'
  apply Iff.intro
  · intro h
    cases it₁; cases it₁'; cases it₂; cases it₂'
    obtain _ | ⟨⟨_⟩⟩ := memo <;> obtain _ | ⟨⟨_⟩⟩ := memo' <;>
      simp_all [toIterM, IterM.toIter, zip, IterM.Intermediate.zip, Option.map_eq_map]
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def Iter.Intermediate.zip_surj [Iterator α₁ Id β₁] :
    ∀ it : Iter (α := Zip α₁ Id α₂ β₂) (β₁ × β₂), ∃ it₁ memo it₂, it = Intermediate.zip it₁ memo it₂ := by
  refine fun it => ⟨it.internalState.left.toIter,
      (fun x => ⟨x.1, x.2.choose.toIter, x.2.choose_spec⟩) <$> it.internalState.memoizedLeft,
      it.internalState.right.toIter, ?_⟩
  simp only [zip, toIterM_toIter, Option.map_eq_map, Option.map_map]
  change it = (IterM.Intermediate.zip _ (Option.map id it.internalState.memoizedLeft) it.internalState.right).toIter
  simp only [Option.map_id_fun, id_eq]
  rfl

theorem Iter.zip_eq_intermediateZip [Iterator α₁ Id β₁]
    [Iterator α₂ Id β₂]
    (it₁ : Iter (α := α₁) β₁) (it₂ : Iter (α := α₂) β₂) :
    it₁.zip it₂ = Intermediate.zip it₁ none it₂ := by
  rfl

theorem Iter.step_intermediateZip
    [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁}
    {memo : Option { out : β₁ //
        ∃ it : Iter (α := α₁) β₁, it.toIterM.IsPlausibleOutput out }}
    {it₂ : Iter (α := α₂) β₂} :
    (Intermediate.zip it₁ memo it₂).step = (
      match memo with
      | none =>
        match it₁.step with
        | .yield it₁' out hp =>
          .skip (Intermediate.zip it₁' (some ⟨out, _, _, hp⟩) it₂)
            (.yieldLeft rfl hp)
        | .skip it₁' hp =>
          .skip (Intermediate.zip it₁' none it₂)
            (.skipLeft rfl hp)
        | .done hp =>
          .done (.doneLeft rfl hp)
      | some out₁ =>
        match it₂.step with
        | .yield it₂' out₂ hp =>
          .yield (Intermediate.zip it₁ none it₂') (out₁, out₂)
            (.yieldRight (it := Intermediate.zip it₁ (some out₁) it₂ |>.toIterM) rfl hp)
        | .skip it₂' hp =>
          .skip (Intermediate.zip it₁ (some out₁) it₂')
            (.skipRight rfl hp)
        | .done hp =>
          .done (.doneRight rfl hp)) := by
  simp only [Intermediate.zip, IterM.step_intermediateZip, Iter.step, toIterM_toIter]
  cases memo
  case none =>
    simp only [Option.map_eq_map, Option.map_none, PlausibleIterStep.skip, PlausibleIterStep.done,
      Id.run_bind, Option.map_some]
    obtain ⟨step, h⟩ := it₁.toIterM.step.run
    cases step <;> simp
  case some out₁ =>
    simp only [Option.map_eq_map, Option.map_some, PlausibleIterStep.yield, PlausibleIterStep.skip,
      PlausibleIterStep.done, Id.run_bind, Option.map_none]
    obtain ⟨step, h⟩ := it₂.toIterM.step.run
    cases step <;> simp

theorem Iter.toList_intermediateZip_of_finite [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {memo} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Finite α₂ Id]
    [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (Intermediate.zip it₁ memo it₂).toList = ((memo.map Subtype.val).toList ++ it₁.toList).zip it₂.toList := by
  generalize h : Intermediate.zip it₁ memo it₂ = it
  revert h it₁ memo it₂
  induction it using Iter.inductSteps with | step _ ihy ihs
  rintro it₁ memo it₂ rfl
  rw [Iter.toList_eq_match_step]
  match hs : (Intermediate.zip it₁ memo it₂).step with
  | .yield it' out hp =>
    rw [step_intermediateZip] at hs
    cases memo
    case none =>
      generalize it₁.step = step₁ at *
      obtain ⟨step₁, h₁⟩ := step₁
      cases step₁ <;> cases hs
    case some =>
      rw [Iter.toList_eq_match_step (it := it₂)]
      generalize it₂.step = step₂ at *
      obtain ⟨step₂, h₂⟩ := step₂
      cases step₂
      · cases hs
        simp [ihy hp rfl]
      · cases hs
      · cases hs
  | .skip it' hp =>
    rw [step_intermediateZip] at hs
    cases memo
    case none =>
      rw [Iter.toList_eq_match_step (it := it₁)]
      generalize it₁.step = step₁ at *
      obtain ⟨step₁, h₁⟩ := step₁
      cases step₁
      · cases hs
        simp [ihs hp rfl]
      · cases hs
        simp [ihs hp rfl]
      · cases hs
    case some =>
      rw [Iter.toList_eq_match_step (it := it₂)]
      generalize it₂.step = step₂ at *
      obtain ⟨step₂, h₂⟩ := step₂
      cases step₂
      · cases hs
      · cases hs
        simp [ihs hp rfl]
      · cases hs
  | .done hp =>
    rw [step_intermediateZip] at hs
    cases memo
    case none =>
      rw [Iter.toList_eq_match_step (it := it₁)]
      generalize it₁.step = step₁ at *
      obtain ⟨step₁, h₁⟩ := step₁
      cases step₁
      · cases hs
      · cases hs
      · cases hs
        simp
    case some =>
      rw [Iter.toList_eq_match_step (it := it₂)]
      generalize it₂.step = step₂ at *
      obtain ⟨step₂, h₁⟩ := step₂
      cases step₂
      · cases hs
      · cases hs
      · cases hs
        simp

theorem Iter.atIdxSlow?_intermediateZip [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β₁} {memo} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    (Intermediate.zip it₁ memo it₂).atIdxSlow? n =
      (match memo with
      | none => do return (← it₁.atIdxSlow? n, ← it₂.atIdxSlow? n)
      | some memo => match n with
        | 0 => do return (memo.val, ← it₂.atIdxSlow? n)
        | n' + 1 => do return (← it₁.atIdxSlow? n', ← it₂.atIdxSlow? (n' + 1))) := by
  generalize h : Intermediate.zip it₁ memo it₂ = it
  revert h it₁ memo it₂
  fun_induction it.atIdxSlow? n
  rintro it₁ memo it₂ rfl
  case case1 it it' out h h' =>
    rw [atIdxSlow?]
    simp only [Option.pure_def, Option.bind_eq_bind]
    simp only [step_intermediateZip, PlausibleIterStep.skip, PlausibleIterStep.done,
      PlausibleIterStep.yield] at h'
    split at h'
    · split at h' <;> cases h'
    · split at h' <;> cases h'
      rename_i hs₂
      rw [atIdxSlow?, hs₂]
      simp
  case case2 it it' out h  h' n ih =>
    rintro it₁ memo it₂ rfl
    simp only [Nat.succ_eq_add_one, Option.pure_def, Option.bind_eq_bind]
    cases memo
    case none =>
      rw [step_intermediateZip] at h'
      simp only at h'
      split at h' <;> cases h'
    case some =>
      rw [step_intermediateZip] at h'
      simp only at h'
      split at h' <;> cases h'
      rename_i hs₂
      simp only [ih rfl, Option.pure_def, Option.bind_eq_bind]
      rw [atIdxSlow?.eq_def (it := it₂), hs₂]
  case case3 it it' h h' ih =>
    rintro it₁ memo it₂ rfl
    obtain ⟨it₁', memo', it₂', rfl⟩ := Intermediate.zip_surj it'
    specialize ih rfl
    rw [step_intermediateZip] at h'
    simp only [PlausibleIterStep.skip, PlausibleIterStep.done, PlausibleIterStep.yield] at h'
    rw [Subtype.ext_iff] at h'
    split at h'
    · split at h' <;> rename_i hs₁
      · simp only [IterStep.skip.injEq, Intermediate.zip_inj] at h'
        obtain ⟨rfl, rfl, rfl⟩ := h'
        simp only [ih, Option.pure_def, Option.bind_eq_bind, atIdxSlow?.eq_def (it := it₁), hs₁]
        split <;> rfl
      · simp only [IterStep.skip.injEq, Intermediate.zip_inj] at h'
        obtain ⟨rfl, rfl, rfl⟩ := h'
        simp [ih, atIdxSlow?.eq_def (it := it₁), hs₁]
      · cases h'
    · split at h' <;> rename_i hs₂ <;> (try cases h')
      simp only [IterStep.skip.injEq, Intermediate.zip_inj] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      simp [ih, atIdxSlow?.eq_def (it := it₂), hs₂]
  case case4 it _ h =>
    rintro it₁ memo it₂ rfl
    rw [atIdxSlow?]
    simp only [step_intermediateZip] at h
    cases memo
    case none =>
      simp only at h
      split at h <;> cases h
      rename_i hs₁
      simp [hs₁]
    case some =>
      simp only at h
      split at h <;> cases h
      rename_i hs₂
      simp only [atIdxSlow?.eq_def (it := it₂), hs₂, Option.pure_def, Option.bind_eq_bind,
        Option.bind_none, Option.bind_fun_none]
      split <;> rfl

theorem Iter.atIdxSlow?_zip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    (it₁.zip it₂).atIdxSlow? n = do return (← it₁.atIdxSlow? n, ← it₂.atIdxSlow? n) := by
  rw [zip_eq_intermediateZip, atIdxSlow?_intermediateZip]

@[simp]
theorem Iter.toList_zip_of_finite {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Finite α₂ Id]
    [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toList = it₁.toList.zip it₂.toList := by
  simp [zip_eq_intermediateZip, Iter.toList_intermediateZip_of_finite]

theorem Iter.toList_zip_of_finite_left {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Productive α₂ Id] [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toList = it₁.toList.zip (it₂.take it₁.toList.length).toList := by
  ext
  simp only [List.getElem?_zip_eq_some, getElem?_toList_eq_atIdxSlow?, atIdxSlow?_zip, Option.pure_def, Option.bind_eq_bind,
    atIdxSlow?_take, Option.ite_none_right_eq_some]
  constructor
  · intro h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
    refine ⟨hb₁, ?_, hb₂⟩
    false_or_by_contra
    rw [← getElem?_toList_eq_atIdxSlow?] at hb₁
    rename_i h
    simp only [Nat.not_lt, ← List.getElem?_eq_none_iff, hb₁] at h
    cases h
  · rintro ⟨h₁, h₂, h₃⟩
    simp [h₁, h₃]

theorem Iter.toList_zip_of_finite_right {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Productive α₁ Id] [Finite α₂ Id] [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toList = (it₁.take it₂.toList.length).toList.zip it₂.toList := by
  ext
  simp only [List.getElem?_zip_eq_some, getElem?_toList_eq_atIdxSlow?, atIdxSlow?_zip, Option.pure_def, Option.bind_eq_bind,
    atIdxSlow?_take, Option.ite_none_right_eq_some]
  constructor
  · intro h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
    refine ⟨⟨?_, hb₁⟩, hb₂⟩
    false_or_by_contra
    rw [← getElem?_toList_eq_atIdxSlow?] at hb₂
    rename_i h
    simp only [Nat.not_lt, ← List.getElem?_eq_none_iff, hb₂] at h
    cases h
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    simp [h₂, h₃]

@[simp]
theorem Iter.toListRev_zip_of_finite {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Finite α₂ Id]
    [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toListRev = (it₁.toList.zip it₂.toList).reverse := by
  simp [toListRev_eq]

theorem Iter.toListRev_zip_of_finite_left {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Productive α₂ Id] [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toListRev = (it₁.toList.zip (it₂.take it₁.toList.length).toList).reverse := by
  simp [toListRev_eq, toList_zip_of_finite_left]

theorem Iter.toListRev_zip_of_finite_right {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Productive α₁ Id] [Finite α₂ Id] [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toListRev = ((it₁.take it₂.toList.length).toList.zip it₂.toList).reverse := by
  simp [toListRev_eq, toList_zip_of_finite_right]

@[simp]
theorem Iter.toArray_zip_of_finite {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Finite α₂ Id]
    [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toArray = it₁.toArray.zip it₂.toArray := by
  simp [← toArray_toList]

theorem Iter.toArray_zip_of_finite_left {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Productive α₂ Id] [IteratorCollect α₁ Id Id] [LawfulIteratorCollect α₁ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toArray = it₁.toArray.zip (it₂.take it₁.toArray.size).toArray := by
  simp [← toArray_toList, toList_zip_of_finite_left]

theorem Iter.toArray_zip_of_finite_right {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Productive α₁ Id] [Finite α₂ Id] [IteratorCollect α₂ Id Id] [LawfulIteratorCollect α₂ Id Id]
    [IteratorCollect (Zip α₁ Id α₂ β₂) Id Id]
    [LawfulIteratorCollect (Zip α₁ Id α₂ β₂) Id Id] :
    (it₁.zip it₂).toArray = (it₁.take it₂.toArray.size).toArray.zip it₂.toArray := by
  simp [← toArray_toList, toList_zip_of_finite_right]

@[simp]
theorem Iter.toList_take_zip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    ((it₁.zip it₂).take n).toList = (it₁.take n).toList.zip (it₂.take n).toList := by
  rw [← toList_zip_of_finite]
  apply toList_eq_of_atIdxSlow?_eq
  intro k
  simp only [atIdxSlow?_take, atIdxSlow?_zip, Option.pure_def, Option.bind_eq_bind]
  split <;> rfl

@[simp]
theorem Iter.toListRev_take_zip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    ((it₁.zip it₂).take n).toListRev = ((it₁.take n).toList.zip (it₂.take n).toList).reverse := by
  simp [toListRev_eq]

@[simp]
theorem Iter.toArray_take_zip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    ((it₁.zip it₂).take n).toArray = ((it₁.take n).toList.zip (it₂.take n).toList).toArray := by
  simp [← toArray_toList]

end Iterators
