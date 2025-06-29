/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Monadic.DropWhile
import Init.Data.Iterators.Lemmas.Consumers.Monadic

namespace Std.Iterators

theorem IterM.Intermediate.dropWhileM_eq_dropWhileWithPostcondition {α m β} [Monad m]
    [Iterator α m β] {it : IterM (α := α) m β} {P dropping} :
    Intermediate.dropWhileM P dropping it =
      Intermediate.dropWhileWithPostcondition (PostconditionT.lift ∘ P) dropping it :=
  rfl

theorem IterM.Intermediate.dropWhile_eq_dropWhileM {α m β} [Monad m]
    [Iterator α m β] {it : IterM (α := α) m β} {P} :
    Intermediate.dropWhile P dropping it =
      Intermediate.dropWhileM (pure ∘ ULift.up ∘ P) dropping it :=
  rfl

theorem IterM.dropWhileWithPostcondition_eq_intermediateDropWhileWithPostcondition {α m β}
    [Iterator α m β] {it : IterM (α := α) m β} {P} :
    it.dropWhileWithPostcondition P = Intermediate.dropWhileWithPostcondition P true it :=
  rfl

theorem IterM.dropWhileM_eq_intermediateDropWhileM {α m β} [Monad m]
    [Iterator α m β] {it : IterM (α := α) m β} {P} :
    it.dropWhileM P = Intermediate.dropWhileM P true it :=
  rfl

theorem IterM.dropWhile_eq_intermediateDropWhile {α m β} [Monad m]
    [Iterator α m β] {it : IterM (α := α) m β} {P} :
    it.dropWhile P = Intermediate.dropWhile P true it :=
  rfl

theorem IterM.step_intermediateDropWhileWithPostcondition {α m β} [Monad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} {dropping} :
    (IterM.Intermediate.dropWhileWithPostcondition P dropping it).step = (do
    match ← it.step with
    | .yield it' out h =>
      if h' : dropping = true then
        match ← (P out).operation with
        | ⟨.up true, h''⟩ =>
          return .skip (IterM.Intermediate.dropWhileWithPostcondition P true it') (.dropped h h' h'')
        | ⟨.up false, h''⟩ =>
          return .yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out (.start h h' h'')
      else
        return .yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out
            (.yield h (Bool.not_eq_true _ ▸ h'))
    | .skip it' h =>
      return .skip (IterM.Intermediate.dropWhileWithPostcondition P dropping it') (.skip h)
    | .done h =>
      return .done (.done h)) := by
  simp only [step, Iterator.step]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> rfl

theorem IterM.step_dropWhileWithPostcondition {α m β} [Monad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.dropWhileWithPostcondition P).step = (do
    match ← it.step with
    | .yield it' out h =>
        match ← (P out).operation with
        | ⟨.up true, h''⟩ =>
          return .skip (IterM.Intermediate.dropWhileWithPostcondition P true it') (.dropped h rfl h'')
        | ⟨.up false, h''⟩ =>
          return .yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out (.start h rfl h'')
    | .skip it' h =>
      return .skip (IterM.Intermediate.dropWhileWithPostcondition P true it') (.skip h)
    | .done h =>
      return .done (.done h)) := by
  simp [dropWhileWithPostcondition_eq_intermediateDropWhileWithPostcondition, step_intermediateDropWhileWithPostcondition]

theorem IterM.step_intermediateDropWhileM {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} {dropping} :
    (IterM.Intermediate.dropWhileM P dropping it).step = (do
    match ← it.step with
    | .yield it' out h =>
      if h' : dropping = true then
        match ← P out with
        | .up true =>
          return .skip (IterM.Intermediate.dropWhileM P true it') (.dropped h h' True.intro)
        | .up false =>
          return .yield (IterM.Intermediate.dropWhileM P false it') out (.start h h' True.intro)
      else
        return .yield (IterM.Intermediate.dropWhileM P false it') out
            (.yield h (Bool.not_eq_true _ ▸ h'))
    | .skip it' h =>
      return .skip (IterM.Intermediate.dropWhileM P dropping it') (.skip h)
    | .done h =>
      return .done (.done h)) := by
  simp only [Intermediate.dropWhileM_eq_dropWhileWithPostcondition, step_intermediateDropWhileWithPostcondition]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · simp only [Function.comp_apply, PostconditionT.operation_lift, PlausibleIterStep.skip,
    PlausibleIterStep.yield, bind_map_left]
    split
    · apply bind_congr
      rintro ⟨x⟩
      cases x <;> rfl
    · rfl
  · rfl
  · rfl

theorem IterM.step_dropWhileM {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.dropWhileM P).step = (do
    match ← it.step with
    | .yield it' out h =>
      match ← P out with
      | .up true =>
        return .skip (IterM.Intermediate.dropWhileM P true it') (.dropped h rfl True.intro)
      | .up false =>
        return .yield (IterM.Intermediate.dropWhileM P false it') out (.start h rfl True.intro)
    | .skip it' h =>
      return .skip (IterM.Intermediate.dropWhileM P true it') (.skip h)
    | .done h =>
      return .done (.done h)) := by
  simp [dropWhileM_eq_intermediateDropWhileM, step_intermediateDropWhileM]

theorem IterM.step_intermediateDropWhile {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} {dropping} :
    (IterM.Intermediate.dropWhile P dropping it).step = (do
    match ← it.step with
    | .yield it' out h =>
      if h' : dropping = true then
        match P out with
        | true =>
          return .skip (IterM.Intermediate.dropWhile P true it') (.dropped h h' True.intro)
        | false =>
          return .yield (IterM.Intermediate.dropWhile P false it') out (.start h h' True.intro)
      else
        return .yield (IterM.Intermediate.dropWhile P false it') out
            (.yield h (Bool.not_eq_true _ ▸ h'))
    | .skip it' h =>
      return .skip (IterM.Intermediate.dropWhile P dropping it') (.skip h)
    | .done h =>
      return .done (.done h)) := by
  simp only [Intermediate.dropWhile_eq_dropWhileM, step_intermediateDropWhileM]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · simp only [Function.comp_apply, PlausibleIterStep.skip,
    PlausibleIterStep.yield]
    split
    · cases P _ <;> simp
    · rfl
  · rfl
  · rfl

theorem IterM.step_dropWhile {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.dropWhile P).step = (do
    match ← it.step with
    | .yield it' out h =>
        match P out with
        | true =>
          return .skip (IterM.Intermediate.dropWhile P true it') (.dropped h rfl True.intro)
        | false =>
          return .yield (IterM.Intermediate.dropWhile P false it') out (.start h rfl True.intro)
    | .skip it' h =>
      return .skip (IterM.Intermediate.dropWhile P true it') (.skip h)
    | .done h =>
      return .done (.done h)) := by
  simp [dropWhile_eq_intermediateDropWhile, step_intermediateDropWhile]

end Std.Iterators
