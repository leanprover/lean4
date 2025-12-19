/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap

public import Init.Data.Iterators.Combinators.Monadic.FlatMap
import all Init.Data.Iterators.Combinators.Monadic.FlatMap

namespace Std
open Std.Internal Std.Iterators

theorem IterM.step_flattenAfter {α α₂ β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    {it₁ : IterM (α := α) m (IterM (α := α₂) m β)} {it₂ : Option (IterM (α := α₂) m β)} :
  (it₁.flattenAfter it₂).step = (do
    match it₂ with
    | none =>
      match (← it₁.step).inflate with
      | .yield it₁' it₂' h => return .deflate (.skip (it₁'.flattenAfter (some it₂')) (.outerYield h))
      | .skip it₁' h => return .deflate (.skip (it₁'.flattenAfter none) (.outerSkip h))
      | .done h => return .deflate (.done (.outerDone h))
    | some it₂ =>
      match (← it₂.step).inflate with
      | .yield it₂' out h => return .deflate (.yield (it₁.flattenAfter (some it₂')) out (.innerYield h))
      | .skip it₂' h => return .deflate (.skip (it₁.flattenAfter (some it₂')) (.innerSkip h))
      | .done h => return .deflate (.skip (it₁.flattenAfter none) (.innerDone h))) := by
  cases it₂
  all_goals
  · apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> simp [IterM.flattenAfter, IterM.mk]

namespace Iterators.Types

public theorem Flatten.IsPlausibleStep.outerYield_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ it₁' : IterM (α := α) m β} {it₂' b}
    (h : it₁.IsPlausibleStep (.yield it₁' b)) (h' : MonadAttach.CanReturn (f b) it₂') :
    (it₁.flatMapAfterM f none).IsPlausibleStep (.skip (it₁'.flatMapAfterM f (some it₂'))) :=
  .outerYield (.yieldSome h ⟨⟨_, h'⟩, rfl⟩)

public theorem Flatten.IsPlausibleStep.outerSkip_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it₁ it₁' : IterM (α := α) m β}
    (h : it₁.IsPlausibleStep (.skip it₁')) :
    (it₁.flatMapAfterM f none).IsPlausibleStep (.skip (it₁'.flatMapAfterM f none)) :=
  .outerSkip (.skip h)

public theorem Flatten.IsPlausibleStep.outerDone_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it₁ : IterM (α := α) m β}
    (h : it₁.IsPlausibleStep .done) :
    (it₁.flatMapAfterM f none).IsPlausibleStep .done :=
  .outerDone (.done h)

public theorem Flatten.IsPlausibleStep.innerYield_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it₁ : IterM (α := α) m β} {it₂ it₂' b}
    (h : it₂.IsPlausibleStep (.yield it₂' b)) :
    (it₁.flatMapAfterM f (some it₂)).IsPlausibleStep (.yield (it₁.flatMapAfterM f (some it₂')) b) :=
  .innerYield h

public theorem Flatten.IsPlausibleStep.innerSkip_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it₁ : IterM (α := α) m β} {it₂ it₂'}
    (h : it₂.IsPlausibleStep (.skip it₂')) :
    (it₁.flatMapAfterM f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfterM f (some it₂'))) :=
  .innerSkip h

public theorem Flatten.IsPlausibleStep.innerDone_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β]
    [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it₁ : IterM (α := α) m β} {it₂}
    (h : it₂.IsPlausibleStep .done) :
    (it₁.flatMapAfterM f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfterM f none)) :=
  .innerDone h

public theorem Flatten.IsPlausibleStep.outerYield_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ it₁' : IterM (α := α) m β} {b}
    (h : it₁.IsPlausibleStep (.yield it₁' b)) :
    (it₁.flatMapAfter f none).IsPlausibleStep (.skip (it₁'.flatMapAfter f (some (f b)))) :=
  .outerYield (.yieldSome h ⟨⟨_, rfl⟩, rfl⟩)

public theorem Flatten.IsPlausibleStep.outerSkip_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ it₁' : IterM (α := α) m β}
    (h : it₁.IsPlausibleStep (.skip it₁')) :
    (it₁.flatMapAfter f none).IsPlausibleStep (.skip (it₁'.flatMapAfter f none)) :=
  .outerSkip (.skip h)

public theorem Flatten.IsPlausibleStep.outerDone_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β}
    (h : it₁.IsPlausibleStep .done) :
    (it₁.flatMapAfter f none).IsPlausibleStep .done :=
  .outerDone (.done h)

public theorem Flatten.IsPlausibleStep.innerYield_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} {it₂ it₂' b}
    (h : it₂.IsPlausibleStep (.yield it₂' b)) :
    (it₁.flatMapAfter f (some it₂)).IsPlausibleStep (.yield (it₁.flatMapAfter f (some it₂')) b) :=
  .innerYield h

public theorem Flatten.IsPlausibleStep.innerSkip_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} {it₂ it₂'}
    (h : it₂.IsPlausibleStep (.skip it₂')) :
    (it₁.flatMapAfter f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfter f (some it₂'))) :=
  .innerSkip h

public theorem Flatten.IsPlausibleStep.innerDone_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} {it₂}
    (h : it₂.IsPlausibleStep .done) :
    (it₁.flatMapAfter f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfter f none)) :=
  .innerDone h

end Iterators.Types

public theorem IterM.step_flatMapAfterM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)} {it₁ : IterM (α := α) m β}
    {it₂ : Option (IterM (α := α₂) m γ)} :
  (it₁.flatMapAfterM f it₂).step = (do
    match it₂ with
    | none =>
      match (← it₁.step).inflate with
      | .yield it₁' b h =>
        let fx ← MonadAttach.attach (f b)
        return .deflate (.skip (it₁'.flatMapAfterM f (some fx.val)) (.outerYield_flatMapM h fx.property))
      | .skip it₁' h => return .deflate (.skip (it₁'.flatMapAfterM f none) (.outerSkip_flatMapM h))
      | .done h => return .deflate (.done (.outerDone_flatMapM h))
    | some it₂ =>
      match (← it₂.step).inflate with
      | .yield it₂' out h => return .deflate (.yield (it₁.flatMapAfterM f (some it₂')) out (.innerYield_flatMapM h))
      | .skip it₂' h => return .deflate (.skip (it₁.flatMapAfterM f (some it₂')) (.innerSkip_flatMapM h))
      | .done h => return .deflate (.skip (it₁.flatMapAfterM f none) (.innerDone_flatMapM h))) := by
  simp only [flatMapAfterM, step_flattenAfter, IterM.step_mapM]
  split
  · simp only [bind_assoc]
    apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only [bind_pure_comp, bind_map_left, Shrink.inflate_deflate]
    · simp
    · simp
  · rfl

public theorem IterM.step_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m]
    [WeaklyLawfulMonadAttach m] [Iterator α m β] [Iterator α₂ m γ] {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : IterM (α := α) m β} :
  (it₁.flatMapM f).step = (do
    match (← it₁.step).inflate with
    | .yield it₁' b h =>
      let fx ← MonadAttach.attach (f b)
      return .deflate (.skip (it₁'.flatMapAfterM f (some fx.val))
        (.outerYield_flatMapM h fx.property))
    | .skip it₁' h => return .deflate (.skip (it₁'.flatMapAfterM f none) (.outerSkip_flatMapM h))
    | .done h => return .deflate (.done (.outerDone_flatMapM h))) := by
  simp [flatMapM, step_flatMapAfterM]

public theorem IterM.step_flatMapAfter {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
  (it₁.flatMapAfter f it₂).step = (do
    match it₂ with
    | none =>
      match (← it₁.step).inflate with
      | .yield it₁' b h =>
        return .deflate (.skip (it₁'.flatMapAfter f (some (f b))) (.outerYield_flatMap h))
      | .skip it₁' h => return .deflate (.skip (it₁'.flatMapAfter f none) (.outerSkip_flatMap h))
      | .done h => return .deflate (.done (.outerDone_flatMap h))
    | some it₂ =>
      match (← it₂.step).inflate with
      | .yield it₂' out h => return .deflate (.yield (it₁.flatMapAfter f (some it₂')) out (.innerYield_flatMap h))
      | .skip it₂' h => return .deflate (.skip (it₁.flatMapAfter f (some it₂')) (.innerSkip_flatMap h))
      | .done h => return .deflate (.skip (it₁.flatMapAfter f none) (.innerDone_flatMap h))) := by
  simp only [flatMapAfter, step_flattenAfter, IterM.step_map]
  split
  · simp only [bind_assoc]
    apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> simp
  · rfl

public theorem IterM.step_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} :
  (it₁.flatMap f).step = (do
    match (← it₁.step).inflate with
    | .yield it₁' b h =>
      return .deflate (.skip (it₁'.flatMapAfter f (some (f b))) (.outerYield_flatMap h))
    | .skip it₁' h => return .deflate (.skip (it₁'.flatMapAfter f none) (.outerSkip_flatMap h))
    | .done h => return .deflate (.done (.outerDone_flatMap h))) := by
  simp [flatMap, step_flatMapAfter]

theorem IterM.toList_flattenAfter {α α₂ β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] [Finite α m] [Finite α₂ m]
    {it₁ : IterM (α := α) m (IterM (α := α₂) m β)} {it₂ : Option (IterM (α := α₂) m β)} :
    (it₁.flattenAfter it₂).toList = do
      match it₂ with
      | none => List.flatten <$> (it₁.mapM fun it₂ => it₂.toList).toList
      | some it₂ => return (← it₂.toList) ++ (← List.flatten <$> (it₁.mapM fun it₂ => it₂.toList).toList) := by
  induction it₁ using IterM.inductSteps generalizing it₂ with | step it₁ ihy₁ ihs₁ =>
  have hn : (it₁.flattenAfter none).toList =
      List.flatten <$> (it₁.mapM fun it₂ => it₂.toList).toList := by
    rw [toList_eq_match_step, toList_eq_match_step, step_flattenAfter, step_mapM]
    simp only [bind_assoc, map_eq_pure_bind]
    apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only [bind_pure_comp, pure_bind, Shrink.inflate_deflate,
        bind_map_left, Functor.map_map, List.flatten_cons, ihy₁ ‹_›]
      conv => lhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := IterM.toList _)]
      simp
    · simp [ihs₁ ‹_›]
    · simp
  cases it₂
  · exact hn
  · rename_i ih₂
    induction ih₂ using IterM.inductSteps with | step it₂ ihy₂ ihs₂ =>
    rw [toList_eq_match_step, step_flattenAfter, bind_assoc]
    simp only
    rw [toList_eq_match_step, bind_assoc]
    apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp [ihy₂ ‹_›]
    · simp [ihs₂ ‹_›]
    · simp [hn]

theorem IterM.toArray_flattenAfter {α α₂ β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] [Finite α m] [Finite α₂ m]
    {it₁ : IterM (α := α) m (IterM (α := α₂) m β)} {it₂ : Option (IterM (α := α₂) m β)} :
    (it₁.flattenAfter it₂).toArray = do
      match it₂ with
      | none => Array.flatten <$> (it₁.mapM fun it₂ => it₂.toArray).toArray
      | some it₂ => return (← it₂.toArray) ++ (← Array.flatten <$> (it₁.mapM fun it₂ => it₂.toArray).toArray) := by
  simp only [← IterM.toArray_toList, toList_flattenAfter]
  split
  · simp only [Functor.map_map]
    simp only [← Array.flatten_map_toArray_toArray, ← Functor.map_map]
    rw [IterM.toArray_toList, IterM.toArray_toList, ← IterM.toArray_map, IterM.toArray_map_mapM]
    apply congrArg (it₁.mapM · |>.toArray |> Functor.map Array.flatten); ext it₂
    simp
  · simp only [bind_pure_comp, Functor.map_map, map_bind, Array.flatten_toArray, bind_map_left,
      List.append_toArray]
    apply bind_congr; intro bs
    simp only [← Functor.map_map, ← IterM.toList_map, IterM.toList_map_mapM]
    apply congrArg (fun f => List.toArray <$> HAppend.hAppend bs <$> List.flatten <$> (mapM f it₁).toList)
    simp

public theorem IterM.toList_flatMapAfterM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfterM f it₂).toList = do
      match it₂ with
      | none => List.flatten <$> (it₁.mapM fun b => do (← f b).toList).toList
      | some it₂ => return (← it₂.toList) ++
          (← List.flatten <$> (it₁.mapM fun b => do (← f b).toList).toList) := by
  simp [flatMapAfterM, toList_flattenAfter]; rfl

public theorem IterM.toArray_flatMapAfterM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfterM f it₂).toArray = do
      match it₂ with
      | none => Array.flatten <$> (it₁.mapM fun b => do (← f b).toArray).toArray
      | some it₂ => return (← it₂.toArray) ++
          (← Array.flatten <$> (it₁.mapM fun b => do (← f b).toArray).toArray) := by
  simp [flatMapAfterM, toArray_flattenAfter]; rfl

public theorem IterM.toList_flatMapM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : IterM (α := α) m β} :
    (it₁.flatMapM f).toList = List.flatten <$> (it₁.mapM fun b => do (← f b).toList).toList := by
  simp [flatMapM, toList_flatMapAfterM]

public theorem IterM.toArray_flatMapM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : IterM (α := α) m β} :
    (it₁.flatMapM f).toArray = Array.flatten <$> (it₁.mapM fun b => do (← f b).toArray).toArray := by
  simp [flatMapM, toArray_flatMapAfterM]

public theorem IterM.toList_flatMapAfter {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → IterM (α := α₂) m γ}
    {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfter f it₂).toList = do
      match it₂ with
      | none => List.flatten <$> (it₁.mapM fun b => (f b).toList).toList
      | some it₂ => return (← it₂.toList) ++
          (← List.flatten <$> (it₁.mapM fun b => (f b).toList).toList) := by
  simp [flatMapAfter, toList_flattenAfter]; rfl

public theorem IterM.toArray_flatMapAfter {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → IterM (α := α₂) m γ}
    {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfter f it₂).toArray = do
      match it₂ with
      | none => Array.flatten <$> (it₁.mapM fun b => (f b).toArray).toArray
      | some it₂ => return (← it₂.toArray) ++
          (← Array.flatten <$> (it₁.mapM fun b => (f b).toArray).toArray) := by
  simp [flatMapAfter, toArray_flattenAfter]; rfl

public theorem IterM.toList_flatMap {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → IterM (α := α₂) m γ}
    {it₁ : IterM (α := α) m β} :
    (it₁.flatMap f).toList = List.flatten <$> (it₁.mapM fun b => (f b).toList).toList := by
  simp [flatMap, toList_flatMapAfter]

public theorem IterM.toArray_flatMap {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {f : β → IterM (α := α₂) m γ}
    {it₁ : IterM (α := α) m β} :
    (it₁.flatMap f).toArray = Array.flatten <$> (it₁.mapM fun b => (f b).toArray).toArray := by
  simp [flatMap, toArray_flatMapAfter]

end Std
