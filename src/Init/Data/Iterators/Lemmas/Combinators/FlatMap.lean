/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Iterators.Combinators.FlatMap
import all Init.Data.Iterators.Combinators.FlatMap
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap
import Init.Control.Lawful.MonadAttach.Lemmas

namespace Std
open Std.Internal Std.Iterators

namespace Iterators.Types

public theorem Flatten.IsPlausibleStep.outerYield_flatMapM_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [Iterator α Id β]
    [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ it₁' : Iter (α := α) β} {it₂' b}
    (h : it₁.IsPlausibleStep (.yield it₁' b)) (h' : MonadAttach.CanReturn (f b) it₂') :
    (it₁.flatMapAfterM f none).IsPlausibleStep (.skip (it₁'.flatMapAfterM f (some it₂'))) := by
  apply outerYield_flatMapM (b := b)
  · exact FilterMap.PlausibleStep.yieldSome h (by simp)
  · exact h'

public theorem Flatten.IsPlausibleStep.outerSkip_flatMapM_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ it₁' : Iter (α := α) β}
    (h : it₁.IsPlausibleStep (.skip it₁')) :
    (it₁.flatMapAfterM f none).IsPlausibleStep (.skip (it₁'.flatMapAfterM f none)) :=
  outerSkip_flatMapM (.skip h)

public theorem Flatten.IsPlausibleStep.outerDone_flatMapM_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ : Iter (α := α) β}
    (h : it₁.IsPlausibleStep .done) :
    (it₁.flatMapAfterM f none).IsPlausibleStep .done :=
  outerDone_flatMapM (.done h)

public theorem Flatten.IsPlausibleStep.innerYield_flatMapM_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ : Iter (α := α) β} {it₂ it₂' b}
    (h : it₂.IsPlausibleStep (.yield it₂' b)) :
    (it₁.flatMapAfterM f (some it₂)).IsPlausibleStep (.yield (it₁.flatMapAfterM f (some it₂')) b) :=
  innerYield_flatMapM h

public theorem Flatten.IsPlausibleStep.innerSkip_flatMapM_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ : Iter (α := α) β} {it₂ it₂'}
    (h : it₂.IsPlausibleStep (.skip it₂')) :
    (it₁.flatMapAfterM f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfterM f (some it₂'))) :=
  innerSkip_flatMapM h

public theorem Flatten.IsPlausibleStep.innerDone_flatMapM_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ : Iter (α := α) β} {it₂}
    (h : it₂.IsPlausibleStep .done) :
    (it₁.flatMapAfterM f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfterM f none)) :=
  innerDone_flatMapM h

public theorem Flatten.IsPlausibleStep.outerYield_flatMap_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ it₁' : Iter (α := α) β} {b}
    (h : it₁.IsPlausibleStep (.yield it₁' b)) :
    (it₁.flatMapAfter f none).IsPlausibleStep (.skip (it₁'.flatMapAfter f (some (f b)))) :=
  outerYield_flatMap h

public theorem Flatten.IsPlausibleStep.outerSkip_flatMap_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ it₁' : Iter (α := α) β}
    (h : it₁.IsPlausibleStep (.skip it₁')) :
    (it₁.flatMapAfter f none).IsPlausibleStep (.skip (it₁'.flatMapAfter f none)) :=
  outerSkip_flatMap h

public theorem Flatten.IsPlausibleStep.outerDone_flatMap_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w}  [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β}
    (h : it₁.IsPlausibleStep .done) :
    (it₁.flatMapAfter f none).IsPlausibleStep .done :=
  outerDone_flatMap h

public theorem Flatten.IsPlausibleStep.innerYield_flatMap_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂ it₂' b}
    (h : it₂.IsPlausibleStep (.yield it₂' b)) :
    (it₁.flatMapAfter f (some it₂)).IsPlausibleStep (.yield (it₁.flatMapAfter f (some it₂')) b) :=
  innerYield_flatMap h

public theorem Flatten.IsPlausibleStep.innerSkip_flatMap_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂ it₂'}
    (h : it₂.IsPlausibleStep (.skip it₂')) :
    (it₁.flatMapAfter f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfter f (some it₂'))) :=
  innerSkip_flatMap h

public theorem Flatten.IsPlausibleStep.innerDone_flatMap_pure {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂}
    (h : it₂.IsPlausibleStep .done) :
    (it₁.flatMapAfter f (some it₂)).IsPlausibleStep (.skip (it₁.flatMapAfter f none)) :=
  innerDone_flatMap h

end Iterators.Types

public theorem Iter.step_flatMapAfterM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ : Iter (α := α) β} {it₂ : Option (IterM (α := α₂) m γ)} :
  (it₁.flatMapAfterM f it₂).step = (do
    match it₂ with
    | none =>
      match it₁.step with
      | .yield it₁' b h =>
        let fx ← MonadAttach.attach (f b)
        return .deflate (.skip (it₁'.flatMapAfterM f (some fx.val)) (.outerYield_flatMapM_pure h fx.property))
      | .skip it₁' h => return .deflate (.skip (it₁'.flatMapAfterM f none) (.outerSkip_flatMapM_pure h))
      | .done h => return .deflate (.done (.outerDone_flatMapM_pure h))
    | some it₂ =>
      match (← it₂.step).inflate with
      | .yield it₂' out h =>
        return .deflate (.yield (it₁.flatMapAfterM f (some it₂')) out (.innerYield_flatMapM_pure h))
      | .skip it₂' h =>
        return .deflate (.skip (it₁.flatMapAfterM f (some it₂')) (.innerSkip_flatMapM_pure h))
      | .done h =>
        return .deflate (.skip (it₁.flatMapAfterM f none) (.innerDone_flatMapM_pure h))) := by
  simp only [flatMapAfterM, IterM.step_flatMapAfterM, Iter.step_mapWithPostcondition,
    PostconditionT.operation_pure]
  split
  · split <;> simp [*]
  · rfl

public theorem Iter.step_flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Iterator α₂ m γ]
    {f : β → m (IterM (α := α₂) m γ)} {it₁ : Iter (α := α) β} :
  (it₁.flatMapM f).step = (do
    match it₁.step with
    | .yield it₁' b h =>
      let fx ← MonadAttach.attach (f b)
      return .deflate (.skip (it₁'.flatMapAfterM f (some fx.val)) (.outerYield_flatMapM_pure h fx.property))
    | .skip it₁' h => return .deflate (.skip (it₁'.flatMapAfterM f none) (.outerSkip_flatMapM_pure h))
    | .done h => return .deflate (.done (.outerDone_flatMapM_pure h))) := by
  simp [flatMapM, step_flatMapAfterM]

public theorem Iter.step_flatMapAfter {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂ : Option (Iter (α := α₂) γ)} :
  (it₁.flatMapAfter f it₂).step = (match it₂ with
    | none =>
      match it₁.step with
      | .yield it₁' b h =>
        .skip (it₁'.flatMapAfter f (some (f b))) (.outerYield_flatMap_pure h)
      | .skip it₁' h => .skip (it₁'.flatMapAfter f none) (.outerSkip_flatMap_pure h)
      | .done h => .done (.outerDone_flatMap_pure h)
    | some it₂ =>
      match it₂.step with
      | .yield it₂' out h => .yield (it₁.flatMapAfter f (some it₂')) out (.innerYield_flatMap_pure h)
      | .skip it₂' h => .skip (it₁.flatMapAfter f (some it₂')) (.innerSkip_flatMap_pure h)
      | .done h => .skip (it₁.flatMapAfter f none) (.innerDone_flatMap_pure h)) := by
  simp only [flatMapAfter, step, toIterM_toIter, IterM.step_flatMapAfter]
  cases it₂
  · simp only [Option.map_eq_map, Option.map_none, Id.run_bind, Option.map_some]
    cases it₁.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;> simp
  · rename_i it₂
    simp only [Option.map_eq_map, Option.map_some, Id.run_bind, Option.map_none]
    cases it₂.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;> simp

public theorem Iter.step_flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} :
  (it₁.flatMap f).step = (match it₁.step with
    | .yield it₁' b h =>
      .skip (it₁'.flatMapAfter f (some (f b))) (.outerYield_flatMap_pure h)
    | .skip it₁' h => .skip (it₁'.flatMapAfter f none) (.outerSkip_flatMap_pure h)
    | .done h => .done (.outerDone_flatMap_pure h)) := by
  simp [flatMap, step_flatMapAfter]

public theorem Iter.toList_flatMapAfterM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Iterator α₂ m γ] [Finite α Id] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : Iter (α := α) β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfterM f it₂).toList = do
      match it₂ with
      | none => List.flatten <$> (it₁.mapM fun b => do (← f b).toList).toList
      | some it₂ => return (← it₂.toList) ++
          (← List.flatten <$> (it₁.mapM fun b => do (← f b).toList).toList) := by
  simp only [flatMapAfterM, IterM.toList_flatMapAfterM]
  split <;> simp [IterM.toList_mapM_eq_toList_mapWithPostcondition]

public theorem Iter.toArray_flatMapAfterM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Iterator α₂ m γ] [Finite α Id] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : Iter (α := α) β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfterM f it₂).toArray = do
      match it₂ with
      | none => Array.flatten <$> (it₁.mapM fun b => do (← f b).toArray).toArray
      | some it₂ => return (← it₂.toArray) ++
          (← Array.flatten <$> (it₁.mapM fun b => do (← f b).toArray).toArray) := by
  simp only [flatMapAfterM, IterM.toArray_flatMapAfterM]
  split <;> simp [IterM.toArray_mapM_eq_toArray_mapWithPostcondition]

public theorem Iter.toList_flatMapM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Iterator α₂ m γ] [Finite α Id] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : Iter (α := α) β} :
    (it₁.flatMapM f).toList = List.flatten <$> (it₁.mapM fun b => do (← f b).toList).toList := by
  simp [flatMapM, toList_flatMapAfterM]

public theorem Iter.toArray_flatMapM {α α₂ β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Iterator α₂ m γ] [Finite α Id] [Finite α₂ m]
    {f : β → m (IterM (α := α₂) m γ)}
    {it₁ : Iter (α := α) β} :
    (it₁.flatMapM f).toArray = Array.flatten <$> (it₁.mapM fun b => do (← f b).toArray).toArray := by
  simp [flatMapM, toArray_flatMapAfterM]

public theorem Iter.toList_flatMapAfter {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂ : Option (Iter (α := α₂) γ)} :
    (it₁.flatMapAfter f it₂).toList = match it₂ with
      | none => (it₁.map fun b => (f b).toList).toList.flatten
      | some it₂ => it₂.toList ++
          (it₁.map fun b => (f b).toList).toList.flatten := by
  simp only [flatMapAfter, Iter.toList, toIterM_toIter, IterM.toList_flatMapAfter]
  cases it₂ <;> simp [map, IterM.toList_map_eq_toList_mapM, - IterM.toList_map]

public theorem Iter.toArray_flatMapAfter {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} {it₂ : Option (Iter (α := α₂) γ)} :
    (it₁.flatMapAfter f it₂).toArray = match it₂ with
      | none => (it₁.map fun b => (f b).toArray).toArray.flatten
      | some it₂ => it₂.toArray ++
          (it₁.map fun b => (f b).toArray).toArray.flatten := by
  simp only [flatMapAfter, Iter.toArray, toIterM_toIter, IterM.toArray_flatMapAfter]
  cases it₂ <;> simp [map, IterM.toArray_map_eq_toArray_mapM, - IterM.toArray_map]

public theorem Iter.toList_flatMap {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id]
    [Iterator α Id β] [Iterator α₂ Id γ] [Finite α Id] [Finite α₂ Id]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} :
    (it₁.flatMap f).toList = (it₁.map fun b => (f b).toList).toList.flatten := by
  simp [flatMap, toList_flatMapAfter]

public theorem Iter.toArray_flatMap {α α₂ β γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id]
    [Iterator α Id β] [Iterator α₂ Id γ] [Finite α Id] [Finite α₂ Id]
    {f : β → Iter (α := α₂) γ} {it₁ : Iter (α := α) β} :
    (it₁.flatMap f).toArray = (it₁.map fun b => (f b).toArray).toArray.flatten := by
  simp [flatMap, toArray_flatMapAfter]

end Std
