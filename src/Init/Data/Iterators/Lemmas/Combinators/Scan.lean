/-
Copyright (c) 2026 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp, Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Scan
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.List.Scan.Basic
import Init.Data.Iterators.Lemmas.Combinators.Monadic.Scan

public section

namespace Std
open Std.Iterators Std.Iterators.Types

variable {α β γ : Type w} [Iterator α Id β] {it : Iter (α := α) β}

theorem Iter.Intermediate.step_scanM [Monad m] [LawfulMonad m]
    {f : γ → β → PostconditionT m γ} {acc : γ} {yieldAcc : Bool} :
    (IterM.Intermediate.scanM f acc yieldAcc it.toIterM).step = (do
        if h : yieldAcc = true then
          return .deflate <| .yield
            (IterM.Intermediate.scanM f acc false it.toIterM)
            acc
            (.yieldAcc (by simp [IterM.Intermediate.scanM, h]))
        else
          match it.step with
          | .yield it' b hp => do
            let ⟨newAcc, h_acc⟩ ← (f acc b).operation
            return .deflate <| .yield
              (IterM.Intermediate.scanM f newAcc false it'.toIterM)
              newAcc
              (.yieldNext (by simp [IterM.Intermediate.scanM, h]) hp h_acc)
          | .skip it' hp =>
            return .deflate <| .skip
              (IterM.Intermediate.scanM f acc false it'.toIterM)
              (.skip (by simp [IterM.Intermediate.scanM, h]) hp)
          | .done hp =>
            return .deflate <|
              .done (.done (by simp [IterM.Intermediate.scanM, h]) hp)) := by
  simp only [IterM.Intermediate.step_scanM]
  cases h : yieldAcc
  case true => rfl
  case false =>
    simp only [monadLift, liftM, pure_bind, Iter.step]
    cases it.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;> simp

@[simp]
theorem Iter.toList_scanWithPostcondition [Monad m] [LawfulMonad m] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} :
    (it.scanWithPostcondition f init).toList = it.toList.scanlM (f · · |>.run) init := by
  simp [Iter.scanWithPostcondition, Iter.toList, Id.run]

@[simp]
theorem Iter.toList_scanM
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Finite α Id] {f : γ → β → m γ} {init : γ} :
    (it.scanM f init).toList = it.toList.scanlM f init := by
  simp [Iter.scanM, Iter.toList, Id.run]

@[simp]
theorem Iter.toList_scan [Finite α Id] {f : γ → β → γ} {init : γ} :
    (it.scan f init).toList = List.scanl f init it.toList := by
  simp only [scan, IterM.toList_toIter, IterM.toList_scan]
  rfl

end Std
