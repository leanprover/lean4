/-
Copyright (c) 2026 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp, Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Scan
public import Init.Data.Iterators.Consumers.Monadic.Collect
public import Init.Data.List.Scan.Basic
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
import Init.Data.Iterators.Lemmas.Monadic.Basic
import Init.Data.List.Scan.Lemmas
import Init.Data.Bool

public section

namespace Std
open Std.Internal Std.Iterators Std.Iterators.Types

theorem IterM.InternalCombinators.step_scanM
    {f : γ → β → PostconditionT n γ} [Iterator α m β] [MonadLiftT m n] [Monad n]
    {it : IterM (α := α) m β} {acc : γ} {yieldAcc : Bool} :
    (IterM.InternalCombinators.scanM f acc yieldAcc it).step = (do
        if h : yieldAcc = true then
          return .deflate <| .yield
            (IterM.InternalCombinators.scanM f acc false it)
            acc
            (.yieldAcc (by simp [IterM.InternalCombinators.scanM, h]))
        else
          match (← it.step).inflate with
          | .yield it' b hp => do
            let ⟨newAcc, h_acc⟩ ← (f acc b).operation
            return .deflate <| .yield
              (IterM.InternalCombinators.scanM f newAcc false it')
              newAcc
              (.yieldNext (by simp [IterM.InternalCombinators.scanM, h]) hp h_acc)
          | .skip it' hp =>
            return .deflate <| .skip
              (IterM.InternalCombinators.scanM f acc false it')
              (.skip (by simp [IterM.InternalCombinators.scanM, h]) hp)
          | .done hp =>
            return .deflate <|
              .done (.done (by simp [IterM.InternalCombinators.scanM, h]) hp)) := by
  simp only [IterM.InternalCombinators.scanM, IterM.step_eq]
  cases h : yieldAcc
  case true => rfl
  case false =>
    apply bind_congr
    intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> simp

private theorem IterM.toList_scanWithPostCondition_afterInit
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : IterM (α := α) Id β) :
    IterM.toList (IterM.InternalCombinators.scanM (m := Id) f init false it) =
      return ((← it.toList.run.scanlM (f · · |>.run) init).tail) := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs =>
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [IterM.InternalCombinators.step_scanM, ↓reduceDIte, Bool.false_eq_true]
  simp only [monadLift, liftM, PostconditionT.run_eq_map] at *
  match hstep : it.step.run.inflate with
  | ⟨.yield inner' out, hp⟩ =>
    simp only [bind_pure_comp, pure_bind, hstep, bind_map_left, Shrink.inflate_deflate, Id.run_bind,
      Id.run_map, List.scanlM_cons, map_bind, ihy hp]
    simp +singlePass only [← List.scanlM_cons_head_tail]
    simp
  | ⟨.skip inner, hp⟩ => simp_all
  | ⟨.done, x⟩ => simp_all

private theorem IterM.toList_scan_afterInit
    [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) m β) :
    IterM.toList (IterM.InternalCombinators.scanM (pure <| f · ·) init false it) =
      (List.scanl f init · |>.tail) <$> it.toList := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs =>
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [IterM.InternalCombinators.step_scanM, ↓reduceDIte, Bool.false_eq_true]
  simp only [monadLift, liftM] at *
  simp only [bind_assoc, map_eq_pure_bind]
  apply bind_congr; intro step
  match step.inflate with
  | ⟨.yield inner' out, hp⟩ =>
    simp only [PostconditionT.operation_pure, bind_pure_comp, map_pure,
      pure_bind, Shrink.inflate_deflate, ihy hp, Functor.map_map, List.scanl_cons, List.tail_cons]
    simp +singlePass only [← List.scanl_cons_head_tail]
    simp
  | ⟨.skip inner, hp⟩ => simp_all
  | ⟨.done, x⟩ => simp_all

@[simp]
theorem IterM.toList_scanWithPostCondition [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : γ → β → PostconditionT m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanWithPostcondition f init).toList = it.toList.run.scanlM (f · · |>.run) init := by
  unfold IterM.scanWithPostcondition
  rw [IterM.toList_eq_match_step, IterM.InternalCombinators.step_scanM]
  simp only [↓reduceDIte, pure_bind, Shrink.inflate_deflate]
  rw [toList_scanWithPostCondition_afterInit, ← List.scanlM_cons_head_tail]
  simp

@[simp]
theorem IterM.toList_scanM [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id] {f : γ → β → m γ} {init : γ} (it : IterM (α := α) Id β) :
    (it.scanM f init).toList = it.toList.run.scanlM f init := by
  simp [IterM.scanM, PostconditionT.run_attachLift]

@[simp]
theorem IterM.toList_scan [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m]
    {f : γ → β → γ} {init : γ} (it : IterM (α := α) m β) :
    (it.scan f init).toList = List.scanl f init <$> it.toList := by
  rw [scan, scanWithPostcondition]
  rw [IterM.toList_eq_match_step, IterM.InternalCombinators.step_scanM]
  simp only [↓reduceDIte, pure_bind, Shrink.inflate_deflate,
    toList_scan_afterInit, bind_pure_comp, Functor.map_map]
  congr 1; apply funext
  simp +singlePass +eta only [← List.scanl_cons_head_tail]
  simp

end Std
