/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.FilterMap
public import Init.Data.Iterators.Lemmas.Consumers.Monadic
import all Init.Data.Iterators.Consumers.Monadic.Collect
import Init.Control.Lawful.MonadAttach.Lemmas
import Init.Data.Array.Monadic

public section

namespace Std
open Std.Internal Std.Iterators Std.Iterators.Types

section Step

variable {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  [Iterator α m β] {it : IterM (α := α) m β}

theorem IterM.step_filterMapWithPostcondition {f : β → PostconditionT n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterWithPostcondition {f : β → PostconditionT n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨.up false, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterWithPostcondition f) (.yieldNone (out := out) h ⟨⟨_, h'⟩, rfl⟩)
      | ⟨.up true, h'⟩ =>
        pure <| .deflate <| .yield (it'.filterWithPostcondition f) out (by exact .yieldSome (out := out) h ⟨⟨_, h'⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterWithPostcondition f) (by exact .skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, PlausibleIterStep.skip, PlausibleIterStep.yield,
      bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_mapWithPostcondition {γ : Type w} {f : β → PostconditionT n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      let out' ← (f out).operation
      pure <| .deflate <| .yield (it'.mapWithPostcondition f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMapM {f : β → n (Option β')}
    [Monad n] [MonadAttach n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapM f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← MonadAttach.attach (f out) with
      | ⟨none, hf⟩ =>
        pure <| .deflate <| .skip (it'.filterMapM f) (.yieldNone (out := out) h hf)
      | ⟨some out', hf⟩ =>
        pure <| .deflate <| .yield (it'.filterMapM f) out' (.yieldSome (out := out) h hf)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterM {f : β → n (ULift Bool)}
    [Monad n] [MonadAttach n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterM f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← MonadAttach.attach (f out) with
      | ⟨.up false, hf⟩ =>
        pure <| .deflate <| .skip (it'.filterM f) (.yieldNone (out := out) h ⟨⟨.up false, hf⟩, rfl⟩)
      | ⟨.up true, hf⟩ =>
        pure <| .deflate <| .yield (it'.filterM f) out (.yieldSome (out := out) h ⟨⟨.up true, hf⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, PlausibleIterStep.skip, PlausibleIterStep.yield,
      bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_mapM {γ : Type w} {f : β → n γ}
    [Monad n] [MonadAttach n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapM f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      let out' ← MonadAttach.attach (f out)
      pure <| .deflate <| .yield (it'.mapM f) out'.val (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [bind_pure_comp]
    simp only [PostconditionT.operation_map, PlausibleIterStep.skip,
      PlausibleIterStep.yield, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMap [Monad m] [LawfulMonad m] {f : β → Option β'} :
  (it.filterMap f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match h' : f out with
      | none =>
        pure <| .deflate <| .skip (it'.filterMap f) (.yieldNone h h')
      | some out' =>
        pure <| .deflate <| .yield (it'.filterMap f) out' (.yieldSome h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMap f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [IterM.filterMap, step_filterMapWithPostcondition, pure]
  apply bind_congr
  intro step
  split
  · simp only [PostconditionT.pure, PlausibleIterStep.skip, PlausibleIterStep.yield, pure_bind]
    split <;> split <;> simp_all
  · simp
  · simp

theorem IterM.step_map [Monad m] [LawfulMonad m] {f : β → β'} :
  (it.map f).step = (do
    match (← it.step).inflate with
    | .yield it' out h =>
      let out' := f out
      pure <| .deflate <| .yield (it'.map f) out' (.yieldSome h ⟨⟨out', rfl⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.map f) (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [map, IterM.step_mapWithPostcondition]
  apply bind_congr
  intro step
  split
  · simp
  · rfl
  · rfl

theorem IterM.step_filter [Monad m] [LawfulMonad m] {f : β → Bool} :
  (it.filter f).step = (do
    match (← it.step).inflate with
    | .yield it' out h =>
      if h' : f out = true then
        pure <| .deflate <| .yield (it'.filter f) out (.yieldSome h (by simp [h']))
      else
        pure <| .deflate <| .skip (it'.filter f) (.yieldNone h (by simp [h']))
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filter f) (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [filter, IterM.step_filterMap]
  apply bind_congr
  intro step
  split
  · split
    · split
      · exfalso; simp_all
      · rfl
    · split
      · congr; simp_all
      · exfalso; simp_all
  · rfl
  · rfl

end Step

section ToList

theorem IterM.InternalConsumers.toList_filterMap {α β γ: Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  rw [step_filterMap]
  simp only [bind_assoc, IterM.step, map_eq_pure_bind]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [List.filterMap_cons, bind_assoc, pure_bind]
    split <;> simp (discharger := assumption) [*]
  · simp [ihs ‹_›]
  · simp

namespace Internal

/-- A variant of `Subtype.casesOn` that is not reduced by `simp`. -/
@[elab_as_elim]
private def subtypeCasesOn' := @Subtype.casesOn

private def optionPelim' {α : Type u_1} (t : Option α) {β :  Sort u_2}
    (n : t = none → β) (s : (val : α) → t = some val → β) : β :=
  match t with
  | some a => s a rfl
  | none => n rfl

/--
Inserts an `Option` case distinction after the first computation of a call to `MonadAttach.pbind`.
This lemma is useful for simplifying the second computation, which often involes `match` expressions
that use `pbind`'s proof term.
-/
private theorem pbind_eq_pbind_if_isSome [Monad m] [MonadAttach m] (x : m (Option α)) (f : (_ : _) → _ → m β) :
    MonadAttach.pbind x f = MonadAttach.pbind x
        (fun a ha => optionPelim' a (fun _ => f none (by simp_all)) (fun a _ => f (some a) (by simp_all))) := by
  intros; congr; ext
  simp only [optionPelim']
  split <;> simp

private theorem bind_subtypeCasesOn'_eq_map_bind [Monad m] [LawfulMonad m] {P : α → Prop}
    (x : m (Subtype P)) (f : α → m β) :
    x >>= (fun a => subtypeCasesOn' a fun a _ => f a) = (Subtype.val <$> x) >>= f := by
  simp [subtypeCasesOn']

private theorem bind_eq_bind_subtypeCasesOn'_optionPelim' [Monad m] [LawfulMonad m]
    {P : Option α → Prop} (x : m (Subtype P)) (f : Subtype P → m β) :
    x >>= f = x >>= (fun a => subtypeCasesOn' a fun (a : Option α) ha => optionPelim' a (fun h =>
          f ⟨none, by simp_all⟩) (fun a h => f ⟨some a, by simp_all⟩)) := by
  apply bind_congr; intro x
  rcases x with ⟨_ | ⟨a⟩⟩
  all_goals simp [subtypeCasesOn', optionPelim']

end Internal

open Internal

theorem IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n γ} {it : IterM (α := α) m β} :
    (it.mapWithPostcondition f).toList =
      (it.filterMapWithPostcondition (PostconditionT.map some <| f ·)).toList := by
  rfl

theorem IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {it : IterM (α := α) m β} :
    (it.filterMapM f).toList =
      (it.filterMapWithPostcondition fun b => .attachLift (f b)).toList := by
  rfl

theorem IterM.toList_mapM_eq_toList_mapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toList =
      (it.mapWithPostcondition fun b => .attachLift (f b)).toList := by
  rfl

theorem IterM.toList_mapM_eq_toList_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toList =
      (it.filterMapM fun b => some <$> f b).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step, step_mapM, step_filterMapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · conv =>
      rhs
      simp only [bind_pure_comp, bind_assoc]
      simp only [MonadAttach.attach_bind_eq_pbind]
      rw [pbind_eq_pbind_if_isSome]
    simp [MonadAttach.attach_bind_eq_pbind, WeaklyLawfulMonadAttach.pbind_eq_bind, optionPelim', ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.toList_map_eq_toList_mapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toList = (it.mapM fun b => pure (f b)).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step, step_map, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [PlausibleIterStep.yield, bind_pure_comp, pure_bind, Shrink.inflate_deflate,
      bind_map_left]
    conv => rhs; rhs; ext a; rw [← pure_bind (x := a.val) (f := fun _ => _ <$> _)]
    simp only [← bind_assoc, bind_pure_comp, WeaklyLawfulMonadAttach.map_attach]
    simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.toList_map_eq_toList_filterMapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toList = (it.filterMapM fun b => pure (some (f b))).toList := by
  simp [toList_map_eq_toList_mapM, toList_mapM_eq_toList_filterMapM]
  congr <;> simp

/--
Variant of `toList_filterMapWithPostcondition_filterMapWithPostcondition` that is intended to be
used with the `apply` tactic. Because neither the LHS nor the RHS determine all implicit parameters,
it cannot be used easily with `rw` or `simp`.
-/
private theorem IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'
    {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → PostconditionT o (Option δ)}
    {fg : β → PostconditionT o (Option δ)}
    {it : IterM (α := α) m β}
    (h : ∀ b, (fg b).run = do match ← (f b).run with | none => return none | some fb => (g fb).run) :
    letI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toList =
      (it.filterMapWithPostcondition (n := o) fg).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  letI : MonadLift n o := ⟨monadLift⟩
  haveI : LawfulMonadLift n o := ⟨by simp [this], by simp [this]⟩
  rw [toList_eq_match_step, toList_eq_match_step, step_filterMapWithPostcondition,
    bind_assoc, step_filterMapWithPostcondition, step_filterMapWithPostcondition]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_bind]
    rw [PostconditionT.operation_eq_map_mk_operation, liftM_map, bind_map_left]
    simp
    conv =>
      rhs
      rw [bind_eq_bind_subtypeCasesOn'_optionPelim' (x := (fg _).operation)]
      simp only [pure_bind, Shrink.inflate_deflate]
      rw [bind_subtypeCasesOn'_eq_map_bind]
    conv =>
      lhs
      rw [bind_eq_bind_subtypeCasesOn'_optionPelim']
      simp only [liftM_pure, pure_bind, Shrink.inflate_deflate, bind_assoc]
      simp +singlePass only [bind_eq_bind_subtypeCasesOn'_optionPelim' (x := (g _).operation)]
      simp only [pure_bind, Shrink.inflate_deflate]
      simp only [bind_subtypeCasesOn'_eq_map_bind]
      rw [← liftM_map]
    simp only [← PostconditionT.run_eq_map, h, bind_assoc, optionPelim']
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

@[simp]
theorem IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → PostconditionT o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toList =
      (it.filterMapWithPostcondition (n := o) (fun b => do
        match ← (f b) with
        | none => return none
        | some fb => g fb)).toList := by
  apply toList_filterMapWithPostcondition_filterMapWithPostcondition'
  intro b
  simp only [PostconditionT.run_bind']
  simp only [liftM, monadLift, MonadLift.monadLift, monadLift_self, PostconditionT.run_eq_map,
    bind_map_left, liftM_map]
  apply bind_congr; intro fx
  split <;> simp [*]

@[simp]
theorem IterM.toList_mapWithPostcondition_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n γ} {g : γ → PostconditionT o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapWithPostcondition f).mapWithPostcondition g).toList =
      (it.mapWithPostcondition (n := o) (f · >>= g)).toList := by
  simp only [toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition]
  apply toList_filterMapWithPostcondition_filterMapWithPostcondition'
  intro b
  simp [liftM, monadLift, MonadLift.monadLift, PostconditionT.run_eq_map, PostconditionT.operation_bind']

@[simp]
theorem IterM.toList_filterMapM_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapM g).toList =
      (it.filterMapM (n := o) (fun b => do
        match ← (f b).run with
        | none => return none
        | some fb => g fb)).toList := by
  apply toList_filterMapWithPostcondition_filterMapWithPostcondition'
  intro b
  simp only [PostconditionT.attachLift, PostconditionT.run_eq_map, WeaklyLawfulMonadAttach.map_attach]
  rfl

@[simp]
theorem IterM.toList_filterMapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).filterMapM g).toList =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => g fb)).toList := by
  apply toList_filterMapWithPostcondition_filterMapWithPostcondition'
  intro b
  simp only [PostconditionT.attachLift, PostconditionT.run_eq_map, WeaklyLawfulMonadAttach.map_attach]
  rfl

@[simp]
theorem IterM.toList_filterMapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toList =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toList := by
  apply toList_filterMapWithPostcondition_filterMapWithPostcondition'
  intro b
  simp only [PostconditionT.attachLift, PostconditionT.run_eq_map, WeaklyLawfulMonadAttach.map_attach,
    PostconditionT.operation_map]
  conv => lhs; simp only [← WeaklyLawfulMonadAttach.map_attach (x := f _)]
  simp

@[simp]
theorem IterM.toList_filterMapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {g : γ → n (Option δ)}
    {it : IterM (α := α) m β} :
    ((it.map f).filterMapM g).toList =
      (it.filterMapM (n := n) (fun b => g (f b))).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step, step_filterMapM,
    bind_assoc, step_filterMapM, step_map]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_pure, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

@[simp]
theorem IterM.toList_mapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).mapM g).toList =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => some <$> g fb)).toList := by
  simp [toList_mapM_eq_toList_filterMapM, toList_filterMapM_filterMapM]

@[simp]
theorem IterM.toList_mapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).mapM g).toList =
      (it.mapM (n := o) (fun b => do g (← f b))).toList := by
  simp only [toList_mapM_eq_toList_filterMapM, toList_filterMapM_mapM]
  congr <;> simp

@[simp]
theorem IterM.toList_mapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {g : γ → n δ}
    {it : IterM (α := α) m β} :
    ((it.map f).mapM g).toList =
      (it.mapM (n := n) (fun b => g (f b))).toList := by
  simp [toList_mapM_eq_toList_filterMapM]

@[simp]
theorem IterM.toList_map_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → δ}
    {it : IterM (α := α) m β} :
    ((it.mapM f).map g).toList =
      (it.mapM (n := n) (fun b => return g (← f b))).toList := by
  simp only [toList_mapM_eq_toList_filterMapM, toList_map_eq_toList_filterMapM,
    toList_filterMapM_mapM]
  congr <;> simp

@[simp]
theorem IterM.toList_filterMapWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id]
    {f : β → PostconditionT m (Option γ)} (it : IterM (α := α) Id β) :
    (it.filterMapWithPostcondition f).toList = it.toList.run.filterMapM (fun x => (f x).run) := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [step_filterMapWithPostcondition]
  simp only [liftM, monadLift, pure_bind]
  split <;> rename_i heq
  · have := congrArg (fun x => pure (f := Id) (Shrink.deflate x)) heq
    simp only [Shrink.deflate_inflate, Id.pure_run] at this
    simp only [bind_pure_comp, bind_assoc, PostconditionT.run_eq_map, this, pure_bind,
      Shrink.inflate_deflate, Id.run_map, List.filterMapM_cons, bind_map_left]
    apply bind_congr; intro a
    split
    · simp [ihy ‹_›, PostconditionT.run_eq_map]
    · simp [ihy ‹_›, PostconditionT.run_eq_map]
  · simp [ihs ‹_›, heq]
  · simp [heq]

@[simp]
theorem IterM.toList_mapWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : β → PostconditionT m γ} (it : IterM (α := α) Id β) :
    (it.mapWithPostcondition f).toList = it.toList.run.mapM (fun x => (f x).run) := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [step_mapWithPostcondition]
  simp only [liftM, monadLift, pure_bind]
  split <;> rename_i heq
  · have := congrArg (fun x => pure (f := Id) (Shrink.deflate x)) heq
    simp only [Shrink.deflate_inflate, Id.pure_run] at this
    simp only [bind_pure_comp, PostconditionT.run_eq_map, this, pure_bind,
      Shrink.inflate_deflate, Id.run_map, bind_map_left, List.mapM_cons]
    apply bind_congr; intro a
    simp [ihy ‹_›, PostconditionT.run_eq_map]
  · simp [ihs ‹_›, heq]
  · simp [heq]

@[simp]
theorem IterM.toList_filterMapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : β → m (Option γ)} (it : IterM (α := α) Id β) :
    (it.filterMapM f).toList = it.toList.run.filterMapM f := by
  simp [toList_filterMapM_eq_toList_filterMapWithPostcondition, toList_filterMapWithPostcondition,
    PostconditionT.attachLift, PostconditionT.run_eq_map, WeaklyLawfulMonadAttach.map_attach]

@[simp]
theorem IterM.toList_mapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : β → m γ} (it : IterM (α := α) Id β) :
    (it.mapM f).toList = it.toList.run.mapM f := by
  simp [toList_mapM_eq_toList_mapWithPostcondition, toList_mapWithPostcondition,
    PostconditionT.attachLift, PostconditionT.run_eq_map, WeaklyLawfulMonadAttach.map_attach]

@[simp]
theorem IterM.toList_filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  rw [step_filterMap]
  simp only [bind_assoc, IterM.step, map_eq_pure_bind]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [List.filterMap_cons, bind_assoc, pure_bind]
    split
    · split
      · simp only [bind_pure_comp, pure_bind, Shrink.inflate_deflate]
        exact ihy ‹_›
      · simp_all
    · split
      · simp_all
      · simp_all [ihy ‹_›]
  · simp only [bind_pure_comp, pure_bind, Shrink.inflate_deflate]
    apply ihs
    assumption
  · simp

@[simp]
theorem IterM.toList_map {α β β' : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {f : β → β'}
    (it : IterM (α := α) m β) :
    (it.map f).toList = (fun x => x.map f) <$> it.toList := by
  rw [← List.filterMap_eq_map, ← toList_filterMap]
  let t := type_of% (it.map f)
  let t' := type_of% (it.filterMap (some ∘ f))
  congr
  · simp [Map]
  · simp [Map.instIterator, inferInstanceAs]
    congr
    simp
  · simp only [map, mapWithPostcondition, InternalCombinators.map, Function.comp_apply, filterMap,
    filterMapWithPostcondition, InternalCombinators.filterMap]
    congr
    · simp [Map]
    · simp

@[simp]
theorem IterM.toList_filter {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β] [Finite α m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    (it.filter f).toList = List.filter f <$> it.toList := by
  simp only [filter, toList_filterMap, ← List.filterMap_eq_filter]
  rfl

end ToList

section ToListRev

theorem IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n γ} {it : IterM (α := α) m β} :
    (it.mapWithPostcondition f).toListRev =
      (it.filterMapWithPostcondition (PostconditionT.map some <| f ·)).toListRev := by
  rfl

theorem IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {it : IterM (α := α) m β} :
    (it.filterMapM f).toListRev =
      (it.filterMapWithPostcondition fun b => .attachLift (f b)).toListRev := by
  rfl

theorem IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toListRev =
      (it.mapWithPostcondition fun b => .attachLift (f b)).toListRev := by
  rfl

theorem IterM.toListRev_mapM_eq_toListRev_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toListRev =
      (it.filterMapM fun b => some <$> f b).toListRev := by
  simp [toListRev_eq, toList_mapM_eq_toList_filterMapM]

theorem IterM.toListRev_map_eq_toListRev_mapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toListRev = (it.mapM fun b => pure (f b)).toListRev := by
  simp [toListRev_eq, toList_map_eq_toList_mapM, - toList_map]

theorem IterM.toListRev_map_eq_toListRev_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toListRev = (it.filterMapM fun b => pure (some (f b))).toListRev := by
  simp [toListRev_eq, toList_map_eq_toList_filterMapM, - toList_map]

@[simp]
theorem IterM.toListRev_filterMapWithPostcondition_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → PostconditionT o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toListRev =
      (it.filterMapWithPostcondition (n := o) (fun b => do
        match ← (f b) with
        | none => return none
        | some fb => g fb)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapWithPostcondition_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n γ} {g : γ → PostconditionT o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapWithPostcondition f).mapWithPostcondition g).toListRev =
      (it.mapWithPostcondition (n := o) (f · >>= g)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do
        match ← (f b).run with
        | none => return none
        | some fb => g fb)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).filterMapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => g fb)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {g : γ → n (Option δ)}
    {it : IterM (α := α) m β} :
    ((it.map f).filterMapM g).toListRev =
      (it.filterMapM (n := n) (fun b => g (f b))).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).mapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => some <$> g fb)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).mapM g).toListRev =
      (it.mapM (n := o) (fun b => do g (← f b))).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] {f : β → γ} {g : γ → n δ} {it : IterM (α := α) m β} :
    ((it.map f).mapM g).toListRev =
      (it.mapM (n := n) (fun b => g (f b))).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_map_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → δ}
    {it : IterM (α := α) m β} :
    ((it.mapM f).map g).toListRev =
      (it.mapM (n := n) (fun b => return g (← f b))).toListRev := by
  simp [toListRev_eq, - toList_map]

@[simp]
theorem IterM.toListRev_filterMapWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id]
    {f : β → PostconditionT m (Option γ)} (it : IterM (α := α) Id β) :
    (it.filterMapWithPostcondition f).toListRev =
      List.reverse <$> it.toList.run.filterMapM (fun x => (f x).run) := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : β → PostconditionT m γ} (it : IterM (α := α) Id β) :
    (it.mapWithPostcondition f).toListRev = List.reverse <$> it.toList.run.mapM (fun x => (f x).run) := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : β → m (Option γ)} (it : IterM (α := α) Id β) :
    (it.filterMapM f).toListRev = List.reverse <$> it.toList.run.filterMapM f := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : β → m γ} (it : IterM (α := α) Id β) :
    (it.mapM f).toListRev = List.reverse <$> it.toList.run.mapM f := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toListRev = (fun x => x.filterMap f) <$> it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_map {α β γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {f : β → γ}
    (it : IterM (α := α) m β) :
    (it.map f).toListRev = (fun x => x.map f) <$> it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filter {α β : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    (it.filter f).toListRev = List.filter f <$> it.toListRev := by
  simp [toListRev_eq]

end ToListRev

section ToArray

theorem IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n γ} {it : IterM (α := α) m β} :
    (it.mapWithPostcondition f).toArray =
      (it.filterMapWithPostcondition (PostconditionT.map some <| f ·)).toArray := by
  rfl

theorem IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {it : IterM (α := α) m β} :
    (it.filterMapM f).toArray =
      (it.filterMapWithPostcondition fun b => .attachLift (f b)).toArray := by
  rfl

theorem IterM.toArray_mapM_eq_toArray_mapWithPostcondition {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toArray =
      (it.mapWithPostcondition fun b => .attachLift (f b)).toArray := by
  rfl

theorem IterM.toArray_mapM_eq_toArray_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toArray = (it.filterMapM fun b => some <$> f b).toArray := by
  simp [← toArray_toList, toList_mapM_eq_toList_filterMapM]

theorem IterM.toArray_map_eq_toArray_mapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toArray = (it.mapM fun b => pure (f b)).toArray := by
  simp [← toArray_toList, toList_map_eq_toList_mapM, - toList_map]

theorem IterM.toArray_map_eq_toArray_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toArray = (it.filterMapM fun b => pure (some (f b))).toArray := by
  simp [← toArray_toList, toList_map_eq_toList_filterMapM, - toList_map]

@[simp]
theorem IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → PostconditionT o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toArray =
      (it.filterMapWithPostcondition (n := o) (fun b => do
        match ← (f b) with
        | none => return none
        | some fb => g fb)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapWithPostcondition_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n γ} {g : γ → PostconditionT o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapWithPostcondition f).mapWithPostcondition g).toArray =
      (it.mapWithPostcondition (n := o) (f · >>= g)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → PostconditionT n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapWithPostcondition f).filterMapM g).toArray =
      (it.filterMapM (n := o) (fun b => do
        match ← (f b).run with
        | none => return none
        | some fb => g fb)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).filterMapM g).toArray =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => g fb)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toArray =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {g : γ → n (Option δ)}
    {it : IterM (α := α) m β} :
    ((it.map f).filterMapM g).toArray =
      (it.filterMapM (n := n) (fun b => g (f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n (Option γ)} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).mapM g).toArray =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => some <$> g fb)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [MonadAttach o] [LawfulMonad o] [WeaklyLawfulMonadAttach o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).mapM g).toArray =
      (it.mapM (n := o) (fun b => do g (← f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {g : γ → n δ}
    {it : IterM (α := α) m β} :
    ((it.map f).mapM g).toArray =
      (it.mapM (n := n) (fun b => g (f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_map_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → δ}
    {it : IterM (α := α) m β} :
    ((it.mapM f).map g).toArray =
      (it.mapM (n := n) (fun b => return g (← f b))).toArray := by
  simp only [toArray_mapM_eq_toArray_filterMapM, toArray_map_eq_toArray_filterMapM,
    toArray_filterMapM_mapM]
  congr <;> simp

@[simp]
theorem IterM.toArray_filterMapWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α Id β] [Finite α Id]
    {f : β → PostconditionT m (Option γ)} (it : IterM (α := α) Id β) :
    (it.filterMapWithPostcondition f).toArray = it.toArray.run.filterMapM (fun x => (f x).run) := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapWithPostcondition {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [Iterator α Id β] [Finite α Id]
    {f : β → PostconditionT m γ} (it : IterM (α := α) Id β) :
    (it.mapWithPostcondition f).toArray = it.toArray.run.mapM (fun x => (f x).run) := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : β → m (Option γ)} (it : IterM (α := α) Id β) :
    (it.filterMapM f).toArray = it.toArray.run.filterMapM f := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Iterator α Id β] [Finite α Id]
    {f : β → m γ} (it : IterM (α := α) Id β) :
    (it.mapM f).toArray = it.toArray.run.mapM f := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toArray = (fun x => x.filterMap f) <$> it.toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_map {α β γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {f : β → γ}
    (it : IterM (α := α) m β) :
    (it.map f).toArray = (fun x => x.map f) <$> it.toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filter {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β] [Finite α m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    (it.filter f).toArray = Array.filter f <$> it.toArray := by
  simp [← toArray_toList]

end ToArray

section ForIn

theorem IterM.forIn_filterMapWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.filterMapWithPostcondition f) init g = forIn it init (fun out acc => do
        match ← (f out).run with
        | some c => g c acc
        | none => return .yield acc) := by
  letI : MonadLift n o := ⟨monadLift⟩
  simp only [PostconditionT.run_eq_map]
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [IterM.forIn_eq_match_step, IterM.forIn_eq_match_step, IterM.step_filterMapWithPostcondition]
  simp only [liftM_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [liftM_bind, bind_assoc, liftM_map, bind_map_left]
    apply bind_congr; intro fx
    match fx with
    | ⟨none, _⟩ =>
      simp [liftM_pure, pure_bind, Shrink.inflate_deflate, ihy ‹_›]
    | ⟨some _, _⟩ =>
      simp only [liftM_pure, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro gx
      split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.forIn_filterMapM
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.filterMapM f) init g = forIn it init (fun out acc => do
        match ← f out with
        | some c => g c acc
        | none => return .yield acc) := by
  rw [filterMapM, forIn_filterMapWithPostcondition]
  simp [PostconditionT.run_attachLift]

theorem IterM.forIn_filterMap
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} :
    forIn (it.filterMap f) init g = forIn it init (fun out acc => do
        match f out with
        | some c => g c acc
        | none => return .yield acc) := by
  rw [filterMap, forIn_filterMapWithPostcondition]
  simp [PostconditionT.run_eq_map]

theorem IterM.forIn_mapWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.mapWithPostcondition f) init g =
      forIn it init (fun out acc => do g (← (f out).run) acc) := by
  rw [mapWithPostcondition, InternalCombinators.map, ← InternalCombinators.filterMap,
    ← filterMapWithPostcondition, forIn_filterMapWithPostcondition]
  simp [PostconditionT.run_eq_map]

theorem IterM.forIn_mapM
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.mapM f) init g = forIn it init (fun out acc => do g (← f out) acc) := by
  rw [mapM, forIn_mapWithPostcondition]
  simp [PostconditionT.run_attachLift]

theorem IterM.forIn_map
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} :
    forIn (it.map f) init g = forIn it init (fun out acc => do g (f out) acc) := by
  rw [map, forIn_mapWithPostcondition]
  simp [PostconditionT.run_eq_map]

theorem IterM.forIn_filterWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.filterWithPostcondition f) init g =
      forIn it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc) := by
  rw [filterWithPostcondition, forIn_filterMapWithPostcondition]
  congr 1; ext out acc
  simp only [PostconditionT.map_eq_pure_bind, PostconditionT.run_eq_map,
    PostconditionT.operation_bind, Function.comp_apply, PostconditionT.operation_pure, map_pure,
    bind_pure_comp, liftM_map, bind_map_left]
  apply bind_congr; intro fx
  cases fx.val.down <;> simp

theorem IterM.forIn_filterM
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    [IteratorLoop α m o] [LawfulIteratorLoop α m o]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.filterM f) init g = forIn it init (fun out acc => do if (← f out).down then g out acc else return .yield acc) := by
  rw [filterM, ← filterWithPostcondition, forIn_filterWithPostcondition]
  simp [PostconditionT.run_attachLift]

theorem IterM.forIn_filter
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    {it : IterM (α := α) m β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)} :
    forIn (it.filter f) init g = forIn it init (fun out acc => do if f out then g out acc else return .yield acc) := by
  rw [filter, forIn_filterMap]
  congr 1; ext out acc
  cases f out <;> simp

end ForIn

section Fold

theorem IterM.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.filterMapWithPostcondition f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | pure d
          g d c) := by
  simp only [foldM_eq_forIn, forIn_filterMapWithPostcondition]
  congr 1; ext out acc
  simp only [map_bind]
  apply bind_congr; intro fx
  split <;> simp

theorem IterM.foldM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.filterMapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          g d c) := by
  simp [filterMapM, foldM_filterMapWithPostcondition, PostconditionT.run_attachLift]

theorem IterM.foldM_mapWithPostcondition {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.mapWithPostcondition f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← (f b).run; g d c) := by
  simp [foldM_eq_forIn, forIn_mapWithPostcondition]

theorem IterM.foldM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.mapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; g d c) := by
  simp [foldM_eq_forIn, forIn_mapM]

theorem IterM.foldM_filterWithPostcondition {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.filterWithPostcondition f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do if (← (f b).run).down then g d b else pure d) := by
  simp only [foldM_eq_forIn, forIn_filterWithPostcondition]
  congr 1; ext out acc
  simp only [map_bind]
  apply bind_congr; intro fx
  split <;> simp

theorem IterM.foldM_filterM {α β δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.filterM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do if (← f b).down then g d b else pure d) := by
  simp [filterM, foldM_filterMapWithPostcondition, PostconditionT.run_attachLift]
  congr 1; ext out acc
  apply bind_congr; intro fx
  cases fx.down <;> simp [PostconditionT.run_eq_map]

theorem IterM.foldM_filterMap {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMap f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c := f b | pure d
          g d c) := by
  simp only [foldM_eq_forIn, forIn_filterMap]
  congr 1; ext out acc
  split <;> simp [*]

theorem IterM.foldM_map {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β} :
    (it.map f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do g d (f b)) := by
  simp [foldM_eq_forIn, forIn_map]

theorem IterM.foldM_filter {α β δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m n]
    [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filter f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => if f b then g d b else pure d) := by
  simp only [foldM_eq_forIn, forIn_filter]
  congr 1; ext out acc
  split <;> simp [*]

theorem IterM.fold_filterMapWithPostcondition {α β γ δ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMapWithPostcondition f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | pure d
          return g d c) := by
  simp [fold_eq_foldM, foldM_filterMapWithPostcondition]

theorem IterM.fold_filterMapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          return g d c) := by
  simp [fold_eq_foldM, foldM_filterMapM]

theorem IterM.fold_mapWithPostcondition {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.mapWithPostcondition f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c) := by
  simp [fold_eq_foldM, foldM_mapWithPostcondition]

theorem IterM.fold_mapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.mapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; return g d c) := by
  simp [fold_eq_foldM, foldM_mapM]

theorem IterM.fold_filterWithPostcondition {α β δ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterWithPostcondition f).fold (init := init) g =
      it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d) := by
  simp only [fold_eq_foldM, foldM_filterWithPostcondition, monadLift_self]
  congr 1; ext out acc
  apply bind_congr; intro fx
  cases fx.down <;> simp

theorem IterM.fold_filterM {α β δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d) := by
  simp only [fold_eq_foldM, foldM_filterM]
  congr 1; ext out acc
  apply bind_congr; intro fx
  cases fx.down <;> simp

theorem IterM.fold_filterMap {α β γ δ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMap f).fold (init := init) g =
      it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d) := by
  simp [fold_eq_foldM, foldM_filterMap]
  congr; ext
  split <;> simp

theorem IterM.fold_map {α β γ δ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.map f).fold (init := init) g =
      it.fold (init := init) (fun d b => g d (f b)) := by
  simp [fold_eq_foldM, foldM_map]

theorem IterM.fold_filter {α β δ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Bool} {g : δ → β → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filter f).fold (init := init) g =
      it.fold (init := init) (fun d b => if f b then g d b else d) := by
  simp [fold_eq_foldM, foldM_filter]
  congr; ext
  split <;> simp

end Fold

section Count

@[simp]
theorem IterM.count_map {α β β' : Type w} {m : Type w → Type w'} [Iterator α m β] [Monad m]
    [IteratorLoop α m m] [Finite α m] [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} :
    (it.map f).count = it.count := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [count_eq_match_step, count_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

end Count

section AnyAll

theorem IterM.anyM_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n]
    [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → n (ULift Bool)} :
    (it.filterMapM f).anyM p = (it.mapM (pure (f := n))).anyM (fun x => do
      match ← f x with
      | some fx => p fx
      | none => return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_filterMapM, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · rename_i out _ _
    simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    have {x : n (ULift Bool)} : x = MonadAttach.attach (pure out) >>= (fun _ => x) := by
      rw (occs := [1]) [show x = pure out >>= (fun _ => x) by simp]
      conv => lhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := pure out)]
      simp
    refine Eq.trans this ?_
    simp only [WeaklyLawfulMonadAttach.bind_attach_of_nonempty (x := pure out), pure_bind]
    split; rotate_left; rfl
    conv => rhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := f _), bind_map_left]
    apply bind_congr; intro fx
    split
    · simp [ihy ‹_›]
    · simp only [PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.anyM_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → n (ULift Bool)} :
    (it.mapM f).anyM p = (it.mapM (pure (f := n))).anyM (fun x => do p (← f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_mapM, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · rename_i out _ _
    simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    have {x : n (ULift Bool)} : x = MonadAttach.attach (pure out) >>= (fun _ => x) := by
      rw (occs := [1]) [show x = pure out >>= (fun _ => x) by simp]
      conv => lhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := pure out)]
      simp
    refine Eq.trans this ?_
    simp only [WeaklyLawfulMonadAttach.bind_attach_of_nonempty (x := pure out), pure_bind]
    split; rotate_left; rfl
    conv => rhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := f _), bind_map_left]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.anyM_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → n (ULift Bool)} :
    (it.filterM f).anyM p = (it.mapM (pure (f := n))).anyM (fun x => do
        if (← f x).down then
          p x
        else
          return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_mapM, step_filterM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · rename_i out _ _
    simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    have {x : n (ULift Bool)} : x = MonadAttach.attach (pure out) >>= (fun _ => x) := by
      rw (occs := [1]) [show x = pure out >>= (fun _ => x) by simp]
      conv => lhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := pure out)]
      simp
    refine Eq.trans this ?_
    simp only [WeaklyLawfulMonadAttach.bind_attach_of_nonempty (x := pure out), pure_bind]
    split; rotate_left; rfl
    conv => rhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := f _), bind_map_left]
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.anyM_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → m (ULift Bool)} :
    (it.filterMap f).anyM p = it.anyM (fun x => do
      match f x with
      | some fx => p fx
      | none => return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_filterMap, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp only [*, PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.anyM_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → m (ULift Bool)} :
    (it.map f).anyM p = it.anyM (fun x => p (f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.anyM_filter {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m][IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Bool} {p : β → m (ULift Bool)} :
    (it.filter f).anyM p = it.anyM (fun x => do
        if f x then
          p x
        else
          return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_filter, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind]
    simp [ihs ‹_›]
  · simp

theorem IterM.any_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n] [IteratorLoop α m m]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → Bool} :
    (it.filterMapM f).any p = (it.mapM (pure (f := n))).anyM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up false) := by
  simp [any_eq_anyM, anyM_filterMapM]

theorem IterM.any_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n] [IteratorLoop α m m]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → Bool} :
    (it.mapM f).any p = (it.mapM (pure (f := n))).anyM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [any_eq_anyM, anyM_mapM]

theorem IterM.any_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n] [IteratorLoop α m m]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → Bool} :
    (it.filterM f).any p = (it.mapM (pure (f := n))).anyM (fun x => do
        if (← f x).down then
          return .up (p x)
        else
          return .up false) := by
  simp [any_eq_anyM, anyM_filterM]

theorem IterM.any_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → Bool} :
    (it.filterMap f).any p = it.any (fun x =>
      match f x with
      | some fx => (p fx)
      | none => false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [any_eq_match_step, any_eq_match_step, step_filterMap, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp only [*, PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      split <;> simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.any_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → Bool} :
    (it.map f).any p = it.any (fun x => p (f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [any_eq_match_step, any_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind]
    simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.allM_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → n (ULift Bool)} :
    (it.filterMapM f).allM p = (it.mapM (pure (f := n))).allM (fun x => do
      match ← f x with
      | some fx => p fx
      | none => return .up true) := by
  rw [allM_eq_not_anyM_not, anyM_filterMapM, allM_eq_not_anyM_not]
  congr 2; ext x
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro y
  split <;> simp

theorem IterM.allM_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] {it : IterM (α := α) m β} {f : β → n β'} {p : β' → n (ULift Bool)} :
    (it.mapM f).allM p = (it.mapM (pure (f := n))).allM (fun x => do p (← f x)) := by
  simp [allM_eq_not_anyM_not, anyM_mapM]

theorem IterM.allM_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → n (ULift Bool)} :
    (it.filterM f).allM p = (it.mapM (pure (f := n))).allM (fun x => do
        if (← f x).down then
          p x
        else
          return .up true) := by
  simp only [allM_eq_not_anyM_not, anyM_filterM, map_bind]
  congr; ext a
  apply bind_congr; intro b
  split <;> simp

theorem IterM.allM_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → m (ULift Bool)} :
    (it.filterMap f).allM p = it.allM (fun x => do
      match f x with
      | some fx => p fx
      | none => return .up true) := by
  simp only [allM_eq_not_anyM_not, anyM_filterMap]
  congr; ext a
  split <;> simp

theorem IterM.allM_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → m (ULift Bool)} :
    (it.map f).allM p = it.allM (fun x => p (f x)) := by
  simp [allM_eq_not_anyM_not, anyM_map]

theorem IterM.allM_filter {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m][IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Bool} {p : β → m (ULift Bool)} :
    (it.filter f).allM p = it.allM (fun x => do
        if f x then
          p x
        else
          return .up true) := by
  simp only [allM_eq_not_anyM_not, anyM_filter]
  congr; ext a
  split <;> simp

theorem IterM.all_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n] [IteratorLoop α m m]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → Bool} :
    (it.filterMapM f).all p = (it.mapM (pure (f := n))).allM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up true) := by
  simp [all_eq_allM, allM_filterMapM]

theorem IterM.all_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n] [IteratorLoop α m m]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → Bool} :
    (it.mapM f).all p = (it.mapM (pure (f := n))).allM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [all_eq_allM, allM_mapM]

theorem IterM.all_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [MonadLiftT m n] [IteratorLoop α m m]
    [Monad m] [LawfulMonad m] [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → Bool} :
    (it.filterM f).all p = (it.mapM (pure (f := n))).allM (fun x => do
        if (← f x).down then
          return .up (p x)
        else
          return .up true) := by
  simp [all_eq_allM, allM_filterM]

theorem IterM.all_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → Bool} :
    (it.filterMap f).all p = it.all (fun x =>
      match f x with
      | some fx => (p fx)
      | none => true) := by
  simp only [all_eq_not_any_not, any_filterMap]
  congr; ext
  split <;> simp

theorem IterM.all_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → Bool} :
    (it.map f).all p = it.all (fun x => p (f x)) := by
  simp [all_eq_not_any_not, any_map]

end AnyAll

end Std
