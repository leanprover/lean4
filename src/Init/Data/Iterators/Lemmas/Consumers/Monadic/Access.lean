/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Access
import all Init.Data.Iterators.Consumers.Monadic.Access
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
public import Init.Control.Lawful.Basic
import Init.Control.Lawful.Lemmas

namespace Std.IterM
open Std.Iterators

public theorem atIdxSlow?_eq_match [Monad m] [LawfulMonad m] [Iterator α m β] [Productive α m]
    {n : Nat} {it : IterM (α := α) m β} :
    it.atIdxSlow? n = (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        match n with
        | 0 => return some out
        | n + 1 => it'.atIdxSlow? n
      | .skip it' => it'.atIdxSlow? n
      | .done => return none) := by
  rw [IterM.atIdxSlow?]
  apply bind_congr; intro step
  obtain ⟨val, prop⟩ := step.inflate
  cases val <;> rfl

private theorem val_nextAtIdxSlow?Go [Monad m] [LawfulMonad m] [Iterator α m β] [Productive α m]
    {n : Nat} {it : IterM (α := α) m β} {n' it' h} :
    Subtype.val <$> IterM.nextAtIdxSlow?.go it n it' n' h =
      Subtype.val <$> IterM.nextAtIdxSlow? it' n' := by
  induction it', n' using IterM.atIdxSlow?.induct generalizing it n
  rw [IterM.nextAtIdxSlow?, IterM.nextAtIdxSlow?.go, IterM.nextAtIdxSlow?.go]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  rename_i it' n' ih₁ ih₂
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [bind_pure_comp]
    cases n'
    · simp
    · simp only at ih₁
      simp [ih₁]
  · simp only at ih₂
    simp (discharger := assumption) [ih₂]
  · simp

public theorem val_nextAtIdxSlow?_eq_match [Monad m] [LawfulMonad m] [Iterator α m β] [Productive α m]
    {n : Nat} {it : IterM (α := α) m β} :
    Subtype.val <$> it.nextAtIdxSlow? n = (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        match n with
        | 0 => return .yield it' out
        | n + 1 => return (← it'.nextAtIdxSlow? n).val
      | .skip it' => return (← it'.nextAtIdxSlow? n).val
      | .done =>
        return .done) := by
  rw [IterM.nextAtIdxSlow?, IterM.nextAtIdxSlow?.go]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · cases n
    · simp
    · simp [val_nextAtIdxSlow?Go]
  · simp [val_nextAtIdxSlow?Go]
  · simp

public theorem nextAtIdxSlow?_eq_match [Monad m] [LawfulMonad m] [Iterator α m β] [Productive α m]
    {n : Nat} {it : IterM (α := α) m β} :
    it.nextAtIdxSlow? n = (do
      match (← it.step).inflate with
      | .yield it' out hp =>
        match n with
        | 0 => return .yield it' out (.zero_yield hp)
        | n + 1 =>
          let s ← it'.nextAtIdxSlow? n
          return ⟨s.val, .yield hp s.property⟩
      | .skip it' hp =>
          let s ← it'.nextAtIdxSlow? n
          return ⟨s.val, .skip hp s.property⟩
      | .done hp =>
        return .done (.done hp)) := by
  apply (map_inj_right Subtype.ext).mp
  rw [val_nextAtIdxSlow?_eq_match]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · cases n <;> simp
  · simp
  · simp

public theorem nextAtIdxSlow?_eq_match_nextAtIdxSlow? [Monad m] [LawfulMonad m] [Iterator α m β] [Productive α m]
    {n : Nat} {it : IterM (α := α) m β} :
    it.nextAtIdxSlow? n = (do
      let step ← it.nextAtIdxSlow? 0
      match n with
      | 0 => return step
      | n + 1 =>
        match step with
        | .yield it' _out hp =>
          let s ← it'.nextAtIdxSlow? n
          return ⟨s.val, isPlausibleNthOutputStep_trans_of_yield hp s.property⟩
        | .skip _it' hp => not_isPlausibleNthOutputStep_skip.elim hp
        | .done hp => return ⟨.done, isPlausibleNthOutputStep_trans_of_done (k := 0) hp (Nat.zero_le _)⟩) := by
  fun_induction it.atIdxSlow? n
  rename_i ih₁ ih₂
  rw [nextAtIdxSlow?_eq_match, nextAtIdxSlow?_eq_match]
  simp only [bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp
  · simp only [bind_pure_comp, bind_map_left] at ih₁ ih₂ ⊢
    rw [ih₂]
    · simp only [map_bind]
      apply bind_congr; intro step'
      split
      · simp
      · split
        · simp
        · exact not_isPlausibleNthOutputStep_skip.elim ‹_›
        · simp
    · assumption
  · simp only [bind_pure_comp, pure_bind]
    split <;> simp

public theorem nextAtIdxSlow?_add_one [Monad m] [LawfulMonad m] [Iterator α m β] [Productive α m]
    {n : Nat} {it : IterM (α := α) m β} :
    it.nextAtIdxSlow? (n + 1) = (do
      match ← it.nextAtIdxSlow? 0 with
      | .yield it' _ hp =>
        let s ← it'.nextAtIdxSlow? n
        return ⟨s.val, isPlausibleNthOutputStep_trans_of_yield hp s.property⟩
      | .skip _ hp => not_isPlausibleNthOutputStep_skip.elim hp
      | .done hp => return ⟨.done, isPlausibleNthOutputStep_trans_of_done (k := 0) hp (Nat.zero_le _)⟩) := by
  rw [nextAtIdxSlow?_eq_match_nextAtIdxSlow?]

public local instance instSubsingletonPlausibleIterStepIsPlausibleNthOutputStep [Iterator α Id β]
    [LawfulDeterministicIterator α Id] {it : IterM (α := α) Id β} :
    Subsingleton (PlausibleIterStep (it.IsPlausibleNthOutputStep n)) where
  allEq s s' := by
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    have := hs.unique hs'
    rwa [Subtype.mk.injEq]

public theorem nextAtIdx?_eq_nextAtIdxSlow? [Iterator α Id β] [Productive α Id]
    [LawfulDeterministicIterator α Id] [IteratorAccess α Id] {it : IterM (α := α) Id β} {n : Nat} :
    it.nextAtIdx? n = it.nextAtIdxSlow? n := by
  apply Id.ext
  apply Subsingleton.allEq

public theorem length_nextAtIdxSlow? [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    (do match ← it.nextAtIdxSlow? n with
      | .yield it' _out _ => it'.length
      | .skip _it' h => IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done _h => return .up 0) = (fun len => .up (len.down - n - 1)) <$> it.length := by
  induction it using IterM.inductSteps generalizing n with | step it ihy ihs
  rw [it.nextAtIdxSlow?_eq_match, it.length_eq_match_step]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [bind_pure_comp, Functor.map_map]
    split
    · simp only [pure_bind, Nat.sub_zero, Nat.add_one_sub_one, id_map']
    · simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right, bind_map_left]
      rw [← ihy ‹_›]
      apply bind_congr; intro step
      cases step using PlausibleIterStep.casesOn <;> simp [Not.elim, absurd]
  · simp only [bind_pure_comp, bind_map_left, id_map']
    rw [← ihs ‹_›]
    apply bind_congr; intro step
    cases step using PlausibleIterStep.casesOn <;> simp [Not.elim, absurd]
  · simp
