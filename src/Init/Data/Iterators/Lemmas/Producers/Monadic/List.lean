/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Monadic
public import Init.Data.Iterators.Producers.Monadic.List

@[expose] public section

/-!
# Lemmas about list iterators

This module provides lemmas about the interactions of `List.iterM` with `IterM.step` and various
collectors.
-/

open Std Std.Internal Std.Iterators Std.Iterators.Types

variable {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] {β : Type w}

@[simp]
theorem List.step_iterM_nil :
    (([] : List β).iterM m).step = pure (.deflate ⟨.done, rfl⟩) := by
  simp only [IterM.step, Iterator.step]; rfl

@[simp]
theorem List.step_iterM_cons {x : β} {xs : List β} :
    ((x :: xs).iterM m).step = pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := by
  simp only [List.iterM, IterM.step, Iterator.step]; rfl

theorem List.step_iterM {l : List β} :
    (l.iterM m).step = match l with
      | [] => pure (.deflate ⟨.done, rfl⟩)
      | x :: xs => pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := by
  cases l <;> simp [List.step_iterM_cons, List.step_iterM_nil]

@[simp, grind =]
theorem List.toArray_iterM [LawfulMonad m] {β : Type w} {l : List β} :
  (l.iterM m).toArray = pure l.toArray := by
  induction l with
  | nil =>
    rw [IterM.toArray_eq_match_step]
    simp [List.step_iterM_nil]
  | cons x xs ih =>
    rw [IterM.toArray_eq_match_step]
    simp [List.step_iterM_cons, pure_bind, ih]

@[simp, grind =]
theorem List.toList_iterM [LawfulMonad m] {l : List β} :
    (l.iterM m).toList = pure l := by
  rw [← IterM.toList_toArray, List.toArray_iterM, map_pure, List.toList_toArray]

@[simp, grind =]
theorem List.toListRev_iterM [LawfulMonad m] {l : List β} :
    (l.iterM m).toListRev = pure l.reverse := by
  simp [IterM.toListRev_eq, List.toList_iterM]
