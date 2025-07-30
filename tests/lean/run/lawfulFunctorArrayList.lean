/-
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Microsoft Corporation

This file demonstrates local Applicative and Monad instances for List and Array.
These instances are kept local due to their O(n²) performance characteristics.
-/
prelude
import Init.Control.Lawful.Instances

/-!
# LawfulFunctor instances test

This file tests the `LawfulFunctor` instances for `List`, `Array`, and `Vector`,
and demonstrates local `Applicative` and `Monad` instances.
-/

section LocalInstances

/-- Helper theorem: Array seq operation is equivalent to flatMap. -/
@[simp]
private theorem Array.seq_eq_flatMap {α β : Type u} (fns : Array (α → β)) (xs : Array α) :
    fns.foldl (fun acc f => acc ++ xs.map f) #[] = fns.flatMap (fun f => xs.map f) := by
  rw [Array.flatMap_eq_foldl]
  rfl

/-- Local Applicative instance for List with O(n²) append-based implementation. -/
local instance : Applicative List where
  pure := List.pure
  seq {α β} (fns : List (α → β)) (fn : Unit → List α) : List β :=
    fns.foldl (fun acc f => acc ++ (fn ()).map f) []

/-- Local Applicative instance for Array with O(n²) append-based implementation. -/
local instance : Applicative Array where
  pure := Array.pure
  seq {α β} (fns : Array (α → β)) (fn : Unit → Array α) : Array β :=
    fns.foldl (fun acc f => acc ++ (fn ()).map f) #[]

/-- Local Monad instance for Array. -/
local instance : Monad Array where
  bind xs f := xs.flatMap f

/-- Local Monad instance for List. -/
local instance : Monad List where
  bind xs f := xs.flatMap f

/-- Array is a lawful applicative with our local instance. -/
local instance : LawfulApplicative Array where
  seqLeft_eq  := by intros; simp only [SeqLeft.seqLeft, Seq.seq]
  seqRight_eq := by intros; simp only [SeqRight.seqRight, Seq.seq]
  seq_pure    := by
    intros; simp only [Seq.seq, pure, Array.pure, Array.singleton,
      Array.singleton_def, Array.mkEmpty, List.map_cons, 
      List.map_nil, Array.foldl_eq, Functor.map]
    rw [Array.toList_eq]
    simp [List.foldl_cons, List.foldl_nil]
  pure_seq    := by intros; simp [pure, Seq.seq, Functor.map]
  map_pure    := by intros; simp [Functor.map, pure]
  seq_assoc   := by
    intros
    simp only [Seq.seq, Functor.map, Array.seq_eq_flatMap, Array.flatMap_flatMap]
    congr; funext f
    simp [Array.flatMap_map]

/-- List is a lawful applicative with our local instance. -/
local instance : LawfulApplicative List where
  seqLeft_eq  := by intros; simp [SeqLeft.seqLeft, Seq.seq]
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq]
  seq_pure    := by
    intros α β g x
    simp [Seq.seq, pure, Functor.map, List.pure]
    induction g with
    | nil => simp
    | cons f fs ih => simp [List.foldl_cons, ih]
  pure_seq    := by
    intros
    simp [pure, Seq.seq, Functor.map, List.pure, List.foldl_cons, List.foldl_nil]
  map_pure    := by
    intros
    simp only [Functor.map, pure, List.pure, List.map_cons, List.map_nil]
  seq_assoc   := by
    intros
    simp only [Seq.seq, Functor.map]
    have foldl_eq_flatMap : ∀ {α β : Type u_1} (fs : List (α → β)) (xs : List α),
      fs.foldl (fun acc f => acc ++ xs.map f) [] = fs.flatMap (fun f => xs.map f) := by
      intros _ _ fs _
      induction fs with
      | nil => simp
      | cons f fs ih => simp [List.foldl_cons, List.flatMap_cons, ih]
    simp [foldl_eq_flatMap, List.flatMap_map, List.flatMap_flatMap]

/-- Array is a lawful monad with our local instance. -/
local instance : LawfulMonad Array where
  bind_pure_comp := by intros; simp [pure, Functor.map, bind, Array.flatMap_map]
  pure_bind      := by intros; simp [bind, pure, Array.flatMap_pure]
  bind_assoc     := by intros; simp [bind, Array.flatMap_flatMap]
  pure_seq       := by intros; simp [pure, Seq.seq, Functor.map]
  bind_map       := by intros; rfl
  seqLeft_eq     := by simp [LawfulApplicative.seqLeft_eq]
  seqRight_eq    := by simp [LawfulApplicative.seqRight_eq]

/-- List is a lawful monad with our local instance. -/
local instance : LawfulMonad List where
  bind_pure_comp := by intros; simp [pure, Functor.map, bind, List.flatMap_map]
  pure_bind      := by intros; simp [bind, pure, List.flatMap_pure]
  bind_assoc     := by intros; simp [bind, List.flatMap_flatMap]
  pure_seq       := by intros; simp [pure, Seq.seq, Functor.map, List.pure]
  bind_map       := by intros; simp [Seq.seq]; rfl
  seqLeft_eq     := by simp [LawfulApplicative.seqLeft_eq]
  seqRight_eq    := by simp [LawfulApplicative.seqRight_eq]

-- Verify that the global LawfulFunctor instances work
example : LawfulFunctor List := inferInstance
example : LawfulFunctor Array := inferInstance
example : LawfulFunctor (Vector · 5) := inferInstance

-- Verify that the local LawfulApplicative and LawfulMonad instances work
example : LawfulApplicative Array := inferInstance
example : LawfulApplicative List := inferInstance
example : LawfulMonad Array := inferInstance
example : LawfulMonad List := inferInstance

end LocalInstances