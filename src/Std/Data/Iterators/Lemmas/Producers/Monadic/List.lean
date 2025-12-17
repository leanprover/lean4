/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Producers.Monadic.List
public import Std.Data.Iterators.Lemmas.Equivalence.Basic


namespace Std
open Std.Internal Std.Iterators Std.Iterators.Types

variable {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] {β : Type w}

-- We don't want to pollute `List` with this rarely used lemma.
public theorem Types.ListIterator.stepAsHetT_iterM [LawfulMonad m] {l : List β} :
    (l.iterM m).stepAsHetT = (match l with
      | [] => pure .done
      | x :: xs => pure (.yield (xs.iterM m) x)) := by
  simp only [List.iterM, IterM.mk, HetT.ext_iff, Equivalence.property_step, IterM.IsPlausibleStep,
    Iterator.IsPlausibleStep, Equivalence.prun_step]
  refine ⟨?_, ?_⟩
  · ext step
    cases step
    · cases l
      · simp [Pure.pure]
      · simp only [List.cons.injEq, pure, HetT.property_pure, IterStep.yield.injEq, IterM.ext_iff,
        ListIterator.ext_iff]
        exact And.comm
    · cases l <;> simp [Pure.pure]
    · cases l <;> simp [Pure.pure]
  · intro β f
    simp only [IterM.step, Iterator.step, pure_bind]
    cases l <;> simp [Pure.pure, IterM.mk]

end Std
