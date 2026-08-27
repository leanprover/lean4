/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Std.Data.Iterators.Consumers.Monadic.Set
public import Init.Data.Iterators.Consumers.Monadic.Collect
import all Std.Data.Iterators.Consumers.Monadic.Set
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import Std.Data.ExtHashSet.Lemmas
import Std.Data.ExtTreeSet.Lemmas

public section

namespace Std
open Iterators

theorem IterM.toHashSet_eq_fold {α β : Type w} {_ : BEq β} {_ : Hashable β} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.toHashSet = it.fold (init := ∅) fun acc a => acc.insert a := (rfl)

@[simp]
theorem IterM.toExtHashSet_eq_ofList {α β : Type w} {_ : BEq β} {_ : Hashable β} [EquivBEq β]
    [LawfulHashable β] {m : Type w → Type w'} [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] [IteratorLoop α m m] [LawfulIteratorLoop α m m] {it : IterM (α := α) m β} :
    it.toExtHashSet = ExtHashSet.ofList <$> it.toList := by
  simp only [toExtHashSet, ← foldl_toList, ← ExtHashSet.ofList_eq_foldl]

theorem IterM.toTreeSet_eq_fold {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] {it : IterM (α := α) m β} {cmp : β → β → Ordering} :
    it.toTreeSet cmp = it.fold (init := ∅) fun acc a => acc.insert a := (rfl)

@[simp]
theorem IterM.toExtTreeSet_eq_ofList {α β : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {cmp : β → β → Ordering} [TransCmp cmp] :
    it.toExtTreeSet cmp = (ExtTreeSet.ofList · cmp) <$> it.toList := by
  simp only [toExtTreeSet, ← foldl_toList, ← ExtTreeSet.ofList_eq_foldl]

end Std
