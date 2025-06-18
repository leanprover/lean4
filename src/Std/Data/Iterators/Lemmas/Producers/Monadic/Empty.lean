/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Producers.Monadic.Empty
import Init.Data.Iterators.Lemmas.Consumers.Monadic
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop

namespace Std.Iterators

@[simp]
theorem IterM.step_empty {m β} [Monad m] :
    (IterM.empty m β).step = pure ⟨.done, rfl⟩ :=
  rfl

@[simp]
theorem IterM.toList_empty {m β} [Monad m] [LawfulMonad m] :
    (IterM.empty m β).toList = pure [] := by
  rw [toList_eq_match_step]
  simp

@[simp]
theorem IterM.toListRev_empty {m β} [Monad m] [LawfulMonad m] :
    (IterM.empty m β).toListRev = pure [] := by
  rw [toListRev_eq_match_step]
  simp

@[simp]
theorem IterM.toArray_empty {m β} [Monad m] [LawfulMonad m] :
    (IterM.empty m β).toArray = pure #[] := by
  rw [toArray_eq_match_step]
  simp

@[simp]
theorem IterM.forIn_empty {m n β γ} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    {init : γ} {f} :
    ForIn.forIn (m := n) (IterM.empty m β) init f = pure init := by
  rw [IterM.forIn_eq_match_step]
  simp

@[simp]
theorem IterM.foldM_empty {m n β γ} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    {init : γ} {f} :
    (IterM.empty m β).foldM (n := n) (init := init) f = pure init := by
  simp [IterM.foldM_eq_forIn]

@[simp]
theorem IterM.fold_empty {m β γ} [Monad m] [LawfulMonad m]
    {init : γ} {f} :
    (IterM.empty m β).fold (init := init) f = pure init := by
  simp [IterM.fold_eq_foldM]

@[simp]
theorem IterM.drain_empty {m β} [Monad m] [LawfulMonad m] :
    (IterM.empty m β).drain = pure .unit := by
  simp [IterM.drain_eq_fold]

end Std.Iterators
