/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Lemmas.Producers.Monadic.Empty
import Init.Data.Iterators.Lemmas.Consumers
import Std.Data.Iterators.Producers.Empty

namespace Std.Iterators

@[simp]
theorem Iter.toIterM_empty {β} :
    (Iter.empty β).toIterM = IterM.empty Id β :=
  rfl

@[simp]
theorem Iter.step_empty {β} :
    (Iter.empty β).step = ⟨.done, rfl⟩ := by
  simp [Iter.step]

@[simp]
theorem Iter.toList_empty {β} :
    (Iter.empty β).toList = [] := by
  simp [Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toListRev_empty {β} :
    (Iter.empty β).toListRev = [] := by
  simp [Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toArray_empty {β} :
    (Iter.empty β).toArray = #[] := by
  simp [Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.forIn_empty {m β γ} [Monad m] [LawfulMonad m]
    {init : γ} {f} :
    ForIn.forIn (m := m) (Iter.empty β) init f = pure init := by
  simp [Iter.forIn_eq_forIn_toIterM]
  letI : MonadLift Id m := ⟨Internal.idToMonad (α := _)⟩
  letI := Internal.LawfulMonadLiftFunction.idToMonad (m := m)
  haveI : LawfulMonadLiftT Id m := inferInstance
  rw [IterM.forIn_empty]


@[simp]
theorem Iter.foldM_empty {m β γ} [Monad m] [LawfulMonad m]
    {init : γ} {f} :
    (Iter.empty β).foldM (m := m) (init := init) f = pure init := by
  simp [Iter.foldM_eq_forIn]

@[simp]
theorem Iter.fold_empty {β γ} {init : γ} {f} :
    (Iter.empty β).fold (init := init) f = init := by
  simp [Iter.fold_eq_foldM]

end Std.Iterators
