/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Control.Basic
import Init.Control.Lawful.Basic
import Init.NotationExtra
import Init.Control.Lawful.MonadLift

/-!
# Typeclass for lawful monad lifting functions

This module provides a typeclass `LawfulMonadLiftFunction f` that asserts that a function `f`
mapping values from one monad to another monad commutes with `pure` and `bind`. This equivalent to
the requirement that the `MonadLift(T)` instance induced by `f` admits a
`LawfulMonadLift(T)` instance.
-/

namespace Std.Internal

class LawfulMonadLiftFunction {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] (lift : ⦃α : Type u⦄ → m α → n α) where
  lift_pure {α : Type u} (a : α) : lift (pure a) = pure a
  lift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    lift (ma >>= f) = lift ma >>= (fun x => lift (f x))

instance {m : Type u → Type v} [Monad m] : LawfulMonadLiftFunction (fun ⦃α⦄ => (id : m α → m α)) where
  lift_pure := by simp
  lift_bind := by simp

instance {m : Type u → Type v} [Monad m] {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] :
    LawfulMonadLiftFunction (fun ⦃α⦄ => (monadLift : m α → n α)) where
  lift_pure := monadLift_pure
  lift_bind := monadLift_bind

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
    {lift : ⦃α : Type u⦄ → m α → n α}

theorem LawfulMonadLiftFunction.lift_map [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftFunction lift] (f : α → β) (ma : m α) :
    lift (f <$> ma) = f <$> (lift ma : n α) := by
  rw [← bind_pure_comp, ← bind_pure_comp, lift_bind (lift := lift)]
  simp only [bind_pure_comp, lift_pure]

theorem LawfulMonadLiftFunction.lift_seq [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftFunction lift] (mf : m (α → β)) (ma : m α) :
    lift (mf <*> ma) = lift mf <*> (lift ma : n α) := by
  simp only [seq_eq_bind, lift_map, lift_bind]

theorem LawfulMonadLiftFunction.lift_seqLeft [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftFunction lift] (x : m α) (y : m β) :
    lift (x <* y) = (lift x : n α) <* (lift y : n β) := by
  simp only [seqLeft_eq, lift_map, lift_seq]

theorem LawfulMonadLiftFunction.lift_seqRight [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftFunction lift] (x : m α) (y : m β) :
    lift (x *> y) = (lift x : n α) *> (lift y : n β) := by
  simp only [seqRight_eq, lift_map, lift_seq]

abbrev idToMonad [Monad m] ⦃α : Type u⦄ (x : Id α) : m α :=
    pure x.run

def LawfulMonadLiftFunction.idToMonad [Monad m] [LawfulMonad m] :
    LawfulMonadLiftFunction (m := Id) (n := m) idToMonad where
  lift_pure := by simp [Internal.idToMonad]
  lift_bind := by simp [Internal.idToMonad]

instance [LawfulMonadLiftFunction lift] :
    letI : MonadLift m n := ⟨lift (α := _)⟩
    LawfulMonadLift m n :=
  letI : MonadLift m n := ⟨lift (α := _)⟩
  { monadLift_pure := LawfulMonadLiftFunction.lift_pure
    monadLift_bind := LawfulMonadLiftFunction.lift_bind }

end Std.Internal
