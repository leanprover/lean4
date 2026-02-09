/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.Lawful.MonadLift

public section

/-!
# Typeclass for lawful monad lifting functions

This module provides a typeclass `LawfulMonadLiftFunction f` that asserts that a function `f`
mapping values from one monad to another monad commutes with `pure` and `bind`. This equivalent to
the requirement that the `MonadLift(T)` instance induced by `f` admits a
`LawfulMonadLift(T)` instance.
-/

namespace Std.Internal

class LawfulMonadLiftBindFunction {m : Type u → Type v} {n : Type w → Type x} [Monad m]
    [Monad n] (liftBind : ∀ γ δ, (γ → n δ) → m γ → n δ) where
  liftBind_pure {γ δ} (f : γ → n δ) (a : γ) : liftBind γ δ f (pure a) = f a
  liftBind_bind {β γ δ} (f : γ → n δ) (x : m β) (g : β → m γ) :
    liftBind γ δ f (x >>= g) = liftBind β δ (fun b => liftBind γ δ f (g b)) x

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
  simp only [seq_eq_bind_map, lift_map, lift_bind]

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

theorem LawfulMonadLiftFunction.idToMonad [LawfulMonad m] :
    LawfulMonadLiftFunction (m := Id) (n := m) idToMonad where
  lift_pure := by simp [Internal.idToMonad]
  lift_bind := by simp [Internal.idToMonad]

instance [LawfulMonadLiftFunction lift] :
    letI : MonadLift m n := ⟨lift (α := _)⟩
    LawfulMonadLift m n :=
  letI : MonadLift m n := ⟨lift (α := _)⟩
  { monadLift_pure := LawfulMonadLiftFunction.lift_pure
    monadLift_bind := LawfulMonadLiftFunction.lift_bind }

section LiftBind

variable {liftBind : ∀ γ δ, (γ → m δ) → m γ → m δ}

instance [LawfulMonadLiftBindFunction (n := n) (fun _ _ f x => lift x >>= f)] [LawfulMonad n] :
    LawfulMonadLiftFunction lift where
  lift_pure {γ} a := by
    simpa using LawfulMonadLiftBindFunction.liftBind_pure (n := n)
      (liftBind := fun _ _ f x => lift x >>= f) (γ := γ) (δ := γ) pure a
  lift_bind {β γ} x g := by
    simpa using LawfulMonadLiftBindFunction.liftBind_bind (n := n)
      (liftBind := fun _ _ f x => lift x >>= f) (β := β) (γ := γ) (δ := γ) pure x g

theorem LawfulMonadLiftBindFunction.id [LawfulMonad m] :
    LawfulMonadLiftBindFunction (m := Id) (n := m) (fun _ _ f x => f x.run) where
  liftBind_pure := by simp
  liftBind_bind := by simp

instance {m : Type u → Type v} [Monad m] {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] [LawfulMonad n] :
    LawfulMonadLiftBindFunction (fun γ δ (f : γ → n δ) (x : m γ) => monadLift x >>= f) where
  liftBind_pure := by simp
  liftBind_bind := by simp

instance {n : Type u → Type w} [Monad n] [LawfulMonad n] :
    LawfulMonadLiftBindFunction (fun γ δ (f : γ → n δ) (x : Id γ) => f x.run) where
  liftBind_pure := by simp
  liftBind_bind := by simp

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] :
    LawfulMonadLiftBindFunction (m := m) (n := m) (fun _ _ => flip Bind.bind) where
  liftBind_pure := by simp [flip]
  liftBind_bind := by simp [flip]

end LiftBind

end Std.Internal
