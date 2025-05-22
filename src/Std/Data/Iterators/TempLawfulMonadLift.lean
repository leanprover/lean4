/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
prelude
import Init.Control.Basic
import Init.Control.Lawful.Basic

/-!
# LawfulMonadLift and LawfulMonadLiftT

This module provides classes asserting that `MonadLift` and `MonadLiftT` are lawful, which means
that `monadLift` is compatible with `pure` and `bind`.
-/

section MonadLift

/-- The `MonadLift` typeclass only contains the lifting operation. `LawfulMonadLift` further
  asserts that lifting commutes with `pure` and `bind`:
```
monadLift (pure a) = pure a
monadLift (ma >>= f) = monadLift ma >>= monadLift ∘ f
```
-/
class LawfulMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [inst : MonadLift m n] : Prop where
  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (pure a) = pure a
  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    inst.monadLift (ma >>= f) = inst.monadLift ma >>= (fun x => inst.monadLift (f x))

/-- The `MonadLiftT` typeclass only contains the transitive lifting operation.
  `LawfulMonadLiftT` further asserts that lifting commutes with `pure` and `bind`:
```
monadLift (pure a) = pure a
monadLift (ma >>= f) = monadLift ma >>= monadLift ∘ f
```
-/
class LawfulMonadLiftT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [inst : MonadLiftT m n] : Prop where
  /-- Lifting preserves `pure` -/
  monadLift_pure {α : Type u} (a : α) : inst.monadLift (pure a) = pure a
  /-- Lifting preserves `bind` -/
  monadLift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    inst.monadLift (ma >>= f) = monadLift ma >>= (fun x => monadLift (f x))

export LawfulMonadLiftT (monadLift_pure monadLift_bind)

end MonadLift

section Lemmas
universe u v w

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [MonadLiftT m n]
  [LawfulMonadLiftT m n] {α β : Type u}

theorem monadLift_map [LawfulMonad m] [LawfulMonad n] (f : α → β) (ma : m α) :
    monadLift (f <$> ma) = f <$> (monadLift ma : n α) := by
  rw [← bind_pure_comp, ← bind_pure_comp, monadLift_bind]
  simp only [bind_pure_comp, monadLift_pure]

theorem monadLift_seq [LawfulMonad m] [LawfulMonad n] (mf : m (α → β)) (ma : m α) :
    monadLift (mf <*> ma) = monadLift mf <*> (monadLift ma : n α) := by
  simp only [seq_eq_bind, monadLift_map, monadLift_bind]

theorem monadLift_seqLeft [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    monadLift (x <* y) = (monadLift x : n α) <* (monadLift y : n β) := by
  simp only [seqLeft_eq, monadLift_map, monadLift_seq]

theorem monadLift_seqRight [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    monadLift (x *> y) = (monadLift x : n α) *> (monadLift y : n β) := by
  simp only [seqRight_eq, monadLift_map, monadLift_seq]

/-! We duplicate the theorems for `monadLift` to `liftM` since `rw` matches on syntax only. -/

@[simp]
theorem liftM_pure (a : α) : liftM (pure a : m α) = pure (f := n) a :=
  monadLift_pure _

@[simp]
theorem liftM_bind (ma : m α) (f : α → m β) :
    liftM (n := n) (ma >>= f) = liftM ma >>= (fun a => liftM (f a)) :=
  monadLift_bind _ _

@[simp]
theorem liftM_map [LawfulMonad m] [LawfulMonad n] (f : α → β) (ma : m α) :
    liftM (f <$> ma) = f <$> (liftM ma : n α) :=
  monadLift_map _ _

@[simp]
theorem liftM_seq [LawfulMonad m] [LawfulMonad n] (mf : m (α → β)) (ma : m α) :
    liftM (mf <*> ma) = liftM mf <*> (liftM ma : n α) :=
  monadLift_seq _ _

@[simp]
theorem liftM_seqLeft [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    liftM (x <* y) = (liftM x : n α) <* (liftM y : n β) :=
  monadLift_seqLeft _ _

@[simp]
theorem liftM_seqRight [LawfulMonad m] [LawfulMonad n] (x : m α) (y : m β) :
    liftM (x *> y) = (liftM x : n α) *> (liftM y : n β) :=
  monadLift_seqRight _ _

end Lemmas

section MonadLiftFunction

class LawfulMonadLiftFunction {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] (lift : ⦃α : Type u⦄ → m α → n α) where
  lift_pure {α : Type u} (a : α) : lift (pure a) = pure a
  lift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    lift (ma >>= f) = lift ma >>= (fun x => lift (f x))

instance {m : Type u → Type v} [Monad m] : LawfulMonadLiftFunction (fun ⦃α⦄ => (id : m α → m α)) where
  lift_pure := by simp
  lift_bind := by simp

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

end MonadLiftFunction
