/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

prelude
public import Init.Control.Id
public import Init.Control.Lawful.Basic
public import Init.Control.Lawful.MonadLift.Basic

public section

universe u v w

theorem instMonadLiftTOfMonadLift_instMonadLiftTOfPure [Monad m] [Monad n] {_ : MonadLift m n}
    [LawfulMonadLift m n] : instMonadLiftTOfMonadLift Id m n = Id.instMonadLiftTOfPure := by
  have hext {a b : MonadLiftT Id n} (h : @a.monadLift = @b.monadLift) : a = b := by
    cases a <;> cases b <;> simp_all
  apply hext
  ext α x
  simp [monadLift, LawfulMonadLift.monadLift_pure]

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n] [MonadLiftT m n]
  [LawfulMonadLiftT m n] {α β : Type u}

theorem monadLift_map [LawfulMonad m] [LawfulMonad n] (f : α → β) (ma : m α) :
    monadLift (f <$> ma) = f <$> (monadLift ma : n α) := by
  rw [← bind_pure_comp, ← bind_pure_comp, monadLift_bind]
  simp only [bind_pure_comp, monadLift_pure]

theorem monadLift_seq [LawfulMonad m] [LawfulMonad n] (mf : m (α → β)) (ma : m α) :
    monadLift (mf <*> ma) = monadLift mf <*> (monadLift ma : n α) := by
  simp only [seq_eq_bind_map, monadLift_map, monadLift_bind]

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
