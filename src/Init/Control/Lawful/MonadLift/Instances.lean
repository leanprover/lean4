/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Paul Reichert
-/
module

prelude
public import all Init.Control.Option
public import all Init.Control.Except
public import all Init.Control.ExceptCps
public import all Init.Control.StateRef
public import all Init.Control.StateCps
public import all Init.Control.Id
public import Init.Control.Lawful.MonadLift.Lemmas
public import Init.Control.Lawful.Instances

public section

universe u v w x

variable {m : Type u → Type v} {n : Type u → Type w} {o : Type u → Type x}

variable (m n o) in
instance [Monad m] [Monad n] [Monad o] [MonadLift n o] [MonadLiftT m n]
    [LawfulMonadLift n o] [LawfulMonadLiftT m n] : LawfulMonadLiftT m o where
  monadLift_pure := fun a => by
    simp only [monadLift, LawfulMonadLift.monadLift_pure, liftM_pure]
  monadLift_bind := fun ma f => by
    simp only [monadLift, LawfulMonadLift.monadLift_bind, liftM_bind]

variable (m) in
instance [Monad m] : LawfulMonadLiftT m m where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

namespace StateT

variable [Monad m] [LawfulMonad m]

instance {σ : Type u} : LawfulMonadLift m (StateT σ m) where
  monadLift_pure _ := by ext; simp [MonadLift.monadLift]
  monadLift_bind _ _ := by ext; simp [MonadLift.monadLift]

end StateT

namespace ReaderT

variable [Monad m]

instance {ρ : Type u} : LawfulMonadLift m (ReaderT ρ m) where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

end ReaderT

namespace OptionT

variable [Monad m] [LawfulMonad m]

@[simp]
theorem lift_pure {α : Type u} (a : α) : OptionT.lift (pure a : m α) = pure a := by
  simp only [OptionT.lift, OptionT.mk, bind_pure_comp, map_pure, pure, OptionT.pure]

@[simp]
theorem lift_bind {α β : Type u} (ma : m α) (f : α → m β) :
    OptionT.lift (ma >>= f) = OptionT.lift ma >>= (fun a => OptionT.lift (f a)) := by
  simp only [instMonad, OptionT.bind, OptionT.mk, OptionT.lift, bind_pure_comp, bind_map_left,
    map_bind]

instance : LawfulMonadLift m (OptionT m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

end OptionT

namespace ExceptT

variable [Monad m] [LawfulMonad m]

@[simp]
theorem lift_bind {α β ε : Type u} (ma : m α) (f : α → m β) :
    ExceptT.lift (ε := ε) (ma >>= f) = ExceptT.lift ma >>= (fun a => ExceptT.lift (f a)) := by
  simp only [instMonad, ExceptT.bind, mk, ExceptT.lift, bind_map_left, ExceptT.bindCont, map_bind]

instance : LawfulMonadLift m (ExceptT ε m) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

instance : LawfulMonadLift (Except ε) (ExceptT ε m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, mk, pure, Except.pure, ExceptT.pure]
  monadLift_bind ma _ := by
    simp only [instMonad, ExceptT.bind, mk, MonadLift.monadLift, pure_bind, ExceptT.bindCont,
      Except.instMonad, Except.bind]
    rcases ma with _ | _ <;> simp

end ExceptT

namespace StateRefT'

instance {ω σ : Type} {m : Type → Type} [Monad m] : LawfulMonadLift m (StateRefT' ω σ m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold StateRefT'.lift ReaderT.pure
    simp only
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold StateRefT'.lift ReaderT.bind
    simp only

end StateRefT'

namespace StateCpsT

instance {σ : Type u} [Monad m] [LawfulMonad m] : LawfulMonadLift m (StateCpsT σ m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold StateCpsT.lift
    simp only [pure_bind]
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold StateCpsT.lift
    simp only [bind_assoc]

end StateCpsT

namespace ExceptCpsT

instance {ε : Type u} [Monad m] [LawfulMonad m] : LawfulMonadLift m (ExceptCpsT ε m) where
  monadLift_pure _ := by
    simp only [MonadLift.monadLift, pure]
    unfold ExceptCpsT.lift
    simp only [pure_bind]
  monadLift_bind _ _ := by
    simp only [MonadLift.monadLift, bind]
    unfold ExceptCpsT.lift
    simp only [bind_assoc]

end ExceptCpsT

namespace Id

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT Id m where
  monadLift_pure a := by simp [monadLift]
  monadLift_bind a f := by simp [monadLift]

end Id
