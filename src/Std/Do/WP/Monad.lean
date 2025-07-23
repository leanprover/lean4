/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP.Basic
import all Std.Do.WP.Basic

@[expose] public section

/-!
# Monad morphisms and weakest precondition interpretations

A `WP m ps` is a `WPMonad m ps` if the interpretation `WP.wp` is also a monad morphism, that is,
it preserves `pure` and `bind`.
-/

namespace Std.Do

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

/--
  A `WP` that is also a monad morphism, preserving `pure` and `bind`. (They all are.)
-/
class WPMonad (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m]
  extends LawfulMonad m, WP m ps where
  wp_pure : ∀ {α} (a : α), wp (pure a) = pure a
  wp_bind : ∀ {α β} (x : m α) (f : α → m β), wp (do let a ← x; f a) = do let a ← wp x; wp (f a)

theorem WPMonad.wp_map [Monad m] [WPMonad m ps] (f : α → β) (x : m α) :
  wp (f <$> x) = f <$> wp x := by simp [← bind_pure_comp, wp_pure, wp_bind]

theorem WPMonad.wp_seq [Monad m] [WPMonad m ps] (f : m (α → β)) (x : m α) :
  wp (f <*> x) = wp f <*> wp x := by simp [← bind_map, wp_map, wp_bind]

open WPMonad

instance Id.instWPMonad : WPMonad Id .pure where
  wp_pure a := by simp only [wp, PredTrans.pure, Pure.pure, Id.run]
  wp_bind x f := by simp only [wp, PredTrans.pure, Bind.bind, Id.run, PredTrans.bind]

instance StateT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  wp_pure a := by ext; simp only [wp, pure, StateT.pure, WPMonad.wp_pure, PredTrans.pure,
    PredTrans.pushArg_apply]
  wp_bind x f := by ext; simp only [wp, bind, StateT.bind, WPMonad.wp_bind, PredTrans.bind,
    PredTrans.pushArg_apply]

instance ReaderT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  wp_pure a := by ext; simp only [wp, pure, ReaderT.pure, WPMonad.wp_pure, PredTrans.pure,
    PredTrans.pushArg_apply, PredTrans.map_apply]
  wp_bind x f := by ext; simp only [wp, bind, ReaderT.bind, WPMonad.wp_bind, PredTrans.bind,
    PredTrans.pushArg_apply, PredTrans.map_apply]

instance ExceptT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  wp_pure a := by ext; simp only [wp, pure, ExceptT.pure, ExceptT.mk, WPMonad.wp_pure,
    PredTrans.pure, PredTrans.pushExcept_apply]
  wp_bind x f := by
    ext Q
    simp only [wp, bind, ExceptT.bind, ExceptT.mk, WPMonad.wp_bind, PredTrans.bind,
      ExceptT.bindCont, PredTrans.pushExcept_apply]
    congr
    ext b
    cases b
    case error a => simp [wp_pure]
    case ok a => rfl

instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp_pure a := by simp only [wp, pure, EStateM.pure, PredTrans.pure]
  wp_bind x f := by
    ext Q : 2
    simp only [wp, bind, EStateM.bind, PredTrans.bind]
    ext s : 1
    cases (x s) <;> rfl

instance Except.instWPMonad : WPMonad (Except ε) (.except ε .pure) where
  wp_pure a := rfl
  wp_bind x f := by cases x <;> rfl

instance State.instWPMonad : WPMonad (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonad : WPMonad (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
