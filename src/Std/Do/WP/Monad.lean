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

set_option linter.missingDocs true

/-!
# Monad morphisms and weakest precondition interpretations

A `WP m ps` is a `WPMonad m ps` if the interpretation `WP.wp` is also a monad morphism, that is,
it preserves `pure` and `bind`.
-/

namespace Std.Do

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

/--
A monad with weakest preconditions (`WP`) that is also a monad morphism, preserving `pure` and
`bind`.

In practice, `mvcgen` is not useful for reasoning about programs in a monad that is without a
`WPMonad` instance. The specification lemmas for `Pure.pure` and `Bind.bind`, as well as those for
operators like `Functor.map`, require that their monad have a `WPMonad` instance.
-/
class WPMonad (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m]
  extends LawfulMonad m, WP m ps where
  /-- `WP.wp` preserves `pure`. -/
  wp_pure : ∀ {α} (a : α), wp (pure a) = pure a
  /-- `WP.wp` preserves `bind`. -/
  wp_bind : ∀ {α β} (x : m α) (f : α → m β), wp (do let a ← x; f a) = do let a ← wp x; wp (f a)

/-- `WP.wp` preserves `map`. -/
theorem WPMonad.wp_map [Monad m] [WPMonad m ps] (f : α → β) (x : m α) :
  wp (f <$> x) = f <$> wp x := by simp [← bind_pure_comp, wp_pure, wp_bind]

/-- `WP.wp` preserves `seq`. -/
theorem WPMonad.wp_seq [Monad m] [WPMonad m ps] (f : m (α → β)) (x : m α) :
  wp (f <*> x) = wp f <*> wp x := by simp [← bind_map, wp_map, wp_bind]

open WPMonad

instance Id.instWPMonad : WPMonad Id .pure where
  wp_pure a := by simp [wp]
  wp_bind x f := by simp [wp]

instance StateT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (StateT σ m) (.arg σ ps) where
  wp_pure a := by ext; simp [wp, wp_pure]
  wp_bind x f := by ext; simp [wp, wp_bind]

instance ReaderT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ReaderT ρ m) (.arg ρ ps) where
  wp_pure a := by ext; simp [wp, wp_pure]
  wp_bind x f := by ext; simp [wp, wp_bind]

instance ExceptT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (ExceptT ε m) (.except ε ps) where
  wp_pure a := by ext; simp [wp, wp_pure]
  wp_bind x f := by
    ext Q
    simp only [wp, ExceptT.run_bind, wp_bind, PredTrans.pushExcept_apply, PredTrans.bind_apply]
    congr
    ext b
    cases b
    case error a => simp [wp_pure]
    case ok a => rfl

instance OptionT.instWPMonad [Monad m] [WPMonad m ps] : WPMonad (OptionT m) (.except PUnit ps) where
  wp_pure a := by ext; simp [wp, wp_pure]
  wp_bind x f := by
    ext Q
    simp only [wp, OptionT.run_bind, Option.elimM, Option.elim, wp_bind, PredTrans.pushOption_apply, PredTrans.bind_apply]
    congr
    ext b
    cases b
    case none => simp [wp_pure]
    case some a => rfl

instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp_pure a := by ext Q : 1; simp only [wp, EStateM.run_pure, PredTrans.pure_apply]; rfl
  wp_bind x f := by
    ext Q : 2
    simp only [wp, EStateM.run_bind, PredTrans.bind_apply]
    simp only [PredTrans.apply]
    cases (x.run _) <;> rfl

instance Except.instWPMonad : WPMonad (Except ε) (.except ε .pure) where
  wp_pure a := rfl
  wp_bind x f := by cases x <;> rfl

instance Option.instWPMonad : WPMonad Option (.except PUnit .pure) where
  wp_pure a := rfl
  wp_bind x f := by cases x <;> rfl

instance State.instWPMonad : WPMonad (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WPMonad (StateT σ Id) (.arg σ .pure))
instance Reader.instWPMonad : WPMonad (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (.arg ρ .pure))
