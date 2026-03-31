/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP.Monad
import Init.Control.MonadAttach

@[expose] public section

set_option linter.missingDocs true

/-!
# WP Adequacy

This module provides a small adequacy principle: a `mayThrow` postcondition is enough to recover
facts about values that `MonadAttach` says can actually be returned.
-/

namespace Std.Do

/-- A small adequacy principle: a `mayThrow` postcondition is enough to recover facts about
values that `MonadAttach` says can actually be returned. -/
class WPAdequacy (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m] [MonadAttach m]
    extends WP m ps where
  /-- If the weakest precondition says that `P` holds for all return values, then `P` holds for
  any value that `MonadAttach.CanReturn` says can be returned. -/
  adequate {α : Type u} {x : m α} {P : α → Prop} :
    (⊢ₛ wp⟦x⟧ (⇓? a => ⌜P a⌝)) → ∀ a, MonadAttach.CanReturn x a → P a

instance : WPAdequacy Id .pure where
  adequate := by
    intro α x P hwp a hret
    have hx : P x.run := by
      simpa [WP.wp] using hwp
    simpa [MonadAttach.CanReturn] using (hret ▸ hx)

instance [Monad m] [MonadAttach m] [WPAdequacy m ps] :
    WPAdequacy (StateT σ m) (.arg σ ps) where
  adequate := by
    intro α x P hwp a hret
    rcases hret with ⟨s, s', hret⟩
    have hwp' : ⊢ₛ wp⟦x.run s⟧ (⇓? r => ⌜P r.1⌝) := hwp s
    exact WPAdequacy.adequate (m := m) (ps := ps) (x := x.run s) (P := fun r => P r.1) hwp' (a, s') hret

instance [Monad m] [MonadAttach m] [WPAdequacy m ps] :
    WPAdequacy (ReaderT ρ m) (.arg ρ ps) where
  adequate := by
    intro α x P hwp a hret
    rcases hret with ⟨r, hret⟩
    have hwp' : ⊢ₛ wp⟦x.run r⟧ (⇓? a => ⌜P a⌝) := hwp r
    exact WPAdequacy.adequate (m := m) (ps := ps) (x := x.run r) (P := P) hwp' a hret

instance [Monad m] [MonadAttach m] [WPAdequacy m .pure] :
    WPAdequacy (ExceptT ε m) (.except ε .pure) where
  adequate := by
    intro α x P hwp a hret
    have hwp0 := hwp
    simp only [WP.wp, PredTrans.apply_pushExcept, ExceptConds.fst_true, ExceptConds.snd_true] at hwp0
    have hwp' : ⊢ₛ wp⟦x.run⟧ (⇓? r => ⌜match r with | .ok a => P a | .error _ => True⌝) := by
      apply SPred.entails.trans hwp0
      apply (wp x.run).mono
      simp [PostCond.entails]
      intro r <;> cases r <;> simp
    exact WPAdequacy.adequate (m := m) (ps := .pure) (x := x.run)
      (P := fun r => match r with | .ok a => P a | .error _ => True) hwp' (.ok a) hret

instance [Monad m] [MonadAttach m] [WPAdequacy m .pure] :
    WPAdequacy (OptionT m) (.except PUnit .pure) where
  adequate := by
    intro α x P hwp a hret
    have hwp0 := hwp
    simp only [WP.wp, PredTrans.apply_pushOption, ExceptConds.fst_true, ExceptConds.snd_true] at hwp0
    have hwp' : ⊢ₛ wp⟦x.run⟧ (⇓? r => ⌜match r with | some a => P a | none => True⌝) := by
      apply SPred.entails.trans hwp0
      apply (wp x.run).mono
      simp [PostCond.entails]
      intro r <;> cases r <;> simp
    exact WPAdequacy.adequate (m := m) (ps := .pure) (x := x.run)
      (P := fun r => match r with | some a => P a | none => True) hwp' (some a) hret

end Std.Do
