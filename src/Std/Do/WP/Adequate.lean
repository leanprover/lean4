/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP.Monad
public import Std.Do.Internal.Ensures.Def

set_option linter.missingDocs true

/-!
# WP Adequacy

`WPAdequate m ps` provides a soundness bridge: if `wp x` proves a postcondition `P`,
then `x` is `Internal.Ensures`-witnessed at `P`. Combined with `Internal.MayReturn x a`,
this yields `P a` for any value `a` that `x` may classically return.
-/

namespace Std.Do

/-- A small adequacy principle: a `wp`-provable postcondition is `Internal.Ensures`-witnessed. -/
public class WPAdequate (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m] [WP m ps] where
  /-- A `wp`-provable postcondition refines `x` via `Internal.Ensures`. -/
  ensures_of_wp {α : Type u} {x : m α} {P : α → Prop} :
     (⊢ₛ wp⟦x⟧ (⇓? a => ⌜P a⌝)) → Internal.Ensures P x

public instance : WPAdequate Id .pure where
  ensures_of_wp hwp := ⟨⟨pure ⟨_, by simpa [WP.wp] using! hwp⟩, ⟨fun {_} _ => rfl⟩⟩⟩

public instance [Monad m] [WP m ps] [WPAdequate m ps] :
    WPAdequate (ReaderT ρ m) (.arg ρ ps) where
  ensures_of_wp hwp := by
    obtain ⟨X, hX⟩ := Classical.skolem.mp fun r =>
      (WPAdequate.ensures_of_wp (m := m) (ps := ps) (hwp r)).exists_refinement
    exact ⟨X, ⟨fun {β} k =>funext fun r => (hX r).bind_eq (fun a => (k a).run r)⟩⟩

public instance [Monad m] [LawfulMonad m] [WP m ps] [WPAdequate m ps] :
    WPAdequate (StateT σ m) (.arg σ ps) where
  ensures_of_wp {α} {x} {P} hwp := by
    obtain ⟨X, hX⟩ := Classical.skolem.mp fun s =>
      (WPAdequate.ensures_of_wp (m := m) (ps := ps) (hwp s)).exists_refinement
    refine ⟨⟨fun s => X s >>= fun r => pure (⟨r.val.1, r.property⟩, r.val.2), ⟨fun {β} k =>funext fun s => ?_⟩⟩⟩
    show (X s >>= fun r : {p : α × σ // P p.1} => pure (⟨r.val.1, r.property⟩, r.val.2)) >>=
         (fun (b : {a // P a} × σ) => (k b.1.val).run b.2) =
         x.run s >>= (fun (a : α × σ) => (k a.1).run a.2)
    rw [bind_assoc]; simp only [pure_bind]
    exact (hX s).bind_eq (fun r : α × σ => (k r.1).run r.2)

public instance [Monad m] [LawfulMonad m] [WP m .pure] [WPAdequate m .pure] :
    WPAdequate (ExceptT ε m) (.except ε .pure) where
  ensures_of_wp {α} {x} {P} hwp := by
    have hwp_inner : ⊢ₛ wp⟦x.run⟧
        (⇓? r => ⌜match r with | .ok a => P a | .error _ => True⌝) := by
      simp only [WP.wp, PredTrans.apply_pushExcept, ExceptConds.fst_true, ExceptConds.snd_true] at hwp
      apply SPred.entails.trans hwp; apply (wp x.run).mono
      simp [PostCond.entails]; intro r <;> cases r <;> simp
    obtain ⟨X, hX⟩ := (WPAdequate.ensures_of_wp (m := m) (ps := .pure) hwp_inner).exists_refinement
    refine ⟨⟨ExceptT.mk (X >>= fun ⟨r, h⟩ => match r, h with
      | .ok a, hp => pure (.ok ⟨a, hp⟩)
      | .error e, _ => pure (.error e)), ⟨fun {β} k =>?_⟩⟩⟩
    show ExceptT.mk _ >>= _ = x >>= k
    simp only [Bind.bind, ExceptT.bind, ExceptT.mk]; rw [bind_assoc]
    refine Eq.trans ?_ (hX.bind_eq (β := Except ε β) (ExceptT.bindCont k))
    exact bind_congr fun ⟨r, _⟩ => by cases r <;> simp [pure_bind, ExceptT.bindCont]

public instance [Monad m] [LawfulMonad m] [WP m .pure] [WPAdequate m .pure] :
    WPAdequate (OptionT m) (.except PUnit .pure) where
  ensures_of_wp {α} {x} {P} hwp := by
    have hwp_inner : ⊢ₛ wp⟦x.run⟧
        (⇓? r => ⌜match r with | some a => P a | none => True⌝) := by
      simp only [WP.wp, PredTrans.apply_pushOption, ExceptConds.fst_true, ExceptConds.snd_true] at hwp
      apply SPred.entails.trans hwp; apply (wp x.run).mono
      simp [PostCond.entails]; intro r <;> cases r <;> simp
    obtain ⟨X, hX⟩ := (WPAdequate.ensures_of_wp (m := m) (ps := .pure) hwp_inner).exists_refinement
    refine ⟨⟨OptionT.mk (X >>= fun ⟨r, h⟩ => match r, h with
      | some a, hp => pure (some ⟨a, hp⟩)
      | none, _ => pure none), ⟨fun {β} k =>?_⟩⟩⟩
    show OptionT.mk _ >>= _ = x >>= k
    simp only [Bind.bind, OptionT.bind, OptionT.mk]; rw [bind_assoc]
    refine Eq.trans ?_
      (hX.bind_eq (β := Option β) (fun r => match r with | some a => (k a).run | none => pure none))
    exact bind_congr fun ⟨r, _⟩ => by cases r <;> simp [pure_bind, OptionT.run]

end Std.Do
