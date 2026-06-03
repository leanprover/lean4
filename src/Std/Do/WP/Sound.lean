/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP.Monad
public import Std.Do.Internal.Ensures

set_option linter.missingDocs true

/-!
# WP Soundness

`WPSound m ps` is the soundness bridge from `wp`-style reasoning to the operational
`Internal.Ensures` predicate: if `wp x` proves a postcondition `P`, then `x` is
`Internal.Ensures`-witnessed at `P`. Combined with `Internal.MayReturn x a`, this
yields `P a` for any value `a` that `x` may classically return.
-/

namespace Std.Do

/-- Soundness of `wp`: a `wp`-provable postcondition is `Internal.Ensures`-witnessed. -/
public class WPSound (m : Type u → Type v) (ps : outParam PostShape.{u}) [Monad m] [WP m ps] where
  /-- A `wp`-provable postcondition refines `x` via `Internal.Ensures`. -/
  ensures_of_wp {α : Type u} {x : m α} {P : α → Prop} :
     (⊢ₛ wp⟦x⟧ (⇓? a => ⌜P a⌝)) → Internal.Ensures P x

/--
From a `wp`-provable postcondition and an `Internal.MayReturn` witness, conclude `P`
at that value.
-/
public theorem WPSound.of_wp [Monad m] [WP m ps] [WPSound m ps]
    {α : Type u} {x : m α} {a : α} {P : α → Prop}
    (hmay : Internal.MayReturn x a) (hwp : ⊢ₛ wp⟦x⟧ (⇓? a => ⌜P a⌝)) : P a :=
  hmay.imp (WPSound.ensures_of_wp hwp)

/--
From a `wp`-provable postcondition and a `MonadAttach.CanReturn` witness, conclude `P`
at that value. Convenient when the monad has a `LawfulMonadAttach` instance, since
`CanReturn` is typically definitional.
-/
public theorem WPSound.of_wp_canReturn [Monad m] [LawfulMonad m] [WP m ps] [WPSound m ps]
    [MonadAttach m] [LawfulMonadAttach m]
    {α : Type u} {x : m α} {a : α} {P : α → Prop}
    (hcan : MonadAttach.CanReturn x a) (hwp : ⊢ₛ wp⟦x⟧ (⇓? a => ⌜P a⌝)) : P a :=
  WPSound.of_wp (Internal.MayReturn.of_canReturn hcan) hwp

public instance : WPSound Id .pure where
  ensures_of_wp hwp := ⟨⟨pure ⟨_, by simpa [WP.wp] using! hwp⟩, ⟨fun {_} _ => rfl⟩⟩⟩

public instance [Monad m] [WP m ps] [WPSound m ps] :
    WPSound (ReaderT ρ m) (.arg ρ ps) where
  ensures_of_wp hwp := by
    obtain ⟨X, hX⟩ := Classical.skolem.mp fun r =>
      (WPSound.ensures_of_wp (m := m) (ps := ps) (hwp r)).exists_refinement
    exact ⟨X, ⟨fun {β} k =>funext fun r => (hX r).bind_eq (fun a => (k a).run r)⟩⟩

public instance [Monad m] [LawfulMonad m] [WP m ps] [WPSound m ps] :
    WPSound (StateT σ m) (.arg σ ps) where
  ensures_of_wp {α} {x} {P} hwp := by
    obtain ⟨X, hX⟩ := Classical.skolem.mp fun s =>
      (WPSound.ensures_of_wp (m := m) (ps := ps) (hwp s)).exists_refinement
    refine ⟨⟨fun s => X s >>= fun r => pure (⟨r.val.1, r.property⟩, r.val.2), ⟨fun {β} k =>funext fun s => ?_⟩⟩⟩
    show (X s >>= fun r : {p : α × σ // P p.1} => pure (⟨r.val.1, r.property⟩, r.val.2)) >>=
         (fun (b : {a // P a} × σ) => (k b.1.val).run b.2) =
         x.run s >>= (fun (a : α × σ) => (k a.1).run a.2)
    rw [bind_assoc]; simp only [pure_bind]
    exact (hX s).bind_eq (fun r : α × σ => (k r.1).run r.2)

public instance [Monad m] [LawfulMonad m] [WP m .pure] [WPSound m .pure] :
    WPSound (ExceptT ε m) (.except ε .pure) where
  ensures_of_wp {α} {x} {P} hwp := by
    have hwp_inner : ⊢ₛ wp⟦x.run⟧
        (⇓? r => ⌜match r with | .ok a => P a | .error _ => True⌝) := by
      simp only [WP.wp, PredTrans.apply_pushExcept, ExceptConds.fst_true, ExceptConds.snd_true] at hwp
      apply SPred.entails.trans hwp; apply (wp x.run).mono
      simp [PostCond.entails]; intro r <;> cases r <;> simp
    obtain ⟨X, hX⟩ := (WPSound.ensures_of_wp (m := m) (ps := .pure) hwp_inner).exists_refinement
    refine ⟨⟨ExceptT.mk (X >>= fun ⟨r, h⟩ => match r, h with
      | .ok a, hp => pure (.ok ⟨a, hp⟩)
      | .error e, _ => pure (.error e)), ⟨fun {β} k =>?_⟩⟩⟩
    show ExceptT.mk _ >>= _ = x >>= k
    simp only [Bind.bind, ExceptT.bind, ExceptT.mk]; rw [bind_assoc]
    refine Eq.trans ?_ (hX.bind_eq (β := Except ε β) (ExceptT.bindCont k))
    exact bind_congr fun ⟨r, _⟩ => by cases r <;> simp [pure_bind, ExceptT.bindCont]

public instance [Monad m] [LawfulMonad m] [WP m .pure] [WPSound m .pure] :
    WPSound (OptionT m) (.except PUnit .pure) where
  ensures_of_wp {α} {x} {P} hwp := by
    have hwp_inner : ⊢ₛ wp⟦x.run⟧
        (⇓? r => ⌜match r with | some a => P a | none => True⌝) := by
      simp only [WP.wp, PredTrans.apply_pushOption, ExceptConds.fst_true, ExceptConds.snd_true] at hwp
      apply SPred.entails.trans hwp; apply (wp x.run).mono
      simp [PostCond.entails]; intro r <;> cases r <;> simp
    obtain ⟨X, hX⟩ := (WPSound.ensures_of_wp (m := m) (ps := .pure) hwp_inner).exists_refinement
    refine ⟨⟨OptionT.mk (X >>= fun ⟨r, h⟩ => match r, h with
      | some a, hp => pure (some ⟨a, hp⟩)
      | none, _ => pure none), ⟨fun {β} k =>?_⟩⟩⟩
    show OptionT.mk _ >>= _ = x >>= k
    simp only [Bind.bind, OptionT.bind, OptionT.mk]; rw [bind_assoc]
    refine Eq.trans ?_
      (hX.bind_eq (β := Option β) (fun r => match r with | some a => (k a).run | none => pure none))
    exact bind_congr fun ⟨r, _⟩ => by cases r <;> simp [pure_bind, OptionT.run]

/--
Soundness lemma for `Id.run`. Derived from `WPSound.of_wp_canReturn`: `Id.run prog = x`
is the `MonadAttach.CanReturn prog x` witness.
-/
public theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : _root_.Id α}
    (h : _root_.Id.run prog = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⟨P a⟩)) → P x := fun hwp =>
  WPSound.of_wp_canReturn (m := _root_.Id) (P := P) (x := prog) (a := x) h hwp

end Std.Do
