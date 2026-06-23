/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP.Monad
public import Std.Do.Internal.Ensures
public import Init.Control.Lawful.MonadAttach.Instances

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

public instance : WPSound (EStateM ε σ) (.except ε (.arg σ .pure)) where
  ensures_of_wp {α} {x} {P} hwp :=
    Internal.Ensures.canReturn.weaken fun a (hcan : MonadAttach.CanReturn x a) => by
      obtain ⟨s, s', heq⟩ := hcan
      have hs := hwp s True.intro
      simp only [WP.wp, PredTrans.apply] at hs
      rw [heq] at hs
      exact hs

/--
Soundness lemma for `Id.run`. Derived from `WPSound.of_wp_canReturn`: `Id.run prog = x`
is the `MonadAttach.CanReturn prog x` witness.
-/
public theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : _root_.Id α}
    (h : _root_.Id.run prog = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⟨P a⟩)) → P x := fun hwp =>
  WPSound.of_wp_canReturn (m := _root_.Id) (P := P) (x := prog) (a := x) h hwp

/-! ### Per-transformer soundness lemmas

For each transformer `T`, `T.ensures_of_wp_run` produces an `Internal.Ensures` over the post-run
computation `prog.run «args» : m _`. `T.of_wp_run` further collapses this to a pure proposition
`P a` when the base monad `m` has `LawfulMonadAttach` and the caller can supply a
`MonadAttach.CanReturn` witness — the natural generalization of the `Id`-specialized
`*.of_wp_run_eq` family below.
-/

/--
A `wp`-provable postcondition refines the post-run computation `prog.run r : m α`
via `Internal.Ensures`.
-/
public theorem ReaderT.ensures_of_wp_run [Monad m] [WP m ps] [WPSound m ps]
    {α : Type u} {ρ : Type u} {prog : ReaderT ρ m α} (r : ρ) (P : α → Prop)
    (hwp : ⊢ₛ wp⟦prog⟧ (⇓? a => ⌜P a⌝) r) :
    Internal.Ensures P (prog.run r) := by
  apply WPSound.ensures_of_wp
  simp only [WP.wp, PredTrans.apply_pushArg] at hwp
  exact hwp

/--
Pure-proposition soundness: from a `MonadAttach.CanReturn` witness for `prog.run r` and a
`wp`-provable postcondition, conclude `P a`.
-/
public theorem ReaderT.of_wp_run [Monad m] [LawfulMonad m] [WP m ps] [WPSound m ps]
    [MonadAttach m] [LawfulMonadAttach m]
    {α : Type u} {ρ : Type u} {prog : ReaderT ρ m α} {r : ρ} {a : α} (P : α → Prop)
    (hcan : MonadAttach.CanReturn (prog.run r) a)
    (hwp : ⊢ₛ wp⟦prog⟧ (⇓? a => ⌜P a⌝) r) : P a :=
  (Internal.MayReturn.of_canReturn hcan).imp (ReaderT.ensures_of_wp_run r P hwp)

/-- Soundness lemma for `ReaderM.run`: `Id`-specialization of `ReaderT.of_wp_run`. -/
public theorem ReaderM.of_wp_run_eq {α ρ : Type u} {x : α} {r : ρ} {prog : ReaderM ρ α}
    (h : ReaderT.run prog r = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a _ => ⌜P a⌝) r) → P x := fun hwp =>
  ReaderT.of_wp_run (m := _root_.Id) (a := x) P h hwp

/--
A `wp`-provable postcondition refines the post-run computation `prog.run s : m (α × σ)`
via `Internal.Ensures`.
-/
public theorem StateT.ensures_of_wp_run [Monad m] [WP m ps] [WPSound m ps]
    {α σ : Type u} {prog : StateT σ m α} (s : σ) (P : α × σ → Prop)
    (hwp : ⊢ₛ wp⟦prog⟧ (⇓ a s' => ⌜P (a, s')⌝) s) :
    Internal.Ensures P (prog.run s) := by
  apply WPSound.ensures_of_wp
  simp only [WP.wp, PredTrans.apply_pushArg] at hwp
  apply SPred.entails.trans hwp
  apply (wp (prog.run s)).mono
  refine ⟨fun _ => SPred.entails.refl _, by simp⟩

/-- Pure-proposition soundness for `StateT.run`, generalizing `StateM.of_wp_run_eq`. -/
public theorem StateT.of_wp_run [Monad m] [LawfulMonad m] [WP m ps] [WPSound m ps]
    [MonadAttach m] [LawfulMonadAttach m]
    {α σ : Type u} {prog : StateT σ m α} {s : σ} {p : α × σ} (P : α × σ → Prop)
    (hcan : MonadAttach.CanReturn (prog.run s) p)
    (hwp : ⊢ₛ wp⟦prog⟧ (⇓ a s' => ⌜P (a, s')⌝) s) : P p :=
  (Internal.MayReturn.of_canReturn hcan).imp (StateT.ensures_of_wp_run s P hwp)

/-- Soundness lemma for `StateM.run`: `Id`-specialization of `StateT.of_wp_run`. -/
public theorem StateM.of_wp_run_eq {α σ : Type} {x : α × σ} {s : σ} {prog : StateM σ α}
    (h : StateT.run prog s = x) (P : α × σ → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a s' => ⌜P (a, s')⌝) s) → P x := fun hwp =>
  StateT.of_wp_run (m := _root_.Id) (p := x) P h hwp

/-- Soundness lemma for `StateM.run'`: `Id`-specialization of `StateT.of_wp_run`. -/
public theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {s : σ} {prog : StateM σ α}
    (h : StateT.run' prog s = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝) s) → P x := fun hwp => by
  have hwp' : ⊢ₛ wp⟦prog⟧ (⇓ a s' => ⌜(fun p : α × σ => P p.1) (a, s')⌝) s := hwp
  have := StateT.of_wp_run (m := _root_.Id) (prog := prog) (s := s) (p := StateT.run prog s)
    (fun p => P p.1) rfl hwp'
  exact h ▸ this

/--
A `wp`-provable postcondition with split `.ok`/`.error` cases refines the post-run computation
`prog.run : m (Except ε α)` via `Internal.Ensures`.
-/
public theorem ExceptT.ensures_of_wp_run
    [Monad m] [LawfulMonad m] [WP m .pure] [WPSound m .pure]
    {ε α : Type u} {prog : ExceptT ε m α} (P : Except ε α → Prop)
    (hwp : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.error e)⌝⟩) :
    Internal.Ensures P prog.run := by
  apply WPSound.ensures_of_wp (m := m) (ps := .pure)
  simp only [WP.wp, PredTrans.apply_pushExcept] at hwp
  apply SPred.entails.trans hwp
  apply (wp prog.run).mono
  refine ⟨fun a => ?_, by simp⟩
  cases a <;> simp

/-- Pure-proposition soundness for `ExceptT.run`, generalizing `Except.of_wp_eq`. -/
public theorem ExceptT.of_wp_run
    [Monad m] [LawfulMonad m] [WP m .pure] [WPSound m .pure]
    [MonadAttach m] [LawfulMonadAttach m]
    {ε α : Type u} {prog : ExceptT ε m α} {x : Except ε α} (P : Except ε α → Prop)
    (hcan : MonadAttach.CanReturn prog.run x)
    (hwp : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.error e)⌝⟩) : P x :=
  (Internal.MayReturn.of_canReturn hcan).imp (ExceptT.ensures_of_wp_run P hwp)

/-- Soundness lemma for `Except`: `Id`-specialization of `ExceptT.of_wp_run`. -/
public theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
    (h : prog = x) (P : Except ε α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.error e)⌝⟩) → P x := fun hwp =>
  ExceptT.of_wp_run (m := _root_.Id) (prog := prog) (x := x) P h hwp

/-- Soundness lemma for `Except` without the equality hypothesis (deprecated). -/
@[deprecated Except.of_wp_eq (since := "2026-01-26")]
public theorem Except.of_wp {ε α : Type} {prog : Except ε α} (P : Except ε α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.error e)⌝⟩) → P prog :=
  Except.of_wp_eq rfl P

/--
A `wp`-provable postcondition with split `some`/`none` cases refines the post-run computation
`prog.run : m (Option α)` via `Internal.Ensures`.
-/
public theorem OptionT.ensures_of_wp_run
    [Monad m] [LawfulMonad m] [WP m .pure] [WPSound m .pure]
    {α : Type u} {prog : OptionT m α} (P : Option α → Prop)
    (hwp : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) :
    Internal.Ensures P prog.run := by
  apply WPSound.ensures_of_wp (m := m) (ps := .pure)
  simp only [WP.wp, PredTrans.apply_pushOption] at hwp
  apply SPred.entails.trans hwp
  apply (wp prog.run).mono
  refine ⟨fun a => ?_, by simp⟩
  cases a <;> simp

/-- Pure-proposition soundness for `OptionT.run`, generalizing `Option.of_wp_eq`. -/
public theorem OptionT.of_wp_run
    [Monad m] [LawfulMonad m] [WP m .pure] [WPSound m .pure]
    [MonadAttach m] [LawfulMonadAttach m]
    {α : Type u} {prog : OptionT m α} {x : Option α} (P : Option α → Prop)
    (hcan : MonadAttach.CanReturn prog.run x)
    (hwp : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) : P x :=
  (Internal.MayReturn.of_canReturn hcan).imp (OptionT.ensures_of_wp_run P hwp)

/-- Soundness lemma for `Option`: `Id`-specialization of `OptionT.of_wp_run`. -/
public theorem Option.of_wp_eq {α : Type} {x prog : Option α}
    (h : prog = x) (P : Option α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) → P x := fun hwp =>
  OptionT.of_wp_run (m := _root_.Id) (prog := prog) (x := x) P h hwp

end Std.Do
