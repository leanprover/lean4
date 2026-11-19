/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.EStack
public import Std.WP.Monad.Basic
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# WPMonad Instances

The weakest precondition interpretation of the base monads and of the monad transformers.

A monad that throws carries the exception postcondition itself. A transformer stacks a product
layer on the exception postcondition of the monad below it, and `EStack⟨⟩` closes the stack.

## Pre-defined instances

* `WPMonad Id Prop EStack⟨⟩` — pure computations.
* `WPMonad (StateT σ m) (σ → Pred) EPosts` — stateful computations.
* `WPMonad (ExceptT ε m) Pred ((ε → Pred) × EPosts)` — computations with exceptions.
* `WPMonad (OptionT m) Pred ((Unit → Pred) × EPosts)` — computations with early termination.
* `WPMonad (ReaderT ρ m) (ρ → Pred) EPosts` — reader computations.
* `WPMonad Option Prop (Unit → Prop)` — concrete early termination.
* `WPMonad (Except ε) Prop (ε → Prop)` — concrete exception type.
* `WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.WP

variable {m : Type u → Type z}

/-- `Id`'s `WP` interpretation: `Prop` assertions and no exceptions. -/
instance Id.wpInst {α : Type u} : WP (Id α) α Prop EStack⟨⟩ where
  trans x := PredTrans.mk (fun post _epost => post x) fun hpost _ => hpost x

theorem Id.wp_apply_eq {α : Type u} (x : Id α) (post : α → Prop) (eposts : EStack⟨⟩) :
    wp x post eposts = post x.run := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> rfl

/-- `Id` is a WPMonad with `Prop` assertions and no exceptions. -/
instance Id.instWPMonad : WPMonad Id.{u} Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> exact PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> exact PartialOrder.rel_refl

/-- `ExceptT`'s `WP` interpretation: lift the base interpretation by adding an exception
postcondition layer. -/
instance ExceptT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPosts] [WP (m (Except ε α)) (Except ε α) Pred EPosts] :
    WP (ExceptT ε m α) α Pred ((ε → Pred) × EPosts) where
  trans x := PredTrans.pushExceptT (WP.trans x.run)

@[simp, grind =]
theorem ExceptT.wp_apply_eq {α ε Pred EPosts}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] (x : ExceptT ε m α)
  (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    wp x post eposts = wp x.run (pushExcept post eposts.fst) eposts.snd := by
  simp only [WP.wp, WP.trans, PredTrans.apply_pushExceptT]

/-- `ExceptT` lifts a `WPMonad` instance by adding an exception postcondition layer. -/
instance ExceptT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] :
    WPMonad (ExceptT ε m) Pred ((ε → Pred) × EPosts) where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post eposts => by
    rw [ExceptT.wp_apply_eq]
    exact WPMonad.pure_le_wp_pure (m := m) (Except.ok x) (pushExcept post eposts.fst) eposts.snd
  bind_le_wp_bind x f := fun post eposts => by
    simp only [ExceptT.wp_apply_eq]
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (pushExcept post eposts.fst) eposts.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact WPMonad.pure_le_wp_pure (m := m) (Except.error el) (pushExcept post eposts.fst) eposts.snd

/-- `OptionT`'s `WP` interpretation: lift the base interpretation by adding a `Unit` exception
postcondition layer. -/
instance OptionT.wpInst {Pred : Type u}
  [Assertion Pred] [Assertion EPosts] [WP (m (Option α)) (Option α) Pred EPosts] :
    WP (OptionT m α) α Pred ((Unit → Pred) × EPosts) where
  trans x := PredTrans.pushOptionT (WP.trans x.run)

@[simp, grind =]
theorem OptionT.wp_apply_eq {α : Type u} {Pred : Type u} {EPosts}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] (x : OptionT m α)
  (post : α → Pred) (eposts : (Unit → Pred) × EPosts) :
    wp x post eposts = wp x.run (pushOption post eposts.fst) eposts.snd := by
  simp only [WP.wp, WP.trans, PredTrans.apply_pushOptionT]

/-- `OptionT` lifts a `WPMonad` instance by adding a `Unit` exception postcondition layer. -/
instance OptionT.instWPMonad {Pred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] :
    WPMonad (OptionT m) Pred ((Unit → Pred) × EPosts) where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post eposts => by
    rw [OptionT.wp_apply_eq]
    exact WPMonad.pure_le_wp_pure (m := m) (some x) (pushOption post eposts.fst) eposts.snd
  bind_le_wp_bind x f := fun post eposts => by
    simp only [OptionT.wp_apply_eq]
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (pushOption post eposts.fst) eposts.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact WPMonad.pure_le_wp_pure (m := m) none (pushOption post eposts.fst) eposts.snd

/-- `StateT`'s `WP` interpretation: lift the base interpretation by adding a state argument. -/
instance StateT.wpInst {EPosts : Type v} {σ : Type u} {Pred : Type w}
  [Assertion Pred] [Assertion EPosts] [WP (m (α × σ)) (α × σ) Pred EPosts] :
    WP (StateT σ m α) α (σ → Pred) EPosts where
  trans x := PredTrans.pushArg (WP.trans <| x.run ·)

@[simp, grind =]
theorem StateT.wp_apply_eq {σ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] (x : StateT σ m α)
  (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    wp x post eposts s = wp (x.run s) (fun (a, s) => post a s) eposts := by
  simp only [WP.wp, WP.trans, PredTrans.apply_pushArg]

/-- `StateT` lifts a `WPMonad` instance by adding a state argument. -/
instance (priority := low) StateT.instWPMonad {EPosts : Type v} {σ : Type u} {Pred : Type w}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] :
    WPMonad (StateT σ m) (σ → Pred) EPosts where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post eposts s => by
    rw [StateT.wp_apply_eq]
    exact WPMonad.pure_le_wp_pure (m := m) (x, s) (fun p => post p.1 p.2) eposts
  bind_le_wp_bind x f := fun post eposts s => by
    simp only [StateT.wp_apply_eq]
    exact WPMonad.bind_le_wp_bind (m := m) (x.run s) (fun p => (f p.1).run p.2)
      (fun p => post p.1 p.2) eposts

/-- `ReaderT`'s `WP` interpretation: lift the base interpretation by adding a reader argument. -/
instance ReaderT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPosts] [WP (m α) α Pred EPosts] :
    WP (ReaderT ρ m α) α (ρ → Pred) EPosts where
  trans x := PredTrans.mk (fun post eposts r => wp (x.run r) (fun a => post a r) eposts)
    fun hpost heposts r => WP.wp_monotone (fun a => hpost a r) heposts

@[simp, grind =]
theorem ReaderT.wp_apply_eq {ρ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] (x : ReaderT ρ m α)
  (post : α → ρ → Pred) (eposts : EPosts) (r : ρ) :
    wp x post eposts r = wp (x.run r) (fun a => post a r) eposts := by
  show (WP.trans x).apply post eposts r = _
  simp only [WP.trans, PredTrans.apply_mk]

/-- `ReaderT` lifts a `WPMonad` instance by adding a reader argument. -/
instance ReaderT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] :
    WPMonad (ReaderT ρ m) (ρ → Pred) EPosts where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post eposts r => by
    rw [ReaderT.wp_apply_eq]
    exact WPMonad.pure_le_wp_pure (m := m) x (fun a => post a r) eposts
  bind_le_wp_bind x f := fun post eposts r => by
    simp only [ReaderT.wp_apply_eq]
    exact WPMonad.bind_le_wp_bind (m := m) (x.run r) (fun a => (f a).run r) (fun a => post a r)
      eposts

/-!
## Type Alias Instances

`WPMonad` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Option`'s `WP` interpretation: `Prop` assertions and a `Unit`-indexed exception
postcondition. -/
instance Option.wpInst {α : Type u} : WP (Option α) α Prop (Unit → Prop) where
  trans x := PredTrans.mk (fun post eposts => pushOption post eposts x) fun hpost heposts => by
    cases x with
    | none => exact heposts ()
    | some a => exact hpost a

theorem Option.wp_apply_eq {α : Type u} (x : Option α) (post : α → Prop)
    (eposts : Unit → Prop) : wp x post eposts = pushOption post eposts x := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

/-- `Option` is a WPMonad with `Prop` assertions and a `Unit`-indexed exception postcondition. -/
instance Option.instWPMonad : WPMonad Option.{u} Prop (Unit → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> exact PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post eposts => by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk]
    cases x <;> exact id

/-- `Except ε`'s `WP` interpretation: `Prop` assertions and an `ε`-indexed exception
postcondition. -/
instance Except.wpInst {α : Type u} : WP (Except ε α) α Prop (ε → Prop) where
  trans x := PredTrans.mk (fun post eposts => pushExcept post eposts x) fun hpost heposts => by
    cases x with
    | ok a => exact hpost a
    | error el => exact heposts el

theorem Except.wp_apply_eq {α : Type u} (x : Except ε α) (post : α → Prop)
    (eposts : ε → Prop) : wp x post eposts = pushExcept post eposts x := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

/-- `Except ε` is a WPMonad with `Prop` assertions and an `ε`-indexed exception postcondition. -/
instance Except.instWPMonad : WPMonad (Except ε) Prop (ε → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> exact PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post eposts => by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk]
    cases x <;> exact id

/-- `EStateM ε σ`'s `WP` interpretation combining state and exceptions. -/
instance EStateM.wpInst {α : Type} : WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop) where
  trans x := PredTrans.mk (fun post eposts s => match x s with
    | .ok a s' => post a s'
    | .error el s' => eposts el s') fun hpost heposts s => by
    cases hxs : x s with
    | ok a s' =>
      simpa [hxs] using hpost a s'
    | error el s' =>
      simpa [hxs] using heposts el s'

theorem EStateM.wp_apply_eq {α : Type} (x : EStateM ε σ α) (post : α → σ → Prop)
    (eposts : ε → σ → Prop) (s : σ) :
    wp x post eposts s = match x s with
      | .ok a s' => post a s'
      | .error el s' => eposts el s' := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

/-- `EStateM ε σ` is a WPMonad combining state and exceptions. -/
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post eposts s => by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> exact PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post eposts s => by
    simp only [WP.wp, WP.trans, PredTrans.apply_mk]
    simp only [bind, EStateM.bind]
    cases (x s) <;> exact id

end Std.WP
