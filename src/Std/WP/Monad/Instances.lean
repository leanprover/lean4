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
* `WPMonad (StateT σ m) (σ → Pred) EPred` — stateful computations.
* `WPMonad (ExceptT ε m) Pred ((ε → Pred) × EPred)` — computations with exceptions.
* `WPMonad (OptionT m) Pred ((Unit → Pred) × EPred)` — computations with early termination.
* `WPMonad (ReaderT ρ m) (ρ → Pred) EPred` — reader computations.
* `WPMonad Option Prop (Unit → Prop)` — concrete early termination.
* `WPMonad (Except ε) Prop (ε → Prop)` — concrete exception type.
* `WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.WP

variable {m : Type u → Type z}

/-- `Id`'s `WP` interpretation: `Prop` assertions and no exceptions. -/
instance Id.wpInst {α : Type u} : WP (Id α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _epost => post x⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x

/-- `Id` is a WPMonad with `Prop` assertions and no exceptions. -/
instance Id.instWPMonad : WPMonad Id.{u} Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl

/-- `ExceptT`'s `WP` interpretation: lift the base interpretation by adding an exception
postcondition layer. -/
instance ExceptT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPred] [WP (m (Except ε α)) (Except ε α) Pred EPred] :
    WP (ExceptT ε m α) α Pred ((ε → Pred) × EPred) where
  wpTrans x := PredTrans.pushExceptT (WP.wpTrans x.run)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    simp only [PredTrans.apply_pushExceptT]
    apply WP.wp_consequence_econs (x := x.run)
    · intro r
      cases r with
      | ok a => exact hpost a
      | error el => exact hepost.left el
    · exact hepost.right

/-- `ExceptT` lifts a `WPMonad` instance by adding an exception postcondition layer. -/
instance ExceptT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (ExceptT ε m) Pred ((ε → Pred) × EPred) where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post epost =>
    WPMonad.pure_le_wp_pure (m := m) (Except.ok x) (pushExcept post epost.fst) epost.snd
  bind_le_wp_bind x f := fun post epost => by
    show (PredTrans.pushExceptT (WP.wpTrans x.run)).apply _ epost ⊑ _
    simp only [PredTrans.apply_pushExceptT]
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (pushExcept post epost.fst) epost.snd)
    apply WP.wp_consequence
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact WPMonad.pure_le_wp_pure (m := m) (Except.error el) (pushExcept post epost.fst) epost.snd

@[simp, grind =]
theorem ExceptT.wp_apply_eq {α ε Pred EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : ExceptT ε m α)
  (post : α → Pred) (epost : (ε → Pred) × EPred) :
    wp x post epost = wp x.run (pushExcept post epost.fst) epost.snd := rfl

/-- `OptionT`'s `WP` interpretation: lift the base interpretation by adding a `Unit` exception
postcondition layer. -/
instance OptionT.wpInst {Pred : Type u}
  [Assertion Pred] [Assertion EPred] [WP (m (Option α)) (Option α) Pred EPred] :
    WP (OptionT m α) α Pred ((Unit → Pred) × EPred) where
  wpTrans x := PredTrans.pushOptionT (WP.wpTrans x.run)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    simp only [PredTrans.apply_pushOptionT]
    apply WP.wp_consequence_econs (x := x.run)
    · intro r; cases r with
      | some a => exact hpost a
      | none => exact hepost.left ()
    · exact hepost.right

/-- `OptionT` lifts a `WPMonad` instance by adding a `Unit` exception postcondition layer. -/
instance OptionT.instWPMonad {Pred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (OptionT m) Pred ((Unit → Pred) × EPred) where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post epost =>
    WPMonad.pure_le_wp_pure (m := m) (some x) (pushOption post epost.fst) epost.snd
  bind_le_wp_bind x f := fun post epost => by
    show (PredTrans.pushOptionT (WP.wpTrans x.run)).apply _ epost ⊑ _
    simp only [PredTrans.apply_pushOptionT]
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (pushOption post epost.fst) epost.snd)
    apply WP.wp_consequence
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact WPMonad.pure_le_wp_pure (m := m) none (pushOption post epost.fst) epost.snd

@[simp, grind =]
theorem OptionT.wp_apply_eq {α : Type u} {Pred : Type u} {EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : OptionT m α)
  (post : α → Pred) (epost : (Unit → Pred) × EPred) :
    wp x post epost = wp x.run (pushOption post epost.fst) epost.snd := rfl

/-- `StateT`'s `WP` interpretation: lift the base interpretation by adding a state argument. -/
instance StateT.wpInst {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Assertion Pred] [Assertion EPred] [WP (m (α × σ)) (α × σ) Pred EPred] :
    WP (StateT σ m α) α (σ → Pred) EPred where
  wpTrans x := PredTrans.pushArg (WP.wpTrans <| x.run ·)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    apply WP.wp_consequence_econs (x := x.run s)
    · intro ⟨a, s'⟩
      exact hpost a s'
    · exact hepost

/-- `StateT` lifts a `WPMonad` instance by adding a state argument. -/
instance (priority := low) StateT.instWPMonad {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (StateT σ m) (σ → Pred) EPred where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post epost s =>
    WPMonad.pure_le_wp_pure (m := m) (x, s) (fun p => post p.1 p.2) epost
  bind_le_wp_bind x f := fun post epost s => by
    apply WPMonad.bind_le_wp_bind

@[simp, grind =]
theorem StateT.wp_apply_eq {σ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : StateT σ m α)
  (post : α → σ → Pred) (epost : EPred) (s : σ) :
    wp x post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

/-- `ReaderT`'s `WP` interpretation: lift the base interpretation by adding a reader argument. -/
instance ReaderT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPred] [WP (m α) α Pred EPred] :
    WP (ReaderT ρ m α) α (ρ → Pred) EPred where
  wpTrans x := ⟨fun post epost r => wp (x.run r) (fun a => post a r) epost⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost r => by
    apply WP.wp_consequence_econs (x := x.run r)
    · intro a
      exact hpost a r
    · exact hepost

/-- `ReaderT` lifts a `WPMonad` instance by adding a reader argument. -/
instance ReaderT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (ReaderT ρ m) (ρ → Pred) EPred where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post epost r =>
    WPMonad.pure_le_wp_pure (m := m) x (fun a => post a r) epost
  bind_le_wp_bind x f := fun post epost r => by
    apply PartialOrder.rel_trans
    · apply WP.wp_consequence
      intro a; exact PartialOrder.rel_refl
    · apply WPMonad.bind_le_wp_bind

@[simp, grind =]
theorem ReaderT.wp_apply_eq {ρ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : ReaderT ρ m α)
  (post : α → ρ → Pred) (epost : EPred) (r : ρ) :
    wp x post epost r = wp (x.run r) (fun a => post a r) epost := rfl

/-!
## Type Alias Instances

`WPMonad` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Option`'s `WP` interpretation: `Prop` assertions and a `Unit`-indexed exception
postcondition. -/
instance Option.wpInst {α : Type u} : WP (Option α) α Prop (Unit → Prop) where
  wpTrans x := ⟨fun post epost => pushOption post epost x⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | none => exact hepost ()
    | some a => exact hpost a

/-- `Option` is a WPMonad with `Prop` assertions and a `Unit`-indexed exception postcondition. -/
instance Option.instWPMonad : WPMonad Option.{u} Prop (Unit → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost => by cases x <;> exact id

/-- `Except ε`'s `WP` interpretation: `Prop` assertions and an `ε`-indexed exception
postcondition. -/
instance Except.wpInst {α : Type u} : WP (Except ε α) α Prop (ε → Prop) where
  wpTrans x := ⟨fun post epost => pushExcept post epost x⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | ok a => exact hpost a
    | error el => exact hepost el

/-- `Except ε` is a WPMonad with `Prop` assertions and an `ε`-indexed exception postcondition. -/
instance Except.instWPMonad : WPMonad (Except ε) Prop (ε → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost => by cases x <;> exact id

/-- `EStateM ε σ`'s `WP` interpretation combining state and exceptions. -/
instance EStateM.wpInst {α : Type} : WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop) where
  wpTrans x := ⟨fun post epost s => match x s with
    | .ok a s' => post a s'
    | .error el s' => epost el s'⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    cases hxs : x s with
    | ok a s' =>
      simpa [hxs] using hpost a s'
    | error el s' =>
      simpa [hxs] using hepost el s'

/-- `EStateM ε σ` is a WPMonad combining state and exceptions. -/
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure x := fun post epost s => PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost s => by
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl

end Std.WP
