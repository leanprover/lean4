/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.ExceptPost
public import Std.WP.Monad.Basic
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# WPMonad Instances

The weakest precondition interpretation of the base monads and of the monad transformers, together
with the `PredTrans` helpers that push a result type into an exception postcondition layer.

## Pre-defined instances

* `WPMonad Id Prop EPost.Nil` — pure computations.
* `WPMonad (StateT σ m) (σ → Pred) EPred` — stateful computations.
* `WPMonad (ExceptT ε m) Pred (EPost.Cons (ε → Pred) EPred)` — computations with exceptions.
* `WPMonad (OptionT m) Pred (EPost.Cons Pred EPred)` — computations with early termination.
* `WPMonad (ReaderT ρ m) (ρ → Pred) EPred` — reader computations.
* `WPMonad Option Prop Prop` — concrete early termination.
* `WPMonad (Except ε) Prop EPost⟨ε → Prop⟩` — concrete exception type.
* `WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.WP

variable {m : Type u → Type z}

/-- `Id`'s `WP` interpretation: `Prop` assertions and no exceptions. -/
@[instance_reducible] def Id.wpInst {α : Type u} : WP (Id α) α Prop EPost.Nil where
  wpTrans x := ⟨fun post _epost => post x⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x

/-- `Id` is a WPMonad with `Prop` assertions and no exceptions. -/
instance Id.instWPMonad : WPMonad Id.{u} Prop EPost.Nil where
  toWP _ := Id.wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl

/-- `MonadExceptOf` instance for the outermost exception layer:
`throw` invokes the head exception postcondition, `tryCatch` intercepts it. -/
instance {ε : Type u} {Pred : Type v} {EPred : Type w} :
    MonadExceptOf ε (PredTrans Pred (EPost.Cons (ε → Pred) EPred)) where
  throw e := ⟨fun _post epost => epost.head e⟩
  tryCatch x handle := ⟨fun post epost => x.apply post ⟨(fun e => (handle e).apply post epost), epost.tail⟩⟩

/-- `MonadExceptOf` instance lifted through an unrelated exception layer:
delegates to the inner instance, threading the extra exception postcondition. -/
instance {ε : Type u} {Pred : Type v} {EPred : Type w} {ε' : Type u}
    [MonadExceptOf ε (PredTrans Pred EPred)] :
    MonadExceptOf ε (PredTrans Pred (EPost.Cons (ε' → Pred) EPred)) where
  throw x := ⟨fun post epost => (throw (m := PredTrans Pred EPred) x).apply post epost.tail⟩
  tryCatch x handle := ⟨fun post epost =>
    (tryCatch (m := PredTrans Pred EPred)
      (⟨fun post' epost' => x.apply post' ⟨epost.head, epost'⟩⟩)
      (fun e => ⟨fun post' epost' => (handle e).apply post' ⟨epost.head, epost'⟩⟩)).apply
      post epost.tail⟩

/-- Adds an exception layer to a predicate transformer.

Given a transformer over `Except ε α`, produces one over `α` with an additional
exception postcondition for `ε`. The normal and error postconditions are combined
via `pushExcept`. -/
def PredTrans.pushExcept {α : Type u} {ε : Type v} {Pred : Type w} {EPred : Type z}
    (x : PredTrans Pred EPred (Except ε α)) : PredTrans Pred (EPost.Cons (ε → Pred) EPred) α :=
  ⟨fun post epost => x.apply (epost.pushExcept post) epost.tail⟩

@[simp, grind =]
theorem PredTrans.apply_pushExcept {α ε Pred EPred}
    (x : PredTrans Pred EPred (Except ε α)) (post : α → Pred)
    (epost : EPost.Cons (ε → Pred) EPred) :
    (PredTrans.pushExcept x).apply post epost = x.apply (epost.pushExcept post) epost.tail := rfl

/-- `ExceptT`'s `WP` interpretation: lift the base interpretation by adding an exception
postcondition layer. -/
@[instance_reducible] def ExceptT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPred] [WP (m (Except ε α)) (Except ε α) Pred EPred] :
    WP (ExceptT ε m α) α Pred (EPost.Cons (ε → Pred) EPred) where
  wpTrans x := PredTrans.pushExcept (WP.wpTrans x.run)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    simp only [PredTrans.apply_pushExcept]
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
      simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
    let hhead := hepost'.1
    let htail := hepost'.2
    apply WP.wp_consequence_econs (x := x.run)
    · intro r
      cases r with
      | ok a => exact hpost a
      | error el => exact hhead el
    · exact htail

/-- `ExceptT` lifts a `WPMonad` instance by adding an exception postcondition layer. -/
instance ExceptT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (ExceptT ε m) Pred (EPost.Cons (ε → Pred) EPred) where
  toWP _ := ExceptT.wpInst
  pure_le_wp_pure x := fun post epost =>
    WPMonad.pure_le_wp_pure (m := m) (Except.ok x) (epost.pushExcept post) epost.tail
  bind_le_wp_bind x f := fun post epost => by
    show (PredTrans.pushExcept (WP.wpTrans x.run)).apply _ epost ⊑ _
    simp only [PredTrans.apply_pushExcept]
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (epost.pushExcept post) epost.tail)
    apply WP.wp_consequence
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact WPMonad.pure_le_wp_pure (m := m) (Except.error el) (epost.pushExcept post) epost.tail

@[simp, grind =]
theorem ExceptT.wp_apply_eq {α ε Pred EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : ExceptT ε m α)
  (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    wp x post epost = wp x.run (epost.pushExcept post) epost.tail := rfl

/-- Adds an early-termination layer to a predicate transformer, modelling `Option` as
early termination. Given a transformer over `Option α`, produces one over `α` with an
additional exception postcondition for the `none` case. -/
def PredTrans.pushOption {α : Type u} {Pred : Type u} {EPred : Type v}
    (x : PredTrans Pred EPred (Option α)) : PredTrans Pred (EPost.Cons Pred EPred) α :=
  ⟨fun post epost => x.apply (epost.pushOption post) epost.tail⟩

/-- Unfolding `pushOption` through `apply`. -/
@[simp, grind =]
theorem PredTrans.apply_pushOption {α : Type u} {Pred : Type u} {EPred : Type v}
    (x : PredTrans Pred EPred (Option α)) (post : α → Pred)
    (epost : EPost.Cons Pred EPred) :
    (PredTrans.pushOption x).apply post epost = x.apply (epost.pushOption post) epost.tail := rfl

/-- `OptionT`'s `WP` interpretation: lift the base interpretation by adding a `PUnit` exception
postcondition layer. -/
@[instance_reducible] def OptionT.wpInst {Pred : Type u}
  [Assertion Pred] [Assertion EPred] [WP (m (Option α)) (Option α) Pred EPred] :
    WP (OptionT m α) α Pred (EPost.Cons Pred EPred) where
  wpTrans x := PredTrans.pushOption (WP.wpTrans x.run)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    simp only [PredTrans.apply_pushOption]
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := hepost
    apply WP.wp_consequence_econs (x := x.run)
    · intro r; cases r with
      | some a => exact hpost a
      | none => exact hepost'.1
    · exact hepost'.2

/-- `OptionT` lifts a `WPMonad` instance by adding a `PUnit` exception postcondition layer. -/
instance OptionT.instWPMonad {Pred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (OptionT m) Pred (EPost.Cons Pred EPred) where
  toWP _ := OptionT.wpInst
  pure_le_wp_pure x := fun post epost =>
    WPMonad.pure_le_wp_pure (m := m) (some x) (epost.pushOption post) epost.tail
  bind_le_wp_bind x f := fun post epost => by
    show (PredTrans.pushOption (WP.wpTrans x.run)).apply _ epost ⊑ _
    simp only [PredTrans.apply_pushOption]
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (epost.pushOption post) epost.tail)
    apply WP.wp_consequence
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact WPMonad.pure_le_wp_pure (m := m) none (epost.pushOption post) epost.tail

@[simp, grind =]
theorem OptionT.wp_apply_eq {α : Type u} {Pred : Type u} {EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : OptionT m α)
  (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    wp x post epost = wp x.run (epost.pushOption post) epost.tail := rfl

/-- `StateT`'s `WP` interpretation: lift the base interpretation by adding a state argument. -/
@[instance_reducible] def StateT.wpInst {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Assertion Pred] [Assertion EPred] [WP (m (α × σ)) (α × σ) Pred EPred] :
    WP (StateT σ m α) α (σ → Pred) EPred where
  wpTrans x := pushArg (WP.wpTrans <| x.run ·)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    apply WP.wp_consequence_econs (x := x.run s)
    · intro ⟨a, s'⟩
      exact hpost a s'
    · exact hepost

/-- `StateT` lifts a `WPMonad` instance by adding a state argument. -/
instance (priority := low) StateT.instWPMonad {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (StateT σ m) (σ → Pred) EPred where
  toWP _ := StateT.wpInst
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
@[instance_reducible] def ReaderT.wpInst {Pred : Type v}
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
  toWP _ := ReaderT.wpInst
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

/-- `Option`'s `WP` interpretation: `Prop` assertions and a single `Prop` exception postcondition. -/
@[instance_reducible] def Option.wpInst {α : Type u} : WP (Option α) α Prop Prop where
  wpTrans x := ⟨fun post epost => x.elim epost post⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | none => exact hepost
    | some a => exact hpost a

/-- `Option` is a WPMonad with `Prop` assertions and a single `Prop` exception postcondition. -/
instance Option.instWPMonad : WPMonad Option.{u} Prop Prop where
  toWP _ := Option.wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost => by cases x <;> exact id

/-- `Except ε`'s `WP` interpretation: `Prop` assertions and a single exception postcondition. -/
@[instance_reducible] def Except.wpInst {α : Type u} : WP (Except ε α) α Prop EPost⟨ε → Prop⟩ where
  wpTrans x := ⟨fun post epost => match x with
    | .ok a => post a
    | .error el => epost.head el⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | ok a => exact hpost a
    | error el =>
      have hhead : epost.head ⊑ epost'.head := by
        have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
          simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
        exact hepost'.1
      exact hhead el

/-- `Except ε` is a WPMonad with `Prop` assertions and a single exception postcondition. -/
instance Except.instWPMonad : WPMonad (Except ε) Prop EPost⟨ε → Prop⟩ where
  toWP _ := Except.wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost => by cases x <;> exact id

/-- `EStateM ε σ`'s `WP` interpretation combining state and exceptions. -/
@[instance_reducible] def EStateM.wpInst {α : Type} : WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop) where
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
  toWP _ := EStateM.wpInst
  pure_le_wp_pure x := fun post epost s => PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost s => by
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl

end Std.WP
