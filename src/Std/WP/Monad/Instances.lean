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
# MonadicWP Instances

The weakest precondition interpretation of the base monads and of the monad transformers.

A monad that throws carries the exception postcondition itself. A transformer stacks a product
layer on the exception postcondition of the monad below it, and `EStack⟨⟩` closes the stack.

Every interpretation here is a monad morphism (`MonadicWP.IsMonadMorphism`) and monotone
(`WP.IsMonotone`). A transformer is also a lax monad morphism over a base that is one.

## Pre-defined instances

* `MonadicWP Id Prop EStack⟨⟩` — pure computations.
* `MonadicWP (StateT σ m) (σ → Pred) EPosts` — stateful computations.
* `MonadicWP (ExceptT ε m) Pred ((ε → Pred) × EPosts)` — computations with exceptions.
* `MonadicWP (OptionT m) Pred ((Unit → Pred) × EPosts)` — computations with early termination.
* `MonadicWP (ReaderT ρ m) (ρ → Pred) EPosts` — reader computations.
* `MonadicWP Option Prop (Unit → Prop)` — concrete early termination.
* `MonadicWP (Except ε) Prop (ε → Prop)` — concrete exception type.
* `MonadicWP (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.WP

variable {m : Type u → Type z}

/-- `Id`'s `WP` interpretation: `Prop` assertions and no exceptions. -/
instance Id.wpInst {α : Type u} : WP (Id α) α Prop EStack⟨⟩ where
  trans x := ⟨fun post _epost => post x⟩

instance {α : Type u} : WP.IsMonotone (Id α) := fun x => ⟨fun _ _ _ _ _ hpost => hpost x⟩

/-- `Id` interprets its programs with `Prop` assertions and no exceptions. -/
instance Id.instWPMonad : MonadicWP Id.{u} Prop EStack⟨⟩ where
  toWP _ := inferInstance

instance : MonadicWP.IsMonadMorphism Id.{u} where
  trans_pure _ := rfl
  trans_bind _ _ := rfl

/-- `ExceptT`'s `WP` interpretation: lift the base interpretation by adding an exception
postcondition layer. -/
instance ExceptT.wpInst {Pred : Type v} [WP (m (Except ε α)) (Except ε α) Pred EPosts] :
    WP (ExceptT ε m α) α Pred ((ε → Pred) × EPosts) where
  trans x := PredTrans.pushExceptT (WP.trans x.run)

instance {Pred : Type v} [WP (m (Except ε α)) (Except ε α) Pred EPosts]
    [PartialOrder Pred] [PartialOrder EPosts] [WP.IsMonotone (m (Except ε α))] :
    WP.IsMonotone (ExceptT ε m α) :=
  fun x => inferInstanceAs (PredTrans.pushExceptT (WP.trans x.run)).IsMonotone

/-- `ExceptT` lifts a `MonadicWP` instance by adding an exception postcondition layer. -/
instance ExceptT.instWPMonad {Pred : Type v} [Monad m] [MonadicWP m Pred EPosts] :
    MonadicWP (ExceptT ε m) Pred ((ε → Pred) × EPosts) where
  toWP _ := inferInstance

@[simp, grind =]
theorem ExceptT.wp_apply_eq {α ε Pred EPosts} [Monad m] [MonadicWP m Pred EPosts]
    (x : ExceptT ε m α) (post : α → Pred) (eposts : (ε → Pred) × EPosts) :
    wp x post eposts = wp x.run (pushExcept post eposts.fst) eposts.snd := rfl

instance {Pred : Type v} [Monad m] [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (ExceptT ε m) where
  trans_pure a := PredTrans.ext fun post eposts =>
    MonadicWP.wp_pure_eq (m := m) (Except.ok a) (pushExcept post eposts.fst) eposts.snd
  trans_bind x f := PredTrans.ext fun post eposts => by
    show wp (x >>= f).run (pushExcept post eposts.fst) eposts.snd =
      wp x.run (pushExcept (fun a => wp (f a).run (pushExcept post eposts.fst) eposts.snd)
        eposts.fst) eposts.snd
    rw [ExceptT.run_bind, MonadicWP.wp_bind_eq]
    congr 1; funext r; cases r with
    | ok a => rfl
    | error e => exact MonadicWP.wp_pure_eq (m := m) _ _ _

instance {Pred : Type v} [Monad m] [MonadicWP m Pred EPosts] [PartialOrder Pred]
    [PartialOrder EPosts] [MonadicWP.IsMonotone m] [MonadicWP.IsLaxMonadMorphism m] :
    MonadicWP.IsLaxMonadMorphism (ExceptT ε m) where
  pure_le x := fun post eposts =>
    MonadicWP.pure_le_wp_pure (m := m) (Except.ok x) (pushExcept post eposts.fst) eposts.snd
  bind_le x f := fun post eposts => by
    show wp x.run _ eposts.snd ⊑ _
    apply PartialOrder.rel_trans _
      (MonadicWP.bind_le_wp_bind (m := m) x.run _ (pushExcept post eposts.fst) eposts.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact MonadicWP.pure_le_wp_pure (m := m) (Except.error el) (pushExcept post eposts.fst)
        eposts.snd

/-- `OptionT`'s `WP` interpretation: lift the base interpretation by adding a `Unit` exception
postcondition layer. -/
instance OptionT.wpInst {Pred : Type u} [WP (m (Option α)) (Option α) Pred EPosts] :
    WP (OptionT m α) α Pred ((Unit → Pred) × EPosts) where
  trans x := PredTrans.pushOptionT (WP.trans x.run)

instance {Pred : Type u} [WP (m (Option α)) (Option α) Pred EPosts]
    [PartialOrder Pred] [PartialOrder EPosts] [WP.IsMonotone (m (Option α))] :
    WP.IsMonotone (OptionT m α) :=
  fun x => inferInstanceAs (PredTrans.pushOptionT (WP.trans x.run)).IsMonotone

/-- `OptionT` lifts a `MonadicWP` instance by adding a `Unit` exception postcondition layer. -/
instance OptionT.instWPMonad {Pred : Type u} [Monad m] [MonadicWP m Pred EPosts] :
    MonadicWP (OptionT m) Pred ((Unit → Pred) × EPosts) where
  toWP _ := inferInstance

@[simp, grind =]
theorem OptionT.wp_apply_eq {α : Type u} {Pred : Type u} {EPosts}
    [Monad m] [MonadicWP m Pred EPosts] (x : OptionT m α)
    (post : α → Pred) (eposts : (Unit → Pred) × EPosts) :
    wp x post eposts = wp x.run (pushOption post eposts.fst) eposts.snd := rfl

instance {Pred : Type u} [Monad m] [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (OptionT m) where
  trans_pure a := PredTrans.ext fun post eposts =>
    MonadicWP.wp_pure_eq (m := m) (some a) (pushOption post eposts.fst) eposts.snd
  trans_bind x f := PredTrans.ext fun post eposts => by
    show wp (x >>= f).run (pushOption post eposts.fst) eposts.snd =
      wp x.run (pushOption (fun a => wp (f a).run (pushOption post eposts.fst) eposts.snd)
        eposts.fst) eposts.snd
    show wp (x.run >>= fun o => match o with | some a => (f a).run | none => pure none) _ _ = _
    rw [MonadicWP.wp_bind_eq]
    congr 1; funext o; cases o with
    | some a => rfl
    | none => exact MonadicWP.wp_pure_eq (m := m) _ _ _

instance {Pred : Type u} [Monad m] [MonadicWP m Pred EPosts] [PartialOrder Pred]
    [PartialOrder EPosts] [MonadicWP.IsMonotone m] [MonadicWP.IsLaxMonadMorphism m] :
    MonadicWP.IsLaxMonadMorphism (OptionT m) where
  pure_le x := fun post eposts =>
    MonadicWP.pure_le_wp_pure (m := m) (some x) (pushOption post eposts.fst) eposts.snd
  bind_le x f := fun post eposts => by
    show wp x.run _ eposts.snd ⊑ _
    apply PartialOrder.rel_trans _
      (MonadicWP.bind_le_wp_bind (m := m) x.run _ (pushOption post eposts.fst) eposts.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact MonadicWP.pure_le_wp_pure (m := m) none (pushOption post eposts.fst) eposts.snd

/-- `StateT`'s `WP` interpretation: lift the base interpretation by adding a state argument. -/
instance StateT.wpInst {EPosts : Type v} {σ : Type u} {Pred : Type w}
    [WP (m (α × σ)) (α × σ) Pred EPosts] :
    WP (StateT σ m α) α (σ → Pred) EPosts where
  trans x := PredTrans.pushArg (WP.trans <| x.run ·)

instance {EPosts : Type v} {σ : Type u} {Pred : Type w} [WP (m (α × σ)) (α × σ) Pred EPosts]
    [PartialOrder Pred] [PartialOrder EPosts] [WP.IsMonotone (m (α × σ))] :
    WP.IsMonotone (StateT σ m α) :=
  fun x => inferInstanceAs (PredTrans.pushArg (WP.trans <| x.run ·)).IsMonotone

/-- `StateT` lifts a `MonadicWP` instance by adding a state argument. -/
instance (priority := low) StateT.instWPMonad {EPosts : Type v} {σ : Type u} {Pred : Type w}
    [Monad m] [MonadicWP m Pred EPosts] :
    MonadicWP (StateT σ m) (σ → Pred) EPosts where
  toWP _ := inferInstance

@[simp, grind =]
theorem StateT.wp_apply_eq {σ : Type u} [Monad m] [MonadicWP m Pred EPosts] (x : StateT σ m α)
    (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    wp x post eposts s = wp (x.run s) (fun (a, s) => post a s) eposts := rfl

instance {EPosts : Type v} {σ : Type u} {Pred : Type w} [Monad m] [MonadicWP m Pred EPosts]
    [MonadicWP.IsMonadMorphism m] : MonadicWP.IsMonadMorphism (StateT σ m) where
  trans_pure a := PredTrans.ext fun post eposts => funext fun s =>
    MonadicWP.wp_pure_eq (m := m) (a, s) (fun p => post p.1 p.2) eposts
  trans_bind x f := PredTrans.ext fun post eposts => funext fun s =>
    MonadicWP.wp_bind_eq (m := m) (x.run s) (fun p => (f p.1).run p.2) (fun p => post p.1 p.2)
      eposts

instance {EPosts : Type v} {σ : Type u} {Pred : Type w} [Monad m] [MonadicWP m Pred EPosts]
    [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP.IsMonotone m]
    [MonadicWP.IsLaxMonadMorphism m] : MonadicWP.IsLaxMonadMorphism (StateT σ m) where
  pure_le x := fun post eposts s =>
    MonadicWP.pure_le_wp_pure (m := m) (x, s) (fun p => post p.1 p.2) eposts
  bind_le x f := fun post eposts s =>
    MonadicWP.bind_le_wp_bind (m := m) (x.run s) (fun p => (f p.1).run p.2)
      (fun p => post p.1 p.2) eposts

/-- `ReaderT`'s `WP` interpretation: lift the base interpretation by adding a reader argument. -/
instance ReaderT.wpInst {Pred : Type v} [WP (m α) α Pred EPosts] :
    WP (ReaderT ρ m α) α (ρ → Pred) EPosts where
  trans x := ⟨fun post eposts r => wp (x.run r) (fun a => post a r) eposts⟩

instance {Pred : Type v} [WP (m α) α Pred EPosts] [PartialOrder Pred] [PartialOrder EPosts]
    [WP.IsMonotone (m α)] : WP.IsMonotone (ReaderT ρ m α) :=
  fun x => ⟨fun _ _ _ _ heposts hpost r =>
    WP.wp_monotone (x := x.run r) (fun a => hpost a r) heposts⟩

/-- `ReaderT` lifts a `MonadicWP` instance by adding a reader argument. -/
instance ReaderT.instWPMonad {Pred : Type v} [Monad m] [MonadicWP m Pred EPosts] :
    MonadicWP (ReaderT ρ m) (ρ → Pred) EPosts where
  toWP _ := inferInstance

@[simp, grind =]
theorem ReaderT.wp_apply_eq {ρ : Type u} [Monad m] [MonadicWP m Pred EPosts] (x : ReaderT ρ m α)
    (post : α → ρ → Pred) (eposts : EPosts) (r : ρ) :
    wp x post eposts r = wp (x.run r) (fun a => post a r) eposts := rfl

instance {Pred : Type v} [Monad m] [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (ReaderT ρ m) where
  trans_pure a := PredTrans.ext fun post eposts => funext fun r =>
    MonadicWP.wp_pure_eq (m := m) a (fun a => post a r) eposts
  trans_bind x f := PredTrans.ext fun post eposts => funext fun r =>
    MonadicWP.wp_bind_eq (m := m) (x.run r) (fun a => (f a).run r) (fun b => post b r) eposts

instance {Pred : Type v} [Monad m] [MonadicWP m Pred EPosts] [PartialOrder Pred]
    [PartialOrder EPosts] [MonadicWP.IsMonotone m] [MonadicWP.IsLaxMonadMorphism m] :
    MonadicWP.IsLaxMonadMorphism (ReaderT ρ m) where
  pure_le x := fun post eposts r =>
    MonadicWP.pure_le_wp_pure (m := m) x (fun a => post a r) eposts
  bind_le x f := fun post eposts r =>
    MonadicWP.bind_le_wp_bind (m := m) (x.run r) (fun a => (f a).run r) (fun b => post b r) eposts

/-!
## Type Alias Instances

`MonadicWP` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Option`'s `WP` interpretation: `Prop` assertions and a `Unit`-indexed exception
postcondition. -/
instance Option.wpInst {α : Type u} : WP (Option α) α Prop (Unit → Prop) where
  trans x := ⟨fun post eposts => pushOption post eposts x⟩

instance {α : Type u} : WP.IsMonotone (Option α) := fun x =>
  ⟨fun _ _ _ _ heposts hpost => by
    cases x with
    | none => exact heposts ()
    | some a => exact hpost a⟩

/-- `Option` interprets its programs with `Prop` assertions and a `Unit`-indexed exception
postcondition. -/
instance Option.instWPMonad : MonadicWP Option.{u} Prop (Unit → Prop) where
  toWP _ := inferInstance

instance : MonadicWP.IsMonadMorphism Option.{u} where
  trans_pure _ := rfl
  trans_bind x _ := by cases x <;> rfl

/-- `Except ε`'s `WP` interpretation: `Prop` assertions and an `ε`-indexed exception
postcondition. -/
instance Except.wpInst {α : Type u} : WP (Except ε α) α Prop (ε → Prop) where
  trans x := ⟨fun post eposts => pushExcept post eposts x⟩

instance {α : Type u} : WP.IsMonotone (Except ε α) := fun x =>
  ⟨fun _ _ _ _ heposts hpost => by
    cases x with
    | ok a => exact hpost a
    | error el => exact heposts el⟩

/-- `Except ε` interprets its programs with `Prop` assertions and an `ε`-indexed exception
postcondition. -/
instance Except.instWPMonad : MonadicWP (Except ε) Prop (ε → Prop) where
  toWP _ := inferInstance

instance : MonadicWP.IsMonadMorphism (Except ε) where
  trans_pure _ := rfl
  trans_bind x _ := by cases x <;> rfl

/-- `EStateM ε σ`'s `WP` interpretation combining state and exceptions. -/
instance EStateM.wpInst {α : Type} : WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop) where
  trans x := ⟨fun post eposts s => match x s with
    | .ok a s' => post a s'
    | .error el s' => eposts el s'⟩

instance {α : Type} : WP.IsMonotone (EStateM ε σ α) := fun x =>
  ⟨fun post post' eposts eposts' heposts hpost s => by
    show (match x s with | .ok a s' => post a s' | .error el s' => eposts el s') →
      (match x s with | .ok a s' => post' a s' | .error el s' => eposts' el s')
    cases x s with
    | ok a s' => exact hpost a s'
    | error el s' => exact heposts el s'⟩

/-- `EStateM ε σ` interprets its programs combining state and exceptions. -/
instance EStateM.instWPMonad : MonadicWP (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  toWP _ := inferInstance

instance : MonadicWP.IsMonadMorphism (EStateM ε σ) where
  trans_pure _ := rfl
  trans_bind x f := PredTrans.ext fun post eposts => funext fun s => by
    show (match (x >>= f) s with | .ok b s' => post b s' | .error el s' => eposts el s') =
      (match x s with
        | .ok a s' => (match f a s' with
          | .ok b s'' => post b s'' | .error el s'' => eposts el s'')
        | .error el s' => eposts el s')
    simp only [bind, EStateM.bind]
    cases x s <;> rfl

end Std.WP
