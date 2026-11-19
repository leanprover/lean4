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
# Monadic WP Instances

The weakest precondition interpretation of the base monads and of the monad transformers.

A monad that throws carries the exception postcondition itself. A transformer stacks a product
layer on the exception postcondition of the monad below it, and `EStack⟨⟩` closes the stack.

Every interpretation here is a monad morphism (`MonadicWP.IsMonadMorphism`). A transformer is also
a lax monad morphism over a base that is one.

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
  trans x := PredTrans.mk (fun post _epost => post x) fun hpost _ => hpost x

instance : MonadicWP Id.{u} Prop EStack⟨⟩ := ⟨fun _ => Id.wpInst⟩

theorem Id.wp_apply_eq {α : Type u} (x : Id α) (post : α → Prop) (eposts : EStack⟨⟩) :
    wp x post eposts = post x.run := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk] <;> rfl

instance : MonadicWP.IsMonadMorphism Id.{u} where
  wp_pure_eq x post eposts := Id.wp_apply_eq (pure x) post eposts
  wp_bind_eq x f post eposts := by simp only [Id.wp_apply_eq]; rfl

/-- `ExceptT`'s `WP` interpretation: lift the base interpretation by adding an exception
postcondition layer. -/
instance ExceptT.wpInst {Pred : Type v} [PartialOrder Pred] [PartialOrder EPosts]
    [WP (m (Except ε α)) (Except ε α) Pred EPosts] :
    WP (ExceptT ε m α) α Pred ((ε → Pred) × EPosts) where
  trans x := PredTrans.pushExceptT (WP.trans x.run)

instance {Pred : Type v} [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (ExceptT ε m) Pred ((ε → Pred) × EPosts) := ⟨fun _ => ExceptT.wpInst⟩

@[simp, grind =]
theorem ExceptT.wp_apply_eq {α ε Pred EPosts} [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] (x : ExceptT ε m α) (post : α → Pred)
    (eposts : (ε → Pred) × EPosts) :
    wp x post eposts = wp x.run (pushExcept post eposts.fst) eposts.snd := by
  simp only [WP.wp, WP.trans, PredTrans.apply_pushExceptT]

instance {Pred : Type v} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (ExceptT ε m) where
  wp_pure_eq a post eposts := by
    simp only [ExceptT.wp_apply_eq]
    exact MonadicWP.wp_pure_eq (m := m) (Except.ok a) (pushExcept post eposts.fst) eposts.snd
  wp_bind_eq x f post eposts := by
    simp only [ExceptT.wp_apply_eq]
    rw [ExceptT.run_bind, MonadicWP.wp_bind_eq]
    congr 1; funext r; cases r with
    | ok a => rfl
    | error e => exact MonadicWP.wp_pure_eq (m := m) _ _ _

instance (priority := low) {Pred : Type v} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] [MonadicWP.IsLaxMonadMorphism m] :
    MonadicWP.IsLaxMonadMorphism (ExceptT ε m) where
  pure_le_wp_pure x post eposts := by
    simp only [ExceptT.wp_apply_eq]
    exact MonadicWP.pure_le_wp_pure (m := m) (Except.ok x) (pushExcept post eposts.fst) eposts.snd
  bind_le_wp_bind x f post eposts := by
    simp only [ExceptT.wp_apply_eq]
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
instance OptionT.wpInst {Pred : Type u} [PartialOrder Pred] [PartialOrder EPosts]
    [WP (m (Option α)) (Option α) Pred EPosts] :
    WP (OptionT m α) α Pred ((Unit → Pred) × EPosts) where
  trans x := PredTrans.pushOptionT (WP.trans x.run)

instance {Pred : Type u} [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (OptionT m) Pred ((Unit → Pred) × EPosts) := ⟨fun _ => OptionT.wpInst⟩

@[simp, grind =]
theorem OptionT.wp_apply_eq {α : Type u} {Pred : Type u} {EPosts} [PartialOrder Pred]
    [PartialOrder EPosts] [MonadicWP m Pred EPosts] (x : OptionT m α)
    (post : α → Pred) (eposts : (Unit → Pred) × EPosts) :
    wp x post eposts = wp x.run (pushOption post eposts.fst) eposts.snd := by
  simp only [WP.wp, WP.trans, PredTrans.apply_pushOptionT]

instance {Pred : Type u} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (OptionT m) where
  wp_pure_eq a post eposts := by
    simp only [OptionT.wp_apply_eq]
    exact MonadicWP.wp_pure_eq (m := m) (some a) (pushOption post eposts.fst) eposts.snd
  wp_bind_eq x f post eposts := by
    simp only [OptionT.wp_apply_eq]
    show wp (x.run >>= fun o => match o with | some a => (f a).run | none => pure none) _ _ = _
    rw [MonadicWP.wp_bind_eq]
    congr 1; funext o; cases o with
    | some a => rfl
    | none => exact MonadicWP.wp_pure_eq (m := m) _ _ _

instance (priority := low) {Pred : Type u} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] [MonadicWP.IsLaxMonadMorphism m] :
    MonadicWP.IsLaxMonadMorphism (OptionT m) where
  pure_le_wp_pure x post eposts := by
    simp only [OptionT.wp_apply_eq]
    exact MonadicWP.pure_le_wp_pure (m := m) (some x) (pushOption post eposts.fst) eposts.snd
  bind_le_wp_bind x f post eposts := by
    simp only [OptionT.wp_apply_eq]
    apply PartialOrder.rel_trans _
      (MonadicWP.bind_le_wp_bind (m := m) x.run _ (pushOption post eposts.fst) eposts.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact MonadicWP.pure_le_wp_pure (m := m) none (pushOption post eposts.fst) eposts.snd

/-- `StateT`'s `WP` interpretation: lift the base interpretation by adding a state argument. -/
instance StateT.wpInst {EPosts : Type v} {σ : Type u} {Pred : Type w} [PartialOrder Pred]
    [PartialOrder EPosts] [WP (m (α × σ)) (α × σ) Pred EPosts] :
    WP (StateT σ m α) α (σ → Pred) EPosts where
  trans x := PredTrans.pushArg (WP.trans <| x.run ·)

instance {EPosts : Type v} {σ : Type u} {Pred : Type w} [PartialOrder Pred]
    [PartialOrder EPosts] [MonadicWP m Pred EPosts] : MonadicWP (StateT σ m) (σ → Pred) EPosts :=
  ⟨fun _ => StateT.wpInst⟩

@[simp, grind =]
theorem StateT.wp_apply_eq {σ : Type u} [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] (x : StateT σ m α) (post : α → σ → Pred) (eposts : EPosts) (s : σ) :
    wp x post eposts s = wp (x.run s) (fun (a, s) => post a s) eposts := by
  simp only [WP.wp, WP.trans, PredTrans.apply_pushArg]

instance {EPosts : Type v} {σ : Type u} {Pred : Type w} [Monad m] [PartialOrder Pred]
    [PartialOrder EPosts] [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (StateT σ m) where
  wp_pure_eq a post eposts := funext fun s => by
    simp only [StateT.wp_apply_eq]
    exact MonadicWP.wp_pure_eq (m := m) (a, s) (fun p => post p.1 p.2) eposts
  wp_bind_eq x f post eposts := funext fun s => by
    simp only [StateT.wp_apply_eq]
    exact MonadicWP.wp_bind_eq (m := m) (x.run s) (fun p => (f p.1).run p.2)
      (fun p => post p.1 p.2) eposts

instance (priority := low) {EPosts : Type v} {σ : Type u} {Pred : Type w} [Monad m]
    [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts]
    [MonadicWP.IsLaxMonadMorphism m] : MonadicWP.IsLaxMonadMorphism (StateT σ m) where
  pure_le_wp_pure x post eposts s := by
    simp only [StateT.wp_apply_eq]
    exact MonadicWP.pure_le_wp_pure (m := m) (x, s) (fun p => post p.1 p.2) eposts
  bind_le_wp_bind x f post eposts s := by
    simp only [StateT.wp_apply_eq]
    exact MonadicWP.bind_le_wp_bind (m := m) (x.run s) (fun p => (f p.1).run p.2)
      (fun p => post p.1 p.2) eposts

/-- `ReaderT`'s `WP` interpretation: lift the base interpretation by adding a reader argument. -/
instance ReaderT.wpInst {Pred : Type v} [PartialOrder Pred] [PartialOrder EPosts]
    [WP (m α) α Pred EPosts] :
    WP (ReaderT ρ m α) α (ρ → Pred) EPosts where
  trans x := PredTrans.mk (fun post eposts r => wp (x.run r) (fun a => post a r) eposts)
    fun hpost heposts r => WP.wp_monotone (fun a => hpost a r) heposts

instance {Pred : Type v} [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (ReaderT ρ m) (ρ → Pred) EPosts := ⟨fun _ => ReaderT.wpInst⟩

@[simp, grind =]
theorem ReaderT.wp_apply_eq {ρ : Type u} [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] (x : ReaderT ρ m α) (post : α → ρ → Pred) (eposts : EPosts) (r : ρ) :
    wp x post eposts r = wp (x.run r) (fun a => post a r) eposts := by
  show (WP.trans x).apply post eposts r = _
  simp only [WP.trans, PredTrans.apply_mk]

instance {Pred : Type v} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] [MonadicWP.IsMonadMorphism m] :
    MonadicWP.IsMonadMorphism (ReaderT ρ m) where
  wp_pure_eq a post eposts := funext fun r => by
    simp only [ReaderT.wp_apply_eq]
    exact MonadicWP.wp_pure_eq (m := m) a (fun a => post a r) eposts
  wp_bind_eq x f post eposts := funext fun r => by
    simp only [ReaderT.wp_apply_eq]
    exact MonadicWP.wp_bind_eq (m := m) (x.run r) (fun a => (f a).run r) (fun b => post b r)
      eposts

instance (priority := low) {Pred : Type v} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] [MonadicWP.IsLaxMonadMorphism m] :
    MonadicWP.IsLaxMonadMorphism (ReaderT ρ m) where
  pure_le_wp_pure x post eposts r := by
    simp only [ReaderT.wp_apply_eq]
    exact MonadicWP.pure_le_wp_pure (m := m) x (fun a => post a r) eposts
  bind_le_wp_bind x f post eposts r := by
    simp only [ReaderT.wp_apply_eq]
    exact MonadicWP.bind_le_wp_bind (m := m) (x.run r) (fun a => (f a).run r) (fun b => post b r)
      eposts

/-!
## Type Alias Instances

`WP` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Option`'s `WP` interpretation: `Prop` assertions and a `Unit`-indexed exception
postcondition. -/
instance Option.wpInst {α : Type u} : WP (Option α) α Prop (Unit → Prop) where
  trans x := PredTrans.mk (fun post eposts => pushOption post eposts x) fun hpost heposts => by
    cases x with
    | none => exact heposts ()
    | some a => exact hpost a

instance : MonadicWP Option.{u} Prop (Unit → Prop) := ⟨fun _ => Option.wpInst⟩

theorem Option.wp_apply_eq {α : Type u} (x : Option α) (post : α → Prop)
    (eposts : Unit → Prop) : wp x post eposts = pushOption post eposts x := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

instance : MonadicWP.IsMonadMorphism Option.{u} where
  wp_pure_eq x post eposts := Option.wp_apply_eq (pure x) post eposts
  wp_bind_eq x _ _ _ := by
    simp only [Option.wp_apply_eq]
    cases x <;> rfl

/-- `Except ε`'s `WP` interpretation: `Prop` assertions and an `ε`-indexed exception
postcondition. -/
instance Except.wpInst {α : Type u} : WP (Except ε α) α Prop (ε → Prop) where
  trans x := PredTrans.mk (fun post eposts => pushExcept post eposts x) fun hpost heposts => by
    cases x with
    | ok a => exact hpost a
    | error el => exact heposts el

instance : MonadicWP (Except ε) Prop (ε → Prop) := ⟨fun _ => Except.wpInst⟩

theorem Except.wp_apply_eq {α : Type u} (x : Except ε α) (post : α → Prop)
    (eposts : ε → Prop) : wp x post eposts = pushExcept post eposts x := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

instance : MonadicWP.IsMonadMorphism (Except ε) where
  wp_pure_eq x post eposts := Except.wp_apply_eq (pure x) post eposts
  wp_bind_eq x _ _ _ := by
    simp only [Except.wp_apply_eq]
    cases x <;> rfl

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

instance : MonadicWP (EStateM ε σ) (σ → Prop) (ε → σ → Prop) := ⟨fun _ => EStateM.wpInst⟩

theorem EStateM.wp_apply_eq {α : Type} (x : EStateM ε σ α) (post : α → σ → Prop)
    (eposts : ε → σ → Prop) (s : σ) :
    wp x post eposts s = match x s with
      | .ok a s' => post a s'
      | .error el s' => eposts el s' := by
  simp only [WP.wp, WP.trans, PredTrans.apply_mk]

instance : MonadicWP.IsMonadMorphism (EStateM ε σ) where
  wp_pure_eq x post eposts := funext fun s => EStateM.wp_apply_eq (pure x) post eposts s
  wp_bind_eq x f post eposts := funext fun s => by
    simp only [EStateM.wp_apply_eq]
    simp only [bind, EStateM.bind]
    cases x s <;> rfl


section Deprecated

set_option linter.missingDocs false

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev Id.instWPMonad : MonadicWP Id.{u} Prop EStack⟨⟩ := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev ExceptT.instWPMonad {m : Type u → Type z} {ε : Type u} {Pred : Type v} {EPosts : Type w}
    [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (ExceptT ε m) Pred ((ε → Pred) × EPosts) := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev OptionT.instWPMonad {m : Type u → Type z} {Pred : Type u} {EPosts : Type w}
    [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (OptionT m) Pred ((Unit → Pred) × EPosts) := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev StateT.instWPMonad {m : Type u → Type z} {σ : Type u} {Pred : Type w} {EPosts : Type v}
    [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (StateT σ m) (σ → Pred) EPosts := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev ReaderT.instWPMonad {m : Type u → Type z} {ρ : Type u} {Pred : Type v} {EPosts : Type w}
    [PartialOrder Pred] [PartialOrder EPosts] [MonadicWP m Pred EPosts] :
    MonadicWP (ReaderT ρ m) (ρ → Pred) EPosts := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev Option.instWPMonad : MonadicWP Option.{u} Prop (Unit → Prop) := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev Except.instWPMonad {ε : Type u} : MonadicWP (Except ε) Prop (ε → Prop) := inferInstance

@[deprecated "use the `MonadicWP` instance, with `MonadicWP.IsLaxMonadMorphism` for the laws" (since := "2026-11-18")]
abbrev EStateM.instWPMonad {ε σ : Type} :
    MonadicWP (EStateM ε σ) (σ → Prop) (ε → σ → Prop) := inferInstance

end Deprecated

end Std.WP
