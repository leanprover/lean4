/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Monad.Instances
public import Init.Control.Lawful.MonadAttach.Instances
public import Init.Data.Option.Attach
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# Soundness of the Weakest Precondition Interpretation

`LawfulWPMonadAttach m Pred EPred` relates the `wp` interpretation of `m` to the values that a
program `x : m α` returns. Its single field `of_canReturn_wp` says: if the postcondition
`fun a => ⌜P a⌝` follows from `⊤` under `wp x`, then `P a` holds for every `a` with
`MonadAttach.CanReturn x a`.

For a transformer, `MonadAttach.CanReturn` speaks about the computation that remains once the
reader or state argument is supplied and the `Except` or `Option` result is exposed. The
`of_canReturn_run_wp` lemmas take the witness in that form, pairing it with `wp prog` at the
supplied argument.

The `of_run_eq_wp` family at the end of the file specializes soundness to the concrete monads
`Id`, `Option`, `StateM`, `ReaderM`, `Except` and `EStateM`, where the witness is an equation
`prog.run s = x`.
-/

namespace Std.WP

/-- Soundness of the weakest precondition interpretation of `m`: a postcondition that `wp` proves
holds of every value the program returns. -/
class LawfulWPMonadAttach (m : Type u → Type v) (Pred : outParam (Type w)) (EPred : outParam (Type z))
    [Monad m] [MonadAttach m] [LawfulMonadAttach m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] where
  /-- From a `wp`-provable postcondition and a `MonadAttach.CanReturn` witness, conclude `P` at
  that value. -/
  of_canReturn_wp {α : Type u} {x : m α} {P : α → Prop} {a : α} :
    MonadAttach.CanReturn x a → (⊤ ⊑ wp x (fun a => ⌜P a⌝) ⊤) → P a

instance Id.instLawfulWPMonadAttach : LawfulWPMonadAttach Id.{u} Prop EStack⟨⟩ where
  of_canReturn_wp hcan hwp := by
    subst hcan
    have h := hwp (by simp)
    simp only [ofProp_prop_eq] at h
    exact h

instance Option.instLawfulWPMonadAttach : LawfulWPMonadAttach Option.{u} Prop (Unit → Prop) where
  of_canReturn_wp hcan hwp := by
    subst hcan
    have h := hwp (by simp)
    simp only [ofProp_prop_eq] at h
    exact h

instance Except.instLawfulWPMonadAttach {ε : Type u} : LawfulWPMonadAttach (Except ε) Prop (ε → Prop) where
  of_canReturn_wp hcan hwp := by
    subst hcan
    have h := hwp (by simp)
    simp only [ofProp_prop_eq] at h
    exact h

instance EStateM.instLawfulWPMonadAttach {ε σ : Type} : LawfulWPMonadAttach (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  of_canReturn_wp := @fun α x P a hcan hwp => by
    obtain ⟨s, s', heq⟩ := hcan
    have hxs : x s = EStateM.Result.ok a s' := heq
    have h := hwp s (by simp)
    simp only [wp, WP.wpTrans, hxs] at h
    simpa using h

instance ExceptT.instLawfulWPMonadAttach {ε m Pred EPred}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred] :
    LawfulWPMonadAttach (ExceptT ε m) Pred ((ε → Pred) × EPred) where
  of_canReturn_wp := @fun α x P a hcan hwp => by
    refine LawfulWPMonadAttach.of_canReturn_wp (m := m)
      (P := fun r : Except ε α => match r with | .ok b => P b | .error _ => True)
      (a := .ok a) hcan ?_
    rw [ExceptT.wp_apply_eq] at hwp
    refine PartialOrder.rel_trans hwp (WP.wp_consequence_econs _ _ _ _ _ ?_ (le_top _))
    intro r
    cases r with
    | ok b => exact PartialOrder.rel_refl
    | error e => exact le_ofProp _ _ trivial

instance OptionT.instLawfulWPMonadAttach {m : Type u → Type z} {Pred : Type u} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred] :
    LawfulWPMonadAttach (OptionT m) Pred ((Unit → Pred) × EPred) where
  of_canReturn_wp := @fun α x P a hcan hwp => by
    refine LawfulWPMonadAttach.of_canReturn_wp (m := m)
      (P := fun r : Option α => match r with | some b => P b | none => True)
      (a := some a) hcan ?_
    rw [OptionT.wp_apply_eq] at hwp
    refine PartialOrder.rel_trans hwp (WP.wp_consequence_econs _ _ _ _ _ ?_ (le_top _))
    intro r
    cases r with
    | some b => exact PartialOrder.rel_refl
    | none => exact le_ofProp _ _ trivial

instance StateT.instLawfulWPMonadAttach {m : Type u → Type z} {σ : Type u} {Pred : Type v} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred] :
    LawfulWPMonadAttach (StateT σ m) (σ → Pred) EPred where
  of_canReturn_wp := @fun α x P a hcan hwp => by
    obtain ⟨s, s', hcan⟩ := hcan
    refine LawfulWPMonadAttach.of_canReturn_wp (m := m) (P := fun q : α × σ => P q.1) (a := (a, s')) hcan ?_
    have h := hwp s
    rw [StateT.wp_apply_eq] at h
    simpa using h

instance ReaderT.instLawfulWPMonadAttach {m : Type u → Type z} {ρ : Type u} {Pred : Type v} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred] :
    LawfulWPMonadAttach (ReaderT ρ m) (ρ → Pred) EPred where
  of_canReturn_wp := @fun α x P a hcan hwp => by
    obtain ⟨r, hcan⟩ := hcan
    refine LawfulWPMonadAttach.of_canReturn_wp (m := m) (P := P) (a := a) hcan ?_
    have h := hwp r
    rw [ReaderT.wp_apply_eq] at h
    simpa using h

/-! ## Soundness at the Post-Run Computation

For a transformer `T`, `T.of_canReturn_run_wp` takes the `MonadAttach.CanReturn` witness for the
base-monad computation that `prog` becomes once its arguments are supplied.
-/

/-- A `wp`-provable postcondition holds at every value that the post-run computation
`prog.run r : m α` returns. -/
theorem ReaderT.of_canReturn_run_wp {m : Type u → Type z} {ρ : Type u} {Pred : Type v} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred]
    {α : Type u} {prog : ReaderT ρ m α} {r : ρ} {a : α} (P : α → Prop)
    (hcan : MonadAttach.CanReturn (prog.run r) a)
    (hwp : ⊤ ⊑ wp prog (fun a => ⌜P a⌝) ⊤ r) : P a := by
  refine LawfulWPMonadAttach.of_canReturn_wp (m := m) hcan ?_
  rw [ReaderT.wp_apply_eq] at hwp
  simpa using hwp

/-- A `wp`-provable postcondition holds at every value-state pair that the post-run computation
`prog.run s : m (α × σ)` returns. -/
theorem StateT.of_canReturn_run_wp {m : Type u → Type z} {σ : Type u} {Pred : Type v} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred]
    {α : Type u} {prog : StateT σ m α} {s : σ} {p : α × σ} (P : α × σ → Prop)
    (hcan : MonadAttach.CanReturn (prog.run s) p)
    (hwp : ⊤ ⊑ wp prog (fun a s' => ⌜P (a, s')⌝) ⊤ s) : P p := by
  refine LawfulWPMonadAttach.of_canReturn_wp (m := m) hcan ?_
  rw [StateT.wp_apply_eq] at hwp
  simpa using hwp

/-- A `wp`-provable postcondition with split `.ok`/`.error` cases holds at every result that the
post-run computation `prog.run : m (Except ε α)` returns. -/
theorem ExceptT.of_canReturn_run_wp {m : Type u → Type z} {ε : Type u} {Pred : Type v} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred]
    {α : Type u} {prog : ExceptT ε m α} {x : Except ε α} (P : Except ε α → Prop)
    (hcan : MonadAttach.CanReturn prog.run x)
    (hwp : ⊤ ⊑ wp prog (fun a => ⌜P (.ok a)⌝) ((fun e => ⌜P (.error e)⌝), ⊤)) :
    P x := by
  refine LawfulWPMonadAttach.of_canReturn_wp (m := m) hcan ?_
  rw [ExceptT.wp_apply_eq] at hwp
  refine PartialOrder.rel_trans hwp (WP.wp_consequence_econs _ _ _ _ _ ?_ (le_top _))
  intro r
  cases r <;> exact PartialOrder.rel_refl

/-- A `wp`-provable postcondition with split `some`/`none` cases holds at every result that the
post-run computation `prog.run : m (Option α)` returns. -/
theorem OptionT.of_canReturn_run_wp {m : Type u → Type z} {Pred : Type u} {EPred : Type w}
    [Monad m] [MonadAttach m] [LawfulMonadAttach m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [LawfulWPMonadAttach m Pred EPred]
    {α : Type u} {prog : OptionT m α} {x : Option α} (P : Option α → Prop)
    (hcan : MonadAttach.CanReturn prog.run x)
    (hwp : ⊤ ⊑ wp prog (fun a => ⌜P (some a)⌝) ((fun _ => ⌜P none⌝), ⊤)) : P x := by
  refine LawfulWPMonadAttach.of_canReturn_wp (m := m) hcan ?_
  rw [OptionT.wp_apply_eq] at hwp
  refine PartialOrder.rel_trans hwp (WP.wp_consequence_econs _ _ _ _ _ ?_ (le_top _))
  intro r
  cases r <;> exact PartialOrder.rel_refl

/-! ## Soundness at a Concrete Result

Each lemma below takes the program's result as an equation and concludes a property of it.
-/

/-- Soundness for `Id`: if `wp prog P` holds, then `P` holds of `Id.run prog`. -/
theorem Id.of_run_eq_wp {α : Type u} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P ()) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `Option`: the postcondition takes a `some` case and a `none` case, and `wp prog`
holds of `prog` itself. -/
theorem Option.of_eq_wp {α : Type u} {x prog : Option α}
  (h : prog = x) (P : Option α → Prop)
  (hwp : wp prog (fun a => P (some a)) (fun _ => P none)) : P x := by
  subst h
  cases prog with
  | none => exact hwp
  | some a => exact hwp

/-- Soundness for `StateM`: if `wp prog P s` holds, then `P` holds of the value and final state of
`StateT.run prog s`. -/
theorem StateM.of_run_eq_wp {x : α × σ} {prog : StateM σ α} {s : σ}
  (h : StateT.run prog s = x) (P : α × σ → Prop)
  (hwp : wp prog (fun a s' => P (a, s')) () s) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `StateM`, at the value alone: if `wp prog P s` holds, then `P` holds of
`StateT.run' prog s`. -/
theorem StateM.of_run'_eq_wp {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) () s) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `ReaderM`: if `wp prog P r` holds, then `P` holds of `ReaderT.run prog r`. -/
theorem ReaderM.of_run_eq_wp {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) () r) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `Except`: the postcondition takes an `ok` case and an `error` case, and
`wp prog` holds of `prog` itself. -/
theorem Except.of_eq_wp {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) (fun e => P (.error e))) : P x := by
  subst h
  cases prog with
  | ok a => simpa only [wp] using! hwp
  | error e => simpa only [wp] using! hwp

/-- Soundness for `EStateM`: if `wp prog P s` holds, then `P` holds of `(prog.run s)`. -/
theorem EStateM.of_run_eq_wp {ε σ α : Type} {x : EStateM.Result ε σ α}
  {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) :
    P x := by
  rw [← h]
  change P (prog s)
  cases heq : prog s with
  | ok a s' =>
    simpa [wp, WP.wpTrans, heq] using hwp
  | error e s' =>
    simpa [wp, WP.wpTrans, heq] using hwp

end Std.WP
