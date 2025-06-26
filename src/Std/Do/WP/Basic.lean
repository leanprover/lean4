/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Std.Do.PredTrans

/-!
# Weakest precondition interpretation

This module defines the weakest precondition interpretation `WP` of monadic programs
in terms of predicate transformers `PredTrans`.

This interpretation forms the basis of our notion of Hoare triples.
It is the main mechanism of this library for reasoning about monadic programs.

An instance `WP m ps` determines an interpretation `wp⟦x⟧` of a program `x : m α` in terms of a
predicate transformer `PredTrans ps α`; The monad `m` determines `ps : PostShape` and hence
the particular shape of the predicate transformer.

This library comes with pre-defined instances for common monads and transformers such as

* `WP Id .pure`, interpreting pure computations `x : Id α` in terms of a function (isomorphic to)
  `(α → Prop) → Prop`.
* `WP (StateT σ m) (.arg σ ps)` given an instance `WP m ps`, interpreting `StateM σ α` in terms of
  a function `(α → σ → Prop) → σ → Prop`.
* `WP (ExceptT ε m) (.except ε ps)` given an instance `WP m ps`, interpreting `Except ε α` in terms
  of `(α → Prop) → (ε → Prop) → Prop`.
* `WP (EStateM ε σ) (.except ε (.arg σ .pure))` interprets `EStateM ε σ α` in terms of
  a function `(α → σ → Prop) → (ε → σ → Prop) → σ → Prop`.

These instances are all monad morphisms, a fact which is properly encoded and exploited
by the subclass `WPMonad`.
-/

namespace Std.Do

universe u
variable {m : Type → Type u}

/--
  A weakest precondition interpretation of a monadic program `x : m α` in terms of a
  predicate transformer `PredTrans ps α`.
  The monad `m` determines `ps : PostShape`. See the module comment for more details.
-/
class WP (m : Type → Type u) (ps : outParam PostShape) where
  wp {α} (x : m α) : PredTrans ps α

export WP (wp)

scoped syntax:max "wp⟦" term:min (":" term)? "⟧" : term
macro_rules
  | `(wp⟦$x:term⟧) => `((WP.wp $x).apply)
  | `(wp⟦$x:term : $ty⟧) => `((WP.wp ($x : $ty)).apply)

@[app_unexpander PredTrans.apply]
protected def unexpandWP : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => match e with
    | `(wp ($x : $ty)) => `(wp⟦$x : $ty⟧)
    | `(wp $e) => `(wp⟦$e⟧)
    | _ => throw ()
  | _ => throw ()
instance Id.instWP : WP Id .pure where
  wp x := PredTrans.pure x.run

instance StateT.instWP [WP m ps] : WP (StateT σ m) (.arg σ ps) where
  wp x := PredTrans.pushArg (fun s => wp (x s))

instance ReaderT.instWP [WP m ps] : WP (ReaderT ρ m) (.arg ρ ps) where
  wp x := PredTrans.pushArg (fun s => (·, s) <$> wp (x s))

instance ExceptT.instWP [WP m ps] : WP (ExceptT ε m) (.except ε ps) where
  wp x := PredTrans.pushExcept (wp x)

instance EStateM.instWP : WP (EStateM ε σ) (.except ε (.arg σ .pure)) where
  wp x := -- Could define as PredTrans.mkExcept (PredTrans.modifyGetM (fun s => pure (EStateM.Result.toExceptState (x s))))
    { apply := fun Q s => match x s with
        | .ok a s' => Q.1 a s'
        | .error e s' => Q.2.1 e s'
      conjunctive := by
        intro _ _
        apply SPred.bientails.of_eq
        ext s
        dsimp
        cases (x s) <;> simp
    }

instance State.instWP : WP (StateM σ) (.arg σ .pure) :=
  inferInstanceAs (WP (StateT σ Id) (.arg σ .pure))
instance Reader.instWP : WP (ReaderM ρ) (.arg ρ .pure) :=
  inferInstanceAs (WP (ReaderT ρ Id) (.arg ρ .pure))
instance Except.instWP : WP (Except ε) (.except ε .pure) :=
  inferInstanceAs (WP (ExceptT ε Id) (.except ε .pure))

theorem Id.by_wp {α} {x : α} {prog : Id α} (h : Id.run prog = x) (P : α → Prop) :
  wp⟦prog⟧ (PostCond.total P) → P x := h ▸ id

theorem StateM.by_wp {α} {x : α × σ} {prog : StateM σ α} (h : StateT.run prog s = x) (P : α × σ → Prop) :
  wp⟦prog⟧ (PostCond.total (fun a s' => P (a, s'))) s → P x := by
    intro hspec
    simp only [wp, PredTrans.pure, PredTrans.pushArg_apply] at hspec
    exact h ▸ hspec

theorem EStateM.by_wp {α} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop) :
  wp⟦prog⟧ (PostCond.total (fun a s' => P (EStateM.Result.ok a s'))) s → P x := by
    intro hspec
    simp only [wp, FailConds.false, FailConds.const, SVal.curry_cons, SVal.curry_nil] at hspec
    split at hspec
    case h_1 a s' heq => rw[← heq] at hspec; exact h ▸ hspec
    case h_2 => contradiction
