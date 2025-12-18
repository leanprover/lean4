/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.PredTrans

@[expose] public section

set_option linter.missingDocs true

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

universe u v
variable {m : Type u → Type v}

/--
A weakest precondition interpretation of a monadic program `x : m α` in terms of a predicate
transformer `PredTrans ps α`. The monad `m` determines `ps : PostShape`.

For practical reasoning, an instance of `WPMonad m ps` is typically needed in addition to `WP m ps`.
-/
class WP (m : Type u → Type v) (ps : outParam PostShape.{u}) where
  /-- Interpret a monadic program `x : m α` in terms of a predicate transformer `PredTrans ps α`. -/
  wp {α} (x : m α) : PredTrans ps α

export WP (wp)

/-- `wp⟦x⟧ Q` is defined as `(WP.wp x).apply Q`. -/
scoped syntax:max "wp⟦" term:min (":" term)? "⟧" : term
macro_rules
  | `(wp⟦$x:term⟧) => `((WP.wp $x).apply)
  | `(wp⟦$x:term : $ty⟧) => `((WP.wp ($x : $ty)).apply)

/--
An unexpander for the `wp⟦...⟧` notation, causing it to be shown correctly in the pretty printer.
-/
@[app_unexpander PredTrans.apply]
protected meta def unexpandWP : Lean.PrettyPrinter.Unexpander
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

instance OptionT.instWP [WP m ps] : WP (OptionT m) (.except PUnit ps) where
  wp x := PredTrans.pushOption (wp x)

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
instance Option.instWP : WP Option (.except PUnit .pure) :=
  inferInstanceAs (WP (OptionT Id) (.except PUnit .pure))

/--
Adequacy lemma for `Id.run`.
Useful if you want to prove a property about an expression `x` defined as `Id.run prog` and you
want to use `mvcgen` to reason about `prog`.
-/
theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : Id α} (h : Id.run prog = x) (P : α → Prop) :
  (⊢ₛ wp⟦prog⟧ (⇓ a => ⟨P a⟩)) → P x := h ▸ (· True.intro)

/--
Adequacy lemma for `StateM.run`.
Useful if you want to prove a property about an expression `x` defined as `StateM.run prog s` and
you want to use `mvcgen` to reason about `prog`.
-/
theorem StateM.of_wp_run_eq {α} {x : α × σ} {prog : StateM σ α} (h : StateT.run prog s = x) (P : α × σ → Prop) :
  (⊢ₛ wp⟦prog⟧ (⇓ a s' => ⌜P (a, s')⌝) s) → P x := h ▸ (· True.intro)

/--
Adequacy lemma for `StateM.run'`.
Useful if you want to prove a property about an expression `x` defined as `StateM.run' prog s` and
you want to use `mvcgen` to reason about `prog`.
-/
theorem StateM.of_wp_run'_eq {α} {x : α} {prog : StateM σ α} (h : StateT.run' prog s = x) (P : α → Prop) :
  (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝) s) → P x := h ▸ (· True.intro)

/--
Adequacy lemma for `ReaderM.run`.
Useful if you want to prove a property about an expression `x` defined as `ReaderM.run prog r` and
you want to use `mvcgen` to reason about `prog`.
-/
theorem ReaderM.of_wp_run_eq {α} {x : α} {prog : ReaderM ρ α} (h : ReaderT.run prog r = x) (P : α → Prop) :
  (⊢ₛ wp⟦prog⟧ (⇓ a _ => ⌜P a⌝) r) → P x := h ▸ (· True.intro)

/--
Adequacy lemma for `Except`.
Useful if you want to prove a property about an expression `prog : Except ε α` and you want to use
`mvcgen` to reason about `prog`.
-/
theorem Except.of_wp {α} {prog : Except ε α} (P : Except ε α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.error e)⌝⟩) → P prog := by
  intro hspec
  simp only [wp, PredTrans.pushExcept_apply, PredTrans.pure_apply] at hspec
  split at hspec
  case h_1 a s' heq => rw[← heq] at hspec; exact hspec True.intro
  case h_2 e s' heq => rw[← heq] at hspec; exact hspec True.intro

/--
Adequacy lemma for `EStateM.run`.
Useful if you want to prove a property about an expression `x` defined as `EStateM.run prog s` and
you want to use `mvcgen` to reason about `prog`.
-/
theorem EStateM.of_wp_run_eq {α} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a s' => ⌜P (EStateM.Result.ok a s')⌝, fun e s' => ⌜P (EStateM.Result.error e s')⌝⟩ s) → P x := by
  intro hspec
  simp only [wp] at hspec
  split at hspec
  case h_1 a s' heq => rw[← heq] at hspec; exact h ▸ hspec True.intro
  case h_2 e s' heq => rw[← heq] at hspec; exact h ▸ hspec True.intro
