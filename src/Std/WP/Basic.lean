/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Assertion
public import Std.Internal.Order.PredTrans
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# Weakest Precondition Interpretation

`WP Prog Value Pred EPosts` interprets a program type `Prog` whose results have type `Value` as a
monotone predicate transformer `PredTrans Pred EPosts Value`. For a program `x : Prog`, a normal
postcondition `post : Value → Pred` and an exception postcondition `eposts : EPosts`, the assertion
`wp x post eposts` is the weakest precondition under which `x` establishes `post` and `eposts`.

The program type `Prog` determines the other three types, which are `outParam`s of the class.
Instance search runs on `Prog` alone. A term `wp x post eposts` therefore fixes the result type, the
assertion lattice and the exception postcondition type from the type of `x`, and each program type
carries one interpretation.

Two examples show the range of `Prog`. The error-state monad `EStateM ε σ` has the instance
`WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop)`. Here a state predicate is the assertion, and an
error paired with a state is the exception postcondition.

A deep embedding is the second example. A command language `Cmd` with assertions `Env → State → Prop`
has the instance `WP Cmd Unit (Env → State → Prop) EStack⟨⟩`. Its `wp` is defined in terms of an
operational semantics such as an omnisemantics. The file `tests/elab/vcgenImp.lean` carries this
example in full.

Everything here is generic over the program type. The interpretation of a monad and of the monad
transformers is in `Std.WP.Monad`.

## Laws

`WP` carries the predicate transformer only. Its laws are `Prop` classes over the transformer:
`WP.IsMonotone Prog` states that the transformer of every program of type `Prog` is monotone for
the orders of `Pred` and `EPosts`, and `PredTrans.IsConjunctive` states conjunctivity for a lattice
of assertions.
-/

namespace Std.WP

/-!
## The WP Typeclass

The `WP` typeclass interprets a program type `Prog` whose results have type `Value` as a
predicate transformer `trans : Prog → PredTrans Pred EPosts Value`.
-/

/-- Weakest precondition interpretation of a program type `Prog` whose results have type `Value`,
as a predicate transformer over assertions `Pred` with exception postconditions `EPosts`. -/
class WP (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPosts : outParam (Type w')) where
  /-- The weakest precondition transformer for a program. -/
  trans : Prog → PredTrans Pred EPosts Value := wpTrans
  /-- Deprecated alias for `trans`; provide either field when defining an instance. -/
  wpTrans : Prog → PredTrans Pred EPosts Value := trans

attribute [deprecated WP.trans (since := "2026-09-17")] WP.wpTrans
attribute [deprecated_arg EPred EPosts (since := "2026-09-18")] WP

/-- Weakest precondition of `x` for normal postcondition `post` and exception postcondition `eposts`.
The `WP` interpretation can be supplied explicitly via dot notation (`inst.wp x post eposts`). -/
def WP.wp {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type w'}
    [self : WP Prog Value Pred EPosts]
    (x : Prog) (post : Value → Pred) (eposts : EPosts) : Pred :=
  (self.trans x).apply post eposts

-- `wp x post eposts` computes the weakest precondition; it is `WP.wp` with the interpretation
-- synthesised as an instance.
export Std.WP.WP (wp)

@[simp, grind =] theorem WP.trans_apply_eq {Prog : Type u} {Value : Type v}
    [WP Prog Value Pred EPosts] (x : Prog) :
  (WP.trans x).apply = wp x := rfl

@[deprecated WP.trans_apply_eq (since := "2026-09-17")]
theorem WP.wpTrans_apply_eq {Prog : Type u} {Value : Type v}
    [WP Prog Value Pred EPosts] (x : Prog) :
    (WP.trans x).apply = wp x := rfl

/-- The predicate transformer of every program of type `Prog` is monotone. -/
abbrev WP.IsMonotone (Prog : Type u) {Value : Type v} {Pred : Type w} {EPosts : Type w'}
    [WP Prog Value Pred EPosts] [PartialOrder Pred] [PartialOrder EPosts] : Prop :=
  ∀ x : Prog, (WP.trans x).IsMonotone

/-!
## Derived WP Lemmas

Monotonicity and weakening consequences of `WP.IsMonotone`.
-/

namespace WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
  [WP Prog Value Pred EPosts] [PartialOrder Pred] [PartialOrder EPosts]
  [WP.IsMonotone Prog]

theorem trans_monotone (x : Prog) (post post' : Value → Pred) (eposts eposts' : EPosts)
    (h' : eposts ⊑ eposts') (h : post ⊑ post') : wp x post eposts ⊑ wp x post' eposts' :=
  PredTrans.IsMonotone.apply_mono (pt := WP.trans x) post post' eposts eposts' h' h

theorem wp_monotone_post {x : Prog}
  {post post' : Value → Pred} {eposts : EPosts} (h : post ⊑ post') :
    wp x post eposts ⊑ wp x post' eposts :=
  trans_monotone x post post' eposts eposts PartialOrder.rel_refl h

theorem wp_monotone {x : Prog}
  {post post' : Value → Pred} {eposts eposts' : EPosts} (h : post ⊑ post') (h' : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post' eposts' :=
  trans_monotone x post post' eposts eposts' h' h

theorem wp_monotone_epost {x : Prog}
  {post : Value → Pred} {eposts eposts' : EPosts} (h : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post eposts' :=
  trans_monotone x post post eposts eposts' h PartialOrder.rel_refl

theorem wp_monotone_post_le (x : Prog)
  (post post' : Value → Pred) (eposts : EPosts) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post' eposts :=
  PartialOrder.rel_trans h' (wp_monotone_post h)

theorem wp_monotone_epost_le (x : Prog)
  (post : Value → Pred) (eposts eposts' : EPosts) (h : eposts ⊑ eposts') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post eposts' :=
  PartialOrder.rel_trans h' (wp_monotone_epost h)

@[deprecated wp_monotone_post (since := "2026-09-17")]
theorem wp_consequence (x : Prog)
  (post post' : Value → Pred) (eposts : EPosts) (h : post ⊑ post') :
    wp x post eposts ⊑ wp x post' eposts :=
  wp_monotone_post h

@[deprecated wp_monotone (since := "2026-09-17")]
theorem wp_consequence_econs (x : Prog)
  (post post' : Value → Pred) (eposts eposts' : EPosts) (h : post ⊑ post') (h' : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post' eposts' :=
  wp_monotone h h'

@[deprecated wp_monotone_epost (since := "2026-09-17")]
theorem wp_econs (x : Prog)
  (post : Value → Pred) (eposts eposts' : EPosts) (h' : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post eposts' :=
  wp_monotone_epost h'

@[deprecated wp_monotone_post_le (since := "2026-09-17")]
theorem wp_consequence_le (x : Prog)
  (post post' : Value → Pred) (eposts : EPosts) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post' eposts :=
  wp_monotone_post_le x post post' eposts h h'

@[deprecated wp_monotone_epost_le (since := "2026-09-17")]
theorem wp_econs_le (x : Prog)
  (post : Value → Pred) (eposts eposts' : EPosts) (h : eposts ⊑ eposts') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post eposts' :=
  wp_monotone_epost_le x post eposts eposts' h h'

end WP

/-!
Weakening from `⊥` needs a least exception postcondition. These lemmas take a complete lattice of
exception postconditions.
-/

namespace WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
  [WP Prog Value Pred EPosts] [PartialOrder Pred] [CompleteLattice EPosts] [WP.IsMonotone Prog]

theorem wp_monotone_bot {x : Prog}
  {post : Value → Pred} {eposts : EPosts} :
    wp x post ⊥ ⊑ wp x post eposts := by
  solve_by_elim [wp_monotone_epost, bot_le]

theorem wp_monotone_bot_le (x : Prog)
  (post : Value → Pred) (eposts : EPosts) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post eposts :=
  PartialOrder.rel_trans h wp_monotone_bot

@[deprecated wp_monotone_bot (since := "2026-09-17")]
theorem wp_econs_bot (x : Prog)
  (post : Value → Pred) (eposts : EPosts) :
    wp x post ⊥ ⊑ wp x post eposts :=
  wp_monotone_bot

@[deprecated wp_monotone_bot_le (since := "2026-09-17")]
theorem wp_econs_bot_le (x : Prog)
  (post : Value → Pred) (eposts : EPosts) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post eposts :=
  wp_monotone_bot_le x post eposts h

end WP

/-- Rewriting the program of a weakest precondition along an equation `x = y` weakens it:
the precondition of `y` entails the precondition of `x`. -/
theorem wp_le_wp_of_eq {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
    [WP Prog Value Pred EPosts] [PartialOrder Pred]
    {x y : Prog} (h : x = y) (post : Value → Pred) (eposts : EPosts) :
    wp y post eposts ⊑ wp x post eposts := by
  subst h; exact PartialOrder.rel_refl

end Std.WP
