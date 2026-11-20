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

`WP` carries the predicate transformer only. Every transformer is monotone for the orders of
`Pred` and `EPosts` by `PredTrans.apply_mono`. Further laws are `Prop` classes over the
transformer: `PredTrans.IsConjunctive` states conjunctivity for a lattice of assertions.
-/

namespace Std.WP

/-!
## The WP Typeclass

The `WP` typeclass interprets a program type `Prog` whose results have type `Value` as a
predicate transformer `trans : Prog → PredTrans Pred EPosts Value`.
-/

set_option linter.deprecated false in
/-- Weakest precondition interpretation of a program type `Prog` whose results have type `Value`,
as a monotone predicate transformer over assertions `Pred` with exception postconditions
`EPosts`. -/
class WP (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPosts : outParam (Type w')) [PartialOrder Pred] [PartialOrder EPosts] where
  /-- The weakest precondition transformer for a program. -/
  trans : Prog → PredTrans Pred EPosts Value := wpTrans
  /-- Deprecated alias for `trans`; provide either field when defining an instance. -/
  wpTrans : Prog → PredTrans Pred EPosts Value := trans
  /-- Deprecated: every transformer is monotone by `PredTrans.apply_mono`. -/
  trans_monotone (x : Prog) : PredTrans.Monotone (trans x) :=
    fun _ _ _ _ heposts hpost => (trans x).apply_mono hpost heposts
  /-- Deprecated alias for `trans_monotone`. -/
  wp_trans_monotone (x : Prog) : PredTrans.Monotone (trans x) := trans_monotone x

attribute [deprecated WP.trans (since := "2026-09-17")] WP.wpTrans
attribute [deprecated "every transformer is monotone by `PredTrans.apply_mono`"
  (since := "2026-11-16")] WP.trans_monotone
attribute [deprecated "every transformer is monotone by `PredTrans.apply_mono`"
  (since := "2026-09-17")] WP.wp_trans_monotone
attribute [deprecated_arg EPred EPosts (since := "2026-09-18")] WP

/-- Weakest precondition of `x` for normal postcondition `post` and exception postcondition `eposts`.
The `WP` interpretation can be supplied explicitly via dot notation (`inst.wp x post eposts`). -/
def WP.wp {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type w'}
    [PartialOrder Pred] [PartialOrder EPosts] [self : WP Prog Value Pred EPosts]
    (x : Prog) (post : Value → Pred) (eposts : EPosts) : Pred :=
  (self.trans x).apply post eposts

-- `wp x post eposts` computes the weakest precondition; it is `WP.wp` with the interpretation
-- synthesised as an instance.
export Std.WP.WP (wp)

@[simp, grind =] theorem WP.trans_apply_eq {Prog : Type u} {Value : Type v}
    [PartialOrder Pred] [PartialOrder EPosts] [WP Prog Value Pred EPosts] (x : Prog) :
  (WP.trans x).apply = wp x := rfl

@[deprecated WP.trans_apply_eq (since := "2026-09-17")]
theorem WP.wpTrans_apply_eq {Prog : Type u} {Value : Type v}
    [PartialOrder Pred] [PartialOrder EPosts] [WP Prog Value Pred EPosts] (x : Prog) :
    (WP.trans x).apply = wp x := rfl

/-!
## Derived WP Lemmas

Monotonicity and weakening consequences of `PredTrans.apply_mono`.
-/

namespace WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
  [PartialOrder Pred] [PartialOrder EPosts] [WP Prog Value Pred EPosts]

theorem wp_mono_post {x : Prog}
  {post post' : Value → Pred} {eposts : EPosts} (h : post ⊑ post') :
    wp x post eposts ⊑ wp x post' eposts :=
  (WP.trans x).apply_mono h PartialOrder.rel_refl

theorem wp_mono {x : Prog}
  {post post' : Value → Pred} {eposts eposts' : EPosts} (h : post ⊑ post') (h' : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post' eposts' :=
  (WP.trans x).apply_mono h h'

theorem wp_mono_epost {x : Prog}
  {post : Value → Pred} {eposts eposts' : EPosts} (h : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post eposts' :=
  (WP.trans x).apply_mono PartialOrder.rel_refl h

theorem wp_mono_post_le (x : Prog)
  (post post' : Value → Pred) (eposts : EPosts) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post' eposts :=
  PartialOrder.rel_trans h' (wp_mono_post h)

theorem wp_mono_epost_le (x : Prog)
  (post : Value → Pred) (eposts eposts' : EPosts) (h : eposts ⊑ eposts') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post eposts' :=
  PartialOrder.rel_trans h' (wp_mono_epost h)

@[deprecated wp_mono_post (since := "2026-09-17")]
theorem wp_consequence (x : Prog)
  (post post' : Value → Pred) (eposts : EPosts) (h : post ⊑ post') :
    wp x post eposts ⊑ wp x post' eposts :=
  wp_mono_post h

@[deprecated wp_mono (since := "2026-09-17")]
theorem wp_consequence_econs (x : Prog)
  (post post' : Value → Pred) (eposts eposts' : EPosts) (h : post ⊑ post') (h' : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post' eposts' :=
  wp_mono h h'

@[deprecated wp_mono_epost (since := "2026-09-17")]
theorem wp_econs (x : Prog)
  (post : Value → Pred) (eposts eposts' : EPosts) (h' : eposts ⊑ eposts') :
    wp x post eposts ⊑ wp x post eposts' :=
  wp_mono_epost h'

@[deprecated wp_mono_post_le (since := "2026-09-17")]
theorem wp_consequence_le (x : Prog)
  (post post' : Value → Pred) (eposts : EPosts) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post' eposts :=
  wp_mono_post_le x post post' eposts h h'

@[deprecated wp_mono_epost_le (since := "2026-09-17")]
theorem wp_econs_le (x : Prog)
  (post : Value → Pred) (eposts eposts' : EPosts) (h : eposts ⊑ eposts') {pre : Pred}
    (h' : pre ⊑ wp x post eposts) :
    pre ⊑ wp x post eposts' :=
  wp_mono_epost_le x post eposts eposts' h h'

section Deprecated
set_option linter.missingDocs false

@[deprecated wp_mono_post (since := "2026-11-20")]
abbrev wp_monotone_post := @wp_mono_post

@[deprecated wp_mono (since := "2026-11-20")]
abbrev wp_monotone := @wp_mono

@[deprecated wp_mono_epost (since := "2026-11-20")]
abbrev wp_monotone_epost := @wp_mono_epost

@[deprecated wp_mono_post_le (since := "2026-11-20")]
abbrev wp_monotone_post_le := @wp_mono_post_le

@[deprecated wp_mono_epost_le (since := "2026-11-20")]
abbrev wp_monotone_epost_le := @wp_mono_epost_le

end Deprecated

end WP

/-!
Weakening from `⊥` needs a least exception postcondition. These lemmas take a complete lattice of
exception postconditions.
-/

namespace WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
  [PartialOrder Pred] [CompleteLattice EPosts] [WP Prog Value Pred EPosts]

theorem wp_mono_bot {x : Prog}
  {post : Value → Pred} {eposts : EPosts} :
    wp x post ⊥ ⊑ wp x post eposts := by
  solve_by_elim [wp_mono_epost, bot_le]

theorem wp_mono_bot_le (x : Prog)
  (post : Value → Pred) (eposts : EPosts) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post eposts :=
  PartialOrder.rel_trans h wp_mono_bot

@[deprecated wp_mono_bot (since := "2026-09-17")]
theorem wp_econs_bot (x : Prog)
  (post : Value → Pred) (eposts : EPosts) :
    wp x post ⊥ ⊑ wp x post eposts :=
  wp_mono_bot

@[deprecated wp_mono_bot_le (since := "2026-09-17")]
theorem wp_econs_bot_le (x : Prog)
  (post : Value → Pred) (eposts : EPosts) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post eposts :=
  wp_mono_bot_le x post eposts h

section Deprecated
set_option linter.missingDocs false

@[deprecated wp_mono_bot (since := "2026-11-20")]
abbrev wp_monotone_bot := @wp_mono_bot

@[deprecated wp_mono_bot_le (since := "2026-11-20")]
abbrev wp_monotone_bot_le := @wp_mono_bot_le

end Deprecated

end WP

/-- Rewriting the program of a weakest precondition along an equation `x = y` weakens it:
the precondition of `y` entails the precondition of `x`. -/
theorem wp_le_wp_of_eq {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
    [PartialOrder Pred] [PartialOrder EPosts] [WP Prog Value Pred EPosts]
    {x y : Prog} (h : x = y) (post : Value → Pred) (eposts : EPosts) :
    wp y post eposts ⊑ wp x post eposts := by
  subst h; exact PartialOrder.rel_refl

end Std.WP
