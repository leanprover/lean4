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

`WP Prog Value Pred EPred` interprets a program type `Prog` whose results have type `Value` as a
monotone predicate transformer `PredTrans Pred EPred Value`. For a program `x : Prog`, a normal
postcondition `post : Value → Pred` and an exception postcondition `epost : EPred`, the assertion
`wp x post epost` is the weakest precondition under which `x` establishes `post` and `epost`.

The program type `Prog` determines the other three types, which are `outParam`s of the class.
Instance search runs on `Prog` alone. A term `wp x post epost` therefore fixes the result type, the
assertion lattice and the exception postcondition type from the type of `x`, and each program type
carries one interpretation.

Two examples show the range of `Prog`. The error-state monad `EStateM ε σ` has the instance
`WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop)`. Here a state predicate is the assertion, and an
error paired with a state is the exception postcondition.

A deep embedding is the second example. A command language `Cmd` with assertions `Env → State → Prop`
has the instance `WP Cmd Unit (Env → State → Prop) EPost.Nil`. Its `wp` is defined in terms of an
operational semantics such as an omnisemantics. The file `tests/elab/vcgenImp.lean` carries this
example in full.

Everything here is generic over the program type. The interpretation of a monad and of the monad
transformers is in `Std.WP.Monad`.

## Assertion Language Classes

`Assertion` is an alias type class for `CompleteLattice`.
We use `Assertion Pred` for the assertion language of normal postconditions
and `Assertion EPred` for exception postconditions.
-/

namespace Std.WP

/-!
## The WP Typeclass

The `WP` typeclass interprets a program type `Prog` whose results have type `Value` as a monotone
predicate transformer `wpTrans : Prog → PredTrans Pred EPred Value`.
-/

/-- Weakest precondition interpretation of a program type `Prog` whose results have type `Value`,
as a monotone predicate transformer over assertion language `Pred` with exception postconditions
`EPred`. -/
class WP (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPred : outParam (Type w')) [Assertion Pred] [Assertion EPred] where
  /-- The weakest precondition transformer for a program. -/
  wpTrans : Prog → PredTrans Pred EPred Value
  /-- Monotonicity: weaker postconditions yield weaker preconditions. -/
  wp_trans_monotone (x : Prog) : wpTrans x |>.monotone

/-- Weakest precondition of `x` for normal postcondition `post` and exception postcondition `epost`.
The `WP` interpretation can be supplied explicitly via dot notation (`inst.wp x post epost`). -/
def WP.wp {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'}
    [Assertion Pred] [Assertion EPred] [self : WP Prog Value Pred EPred]
    (x : Prog) (post : Value → Pred) (epost : EPred) : Pred :=
  (self.wpTrans x).apply post epost

-- `wp x post epost` computes the weakest precondition; it is `WP.wp` with the interpretation
-- synthesised as an instance.
export Std.WP.WP (wp)

@[simp, grind =] theorem WP.wpTrans_apply_eq {Prog : Type u} {Value : Type v}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred] (x : Prog) :
  (WP.wpTrans x).apply = wp x := rfl

/-!
## Derived WP Lemmas

Monotonicity and weakening consequences of the `WP` monotonicity axiom.
-/

namespace WP

variable {Prog : Type u} {Value : Type v} [Assertion Pred] [Assertion EPred]
  [WP Prog Value Pred EPred]

theorem wp_consequence (x : Prog)
  (post post' : Value → Pred) (epost : EPred) (h : post ⊑ post') :
    wp x post epost ⊑ wp x post' epost :=
  wp_trans_monotone x post post' epost epost PartialOrder.rel_refl h

theorem wp_consequence_econs (x : Prog)
  (post post' : Value → Pred) (epost epost' : EPred) (h : post ⊑ post') (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post' epost' :=
  wp_trans_monotone x post post' epost epost' h' h

theorem wp_econs (x : Prog)
  (post : Value → Pred) (epost epost' : EPred) (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post epost' :=
  wp_trans_monotone x post post epost epost' h' PartialOrder.rel_refl

theorem wp_econs_bot (x : Prog)
  (post : Value → Pred) (epost : EPred) :
    wp x post ⊥ ⊑ wp x post epost := by
  solve_by_elim [wp_econs, bot_le]

theorem wp_consequence_le (x : Prog)
  (post post' : Value → Pred) (epost : EPred) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post' epost :=
  PartialOrder.rel_trans h' (wp_consequence x post post' epost h)

theorem wp_econs_le (x : Prog)
  (post : Value → Pred) (epost epost' : EPred) (h : epost ⊑ epost') {pre : Pred}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post epost' :=
  PartialOrder.rel_trans h' (wp_econs x post epost epost' h)

theorem wp_econs_bot_le (x : Prog)
  (post : Value → Pred) (epost : EPred) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post epost :=
  PartialOrder.rel_trans h (wp_econs_bot x post epost)

end WP

/-- Rewriting the program of a weakest precondition along an equation `x = y` weakens it:
the precondition of `y` entails the precondition of `x`. -/
theorem wp_le_wp_of_eq {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    {x y : Prog} (h : x = y) (post : Value → Pred) (epost : EPred) :
    wp y post epost ⊑ wp x post epost := by
  subst h; exact PartialOrder.rel_refl

end Std.WP
