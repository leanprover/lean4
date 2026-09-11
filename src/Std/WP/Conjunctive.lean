/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Basic
public import Std.Internal.Order.Instances
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# Conjunctive weakest preconditions

`WPConjunctive x` states that the meet `wp x Q₁ E₁ ⊓ wp x Q₂ E₂` of two weakest preconditions lies
below the weakest precondition `wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)` of the componentwise meet of the
postconditions. The instances for the base monads and the monad transformers are in
`Std.WP.Monad.Conjunctive`.
-/

namespace Std.WP

/-- `wp x` is sub-conjunctive: the meet of the weakest preconditions of two postconditions lies
below the weakest precondition of the componentwise meet of the postconditions. A healthiness
condition of the `WP` interpretation for the individual program `x`; it holds for the base
interpretations and lifts through the transformers. -/
class WPConjunctive {Prog : Type u} {Value : outParam (Type v)} {Pred : outParam (Type w)}
    {EPred : outParam (Type z)} [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    (x : Prog) : Prop where
  /-- The meet of the weakest preconditions `wp x Q₁ E₁` and `wp x Q₂ E₂` lies below the weakest
  precondition `wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)` of the componentwise meet of the postconditions. -/
  wp_meet_wp_le (Q₁ Q₂ : Value → Pred) (E₁ E₂ : EPred) :
    wp x Q₁ E₁ ⊓ wp x Q₂ E₂ ⊑ wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)

end Std.WP
