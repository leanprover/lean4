/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
public import Std.Internal.Order.Instances
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

/-!
# Conjunctive weakest preconditions

`WPConjunctive x` states that the `wp` of the individual program `x` maps a meet of postconditions
below the `wp` of their meet. The instances for the base monads and the monad transformers are in
`Std.Internal.Do.WP.Monad.Conjunctive`.
-/

namespace Std.Internal.Do

/-- `wp x` is sub-conjunctive: a meet of postconditions maps below the `wp` of their meet. A
healthiness condition of the `WP` interpretation for the individual program `x`; it holds for the base
interpretations and lifts through the transformers. -/
class WPConjunctive {Prog : Type u} {Value : outParam (Type v)} {Pred : outParam (Type w)}
    {EPred : outParam (Type z)} [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    (x : Prog) : Prop where
  /-- A meet of postconditions maps below the `wp` of their meet. -/
  wp_meet_wp_le (Q₁ Q₂ : Value → Pred) (E₁ E₂ : EPred) :
    wp x Q₁ E₁ ⊓ wp x Q₂ E₂ ⊑ wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)

end Std.Internal.Do
