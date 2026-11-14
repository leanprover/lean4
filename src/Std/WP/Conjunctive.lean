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

A program `x` has a conjunctive weakest precondition when its transformer is conjunctive:
`WP.IsConjunctive x`, which abbreviates `(WP.trans x).IsConjunctive`. The meet
`wp x Q₁ E₁ ⊓ wp x Q₂ E₂` of two weakest preconditions then lies below the weakest precondition
`wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)` of the componentwise meet of the postconditions. The instances for the
base monads and the monad transformers are in `Std.WP.Monad.Conjunctive`.
-/

namespace Std.WP

/-- The transformer of the program `x` is conjunctive. -/
abbrev WP.IsConjunctive {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
    [WP Prog Value Pred EPosts] [CompleteLattice Pred] [CompleteLattice EPosts] (x : Prog) : Prop :=
  (WP.trans x).IsConjunctive

/-- The transformer of the program `x` is conjunctive. -/
@[deprecated WP.IsConjunctive (since := "2026-11-13")]
abbrev WPConjunctive {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
    [WP Prog Value Pred EPosts] [CompleteLattice Pred] [CompleteLattice EPosts] (x : Prog) : Prop :=
  WP.IsConjunctive x

end Std.WP
