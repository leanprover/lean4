/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Tactic.Config

namespace Std.Tactic.Omega

/-- Configures the behaviour of the `omega` tactic. -/
structure OmegaConfig where
  /--
  Split disjunctions in the context.

  Note that with `splitDisjunctions := false` omega will not be able to solve `x = y` goals
  as these are usually handled by introducing `¬ x = y` as a hypothesis, then replacing this with
  `x < y ∨ x > y`.

  On the other hand, `omega` does not currently detect disjunctions which, when split,
  introduce no new useful information, so the presence of irrelevant disjunctions in the context
  can significantly increase run time.
  -/
  splitDisjunctions : Bool := true
  /--
  Whenever `((a - b : Nat) : Int)` is found, register the disjunction
  `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`
  for later splitting.
  -/
  splitNatSub : Bool := true
  /--
  Whenever `Int.natAbs a` is found, register the disjunction
  `0 ≤ a ∧ Int.natAbs a = a ∨ a < 0 ∧ Int.natAbs a = - a` for later splitting.
  -/
  splitNatAbs : Bool := true
  /--
  Whenever `min a b` or `max a b` is found, rewrite in terms of the definition
  `if a ≤ b ...`, for later case splitting.
  -/
  splitMinMax : Bool := true

/--
Allow elaboration of `OmegaConfig` arguments to tactics.
-/
declare_config_elab elabOmegaConfig OmegaConfig
