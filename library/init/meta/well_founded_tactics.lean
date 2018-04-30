/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta

/-- Argument for using_well_founded

  The tactic `rel_tac` has to synthesize an element of type (has_well_founded A).
  The two arguments are: a local representing the function being defined by well
  founded recursion, and a list of recursive equations.
  The equations can be used to decide which well founded relation should be used.

  The tactic `dec_tac` has to synthesize decreasing proofs.
-/
meta structure well_founded_tactics :=
(rel_tac : expr → list expr → tactic unit := λ _ _, tactic.apply_instance)
(dec_tac : tactic unit := tactic.assumption)

meta def well_founded_tactics.default : well_founded_tactics :=
{}
