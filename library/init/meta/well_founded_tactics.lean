/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

/-- Argument for using_well_founded -/
meta structure well_founded_tactics :=
(rel_tac : tactic unit := tactic.apply_instance)
/- TODO(Leo): replace tactic.admit -/
(dec_tac : tactic unit := tactic.admit)

meta def well_founded_tactics.default : well_founded_tactics :=
{}
