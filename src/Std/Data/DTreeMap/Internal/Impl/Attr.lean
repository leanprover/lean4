/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Lean.Elab.Tactic.Simp
import Lean.Meta.Tactic.Simp.RegisterCommand

open Lean

/-!
# `@[tree_tac]` attribute
-/

register_simp_attr tree_tac

-- builtin_initialize treeTacExt : Meta.SimpExtension ←
--   Meta.registerSimpAttr `tree_tac "simp theorems used by the internal tree_tac tactic"
