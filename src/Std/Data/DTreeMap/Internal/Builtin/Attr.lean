/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Lean.Elab.Tactic.Simp

open Lean Meta.Simp

/-!
# `@[tree_tac]` attribute
-/

namespace Std.Internal.TreeMap

builtin_initialize treeTacExt : Meta.SimpExtension
  ← Meta.registerSimpAttr `tree_tac "simp theorems used by internal DTreeMap lemmas"
