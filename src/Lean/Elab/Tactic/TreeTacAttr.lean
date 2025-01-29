/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Lean.Meta.Tactic.Simp

open Lean.Meta

builtin_initialize treeTacExt : SimpExtension
  ← registerSimpAttr `Std.Internal.tree_tac "simp theorems used by internal DTreeMap lemmas"
