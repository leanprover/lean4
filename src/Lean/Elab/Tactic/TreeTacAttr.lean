prelude
import Lean.Meta.Tactic.Simp

open Lean Elab Tactic Meta

builtin_initialize treeTacExt : Meta.SimpExtension
  ← Meta.registerSimpAttr `Std.Internal.tree_tac "simp theorems used by internal DTreeMap lemmas"
