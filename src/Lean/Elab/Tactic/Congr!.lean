/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Tactic.Congr!

/-!
# The `congr!` tactic

This is a more powerful version of the `congr` tactic that knows about more congruence lemmas and
can apply to more situations. It is similar to the `congr'` tactic from Mathlib 3.

The `congr!` tactic is used by the `convert` and `convert_to` tactics.

See the syntax docstring for more details.
-/

open Lean Elab Tactic Meta.Tactic.Congr!

namespace Lean.Elab.Tactic

declare_config_elab elabConfig Config

@[builtin_tactic «congr!»] def evalCongr! : Tactic := fun stx =>
  match stx with
  | `(tactic| congr! $[$cfg:config]? $[$n]? $[with $ps?*]?) => do
    let config ← elabConfig (mkOptionalNode cfg)
    let patterns := (Lean.Elab.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
    liftMetaTactic fun g ↦
      let depth := n.map (·.getNat)
      g.congrN! depth config patterns
  | _                     => throwUnsupportedSyntax

end Lean.Elab.Tactic
