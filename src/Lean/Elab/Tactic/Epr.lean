/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
import Lean.Meta.Tactic.Epr
import Init.Tactics
import Lean.Elab.Tactic.BVDecide
import Lean.Meta.Tactic.BVDecide.Attr

/-!
This module is the entrypoint to the `epr` tactic for effectively propositional first order logic
(EPR).
-/

namespace Lean.Elab.Tactic.Epr

@[builtin_tactic Lean.Parser.Tactic.epr]
def evalEpr : Tactic := fun
  | `(tactic| epr $cfg:optConfig) => do
    BVDecide.ensureBvDecide
    let cfg ← Meta.Tactic.BVDecide.elabEprConfig cfg
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← Meta.Tactic.BVDecide.TacticContext.new lratFile cfg.toBVDecideConfig (some #[])
      liftMetaFinishingTactic fun g => do
        Meta.Tactic.epr g cfg
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Epr
