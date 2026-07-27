/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Main

public section

/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/

namespace Lean.Elab.Tactic.BVDecide

open Meta.Tactic.BVDecide

@[builtin_tactic Lean.Parser.Tactic.bvDecide]
def evalBvDecide : Tactic := fun
  | `(tactic| bv_decide $cfg:optConfig) => do
    let cfg ← elabBVDecideConfig cfg
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile cfg
      liftMetaFinishingTactic fun g => do
        discard <| bvDecide g cfg
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.BVDecide
