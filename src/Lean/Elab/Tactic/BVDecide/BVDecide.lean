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

def ensureBvDecide : CoreM Unit := do
  let env ← getEnv
  if (env.getModuleIdx? `Std.Tactic.BVDecide).isNone then
    throwError "to use `bv_decide`, please include `import Std.Tactic.BVDecide`"

@[builtin_tactic Lean.Parser.Tactic.bvDecide]
def evalBvDecide : Tactic := fun
  | `(tactic| bv_decide $cfg:optConfig $[$types:bvTypes]?) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfg
    let types ← elabBVDecideTypes types
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile cfg types
      liftMetaFinishingTactic fun g => do
        discard <| Meta.Sym.SymM.run <| bvDecide g cfg
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.BVDecide
