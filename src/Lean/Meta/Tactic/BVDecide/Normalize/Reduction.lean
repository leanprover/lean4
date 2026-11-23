/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.DSimp

/-!
This module implements the reduction pass which applies various kinds of type theoretic reductions:
- zeta
- zetaDelta
- beta
- ground term evaluation
- match of known ctor
- proj of ctor
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Variant of dsimpProj that only operates on constructors.
-/
def dsimpProj' : Sym.DSimp.DSimproc := fun e => do
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  let some projInfo ← getProjectionFnInfo? declName | return .rfl
  let args := e.getAppArgs
  unless projInfo.numParams < args.size do return .rfl
  let discr := args[projInfo.numParams]!
  unless ← isConstructorApp discr do return .rfl
  Sym.DSimp.dsimpProj e

/--
Apply zeta, zetaDelta, beta, ground term evaluation, match of known ctor and proj of ctor.
-/
public def reductionPass : Pass where
  name := `reductionPass
  run' := do
    let cfg ← PreProcessM.getConfig
    let config := {
      maxSteps := cfg.maxSteps
      instances := true
    }
    let methods := {
      pre := Sym.DSimp.evalGround
        >> Sym.DSimp.zeta
        >> Sym.DSimp.zetaDeltaAll
        >> Sym.DSimp.beta
        >> Sym.DSimp.dsimpMatch
        >> dsimpProj'
    }

    let goal ← PreProcessM.getTargetMVarId
    goal.withContext do
      PreProcessM.dsimpHyps .reduction methods config

end Normalize
end Lean.Meta.Tactic.BVDecide
