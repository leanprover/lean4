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
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Apply zeta, zetaDelta, beta, and ground term evaluation.
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
    }

    let goal ← PreProcessM.getTargetMVarId
    goal.withContext do
      PreProcessM.mapDSimpHyps methods config

end Normalize
end Lean.Meta.Tactic.BVDecide
