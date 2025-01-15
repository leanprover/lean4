/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.DoNotSimp

namespace Lean.Meta.Grind

/-- Returns the array of simprocs used by `grind`. -/
protected def getSimprocs : MetaM (Array Simprocs) := do
  let s ← grindNormSimprocExt.getSimprocs
  let s ← addDoNotSimp s
  return #[s, (← Simp.getSEvalSimprocs)]

/-- Returns the simplification context used by `grind`. -/
protected def getSimpContext : MetaM Simp.Context := do
  let thms ← grindNormExt.getTheorems
  Simp.mkContext
    (config := { arith := true })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))

@[export lean_grind_normalize]
def normalizeImp (e : Expr) : MetaM Expr := do
  let (r, _) ← Meta.simp e (← Grind.getSimpContext) (← Grind.getSimprocs)
  return r.expr

end Lean.Meta.Grind
