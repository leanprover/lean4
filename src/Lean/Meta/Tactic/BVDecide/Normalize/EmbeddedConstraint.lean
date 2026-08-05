/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.Normalize.Bool
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic

/-!
This module contains the implementation of the embedded constraint substitution pass in the fixpoint
pipeline, substituting hypotheses of the form `h : x = true` in other hypotheses.


-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

def embeddedConstraintProc (minDepth : UInt32) (hypMap : PersistentHashMap Sym.ExprPtr Expr) :
    Sym.Simp.Simproc := fun e => do
  if e.approxDepth < minDepth then
    return .rfl (done := true)
  let some proof := hypMap.find? ⟨e⟩ | return .rfl
  return .step (← Sym.share <| toExpr Bool.true) proof (done := true) (contextDependent := true)

/--
Substitute embedded constraints. That is look for hypotheses of the form `h : x = true` and use
them to substitute occurrences of `x` within other hypotheses. Additionally this drops all
redundant top level hypotheses.
-/
public def embeddedConstraintPass : Pass where
  name := `embeddedConstraintSubstitution
  run' := do
    let goal ← PreProcessM.getGoal
    goal.withContext do
      let hyps ← PreProcessM.getHyps
      let mut relevantHypsMap : PersistentHashMap Sym.ExprPtr Expr := {}
      let mut relevantHypsIdxMap : Std.HashMap Nat Sym.ExprPtr := {}
      let mut seen : Std.HashSet Sym.ExprPtr := {}
      let mut minDepth := UInt32.size
      for h : idx in 0...hyps.size do
        let hyp := hyps[idx]
        let type := hyp.type
        let_expr Eq _ lhs rhs := type | continue
        let_expr Bool.true := rhs | continue
        if !seen.contains ⟨lhs⟩ then
          seen := seen.insert ⟨lhs⟩
          relevantHypsIdxMap := relevantHypsIdxMap.insert idx ⟨lhs⟩
          minDepth := minDepth.min lhs.approxDepth.toNat
          relevantHypsMap := relevantHypsMap.insert ⟨lhs⟩ hyp.value

      trace[Meta.Tactic.bv] m!"Chose min depth at: {minDepth}"
      if relevantHypsMap.isEmpty then
        return false

      let cfg ← PreProcessM.getConfig
      let config := {
        maxSteps := cfg.maxSteps
      }
      PreProcessM.mapIdxHyps fun idx hyp => do
        let relevantHypsMap :=
          if let some ptr := relevantHypsIdxMap[idx]? then
            relevantHypsMap.erase ptr
          else
            relevantHypsMap
        let methods := {
          pre := embeddedConstraintProc minDepth.toUInt32 relevantHypsMap
        }
        let res ← Sym.simp hyp.type methods config
        hyp.applySimpResult res

end Normalize
end Lean.Meta.Tactic.BVDecide
