/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic

/-!
This file implements the type analysis pass for the structures and enum inductives pass. It figures
out which types that occur either directly or transitively (e.g. through being contained in a
structure) qualify for further treatment by the structures or enum pass.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

partial def typeAnalysisPass : Pass where
  name := `typeAnalysis
  run' goal := do
    checkContext goal
    return goal
where
  checkContext (goal : MVarId) : PreProcessM Unit := do
    goal.withContext do
      for decl in ← getLCtx do
        if !decl.isLet && !decl.isImplementationDetail then
          discard <| typeInteresting decl.type

  constInteresting (n : Name) : PreProcessM Bool := do
    let analysis ← PreProcessM.getTypeAnalysis
    if analysis.interestingStructures.contains n || analysis.interestingEnums.contains n then
      return true
    else if analysis.uninteresting.contains n then
      return false

    let env ← getEnv
    if isStructure env n then
      let constInfo ← getConstInfoInduct n
      if constInfo.isRec then
        PreProcessM.markUninterestingType n
        return false

      let ctorTyp := (← getConstInfoCtor constInfo.ctors.head!).type
      let analyzer state arg := do return state || (← typeInteresting (← arg.fvarId!.getType))
      let interesting ← forallTelescope ctorTyp fun args _ => args.foldlM (init := false) analyzer
      if interesting then
        PreProcessM.markInterestingStructure n
      return interesting
    else if ← isEnumType n then
      PreProcessM.markInterestingEnum n
      return true
    else
      PreProcessM.markUninterestingType n
      return false

  typeInteresting (expr : Expr) : PreProcessM Bool := do
    match_expr expr with
    | BitVec n => return (← getNatValue? n).isSome
    | UInt8 => return true
    | UInt16 => return true
    | UInt32 => return true
    | UInt64 => return true
    | USize => return true
    | Bool => return true
    | _ =>
      let some const := expr.getAppFn.constName? | return false
      constInteresting const

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
