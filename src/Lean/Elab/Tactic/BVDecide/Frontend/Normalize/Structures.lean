/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Simp
import Lean.Meta.Injective

/-!
This module contains the implementation of the pre processing pass for automatically splitting up
structures containing information about supported types into individual parts recursively.

The implementation runs cases recursively on all "interesting" types where a type is interesting if
it is a non recursive structure and at least one of the following conditions hold:
- it contains something of type `BitVec`/`UIntX`/`Bool`
- it is parametrized by an interesting type
- it contains another interesting type
Afterwards we also apply relevant `injEq` theorems to support at least equality for these types out
of the box.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

partial def structuresPass : Pass where
  name := `structures
  run' goal := do
    let interesting := (← PreProcessM.getTypeAnalysis).interestingStructures
    if interesting.isEmpty then return goal
    let goals ← goal.casesRec fun decl => do
      if decl.isLet || decl.isImplementationDetail then
        return false
      else
        let some const := decl.type.getAppFn.constName? | return false
        return interesting.contains const
    match goals with
    | [goal] => postprocess goal interesting
    | _ => throwError "structures preprocessor generated more than 1 goal"
where
  postprocess (goal : MVarId) (interesting : Std.HashSet Name) : PreProcessM (Option MVarId) := do
    goal.withContext do
      let mut relevantLemmas : SimpTheoremsArray := #[]
      relevantLemmas ← relevantLemmas.addTheorem (.decl ``ne_eq) (← mkConstWithLevelParams ``ne_eq)
      for const in interesting do
        let constInfo ← getConstInfoInduct const
        let ctorName := (← getConstInfoCtor constInfo.ctors.head!).name
        let lemmaName := mkInjectiveEqTheoremNameFor ctorName
        if (← getEnv).find? lemmaName |>.isSome then
          trace[Meta.Tactic.bv] m!"Using injEq lemma: {lemmaName}"
          let statement ← mkConstWithLevelParams lemmaName
          relevantLemmas ← relevantLemmas.addTheorem (.decl lemmaName) statement
      let cfg ← PreProcessM.getConfig
      let simpCtx ← Simp.mkContext
        (config := { failIfUnchanged := false, maxSteps := cfg.maxSteps })
        (simpTheorems := relevantLemmas)
        (congrTheorems := ← getSimpCongrTheorems)
      let ⟨result?, _⟩ ← simpGoal goal (ctx := simpCtx) (fvarIdsToSimp := ← getPropHyps)
      let some (_, newGoal) := result? | return none
      return newGoal

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
