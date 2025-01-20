/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Elab.Tactic.BVDecide.Frontend.Attr
import Lean.Elab.Tactic.Simp

/-!
This module contains the implementation of the pre processing pass for reducing `UIntX`/`IntX` to
`BitVec` and thus allow `bv_decide` to reason about them.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

def intToBitVecPass : Pass where
  name := `intToBitVec
  run' goal := do
    -- TODO: change this to "if we detect usize look for hypothesis"
    if ← detectUSize goal then
      logWarning "bv_decide is currently unable to reason about USize"
    let intToBvThms ← intToBitVecExt.getTheorems
    let cfg ← PreProcessM.getConfig
    let simpCtx ← Simp.mkContext
      (config := { failIfUnchanged := false, zetaDelta := true, maxSteps := cfg.maxSteps })
      (simpTheorems := #[intToBvThms])
      (congrTheorems := (← getSimpCongrTheorems))

    let hyps ← goal.getNondepPropHyps
    let ⟨result?, _⟩ ← simpGoal goal (ctx := simpCtx) (fvarIdsToSimp := hyps)
    let some (_, newGoal) := result? | return none
    return newGoal
where
  detectUSize (goal : MVarId) : MetaM Bool := do
    let checker e :=
      match e with
      | .const n _ => n == ``USize || n == ``System.Platform.numBits
      | _ => false

    let indicatesUSize (e : Expr) := Option.isSome <| e.find? checker

    goal.withContext do
      let lctx ← getLCtx
      if lctx.any (fun decl => indicatesUSize decl.type) then
        return true
      else
        return indicatesUSize (← goal.getType)

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
