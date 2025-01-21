/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Meta.Tactic.Cases

/-!
This module contains the implementation of the pre processing pass for automatically splitting up
structures containing information about supported types into individual parts recursively.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

partial def structuresPass : Pass where
  name := `structures
  run' goal := do
    let (_, supportedTypes) ← checkContext goal |>.run {}

    let detector decl := do
      if decl.isLet then
        return false
      else
        let some const := decl.type.getAppFn.constName? | return false
        return supportedTypes.contains const
    let goals ← goal.casesRec detector
    match goals with
    | [goal] => return goal
    | _ => throwError "structures preprocessor generated more than 1 goal"
where
  checkContext (goal : MVarId) : StateRefT (Std.HashSet Name) MetaM Unit := do
    goal.withContext do
      for decl in ← getLCtx do
        -- TODO: support lets?
        if !decl.isLet then
          let some const := decl.type.getAppFn.constName? | continue
          discard <| checkType const

  checkType (n : Name) : StateRefT (Std.HashSet Name) MetaM Bool := do
    -- TODO: support structures parametrized by BitVec/UInt/Bool
    if (← get).contains n then
     return true

    let env ← getEnv
    let some info := getStructureInfo? env n | return false
    if (← getConstInfoInduct n).isRec then
      return false

    let analyzer field := do
      let typ := (← getConstInfo field.projFn).type
      forallTelescope typ fun _ ret => do
        match_expr ret with
        | BitVec n => return (← getNatValue? n).isSome
        | UInt8 => return true
        | UInt16 => return true
        | UInt32 => return true
        | UInt64 => return true
        | USize => return true
        | Bool => return true
        | _ =>
          let some const := ret.getAppFn.constName? | return false
          checkType const

    let projs ← info.fieldInfo.mapM analyzer
    if projs.contains true then
      modify fun s => s.insert n
      return true
    else
      return false

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
