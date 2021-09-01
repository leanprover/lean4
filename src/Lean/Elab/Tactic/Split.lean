/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Split
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

@[builtinTactic Lean.Parser.Tactic.split] def evalSplit : Tactic := fun stx => do
  unless stx[1].isNone do
    throwError "'split' tatic, term to split is not supported yet"
  liftMetaTactic fun mvarId => do
    let loc := expandOptLocation stx[2]
    match loc with
    | Location.targets hUserNames simplifyTarget =>
      if (hUserNames.size > 0 && simplifyTarget) || hUserNames.size > 1 then
        throwErrorAt stx[2] "'split' tactic failed, select a single target to split"
      if simplifyTarget then
        let some mvarIds ← splitTarget? mvarId | throwError "'split' tactic failed"
        return mvarIds
      else
        let fvarId := (← getLocalDeclFromUserName hUserNames[0]).fvarId
        let some mvarIds ← splitLocalDecl? mvarId fvarId | throwError "'split' tactic failed"
        return mvarIds
    | Location.wildcard =>
      let fvarIds ← getNondepPropHyps mvarId
      for fvarId in fvarIds do
        if let some mvarIds ← splitLocalDecl? mvarId fvarId then
          return mvarIds
      let some mvarIds ← splitTarget? mvarId | throwError "'split' tactic failed"
      return mvarIds

end Lean.Elab.Tactic
