/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Check
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

def constructor (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `constructor
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        for ctor in ival.ctors do
          try
            return ← apply mvarId (Lean.mkConst ctor us)
          catch _ =>
            pure ()
        throwTacticEx `constructor mvarId "no applicable constructor found"

def existsIntro (mvarId : MVarId) (w : Expr) : MetaM MVarId := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `exists
    let target ← getMVarType' mvarId
    matchConstStruct target.getAppFn
      (fun _ => throwTacticEx `exists mvarId "target is not an inductive datatype with one constructor")
      fun ival us cval => do
        if cval.numFields < 2 then
          throwTacticEx `exists mvarId "constructor must have at least two fields"
        let ctor := mkAppN (Lean.mkConst cval.name us) target.getAppArgs[:cval.numParams]
        let ctorType ← inferType ctor
        let (mvars, _, _) ← forallMetaTelescopeReducing ctorType (some (cval.numFields-2))
        let f := mkAppN ctor mvars
        checkApp f w
        let [mvarId] ← apply mvarId <| mkApp f w
          | throwTacticEx `exists mvarId "unexpected number of subgoals"
        pure mvarId

end Lean.Meta
