/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Check
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

/--
When the goal `mvarId` type is an inductive datatype,
`constructor` calls `apply` with the first matching constructor.
-/
def _root_.Lean.MVarId.constructor (mvarId : MVarId) (cfg : ApplyConfig := {}) : MetaM (List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `constructor
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        for ctor in ival.ctors do
          try
            return ← mvarId.apply (Lean.mkConst ctor us) cfg
          catch _ =>
            pure ()
        throwTacticEx `constructor mvarId "no applicable constructor found"

def _root_.Lean.MVarId.existsIntro (mvarId : MVarId) (w : Expr) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `exists
    let target ← mvarId.getType'
    matchConstStructure target.getAppFn
      (fun _ => throwTacticEx `exists mvarId "target is not an inductive datatype with one constructor")
      fun _ us cval => do
        if cval.numFields < 2 then
          throwTacticEx `exists mvarId "constructor must have at least two fields"
        let ctor := mkAppN (Lean.mkConst cval.name us) target.getAppArgs[:cval.numParams]
        let ctorType ← inferType ctor
        let (mvars, _, _) ← forallMetaTelescopeReducing ctorType (some (cval.numFields-2))
        let f := mkAppN ctor mvars
        checkApp f w
        let [mvarId] ← mvarId.apply <| mkApp f w
          | throwTacticEx `exists mvarId "unexpected number of subgoals"
        pure mvarId

end Lean.Meta
