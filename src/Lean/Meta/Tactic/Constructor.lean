/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Apply

public section

namespace Lean.Meta

/--
When the goal `mvarId` type is an inductive datatype,
`constructorCore` calls `apply` with the first matching constructor.

Along with the resulting goals, it returns the constructors that `apply` succeeds with, in
declaration order. When `findAll` is `false`, the search stops at the first match, so at most one
constructor is reported.

Private constructors that are not accessible in the current context are skipped.
-/
def _root_.Lean.MVarId.constructorCore (mvarId : MVarId) (cfg : ApplyConfig := {})
    (findAll : Bool := true) : MetaM (List MVarId × Array Name) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `constructor
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        let mut matching := #[]
        let mut skipped? : Option Name := none
        for ctor in ival.ctors do
          -- The accessibility check may log a warning, which is discarded here with the trial state.
          let (applies, inaccessible) ← withoutModifyingState do
            let applies := (← observing? (mvarId.apply (Lean.mkConst ctor us) cfg)).isSome
            return (applies, ← isInaccessiblePrivateName ctor)
          if applies then
            if inaccessible then
              skipped? := skipped? <|> some ctor
            else
              matching := matching.push ctor
              if !findAll then break
        let some ctor := matching[0]?
          | if let some ctor := skipped? then
              throwTacticEx `constructor mvarId m!"constructor `{.ofConstName ctor}` is marked as private"
            throwTacticEx `constructor mvarId "no applicable constructor found"
        checkPrivateInPublic ctor
        return (← mvarId.apply (Lean.mkConst ctor us) cfg, matching)

/--
When the goal `mvarId` type is an inductive datatype,
`constructor` calls `apply` with the first matching constructor.
-/
def _root_.Lean.MVarId.constructor (mvarId : MVarId) (cfg : ApplyConfig := {}) : MetaM (List MVarId) :=
  return (← mvarId.constructorCore cfg (findAll := false)).1

def _root_.Lean.MVarId.existsIntro (mvarId : MVarId) (w : Expr) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `exists
    let target ← mvarId.getType'
    matchConstStructure target.getAppFn
      (fun _ => throwTacticEx `exists mvarId "target is not an inductive datatype with one constructor")
      fun _ us cval => do
        if cval.numFields < 2 then
          throwTacticEx `exists mvarId "constructor must have at least two fields"
        let ctor := mkAppN (Lean.mkConst cval.name us) target.getAppArgs[*...cval.numParams]
        let ctorType ← inferType ctor
        let (mvars, _, _) ← forallMetaTelescopeReducing ctorType (some (cval.numFields-2))
        let f := mkAppN ctor mvars
        checkApp f w
        let [mvarId] ← mvarId.apply <| mkApp f w
          | throwTacticEx `exists mvarId "unexpected number of subgoals"
        pure mvarId

end Lean.Meta
