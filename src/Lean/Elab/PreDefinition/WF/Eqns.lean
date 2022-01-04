/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo where
  declNames      : Array Name
  levelParams    : List Name
  type           : Expr
  value          : Expr
  declNameNonRec : Name
  deriving Inhabited

def mkEqns (info : EqnInfo) : MetaM (Array Name) := do
  return #[] -- TODO

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension `wfEqInfo

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) : CoreM Unit := do
  let declNames := preDefs.map (·.declName)
  modifyEnv fun env =>
    preDefs.foldl (init := env) fun env preDef =>
      eqnInfoExt.insert env preDef.declName { preDef with declNames, declNameNonRec }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  if let some eqs := eqnsExt.getState env |>.map.find? declName then
    return some eqs
  else if let some info := eqnInfoExt.find? env declName then
    let eqs ← mkEqns info
    modifyEnv fun env => eqnsExt.modifyState env fun s => { s with map := s.map.insert declName eqs }
    return some eqs
  else
    return none

builtin_initialize
  registerGetEqnsFn getEqnsFor?
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
