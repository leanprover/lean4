/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Split
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural
open Meta

structure EqnInfo where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  recArgPos   : Nat
  deriving Inhabited

def mkEqns (info : EqnInfo) : MetaM (Array Name) := do
  -- TODO
  trace[Elab.definition.structural.eqns] "mkEqns:\n{info.value}"
  return #[]

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension `structEqInfo

def registerEqnsInfo (preDef : PreDefinition) (recArgPos : Nat) : CoreM Unit := do
  modifyEnv fun env => eqnInfoExt.insert env preDef.declName { preDef with recArgPos }

structure EqnsExtState where
  map : Std.PHashMap Name (Array Name) := {}
  deriving Inhabited

/- We generate the equations on demand, and do not save them on .olean files. -/
builtin_initialize eqnsExt : EnvExtension EqnsExtState ←
  registerEnvExtension (pure {})

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
  registerTraceClass `Elab.definition.structural.eqns

end Lean.Elab.Structural
