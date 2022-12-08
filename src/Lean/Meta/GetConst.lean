/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.GlobalInstances

namespace Lean.Meta

private def canUnfoldDefault (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  match cfg.transparency with
  | .all => return true
  | .default => return !(← isIrreducible info.name)
  | m =>
    if (← isReducible info.name) then
      return true
    else if m == .instances && isGlobalInstance (← getEnv) info.name then
      return true
    else
      return false

def canUnfold (info : ConstantInfo) : MetaM Bool := do
  let ctx ← read
  if let some f := ctx.canUnfold? then
    f ctx.config info
  else
    canUnfoldDefault ctx.config info

def getConst? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                 => return some info
  | none                      => throwUnknownConstant constName

def getConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                 => return some info
  | none                      => return none

end Meta
