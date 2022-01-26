/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.GlobalInstances

namespace Lean.Meta

private def canUnfoldDefault (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  match cfg.transparency with
  | TransparencyMode.all => return true
  | TransparencyMode.default => return !(← isIrreducible info.name)
  | m =>
    if (← isReducible info.name) then
      return true
    else if m == TransparencyMode.instances && isGlobalInstance (← getEnv) info.name then
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
  let env ← getEnv
  match env.find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                             => pure (some info)
  | none                                  => throwUnknownConstant constName

def getConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  let env ← getEnv
  match env.find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                             => pure (some info)
  | none                                  => pure none

end Meta
