/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.GlobalInstances

namespace Lean.Meta

private def getDefInfo (info : ConstantInfo) : MetaM (Option ConstantInfo) := do
  match (← read).config.transparency with
  | TransparencyMode.all => return some info
  | TransparencyMode.default => return some info
  | m =>
    if (← isReducible info.name) then
      return some info
    else if m == TransparencyMode.instances && isGlobalInstance (← getEnv) info.name then
      return some info
    else
      return none

def getConst? (constName : Name) : MetaM (Option ConstantInfo) := do
  let env ← getEnv
  match env.find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => getDefInfo info
  | some info                             => pure (some info)
  | none                                  => throwUnknownConstant constName

def getConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  let env ← getEnv
  match env.find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => getDefInfo info
  | some info                             => pure (some info)
  | none                                  => pure none

end Meta
