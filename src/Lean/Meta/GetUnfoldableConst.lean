/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
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
  let cfg ← getConfig
  if let some f := ctx.canUnfold? then
    f cfg info
  else
    canUnfoldDefault cfg info

/--
Look up a constant name, returning the `ConstantInfo`
if it is a def/theorem that should be unfolded at the current reducibility settings,
or `none` otherwise.

This is part of the implementation of `whnf`.
External users wanting to look up names should be using `Lean.getConstInfo`.
-/
def getUnfoldableConst? (constName : Name) : MetaM (Option ConstantInfo) := do
  let some ainfo := (← getEnv).findAsync? constName | throwUnknownConstant constName
  match ainfo.kind with
  | .thm =>
    if (← shouldReduceAll) then
      return some ainfo.constInfo.get
    else
      return none
  | _ => match ainfo.toConstantInfo with
    | info@(.defnInfo _) => if (← canUnfold info) then return info else return none
    | _                  => return none

/--
As with `getUnfoldableConst?` but return `none` instead of failing if the constant is not found.
-/
def getUnfoldableConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | _                         => return none

end Meta
