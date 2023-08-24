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

/--
Look up a constant name, returning the `ConstantInfo`
if it should be unfolded at the current reducibility settings,
or `none` otherwise.

This is part of the implementation of `whnf`.
External users wanting to look up names should be using `Lean.getConstInfo`.
-/
def getUnfoldableConst? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                 => return some info
  | none                      => throwUnknownConstant constName

/--
As with `getUnfoldableConst?` but return `none` instead of failing if the constant is not found.
-/
def getUnfoldableConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                 => return some info
  | none                      => return none

end Meta
