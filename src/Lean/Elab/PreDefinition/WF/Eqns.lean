/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Rewrite
public import Lean.Meta.Tactic.Split
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Eqns
public import Lean.Meta.ArgsPacker.Basic
public import Lean.Elab.PreDefinition.FixedParams
public import Init.Data.Array.Basic

public section

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo extends EqnInfoCore where
  declNames       : Array Name
  declNameNonRec  : Name
  argsPacker      : ArgsPacker
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) (fixedParamPerms : FixedParamPerms)
    (argsPacker : ArgsPacker) : MetaM Unit := do
  preDefs.forM fun preDef => ensureEqnReservedNamesAvailable preDef.declName
  /-
  See issue #2327.
  Remark: we could do better for mutual declarations that mix theorems and definitions. However, this is a rare
  combination, and we would have add support for it in the equation generator. I did not check which assumptions are made there.
  -/
  unless preDefs.all fun p => p.kind.isTheorem do
    unless (← preDefs.allM fun p => isProp p.type) do
      let declNames := preDefs.map (·.declName)
      modifyEnv fun env =>
        preDefs.foldl (init := env) fun env preDef =>
          eqnInfoExt.insert env preDef.declName { preDef with
            declNames, declNameNonRec, argsPacker, fixedParamPerms }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    mkEqns declName info.declNames (tryRefl := false)
  else
    return none

builtin_initialize
  registerGetEqnsFn getEqnsFor?


/--
This is a hack to fix fallout from #8519, where a non-exposed wfrec definition `foo`
in a module would cause `foo.eq_def` to be defined eagerly and privately,
but it should still be visible from non-module files.

So we create a unfold equation generator that aliases an existing private `eq_def` to
wherever the current module expects it.
-/
def copyPrivateUnfoldTheorem : GetUnfoldEqnFn := fun declName => do
  withTraceNode `ReservedNameAction (pure m!"{exceptOptionEmoji ·} copyPrivateUnfoldTheorem running for {declName}") do
  let name := mkEqLikeNameFor (← getEnv) declName unfoldThmSuffix
  if let some mod ← findModuleOf? declName then
    let unfoldName' := mkPrivateNameCore mod (.str declName unfoldThmSuffix)
    if let some (.thmInfo info) := (← getEnv).find? unfoldName' then
      realizeConst declName name do
        addDecl <| Declaration.thmDecl {
          name,
          type := info.type,
          value := .const unfoldName' (info.levelParams.map mkLevelParam),
          levelParams := info.levelParams
        }
      return name
  return none

builtin_initialize
  registerGetUnfoldEqnFn copyPrivateUnfoldTheorem

end Lean.Elab.WF
