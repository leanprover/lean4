/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.FixedParams
public import Lean.Meta.ArgsPacker.Basic

namespace Lean.Elab.WF
open Meta

public structure EqnInfo where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  declNames       : Array Name
  declNameNonRec  : Name
  argsPacker      : ArgsPacker
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

public builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s =>
    let all := s.toArray
    -- Do not export for non-exposed defs at exported/server levels
    let exported := s.filter (fun n _ => env.hasExposedBody n) |>.toArray
    { exported, server := exported, «private» := all })

public def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) (fixedParamPerms : FixedParamPerms)
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

/--
This is a hack to fix fallout from #8519, where a non-exposed wfrec definition `foo`
in a module would cause `foo.eq_def` to be defined eagerly and privately,
but it should still be visible from non-module files.

So we create a unfold equation generator that aliases an existing private `eq_def` to
wherever the current module expects it.

We also handle the converse case (#14558): an exposed wfrec definition `foo` from a module
imported without `public import` has its `foo.eq_def` stored under the public name, but
the realization environment may compute a private name for the lookup. In that case,
we alias the public theorem to wherever the current module expects it.
-/
def copyPrivateUnfoldTheorem : GetUnfoldEqnFn := fun declName => do
  withTraceNode `ReservedNameAction (fun _ => pure m!"copyPrivateUnfoldTheorem running for {declName}") do
  let name := mkEqLikeNameFor (← getEnv) declName unfoldThmSuffix
  if let some mod ← findModuleOf? declName then
    let unfoldName' := mkPrivateNameCore mod (.str (privateToUserName declName) unfoldThmSuffix)
    if let some (.thmInfo info) := (← getEnv).find? unfoldName' then
      realizeConst declName name do
        addDecl <| Declaration.thmDecl {
          name,
          type := info.type,
          value := .const unfoldName' (info.levelParams.map mkLevelParam),
          levelParams := info.levelParams
        }
      return name
    -- Also handle the case where the eq_def was stored under the public name (for exposed
    -- definitions from modules imported without `public import`). In this case,
    -- `hasExposedBody` returns false in the realization environment (the defining module is
    -- not in the public view), so `mkEqLikeNameFor` computes a private name while the actual
    -- theorem is stored publicly.
    let unfoldNamePub := .str (privateToUserName declName) unfoldThmSuffix
    if unfoldNamePub != unfoldName' then
      if let some info := (← getEnv).find? unfoldNamePub then
        if info matches .thmInfo _ | .axiomInfo _ then
          realizeConst declName name do
            addDecl <| Declaration.thmDecl {
              name
              type := info.type
              value := .const unfoldNamePub (info.levelParams.map mkLevelParam)
              levelParams := info.levelParams
            }
          return name
  return none

builtin_initialize
  registerGetUnfoldEqnFn copyPrivateUnfoldTheorem

end Lean.Elab.WF
