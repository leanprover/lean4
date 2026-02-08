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
  mkMapDeclarationExtension (exportEntriesFn := fun env s _ =>
    -- Do not export for non-exposed defs
    s.filter (fun n _ => env.find? n |>.any (·.hasValue)) |>.toArray)

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
-/
def copyPrivateUnfoldTheorem : GetUnfoldEqnFn := fun declName => do
  withTraceNode `ReservedNameAction (pure m!"{exceptOptionEmoji ·} copyPrivateUnfoldTheorem running for {declName}") do
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
  return none

builtin_initialize
  registerGetUnfoldEqnFn copyPrivateUnfoldTheorem

end Lean.Elab.WF
