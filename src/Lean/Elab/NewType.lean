/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Elab.DeclModifiers
public import Lean.Elab.DeclarationRange
public import Lean.Meta.VirtualStructure

public section

namespace Lean.Elab.Command
open Meta

/--
Adds the constructor `ctorName` and projector `projName` of the already elaborated `newtype`
`declName`, whose underlying type is the body of its definition. Reading the parameters off the
elaborated `declName` (instead of re-elaborating its binders) is what makes section variables,
auto-bound implicits and universe parameters behave exactly as for `def`.
-/
private def addNewtypeCtorProj (declName ctorName projName fieldName : Name) : TermElabM Nat := do
  let info ← getConstInfoDefn declName
  let us := info.levelParams.map mkLevelParam
  forallTelescope info.type fun params resultType => do
    unless (← whnf resultType).isSort do
      throwError "invalid `newtype`, the right-hand side must be a type, but has type{indentExpr resultType}"
    let underlying := info.value.beta params
    let self := mkAppN (mkConst declName us) params
    let implicitParams ← params.filterMapM fun p => do
      return if (← p.fvarId!.getDecl).binderInfo.isExplicit then some (p.fvarId!, .implicit) else none
    -- Importers can only reduce `projName (ctorName a)` in the kernel if both bodies are exposed,
    -- so mirror whatever the `def` elaborator decided for `declName`.
    let exposed := (← getEnv).hasExposedBody declName
    withNewBinderInfos implicitParams do
      let addIdentity (name argName : Name) (argType resultType : Expr) : TermElabM Unit :=
        withLocalDeclD argName argType fun a => do
          let type ← mkForallFVars (params.push a) resultType
          let value ← mkLambdaFVars (params.push a) a
          let hints := .regular (getMaxHeight (← getEnv) value + 1)
          let decl := .defnDecl (← mkDefinitionValInferringUnsafe name info.levelParams type value hints)
          addDecl decl (forceExpose := exposed)
          compileDecl decl
      addIdentity ctorName fieldName underlying self
      addIdentity projName `self self underlying
    return params.size

@[builtin_command_elab Lean.Parser.Command.newtypeCmd]
def elabNewtype : CommandElab
  | `($mods:declModifiers newtype $declId $params* := $ty with $projId:ident) => do
    let modifiers ← elabModifiers mods
    let { declName, .. } ← liftTermElabM <|
      Term.expandDeclId (← getCurrNamespace) (← getLevelNames) declId modifiers
    let ctorName := declName ++ `mk
    let projName := declName ++ projId.getId
    elabCommand <| ← `($mods:declModifiers def $declId $params* := $ty)
    let numParams ← liftTermElabM <| addNewtypeCtorProj declName ctorName projName projId.getId
    addDeclarationRangesFromSyntax ctorName declId
    addDeclarationRangesFromSyntax projName projId
    addConstInfo projId projName
    for n in [declName, ctorName, projName] do
      setIrreducibleAttribute n
    modifyEnv (registerVirtualStructure · { typeName := declName, ctorName, projName, numParams })
    for n in [ctorName, projName] do
      liftCoreM <| enableRealizationsForConst n
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
