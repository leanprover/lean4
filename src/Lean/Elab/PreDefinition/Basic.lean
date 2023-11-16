/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.NoncomputableAttr
import Lean.Util.CollectLevelParams
import Lean.Meta.AbstractNestedProofs
import Lean.Elab.RecAppSyntax
import Lean.Elab.DefView

namespace Lean.Elab
open Meta
open Term

/--
  A (potentially recursive) definition.
  The elaborator converts it into Kernel definitions using many different strategies.
-/
structure PreDefinition where
  ref         : Syntax
  kind        : DefKind
  levelParams : List Name
  modifiers   : Modifiers
  declName    : Name
  type        : Expr
  value       : Expr
  deriving Inhabited

def instantiateMVarsAtPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    pure { preDef with type := (← instantiateMVars preDef.type), value := (← instantiateMVars preDef.value) }

def levelMVarToParamPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    pure { preDef with type := (← levelMVarToParam preDef.type), value := (← levelMVarToParam preDef.value) }

private def getLevelParamsPreDecls (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (List Name) := do
  let mut s : CollectLevelParams.State := {}
  for preDef in preDefs do
    s := collectLevelParams s preDef.type
    s := collectLevelParams s preDef.value
  match sortDeclLevelParams scopeLevelNames allUserLevelNames s.params with
  | Except.error msg      => throwError msg
  | Except.ok levelParams => pure levelParams

def fixLevelParams (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (Array PreDefinition) := do
  -- We used to use `shareCommon` here, but is was a bottleneck
  let levelParams ← getLevelParamsPreDecls preDefs scopeLevelNames allUserLevelNames
  let us := levelParams.map mkLevelParam
  let fixExpr (e : Expr) : Expr :=
    e.replace fun c => match c with
      | Expr.const declName _ => if preDefs.any fun preDef => preDef.declName == declName then some $ Lean.mkConst declName us else none
      | _ => none
  return preDefs.map fun preDef =>
    { preDef with
      type        := fixExpr preDef.type,
      value       := fixExpr preDef.value,
      levelParams := levelParams }

def applyAttributesOf (preDefs : Array PreDefinition) (applicationTime : AttributeApplicationTime) : TermElabM Unit := do
  for preDef in preDefs do
    applyAttributesAt preDef.declName preDef.modifiers.attrs applicationTime

def abstractNestedProofs (preDef : PreDefinition) : MetaM PreDefinition := withRef preDef.ref do
  if preDef.kind.isTheorem || preDef.kind.isExample then
    pure preDef
  else do
    let value ← Meta.abstractNestedProofs preDef.declName preDef.value
    pure { preDef with value := value }

/-- Auxiliary method for (temporarily) adding pre definition as an axiom -/
def addAsAxiom (preDef : PreDefinition) : MetaM Unit := do
  withRef preDef.ref do
    addDecl <| Declaration.axiomDecl { name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, isUnsafe := preDef.modifiers.isUnsafe }

private def shouldGenCodeFor (preDef : PreDefinition) : Bool :=
  !preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable

private def compileDecl (decl : Declaration) : TermElabM Bool := do
  try
    Lean.compileDecl decl
  catch ex =>
    if (← read).isNoncomputableSection then
      return false
    else
      throw ex
  return true

private def addNonRecAux (preDef : PreDefinition) (compile : Bool) (all : List Name) (applyAttrAfterCompilation := true) : TermElabM Unit :=
  withRef preDef.ref do
    let preDef ← abstractNestedProofs preDef
    let decl ←
      match preDef.kind with
      | DefKind.«theorem» =>
        pure <| Declaration.thmDecl {
          name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value, all
        }
      | DefKind.«opaque»  =>
        pure <| Declaration.opaqueDecl {
          name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value
          isUnsafe := preDef.modifiers.isUnsafe, all
        }
      | DefKind.«abbrev»  =>
        pure <| Declaration.defnDecl {
          name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value
          hints := ReducibilityHints.«abbrev»
          safety := if preDef.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe,
          all }
      | _ => -- definitions and examples
        pure <| Declaration.defnDecl {
          name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value
          hints := ReducibilityHints.regular (getMaxHeight (← getEnv) preDef.value + 1)
          safety := if preDef.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe,
          all }
    addDecl decl
    withSaveInfoContext do  -- save new env
      addTermInfo' preDef.ref (← mkConstWithLevelParams preDef.declName) (isBinder := true)
    applyAttributesOf #[preDef] AttributeApplicationTime.afterTypeChecking
    if preDef.modifiers.isNoncomputable then
      modifyEnv fun env => addNoncomputable env preDef.declName
    if compile && shouldGenCodeFor preDef then
      discard <| compileDecl decl
    if applyAttrAfterCompilation then
      applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

def addAndCompileNonRec (preDef : PreDefinition) (all : List Name := [preDef.declName]) : TermElabM Unit := do
  addNonRecAux preDef (compile := true) (all := all)

def addNonRec (preDef : PreDefinition) (applyAttrAfterCompilation := true) (all : List Name := [preDef.declName]) : TermElabM Unit := do
  addNonRecAux preDef (compile := false) (applyAttrAfterCompilation := applyAttrAfterCompilation) (all := all)

/--
  Eliminate recursive application annotations containing syntax. These annotations are used by the well-founded recursion module
  to produce better error messages. -/
def eraseRecAppSyntaxExpr (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => pure <| TransformStep.done <| if (getRecAppSyntax? e).isSome then e.mdataExpr! else e)

def eraseRecAppSyntax (preDef : PreDefinition) : CoreM PreDefinition :=
  return { preDef with value := (← eraseRecAppSyntaxExpr preDef.value) }

def addAndCompileUnsafe (preDefs : Array PreDefinition) (safety := DefinitionSafety.unsafe) : TermElabM Unit := do
  let preDefs ← preDefs.mapM fun d => eraseRecAppSyntax d
  withRef preDefs[0]!.ref do
    let all  := preDefs.toList.map (·.declName)
    let decl := Declaration.mutualDefnDecl <| ← preDefs.toList.mapM fun preDef => return {
        name        := preDef.declName
        levelParams := preDef.levelParams
        type        := preDef.type
        value       := preDef.value
        hints       := ReducibilityHints.opaque
        safety, all
      }
    addDecl decl
    withSaveInfoContext do  -- save new env
      for preDef in preDefs do
        addTermInfo' preDef.ref (← mkConstWithLevelParams preDef.declName) (isBinder := true)
    applyAttributesOf preDefs AttributeApplicationTime.afterTypeChecking
    discard <| compileDecl decl
    applyAttributesOf preDefs AttributeApplicationTime.afterCompilation
    return ()

def addAndCompilePartialRec (preDefs : Array PreDefinition) : TermElabM Unit := do
  if preDefs.all shouldGenCodeFor then
    withEnableInfoTree false do
      addAndCompileUnsafe (safety := DefinitionSafety.partial) <| preDefs.map fun preDef =>
        { preDef with
          declName  := Compiler.mkUnsafeRecName preDef.declName
          value     := preDef.value.replace fun e => match e with
            | Expr.const declName us =>
              if preDefs.any fun preDef => preDef.declName == declName then
                some <| mkConst (Compiler.mkUnsafeRecName declName) us
              else
                none
            | _ => none
          modifiers := {} }

private def containsRecFn (recFnName : Name) (e : Expr) : Bool :=
  (e.find? fun e => e.isConstOf recFnName).isSome

def ensureNoRecFn (recFnName : Name) (e : Expr) : MetaM Expr := do
  if containsRecFn recFnName e then
    Meta.forEachExpr e fun e => do
      if e.isAppOf recFnName then
        throwError "unexpected occurrence of recursive application{indentExpr e}"
    pure e
  else
    pure e

end Lean.Elab
