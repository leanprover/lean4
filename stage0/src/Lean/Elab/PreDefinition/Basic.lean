/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.SCC
import Lean.Meta.AbstractNestedProofs
import Lean.Elab.Term
import Lean.Elab.DefView
import Lean.Elab.PreDefinition.MkInhabitant

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

private def levelMVarToParamPreDeclsAux (preDefs : Array PreDefinition) : StateRefT Nat TermElabM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    pure { preDef with type := (← levelMVarToParam' preDef.type), value := (← levelMVarToParam' preDef.value) }

def levelMVarToParamPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
  (levelMVarToParamPreDeclsAux preDefs).run' 1

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
      | Expr.const declName _ _ => if preDefs.any fun preDef => preDef.declName == declName then some $ Lean.mkConst declName us else none
      | _ => none
  pure $ preDefs.map fun preDef =>
    { preDef with
      type        := fixExpr preDef.type,
      value       := fixExpr preDef.value,
      levelParams := levelParams }

def applyAttributesOf (preDefs : Array PreDefinition) (applicationTime : AttributeApplicationTime) : TermElabM Unit := do
  for preDef in preDefs do
    applyAttributesAt preDef.declName preDef.modifiers.attrs applicationTime

def abstractNestedProofs (preDef : PreDefinition) : MetaM PreDefinition :=
  if preDef.kind.isTheorem || preDef.kind.isExample then
    pure preDef
  else do
    let value ← Meta.abstractNestedProofs preDef.declName preDef.value
    pure { preDef with value := value }

/- Auxiliary method for (temporarily) adding pre definition as an axiom -/
def addAsAxiom (preDef : PreDefinition) : MetaM Unit := do
  withRef preDef.ref do
    addDecl <| Declaration.axiomDecl { name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, isUnsafe := preDef.modifiers.isUnsafe }

private def shouldGenCodeFor (preDef : PreDefinition) : Bool :=
  !preDef.kind.isTheorem && !preDef.modifiers.isNoncomputable

private def addNonRecAux (preDef : PreDefinition) (compile : Bool) : TermElabM Unit :=
  withRef preDef.ref do
    let preDef ← abstractNestedProofs preDef
    let env ← getEnv
    let decl :=
      match preDef.kind with
      | DefKind.«theorem» =>
        Declaration.thmDecl { name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value }
      | DefKind.«opaque»  =>
        Declaration.opaqueDecl { name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value,
                                 isUnsafe := preDef.modifiers.isUnsafe }
      | DefKind.«abbrev»  =>
        Declaration.defnDecl { name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value,
                               hints := ReducibilityHints.«abbrev»,
                               safety := if preDef.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe }
      | _ => -- definitions and examples
        Declaration.defnDecl { name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value,
                               hints := ReducibilityHints.regular (getMaxHeight env preDef.value + 1),
                               safety := if preDef.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe }
    addDecl decl
    applyAttributesOf #[preDef] AttributeApplicationTime.afterTypeChecking
    if compile && shouldGenCodeFor preDef then
      compileDecl decl
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

def addAndCompileNonRec (preDef : PreDefinition) : TermElabM Unit := do
  addNonRecAux preDef true

def addNonRec (preDef : PreDefinition) : TermElabM Unit := do
  addNonRecAux preDef false

def addAndCompileUnsafe (preDefs : Array PreDefinition) (safety := DefinitionSafety.unsafe) : TermElabM Unit :=
  withRef preDefs[0].ref do
    let decl := Declaration.mutualDefnDecl $ preDefs.toList.map fun preDef => {
        name        := preDef.declName
        levelParams := preDef.levelParams
        type        := preDef.type
        value       := preDef.value
        safety      := safety
        hints       := ReducibilityHints.opaque
      }
    addDecl decl
    applyAttributesOf preDefs AttributeApplicationTime.afterTypeChecking
    compileDecl decl
    applyAttributesOf preDefs AttributeApplicationTime.afterCompilation
    pure ()

def addAndCompilePartialRec (preDefs : Array PreDefinition) : TermElabM Unit := do
  if preDefs.all shouldGenCodeFor then
    addAndCompileUnsafe (safety := DefinitionSafety.partial) <| preDefs.map fun preDef =>
      { preDef with
        declName  := Compiler.mkUnsafeRecName preDef.declName,
        value     := preDef.value.replace fun e => match e with
          | Expr.const declName us _ =>
            if preDefs.any fun preDef => preDef.declName == declName then
              some $ mkConst (Compiler.mkUnsafeRecName declName) us
            else
              none
          | _ => none,
        modifiers := {} }

end Lean.Elab
