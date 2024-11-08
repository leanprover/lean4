/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.ShareCommon
import Lean.Compiler.NoncomputableAttr
import Lean.Util.CollectLevelParams
import Lean.Util.NumObjs
import Lean.Util.NumApps
import Lean.PrettyPrinter
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.ForEachExpr
import Lean.Meta.Eqns
import Lean.Elab.RecAppSyntax
import Lean.Elab.DefView
import Lean.Elab.PreDefinition.TerminationHint

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
  termination : TerminationHints
  deriving Inhabited

def PreDefinition.filterAttrs (preDef : PreDefinition) (p : Attribute → Bool) : PreDefinition :=
  { preDef with modifiers := preDef.modifiers.filterAttrs p }

/--
Applies `Lean.instantiateMVars` to the types of values of each predefinition.
-/
def instantiateMVarsAtPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    pure { preDef with type := (← instantiateMVars preDef.type), value := (← instantiateMVars preDef.value) }

/--
Applies `Lean.Elab.Term.levelMVarToParam` to the types of each predefinition.
-/
def levelMVarToParamTypesPreDecls (preDefs : Array PreDefinition) : TermElabM (Array PreDefinition) :=
  preDefs.mapM fun preDef => do
    pure { preDef with type := (← levelMVarToParam preDef.type) }

/--
Collects all the level parameters in sorted order from the types and values of each predefinition.
Throws an "unused universe parameter" error if there is an unused `.{...}` parameter.

See `Lean.collectLevelParams`.
-/
private def getLevelParamsPreDecls (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (List Name) := do
  let mut s : CollectLevelParams.State := {}
  for preDef in preDefs do
    s := collectLevelParams s preDef.type
    s := collectLevelParams s preDef.value
  match sortDeclLevelParams scopeLevelNames allUserLevelNames s.params with
  | Except.error msg      => throwError msg
  | Except.ok levelParams => pure levelParams

def fixLevelParams (preDefs : Array PreDefinition) (scopeLevelNames allUserLevelNames : List Name) : TermElabM (Array PreDefinition) := do
  profileitM Exception s!"fix level params" (← getOptions) do
    withTraceNode `Elab.def.fixLevelParams (fun _ => return m!"fix level params") do
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

register_builtin_option diagnostics.threshold.proofSize : Nat := {
  defValue := 16384
  group    := "diagnostics"
  descr    := "only display proof statistics when proof has at least this number of terms"
}

private def reportTheoremDiag (d : TheoremVal) : TermElabM Unit := do
  if (← isDiagnosticsEnabled) then
    let proofSize ← d.value.numObjs
    if proofSize > diagnostics.threshold.proofSize.get (← getOptions) then
      let sizeMsg := MessageData.trace { cls := `size } m!"{proofSize}" #[]
      let constOccs ← d.value.numApps (threshold := diagnostics.threshold.get (← getOptions))
      let constOccsMsg ← constOccs.mapM fun (declName, numOccs) => return MessageData.trace { cls := `occs } m!"{.ofConstName declName} ↦ {numOccs}" #[]
      -- let info
      logInfo <| MessageData.trace { cls := `theorem } m!"{d.name}" (#[sizeMsg] ++ constOccsMsg)

private def addNonRecAux (preDef : PreDefinition) (compile : Bool) (all : List Name) (applyAttrAfterCompilation := true) : TermElabM Unit :=
  withRef preDef.ref do
    let preDef ← abstractNestedProofs preDef
    let mkDefDecl : TermElabM Declaration :=
      return Declaration.defnDecl {
          name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value
          hints := ReducibilityHints.regular (getMaxHeight (← getEnv) preDef.value + 1)
          safety := if preDef.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe,
          all }
    let mkThmDecl : TermElabM Declaration := do
      let d := {
        name := preDef.declName, levelParams := preDef.levelParams, type := preDef.type, value := preDef.value, all
      }
      reportTheoremDiag d
      return Declaration.thmDecl d
    let decl ←
      match preDef.kind with
      | DefKind.«theorem» => mkThmDecl
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
      | DefKind.def | DefKind.example => mkDefDecl
      | DefKind.«instance» => if ← Meta.isProp preDef.type then mkThmDecl else mkDefDecl
    addDecl decl
    withSaveInfoContext do  -- save new env
      addTermInfo' preDef.ref (← mkConstWithLevelParams preDef.declName) (isBinder := true)
    applyAttributesOf #[preDef] AttributeApplicationTime.afterTypeChecking
    if preDef.modifiers.isNoncomputable then
      modifyEnv fun env => addNoncomputable env preDef.declName
    if compile && shouldGenCodeFor preDef then
      discard <| compileDecl decl
    if applyAttrAfterCompilation then
      generateEagerEqns preDef.declName
      applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

def addAndCompileNonRec (preDef : PreDefinition) (all : List Name := [preDef.declName]) : TermElabM Unit := do
  addNonRecAux preDef (compile := true) (all := all)

def addNonRec (preDef : PreDefinition) (applyAttrAfterCompilation := true) (all : List Name := [preDef.declName]) : TermElabM Unit := do
  addNonRecAux preDef (compile := false) (applyAttrAfterCompilation := applyAttrAfterCompilation) (all := all)

/--
  Eliminate recursive application annotations containing syntax. These annotations are used by the well-founded recursion module
  to produce better error messages. -/
def eraseRecAppSyntaxExpr (e : Expr) : CoreM Expr := do
  if e.find? hasRecAppSyntax |>.isSome then
    Core.transform e (post := fun e => pure <| TransformStep.done <| if hasRecAppSyntax e then e.mdataExpr! else e)
  else
    return e

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
          modifiers := default }

private def containsRecFn (recFnNames : Array Name) (e : Expr) : Bool :=
  (e.find? fun e => e.isConst && recFnNames.contains e.constName!).isSome

def ensureNoRecFn (recFnNames : Array Name) (e : Expr) : MetaM Unit := do
  if containsRecFn recFnNames e then
    Meta.forEachExpr e fun e => do
      if e.getAppFn.isConst && recFnNames.contains e.getAppFn.constName! then
        throwError "unexpected occurrence of recursive application{indentExpr e}"

/--
Checks that all codomains have the same level, throws an error otherwise.
-/
def checkCodomainsLevel (preDefs : Array PreDefinition) : MetaM Unit := do
  if preDefs.size = 1 then return
  let arities ← preDefs.mapM fun preDef =>
    lambdaTelescope preDef.value fun xs _ => return xs.size
  forallBoundedTelescope preDefs[0]!.type arities[0]!  fun _ type₀ => do
    let u₀ ← getLevel type₀
    for i in [1:preDefs.size] do
      forallBoundedTelescope preDefs[i]!.type arities[i]! fun _ typeᵢ =>
      unless ← isLevelDefEq u₀ (← getLevel typeᵢ) do
        withOptions (fun o => pp.sanitizeNames.set o false) do
          throwError m!"invalid mutual definition, result types must be in the same universe " ++
            m!"level, resulting type " ++
            m!"for `{preDefs[0]!.declName}` is{indentExpr type₀} : {← inferType type₀}\n" ++
            m!"and for `{preDefs[i]!.declName}` is{indentExpr typeᵢ} : {← inferType typeᵢ}"

def shareCommonPreDefs (preDefs : Array PreDefinition) : CoreM (Array PreDefinition) := do
  profileitM Exception "share common exprs" (← getOptions) do
    withTraceNode `Elab.def.maxSharing (fun _ => return m!"share common exprs") do
      let mut es := #[]
      for preDef in preDefs do
        es := es.push preDef.type |>.push preDef.value
      es := ShareCommon.shareCommon' es
      let mut result := #[]
      for h : i in [:preDefs.size] do
        let preDef := preDefs[i]
        result := result.push { preDef with type := es[2*i]!, value := es[2*i+1]! }
      return result

end Lean.Elab
