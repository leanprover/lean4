#lang lean4
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Closure
import Lean.Elab.Command
import Lean.Elab.DeclModifiers
import Lean.Elab.DeclUtil
import Lean.Elab.Inductive

namespace Lean.Elab.Command

open Meta

/- Recall that the `structure command syntax is
```
parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> optional (" := " >> optional structCtor >> structFields)
```
-/

structure StructCtorView :=
  (ref       : Syntax)
  (modifiers : Modifiers)
  (inferMod  : Bool)  -- true if `{}` is used in the constructor declaration
  (name      : Name)
  (declName  : Name)

structure StructFieldView :=
  (ref        : Syntax)
  (modifiers  : Modifiers)
  (binderInfo : BinderInfo)
  (inferMod   : Bool)
  (declName   : Name)
  (name       : Name)
  (binders    : Syntax)
  (type?      : Option Syntax)
  (value?     : Option Syntax)

structure StructView :=
  (ref               : Syntax)
  (modifiers         : Modifiers)
  (scopeLevelNames   : List Name)  -- All `universe` declarations in the current scope
  (allUserLevelNames : List Name)  -- `scopeLevelNames` ++ explicit universe parameters provided in the `structure` command
  (isClass           : Bool)
  (declName          : Name)
  (scopeVars         : Array Expr) -- All `variable` declaration in the current scope
  (params            : Array Expr) -- Explicit parameters provided in the `structure` command
  (parents           : Array Syntax)
  (type              : Syntax)
  (ctor              : StructCtorView)
  (fields            : Array StructFieldView)

inductive StructFieldKind
  | newField | fromParent | subobject

structure StructFieldInfo :=
  (name     : Name)
  (declName : Name) -- Remark: this field value doesn't matter for fromParent fields.
  (fvar     : Expr)
  (kind     : StructFieldKind)
  (inferMod : Bool := false)
  (value?   : Option Expr := none)

instance : Inhabited StructFieldInfo :=
  ⟨{ name := arbitrary _, declName := arbitrary _, fvar := arbitrary _, kind := StructFieldKind.newField }⟩

def StructFieldInfo.isFromParent (info : StructFieldInfo) : Bool :=
  match info.kind with
  | StructFieldKind.fromParent => true
  | _                          => false

def StructFieldInfo.isSubobject (info : StructFieldInfo) : Bool :=
  match info.kind with
  | StructFieldKind.subobject => true
  | _                         => false

/- Auxiliary declaration for `mkProjections` -/
structure ProjectionInfo :=
  (declName : Name)
  (inferMod : Bool)

structure ElabStructResult :=
  (decl            : Declaration)
  (projInfos       : List ProjectionInfo)
  (projInstances   : List Name) -- projections (to parent classes) that must be marked as instances.
  (mctx            : MetavarContext)
  (lctx            : LocalContext)
  (localInsts      : LocalInstances)
  (defaultAuxDecls : Array (Name × Expr × Expr))

private def defaultCtorName := `mk

/-
The structure constructor syntax is
```
parser! try (declModifiers >> ident >> optional inferMod >> " :: ")
```
-/
private def expandCtor (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : CommandElabM StructCtorView :=
  let useDefault :=
    pure { ref := structStx, modifiers := {}, inferMod := false, name := defaultCtorName, declName := structDeclName ++ defaultCtorName }
  if structStx[5].isNone then
    useDefault
  else
    let optCtor := structStx[5][1]
    if optCtor.isNone then
      useDefault
    else
      let ctor := optCtor[0]
      withRef ctor do
      let ctorModifiers ← elabModifiers ctor[0]
      checkValidCtorModifier ctorModifiers
      if ctorModifiers.isPrivate && structModifiers.isPrivate then
        throwError "invalid 'private' constructor in a 'private' structure"
      if ctorModifiers.isProtected && structModifiers.isPrivate then
        throwError "invalid 'protected' constructor in a 'private' structure"
      let inferMod := !ctor[2].isNone
      let name := ctor[1].getId
      let declName := structDeclName ++ name
      let declName ← applyVisibility ctorModifiers.visibility declName
      pure { ref := ctor, name := name, modifiers := ctorModifiers, inferMod := inferMod, declName := declName }

def checkValidFieldModifier (modifiers : Modifiers) : CommandElabM Unit := do
  if modifiers.isNoncomputable then
    throwError "invalid use of 'noncomputable' in field declaration"
  if modifiers.isPartial then
    throwError "invalid use of 'partial' in field declaration"
  if modifiers.isUnsafe then
    throwError "invalid use of 'unsafe' in field declaration"
  if modifiers.attrs.size != 0 then
    throwError "invalid use of attributes in field declaration"
  if modifiers.isPrivate then
    throwError "private fields are not supported yet"

/-
```
def structExplicitBinder := parser! try (declModifiers >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! try (declModifiers >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := parser! try (declModifiers >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
```
-/
private def expandFields (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : CommandElabM (Array StructFieldView) :=
  let fieldBinders := if structStx[5].isNone then #[] else structStx[5][2][0].getArgs
  fieldBinders.foldlM (init := #[]) fun (views : Array StructFieldView) fieldBinder => withRef fieldBinder do
    let k := fieldBinder.getKind
    let binfo ←
      if k == `Lean.Parser.Command.structExplicitBinder then pure BinderInfo.default
      else if k == `Lean.Parser.Command.structImplicitBinder then pure BinderInfo.implicit
      else if k == `Lean.Parser.Command.structInstBinder then pure BinderInfo.instImplicit
      else throwError "unexpected kind of structure field"
    let fieldModifiers ← elabModifiers fieldBinder[0]
    checkValidFieldModifier fieldModifiers
    if fieldModifiers.isPrivate && structModifiers.isPrivate then
      throwError "invalid 'private' field in a 'private' structure"
    if fieldModifiers.isProtected && structModifiers.isPrivate then
      throwError "invalid 'protected' field in a 'private' structure"
    let inferMod         := !fieldBinder[3].isNone
    let (binders, type?) :=
      if binfo == BinderInfo.default then
        expandOptDeclSig fieldBinder[4]
      else
        let (binders, type) := expandDeclSig fieldBinder[4]
        (binders, some type)
    let value? :=
      if binfo != BinderInfo.default then none
      else
        let optBinderDefault := fieldBinder[5]
        if optBinderDefault.isNone then none
        else
          -- binderDefault := parser! " := " >> termParser
          some optBinderDefault[0][1]
    let idents := fieldBinder[2].getArgs
    idents.foldlM (init := views) fun (views : Array StructFieldView) ident => withRef ident do
      let name     := ident.getId
      if isInternalSubobjectFieldName name then
        throwError! "invalid field name '{name}', identifiers starting with '_' are reserved to the system"
      let declName := structDeclName ++ name
      let declName ← applyVisibility fieldModifiers.visibility declName
      pure $ views.push {
        ref        := ident,
        modifiers  := fieldModifiers,
        binderInfo := binfo,
        inferMod   := inferMod,
         declName   := declName,
        name       := name,
        binders    := binders,
        type?      := type?,
        value?     := value?
      }

private def validStructType (type : Expr) : Bool :=
  match type with
  | Expr.sort .. => true
  | _            => false

private def checkParentIsStructure (parent : Expr) : TermElabM Name :=
  match parent.getAppFn with
  | Expr.const c _ _ => do
    unless isStructure (← getEnv) c do
      throwError! "'{c}' is not a structure"
    pure c
  | _ => throwError "expected structure"

private def findFieldInfo? (infos : Array StructFieldInfo) (fieldName : Name) : Option StructFieldInfo :=
  infos.find? fun info => info.name == fieldName

private def containsFieldName (infos : Array StructFieldInfo) (fieldName : Name) : Bool :=
  (findFieldInfo? infos fieldName).isSome

private partial def processSubfields {α} (structDeclName : Name) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
    (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (infos : Array StructFieldInfo) := do
    if h : i < subfieldNames.size then
      let subfieldName := subfieldNames.get ⟨i, h⟩
      if containsFieldName infos subfieldName then
        throwError! "field '{subfieldName}' from '{parentStructName}' has already been declared"
      let val  ← mkProjection parentFVar subfieldName
      let type ← inferType val
      withLetDecl subfieldName type val fun subfieldFVar =>
        /- The following `declName` is only used for creating the `_default` auxiliary declaration name when
           its default value is overwritten in the structure. -/
        let declName := structDeclName ++ subfieldName
        let infos := infos.push { name := subfieldName, declName := declName, fvar := subfieldFVar, kind := StructFieldKind.fromParent }
        loop (i+1) infos
    else
      k infos
  loop 0 infos

private partial def withParents {α} (view : StructView) (i : Nat) (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  if h : i < view.parents.size then
    let parentStx := view.parents.get ⟨i, h⟩
    withRef parentStx do
    let parent ← Term.elabType parentStx
    let parentName ← checkParentIsStructure parent
    let toParentName := mkNameSimple $ "to" ++ parentName.eraseMacroScopes.getString! -- erase macro scopes?
    if containsFieldName infos toParentName then
      throwErrorAt! parentStx "field '{toParentName}' has already been declared"
    let env ← getEnv
    let binfo := if view.isClass && isClass env parentName then BinderInfo.instImplicit else BinderInfo.default
    withLocalDecl toParentName binfo parent fun parentFVar =>
      let infos := infos.push { name := toParentName, declName := view.declName ++ toParentName, fvar := parentFVar, kind := StructFieldKind.subobject }
      let subfieldNames := getStructureFieldsFlattened env parentName
      processSubfields view.declName parentFVar parentName subfieldNames infos fun infos => withParents view (i+1) infos k
  else
    k infos

private def elabFieldTypeValue (view : StructFieldView) (params : Array Expr) : TermElabM (Option Expr × Option Expr) := do
  match view.type? with
  | none         =>
    match view.value? with
    | none        => pure (none, none)
    | some valStx =>
      let value ← Term.elabTerm valStx none
      let value ← mkLambdaFVars params value
      pure (none, value)
  | some typeStx =>
    let type ← Term.elabType typeStx
    match view.value? with
    | none        =>
      let type  ← mkForallFVars params type
      pure (type, none)
    | some valStx =>
      let value ← Term.elabTermEnsuringType valStx type
      let type  ← mkForallFVars params type
      let value ← mkLambdaFVars params value
      pure (type, value)

private partial def withFields {α}
    (views : Array StructFieldView) (i : Nat) (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  if h : i < views.size then
    let view := views.get ⟨i, h⟩
    withRef view.ref $
    match findFieldInfo? infos view.name with
    | none      => do
      let (type?, value?) ← Term.elabBinders view.binders.getArgs fun params => elabFieldTypeValue view params
      match type?, value? with
      | none,      none => throwError "invalid field, type expected"
      | some type, _    =>
        withLocalDecl view.name view.binderInfo type fun fieldFVar =>
          let infos := infos.push { name := view.name, declName := view.declName, fvar := fieldFVar, value? := value?,
                                    kind := StructFieldKind.newField, inferMod := view.inferMod }
          withFields views (i+1) infos k
      | none, some value =>
        let type ← inferType value
        withLocalDecl view.name view.binderInfo type fun fieldFVar =>
          let infos := infos.push { name := view.name, declName := view.declName, fvar := fieldFVar, value? := value,
                                    kind := StructFieldKind.newField, inferMod := view.inferMod }
          withFields views (i+1) infos k
    | some info =>
      match info.kind with
      | StructFieldKind.newField   => throwError! "field '{view.name}' has already been declared"
      | StructFieldKind.fromParent =>
        match view.value? with
        | none       => throwError! "field '{view.name}' has been declared in parent structure"
        | some valStx => do
          if !view.binders.getArgs.isEmpty || view.type?.isSome then
            throwErrorAt! view.type?.get! "omit field '{view.name}' type to set default value"
          let fvarType ← inferType info.fvar
          let value ← Term.elabTermEnsuringType valStx fvarType
          let infos := infos.push { info with value? := value }
          withFields views (i+1) infos k
      | StructFieldKind.subobject => unreachable!
  else
    k infos

private def getResultUniverse (type : Expr) : TermElabM Level := do
  let type ← whnf type
  match type with
  | Expr.sort u _ => pure u
  | _             => throwError "unexpected structure resulting type"

private def collectUsed (params : Array Expr) (fieldInfos : Array StructFieldInfo) : StateRefT CollectFVars.State TermElabM Unit := do
  params.forM fun p => do
    let type ← inferType p
    Term.collectUsedFVars type
  fieldInfos.forM fun info => do
    let fvarType ← inferType info.fvar
    Term.collectUsedFVars fvarType
    match info.value? with
    | none       => pure ()
    | some value => Term.collectUsedFVars value

private def removeUnused (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed params fieldInfos).run {}
  Term.removeUnused scopeVars used

private def withUsed {α} (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) (k : Array Expr → TermElabM α)
    : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused scopeVars params fieldInfos
  withLCtx lctx localInsts $ k vars

private def levelMVarToParamFVar (fvar : Expr) : StateRefT Nat TermElabM Unit := do
  let type ← inferType fvar
  Term.levelMVarToParam' type
  pure ()

private def levelMVarToParamFVars (fvars : Array Expr) : StateRefT Nat TermElabM Unit :=
  fvars.forM levelMVarToParamFVar

private def levelMVarToParamAux (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : StateRefT Nat TermElabM (Array StructFieldInfo) := do
  levelMVarToParamFVars scopeVars
  levelMVarToParamFVars params
  fieldInfos.mapM fun info => do
    levelMVarToParamFVar info.fvar
    match info.value? with
    | none       => pure info
    | some value =>
      let value ← Term.levelMVarToParam' value
      pure { info with value? := value }

private def levelMVarToParam (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM (Array StructFieldInfo) :=
  (levelMVarToParamAux scopeVars params fieldInfos).run' 1

private partial def collectUniversesFromFields (r : Level) (rOffset : Nat) (fieldInfos : Array StructFieldInfo) : TermElabM (Array Level) := do
  fieldInfos.foldlM (init := #[]) fun (us : Array Level) (info : StructFieldInfo) => do
    let type ← inferType info.fvar
    let u ← getLevel type
    let u ← instantiateLevelMVars u
    match accLevelAtCtor u r rOffset us with
    | Except.error msg => throwError msg
    | Except.ok us     => pure us

private def updateResultingUniverse (fieldInfos : Array StructFieldInfo) (type : Expr) : TermElabM Expr := do
  let r ← getResultUniverse type
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  match r with
  | Level.mvar mvarId _ =>
    let us ← collectUniversesFromFields r rOffset fieldInfos
    let rNew := Level.mkNaryMax us.toList
    assignLevelMVar mvarId rNew
    instantiateMVars type
  | _ => throwError "failed to compute resulting universe level of structure, provide universe explicitly"

private def collectLevelParamsInFVar (s : CollectLevelParams.State) (fvar : Expr) : TermElabM CollectLevelParams.State := do
  let type ← inferType fvar
  let type ← instantiateMVars type
  pure $ collectLevelParams s type

private def collectLevelParamsInFVars (fvars : Array Expr) (s : CollectLevelParams.State) : TermElabM CollectLevelParams.State :=
  fvars.foldlM collectLevelParamsInFVar s

private def collectLevelParamsInStructure (structType : Expr) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : TermElabM (Array Name) := do
  let s := collectLevelParams {} structType
  let s ← collectLevelParamsInFVars scopeVars s
  let s ← collectLevelParamsInFVars params s
  let s ← fieldInfos.foldlM (fun (s : CollectLevelParams.State) info => collectLevelParamsInFVar s info.fvar) s
  pure s.params

private def addCtorFields (fieldInfos : Array StructFieldInfo) : Nat → Expr → TermElabM Expr
  | 0,   type => pure type
  | i+1, type => do
    let info := fieldInfos[i]
    let decl ← Term.getFVarLocalDecl! info.fvar
    let type ← instantiateMVars type
    let type := type.abstract #[info.fvar]
    match info.kind with
    | StructFieldKind.fromParent =>
      let val := decl.value
      addCtorFields fieldInfos i (type.instantiate1 val)
    | StructFieldKind.subobject =>
      let n := mkInternalSubobjectFieldName $ decl.userName
      addCtorFields fieldInfos i (mkForall n decl.binderInfo decl.type type)
    | StructFieldKind.newField =>
      addCtorFields fieldInfos i (mkForall decl.userName decl.binderInfo decl.type type)

private def mkCtor (view : StructView) (levelParams : List Name) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM Constructor :=
  withRef view.ref do
  let type := mkAppN (mkConst view.declName (levelParams.map mkLevelParam)) params
  let type ← addCtorFields fieldInfos fieldInfos.size type
  let type ← mkForallFVars params type
  let type ← instantiateMVars type
  let type := type.inferImplicit params.size !view.ctor.inferMod
  pure { name := view.ctor.declName, type := type }

@[extern "lean_mk_projections"]
private constant mkProjections (env : Environment) (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : Except String Environment

private def addProjections (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : TermElabM Unit := do
  let env ← getEnv
  match mkProjections env structName projs isClass with
  | Except.ok env    => setEnv env
  | Except.error msg => throwError msg

private def mkAuxConstructions (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  let hasUnit := env.contains `PUnit
  let hasEq   := env.contains `Eq
  let hasHEq  := env.contains `HEq
  mkRecOn declName
  if hasUnit then mkCasesOn declName
  if hasUnit && hasEq && hasHEq then mkNoConfusion declName

private def addDefaults (lctx : LocalContext) (defaultAuxDecls : Array (Name × Expr × Expr)) : TermElabM Unit := do
  let localInsts ← getLocalInstances
  withLCtx lctx localInsts do
    defaultAuxDecls.forM fun (declName, type, value) => do
      /- The identity function is used as "marker". -/
      let value ← mkId value
      mkAuxDefinition declName type value (zeta := true)
      modifyEnv fun env => setReducibilityStatus env declName ReducibilityStatus.reducible

private def elabStructureView (view : StructView) : TermElabM Unit := do
  let numExplicitParams := view.params.size
  let type ← Term.elabType view.type
  unless validStructType type do throwErrorAt view.type "expected Type"
  withRef view.ref do
  withParents view 0 #[] fun fieldInfos =>
  withFields view.fields 0 fieldInfos fun fieldInfos => do
    Term.synthesizeSyntheticMVarsNoPostponing
    let u ← getResultUniverse type
    let inferLevel ← shouldInferResultUniverse u
    withUsed view.scopeVars view.params fieldInfos $ fun scopeVars => do
      let numParams := scopeVars.size + numExplicitParams
      let fieldInfos ← levelMVarToParam scopeVars view.params fieldInfos
      let type ← if inferLevel then updateResultingUniverse fieldInfos type else pure type
      trace[Elab.structure]! "type: {type}"
      let usedLevelNames ← collectLevelParamsInStructure type scopeVars view.params fieldInfos
      match sortDeclLevelParams view.scopeLevelNames view.allUserLevelNames usedLevelNames with
      | Except.error msg      => throwError msg
      | Except.ok levelParams =>
        let params := scopeVars ++ view.params
        let ctor ← mkCtor view levelParams params fieldInfos
        let type ← mkForallFVars params type
        let type ← instantiateMVars type
        let indType := { name := view.declName, type := type, ctors := [ctor] : InductiveType }
        let decl    := Declaration.inductDecl levelParams params.size [indType] view.modifiers.isUnsafe
        Term.ensureNoUnassignedMVars decl
        addDecl decl
        let projInfos := (fieldInfos.filter fun (info : StructFieldInfo) => !info.isFromParent).toList.map fun (info : StructFieldInfo) =>
          { declName := info.declName, inferMod := info.inferMod : ProjectionInfo }
        addProjections view.declName projInfos view.isClass
        mkAuxConstructions view.declName
        let instParents ← fieldInfos.filterM fun info => do
          let decl ← Term.getFVarLocalDecl! info.fvar
          pure (info.isSubobject && decl.binderInfo.isInstImplicit)
        let projInstances := instParents.toList.map fun info => info.declName
        Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
        projInstances.forM addGlobalInstance
        let lctx ← getLCtx
        let fieldsWithDefault := fieldInfos.filter fun info => info.value?.isSome
        let defaultAuxDecls ← fieldsWithDefault.mapM fun info => do
          let type ← inferType info.fvar
          pure (info.declName ++ `_default, type, info.value?.get!)
        /- The `lctx` and `defaultAuxDecls` are used to create the auxiliary `_default` declarations
           The parameters `params` for these definitions must be marked as implicit, and all others as explicit. -/
        let lctx :=
          params.foldl (init := lctx) fun (lctx : LocalContext) (p : Expr) =>
            lctx.updateBinderInfo p.fvarId! BinderInfo.implicit
        let lctx :=
          fieldInfos.foldl (init := lctx) fun (lctx : LocalContext) (info : StructFieldInfo) =>
            if info.isFromParent then lctx -- `fromParent` fields are elaborated as let-decls, and are zeta-expanded when creating `_default`.
            else lctx.updateBinderInfo info.fvar.fvarId! BinderInfo.default
        addDefaults lctx defaultAuxDecls

/-
parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> structFields

where
def «extends» := parser! " extends " >> sepBy1 termParser ", "
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec

def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := parser! try (declModifiers >> ident >> optional inferMod >> " :: ")

-/
def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  checkValidInductiveModifier modifiers
  let isClass   := stx[0].getKind == `Lean.Parser.Command.classTk
  let modifiers := if isClass then modifiers.addAttribute { name := `class } else modifiers
  let declId    := stx[1]
  let params    := stx[2].getArgs
  let exts      := stx[3]
  let parents   := if exts.isNone then #[] else exts[0][1].getSepArgs
  let optType   := stx[4]
  let type ← if optType.isNone then `(Type _) else pure optType[0][1]
  let scopeLevelNames ← getLevelNames
  let ⟨name, declName, allUserLevelNames⟩ ← expandDeclId declId modifiers
  let ctor ← expandCtor stx modifiers declName
  let fields ← expandFields stx modifiers declName
  runTermElabM declName $ fun scopeVars => Term.withLevelNames allUserLevelNames $ Term.elabBinders params fun params => elabStructureView {
    ref               := stx,
    modifiers         := modifiers,
    scopeLevelNames   := scopeLevelNames,
    allUserLevelNames := allUserLevelNames,
    declName          := declName,
    isClass           := isClass,
    scopeVars         := scopeVars,
    params            := params,
    parents           := parents,
    type              := type,
    ctor              := ctor,
    fields            := fields
  }

builtin_initialize registerTraceClass `Elab.structure

end Lean.Elab.Command
