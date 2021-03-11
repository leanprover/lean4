/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command
import Lean.Meta.Closure
import Lean.Meta.SizeOf
import Lean.Elab.Command
import Lean.Elab.DeclModifiers
import Lean.Elab.DeclUtil
import Lean.Elab.Inductive
import Lean.Elab.DeclarationRange

namespace Lean.Elab.Command

open Meta

/- Recall that the `structure command syntax is
```
parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> optional (" := " >> optional structCtor >> structFields)
```
-/

structure StructCtorView where
  ref       : Syntax
  modifiers : Modifiers
  inferMod  : Bool  -- true if `{}` is used in the constructor declaration
  name      : Name
  declName  : Name

structure StructFieldView where
  ref        : Syntax
  modifiers  : Modifiers
  binderInfo : BinderInfo
  inferMod   : Bool
  declName   : Name
  name       : Name
  binders    : Syntax
  type?      : Option Syntax
  value?     : Option Syntax

structure StructView where
  ref               : Syntax
  modifiers         : Modifiers
  scopeLevelNames   : List Name  -- All `universe` declarations in the current scope
  allUserLevelNames : List Name  -- `scopeLevelNames` ++ explicit universe parameters provided in the `structure` command
  isClass           : Bool
  declName          : Name
  scopeVars         : Array Expr -- All `variable` declaration in the current scope
  params            : Array Expr -- Explicit parameters provided in the `structure` command
  parents           : Array Syntax
  type              : Syntax
  ctor              : StructCtorView
  fields            : Array StructFieldView

inductive StructFieldKind where
  | newField | fromParent | subobject
  deriving Inhabited

structure StructFieldInfo where
  name     : Name
  declName : Name -- Remark: this field value doesn't matter for fromParent fields.
  fvar     : Expr
  kind     : StructFieldKind
  inferMod : Bool := false
  value?   : Option Expr := none
  deriving Inhabited

def StructFieldInfo.isFromParent (info : StructFieldInfo) : Bool :=
  match info.kind with
  | StructFieldKind.fromParent => true
  | _                          => false

def StructFieldInfo.isSubobject (info : StructFieldInfo) : Bool :=
  match info.kind with
  | StructFieldKind.subobject => true
  | _                         => false

/- Auxiliary declaration for `mkProjections` -/
structure ProjectionInfo where
  declName : Name
  inferMod : Bool

structure ElabStructResult where
  decl            : Declaration
  projInfos       : List ProjectionInfo
  projInstances   : List Name -- projections (to parent classes) that must be marked as instances.
  mctx            : MetavarContext
  lctx            : LocalContext
  localInsts      : LocalInstances
  defaultAuxDecls : Array (Name × Expr × Expr)

private def defaultCtorName := `mk

/-
The structure constructor syntax is
```
parser! try (declModifiers >> ident >> optional inferMod >> " :: ")
```
-/
private def expandCtor (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : TermElabM StructCtorView := do
  let useDefault := do
    let declName := structDeclName ++ defaultCtorName
    addAuxDeclarationRanges declName structStx[2] structStx[2]
    pure { ref := structStx, modifiers := {}, inferMod := false, name := defaultCtorName, declName := declName }
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
      addDocString' declName ctorModifiers.docString?
      addAuxDeclarationRanges declName ctor[1] ctor[1]
      pure { ref := ctor, name := name, modifiers := ctorModifiers, inferMod := inferMod, declName := declName }

def checkValidFieldModifier (modifiers : Modifiers) : TermElabM Unit := do
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
def structExplicitBinder := parser! atomic (declModifiers true >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! atomic (declModifiers true >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := parser! atomic (declModifiers true >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structSimpleBinder   := parser! atomic (declModifiers true >> ident) >> optional inferMod >> optDeclSig >> optional Term.binderDefault
def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
```
-/
private def expandFields (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : TermElabM (Array StructFieldView) :=
  let fieldBinders := if structStx[5].isNone then #[] else structStx[5][2][0].getArgs
  fieldBinders.foldlM (init := #[]) fun (views : Array StructFieldView) fieldBinder => withRef fieldBinder do
    let mut fieldBinder := fieldBinder
    if fieldBinder.getKind == ``Parser.Command.structSimpleBinder then
      fieldBinder := Syntax.node ``Parser.Command.structExplicitBinder
        #[ fieldBinder[0], mkAtomFrom fieldBinder "(", mkNullNode #[ fieldBinder[1] ], fieldBinder[2], fieldBinder[3], fieldBinder[4], mkAtomFrom fieldBinder ")" ]
    let k := fieldBinder.getKind
    let binfo ←
      if k == ``Parser.Command.structExplicitBinder then pure BinderInfo.default
      else if k == ``Parser.Command.structImplicitBinder then pure BinderInfo.implicit
      else if k == ``Parser.Command.structInstBinder then pure BinderInfo.instImplicit
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
      addDocString' declName fieldModifiers.docString?
      return views.push {
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

private partial def processSubfields (structDeclName : Name) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
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

private partial def withParents (view : StructView) (i : Nat) (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  if h : i < view.parents.size then
    let parentStx := view.parents.get ⟨i, h⟩
    withRef parentStx do
    let parent ← Term.elabType parentStx
    let parentName ← checkParentIsStructure parent
    let toParentName := Name.mkSimple $ "to" ++ parentName.eraseMacroScopes.getString! -- erase macro scopes?
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

private def elabFieldTypeValue (view : StructFieldView) : TermElabM (Option Expr × Option Expr) := do
  Term.withAutoBoundImplicitLocal <| Term.elabBinders (catchAutoBoundImplicit := true) view.binders.getArgs fun params => do
    match view.type? with
    | none         =>
      match view.value? with
      | none        => return (none, none)
      | some valStx =>
        let params ← Term.addAutoBoundImplicits params
        let value ← Term.elabTerm valStx none
        let value ← mkLambdaFVars params value
        return (none, value)
    | some typeStx =>
      Term.elabTypeWithAutoBoundImplicit typeStx fun type => do
        let params ← Term.addAutoBoundImplicits params
        match view.value? with
        | none        =>
          let type  ← mkForallFVars params type
          return (type, none)
        | some valStx =>
          let value ← Term.elabTermEnsuringType valStx type
          let type  ← mkForallFVars params type
          let value ← mkLambdaFVars params value
          return (type, value)

private partial def withFields
    (views : Array StructFieldView) (i : Nat) (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  if h : i < views.size then
    let view := views.get ⟨i, h⟩
    withRef view.ref $
    match findFieldInfo? infos view.name with
    | none      => do
      let (type?, value?) ← elabFieldTypeValue view
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
          if let some type := view.type? then
            throwErrorAt! type "omit field '{view.name}' type to set default value"
          else
            let mut valStx := valStx
            if view.binders.getArgs.size > 0 then
              valStx ← `(fun $(view.binders.getArgs)* => $valStx:term)
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
  discard <| Term.levelMVarToParam' type

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
    accLevelAtCtor u r rOffset us

private def updateResultingUniverse (fieldInfos : Array StructFieldInfo) (type : Expr) : TermElabM Expr := do
  let r ← getResultUniverse type
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  match r with
  | Level.mvar mvarId _ =>
    let us ← collectUniversesFromFields r rOffset fieldInfos
    let rNew := mkResultUniverse us rOffset
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
private constant mkProjections (env : Environment) (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : Except KernelException Environment

private def addProjections (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : TermElabM Unit := do
  let env ← getEnv
  match mkProjections env structName projs isClass with
  | Except.ok env   => setEnv env
  | Except.error ex => throwKernelException ex

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
      let value ← instantiateMVars value
      if value.hasExprMVar then
        throwError! "invalid default value for field, it contains metavariables{indentExpr value}"
      /- The identity function is used as "marker". -/
      let value ← mkId value
      discard <| mkAuxDefinition declName type value (zeta := true)
      setReducibleAttribute declName

private def elabStructureView (view : StructView) : TermElabM Unit := do
  view.fields.forM fun field => do
    if field.declName == view.ctor.declName then
      throwErrorAt! field.ref "invalid field name '{field.name}', it is equal to structure constructor name"
    addAuxDeclarationRanges field.declName field.ref field.ref
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
      let type ← withRef view.ref do
        if inferLevel then
          updateResultingUniverse fieldInfos type
        else
          checkResultingUniverse (← getResultUniverse type)
          pure type
      trace[Elab.structure] "type: {type}"
      let usedLevelNames ← collectLevelParamsInStructure type scopeVars view.params fieldInfos
      match sortDeclLevelParams view.scopeLevelNames view.allUserLevelNames usedLevelNames with
      | Except.error msg      => withRef view.ref <| throwError msg
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
        projInstances.forM fun declName => addInstance declName AttributeKind.global (evalPrio! default)
        let lctx ← getLCtx
        let fieldsWithDefault := fieldInfos.filter fun info => info.value?.isSome
        let defaultAuxDecls ← fieldsWithDefault.mapM fun info => do
          let type ← inferType info.fvar
          pure (info.declName ++ `_default, type, info.value?.get!)
        /- The `lctx` and `defaultAuxDecls` are used to create the auxiliary `_default` declarations
           The parameters `params` for these definitions must be marked as implicit, and all others as explicit. -/
        let lctx :=
          params.foldl (init := lctx) fun (lctx : LocalContext) (p : Expr) =>
            lctx.setBinderInfo p.fvarId! BinderInfo.implicit
        let lctx :=
          fieldInfos.foldl (init := lctx) fun (lctx : LocalContext) (info : StructFieldInfo) =>
            if info.isFromParent then lctx -- `fromParent` fields are elaborated as let-decls, and are zeta-expanded when creating `_default`.
            else lctx.setBinderInfo info.fvar.fvarId! BinderInfo.default
        addDefaults lctx defaultAuxDecls

/-
parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> structFields >> optDeriving

where
def «extends» := parser! " extends " >> sepBy1 termParser ", "
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec

def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := parser! try (declModifiers >> ident >> optional inferMod >> " :: ")

-/
def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  checkValidInductiveModifier modifiers
  let isClass   := stx[0].getKind == ``Parser.Command.classTk
  let modifiers := if isClass then modifiers.addAttribute { name := `class } else modifiers
  let declId    := stx[1]
  let params    := stx[2].getArgs
  let exts      := stx[3]
  let parents   := if exts.isNone then #[] else exts[0][1].getSepArgs
  let optType   := stx[4]
  let derivingClassViews ← getOptDerivingClasses stx[6]
  let type ← if optType.isNone then `(Sort _) else pure optType[0][1]
  let declName ←
    runTermElabM none fun scopeVars => do
      let scopeLevelNames ← Term.getLevelNames
      let ⟨name, declName, allUserLevelNames⟩ ← Elab.expandDeclId (← getCurrNamespace) scopeLevelNames declId modifiers
      addDeclarationRanges declName stx
      Term.withDeclName declName do
        let ctor ← expandCtor stx modifiers declName
        let fields ← expandFields stx modifiers declName
        Term.withLevelNames allUserLevelNames <| Term.withAutoBoundImplicitLocal <|
          Term.elabBinders params (catchAutoBoundImplicit := true) fun params => do
            let params ← Term.addAutoBoundImplicits params
            let allUserLevelNames ← Term.getLevelNames
            Term.withAutoBoundImplicitLocal (flag := false) do
              elabStructureView {
                ref               := stx
                modifiers         := modifiers
                scopeLevelNames   := scopeLevelNames
                allUserLevelNames := allUserLevelNames
                declName          := declName
                isClass           := isClass
                scopeVars         := scopeVars
                params            := params
                parents           := parents
                type              := type
                ctor              := ctor
                fields            := fields
              }
            unless isClass do
              mkSizeOfInstances declName
            return declName
  derivingClassViews.forM fun view => view.applyHandlers #[declName]

builtin_initialize registerTraceClass `Elab.structure

end Lean.Elab.Command
