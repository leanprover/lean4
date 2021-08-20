/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command
import Lean.Meta.Closure
import Lean.Meta.SizeOf
import Lean.Meta.Injective
import Lean.Meta.Structure
import Lean.Meta.AppBuilder
import Lean.Elab.Command
import Lean.Elab.DeclModifiers
import Lean.Elab.DeclUtil
import Lean.Elab.Inductive
import Lean.Elab.DeclarationRange
import Lean.Elab.Binders

namespace Lean.Elab.Command

open Meta

/- Recall that the `structure command syntax is
```
leading_parser (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> optional (" := " >> optional structCtor >> structFields)
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
  | newField | copiedField | fromParent | subobject
  deriving Inhabited, BEq

structure StructFieldInfo where
  name     : Name
  declName : Name -- Remark: for `fromParent` fields, `declName` is only relevant in the generation of auxiliary "default value" functions.
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
leading_parser try (declModifiers >> ident >> optional inferMod >> " :: ")
```
-/
private def expandCtor (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : TermElabM StructCtorView := do
  let useDefault := do
    let declName := structDeclName ++ defaultCtorName
    addAuxDeclarationRanges declName structStx[2] structStx[2]
    pure { ref := structStx, modifiers := {}, inferMod := false, name := defaultCtorName, declName }
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
      pure { ref := ctor, name, modifiers := ctorModifiers, inferMod, declName }

def checkValidFieldModifier (modifiers : Modifiers) : TermElabM Unit := do
  if modifiers.isNoncomputable then
    throwError "invalid use of 'noncomputable' in field declaration"
  if modifiers.isPartial then
    throwError "invalid use of 'partial' in field declaration"
  if modifiers.isUnsafe then
    throwError "invalid use of 'unsafe' in field declaration"
  if modifiers.attrs.size != 0 then
    throwError "invalid use of attributes in field declaration"

/-
```
def structExplicitBinder := leading_parser atomic (declModifiers true >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault) >> ")"
def structImplicitBinder := leading_parser atomic (declModifiers true >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := leading_parser atomic (declModifiers true >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structSimpleBinder   := leading_parser atomic (declModifiers true >> ident) >> optional inferMod >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault)
def structFields         := leading_parser many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
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
    let (binders, type?) ←
      if binfo == BinderInfo.default then
        let (binders, type?) := expandOptDeclSig fieldBinder[4]
        let optBinderTacticDefault := fieldBinder[5]
        if optBinderTacticDefault.isNone then
          pure (binders, type?)
        else if optBinderTacticDefault[0].getKind != ``Parser.Term.binderTactic then
          pure (binders, type?)
        else
          let binderTactic := optBinderTacticDefault[0]
          match type? with
          | none => throwErrorAt binderTactic "invalid field declaration, type must be provided when auto-param (tactic) is used"
          | some type =>
            let tac := binderTactic[2]
            let name ← Term.declareTacticSyntax tac
            -- The tactic should be for binders+type.
            -- It is safe to reset the binders to a "null" node since there is no value to be elaborated
            let type ← `(forall $(binders.getArgs):bracketedBinder*, $type)
            let type ← `(autoParam $type $(mkIdentFrom tac name))
            pure (mkNullNode, some type)
      else
        let (binders, type) := expandDeclSig fieldBinder[4]
        pure (binders, some type)
    let value? ←
      if binfo != BinderInfo.default then
        pure none
      else
        let optBinderTacticDefault := fieldBinder[5]
        -- trace[Elab.struct] ">>> {optBinderTacticDefault}"
        if optBinderTacticDefault.isNone then
          pure none
        else if optBinderTacticDefault[0].getKind == ``Parser.Term.binderTactic then
          pure none
        else
          -- binderDefault := leading_parser " := " >> termParser
          pure (some optBinderTacticDefault[0][1])
    let idents := fieldBinder[2].getArgs
    idents.foldlM (init := views) fun (views : Array StructFieldView) ident => withRef ident do
      let name := ident.getId.eraseMacroScopes
      unless name.isAtomic do
        throwErrorAt ident "invalid field name '{name.eraseMacroScopes}', field names must be atomic"
      let declName := structDeclName ++ name
      let declName ← applyVisibility fieldModifiers.visibility declName
      addDocString' declName fieldModifiers.docString?
      return views.push {
        ref        := ident
        modifiers  := fieldModifiers
        binderInfo := binfo
        inferMod
        declName
        name
        binders
        type?
        value?
      }

private def validStructType (type : Expr) : Bool :=
  match type with
  | Expr.sort .. => true
  | _            => false

private def findFieldInfo? (infos : Array StructFieldInfo) (fieldName : Name) : Option StructFieldInfo :=
  infos.find? fun info => info.name == fieldName

private def containsFieldName (infos : Array StructFieldInfo) (fieldName : Name) : Bool :=
  (findFieldInfo? infos fieldName).isSome

private def updateFieldInfoVal (infos : Array StructFieldInfo) (fieldName : Name) (value : Expr) : Array StructFieldInfo :=
  infos.map fun info =>
    if info.name == fieldName then
      { info with value? := value  }
    else
      info

register_builtin_option structureDiamondWarning : Bool := {
  defValue := false
  descr    := "enable/disable warning messages for structure diamonds"
}

/-- Return `some fieldName` if field `fieldName` of the parent structure `parentStructName` is already in `infos` -/
private def findExistingField? (infos : Array StructFieldInfo) (parentStructName : Name) : CoreM (Option Name) := do
  let fieldNames := getStructureFieldsFlattened (← getEnv) parentStructName
  for fieldName in fieldNames do
    if containsFieldName infos fieldName then
      return some fieldName
  return none

private partial def processSubfields (structDeclName : Name) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
    (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α :=
  go 0 infos
where
  go (i : Nat) (infos : Array StructFieldInfo) := do
    if h : i < subfieldNames.size then
      let subfieldName := subfieldNames.get ⟨i, h⟩
      if containsFieldName infos subfieldName then
        throwError "field '{subfieldName}' from '{parentStructName}' has already been declared"
      let val  ← mkProjection parentFVar subfieldName
      let type ← inferType val
      withLetDecl subfieldName type val fun subfieldFVar =>
        /- The following `declName` is only used for creating the `_default` auxiliary declaration name when
           its default value is overwritten in the structure. If the default value is not overwritten, then its value is irrelevant. -/
        let declName := structDeclName ++ subfieldName
        let infos := infos.push { name := subfieldName, declName, fvar := subfieldFVar, kind := StructFieldKind.fromParent }
        go (i+1) infos
    else
      k infos

/-- Return `some (structName, fieldName, struct)` if `e` is a projection function application -/
private def isProjFnApp? (e : Expr) : MetaM (Option (Name × Name × Expr)) := do
  match e.getAppFn with
  | Expr.const declName .. =>
    match (← getProjectionFnInfo? declName) with
    | some { ctorName := ctorName, numParams := n, .. } =>
      if declName.isStr && e.getAppNumArgs == n+1 then
        let ConstantInfo.ctorInfo ctorVal ← getConstInfo ctorName | unreachable!
        return some (ctorVal.induct, declName.getString!, e.appArg!)
      else
        return none
    | _ => return none
  | _ => return none

/--
  Return `some fieldName`, if `e` is an expression that represents an access to field `fieldName` of the structure `s`.
  The name of the structure type must be `structName`. -/
private partial def isProjectionOf? (e : Expr) (structName : Name) (s : Expr) : MetaM (Option Name) := do
  if let some (baseStructName, fieldName, e) ← isProjFnApp? e then
    if let some path ← visit e #[] then
      if let some path' := getPathToBaseStructure? (← getEnv) baseStructName structName then
        if path'.toArray == path.reverse then
          return some fieldName
  return none
where
  visit (e : Expr) (path : Array Name) : MetaM (Option (Array Name)) := do
    if e == s then return some path
    -- Check whether `e` is a `toParent` field
    if let some (_, _, e') ← isProjFnApp? e then
      visit e' (path.push e.getAppFn.constName!)
    else
      return none

/-- Auxiliary method for `copyNewFieldsFrom`. -/
private def getFieldType (infos : Array StructFieldInfo) (parentStructName : Name) (parentType : Expr) (fieldName : Name) : MetaM Expr := do
  withLocalDeclD (← mkFreshId) parentType fun parent => do
    let proj ← mkProjection parent fieldName
    let projType ← inferType proj
    /- Eliminate occurrences of `parent`. This may happen when structure contains dependent fields. -/
    let visit (e : Expr) : MetaM TransformStep := do
      if let some fieldName ← isProjectionOf? e parentStructName parent then
        -- trace[Meta.debug] "field '{fieldName}' of {e}"
        match (← findFieldInfo? infos fieldName) with
        | some existingFieldInfo => return TransformStep.done existingFieldInfo.fvar
        | none => throwError "unexpected field access {indentExpr e}"
      else
        return TransformStep.done e
    Meta.transform projType (post := visit)

private def toVisibility (fieldInfo : StructureFieldInfo) : CoreM Visibility := do
  if isProtected (← getEnv) fieldInfo.projFn then
    return Visibility.protected
  else if isPrivateName fieldInfo.projFn then
    return Visibility.private
  else
    return Visibility.regular

abbrev FieldMap := NameMap Expr -- Map from field name to expression representing the field

/-- Reduce projetions of the structures in `structNames` -/
private def reduceProjs (e : Expr) (structNames : NameSet) : MetaM Expr :=
  let reduce (e : Expr) : MetaM TransformStep := do
    match (← reduceProjOf? e structNames.contains) with
    | some v => return TransformStep.done v
    | _ => return TransformStep.done e
  transform e (post := reduce)

/--
  Copy the default value for field `fieldName` set at structure `structName`.
  The arguments for the `_default` auxiliary function are provided by `fieldMap`.
  Recall some of the entries in `fieldMap` are constructor applications, and they needed
  to be reduced using `reduceProjs`. Otherwise, the produced default value may be "cyclic".
  That is, we reduce projections of the structures in `expandedStructNames`. Here is
  an example that shows why the reduction is needed.
  ```
  structure A where
    a : Nat

  structure B where
    a : Nat
    b : Nat
    c : Nat

  structure C extends B where
    d : Nat
    c := b + d

  structure D extends A, C

  #print D.c._default
  ```
  Without the reduction, it produces
  ```
  def D.c._default : A → Nat → Nat → Nat → Nat :=
  fun toA b c d => id ({ a := toA.a, b := b, c := c : B }.b + d)
  ```
-/
private partial def copyDefaultValue? (fieldMap : FieldMap) (expandedStructNames : NameSet) (structName : Name) (fieldName : Name) : TermElabM (Option Expr) := do
  match getDefaultFnForField? (← getEnv) structName fieldName with
  | none => return none
  | some defaultFn =>
    let cinfo ← getConstInfo defaultFn
    let us ← mkFreshLevelMVarsFor cinfo
    go? (cinfo.instantiateValueLevelParams us)
where
  failed : TermElabM (Option Expr) := do
    logWarning s!"ignoring default value for field '{fieldName}' defined at '{structName}'"
    return none

  go? (e : Expr) : TermElabM (Option Expr) := do
    match e with
    | Expr.lam n d b c =>
      if c.binderInfo.isExplicit then
        let fieldName := n
        match fieldMap.find? n with
        | none => failed
        | some val =>
          let valType ← inferType val
          if (← isDefEq valType d) then
            go? (b.instantiate1 val)
          else
            failed
      else
        let arg ← mkFreshExprMVar d
        go? (b.instantiate1 arg)
    | e =>
      let r := if e.isAppOfArity ``id 2 then e.appArg! else e
      return some (← reduceProjs (← instantiateMVars e.appArg!) expandedStructNames)

private partial def copyNewFieldsFrom (structDeclName : Name) (infos : Array StructFieldInfo) (parentType : Expr) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  copyFields infos {} parentType fun infos _ _ => k infos
where
  copyFields (infos : Array StructFieldInfo) (expandedStructNames : NameSet) (parentType : Expr) (k : Array StructFieldInfo → FieldMap → NameSet → TermElabM α) : TermElabM α := do
    let parentStructName ← getStructureName parentType
    let fieldNames := getStructureFields (← getEnv) parentStructName
    let rec copy (i : Nat) (infos : Array StructFieldInfo) (fieldMap : FieldMap) (expandedStructNames : NameSet) : TermElabM α := do
      if h : i < fieldNames.size then
        let fieldName := fieldNames.get ⟨i, h⟩
        let fieldType ← getFieldType infos parentStructName parentType fieldName
        match (← findFieldInfo? infos fieldName) with
        | some existingFieldInfo =>
          let existingFieldType ← inferType existingFieldInfo.fvar
          unless (← isDefEq fieldType existingFieldType) do
            throwError "parent field type mismatch, field '{fieldName}' from parent '{parentStructName}' {← mkHasTypeButIsExpectedMsg fieldType existingFieldType}"
          /- Remark: if structure has a default value for this field, it will be set at the `processOveriddenDefaultValues` below. -/
          copy (i+1) infos (fieldMap.insert fieldName existingFieldInfo.fvar) expandedStructNames
        | none =>
          let some fieldInfo ← getFieldInfo? (← getEnv) parentStructName fieldName | unreachable!
          let addNewField : TermElabM α := do
            let value? ← copyDefaultValue? fieldMap expandedStructNames parentStructName fieldName
            withLocalDecl fieldName fieldInfo.binderInfo fieldType fun fieldFVar => do
              let fieldDeclName := structDeclName ++ fieldName
              let fieldDeclName ← applyVisibility (← toVisibility fieldInfo) fieldDeclName
              let infos := infos.push { name := fieldName, declName := fieldDeclName, fvar := fieldFVar, value?,
                                        kind := StructFieldKind.copiedField, inferMod := fieldInfo.inferMod }
              copy (i+1) infos (fieldMap.insert fieldName fieldFVar) expandedStructNames
          if fieldInfo.subobject?.isSome then
            let fieldParentStructName ← getStructureName fieldType
            if (← findExistingField? infos fieldParentStructName).isSome then
              -- See comment at `copyDefaultValue?`
              let expandedStructNames := expandedStructNames.insert fieldParentStructName
              copyFields infos expandedStructNames fieldType fun infos nestedFieldMap expandedStructNames => do
                let fieldVal ← mkCompositeField fieldType nestedFieldMap
                trace[Meta.debug] "composite, {fieldName} := {fieldVal}"
                copy (i+1) infos (fieldMap.insert fieldName fieldVal) expandedStructNames
            else
              addNewField
          else
            addNewField
      else
        let infos ← processOveriddenDefaultValues infos fieldMap expandedStructNames parentStructName
        k infos fieldMap expandedStructNames
    copy 0 infos {} expandedStructNames

  processOveriddenDefaultValues (infos : Array StructFieldInfo) (fieldMap : FieldMap) (expandedStructNames : NameSet) (parentStructName : Name) : TermElabM (Array StructFieldInfo) :=
    infos.mapM fun info => do
      match (← copyDefaultValue? fieldMap expandedStructNames parentStructName info.name) with
      | some value => return { info with value? := value }
      | none       => return info

  mkCompositeField (parentType : Expr) (fieldMap : FieldMap) : TermElabM Expr := do
    let env ← getEnv
    let Expr.const parentStructName us _ ← pure parentType.getAppFn | unreachable!
    let parentCtor := getStructureCtor env parentStructName
    let mut result := mkAppN (mkConst parentCtor.name us) parentType.getAppArgs
    for fieldName in getStructureFields env parentStructName do
      match fieldMap.find? fieldName with
      | some val => result := mkApp result val
      | none => throwError "failed to copied fields from parent structure{indentExpr parentType}" -- TODO improve error message
    return result

private partial def mkToParentName (parentStructName : Name) (p : Name → Bool) : Name := do
  let base := Name.mkSimple $ "to" ++ parentStructName.eraseMacroScopes.getString!
  if p base then
    base
  else
    let rec go (i : Nat) : Name :=
      let curr := base.appendIndexAfter i
      if p curr then curr else go (i+1)
    go 1

private partial def withParents (view : StructView) (k : Array StructFieldInfo → Array Expr → TermElabM α) : TermElabM α := do
  go 0 #[] #[]
where
  go (i : Nat) (infos : Array StructFieldInfo) (copiedParents : Array Expr) : TermElabM α := do
    if h : i < view.parents.size then
      let parentStx := view.parents.get ⟨i, h⟩
      withRef parentStx do
      let parentType ← Term.elabType parentStx
      let parentStructName ← getStructureName parentType
      if let some existingFieldName ← findExistingField? infos parentStructName then
        if structureDiamondWarning.get (← getOptions) then
          logWarning s!"field '{existingFieldName}' from '{parentStructName}' has already been declared"
        copyNewFieldsFrom view.declName infos parentType fun infos => go (i+1) infos (copiedParents.push parentType)
        -- TODO: if `class`, then we need to create a let-decl that stores the local instance for the `parentStructure`
      else
        let env ← getEnv
        let subfieldNames := getStructureFieldsFlattened env parentStructName
        let toParentName := mkToParentName parentStructName fun n => !containsFieldName infos n && !subfieldNames.contains n
        let binfo := if view.isClass && isClass env parentStructName then BinderInfo.instImplicit else BinderInfo.default
        withLocalDecl toParentName binfo parentType fun parentFVar =>
          let infos := infos.push { name := toParentName, declName := view.declName ++ toParentName, fvar := parentFVar, kind := StructFieldKind.subobject }
          processSubfields view.declName parentFVar parentStructName subfieldNames infos fun infos => go (i+1) infos copiedParents
    else
      k infos copiedParents

private def elabFieldTypeValue (view : StructFieldView) : TermElabM (Option Expr × Option Expr) := do
  Term.withAutoBoundImplicit <| Term.elabBinders view.binders.getArgs fun params => do
    match view.type? with
    | none         =>
      match view.value? with
      | none        => return (none, none)
      | some valStx =>
        Term.synthesizeSyntheticMVarsNoPostponing
        let params ← Term.addAutoBoundImplicits params
        let value ← Term.elabTerm valStx none
        let value ← mkLambdaFVars params value
        return (none, value)
    | some typeStx =>
      let type ← Term.elabType typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let params ← Term.addAutoBoundImplicits params
      match view.value? with
      | none        =>
        let type  ← mkForallFVars params type
        return (type, none)
      | some valStx =>
        let value ← Term.elabTermEnsuringType valStx type
        Term.synthesizeSyntheticMVarsNoPostponing
        let type  ← mkForallFVars params type
        let value ← mkLambdaFVars params value
        return (type, value)

private partial def withFields (views : Array StructFieldView) (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  go 0 {} infos
where
  go (i : Nat) (defaultValsOverridden : NameSet) (infos : Array StructFieldInfo) : TermElabM α := do
    if h : i < views.size then
      let view := views.get ⟨i, h⟩
      withRef view.ref do
      match findFieldInfo? infos view.name with
      | none      =>
        let (type?, value?) ← elabFieldTypeValue view
        match type?, value? with
        | none,      none => throwError "invalid field, type expected"
        | some type, _    =>
          withLocalDecl view.name view.binderInfo type fun fieldFVar =>
            let infos := infos.push { name := view.name, declName := view.declName, fvar := fieldFVar, value? := value?,
                                      kind := StructFieldKind.newField, inferMod := view.inferMod }
            go (i+1) defaultValsOverridden infos
        | none, some value =>
          let type ← inferType value
          withLocalDecl view.name view.binderInfo type fun fieldFVar =>
            let infos := infos.push { name := view.name, declName := view.declName, fvar := fieldFVar, value? := value,
                                      kind := StructFieldKind.newField, inferMod := view.inferMod }
            go (i+1) defaultValsOverridden infos
      | some info =>
        let updateDefaultValue (fromParent : Bool) : TermElabM α := do
          match view.value? with
          | none       => throwError "field '{view.name}' has been declared in parent structure"
          | some valStx =>
            if let some type := view.type? then
              throwErrorAt type "omit field '{view.name}' type to set default value"
            else
              if defaultValsOverridden.contains info.name then
                throwError "field '{view.name}' new default value has already been set"
              let defaultValsOverridden := defaultValsOverridden.insert info.name
              let mut valStx := valStx
              if view.binders.getArgs.size > 0 then
                valStx ← `(fun $(view.binders.getArgs)* => $valStx:term)
              let fvarType ← inferType info.fvar
              let value ← Term.elabTermEnsuringType valStx fvarType
              let infos := updateFieldInfoVal infos info.name value
              go (i+1) defaultValsOverridden infos
        match info.kind with
        | StructFieldKind.newField    => throwError "field '{view.name}' has already been declared"
        | StructFieldKind.subobject   => throwError "unexpected subobject field reference" -- improve error message
        | StructFieldKind.copiedField => updateDefaultValue false
        | StructFieldKind.fromParent  => updateDefaultValue true
    else
      k infos

private def getResultUniverse (type : Expr) : TermElabM Level := do
  let type ← whnf type
  match type with
  | Expr.sort u _ => pure u
  | _             => throwError "unexpected structure resulting type"

private def collectUsed (params : Array Expr) (fieldInfos : Array StructFieldInfo) : StateRefT CollectFVars.State MetaM Unit := do
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
  withLCtx lctx localInsts <| k vars

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
  return collectLevelParams s type

private def collectLevelParamsInFVars (fvars : Array Expr) (s : CollectLevelParams.State) : TermElabM CollectLevelParams.State :=
  fvars.foldlM collectLevelParamsInFVar s

private def collectLevelParamsInStructure (structType : Expr) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : TermElabM (Array Name) := do
  let s := collectLevelParams {} structType
  let s ← collectLevelParamsInFVars scopeVars s
  let s ← collectLevelParamsInFVars params s
  let s ← fieldInfos.foldlM (init := s) fun s info => collectLevelParamsInFVar s info.fvar
  return s.params

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
    | _  =>
      addCtorFields fieldInfos i (mkForall decl.userName decl.binderInfo decl.type type)

private def mkCtor (view : StructView) (levelParams : List Name) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM Constructor :=
  withRef view.ref do
  let type := mkAppN (mkConst view.declName (levelParams.map mkLevelParam)) params
  let type ← addCtorFields fieldInfos fieldInfos.size type
  let type ← mkForallFVars params type
  let type ← instantiateMVars type
  let type := type.inferImplicit params.size !view.ctor.inferMod
  -- trace[Meta.debug] "ctor type {type}"
  pure { name := view.ctor.declName, type }

@[extern "lean_mk_projections"]
private constant mkProjections (env : Environment) (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : Except KernelException Environment

private def addProjections (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : TermElabM Unit := do
  let env ← getEnv
  match mkProjections env structName projs isClass with
  | Except.ok env   => setEnv env
  | Except.error ex => throwKernelException ex

private def registerStructure (structName : Name) (infos : Array StructFieldInfo) : TermElabM Unit := do
  let fields ← infos.filterMapM fun info => do
      if info.kind == StructFieldKind.fromParent then
        return none
      else
        return some {
          fieldName  := info.name
          projFn     := info.declName
          inferMod   := info.inferMod
          binderInfo := (← getFVarLocalDecl info.fvar).binderInfo
          subobject? :=
            if info.kind == StructFieldKind.subobject then
              match (← getEnv).find? info.declName with
              | some (ConstantInfo.defnInfo val) =>
                match val.type.getForallBody.getAppFn with
                | Expr.const parentName .. => some parentName
                | _ => panic! "ill-formed structure"
              | _ => panic! "ill-formed environment"
            else
              none
        }
  modifyEnv fun env => Lean.registerStructure env { structName, fields }

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
        throwError "invalid default value for field, it contains metavariables{indentExpr value}"
      /- The identity function is used as "marker". -/
      let value ← mkId value
      discard <| mkAuxDefinition declName type value (zeta := true)
      setReducibleAttribute declName

private partial def mkCoercionToCopiedParent (levelParams : List Name) (params : Array Expr) (view : StructView) (parentType : Expr) : MetaM Unit := do
  let env ← getEnv
  let structName := view.declName
  let sourceFieldNames := getStructureFieldsFlattened env structName
  let structType ← mkAppN (Lean.mkConst structName (levelParams.map mkLevelParam)) params
  let Expr.const parentStructName us _ ← pure parentType.getAppFn | unreachable!
  let binfo := if view.isClass && isClass env parentStructName then BinderInfo.instImplicit else BinderInfo.default
  withLocalDecl `self binfo structType fun source => do
    let declType ← instantiateMVars (← mkForallFVars params (← mkForallFVars #[source] parentType))
    let declType := declType.inferImplicit params.size true
    let rec copyFields (parentType : Expr) : MetaM Expr := do
      let Expr.const parentStructName us _ ← pure parentType.getAppFn | unreachable!
      let parentCtor := getStructureCtor env parentStructName
      let mut result := mkAppN (mkConst parentCtor.name us) parentType.getAppArgs
      for fieldName in getStructureFields env parentStructName do
        if sourceFieldNames.contains fieldName then
          let fieldVal ← mkProjection source fieldName
          result := mkApp result fieldVal
        else
          -- fieldInfo must be a field of `parentStructName`
          let some fieldInfo ← getFieldInfo? env parentStructName fieldName | unreachable!
          if fieldInfo.subobject?.isNone then throwError "failed to build coercion to parent structure"
          let resultType ← whnfD (← inferType result)
          unless resultType.isForall do throwError "failed to build coercion to parent structure, unexpect type{indentExpr resultType}"
          let fieldVal ← copyFields resultType.bindingDomain!
          result := mkApp result fieldVal
      return result
    let declVal ← instantiateMVars (← mkLambdaFVars params (← mkLambdaFVars #[source] (← copyFields parentType)))
    let declName := structName ++ mkToParentName (← getStructureName parentType) fun n => !env.contains (structName ++ n)
    addAndCompile <| Declaration.defnDecl {
      name        := declName
      levelParams := levelParams
      type        := declType
      value       := declVal
      hints       := ReducibilityHints.abbrev
      safety      := if view.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe
    }
    if binfo.isInstImplicit then
      addInstance declName AttributeKind.global (eval_prio default)
    else
      setReducibleAttribute declName

private def elabStructureView (view : StructView) : TermElabM Unit := do
  view.fields.forM fun field => do
    if field.declName == view.ctor.declName then
      throwErrorAt field.ref "invalid field name '{field.name}', it is equal to structure constructor name"
    addAuxDeclarationRanges field.declName field.ref field.ref
  let numExplicitParams := view.params.size
  let type ← Term.elabType view.type
  unless validStructType type do throwErrorAt view.type "expected Type"
  withRef view.ref do
  withParents view fun fieldInfos copiedParents => do
  withFields view.fields fieldInfos fun fieldInfos => do
    Term.synthesizeSyntheticMVarsNoPostponing
    let u ← getResultUniverse type
    let inferLevel ← shouldInferResultUniverse u
    withUsed view.scopeVars view.params fieldInfos fun scopeVars => do
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
        registerStructure view.declName fieldInfos
        mkAuxConstructions view.declName
        let instParents ← fieldInfos.filterM fun info => do
          let decl ← Term.getFVarLocalDecl! info.fvar
          pure (info.isSubobject && decl.binderInfo.isInstImplicit)
        let projInstances := instParents.toList.map fun info => info.declName
        Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
        projInstances.forM fun declName => addInstance declName AttributeKind.global (eval_prio default)
        copiedParents.forM fun parent => mkCoercionToCopiedParent levelParams params view parent
        let lctx ← getLCtx
        let fieldsWithDefault := fieldInfos.filter fun info => info.value?.isSome
        let defaultAuxDecls ← fieldsWithDefault.mapM fun info => do
          let type ← inferType info.fvar
          pure (mkDefaultFnOfProjFn info.declName, type, info.value?.get!)
        /- The `lctx` and `defaultAuxDecls` are used to create the auxiliary "default value" declarations
           The parameters `params` for these definitions must be marked as implicit, and all others as explicit. -/
        let lctx :=
          params.foldl (init := lctx) fun (lctx : LocalContext) (p : Expr) =>
            lctx.setBinderInfo p.fvarId! BinderInfo.implicit
        let lctx :=
          fieldInfos.foldl (init := lctx) fun (lctx : LocalContext) (info : StructFieldInfo) =>
            if info.isFromParent then lctx -- `fromParent` fields are elaborated as let-decls, and are zeta-expanded when creating "default value" auxiliary functions
            else lctx.setBinderInfo info.fvar.fvarId! BinderInfo.default
        addDefaults lctx defaultAuxDecls

/-
leading_parser (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> structFields >> optDeriving

where
def «extends» := leading_parser " extends " >> sepBy1 termParser ", "
def typeSpec := leading_parser " : " >> termParser
def optType : Parser := optional typeSpec

def structFields         := leading_parser many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := leading_parser try (declModifiers >> ident >> optional inferMod >> " :: ")

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
        Term.withLevelNames allUserLevelNames <| Term.withAutoBoundImplicit <|
          Term.elabBinders params fun params => do
            Term.synthesizeSyntheticMVarsNoPostponing
            let params ← Term.addAutoBoundImplicits params
            let allUserLevelNames ← Term.getLevelNames
            elabStructureView {
              ref := stx
              modifiers
              scopeLevelNames
              allUserLevelNames
              declName
              isClass
              scopeVars
              params
              parents
              type
              ctor
              fields
            }
            unless isClass do
              mkSizeOfInstances declName
              mkInjectiveTheorems declName
            return declName
  derivingClassViews.forM fun view => view.applyHandlers #[declName]

builtin_initialize registerTraceClass `Elab.structure

end Lean.Elab.Command
