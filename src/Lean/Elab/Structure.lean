/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Class
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

register_builtin_option structureDiamondWarning : Bool := {
  defValue := false
  descr    := "if true, enable warnings when a structure has diamond inheritance"
}

register_builtin_option structure.strictResolutionOrder : Bool := {
  defValue := false
  descr := "if true, require a strict resolution order for structures"
}

open Meta
open TSyntax.Compat

/-! Recall that the `structure command syntax is
```
leading_parser (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> optional (" := " >> optional structCtor >> structFields)
```
-/

structure StructCtorView where
  ref       : Syntax
  modifiers : Modifiers
  name      : Name
  declName  : Name
  deriving Inhabited

structure StructFieldView where
  ref        : Syntax
  modifiers  : Modifiers
  binderInfo : BinderInfo
  declName   : Name
  /-- Ref for the field name -/
  nameId     : Syntax
  /-- The name of the field. (Without macro scopes.) -/
  name       : Name
  /-- Same as `name` but includes macro scopes. Used for field elaboration. -/
  rawName    : Name
  binders    : Syntax
  type?      : Option Syntax
  value?     : Option Syntax

structure StructView where
  ref             : Syntax
  declId          : Syntax
  modifiers       : Modifiers
  isClass         : Bool -- struct-only
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Syntax
  type            : Syntax -- modified (inductive has type?)
  parents         : Array Syntax -- struct-only
  ctor            : StructCtorView -- struct-only
  fields          : Array StructFieldView -- struct-only
  derivingClasses : Array DerivingClassView
  deriving Inhabited

structure StructParentInfo where
  ref        : Syntax
  fvar?      : Option Expr
  structName : Name
  subobject  : Bool
  type       : Expr
  deriving Inhabited

inductive StructFieldKind where
  | newField | copiedField | fromParent
  /-- The field is an embedded parent. -/
  | subobject (structName : Name)
  deriving Inhabited, DecidableEq, Repr

structure StructFieldInfo where
  ref      : Syntax
  name     : Name
  /-- Name of projection function.
  Remark: for `fromParent` fields, `declName` is only relevant in the generation of auxiliary "default value" functions. -/
  declName : Name
  fvar     : Expr
  kind     : StructFieldKind
  value?   : Option Expr := none
  deriving Inhabited, Repr

structure ElabStructHeaderResult where
  view             : StructView
  lctx             : LocalContext
  localInsts       : LocalInstances
  levelNames       : List Name
  params           : Array Expr
  type             : Expr
  parents          : Array StructParentInfo
  /-- Field infos from parents. -/
  parentFieldInfos : Array StructFieldInfo
  deriving Inhabited

def StructFieldInfo.isFromParent (info : StructFieldInfo) : Bool :=
  match info.kind with
  | StructFieldKind.fromParent => true
  | _                          => false

def StructFieldInfo.isSubobject (info : StructFieldInfo) : Bool :=
  info.kind matches StructFieldKind.subobject ..

private def defaultCtorName := `mk

/-
The structure constructor syntax is
```
leading_parser try (declModifiers >> ident >> " :: ")
```
-/
private def expandCtor (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : TermElabM StructCtorView := do
  let useDefault := do
    let declName := structDeclName ++ defaultCtorName
    let ref := structStx[1].mkSynthetic
    addDeclarationRangesFromSyntax declName ref
    pure { ref, modifiers := default, name := defaultCtorName, declName }
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
      let name := ctor[1].getId
      let declName := structDeclName ++ name
      let declName ← applyVisibility ctorModifiers.visibility declName
      addDocString' declName ctorModifiers.docString?
      addDeclarationRangesFromSyntax declName ctor[1]
      pure { ref := ctor[1], name, modifiers := ctorModifiers, declName }

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
def structExplicitBinder := leading_parser atomic (declModifiers true >> "(") >> many1 ident >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault) >> ")"
def structImplicitBinder := leading_parser atomic (declModifiers true >> "{") >> many1 ident >> declSig >> "}"
def structInstBinder     := leading_parser atomic (declModifiers true >> "[") >> many1 ident >> declSig >> "]"
def structSimpleBinder   := leading_parser atomic (declModifiers true >> ident) >> optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault)
def structFields         := leading_parser many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
```
-/
private def expandFields (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : TermElabM (Array StructFieldView) := do
  if structStx[5][0].isToken ":=" then
    -- https://github.com/leanprover/lean4/issues/5236
    let cmd := if structStx[0].getKind == ``Parser.Command.classTk then "class" else "structure"
    withRef structStx[0] <| Linter.logLintIf Linter.linter.deprecated structStx[5][0]
      s!"{cmd} ... :=' has been deprecated in favor of '{cmd} ... where'."
  let fieldBinders := if structStx[5].isNone then #[] else structStx[5][2][0].getArgs
  fieldBinders.foldlM (init := #[]) fun (views : Array StructFieldView) fieldBinder => withRef fieldBinder do
    let mut fieldBinder := fieldBinder
    if fieldBinder.getKind == ``Parser.Command.structSimpleBinder then
      fieldBinder := mkNode ``Parser.Command.structExplicitBinder
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
    let (binders, type?, value?) ←
      if binfo == BinderInfo.default then
        let (binders, type?) := expandOptDeclSig fieldBinder[3]
        let optBinderTacticDefault := fieldBinder[4]
        if optBinderTacticDefault.isNone then
          pure (binders, type?, none)
        else if optBinderTacticDefault[0].getKind != ``Parser.Term.binderTactic then
          -- binderDefault := leading_parser " := " >> termParser
          pure (binders, type?, some optBinderTacticDefault[0][1])
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
            pure (mkNullNode, some type.raw, none)
      else
        let (binders, type) := expandDeclSig fieldBinder[3]
        pure (binders, some type, none)
    let idents := fieldBinder[2].getArgs
    idents.foldlM (init := views) fun (views : Array StructFieldView) ident => withRef ident do
      let rawName := ident.getId
      let name    := rawName.eraseMacroScopes
      unless name.isAtomic do
        throwErrorAt ident "invalid field name '{name.eraseMacroScopes}', field names must be atomic"
      let declName := structDeclName ++ name
      let declName ← applyVisibility fieldModifiers.visibility declName
      addDocString' declName fieldModifiers.docString?
      return views.push {
        ref        := ident
        modifiers  := fieldModifiers
        binderInfo := binfo
        declName
        name
        nameId     := ident
        rawName
        binders
        type?
        value?
      }

/-
leading_parser (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >>
  optional (("where" <|> ":=") >> optional structCtor >> structFields) >> optDeriving

where
def «extends» := leading_parser " extends " >> sepBy1 termParser ", "
def typeSpec := leading_parser " : " >> termParser
def optType : Parser := optional typeSpec

def structFields         := leading_parser many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := leading_parser try (declModifiers >> ident >> " :: ")
-/
def structureSyntaxToView (modifiers : Modifiers) (stx : Syntax) : TermElabM StructView := do
  checkValidInductiveModifier modifiers
  let isClass   := stx[0].getKind == ``Parser.Command.classTk
  let modifiers := if isClass then modifiers.addAttr { name := `class } else modifiers
  let declId    := stx[1]
  let ⟨name, declName, levelNames⟩ ← Term.expandDeclId (← getCurrNamespace) (← Term.getLevelNames) declId modifiers
  addDeclarationRangesForBuiltin declName modifiers.stx stx
  let binders   := stx[2]
  let exts      := stx[3]
  let parents   := if exts.isNone then #[] else exts[0][1].getSepArgs
  let optType   := stx[4]
  let derivingClasses ← getOptDerivingClasses stx[6]
  let type      ← if optType.isNone then `(Sort _) else pure optType[0][1]
  let ctor ← expandCtor stx modifiers declName
  let fields ← expandFields stx modifiers declName
  fields.forM fun field => do
    if field.declName == ctor.declName then
      throwErrorAt field.ref "invalid field name '{field.name}', it is equal to structure constructor name"
    addDeclarationRangesFromSyntax field.declName field.ref
  return {
    ref := stx
    declId
    modifiers
    isClass
    shortDeclName := name
    declName
    levelNames
    binders
    type
    parents
    ctor
    fields
    derivingClasses
  }

private def findFieldInfo? (infos : Array StructFieldInfo) (fieldName : Name) : Option StructFieldInfo :=
  infos.find? fun info => info.name == fieldName

private def containsFieldName (infos : Array StructFieldInfo) (fieldName : Name) : Bool :=
  (findFieldInfo? infos fieldName).isSome

private def replaceFieldInfo (infos : Array StructFieldInfo) (info : StructFieldInfo) : Array StructFieldInfo :=
  infos.map fun info' =>
    if info'.name == info.name then
      info
    else
      info'

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
      let subfieldName := subfieldNames[i]
      if containsFieldName infos subfieldName then
        throwError "field '{subfieldName}' from '{.ofConstName parentStructName}' has already been declared"
      let val  ← mkProjection parentFVar subfieldName
      let type ← inferType val
      withLetDecl subfieldName type val fun subfieldFVar => do
        /- The following `declName` is only used for creating the `_default` auxiliary declaration name when
           its default value is overwritten in the structure. If the default value is not overwritten, then its value is irrelevant. -/
        let declName := structDeclName ++ subfieldName
        let infos := infos.push { ref := (← getRef), name := subfieldName, declName, fvar := subfieldFVar, kind := StructFieldKind.fromParent }
        go (i+1) infos
    else
      k infos

/-- Given `obj.foo.bar.baz`, return `obj`. -/
private partial def getNestedProjectionArg (e : Expr) : MetaM Expr := do
  if let Expr.const subProjName .. := e.getAppFn then
    if let some { numParams, .. } ← getProjectionFnInfo? subProjName then
      if e.getAppNumArgs == numParams + 1 then
        return ← getNestedProjectionArg e.appArg!
  return e

/--
  Get field type of `fieldName` in `parentType`, but replace references
  to other fields of that structure by existing field fvars.
  Auxiliary method for `copyNewFieldsFrom`.

-/
private def getFieldType (infos : Array StructFieldInfo) (parentType : Expr) (fieldName : Name) : MetaM Expr := do
  withLocalDeclD (← mkFreshId) parentType fun parent => do
    let proj ← mkProjection parent fieldName
    let projType ← inferType proj
    /- Eliminate occurrences of `parent.field`. This happens when the structure contains dependent fields.
    If the copied parent extended another structure via a subobject,
    then the occurrence can also look like `parent.toGrandparent.field`
    (where `toGrandparent` is not a field of the current structure). -/
    let visit (e : Expr) : MetaM TransformStep := do
      if let Expr.const subProjName .. := e.getAppFn then
        if let some { numParams, .. } ← getProjectionFnInfo? subProjName then
          let Name.str _ subFieldName .. := subProjName
            | throwError "invalid projection name {subProjName}"
          let args := e.getAppArgs
          if let some major := args.get? numParams then
            if (← getNestedProjectionArg major) == parent then
              if let some existingFieldInfo := findFieldInfo? infos (.mkSimple subFieldName) then
                return TransformStep.done <| mkAppN existingFieldInfo.fvar args[numParams+1:args.size]
      return TransformStep.done e
    let projType ← Meta.transform projType (post := visit)
    if projType.containsFVar parent.fvarId! then
      throwError "unsupported dependent field in {fieldName} : {projType}"
    if let some info := getFieldInfo? (← getEnv) (← getStructureName parentType) fieldName then
      if let some autoParamExpr := info.autoParam? then
        return (← mkAppM ``autoParam #[projType, autoParamExpr])
    return projType

private def toVisibility (fieldInfo : StructureFieldInfo) : CoreM Visibility := do
  if isProtected (← getEnv) fieldInfo.projFn then
    return Visibility.protected
  else if isPrivateName fieldInfo.projFn then
    return Visibility.private
  else
    return Visibility.regular

abbrev FieldMap := NameMap Expr -- Map from field name to expression representing the field

/-- Reduce projections of the structures in `structNames` -/
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
    go? (← instantiateValueLevelParams cinfo us)
where
  failed : TermElabM (Option Expr) := do
    logWarning m!"ignoring default value for field '{fieldName}' defined at '{.ofConstName structName}'"
    return none

  go? (e : Expr) : TermElabM (Option Expr) := do
    match e with
    | Expr.lam n d b c =>
      if c.isExplicit then
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
      return some (← reduceProjs (← instantiateMVars r) expandedStructNames)

private partial def copyNewFieldsFrom (structDeclName : Name) (infos : Array StructFieldInfo) (parentType : Expr) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  copyFields infos {} parentType fun infos _ _ => k infos
where
  copyFields (infos : Array StructFieldInfo) (expandedStructNames : NameSet) (parentType : Expr) (k : Array StructFieldInfo → FieldMap → NameSet → TermElabM α) : TermElabM α := do
    let parentStructName ← getStructureName parentType
    let fieldNames := getStructureFields (← getEnv) parentStructName
    let rec copy (i : Nat) (infos : Array StructFieldInfo) (fieldMap : FieldMap) (expandedStructNames : NameSet) : TermElabM α := do
      if h : i < fieldNames.size then
        let fieldName := fieldNames[i]
        let fieldType ← getFieldType infos parentType fieldName
        match findFieldInfo? infos fieldName with
        | some existingFieldInfo =>
          let existingFieldType ← inferType existingFieldInfo.fvar
          unless (← isDefEq fieldType existingFieldType) do
            throwError "parent field type mismatch, field '{fieldName}' from parent '{.ofConstName parentStructName}' {← mkHasTypeButIsExpectedMsg fieldType existingFieldType}"
          /- Remark: if structure has a default value for this field, it will be set at the `processOveriddenDefaultValues` below. -/
          copy (i+1) infos (fieldMap.insert fieldName existingFieldInfo.fvar) expandedStructNames
        | none =>
          let some fieldInfo := getFieldInfo? (← getEnv) parentStructName fieldName | unreachable!
          let addNewField : TermElabM α := do
            withLocalDecl fieldName fieldInfo.binderInfo fieldType fun fieldFVar => do
              let fieldMap := fieldMap.insert fieldName fieldFVar
              let value? ← copyDefaultValue? fieldMap expandedStructNames parentStructName fieldName
              let fieldDeclName := structDeclName ++ fieldName
              let fieldDeclName ← applyVisibility (← toVisibility fieldInfo) fieldDeclName
              addDocString' fieldDeclName (← findDocString? (← getEnv) fieldInfo.projFn)
              let infos := infos.push { ref := (← getRef)
                                        name := fieldName, declName := fieldDeclName, fvar := fieldFVar, value?,
                                        kind := StructFieldKind.copiedField }
              copy (i+1) infos fieldMap expandedStructNames
          if let some parentParentStructName := fieldInfo.subobject? then
            let fieldParentStructName ← getStructureName fieldType
            if (← findExistingField? infos fieldParentStructName).isSome then
              -- See comment at `copyDefaultValue?`
              let expandedStructNames := expandedStructNames.insert fieldParentStructName
              copyFields infos expandedStructNames fieldType fun infos nestedFieldMap expandedStructNames => do
                let fieldVal ← mkCompositeField fieldType nestedFieldMap
                copy (i+1) infos (fieldMap.insert fieldName fieldVal) expandedStructNames
            else
              let subfieldNames := getStructureFieldsFlattened (← getEnv) fieldParentStructName
              let fieldName := fieldInfo.fieldName
              withLocalDecl fieldName fieldInfo.binderInfo fieldType fun parentFVar => do
                let infos := infos.push { ref := (← getRef)
                                          name := fieldName, declName := structDeclName ++ fieldName, fvar := parentFVar,
                                          kind := StructFieldKind.subobject parentParentStructName }
                processSubfields structDeclName parentFVar fieldParentStructName subfieldNames infos fun infos =>
                  copy (i+1) infos (fieldMap.insert fieldName parentFVar) expandedStructNames
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
    let Expr.const parentStructName us ← pure parentType.getAppFn | unreachable!
    let parentCtor := getStructureCtor env parentStructName
    let mut result := mkAppN (mkConst parentCtor.name us) parentType.getAppArgs
    for fieldName in getStructureFields env parentStructName do
      match fieldMap.find? fieldName with
      | some val => result := mkApp result val
      | none => throwError "failed to copy fields from parent structure{indentExpr parentType}" -- TODO improve error message
    return result

private partial def mkToParentName (parentStructName : Name) (p : Name → Bool) : Name := Id.run do
  let base := Name.mkSimple $ "to" ++ parentStructName.eraseMacroScopes.getString!
  if p base then
    base
  else
    let rec go (i : Nat) : Name :=
      let curr := base.appendIndexAfter i
      if p curr then curr else go (i+1)
    go 1

private partial def elabParents (view : StructView)
    (k : Array StructFieldInfo → Array StructParentInfo → TermElabM α) : TermElabM α := do
  go 0 #[] #[]
where
  go (i : Nat) (infos : Array StructFieldInfo) (parents : Array StructParentInfo) : TermElabM α := do
    if h : i < view.parents.size then
      let parent := view.parents[i]
      withRef parent do
      let type ← Term.elabType parent
      let parentType ← whnf type
      let parentStructName ← getStructureName parentType
      if parents.any (fun info => info.structName == parentStructName) then
        logWarningAt parent m!"duplicate parent structure '{.ofConstName parentStructName}', skipping"
        go (i + 1) infos parents
      else if let some existingFieldName ← findExistingField? infos parentStructName then
        if structureDiamondWarning.get (← getOptions) then
          logWarning m!"field '{existingFieldName}' from '{.ofConstName parentStructName}' has already been declared"
        let parents := parents.push { ref := parent, fvar? := none, subobject := false, structName := parentStructName, type := parentType }
        copyNewFieldsFrom view.declName infos parentType fun infos => go (i+1) infos parents
        -- TODO: if `class`, then we need to create a let-decl that stores the local instance for the `parentStructure`
      else
        let env ← getEnv
        let subfieldNames := getStructureFieldsFlattened env parentStructName
        let toParentName := mkToParentName parentStructName fun n => !containsFieldName infos n && !subfieldNames.contains n
        let binfo := if view.isClass && isClass env parentStructName then BinderInfo.instImplicit else BinderInfo.default
        withLocalDecl toParentName binfo parentType fun parentFVar =>
          let infos := infos.push { ref := parent,
                                    name := toParentName, declName := view.declName ++ toParentName, fvar := parentFVar,
                                    kind := StructFieldKind.subobject parentStructName }
          let parents := parents.push { ref := parent, fvar? := parentFVar, subobject := true, structName := parentStructName, type := parentType }
          processSubfields view.declName parentFVar parentStructName subfieldNames infos fun infos => go (i+1) infos parents
    else
      k infos parents

private def elabFieldTypeValue (view : StructFieldView) : TermElabM (Option Expr × Option Expr) :=
  Term.withAutoBoundImplicit <| Term.withAutoBoundImplicitForbiddenPred (fun n => view.name == n) <| Term.elabBinders view.binders.getArgs fun params => do
    match view.type? with
    | none         =>
      match view.value? with
      | none        => return (none, none)
      | some valStx =>
        Term.synthesizeSyntheticMVarsNoPostponing
        -- TODO: add forbidden predicate using `shortDeclName` from `view`
        let params ← Term.addAutoBoundImplicits params
        let value ← Term.withoutAutoBoundImplicit <| Term.elabTerm valStx none
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
        let value ← Term.withoutAutoBoundImplicit <| Term.elabTermEnsuringType valStx type
        Term.synthesizeSyntheticMVarsNoPostponing
        let type  ← mkForallFVars params type
        let value ← mkLambdaFVars params value
        return (type, value)

private partial def withFields (views : Array StructFieldView) (infos : Array StructFieldInfo) (k : Array StructFieldInfo → TermElabM α) : TermElabM α := do
  go 0 {} infos
where
  go (i : Nat) (defaultValsOverridden : NameSet) (infos : Array StructFieldInfo) : TermElabM α := do
    if h : i < views.size then
      let view := views[i]
      withRef view.ref do
      match findFieldInfo? infos view.name with
      | none      =>
        let (type?, value?) ← elabFieldTypeValue view
        match type?, value? with
        | none,      none => throwError "invalid field, type expected"
        | some type, _    =>
          withLocalDecl view.rawName view.binderInfo type fun fieldFVar =>
            let infos := infos.push { ref := view.nameId
                                      name := view.name, declName := view.declName, fvar := fieldFVar, value? := value?,
                                      kind := StructFieldKind.newField }
            go (i+1) defaultValsOverridden infos
        | none, some value =>
          let type ← inferType value
          withLocalDecl view.rawName view.binderInfo type fun fieldFVar =>
            let infos := infos.push { ref := view.nameId
                                      name := view.name, declName := view.declName, fvar := fieldFVar, value? := value,
                                      kind := StructFieldKind.newField }
            go (i+1) defaultValsOverridden infos
      | some info =>
        let updateDefaultValue : TermElabM α := do
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
              pushInfoLeaf <| .ofFieldRedeclInfo { stx := view.ref }
              let infos := replaceFieldInfo infos { info with ref := view.nameId, value? := value }
              go (i+1) defaultValsOverridden infos
        match info.kind with
        | StructFieldKind.newField    => throwError "field '{view.name}' has already been declared"
        | StructFieldKind.subobject n => throwError "unexpected reference to subobject field '{n}'" -- improve error message
        | StructFieldKind.copiedField => updateDefaultValue
        | StructFieldKind.fromParent  => updateDefaultValue
    else
      k infos

private def getResultUniverse (type : Expr) : TermElabM Level := do
  let type ← whnf type
  match type with
  | Expr.sort u => pure u
  | _           => throwError "unexpected structure resulting type"

private def collectUsed (params : Array Expr) (fieldInfos : Array StructFieldInfo) : StateRefT CollectFVars.State MetaM Unit := do
  params.forM fun p => do
    let type ← inferType p
    type.collectFVars
  fieldInfos.forM fun info => do
    let fvarType ← inferType info.fvar
    fvarType.collectFVars
    match info.value? with
    | none       => pure ()
    | some value => value.collectFVars

private def removeUnused (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed params fieldInfos).run {}
  Meta.removeUnused scopeVars used

private def withUsed {α} (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) (k : Array Expr → TermElabM α)
    : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused scopeVars params fieldInfos
  withLCtx lctx localInsts <| k vars

private def levelMVarToParam (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) (univToInfer? : Option LMVarId) : TermElabM (Array StructFieldInfo) := do
  levelMVarToParamFVars scopeVars
  levelMVarToParamFVars params
  fieldInfos.mapM fun info => do
    levelMVarToParamFVar info.fvar
    match info.value? with
    | none       => pure info
    | some value =>
      let value ← levelMVarToParam' value
      pure { info with value? := value }
where
  levelMVarToParam' (type : Expr) : TermElabM Expr := do
    Term.levelMVarToParam type (except := fun mvarId => univToInfer? == some mvarId)

  levelMVarToParamFVars (fvars : Array Expr) : TermElabM Unit :=
    fvars.forM levelMVarToParamFVar

  levelMVarToParamFVar (fvar : Expr) : TermElabM Unit := do
    let type ← inferType fvar
    discard <| levelMVarToParam' type


private partial def collectUniversesFromFields (r : Level) (rOffset : Nat) (fieldInfos : Array StructFieldInfo) : TermElabM (Array Level) := do
  let (_, us) ← go |>.run #[]
  return us
where
  go : StateRefT (Array Level) TermElabM Unit :=
    for info in fieldInfos do
      let type ← inferType info.fvar
      let u ← getLevel type
      let u ← instantiateLevelMVars u
      match (← modifyGet fun s => accLevel u r rOffset |>.run |>.run s) with
      | some _ => pure ()
      | none =>
        let typeType ← inferType type
        let mut msg := m!"failed to compute resulting universe level of structure, field '{info.declName}' has type{indentD m!"{type} : {typeType}"}\nstructure resulting type{indentExpr (mkSort (r.addOffset rOffset))}"
        if r.isMVar then
          msg := msg ++ "\nrecall that Lean only infers the resulting universe level automatically when there is a unique solution for the universe level constraints, consider explicitly providing the structure resulting universe level"
        throwError msg

/--
Decides whether the structure should be `Prop`-valued when the universe is not given
and when the universe inference algorithm `collectUniversesFromFields` determines
that the inductive type could naturally be `Prop`-valued.

See `Lean.Elab.Command.isPropCandidate` for an explanation.
Specialized to structures, the heuristic is that we prefer a `Prop` instead of a `Type` structure
when it could be a syntactic subsingleton.
Exception: no-field structures are `Type` since they are likely stubbed-out declarations.
-/
private def isPropCandidate (fieldInfos : Array StructFieldInfo) : Bool :=
  !fieldInfos.isEmpty

private def updateResultingUniverse (fieldInfos : Array StructFieldInfo) (type : Expr) : TermElabM Expr := do
  let r ← getResultUniverse type
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  unless r.isMVar do
    throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly: {r}"
  let us ← collectUniversesFromFields r rOffset fieldInfos
  trace[Elab.structure] "updateResultingUniverse us: {us}, r: {r}, rOffset: {rOffset}"
  let rNew := mkResultUniverse us rOffset (isPropCandidate fieldInfos)
  assignLevelMVar r.mvarId! rNew
  instantiateMVars type

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
    let info := fieldInfos[i]!
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
  let type := type.inferImplicit params.size true
  pure { name := view.ctor.declName, type }

@[extern "lean_mk_projections"]
private opaque mkProjections (env : Environment) (structName : Name) (projs : List Name) (isClass : Bool) : Except KernelException Environment

private def addProjections (r : ElabStructHeaderResult) (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
  if r.type.isProp then
    if let some fieldInfo ← fieldInfos.findM? (not <$> Meta.isProof ·.fvar) then
      throwErrorAt fieldInfo.ref m!"failed to generate projections for 'Prop' structure, field '{format fieldInfo.name}' is not a proof"
  let projNames := fieldInfos |>.filter (!·.isFromParent) |>.map (·.declName)
  let env ← getEnv
  let env ← ofExceptKernelException (mkProjections env r.view.declName projNames.toList r.view.isClass)
  setEnv env

private def registerStructure (structName : Name) (infos : Array StructFieldInfo) : TermElabM Unit := do
  let fields ← infos.filterMapM fun info => do
      if info.kind == StructFieldKind.fromParent then
        return none
      else
        return some {
          fieldName  := info.name
          projFn     := info.declName
          binderInfo := (← getFVarLocalDecl info.fvar).binderInfo
          autoParam? := (← inferType info.fvar).getAutoParamTactic?
          subobject? := if let .subobject parentName := info.kind then parentName else none
        }
  modifyEnv fun env => Lean.registerStructure env { structName, fields }

private def mkAuxConstructions (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  mkRecOn declName
  if hasUnit then mkCasesOn declName
  if hasUnit && hasEq && hasHEq then mkNoConfusion declName
  let ival ← getConstInfoInduct declName
  if ival.isRec then
    if hasUnit && hasProd then mkBelow declName
    if hasUnit && hasProd then mkIBelow declName
    if hasUnit && hasProd then mkBRecOn declName
    if hasUnit && hasProd then mkBInductionOn declName

private def addDefaults (lctx : LocalContext) (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
  withLCtx lctx (← getLocalInstances) do
    fieldInfos.forM fun fieldInfo => do
      if let some value := fieldInfo.value? then
        let declName := mkDefaultFnOfProjFn fieldInfo.declName
        let type ← inferType fieldInfo.fvar
        let value ← instantiateMVars value
        if value.hasExprMVar then
          discard <| Term.logUnassignedUsingErrorInfos (← getMVars value)
          throwErrorAt fieldInfo.ref "invalid default value for field '{format fieldInfo.name}', it contains metavariables{indentExpr value}"
        /- The identity function is used as "marker". -/
        let value ← mkId value
        -- No need to compile the definition, since it is only used during elaboration.
        discard <| mkAuxDefinition declName type value (zetaDelta := true) (compile := false)
        setReducibleAttribute declName

/--
Given `type` of the form `forall ... (source : A), B`, return `forall ... [source : A], B`.
-/
private def setSourceInstImplicit (type : Expr) : Expr :=
  match type with
  | .forallE _ d b _ =>
    if b.isForall then
      type.updateForallE! d (setSourceInstImplicit b)
    else
      type.updateForall! .instImplicit d b
  | _ => unreachable!

/--
Creates a projection function to a non-subobject parent.
-/
private partial def mkCoercionToCopiedParent (levelParams : List Name) (params : Array Expr) (view : StructView) (parentStructName : Name) (parentType : Expr) : MetaM StructureParentInfo := do
  let isProp ← Meta.isProp parentType
  let env ← getEnv
  let structName := view.declName
  let sourceFieldNames := getStructureFieldsFlattened env structName
  let structType := mkAppN (Lean.mkConst structName (levelParams.map mkLevelParam)) params
  let binfo := if view.isClass && isClass env parentStructName then BinderInfo.instImplicit else BinderInfo.default
  withLocalDeclD `self structType fun source => do
    let mut declType ← instantiateMVars (← mkForallFVars params (← mkForallFVars #[source] parentType))
    if view.isClass && isClass env parentStructName then
      declType := setSourceInstImplicit declType
    declType := declType.inferImplicit params.size true
    let rec copyFields (parentType : Expr) : MetaM Expr := do
      let Expr.const parentStructName us ← pure parentType.getAppFn | unreachable!
      let parentCtor := getStructureCtor env parentStructName
      let mut result := mkAppN (mkConst parentCtor.name us) parentType.getAppArgs
      for fieldName in getStructureFields env parentStructName do
        if sourceFieldNames.contains fieldName then
          let fieldVal ← mkProjection source fieldName
          result := mkApp result fieldVal
        else
          -- fieldInfo must be a field of `parentStructName`
          let some fieldInfo := getFieldInfo? env parentStructName fieldName | unreachable!
          if fieldInfo.subobject?.isNone then throwError "failed to build coercion to parent structure"
          let resultType ← whnfD (← inferType result)
          unless resultType.isForall do throwError "failed to build coercion to parent structure, unexpected type{indentExpr resultType}"
          let fieldVal ← copyFields resultType.bindingDomain!
          result := mkApp result fieldVal
      return result
    let declVal ← instantiateMVars (← mkLambdaFVars params (← mkLambdaFVars #[source] (← copyFields parentType)))
    let declName := structName ++ mkToParentName (← getStructureName parentType) fun n => !env.contains (structName ++ n)
    -- Logic from `mk_projections`: prop-valued projections are theorems (or at least opaque)
    let cval : ConstantVal := { name := declName, levelParams, type := declType }
    if isProp then
      addDecl <|
        if view.modifiers.isUnsafe then
          -- Theorems cannot be unsafe.
          Declaration.opaqueDecl { cval with value := declVal, isUnsafe := true }
        else
          Declaration.thmDecl { cval with value := declVal }
    else
      addAndCompile <| Declaration.defnDecl { cval with
        value       := declVal
        hints       := ReducibilityHints.abbrev
        safety      := if view.modifiers.isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe
      }
    -- Logic from `mk_projections`: non-instance-implicits that aren't props become reducible.
    -- (Instances will get instance reducibility in `Lean.Elab.Command.addParentInstances`.)
    if !binfo.isInstImplicit && !(← Meta.isProp parentType) then
      setReducibleAttribute declName
    return { structName := parentStructName, subobject := false, projFn := declName }

private def elabStructHeader (view : StructView) : TermElabM ElabStructHeaderResult :=
  Term.withAutoBoundImplicitForbiddenPred (fun n => view.shortDeclName == n) do
  Term.withAutoBoundImplicit do
  Term.elabBinders view.binders.getArgs fun params => do
  elabParents view fun parentFieldInfos parents => do
    let type ← Term.elabType view.type
    Term.synthesizeSyntheticMVarsNoPostponing
    let u ← mkFreshLevelMVar
    unless ← isDefEq type (mkSort u) do
      throwErrorAt view.type "invalid structure type, expecting 'Type _' or 'Prop'"
    let type ← instantiateMVars (← whnf type)
    Term.addAutoBoundImplicits' params type fun params type => do
      let levelNames ← Term.getLevelNames
      trace[Elab.structure] "header params: {params}, type: {type}, levelNames: {levelNames}"
      return { lctx := (← getLCtx), localInsts := (← getLocalInstances), levelNames, params, type, view, parents, parentFieldInfos }

private def mkTypeFor (r : ElabStructHeaderResult) : TermElabM Expr := do
  withLCtx r.lctx r.localInsts do
    mkForallFVars r.params r.type

/--
Create a local declaration for the structure and execute `x params indFVar`, where `params` are the structure's type parameters and
`indFVar` is the new local declaration.
-/
private partial def withStructureLocalDecl (r : ElabStructHeaderResult) (x : Array Expr → Expr → TermElabM α) : TermElabM α := do
  let declName := r.view.declName
  let shortDeclName := r.view.shortDeclName
  let type ← mkTypeFor r
  let params := r.params
  withLCtx r.lctx r.localInsts <| withRef r.view.ref do
    Term.withAuxDecl shortDeclName type declName fun indFVar =>
      x params indFVar

/--
Remark: `numVars <= numParams`.
`numVars` is the number of context `variables` used in the declaration,
and `numParams - numVars` is the number of parameters provided as binders in the declaration.
-/
private def mkInductiveType (view : StructView) (indFVar : Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (type : Expr) (ctor : Constructor) : TermElabM InductiveType := do
  let levelParams := levelNames.map mkLevelParam
  let const := mkConst view.declName levelParams
  let ctorType ← forallBoundedTelescope ctor.type numParams fun params type => do
    let type := type.replace fun e =>
      if e == indFVar then
        mkAppN const (params.extract 0 numVars)
      else
        none
    instantiateMVars (← mkForallFVars params type)
  return { name := view.declName, type := ← instantiateMVars type, ctors := [{ ctor with type := ← instantiateMVars ctorType }] }

/--
Precomputes the structure's resolution order.
Option `structure.strictResolutionOrder` controls whether to create a warning if the C3 algorithm failed.
-/
private def checkResolutionOrder (structName : Name) : TermElabM Unit := do
  let resolutionOrderResult ← computeStructureResolutionOrder structName (relaxed := !structure.strictResolutionOrder.get (← getOptions))
  trace[Elab.structure.resolutionOrder] "computed resolution order: {resolutionOrderResult.resolutionOrder}"
  unless resolutionOrderResult.conflicts.isEmpty do
    let mut defects : List MessageData := []
    for conflict in resolutionOrderResult.conflicts do
      let parentKind direct := if direct then "parent" else "indirect parent"
      let conflicts := conflict.conflicts.map fun (isDirect, name) =>
        m!"{parentKind isDirect} '{MessageData.ofConstName name}'"
      defects := m!"- {parentKind conflict.isDirectParent} '{MessageData.ofConstName conflict.badParent}' \
        must come after {MessageData.andList conflicts.toList}" :: defects
    logWarning m!"failed to compute strict resolution order:\n{MessageData.joinSep defects.reverse "\n"}"

/--
Adds each direct parent projection to a class as an instance, so long as the parent isn't an ancestor of the others.
-/
private def addParentInstances (parents : Array StructureParentInfo) : MetaM Unit := do
  let env ← getEnv
  let instParents := parents.filter fun parent => isClass env parent.structName
  -- A parent is an ancestor of the others if it appears with index ≥ 1 in one of the resolution orders.
  let resOrders : Array (Array Name) ← instParents.mapM fun parent => getStructureResolutionOrder parent.structName
  let instParents := instParents.filter fun parent =>
    !resOrders.any (fun resOrder => resOrder[1:].any (· == parent.structName))
  for instParent in instParents do
    addInstance instParent.projFn AttributeKind.global (eval_prio default)

def mkStructureDecl (vars : Array Expr) (view : StructView) : TermElabM Unit := Term.withoutSavingRecAppSyntax do
  let scopeLevelNames ← Term.getLevelNames
  let isUnsafe := view.modifiers.isUnsafe
  withRef view.ref <| Term.withLevelNames view.levelNames do
    let r ← elabStructHeader view
    Term.synthesizeSyntheticMVarsNoPostponing
    withLCtx r.lctx r.localInsts do
    withStructureLocalDecl r fun params indFVar => do
    trace[Elab.structure] "indFVar: {indFVar}"
    Term.addLocalVarInfo view.declId indFVar
    withFields view.fields r.parentFieldInfos fun fieldInfos =>
    withRef view.ref do
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars r.type
      let u ← getResultUniverse type
      let univToInfer? ← shouldInferResultUniverse u
      withUsed vars params fieldInfos fun scopeVars => do
        let fieldInfos ← levelMVarToParam scopeVars params fieldInfos univToInfer?
        let type ← withRef view.ref do
          if univToInfer?.isSome then
            updateResultingUniverse fieldInfos type
          else
            checkResultingUniverse (← getResultUniverse type)
            pure type
        trace[Elab.structure] "type: {type}"
        let usedLevelNames ← collectLevelParamsInStructure type scopeVars params fieldInfos
        match sortDeclLevelParams scopeLevelNames r.levelNames usedLevelNames with
        | Except.error msg      => throwErrorAt view.declId msg
        | Except.ok levelParams =>
          let params := scopeVars ++ params
          let ctor ← mkCtor view levelParams params fieldInfos
          let type ← mkForallFVars params type
          let type ← instantiateMVars type
          let indType ← mkInductiveType view indFVar levelParams scopeVars.size params.size type ctor
          let decl    := Declaration.inductDecl levelParams params.size [indType] isUnsafe
          Term.ensureNoUnassignedMVars decl
          addDecl decl
          -- rename indFVar so that it does not shadow the actual declaration:
          let lctx := (← getLCtx).modifyLocalDecl indFVar.fvarId! fun decl => decl.setUserName .anonymous
          withLCtx lctx (← getLocalInstances) do
          addProjections r fieldInfos
          registerStructure view.declName fieldInfos
          mkAuxConstructions view.declName
          withSaveInfoContext do  -- save new env
            Term.addLocalVarInfo view.ref[1] (← mkConstWithLevelParams view.declName)
            if let some _ := view.ctor.ref.getPos? (canonicalOnly := true) then
              Term.addTermInfo' view.ctor.ref (← mkConstWithLevelParams view.ctor.declName) (isBinder := true)
            for field in view.fields do
              -- may not exist if overriding inherited field
              if (← getEnv).contains field.declName then
                Term.addTermInfo' field.ref (← mkConstWithLevelParams field.declName) (isBinder := true)
          withRef view.declId do
            Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
          let parentInfos ← r.parents.mapM fun parent => do
            if parent.subobject then
              let some info := fieldInfos.find? (·.kind == .subobject parent.structName) | unreachable!
              pure { structName := parent.structName, subobject := true, projFn := info.declName }
            else
              mkCoercionToCopiedParent levelParams params view parent.structName parent.type
          setStructureParents view.declName parentInfos
          checkResolutionOrder view.declName
          if view.isClass then
            addParentInstances parentInfos

          let lctx ← getLCtx
          /- The `lctx` and `defaultAuxDecls` are used to create the auxiliary "default value" declarations
            The parameters `params` for these definitions must be marked as implicit, and all others as explicit. -/
          let lctx :=
            params.foldl (init := lctx) fun (lctx : LocalContext) (p : Expr) =>
              if p.isFVar then
                lctx.setBinderInfo p.fvarId! BinderInfo.implicit
              else
                lctx
          let lctx :=
            fieldInfos.foldl (init := lctx) fun (lctx : LocalContext) (info : StructFieldInfo) =>
              if info.isFromParent then lctx -- `fromParent` fields are elaborated as let-decls, and are zeta-expanded when creating "default value" auxiliary functions
              else lctx.setBinderInfo info.fvar.fvarId! BinderInfo.default
          addDefaults lctx fieldInfos


def elabStructureView (vars : Array Expr) (view : StructView) : TermElabM Unit := do
  Term.withDeclName view.declName <| withRef view.ref do
    mkStructureDecl vars view
    unless view.isClass do
      Lean.Meta.IndPredBelow.mkBelow view.declName
      mkSizeOfInstances view.declName
      mkInjectiveTheorems view.declName

def elabStructureViewPostprocessing (view : StructView) : CommandElabM Unit := do
  view.derivingClasses.forM fun classView => classView.applyHandlers #[view.declName]
  runTermElabM fun _ => Term.withDeclName view.declName <| withRef view.declId do
    Term.applyAttributesAt view.declName view.modifiers.attrs .afterCompilation

def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  let view ← runTermElabM fun vars => do
    let view ← structureSyntaxToView modifiers stx
    trace[Elab.structure] "view.levelNames: {view.levelNames}"
    elabStructureView vars view
    pure view
  elabStructureViewPostprocessing view

builtin_initialize
  registerTraceClass `Elab.structure
  registerTraceClass `Elab.structure.resolutionOrder

end Lean.Elab.Command
