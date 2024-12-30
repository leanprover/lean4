/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Structure
import Lean.Elab.MutualInductive

namespace Lean.Elab.Command

builtin_initialize
  registerTraceClass `Elab.structure
  registerTraceClass `Elab.structure.resolutionOrder

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

structure StructView extends InductiveView where
  parents         : Array Syntax
  fields          : Array StructFieldView
  deriving Inhabited

def StructView.ctor : StructView → CtorView
  | { ctors := #[ctor], ..} => ctor
  | _ => unreachable!

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
private def expandCtor (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : TermElabM CtorView := do
  let useDefault := do
    let declName := structDeclName ++ defaultCtorName
    let ref := structStx[1].mkSynthetic
    addDeclarationRangesFromSyntax declName ref
    pure { ref, declId := ref, modifiers := default, declName }
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
      pure { ref := ctor[1], declId := ctor[1], modifiers := ctorModifiers, declName }

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
  let type?     := if optType.isNone then none else some optType[0][1]
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
    type?
    allowIndices := false
    allowSortPolymorphism := false
    ctors := #[ctor]
    parents
    fields
    computedFields := #[]
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

private def processSubfields (structDeclName : Name) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
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

private def withParents (view : StructView) (rs : Array ElabHeaderResult) (indFVar : Expr)
    (k : Array StructFieldInfo → Array StructParentInfo → TermElabM α) : TermElabM α := do
  go 0 #[] #[]
where
  go (i : Nat) (infos : Array StructFieldInfo) (parents : Array StructParentInfo) : TermElabM α := do
    if h : i < view.parents.size then
      let parent := view.parents[i]
      withRef parent do
      -- The only use case for autobound implicits for parents might be outParams, but outParam is not propagated.
      let type ← Term.withoutAutoBoundImplicit <| Term.elabType parent
      let parentType ← whnf type
      if parentType.getAppFn == indFVar then
        logWarning "structure extends itself, skipping"
        return ← go (i + 1) infos parents
      if rs.any (fun r => r.indFVar == parentType.getAppFn) then
        throwError "structure cannot extend types defined in the same mutual block"
      let parentStructName ← getStructureName parentType
      if parents.any (fun info => info.structName == parentStructName) then
        logWarning m!"duplicate parent structure '{.ofConstName parentStructName}', skipping"
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

private def registerFailedToInferFieldType (fieldName : Name) (e : Expr) (ref : Syntax) : TermElabM Unit := do
  Term.registerCustomErrorIfMVar (← instantiateMVars e) ref m!"failed to infer type of field '{.ofConstName fieldName}'"

private def registerFailedToInferDefaultValue (fieldName : Name) (e : Expr) (ref : Syntax) : TermElabM Unit := do
  Term.registerCustomErrorIfMVar (← instantiateMVars e) ref m!"failed to infer default value for field '{.ofConstName fieldName}'"
  Term.registerLevelMVarErrorExprInfo e ref m!"failed to infer universe levels in default value for field '{.ofConstName fieldName}'"

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
        registerFailedToInferFieldType view.name (← inferType value) view.nameId
        registerFailedToInferDefaultValue view.name value valStx
        let value ← mkLambdaFVars params value
        return (none, value)
    | some typeStx =>
      let type ← Term.elabType typeStx
      registerFailedToInferFieldType view.name type typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let params ← Term.addAutoBoundImplicits params
      match view.value? with
      | none        =>
        let type  ← mkForallFVars params type
        return (type, none)
      | some valStx =>
        let value ← Term.withoutAutoBoundImplicit <| Term.elabTermEnsuringType valStx type
        registerFailedToInferDefaultValue view.name value valStx
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
              registerFailedToInferDefaultValue view.name value valStx
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

private def collectUsedFVars (lctx : LocalContext) (localInsts : LocalInstances) (fieldInfos : Array StructFieldInfo) :
    StateRefT CollectFVars.State MetaM Unit := do
  withLCtx lctx localInsts do
    fieldInfos.forM fun info => do
      let fvarType ← inferType info.fvar
      fvarType.collectFVars
      if let some value := info.value? then
        value.collectFVars

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

private def mkCtor (view : StructView) (r : ElabHeaderResult) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM Constructor :=
  withRef view.ref do
  let type := mkAppN r.indFVar params
  let type ← addCtorFields fieldInfos fieldInfos.size type
  let type ← mkForallFVars params type
  let type ← instantiateMVars type
  let type := type.inferImplicit params.size true
  pure { name := view.ctor.declName, type }

private partial def checkResultingUniversesForFields (fieldInfos : Array StructFieldInfo) (u : Level) : TermElabM Unit := do
  for info in fieldInfos do
    let type ← inferType info.fvar
    let v := (← instantiateLevelMVars (← getLevel type)).normalize
    unless u.geq v do
      let msg := m!"invalid universe level for field '{info.name}', has type{indentExpr type}\n\
        at universe level{indentD v}\n\
        which is not less than or equal to the structure's resulting universe level{indentD u}"
      throwErrorAt info.ref msg

@[extern "lean_mk_projections"]
private opaque mkProjections (env : Environment) (structName : Name) (projs : List Name) (isClass : Bool) : Except Kernel.Exception Environment

private def addProjections (r : ElabHeaderResult) (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
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

private def checkDefaults (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
  let mut mvars := {}
  let mut lmvars := {}
  for fieldInfo in fieldInfos do
    if let some value := fieldInfo.value? then
      let value ← instantiateMVars value
      mvars := Expr.collectMVars mvars value
      lmvars := collectLevelMVars lmvars value
  -- Log errors and ignore the failure; we later will just omit adding a default value.
  if ← Term.logUnassignedUsingErrorInfos mvars.result then
    return
  else if ← Term.logUnassignedLevelMVarsUsingErrorInfos lmvars.result then
    return

private def addDefaults (params : Array Expr) (replaceIndFVars : Expr → MetaM Expr) (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
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
  -- Make all indFVar replacements in the local context.
  let lctx ←
    lctx.foldlM (init := {}) fun lctx ldecl => do
     match ldecl with
     | .cdecl _ fvarId userName type bi k =>
       let type ← replaceIndFVars type
       return lctx.mkLocalDecl fvarId userName type bi k
     | .ldecl _ fvarId userName type value nonDep k =>
       let type ← replaceIndFVars type
       let value ← replaceIndFVars value
       return lctx.mkLetDecl fvarId userName type value nonDep k
  withLCtx lctx (← getLocalInstances) do
    fieldInfos.forM fun fieldInfo => do
      if let some value := fieldInfo.value? then
        let declName := mkDefaultFnOfProjFn fieldInfo.declName
        let type ← replaceIndFVars (← inferType fieldInfo.fvar)
        let value ← instantiateMVars (← replaceIndFVars value)
        trace[Elab.structure] "default value after 'replaceIndFVars': {indentExpr value}"
        -- If there are mvars, `checkDefaults` already logged an error.
        unless value.hasMVar || value.hasSyntheticSorry do
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
private partial def mkCoercionToCopiedParent (levelParams : List Name) (params : Array Expr) (view : StructView) (source : Expr) (parentStructName : Name) (parentType : Expr) : MetaM StructureParentInfo := do
  let isProp ← Meta.isProp parentType
  let env ← getEnv
  let structName := view.declName
  let sourceFieldNames := getStructureFieldsFlattened env structName
  let binfo := if view.isClass && isClass env parentStructName then BinderInfo.instImplicit else BinderInfo.default
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

private def mkRemainingProjections (levelParams : List Name) (params : Array Expr) (view : StructView)
    (parents : Array StructParentInfo) (fieldInfos : Array StructFieldInfo) : TermElabM (Array StructureParentInfo) := do
  let structType := mkAppN (Lean.mkConst view.declName (levelParams.map mkLevelParam)) params
  withLocalDeclD `self structType fun source => do
    /-
    Remark: copied parents might still be referring to the fvars of other parents. We need to replace these fvars with projection constants.
    For subobject parents, this has already been done by `mkProjections`.
    https://github.com/leanprover/lean4/issues/2611
    -/
    let mut parentInfos := #[]
    let mut parentFVarToConst : ExprMap Expr := {}
    for h : i in [0:parents.size] do
      let parent := parents[i]
      let parentInfo : StructureParentInfo ← (do
        if parent.subobject then
          let some info := fieldInfos.find? (·.kind == .subobject parent.structName) | unreachable!
          pure { structName := parent.structName, subobject := true, projFn := info.declName }
        else
          let parent_type := (← instantiateMVars parent.type).replace fun e => parentFVarToConst[e]?
          mkCoercionToCopiedParent levelParams params view source parent.structName parent_type)
      parentInfos := parentInfos.push parentInfo
      if let some fvar := parent.fvar? then
        parentFVarToConst := parentFVarToConst.insert fvar <|
          mkApp (mkAppN (.const parentInfo.projFn (levelParams.map mkLevelParam)) params) source
    pure parentInfos

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

@[builtin_inductive_elab Lean.Parser.Command.«structure»]
def elabStructureCommand : InductiveElabDescr where
  mkInductiveView (modifiers : Modifiers) (stx : Syntax) := do
    let view ← structureSyntaxToView modifiers stx
    trace[Elab.structure] "view.levelNames: {view.levelNames}"
    return {
      view := view.toInductiveView
      elabCtors := fun rs r params => do
        withParents view rs r.indFVar fun parentFieldInfos parents =>
        withFields view.fields parentFieldInfos fun fieldInfos => do
        withRef view.ref do
          Term.synthesizeSyntheticMVarsNoPostponing
          let lctx ← getLCtx
          let localInsts ← getLocalInstances
          let ctor ← mkCtor view r params fieldInfos
          return {
            ctors := [ctor]
            collectUsedFVars := collectUsedFVars lctx localInsts fieldInfos
            checkUniverses := fun _ u => withLCtx lctx localInsts do checkResultingUniversesForFields fieldInfos u
            finalizeTermElab := withLCtx lctx localInsts do checkDefaults fieldInfos
            prefinalize := fun _ _ _ => do
              withLCtx lctx localInsts do
                addProjections r fieldInfos
                registerStructure view.declName fieldInfos
              withSaveInfoContext do  -- save new env
                for field in view.fields do
                  -- may not exist if overriding inherited field
                  if (← getEnv).contains field.declName then
                    Term.addTermInfo' field.ref (← mkConstWithLevelParams field.declName) (isBinder := true)
            finalize := fun levelParams params replaceIndFVars => do
              let parentInfos ← mkRemainingProjections levelParams params view parents fieldInfos
              setStructureParents view.declName parentInfos
              checkResolutionOrder view.declName
              if view.isClass then
                addParentInstances parentInfos

              withLCtx lctx localInsts do
                addDefaults params replaceIndFVars fieldInfos
          }
    }

end Lean.Elab.Command
