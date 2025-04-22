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

namespace Structure

/-! Recall that the `structure command syntax is
```
leading_parser (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> Term.optType >> optional «extends» >> optional (" := " >> optional structCtor >> structFields)
```
-/

/--
Represents the data of the syntax of a structure parent.
-/
structure StructParentView where
  ref        : Syntax
  /-- Ref to use for the parent projection. -/
  projRef    : Syntax
  /-- The name of the parent projection (without macro scopes). -/
  name?      : Option Name
  /-- The name of the parent projection (with macro scopes). Used for local name during elaboration. -/
  rawName?   : Option Name
  type       : Syntax

inductive StructFieldViewDefault where
  | optParam (value : Syntax)
  | autoParam (tactic : Syntax)

/--
Represents the data of the syntax of a structure field declaration.
-/
structure StructFieldView where
  ref        : Syntax
  modifiers  : Modifiers
  binderInfo : BinderInfo
  declName   : Name
  /-- Ref for the field name -/
  nameId     : Syntax
  /-- The name of the field (without macro scopes). -/
  name       : Name
  /-- The name of the field (with macro scopes).
  Used when adding the field to the local context, for field elaboration. -/
  rawName    : Name
  binders    : Syntax
  type?      : Option Syntax
  default?   : Option StructFieldViewDefault

structure StructView extends InductiveView where
  parents : Array StructParentView
  fields  : Array StructFieldView
  deriving Inhabited

/--
Gets the single constructor view from the underlying `InductiveView`.
Recall that `structure`s have exactly one constructor.
-/
def StructView.ctor (view : StructView) : CtorView :=
  view.ctors[0]!

/--
Elaborated parent info.
-/
structure StructParentInfo where
  ref         : Syntax
  /-- Whether to add term info to the ref. False if there's no user-provided parent projection. -/
  addTermInfo : Bool
  /-- A let variable that represents this structure parent. -/
  fvar        : Expr
  structName  : Name
  /-- Field name for parent. -/
  name        : Name
  /-- Name of the projection function. -/
  declName    : Name
  /-- Whether this parent corresponds to a `subobject` field. -/
  subobject   : Bool
  deriving Inhabited

/--
Records the way in which a field is represented in a structure.

Standard fields are one of `.newField`, `.copiedField`, or `.fromSubobject`.
Parent fields are one of `.subobject` or `.otherParent`.
-/
inductive StructFieldKind where
  /-- New field defined by the `structure`.
  Represented as a constructor argument. Will have a projection function. -/
  | newField
  /-- Field that comes from a parent but will be represented as a new field.
  Represented as a constructor argument. Will have a projection function.
  Its inherited default value may be overridden. -/
  | copiedField
  /-- Field that comes from a embedded parent field, and is represented within a `subobject` field.
  Not represented as a constructor argument. Will not have a projection function.
  Its inherited default value may be overridden. -/
  | fromSubobject
  /-- The field is an embedded parent structure.
  Represented as a constructor argument. Will have a projection function.
  Default values are not allowed. -/
  | subobject (structName : Name)
  /-- The field represents a parent projection for a parent that is not itself embedded as a subobject.
  (Note: parents of `subobject` fields are `otherParent` fields.)
  Not represented as a constructor argument. Will only have a projection function if it is a direct parent.
  Default values are not allowed. -/
  | otherParent (structName : Name)
  deriving Inhabited, DecidableEq, Repr

def StructFieldKind.isFromSubobject (kind : StructFieldKind) : Bool :=
  kind matches StructFieldKind.fromSubobject

def StructFieldKind.isSubobject (kind : StructFieldKind) : Bool :=
  kind matches StructFieldKind.subobject ..

/-- Returns `true` if the field represents a parent projection. -/
def StructFieldKind.isParent (kind : StructFieldKind) : Bool :=
  kind matches StructFieldKind.subobject .. | StructFieldKind.otherParent ..

/-- Returns `true` if the field is represented as a field in the constructor. -/
def StructFieldKind.isInCtor (kind : StructFieldKind) : Bool :=
  kind matches .newField | .copiedField | .subobject ..

inductive StructFieldDefault where
  | optParam (value : Expr)
  | autoParam (tactic : Expr)
  deriving Repr

/--
Elaborated field info.
-/
structure StructFieldInfo where
  ref      : Syntax
  name     : Name
  kind     : StructFieldKind
  /-- Name of projection function.
  Remark: for fields that don't get projection functions (like `fromSubobject` fields), only relevant for the auxiliary "default value" functions. -/
  declName : Name
  /-- Binder info to use when making the constructor. Only applies to those fields that will appear in the constructor. -/
  binfo    : BinderInfo
  /-- Overrides for the parameters' binder infos when making the projections. The first component is a ref for the binder. -/
  paramInfoOverrides : ExprMap (Syntax × BinderInfo) := {}
  /--
  Structure names that are responsible for this field being here.
  - Empty if the field is a `newField`.
  - Otherwise, it is a stack with the last element being a parent in the `extends` clause.
    The first element is the (indirect) parent that is responsible for this field.
  -/
  sourceStructNames : List Name
  /-- Local variable for the field.
  All fields (both real fields and parent projection fields) get a local variable.
  Parent fields are ldecls constructed from non-parent fields. -/
  fvar     : Expr
  /-- An expression representing a `.fromSubobject` field as a projection of a `.subobject` field.
  Used when making the constructor.
  Note: `.otherParent` fields are let decls, there is no need for `projExpr?`. -/
  projExpr? : Option Expr := none
  /-- The default value, as explicitly given in this `structure`. -/
  default?  : Option StructFieldDefault := none
  /-- If this is an inherited field, the name of the projection function.
  Used for adding terminfo for fields with overridden default values. -/
  projFn?   : Option Name := none
  /-- The inherited default values, as parent structure / value pairs. -/
  inheritedDefaults : Array (Name × StructFieldDefault) := #[]
  /-- The default that will be used for this structure. -/
  resolvedDefault?  : Option StructFieldDefault := none
  deriving Inhabited

/-!
### View construction
-/

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

/--
```
def structParent := leading_parser optional (atomic (ident >> " : ")) >> termParser
def «extends»    := leading_parser " extends " >> sepBy1 structParent ", "
```
-/
private def expandParents (optExtendsStx : Syntax) : TermElabM (Array StructParentView) := do
  let parentDecls := if optExtendsStx.isNone then #[] else optExtendsStx[0][1].getSepArgs
  parentDecls.mapM fun parentDecl => withRef parentDecl do
    let mut projRef  := parentDecl
    let mut rawName? := none
    let mut name? := none
    unless parentDecl[0].isNone do
      let ident := parentDecl[0][0]
      let rawName := ident.getId
      let name := rawName.eraseMacroScopes
      unless name.isAtomic do
        throwErrorAt ident "invalid parent projection name '{name}', names must be atomic"
      projRef  := ident
      rawName? := rawName
      name? := name
    let type := parentDecl[1]
    return {
      ref := parentDecl
      projRef
      name?
      rawName?
      type
    }

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
    let (binders, type?, default?) ←
      if binfo == BinderInfo.default then
        let (binders, type?) := expandOptDeclSig fieldBinder[3]
        let optBinderTacticDefault := fieldBinder[4]
        if optBinderTacticDefault.isNone then
          pure (binders, type?, none)
        else if optBinderTacticDefault[0].getKind != ``Parser.Term.binderTactic then
          -- binderDefault := leading_parser " := " >> termParser
          let value := optBinderTacticDefault[0][1]
          pure (binders, type?, some <| StructFieldViewDefault.optParam value)
        else
          let binderTactic := optBinderTacticDefault[0]
          let tac := binderTactic[2]
          -- Auto-param applies to `forall $binders*, $type`, which will be handled in `elabFieldTypeValue`
          pure (binders, type?, some <| StructFieldViewDefault.autoParam tac)
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
        default?
      }

/-
leading_parser (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> Term.optType >> optional «extends» >>
  optional (("where" <|> ":=") >> optional structCtor >> structFields) >> optDeriving

where
def structParent := leading_parser optional (atomic (ident >> " : ")) >> termParser
def «extends» := leading_parser " extends " >> sepBy1 structParent ", "
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
  let (optType, exts) ←
    -- Compatibility mode for `structure S extends P : Type` syntax
    if stx[3].isNone && !stx[4].isNone && !stx[4][0][2].isNone then
      logWarningAt stx[4][0][2][0] "\
        The syntax is now 'structure S : Type extends P' rather than 'structure S extends P : Type'.\n\n\
        The purpose of this change is to accommodate 'structure S extends toP : P' syntax for naming parent projections."
      pure (stx[4][0][2], stx[4])
    else
      if !stx[4].isNone && !stx[4][0][2].isNone then
        logErrorAt stx[4][0][2][0] "\
          Unexpected additional resulting type. \
          The syntax is now 'structure S : Type extends P' rather than 'structure S extends P : Type'.\n\n\
          The purpose of this change is to accommodate 'structure S extends toP : P' syntax for naming parent projections."
      pure (stx[3], stx[4])
  let parents   ← expandParents exts
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


/-!
### Elaboration
-/

private structure State where
  /-- Immediate parents. -/
  parents : Array StructParentInfo := #[]
  /-- All fields, both newly defined and inherited. Every parent has a `StructFieldInfo` too. -/
  fields : Array StructFieldInfo := #[]
  /-- Map from field name to its index in `fields`. -/
  fieldIdx : NameMap Nat := {}
  /-- Map from structure name to `field` index. -/
  ancestorFieldIdx : NameMap Nat := {}
  /-- Map from fvar ids to its index in `fields`. -/
  fvarIdFieldIdx : FVarIdMap Nat := {}
  deriving Inhabited

/--
Monad for elaborating parents and fields of a `structure`.
-/
private abbrev StructElabM := StateT State TermElabM

instance : Inhabited (StructElabM α) where
  default := throw default

def runStructElabM (k : StructElabM α) (init : State := {}) : TermElabM α := k.run' init

private def addParentInfo (parent : StructParentInfo) : StructElabM Unit := do
  modify fun s => { s with parents := s.parents.push parent }

private def findFieldInfo? (fieldName : Name) : StructElabM (Option StructFieldInfo) := do
  let s ← get
  return s.fieldIdx.find? fieldName |>.map fun idx => s.fields[idx]!

private def hasFieldName (fieldName : Name) : StructElabM Bool :=
  return (← get).fieldIdx.contains fieldName

private def findFieldInfoByFVarId? (fvarId : FVarId) : StructElabM (Option StructFieldInfo) := do
  let s ← get
  return s.fvarIdFieldIdx.find? fvarId |>.map fun idx => s.fields[idx]!

/--
Inserts a field info into the current state.
Throws an error if there is already a field with that name.
-/
private def addFieldInfo (info : StructFieldInfo) : StructElabM Unit := do
  if ← hasFieldName info.name then
    throwError "(in addFieldInfo) structure field '{info.name}' already exists"
  else
    modify fun s =>
      let idx := s.fields.size
      { s with
        fields           := s.fields.push info
        fieldIdx         := s.fieldIdx.insert info.name idx
        fvarIdFieldIdx   := s.fvarIdFieldIdx.insert info.fvar.fvarId! idx
        ancestorFieldIdx :=
          match info.kind with
          | .subobject structName | .otherParent structName =>
            s.ancestorFieldIdx.insert structName idx
          | _ =>
            s.ancestorFieldIdx
      }

private def findParentFieldInfo? (structName : Name) : StructElabM (Option StructFieldInfo) := do
  let s ← get
  return s.ancestorFieldIdx.find? structName |>.map fun idx => s.fields[idx]!

/--
Replaces the field info for a given field.
Throws an error if there is not already a field with that name.
-/
private def replaceFieldInfo (info : StructFieldInfo) : StructElabM Unit := do
  if let some idx := (← get).fieldIdx.find? info.name then
    modify fun s => { s with fields := s.fields.set! idx info }
  else
    throwError "(in replaceFieldInfo) structure field '{info.name}' does not already exist"

private def addFieldInheritedDefault (fieldName : Name) (structName : Name) (d : StructFieldDefault) : StructElabM Unit := do
  let some info ← findFieldInfo? fieldName
    | throwError "(in addFieldInheritedDefault) structure field '{fieldName}' does not already exist"
  replaceFieldInfo { info with inheritedDefaults := info.inheritedDefaults.push (structName, d) }

/--
Reduces projections applied to constructors or parent fvars, for structure types that have appeared as parents.

If `zetaDelta` is true (default), then zeta reduces parent fvars as needed to do the reductions.
-/
private def reduceFieldProjs (e : Expr) (zetaDelta := true) : StructElabM Expr := do
  let e ← instantiateMVars e
  let postVisit (e : Expr) : StructElabM TransformStep := do
    if let Expr.const projName .. := e.getAppFn then
      if let some projInfo ← getProjectionFnInfo? projName then
        let ConstantInfo.ctorInfo cval := (← getEnv).find? projInfo.ctorName | unreachable!
        if let some info ← findParentFieldInfo? cval.induct then
          let args := e.getAppArgs
          if let some major := args[projInfo.numParams]? then
            let major ←
              if zetaDelta && major == info.fvar then
                pure <| (← major.fvarId!.getValue?).getD major
              else
                pure major
            if major.isAppOfArity projInfo.ctorName (cval.numParams + cval.numFields) then
              if let some arg := major.getAppArgs[projInfo.numParams + projInfo.i]? then
                return TransformStep.visit <| mkAppN arg args[projInfo.numParams+1:]
    return TransformStep.continue
  Meta.transform e (post := postVisit)

/--
Puts an expression into "field normal form".
- All projections of constructors for parent structures are reduced.
- If `zetaDelta` is true (default) then all parent fvars are zeta reduced.
- Constructors of parent structures are eta reduced.
-/
private def fieldNormalizeExpr (e : Expr) (zetaDelta : Bool := true) : StructElabM Expr := do
  let ancestors := (← get).ancestorFieldIdx
  etaStructReduce (p := ancestors.contains) <| ← reduceFieldProjs e (zetaDelta := zetaDelta)

private def fieldFromMsg (info : StructFieldInfo) : MessageData :=
  if let some sourceStructName := info.sourceStructNames.head? then
    m!"field '{info.name}' from '{.ofConstName sourceStructName}'"
  else
    m!"field '{info.name}'"

/--
Instantiates default value for field `fieldName` set at structure `structName`, using the field fvars in the `StructFieldInfo`s.
After default values are resolved, then the one that is added to the environment
as an `_inherited_default` auxiliary function is normalized;
we don't do those normalizations here, since that could be wasted effort if this default isn't chosen.
-/
private partial def getFieldDefaultValue? (structName : Name) (params : Array Expr) (fieldName : Name) : StructElabM (Option Expr) := do
  let some defFn := getDefaultFnForField? (← getEnv) structName fieldName
    | return none
  let fieldVal? (n : Name) : StructElabM (Option Expr) := do
    let some info ← findFieldInfo? n | return none
    return info.fvar
  let some (_, val) ← instantiateStructDefaultValueFn? defFn none params fieldVal?
    | logWarning m!"default value for field '{fieldName}' of structure '{.ofConstName structName}' could not be instantiated, ignoring"
      return none
  return val

private def getFieldDefault? (structName : Name) (params : Array Expr) (fieldName : Name) :
    StructElabM (Option StructFieldDefault) := do
  if let some val ← getFieldDefaultValue? structName params fieldName then
    -- Important: we use `getFieldDefaultValue?` because we want default value definitions, not *inherited* ones, to properly handle diamonds
    trace[Elab.structure] "found default value for '{fieldName}' from '{.ofConstName structName}'{indentExpr val}"
    return StructFieldDefault.optParam val
  else if let some fn := getAutoParamFnForField? (← getEnv) structName fieldName then
    trace[Elab.structure] "found autoparam for '{fieldName}' from '{.ofConstName structName}'"
    return StructFieldDefault.autoParam (Expr.const fn [])
  else
    return none

private def toVisibility (fieldInfo : StructureFieldInfo) : CoreM Visibility := do
  if isProtected (← getEnv) fieldInfo.projFn then
    return Visibility.protected
  else if isPrivateName fieldInfo.projFn then
    return Visibility.private
  else
    return Visibility.regular

mutual

/--
Adds `fieldName` of type `fieldType` from structure `structName`.
See `withStructFields` for meanings of other arguments.
-/
private partial def withStructField (view : StructView) (sourceStructNames : List Name) (inSubobject? : Option Expr)
    (structName : Name) (params : Array Expr) (fieldName : Name) (fieldType : Expr)
    (k : Expr → StructElabM α) : StructElabM α := do
  trace[Elab.structure] "withStructField '{.ofConstName structName}', field '{fieldName}'"
  let fieldType ← instantiateMVars fieldType
  let fieldType := fieldType.consumeTypeAnnotations -- remove autoParam from constructor field
  let env ← getEnv
  let some fieldInfo := getFieldInfo? env structName fieldName
    | throwError "(withStructField internal error) no such field '{fieldName}' of '{.ofConstName structName}'"
  if let some _ := fieldInfo.subobject? then
    -- It's a subobject field, add it and its fields
    withStruct view (structName :: sourceStructNames) (binfo := fieldInfo.binderInfo)
      fieldName fieldType inSubobject? fun info => k info.fvar
  else if let some existingField ← findFieldInfo? fieldName then
    -- It's a pre-existing field, make sure it is compatible (unless diamonds are not allowed)
    if structureDiamondWarning.get (← getOptions) then
      logWarning m!"field '{fieldName}' from '{.ofConstName structName}' has already been declared"
    let existingFieldType ← inferType existingField.fvar
    unless (← isDefEq fieldType existingFieldType) do
      throwError "field type mismatch, field '{fieldName}' from parent '{.ofConstName structName}' {← mkHasTypeButIsExpectedMsg fieldType existingFieldType}"
    if let some d ← getFieldDefault? structName params fieldName then
      addFieldInheritedDefault fieldName structName d
    k existingField.fvar
  else
    -- It's a not-yet-seen field
    /- For `.fromSubobject`: the following `declName` is only used for creating the `_default`/`_inherited_default` auxiliary declaration name when
       its default value is overridden, otherwise the `declName` is irrelevant, except to ensure a declaration is not already declared. -/
    let mut declName := view.declName ++ fieldName
    if inSubobject?.isNone then
      declName ← applyVisibility (← toVisibility fieldInfo) declName
      -- No need to validate links because this docstring was already added to the environment previously
      addDocStringCore' declName (← findDocString? (← getEnv) fieldInfo.projFn)
      addDeclarationRangesFromSyntax declName (← getRef)
    checkNotAlreadyDeclared declName
    withLocalDecl fieldName fieldInfo.binderInfo (← reduceFieldProjs fieldType) fun fieldFVar => do
      let projExpr? ← inSubobject?.mapM fun subobject => mkProjection subobject fieldName
      addFieldInfo {
        ref := (← getRef)
        sourceStructNames := structName :: sourceStructNames
        name := fieldName
        declName
        kind := if inSubobject?.isSome then .fromSubobject else .copiedField
        fvar := fieldFVar
        projExpr?
        binfo := fieldInfo.binderInfo
        projFn? := fieldInfo.projFn
      }
      if let some d ← getFieldDefault? structName params fieldName then
        addFieldInheritedDefault fieldName structName d
      k fieldFVar

/--
Adds all the fields from `structType` along with its parent projection fields.
Does not add a parent field for the structure itself; that is done by `withStruct`.
- if `inSubobject?` is `some e`, then `e` must be an expression representing the `.subobject` parent being constructed (a metavariable),
  and the added fields are marked `.fromSubobject` and are set to have `e` projections
- `sourceStructNames` is a stack of the structures visited, used for error reporting
- the continuation `k` is run with a constructor expression for this structure
-/
private partial def withStructFields (view : StructView) (sourceStructNames : List Name)
    (structType : Expr) (inSubobject? : Option Expr)
    (k : Expr → StructElabM α) : StructElabM α := do
  let structName ← getStructureName structType
  let .const _ us := structType.getAppFn | unreachable!
  let params := structType.getAppArgs

  trace[Elab.structure] "withStructFields '{.ofConstName structName}'"

  let env ← getEnv
  let fields := getStructureFields env structName
  let parentInfos := getStructureParentInfo env structName

  let ctorVal := getStructureCtor env structName
  let ctor := mkAppN (mkConst ctorVal.name us) params
  let (fieldMVars, _, _) ← forallMetaTelescope (← inferType ctor)
  assert! fieldMVars.size == fields.size

  -- Go through all parents to make sure parent projections are consistent.
  let rec goParents (s : Expr) (i : Nat) : StructElabM α := do
    if h : i < parentInfos.size then
      let parentInfo := parentInfos[i]
      if parentInfo.subobject then
        goParents s (i + 1)
      else
        let fieldName := Name.mkSimple parentInfo.projFn.getString!
        let fieldType ← inferType <| mkApp (mkAppN (.const parentInfo.projFn us) params) s
        withStruct view (structName :: sourceStructNames) (binfo := .default)
          fieldName fieldType inSubobject? fun _ => goParents s (i + 1)
    else
      k s

  let rec goFields (i : Nat) : StructElabM α := do
    if h : i < fields.size then
      let fieldName := fields[i]
      let fieldMVar := fieldMVars[i]!
      let fieldType ← inferType fieldMVar
      withStructField view sourceStructNames inSubobject? structName params fieldName fieldType fun fieldFVar => do
        fieldMVar.mvarId!.assign fieldFVar
        goFields (i + 1)
    else
      let s ← instantiateMVars <| mkAppN ctor fieldMVars
      goParents s 0

  goFields 0

/--
Adds a parent structure and all its fields.
- `structFieldName` is the name to use for the parent field.
- `rawStructFieldName` is name to use in local context, for hygiene. By default it is `structFieldName`.

See `withStructFields` for meanings of other arguments.
-/
private partial def withStruct (view : StructView) (sourceStructNames : List Name) (binfo : BinderInfo)
    (structFieldName : Name)
    (structType : Expr) (inSubobject? : Option Expr)
    (k : StructFieldInfo → StructElabM α)
    (rawStructFieldName := structFieldName) (projRef := Syntax.missing) :
    StructElabM α := do
  let env ← getEnv
  let structType ← reduceFieldProjs (← whnf structType)
  let structName ← getStructureName structType
  let params := structType.getAppArgs
  trace[Elab.structure] "withStructField '{.ofConstName structName}', using parent field '{structFieldName}'"
  if let some info ← findFieldInfo? structFieldName then
    -- Exact field name match. If it's a parent, then check defeq, otherwise it's a name conflict.
    if info.kind.isParent then
      let infoType ← inferType info.fvar
      if ← isDefEq infoType structType then
        k info
      else
        throwError "parent type mismatch, {← mkHasTypeButIsExpectedMsg structType infoType}"
    else
      throwErrorAt projRef "{fieldFromMsg info} has a name conflict with parent projection for '{.ofConstName structName}'\n\n\
        The 'toParent : P' syntax can be used to adjust the name for the parent projection"
  else if let some info ← findParentFieldInfo? structName then
    -- The field name is different. Error.
    assert! structFieldName != info.name
    throwErrorAt projRef "expecting '{structFieldName}' to match {fieldFromMsg info} for parent '{.ofConstName structName}'\n\n\
      The 'toParent : P' syntax can be used to adjust the name for the parent projection"
  else
    -- Main case: there is no field named `structFieldName` and there is no field for the structure `structName` yet.

    let projDeclName := view.declName ++ structFieldName
    withRef projRef do checkNotAlreadyDeclared projDeclName

    let allFields := getStructureFieldsFlattened env structName (includeSubobjectFields := false)
    let withStructFields' (kind : StructFieldKind) (inSubobject? : Option Expr) (k : StructFieldInfo → StructElabM α) : StructElabM α := do
      withStructFields view sourceStructNames structType inSubobject? fun structVal => do
        if let some _ ← findFieldInfo? structFieldName then
          throwErrorAt projRef "field '{structFieldName}' has already been declared\n\n\
            The 'toParent : P' syntax can be used to adjust the name for the parent projection"
        -- Add default values.
        -- We've added some default values so far, but we want all overridden default values,
        -- which for inherited fields might not have been seen yet.
        -- Note: duplication is ok for now. We use a stable sort later.
        for fieldName in allFields do
          if let some d ← getFieldDefault? structName params fieldName then
            addFieldInheritedDefault fieldName structName d
        withLetDecl rawStructFieldName structType structVal fun structFVar => do
          let info : StructFieldInfo := {
            ref := (← getRef)
            sourceStructNames := sourceStructNames
            name := structFieldName
            declName := projDeclName
            fvar := structFVar
            binfo := binfo
            kind
          }
          addFieldInfo info
          k info

    if inSubobject?.isSome then
      -- If we are currently in a subobject, then we can't use a subobject to represent this parent.
      withStructFields' (.otherParent structName) inSubobject? k
    else
      /-
      If there are no fields, we can avoid representing this structure in the constructor.
      This is mainly to support test files that define structures with no fields.
      TODO(kmill): remove check that there are any fields so far.
      This is to get around some oddities when parent projections are all no-ops (tests fail when it is removed).
      TODO(kmill): allow overlapping proof fields between subobjects! This does not harm defeq, and it should be more efficient.
      -/
      let elideParent := allFields.isEmpty && (← get).fields.any (·.kind.isInCtor)
      if elideParent || (← allFields.anyM hasFieldName) then
        -- Or, if there is an overlapping field, we need to copy/reuse fields rather than embed the parent as a subobject.
        withStructFields' (.otherParent structName) none k
      else
        -- Use a subobject for this parent.
        -- We create a metavariable to represent the subobject, so that `withStructField` can create projections
        let inSubobject ← mkFreshExprMVar structType
        withStructFields' (.subobject structName) inSubobject fun info => do
          inSubobject.mvarId!.assign info.fvar
          k info

end

/--
- `view` is the view of the structure being elaborated
- `projRef` is the ref to use for errors about the projection, set to the current ref when recursing
- `rawStructFieldName` is the name to use for the local declaration for this parent
- `structFieldName` is the field name to use for this parent
- `structType` is the parent's type
- `k` is a continuation that is run with a local context containing the fields and the ancestor fields,
  and it's provided the field info for the parent
-/
private partial def withParent (view : StructView) (projRef : Syntax)
    (rawStructFieldName structFieldName : Name)
    (structType : Expr)
    (k : StructFieldInfo → StructElabM α) :
    StructElabM α := do
  let env ← getEnv
  let structType ← whnf structType
  let structName ← getStructureName structType
  let binfo := if view.isClass && isClass env structName then BinderInfo.instImplicit else BinderInfo.default
  trace[Elab.structure] "binfo for {structFieldName} is {repr binfo}"
  withStruct view [] (projRef := projRef) (rawStructFieldName := rawStructFieldName)
    (binfo := binfo) (inSubobject? := none) structFieldName structType k

private def mkToParentName (parentStructName : Name) : Name :=
  Name.mkSimple <| "to" ++ parentStructName.eraseMacroScopes.getString!

private def StructParentView.mkToParentNames (parentView : StructParentView) (parentStructName : Name) : Name × Name :=
  match parentView.rawName?, parentView.name? with
  | some rawName, some name => (rawName, name)
  | _, _ =>
    let toParentName := mkToParentName parentStructName
    (toParentName, toParentName)

private def withParents (view : StructView) (rs : Array ElabHeaderResult) (indFVar : Expr) (k : StructElabM α) : StructElabM α := do
  go 0
where
  go (i : Nat) : StructElabM α := do
    if h : i < view.parents.size then
      let parentView := view.parents[i]
      withRef parentView.ref do
      -- The only use case for autobound implicits for parents might be outParams, but outParam is not propagated.
      let parentType ← Term.withoutAutoBoundImplicit <| Term.elabType parentView.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let parentType ← whnf parentType
      if parentType.getAppFn == indFVar then
        logWarning "structure extends itself, skipping"
        return ← go (i + 1)
      if rs.any (fun r => r.indFVar == parentType.getAppFn) then
        throwError "structure cannot extend types defined in the same mutual block"
      let parentStructName ← try
          getStructureName parentType
        catch ex =>
          throwErrorAt parentView.type "{ex.toMessageData}\n\n\
            This error is possibly due to a change in the 'structure' syntax. \
            Now the syntax is 'structure S : Type extends P' rather than 'structure S extends P' : Type'.\n\n\
            The purpose of the change is to accommodate 'structure S extends toP : P' syntax for naming parent projections."
      let (rawToParentName, toParentName) := parentView.mkToParentNames parentStructName
      if (← get).parents.any (·.structName == parentStructName) then
        logWarning m!"duplicate parent structure '{.ofConstName parentStructName}', skipping"
        go (i + 1)
      else if (← get).parents.any (·.name == toParentName) then
        throwError "field '{toParentName}' has already been declared\n\n\
          The 'toParent : P' syntax can be used to adjust the name for the parent projection"
      else
        withParent view parentView.projRef rawToParentName toParentName parentType fun parentFieldInfo => do
          addParentInfo {
            ref := parentView.projRef
            addTermInfo := parentView.name?.isSome
            fvar := parentFieldInfo.fvar
            subobject := parentFieldInfo.kind.isSubobject
            structName := parentStructName
            name := toParentName
            declName := parentFieldInfo.declName
          }
          go (i + 1)
    else
      k

private def registerFailedToInferFieldType (fieldName : Name) (e : Expr) (ref : Syntax) : TermElabM Unit := do
  Term.registerCustomErrorIfMVar (← instantiateMVars e) ref m!"failed to infer type of field '{.ofConstName fieldName}'"

private def registerFailedToInferDefaultValue (fieldName : Name) (e : Expr) (ref : Syntax) : TermElabM Unit := do
  Term.registerCustomErrorIfMVar (← instantiateMVars e) ref m!"failed to infer default value for field '{.ofConstName fieldName}'"
  Term.registerLevelMVarErrorExprInfo e ref m!"failed to infer universe levels in default value for field '{.ofConstName fieldName}'"

/--
Goes through all the natural mvars appearing in `e`, assigning any whose type is one of the inherited parents.

Rationale 1: Structures can only extend a parent once.
There should be no other occurences of a parent except for the parent itself.

Rationale 2: Consider the following code in the test `lean/run/balg.lean`:
```lean
structure Magma where
  α   : Type u
  mul : α → α → α

instance : CoeSort Magma (Type u) where
  coe s := s.α

abbrev mul {M : Magma} (a b : M) : M :=
  M.mul a b

infixl:70 (priority := high) "*" => mul

structure Semigroup extends Magma where
  mul_assoc (a b c : α) : a * b * c = a * (b * c)
```
When elaborating `*` in `mul_assoc`'s type, the `M` parameter of `mul` cannot be synthesized by unification.
Now `α` and `mul` are cdecls and `toMagma` is an ldecl,
but it used to be that `toMagma` was the cdecl and `α` and `mul` were projections of it,
which made it possible for unification to infer `toMagma` from `α`.
However, now `α` does not know its relationship to `toMagma`.

This was not robust, since in diamond inheritance `α` only remembered *one* of its parents in this indirect way.
-/
private def solveParentMVars (e : Expr) : StructElabM Expr := do
  let env ← getEnv
  Term.synthesizeSyntheticMVars (postpone := .yes)
  let mvars ← getMVarsNoDelayed e
  for mvar in mvars do
    unless ← mvar.isAssigned do
      let decl ← mvar.getDecl
      if decl.kind.isNatural then
        if let .const name .. := (← whnf decl.type).getAppFn then
          if isStructure env name then
            if let some parentInfo ← findParentFieldInfo? name then
              if ← isDefEq (← mvar.getType) (← inferType parentInfo.fvar) then
                discard <| MVarId.checkedAssign mvar parentInfo.fvar
  return e

open Parser.Term in
private def typelessBinder? : Syntax → Option ((Array Ident) × BinderInfo)
  | `(bracketedBinderF|($ids:ident*)) => some (ids, .default)
  | `(bracketedBinderF|{$ids:ident*}) => some (ids, .implicit)
  | `(bracketedBinderF|⦃$ids:ident*⦄)  => some (ids, .strictImplicit)
  | `(bracketedBinderF|[$id:ident])   => some (#[id], .instImplicit)
  | _                                 => none

/--
Takes a binder list and interprets the prefix to see if any could be construed to be binder info updates.
Returns the binder list without these updates along with the new binder infos for these parameters.
-/
private def elabParamInfoUpdates (structParams : Array Expr) (binders : Array Syntax) : StructElabM (Array Syntax × ExprMap (Syntax × BinderInfo)) := do
  let mut overrides : ExprMap (Syntax × BinderInfo) := {}
  for i in [0:binders.size] do
    match typelessBinder? binders[i]! with
    | none => return (binders.extract i, overrides)
    | some (ids, bi) =>
      let lctx ← getLCtx
      let decls := ids.filterMap fun id => lctx.findFromUserName? id.getId
      -- Filter out all fields. We assume the remaining fvars are the possible parameters.
      let decls ← decls.filterM fun decl => return (← findFieldInfoByFVarId? decl.fvarId).isNone
      if decls.size != ids.size then
        -- Then either these are for a new variables or the binder isn't only for parameters
        return (binders.extract i, overrides)
      for decl in decls, id in ids do
        Term.addTermInfo' id decl.toExpr
        unless structParams.contains decl.toExpr do
          throwErrorAt id m!"only parameters appearing in the declaration header may have their binders kinds be overridden\n\n\
            If this is not intended to be an override, use a binder with a type, for example '(x : _)'."
        overrides := overrides.insert decl.toExpr (id, bi)
  return (#[], overrides)

private def elabFieldTypeValue (structParams : Array Expr) (view : StructFieldView) :
    StructElabM (Option Expr × ExprMap (Syntax × BinderInfo) × Option StructFieldDefault) := do
  let state ← get
  let binders := view.binders.getArgs
  let (binders, paramInfoOverrides) ← elabParamInfoUpdates structParams binders
  Term.withAutoBoundImplicit <| Term.withAutoBoundImplicitForbiddenPred (fun n => view.name == n) <| Term.elabBinders binders fun params => do
    match view.type? with
    | none =>
      match view.default? with
      | none => return (none, paramInfoOverrides, none)
      | some (.optParam valStx) =>
        Term.synthesizeSyntheticMVarsNoPostponing
        let params ← Term.addAutoBoundImplicits params (view.nameId.getTailPos? (canonicalOnly := true))
        let value ← Term.withoutAutoBoundImplicit <| Term.elabTerm valStx none
        let value ← runStructElabM (init := state) <| solveParentMVars value
        registerFailedToInferFieldType view.name (← inferType value) view.nameId
        registerFailedToInferDefaultValue view.name value valStx
        let value ← mkLambdaFVars params value
        return (none, paramInfoOverrides, StructFieldDefault.optParam value)
      | some (.autoParam tacticStx) =>
        throwErrorAt tacticStx "invalid field declaration, type must be provided when auto-param tactic is used"
    | some typeStx =>
      let type ← Term.elabType typeStx
      let type ← runStructElabM (init := state) <| solveParentMVars type
      registerFailedToInferFieldType view.name type typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let params ← Term.addAutoBoundImplicits params (view.nameId.getTailPos? (canonicalOnly := true))
      match view.default? with
      | none =>
        let type ← mkForallFVars params type
        return (type, paramInfoOverrides, none)
      | some (.optParam valStx) =>
        let value ← Term.withoutAutoBoundImplicit <| Term.elabTermEnsuringType valStx type
        let value ← runStructElabM (init := state) <| solveParentMVars value
        registerFailedToInferDefaultValue view.name value valStx
        Term.synthesizeSyntheticMVarsNoPostponing
        let type  ← mkForallFVars params type
        let value ← mkLambdaFVars params value
        return (type, paramInfoOverrides, StructFieldDefault.optParam value)
      | some (.autoParam tacticStx) =>
        let name := mkAutoParamFnOfProjFn view.declName
        discard <| Term.declareTacticSyntax tacticStx name
        let type ← mkForallFVars params type
        return (type, paramInfoOverrides, StructFieldDefault.autoParam <| .const name [])

private partial def withFields (structParams : Array Expr) (views : Array StructFieldView) (k : StructElabM α) : StructElabM α := do
  go 0
where
  go (i : Nat) : StructElabM α := do
    if h : i < views.size then
      let view := views[i]
      withRef view.ref do
      if let some parent := (← get).parents.find? (·.name == view.name) then
        throwError "field '{view.name}' has already been declared as a projection for parent '{.ofConstName parent.structName}'"
      match ← findFieldInfo? view.name with
      | none      =>
        let (type?, paramInfoOverrides, default?) ← elabFieldTypeValue structParams view
        match type?, default? with
        | none,      none => throwError "invalid field, type expected"
        | some type, _    =>
          withLocalDecl view.rawName view.binderInfo type fun fieldFVar => do
            addFieldInfo { ref := view.nameId, sourceStructNames := [],
                           name := view.name, declName := view.declName, fvar := fieldFVar, default? := default?,
                           binfo := view.binderInfo, paramInfoOverrides,
                           kind := StructFieldKind.newField }
            go (i+1)
        | none, some (.optParam value) =>
          let type ← inferType value
          withLocalDecl view.rawName view.binderInfo type fun fieldFVar => do
            addFieldInfo { ref := view.nameId, sourceStructNames := [],
                           name := view.name, declName := view.declName, fvar := fieldFVar, default? := default?,
                           binfo := view.binderInfo, paramInfoOverrides,
                           kind := StructFieldKind.newField }
            go (i+1)
        | none, some (.autoParam _) =>
          throwError "field '{view.name}' has an autoparam but no type"
      | some info =>
        let updateDefaultValue : StructElabM α := do
          match view.default? with
          | none       => throwError "field '{view.name}' has been declared in parent structure"
          | some (.optParam valStx) =>
            if let some type := view.type? then
              throwErrorAt type "omit field '{view.name}' type to set default value"
            else
              if info.default?.isSome then
                throwError "field '{view.name}' new default value has already been set"
              let mut valStx := valStx
              let (binders, paramInfoOverrides) ← elabParamInfoUpdates structParams view.binders.getArgs
              unless paramInfoOverrides.isEmpty do
                let params := MessageData.joinSep (paramInfoOverrides.toList.map (m!"{·.1}")) ", "
                throwError "cannot override structure parameter binder kinds when overriding the default value: {params}"
              if binders.size > 0 then
                valStx ← `(fun $binders* => $valStx:term)
              let fvarType ← inferType info.fvar
              let value ← Term.elabTermEnsuringType valStx fvarType
              registerFailedToInferDefaultValue view.name value valStx
              pushInfoLeaf <| .ofFieldRedeclInfo { stx := view.ref }
              if let some projFn := info.projFn? then Term.addTermInfo' view.ref (← mkConstWithLevelParams projFn)
              replaceFieldInfo { info with ref := view.nameId, default? := StructFieldDefault.optParam value }
              go (i+1)
          | some (.autoParam tacticStx) =>
            if let some type := view.type? then
              throwErrorAt type "omit field '{view.name}' type to set auto-param tactic"
            else
              if info.default?.isSome then
                throwError "field '{view.name}' new default value has already been set"
              if view.binders.getArgs.size > 0 then
                throwErrorAt view.binders "invalid field, unexpected binders when setting auto-param tactic for inherited field"
              let name := mkAutoParamFnOfProjFn view.declName
              discard <| Term.declareTacticSyntax tacticStx name
              replaceFieldInfo { info with ref := view.nameId, default? := StructFieldDefault.autoParam (.const name []) }
              pushInfoLeaf <| .ofFieldRedeclInfo { stx := view.ref }
              if let some projFn := info.projFn? then Term.addTermInfo' view.ref (← mkConstWithLevelParams projFn)
              go (i+1)
        match info.kind with
        | StructFieldKind.newField      => throwError "field '{view.name}' has already been declared"
        | StructFieldKind.subobject n
        | StructFieldKind.otherParent n => throwError "unexpected reference to parent field '{n}'" -- improve error message
        | StructFieldKind.copiedField
        | StructFieldKind.fromSubobject => updateDefaultValue
    else
      k

private def collectUsedFVars (lctx : LocalContext) (localInsts : LocalInstances) (fieldInfos : Array StructFieldInfo) :
    StateRefT CollectFVars.State MetaM Unit := do
  withLCtx lctx localInsts do
    fieldInfos.forM fun info => do
      let fvarType ← inferType info.fvar
      fvarType.collectFVars
      if let some (.optParam value) := info.default? then
        value.collectFVars

/--
Creates a local context suitable for creating the constructor.
- Eliminates fields with a `projExpr?` field
- Eliminates non-subobject parent fields
- Adds autoParam for default values (not used by structure elaborator or structure instance elaborator)

Does not do any reductions.
-/
private def mkCtorLCtx : StructElabM LocalContext := do
  let fieldInfos := (← get).fields
  -- A map of all field fvars to eliminate
  let mut fvarMap : ExprMap Expr := {}
  let mut lctx ← instantiateLCtxMVars (← getLCtx)
  let replace (fvarMap : ExprMap Expr) (e : Expr) : Expr := e.replace fun e' => fvarMap[e']?
  -- As we build the map, we eagerly do the replacements. We go through the local context in order, so replacements do not need to be recursive.
  let insert (fvarMap : ExprMap Expr) (field : StructFieldInfo) (e : Expr) : MetaM (ExprMap Expr) := do
    let e ← instantiateMVars e
    return fvarMap.insert field.fvar (replace fvarMap e)
  for field in fieldInfos do
    let fvarId := field.fvar.fvarId!
    if !field.kind.isInCtor then
      lctx := lctx.erase fvarId
      let some e ← pure field.projExpr? <||> fvarId.getValue?
        | throwError "(mkCtorLCtx internal error) non-constructor field has no value"
      fvarMap ← insert fvarMap field e
    else
      -- Do replacements.
      -- If it is a subobject field, change the ldecl to be a cdecl
      lctx := lctx.modifyLocalDecl fvarId fun decl =>
        .cdecl decl.index decl.fvarId decl.userName (replace fvarMap decl.type) field.binfo decl.kind
      -- Add autoParams
      if let some (.autoParam tactic) := field.resolvedDefault? then
        let u ← getLevel (← inferType field.fvar)
        lctx := lctx.modifyLocalDecl fvarId fun decl => decl.setType (mkApp2 (.const ``autoParam [u]) decl.type tactic)
  return lctx

/--
Builds a constructor for the type, for adding the inductive type to the environment.
-/
private def mkCtor (view : StructView) (r : ElabHeaderResult) (params : Array Expr) : StructElabM Constructor :=
  withRef view.ref do
  let lctx ← mkCtorLCtx
  let type ← instantiateMVars <| mkAppN r.indFVar params
  let fieldInfos := (← get).fields
  let fieldCtorFVars := fieldInfos |>.filter (·.kind.isInCtor) |>.map (·.fvar)
  let type := lctx.mkForall fieldCtorFVars type
  withLCtx lctx {} do
    trace[Elab.structure] "constructor type before reductions:{indentExpr type}"
    let type ← fieldNormalizeExpr type
    trace[Elab.structure] "constructor type after reductions:{indentExpr type}"
    let type ← mkForallFVars params type
    let type ← instantiateMVars type
    let type := type.inferImplicit params.size true
    trace[Elab.structure] "full constructor type:{indentExpr type}"
    pure { name := view.ctor.declName, type }

/--
Creates an alternative constructor that takes all the fields directly.
Assumes the inductive type has already been added to the environment.

Note: we can't generally use optParams here since the default values might depend on previous ones.
We include autoParams however.
-/
private def mkFlatCtorExpr (levelParams : List Name) (params : Array Expr) (ctor : ConstructorVal) (replaceIndFVars : Expr → MetaM Expr) :
    StructElabM Expr := do
  -- build the constructor application using the fields in the local context
  let mut val := mkAppN (mkConst ctor.name (levelParams.map mkLevelParam)) params
  let fieldInfos := (← get).fields
  for fieldInfo in fieldInfos do
    if fieldInfo.kind.isInCtor then
      val := mkApp val fieldInfo.fvar
  -- zeta delta reduce the parent ldecls
  let parentFVars := fieldInfos |>.filter (·.kind.isParent) |>.map (·.fvar.fvarId!)
  val ← zetaDeltaFVars (← instantiateMVars val) parentFVars
  -- abstract all non-parent fields to make a lambda expression
  let fields' := fieldInfos |>.filter (!·.kind.isParent)
  val ← fields'.foldrM (init := val) fun fieldInfo val => do
    let decl ← fieldInfo.fvar.fvarId!.getDecl
    let type ←
      match fieldInfo.resolvedDefault? with
      | some (.autoParam tactic) => mkAppM ``autoParam #[decl.type, tactic]
      | _ => pure decl.type
    let type ← zetaDeltaFVars (← instantiateMVars type) parentFVars
    let type ← replaceIndFVars type
    return .lam decl.userName.eraseMacroScopes type (val.abstract #[fieldInfo.fvar]) decl.binderInfo
  val ← mkLambdaFVars params val
  val ← replaceIndFVars val
  fieldNormalizeExpr val

private partial def mkFlatCtor (levelParams : List Name) (params : Array Expr) (structName : Name) (replaceIndFVars : Expr → MetaM Expr) :
    StructElabM Unit := do
  let env ← getEnv
  let ctor := getStructureCtor env structName
  let val ← mkFlatCtorExpr levelParams params ctor replaceIndFVars
  withLCtx {} {} do trace[Elab.structure] "created flat constructor:{indentExpr val}"
  unless val.hasSyntheticSorry do
    -- Note: flatCtorName will be private if the constructor is private
    let flatCtorName := mkFlatCtorOfStructCtorName ctor.name
    let valType ← replaceIndFVars (← instantiateMVars (← inferType val))
    let valType := valType.inferImplicit params.size true
    addDecl <| Declaration.defnDecl (← mkDefinitionValInferrringUnsafe flatCtorName levelParams valType val .abbrev)

private partial def checkResultingUniversesForFields (fieldInfos : Array StructFieldInfo) (u : Level) : TermElabM Unit := do
  for info in fieldInfos do
    let type ← inferType info.fvar
    let v := (← instantiateLevelMVars (← getLevel type)).normalize
    unless u.geq v do
      let msg := m!"invalid universe level for field '{info.name}', has type{indentExpr type}\n\
        at universe level{indentD v}\n\
        which is not less than or equal to the structure's resulting universe level{indentD u}"
      throwErrorAt info.ref msg

private def addProjections (params : Array Expr) (r : ElabHeaderResult) (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
  let projDecls : Array StructProjDecl ←
    fieldInfos
    |>.filter (·.kind.isInCtor)
    |>.mapM (fun info => do
      info.paramInfoOverrides.forM fun p (ref, _) => do
        unless params.contains p do
          throwErrorAt ref "invalid parameter binder update, not a parameter"
      let paramInfoOverrides := params |>.map (fun param => info.paramInfoOverrides[param]?.map Prod.snd) |>.toList
      return { ref := info.ref, projName := info.declName, paramInfoOverrides })
  mkProjections r.view.declName projDecls r.view.isClass
  for fieldInfo in fieldInfos do
    if fieldInfo.kind.isSubobject then
      addDeclarationRangesFromSyntax fieldInfo.declName r.view.ref fieldInfo.ref
  for decl in projDecls do
    -- projections may generate equation theorems
    enableRealizationsForConst decl.projName

private def registerStructure (structName : Name) (infos : Array StructFieldInfo) : TermElabM Unit := do
  let fields ← infos.filterMapM fun info => do
    if info.kind.isInCtor then
      return some {
        fieldName  := info.name
        projFn     := info.declName
        binderInfo := info.binfo
        subobject? := if let .subobject parentName := info.kind then parentName else none
        autoParam? := none -- deprecated field
      }
    else
      return none
  modifyEnv fun env => Lean.registerStructure env { structName, fields }

private def checkDefaults (fieldInfos : Array StructFieldInfo) : TermElabM Unit := do
  let mut mvars := {}
  let mut lmvars := {}
  for fieldInfo in fieldInfos do
    if let some (.optParam value) := fieldInfo.resolvedDefault? then
      let value ← instantiateMVars value
      mvars := Expr.collectMVars mvars value
      lmvars := collectLevelMVars lmvars value
  -- Log errors and ignore the failure; we later will just omit adding a default value.
  if ← Term.logUnassignedUsingErrorInfos mvars.result then
    return
  else if ← Term.logUnassignedLevelMVarsUsingErrorInfos lmvars.result then
    return

/--
Computes the resolution order and for the structure and sorts the inherited defaults.
-/
private def resolveFieldDefaults (structName : Name) : StructElabM Unit := do
  -- Resolve the order, but don't report any resolution order issues at this point.
  -- We will do that in `checkResolutionOrder`, which is after the structure is registered.
  let { resolutionOrder, .. } ← mergeStructureResolutionOrders structName ((← get).parents.map (·.structName)) (relaxed := true)
  let mut resOrderMap : NameMap Nat := {}
  for h : i in [0:resolutionOrder.size] do
    resOrderMap := resOrderMap.insert resolutionOrder[i] i
  for fieldInfo in (← get).fields do
    if fieldInfo.default?.isSome then
      replaceFieldInfo { fieldInfo with resolvedDefault? := fieldInfo.default? }
    else if !fieldInfo.inheritedDefaults.isEmpty then
      let inheritedDefaults := fieldInfo.inheritedDefaults.insertionSort fun d1 d2 => resOrderMap.find! d1.1 < resOrderMap.find! d2.1
      trace[Elab.structure] "inherited defaults for '{fieldInfo.name}' are {repr inheritedDefaults}"
      replaceFieldInfo { fieldInfo with
        inheritedDefaults
        resolvedDefault? := inheritedDefaults[0]?.map (·.2)
      }

/--
Adds declarations representing default values to the environment.

- Default values introduced for this structure specifically are registered under the name given by `mkDefaultFnOfProjFn`
- Default values inherited by this structure are registered under the name given by `mkInheritedDefaultFnOfProjFn`

Having both is how we are able to handle diamond inheritance of default values.
When a `structure` extends other structures, only the first type of default values are considered.

In both cases, the default values take the fields as arguments, and everything is suitably normalized.
It used to be that subobject fields would appear as fields too, but that required
the structure instance notation elaborator to do reductions when making use of default values.
This arrangement of having declarations for all inherited values also makes
the structure instance notation delaborator able to omit default values reliably.
-/
private def addDefaults (levelParams : List Name) (params : Array Expr) (replaceIndFVars : Expr → MetaM Expr) : StructElabM Unit := do
  let fieldInfos := (← get).fields
  let lctx ← instantiateLCtxMVars (← getLCtx)
  /- The parameters `params` for the auxiliary "default value" definitions must be marked as implicit, and all others as explicit. -/
  let lctx := params.foldl (init := lctx) fun (lctx : LocalContext) (p : Expr) =>
    lctx.setBinderInfo p.fvarId! BinderInfo.implicit
  let parentFVarIds := fieldInfos |>.filter (·.kind.isParent) |>.map (·.fvar.fvarId!)
  let fields := fieldInfos |>.filter (!·.kind.isParent)
  withLCtx lctx (← getLocalInstances) do
    let addDefault (declName : Name) (value : Expr) : StructElabM Unit := do
      let value ← instantiateMVars value
      -- If there are mvars, `checkDefaults` already logged an error.
      unless value.hasMVar || value.hasSyntheticSorry do
        /- The identity function is used as "marker". -/
        let value ← mkId value
        let value ← zetaDeltaFVars value parentFVarIds
        let value ← fields.foldrM (init := value) fun fieldInfo val => do
          let decl ← fieldInfo.fvar.fvarId!.getDecl
          let type ← zetaDeltaFVars decl.type parentFVarIds
          let val' := val.abstract #[fieldInfo.fvar]
          if val'.hasLooseBVar 0 then
            return .lam decl.userName type val' .default
          else
            return val
        let value ← mkLambdaFVars params value
        let value ← fieldNormalizeExpr value
        let value ← replaceIndFVars value
        withLCtx {} {} do trace[Elab.structure] "default value after abstraction:{indentExpr value}"
        if value.hasFVar then withLCtx {} {} <| logError m!"(internal error) default value contains fvars{indentD value}"
        let type ← inferType value
        -- No need to compile the definition, since it is only used during elaboration.
        addDecl <| Declaration.defnDecl
          (← mkDefinitionValInferrringUnsafe declName levelParams type value ReducibilityHints.abbrev)
    for fieldInfo in fieldInfos do
      if let some (.optParam value) := fieldInfo.default? then
        addDefault (mkDefaultFnOfProjFn fieldInfo.declName) value
      else if let some (.optParam value) := fieldInfo.resolvedDefault? then
        addDefault (mkInheritedDefaultFnOfProjFn fieldInfo.declName) value

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
private partial def mkCoercionToCopiedParent (levelParams : List Name) (params : Array Expr) (view : StructView) (source : Expr) (parent : StructParentInfo) (parentType parentVal : Expr) : MetaM StructureParentInfo := do
  let isProp ← Meta.isProp parentType
  let env ← getEnv
  let binfo := if view.isClass && isClass env parent.structName then BinderInfo.instImplicit else BinderInfo.default
  let mut declType ← instantiateMVars (← mkForallFVars params (← mkForallFVars #[source] parentType))
  if view.isClass && isClass env parent.structName then
    declType := setSourceInstImplicit declType
  declType := declType.inferImplicit params.size true
  let declVal ← instantiateMVars (← mkLambdaFVars params (← mkLambdaFVars #[source] parentVal))
  let declName := parent.declName
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
  addDeclarationRangesFromSyntax declName view.ref parent.ref
  return { structName := parent.structName, subobject := false, projFn := declName }

/--
Make projections to parents that are not represented as subobjects.

All other projections we get indirectly from the elaborator, which can construct projections by chaining subobject projections.
-/
private def mkRemainingProjections (levelParams : List Name) (params : Array Expr) (view : StructView) : StructElabM (Array StructureParentInfo) := do
  let us := levelParams.map mkLevelParam
  let structType := mkAppN (Lean.mkConst view.declName us) params
  withLocalDeclD `self structType fun source => do
    /-
    Remark: copied parents might still be referring to the fvars of other parents. We need to replace these fvars with projection constants.
    For subobject parents, this has already been done by `mkProjections`.
    https://github.com/leanprover/lean4/issues/2611
    -/
    let mut fvarToConst : ExprMap Expr := {}
    -- First add all constructor projections to `fvarToConst`
    for field in (← get).fields do
      if field.kind.isInCtor then
        fvarToConst := fvarToConst.insert field.fvar <| mkApp (mkAppN (.const field.declName us) params) source
    -- Then add remaining fields to `fvarToConst`
    for field in (← get).fields do
      if !field.kind.isInCtor then
        if let some val ← pure field.projExpr? <||> field.fvar.fvarId!.getValue? then
          let val ← instantiateMVars val
          let val := val.replace (fvarToConst[·]?)
          -- No need to zeta delta reduce; `fvarToConst` has replaced such fvars.
          let val ← fieldNormalizeExpr val (zetaDelta := false)
          fvarToConst := fvarToConst.insert field.fvar val
          -- TODO(kmill): if it is a direct parent, try adding the coercion function from the environment and use that instead of `val`.
          -- (This should be evaluated to see if it is a good idea.)
        else
          throwError m!"(mkRemainingProjections internal error) {field.name} has no value"

    let mut parentInfos := #[]
    for parent in (← get).parents do
      if parent.subobject then
        let some info ← findParentFieldInfo? parent.structName | unreachable!
        parentInfos := parentInfos.push { structName := parent.structName, subobject := true, projFn := info.declName }
      else
        let parent_type := (← instantiateMVars (← inferType parent.fvar)).replace (fvarToConst[·]?)
        let parent_type ← fieldNormalizeExpr parent_type (zetaDelta := false)
        let parent_value := fvarToConst[parent.fvar]!
        let parentInfo ← mkCoercionToCopiedParent levelParams params view source parent parent_type parent_value
        parentInfos := parentInfos.push parentInfo
    return parentInfos

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
      elabCtors := fun rs r params => runStructElabM do
        withParents view rs r.indFVar do
        withFields params view.fields do
        withRef view.ref do
          Term.synthesizeSyntheticMVarsNoPostponing
          resolveFieldDefaults view.declName
          let state ← get
          let parents := state.parents
          let fieldInfos := state.fields
          let lctx ← getLCtx
          let localInsts ← getLocalInstances
          let ctor ← mkCtor view r params
          return {
            ctors := [ctor]
            collectUsedFVars := collectUsedFVars lctx localInsts fieldInfos
            checkUniverses := fun _ u => withLCtx lctx localInsts do checkResultingUniversesForFields fieldInfos u
            finalizeTermElab := withLCtx lctx localInsts do checkDefaults fieldInfos
            prefinalize := fun levelParams params replaceIndFVars => do
              withLCtx lctx localInsts do
                addProjections params r fieldInfos
                registerStructure view.declName fieldInfos
                runStructElabM (init := state) do
                  mkFlatCtor levelParams params view.declName replaceIndFVars
                  addDefaults levelParams params replaceIndFVars
              let parentInfos ← withLCtx lctx localInsts <| runStructElabM (init := state) do
                mkRemainingProjections levelParams params view
              setStructureParents view.declName parentInfos
              withSaveInfoContext do  -- save new env
                for field in view.fields do
                  -- may not exist if overriding inherited field
                  if (← getEnv).contains field.declName then
                    Term.addTermInfo' field.ref (← mkConstWithLevelParams field.declName) (isBinder := true)
                -- Add terminfo for parents now that all parent projections exist.
                for parent in parents do
                  if parent.addTermInfo then
                    Term.addTermInfo' parent.ref (← mkConstWithLevelParams parent.declName) (isBinder := true)
              checkResolutionOrder view.declName
              return {
                finalize := do
                  if view.isClass then
                    addParentInstances parentInfos
              }
          }
    }

end Lean.Elab.Command.Structure
