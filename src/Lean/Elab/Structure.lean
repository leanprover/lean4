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
  value?     : Option Syntax

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
  /-- The field represents a parent projection for a parent that is not embedded as a subobject.
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
  /--
  Structure names that are responsible for this field being here.
  - Empty if the field is a `newField`.
  - Otherwise, it is a stack with the last element being a parent in the `extends` clause.
  -/
  sourceStructNames : List Name
  /-- All fields (both real fields and parent projection fields) get a local variable.
  Parent fields are ldecls constructed from "actual" fields. -/
  fvar     : Expr
  /--
  The fvar to use for this field when making the constructor (if any).
  - For `.newField` and `.copiedField` fields, this is `fvar`.
  - For `.subobject` fields, this is an `.implDetail` fvar that comes before all the `.fromSubobject` field fvars.
  -/
  ctorFVar? : Option Expr
  /-- An expression representing a `.fromSubobject` field as a projection of a `.subobject` field.
  Used when putting expressions into "constructor-normal form". -/
  projExpr? : Option Expr := none
  /-- The default value, as explicitly given in this `structure`. -/
  value?   : Option Expr := none
  deriving Inhabited, Repr

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

-- /--
-- Puts an expression into "field normal form".
-- This means unfolding parent fvars and reducing projections that are applied to constructors.
-- -/
-- private def fieldNormalForm (e : Expr) : StructElabM Expr := withReducible <| do
--   let e ← instantiateMVars e
--   let parentFVars := (← get).fields |>.filter (·.kind.isParent) |>.map (·.fvar.fvarId!)
--   let e ← zetaDeltaFVars e parentFVars
--   let postVisit (e : Expr) : StructElabM TransformStep := do
--     if let Expr.const projName .. := e.getAppFn then
--       if let some projInfo ← getProjectionFnInfo? projName then
--         let ConstantInfo.ctorInfo cval := (← getEnv).find? projInfo.ctorName | unreachable!
--         if (← findParentFieldInfo? cval.induct).isSome then
--           let args := e.getAppArgs
--           if let some major := args[projInfo.numParams]? then
--             if major.isAppOf projInfo.ctorName then
--               if let some arg := args[projInfo.numParams + projInfo.i]? then
--                 return TransformStep.done <| mkAppN arg args[projInfo.numParams+1:]
--     return TransformStep.continue
--   Meta.transform e (post := postVisit)

/--
Reduces projections applied to constructors or parent fvars, for structure types that have appeared as parents.
-/
private def reduceFieldProjs (e : Expr) : StructElabM Expr := do
  let e ← instantiateMVars e
  let postVisit (e : Expr) : StructElabM TransformStep := do
    if let Expr.const projName .. := e.getAppFn then
      if let some projInfo ← getProjectionFnInfo? projName then
        let ConstantInfo.ctorInfo cval := (← getEnv).find? projInfo.ctorName | unreachable!
        if let some info ← findParentFieldInfo? cval.induct then
          let args := e.getAppArgs
          if let some major := args[projInfo.numParams]? then
            let major ←
              if major == info.fvar then
                pure <| (← major.fvarId!.getValue?).getD major
              else
                pure major
            if major.isAppOfArity projInfo.ctorName (cval.numParams + cval.numFields) then
              if let some arg := major.getAppArgs[projInfo.numParams + projInfo.i]? then
                return TransformStep.visit <| mkAppN arg args[projInfo.numParams+1:]
    return TransformStep.continue
  Meta.transform e (post := postVisit)

/-- Given an expression that's either a native projection or a registered projection
function, gives (1) the name of the structure type, (2) the index of the projection, and
(3) the object being projected. -/
private def getProjectedExpr (e : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  if let .proj S i x := e then
    return (S, i, x)
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? info.ctorName then
          return (fVal.induct, info.i, e.appArg!)
  return none

/-- Checks if the expression is of the form `S.mk x.1 ... x.n` with `n` nonzero
and `S.mk` a structure constructor with `S` one of the recorded structure parents.
Returns `x`.
Each projection `x.i` can be either a native projection or from a projection function. -/
private def etaStruct? (e : Expr) : StructElabM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? f | return none
  unless (← findParentFieldInfo? fVal.induct).isSome do return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  let args := e.getAppArgs
  let some (S0, i0, x) ← getProjectedExpr args[fVal.numParams]! | return none
  unless S0 == fVal.induct && i0 == 0 do return none
  for i in [1 : fVal.numFields] do
    let arg := args[fVal.numParams + i]!
    let some (S', i', x') ← getProjectedExpr arg | return none
    unless S' == fVal.induct && i' == i && x' == x do return none
  return x

/-- Runs `etaStruct?` over the whole expression. -/
private def etaStructReduce (e : Expr) : StructElabM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (post := fun e => do
    if let some e ← etaStruct? e then
      return .done e
    else
      return .continue)

-- /--
-- Puts an expression into "constructor normal form".
-- This means
-- 1. unfolding non-subobject parents (`.otherParent`s)
-- 2. replacing `.fromSubobject` fields with their recorded projections.
-- 3. eta unexpanding parent structures
-- -/
-- private def constructorNormalForm (e : Expr) : StructElabM Expr := withReducible <| do
--   let e ← instantiateMVars e
--   let otherParentFVars : FVarIdSet := (← get).fields |>.foldl (init := {}) fun set info =>
--     if info.kind matches .otherParent _ then set.insert info.fvar.fvarId! else set
--   -- Unfold non-subobject parents and replace `.fromSubobject` fields with their projections.
--   let preVisit (e : Expr) : StructElabM TransformStep := do
--     if let .fvar fvarId := e then
--       if otherParentFVars.contains fvarId then
--         return .visit (← fvarId.getValue?).get!
--       else if let some info ← findFieldInfoByFVarId? fvarId then
--         if let some proj := info.proj? then
--           return .visit proj
--     return .continue
--   let e ← Meta.transform e (pre := preVisit)
--   -- Eta unexpand parent structures
--   Meta.transform e (post := fun e => do
--     if let some e ← etaStruct? e then
--       return .done e
--     else
--       return .continue)

-- /--
-- Returns a list of local decls that have been modified to be in constructor form.
-- All constructor fields are cdecls, and they come first,
-- and the remaining decls are ldecls for just the non-subobject direct parents.
-- -/
-- private def getConstructorFieldLocalDecls : StructElabM (List LocalDecl) := do
--   let mut ctorDecls := #[]
--   let mut otherDecls := #[]
--   for info in (← get).fields do
--     let type ← constructorNormalForm (← inferType info.fvar)
--     if info.kind.isInCtor then
--       ctorDecls := ctorDecls.push <| LocalDecl.cdecl 0 info.fvar.fvarId! info.name type info.binfo LocalDeclKind.default
--     else if info.kind.isParent && (← get).parents.any fun parent => parent.fvar == info.fvar then
--       let decl ← info.fvar.fvarId!.getDecl
--       let value ← constructorNormalForm decl.value
--       let decl := decl |>.setUserName info.declName |>.setType type |>.setValue value
--       otherDecls := otherDecls.push decl
--   return (ctorDecls ++ otherDecls).toList

--def mkLCtxForConstructor

private def fieldFromMsg (info : StructFieldInfo) : MessageData :=
  if let some sourceStructName := info.sourceStructNames.head? then
    m!"field '{info.name}' from '{.ofConstName sourceStructName}'"
  else
    m!"field '{info.name}'"

mutual

/--
Adds all the fields from `structType` along with its parent projection fields.
- if `inSubobject` is true, then the fields are marked `.fromSubobject`
- the continuation `k` is run with a constructor expression for this structure
-/
private partial def withStructFields (view : StructView) (sourceStructNames : List Name)
    (structType : Expr) (inSubobject : Bool)
    (k : Expr → StructElabM α) : StructElabM α := do
  let structName ← getStructureName structType
  let .const _ us := structType.getAppFn | unreachable!
  let params := structType.getAppArgs

  let env ← getEnv
  let fields := getStructureFields env structName
  let parentInfos := getStructureParentInfo env structName

  let ctorVal := getStructureCtor env structName
  let ctor := mkAppN (mkConst ctorVal.name us) params
  let (args, _, _) ← forallMetaTelescope (← inferType ctor)
  assert! args.size == fields.size

  let rec goFields (i : Nat) : StructElabM α := do
    if h : i < fields.size then
      let fieldName := fields[i]
      let arg := args[i]!
      let fieldType ← inferType arg
      let some fieldInfo := getFieldInfo? env structName fieldName | unreachable!
      if let some subStructName := fieldInfo.subobject? then
        -- It's a subobject field, add it and its fields
        withStruct view (structName :: sourceStructNames) (binfo := fieldInfo.binderInfo)
            fieldName fieldType inSubobject fun info => do
          arg.mvarId!.assign info.fvar
          goFields (i + 1)
      else if let some existingField ← findFieldInfo? fieldName then
        -- It's a pre-existing field, make sure it is compatible (unless diamonds are not allowed)
        if structureDiamondWarning.get (← getOptions) then
          logWarning m!"{fieldFromMsg existingField} has already been declared"
        let existingFieldType ← inferType existingField.fvar
        unless (← isDefEq fieldType existingFieldType) do
          throwError "field type mismatch, field '{fieldName}' from parent '{.ofConstName structName}' {← mkHasTypeButIsExpectedMsg fieldType existingFieldType}"
        arg.mvarId!.assign existingField.fvar
        goFields (i + 1)
      else
        -- It's a not-yet-seen field
        /- For `.fromSubobject`, the following `declName` is only used for creating the `_default` auxiliary declaration name when
           its default value is overwritten in the structure. If the default value is not overwritten, then the `declName` is irrelevant. -/
        let declName := view.declName ++ fieldName
        checkNotAlreadyDeclared declName
        withLocalDecl fieldName fieldInfo.binderInfo (← reduceFieldProjs fieldType) fun fieldFVar => do
          addFieldInfo {
            ref := (← getRef)
            sourceStructNames := structName :: sourceStructNames
            name := fieldName
            declName
            kind := if inSubobject then .fromSubobject else .copiedField
            fvar := fieldFVar
            ctorFVar? := if inSubobject then none else fieldFVar
            binfo := fieldInfo.binderInfo
          }
          arg.mvarId!.assign fieldFVar
          goFields (i + 1)
    else
      k <| ← instantiateMVars <| mkAppN ctor args

  goFields 0

private partial def withStruct (view : StructView) (sourceStructNames : List Name) (binfo : BinderInfo)
    (structFieldName : Name)
    (structType : Expr) (inSubobject : Bool)
    (k : StructFieldInfo → StructElabM α)
    (rawStructFieldName := structFieldName) (projRef := Syntax.missing) :
    StructElabM α := do
  let env ← getEnv
  let structType ← reduceFieldProjs (← whnf structType)
  let structName ← getStructureName structType
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
    throwErrorAt projRef "expecting '{structFieldName}' to match {fieldFromMsg info} for parent '{.ofConstName structName}'\n\n\
      The 'toParent : P' syntax can be used to adjust the name for the parent projection"
  else
    -- Main case: there is no field named `structFieldName` and there is no field for the structure `structName`.

    let projDeclName := view.declName ++ structFieldName
    withRef projRef do checkNotAlreadyDeclared projDeclName

    -- If we are currently in a subobject, then we shouldn't use a subobject to represent this struct.
    -- If we're not in a subobject, then check to see if any of the fields overlap with existing fields; if so, we can't use a subobject.
    -- We also don't use subobjects for structures with no fields.
    let mut useSubobject := !inSubobject
    if useSubobject then
      let allFields := getStructureFieldsFlattened env structName (includeSubobjectFields := false)
      useSubobject := !allFields.isEmpty && !(← allFields.anyM hasFieldName)

    if useSubobject then
      /- The implDetail fvar is used for the constructor field.
         It comes first so that it is easy to reduce other fields to be in terms of it. -/
      withLocalDecl (← mkFreshUserName structFieldName) binfo structType (kind := .implDetail) fun structFVar' => do
        /- Then we add all the fields of the structure. -/
        withStructFields view sourceStructNames structType (inSubobject := true) fun structVal => do
          /- And lastly we add an ldecl for the parent in terms of those fields. -/
          withLetDecl rawStructFieldName structType structVal fun structFVar => do
            let info : StructFieldInfo := {
              ref := (← getRef)
              sourceStructNames := sourceStructNames
              name := structFieldName
              declName := projDeclName
              fvar := structFVar
              ctorFVar? := structFVar'
              binfo := binfo
              kind := .subobject structName
            }
            addFieldInfo info
            -- Update `.fromSubobject` fields that don't have projections yet, using the implDetail fvar
            let .const _ us := structType.getAppFn | unreachable!
            for fieldName in getStructureFields env structName do
              let some fieldInfo ← findFieldInfo? fieldName | unreachable!
              if fieldInfo.kind.isFromSubobject then
                let some projFn := getProjFnForField? env structName fieldName | unreachable!
                let params := structType.getAppArgs
                let proj := mkApp (mkAppN (.const projFn us) params) structFVar'
                replaceFieldInfo { fieldInfo with projExpr? := proj }
            k info
    else
      withStructFields view sourceStructNames structType (inSubobject := inSubobject) fun structVal => do
        let structVal ← reduceFieldProjs structVal
        withLetDecl rawStructFieldName structType structVal fun structFVar => do
          let info : StructFieldInfo := {
            ref := (← getRef)
            sourceStructNames := sourceStructNames
            name := structFieldName
            declName := projDeclName
            fvar := structFVar
            ctorFVar? := none
            binfo := binfo
            kind := .otherParent structName
          }
          addFieldInfo info
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
  withStruct view [] (projRef := projRef) (rawStructFieldName := rawStructFieldName)
    (binfo := binfo) (inSubobject := false) structFieldName structType k

-- /-- Return `some fieldName` if field `fieldName` of the parent structure `parentStructName` is already in `infos` -/
-- private def findExistingField? (parentStructName : Name) : StructElabM (Option Name) := do
--   let infos := (← get).fields
--   -- Check if `parentStructName` is represented as a subobject field.
--   if let some info := infos.find? (·.kind == .subobject parentStructName) then
--     return info.name
--   -- Otherwise check for field overlap.
--   let fieldNames := getStructureFieldsFlattened (← getEnv) parentStructName
--   for fieldName in fieldNames do
--     if ← hasFieldName fieldName then
--       return some fieldName
--   return none

-- private def processSubfields (structDeclName : Name) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
--     (k : StructElabM α) : StructElabM α :=
--   go 0
-- where
--   go (i : Nat) : StructElabM α := do
--     if h : i < subfieldNames.size then
--       let subfieldName := subfieldNames[i]
--       if ← hasFieldName subfieldName then
--         throwError "field '{subfieldName}' from '{.ofConstName parentStructName}' has already been declared"
--       let val  ← mkProjection parentFVar subfieldName
--       let type ← inferType val
--       withLetDecl subfieldName type val fun subfieldFVar => do
--         /- The following `declName` is only used for creating the `_default` auxiliary declaration name when
--            its default value is overwritten in the structure. If the default value is not overwritten, then the `declName` is irrelevant. -/
--         let declName := structDeclName ++ subfieldName
--         addFieldInfo {
--           ref := (← getRef)
--           name := subfieldName
--           declName
--           fvar := subfieldFVar
--           kind := StructFieldKind.fromSubobject
--           sourceStructNames := [parentStructName]
--         }
--         go (i+1)
--     else
--       k

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
private def getFieldType (parentType : Expr) (fieldName : Name) : StructElabM Expr := do
  withLocalDeclD (← mkFreshId) parentType fun parent => do
    let proj ← mkProjection parent fieldName
    let projType ← inferType proj
    /- Eliminate occurrences of `parent.field`. This happens when the structure contains dependent fields.
    If the copied parent extended another structure via a subobject,
    then the occurrence can also look like `parent.toGrandparent.field`
    (where `toGrandparent` is not a field of the current structure). -/
    let visit (e : Expr) : StructElabM TransformStep := do
      if let Expr.const subProjName .. := e.getAppFn then
        if let some { numParams, .. } ← getProjectionFnInfo? subProjName then
          let Name.str _ subFieldName .. := subProjName
            | throwError "invalid projection name {subProjName}"
          let args := e.getAppArgs
          if let some major := args[numParams]? then
            if (← getNestedProjectionArg major) == parent then
              if let some existingFieldInfo ← findFieldInfo? (.mkSimple subFieldName) then
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

/-- Map from field name to expression representing the field. -/
abbrev FieldMap := NameMap Expr

/-- Reduce projections of the structures in `structNames` -/
private def reduceProjs (e : Expr) (structNames : NameSet) : MetaM Expr :=
  let reduce (e : Expr) : MetaM TransformStep := do
    match (← reduceProjOf? e structNames.contains) with
    | some v => return TransformStep.done v
    | _ => return TransformStep.done e
  transform e (post := reduce)

/--
Copies the default value for field `fieldName` set at structure `structName`.
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
private partial def copyDefaultValue? (fieldMap : FieldMap) (expandedStructNames : NameSet) (structName : Name) (fieldName : Name) :
    TermElabM (Option Expr) := do
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

-- private partial def copyNewFieldsFrom (structDeclName : Name) (parentType : Expr) (k : StructElabM α) : StructElabM α := do
--   copyFields {} parentType fun _ _ => k
-- where
--   copyFields (expandedStructNames : NameSet) (parentType : Expr) (k : FieldMap → NameSet → StructElabM α) : StructElabM α := do
--     let parentStructName ← getStructureName parentType
--     let fieldNames := getStructureFields (← getEnv) parentStructName
--     let rec copy (i : Nat) (fieldMap : FieldMap) (expandedStructNames : NameSet) : StructElabM α := do
--       if h : i < fieldNames.size then
--         let fieldName := fieldNames[i]
--         let fieldType ← getFieldType parentType fieldName
--         match ← findFieldInfo? fieldName with
--         | some existingFieldInfo =>
--           -- TODO: make sure parent projections are checked too
--           let existingFieldType ← inferType existingFieldInfo.fvar
--           unless (← isDefEq fieldType existingFieldType) do
--             throwError "parent field type mismatch, field '{fieldName}' from parent '{.ofConstName parentStructName}' {← mkHasTypeButIsExpectedMsg fieldType existingFieldType}"
--           /- Remark: if structure has a default value for this field, it will be set at the `processOveriddenDefaultValues` below. -/
--           copy (i+1) (fieldMap.insert fieldName existingFieldInfo.fvar) expandedStructNames
--         | none =>
--           let some fieldInfo := getFieldInfo? (← getEnv) parentStructName fieldName | unreachable!
--           if let some fieldParentStructName := fieldInfo.subobject? then
--             if (← findExistingField? fieldParentStructName).isSome then
--               -- See comment at `copyDefaultValue?`
--               let expandedStructNames := expandedStructNames.insert fieldParentStructName
--               copyFields expandedStructNames fieldType fun nestedFieldMap expandedStructNames => do
--                 let fieldVal ← mkCompositeField fieldType nestedFieldMap
--                 copy (i+1) (fieldMap.insert fieldName fieldVal) expandedStructNames
--             else
--               let subfieldNames := getStructureFieldsFlattened (← getEnv) fieldParentStructName
--               let fieldName := fieldInfo.fieldName
--               -- This error should never happen:
--               if let some info := (← get).fields.find? (·.kind == .subobject fieldParentStructName) then
--                 throwError "projection field name conflict, ancestor '{.ofConstName fieldParentStructName}' \
--                   has projection fields '{info.name}' and '{fieldName}'"
--               withLocalDecl fieldName fieldInfo.binderInfo fieldType fun parentFVar => do
--                 addFieldInfo { ref := (← getRef), sourceStructName? := parentStructName,
--                                name := fieldName, declName := structDeclName ++ fieldName, fvar := parentFVar,
--                                kind := StructFieldKind.subobject fieldParentStructName }
--                 processSubfields structDeclName parentFVar fieldParentStructName subfieldNames do
--                   copy (i+1) (fieldMap.insert fieldName parentFVar) expandedStructNames
--           else
--             withLocalDecl fieldName fieldInfo.binderInfo fieldType fun fieldFVar => do
--               let fieldMap := fieldMap.insert fieldName fieldFVar
--               let value? ← copyDefaultValue? fieldMap expandedStructNames parentStructName fieldName
--               let fieldDeclName := structDeclName ++ fieldName
--               let fieldDeclName ← applyVisibility (← toVisibility fieldInfo) fieldDeclName
--               addDocString' fieldDeclName (← findDocString? (← getEnv) fieldInfo.projFn)
--               addFieldInfo { ref := (← getRef), sourceStructName? := parentStructName,
--                              name := fieldName, declName := fieldDeclName, fvar := fieldFVar, value?,
--                              kind := StructFieldKind.copiedField }
--               copy (i+1) fieldMap expandedStructNames
--       else
--         processOveriddenDefaultValues fieldMap expandedStructNames parentStructName
--         k fieldMap expandedStructNames
--     copy 0 {} expandedStructNames

--   processOveriddenDefaultValues (fieldMap : FieldMap) (expandedStructNames : NameSet) (parentStructName : Name) : StructElabM Unit :=
--     for info in (← get).fields do
--       if let some value ← copyDefaultValue? fieldMap expandedStructNames parentStructName info.name then
--         replaceFieldInfo { info with value? := value }

--   mkCompositeField (parentType : Expr) (fieldMap : FieldMap) : TermElabM Expr := do
--     let env ← getEnv
--     let Expr.const parentStructName us ← pure parentType.getAppFn | unreachable!
--     let parentCtor := getStructureCtor env parentStructName
--     let mut result := mkAppN (mkConst parentCtor.name us) parentType.getAppArgs
--     for fieldName in getStructureFields env parentStructName do
--       match fieldMap.find? fieldName with
--       | some val => result := mkApp result val
--       | none => throwError "failed to copy fields from parent structure{indentExpr parentType}" -- TODO improve error message
--     return result

def mkToParentName (parentStructName : Name) : Name :=
  Name.mkSimple <| "to" ++ parentStructName.eraseMacroScopes.getString!

private def StructParentView.mkToParentNames (parentView : StructParentView) (parentStructName : Name) : Name × Name :=
  match parentView.rawName?, parentView.name? with
  | some rawName, some name => (rawName, name)
  | _, _ => Id.run do
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
      let parentType ← whnf <| ← Term.withoutAutoBoundImplicit <| Term.elabType parentView.type
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

private def elabFieldTypeValue (view : StructFieldView) : TermElabM (Option Expr × Option Expr) :=
  Term.withAutoBoundImplicit <| Term.withAutoBoundImplicitForbiddenPred (fun n => view.name == n) <| Term.elabBinders view.binders.getArgs fun params => do
    match view.type? with
    | none         =>
      match view.value? with
      | none        => return (none, none)
      | some valStx =>
        Term.synthesizeSyntheticMVarsNoPostponing
        -- TODO: add forbidden predicate using `shortDeclName` from `view`
        let params ← Term.addAutoBoundImplicits params (view.nameId.getTailPos? (canonicalOnly := true))
        let value ← Term.withoutAutoBoundImplicit <| Term.elabTerm valStx none
        registerFailedToInferFieldType view.name (← inferType value) view.nameId
        registerFailedToInferDefaultValue view.name value valStx
        let value ← mkLambdaFVars params value
        return (none, value)
    | some typeStx =>
      let type ← Term.elabType typeStx
      registerFailedToInferFieldType view.name type typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let params ← Term.addAutoBoundImplicits params (view.nameId.getTailPos? (canonicalOnly := true))
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

private partial def withFields (views : Array StructFieldView) (k : StructElabM α) : StructElabM α := do
  go 0 {}
where
  go (i : Nat) (defaultValsOverridden : NameSet) : StructElabM α := do
    if h : i < views.size then
      let view := views[i]
      withRef view.ref do
      if let some parent := (← get).parents.find? (·.name == view.name) then
        throwError "field '{view.name}' has already been declared as a projection for parent '{.ofConstName parent.structName}'"
      match ← findFieldInfo? view.name with
      | none      =>
        let (type?, value?) ← elabFieldTypeValue view
        match type?, value? with
        | none,      none => throwError "invalid field, type expected"
        | some type, _    =>
          withLocalDecl view.rawName view.binderInfo type fun fieldFVar => do
            addFieldInfo { ref := view.nameId, sourceStructNames := [],
                           name := view.name, declName := view.declName, fvar := fieldFVar, ctorFVar? := fieldFVar, value? := value?,
                           binfo := view.binderInfo,
                           kind := StructFieldKind.newField }
            go (i+1) defaultValsOverridden
        | none, some value =>
          let type ← inferType value
          withLocalDecl view.rawName view.binderInfo type fun fieldFVar => do
            addFieldInfo { ref := view.nameId, sourceStructNames := [],
                           name := view.name, declName := view.declName, fvar := fieldFVar, ctorFVar? := fieldFVar, value? := value,
                           binfo := view.binderInfo,
                           kind := StructFieldKind.newField }
            go (i+1) defaultValsOverridden
      | some info =>
        let updateDefaultValue : StructElabM α := do
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
              replaceFieldInfo { info with ref := view.nameId, value? := value }
              go (i+1) defaultValsOverridden
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
      if let some value := info.value? then
        value.collectFVars

private def eliminateNonFields (e : Expr) : StructElabM Expr := do
  let fieldInfos := (← get).fields
  let rec go : Nat → Expr → StructElabM Expr
    | 0,   type => pure type
    | i+1, type => do
      let info := fieldInfos[i]!
      if let some value ← info.fvar.fvarId!.getValue? then
        go i <| type.replaceFVar info.fvar (← instantiateMVars value)
      else if let some value := info.projExpr? then
        go i <| type.replaceFVar info.fvar (← instantiateMVars value)
      else
        go i type
  go fieldInfos.size (← instantiateMVars e)

private def mkCtor (view : StructView) (r : ElabHeaderResult) (params : Array Expr) : StructElabM Constructor :=
  withRef view.ref do
  let type ← instantiateMVars <| mkAppN r.indFVar params
  let fieldInfos := (← get).fields
  let type ← eliminateNonFields type
  let type ← addCtorFields fieldInfos fieldInfos.size type
  let type ← etaStructReduce type
  -- let ctorFieldFVars := fieldInfos |>.filter (·.kind.isInCtor) |>.map (·.fvar)
  -- let type ← mkForallFVars ctorFieldFVars type
  let type ← mkForallFVars params type
  let type ← instantiateMVars type
  let type := type.inferImplicit params.size true
  trace[Elab.structure] "constructor type:{indentExpr type}"
  pure { name := view.ctor.declName, type }
where
  addCtorFields (fieldInfos : Array StructFieldInfo) : Nat → Expr → StructElabM Expr
  | 0,   type => pure type
  | i+1, type => do
    let info := fieldInfos[i]!
    if let some fvar := info.ctorFVar? then
      unless fvar.isFVar do
        logInfo m!"should be fvar for {info.name}, but it's {fvar}\n{info.ctorFVar?}\n{info.fvar}"
      assert! fvar.isFVar
      let decl ← fvar.fvarId!.getDecl
      let type := type.abstract #[info.fvar]
      addCtorFields fieldInfos i <| mkForall info.name info.binfo (← instantiateMVars decl.type) type
    else
      addCtorFields fieldInfos i type

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
  let projNames := fieldInfos |>.filter (·.kind.isInCtor) |>.map (·.declName)
  let env ← getEnv
  let env ← ofExceptKernelException (mkProjections env r.view.declName projNames.toList r.view.isClass)
  setEnv env
  for fieldInfo in fieldInfos do
    if fieldInfo.kind.isSubobject then
      addDeclarationRangesFromSyntax fieldInfo.declName r.view.ref fieldInfo.ref
  for n in projNames do
    -- projections may generate equation theorems
    enableRealizationsForConst n

private def registerStructure (structName : Name) (infos : Array StructFieldInfo) : TermElabM Unit := do
  let fields ← infos.filterMapM fun info => do
    if info.kind == StructFieldKind.fromSubobject then
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
      if info.kind.isFromSubobject then lctx
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
private partial def mkCoercionToCopiedParent (levelParams : List Name) (params : Array Expr) (view : StructView) (source : Expr) (parent : StructParentInfo) (parentType parentVal : Expr) : MetaM StructureParentInfo := do
  let isProp ← Meta.isProp parentType
  let env ← getEnv
  let binfo := if view.isClass && isClass env parent.structName then BinderInfo.instImplicit else BinderInfo.default
  let mut declType ← instantiateMVars (← mkForallFVars params (← mkForallFVars #[source] parentType))
  if view.isClass && isClass env parent.structName then
    declType := setSourceInstImplicit declType
  declType := declType.inferImplicit params.size true
  let declVal ← instantiateMVars (← mkLambdaFVars params (← mkLambdaFVars #[source] parentVal))
  logInfo m!"adding projection {parent.declName} with type{indentD declType}\nand value{indentD declVal}"
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
    for field in (← get).fields do
      if let some fvar := field.ctorFVar? then
        unless fvar.isFVar do
          logInfo m!"should be fvar for {field.name}, but it's {fvar}\n{field.ctorFVar?}\n{field.fvar}"
        fvarToConst := fvarToConst.insert fvar <| mkApp (mkAppN (.const field.declName us) params) source
    logInfo m!"{fvarToConst.keys}"
    (← get).parents.mapM fun parent => do
        if parent.subobject then
          let some info ← findParentFieldInfo? parent.structName | unreachable!
          pure { structName := parent.structName, subobject := true, projFn := info.declName }
        else
          logInfo m!"{parent.name}. Value 1:{indentExpr parent.fvar}"
          let parent_type ← eliminateNonFields (← inferType parent.fvar)
          let parent_value ← eliminateNonFields parent.fvar
          logInfo m!"{parent.name}. Value 2:{indentExpr parent_value}"
          let parent_type ← etaStructReduce <| parent_type.replace fun e => fvarToConst[e]?
          let parent_value ← etaStructReduce <| parent_value.replace fun e => fvarToConst[e]?
          logInfo m!"{parent.name}. Value 3:{indentExpr parent_value}"
          logInfo m!"adding projection {parent.declName} with type{indentD parent_type}\nand value{indentD parent_value}"
          mkCoercionToCopiedParent levelParams params view source parent parent_type parent_value

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
        let initLCtx ← getLCtx
        let initLocalInsts ← getLocalInstances
        withParents view rs r.indFVar do
        withFields view.fields do
        withRef view.ref do
          Term.synthesizeSyntheticMVarsNoPostponing
          let state ← get
          let parents := state.parents
          let fieldInfos := state.fields
          let lctx ← getLCtx
          let localInsts ← getLocalInstances
          logInfo m!"{(← mkFreshExprMVar none).mvarId!}"
          -- let ctorLCtx ← getConstructorFieldLocalDecls
          -- let ctor ← withLCtx initLCtx initLocalInsts <| withExistingLocalDecls ctorLCtx <| mkCtor view r params
          let ctor ← mkCtor view r params
          return {
            ctors := [ctor]
            collectUsedFVars := collectUsedFVars lctx localInsts fieldInfos
            checkUniverses := fun _ u => withLCtx lctx localInsts do checkResultingUniversesForFields fieldInfos u
            finalizeTermElab := withLCtx lctx localInsts do checkDefaults fieldInfos
            prefinalize := fun _ _ _ => do
              withLCtx lctx localInsts do
              -- withLCtx initLCtx initLocalInsts <| withExistingLocalDecls ctorLCtx do
                trace[Elab.structure] "adding projections"
                addProjections r fieldInfos
                trace[Elab.structure] "added projections"
                registerStructure view.declName fieldInfos
              withSaveInfoContext do  -- save new env
                for field in view.fields do
                  -- may not exist if overriding inherited field
                  if (← getEnv).contains field.declName then
                    Term.addTermInfo' field.ref (← mkConstWithLevelParams field.declName) (isBinder := true)
            finalize := fun levelParams params replaceIndFVars => do
              trace[Elab.structure] "adding remaining projections"
              let parentInfos ← runStructElabM (init := state) <| withLCtx lctx localInsts <| mkRemainingProjections levelParams params view
              trace[Elab.structure] "added remaining projections"
              withSaveInfoContext do
                -- Add terminfo for parents now that all parent projections exist.
                for parent in parents do
                  if parent.addTermInfo then
                    Term.addTermInfo' parent.ref (← mkConstWithLevelParams parent.declName) (isBinder := true)
              setStructureParents view.declName parentInfos
              checkResolutionOrder view.declName
              if view.isClass then
                addParentInstances parentInfos

              -- withLCtx lctx localInsts do
              --   addDefaults params replaceIndFVars fieldInfos
          }
    }

end Lean.Elab.Command.Structure
