/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
prelude
import Lean.Util.FindExpr
import Lean.Parser.Term
import Lean.Meta.Structure
import Lean.Elab.App
import Lean.Elab.Binders
import Lean.PrettyPrinter

/-!
# Structure instance elaborator

A *structure instance* is notation to construct a term of a `structure`.
Examples: `{ x := 2, y.z := true }`, `{ s with cache := c' }`, and `{ s with values[2] := v }`.
Structure instances are the preferred way to invoke a `structure`'s constructor,
since they hide Lean implementation details such as whether parents are represented as subobjects,
and also they do correct processing of default values,
which are complicated due to the fact that `structure`s can override default values of their parents,
and furthermore overridden default values can use fields that come after in the order the fields appear in the constructor.

This module elaborates structure instance notation.
Note that the `where` syntax to define structures (`Lean.Parser.Command.whereStructInst`)
macro expands into the structure instance notation elaborated by this module.
-/

namespace Lean.Elab.Term.StructInst

open Meta
open TSyntax.Compat

/-!
Recall that structure instances are (after removing parsing and pretty printing hints):

```lean
def structInst := leading_parser
  "{ " >> optional (sepBy1 termParser ", " >> " with ")
    >> structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))
    >> optEllipsis
    >> optional (" : " >> termParser) >> " }"

def structInstField := leading_parser
  structInstLVal >> optional (many structInstFieldBinder >> optType >> structInstFieldDecl)

@[builtin_structInstFieldDecl_parser]
def structInstFieldDef := leading_parser
  " := " >> termParser

@[builtin_structInstFieldDecl_parser]
def structInstFieldEqns := leading_parser
  matchAlts

def structInstWhereBody := leading_parser
  structInstFields (sepByIndent structInstField "; " (allowTrailingSep := true))

@[builtin_structInstFieldDecl_parser]
def structInstFieldWhere := leading_parser
  "where" >> structInstWhereBody
```
-/

/--
Transforms structure instances such as `{ x := 0 : Foo }` into `({ x := 0 } : Foo)`.
Structure instance notation makes use of the expected type.
-/
@[builtin_macro Lean.Parser.Term.structInst] def expandStructInstExpectedType : Macro := fun stx =>
  let expectedArg := stx[4]
  if expectedArg.isNone then
    Macro.throwUnsupported
  else
    let expected := expectedArg[1]
    let stxNew   := stx.setArg 4 mkNullNode
    `(($stxNew : $expected))

private def mkStructInstField (lval : TSyntax ``Parser.Term.structInstLVal) (binders : TSyntaxArray ``Parser.Term.structInstFieldBinder)
    (type? : Option Term) (val : Term) : MacroM (TSyntax ``Parser.Term.structInstField) := do
  let mut val := val
  if let some type := type? then
    val ← `(($val : $type))
  if !binders.isEmpty then
    -- HACK: this produces invalid syntax, but the fun elaborator supports structInstFieldBinder as well
    val ← `(fun $binders* => $val)
  `(Parser.Term.structInstField| $lval := $val)

/--
Takes an arbitrary `structInstField` and expands it to be a `structInstFieldDef` without any binders or type ascription.
-/
private def expandStructInstField (stx : Syntax) : MacroM (Option Syntax) := withRef stx do
  match stx with
  | `(Parser.Term.structInstField| $_:structInstLVal := $_) =>
    -- Already expanded.
    return none
  | `(Parser.Term.structInstField| $lval:structInstLVal $[$binders]* $[: $ty?]? $decl:structInstFieldDecl) =>
    match decl with
    | `(Parser.Term.structInstFieldDef| := $val) =>
      mkStructInstField lval binders ty? val
    | `(Parser.Term.structInstFieldEqns| $alts:matchAlts) =>
      let val ← expandMatchAltsIntoMatch stx alts (useExplicit := false)
      mkStructInstField lval binders ty? val
    | _ => Macro.throwUnsupported
  | `(Parser.Term.structInstField| $lval:structInstLVal) =>
    -- Abbreviation
    match lval with
    | `(Parser.Term.structInstLVal| $id:ident) =>
      mkStructInstField lval #[] none id
    | _ =>
      Macro.throwErrorAt lval "unsupported structure instance field abbreviation, expecting identifier"
  | _ => Macro.throwUnsupported

/--
Expands fields.
* Abbrevations. Example: `{ x }` expands to `{ x := x }`.
* Equations. Example: `{ f | 0 => 0 | n + 1 => n }` expands to `{ f := fun x => match x with | 0 => 0 | n + 1 => n }`.
* Binders and types. Example: `{ f n : Nat := n + 1 }` expands to `{ f := fun n => (n + 1 : Nat) }`.
-/
@[builtin_macro Lean.Parser.Term.structInst] def expandStructInstFields : Macro | stx => do
  let structInstFields := stx[2]
  let fields := structInstFields[0].getSepArgs
  let fields? ← fields.mapM expandStructInstField
  if fields?.all (·.isNone) then
    Macro.throwUnsupported
  let fields := Array.zipWith Option.getD fields? fields
  let structInstFields := structInstFields.setArg 0 <| Syntax.mkSep fields (mkAtomFrom stx ", ")
  return stx.setArg 2 structInstFields

/--
An *explicit source* is one of the structures `sᵢ` that appear in `{ s₁, …, sₙ with … }`.
-/
structure ExplicitSourceView where
  /-- The syntax of the explicit source. -/
  stx        : Syntax
  /-- The local variable for this source. -/
  fvar       : Expr
  /-- The name of the structure for the type of the explicit source. -/
  structName : Name
  deriving Inhabited

/--
A view of the sources of fields for the structure instance notation.
-/
structure SourcesView where
  /-- Explicit sources (i.e., one of the structures `sᵢ` that appear in `{ s₁, …, sₙ with … }`). -/
  explicit : Array ExplicitSourceView
  /-- The syntax for a trailing `..`. This is "ellipsis mode" for missing fields, similar to ellipsis mode for applications. -/
  implicit : Option Syntax
  deriving Inhabited

/--
Given an array of explicit sources, returns syntax of the form
`optional (atomic (sepBy1 termParser ", " >> " with ")`
-/
private def mkSourcesWithSyntax (sources : Array Syntax) : Syntax :=
  let ref := sources[0]!
  let stx := Syntax.mkSep sources (mkAtomFrom ref ", ")
  mkNullNode #[stx, mkAtomFrom ref "with "]

/--
Creates a structure source view from structure instance notation.
-/
private def getStructSources (structStx : Syntax) : TermElabM SourcesView :=
  withRef structStx do
    let explicitSource := structStx[1]
    let implicitSource := structStx[3]
    let explicit ← if explicitSource.isNone then
      pure #[]
    else
      explicitSource[0].getSepArgs.mapM fun stx => do
        let some src ← isLocalIdent? stx | unreachable!
        addTermInfo' stx src
        let srcType ← whnf (← inferType src)
        tryPostponeIfMVar srcType
        let structName ← getStructureName srcType
        return { stx, fvar := src, structName }
    let implicit := if implicitSource[0].isNone then none else implicitSource
    return { explicit, implicit }

/--
We say a structure instance notation is a "modifyOp" if it contains only a single array update.
```lean
def structInstArrayRef := leading_parser "[" >> termParser >>"]"
```
-/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
  let s? ← stx[2][0].getSepArgs.foldlM (init := none) fun s? arg => do
    /- arg is of the form `structInstField`. It should be macro expanded at this point, but we make sure it's the case. -/
    if arg[1][2].getKind == ``Lean.Parser.Term.structInstFieldDef then
      /- Remark: the syntax for `structInstField` after macro expansion is
         ```
         def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (group ("." >> (ident <|> numLit)) <|> structInstArrayRef)
         def structInstFieldDef := leading_parser
           structInstLVal >> group (null >> null >> group (" := " >> termParser))
         ```
      -/
      let lval := arg[0]
      let k    := lval[0].getKind
      if k == ``Lean.Parser.Term.structInstArrayRef then
        match s? with
        | none   => return some arg
        | some s =>
          if s[0][0].getKind == ``Lean.Parser.Term.structInstArrayRef then
            throwErrorAt arg "invalid \{...} notation, can have at most one `[..]` at a given level"
          else
            throwErrorAt arg "invalid \{...} notation, can't mix field and `[..]` at a given level"
      else
        match s? with
        | none   => return some arg
        | some s =>
          if s[0][0].getKind == ``Lean.Parser.Term.structInstArrayRef then
            throwErrorAt arg "invalid \{...} notation, can't mix field and `[..]` at a given level"
          else
            return s?
    else
      return s?
  match s? with
  | none   => return none
  | some s => if s[0][0].getKind == ``Lean.Parser.Term.structInstArrayRef then return s? else return none

/--
Given a `stx` that is a structure instance notation that's a modifyOp (according to `isModifyOp?`), elaborates it.
Only supports structure instances with a single source.
-/
private def elabModifyOp (stx modifyOp : Syntax) (sourcesView : SourcesView) (expectedType? : Option Expr) : TermElabM Expr := do
  unless sourcesView.explicit.size == 1 do
    throwError "invalid \{...} notation, exactly one explicit source is required when using '[<index>] := <value>' update notation"
  if let some implicit := sourcesView.implicit then
    throwErrorAt implicit "invalid \{...} notation, '[<index>] := <value>' update notation does not support ellipsis"
  let source := sourcesView.explicit[0]!
  let cont (val : Syntax) : TermElabM Expr := do
    let lval := modifyOp[0][0]
    let idx  := lval[1]
    let self := source.stx
    let stxNew ← `($(self).modifyOp (idx := $idx) (fun s => $val))
    trace[Elab.struct.modifyOp] "{stx}\n===>\n{stxNew}"
    withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  let rest := modifyOp[0][1]
  if rest.isNone then
    cont modifyOp[1][2][1]
  else
    let s ← `(s)
    let valFirst  := rest[0]
    let valFirst  := if valFirst.getKind == ``Lean.Parser.Term.structInstArrayRef then valFirst else valFirst[1]
    let restArgs  := rest.getArgs
    let valRest   := mkNullNode restArgs[1:restArgs.size]
    let valField  := modifyOp.setArg 0 <| mkNode ``Parser.Term.structInstLVal #[valFirst, valRest]
    let valSource := mkSourcesWithSyntax #[s]
    let val       := stx.setArg 1 valSource
    let val       := val.setArg 2 <| mkNode ``Parser.Term.structInstFields #[mkNullNode #[valField]]
    trace[Elab.struct.modifyOp] "{stx}\nval: {val}"
    cont val

/--
A component of a left-hand side for a field appearing in structure instance syntax.
-/
inductive FieldLHS where
  /-- A name component for a field left-hand side. For example, `x` and `y` in `{ x.y := v }`. -/
  | fieldName  (ref : Syntax) (name : Name)
  /-- (Can't be written by users.) A field setting an entire parent.
  The `structName` is the name of the parent structure, and `name` is the projection field name.
  Always appears as the only LHS component.  -/
  | parentFieldName (ref : Syntax) (structName : Name) (name : Name)
  /-- A numeric index component for a field left-hand side. For example `3` in `{ x.3 := v }`. -/
  | fieldIndex (ref : Syntax) (idx : Nat)
  /-- An array indexing component for a field left-hand side. For example `[3]` in `{ arr[3] := v }`. -/
  | modifyOp   (ref : Syntax) (index : Syntax)
  deriving Inhabited

instance : ToFormat FieldLHS where
  format
    | .fieldName _ n         => format n
    | .parentFieldName _ _ n => format n
    | .fieldIndex _ i        => format i
    | .modifyOp _ i          => "[" ++ i.prettyPrint ++ "]"

/--
`Field StructInstView` is a representation of a field in the structure instance.
-/
structure FieldView where
  /-- The whole field syntax. -/
  ref   : Syntax
  /-- The LHS components. This is nonempty. -/
  lhs   : List FieldLHS
  /-- The value of the field. -/
  val   : Term
  deriving Inhabited

/--
The view for structure instance notation.
-/
structure StructInstView where
  /-- The syntax for the whole structure instance. -/
  ref : Syntax
  /-- The fields of the structure instance. -/
  fields : Array FieldView
  /-- The additional sources for fields for the structure instance. -/
  sources : SourcesView
  deriving Inhabited

private def formatField (field : FieldView) : Format :=
  Format.joinSep field.lhs " . " ++ " := " ++ format field.val

private def formatStruct : StructInstView → Format
  | ⟨_, fields, source⟩ =>
    let fieldsFmt := Format.joinSep (fields.toList.map formatField) ", "
    let implicitFmt := if source.implicit.isSome then " .. " else ""
    if source.explicit.isEmpty then
      "{" ++ fieldsFmt ++ implicitFmt ++ "}"
    else
      "{" ++ format (source.explicit.map (·.stx)) ++ " with " ++ fieldsFmt ++ implicitFmt ++ "}"

instance : ToFormat FieldView := ⟨formatField⟩
instance : ToFormat StructInstView := ⟨formatStruct⟩

/--
Converts a `FieldLHS` back into syntax. This assumes the `ref` fields have the correct structure.

Recall that `structInstField` elements have the form
```lean
def structInstField  := leading_parser structInstLVal >> group (null >> null >> group (" := " >> termParser))
def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
def structInstArrayRef := leading_parser "[" >> termParser >>"]"
```
-/
-- Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
private def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
  | .modifyOp stx .. => stx
  | .fieldName stx name | .parentFieldName stx _ name =>
    if first then mkIdentFrom stx name else mkGroupNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
  | .fieldIndex stx .. => if first then stx else mkGroupNode #[mkAtomFrom stx ".", stx]

/--
Converts a `FieldView` back into syntax. Used to construct synthetic structure instance notation for subobjects in `StructInst.expandStruct` processing.
-/
private def FieldView.toSyntax : FieldView → TSyntax ``Parser.Term.structInstField
  | field =>
    let stx := field.ref
    let stx := stx.setArg 1 <| stx[1].setArg 2 <| stx[1][2].setArg 1 field.val
    match field.lhs with
    | first::rest => stx.setArg 0 <| mkNode ``Parser.Term.structInstLVal #[first.toSyntax true, mkNullNode <| rest.toArray.map (FieldLHS.toSyntax false) ]
    | _ => unreachable!

/-- Creates a view of a field left-hand side. -/
private def toFieldLHS (stx : Syntax) : MacroM FieldLHS :=
  if stx.getKind == ``Lean.Parser.Term.structInstArrayRef then
    return FieldLHS.modifyOp stx stx[1]
  else
    -- Note that the representation of the first field is different.
    let stx := if stx.getKind == groupKind then stx[1] else stx
    if stx.isIdent then
      return FieldLHS.fieldName stx stx.getId.eraseMacroScopes
    else match stx.isFieldIdx? with
      | some idx => return FieldLHS.fieldIndex stx idx
      | none     => Macro.throwErrorAt stx "unexpected structure syntax"

/--
Creates a view from structure instance notation
and structure source view (from `Lean.Elab.Term.StructInst.getStructSources`).
-/
private def mkStructView (stx : Syntax) (sources : SourcesView) : MacroM StructInstView := do
  /-
  Recall that `stx` is of the form
  ```
  leading_parser "{" >> optional (atomic (sepBy1 termParser ", " >> " with "))
              >> structInstFields (sepByIndent structInstField ...)
              >> optional ".."
              >> optional (" : " >> termParser)
              >> " }"
  ```
  This method assumes that `structInstField` had already been expanded by the macro `expandStructInstFields`.
  -/
  let fields ← stx[2][0].getSepArgs.mapM fun fieldStx => do
    let `(Parser.Term.structInstField| $lval:structInstLVal := $val) := fieldStx | Macro.throwUnsupported
    let first ← toFieldLHS lval.raw[0]
    let rest  ← lval.raw[1].getArgs.toList.mapM toFieldLHS
    return { ref := fieldStx, lhs := first :: rest, val : FieldView }
  return { ref := stx, fields, sources }

/--
The constructor to use for the structure instance notation.
-/
private structure CtorHeaderResult where
  /-- The constructor function with applied structure parameters. -/
  ctorFn     : Expr
  /-- The type of `ctorFn` -/
  ctorFnType : Expr
  /-- The type of the structure. -/
  structType : Expr
  /-- Universe levels. -/
  levels     : List Level
  /-- Parameters for the type. -/
  params     : Array Expr

/--
Elaborates the structure's flat constructor using the expected type, filling in the structure type parameters.

The `structureType?` is the expected type of the structure instance.
-/
private def mkCtorHeader (ctorVal : ConstructorVal) (structureType? : Option Expr) : TermElabM CtorHeaderResult := do
  let flatCtorName := mkFlatCtorOfStructCtorName ctorVal.name
  let cinfo ← getConstInfo flatCtorName
  let us ← mkFreshLevelMVars ctorVal.levelParams.length
  let mut type ← instantiateTypeLevelParams cinfo.toConstantVal us
  let mut params : Array Expr := #[]
  let mut instMVars : Array MVarId := #[]
  for _ in [0 : ctorVal.numParams] do
    let .forallE _ d b bi := type
      | throwError "unexpected constructor type"
    let param ←
      if bi.isInstImplicit then
        let mvar ← mkFreshExprMVar d .synthetic
        instMVars := instMVars.push mvar.mvarId!
        pure mvar
      else
        mkFreshExprMVar d
    params := params.push param
    type := b.instantiate1 param
  let structType := mkAppN (.const ctorVal.induct us) params
  if let some structureType := structureType? then
    discard <| isDefEq structureType structType
  let val ← instantiateValueLevelParams cinfo us
  let val := val.beta params
  synthesizeAppInstMVars instMVars val
  return { ctorFn := val, ctorFnType := type, structType, levels := us, params }

/--
Normalizes the head of the LHS of the `FieldView` in the following ways:
- Replaces numeric index field LHS's with the corresponding named field.
  If this is a subobject field, continues normalizing it.
- Consumes nonterminal parent projections, e.g. `toA.x` becomes `x`. Throws an error if `A` does not have an `x` field.
- If a field name is not atomic, splits it into a multi-component LHS.

Normalization is not done for the entire LHS; only the head of each field LHS is normalized.

Validates that fields are indeed fields, and adds completion info.
On validation errors, errors are logged and the corresponding fields are omitted.

Assumed invariant: parent projections and field names are disjoint sets. This is validated in the `structure` elaborator.

Resulting invariant: the field has a LHS that has one of these forms:
- `.fieldName .. :: _`
- `[.parentFieldName ..]`
-/
private partial def normalizeField (structName : Name) (fieldView : FieldView) : MetaM FieldView := do
  let env ← getEnv
  match fieldView.lhs with
  | .fieldIndex ref idx :: rest =>
    if idx == 0 then
      throwErrorAt ref m!"invalid field index, index must be greater than 0"
    let fieldNames := getStructureFields env structName
    if idx > fieldNames.size then
      throwErrorAt ref m!"invalid field index, structure '{.ofConstName structName}' has only {fieldNames.size} fields"
    normalizeField structName { fieldView with lhs := .fieldName ref fieldNames[idx - 1]! :: rest }
  | .fieldName ref name :: rest =>
    if !name.isAtomic then
      let newEntries := name.components.map (FieldLHS.fieldName ref ·)
      normalizeField structName { fieldView with lhs := newEntries ++ rest }
    else
      addCompletionInfo <| CompletionInfo.fieldId ref name (← getLCtx) structName
      if let some parentName := findParentProjStruct? env structName name then
        if rest.isEmpty then
          return { fieldView with lhs := [.parentFieldName ref parentName name] }
        else
          normalizeField parentName { fieldView with lhs := rest }
      else if (findField? env structName name).isSome then
        return fieldView
      else
        throwErrorAt ref m!"'{name}' is not a field of structure '{.ofConstName structName}'"
  | _ => unreachable!

private inductive ExpandedFieldVal
  | term (stx : Term)
  /-- Like `stx.fieldName`, but later we will be sure to elaborate `stx` exactly once for the given `parentStructName`.
  The `fvarId` will be used later when elaborating `stx`. It becomes a local decl; if it is a new fvar, an impl. detail. -/
  | proj (fvarId : FVarId) (stx : Term) (parentStructName : Name) (parentFieldName : Name)
  | source (fvar : Expr)
  | nested (fieldViews : Array FieldView) (sources : Array ExplicitSourceView)

private structure ExpandedField where
  ref  : Syntax
  name : Name
  val  : ExpandedFieldVal

private def ExpandedField.isNested (f : ExpandedField) : Bool := f.val matches .nested ..

instance : ToMessageData ExpandedFieldVal where
  toMessageData
    | .term stx => m!"term {stx}"
    | .proj fvarId stx parentStructName _ => m!"proj {Expr.fvar fvarId} {.ofConstName parentStructName}{indentD stx}"
    | .source fvar => m!"source {fvar}"
    | .nested fieldViews sources => m!"nested {MessageData.joinSep (sources.map (·.stx)).toList ", "} {MessageData.joinSep (fieldViews.map (indentD <| toMessageData ·)).toList "\n"}"

instance : ToMessageData ExpandedField where
  toMessageData field := m!"field '{field.name}' is {field.val}"

abbrev ExpandedFields := NameMap ExpandedField

/--
Normalizes and expands the field views.
Validates that there are no duplicate fields.
-/
private def expandFields (structName : Name) (fieldViews : Array FieldView) (recover : Bool) : MetaM (Bool × ExpandedFields) := do
  let mut fields : ExpandedFields := {}
  let mut errors : Bool := false
  for fieldView in fieldViews do
    try
      let fieldView ← normalizeField structName fieldView
      match fieldView.lhs with
      | .fieldName ref name :: rest =>
        if let some field := fields.find? name then
          if rest.isEmpty || !field.isNested then
            throwErrorAt ref m!"field '{name}' has already been specified"
          else
            -- There is a pre-existing nested field, and we are looking at a nested field. So, insert.
            let .nested views' sources := field.val | unreachable!
            let views' := views'.push { fieldView with lhs := rest }
            fields := fields.insert name { field with val := .nested views' sources }
        else if rest.isEmpty then
          -- A simple field
          fields := fields.insert name { ref := ref, name, val := .term fieldView.val }
        else
          -- A new nested field
          let fieldView' := { fieldView with lhs := rest }
          fields := fields.insert name { ref := ref, name, val := .nested #[fieldView'] #[] }
      | [.parentFieldName ref parentStructName name] =>
        -- Parent field
        let fvarId ← mkFreshFVarId
        for parentField in getStructureFieldsFlattened (← getEnv) parentStructName false do
          if fields.contains parentField then
            throwErrorAt ref m!"field '{name}' from structure '{.ofConstName parentStructName}' has already been specified"
          else
            let val := ExpandedFieldVal.proj fvarId fieldView.val parentStructName name
            fields := fields.insert parentField { ref := ref, name := parentField, val }
      | _ => unreachable!
    catch ex =>
      if recover then
        logException ex
        errors := true
      else
        throw ex
  return (errors, fields)

/--
Adds fields from the sources, updating any nested fields.

Rule: a missing field always comes from the first source that can provide it.
-/
private def addSourceFields (structName : Name) (sources : Array ExplicitSourceView) (fields : ExpandedFields) : MetaM ExpandedFields := do
  let mut fields := fields
  let env ← getEnv
  let fieldNames := getStructureFieldsFlattened env structName false
  for source in sources do
    let sourceFieldNames := getStructureFieldsFlattened env source.structName false
    for fieldName in sourceFieldNames do
      if fieldNames.contains fieldName then
        match fields.find? fieldName with
        | none =>
          -- Missing field, take it from this source
          let val := ExpandedFieldVal.source source.fvar
          fields := fields.insert fieldName { ref := source.stx.mkSynthetic, name := fieldName, val }
        | some field@{ val := .nested subFields sources', .. } =>
          -- Existing nested field, add this source
          let val := ExpandedFieldVal.nested subFields (sources'.push source)
          fields := fields.insert fieldName { field with val }
        | _ =>
          -- Field already exists and is known to be complete.
          pure ()
  return fields

private structure StructInstContext where
  view : StructInstView
  /-- True if the structure instance has a trailing `..`. -/
  ellipsis : Bool
  structName : Name
  structType : Expr
  /-- Structure universe levels. -/
  levels : List Level
  /-- Structure parameters. -/
  params : Array Expr
  /-- The flat constructor with applied parameters. -/
  val : Expr
  /-- The expanded structure instance fields, to be elaborated. -/
  fieldViews : ExpandedFields

private structure StructInstState where
  /-- The type of the flat constructor with applied parameters and applied fields. -/
  type : Expr
  /-- A set of the structure name and all its parents. -/
  structNameSet : NameSet := {}
  /-- The elaborated fields. -/
  fieldMap : NameMap Expr := {}
  /-- The elaborated fields, in order. -/
  fields : Array Expr := #[]
  /-- Metavariables for instance implicit fields. These will be registered after default value propagation. -/
  instMVars : Array MVarId := #[]
  /-- The let decls created when processing `ExpandedFieldVal.proj` fields. -/
  liftedFVars : Array Expr := #[]
  /-- When processing `ExpandedFieldVal.proj` fields, sometimes we can re-use pre-existing fvars. -/
  liftedFVarRemap : FVarIdMap FVarId := {}
  /-- Fields to synthesize using default values, if they don't get synthesized by other means.
  If the boolean is `true`, then the field *must* be solved for. This is used for explicit fields. -/
  optParamFields : Array (Name × Expr × Bool) := #[]
  deriving Inhabited

/--
Monad for elaborating the fields of structure instance notation.
-/
private abbrev StructInstM := ReaderT StructInstContext (StateRefT StructInstState TermElabM)

private structure SavedState where
  termState : Term.SavedState
  state : StructInstState
  deriving Nonempty

private def saveState : StructInstM SavedState :=
  return { termState := (← Term.saveState), state := (← get) }

private def SavedState.restore (s : SavedState) : StructInstM Unit := do
  s.termState.restore
  set s.state

private instance : MonadBacktrack SavedState StructInstM where
  saveState      := saveState
  restoreState b := b.restore

/--
Initialize cached data.
-/
private def initializeState : StructInstM Unit := do
  let structName := (← read).structName
  let resolutionOrder ← getStructureResolutionOrder structName
  let structNameSet : NameSet := resolutionOrder.foldl (·.insert ·) {}
  modify fun s => { s with structNameSet }

private def withViewRef {α : Type} (x : StructInstM α) : StructInstM α := do
  let ref := (← read).view.ref
  withRef ref x

/--
If the field has already been visited by `loop` but has not been solved for yet, returns its metavariable.
-/
private def isFieldNotSolved? (fieldName : Name) : StructInstM (Option MVarId) := do
  let some val := (← get).fieldMap.find? fieldName | return none
  let .mvar mvarId ← instantiateMVars val | return none
  return mvarId

/--
Reduce projections for all structures appearing in `structNameSet`.
-/
private def reduceFieldProjs (e : Expr) : StructInstM Expr := do
  let e ← instantiateMVars e
  let postVisit (e : Expr) : StructInstM TransformStep := do
    if let Expr.const projName .. := e.getAppFn then
      if let some projInfo ← getProjectionFnInfo? projName then
        let ConstantInfo.ctorInfo cval := (← getEnv).find? projInfo.ctorName | unreachable!
        if (← get).structNameSet.contains cval.induct then
          let args := e.getAppArgs
          if let some major := args[projInfo.numParams]? then
            if major.isAppOfArity projInfo.ctorName (cval.numParams + cval.numFields) then
              if let some arg := major.getAppArgs[projInfo.numParams + projInfo.i]? then
                return TransformStep.visit <| mkAppN arg args[projInfo.numParams+1:]
    return TransformStep.continue
  Meta.transform e (post := postVisit)

/--
Unfolds implementation decl let vars that appear in propositions.
-/
private def zetaDeltaImplDetailsInProps (e : Expr) : MetaM Expr := do
  let unfoldPre (e : Expr) : MetaM TransformStep := do
    let .fvar fvarId := e.getAppFn | return .continue
    let decl ← fvarId.getDecl
    if decl.isLet && decl.kind matches .implDetail then
      return .visit <| (← instantiateMVars decl.value).beta e.getAppArgs
    else
      return .continue
  let pre (e : Expr) : MetaM TransformStep := do
    if ← Meta.isProp e then
      let e ← transform e (pre := unfoldPre)
      return .done e
    else
      return .continue
  transform (← instantiateMVars e) (pre := pre)

private def etaStructReduce' (e : Expr) : StructInstM Expr := do
  let names := (← get).structNameSet
  etaStructReduce e names.contains

private def normalizeExpr (e : Expr) (zetaDeltaImpl : Bool := true) : StructInstM Expr := do
  let e ← if zetaDeltaImpl then zetaDeltaImplDetailsInProps e else pure e
  let e ← reduceFieldProjs e
  etaStructReduce' e

private def addStructFieldAux (fieldName : Name) (e : Expr) : StructInstM Unit := do
  trace[Elab.struct] "setting '{fieldName}' value to{indentExpr e}"
  modify fun s => { s with
    type := s.type.bindingBody!.instantiateBetaRevRange 0 1 #[e]
    fields := s.fields.push e
    fieldMap := s.fieldMap.insert fieldName e
  }

private def addStructField (fieldView : ExpandedField) (e : Expr) : StructInstM Unit := do
  let fieldName := fieldView.name
  addStructFieldAux fieldName e
  let env ← getEnv
  if let some structName := findField? env (← read).structName fieldName then
    if let some fieldInfo := getFieldInfo? env structName fieldName then
      pushInfoTree <| InfoTree.node (children := {}) <| Info.ofFieldInfo {
        projName := fieldInfo.projFn, fieldName, lctx := (← getLCtx), val := e, stx := fieldView.ref
      }

private def elabStructField (_fieldName : Name) (stx : Term) (fieldType : Expr) : StructInstM Expr := do
  let fieldType ← normalizeExpr fieldType
  elabTermEnsuringType stx fieldType

private def addStructFieldMVar (fieldName : Name) (ty : Expr) (kind : MetavarKind := .natural) : StructInstM Expr := do
  let ty ← normalizeExpr ty
  let e ← mkFreshExprMVar ty (kind := kind)
  addStructFieldAux fieldName e
  return e

/--
Instantiates default value for field `fieldName` set at structure `structName`.
The arguments for the `_default` auxiliary function are provided by `fieldMap`.
After default values are resolved, then the one that is added to the environment
as an `_inherited_default` auxiliary function is normalized; we don't do those normalizations here.
-/
private partial def getFieldDefaultValue? (fieldName : Name) : StructInstM (NameSet × Option Expr) := do
  let some defFn := getEffectiveDefaultFnForField? (← getEnv) (← read).structName fieldName
    | return ({}, none)
  let fieldMap := (← get).fieldMap
  let some (fields, val) ← instantiateStructDefaultValueFn? defFn (← read).levels (← read).params (pure ∘ fieldMap.find?)
    | logError m!"default value for field '{fieldName}' of structure '{.ofConstName (← read).structName}' could not be instantiated, ignoring"
      return ({}, none)
  return (fields, val)

/--
Auxiliary type for `synthDefaultFields`
-/
private structure PendingField where
  fieldName : Name
  fieldType : Expr
  required : Bool
  deps : NameSet
  val? : Option Expr

/--
Synthesize pending optParams.
-/
private def synthOptParamFields : StructInstM Unit := do
  let optParamFields ← modifyGet fun s => (s.optParamFields, { s with optParamFields := #[] })
  if optParamFields.isEmpty then return
  /-
  We try to synthesize pending mvars before trying to use default values.
  This is important in examples such as
  ```
  structure MyStruct where
      {α : Type u}
      {β : Type v}
      a : α
      b : β

  #check { a := 10, b := true : MyStruct }
  ```
  were the `α` will remain "unknown" until the default instance for `OfNat` is used to ensure that `10` is a `Nat`.

  TODO: investigate whether this design decision may have unintended side effects or produce confusing behavior.
  -/
  synthesizeSyntheticMVarsUsingDefault

  trace[Elab.struct] "field values before default value synth:{indentD <| toMessageData (← get).fieldMap.toArray}"

  -- Process default values for pending optParam fields.
  let mut pendingFields : Array PendingField ← optParamFields.filterMapM fun (fieldName, fieldType, required) => do
    if required || (← isFieldNotSolved? fieldName).isSome then
      let (deps, val?) ← getFieldDefaultValue? fieldName
      if let some val := val? then
        trace[Elab.struct] "default value for {fieldName}:{indentExpr val}"
      else
        trace[Elab.struct] "no default value for {fieldName}"
      pure <| some { fieldName, fieldType, required, deps, val? }
    else
      pure none
  -- We then iteratively look for pending fields that do not depend on unsolved-for fields.
  -- The assignments might fail (due to occurs checks or stuck metavariables),
  -- so we need to keep trying until no more progress is made.
  let mut pendingSet : NameSet := pendingFields.foldl (init := {}) fun set pending => set.insert pending.fieldName
  while !pendingSet.isEmpty do
    let selectedFields := pendingFields.filter fun pendingField =>
      pendingField.val?.isSome && pendingField.deps.all (fun dep => !pendingSet.contains dep)
    let mut toRemove : Array Name := #[]
    let mut assignErrors : Array MessageData := #[]
    for selected in selectedFields do
      let some selectedVal := selected.val? | unreachable!
      if let some mvarId ← isFieldNotSolved? selected.fieldName then
        let fieldType := selected.fieldType
        let selectedType ← inferType selectedVal
        if ← isDefEq fieldType selectedType then
          /-
          We must use `checkedAssign` here to ensure we do not create a cyclic
          assignment. See #3150.
          This can happen when there are holes in the the fields the default value
          depends on.
          Possible improvement: create a new `_` instead of returning `false` when
          `checkedAssign` fails. Reason: the field will not be needed after the
          other `_` are resolved by the user.
          -/
          if ← MVarId.checkedAssign mvarId selectedVal then
            toRemove := toRemove.push selected.fieldName
          else
            assignErrors := assignErrors.push m!"\
              occurs check failed, field '{selected.fieldName}' of type{indentExpr fieldType}\n\
              cannot be assigned the default value{indentExpr selectedVal}"
        else
          assignErrors := assignErrors.push m!"\
            default value for field '{selected.fieldName}' {← mkHasTypeButIsExpectedMsg selectedType fieldType}"
      else
        if selected.required then
          -- Clear the value but preserve its pending status, for the "fields missing" error.
          -- Rationale: this is a field that must be explicitly provided (if default values don't solve for it),
          -- and *not* solved for by unification. Users expect explicit fields to be required to be provided by some explicit means.
          pendingFields := pendingFields.map fun pending =>
            if pending.fieldName = selected.fieldName then
              { pending with val? := none }
            else
              pending
        toRemove := toRemove.push selected.fieldName
    if toRemove.isEmpty then
      if (← read).ellipsis then
        for pendingField in pendingFields do
          if let some mvarId ← isFieldNotSolved? pendingField.fieldName then
            registerCustomErrorIfMVar (.mvar mvarId) (← read).view.ref m!"\
              cannot synthesize placeholder for field '{pendingField.fieldName}'"
        return
      let assignErrorsMsg := MessageData.joinSep (assignErrors.map (m!"\n\n" ++ ·)).toList ""
      let mut requiredErrors : Array MessageData := #[]
      for pendingField in pendingFields do
        if (← isFieldNotSolved? pendingField.fieldName).isNone then
          let e := (← get).fieldMap.find! pendingField.fieldName
          requiredErrors := requiredErrors.push m!"\
            field '{pendingField.fieldName}' must be explicitly provided, its synthesized value is{indentExpr e}"
      let requiredErrorsMsg := MessageData.joinSep (requiredErrors.map (m!"\n\n" ++ ·)).toList ""
      let missingFields := pendingFields |>.filter (fun pending => pending.val?.isNone)
      -- TODO(kmill): when fields are all stuck, report better.
      -- For now, just report all pending fields in case there are no obviously missing ones.
      let missingFields := if missingFields.isEmpty then pendingFields else missingFields
      let missing := missingFields |>.map (s!"'{·.fieldName}'") |>.toList
      let msg := m!"fields missing: {", ".intercalate missing}{assignErrorsMsg}{requiredErrorsMsg}"
      if (← readThe Term.Context).errToSorry then
        -- Assign all pending problems using synthetic sorries and log an error.
        for pendingField in pendingFields do
          if let some mvarId ← isFieldNotSolved? pendingField.fieldName then
            mvarId.assign <| ← mkLabeledSorry (← mvarId.getType) (synthetic := true) (unique := true)
        logError msg
        return
      else
        throwError msg
    pendingSet := pendingSet.filter (!toRemove.contains ·)
    pendingFields := pendingFields.filter fun pendingField => pendingField.val?.isNone || !toRemove.contains pendingField.fieldName

private def finalize : StructInstM Expr := withViewRef do
  let val := (← read).val.beta (← get).fields
  trace[Elab.struct] "constructor{indentExpr val}"
  synthesizeAppInstMVars (← get).instMVars val
  trace[Elab.struct] "constructor after synthesizing instMVars{indentExpr val}"
  synthOptParamFields
  trace[Elab.struct] "constructor after synthesizing defaults{indentExpr val}"
  -- Compact the constructors:
  let val ← etaStructReduce' val
  if (← readThe Term.Context).inPattern then
    -- In patterns, there is no multiple evaluation worry.
    -- We also don't want any lingering `let`s in that case.
    zetaDeltaFVars (← instantiateMVars val) ((← get).liftedFVars.map Expr.fvarId!)
  else
    mkLetFVars (← get).liftedFVars val

/--
Replace (subobject) parent projections of a `self` fvar by a constructor expression,
if all the fields for the parent are already defined.
-/
private partial def reduceSelfProjs (self : Expr) (e : Expr) : StructInstM Expr := do
  let e ← instantiateMVars e
  Meta.transform (skipConstInApp := true) e (pre := replaceParentProj)
where
  /-- If `e` is a subobject projection from a structure type that is in `structNameSet`,
  return the name of the structure being projected to and the object being projected. -/
  parentProjInfo? (e : Expr) : StructInstM (Option (Name × Expr)) := do
    let env ← getEnv
    let .const c@(.str _ field) _ := e.getAppFn | return none
    let some info := env.getProjectionFnInfo? c | return none
    let some (.ctorInfo cVal) := env.find? info.ctorName | return none
    let numArgs := e.getAppNumArgs
    unless numArgs == cVal.numParams + 1 do return none
    unless (← get).structNameSet.contains cVal.induct do return none
    let some parentStruct := isSubobjectField? env cVal.induct (Name.mkSimple field) | return none
    return (parentStruct, e.appArg!)
  /-- Recursively applies `parentProjInfo?`. -/
  withoutParentProj? (e : Expr) : StructInstM (Option (Name × Expr)) := do
    let some (field, e') ← parentProjInfo? e | return none
    let some (_, e'') ← withoutParentProj? e.appArg! | return (field, e')
    return (field, e'')
  replaceParentProj (e : Expr) : StructInstM TransformStep := do
    let some (parentName, x) ← withoutParentProj? e | return .continue
    unless x == self do return .continue
    let parentFields := getStructureFieldsFlattened (← getEnv) parentName (includeSubobjectFields := false)
    let fieldMap := (← get).fieldMap
    -- Unless every field is present, we cannot eliminate this expression or any subexpressions
    unless parentFields.all fieldMap.contains do return .done e
    let type ← whnf (← inferType e)
    let .const _ us := type.getAppFn | return .done e
    let params := type.getAppArgs
    let ctor := getStructureCtor (← getEnv) parentName
    unless params.size == ctor.numParams do return .done e
    let flatCtorName := mkFlatCtorOfStructCtorName ctor.name
    let cinfo ← getConstInfo flatCtorName
    let ctorVal ← instantiateValueLevelParams cinfo us
    let fieldArgs := parentFields.map fieldMap.find!
    -- Normalize the expressions since there might be some projections.
    let params ← params.mapM normalizeExpr
    let e' := (ctorVal.beta params).beta fieldArgs
    -- Continue, since we need to reduce the parameters.
    return .continue e'

private def getParentStructType? (parentStructName : Name) : StructInstM (Option (Expr × Option Name)) := do
  let env ← getEnv
  let structName := (← read).structName
  let structType := (← read).structType
  let some path := getPathToBaseStructure? env parentStructName structName | return none
  withLocalDeclD `self structType fun self => do
    let proj ← path.foldlM (init := self) fun e projFn => do
      let ty ← whnf (← inferType e)
      let .const _ us := ty.getAppFn | unreachable!
      let params := ty.getAppArgs
      pure <| mkApp (mkAppN (.const projFn us) params) e
    let projTy ← whnf <| ← inferType proj
    let projTy ← normalizeExpr projTy
    let projTy ← reduceSelfProjs self projTy
    let projTy ← normalizeExpr projTy
    if projTy.containsFVar self.fvarId! then
      -- unsupported dependent type, parent depends on fields that haven't been visited yet.
      trace[Elab.struct] "getParentStructType? '{parentStructName}', failed, computed type depends on {self}{indentExpr projTy}"
      return none
    return (projTy, path.getLast?)

/--
If there is a path to `parentStructName`, compute its type. Also returns the last projection to the parent.
Otherwise, create a type with fresh metavariables.
-/
private def getParentStructType (parentStructName : Name) : StructInstM (Expr × Option Name) := do
  if let some res ← getParentStructType? parentStructName then
    return res
  else
    let c ← mkConstWithFreshMVarLevels parentStructName
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType c)
    return (mkAppN c args, none)

/--
Creates projection notation for the given structure field.
-/
private def mkProjStx (s : Syntax) (fieldName : Name) : Syntax :=
  mkNode ``Parser.Term.explicit
    #[mkAtomFrom s "@",
      mkNode ``Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]]

private def processField (loop : StructInstM α) (field : ExpandedField) (fieldType : Expr) : StructInstM α := withRef field.ref do
  let fieldType := fieldType.consumeTypeAnnotations
  trace[Elab.struct] "processing field '{field.name}' of type {fieldType}{indentD (toMessageData field)}"
  match field.val with
  | .term val => withRef val do
    trace[Elab.struct] "field.val is term {field.name}"
    let e ← elabStructField field.name val fieldType
    addStructField field e
    loop
  | .nested fields sources =>
    trace[Elab.struct] "field.val is nested {field.name}"
    -- Nested field. Create synthetic structure instance notation with projected sources, then elaborate it like a `.term` field.
    let sourceStxs : Array Term := sources.map (fun source => mkProjStx source.stx field.name)
    let fieldStxs := fields.map (fun field => field.toSyntax)
    let ellipsis := (← read).view.sources.implicit
    let stx ← `({ $sourceStxs,* with $fieldStxs,* $[..%$ellipsis]? })
    let e ← elabStructField field.name stx fieldType
    addStructField field e
    loop
  | .source fvar =>
    trace[Elab.struct] "field.val is source {field.name} from {fvar}"
    let e ← mkProjection fvar field.name
    let e ← ensureHasType fieldType e
    addStructFieldAux field.name e
    loop
  | .proj fvarId val parentStructName parentFieldName =>
    trace[Elab.struct] "field.val is proj {field.name}"
    let processProjAux (fvarId : FVarId) : StructInstM α := do
      try
        let e ← mkProjection (.fvar fvarId) field.name
        let eType ← inferType e
        unless ← isDefEq eType fieldType do
          throwError m!"type of field '{field.name}' from structure '{.ofConstName parentStructName}' \
            {← mkHasTypeButIsExpectedMsg eType fieldType}"
        addStructFieldAux field.name e
      catch ex =>
        if (← readThe Term.Context).errToSorry then
          let e ← exceptionToSorry ex fieldType
          addStructFieldAux field.name e
        else
          throw ex
      loop
    if let some fvarId' := (← get).liftedFVarRemap.find? fvarId then
      processProjAux fvarId'
    else if (← getLCtx).contains fvarId then
      processProjAux fvarId
    else
      let (parentTy, projName?) ← getParentStructType parentStructName
      let parentVal ← elabTermEnsuringType val parentTy
      -- Add terminfo so that the `toParent` field has some hover information.
      if let some projName := projName? then
        pushInfoTree <| InfoTree.node (children := {}) <| Info.ofFieldInfo {
          projName, fieldName := parentFieldName, lctx := (← getLCtx), val := parentVal, stx := field.ref
        }
      let parentVal ← instantiateMVars parentVal
      if parentVal.isFVar then
        -- Reuse the fvar rather than add a new decl to the environment.
        let fvarId' := parentVal.fvarId!
        modify fun s => { s with liftedFVarRemap := s.liftedFVarRemap.insert fvarId fvarId' }
        processProjAux fvarId'
      else
        let parentStructName' := parentStructName.eraseMacroScopes
        let declNameStr := if parentStructName'.isStr then s!"__{parentStructName'.getString!}" else "__psrc"
        let declName ← Core.mkFreshUserName (Name.mkSimple declNameStr)
        let decl := LocalDecl.ldecl 0 fvarId declName parentTy parentVal false .implDetail
        modify fun s => { s with liftedFVars := s.liftedFVars.push (.fvar fvarId) }
        withExistingLocalDecls [decl] do processProjAux fvarId

/--
Handle the case when no field is given.

These fields can still be solved for by parent instance synthesis later.
-/
private def processNoField (loop : StructInstM α) (fieldName : Name) (binfo : BinderInfo) (fieldType : Expr) : StructInstM α := do
  trace[Elab.struct] "processNoField '{fieldName}' of type {fieldType}"
  if (← read).ellipsis && (← readThe Term.Context).inPattern then
    -- See the note in `ElabAppArgs.processExplicitArg`
    -- In ellipsis & pattern mode, do not use optParams or autoParams.
    let e ← addStructFieldMVar fieldName fieldType
    registerCustomErrorIfMVar e (← read).view.ref m!"don't know how to synthesize placeholder for field '{fieldName}'"
    loop
  else
    let autoParam? := fieldType.getAutoParamTactic?
    let fieldType := fieldType.consumeTypeAnnotations
    if binfo.isInstImplicit then
      let e ← addStructFieldMVar fieldName fieldType .synthetic
      modify fun s => { s with instMVars := s.instMVars.push e.mvarId! }
      loop
    else if let some (.const tacticDecl ..) := autoParam? then
      match evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl with
      | .error err       => throwError err
      | .ok tacticSyntax =>
        let stx ← `(by $tacticSyntax)
        -- See comment in `Lean.Elab.Term.ElabAppArgs.processExplicitArg` about `tacticSyntax`.
        -- We add info to get reliable positions for messages from evaluating the tactic script.
        let info := (← getRef).getHeadInfo.nonCanonicalSynthetic
        let stx := stx.raw.rewriteBottomUp (·.setInfo info)
        let fieldType ← normalizeExpr fieldType
        let mvar ← mkTacticMVar fieldType stx (.fieldAutoParam fieldName (← read).structName)
        -- Note(kmill): We are adding terminfo to simulate a previous implementation that elaborated `tacticSyntax`.
        -- This is necessary for the unused variable linter.
        -- (See `processExplicitArg` for a comment about this.)
        addTermInfo' stx mvar
        addStructFieldAux fieldName mvar
        loop
    else
      -- Default case: natural metavariable, register it for optParams
      discard <| addStructFieldMVar fieldName fieldType
      modify fun s => { s with optParamFields := s.optParamFields.push (fieldName, fieldType, binfo.isExplicit) }
      loop

private partial def loop : StructInstM Expr := withViewRef do
  let type := (← get).type
  trace[Elab.struct] "loop, constructor type:{indentExpr type}"
  if let .forallE fieldName fieldType _ binfo := type then
    if let some fieldValue := (← get).fieldMap.find? fieldName then
      -- This is a field that was added by `addParentInstanceFields`
      trace[Elab.struct] "field '{fieldName}' already exists, with type {fieldType}"
      let fieldValueType ← inferType fieldValue
      unless ← isDefEq fieldType fieldValueType do
        throwError "field '{fieldName}' inferred from a parent class {← mkHasTypeButIsExpectedMsg fieldValueType fieldType}"
      addStructFieldAux fieldName fieldValue
      loop
    else if let some field := (← read).fieldViews.find? fieldName then
      processField loop field fieldType
    else
      processNoField loop fieldName binfo fieldType
  else
    finalize

/--
For each parent class, see if it can be used to synthesize the fields that haven't been provided.
-/
private partial def addParentInstanceFields : StructInstM Unit := do
  let env ← getEnv
  let structName := (← read).structName
  let fieldNames := getStructureFieldsFlattened env structName (includeSubobjectFields := false)
  let fieldViews := (← read).fieldViews
  if fieldNames.all fieldViews.contains then
    -- Every field is accounted for already
    return

  -- We look at class parents in resolution order
  let parents ← getAllParentStructures structName
  let classParents := parents.filter (isClass env)
  if classParents.isEmpty then return

  let allowedFields := fieldNames.filter (!fieldViews.contains ·)
  let mut remainingFields := allowedFields

  -- Worklist of parent/fields pairs. If fields is empty, then it will be computed later.
  let mut worklist : List (Name × Array Name) := classParents |>.map (·, #[]) |>.toList
  let mut deferred : List (Name × Array Name) := []

  while !worklist.isEmpty do
    let (parentName, parentFields) :: worklist' := worklist | unreachable!
    worklist := worklist'
    let parentFields := if parentFields.isEmpty then getStructureFieldsFlattened env parentName (includeSubobjectFields := false) else parentFields
    -- We only try synthesizing if the parent contains one of the remaining fields
    -- and if every parent field is an allowed field.
    if remainingFields.any parentFields.contains && parentFields.all allowedFields.contains then
      -- We also need to be able to compute the parent type from the structure type.
      -- This may fail if there is a complicated dependence. In that case, we put the problem on the deferred list.
      match ← getParentStructType? parentName with
      | none =>
        trace[Elab.struct] "could not calculate type for parent '{.ofConstName parentName}'"
        deferred := (parentName, parentFields) :: deferred
      | some (parentTy, _) =>
        match ← trySynthInstance parentTy with
        | .none => trace[Elab.struct] "failed to synthesize instance for parent {parentTy}"
        | .undef =>
          trace[Elab.struct] "instance synthesis stuck for parent {parentTy}"
          deferred := (parentName, parentFields) :: deferred
        | .some inst =>
          -- The fields are all-or-nothing
          let saved ← saveState
          try
            for parentField in parentFields do
              let proj ← mkProjection inst parentField
              let proj ← normalizeExpr proj
              match (← get).fieldMap.find? parentField with
              | some fieldVal =>
                let projType ← inferType proj
                let fieldType ← inferType fieldVal
                unless ← isDefEq projType fieldType do
                  throwError "parent field '{parentField}' {← mkHasTypeButIsExpectedMsg proj fieldType}"
                unless ← isDefEq proj fieldVal do
                  throwError "parent field '{parentField}'{indentExpr proj}\nis not definitionally equal to overlapping field{indentExpr fieldVal}"
                trace[Elab.struct] "checked field '{parentField}' from parent '{parentTy}' is definitionally equal"
              | none =>
                modify fun s => { s with fieldMap := s.fieldMap.insert parentField proj }
                trace[Elab.struct] "added field '{parentField}' from parent '{parentTy}'"
            -- All the fields have been added, update the list of remaining fields.
            remainingFields := remainingFields.filter (!parentFields.contains ·)
            -- Move the deferred list back the front of the work list
            worklist := deferred.reverseAux worklist
            deferred := []
          catch ex =>
            restoreState saved
            -- Failed, don't try this parent again.
            trace[Elab.struct] "failed to use instance for {parentTy}\n{ex.toMessageData}"

private def main : StructInstM Expr := do
  initializeState
  unless (← read).ellipsis && (← readThe Term.Context).inPattern do
    -- Inside a pattern with ellipsis mode, users expect to match just the fields provided.
    addParentInstanceFields
  loop

/--
Main elaborator for structure instances.
-/
private def elabStructInstView (s : StructInstView) (structName : Name) (structType? : Option Expr) :
    TermElabM Expr := withRef s.ref do
  let env ← getEnv
  let ctorVal := getStructureCtor env structName
  if isPrivateNameFromImportedModule env ctorVal.name then
    throwError "invalid \{...} notation, constructor for '{structName}' is marked as private"
  let { ctorFn, ctorFnType, structType, levels, params } ← mkCtorHeader ctorVal structType?
  let (_, fields) ← expandFields structName s.fields (recover := (← read).errToSorry)
  let fields ← addSourceFields structName s.sources.explicit fields
  trace[Elab.struct] "expanded fields:\n{MessageData.joinSep (fields.toList.map (fun (_, field) => m!"- {MessageData.nestD (toMessageData field)}")) "\n"}"
  let ellipsis := s.sources.implicit.isSome
  let (val, _) ← main
    |>.run { view := s, structName, structType, levels, params, fieldViews := fields, val := ctorFn, ellipsis }
    |>.run { type := ctorFnType }
  return val

/--
If `stx` is of the form `{ s₁, ..., sₙ with ... }` and `sᵢ` is not a local variable,
expands into `let __src := sᵢ; { ..., __src, ... with ... }`.
The significance of `__src` is that the variable is treated as an implementation-detail local variable,
which can be unfolded by `simp` when `zetaDelta := false`.

Note that this one is not a `Macro` because we need to access the local context.

Note also that having this as a separate step from main elaboration lets it postpone without re-elaborating the sources.
-/
private def expandNonAtomicExplicitSources (stx : Syntax) : TermElabM (Option Syntax) := do
  let sourcesOpt := stx[1]
  if sourcesOpt.isNone then
    return none
  else
    let sources := sourcesOpt[0]
    if sources.isMissing then
      throwAbortTerm
    let sources := sources.getSepArgs
    if (← sources.allM fun source => return (← isLocalIdent? source).isSome) then
      return none
    if sources.any (·.isMissing) then
      throwAbortTerm
    return some (← go sources.toList #[])
where
  /--
  If the source is a local, we can use it.
  *However*, we need to watch out that the local doesn't have implicit arguemnts,
  since that could cause multiple evaluation.
  For simplicity, we just check that the fvar isn't a forall.
  -/
  isSuitableLocalIdent (term : Syntax) : TermElabM Bool := do
    let some fvar ← isLocalIdent? term | return false
    let type ← whnf (← inferType fvar)
    return !type.isForall
  go (sources : List Syntax) (sourcesNew : Array Syntax) : TermElabM Syntax := do
    match sources with
    | [] =>
      let sources := Syntax.mkSep sourcesNew (mkAtomFrom stx ", ")
      return stx.setArg 1 (stx[1].setArg 0 sources)
    | source :: sources =>
      if (← isSuitableLocalIdent source) then
        go sources (sourcesNew.push source)
      else
        withFreshMacroScope do
          /-
          Recall that local variables starting with `__` are treated as impl detail.
          See `LocalContext.lean`.
          Moreover, implementation detail let-vars are unfolded by `simp`
          even when `zetaDelta := false`.
          Motivation: the following failure when `zetaDelta := true`
          ```
          structure A where
            a : Nat
          structure B extends A where
            b : Nat
            w : a = b
          def x : A where a := 37
          @[simp] theorem x_a : x.a = 37 := rfl

          def y : B := { x with b := 37, w := by simp }
          ```
          -/
          let sourceNew ← `(__src)
          let r ← go sources (sourcesNew.push sourceNew)
          `(let __src := $source; $r)

/--
Uses the expected type and sources to determine the structure type name to use for the structure instance.
This function tries to postpone execution if the expected type is not available.

If the expected type is available and it is a structure, then we use it.
Otherwise, we use the type of the first source.

Possibly returns the expected structure type as well.
-/
private def getStructName (expectedType? : Option Expr) (sourceView : SourcesView) : TermElabM (Name × Option Expr) := do
  tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | none => useSource ()
  | some expectedType =>
    let expectedType ← whnf expectedType
    match expectedType.getAppFn with
    | Expr.const constName _ =>
      unless isStructure (← getEnv) constName do
        throwError "invalid \{...} notation, structure type expected{indentExpr expectedType}"
      return (constName, expectedType)
    | _ => useSource ()
where
  useSource : Unit → TermElabM (Name × Option Expr) := fun _ => do
    unless sourceView.explicit.isEmpty do
      return (sourceView.explicit[0]!.structName, none)
    match expectedType? with
    | some expectedType => throwUnexpectedExpectedType expectedType
    | none => throwUnknownExpectedType
  throwUnknownExpectedType :=
    throwError "invalid \{...} notation, expected type is not known"
  throwUnexpectedExpectedType type (kind := "expected") := do
    let type ← instantiateMVars type
    if type.getAppFn.isMVar then
      throwUnknownExpectedType
    else
      throwError "invalid \{...} notation, {kind} type is not of the form (C ...){indentExpr type}"

@[builtin_term_elab structInst] def elabStructInst : TermElab := fun stx expectedType? => do
  match (← expandNonAtomicExplicitSources stx) with
  | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | none =>
    let sourcesView ← getStructSources stx
    if let some modifyOp ← isModifyOp? stx then
      elabModifyOp stx modifyOp sourcesView expectedType?
    else
      let (structName, structType?) ← getStructName expectedType? sourcesView
      let struct ← liftMacroM <| mkStructView stx sourcesView
      trace[Elab.struct] "StructInstView:{indentD (toMessageData struct)}"
      let r ← withSynthesize (postpone := .yes) <| elabStructInstView struct structName structType?
      trace[Elab.struct] "result:{indentExpr r}"
      return r

builtin_initialize
  registerTraceClass `Elab.struct
  registerTraceClass `Elab.struct.modifyOp

end Lean.Elab.Term.StructInst
