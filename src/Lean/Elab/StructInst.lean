/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
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
and also they do correct processing of default values, which are complicated due to the fact that `structure`s can override default values of their parents.

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

def mkStructInstField (lval : TSyntax ``Parser.Term.structInstLVal) (binders : TSyntaxArray ``Parser.Term.structInstFieldBinder)
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
  let fields := fields?.zipWith fields Option.getD
  let structInstFields := structInstFields.setArg 0 <| Syntax.mkSep fields (mkAtomFrom stx ", ")
  return stx.setArg 2 structInstFields

/--
If `stx` is of the form `{ s₁, ..., sₙ with ... }` and `sᵢ` is not a local variable,
expands into `let __src := sᵢ; { ..., __src, ... with ... }`.
The significance of `__src` is that the variable is treated as an implementation-detail local variable,
which can be unfolded by `simp` when `zetaDelta := false`.

Note that this one is not a `Macro` because we need to access the local context.
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
  go (sources : List Syntax) (sourcesNew : Array Syntax) : TermElabM Syntax := do
    match sources with
    | [] =>
      let sources := Syntax.mkSep sourcesNew (mkAtomFrom stx ", ")
      return stx.setArg 1 (stx[1].setArg 0 sources)
    | source :: sources =>
      if (← isLocalIdent? source).isSome then
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
An *explicit source* is one of the structures `sᵢ` that appear in `{ s₁, …, sₙ with … }`.
-/
structure ExplicitSourceView where
  /-- The syntax of the explicit source. -/
  stx        : Syntax
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

/-- Returns `true` if the structure instance has no sources (neither explicit sources nor a `..`). -/
def SourcesView.isNone : SourcesView → Bool
  | { explicit := #[], implicit := none } => true
  | _ => false

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
        return { stx, structName }
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
          if s.getKind == ``Lean.Parser.Term.structInstArrayRef then
            throwErrorAt arg "invalid \{...} notation, at most one `[..]` at a given level"
          else
            throwErrorAt arg "invalid \{...} notation, can't mix field and `[..]` at a given level"
      else
        match s? with
        | none   => return some arg
        | some s =>
          if s.getKind == ``Lean.Parser.Term.structInstArrayRef then
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
private def elabModifyOp (stx modifyOp : Syntax) (sources : Array ExplicitSourceView) (expectedType? : Option Expr) : TermElabM Expr := do
  if sources.size > 1 then
    throwError "invalid \{...} notation, multiple sources and array update is not supported."
  let cont (val : Syntax) : TermElabM Expr := do
    let lval := modifyOp[0][0]
    let idx  := lval[1]
    let self := sources[0]!.stx
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
Gets the structure name for the structure instance from the expected type and the sources.
This method tries to postpone execution if the expected type is not available.

If the expected type is available and it is a structure, then we use it.
Otherwise, we use the type of the first source.
-/
private def getStructName (expectedType? : Option Expr) (sourceView : SourcesView) : TermElabM Name := do
  tryPostponeIfNoneOrMVar expectedType?
  let useSource : Unit → TermElabM Name := fun _ => do
    unless sourceView.explicit.isEmpty do
      return sourceView.explicit[0]!.structName
    match expectedType? with
    | some expectedType => throwUnexpectedExpectedType expectedType
    | none => throwUnknownExpectedType
  match expectedType? with
  | none => useSource ()
  | some expectedType =>
    let expectedType ← whnf expectedType
    match expectedType.getAppFn with
    | Expr.const constName _ =>
      unless isStructure (← getEnv) constName do
        throwError "invalid \{...} notation, structure type expected{indentExpr expectedType}"
      return constName
    | _ => useSource ()
where
  throwUnknownExpectedType :=
    throwError "invalid \{...} notation, expected type is not known"
  throwUnexpectedExpectedType type (kind := "expected") := do
    let type ← instantiateMVars type
    if type.getAppFn.isMVar then
      throwUnknownExpectedType
    else
      throwError "invalid \{...} notation, {kind} type is not of the form (C ...){indentExpr type}"

/--
A component of a left-hand side for a field appearing in structure instance syntax.
-/
inductive FieldLHS where
  /-- A name component for a field left-hand side. For example, `x` and `y` in `{ x.y := v }`. -/
  | fieldName  (ref : Syntax) (name : Name)
  /-- A numeric index component for a field left-hand side. For example `3` in `{ x.3 := v }`. -/
  | fieldIndex (ref : Syntax) (idx : Nat)
  /-- An array indexing component for a field left-hand side. For example `[3]` in `{ arr[3] := v }`. -/
  | modifyOp   (ref : Syntax) (index : Syntax)
  deriving Inhabited

instance : ToFormat FieldLHS where
  format
    | .fieldName _ n  => format n
    | .fieldIndex _ i => format i
    | .modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"

mutual
  /--
  `FieldVal StructInstView` is a representation of a field value in the structure instance.
  -/
  inductive FieldVal where
    /-- A `term` to use for the value of the field. -/
    | term (stx : Syntax)         : FieldVal
    /-- A `StructInstView` to use for the value of a subobject field. -/
    | nested (s : StructInstView) : FieldVal
    /-- A field that was not provided and should be synthesized using default values. -/
    | default                     : FieldVal
    deriving Inhabited

  /--
  `Field StructInstView` is a representation of a field in the structure instance.
  -/
  structure Field where
    /-- The whole field syntax. -/
    ref   : Syntax
    /-- The LHS decomposed into components. -/
    lhs   : List FieldLHS
    /-- The value of the field. -/
    val   : FieldVal
    /-- The elaborated field value, filled in at `elabStruct`.
    Missing fields use a metavariable for the elaborated value and are later solved for in `DefaultFields.propagate`. -/
    expr? : Option Expr := none
    deriving Inhabited

  /--
  The view for structure instance notation.
  -/
  structure StructInstView where
    /-- The syntax for the whole structure instance. -/
    ref : Syntax
    /-- The name of the structure for the type of the structure instance. -/
    structName : Name
    /-- Used for default values, to propagate structure type parameters. It is initially empty, and then set at `elabStruct`. -/
    params : Array (Name × Expr)
    /-- The fields of the structure instance. -/
    fields : List Field
    /-- The additional sources for fields for the structure instance. -/
    sources : SourcesView
    deriving Inhabited
end

/--
Returns if the field has a single component in its LHS.
-/
def Field.isSimple : Field → Bool
  | { lhs := [_], .. } => true
  | _                  => false

/-- `true` iff all fields of the given structure are marked as `default` -/
partial def StructInstView.allDefault (s : StructInstView) : Bool :=
  s.fields.all fun { val := val,  .. } => match val with
    | .term _   => false
    | .default  => true
    | .nested s => allDefault s

def formatField (formatStruct : StructInstView → Format) (field : Field) : Format :=
  Format.joinSep field.lhs " . " ++ " := " ++
    match field.val with
    | .term v   => v.prettyPrint
    | .nested s => formatStruct s
    | .default  => "<default>"

partial def formatStruct : StructInstView → Format
  | ⟨_, _,          _, fields, source⟩ =>
    let fieldsFmt := Format.joinSep (fields.map (formatField formatStruct)) ", "
    let implicitFmt := if source.implicit.isSome then " .. " else ""
    if source.explicit.isEmpty then
      "{" ++ fieldsFmt ++ implicitFmt ++ "}"
    else
      "{" ++ format (source.explicit.map (·.stx)) ++ " with " ++ fieldsFmt ++ implicitFmt ++ "}"

instance : ToFormat StructInstView := ⟨formatStruct⟩
instance : ToString StructInstView := ⟨toString ∘ format⟩

instance : ToFormat Field := ⟨formatField formatStruct⟩
instance : ToString Field := ⟨toString ∘ format⟩

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
  | .modifyOp   stx _    => stx
  | .fieldName  stx name => if first then mkIdentFrom stx name else mkGroupNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
  | .fieldIndex stx _    => if first then stx else mkGroupNode #[mkAtomFrom stx ".", stx]

/--
Converts a `FieldVal StructInstView` back into syntax. Only supports `.term`, and it assumes the `stx` field has the correct structure.
-/
private def FieldVal.toSyntax : FieldVal → Syntax
  | .term stx => stx
  | _         => unreachable!

/--
Converts a `Field StructInstView` back into syntax. Used to construct synthetic structure instance notation for subobjects in `StructInst.expandStruct` processing.
-/
private def Field.toSyntax : Field → Syntax
  | field =>
    let stx := field.ref
    let stx := stx.setArg 1 <| stx[1].setArg 2 <| stx[1][2].setArg 1 field.val.toSyntax
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
Creates a structure instance view from structure instance notation
and the computed structure name (from `Lean.Elab.Term.StructInst.getStructName`)
and structure source view (from `Lean.Elab.Term.StructInst.getStructSources`).
-/
private def mkStructView (stx : Syntax) (structName : Name) (sources : SourcesView) : MacroM StructInstView := do
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
  let fields ← stx[2][0].getSepArgs.toList.mapM fun fieldStx => do
    let `(Parser.Term.structInstField| $lval:structInstLVal := $val) := fieldStx | Macro.throwUnsupported
    let first ← toFieldLHS lval.raw[0]
    let rest  ← lval.raw[1].getArgs.toList.mapM toFieldLHS
    return { ref := fieldStx, lhs := first :: rest, val := FieldVal.term val : Field }
  return { ref := stx, structName, params := #[], fields, sources }

def StructInstView.modifyFieldsM {m : Type → Type} [Monad m] (s : StructInstView) (f : List Field → m (List Field)) : m StructInstView :=
  match s with
  | { ref, structName, params, fields, sources } => return { ref, structName, params, fields := (← f fields), sources }

def StructInstView.modifyFields (s : StructInstView) (f : List Field → List Field) : StructInstView :=
  Id.run <| s.modifyFieldsM f

/-- Expands name field LHSs with multi-component names into multi-component LHSs. -/
private def expandCompositeFields (s : StructInstView) : StructInstView :=
  s.modifyFields fun fields => fields.map fun field => match field with
    | { lhs := .fieldName _ (.str Name.anonymous ..) :: _, .. } => field
    | { lhs := .fieldName ref n@(.str ..) :: rest, .. } =>
      let newEntries := n.components.map <| FieldLHS.fieldName ref
      { field with lhs := newEntries ++ rest }
    | _ => field

/-- Replaces numeric index field LHSs with the corresponding named field, or throws an error if no such field exists. -/
private def expandNumLitFields (s : StructInstView) : TermElabM StructInstView :=
  s.modifyFieldsM fun fields => do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    fields.mapM fun field => match field with
      | { lhs := .fieldIndex ref idx :: rest, .. } =>
        if idx == 0 then throwErrorAt ref "invalid field index, index must be greater than 0"
        else if idx > fieldNames.size then throwErrorAt ref "invalid field index, structure has only #{fieldNames.size} fields"
        else return { field with lhs := .fieldName ref fieldNames[idx - 1]! :: rest }
      | _ => return field

/--
Expands fields that are actually represented as fields of subobject fields.

For example, consider the following structures:
```
structure A where
  x : Nat

structure B extends A where
  y : Nat

structure C extends B where
  z : Bool
```
This method expands parent structure fields using the path to the parent structure.
For example,
```
{ x := 0, y := 0, z := true : C }
```
is expanded into
```
{ toB.toA.x := 0, toB.y := 0, z := true : C }
```
-/
private def expandParentFields (s : StructInstView) : TermElabM StructInstView := do
  let env ← getEnv
  s.modifyFieldsM fun fields => fields.mapM fun field => do match field with
    | { lhs := .fieldName ref fieldName :: _,    .. } =>
      addCompletionInfo <| CompletionInfo.fieldId ref fieldName (← getLCtx) s.structName
      match findField? env s.structName fieldName with
      | none => throwErrorAt ref "'{fieldName}' is not a field of structure '{.ofConstName s.structName}'"
      | some baseStructName =>
        if baseStructName == s.structName then pure field
        else match getPathToBaseStructure? env baseStructName s.structName with
          | some path =>
            let path := path.map fun funName => match funName with
              | .str _ s => .fieldName ref (Name.mkSimple s)
              | _        => unreachable!
            return { field with lhs := path ++ field.lhs }
          | _ => throwErrorAt ref "failed to access field '{fieldName}' in parent structure"
    | _ => return field

private abbrev FieldMap := Std.HashMap Name (List Field)

/--
Creates a hash map collecting all fields with the same first name component.
Throws an error if there are multiple simple fields with the same name.
Used by `StructInst.expandStruct` processing.
-/
private def mkFieldMap (fields : List Field) : TermElabM FieldMap :=
  fields.foldlM (init := {}) fun fieldMap field =>
    match field.lhs with
    | .fieldName _ fieldName :: _    =>
      match fieldMap[fieldName]? with
      | some (prevField::restFields) =>
        if field.isSimple || prevField.isSimple then
          throwErrorAt field.ref "field '{fieldName}' has already been specified"
        else
          return fieldMap.insert fieldName (field::prevField::restFields)
      | _ => return fieldMap.insert fieldName [field]
    | _ => unreachable!

/--
Given a value of the hash map created by `mkFieldMap`, returns true if the value corresponds to a simple field.
-/
private def isSimpleField? : List Field → Option Field
  | [field] => if field.isSimple then some field else none
  | _       => none

/--
Creates projection notation for the given structure field. Used
-/
def mkProjStx? (s : Syntax) (structName : Name) (fieldName : Name) : TermElabM (Option Syntax) := do
  if (findField? (← getEnv) structName fieldName).isNone then
    return none
  return some <|
    mkNode ``Parser.Term.explicit
      #[mkAtomFrom s "@",
        mkNode ``Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]]

/--
Finds a simple field of the given name.
-/
def findField? (fields : List Field) (fieldName : Name) : Option Field :=
  fields.find? fun field =>
    match field.lhs with
    | [.fieldName _ n] => n == fieldName
    | _                => false

mutual

  /--
  Groups compound fields according to which subobject they are from.
  -/
  private partial def groupFields (s : StructInstView) : TermElabM StructInstView := do
    let env ← getEnv
    withRef s.ref do
    s.modifyFieldsM fun fields => do
      let fieldMap ← mkFieldMap fields
      fieldMap.toList.mapM fun ⟨fieldName, fields⟩ => do
        match isSimpleField? fields with
        | some field => pure field
        | none =>
          let substructFields := fields.map fun field => { field with lhs := field.lhs.tail! }
          let field := fields.head!
          match Lean.isSubobjectField? env s.structName fieldName with
          | some substructName =>
            let substruct := { ref := s.ref, structName := substructName, params := #[], fields := substructFields, sources := s.sources }
            let substruct ← expandStruct substruct
            pure { field with lhs := [field.lhs.head!], val := FieldVal.nested substruct }
          | none =>
            let updateSource (structStx : Syntax) : TermElabM Syntax := do
              let sourcesNew ← s.sources.explicit.filterMapM fun source => mkProjStx? source.stx source.structName fieldName
              let explicitSourceStx := if sourcesNew.isEmpty then mkNullNode else mkSourcesWithSyntax sourcesNew
              let implicitSourceStx := s.sources.implicit.getD (mkNode ``Parser.Term.optEllipsis #[mkNullNode])
              return (structStx.setArg 1 explicitSourceStx).setArg 3 implicitSourceStx
            let valStx := s.ref -- construct substructure syntax using s.ref as template
            let valStx := valStx.setArg 4 mkNullNode -- erase optional expected type
            let args   := substructFields.toArray.map (·.toSyntax)
            let fieldsStx := mkNode ``Parser.Term.structInstFields
              #[mkNullNode <| mkSepArray args (mkAtom ",")]
            let valStx := valStx.setArg 2 fieldsStx
            let valStx ← updateSource valStx
            return { field with lhs := [field.lhs.head!], val := FieldVal.term valStx }
  /--
  Adds in the missing fields using the explicit sources.
  Invariant: a missing field always comes from the first source that can provide it.
  -/
  private partial def addMissingFields (s : StructInstView) : TermElabM StructInstView := do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    let ref := s.ref.mkSynthetic
    withRef ref do
      let fields ← fieldNames.foldlM (init := []) fun fields fieldName => do
        match findField? s.fields fieldName with
        | some field => return field::fields
        | none       =>
          let addField (val : FieldVal) : TermElabM (List Field) := do
            return { ref, lhs := [FieldLHS.fieldName ref fieldName], val := val } :: fields
          match Lean.isSubobjectField? env s.structName fieldName with
          | some substructName =>
            -- Get all leaf fields of `substructName`
            let downFields := getStructureFieldsFlattened env substructName false
            -- Filter out all explicit sources that do not share a leaf field keeping
            -- structure with no fields
            let filtered := s.sources.explicit.filter fun sources =>
              let sourceFields := getStructureFieldsFlattened env sources.structName false
              sourceFields.any (fun name => downFields.contains name) || sourceFields.isEmpty
            -- Take the first such one remaining
            match filtered[0]? with
            | some src =>
              -- If it is the correct type, use it
              if src.structName == substructName then
                addField (FieldVal.term src.stx)
              -- If a projection of it is the correct type, use it
              else if let some val ← mkProjStx? src.stx src.structName fieldName then
                addField (FieldVal.term val)
              -- No sources could provide this subobject in the proper order.
              -- Recurse to handle default values for fields.
              else
                let substruct := { ref, structName := substructName, params := #[], fields := [], sources := s.sources }
                let substruct ← expandStruct substruct
                addField (FieldVal.nested substruct)
            -- No sources could provide this subobject.
            -- Recurse to handle default values for fields.
            | none =>
              let substruct := { ref, structName := substructName, params := #[], fields := [], sources := s.sources }
              let substruct ← expandStruct substruct
              addField (FieldVal.nested substruct)
          -- Since this is not a subobject field, we are free to use the first source that can
            -- provide it.
          | none =>
            if let some val ← s.sources.explicit.findSomeM? fun source => mkProjStx? source.stx source.structName fieldName then
              addField (FieldVal.term val)
            else if s.sources.implicit.isSome then
              addField (FieldVal.term (mkHole ref))
            else
              addField FieldVal.default
      return { s with fields := fields.reverse }

  /--
  Expands all fields of the structure instance, consolidates compound fields into subobject fields, and adds missing fields.
  -/
  private partial def expandStruct (s : StructInstView) : TermElabM StructInstView := do
    let s := expandCompositeFields s
    let s ← expandNumLitFields s
    let s ← expandParentFields s
    let s ← groupFields s
    addMissingFields s

end

/--
The constructor to use for the structure instance notation.
-/
structure CtorHeaderResult where
  /-- The constructor function with applied structure parameters. -/
  ctorFn     : Expr
  /-- The type of `ctorFn` -/
  ctorFnType : Expr
  /-- Instance metavariables for structure parameters that are instance implicit. -/
  instMVars  : Array MVarId
  /-- Type parameter names and metavariables for each parameter. Used to seed `StructInstView.params`. -/
  params     : Array (Name × Expr)

private def mkCtorHeaderAux : Nat → Expr → Expr → Array MVarId → Array (Name × Expr) → TermElabM CtorHeaderResult
  | 0,   type, ctorFn, instMVars, params => return { ctorFn , ctorFnType := type, instMVars, params }
  | n+1, type, ctorFn, instMVars, params => do
    match (← whnfForall type) with
    | .forallE paramName d b c =>
      match c with
      | .instImplicit =>
        let a ← mkFreshExprMVar d .synthetic
        mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) (instMVars.push a.mvarId!) (params.push (paramName, a))
      | _ =>
        let a ← mkFreshExprMVar d
        mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) instMVars (params.push (paramName, a))
    | _ => throwError "unexpected constructor type"

private partial def getForallBody : Nat → Expr → Option Expr
  | i+1, .forallE _ _ b _ => getForallBody i b
  | _+1, _                => none
  | 0,   type             => type

/-- Attempts to use the expected type to solve for structure parameters. -/
private def propagateExpectedType (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit := do
  match expectedType? with
  | none              => return ()
  | some expectedType =>
    match getForallBody numFields type with
      | none           => pure ()
      | some typeBody =>
        unless typeBody.hasLooseBVars do
          discard <| isDefEq expectedType typeBody

/-- Elaborates the structure constructor using the expected type, filling in all structure parameters. -/
private def mkCtorHeader (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
  let us ← mkFreshLevelMVars ctorVal.levelParams.length
  let val  := Lean.mkConst ctorVal.name us
  let type ← instantiateTypeLevelParams (ConstantInfo.ctorInfo ctorVal) us
  let r ← mkCtorHeaderAux ctorVal.numParams type val #[] #[]
  propagateExpectedType r.ctorFnType ctorVal.numFields expectedType?
  synthesizeAppInstMVars r.instMVars r.ctorFn
  return r

/-- Annotates an expression that it is a value for a missing field. -/
def markDefaultMissing (e : Expr) : Expr :=
  mkAnnotation `structInstDefault e

/-- If the expression has been annotated by `markDefaultMissing`, returns the unannotated expression. -/
def defaultMissing? (e : Expr) : Option Expr :=
  annotation? `structInstDefault e

/-- Throws "failed to elaborate field" error. -/
def throwFailedToElabField {α} (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
  throwError "failed to elaborate field '{fieldName}' of '{structName}, {msgData}"

/-- If the struct has all-missing fields, tries to synthesize the structure using typeclass inference. -/
def trySynthStructInstance? (s : StructInstView) (expectedType : Expr) : TermElabM (Option Expr) := do
  if !s.allDefault then
    return none
  else
    try synthInstance? expectedType catch _ => return none

/-- The result of elaborating a `StructInstView` structure instance view. -/
structure ElabStructResult where
  /-- The elaborated value. -/
  val       : Expr
  /-- The modified `StructInstView` view after elaboration. -/
  struct    : StructInstView
  /-- Metavariables for instance implicit fields. These will be registered after default value propagation. -/
  instMVars : Array MVarId

/--
Main elaborator for structure instances.
-/
private partial def elabStructInstView (s : StructInstView) (expectedType? : Option Expr) : TermElabM ElabStructResult := withRef s.ref do
  let env ← getEnv
  let ctorVal := getStructureCtor env s.structName
  if isPrivateNameFromImportedModule env ctorVal.name then
    throwError "invalid \{...} notation, constructor for `{s.structName}` is marked as private"
  -- We store the parameters at the resulting `StructInstView`. We use this information during default value propagation.
  let { ctorFn, ctorFnType, params, .. } ← mkCtorHeader ctorVal expectedType?
  let (e, _, fields, instMVars) ← s.fields.foldlM (init := (ctorFn, ctorFnType, [], #[])) fun (e, type, fields, instMVars) field => do
    match field.lhs with
    | [.fieldName ref fieldName] =>
      let type ← whnfForall type
      trace[Elab.struct] "elabStruct {field}, {type}"
      match type with
      | .forallE _ d b bi =>
        let cont (val : Expr) (field : Field) (instMVars := instMVars) : TermElabM (Expr × Expr × List Field × Array MVarId) := do
          pushInfoTree <| InfoTree.node (children := {}) <| Info.ofFieldInfo {
            projName := s.structName.append fieldName, fieldName, lctx := (← getLCtx), val, stx := ref }
          let e     := mkApp e val
          let type  := b.instantiate1 val
          let field := { field with expr? := some val }
          return (e, type, field::fields, instMVars)
        match field.val with
        | .term stx => cont (← elabTermEnsuringType stx d.consumeTypeAnnotations) field
        | .nested s =>
          -- if all fields of `s` are marked as `default`, then try to synthesize instance
          match (← trySynthStructInstance? s d) with
          | some val => cont val { field with val := FieldVal.term (mkHole field.ref) }
          | none     =>
            let { val, struct := sNew, instMVars := instMVarsNew } ← elabStructInstView s (some d)
            let val ← ensureHasType d val
            cont val { field with val := FieldVal.nested sNew } (instMVars ++ instMVarsNew)
        | .default  =>
          match d.getAutoParamTactic? with
          | some (.const tacticDecl ..) =>
            match evalSyntaxConstant env (← getOptions) tacticDecl with
            | .error err       => throwError err
            | .ok tacticSyntax =>
              let stx ← `(by $tacticSyntax)
              -- See comment in `Lean.Elab.Term.ElabAppArgs.processExplicitArg` about `tacticSyntax`.
              -- We add info to get reliable positions for messages from evaluating the tactic script.
              let info := field.ref.getHeadInfo
              let stx := stx.raw.rewriteBottomUp (·.setInfo info)
              let type := (d.getArg! 0).consumeTypeAnnotations
              let mvar ← mkTacticMVar type stx (.fieldAutoParam fieldName s.structName)
              -- Note(kmill): We are adding terminfo to simulate a previous implementation that elaborated `tacticBlock`.
              -- (See the aforementioned `processExplicitArg` for a comment about this.)
              addTermInfo' stx mvar
              cont mvar field
          | _ =>
            if bi == .instImplicit then
              let val ← withRef field.ref <| mkFreshExprMVar d .synthetic
              cont val field (instMVars.push val.mvarId!)
            else
              let val ← withRef field.ref <| mkFreshExprMVar (some d)
              cont (markDefaultMissing val) field
      | _ => withRef field.ref <| throwFailedToElabField fieldName s.structName m!"unexpected constructor type{indentExpr type}"
    | _ => throwErrorAt field.ref "unexpected unexpanded structure field"
  return { val := e, struct := { s with fields := fields.reverse, params }, instMVars }

namespace DefaultFields

/--
Context for default value propagation.
-/
structure Context where
  /-- The current path through `.nested` subobject structures. We must search for default values overridden in derived structures. -/
  structs : Array StructInstView := #[]
  /-- The collection of structures that could provide a default value. -/
  allStructNames : Array Name := #[]
  /--
  Consider the following example:
  ```lean
  structure A where
    x : Nat := 1

  structure B extends A where
    y : Nat := x + 1
    x := y + 1

  structure C extends B where
    z : Nat := 2*y
    x := z + 3
  ```
  And we are trying to elaborate a structure instance for `C`. There are default values for `x` at `A`, `B`, and `C`.
  We say the default value at `C` has distance 0, the one at `B` distance 1, and the one at `A` distance 2.
  The field `maxDistance` specifies the maximum distance considered in a round of Default field computation.
  Remark: since `C` does not set a default value of `y`, the default value at `B` is at distance 0.

  The fixpoint for setting default values works in the following way.
  - Keep computing default values using `maxDistance == 0`.
  - We increase `maxDistance` whenever we failed to compute a new default value in a round.
  - If `maxDistance > 0`, then we interrupt a round as soon as we compute some default value.
    We use depth-first search.
  - We sign an error if no progress is made when `maxDistance` == structure hierarchy depth (2 in the example above).
  -/
  maxDistance : Nat := 0

/--
State for default value propagation
-/
structure State where
  /-- Whether progress has been made so far on this round of the propagation loop. -/
  progress : Bool := false

/-- Collects all structures that may provide default values for fields. -/
partial def collectStructNames (struct : StructInstView) (names : Array Name) : Array Name :=
  let names := names.push struct.structName
  struct.fields.foldl (init := names) fun names field =>
    match field.val with
    | .nested struct => collectStructNames struct names
    | _ => names

/-- Gets the maximum nesting depth of subobjects. -/
partial def getHierarchyDepth (struct : StructInstView) : Nat :=
  struct.fields.foldl (init := 0) fun max field =>
    match field.val with
    | .nested struct => Nat.max max (getHierarchyDepth struct + 1)
    | _ => max

/-- Returns whether the field is still missing. -/
def isDefaultMissing? [Monad m] [MonadMCtx m] (field : Field) : m Bool := do
  if let some expr := field.expr? then
    if let some (.mvar mvarId) := defaultMissing? expr then
      unless (← mvarId.isAssigned) do
        return true
  return false

/-- Returns a field that is still missing. -/
partial def findDefaultMissing? [Monad m] [MonadMCtx m] (struct : StructInstView) : m (Option Field) :=
  struct.fields.findSomeM? fun field => do
   match field.val with
   | .nested struct => findDefaultMissing? struct
   | _ => return if (← isDefaultMissing? field) then field else none

/-- Returns all fields that are still missing. -/
partial def allDefaultMissing [Monad m] [MonadMCtx m] (struct : StructInstView) : m (Array Field) :=
  go struct *> get |>.run' #[]
where
  go (struct : StructInstView) : StateT (Array Field) m Unit :=
    for field in struct.fields do
      if let .nested struct := field.val then
        go struct
      else if (← isDefaultMissing? field) then
        modify (·.push field)

/-- Returns the name of the field. Assumes all fields under consideration are simple and named. -/
def getFieldName (field : Field) : Name :=
  match field.lhs with
  | [.fieldName _ fieldName] => fieldName
  | _ => unreachable!

abbrev M := ReaderT Context (StateRefT State TermElabM)

/-- Returns whether we should interrupt the round because we have made progress allowing nonzero depth. -/
def isRoundDone : M Bool := do
  return (← get).progress && (← read).maxDistance > 0

/-- Returns the `expr?` for the given field. -/
def getFieldValue? (struct : StructInstView) (fieldName : Name) : Option Expr :=
  struct.fields.findSome? fun field =>
    if getFieldName field == fieldName then
      field.expr?
    else
      none

/-- Instantiates a default value from the given default value declaration, if applicable. -/
partial def mkDefaultValue? (struct : StructInstView) (cinfo : ConstantInfo) : TermElabM (Option Expr) :=
  withRef struct.ref do
  let us ← mkFreshLevelMVarsFor cinfo
  process (← instantiateValueLevelParams cinfo us)
where
  process : Expr → TermElabM (Option Expr)
  | .lam n d b c => withRef struct.ref do
    if c.isExplicit then
      let fieldName := n
      match getFieldValue? struct fieldName with
      | none     => return none
      | some val =>
        let valType ← inferType val
        if (← isDefEq valType d) then
          process (b.instantiate1 val)
        else
          return none
    else
      if let some (_, param) := struct.params.find? fun (paramName, _) => paramName == n then
        -- Recall that we did not use to have support for parameter propagation here.
        if (← isDefEq (← inferType param) d) then
          process (b.instantiate1 param)
        else
          return none
      else
        let arg ← mkFreshExprMVar d
        process (b.instantiate1 arg)
  | e =>
    let_expr id _ a := e | return some e
    return some a

/--
Reduces a default value. It performs beta reduction and projections of the given structures to reduce them to the provided values for fields.
-/
partial def reduce (structNames : Array Name) (e : Expr) : MetaM Expr := do
  match e with
  | .forallE ..   =>
    forallTelescope e fun xs b => withReduceLCtx xs do
      mkForallFVars xs (← reduce structNames b)
  | .lam .. | .letE .. =>
    lambdaLetTelescope e fun xs b => withReduceLCtx xs do
      mkLambdaFVars (usedLetOnly := true) xs (← reduce structNames b)
  | .proj _ i b   =>
    match (← Meta.project? b i) with
    | some r => reduce structNames r
    | none   => return e.updateProj! (← reduce structNames b)
  | .app f .. =>
    -- Recall that proposition fields are theorems. Thus, we must set transparency to .all
    -- to ensure they are unfolded here
    match (← withTransparency .all <| reduceProjOf? e structNames.contains) with
    | some r => reduce structNames r
    | none   =>
      let f := f.getAppFn
      let f' ← reduce structNames f
      if f'.isLambda then
        let revArgs := e.getAppRevArgs
        reduce structNames (f'.betaRev revArgs)
      else
        let args ← e.getAppArgs.mapM (reduce structNames)
        return mkAppN f' args
  | .mdata _ b =>
    let b ← reduce structNames b
    if (defaultMissing? e).isSome && !b.isMVar then
      return b
    else
      return e.updateMData! b
  | .mvar mvarId =>
    match (← getExprMVarAssignment? mvarId) with
    | some val => if val.isMVar then pure val else reduce structNames val
    | none     => return e
  | e => return e
where
  /--
  Reduce the types and values of the local variables `xs` in the local context.
  -/
  withReduceLCtx {α} (xs : Array Expr) (k : MetaM α) (i : Nat := 0) : MetaM α := do
    if h : i < xs.size then
      let fvarId := xs[i].fvarId!
      let decl ← fvarId.getDecl
      let type ← reduce structNames decl.type
      let mut lctx ← getLCtx
      if let some value := decl.value? then
        let value ← reduce structNames value
        lctx := lctx.modifyLocalDecl fvarId (· |>.setType type |>.setValue value)
      else
        lctx := lctx.modifyLocalDecl fvarId (· |>.setType type)
      withLCtx lctx (← getLocalInstances) (withReduceLCtx xs k (i + 1))
    else
      k

/--
Attempts to synthesize a default value for a missing field `fieldName` using default values from each structure in `structs`.
-/
def tryToSynthesizeDefault (structs : Array StructInstView) (allStructNames : Array Name) (maxDistance : Nat) (fieldName : Name) (mvarId : MVarId) : TermElabM Bool :=
  let rec loop (i : Nat) (dist : Nat) := do
    if dist > maxDistance then
      return false
    else if h : i < structs.size then
      let struct := structs[i]
      match getDefaultFnForField? (← getEnv) struct.structName fieldName with
      | some defFn =>
        let cinfo ← getConstInfo defFn
        let mctx ← getMCtx
        match (← mkDefaultValue? struct cinfo) with
        | none     => setMCtx mctx; loop (i+1) (dist+1)
        | some val =>
          let val ← reduce allStructNames val
          trace[Elab.struct] "default value for {fieldName}:{indentExpr val}"
          match val.find? fun e => (defaultMissing? e).isSome with
          | some _ => setMCtx mctx; loop (i+1) (dist+1)
          | none   =>
            let mvarDecl ← getMVarDecl mvarId
            let val ← ensureHasType mvarDecl.type val
            /-
            We must use `checkedAssign` here to ensure we do not create a cyclic
            assignment. See #3150.
            This can happen when there are holes in the the fields the default value
            depends on.
            Possible improvement: create a new `_` instead of returning `false` when
            `checkedAssign` fails. Reason: the field will not be needed after the
            other `_` are resolved by the user.
            -/
            mvarId.checkedAssign val
      | _ => loop (i+1) dist
    else
      return false
  loop 0 0

/--
Performs one step of default value synthesis.
-/
partial def step (struct : StructInstView) : M Unit :=
  unless (← isRoundDone) do
    withReader (fun ctx => { ctx with structs := ctx.structs.push struct }) do
      for field in struct.fields do
        match field.val with
        | .nested struct => step struct
        | _ => match field.expr? with
          | none      => unreachable!
          | some expr =>
            match defaultMissing? expr with
            | some (.mvar mvarId) =>
              unless (← mvarId.isAssigned) do
                let ctx ← read
                if (← withRef field.ref <| tryToSynthesizeDefault ctx.structs ctx.allStructNames ctx.maxDistance (getFieldName field) mvarId) then
                  modify fun _ => { progress := true }
            | _ => pure ()

/--
Main entry point to default value synthesis in the `M` monad.
-/
partial def propagateLoop (hierarchyDepth : Nat) (d : Nat) (struct : StructInstView) : M Unit := do
  match (← findDefaultMissing? struct) with
  | none       => return () -- Done
  | some field =>
    trace[Elab.struct] "propagate [{d}] [field := {field}]: {struct}"
    if d > hierarchyDepth then
      let missingFields := (← allDefaultMissing struct).map getFieldName
      let missingFieldsWithoutDefault :=
        let env := (← getEnv)
        let structs := (← read).allStructNames
        missingFields.filter fun fieldName => structs.all fun struct =>
          (getDefaultFnForField? env struct fieldName).isNone
      let fieldsToReport :=
        if missingFieldsWithoutDefault.isEmpty then missingFields else missingFieldsWithoutDefault
      throwErrorAt field.ref "fields missing: {fieldsToReport.toList.map (s!"'{·}'") |> ", ".intercalate}"
    else withReader (fun ctx => { ctx with maxDistance := d }) do
      modify fun _ => { progress := false }
      step struct
      if (← get).progress then
        propagateLoop hierarchyDepth 0 struct
      else
        propagateLoop hierarchyDepth (d+1) struct

/--
Synthesizes default values for all missing fields, if possible.
-/
def propagate (struct : StructInstView) : TermElabM Unit :=
  let hierarchyDepth := getHierarchyDepth struct
  let structNames := collectStructNames struct #[]
  propagateLoop hierarchyDepth 0 struct { allStructNames := structNames } |>.run' {}

end DefaultFields

/--
Main entry point to elaborator for structure instance notation, unless the structure instance is a modifyOp.
-/
private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (sources : SourcesView) : TermElabM Expr := do
  let structName ← getStructName expectedType? sources
  let struct ← liftMacroM <| mkStructView stx structName sources
  let struct ← expandStruct struct
  trace[Elab.struct] "{struct}"
  /- We try to synthesize pending problems with `withSynthesize` combinator before trying to use default values.
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
  let { val := r, struct, instMVars } ← withSynthesize (postpone := .yes) <| elabStructInstView struct expectedType?
  trace[Elab.struct] "before propagate {r}"
  DefaultFields.propagate struct
  synthesizeAppInstMVars instMVars r
  return r

@[builtin_term_elab structInst] def elabStructInst : TermElab := fun stx expectedType? => do
  match (← expandNonAtomicExplicitSources stx) with
  | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | none =>
    let sourcesView ← getStructSources stx
    if let some modifyOp ← isModifyOp? stx then
      if sourcesView.explicit.isEmpty then
        throwError "invalid \{...} notation, explicit source is required when using '[<index>] := <value>'"
      elabModifyOp stx modifyOp sourcesView.explicit expectedType?
    else
      elabStructInstAux stx expectedType? sourcesView

builtin_initialize
  registerTraceClass `Elab.struct
  registerTraceClass `Elab.struct.modifyOp

end Lean.Elab.Term.StructInst
