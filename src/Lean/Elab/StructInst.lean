/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindExpr
import Lean.Parser.Term
import Lean.Meta.Structure
import Lean.Elab.App
import Lean.Elab.Binders

namespace Lean.Elab.Term.StructInst

open Meta
open TSyntax.Compat

/-
  Structure instances are of the form:

      "{" >> optional (atomic (sepBy1 termParser ", " >> " with "))
          >> manyIndent (group ((structInstFieldAbbrev <|> structInstField) >> optional ", "))
          >> optEllipsis
          >> optional (" : " >> termParser)
          >> " }"
-/

@[builtin_macro Lean.Parser.Term.structInst] def expandStructInstExpectedType : Macro := fun stx =>
  let expectedArg := stx[4]
  if expectedArg.isNone then
    Macro.throwUnsupported
  else
    let expected := expectedArg[1]
    let stxNew   := stx.setArg 4 mkNullNode
    `(($stxNew : $expected))

/-- Expand field abbreviations. Example: `{ x, y := 0 }` expands to `{ x := x, y := 0 }` -/
@[builtin_macro Lean.Parser.Term.structInst] def expandStructInstFieldAbbrev : Macro
  | `({ $[$srcs,* with]? $fields,* $[..%$ell]? $[: $ty]? }) =>
    if fields.getElems.raw.any (·.getKind == ``Lean.Parser.Term.structInstFieldAbbrev) then do
      let fieldsNew ← fields.getElems.mapM fun
        | `(Parser.Term.structInstFieldAbbrev| $id:ident) =>
          `(Parser.Term.structInstField| $id:ident := $id:ident)
        | field => return field
      `({ $[$srcs,* with]? $fieldsNew,* $[..%$ell]? $[: $ty]? })
    else
      Macro.throwUnsupported
  | _ => Macro.throwUnsupported

/--
  If `stx` is of the form `{ s₁, ..., sₙ with ... }` and `sᵢ` is not a local variable, expand into `let src := sᵢ; { ..., src, ... with ... }`.

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
          let sourceNew ← `(src)
          let r ← go sources (sourcesNew.push sourceNew)
          `(let src := $source; $r)

structure ExplicitSourceInfo where
  stx        : Syntax
  structName : Name
  deriving Inhabited

structure Source where
  explicit : Array ExplicitSourceInfo -- `s₁ ... sₙ with`
  implicit : Option Syntax -- `..`
  deriving Inhabited

def Source.isNone : Source → Bool
  | { explicit := #[], implicit := none } => true
  | _ => false

/-- `optional (atomic (sepBy1 termParser ", " >> " with ")` -/
private def mkSourcesWithSyntax (sources : Array Syntax) : Syntax :=
  let ref := sources[0]!
  let stx := Syntax.mkSep sources (mkAtomFrom ref ", ")
  mkNullNode #[stx, mkAtomFrom ref "with "]

private def getStructSource (structStx : Syntax) : TermElabM Source :=
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
  We say a `{ ... }` notation is a `modifyOp` if it contains only one
  ```
  def structInstArrayRef := leading_parser "[" >> termParser >>"]"
  ```
-/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
  let s? ← stx[2].getSepArgs.foldlM (init := none) fun s? arg => do
    /- arg is of the form `structInstFieldAbbrev <|> structInstField` -/
    if arg.getKind == ``Lean.Parser.Term.structInstField then
      /- Remark: the syntax for `structInstField` is
         ```
         def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (group ("." >> (ident <|> numLit)) <|> structInstArrayRef)
         def structInstField  := leading_parser structInstLVal >> " := " >> termParser
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

private def elabModifyOp (stx modifyOp : Syntax) (sources : Array ExplicitSourceInfo) (expectedType? : Option Expr) : TermElabM Expr := do
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
    cont modifyOp[2]
  else
    let s ← `(s)
    let valFirst  := rest[0]
    let valFirst  := if valFirst.getKind == ``Lean.Parser.Term.structInstArrayRef then valFirst else valFirst[1]
    let restArgs  := rest.getArgs
    let valRest   := mkNullNode restArgs[1:restArgs.size]
    let valField  := modifyOp.setArg 0 <| mkNode ``Parser.Term.structInstLVal #[valFirst, valRest]
    let valSource := mkSourcesWithSyntax #[s]
    let val       := stx.setArg 1 valSource
    let val       := val.setArg 2 <| mkNullNode #[valField]
    trace[Elab.struct.modifyOp] "{stx}\nval: {val}"
    cont val

/--
  Get structure name.
  This method triest to postpone execution if the expected type is not available.

  If the expected type is available and it is a structure, then we use it.
  Otherwise, we use the type of the first source. -/
private def getStructName (expectedType? : Option Expr) (sourceView : Source) : TermElabM Name := do
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
    | _                        => useSource ()
where
  throwUnknownExpectedType :=
    throwError "invalid \{...} notation, expected type is not known"
  throwUnexpectedExpectedType type (kind := "expected") := do
    let type ← instantiateMVars type
    if type.getAppFn.isMVar then
      throwUnknownExpectedType
    else
      throwError "invalid \{...} notation, {kind} type is not of the form (C ...){indentExpr type}"

inductive FieldLHS where
  | fieldName  (ref : Syntax) (name : Name)
  | fieldIndex (ref : Syntax) (idx : Nat)
  | modifyOp   (ref : Syntax) (index : Syntax)
  deriving Inhabited

instance : ToFormat FieldLHS := ⟨fun lhs =>
  match lhs with
  | .fieldName _ n  => format n
  | .fieldIndex _ i => format i
  | .modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"⟩

inductive FieldVal (σ : Type) where
  | term  (stx : Syntax) : FieldVal σ
  | nested (s : σ)       : FieldVal σ
  | default              : FieldVal σ -- mark that field must be synthesized using default value
  deriving Inhabited

structure Field (σ : Type) where
  ref   : Syntax
  lhs   : List FieldLHS
  val   : FieldVal σ
  expr? : Option Expr := none
  deriving Inhabited

def Field.isSimple {σ} : Field σ → Bool
  | { lhs := [_], .. } => true
  | _                  => false

inductive Struct where
  /-- Remark: the field `params` is use for default value propagation. It is initially empty, and then set at `elabStruct`. -/
  | mk (ref : Syntax) (structName : Name) (params : Array (Name × Expr)) (fields : List (Field Struct)) (source : Source)
  deriving Inhabited

abbrev Fields := List (Field Struct)

def Struct.ref : Struct → Syntax
  | ⟨ref, _, _, _, _⟩ => ref

def Struct.structName : Struct → Name
  | ⟨_, structName, _, _, _⟩ => structName

def Struct.params : Struct → Array (Name × Expr)
  | ⟨_, _, params, _, _⟩ => params

def Struct.fields : Struct → Fields
  | ⟨_, _, _, fields, _⟩ => fields

def Struct.source : Struct → Source
  | ⟨_, _, _, _, s⟩ => s

/-- `true` iff all fields of the given structure are marked as `default` -/
partial def Struct.allDefault (s : Struct) : Bool :=
  s.fields.all fun { val := val,  .. } => match val with
    | .term _   => false
    | .default  => true
    | .nested s => allDefault s

def formatField (formatStruct : Struct → Format) (field : Field Struct) : Format :=
  Format.joinSep field.lhs " . " ++ " := " ++
    match field.val with
    | .term v   => v.prettyPrint
    | .nested s => formatStruct s
    | .default  => "<default>"

partial def formatStruct : Struct → Format
  | ⟨_, _,          _, fields, source⟩ =>
    let fieldsFmt := Format.joinSep (fields.map (formatField formatStruct)) ", "
    let implicitFmt := if source.implicit.isSome then " .. " else ""
    if source.explicit.isEmpty then
      "{" ++ fieldsFmt ++ implicitFmt ++ "}"
    else
      "{" ++ format (source.explicit.map (·.stx)) ++ " with " ++ fieldsFmt ++ implicitFmt ++ "}"

instance : ToFormat Struct     := ⟨formatStruct⟩
instance : ToString Struct := ⟨toString ∘ format⟩

instance : ToFormat (Field Struct) := ⟨formatField formatStruct⟩
instance : ToString (Field Struct) := ⟨toString ∘ format⟩

/-
Recall that `structInstField` elements have the form
```
   def structInstField  := leading_parser structInstLVal >> " := " >> termParser
   def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
   def structInstArrayRef := leading_parser "[" >> termParser >>"]"
```
-/
-- Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
  | .modifyOp   stx _    => stx
  | .fieldName  stx name => if first then mkIdentFrom stx name else mkGroupNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
  | .fieldIndex stx _    => if first then stx else mkGroupNode #[mkAtomFrom stx ".", stx]

def FieldVal.toSyntax : FieldVal Struct → Syntax
  | .term stx => stx
  | _                 => unreachable!

def Field.toSyntax : Field Struct → Syntax
  | field =>
    let stx := field.ref
    let stx := stx.setArg 2 field.val.toSyntax
    match field.lhs with
    | first::rest => stx.setArg 0 <| mkNullNode #[first.toSyntax true, mkNullNode <| rest.toArray.map (FieldLHS.toSyntax false) ]
    | _ => unreachable!

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
      | none     => Macro.throwError "unexpected structure syntax"

private def mkStructView (stx : Syntax) (structName : Name) (source : Source) : MacroM Struct := do
  /- Recall that `stx` is of the form
     ```
     leading_parser "{" >> optional (atomic (sepBy1 termParser ", " >> " with "))
                 >> sepByIndent (structInstFieldAbbrev <|> structInstField) ...
                 >> optional ".."
                 >> optional (" : " >> termParser)
                 >> " }"
     ```

     This method assumes that `structInstFieldAbbrev` had already been expanded.
  -/
  let fields ← stx[2].getSepArgs.toList.mapM fun fieldStx => do
    let val      := fieldStx[2]
    let first    ← toFieldLHS fieldStx[0][0]
    let rest     ← fieldStx[0][1].getArgs.toList.mapM toFieldLHS
    return { ref := fieldStx, lhs := first :: rest, val := FieldVal.term val : Field Struct }
  return ⟨stx, structName, #[], fields, source⟩

def Struct.modifyFieldsM {m : Type → Type} [Monad m] (s : Struct) (f : Fields → m Fields) : m Struct :=
  match s with
  | ⟨ref, structName, params, fields, source⟩ => return ⟨ref, structName, params, (← f fields), source⟩

def Struct.modifyFields (s : Struct) (f : Fields → Fields) : Struct :=
  Id.run <| s.modifyFieldsM f

def Struct.setFields (s : Struct) (fields : Fields) : Struct :=
  s.modifyFields fun _ => fields

def Struct.setParams (s : Struct) (ps : Array (Name × Expr)) : Struct :=
  match s with
  | ⟨ref, structName, _, fields, source⟩ => ⟨ref, structName, ps, fields, source⟩

private def expandCompositeFields (s : Struct) : Struct :=
  s.modifyFields fun fields => fields.map fun field => match field with
    | { lhs := .fieldName _ (.str Name.anonymous ..) :: _, .. } => field
    | { lhs := .fieldName ref n@(.str ..) :: rest, .. } =>
      let newEntries := n.components.map <| FieldLHS.fieldName ref
      { field with lhs := newEntries ++ rest }
    | _ => field

private def expandNumLitFields (s : Struct) : TermElabM Struct :=
  s.modifyFieldsM fun fields => do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    fields.mapM fun field => match field with
      | { lhs := .fieldIndex ref idx :: rest, .. } =>
        if idx == 0 then throwErrorAt ref "invalid field index, index must be greater than 0"
        else if idx > fieldNames.size then throwErrorAt ref "invalid field index, structure has only #{fieldNames.size} fields"
        else return { field with lhs := .fieldName ref fieldNames[idx - 1]! :: rest }
      | _ => return field

/-- For example, consider the following structures:
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
private def expandParentFields (s : Struct) : TermElabM Struct := do
  let env ← getEnv
  s.modifyFieldsM fun fields => fields.mapM fun field => do match field with
    | { lhs := .fieldName ref fieldName :: _,    .. } =>
      addCompletionInfo <| CompletionInfo.fieldId ref fieldName (← getLCtx) s.structName
      match findField? env s.structName fieldName with
      | none => throwErrorAt ref "'{fieldName}' is not a field of structure '{s.structName}'"
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

private abbrev FieldMap := HashMap Name Fields

private def mkFieldMap (fields : Fields) : TermElabM FieldMap :=
  fields.foldlM (init := {}) fun fieldMap field =>
    match field.lhs with
    | .fieldName _ fieldName :: _    =>
      match fieldMap.find? fieldName with
      | some (prevField::restFields) =>
        if field.isSimple || prevField.isSimple then
          throwErrorAt field.ref "field '{fieldName}' has already been specified"
        else
          return fieldMap.insert fieldName (field::prevField::restFields)
      | _ => return fieldMap.insert fieldName [field]
    | _ => unreachable!

private def isSimpleField? : Fields → Option (Field Struct)
  | [field] => if field.isSimple then some field else none
  | _       => none

private def getFieldIdx (structName : Name) (fieldNames : Array Name) (fieldName : Name) : TermElabM Nat := do
  match fieldNames.findIdx? fun n => n == fieldName with
  | some idx => return idx
  | none     => throwError "field '{fieldName}' is not a valid field of '{structName}'"

def mkProjStx? (s : Syntax) (structName : Name) (fieldName : Name) : TermElabM (Option Syntax) := do
  if (findField? (← getEnv) structName fieldName).isNone then
    return none
  return some <| mkNode ``Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

def findField? (fields : Fields) (fieldName : Name) : Option (Field Struct) :=
  fields.find? fun field =>
    match field.lhs with
    | [.fieldName _ n] => n == fieldName
    | _                => false

mutual

  private partial def groupFields (s : Struct) : TermElabM Struct := do
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
            let substruct := Struct.mk s.ref substructName #[] substructFields s.source
            let substruct ← expandStruct substruct
            pure { field with lhs := [field.lhs.head!], val := FieldVal.nested substruct }
          | none =>
            let updateSource (structStx : Syntax) : TermElabM Syntax := do
              let sourcesNew ← s.source.explicit.filterMapM fun source => mkProjStx? source.stx source.structName fieldName
              let explicitSourceStx := if sourcesNew.isEmpty then mkNullNode else mkSourcesWithSyntax sourcesNew
              let implicitSourceStx := s.source.implicit.getD mkNullNode
              return (structStx.setArg 1 explicitSourceStx).setArg 3 implicitSourceStx
            let valStx := s.ref -- construct substructure syntax using s.ref as template
            let valStx := valStx.setArg 4 mkNullNode -- erase optional expected type
            let args   := substructFields.toArray.map (·.toSyntax)
            let valStx := valStx.setArg 2 (mkNullNode <| mkSepArray args (mkAtom ","))
            let valStx ← updateSource valStx
            return { field with lhs := [field.lhs.head!], val := FieldVal.term valStx }

  private partial def addMissingFields (s : Struct) : TermElabM Struct := do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    let ref := s.ref.mkSynthetic
    withRef ref do
      let fields ← fieldNames.foldlM (init := []) fun fields fieldName => do
        match findField? s.fields fieldName with
        | some field => return field::fields
        | none       =>
          let addField (val : FieldVal Struct) : TermElabM Fields := do
            return { ref, lhs := [FieldLHS.fieldName ref fieldName], val := val } :: fields
          match Lean.isSubobjectField? env s.structName fieldName with
          | some substructName =>
            -- If one of the sources has the subobject field, use it
            if let some val ← s.source.explicit.findSomeM? fun source => mkProjStx? source.stx source.structName fieldName then
              addField (FieldVal.term val)
            else
              let substruct := Struct.mk ref substructName #[] [] s.source
              let substruct ← expandStruct substruct
              addField (FieldVal.nested substruct)
          | none =>
            if let some val ← s.source.explicit.findSomeM? fun source => mkProjStx? source.stx source.structName fieldName then
              addField (FieldVal.term val)
            else if s.source.implicit.isSome then
              addField (FieldVal.term (mkHole ref))
            else
              addField FieldVal.default
      return s.setFields fields.reverse

  private partial def expandStruct (s : Struct) : TermElabM Struct := do
    let s := expandCompositeFields s
    let s ← expandNumLitFields s
    let s ← expandParentFields s
    let s ← groupFields s
    addMissingFields s

end

structure CtorHeaderResult where
  ctorFn     : Expr
  ctorFnType : Expr
  instMVars  : Array MVarId
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

private def propagateExpectedType (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit := do
  match expectedType? with
  | none              => return ()
  | some expectedType =>
    match getForallBody numFields type with
      | none           => pure ()
      | some typeBody =>
        unless typeBody.hasLooseBVars do
          discard <| isDefEq expectedType typeBody

private def mkCtorHeader (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
  let us ← mkFreshLevelMVars ctorVal.levelParams.length
  let val  := Lean.mkConst ctorVal.name us
  let type ← instantiateTypeLevelParams (ConstantInfo.ctorInfo ctorVal) us
  let r ← mkCtorHeaderAux ctorVal.numParams type val #[] #[]
  propagateExpectedType r.ctorFnType ctorVal.numFields expectedType?
  synthesizeAppInstMVars r.instMVars r.ctorFn
  return r

def markDefaultMissing (e : Expr) : Expr :=
  mkAnnotation `structInstDefault e

def defaultMissing? (e : Expr) : Option Expr :=
  annotation? `structInstDefault e

def throwFailedToElabField {α} (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
  throwError "failed to elaborate field '{fieldName}' of '{structName}, {msgData}"

def trySynthStructInstance? (s : Struct) (expectedType : Expr) : TermElabM (Option Expr) := do
  if !s.allDefault then
    return none
  else
    try synthInstance? expectedType catch _ => return none

structure ElabStructResult where
  val       : Expr
  struct    : Struct
  instMVars : Array MVarId

private partial def elabStruct (s : Struct) (expectedType? : Option Expr) : TermElabM ElabStructResult := withRef s.ref do
  let env ← getEnv
  let ctorVal := getStructureCtor env s.structName
  if isPrivateNameFromImportedModule env ctorVal.name then
    throwError "invalid \{...} notation, constructor for `{s.structName}` is marked as private"
  -- We store the parameters at the resulting `Struct`. We use this information during default value propagation.
  let { ctorFn, ctorFnType, params, .. } ← mkCtorHeader ctorVal expectedType?
  let (e, _, fields, instMVars) ← s.fields.foldlM (init := (ctorFn, ctorFnType, [], #[])) fun (e, type, fields, instMVars) field => do
    match field.lhs with
    | [.fieldName ref fieldName] =>
      let type ← whnfForall type
      trace[Elab.struct] "elabStruct {field}, {type}"
      match type with
      | .forallE _ d b bi =>
        let cont (val : Expr) (field : Field Struct) (instMVars := instMVars) : TermElabM (Expr × Expr × Fields × Array MVarId) := do
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
            let { val, struct := sNew, instMVars := instMVarsNew } ← elabStruct s (some d)
            let val ← ensureHasType d val
            cont val { field with val := FieldVal.nested sNew } (instMVars ++ instMVarsNew)
        | .default  =>
          match d.getAutoParamTactic? with
          | some (.const tacticDecl ..) =>
            match evalSyntaxConstant env (← getOptions) tacticDecl with
            | .error err       => throwError err
            | .ok tacticSyntax =>
              let stx ← `(by $tacticSyntax)
              cont (← elabTermEnsuringType stx (d.getArg! 0).consumeTypeAnnotations) field
          | _ =>
            if bi == .instImplicit then
              let val ← withRef field.ref <| mkFreshExprMVar d .synthetic
              cont val field (instMVars.push val.mvarId!)
            else
              let val ← withRef field.ref <| mkFreshExprMVar (some d)
              cont (markDefaultMissing val) field
      | _ => withRef field.ref <| throwFailedToElabField fieldName s.structName m!"unexpected constructor type{indentExpr type}"
    | _ => throwErrorAt field.ref "unexpected unexpanded structure field"
  return { val := e, struct := s.setFields fields.reverse |>.setParams params, instMVars }

namespace DefaultFields

structure Context where
  -- We must search for default values overridden in derived structures
  structs : Array Struct := #[]
  allStructNames : Array Name := #[]
  /--
  Consider the following example:
  ```
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

structure State where
  progress : Bool := false

partial def collectStructNames (struct : Struct) (names : Array Name) : Array Name :=
  let names := names.push struct.structName
  struct.fields.foldl (init := names) fun names field =>
    match field.val with
    | .nested struct => collectStructNames struct names
    | _ => names

partial def getHierarchyDepth (struct : Struct) : Nat :=
  struct.fields.foldl (init := 0) fun max field =>
    match field.val with
    | .nested struct => Nat.max max (getHierarchyDepth struct + 1)
    | _ => max

def isDefaultMissing? [Monad m] [MonadMCtx m] (field : Field Struct) : m Bool := do
  if let some expr := field.expr? then
    if let some (.mvar mvarId) := defaultMissing? expr then
      unless (← mvarId.isAssigned) do
        return true
  return false

partial def findDefaultMissing? [Monad m] [MonadMCtx m] (struct : Struct) : m (Option (Field Struct)) :=
  struct.fields.findSomeM? fun field => do
   match field.val with
   | .nested struct => findDefaultMissing? struct
   | _ => return if (← isDefaultMissing? field) then field else none

partial def allDefaultMissing [Monad m] [MonadMCtx m] (struct : Struct) : m (Array (Field Struct)) :=
  go struct *> get |>.run' #[]
where
  go (struct : Struct) : StateT (Array (Field Struct)) m Unit :=
    for field in struct.fields do
      if let .nested struct := field.val then
        go struct
      else if (← isDefaultMissing? field) then
        modify (·.push field)

def getFieldName (field : Field Struct) : Name :=
  match field.lhs with
  | [.fieldName _ fieldName] => fieldName
  | _ => unreachable!

abbrev M := ReaderT Context (StateRefT State TermElabM)

def isRoundDone : M Bool := do
  return (← get).progress && (← read).maxDistance > 0

def getFieldValue? (struct : Struct) (fieldName : Name) : Option Expr :=
  struct.fields.findSome? fun field =>
    if getFieldName field == fieldName then
      field.expr?
    else
      none

partial def mkDefaultValueAux? (struct : Struct) : Expr → TermElabM (Option Expr)
  | .lam n d b c => withRef struct.ref do
    if c.isExplicit then
      let fieldName := n
      match getFieldValue? struct fieldName with
      | none     => return none
      | some val =>
        let valType ← inferType val
        if (← isDefEq valType d) then
          mkDefaultValueAux? struct (b.instantiate1 val)
        else
          return none
    else
      if let some (_, param) := struct.params.find? fun (paramName, _) => paramName == n then
        -- Recall that we did not use to have support for parameter propagation here.
        if (← isDefEq (← inferType param) d) then
          mkDefaultValueAux? struct (b.instantiate1 param)
        else
          return none
      else
        let arg ← mkFreshExprMVar d
        mkDefaultValueAux? struct (b.instantiate1 arg)
  | e =>
    if e.isAppOfArity ``id 2 then
      return some e.appArg!
    else
      return some e

def mkDefaultValue? (struct : Struct) (cinfo : ConstantInfo) : TermElabM (Option Expr) :=
  withRef struct.ref do
  let us ← mkFreshLevelMVarsFor cinfo
  mkDefaultValueAux? struct (← instantiateValueLevelParams cinfo us)

/-- Reduce default value. It performs beta reduction and projections of the given structures. -/
partial def reduce (structNames : Array Name) (e : Expr) : MetaM Expr := do
  match e with
  | .lam ..       => lambdaLetTelescope e fun xs b => do mkLambdaFVars xs (← reduce structNames b)
  | .forallE ..   => forallTelescope e fun xs b => do mkForallFVars xs (← reduce structNames b)
  | .letE ..      => lambdaLetTelescope e fun xs b => do mkLetFVars xs (← reduce structNames b)
  | .proj _ i b   =>
    match (← Meta.project? b i) with
    | some r => reduce structNames r
    | none   => return e.updateProj! (← reduce structNames b)
  | .app f .. =>
    match (← reduceProjOf? e structNames.contains) with
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

partial def tryToSynthesizeDefault (structs : Array Struct) (allStructNames : Array Name) (maxDistance : Nat) (fieldName : Name) (mvarId : MVarId) : TermElabM Bool :=
  let rec loop (i : Nat) (dist : Nat) := do
    if dist > maxDistance then
      return false
    else if h : i < structs.size then
      let struct := structs.get ⟨i, h⟩
      match getDefaultFnForField? (← getEnv) struct.structName fieldName with
      | some defFn =>
        let cinfo ← getConstInfo defFn
        let mctx ← getMCtx
        match (← mkDefaultValue? struct cinfo) with
        | none     => setMCtx mctx; loop (i+1) (dist+1)
        | some val =>
          let val ← reduce allStructNames val
          match val.find? fun e => (defaultMissing? e).isSome with
          | some _ => setMCtx mctx; loop (i+1) (dist+1)
          | none   =>
            let mvarDecl ← getMVarDecl mvarId
            let val ← ensureHasType mvarDecl.type val
            mvarId.assign val
            return true
      | _ => loop (i+1) dist
    else
      return false
  loop 0 0

partial def step (struct : Struct) : M Unit :=
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

partial def propagateLoop (hierarchyDepth : Nat) (d : Nat) (struct : Struct) : M Unit := do
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

def propagate (struct : Struct) : TermElabM Unit :=
  let hierarchyDepth := getHierarchyDepth struct
  let structNames := collectStructNames struct #[]
  propagateLoop hierarchyDepth 0 struct { allStructNames := structNames } |>.run' {}

end DefaultFields

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (source : Source) : TermElabM Expr := do
  let structName ← getStructName expectedType? source
  let struct ← liftMacroM <| mkStructView stx structName source
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
  let { val := r, struct, instMVars } ← withSynthesize (mayPostpone := true) <| elabStruct struct expectedType?
  trace[Elab.struct] "before propagate {r}"
  DefaultFields.propagate struct
  synthesizeAppInstMVars instMVars r
  return r

@[builtin_term_elab structInst] def elabStructInst : TermElab := fun stx expectedType? => do
  match (← expandNonAtomicExplicitSources stx) with
  | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | none =>
    let sourceView ← getStructSource stx
    if let some modifyOp ← isModifyOp? stx then
      if sourceView.explicit.isEmpty then
        throwError "invalid \{...} notation, explicit source is required when using '[<index>] := <value>'"
      elabModifyOp stx modifyOp sourceView.explicit expectedType?
    else
      elabStructInstAux stx expectedType? sourceView

builtin_initialize registerTraceClass `Elab.struct

end Lean.Elab.Term.StructInst
