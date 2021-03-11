/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindExpr
import Lean.Parser.Term
import Lean.Elab.App
import Lean.Elab.Binders

namespace Lean.Elab.Term.StructInst

open Std (HashMap)
open Meta

/-
  Structure instances are of the form:

      "{" >> optional (atomic (termParser >> " with "))
          >> manyIndent (group (structInstField >> optional ", "))
          >> optEllipsis
          >> optional (" : " >> termParser)
          >> " }"
-/

@[builtinMacro Lean.Parser.Term.structInst] def expandStructInstExpectedType : Macro := fun stx =>
  let expectedArg := stx[4]
  if expectedArg.isNone then
    Macro.throwUnsupported
  else
    let expected := expectedArg[1]
    let stxNew   := stx.setArg 4 mkNullNode
    `(($stxNew : $expected))

/-
If `stx` is of the form `{ s with ... }` and `s` is not a local variable, expand into `let src := s; { src with ... }`.

Note that this one is not a `Macro` because we need to access the local context.
-/
private def expandNonAtomicExplicitSource (stx : Syntax) : TermElabM (Option Syntax) :=
  withFreshMacroScope do
    let sourceOpt := stx[1]
    if sourceOpt.isNone then
      pure none
    else
      let source := sourceOpt[0]
      match (← isLocalIdent? source) with
      | some _ => pure none
      | none   =>
        let src ← `(src)
        let sourceOpt := sourceOpt.setArg 0 src
        let stxNew    := stx.setArg 1 sourceOpt
        `(let src := $source; $stxNew)

inductive Source where
  | none     -- structure instance source has not been provieded
  | implicit (stx : Syntax) -- `..`
  | explicit (stx : Syntax) (src : Expr) -- `src with`
  deriving Inhabited

def Source.isNone : Source → Bool
  | Source.none => true
  | _           => false

def setStructSourceSyntax (structStx : Syntax) : Source → Syntax
  | Source.none           => (structStx.setArg 1 mkNullNode).setArg 3 mkNullNode
  | Source.implicit stx   => (structStx.setArg 1 mkNullNode).setArg 3 stx
  | Source.explicit stx _ => (structStx.setArg 1 stx).setArg 3 mkNullNode

private def getStructSource (stx : Syntax) : TermElabM Source :=
  withRef stx do
    let explicitSource := stx[1]
    let implicitSource := stx[3]
    if explicitSource.isNone && implicitSource[0].isNone then
      return Source.none
    else if explicitSource.isNone then
      return Source.implicit implicitSource
    else if implicitSource[0].isNone then
      let fvar? ← isLocalIdent? explicitSource[0]
      match fvar? with
      | none      => unreachable! -- expandNonAtomicExplicitSource must have been used when we get here
      | some src  => return Source.explicit explicitSource src
    else
      throwError "invalid structure instance `with` and `..` cannot be used together"

/-
  We say a `{ ... }` notation is a `modifyOp` if it contains only one
  ```
  def structInstArrayRef := parser! "[" >> termParser >>"]"
  ```
-/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
  let s? ← stx[2].getArgs.foldlM (init := none) fun s? p =>
    /- p is of the form `(group (structInstField >> optional ", "))` -/
    let arg := p[0]
    /- Remark: the syntax for `structInstField` is
       ```
       def structInstLVal   := parser! (ident <|> numLit <|> structInstArrayRef) >> many (group ("." >> (ident <|> numLit)) <|> structInstArrayRef)
       def structInstField  := parser! structInstLVal >> " := " >> termParser
       ```
    -/
    let lval := arg[0]
    let k    := lval[0].getKind
    if k == `Lean.Parser.Term.structInstArrayRef then
      match s? with
      | none   => pure (some arg)
      | some s =>
        if s.getKind == `Lean.Parser.Term.structInstArrayRef then
          throwErrorAt arg "invalid {...} notation, at most one `[..]` at a given level"
        else
          throwErrorAt arg "invalid {...} notation, can't mix field and `[..]` at a given level"
    else
      match s? with
      | none   => pure (some arg)
      | some s =>
        if s.getKind == `Lean.Parser.Term.structInstArrayRef then
          throwErrorAt arg "invalid {...} notation, can't mix field and `[..]` at a given level"
        else
          pure s?
  match s? with
  | none   => pure none
  | some s => if s[0][0].getKind == `Lean.Parser.Term.structInstArrayRef then pure s? else pure none

private def elabModifyOp (stx modifyOp source : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let cont (val : Syntax) : TermElabM Expr := do
    let lval := modifyOp[0][0]
    let idx  := lval[1]
    let self := source[0]
    let stxNew ← `($(self).modifyOp (idx := $idx) (fun s => $val))
    trace[Elab.struct.modifyOp] "{stx}\n===>\n{stxNew}"
    withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  trace[Elab.struct.modifyOp] "{modifyOp}\nSource: {source}"
  let rest := modifyOp[0][1]
  if rest.isNone then
    cont modifyOp[2]
  else
    let s ← `(s)
    let valFirst  := rest[0]
    let valFirst  := if valFirst.getKind == `Lean.Parser.Term.structInstArrayRef then valFirst else valFirst[1]
    let restArgs  := rest.getArgs
    let valRest   := mkNullNode restArgs[1:restArgs.size]
    let valField  := modifyOp.setArg 0 <| Syntax.node ``Parser.Term.structInstLVal #[valFirst, valRest]
    let valSource := source.modifyArg 0 fun _ => s
    let val       := stx.setArg 1 valSource
    let val       := val.setArg 2 <| mkNullNode #[mkNullNode #[valField, mkNullNode]]
    trace[Elab.struct.modifyOp] "{stx}\nval: {val}"
    cont val

/- Get structure name and elaborate explicit source (if available) -/
private def getStructName (stx : Syntax) (expectedType? : Option Expr) (sourceView : Source) : TermElabM Name := do
  tryPostponeIfNoneOrMVar expectedType?
  let useSource : Unit → TermElabM Name := fun _ =>
    match sourceView, expectedType? with
    | Source.explicit _ src, _ => do
      let srcType ← inferType src
      let srcType ← whnf srcType
      tryPostponeIfMVar srcType
      match srcType.getAppFn with
      | Expr.const constName _ _ => pure constName
      | _ => throwUnexpectedExpectedType srcType "source"
    | _, some expectedType => throwUnexpectedExpectedType expectedType
    | _, none              => throwUnknownExpectedType
  match expectedType? with
  | none => useSource ()
  | some expectedType =>
    let expectedType ← whnf expectedType
    match expectedType.getAppFn with
    | Expr.const constName _ _ => pure constName
    | _                        => useSource ()
where
  throwUnknownExpectedType :=
    throwError! "invalid \{...} notation, expected type is not known"
  throwUnexpectedExpectedType type (kind := "expected") := do
    let type ← instantiateMVars type
    if type.getAppFn.isMVar then
      throwUnknownExpectedType
    else
      throwError! "invalid \{...} notation, {kind} type is not of the form (C ...){indentExpr type}"

inductive FieldLHS where
  | fieldName  (ref : Syntax) (name : Name)
  | fieldIndex (ref : Syntax) (idx : Nat)
  | modifyOp   (ref : Syntax) (index : Syntax)
  deriving Inhabited

instance : ToFormat FieldLHS := ⟨fun lhs =>
  match lhs with
  | FieldLHS.fieldName _ n  => fmt n
  | FieldLHS.fieldIndex _ i => fmt i
  | FieldLHS.modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"⟩

inductive FieldVal (σ : Type) where
  | term  (stx : Syntax) : FieldVal σ
  | nested (s : σ)       : FieldVal σ
  | default              : FieldVal σ -- mark that field must be synthesized using default value
  deriving Inhabited

structure Field (σ : Type) where
  ref : Syntax
  lhs : List FieldLHS
  val : FieldVal σ
  expr? : Option Expr := none
  deriving Inhabited

def Field.isSimple {σ} : Field σ → Bool
  | { lhs := [_], .. } => true
  | _                  => false

inductive Struct where
  | mk (ref : Syntax) (structName : Name) (fields : List (Field Struct)) (source : Source)
  deriving Inhabited

abbrev Fields := List (Field Struct)

/- true if all fields of the given structure are marked as `default` -/
partial def Struct.allDefault : Struct → Bool
  | ⟨_, _, fields, _⟩ => fields.all fun ⟨_, _, val, _⟩ => match val with
    | FieldVal.term _   => false
    | FieldVal.default  => true
    | FieldVal.nested s => allDefault s

def Struct.ref : Struct → Syntax
  | ⟨ref, _, _, _⟩ => ref

def Struct.structName : Struct → Name
  | ⟨_, structName, _, _⟩ => structName

def Struct.fields : Struct → Fields
  | ⟨_, _, fields, _⟩ => fields

def Struct.source : Struct → Source
  | ⟨_, _, _, s⟩ => s

def formatField (formatStruct : Struct → Format) (field : Field Struct) : Format :=
  Format.joinSep field.lhs " . " ++ " := " ++
    match field.val with
    | FieldVal.term v   => v.prettyPrint
    | FieldVal.nested s => formatStruct s
    | FieldVal.default  => "<default>"

partial def formatStruct : Struct → Format
  | ⟨_, structName, fields, source⟩ =>
    let fieldsFmt := Format.joinSep (fields.map (formatField formatStruct)) ", "
    match source with
    | Source.none           => "{" ++ fieldsFmt ++ "}"
    | Source.implicit _     => "{" ++ fieldsFmt ++ " .. }"
    | Source.explicit _ src => "{" ++ format src ++ " with " ++ fieldsFmt ++ "}"

instance : ToFormat Struct     := ⟨formatStruct⟩
instance : ToString Struct := ⟨toString ∘ format⟩

instance : ToFormat (Field Struct) := ⟨formatField formatStruct⟩
instance : ToString (Field Struct) := ⟨toString ∘ format⟩

/-
Recall that `structInstField` elements have the form
```
   def structInstField  := parser! structInstLVal >> " := " >> termParser
   def structInstLVal   := parser! (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
   def structInstArrayRef := parser! "[" >> termParser >>"]"
```
-/
-- Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
  | FieldLHS.modifyOp   stx _    => stx
  | FieldLHS.fieldName  stx name => if first then mkIdentFrom stx name else mkNullNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
  | FieldLHS.fieldIndex stx _    => if first then stx else mkNullNode #[mkAtomFrom stx ".", stx]

def FieldVal.toSyntax : FieldVal Struct → Syntax
  | FieldVal.term stx => stx
  | _                 => unreachable!

def Field.toSyntax : Field Struct → Syntax
  | field =>
    let stx := field.ref
    let stx := stx.setArg 2 field.val.toSyntax
    match field.lhs with
    | first::rest => stx.setArg 0 <| mkNullNode #[first.toSyntax true, mkNullNode <| rest.toArray.map (FieldLHS.toSyntax false) ]
    | _ => unreachable!

private def toFieldLHS (stx : Syntax) : Except String FieldLHS :=
  if stx.getKind == `Lean.Parser.Term.structInstArrayRef then
    return FieldLHS.modifyOp stx stx[1]
  else
    -- Note that the representation of the first field is different.
    let stx := if stx.getKind == nullKind then stx[1] else stx
    if stx.isIdent then
      return FieldLHS.fieldName stx stx.getId.eraseMacroScopes
    else match stx.isFieldIdx? with
      | some idx => return FieldLHS.fieldIndex stx idx
      | none     => throw "unexpected structure syntax"

private def mkStructView (stx : Syntax) (structName : Name) (source : Source) : Except String Struct := do
  /- Recall that `stx` is of the form
     ```
     parser! "{" >> optional (atomic (termParser >> " with "))
                 >> manyIndent (group (structInstField >> optional ", "))
                 >> optional ".."
                 >> optional (" : " >> termParser)
                 >> " }"
     ```
  -/
  let fieldsStx := stx[2].getArgs.map (·[0])
  let fields ← fieldsStx.toList.mapM fun fieldStx => do
    let val   := fieldStx[2]
    let first ← toFieldLHS fieldStx[0][0]
    let rest  ← fieldStx[0][1].getArgs.toList.mapM toFieldLHS
    pure { ref := fieldStx, lhs := first :: rest, val := FieldVal.term val : Field Struct }
  pure ⟨stx, structName, fields, source⟩

def Struct.modifyFieldsM {m : Type → Type} [Monad m] (s : Struct) (f : Fields → m Fields) : m Struct :=
  match s with
  | ⟨ref, structName, fields, source⟩ => return ⟨ref, structName, (← f fields), source⟩

@[inline] def Struct.modifyFields (s : Struct) (f : Fields → Fields) : Struct :=
  Id.run <| s.modifyFieldsM f

def Struct.setFields (s : Struct) (fields : Fields) : Struct :=
  s.modifyFields fun _ => fields

private def expandCompositeFields (s : Struct) : Struct :=
  s.modifyFields fun fields => fields.map fun field => match field with
    | { lhs := FieldLHS.fieldName ref (Name.str Name.anonymous _ _) :: rest, .. } => field
    | { lhs := FieldLHS.fieldName ref n@(Name.str _ _ _) :: rest, .. } =>
      let newEntries := n.components.map <| FieldLHS.fieldName ref
      { field with lhs := newEntries ++ rest }
    | _ => field

private def expandNumLitFields (s : Struct) : TermElabM Struct :=
  s.modifyFieldsM fun fields => do
    let env ← getEnv
    let fieldNames := getStructureFields env s.structName
    fields.mapM fun field => match field with
      | { lhs := FieldLHS.fieldIndex ref idx :: rest, .. } =>
        if idx == 0 then throwErrorAt ref "invalid field index, index must be greater than 0"
        else if idx > fieldNames.size then throwErrorAt! ref "invalid field index, structure has only #{fieldNames.size} fields"
        else pure { field with lhs := FieldLHS.fieldName ref fieldNames[idx - 1] :: rest }
      | _ => pure field

/- For example, consider the following structures:
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
  s.modifyFieldsM fun fields => fields.mapM fun field => match field with
    | { lhs := FieldLHS.fieldName ref fieldName :: rest, .. } =>
      match findField? env s.structName fieldName with
      | none => throwErrorAt! ref "'{fieldName}' is not a field of structure '{s.structName}'"
      | some baseStructName =>
        if baseStructName == s.structName then pure field
        else match getPathToBaseStructure? env baseStructName s.structName with
          | some path => do
            let path := path.map fun funName => match funName with
              | Name.str _ s _ => FieldLHS.fieldName ref (Name.mkSimple s)
              | _              => unreachable!
            pure { field with lhs := path ++ field.lhs }
          | _ => throwErrorAt! ref "failed to access field '{fieldName}' in parent structure"
    | _ => pure field

private abbrev FieldMap := HashMap Name Fields

private def mkFieldMap (fields : Fields) : TermElabM FieldMap :=
  fields.foldlM (init := {}) fun fieldMap field =>
    match field.lhs with
    | FieldLHS.fieldName _ fieldName :: rest =>
      match fieldMap.find? fieldName with
      | some (prevField::restFields) =>
        if field.isSimple || prevField.isSimple then
          throwErrorAt! field.ref "field '{fieldName}' has already beed specified"
        else
          return fieldMap.insert fieldName (field::prevField::restFields)
      | _ => return fieldMap.insert fieldName [field]
    | _ => unreachable!

private def isSimpleField? : Fields → Option (Field Struct)
  | [field] => if field.isSimple then some field else none
  | _       => none

private def getFieldIdx (structName : Name) (fieldNames : Array Name) (fieldName : Name) : TermElabM Nat := do
  match fieldNames.findIdx? fun n => n == fieldName with
  | some idx => pure idx
  | none     => throwError! "field '{fieldName}' is not a valid field of '{structName}'"

private def mkProjStx (s : Syntax) (fieldName : Name) : Syntax :=
  Syntax.node `Lean.Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

private def mkSubstructSource (structName : Name) (fieldNames : Array Name) (fieldName : Name) (src : Source) : TermElabM Source :=
  match src with
  | Source.explicit stx src => do
    let idx ← getFieldIdx structName fieldNames fieldName
    let stx := stx.modifyArg 0 fun stx => mkProjStx stx fieldName
    return Source.explicit stx (mkProj structName idx src)
  | s => return s

@[specialize] private def groupFields (expandStruct : Struct → TermElabM Struct) (s : Struct) : TermElabM Struct := do
  let env ← getEnv
  let fieldNames := getStructureFields env s.structName
  withRef s.ref do
  s.modifyFieldsM fun fields => do
    let fieldMap ← mkFieldMap fields
    fieldMap.toList.mapM fun ⟨fieldName, fields⟩ => do
      match isSimpleField? fields with
      | some field => pure field
      | none =>
        let substructFields := fields.map fun field => { field with lhs := field.lhs.tail! }
        let substructSource ← mkSubstructSource s.structName fieldNames fieldName s.source
        let field := fields.head!
        match Lean.isSubobjectField? env s.structName fieldName with
        | some substructName =>
          let substruct := Struct.mk s.ref substructName substructFields substructSource
          let substruct ← expandStruct substruct
          pure { field with lhs := [field.lhs.head!], val := FieldVal.nested substruct }
        | none => do
          -- It is not a substructure field. Thus, we wrap fields using `Syntax`, and use `elabTerm` to process them.
          let valStx := s.ref -- construct substructure syntax using s.ref as template
          let valStx := valStx.setArg 4 mkNullNode -- erase optional expected type
          let args   := substructFields.toArray.map fun field => mkNullNode #[field.toSyntax, mkNullNode]
          let valStx := valStx.setArg 2 (mkNullNode args)
          let valStx := setStructSourceSyntax valStx substructSource
          pure { field with lhs := [field.lhs.head!], val := FieldVal.term valStx }

def findField? (fields : Fields) (fieldName : Name) : Option (Field Struct) :=
  fields.find? fun field =>
    match field.lhs with
    | [FieldLHS.fieldName _ n] => n == fieldName
    | _                        => false

@[specialize] private def addMissingFields (expandStruct : Struct → TermElabM Struct) (s : Struct) : TermElabM Struct := do
  let env ← getEnv
  let fieldNames := getStructureFields env s.structName
  let ref := s.ref
  withRef ref do
    let fields ← fieldNames.foldlM (init := []) fun fields fieldName => do
      match findField? s.fields fieldName with
      | some field => return field::fields
      | none       =>
        let addField (val : FieldVal Struct) : TermElabM Fields := do
          return { ref := s.ref, lhs := [FieldLHS.fieldName s.ref fieldName], val := val } :: fields
        match Lean.isSubobjectField? env s.structName fieldName with
        | some substructName => do
          let substructSource ← mkSubstructSource s.structName fieldNames fieldName s.source
          let substruct := Struct.mk s.ref substructName [] substructSource
          let substruct ← expandStruct substruct
          addField (FieldVal.nested substruct)
        | none =>
          match s.source with
          | Source.none           => addField FieldVal.default
          | Source.implicit _     => addField (FieldVal.term (mkHole s.ref))
          | Source.explicit stx _ =>
            -- stx is of the form `optional (try (termParser >> "with"))`
            let src := stx[0]
            let val := mkProjStx src fieldName
            addField (FieldVal.term val)
    return s.setFields fields.reverse

private partial def expandStruct (s : Struct) : TermElabM Struct := do
  let s := expandCompositeFields s
  let s ← expandNumLitFields s
  let s ← expandParentFields s
  let s ← groupFields expandStruct s
  addMissingFields expandStruct s

structure CtorHeaderResult where
  ctorFn     : Expr
  ctorFnType : Expr
  instMVars  : Array MVarId := #[]

private def mkCtorHeaderAux : Nat → Expr → Expr → Array MVarId → TermElabM CtorHeaderResult
  | 0,   type, ctorFn, instMVars => pure { ctorFn := ctorFn, ctorFnType := type, instMVars := instMVars }
  | n+1, type, ctorFn, instMVars => do
    let type ← whnfForall type
    match type with
    | Expr.forallE _ d b c =>
      match c.binderInfo with
      | BinderInfo.instImplicit =>
        let a ← mkFreshExprMVar d MetavarKind.synthetic
        mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) (instMVars.push a.mvarId!)
      | _ =>
        let a ← mkFreshExprMVar d
        mkCtorHeaderAux n (b.instantiate1 a) (mkApp ctorFn a) instMVars
    | _ => throwError "unexpected constructor type"

private partial def getForallBody : Nat → Expr → Option Expr
  | i+1, Expr.forallE _ _ b _ => getForallBody i b
  | i+1, _                    => none
  | 0,   type                 => type

private def propagateExpectedType (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit :=
  match expectedType? with
  | none              => pure ()
  | some expectedType => do
    match getForallBody numFields type with
      | none           => pure ()
      | some typeBody =>
        unless typeBody.hasLooseBVars do
          discard <| isDefEq expectedType typeBody

private def mkCtorHeader (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
  let us ← ctorVal.levelParams.mapM fun _ => mkFreshLevelMVar
  let val  := Lean.mkConst ctorVal.name us
  let type := (ConstantInfo.ctorInfo ctorVal).instantiateTypeLevelParams us
  let r ← mkCtorHeaderAux ctorVal.numParams type val #[]
  propagateExpectedType r.ctorFnType ctorVal.numFields expectedType?
  synthesizeAppInstMVars r.instMVars
  pure r

def markDefaultMissing (e : Expr) : Expr :=
  mkAnnotation `structInstDefault e

def defaultMissing? (e : Expr) : Option Expr :=
  annotation? `structInstDefault e

def throwFailedToElabField {α} (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
  throwError! "failed to elaborate field '{fieldName}' of '{structName}, {msgData}"

def trySynthStructInstance? (s : Struct) (expectedType : Expr) : TermElabM (Option Expr) := do
  if !s.allDefault then
    pure none
  else
    try synthInstance? expectedType catch _ => pure none

private partial def elabStruct (s : Struct) (expectedType? : Option Expr) : TermElabM (Expr × Struct) := withRef s.ref do
  let env ← getEnv
  let ctorVal := getStructureCtor env s.structName
  let { ctorFn := ctorFn, ctorFnType := ctorFnType, .. } ← mkCtorHeader ctorVal expectedType?
  let (e, _, fields) ← s.fields.foldlM (init := (ctorFn, ctorFnType, [])) fun (e, type, fields) field =>
    match field.lhs with
    | [FieldLHS.fieldName ref fieldName] => do
      let type ← whnfForall type
      match type with
      | Expr.forallE _ d b c =>
        let cont (val : Expr) (field : Field Struct) : TermElabM (Expr × Expr × Fields) := do
          pushInfoTree <| InfoTree.node (children := {}) <| Info.ofFieldInfo { lctx := (← getLCtx), val := val, name := fieldName, stx := ref }
          let e     := mkApp e val
          let type  := b.instantiate1 val
          let field := { field with expr? := some val }
          pure (e, type, field::fields)
        match field.val with
        | FieldVal.term stx => cont (← elabTermEnsuringType stx d) field
        | FieldVal.nested s => do
          -- if all fields of `s` are marked as `default`, then try to synthesize instance
          match (← trySynthStructInstance? s d) with
          | some val => cont val { field with val := FieldVal.term (mkHole field.ref) }
          | none     => do let (val, sNew) ← elabStruct s (some d); let val ← ensureHasType d val; cont val { field with val := FieldVal.nested sNew }
        | FieldVal.default  => do let val ← withRef field.ref <| mkFreshExprMVar (some d); cont (markDefaultMissing val) field
      | _ => withRef field.ref <| throwFailedToElabField fieldName s.structName m!"unexpected constructor type{indentExpr type}"
    | _ => throwErrorAt field.ref "unexpected unexpanded structure field"
  pure (e, s.setFields fields.reverse)

namespace DefaultFields

structure Context where
  -- We must search for default values overriden in derived structures
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
    | FieldVal.nested struct => collectStructNames struct names
    | _ => names

partial def getHierarchyDepth (struct : Struct) : Nat :=
  struct.fields.foldl (init := 0) fun max field =>
    match field.val with
    | FieldVal.nested struct => Nat.max max (getHierarchyDepth struct + 1)
    | _ => max

partial def findDefaultMissing? (mctx : MetavarContext) (struct : Struct) : Option (Field Struct) :=
  struct.fields.findSome? fun field =>
   match field.val with
   | FieldVal.nested struct => findDefaultMissing? mctx struct
   | _ => match field.expr? with
     | none      => unreachable!
     | some expr => match defaultMissing? expr with
       | some (Expr.mvar mvarId _) => if mctx.isExprAssigned mvarId then none else some field
       | _                         => none

def getFieldName (field : Field Struct) : Name :=
  match field.lhs with
  | [FieldLHS.fieldName _ fieldName] => fieldName
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
  | Expr.lam n d b c => withRef struct.ref do
    if c.binderInfo.isExplicit then
      let fieldName := n
      match getFieldValue? struct fieldName with
      | none     => pure none
      | some val =>
        let valType ← inferType val
        if (← isDefEq valType d) then
          mkDefaultValueAux? struct (b.instantiate1 val)
        else
          pure none
    else
      let arg ← mkFreshExprMVar d
      mkDefaultValueAux? struct (b.instantiate1 arg)
  | e =>
    if e.isAppOfArity `id 2 then
      pure (some e.appArg!)
    else
      pure (some e)

def mkDefaultValue? (struct : Struct) (cinfo : ConstantInfo) : TermElabM (Option Expr) :=
  withRef struct.ref do
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  mkDefaultValueAux? struct (cinfo.instantiateValueLevelParams us)

/-- If `e` is a projection function of one of the given structures, then reduce it -/
def reduceProjOf? (structNames : Array Name) (e : Expr) : MetaM (Option Expr) := do
  if !e.isApp then pure none
  else match e.getAppFn with
    | Expr.const name _ _ => do
      let env ← getEnv
      match env.getProjectionStructureName? name with
      | some structName =>
        if structNames.contains structName then
          Meta.unfoldDefinition? e
        else
          pure none
      | none => pure none
    | _ => pure none

/-- Reduce default value. It performs beta reduction and projections of the given structures. -/
partial def reduce (structNames : Array Name) : Expr → MetaM Expr
  | e@(Expr.lam _ _ _ _)     => lambdaLetTelescope e fun xs b => do mkLambdaFVars xs (← reduce structNames b)
  | e@(Expr.forallE _ _ _ _) => forallTelescope e fun xs b => do mkForallFVars xs (← reduce structNames b)
  | e@(Expr.letE _ _ _ _ _)  => lambdaLetTelescope e fun xs b => do mkLetFVars xs (← reduce structNames b)
  | e@(Expr.proj _ i b _)    => do
    match (← Meta.project? b i) with
    | some r => reduce structNames r
    | none   => return e.updateProj! (← reduce structNames b)
  | e@(Expr.app f _ _) => do
    match (← reduceProjOf? structNames e) with
    | some r => reduce structNames r
    | none   =>
      let f := f.getAppFn
      let f' ← reduce structNames f
      if f'.isLambda then
        let revArgs := e.getAppRevArgs
        reduce structNames (f'.betaRev revArgs)
      else
        let args ← e.getAppArgs.mapM (reduce structNames)
        return (mkAppN f' args)
  | e@(Expr.mdata _ b _) => do
    let b ← reduce structNames b
    if (defaultMissing? e).isSome && !b.isMVar then
      return b
    else
      return e.updateMData! b
  | e@(Expr.mvar mvarId _) => do
    match (← getExprMVarAssignment? mvarId) with
    | some val => if val.isMVar then reduce structNames val else pure val
    | none     => return e
  | e => return e

partial def tryToSynthesizeDefault (structs : Array Struct) (allStructNames : Array Name) (maxDistance : Nat) (fieldName : Name) (mvarId : MVarId) : TermElabM Bool :=
  let rec loop (i : Nat) (dist : Nat) := do
    if dist > maxDistance then
      pure false
    else if h : i < structs.size then do
      let struct := structs.get ⟨i, h⟩
      let defaultName := struct.structName ++ fieldName ++ `_default
      let env ← getEnv
      match env.find? defaultName with
      | some cinfo@(ConstantInfo.defnInfo defVal) => do
        let mctx ← getMCtx
        let val? ← mkDefaultValue? struct cinfo
        match val? with
        | none     => do setMCtx mctx; loop (i+1) (dist+1)
        | some val => do
          let val ← reduce allStructNames val
          match val.find? fun e => (defaultMissing? e).isSome with
          | some _ => setMCtx mctx; loop (i+1) (dist+1)
          | none   =>
            let mvarDecl ← getMVarDecl mvarId
            let val ← ensureHasType mvarDecl.type val
            assignExprMVar mvarId val
            pure true
      | _ => loop (i+1) dist
    else
      pure false
  loop 0 0

partial def step (struct : Struct) : M Unit :=
  unless (← isRoundDone) do
    withReader (fun ctx => { ctx with structs := ctx.structs.push struct }) do
      for field in struct.fields do
        match field.val with
        | FieldVal.nested struct => step struct
        | _ => match field.expr? with
          | none      => unreachable!
          | some expr => match defaultMissing? expr with
            | some (Expr.mvar mvarId _) =>
              unless (← isExprMVarAssigned mvarId) do
                let ctx ← read
                if (← withRef field.ref <| tryToSynthesizeDefault ctx.structs ctx.allStructNames ctx.maxDistance (getFieldName field) mvarId) then
                  modify fun s => { s with progress := true }
            | _ => pure ()

partial def propagateLoop (hierarchyDepth : Nat) (d : Nat) (struct : Struct) : M Unit := do
  match findDefaultMissing? (← getMCtx) struct with
  | none       => pure () -- Done
  | some field =>
    if d > hierarchyDepth then
      throwErrorAt! field.ref "field '{getFieldName field}' is missing"
    else withReader (fun ctx => { ctx with maxDistance := d }) do
      modify fun s => { s with progress := false }
      step struct
      if (← get).progress then do
        propagateLoop hierarchyDepth 0 struct
      else
        propagateLoop hierarchyDepth (d+1) struct

def propagate (struct : Struct) : TermElabM Unit :=
  let hierarchyDepth := getHierarchyDepth struct
  let structNames := collectStructNames struct #[]
  (propagateLoop hierarchyDepth 0 struct { allStructNames := structNames }).run' {}

end DefaultFields

private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (source : Source) : TermElabM Expr := do
  let structName ← getStructName stx expectedType? source
  unless isStructureLike (← getEnv) structName do
    throwError! "invalid \{...} notation, '{structName}' is not a structure"
  match mkStructView stx structName source with
  | Except.error ex  => throwError ex
  | Except.ok struct =>
    let struct ← expandStruct struct
    trace[Elab.struct] "{struct}"
    let (r, struct) ← elabStruct struct expectedType?
    DefaultFields.propagate struct
    pure r

@[builtinTermElab structInst] def elabStructInst : TermElab := fun stx expectedType? => do
  match (← expandNonAtomicExplicitSource stx) with
  | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | none =>
    let sourceView ← getStructSource stx
    match (← isModifyOp? stx), sourceView with
    | some modifyOp, Source.explicit source _ => elabModifyOp stx modifyOp source expectedType?
    | some _,        _                        => throwError "invalid {...} notation, explicit source is required when using '[<index>] := <value>'"
    | _,             _                        => elabStructInstAux stx expectedType? sourceView

builtin_initialize registerTraceClass `Elab.struct

end Lean.Elab.Term.StructInst
