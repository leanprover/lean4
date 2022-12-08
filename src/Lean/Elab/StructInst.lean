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
/-!
  # Structure Instances

  This file defines a term elaborator for structure instances, which are schematically of the form
  `{ $[s,* with]? fields,* $[..]? $[: type] }`. Each field in `field` is of the form `x := val`,
  with `x` the name of the field or a literal specifying its index in the structure (e.g. `3`) and
  `val` the field's value. If `x` is a variable, we can abbreviate `x := x` as simply `x`. (We can
  also use `modifyOp`s via `[]` syntax.) A list of structures `s,*` can be given to perform a
  structure update; `..` can be provided to indicate that all unspecified fields should be filled
  by holes, and is used in patterns; and the type can be specified within the structure instance
  syntax as well.

  ## Overview of code - Short version

  We start by applying some basic macros to the syntax, then parse it into a bare-bones `Struct`
  with `mkStructView`. This `Struct` will be updated with representations of its fields (and other
  information) as they're computed over the course of the elaboration. We then use `expandStruct`
  to put the fields in a canonical form (normalizing the LHS's of any field bindings, collecting
  fields specified in sources, grouping the fields of parent structures together, accounting for
  omitted fields) and create indicators of the field values (`FieldVal`s) for each field. These
  hold the raw syntax encountered for a field or indicate its absence or nested quality. We then
  `elabStruct` that `Struct` into an `ElabStructResult`, which holds the potential resulting
  elaborated expression (an application of the structure's single constructor to its fields'
  values—these values may be metavariables if they were omitted in the original syntax) plus info
  on the original `Struct`. We then attempt to synthesize default values for all omitted fields
  using `propagate` to assign any metavariables that are standing in for default values, and then
  return the expression.

  ## Overview of code - Long version

  Before we start, we apply macros which take care of type annotations and expand field
  abbreviations (e.g. turning `x` into `x := x`).

  Our first non-macro step is to extract the sources (everything before `with`, if present, and any
  occurrences of `..`). Then we feed this to `elabStructInstAux` along with the
  raw syntax and expected type. Inside `elabStructInstAux` we make the syntax into an extremely
  basic `Struct` (`mkStructView`).

  The `Struct` organizes all information pertaining to the structure instance, and is updated
  throughout the elaboration as various parts are computed.

  One of its fields is `field`, which holds a list of `Field Struct`'s. (The appearance of `Struct`
  within `Field Struct` is to allow the `Struct`s to nest other `Struct`s when we have subobjects.)

  The fields of each element of the `field : List (Field Struct)` field (got that?) are

  * `ref : Syntax`, which holds the `Syntax` found for that field
  * `lhs : FieldLHS`, which describes the name of the field in question
  * `val : FieldVal`, which holds basic information on what values were encountered in the syntax
  * `expr? : Option Expr`, which holds the elaborated expression when it becomes available (or a
    metavariable, if the value needs to be synthesized as a default value). It begins at
    this stage as `none`.

  There's a "pre-expression framework" set up early on in the process in the form of FieldVal's,
  which organize the raw information for each field. Each `FieldVal` can be a:

  * `.term stx` where `stx` is syntax, if a term was provided via syntax
  * `.default` if the field was omitted—however, if we had encountered `..` in the syntax, we use
    a `.term` with a syntactic hole for each missing field instead of using a `.default` value
  * `.nested s` where `s` is a `Struct` if the field represents a parent structure, e.g.
    `toFoo`

  The `FieldVal`s in a struct might be modified or re-organized as elaboration proceeds: for
  example, we might start with a `.term` but then turn it into a field within a `.nested` struct
  during `groupFields` if they belong to a subobject. `mkStructView` turns any encountered syntax
  specifying a field into a `.term stx`. `expandStruct` sets up the rest: canonicalizing different
  ways of specifying fields into `FieldLHS`s (`expandCompositeFields`, `expandNumLitFields`,
  `expandParentFields`), grouping fields into `.nested` substructures (`groupFields`), and taking
  care of missing fields by e.g. adding them as `.default` `FieldVal`s (`addMissingFields`).

  `elabStructInstAux` then calls `elabStruct` on the still-skeletal `Struct` (which has appropriate
  `FieldVal`s, but `none` for each field's `expr?`), which turns the `Struct` into an
  `ElabStructResult`.

  `elabStruct` elaborates everything but defaults, constructing the structure instance as an
  expression given by the application of the structure's constructor to the values it finds by
  elaborating the `stx` in any `.term stx` `FieldVal` while ensuring the appropriate type. (It's
  not quite true that no defaults are taken care of here: `autoparam`s are turned into `.term`s.)
  If the `FieldVal` is `.nested s`, it calls `elabStruct` on `s`; if it finds a `.default`
  `FieldVal`, it uses a fresh metavariable as the elaborated expression, and defers synthesis of
  that default value to the default loop. Like other elaborated expressions, this is both inserted
  into the constructor application expression and stored in `expr?`. We also annotate that
  metavariable with ``structInstDefault` to directly indicate that it must be synthesized during
  the default loop.

  As it does this, it stores any elaborated expressions in the `expr?` field of the corresponding
  fields and builds the constructor application expression, which is stored in a field of the
  resulting `ElabStructResult` structure (coincidentally also named "`val`"). Occasionally the
  `FieldVals` for each field are updated as well. Also returned in `ElabStructResult` is the
  updated `Struct` with all its new fields, and `instMVars`, an array of metavariables for dealing
  with typeclass instance synthesis.

  We finish our elaboration of the structure instance with the `propagate` loop, which iteratively
  synthesizes the defaults. We find out which defaults have not yet been synthesized with
  `isMissingDefault?`, which checks that the metavariables which we used as a placeholder for
  unsynthesized default values back in `elabStruct` is annotated with the ``structInstDefault`
  indicator and that it's still unassigned (i.e. that it has not yet had a default value attached
  to it). As we synthesize default values, we assign these metavariables to the values
  we find. This leads the new values to appear in the constructor application expression we've
  constructed upon instantiation.

  The fact that it "iteratively" synthesizes defaults refers to the fact that sometimes the default
  values of fields reference fields in parent structures which may also need to be synthesized via
  the default value loop (etc.). If we've searched as far as we can and there are still fields that
  are `isMissingDefault?`, we throw an error with the missing fields.

-/

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

/--
  Syntactically move any type specification outside of the structure instance syntax:
  `{ x := 0 : Foo }` becomes `{ x := 0 } : Foo`.
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

/-- Information for any explicit sources encountered, i.e. for an `sᵢ` in `s₁, ..., sₙ with` -/
structure ExplicitSourceInfo where
  /-- The syntax of some `sᵢ` in `s₁, ..., sₙ with` -/
  stx        : Syntax
  /-- The name of some structure `sᵢ` in `s₁, ..., sₙ with` -/
  structName : Name
  deriving Inhabited

/--
  Information on other sources of field values via structure update syntax or `..`.

  Collects explicit source info (that which precedes `with` in structure updates) and implicit
  source info (that which is given by the presence or absence of `..`).
-/
structure Source where
  /-- info for all `sᵢ` in `s₁, ..., sₙ with` -/
  explicit : Array ExplicitSourceInfo
  /-- `..` syntax, if encountered -/
  implicit : Option Syntax
  deriving Inhabited

/--
  Check if neither an explicit nor an implicit source has been specified (i.e. no `with` nor `..`)
-/
def Source.isNone : Source → Bool
  | { explicit := #[], implicit := none } => true
  | _ => false

/--
  Put an array of source syntax into a form which matches
  `optional (atomic (sepBy1 termParser ", " >> " with ")`, e.g. `s₁, s₂, s₃ with`.

  Panics if its first argument is an empty `Array`.
-/
private def mkSourcesWithSyntax (sources : Array Syntax) : Syntax :=
  let ref := sources[0]!
  let stx := Syntax.mkSep sources (mkAtomFrom ref ", ")
  mkNullNode #[stx, mkAtomFrom ref "with "]

/--
  Extract and process both explicit (`s₁, ..., sₙ with`) and implicit (`..`) source
  syntax from structure syntax.
-/
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
  ```lean
  def structInstArrayRef := leading_parser "[" >> termParser >>"]"
  ```
-/
private def isModifyOp? (stx : Syntax) : TermElabM (Option Syntax) := do
  let s? ← stx[2].getSepArgs.foldlM (init := none) fun s? arg => do
    /- arg is of the form `structInstFieldAbbrev <|> structInstField` -/
    if arg.getKind == ``Lean.Parser.Term.structInstField then
      /- Remark: the syntax for `structInstField` is
         ```lean
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

/-- Elaborate `modifyOp`s given a single explicit source. -/
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
  This method tries to postpone execution if the expected type is not available.

  If the expected type is available and it is a structure, then we use it.
  Otherwise, we use the type of the first source.
-/
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
    | _                      => useSource ()
where
  throwUnknownExpectedType :=
    throwError "invalid \{...} notation, expected type is not known"
  throwUnexpectedExpectedType type (kind := "expected") := do
    let type ← instantiateMVars type
    if type.getAppFn.isMVar then
      throwUnknownExpectedType
    else
      throwError "invalid \{...} notation, {kind} type is not of the form (C ...){indentExpr type}"

/-- Information on the left hand side of a binding encountered in structure syntax. -/
inductive FieldLHS where
  /-- A representation of the name of a field as encountered in binding syntax (e.g. `x` in
      `x := ...`). -/
  | fieldName  (ref : Syntax) (name : Name)
  /-- A representation of the index of a field as encountered in binding syntax (e.g. `3` in
    `3 := ...`). -/
  | fieldIndex (ref : Syntax) (idx : Nat)
  /-- A representation of a modifyOp as encountered in binding syntax. -/
  | modifyOp   (ref : Syntax) (index : Syntax)
  deriving Inhabited

instance : ToFormat FieldLHS := ⟨fun lhs =>
  match lhs with
  | .fieldName _ n  => format n
  | .fieldIndex _ i => format i
  | .modifyOp _ i   => "[" ++ i.prettyPrint ++ "]"⟩

/--
  A limited, pre-expression description of the values of fields. Only terms given by raw syntax,
  nested values (for subobjects), and missing values are can be specified.

  The polymorphism via its `Type` argument is only used for nested `FieldVal`s, which need to
  know what type their argument should be. In practice, we only ever take this argument to be
  `Struct`.
-/
inductive FieldVal (σ : Type) where
  /-- Term syntax encountered on the RHS of a binding, e.g. `1+1` in `x := 1+1`. -/
  | term  (stx : Syntax) : FieldVal σ
  /-- A nested `FieldVal`, which in practice is used to hold subobjects as `Struct`s. -/
  | nested (s : σ)       : FieldVal σ
  /-- An indication that this field was missing, i.e. not specified explicitly in the syntax. -/
  | default              : FieldVal σ -- mark that field must be synthesized using default value
  deriving Inhabited

/--
  A representation of a field in a structure. This contains the original syntax of the field
  (`ref`), a representation of the LHS of the `:=` binding (`lhs`), the pre-expression `FieldVal`
  (`val`), and the actual expression that we take to be the value of the field (`expr?`).

  `expr?` begins as `none`, and is modified over the course of this code as we figure out whether
  we need to elaborate some syntax encountered (e.g. if `.term stx` is in `val`) or if the field
  value is `.default` (in which case we make a metavariable).
-/
structure Field (σ : Type) where
  /-- The syntax of the binding used to specify this field. -/
  ref   : Syntax
  /-- Information on the LHS of the binding used to specify this field. -/
  lhs   : List FieldLHS
  /-- The basic content of the field value, prior to elaboration. -/
  val   : FieldVal σ
  /-- The elaborated value of the field in question as it becomes available, which starts
      out as `none` and is updated during `elabStruct` to either elaborated term syntax if
      available or metavariables if not. These metavariables may later get assigned to synthesized
      defaults. -/
  expr? : Option Expr := none
  deriving Inhabited

/-- Check if the LHS of the binding specifying a field is a single `FieldLHS`. -/
def Field.isSimple {σ} : Field σ → Bool
  | { lhs := [_], .. } => true
  | _                  => false

/--
  The organized content of the structure instance.

  The field `params` is used for `.default` value propagation. It is initially empty, and
  then set at `elabStruct`.
-/
inductive Struct where
  /-- Remark: the field `params` is use for default value propagation. It is initially empty, and
      then set at `elabStruct`. -/
  | mk (ref : Syntax) (structName : Name) (params : Array (Name × Expr)) (fields : List (Field Struct)) (source : Source)
  deriving Inhabited

/-- Abbreviation for `List (Field Struct)`: A list of representations of the structure's fields. -/
abbrev Fields := List (Field Struct)

/-- The original syntax of the structure instance. -/
def Struct.ref : Struct → Syntax
  | ⟨ref, _, _, _, _⟩ => ref

/-- The name of the structure. -/
def Struct.structName : Struct → Name
  | ⟨_, structName, _, _, _⟩ => structName

/-- Parameters used during the initial processing of `.default` fields. Initially `none`, and set
    at `elabStruct`. -/
def Struct.params : Struct → Array (Name × Expr)
  | ⟨_, _, params, _, _⟩ => params

/-- The list of `fields` in the structure instance as `Field Struct`s. Updated over the course of
    the elaboration to include computed values. -/
def Struct.fields : Struct → Fields
  | ⟨_, _, _, fields, _⟩ => fields

/-- Information on other sources of values for the structure, which consists of any structures
    preceding `with` in structure update syntax and any `..` syntax following the field bindings. -/
def Struct.source : Struct → Source
  | ⟨_, _, _, _, s⟩ => s

/-- `true` iff all fields of the given structure are marked as `default` -/
partial def Struct.allDefault (s : Struct) : Bool :=
  s.fields.all fun { val := val,  .. } => match val with
    | .term _   => false
    | .default  => true
    | .nested s => allDefault s

/-- Pretty-prints a field (`Field Struct`). Uses the field LHS's and its `val : FieldVal Struct`. -/
def formatField (formatStruct : Struct → Format) (field : Field Struct) : Format :=
  Format.joinSep field.lhs " . " ++ " := " ++
    match field.val with
    | .term v   => v.prettyPrint
    | .nested s => formatStruct s
    | .default  => "<default>"

/-- Pretty-prints a `Struct`. -/
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

/--
  Turns a `FieldLHS` into syntax. The first argument specifies whether this is the first in a list
  of `FieldLHS`'s or not.

  Recall that `structInstField` elements have the form
  ```lean
    def structInstField  := leading_parser structInstLVal >> " := " >> termParser
    def structInstLVal   := leading_parser (ident <|> numLit <|> structInstArrayRef) >> many (("." >> (ident <|> numLit)) <|> structInstArrayRef)
    def structInstArrayRef := leading_parser "[" >> termParser >>"]"
  ```

  Remark: this code relies on the fact that `expandStruct` only transforms `fieldLHS.fieldName`
-/
def FieldLHS.toSyntax (first : Bool) : FieldLHS → Syntax
  | .modifyOp   stx _    => stx
  | .fieldName  stx name => if first then mkIdentFrom stx name else mkGroupNode #[mkAtomFrom stx ".", mkIdentFrom stx name]
  | .fieldIndex stx _    => if first then stx else mkGroupNode #[mkAtomFrom stx ".", stx]

/-- Extracts the `stx` from a `.term stx : FieldVal Struct`. Panics when called on any other
    constructor of `FieldVal Struct`. -/
def FieldVal.toSyntax : FieldVal Struct → Syntax
  | .term stx => stx
  | _                 => unreachable!

/-- Turns a field (as a `Field Struct`) into syntax if has a `val` of the form `.term stx`; panics
    otherwise. Panics if the `lhs` is an empty list. -/
def Field.toSyntax : Field Struct → Syntax
  | field =>
    let stx := field.ref
    let stx := stx.setArg 2 field.val.toSyntax
    match field.lhs with
    | first::rest => stx.setArg 0 <| mkNullNode #[first.toSyntax true, mkNullNode <| rest.toArray.map (FieldLHS.toSyntax false) ]
    | _ => unreachable!

/-- Processes syntax into a `FieldLHS`. -/
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

/-- Processes structure instance syntax into a `Struct` given the `structName` and its `source`s. -/
private def mkStructView (stx : Syntax) (structName : Name) (source : Source) : MacroM Struct := do
  /- Recall that `stx` is of the form
     ```lean
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

/-- (Monadic) Modifies a `Struct`'s fields with a monadic function. -/
def Struct.modifyFieldsM {m : Type → Type} [Monad m] (s : Struct) (f : Fields → m Fields) : m Struct :=
  match s with
  | ⟨ref, structName, params, fields, source⟩ => return ⟨ref, structName, params, (← f fields), source⟩

/-- Modify a `Struct`'s `Fields` with a function. -/
def Struct.modifyFields (s : Struct) (f : Fields → Fields) : Struct :=
  Id.run <| s.modifyFieldsM f

/-- Overwrite a `Struct`'s fields. -/
def Struct.setFields (s : Struct) (fields : Fields) : Struct :=
  s.modifyFields fun _ => fields

/-- Overwrite a `Struct`'s params. -/
def Struct.setParams (s : Struct) (ps : Array (Name × Expr)) : Struct :=
  match s with
  | ⟨ref, structName, _, fields, source⟩ => ⟨ref, structName, ps, fields, source⟩

/-- Breaks down non-anonymous names in the lhs of fields into lists of their components.  -/
private def expandCompositeFields (s : Struct) : Struct :=
  s.modifyFields fun fields => fields.map fun field => match field with
    | { lhs := .fieldName _ (.str Name.anonymous ..) :: _, .. } => field
    | { lhs := .fieldName ref n@(.str ..) :: rest, .. } =>
      let newEntries := n.components.map <| FieldLHS.fieldName ref
      { field with lhs := newEntries ++ rest }
    | _ => field

/--
  Replaces field lhs's that are specified by index with the name of the field (as registered in
  the structure).
-/
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

/--
  For example, consider the following structures:
  ```lean
  structure A where
    x : Nat

  structure B extends A where
    y : Nat

  structure C extends B where
    z : Bool
  ```
  This method expands parent structure fields using the path to the parent structure.
  For example,
  ```lean
  { x := 0, y := 0, z := true : C }
  ```
  is expanded into
  ```lean
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

/--
  Abbreviation for `HashMap Name Fields`: A hash map from field names to lists of representations
  of fields.
-/
private abbrev FieldMap := HashMap Name Fields

/--
  Creates a hash map from field names to lists of representations of fields. The length of the
  list can be greater than one if the field is not simple. Panics if the lhs of a field is empty.
-/
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

/-- Unwraps a `Field Struct` from a list of length one, and otherwise returns `none`. -/
private def isSimpleField? : Fields → Option (Field Struct)
  | [field] => if field.isSimple then some field else none
  | _       => none

/--
  Finds the index of the field name in its third argument in the list of field names in its
  second. The first argument (the name of the structure) is used only for descriptive error
  messages.
-/
private def getFieldIdx (structName : Name) (fieldNames : Array Name) (fieldName : Name) : TermElabM Nat := do
  match fieldNames.findIdx? fun n => n == fieldName with
  | some idx => return idx
  | none     => throwError "field '{fieldName}' is not a valid field of '{structName}'"

/--
  Constructs the syntax for a field projection. Only does so if the given field name is in fact a
  field of the given structure name; returns `none` otherwise.
-/
def mkProjStx? (s : Syntax) (structName : Name) (fieldName : Name) : TermElabM (Option Syntax) := do
  if (findField? (← getEnv) structName fieldName).isNone then
    return none
  return some <| mkNode ``Parser.Term.proj #[s, mkAtomFrom s ".", mkIdentFrom s fieldName]

/-- Gets a field from a list of fields by name. If not found, returns `none`. -/
def findField? (fields : Fields) (fieldName : Name) : Option (Field Struct) :=
  fields.find? fun field =>
    match field.lhs with
    | [.fieldName _ n] => n == fieldName
    | _                => false

mutual

  /--
    Group fields that belong to a subobject as a `Struct` under that subobject field via a
    `.nested s` `FieldVal`. For example, a `Struct` representing
    `{ toFoo.x := 1, toFoo.y := 2, z := 3 }` will become one representing
    `{ toFoo := { x := 1, y := 2 }, z := 3 }`.
  -/
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

  /--
    Add `val : FieldVal`s to fields as specified by the sources.

    If a value is found in the explicit sources (i.e. prior to `with`), add it as a `.term` or a
    `.nested` `FieldVal`, as appropriate. If it's missing, check for `..`: if present, make a hole
    via syntax as a `.term`. In all other cases, mark missing fields as `.default`.
  -/
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

  /--
    Put the `Struct` into canonical form by expanding different ways of specifying fields
    (composite, by index, subobject); group fields by subobject; and incorporate values (or
    holes) sources.
  -/
  private partial def expandStruct (s : Struct) : TermElabM Struct := do
    let s := expandCompositeFields s
    let s ← expandNumLitFields s
    let s ← expandParentFields s
    let s ← groupFields s
    addMissingFields s

end

/-- Information about the constructor. -/
structure CtorHeaderResult where
  /-- The constructor function itself as an `Expr`. -/
  ctorFn     : Expr
  /-- The type of the constructor as an `Expr`. -/
  ctorFnType : Expr
  /-- Metavariables for instances. -/
  instMVars  : Array MVarId
  /-- Named parameters encountered in bindings of the type and the expressions used for them. -/
  params     : Array (Name × Expr)

/--
  Helper function that processes the constructor and its type until its first parameter, which
  represents the remaining arity of the constructor, reaches 0.
-/
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

/--
  Burrows into the body of a `.forallE` expression `n` times if possible, and returns the result.
  If an expression not of the form `.forallE` is encountered along the way, return `none`.
-/
private partial def getForallBody : Nat → Expr → Option Expr
  | i+1, .forallE _ _ b _ => getForallBody i b
  | _+1, _                => none
  | 0,   type             => type

/--
  When the expected type is known, attempt to get the type of the constructor by stripping `n`
  `.forallE`'s off of the expression and then assigning metavariables by `isDefEq`'ing with
  the expected type.
-/
private def propagateExpectedType (type : Expr) (numFields : Nat) (expectedType? : Option Expr) : TermElabM Unit := do
  match expectedType? with
  | none              => return ()
  | some expectedType =>
    match getForallBody numFields type with
      | none           => pure ()
      | some typeBody =>
        unless typeBody.hasLooseBVars do
          discard <| isDefEq expectedType typeBody

/-- Process information about a given `ConstructorVal`. -/
private def mkCtorHeader (ctorVal : ConstructorVal) (expectedType? : Option Expr) : TermElabM CtorHeaderResult := do
  let us ← mkFreshLevelMVars ctorVal.levelParams.length
  let val  := Lean.mkConst ctorVal.name us
  let type ← instantiateTypeLevelParams (ConstantInfo.ctorInfo ctorVal) us
  let r ← mkCtorHeaderAux ctorVal.numParams type val #[] #[]
  propagateExpectedType r.ctorFnType ctorVal.numFields expectedType?
  synthesizeAppInstMVars r.instMVars r.ctorFn
  return r

/--
  Annotate an expression to indicate that it must be synthesized as a default value.
  In practice, the expression will be a metavariable.
-/
def markDefaultMissing (e : Expr) : Expr :=
  mkAnnotation `structInstDefault e

/--
  Check if an expression has been annotated in a way that indicates it should be synthesized
  during the default loop.
-/
def defaultMissing? (e : Expr) : Option Expr :=
  annotation? `structInstDefault e

/-- Provide a descriptive error message if the structure instance elaboration fails. -/
def throwFailedToElabField {α} (fieldName : Name) (structName : Name) (msgData : MessageData) : TermElabM α :=
  throwError "failed to elaborate field '{fieldName}' of '{structName}, {msgData}"

/-- Attempt to synthesize a whole structure instance. Used when dealing with `.nested struct`s.  -/
def trySynthStructInstance? (s : Struct) (expectedType : Expr) : TermElabM (Option Expr) := do
  if !s.allDefault then
    return none
  else
    try synthInstance? expectedType catch _ => return none

/--
  The result of running `elabStruct` on a `Struct`, containing:
  * `struct : Struct`, now with updated `expr?` values in its fields, representing the values for
    those fields.
  * `val : Expr`, the constructor applied to the field values (`expr?`s). This is the actual
    expression that the structure instance elaborates to. (Note that this is distinct from the
    `val` of each field, which is a `FieldVal`.)
  * `instMVars : Array MVarId`, used for keeping track of instances.
-/
structure ElabStructResult where
  /-- The structure's constructor applied to the field values (`expr?`s). This is the actual
      expression that the structure instance elaborates to. -/
  val       : Expr
  /-- The `struct` that was fed to `elabStruct`, but now with updated `expr?` values for all of its
      fields containing their values as expressions. -/
  struct    : Struct
  /-- Used for dealing with instances. -/
  instMVars : Array MVarId

/--
  Elaborates a `Struct` into an `ElabStructResult`.

  This computes values for all fields of a structure (in `expr?`) on the basis of the given
  `FieldVal`s, while simultaneously building the expression for structure instance itself, in the
  form of its constructor applied to the expressions for each of its fields in turn.

  * `.term stx` `FieldVal`s are elaborated while ensuring the type (as given by the constructor's
    type)
  * `.nested s` `FieldVal`s are recursed into
  * `.default` `FieldVal`s are replaced with metavariables and annotated to indicate that they will
    get assigned during the default synthesis loop. Note that in this case the same metavariable is
    used both in the `expr?` field and the final constructed expression (`val`), so that assigning
    it gives access to the value in both places. If an `autoParam` is encountered in the type of a
    `.default` field, the tactic is elaborated immediately.
-/
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
        /- define a function that collects the values and fields that we compute at the end of each
          `fold` pass and organizes them into an output that builds up the structure instance as an
          `Expr` (starting with its cosntructor), the resulting type of that (partial) application,
          the list of `Field`s, and an array of any metavariables involved in typeclass inference.
          -/
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

/--
  Updated as we search for default values. We must search for default values overriden in derived
  structures.
-/
structure Context where
  /-- `Struct`s in the context which might supply default values. -/
  structs : Array Struct := #[]
  /-- The names of structures in the context which might supply default values. -/
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

/-- Stores an indicator of whether progress has been made during a round in the default loop. -/
structure State where
  /-- Indicates whether progress has been made during a round in the default loop. -/
  progress : Bool := false

/--
  Collects the names of all nested structures in a `Struct` (at any depth), including the name of
  the structure itself.
-/
partial def collectStructNames (struct : Struct) (names : Array Name) : Array Name :=
  let names := names.push struct.structName
  struct.fields.foldl (init := names) fun names field =>
    match field.val with
    | .nested struct => collectStructNames struct names
    | _ => names

/--
  Gets the maximum depth at which any structure is nested within the given structure, i.e. the
  height of its subobject poset.
-/
partial def getHierarchyDepth (struct : Struct) : Nat :=
  struct.fields.foldl (init := 0) fun max field =>
    match field.val with
    | .nested struct => Nat.max max (getHierarchyDepth struct + 1)
    | _ => max

/--
  (Monadic) Checks if the value of a field (`expr?`) is an unassigned metavariable that is
  annotated to indicate that it should be synthesized during the default loop.
-/
def isDefaultMissing? [Monad m] [MonadMCtx m] (field : Field Struct) : m Bool := do
  if let some expr := field.expr? then
    if let some (.mvar mvarId) := defaultMissing? expr then
      unless (← mvarId.isAssigned) do
        return true
  return false

/--
  (Monadic) Gets the first encountered field in a `Struct` whose value (`expr?`) is an unassigned
  metavariable that is annotated to indicate that it should be synthesized during the default
  loop.
-/
partial def findDefaultMissing? [Monad m] [MonadMCtx m] (struct : Struct) : m (Option (Field Struct)) :=
  struct.fields.findSomeM? fun field => do
   match field.val with
   | .nested struct => findDefaultMissing? struct
   | _ => return if (← isDefaultMissing? field) then field else none

/--
  (Monadic) Gets an array containing all fields in the `Struct` whose value (`expr?`) is an
  unassigned metavariable that is annotated to indicate that it should be synthesized during the
  default loop.
-/
partial def allDefaultMissing [Monad m] [MonadMCtx m] (struct : Struct) : m (Array (Field Struct)) :=
  go struct *> get |>.run' #[]
where
  /-- Loop through all fields in the `Struct`, recursing if a `.nested` one is found, and storing
      the field in a mutable array if it `isDefaultMissing?` -/
  go (struct : Struct) : StateT (Array (Field Struct)) m Unit :=
    for field in struct.fields do
      if let .nested struct := field.val then
        go struct
      else if (← isDefaultMissing? field) then
        modify (·.push field)

/--
  Gets the name of a field, assuming that its `lhs` is of the form `[.fieldName _ fieldName]`.
  Panics otherwise.
-/
def getFieldName (field : Field Struct) : Name :=
  match field.lhs with
  | [.fieldName _ fieldName] => fieldName
  | _ => unreachable!

/--
  Abbreviation for `ReaderT Context (StateRefT State TermElabM)`: A monad transformation of
  `TermElabM` that lets us access the `Context` (relevant for checking if default values are
  overridden) and keeping track of whether progress has been made during a round of the default
  loop (`State`).
-/
abbrev M := ReaderT Context (StateRefT State TermElabM)

/--
  Checks if the round has completed by checking that progress has been made and that the
  `maxDistance > 0`.
-/
def isRoundDone : M Bool := do
  return (← get).progress && (← read).maxDistance > 0

/-- Gets the value (`expr?`) of a field in a `Struct` given the name of the field. -/
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

/--
  If possible, make a default value by applying lambdas in the given constant to the appropriate
  field values or propagated parameter values.
-/
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

/--
  Attempt to synthesize the default value for a field, looping through nested structures if
  necessary. If a default value is found, assign it to the metavariable that we created for the
  field's value back in `elabStruct`, and return `true`. Otherwise return `false`.
-/
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

/--
  A step within the default synthesis loop. We proceed only if the round is not done. We loop
  through all fields in the structure, attempting to synthesize a default via
  `tryToSynthesizeDefault` when possible. If we succeed, we set `progress := true` in the `State`.

  Note: by now, all `expr?`s should be `some expr` from `elabStruct`, even if that `expr` is a
  metavariable; as such, we panic if one of them is `none`.
-/
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

/--
  The workhorse of the default synthesis loop.

  If there are no fields left that need to be synthesized during the default loop, we return from
  the loop.

  Otherwise, when we find a field that ought to be synthesized during the default loop, we take a
  `step`. If we've made `progress`, we call `propagateLoop` again and reset the depth to `0`. If we
  haven't, we call `propagateLoop` again with a higher depth.

  If the depth ever exceeds the hierarchy depth, we know that we've searched all nested structures,
  but no default values were to be found. In this case, we throw an error with the missing
  fields.
-/
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

/--
  The default synthesis loop.

  We call our workhorse function `propagateLoop` with appropriate initial values, which implements
  the loop itself (unless there is a variadic hole that specifies defaults are not to be used).

  Then, if there is a variadic hole, we assign the remaining metavariables that couldn't be
  synthesized into default values to (named) field holes.
-/
def propagate (struct : Struct) : TermElabM Unit :=
  let hierarchyDepth := getHierarchyDepth struct
  let structNames := collectStructNames struct #[]
  propagateLoop hierarchyDepth 0 struct { allStructNames := structNames } |>.run' {}

end DefaultFields

/--
  The main elaboration work. We normalize the `Struct`'s form, call
  `elabStruct` to compute field values and construct the elaborated expression, run the default
  synthesis loop (and provide named field holes if warranted), and synthesize instances.
-/
private def elabStructInstAux (stx : Syntax) (expectedType? : Option Expr) (source : Source) : TermElabM Expr := do
  let structName ← getStructName expectedType? source
  let struct ← liftMacroM <| mkStructView stx structName source
  let struct ← expandStruct struct
  trace[Elab.struct] "{struct}"
  /- We try to synthesize pending problems with `withSynthesize` combinator before trying to use default values.
     This is important in examples such as
      ```lean
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

/-- The term elaborator for structure instances. -/
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
