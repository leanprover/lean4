/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
prelude
import Lean.Elab.DocString.Builtin.Parsing
public import Lean.Elab.DocString.Builtin.Scopes
public import Lean.Elab.DocString.Builtin.Postponed
import Lean.Elab.Open
import Lean.Meta.Reduce
import Lean.Elab.Tactic.Doc
import Lean.Data.EditDistance
public import Lean.Elab.DocString.Builtin.Keywords
import Lean.Server.InfoUtils
import Init.Omega


namespace Lean.Doc
open Lean Elab Term
open Lean.Parser
open Lean.EditDistance
open scoped Lean.Doc.Syntax

set_option linter.missingDocs true

public section

/--
As elaboration results are not added to the environment as part of constants, manually record
references so that `shake` keeps their imports.
-/
private def elabExtraTerm (stx : Syntax) (expectedType? : Option Expr := none) : TermElabM Expr := do
  let e ← elabTermAndSynthesize stx expectedType?
  for c in e.getUsedConstants do
    recordExtraModUseFromDecl (isMeta := false) c
  return e

/-- Create an identifier while directly copying info -/
private def mkIdentFrom' (src : Syntax) (val : Name) : Ident :=
  ⟨Syntax.ident src.getHeadInfo (toString val).toRawSubstring val []⟩

/-- The code represents a global constant. -/
structure Data.Const where
  /-- The constant's name. -/
  name : Name
deriving TypeName, Repr

/-- The code represents a local variable. -/
structure Data.Local where
  /-- The local variable's name. -/
  name : Name
  /-- The local variable's ID. -/
  fvarId : FVarId
  /-- The local variable's context. -/
  lctx : LocalContext
  /-- The local variable's type. -/
  type : Expr
deriving TypeName


/-- The code represents a tactic. -/
structure Data.Tactic where
  /-- The name of the tactic's syntax kind. -/
  name : Name
deriving TypeName, Repr

/-- The code represents a conv tactic. -/
structure Data.ConvTactic where
  /-- The name of the tactic's syntax kind. -/
  name : Name
deriving TypeName, Repr

/-- The code represents an attribute application `@[...]`. -/
structure Data.Attributes where
  /-- The attribute syntax. -/
  stx : Syntax
deriving TypeName, Repr

/-- The code represents a single attribute. -/
structure Data.Attribute where
  /-- The attribute syntax. -/
  stx : Syntax
deriving TypeName, Repr

/-- The code represents an option. -/
structure Data.Option where
  /-- The option's name. -/
  name : Name
  /-- The option's declaration name. -/
  declName : Name
deriving TypeName, Repr


/-- The code represents a syntax category name. -/
structure Data.SyntaxCat where
  /-- The syntax category. -/
  name : Name
deriving TypeName, Repr

/-- The code represents syntax in a given category. -/
structure Data.Syntax where
  /-- The syntax category. -/
  category : Name
  /-- The parsed syntax. -/
  stx : Lean.Syntax
deriving TypeName, Repr

/-- The code represents a module name. -/
structure Data.ModuleName where
  /-- The module. -/
  «module» : Name
deriving TypeName, Repr



private def onlyCodes [Monad m] [MonadError m] (stxs : TSyntaxArray `inline) : m (Array StrLit) := do
  let mut codes := #[]
  for stx in stxs do
    match stx with
    | `(inline|code($s)) => codes := codes.push s
    | `(inline|$s:str) =>
      unless s.getString.all (·.isWhitespace) do
        throwErrorAt stx "Expected code"
    | other => throwErrorAt other "Expected code"
  return codes

private def onlyCode [Monad m] [MonadError m] (stxs : TSyntaxArray `inline) : m StrLit := do
  let codes ← onlyCodes stxs
  if h : codes.size = 1 then return codes[0]
  else throwError "Expected precisely 1 code argument"

private def strLitRange [Monad m] [MonadFileMap m] (s : StrLit) : m Lean.Syntax.Range := do
  let pos := (s.raw.getPos? (canonicalOnly := true)).get!
  let endPos := s.raw.getTailPos? true |>.get!
  return ⟨pos, endPos⟩

/--
Checks that a name exists when it is expected to.
-/
meta def checkNameExists : PostponedCheckHandler := fun _ info => do
  let some {name} := info.get? PostponedName
    | throwError "Expected `{.ofConstName ``PostponedName}`, got `{.ofConstName info.typeName}`"
  discard <| realizeGlobalConstNoOverload (mkIdent name)

private def getQualified (x : Name) : DocM (Array Name) := do
  -- We don't want to check whether the empty name is a suffix of names
  if x.isAnonymous then return #[]
  let names := (← getEnv).constants.toList
  let names := names.filterMap fun (y, _) => if !isPrivateName y && x.isSuffixOf y then some y else none
  names.toArray.mapM fun y => do
    let y ← unresolveNameGlobalAvoidingLocals y
    pure y

open Lean.Doc

/--
Displays a name, without attempting to elaborate implicit arguments.
-/
@[builtin_doc_role]
def name (full : Option Ident := none) (scope : DocScope := .local)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let x := s.getString.toName
  if x.isAnonymous then
    let h ←
      if s.getString.toSlice != s.getString.trimAscii && !s.getString.trimAscii.isEmpty then
        -- Like Markdown, Verso code elements that start and end with a space will strip the space,
        -- to allow code with leading or trailing backticks. But our suggestions shouldn't prefer
        -- that form here. Thus, the suggestion uses the delimiter positions instead of the string
        -- literal.
        let text ← getFileMap
        let ref? := do
          let stx ← (xs : Array Syntax)[0]?
          let `(inline|code(%$tk1 $_ )%$tk2) := stx
            | none
          let ⟨_, pos⟩ ← tk1.getRange?
          let ⟨tailPos, _⟩ ← tk2.getRange?
          pure <| Syntax.mkStrLit (String.Pos.Raw.extract text.source pos tailPos) (info := .synthetic pos tailPos)
        if let some ref := ref? then
            m!"Remove surrounding whitespace:".hint #[s.getString.trimAscii.copy] (ref? := some ref)
        else pure m!""
      else pure m!""
    throwErrorAt s "Not a valid name.{h}"
  let n := mkIdentFrom' s x
  if let some r := full then
    unless x.isSuffixOf r.getId do
      logErrorAt r "Expected a qualified version of {x}"
      return .code s.getString
  else
    if let some (e, fields) := (← resolveLocalName n.getId) then
      let t ← Meta.inferType e
      if fields.isEmpty then
        pushInfoLeaf <| .ofTermInfo {
          elaborator := .anonymous
          stx := n
          lctx := ← getLCtx
          expr := e
          expectedType? := some t
        }
        let data : Data.Local := {name := x, lctx := ← getLCtx, type := t, fvarId := e.fvarId!}
        return .other {
          name := ``Data.Local, val := .mk data
        } #[.code s.getString]
  match scope with
  | .local =>
    let x ←
      if let some r := full then
        let x ← realizeGlobalConstNoOverloadWithInfo r
        addConstInfo n x
        pure x
      else
        try
          realizeGlobalConstNoOverloadWithInfo n
        catch
          | err => do
            let ref ← getRef
            if let `(inline|role{$_x $_args*}%$tok[$_*]) := ref then
              let ss ← getQualified n.raw.getId
              let h ←
                if ss.isEmpty then pure m!""
                else m!"Insert a fully-qualified name:".hint (ref? := some tok) <|
                  ss.map fun x => { suggestion := s!" (full := {x})" ++ "}", previewSpan? := ref}
              logErrorAt s m!"{err.toMessageData}{h}"
            else logErrorAt s m!"{err.toMessageData}"
            return .code s!"{n.raw.getId}"
    return .other (.mk ``Data.Const (.mk (Data.Const.mk x))) #[.code s.getString]
  | .import xs =>
    let name :=
      if let some r := full then r.getId
      else x
    -- There should be a reference to the future task saved here, so doc rendering tools can
    -- create a link.
    let val : PostponedCheck := {
      handler := ``checkNameExists
      imports := xs.map (⟨·⟩)
      info := .mk { name : PostponedName }
    }
    return .other { name := ``PostponedCheck, val := .mk val } #[.code s.getString]

private def similarNames (x : Name) (xs : Array Name) : Array Name := Id.run do
  let s := x.toString
  let mut threshold := if s.length < 5 then 1 else if s.length < 8 then 2 else 3
  let mut candidates := #[]
  for x in xs do
    if let some d ← levenshtein s x.toString threshold then
      if d < threshold then threshold := d
      if d ≤ threshold then candidates := candidates.push (x, d)
  -- Only keep the smallest distance
  return candidates.filterMap fun (x, d) => do
    guard (d ≤ threshold)
    pure x

/--
Displays a name, without attempting to elaborate implicit arguments.
-/
@[builtin_doc_role]
def module (checked : flag true) (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let x := s.getString.toName
  let n := mkIdentFrom' s x
  if checked then
    let env ← getEnv
    if x != env.mainModule && x ∉ env.header.moduleNames then
      let ss := similarNames x env.header.moduleNames
      let ref ← getRef
      let unchecked : Option Meta.Hint.Suggestion ←
        match ref with
        | `(inline|role{$x +checked}%$tk2[$_]) =>
          let some b := x.raw.getTailPos?
            | pure none
          let some e := tk2.getPos?
            | pure none
          pure <| some {
            span? := some (Syntax.mkStrLit (String.Pos.Raw.extract (← getFileMap).source b e) (info := .synthetic b e)),
            previewSpan? := some ref,
            suggestion := "" : Meta.Hint.Suggestion
          }
        | `(inline|role{$_}%$tk2[$_]) =>
          pure <| some {
            span? := some tk2
            previewSpan? := some ref,
            suggestion := " -checked}": Meta.Hint.Suggestion
          }
        | _ => pure none
      let ss := unchecked.toArray ++ ss.map fun x =>
        { suggestion := x.toString, span? := some n, previewSpan? := some ref }
      let h ←
        if ss.isEmpty then pure m!""
        else m!"Either disable the existence check or use an imported module:".hint ss (ref? := some ref)
      logErrorAt n m!"Module is not transitively imported by the current module.{h}"

  return .other {name := ``Data.ModuleName, val := .mk (Data.ModuleName.mk x)} #[.code s.getString]


private def introduceAntiquotes (stx : Syntax) : DocM Unit :=
  discard <| stx.rewriteBottomUpM fun stx' =>
    match stx' with
    | .node _ (.str k "antiquot") #[_dollar, _, name, _] => do
      let k := if let .str k' "pseudo" := k then k' else k
      let ty ← Meta.mkAppM ``TSyntax #[← Meta.mkListLit (.const ``SyntaxNodeKind []) [toExpr k]]
      let lctx ← do
        let lctx ← getLCtx
        let fv ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fv name.getId ty
        addTermInfo' name (.fvar fv) (lctx? := some lctx) (isBinder := true) (expectedType? := some ty)
        pure lctx
      modify (fun st => { st with lctx })
      pure stx'
    | _ => pure stx'

/--
A reference to a tactic.

In `` {tactic}`T` ``, `T` can be any of the following:
 * The name of a tactic syntax kind (e.g. `Lean.Parser.Tactic.induction`)
 * The first token of a tactic (e.g. `induction`)
 * Valid tactic syntax, potentially including antiquotations (e.g. `intro $x*`)
-/
@[builtin_doc_role]
def tactic (checked : flag true) (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  if !checked then
    return .code s.getString
  else
    withRef s do
      let asString := s.getString
      let asName := asString.toName
      let allTactics ← Tactic.Doc.allTacticDocs
      let found := allTactics.filter fun tac => tac.userName == asString || tac.internalName == asName
      let mut exns := #[]
      if h : found.size = 0 then
        let (s, msg) ← AddErrorMessageContext.add s m!"Tactic `{asString}` not found"
        exns := exns.push <| Exception.error s msg
      else if h : found.size > 1 then
        let found := found.map (MessageData.ofConstName ·.internalName) |>.toList
        let (s, msg) ←
          AddErrorMessageContext.add s m!"Tactic name `{asString}` matches {.andList found}"
        exns := exns.push <| Exception.error s msg
      else
        let found := found[0]
        addConstInfo s found.internalName
        return .other {
            name := ``Data.Tactic, val := .mk { name := found.internalName : Data.Tactic}
          } #[.code s.getString]
      try
        let p := whitespace >> categoryParserFn `tactic
        let stx ← parseStrLit p s
        introduceAntiquotes stx
        return .code s.getString
      catch
        | e => exns := exns.push e
      if h : exns.size = 1 then
        throw exns[0]
      else
        throwErrorWithNestedErrors m!"Couldn't resolve tactic" exns

private def getConvTactic (name : StrLit) : DocM Name := do
    let p := rawIdentFn
    let stx ← parseStrLit p name
    let name := stx.getId
    let parserState := parserExtension.getState (← getEnv)
    let some convs := parserState.categories.find? `conv
      | throwError "Couldn't find conv tactic list"
    let found := convs.kinds.toArray.filterMap fun ⟨x, _⟩ =>
      if name.isSuffixOf x then some x else none
    if h : found.size = 0 then throwError m!"Conv tactic not found: `{name}`"
    else if h : found.size > 1 then
      let opts := (found.map MessageData.ofConstName).toList
      throwError m!"Multiple matching conv tactics: {.andList opts}"
    else
      return found[0]

private def throwOrNest (msg : MessageData) (exns : Array Exception) : DocM α :=
  if h : exns.size = 1 then
    throw exns[0]
  else
    throwErrorWithNestedErrors msg exns

/--
A reference to a conv tactic.

In `` {conv}`T` ``, `T` can be any of the following:
 * The name of a conv tactic syntax kind (e.g. `Lean.Parser.Tactic.Conv.lhs`)
 * Valid conv tactic syntax, potentially including antiquotations (e.g. `lhs`)
-/
@[builtin_doc_role]
def conv (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  withRef s do
    let mut exns := #[]
    try
      let t ← getConvTactic s
      addConstInfo s t
      return .other {
          name := ``Data.ConvTactic, val := .mk { name := t : Data.Tactic}
        } #[.code s.getString]
    catch
      | e => exns := exns.push e
    try
      let p := whitespace >> categoryParserFn `conv
      let stx ← parseStrLit p s
      introduceAntiquotes stx
      return .code s.getString
    catch
      | e => exns := exns.push e
    throwOrNest m!"Couldn't resolve conv tactic" exns

open Lean.Parser.Term in
/--
A reference to an attribute or attribute-application syntax.
-/
@[builtin_doc_role]
def attr (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  withRef s do
    let mut exns := #[]

    try
      let stx ← parseStrLit attributes.fn s
      let `(attributes|@[$attrs,*]) := stx
        | throwError "Not `@[attribute]` syntax"
      for a in (attrs : Array Syntax) do
        -- here `a` is of kind `attrInstance`, which is `("scoped" <|> "local")? attr`
        validateAttr a[1]

      return .other {name := ``Data.Attributes, val := .mk <| Data.Attributes.mk stx} #[
        .code s.getString
      ]
    catch
      | e => exns := exns.push e

    try
      let stx ← parseStrLit attrParser.fn s
      validateAttr stx
      return .other {name := ``Data.Attribute, val := .mk <| Data.Attribute.mk stx} #[
        .code s.getString
      ]
    catch
      | e => exns := exns.push e

    throwOrNest m!"Couldn't parse attributes" exns
where
  validateAttr (stx : Syntax) : DocM Unit := do
    if stx.getKind == ``Lean.Parser.Attr.simple then
      let attrName := stx[0].getId.eraseMacroScopes
      unless isAttribute (← getEnv) attrName do
        let nameStr := attrName.toString
        let threshold := max 2 (nameStr.length / 3)
        let attrs := getAttributeNames (← getEnv) |>.toArray |>.filterMap fun x =>
          let x := x.toString
          levenshtein x nameStr threshold |>.map (x, ·)
        let attrs := attrs.qsort (fun (_, i) (_, j) => i < j) |>.map (·.1)
        let hint ←
          if attrs.isEmpty then pure m!""
          else m!"Use a known attribute:".hint attrs (ref? := stx)
        logErrorAt stx m!"Unknown attribute `{attrName}`{hint}"

private def optionNameAndVal (stx : Syntax) : DocM (Ident × DataValue) := do
  let id := stx[1]
  let val := stx[3]

  let val ←
    if let some s := val.isStrLit? then pure <| .ofString s
    else if let some n := val.isNatLit? then pure <| .ofNat n
    else if val matches .atom _ "true" then pure <| .ofBool true
    else if val matches .atom _ "false" then pure <| .ofBool false
    else throwErrorAt val m!"Invalid option value. Expected a string, a number, `true`, or `false`,\
      but got {val}."
  return (⟨id⟩, val)

private def validateCat (x : Ident) : DocM Bool := do
  let c := x.getId
  let parsers := parserExtension.getState (← getEnv)
  if parsers.categories.contains c then
    return true
  else
    let allCats := parsers.categories.toArray.map (toString ·.1) |>.qsort
    let allCats := allCats.map (fun c => { suggestion := c })
    let h ← MessageData.hint m!"Use a syntax category name:" allCats (ref? := x)
    logErrorAt x m!"Unknown syntax category `{c}`{h}"
    return false

/--
A reference to a syntax category.
-/
@[builtin_doc_role]
def syntaxCat (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let x ← parseStrLit rawIdentFn s
  let c := x.getId
  if (← validateCat ⟨x⟩) then
    return .other {name := ``Data.SyntaxCat, val := .mk (Data.SyntaxCat.mk c)} #[.code (toString c)]
  else
    return .code (toString c)

private partial def onlyIdent : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty ·)
    if h : nonEmpty.size = 1 then onlyIdent nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
where
  isEmpty : Syntax → Bool
  | .node _ _ xs =>
    xs.all isEmpty
  | _ => false

/--
A description of syntax in the provided category.
-/
@[builtin_doc_role]
def «syntax» (cat : Ident) (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  if (← validateCat cat) then
    let cat := cat.getId
    let stx ← parseStrLit (categoryParserFn cat) s
    introduceAntiquotes stx
    return .other {name := ``Data.Syntax, val := .mk (Data.Syntax.mk cat stx)} #[.code s.getString]
  else
    return .code s.getString

private def givenContents : ParserFn :=
  whitespace >>
  sepBy1Fn false
    (nodeFn nullKind
     (identFn >>
       optionalFn (symbolFn ":=" >> termParser.fn) >>
       optionalFn (symbolFn ":" >> termParser.fn)))
    (symbolFn ",")

/--
A metavariable to be discussed in the remainder of the docstring.

There are four syntaxes that can be used:
 * `` {given}`x` `` establishes `x`'s type as a metavariable.
 * `` {given (type := "A")}`x` `` uses `A` as the type for metavariable `x`, but does not show that
   to readers.
 * `` {given}`x : A` `` uses `A` as the type for metavariable `x`.
 * `` {given}`x = e` `` establishes `x` as an alias for the term `e`

Additionally, the contents of the code literal can be repeated, with comma separators.

If the `show` flag is `false` (default `true`), then the metavariable is not shown in the docstring.
-/
@[builtin_doc_role]
def given (type : Option StrLit := none) (typeIsMeta : flag false) («show» : flag true) (xs : TSyntaxArray `inline) :
    DocM (Inline ElabInline) := do
  let s ← onlyCode xs

  let stxs ← parseStrLit givenContents s
  let stxs := stxs.getArgs.mapIdx Prod.mk |>.filterMap fun (n, s) =>
    if n % 2 = 0 then some s else none
  let mut lctx ← getLCtx
  for stx in stxs do
    let x := stx[0]
    let ty ← do
      let tyStx := stx[2][1]
      if tyStx.isMissing then
        if let some typeStr := type then
          some <$> parseQuotedStrLit (whitespace >> termParser.fn) typeStr
        else pure none
      else
        if let some s' := type then
          logWarningAt s' m!"Ignoring `type` argument because a type was provided"
        pure tyStx
    let ty' : Expr ←
      if let some stx := ty then
        if typeIsMeta then
          if let `(term|$x:ident) := stx then
            let u ← Meta.mkFreshLevelMVar
            let fv ← mkFreshFVarId
            let uni := mkSort u
            let t : Expr := .fvar fv
            let mv ← Meta.mkFreshExprMVar (type? := some uni) (userName := x.getId)
            lctx := lctx.mkLetDecl fv x.getId uni mv
            addTermInfo' x t (lctx? := some lctx) (isBinder := true) (expectedType? := some uni)
            pure t
          else
            logErrorAt stx m!"Expected identifier because flag `typeIsMeta` is set, but got {stx}"
            Meta.mkFreshExprMVar none
        else
          let ty' ← elabType stx
          registerDocMVar decl_name% ty' x m!"type of variable `{x.getId}`"
          pure ty'
      else
        let m ← Meta.mkFreshExprMVar none
        registerDocMVar decl_name% m x m!"type of variable `{x.getId}`"
        pure m
    let val : Option Expr ← do
      let valStx := stx[1][1]
      if valStx.isMissing then pure none
      else
        let v ← elabExtraTerm valStx (some ty')
        registerDocMVar decl_name% v x m!"value of variable `{x.getId}`"
        pure (some v)
    let fv ← mkFreshFVarId
    lctx :=
      if let some v := val then
        lctx.mkLetDecl fv x.getId ty' v
      else
        lctx.mkLocalDecl fv x.getId ty'
    addTermInfo' x (.fvar fv) (lctx? := some lctx) (isBinder := true) (expectedType? := some ty')
  modify (fun st => { st with lctx })

  if «show» then
    let text ← getFileMap
    let mut outStrs := #[]
    let mut failed := false
    for stx in stxs do
      let thisStr ←
        if let some ⟨b, e⟩ := stx[0].getRange? then
          if let some ⟨b', e'⟩ := stx[2][1].getRange? then
            pure <| s!"{String.Pos.Raw.extract text.source b e} : {String.Pos.Raw.extract text.source b' e'}"
          else pure <| String.Pos.Raw.extract text.source b e
        else
          failed := true
          break
      outStrs := outStrs.push thisStr
    if failed then
      return .code s.getString
    else
      return outStrs.map Inline.code
        |>.toList |>.intersperse (Inline.text ", ") |>.toArray
        |> Inline.concat
  else return .empty

private def givenInstanceContents : ParserFn :=
  whitespace >>
  sepBy1Fn false
    (nodeFn nullKind
     (optionalFn (atomicFn (identFn >> symbolFn ":")) >>
       termParser.fn))
    (symbolFn ",")

/--
An instance metavariable to be discussed in the remainder of the docstring.

This is similar to {given}, but the resulting variable is marked for instance synthesis
(with `BinderInfo.instImplicit`), and the name is optional.

There are two syntaxes that can be used:
 * `` {givenInstance}`T` `` establishes an unnamed instance of type `T`.
 * `` {givenInstance}`x : T` `` establishes a named instance `x` of type `T`.

Additionally, the contents of the code literal can be repeated, with comma separators.

If the `show` flag is `false` (default `true`), then the instance is not shown in the docstring.
-/
@[builtin_doc_role]
def givenInstance («show» : flag true) (xs : TSyntaxArray `inline) :
    DocM (Inline ElabInline) := do
  let s ← onlyCode xs

  let stxs ← parseStrLit givenInstanceContents s
  let stxs := stxs.getArgs.mapIdx Prod.mk |>.filterMap fun (n, s) =>
    if n % 2 = 0 then some s else none
  let mut lctx ← getLCtx
  let mut localInstances ← Meta.getLocalInstances
  let mut instCounter := 0
  for stx in stxs do
    let nameColonOpt := stx[0][0]
    let tyStx := stx[1]

    let ty' : Expr ← elabType tyStx
    registerDocMVar decl_name% ty' tyStx m!"instance type"
    let class? ← Meta.isClass? ty'
    let some className := class?
      | throwError m!"Expected a type class, but got `{.ofExpr ty'}`"

    -- Generate a fresh name if no name is provided
    let (userName, hasUserName) ←
      if nameColonOpt.isMissing then
        instCounter := instCounter + 1
        let n ← mkFreshUserName (`inst ++ className)
        pure (n, false)
      else
        pure (nameColonOpt.getId, true)

    let fv ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fv userName ty' BinderInfo.instImplicit
    localInstances := localInstances.push { fvar := .fvar fv, className }

    if hasUserName then
      addTermInfo' nameColonOpt[0] (.fvar fv)
        (lctx? := some lctx) (isBinder := true) (expectedType? := some ty')

  modify fun st => { st with lctx, localInstances }

  if «show» then
    let text ← getFileMap
    let mut outStrs := #[]
    let mut failed := false
    for stx in stxs do
      let nameColonOpt := stx[0][0]
      let thisStr ←
        if let some ⟨b', e'⟩ := stx[1].getRange? then
          -- Has type annotation
          if nameColonOpt.isMissing then
            -- No name, just show type
            pure <| String.Pos.Raw.extract text.source b' e'
          else
            -- Has name and type, nameColonOpt is `identFn >> symbolFn ":"`
            if let some ⟨b, e⟩ := nameColonOpt[0].getRange? then
              pure <| s!"{b.extract text.source e} : {b'.extract text.source e'}"
            else
              failed := true
              break
        else
          failed := true
          break
      outStrs := outStrs.push thisStr
    if failed then
      return .code s.getString
    else
      return outStrs.map Inline.code
        |>.toList |>.intersperse (Inline.text ", ") |>.toArray
        |> Inline.concat
  else return .empty


private def firstToken? (stx : Syntax) : Option Syntax :=
  stx.find? fun
    | .ident info .. => usable info
    | .atom info .. => usable info
    | _ => false
where
  usable
    | .original .. => true
    | _ => false

private builtin_initialize
  leanOutputExt : EnvExtension (NameMap (Array (MessageSeverity × String))) ←
    registerEnvExtension (asyncMode := .local) (pure {})


/--
Semantic highlighting included on syntax from elaborated terms in documentation.
-/
inductive DocHighlight where
  /-- The text represents the indicated constant. -/
  | const (name : Name) (signature : Format)
  /--
  The text represents the indicated local variable.

  The `fvarId` is not connected to a local context, but it can be useful for tracking bindings
  across elaborated fragments of syntax.
  -/
  | var (userName : Name) (fvarId : FVarId) (type : Format)
  /--
  The text represents the name of a field. `name` and `signature` refer to the projection function.
  -/
  | field (name : Name) (signature : Format)
  /--
  The text represents the name of a compiler option.
  -/
  | option (name declName : Name)
  /--
  The text is an atom, such as `if` or `def`.
  -/
  | keyword
  /--
  The text is an atom that represents a literal, such as a string literal.

  `isLitKind` returns `true` for `kind`.
  -/
  | literal (kind : SyntaxNodeKind) (type? : Option Format)

/--
A code snippet contained within a docstring. Code snippets consist of a series of strings, which are
optionally associated with highlighting information.
-/
structure DocCode where
  /--
  The highlighted strings.
  -/
  code : Array (String × Option DocHighlight) := #[]

/--
Adds the provided string `str`, with optional highlighting `hl?`, to the end of the code.
-/
def DocCode.push (code : DocCode) (str : String) (hl? : Option DocHighlight := none) : DocCode :=
  { code with code := code.code.push (str, hl?) }

instance : HAppend DocCode String DocCode where
  hAppend
    | ⟨c⟩, s => ⟨c.push (s, none)⟩

instance : Append DocCode where
  append
    | ⟨c1⟩, ⟨c2⟩ => ⟨c1 ++ c2⟩


private partial def highlightSyntax
    [Monad m] [MonadLiftT IO m]
    (trees : PersistentArray InfoTree) (stx : Syntax) : m DocCode := do
  (go stx).run {} <&> (·.2)
where
  go (stx : Syntax) : StateT DocCode m Unit := do
    match stx with
    | .node info kind args =>
      emitLeading info
      if kind == hygieneInfoKind then
        -- hygieneInfo nodes contain no source text; skip content but preserve whitespace
        for arg in args do
          emitLeading arg.getHeadInfo
          emitTrailing arg.getHeadInfo
        emitTrailing info
        return
      if isLitKind kind then
        match args with
        | #[.atom info' str] =>
          emitLeading info'
          let ty? ← typeFromInfo <| deepestNodes trees fun ci i _ =>
            if i.stx == stx then some (ci, i) else none
          emit str (some <| .literal kind ty?)
          emitTrailing info'
          emitTrailing info
          return
        | _ => pure ()
      args.forM go
      emitTrailing info
    | .ident info _x str _pre =>
      -- TODO: find projections in the info tree as well as syntactically (see comment on
      -- `identProjKind`)
      let docInfo? ← toDocInfo <| deepestNodes trees fun ci i _ =>
        if i.stx == stx then some (ci, i) else none
      emitLeading info
      emit str.toString docInfo?
      emitTrailing info
    | .atom info str =>
      emitLeading info
      emit str (some .keyword)
      emitTrailing info
    | .missing => return

  emit (code : String) (info? : Option DocHighlight := none) : StateT DocCode m Unit :=
    modify (fun st => st.push code info?)

  emitLeading : SourceInfo → StateT DocCode m Unit
  | .original leading .. => emit leading.toString
  | _ => pure ()

  emitTrailing : SourceInfo → StateT DocCode m Unit
  | .original _ _ trailing .. => emit trailing.toString
  | _ => pure ()

  typeFromInfo (infos : List (ContextInfo × Info)) : m (Option Format) := do
    for (ci, i) in infos do
      if let some ty ← ci.runMetaM i.lctx do
        (← i.type?).mapM (PrettyPrinter.ppExpr)
      then return some ty
    return none

  deepestNodes
      (trees : PersistentArray InfoTree)
      (f : ContextInfo → Info → PersistentArray InfoTree → Option (ContextInfo × Info)) :=
    trees.foldl (init := []) fun xs t => xs ++ (t.deepestNodes f)

  toDocInfo (infos : List (ContextInfo × Info)) : m (Option DocHighlight) := do
    let mut best := none
    for (ci, i) in infos do
      match i with
      | .ofTermInfo ti =>
        if let some (.var ..) := best then
          if let .const n _ := ti.expr then
            let sig ← ci.runMetaM ti.lctx <| PrettyPrinter.ppSignature n
            best := some <| .const n sig.fmt
        else if best.isNone then
          match ti.expr with
          | .const n .. =>
            let sig ← ci.runMetaM ti.lctx <| PrettyPrinter.ppSignature n
            best := some <| .const n sig.fmt
          | .fvar fvid =>
            let docInfo? ← ci.runMetaM ti.lctx do
              if let some ldecl := (← getLCtx).find? fvid then
                let type ← PrettyPrinter.ppExpr ldecl.type
                pure <| some <| .var ldecl.userName fvid type
              else pure none
            if let some docInfo := docInfo? then
              best := some docInfo
          | _ => continue
      | .ofFieldInfo fi =>
        let docInfo ← ci.runMetaM fi.lctx do
          let sig ← PrettyPrinter.ppSignature fi.projName
          pure <| .field fi.projName sig.fmt
        best := some docInfo
      | .ofOptionInfo oi =>
        best := some <| .option oi.optionName oi.declName
      | _ => continue
    return best

private structure NoInfo deriving TypeName

/--
The code represents an elaborated Lean command sequence.
-/
structure Data.LeanBlock where
  /--
  The highlighted code to be displayed.
  -/
  commands : DocCode := {}
deriving TypeName


/--
Elaborates a sequence of Lean commands as examples.

To make examples self-contained, elaboration ignores the surrounding section scopes. Modifications
to the environment are preserved during a single documentation comment, and discarded afterwards.

The named argument `name` allows a name to be assigned to the code block; any messages created by
elaboration are saved under this name.

The flags `error` and `warning` indicate that an error or warning is expected in the code.
-/
@[builtin_doc_code_block]
def lean (name : Option Ident := none) (error warning : flag false) («show» : flag true) (code : StrLit) :
    DocM (Block ElabInline ElabBlock) := do
  let text ← getFileMap
  let env ← getEnv
  let p := andthenFn whitespace (categoryParserFnImpl `command)
  -- TODO fallback for non-original syntax
  let pos := code.raw.getPos? true |>.get!
  let endPos := code.raw.getTailPos? true |>.get!
  let endPos := if endPos ≤ text.source.rawEndPos then endPos else text.source.rawEndPos
  let ictx :=
    mkInputContext text.source (← getFileName)
      (endPos := endPos) (endPos_valid := by simp only [endPos]; split <;> simp [*])
  let cctx : Command.Context := {fileName := ← getFileName, fileMap := text, snap? := none, cancelTk? := none}
  let scopes := (← get).scopes
  let (cmds, cmdState, trees) ← withSaveInfoContext do
    let mut cmdState : Command.State := { env, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes }
    let mut pstate : Parser.ModuleParserState := {
      pos
      recovering := false
      hasLeading := false
    }
    let mut cmds := #[]
    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := { cmdState with messages := messages }
      cmdState ← runCommand (Command.elabCommand cmd) cmd cctx cmdState
      if Parser.isTerminalCommand cmd then break
    setEnv cmdState.env
    modify fun st => { st with scopes := cmdState.scopes }

    for t in cmdState.infoState.trees do
      pushInfoTree t
    let trees := (← getInfoTrees)
    pure (cmds, cmdState, trees)

  let mut output := #[]
  for msg in cmdState.messages.toArray do
    let b := text.ofPosition msg.pos
    let e := msg.endPos |>.map text.ofPosition |>.getD (b.next text.source)
    let msgStr := b.extract text.source e
    let msgStx := Syntax.mkStrLit msgStr (info := .synthetic b e (canonical := true))
    unless msg.isSilent do
      if name.isSome then output := output.push (msg.severity, ← msg.data.toString)
      if msg.severity == .error && !error then
        let hint ← flagHint m!"The `+error` flag indicates that errors are expected:" #[" +error"]
        logErrorAt msgStx m!"Unexpected error:{indentD msg.data}{hint.getD m!""}"
      if msg.severity == .warning && !warning then
        let hint ← flagHint m!"The `+warning` flag indicates that warnings are expected:" #[" +warning"]
        logErrorAt msgStx m!"Unexpected warning:{indentD msg.data}{hint.getD m!""}"
      else
        withRef msgStx <| log msg.data (severity := .information) (isSilent := true)
    if let some x := name then
      modifyEnv (leanOutputExt.modifyState · (·.insert x.getId output))
  if «show» then
    if h : trees.size > 0 then
      let hl := Data.LeanBlock.mk (← highlightSyntax trees (mkNullNode cmds))
      return .other {name := ``Data.LeanBlock, val := .mk hl} #[.code code.getString]
    else
      return .code code.getString
  else
    return .empty
where
  runCommand (act : Command.CommandElabM Unit) (stx : Syntax)
      (cctx : Command.Context) (cmdState : Command.State) :
      DocM Command.State := do
    let (output, cmdState) ←
      match (← liftM <| IO.FS.withIsolatedStreams <| EIO.toIO' <| (act.run cctx).run cmdState) with
      | (output, .error e) => Lean.logError e.toMessageData; pure (output, cmdState)
      | (output, .ok ((), cmdState)) => pure (output, cmdState)

    if output.trimAscii.isEmpty then return cmdState

    let log : MessageData → Command.CommandElabM Unit :=
      if let some tok := firstToken? stx then logInfoAt tok
      else logInfo

    match (← liftM <| EIO.toIO' <| ((log output).run cctx).run cmdState) with
    | .error _ => pure cmdState
    | .ok ((), cmdState) => pure cmdState

  flagHint (hintText) (suggestions : Array String) : DocM (Option MessageData) := do
    let range? :=
      match ← getRef with
      | `(block|```$name $args* | $s ```) =>
        (mkNullNode (#[name] ++ args)).getRange?
      | `(inline|role{$name $args*}[$_]) =>
        (mkNullNode (#[name] ++ args)).getRange?
      | _ => none
    if let some ⟨b, e⟩ := range? then
      let str := b.extract (← getFileMap).source e
      let str := if str.startsWith "kw?" then "kw" ++ str.drop 3 else str
      let stx := Syntax.mkStrLit str (info := .synthetic b e (canonical := true))
      let suggs := suggestions.map (fun (s : String) => {suggestion := str ++ s})
      some <$> MessageData.hint hintText suggs (ref? := some stx)
    else pure none

/--
Displays output from a named Lean code block.
-/
@[builtin_doc_code_block]
def output (name : Ident) (severity : Option (WithSyntax MessageSeverity) := none) (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let allOut := leanOutputExt.getState (← getEnv)
  let some outs := allOut.find? name.getId
    | let possible := allOut.keysArray.map ({suggestion := ·.toString, diffGranularity := .word})
      let plurality := if possible.size > 1 then m!"one of the named blocks" else m!"the named block"
      let h ← MessageData.hint m!"Use {plurality}:" possible (ref? := some name)
      logErrorAt name m!"Output from block `{name.getId}` not found{h}"
      return .code code.getString
  let codeStr := code.getString
  for (sev, out) in outs do
    if out.trimAscii == codeStr.trimAscii then
      if let some s := severity then
        if s.val != sev then
          let sevName :=
            match sev with
            | .error => ``MessageSeverity.error
            | .warning => ``MessageSeverity.warning
            | .information => ``MessageSeverity.information
          let sevName ← unresolveNameGlobalAvoidingLocals sevName
          let h ← MessageData.hint m!"Update severity:" #[{suggestion := sevName.toString}] (ref? := some s.stx)
          logErrorAt s.stx m!"Mismatched severity. Message has severity `{sev}`.{h}"
      return .code codeStr
  let outs := sortByDistance codeStr outs
  let msg := if outs.size > 1 then m!"Use one of the outputs:" else m!"Use the output:"
  let h ← msg.hint (outs.map (withNl ·.2)) (ref? := code)
  logErrorAt code m!"Output not found.{h}"
  return .code codeStr
where
  withNl (s : String) :=
    if s.endsWith "\n" then s else s ++ "\n"

  sortByDistance {α} (target : String) (strings : Array (α × String)) : Array (α × String) :=
    let withDistance := strings.map fun (x, s) =>
      let d := levenshtein target s target.length
      (x, s, d.getD target.length)
    withDistance.qsort (fun (_, _, d1) (_, _, d2) => d1 < d2) |>.map fun (x, s, _) => (x, s)

/--
Indicates that a code element is intended as just a literal string, with no further meaning.

This is equivalent to a bare code element, except suggestions will not be provided for it.
-/
@[builtin_doc_role]
def lit (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  pure (.code s.getString)


/--
The code represents an elaborated Lean term.
-/
structure Data.LeanTerm where
  /--
  The highlighted code to be displayed.
  -/
  term : DocCode := {}
deriving TypeName

/-- The code represents syntax to set an option. -/
structure Data.SetOption where
  /-- The `set_option ...` syntax. -/
  term : DocCode := {}
deriving TypeName


private def leanTermContents : ParserFn :=
  whitespace >>
  (node nullKind (termParser >> optional (symbol ":" >> termParser))).fn

/--
Treats the provided term as Lean syntax in the documentation's scope.
-/
@[builtin_doc_role lean]
def leanRole (type : Option StrLit := none) (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let stx ← parseStrLit leanTermContents s
  withSaveInfoContext do
    let ty? ←
      withoutErrToSorry <| do
      if stx[1][1].isMissing then -- no colon
        if let some tyStr := type then
          let stx ← parseQuotedStrLit (whitespace >> termParser.fn) tyStr
          some <$> elabType stx
        else pure none
      else -- type after colon
        if let some t := type then
          logErrorAt t m!"Ignoring `{s.getString}` in favor of type provided after colon"
        some <$> elabType stx[1][1]
    withoutErrToSorry <| discard <| elabExtraTerm stx[0] ty?
  let trees := (← getInfoTrees)
  if h : trees.size > 0 then
    let tm := Data.LeanTerm.mk (← highlightSyntax trees stx)
    return .other {name := ``Data.LeanTerm, val := .mk tm} #[.code s.getString]
  else
    -- No info
    return .code s.getString

/--
Treats the provided term as Lean syntax in the documentation's scope.
-/
@[builtin_doc_code_block]
def leanTerm (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let stx ← parseStrLit leanTermContents code
  withSaveInfoContext do
    let ty? ←
      withoutErrToSorry <|
      if stx[1][1].isMissing then -- no colon
        pure none
      else -- type after colon
        some <$> elabType stx[1][1]
    withoutErrToSorry <| discard <| elabExtraTerm stx[0] ty?
  let trees := (← getInfoTrees)
  if h : trees.size > 0 then
    let tm := Data.LeanTerm.mk (← highlightSyntax trees stx)
    return .other {name := ``Data.LeanTerm, val := .mk tm} #[.code code.getString]
  else
    -- No info
    return .code code.getString


open Lean.Parser.Command («set_option») in
/--
A reference to an option.

In `` {option}`O` ``, `O` can be either:
 * The name of an option (e.g. `pp.all`)
 * Syntax to set an option to a particular value (e.g. `set_option pp.all true`)
-/
@[builtin_doc_role]
def option (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  withRef s do
    let spec : Syntax ⊕ Syntax ←
      try
        let stx ← parseStrLit «set_option».fn s
        pure (Sum.inl stx)
      catch
      | e1 =>
        try
          -- Here it's important to get the partial syntax in order to add completion info,
          -- but then abort processing.
          let (stx, err) ← parseStrLit' (nodeFn nullKind identWithPartialTrailingDot.fn) s
          addCompletionInfo <| CompletionInfo.option stx[0]
          if err then throw e1 else pure (Sum.inr stx[0])
        catch
        | e2 =>
          throwOrNest m!"Expected an option name or a valid `set_option`" #[e1, e2]
    match spec with
    | .inl stx =>
      let (id, val) ← optionNameAndVal stx
      -- For completion purposes, we discard `val` and any later arguments. We include the first
      -- argument (the keyword) for position information in case `id` is `missing`.
      addCompletionInfo <| CompletionInfo.option (stx.setArgs (stx.getArgs[*...3]))
      let optionName := id.getId.eraseMacroScopes
      try
        let decl ← getOptionDecl optionName
        pushInfoLeaf <| .ofOptionInfo { stx := id, optionName, declName := decl.declName }
        validateOptionValue optionName decl val
        let valStr :=
          match val with
          | .ofString v => v.quote
          | v => toString v
        let valHl : DocHighlight ←
          match val with
          | .ofBool b =>
            let constName := if b then ``Bool.true else ``Bool.false
            let sig ← PrettyPrinter.ppSignature constName
            pure <| .const constName sig.fmt
          | _ => pure <| .literal stx[3].getKind none
        let code := #[
          ("set_option", some .keyword), (" ", none),
          (toString optionName, some <| .option optionName decl.declName), (" ", none),
          (valStr, some valHl)
        ]
        return .other {name := ``Data.SetOption, val := .mk <| Data.SetOption.mk ⟨code⟩} #[
          .code s.getString
        ]
      catch
        | e =>
          let ref := e.getRef
          let ref ← if ref.isMissing then getRef else pure ref
          logErrorAt ref e.toMessageData
          return .code s.getString
    | .inr stx =>
      let optionName := stx.getId.eraseMacroScopes
      try
        let decl ← getOptionDecl optionName
        pushInfoLeaf <| .ofOptionInfo { stx, optionName, declName := decl.declName }

        return .other {
          name := ``Data.Option,
          val := .mk <| Data.Option.mk optionName decl.declName
        } #[
          .code s.getString
        ]
      catch
        | e =>
          let ref := e.getRef
          let ref ← if ref.isMissing then getRef else pure ref
          logErrorAt ref e.toMessageData
          return .code s.getString


private def assertTermContents : ParserFn :=
  whitespace >> termParser.fn

/--
Asserts that two terms are definitionally equal.

The terms are provided as two separate code elements, optionally followed by a third code element
that contains the type at which the terms are elaborated e.g.
`` {assert'}[`Nat.zero` `Nat.zero` `Nat`] ``.

Unlike `assert`, this role doesn't use the equality type, because it is needed in the prelude,
before the `=` notation is introduced.
-/
@[builtin_doc_role]
def assert' (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let codes ← onlyCodes xs
  let (lhsCode, rhsCode, tyCode?) ←
    match h : codes.size with
    | 2 => pure (codes[0], codes[1], none)
    | 3 => pure (codes[0], codes[1], some codes[2])
    | _ => throwError "Expected two or three code arguments: the two sides of the equality, \
        optionally followed by their type, but got {codes.size} arguments."
  let lhsStx ← parseStrLit assertTermContents lhsCode
  let rhsStx ← parseStrLit assertTermContents rhsCode
  let tyStx? ← tyCode?.mapM (parseStrLit assertTermContents)
  withSaveInfoContext do
    let ty? ← withoutErrToSorry <|
      match tyStx? with
      | some tyStx => some <$> elabType tyStx
      | none => pure none
    let lhs ← elabExtraTerm lhsStx ty?
    let rhs ← elabExtraTerm rhsStx ty?
    unless ← Meta.withTransparency .all <| Meta.isDefEq lhs rhs do
      throwError m!"Expected {lhs} = {rhs}, which is {← Meta.whnf lhs} = {← Meta.whnf rhs}, reducing to {← Meta.reduceAll lhs} = {← Meta.reduceAll rhs} but they are not equal."
  let str := lhsCode.getString ++ " = " ++ rhsCode.getString ++
    (tyCode?.map (" : " ++ ·.getString) |>.getD "")
  let trees ← getInfoTrees
  if trees.size > 0 then
    let mut code := (← highlightSyntax trees lhsStx) ++ " = " ++ (← highlightSyntax trees rhsStx)
    if let some tyStx := tyStx? then
      code := code ++ " : " ++ (← highlightSyntax trees tyStx)
    return .other {name := ``Data.LeanTerm, val := .mk <| Data.LeanTerm.mk code} #[.code str]
  else
    -- No info
    return .code str

/--
Asserts that an equality holds.
-/
@[builtin_doc_role]
def assert (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let stx ← parseStrLit termParser.fn s
  withSaveInfoContext do
    let ty ← withoutErrToSorry <| elabType stx
    match_expr (← Meta.whnf ty) with
    | Eq _ lhs rhs =>
      unless (← Meta.isDefEq lhs rhs) do
        throwErrorAt stx m!"Expected {lhs} = {rhs}, but they are not definitionally equal"
    | _ => throwErrorAt stx m!"Expected equality type"
  let trees ← getInfoTrees
  if trees.size > 0 then
    let tm := Data.LeanTerm.mk (← highlightSyntax trees stx)
    return .other {name := ``Data.LeanTerm, val := .mk tm} #[.code s.getString]
  else
    -- No info
    return .code s.getString

/--
Opens a namespace in the remainder of the documentation comment.

The `+scoped` flag causes scoped instances and attributes to be activated, but no identifiers are
brought into scope. The named argument `only`, which can be repeated, specifies a subset of names to
bring into scope from the namespace.
-/
@[builtin_doc_command]
def «open» (n : Ident) («scoped» : flag false) («only» : many Ident) : DocM (Block ElabInline ElabBlock) := do
  let nss ← resolveNamespace n
  if only.isEmpty then
    for ns in nss do
      unless «scoped» do
        let d := .simple ns []
        modify fun st => { st with openDecls := d :: st.openDecls }
      activateScoped ns
  else
    if «scoped» then
      throwError "`scoped` and `only` cannot be used together"
    for idStx in only do
      let declName ← OpenDecl.resolveNameUsingNamespacesCore nss idStx
      let d := .explicit idStx.getId declName
      modify fun st => { st with openDecls := d :: st.openDecls }
      if (← getInfoState).enabled then
        addConstInfo idStx declName
  return .empty

/--
Sets the specified option to the specified value for the remainder of the comment.
-/
@[builtin_doc_command]
def «set_option» (option : Ident) (value : DataValue) : DocM (Block ElabInline ElabBlock) := do
  addCompletionInfo <| CompletionInfo.option option
  let optionName := option.getId
  let decl ← withRef option <| getOptionDecl optionName
  pushInfoLeaf <| .ofOptionInfo { stx := option, optionName, declName := decl.declName }
  validateOptionValue optionName decl value
  let o ← getOptions
  modify fun s => { s with options := o.set optionName value }
  return .empty

/--
Constructs a link to the Lean language reference. Two positional arguments are expected:
 * `domain` should be one of the valid domains, such as `section`.
 * `name` should be the content's canonical name in the domain.
-/
@[builtin_doc_role]
def manual (domain : Ident) (name : String) (content : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let domStr := domain.getId.toString
  if domStr ∉ manualDomains then
    let h ← MessageData.hint "Use one of the valid documentation domains:"
      (manualDomains.map ({ suggestion := · })).toArray
      (ref? := some domain)
    throwErrorAt domain m!"Invalid documentation domain.{h}"
  match manualLink domStr name with
  | .ok url => return .link (← content.mapM elabInline) url
  | .error e => throwError e

/--
Suggests the `name` and `given` roles, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestName (code : StrLit) : DocM (Array CodeSuggestion) := do
  let stx ← parseStrLit identFn code
  let mut suggestions := #[]
  try
    discard <| realizeGlobalConstNoOverload stx
    suggestions := suggestions.push <| .mk ``name none none
  catch
    | _ =>
    if let some (_, []) := (← resolveLocalName stx.getId) then
      suggestions := suggestions.push <| .mk ``name none none
    else if stx.getId.components.length == 1 then
      suggestions := suggestions.push <| .mk ``given none none
  return suggestions

/--
Suggests `given` for the syntaxes not covered by `suggestName`.
-/
@[builtin_doc_code_suggestions]
def suggestGiven (code : StrLit) : DocM (Array CodeSuggestion) := do
  let stx ← parseStrLit givenContents code
  if stx[1][1].isMissing && stx[2][1].isMissing then
    return #[]
  else return #[.mk ``given none none]

/--
Suggests the `lean` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestLean (code : StrLit) : DocM (Array CodeSuggestion) := do
  try
    let stx ← parseStrLit leanTermContents code
    -- To cut down on false positives, we only suggest identifiers if their
    -- elaboration succeeds. Other terms are suggested if they parse.
    if onlyIdent stx then
      let ty? ←
        withoutErrToSorry <|
        if stx[1][1].isMissing then pure none
        else some <$> elabType stx[1][1]
      let tm ← withoutErrToSorry <| elabExtraTerm stx[0] ty?
    return #[.mk ``lean none none]

  catch | _ => return #[]

/--
Suggests the `leanTerm` code block, if applicable.
-/
@[builtin_doc_code_block_suggestions]
def suggestLeanTermBlock (code : StrLit) : DocM (Array CodeBlockSuggestion) := do
  try
    let stx ← parseStrLit leanTermContents code
    -- To cut down on false positives, we only suggest identifiers if their
    -- elaboration succeeds. Other terms are suggested if they parse.
    if onlyIdent stx then
      let ty? ←
        withoutErrToSorry <|
        if stx[1][1].isMissing then pure none
        else some <$> elabType stx[1][1]
      discard <| withoutErrToSorry <| elabExtraTerm stx[0] ty?
    return #[.mk ``leanTerm none none]
  catch | _ => return #[]

/--
Suggests the `lean` code block, if applicable.
-/
@[builtin_doc_code_block_suggestions]
def suggestLeanBlock (code : StrLit) : DocM (Array CodeBlockSuggestion) := do
  let p : ParserFn := whitespace >> many1Fn commandParser.fn
  try
    discard <| parseStrLit p code
    return #[.mk ``lean none none]
  catch | _ => return #[]

/--
Suggests the `tactic` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestTactic (code : StrLit) : DocM (Array CodeSuggestion) := do
  let asString := code.getString
  let asName := asString.toName
  let allTactics ← Tactic.Doc.allTacticDocs
  let found := allTactics.filter fun tac => tac.userName == asString || tac.internalName == asName
  if found.size = 1 then return #[.mk ``tactic none none]
  else
    let p := whitespace >> categoryParserFn `tactic
    try
      discard <| parseStrLit p code
      return #[.mk ``tactic none none]
    catch | _ => return #[]

/--
Suggests the `conv` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestConvTactic (code : StrLit) : DocM (Array CodeSuggestion) := do
  try
    _ ← getConvTactic code
    return #[.mk ``conv none none]
  catch
  | _ =>
    try
      let p := whitespace >> categoryParserFn `conv
      _ ← parseStrLit p code
      return #[.mk ``conv none none]
    catch
    | _ => return #[]

open Lean.Parser.Term in
/--
Suggests the `attr` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestAttr (code : StrLit) : DocM (Array CodeSuggestion) := do
  try
    let stx ← parseStrLit attributes.fn code
    let `(attributes|@[$_attrs,*]) := stx
      | return #[]
    return #[.mk ``attr none none]
  catch
    | _ => pure ()
  try
    let stx ← parseStrLit attrParser.fn code
    if stx.getKind == ``Lean.Parser.Attr.simple then
      let attrName := stx[0].getId.eraseMacroScopes
      if isAttribute (← getEnv) attrName then
        return #[.mk ``attr none none]
      else return #[]
    else
      return #[.mk ``attr none none]
  catch
    | _ => pure ()
  return #[]

open Lean.Parser.Command in
/--
Suggests the `option` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestOption (code : StrLit) : DocM (Array CodeSuggestion) := do
  try
    discard <| parseStrLit Command.«set_option».fn code
    return #[CodeSuggestion.mk ``option none none]
  catch
  | _ =>
    try
      let stx ← parseStrLit rawIdentFn code
      let name := stx.getId.eraseMacroScopes
      discard <| getOptionDecl name
      return #[CodeSuggestion.mk ``option none none]
    catch
    | _ =>
      return #[]

/--
Suggests the `syntaxCat` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestCat (code : StrLit) : DocM (Array CodeSuggestion) := do
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  if parsers.categories.contains code.getString.toName then
    return #[.mk ``syntaxCat none none]
  else
    return #[]

/--
Suggests the `syntax` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestSyntax (code : StrLit) : DocM (Array CodeSuggestion) := do
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  let cats := parsers.categories.toArray

  let mut candidates := #[]
  for (catName, _) in cats do
    try
      let stx ← parseStrLit (whitespace >> (categoryParser catName 0).fn) code
      -- Many syntax categories admit identifiers, so the false positive rate is high
      unless onlyIdent stx do
        candidates := candidates.push catName
    catch | _ => pure ()

  candidates.mapM fun cat => do
    return .mk ``«syntax» (some s!"{cat}") none

/--
Suggests the `module` role, if applicable.
-/
@[builtin_doc_code_suggestions]
def suggestModule (code : StrLit) : DocM (Array CodeSuggestion) := do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let s := code.getString
  if moduleNames.any (·.toString == s) then
    return #[.mk ``module none none]
  else return #[]
