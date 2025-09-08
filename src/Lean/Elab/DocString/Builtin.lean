/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
prelude
public import Lean.Elab.DocString
import Lean.DocString.Links
public import Lean.DocString.Syntax
public import Lean.Elab.InfoTree
public import Lean.Elab.Term.TermElabM
import Lean.Elab.Open
public import Lean.Parser
import Lean.Meta.Hint
import Lean.Elab.Tactic.Doc
import Lean.Data.EditDistance


namespace Lean.Doc
open Lean Elab Term
open Lean.Parser
open Lean.EditDistance
open scoped Lean.Doc.Syntax

set_option linter.missingDocs true

public section

/-- Create an identifier while directly copying info -/
private def mkIdentFrom' (src : Syntax) (val : Name) : Ident :=
  ⟨Syntax.ident src.getHeadInfo (toString val).toSubstring val []⟩

/-- The code represents a global constant. -/
structure Data.Const where
  /-- The constant's name. -/
  name : Name
deriving TypeName

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
deriving TypeName

/-- The code represents a conv tactic. -/
structure Data.ConvTactic where
  /-- The name of the tactic's syntax kind. -/
  name : Name
deriving TypeName

/-- The code represents an attribute application `@[...]`. -/
structure Data.Attributes where
  /-- The attribute syntax. -/
  stx : Syntax
deriving TypeName

/-- The code represents a single attribute. -/
structure Data.Attribute where
  /-- The attribute syntax. -/
  stx : Syntax
deriving TypeName

/-- The code represents syntax to set an option. -/
structure Data.SetOption where
  /-- The `set_option ...` syntax. -/
  stx : Syntax
deriving TypeName

/-- The code represents an option. -/
structure Data.Option where
  /-- The option's name. -/
  name : Name
deriving TypeName

/-- The code represents an atom drawn from some syntax. -/
structure Data.Atom where
  /-- The syntax kind's name. -/
  name : Name
  /-- The syntax category -/
  category : Name
deriving TypeName

/-- The code represents a syntax category name. -/
structure Data.SyntaxCat where
  /-- The syntax category. -/
  name : Name
deriving TypeName

/-- The code represents syntax in a given category. -/
structure Data.Syntax where
  /-- The syntax category. -/
  category : Name
  /-- The parsed syntax. -/
  stx : Lean.Syntax
deriving TypeName

private def onlyCode (xs : TSyntaxArray `inline) : DocM StrLit := do
  if h : xs.size = 1 then
    match xs[0] with
    | `(inline|code($s)) => return s
    | other => throwErrorAt other "Expected code"
  else
    throwError "Expected precisely 1 code argument"

/--
Displays a name, without attempting to elaborate implicit arguments.
-/
--@[builtin_doc_role]
def name (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let x := s.getString.toName
  let n := mkIdentFrom' s x
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
  let x ← realizeGlobalConstNoOverloadWithInfo n
  return .other (.mk ``Data.Const (.mk (Data.Const.mk x))) #[.code s.getString]

private def parseStrLit (p : ParserFn) (s : StrLit) : DocM Syntax := do
  let text ← getFileMap
  let env ← getEnv
  let endPos := s.raw.getTailPos? true |>.get!
  let endPos := if endPos ≤ text.source.endPos then endPos else text.source.endPos
  let ictx :=
    mkInputContext text.source (← getFileName)
      (endPos := endPos) (endPos_valid := by simp only [endPos]; split <;> simp [*])
  -- TODO fallback for non-original syntax
  let s := (mkParserState text.source).setPos (s.raw.getPos? (canonicalOnly := true)).get!
  let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) s

  if !s.allErrors.isEmpty  then
    throwError (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    pure s.stxStack.back
  else
    throwError ((s.mkError "end of input").toErrorMsg ictx)

private def parseStrLit' (p : ParserFn) (s : StrLit) : DocM (Syntax × Bool) := do
  let text ← getFileMap
  let env ← getEnv
  let endPos := s.raw.getTailPos? true |>.get!
  let endPos := if endPos ≤ text.source.endPos then endPos else text.source.endPos
  let ictx :=
    mkInputContext text.source (← getFileName)
      (endPos := endPos) (endPos_valid := by simp only [endPos]; split <;> simp [*])
  -- TODO fallback for non-original syntax
  let s := (mkParserState text.source).setPos (s.raw.getPos? (canonicalOnly := true)).get!
  let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) s

  let err ←
    if !s.allErrors.isEmpty then
      logError (s.toErrorMsg ictx)
      pure true
    else if !ictx.atEnd s.pos then
      logError ((s.mkError "end of input").toErrorMsg ictx)
      pure true
    else pure false
  pure (s.stxStack.back, err)

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
--@[builtin_doc_role]
def tactic (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
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
--@[builtin_doc_role]
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
--@[builtin_doc_role]
def attr (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  withRef s do
    let mut exns := #[]

    try
      let stx ← parseStrLit attributes.fn s
      let `(attributes|@[$_attrs,*]) := stx
        | throwError "Not `@[attribute]` syntax"
      return .other {name := ``Data.Attributes, val := .mk <| Data.Attributes.mk stx} #[
        .code s.getString
      ]
    catch
      | e => exns := exns.push e

    try
      let stx ← parseStrLit attrParser.fn s
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
            else m!"Use a known attribute:".hint attrs (ref? := s)
          logErrorAt stx m!"Unknown attribute `{attrName}`{hint}"

      return .other {name := ``Data.Attribute, val := .mk <| Data.Attribute.mk stx} #[
        .code s.getString
      ]
    catch
      | e => exns := exns.push e

    throwOrNest m!"Couldn't parse attributes" exns

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

open Lean.Parser.Command («set_option») in
/--
A reference to an option.

In `` {option}`O` ``, `O` can be either:
 * The name of an option (e.g. `pp.all`)
 * Syntax to set an option to a particular value (e.g. `set_option pp.all true`)
-/
--@[builtin_doc_role]
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

        return .other {name := ``Data.SetOption, val := .mk <| Data.SetOption.mk stx} #[
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

        return .other {name := ``Data.Option, val := .mk <| Data.Option.mk optionName} #[
          .code s.getString
        ]
      catch
        | e =>
          let ref := e.getRef
          let ref ← if ref.isMissing then getRef else pure ref
          logErrorAt ref e.toMessageData
          return .code s.getString

/--
Checks whether a syntax descriptor's value contains the given atom.
-/
private partial def containsAtom (e : Expr) (atom : String) : MetaM Bool := do
  let rec attempt (p : Expr) (tryWhnf : Bool) : MetaM Bool := do
    match p.getAppFnArgs with
    | (``ParserDescr.node, #[_, _, p]) => containsAtom p atom
    | (``ParserDescr.trailingNode, #[_, _, _, p]) => containsAtom p atom
    | (``ParserDescr.unary, #[.app _ (.lit (.strVal _)), p]) => containsAtom p atom
    | (``ParserDescr.binary, #[.app _ (.lit (.strVal "andthen")), p, _]) => containsAtom p atom
    | (``ParserDescr.nonReservedSymbol, #[.lit (.strVal tk), _]) => pure (tk.trim == atom)
    | (``ParserDescr.symbol, #[.lit (.strVal tk)]) => pure (tk.trim == atom)
    | (``Parser.withAntiquot, #[_, p]) => containsAtom p atom
    | (``Parser.leadingNode, #[_, _, p]) => containsAtom p atom
    | (``HAndThen.hAndThen, #[_, _, _, _, p1, p2]) =>
      containsAtom p1 atom <||> containsAtom p2 atom
    | (``Parser.nonReservedSymbol, #[.lit (.strVal tk), _]) => pure (tk.trim == atom)
    | (``Parser.symbol, #[.lit (.strVal tk)]) => pure (tk.trim == atom)
    | (``Parser.symbol, #[_nonlit]) => pure false
    | (``Parser.withCache, #[_, p]) => containsAtom p atom
    | _ => if tryWhnf then attempt (← Meta.whnf p) false else pure false
  attempt e true


private def withAtom (cat : Name) (atom : String) : DocM (Array Name) := do
  let env ← getEnv
  let some catContents := (Lean.Parser.parserExtension.getState env).categories.find? cat
    | return #[]
  let kinds := catContents.kinds
  let mut found := #[]
  for (k, _) in kinds do
    if let some d := env.find? k |>.bind (·.value?) then
      if (← containsAtom d atom) then
        found := found.push k
  return found

private def kwImpl (cat : Ident := mkIdent .anonymous) (of : Ident := mkIdent .anonymous)
    (suggest : Bool)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let atom := s.getString
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  let cat' := cat.getId
  let of' ← do
    let x := of.getId
    if x.isAnonymous then pure x else realizeGlobalConstNoOverloadWithInfo of
  let cats ←
    if cat'.isAnonymous then
      pure parsers.categories.toArray
    else
      if let some catImpl := parsers.categories.find? cat' then
        pure #[(cat', catImpl)]
      else throwError m!"Syntax category `{cat'}` not found"

  let mut candidates := #[]
  for (catName, category) in cats do
    if !of'.isAnonymous then
      if category.kinds.contains of' then
        if let some d := env.find? of' |>.bind (·.value?) then
          if (← containsAtom d atom) then
            candidates := candidates.push (catName, of')
    else
      let which ← withAtom catName atom
      candidates := candidates ++ (which.map (catName, ·))

  if h : candidates.size = 0 then
    logErrorAt s m!"No syntax found with atom `{atom}`"
    return .code atom
  else if h : candidates.size > 1 then
    let choices := .andList (candidates.map (fun (c, k) => m!"{.ofConstName k} : {c}")).toList
    let catSuggs := categorySuggestions cat' candidates
    let ofSuggs ← ofSuggestions of' candidates
    let hintText :=
      if catSuggs.isEmpty then
        if ofSuggs.isEmpty then m!""
        else m!"Specify the syntax kind:"
      else
        if ofSuggs.isEmpty then m!"Specify the category:"
        else m!"Specify the category or syntax kind:"

    let range? :=
      match ← getRef with
      | `(inline|role{$name $args*}[$_]) =>
        (mkNullNode (#[name] ++ args)).getRange?
      | _ => none

    let hint ← makeHint hintText (ofSuggs ++ catSuggs)

    logErrorAt s m!"Multiple syntax entries found with atom `{atom}`: {choices}{hint.getD m!""}"
    return .code atom
  else
    let (catName, k) := candidates[0]
    addConstInfo s k
    if of'.isAnonymous && suggest then
      let k' ← unresolveNameGlobalAvoidingLocals k
      if let some h ← makeHint m!"Specify the syntax kind:" #[s!" (of := {k'})"] then
        logInfo h

    return .other {name := ``Data.Atom, val := .mk (Data.Atom.mk k catName)} #[.code atom]
where
  categorySuggestions (c candidates) := Id.run do
    if c.isAnonymous then
      let mut counts : NameMap Nat := {}
      for (cat, _) in candidates do
        counts := counts.alter cat (some <| 1 + ·.getD 0)
      counts := counts.filter fun _ n => n == 1
      let sorted := counts.keys.toArray.qsort (fun x y => x.toString < y.toString)
      return sorted.map (s!" (cat := {·})")
    else return #[]
  ofSuggestions (o candidates) : DocM (Array String):= do
    if o.isAnonymous then
      let sorted := candidates |>.map (·.2) |>.qsort (fun x y => x.toString < y.toString)
      sorted.mapM fun k => do
        let k ← unresolveNameGlobalAvoidingLocals k
        pure s!" (of := {k})"
    else return #[]
  makeHint (hintText) (suggestions : Array String) : DocM (Option MessageData) := do
    let range? :=
      match ← getRef with
      | `(inline|role{$name $args*}[$_]) =>
        (mkNullNode (#[name] ++ args)).getRange?
      | _ => none
    if let some ⟨b, e⟩ := range? then
      let str := (← getFileMap).source.extract b e
      let str := if str.startsWith "kw?" then "kw" ++ str.drop 3 else str
      let stx := Syntax.mkStrLit str (info := .synthetic b e (canonical := true))
      let suggs := suggestions.map (fun (s : String) => {suggestion := str ++ s})
      some <$> MessageData.hint hintText suggs (ref? := some stx)
    else pure none

/--
A reference to a particular syntax kind, via one of its atoms.

It is an error if the syntax kind can't be automatically determined to contain the atom, or if
multiple syntax kinds contain it. If the parser for the syntax kind is sufficiently complex,
detection may fail.

Specifying the category or kind using the named arguments `cat` and `of` can narrow down the
process.

Use `kw?` to receive a suggestion of a specific kind.
-/
--@[builtin_doc_role]
def kw (cat : Ident := mkIdent .anonymous) (of : Ident := mkIdent .anonymous)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) :=
  kwImpl (cat := cat) (of := of) false xs

@[inherit_doc kw /-, builtin_doc_role -/]
def kw? (cat : Ident := mkIdent .anonymous) (of : Ident := mkIdent .anonymous)
    (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) :=
  kwImpl (cat := cat) (of := of) true xs

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
--@[builtin_doc_role]
def syntaxCat (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let x ← parseStrLit rawIdentFn s
  let c := x.getId
  if (← validateCat ⟨x⟩) then
    return .other {name := ``Data.SyntaxCat, val := .mk (Data.SyntaxCat.mk c)} #[.code (toString c)]
  else
    return .code (toString c)

/--
A description of syntax in the provided category.
-/
--@[builtin_doc_role]
def «syntax» (cat : Ident) (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  if (← validateCat cat) then
    let cat := cat.getId
    let stx ← parseStrLit (categoryParserFn cat) s
    introduceAntiquotes stx
    return .other {name := ``Data.Syntax, val := .mk (Data.Syntax.mk cat stx)} #[.code s.getString]
  else
    return .code s.getString

/--
A metavariable to be discussed in the remainder of the docstring.

There are two syntaxes that can be used:
 * `` {given}`x` `` establishes `x`'s type as a metavariable.
 * `` {given}`x : A`` uses `A` as the type for metavariable `x`.
-/
--@[builtin_doc_role]
def given (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let p : ParserFn := whitespace >> nodeFn nullKind (identFn >> optionalFn (symbolFn ":" >> termParser.fn))
  let stx ← parseStrLit p s
  let x := stx[0]
  let ty := stx[1][1]
  let ty' ←
    if !ty.isMissing then elabType ty
    else
      withoutErrToSorry <| Meta.mkFreshExprMVar none
  let lctx ← do
    let lctx ← getLCtx
    let fv ← mkFreshFVarId
    let lctx := lctx.mkLocalDecl fv x.getId ty'
    addTermInfo' x (.fvar fv) (lctx? := some lctx) (isBinder := true) (expectedType? := some ty')
    pure lctx
  modify (fun st => { st with lctx })
  pure .empty

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
Elaborates a sequence of Lean commands as examples.

To make examples self-contained, elaboration ignores the surrouncing section scopes. Modifications
to the environment are preserved during a single documentation comment, and discarded afterwards.

The named argument `name` allows a name to be assigned to the code block; any messages created by
elaboration are saved under this name.

The flags `error` and `warning` indicate that an error or warning is expected in the code.
-/
--@[builtin_doc_code_block]
def lean (name : Option Ident := none) (error warning : flag false) (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let text ← getFileMap
  let env ← getEnv
  let p := andthenFn whitespace (categoryParserFnImpl `command)
  -- TODO fallback for non-original syntax
  let pos := code.raw.getPos? true |>.get!
  let endPos := code.raw.getTailPos? true |>.get!
  let endPos := if endPos ≤ text.source.endPos then endPos else text.source.endPos
  let ictx :=
    mkInputContext text.source (← getFileName)
      (endPos := endPos) (endPos_valid := by simp only [endPos]; split <;> simp [*])
  let cctx : Command.Context := {fileName := ← getFileName, fileMap := text, snap? := none, cancelTk? := none}
  let scopes := (← get).scopes
  let mut cmdState : Command.State := { env, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes }
  let mut pstate : Parser.ModuleParserState := {pos := pos, recovering := false}
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
  -- TODO Nice highlighted code
  let mut output := #[]
  for msg in cmdState.messages.toArray do
    let b := text.ofPosition msg.pos
    let e := msg.endPos |>.map text.ofPosition |>.getD (text.source.next b)
    let msgStr := text.source.extract b e
    let msgStx := Syntax.mkStrLit msgStr (info := .synthetic b e (canonical := true))
    unless msg.isSilent do
      if name.isSome then output := output.push (msg.severity, ← msg.data.toString)
      if msg.severity == .error && !error then
        let hint ← flagHint m!"The `+error` flag indicates that errors are expected:" #[" +error"]
        logErrorAt msgStx m!"Unexpected error:{indentD msg.data}{hint.getD m!""}"
      if msg.severity == .warning && !warning then
        let hint ← flagHint m!"The `+error` flag indicates that warnings are expected:" #[" +warning"]
        logErrorAt msgStx m!"Unexpected warning:{indentD msg.data}{hint.getD m!""}"
      else
        withRef msgStx <| log msg.data (severity := .information) (isSilent := true)
    if let some x := name then
      modifyEnv (leanOutputExt.modifyState · (·.insert x.getId output))
  pure (Block.code (toString (mkNullNode cmds)))
where
  runCommand (act : Command.CommandElabM Unit) (stx : Syntax)
      (cctx : Command.Context) (cmdState : Command.State) :
      DocM Command.State := do
    let (output, cmdState) ←
      match (← liftM <| IO.FS.withIsolatedStreams <| EIO.toIO' <| (act.run cctx).run cmdState) with
      | (output, .error e) => Lean.logError e.toMessageData; pure (output, cmdState)
      | (output, .ok ((), cmdState)) => pure (output, cmdState)

    if output.trim.isEmpty then return cmdState

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
      let str := (← getFileMap).source.extract b e
      let str := if str.startsWith "kw?" then "kw" ++ str.drop 3 else str
      let stx := Syntax.mkStrLit str (info := .synthetic b e (canonical := true))
      let suggs := suggestions.map (fun (s : String) => {suggestion := str ++ s})
      some <$> MessageData.hint hintText suggs (ref? := some stx)
    else pure none

/--
Displays output from a named Lean code block.
-/
--@[builtin_doc_code_block]
def output (name : Ident) (severity : Option (WithSyntax MessageSeverity) := none) (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let allOut := leanOutputExt.getState (← getEnv)
  let some outs := allOut.find? name.getId
    | let possible := allOut.keysArray.map ({suggestion := ·.toString})
      let h ← MessageData.hint m!"Use one of the named blocks:" possible
      logErrorAt name m!"Output from block `{name.getId}` not found{h}"
      return .code code.getString
  let codeStr := code.getString
  for (sev, out) in outs do
    if out.trim == codeStr.trim then
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
  let h ← m!"Use one of the outputs:".hint (outs.map (withNl ·.2)) (ref? := code)
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
Treats the provided term as Lean syntax in the documentation's scope.
-/
--@[builtin_doc_role lean]
def leanTerm (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let p : ParserFn := whitespace >> termParser.fn
  let stx ← parseStrLit p s
  discard <| withoutErrToSorry <| elabTerm stx none
  pure (.code s.getString)

/--
Opens a namespace in the remainder of the documentation comment.

The `+scoped` flag causes scoped instances and attributes to be activated, but no identifiers are
brought into scope. The named argument `only`, which can be repeated, specifies a subset of names to
bring into scope from the namespace.
-/
--@[builtin_doc_command]
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
--@[builtin_doc_command]
def «set_option» (option : Ident) (value : DataValue) : DocM (Block ElabInline ElabBlock) := do
  addCompletionInfo <| CompletionInfo.option option
  let optionName := option.getId
  let decl ← withRef option <| getOptionDecl optionName
  pushInfoLeaf <| .ofOptionInfo { stx := option, optionName, declName := decl.declName }
  validateOptionValue optionName decl value
  let o ← getOptions
  modify fun s => { s with options := o.insert optionName value }
  return .empty

/--
Constructs a link to the Lean langauge reference. Two positional arguments are expected:
 * `domain` should be one of the valid domains, such as `section`.
 * `name` should be the content's canonical name in the domain.
-/
--@[builtin_doc_role]
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
Suggests the `name` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
def suggestName (code : StrLit) : DocM (Array CodeSuggestion) := do
  let stx ← parseStrLit identFn code
  try
    discard <| realizeGlobalConstNoOverload stx
    return #[.mk ``name none none]
  catch
    | _ =>
    if let some (_, []) := (← resolveLocalName stx.getId) then
      return #[.mk ``name none none]
  return #[]

/--
Suggests the `lean` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
def suggestLean (code : StrLit) : DocM (Array CodeSuggestion) := do
  let p : ParserFn := whitespace >> termParser.fn
  try
    let stx ← parseStrLit p code
    discard <| withoutErrToSorry <| elabTerm stx none
    return #[.mk ``lean none none]
  catch | _ => return #[]

/--
Suggests the `tactic` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
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

open Lean.Parser.Term in
/--
Suggests the `attr` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
def suggestAttr (code : StrLit) : DocM (Array CodeSuggestion) := do
  try
    let stx ← parseStrLit attributes.fn code
    let `(attributes|@[$_attrs,*]) := stx
      | return #[]
    return #[.mk ``attr none none]
  catch
    | _ => pure ()
  try
    discard <| parseStrLit attrParser.fn code
    return #[.mk ``attr none none]
  catch
    | _ => pure ()
  return #[]

open Lean.Parser.Command in
/--
Suggests the `option` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
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
Suggests the `kw` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
def suggestKw (code : StrLit) : DocM (Array CodeSuggestion) := do
  let atom := code.getString
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  let cats := parsers.categories.toArray

  let mut candidates := #[]
  for (catName, _) in cats do
    let which ← withAtom catName atom
    candidates := candidates ++ (which.map (catName, ·))

  candidates.mapM fun (cat, of) => do
    return .mk ``kw (some s!"(of := {of})") (some s!"(in `{cat}`)")

/--
Suggests the `syntaxCat` role, if applicable.
-/
--@[builtin_doc_code_suggestions]
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
--@[builtin_doc_code_suggestions]
def suggestSyntax (code : StrLit) : DocM (Array CodeSuggestion) := do
  let env ← getEnv
  let parsers := Lean.Parser.parserExtension.getState env
  let cats := parsers.categories.toArray

  let mut candidates := #[]
  for (catName, _) in cats do
    try
      discard <| parseStrLit (whitespace >> (categoryParser catName 0).fn) code
      candidates := candidates.push catName
    catch | _ => pure ()

  candidates.mapM fun cat => do
    return .mk ``«syntax» (some s!"{cat}") none
