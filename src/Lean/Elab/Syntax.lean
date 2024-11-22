/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Command
import Lean.Parser.Syntax
import Lean.Elab.Util

namespace Lean.Elab.Term
/--
Expand `optional «precedence»` where
 «precedence» := leading_parser " : " >> precedenceParser -/
def expandOptPrecedence (stx : Syntax) : MacroM (Option Nat) :=
  if stx.isNone then
    return none
  else
    return some (← evalPrec stx[0][1])

private def mkParserSeq (ds : Array (Term × Nat)) : TermElabM (Term × Nat) := do
  if h₀ : ds.size = 0 then
    throwUnsupportedSyntax
  else if h₁ : ds.size = 1 then
    pure ds[0]
  else
    let mut (r, stackSum) := ds[0]
    for (d, stackSz) in ds[1:ds.size] do
      r ← `(ParserDescr.binary `andthen $r $d)
      stackSum := stackSum + stackSz
    return (r, stackSum)

structure ToParserDescrContext where
  catName  : Name
  first    : Bool
  leftRec  : Bool -- true iff left recursion is allowed
  /-- See comment at `Parser.ParserCategory`. -/
  behavior : Parser.LeadingIdentBehavior

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateRefT (Option Nat) TermElabM)
abbrev ToParserDescr := ToParserDescrM (Term × Nat)
private def markAsTrailingParser (lhsPrec : Nat) : ToParserDescrM Unit := set (some lhsPrec)

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with first := false }) x

def ensureUnaryOutput (x : Term × Nat) : Term :=
  let (stx, stackSz) := x
  if stackSz != 1 then
    Unhygienic.run ``(ParserDescr.unary $(quote `group) $stx)
  else
    stx

@[inline] private def withNestedParser (x : ToParserDescr) : ToParserDescr := do
  withReader (fun ctx => { ctx with leftRec := false, first := false }) x

/-- (Try to) add a term info for the category `catName` at `ref`. -/
def addCategoryInfo (ref : Syntax) (catName : Name) : TermElabM Unit := do
  let declName := ``Lean.Parser.Category ++ catName
  if (← getEnv).contains declName then
    addTermInfo' ref (Lean.mkConst declName)

/-- (Try to) add a term info for the alias with info `info` at `ref`. -/
def addAliasInfo (ref : Syntax) (info : Parser.ParserAliasInfo) : TermElabM Unit := do
  if (← getInfoState).enabled then
    if (← getEnv).contains info.declName then
      addTermInfo' ref (Lean.mkConst info.declName)

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
  let ctx ← read
  unless ctx.first && stx.getKind == ``Lean.Parser.Syntax.cat do
    return false
  let cat := stx[0].getId.eraseMacroScopes
  unless cat == ctx.catName do
    return false
  addCategoryInfo stx cat
  let prec? ← liftMacroM <| expandOptPrecedence stx[1]
  unless ctx.leftRec do
    throwErrorAt stx[3] "invalid occurrence of '{cat}', parser algorithm does not allow this form of left recursion"
  markAsTrailingParser (prec?.getD 0)
  return true

def elabParserName? (stx : Syntax.Ident) : TermElabM (Option Parser.ParserResolution) := do
  match ← Parser.resolveParserName stx with
  | [n@(.category cat)] =>
    addCategoryInfo stx cat
    return n
  | [n@(.parser parser _)] =>
    addTermInfo' stx (Lean.mkConst parser)
    return n
  | [n@(.alias _)] =>
    return n
  | _::_::_ => throwErrorAt stx "ambiguous parser {stx}"
  | [] => return none

def elabParserName (stx : Syntax.Ident) : TermElabM Parser.ParserResolution := do
  match ← elabParserName? stx with
  | some n => return n
  | none => throwErrorAt stx "unknown parser {stx}"

open TSyntax.Compat in
/--
  Given a `stx` of category `syntax`, return a `(newStx, lhsPrec?)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `lhsPrec?.isSome`, and `ParserDescr` otherwise. -/
partial def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Term × Option Nat) := do
  let env ← getEnv
  let behavior := Parser.leadingIdentBehavior env catName
  let ((newStx, _), lhsPrec?) ← (process stx { catName := catName, first := true, leftRec := true, behavior := behavior }).run none
  return (newStx, lhsPrec?)
where
  process (stx : Syntax) : ToParserDescr := withRef stx do
    let kind := stx.getKind
    if kind == nullKind then
      processSeq stx
    else if kind == choiceKind then
      process stx[0]
    else if kind == ``Lean.Parser.Syntax.paren then
      process stx[1]
    else if kind == ``Lean.Parser.Syntax.cat then
      processNullaryOrCat stx
    else if kind == ``Lean.Parser.Syntax.unary then
      processAlias stx[0] #[stx[2]]
    else if kind == ``Lean.Parser.Syntax.binary then
      processAlias stx[0] #[stx[2], stx[4]]
    else if kind == ``Lean.Parser.Syntax.sepBy then
      processSepBy stx
    else if kind == ``Lean.Parser.Syntax.sepBy1 then
      processSepBy1 stx
    else if kind == ``Lean.Parser.Syntax.atom then
      processAtom stx
    else if kind == ``Lean.Parser.Syntax.nonReserved then
      processNonReserved stx
    else
      let stxNew? ← liftM (liftMacroM (expandMacro? stx) : TermElabM _)
      match stxNew? with
      | some stxNew => process stxNew
      | none => throwErrorAt stx "unexpected syntax kind of category `syntax`: {kind}"

  /-- Sequence (aka NullNode) -/
  processSeq (stx : Syntax) := do
    let args := stx.getArgs
    if (← checkLeftRec stx[0]) then
      if args.size == 1 then throwErrorAt stx "invalid atomic left recursive syntax"
      let args := args.eraseIdxIfInBounds 0
      let args ← args.mapM fun arg => withNestedParser do process arg
      mkParserSeq args
    else
      let args ← args.mapIdxM fun i arg => withReader (fun ctx => { ctx with first := ctx.first && i == 0 }) do process arg
      mkParserSeq args

  ensureNoPrec (stx : Syntax) :=
    unless stx[1].isNone do
      throwErrorAt stx[1] "unexpected precedence"

  processParserCategory (stx : Syntax) := do
    let catName := stx[0].getId.eraseMacroScopes
    if (← read).first && catName == (← read).catName then
      throwErrorAt stx "invalid atomic left recursive syntax"
    let prec? ← liftMacroM <| expandOptPrecedence stx[1]
    let prec := prec?.getD 0
    return (← `(ParserDescr.cat $(quote catName) $(quote prec)), 1)

  processAlias (id : Syntax) (args : Array Syntax) := do
    let aliasName := id.getId.eraseMacroScopes
    let info ← Parser.getParserAliasInfo aliasName
    addAliasInfo id info
    let args' ← args.mapM (withNestedParser ∘ process)
    -- wrap lone string literals in `<|>` in dedicated node (#1275)
    let args' ← if aliasName == `orelse then  -- TODO: generalize if necessary
      args.zip args' |>.mapM fun (arg, arg') => do
        let mut #[arg] := arg.getArgs | return arg'
        let sym ← match arg with
          | `(stx| &$sym) => pure sym
          | `(stx| $sym:str) => pure sym
          | _ => return arg'
        let sym := sym.getString
        return (← `(ParserDescr.nodeWithAntiquot $(quote sym) $(quote (Name.str `token sym)) $(arg'.1)), 1)
    else
      pure args'
    let (args', stackSz) := if let some stackSz := info.stackSz? then
      if !info.autoGroupArgs then
        (args'.map (·.1), stackSz)
      else
        (args'.map ensureUnaryOutput, stackSz)
    else
      let (args', stackSzs) := args'.unzip
      (args', stackSzs.foldl (· + ·) 0)
    let stx ← match args' with
      | #[]       => Parser.ensureConstantParserAlias aliasName; ``(ParserDescr.const $(quote aliasName))
      | #[p1]     => Parser.ensureUnaryParserAlias aliasName; ``(ParserDescr.unary $(quote aliasName) $p1)
      | #[p1, p2] => Parser.ensureBinaryParserAlias aliasName; ``(ParserDescr.binary $(quote aliasName) $p1 $p2)
      | _         => unreachable!
    return (stx, stackSz)

  processNullaryOrCat (stx : Syntax) := do
    let ident := stx[0]
    let id := ident.getId.eraseMacroScopes
    match (← elabParserName? ident) with
    | some (.parser c (isDescr := true)) =>
      ensureNoPrec stx
      -- `syntax _ :=` at least enforces this
      let stackSz := 1
      return (mkIdentFrom stx c, stackSz)
    | some (.parser c (isDescr := false)) =>
      if (← Parser.getParserAliasInfo id).declName == c then
        -- prefer parser alias over base declaration because it has more metadata, #2249
        ensureNoPrec stx
        return (← processAlias ident #[])
      ensureNoPrec stx
      -- as usual, we assume that people using `Parser` know what they are doing
      let stackSz := 1
      return (← `(ParserDescr.parser $(quote c)), stackSz)
    | some (.category _) =>
      processParserCategory stx
    | some (.alias _) =>
      ensureNoPrec stx
      processAlias ident #[]
    | none => throwError "unknown parser declaration/category/alias '{id}'"

  processSepBy (stx : Syntax) := do
    let p ← ensureUnaryOutput <$> withNestedParser do process stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else ensureUnaryOutput <$> withNestedParser do process stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    return (← `((with_annotate_term $(stx[0]) @ParserDescr.sepBy) $p $sep $psep $(quote allowTrailingSep)), 1)

  processSepBy1 (stx : Syntax) := do
    let p ← ensureUnaryOutput <$> withNestedParser do process stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else ensureUnaryOutput <$> withNestedParser do process stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    return (← `((with_annotate_term $(stx[0]) @ParserDescr.sepBy1) $p $sep $psep $(quote allowTrailingSep)), 1)

  isValidAtom (s : String) : Bool :=
    -- Pretty-printing instructions shouldn't affect validity
    let s := s.trim
    !s.isEmpty &&
    (s.front != '\'' || "''".isPrefixOf s) &&
    s.front != '\"' &&
    !(isIdBeginEscape s.front) &&
    !(s.front == '`' && (s.endPos == ⟨1⟩ || isIdFirst (s.get ⟨1⟩) || isIdBeginEscape (s.get ⟨1⟩))) &&
    !s.front.isDigit &&
    !(s.any Char.isWhitespace)

  processAtom (stx : Syntax) := do
    match stx[0].isStrLit? with
    | some atom =>
      unless isValidAtom atom do
        throwErrorAt stx "invalid atom"
      /- For syntax categories where initialized with `LeadingIdentBehavior` different from default (e.g., `tactic`), we automatically mark
         the first symbol as nonReserved. -/
      if (← read).behavior != Parser.LeadingIdentBehavior.default && (← read).first then
        return (← `(ParserDescr.nonReservedSymbol $(quote atom) false), 1)
      else
        return (← `(ParserDescr.symbol $(quote atom)), 1)
    | none => throwUnsupportedSyntax

  processNonReserved (stx : Syntax) := do
    let some atom := stx[1].isStrLit? | throwUnsupportedSyntax
    return (← `((with_annotate_term $(stx[0]) @ParserDescr.nonReservedSymbol) $(quote atom) false), 1)


end Term

namespace Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

private def declareSyntaxCatQuotParser (catName : Name) : CommandElabM Unit := do
  if let .str _ suffix := catName then
    let quotSymbol := "`(" ++ suffix ++ "| "
    let name := catName ++ `quot
    let cmd ← `(
      @[term_parser] def $(mkIdent name) : Lean.ParserDescr :=
        Lean.ParserDescr.node `Lean.Parser.Term.quot $(quote Lean.Parser.maxPrec)
          (Lean.ParserDescr.node $(quote name) $(quote Lean.Parser.maxPrec)
            (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol $(quote quotSymbol))
              (Lean.ParserDescr.binary `andthen
                (Lean.ParserDescr.cat $(quote catName) 0)
                (Lean.ParserDescr.symbol ")")))))
    elabCommand cmd

@[builtin_command_elab syntaxCat] def elabDeclareSyntaxCat : CommandElab := fun stx => do
  let docString? := stx[0].getOptional?.map fun stx => ⟨stx⟩
  let catName    := stx[2].getId
  let catBehavior :=
    if stx[3].isNone then
      Parser.LeadingIdentBehavior.default
    else if stx[3][3].getKind == ``Parser.Command.catBehaviorBoth then
      Parser.LeadingIdentBehavior.both
    else
      Parser.LeadingIdentBehavior.symbol
  let attrName := catName.appendAfter "_parser"
  let catDeclName := ``Lean.Parser.Category ++ catName
  setEnv (← Parser.registerParserCategory (← getEnv) attrName catName catBehavior catDeclName)
  let cmd ← `($[$docString?]? def $(mkIdentFrom stx[2] (`_root_ ++ catDeclName) (canonical := true)) : Lean.Parser.Category := {})
  declareSyntaxCatQuotParser catName
  elabCommand cmd

/--
  Auxiliary function for creating declaration names from parser descriptions.
  Example:
  Given
  ```
  syntax term "+" term : term
  syntax "[" sepBy(term, ", ") "]"  : term
  ```
  It generates the names `term_+_` and `term[_,]`
-/
partial def mkNameFromParserSyntax (catName : Name) (stx : Syntax) : MacroM Name := do
  mkUnusedBaseName <| Name.mkSimple <| appendCatName <| visit stx ""
where
  visit (stx : Syntax) (acc : String) : String :=
    match stx.isStrLit? with
    | some val => acc ++ (val.trim.map fun c => if c.isWhitespace then '_' else c).capitalize
    | none =>
      match stx with
      | Syntax.node _ k args =>
        if k == ``Lean.Parser.Syntax.cat then
          acc ++ "_"
        else
          args.foldl (init := acc) fun acc arg => visit arg acc
      | Syntax.ident ..    => acc
      | Syntax.atom ..     => acc
      | Syntax.missing     => acc

  appendCatName (str : String) :=
    match catName with
    | .str _ s => s ++ str
    | _ => str

/-- We assume a new syntax can be treated as an atom when it starts and ends with a token.
   Here are examples of atom-like syntax.
   ```
   syntax "(" term ")" : term
   syntax "[" (sepBy term ",") "]" : term
   syntax "foo" : term
   ```
 -/
private partial def isAtomLikeSyntax (stx : Syntax) : Bool :=
  let kind := stx.getKind
  if kind == nullKind then
    isAtomLikeSyntax stx[0] && isAtomLikeSyntax stx[stx.getNumArgs - 1]
  else if kind == choiceKind then
    isAtomLikeSyntax stx[0] -- see toParserDescr
  else if kind == ``Lean.Parser.Syntax.paren then
    isAtomLikeSyntax stx[1]
  else
    kind == ``Lean.Parser.Syntax.atom

def resolveSyntaxKind (k : Name) : CommandElabM Name := do
  checkSyntaxNodeKindAtNamespaces k (← getCurrNamespace)
  <|>
  throwError "invalid syntax node kind '{k}'"

def isLocalAttrKind (attrKind : Syntax) : Bool :=
  match attrKind with
  | `(Parser.Term.attrKind| local) => true
  | _ => false

/--
Add macro scope to `name` if it does not already have them, and `attrKind` is `local`.
-/
def addMacroScopeIfLocal [MonadQuotation m] [Monad m] (name : Name) (attrKind : Syntax) : m Name := do
  if isLocalAttrKind attrKind && !name.hasMacroScopes then
    MonadQuotation.addMacroScope name
  else
    return name

@[builtin_command_elab «syntax»] def elabSyntax : CommandElab := fun stx => do
  let `($[$doc?:docComment]? $[ @[ $attrInstances:attrInstance,* ] ]? $attrKind:attrKind
      syntax%$tk $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $[$ps:stx]* : $catStx) := stx
    | throwUnsupportedSyntax
  let cat := catStx.getId.eraseMacroScopes
  unless (Parser.isParserCategory (← getEnv) cat) do
    throwErrorAt catStx "unknown category '{cat}'"
  liftTermElabM <| Term.addCategoryInfo catStx cat
  let syntaxParser := mkNullNode ps
  -- If the user did not provide an explicit precedence, we assign `maxPrec` to atom-like syntax and `leadPrec` otherwise.
  let precDefault  := if isAtomLikeSyntax syntaxParser then Parser.maxPrec else Parser.leadPrec
  let prec ← match prec? with
    | some prec => liftMacroM <| evalPrec prec
    | none      => pure precDefault
  let name ← match name? with
    | some name => pure name.getId
    | none => addMacroScopeIfLocal (← liftMacroM <| mkNameFromParserSyntax cat syntaxParser) attrKind
  let prio ← liftMacroM <| evalOptPrio prio?
  let idRef := (name?.map (·.raw)).getD tk
  let stxNodeKind := (← getCurrNamespace) ++ name
  let catParserId := mkIdentFrom idRef (cat.appendAfter "_parser")
  let (val, lhsPrec?) ← runTermElabM fun _ => Term.toParserDescr syntaxParser cat
  let declName := name?.getD (mkIdentFrom idRef name (canonical := true))
  let attrInstance ← `(attrInstance| $attrKind:attrKind $catParserId:ident $(quote prio):num)
  let attrInstances := attrInstances.getD { elemsAndSeps := #[] }
  let attrInstances := attrInstances.push attrInstance
  let d ← if let some lhsPrec := lhsPrec? then
    `($[$doc?:docComment]? @[$attrInstances,*] def $declName:ident : Lean.TrailingParserDescr :=
        ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $(quote lhsPrec) $val)
  else
    `($[$doc?:docComment]? @[$attrInstances,*] def $declName:ident : Lean.ParserDescr :=
        ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
  trace `Elab fun _ => d
  withMacroExpansion stx d <| elabCommand d

@[builtin_command_elab «syntaxAbbrev»] def elabSyntaxAbbrev : CommandElab := fun stx => do
  let `($[$doc?:docComment]? syntax $declName:ident := $[$ps:stx]*) ← pure stx | throwUnsupportedSyntax
  -- TODO: nonatomic names
  let (val, _) ← runTermElabM fun _ => Term.toParserDescr (mkNullNode ps) Name.anonymous
  let stxNodeKind := (← getCurrNamespace) ++ declName.getId
  let stx' ← `($[$doc?:docComment]? def $declName:ident : Lean.ParserDescr := ParserDescr.nodeWithAntiquot $(quote (toString declName.getId)) $(quote stxNodeKind) $val)
  withMacroExpansion stx stx' <| elabCommand stx'

def checkRuleKind (given expected : SyntaxNodeKind) : Bool :=
  given == expected || given == expected ++ `antiquot

def inferMacroRulesAltKind : TSyntax ``matchAlt → CommandElabM SyntaxNodeKind
  | `(matchAltExpr| | $pat:term => $_) => do
    if !pat.raw.isQuot then
      throwUnsupportedSyntax
    let quoted := getQuotContent pat
    pure quoted.getKind
  | _ => throwUnsupportedSyntax

/--
Infer syntax kind `k` from first pattern, put alternatives of same kind into new `macro/elab_rules (kind := k)` via `mkCmd (some k)`,
leave remaining alternatives (via `mkCmd none`) to be recursively expanded. -/
def expandNoKindMacroRulesAux (alts : Array (TSyntax ``matchAlt)) (cmdName : String) (mkCmd : Option Name → Array (TSyntax ``matchAlt) → CommandElabM Command) : CommandElabM Command := do
  let mut k ← inferMacroRulesAltKind alts[0]!
  if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
  if k == choiceKind then
    throwErrorAt alts[0]!
      "invalid {cmdName} alternative, multiple interpretations for pattern (solution: specify node kind using `{cmdName} (kind := ...) ...`)"
  else
    let altsK    ← alts.filterM fun alt => return checkRuleKind (← inferMacroRulesAltKind alt) k
    let altsNotK ← alts.filterM fun alt => return !checkRuleKind (← inferMacroRulesAltKind alt) k
    if altsNotK.isEmpty then
      mkCmd k altsK
    else
      `($(← mkCmd k altsK):command $(← mkCmd none altsNotK))

def strLitToPattern (stx: Syntax) : MacroM Syntax :=
  match stx.isStrLit? with
  | some str => return mkAtomFrom stx str
  | none     => Macro.throwUnsupported

builtin_initialize
  registerTraceClass `Elab.defaultInstance

end Lean.Elab.Command
