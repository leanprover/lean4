/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Parser.Syntax

namespace Lean.Elab.Term
/-
Expand `optional «precedence»` where
 «precedence» := leading_parser " : " >> precedenceParser -/
def expandOptPrecedence (stx : Syntax) : MacroM (Option Nat) :=
  if stx.isNone then
    return none
  else
    return some (← evalPrec stx[0][1])

private def mkParserSeq (ds : Array Syntax) : TermElabM Syntax := do
  if ds.size == 0 then
    throwUnsupportedSyntax
  else if ds.size == 1 then
    pure ds[0]
  else
    let mut r := ds[0]
    for d in ds[1:ds.size] do
      r ← `(ParserDescr.binary `andthen $r $d)
    return r

structure ToParserDescrContext where
  catName  : Name
  first    : Bool
  leftRec  : Bool -- true iff left recursion is allowed
  /- See comment at `Parser.ParserCategory`. -/
  behavior : Parser.LeadingIdentBehavior

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateRefT (Option Nat) TermElabM)
private def markAsTrailingParser (lhsPrec : Nat) : ToParserDescrM Unit := set (some lhsPrec)

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with first := false }) x

@[inline] private def withNestedParser {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with leftRec := false, first := false }) x

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
  let ctx ← read
  unless ctx.first && stx.getKind == `Lean.Parser.Syntax.cat do
    return false
  let cat := stx[0].getId.eraseMacroScopes
  unless cat == ctx.catName do
    return false
  let prec? ← liftMacroM <| expandOptPrecedence stx[1]
  unless ctx.leftRec do
    throwErrorAt stx[3] "invalid occurrence of '{cat}', parser algorithm does not allow this form of left recursion"
  markAsTrailingParser (prec?.getD 0)
  return true

/--
  Given a `stx` of category `syntax`, return a pair `(newStx, lhsPrec?)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `lhsPrec?.isSome`, and `ParserDescr` otherwise. -/
partial def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Syntax × Option Nat) := do
  let env ← getEnv
  let behavior := Parser.leadingIdentBehavior env catName
  (process stx { catName := catName, first := true, leftRec := true, behavior := behavior }).run none
where
  process (stx : Syntax) : ToParserDescrM Syntax := withRef stx do
    let kind := stx.getKind
    if kind == nullKind then
      processSeq stx
    else if kind == choiceKind then
      process stx[0]
    else if kind == `Lean.Parser.Syntax.paren then
      process stx[1]
    else if kind == `Lean.Parser.Syntax.cat then
      processNullaryOrCat stx
    else if kind == `Lean.Parser.Syntax.unary then
      processUnary stx
    else if kind == `Lean.Parser.Syntax.binary then
      processBinary stx
    else if kind == `Lean.Parser.Syntax.sepBy then
      processSepBy stx
    else if kind == `Lean.Parser.Syntax.sepBy1 then
      processSepBy1 stx
    else if kind == `Lean.Parser.Syntax.atom then
      processAtom stx
    else if kind == `Lean.Parser.Syntax.nonReserved then
      processNonReserved stx
    else
      let stxNew? ← liftM (liftMacroM (expandMacro? stx) : TermElabM _)
      match stxNew? with
      | some stxNew => process stxNew
      | none => throwErrorAt stx "unexpected syntax kind of category `syntax`: {kind}"

  /- Sequence (aka NullNode) -/
  processSeq (stx : Syntax) := do
    let args := stx.getArgs
    if (← checkLeftRec stx[0]) then
      if args.size == 1 then throwErrorAt stx "invalid atomic left recursive syntax"
      let args := args.eraseIdx 0
      let args ← args.mapM fun arg => withNestedParser do process arg
      mkParserSeq args
    else
      let args ← args.mapIdxM fun i arg => withReader (fun ctx => { ctx with first := ctx.first && i.val == 0 }) do process arg
      mkParserSeq args

  /- Resolve the given parser name and return a list of candidates.
     Each candidate is a pair `(resolvedParserName, isDescr)`.
     `isDescr == true` if the type of `resolvedParserName` is a `ParserDescr`. -/
  resolveParserName (parserName : Name) : ToParserDescrM (List (Name × Bool)) := do
    try
      let candidates ← resolveGlobalConstWithInfos (← getRef) parserName
      /- Convert `candidates` in a list of pairs `(c, isDescr)`, where `c` is the parser name,
         and `isDescr` is true iff `c` has type `Lean.ParserDescr` or `Lean.TrailingParser` -/
      candidates.filterMap fun c =>
         match (← getEnv).find? c with
         | none      => none
         | some info =>
           match info.type with
          | Expr.const `Lean.Parser.TrailingParser _ _ => (c, false)
          | Expr.const `Lean.Parser.Parser _ _         => (c, false)
          | Expr.const `Lean.ParserDescr _ _           => (c, true)
          | Expr.const `Lean.TrailingParserDescr _ _   => (c, true)
          | _                                          => none
    catch _ => return []

  ensureNoPrec (stx : Syntax) :=
    unless stx[1].isNone do
      throwErrorAt stx[1] "unexpected precedence"

  processParserCategory (stx : Syntax) := do
    let catName := stx[0].getId.eraseMacroScopes
    if (← read).first && catName == (← read).catName then
      throwErrorAt stx "invalid atomic left recursive syntax"
    let prec? ← liftMacroM <| expandOptPrecedence stx[1]
    let prec := prec?.getD 0
    `(ParserDescr.cat $(quote catName) $(quote prec))

  processNullaryOrCat (stx : Syntax) := do
    let id := stx[0].getId.eraseMacroScopes
    match (← withRef stx[0] <| resolveParserName id) with
    | [(c, true)]      => ensureNoPrec stx; return mkIdentFrom stx c
    | [(c, false)]     => ensureNoPrec stx; `(ParserDescr.parser $(quote c))
    | cs@(_ :: _ :: _) => throwError "ambiguous parser declaration {cs.map (·.1)}"
    | [] =>
      if Parser.isParserCategory (← getEnv) id then
        processParserCategory stx
      else if (← Parser.isParserAlias id) then
        ensureNoPrec stx
        Parser.ensureConstantParserAlias id
        `(ParserDescr.const $(quote id))
      else
        throwError "unknown parser declaration/category/alias '{id}'"

  processUnary (stx : Syntax) := do
    let aliasName := (stx[0].getId).eraseMacroScopes
    Parser.ensureUnaryParserAlias aliasName
    let d ← withNestedParser do process stx[2]
    `(ParserDescr.unary $(quote aliasName) $d)

  processBinary (stx : Syntax) := do
    let aliasName := (stx[0].getId).eraseMacroScopes
    Parser.ensureBinaryParserAlias aliasName
    let d₁ ← withNestedParser do process stx[2]
    let d₂ ← withNestedParser do process stx[4]
    `(ParserDescr.binary $(quote aliasName) $d₁ $d₂)

  processSepBy (stx : Syntax) := do
    let p ← withNestedParser $ process stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else process stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    `(ParserDescr.sepBy $p $sep $psep $(quote allowTrailingSep))

  processSepBy1 (stx : Syntax) := do
    let p ← withNestedParser do process stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else process stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    `(ParserDescr.sepBy1 $p $sep $psep $(quote allowTrailingSep))

  processAtom (stx : Syntax) := do
    match stx[0].isStrLit? with
    | some atom =>
      /- For syntax categories where initialized with `LeadingIdentBehavior` different from default (e.g., `tactic`), we automatically mark
         the first symbol as nonReserved. -/
      if (← read).behavior != Parser.LeadingIdentBehavior.default && (← read).first then
        `(ParserDescr.nonReservedSymbol $(quote atom) false)
      else
        `(ParserDescr.symbol $(quote atom))
    | none => throwUnsupportedSyntax

  processNonReserved (stx : Syntax) := do
    match stx[1].isStrLit? with
    | some atom => `(ParserDescr.nonReservedSymbol $(quote atom) false)
    | none      => throwUnsupportedSyntax


end Term

namespace Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

private def getCatSuffix (catName : Name) : String :=
  match catName with
  | Name.str _ s _ => s
  | _              => unreachable!

private def declareSyntaxCatQuotParser (catName : Name) : CommandElabM Unit := do
  let quotSymbol := "`(" ++ getCatSuffix catName ++ "|"
  let name := catName ++ `quot
  -- TODO(Sebastian): this might confuse the pretty printer, but it lets us reuse the elaborator
  let kind := ``Lean.Parser.Term.quot
  let cmd ← `(
    @[termParser] def $(mkIdent name) : Lean.ParserDescr :=
      Lean.ParserDescr.node $(quote kind) $(quote Lean.Parser.maxPrec)
        (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol $(quote quotSymbol))
          (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.cat $(quote catName) 0) (Lean.ParserDescr.symbol ")"))))
  elabCommand cmd

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab := fun stx => do
  let catName  := stx[1].getId
  let attrName := catName.appendAfter "Parser"
  let env ← getEnv
  let env ← liftIO $ Parser.registerParserCategory env attrName catName
  setEnv env
  declareSyntaxCatQuotParser catName

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
partial def mkNameFromParserSyntax (catName : Name) (stx : Syntax) : CommandElabM Name :=
  mkUnusedBaseName <| Name.mkSimple <| appendCatName <| visit stx ""
where
  visit (stx : Syntax) (acc : String) : String :=
    match stx.isStrLit? with
    | some val => acc ++ (val.trim.map fun c => if c.isWhitespace then '_' else c).capitalize
    | none =>
      match stx with
      | Syntax.node k args =>
        if k == `Lean.Parser.Syntax.cat then
          acc ++ "_"
        else
          args.foldl (init := acc) fun acc arg => visit arg acc
      | Syntax.ident ..    => acc
      | Syntax.atom ..     => acc
      | Syntax.missing     => acc

  appendCatName (str : String) :=
    match catName with
    | Name.str _ s _ => s ++ str
    | _ => str

/- We assume a new syntax can be treated as an atom when it starts and ends with a token.
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
  else if kind == `Lean.Parser.Syntax.paren then
    isAtomLikeSyntax stx[1]
  else
    kind == `Lean.Parser.Syntax.atom

@[builtinCommandElab «syntax»] def elabSyntax : CommandElab := fun stx => do
  let `($attrKind:attrKind syntax $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $[$ps:stx]* : $catStx) ← pure stx
    | throwUnsupportedSyntax
  let cat := catStx.getId.eraseMacroScopes
  unless (Parser.isParserCategory (← getEnv) cat) do
    throwErrorAt catStx "unknown category '{cat}'"
  let syntaxParser := mkNullNode ps
  -- If the user did not provide an explicit precedence, we assign `maxPrec` to atom-like syntax and `leadPrec` otherwise.
  let precDefault  := if isAtomLikeSyntax syntaxParser then Parser.maxPrec else Parser.leadPrec
  let prec ← match prec? with
    | some prec => liftMacroM <| evalPrec prec
    | none      => precDefault
  let name ← match name? with
    | some name => pure name.getId
    | none => mkNameFromParserSyntax cat syntaxParser
  let prio ← liftMacroM <| evalOptPrio prio?
  let stxNodeKind := (← getCurrNamespace) ++ name
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser")
  let (val, lhsPrec?) ← runTermElabM none fun _ => Term.toParserDescr syntaxParser cat
  let declName := mkIdentFrom stx name
  let d ←
    if let some lhsPrec := lhsPrec? then
      `(@[$attrKind:attrKind $catParserId:ident $(quote prio):numLit] def $declName : Lean.TrailingParserDescr :=
        ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $(quote lhsPrec) $val)
    else
      `(@[$attrKind:attrKind $catParserId:ident $(quote prio):numLit] def $declName : Lean.ParserDescr :=
        ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
  trace `Elab fun _ => d
  withMacroExpansion stx d <| elabCommand d

/-
def syntaxAbbrev  := leading_parser "syntax " >> ident >> " := " >> many1 syntaxParser
-/
@[builtinCommandElab «syntaxAbbrev»] def elabSyntaxAbbrev : CommandElab := fun stx => do
  let declName := stx[1]
  -- TODO: nonatomic names
  let (val, _) ← runTermElabM none $ fun _ => Term.toParserDescr stx[3] Name.anonymous
  let stxNodeKind := (← getCurrNamespace) ++ declName.getId
  let stx' ← `(def $declName : Lean.ParserDescr := ParserDescr.nodeWithAntiquot $(quote (toString declName.getId)) $(quote stxNodeKind) $val)
  withMacroExpansion stx stx' $ elabCommand stx'

/-
  Remark: `k` is the user provided kind with the current namespace included.
  Recall that syntax node kinds contain the current namespace.
-/
def elabMacroRulesAux (k : SyntaxNodeKind) (alts : Array Syntax) : CommandElabM Syntax := do
  let alts ← alts.mapM fun alt => match alt with
    | `(matchAltExpr| | $pats,* => $rhs) => do
      let pat := pats.elemsAndSeps[0]
      if !pat.isQuot then
        throwUnsupportedSyntax
      let quoted := getQuotContent pat
      let k' := quoted.getKind
      if k' == k then
        pure alt
      else if k' == choiceKind then
         match quoted.getArgs.find? fun quotAlt => quotAlt.getKind == k with
         | none        => throwErrorAt alt "invalid macro_rules alternative, expected syntax node kind '{k}'"
         | some quoted =>
           let pat := pat.setArg 1 quoted
           let pats := pats.elemsAndSeps.set! 0 pat
           `(matchAltExpr| | $pats,* => $rhs)
      else
        throwErrorAt alt "invalid macro_rules alternative, unexpected syntax node kind '{k'}'"
    | _ => throwUnsupportedSyntax
  `(@[macro $(Lean.mkIdent k)] def myMacro : Macro :=
     fun $alts:matchAlt* | _ => throw Lean.Macro.Exception.unsupportedSyntax)

def inferMacroRulesAltKind : Syntax → CommandElabM SyntaxNodeKind
  | `(matchAltExpr| | $pats,* => $rhs) => do
    let pat := pats.elemsAndSeps[0]
    if !pat.isQuot then
      throwUnsupportedSyntax
    let quoted := getQuotContent pat
    pure quoted.getKind
  | _ => throwUnsupportedSyntax

def elabNoKindMacroRulesAux (alts : Array Syntax) : CommandElabM Syntax := do
  let k ← inferMacroRulesAltKind alts[0]
  if k == choiceKind then
    throwErrorAt alts[0]
      "invalid macro_rules alternative, multiple interpretations for pattern (solution: specify node kind using `macro_rules [<kind>] ...`)"
  else
    let altsK    ← alts.filterM fun alt => do pure $ k == (← inferMacroRulesAltKind alt)
    let altsNotK ← alts.filterM fun alt => do pure $ k != (← inferMacroRulesAltKind alt)
    let defCmd   ← elabMacroRulesAux k altsK
    if altsNotK.isEmpty then
      pure defCmd
    else
      `($defCmd:command macro_rules $altsNotK:matchAlt*)

@[builtinCommandElab «macro_rules»] def elabMacroRules : CommandElab :=
  adaptExpander fun stx => match stx with
  | `(macro_rules $alts:matchAlt*)         => elabNoKindMacroRulesAux alts
  | `(macro_rules [$kind] $alts:matchAlt*) => do elabMacroRulesAux ((← getCurrNamespace) ++ kind.getId) alts
  | _                                      => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Command.mixfix] def expandMixfix : Macro := fun stx =>
  withAttrKindGlobal stx fun stx => do
    match stx with
    | `(infixl $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalOptPrec prec) + 1
      `(notation $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? lhs$[:$prec]? $op:strLit rhs:$prec1 => $f lhs rhs)
    | `(infix $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalOptPrec prec) + 1
      `(notation $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? lhs:$prec1 $op:strLit rhs:$prec1 => $f lhs rhs)
    | `(infixr $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      let prec1 := quote <| (← evalOptPrec prec) + 1
      `(notation $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? lhs:$prec1 $op:strLit rhs $[: $prec]? => $f lhs rhs)
    | `(prefix $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      `(notation $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? $op:strLit arg $[: $prec]? => $f arg)
    | `(postfix $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? $op => $f) =>
      `(notation $[: $prec]? $[(name := $name)]? $[(priority := $prio)]? arg$[:$prec]? $op:strLit => $f arg)
    | _ => Macro.throwUnsupported
where
  -- set "global" `attrKind`, apply `f`, and restore `attrKind` to result
  withAttrKindGlobal stx f := do
    let attrKind := stx[0]
    let stx  := stx.setArg 0 mkAttrKindGlobal
    let stx ← f stx
    return stx.setArg 0 attrKind

/- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
  | stx => match stx with
  | `($id:ident) =>
    if (vars.findIdx? (fun var => var.getId == id.getId)).isSome then
      mkAntiquotNode id
    else
      stx
  | _ => match stx with
    | Syntax.node k args => Syntax.node k (args.map (antiquote vars))
    | stx => stx

/- Convert `notation` command lhs item into a `syntax` command item -/
def expandNotationItemIntoSyntaxItem (stx : Syntax) : CommandElabM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    pure $ Syntax.node `Lean.Parser.Syntax.cat #[mkIdentFrom stx `term,  stx[1]]
  else if k == strLitKind then
    pure $ Syntax.node `Lean.Parser.Syntax.atom #[stx]
  else
    throwUnsupportedSyntax

def strLitToPattern (stx: Syntax) : MacroM Syntax :=
  match stx.isStrLit? with
  | some str => pure $ mkAtomFrom stx str
  | none     => Macro.throwUnsupported

/- Convert `notation` command lhs item into a pattern element -/
def expandNotationItemIntoPattern (stx : Syntax) : CommandElabM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    mkAntiquotNode stx[0]
  else if k == strLitKind then
    liftMacroM <| strLitToPattern stx
  else
    throwUnsupportedSyntax

/-- Try to derive a `SimpleDelab` from a notation.
    The notation must be of the form `notation ... => c var_1 ... var_n`
    where `c` is a declaration in the current scope and the `var_i` are a permutation of the LHS vars. -/
def mkSimpleDelab (attrKind : Syntax) (vars : Array Syntax) (pat qrhs : Syntax) : OptionT CommandElabM Syntax := do
  match qrhs with
  | `($c:ident $args*) =>
    let [(c, [])] ← resolveGlobalName c.getId | failure
    guard <| args.all (Syntax.isIdent ∘ getAntiquotTerm)
    guard <| args.allDiff
    -- replace head constant with fresh (unused) antiquotation so we're not dependent on the exact pretty printing of the head
    let qrhs ← `($(mkAntiquotNode (mkIdent "c")) $args*)
    `(@[$attrKind:attrKind appUnexpander $(mkIdent c):ident] def unexpand : Lean.PrettyPrinter.Unexpander := fun
       | `($qrhs) => `($pat)
       | _        => throw ())
  | `($c:ident)        =>
    let [(c, [])] ← resolveGlobalName c.getId | failure
    `(@[$attrKind:attrKind appUnexpander $(mkIdent c):ident] def unexpand : Lean.PrettyPrinter.Unexpander := fun _ => `($pat))
  | _                  => failure

private def expandNotationAux (ref : Syntax)
    (currNamespace : Name) (attrKind : Syntax) (prec? : Option Syntax) (name? : Option Syntax) (prio? : Option Syntax) (items : Array Syntax) (rhs : Syntax) : CommandElabM Syntax := do
  let prio ← liftMacroM <| evalOptPrio prio?
  -- build parser
  let syntaxParts ← items.mapM expandNotationItemIntoSyntaxItem
  let cat := mkIdentFrom ref `term
  let name ←
    match name? with
    | some name => pure name.getId
    | none => mkNameFromParserSyntax `term (mkNullNode syntaxParts)
  -- build macro rules
  let vars := items.filter fun item => item.getKind == `Lean.Parser.Command.identPrec
  let vars := vars.map fun var => var[0]
  let qrhs := antiquote vars rhs
  let patArgs ← items.mapM expandNotationItemIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let fullName := currNamespace ++ name
  let pat := Syntax.node fullName patArgs
  let stxDecl ← `($attrKind:attrKind syntax $[: $prec?]? (name := $(mkIdent name)) (priority := $(quote prio):numLit) $[$syntaxParts]* : $cat)
  let macroDecl ← `(macro_rules | `($pat) => `($qrhs))
  match (← mkSimpleDelab attrKind vars pat qrhs |>.run) with
  | some delabDecl => mkNullNode #[stxDecl, macroDecl, delabDecl]
  | none           => mkNullNode #[stxDecl, macroDecl]

@[builtinCommandElab «notation»] def expandNotation : CommandElab :=
  adaptExpander fun stx => do
    let currNamespace ← getCurrNamespace
    match stx with
    | `($attrKind:attrKind notation $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $items* => $rhs) =>
      -- trigger scoped checks early and only once
      let _ ← toAttributeKind attrKind
      expandNotationAux stx currNamespace attrKind prec? name? prio? items rhs
    | _ => throwUnsupportedSyntax

/- Convert `macro` argument into a `syntax` command item -/
def expandMacroArgIntoSyntaxItem : Macro
  | `(macroArg|$id:ident:$stx)    => stx
  -- can't match against `$s:strLit%$id` because the latter part would be interpreted as an antiquotation on the token
  -- `strLit`.
  | `(macroArg|$s:macroArgSymbol) => `(stx|$(s[0]):strLit)
  | _                             => Macro.throwUnsupported

/- Convert `macro` arg into a pattern element -/
def expandMacroArgIntoPattern (stx : Syntax) : MacroM Syntax := do
  match (← expandMacros stx) with
  | `(macroArg|$id:ident:optional($stx)) =>
    mkSplicePat `optional id "?"
  | `(macroArg|$id:ident:many($stx)) =>
    mkSplicePat `many id "*"
  | `(macroArg|$id:ident:many1($stx)) =>
    mkSplicePat `many id "*"
  | `(macroArg|$id:ident:sepBy($stx, $sep:strLit $[, $stxsep]? $[, allowTrailingSep]?)) =>
    mkSplicePat `sepBy id ((isStrLit? sep).get! ++ "*")
  | `(macroArg|$id:ident:sepBy1($stx, $sep:strLit $[, $stxsep]? $[, allowTrailingSep]?)) =>
    mkSplicePat `sepBy id ((isStrLit? sep).get! ++ "*")
  | `(macroArg|$id:ident:$stx) => mkAntiquotNode id
  | `(macroArg|$s:strLit) => strLitToPattern s
  -- `"tk"%id` ~> `"tk"%$id`
  | `(macroArg|$s:macroArgSymbol) => mkNode `token_antiquot #[← strLitToPattern s[0], mkAtom "%", mkAtom "$", s[1][1]]
  | _                          => Macro.throwUnsupported
  where mkSplicePat kind id suffix :=
    mkNullNode #[mkAntiquotSuffixSpliceNode kind (mkAntiquotNode id) suffix]


/- «macro» := leading_parser suppressInsideQuot (Term.attrKind >> "macro " >> optPrecedence >> optNamedName >> optNamedPrio >> macroHead >> many macroArg >> macroTail) -/
def expandMacro (currNamespace : Name) (stx : Syntax) : CommandElabM Syntax := do
  let attrKind := stx[0]
  let prec := stx[2].getOptional?
  let name? ← liftMacroM <| expandOptNamedName stx[3]
  let prio  ← liftMacroM <| expandOptNamedPrio stx[4]
  let head := stx[5]
  let args := stx[6].getArgs
  let cat  := stx[8]
  -- build parser
  let stxPart  ← liftMacroM <| expandMacroArgIntoSyntaxItem head
  let stxParts ← liftMacroM <| args.mapM expandMacroArgIntoSyntaxItem
  let stxParts := #[stxPart] ++ stxParts
  -- name
  let name ← match name? with
    | some name => pure name
    | none => mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
  -- build macro rules
  let patHead ← liftMacroM <| expandMacroArgIntoPattern head
  let patArgs ← liftMacroM <| args.mapM expandMacroArgIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let pat := Syntax.node (currNamespace ++ name) (#[patHead] ++ patArgs)
  if stx.getArgs.size == 11 then
    -- `stx` is of the form `macro $head $args* : $cat => term`
    let rhs := stx[10]
    let stxCmd ← `(Parser.Command.syntax| $attrKind:attrKind syntax $(prec)? (name := $(mkIdentFrom stx name):ident) (priority := $(quote prio):numLit) $[$stxParts]* : $cat)
    let macroRulesCmd ← `(macro_rules | `($pat) => $rhs)
    return mkNullNode #[stxCmd, macroRulesCmd]
  else
    -- `stx` is of the form `macro $head $args* : $cat => `( $body )`
    let rhsBody := stx[11]
    let stxCmd ← `(Parser.Command.syntax| $attrKind:attrKind syntax $(prec)? (name := $(mkIdentFrom stx name):ident) (priority := $(quote prio):numLit) $[$stxParts]* : $cat)
    let macroRulesCmd ← `(macro_rules | `($pat) => `($rhsBody))
    return mkNullNode #[stxCmd, macroRulesCmd]

@[builtinCommandElab «macro»] def elabMacro : CommandElab :=
  adaptExpander fun stx => do
    expandMacro (← getCurrNamespace) stx

builtin_initialize
  registerTraceClass `Elab.syntax

@[inline] def withExpectedType (expectedType? : Option Expr) (x : Expr → TermElabM Expr) : TermElabM Expr := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType?
    | throwError "expected type must be known"
  x expectedType

/-
def elabTail := try (" : " >> ident) >> darrow >> termParser
def «elab» := leading_parser suppressInsideQuot (Term.attrKind >> "elab " >> optPrecedence >> optNamedName >> optNamedPrio >> elabHead >> many elabArg >> elabTail)
-/
def expandElab (currNamespace : Name) (stx : Syntax) : CommandElabM Syntax := do
  let ref := stx
  let attrKind := stx[0]
  let prec     := stx[2].getOptional?
  let name?   ← liftMacroM <| expandOptNamedName stx[3]
  let prio    ← liftMacroM <| expandOptNamedPrio stx[4]
  let head    := stx[5]
  let args    := stx[6].getArgs
  let cat     := stx[8]
  let expectedTypeSpec := stx[9]
  let rhs     := stx[11]
  let catName := cat.getId
  -- build parser
  let stxPart  ← liftMacroM <| expandMacroArgIntoSyntaxItem head
  let stxParts ← liftMacroM <| args.mapM expandMacroArgIntoSyntaxItem
  let stxParts := #[stxPart] ++ stxParts
  -- name
  let name ← match name? with
    | some name => pure name
    | none => mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
  -- build pattern for `martch_syntax
  let patHead ← liftMacroM <| expandMacroArgIntoPattern head
  let patArgs ← liftMacroM <| args.mapM expandMacroArgIntoPattern
  let pat := Syntax.node (currNamespace ++ name) (#[patHead] ++ patArgs)
  let stxCmd ← `(Parser.Command.syntax|
    $attrKind:attrKind syntax $(prec)? (name := $(mkIdentFrom stx name):ident) (priority := $(quote prio):numLit) $[$stxParts]* : $cat)
  let elabCmd ←
    if expectedTypeSpec.hasArgs then
      if catName == `term then
        let expId := expectedTypeSpec[1]
        `(@[termElab $(mkIdentFrom stx name):ident] def elabFn : Lean.Elab.Term.TermElab :=
          fun stx expectedType? => match stx with
            | `($pat) => Lean.Elab.Command.withExpectedType expectedType? fun $expId => $rhs
            | _ => throwUnsupportedSyntax)
      else
        throwErrorAt expectedTypeSpec "syntax category '{catName}' does not support expected type specification"
    else if catName == `term then
      `(@[termElab $(mkIdentFrom stx name):ident] def elabFn : Lean.Elab.Term.TermElab :=
        fun stx _ => match stx with
          | `($pat) => $rhs
          | _ => throwUnsupportedSyntax)
    else if catName == `command then
      `(@[commandElab $(mkIdentFrom stx name):ident] def elabFn : Lean.Elab.Command.CommandElab :=
        fun
          | `($pat) => $rhs
          | _ => throwUnsupportedSyntax)
    else if catName == `tactic then
      `(@[tactic $(mkIdentFrom stx name):ident] def elabFn : Lean.Elab.Tactic.Tactic :=
        fun
          | `(tactic|$pat) => $rhs
          | _ => throwUnsupportedSyntax)
    else
      -- We considered making the command extensible and support new user-defined categories. We think it is unnecessary.
      -- If users want this feature, they add their own `elab` macro that uses this one as a fallback.
      throwError "unsupported syntax category '{catName}'"
  return mkNullNode #[stxCmd, elabCmd]

@[builtinCommandElab «elab»] def elabElab : CommandElab :=
  adaptExpander fun stx => do
    expandElab (← getCurrNamespace) stx

end Lean.Elab.Command
