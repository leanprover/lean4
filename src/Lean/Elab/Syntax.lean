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
 «precedence» := parser! " : " >> precedenceParser -/
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

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateRefT Bool TermElabM)
private def markAsTrailingParser : ToParserDescrM Unit := set true

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with first := false }) x

@[inline] private def withNestedParser {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with leftRec := false, first := false }) x

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
  let ctx ← read
  if ctx.first && stx.getKind == `Lean.Parser.Syntax.cat then
    let cat := stx[0].getId.eraseMacroScopes
    if cat == ctx.catName then
      let prec? ← liftMacroM <| expandOptPrecedence stx[1]
      unless prec?.isNone do throwErrorAt stx[1] ("invalid occurrence of ':<num>' modifier in head")
      unless ctx.leftRec do
        throwErrorAt! stx[3] "invalid occurrence of '{cat}', parser algorithm does not allow this form of left recursion"
      markAsTrailingParser -- mark as trailing par
      pure true
    else
      pure false
  else
    pure false

partial def toParserDescrAux (stx : Syntax) : ToParserDescrM Syntax := withRef stx do
  let kind := stx.getKind
  if kind == nullKind then
    let args := stx.getArgs
    if (← checkLeftRec stx[0]) then
      if args.size == 1 then throwErrorAt stx "invalid atomic left recursive syntax"
      let args := args.eraseIdx 0
      let args ← args.mapM fun arg => withNestedParser $ toParserDescrAux arg
      mkParserSeq args
    else
      let args ← args.mapIdxM fun i arg => withReader (fun ctx => { ctx with first := ctx.first && i.val == 0 }) $ toParserDescrAux arg
      mkParserSeq args
  else if kind == choiceKind then
    toParserDescrAux stx[0]
  else if kind == `Lean.Parser.Syntax.paren then
    toParserDescrAux stx[1]
  else if kind == `Lean.Parser.Syntax.unary then
    let aliasName := (stx[0].getId).eraseMacroScopes
    Parser.ensureUnaryParserAlias aliasName
    let d ← withNestedParser $ toParserDescrAux stx[2]
    `(ParserDescr.unary $(quote aliasName) $d)
  else if kind == `Lean.Parser.Syntax.binary then
    let aliasName := (stx[0].getId).eraseMacroScopes
    Parser.ensureBinaryParserAlias aliasName
    let d₁ ← withNestedParser $ toParserDescrAux stx[2]
    let d₂ ← withNestedParser $ toParserDescrAux stx[4]
    `(ParserDescr.binary $(quote aliasName) $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.sepBy then
    let p ← withNestedParser $ toParserDescrAux stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else toParserDescrAux stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    `(ParserDescr.sepBy $p $sep $psep $(quote allowTrailingSep))
  else if kind == `Lean.Parser.Syntax.sepBy1 then
    let p ← withNestedParser $ toParserDescrAux stx[1]
    let sep := stx[3]
    let psep ← if stx[4].isNone then `(ParserDescr.symbol $sep) else toParserDescrAux stx[4][1]
    let allowTrailingSep := !stx[5].isNone
    `(ParserDescr.sepBy1 $p $sep $psep $(quote allowTrailingSep))
  else if kind == `Lean.Parser.Syntax.cat then
    let cat   := stx[0].getId.eraseMacroScopes
    let prec? ← liftMacroM <| expandOptPrecedence stx[1]
    if (← Parser.isParserAlias cat) then
      Parser.ensureConstantParserAlias cat
      if prec?.isSome then
        throwErrorAt! stx[1] "unexpected precedence in atomic parser"
      `(ParserDescr.const $(quote cat))
    else
      let ctx ← read
      if ctx.first && cat == ctx.catName then
        throwErrorAt stx "invalid atomic left recursive syntax"
      else
        let env ← getEnv
        if Parser.isParserCategory env cat then
          let prec := prec?.getD 0
          `(ParserDescr.cat $(quote cat) $(quote prec))
        else
          -- `cat` is not a valid category name. Thus, we test whether it is a valid constant
          let candidates ← resolveGlobalConst cat
          /- Convert `candidates` in a list of pairs `(c, isDescr)`, where `c` is the parser name,
             and `isDescr` is true iff `c` has type `Lean.ParserDescr` or `Lean.TrailingParser` -/
          let candidates := candidates.filterMap fun c =>
              match env.find? c with
              | none      => none
              | some info =>
                match info.type with
                | Expr.const `Lean.Parser.TrailingParser _ _ => (c, false)
                | Expr.const `Lean.Parser.Parser _ _         => (c, false)
                | Expr.const `Lean.ParserDescr _ _           => (c, true)
                | Expr.const `Lean.TrailingParserDescr _ _   => (c, true)
                | _                                          => none
           match candidates with
           | []  => throwErrorAt! stx[3] "unknown category '{cat}' or parser declaration"
           | [(c, isDescr)] =>
             unless prec?.isNone do throwErrorAt stx[3] "unexpected precedence"
             if isDescr then
               mkIdentFrom stx c
             else
               `(ParserDescr.parser $(quote c))
           | cs  => throwErrorAt! stx[3] "ambiguous parser declaration {cs}"
  else if kind == `Lean.Parser.Syntax.atom then
    match stx[0].isStrLit? with
    | some atom =>
      /- For syntax categories where initialized with `LeadingIdentBehavior` different from default (e.g., `tactic`), we automatically mark
         the first symbol as nonReserved. -/
      if (← read).behavior != Parser.LeadingIdentBehavior.default && (← read).first then
        `(ParserDescr.nonReservedSymbol $(quote atom) false)
      else
        `(ParserDescr.symbol $(quote atom))
    | none => throwUnsupportedSyntax
  else if kind == `Lean.Parser.Syntax.nonReserved then
    match stx[1].isStrLit? with
    | some atom => `(ParserDescr.nonReservedSymbol $(quote atom) false)
    | none      => throwUnsupportedSyntax
  else
    let stxNew? ← liftM (liftMacroM (expandMacro? stx) : TermElabM _)
    match stxNew? with
    | some stxNew => toParserDescrAux stxNew
    | none => throwErrorAt! stx "unexpected syntax kind of category `syntax`: {kind}"

/--
  Given a `stx` of category `syntax`, return a pair `(newStx, trailingParser)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `trailingParser == true`, and `ParserDescr` otherwise. -/
def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Syntax × Bool) := do
  let env ← getEnv
  let behavior := Parser.leadingIdentBehavior env catName
  (toParserDescrAux stx { catName := catName, first := true, leftRec := true, behavior := behavior }).run false

end Term

namespace Command
open Lean.Syntax
open Lean.Parser.Command

private def getCatSuffix (catName : Name) : String :=
  match catName with
  | Name.str _ s _ => s
  | _              => unreachable!

private def declareSyntaxCatQuotParser (catName : Name) : CommandElabM Unit := do
  let quotSymbol := "`(" ++ getCatSuffix catName ++ "|"
  let kind := catName ++ `quot
  let cmd ← `(
    @[termParser] def $(mkIdent kind) : Lean.ParserDescr :=
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

private def elabKindPrio (stx : Syntax) (catName : Name) : CommandElabM (Option Name × Nat) := do
  if stx.isNone then
    pure (none, 0)
  else
    let arg := stx[1]
    if arg.getKind == `Lean.Parser.Command.parserKind then
      let k := arg[0].getId
      pure (k, 0)
    else if arg.getKind == `Lean.Parser.Command.parserPrio then
      let prio ← liftMacroM <| evalPrio arg[0]
      pure (none, prio)
    else if arg.getKind == `Lean.Parser.Command.parserKindPrio then
      let k := arg[0].getId
      let prio ← liftMacroM <| evalPrio arg[2]
      pure (k, prio)
    else
      throwError "unexpected syntax kind/priority"

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
    isAtomLikeSyntax stx[0] -- see toParserDescrAux
  else if kind == `Lean.Parser.Syntax.paren then
    isAtomLikeSyntax stx[1]
  else
    kind == `Lean.Parser.Syntax.atom

/-
def «syntax»      := parser! attrKind >> "syntax " >> optPrecedence >> optKindPrio >> many1 syntaxParser >> " : " >> ident
-/
@[builtinCommandElab «syntax»] def elabSyntax : CommandElab := fun stx => do
  let env ← getEnv
  let attrKind ← toAttributeKind stx[0]
  let cat      := stx[6].getId.eraseMacroScopes
  unless (Parser.isParserCategory env cat) do
    throwErrorAt! stx[6] "unknown category '{cat}'"
  let syntaxParser := stx[4]
  -- If the user did not provide an explicit precedence, we assign `maxPrec` to atom-like syntax and `leadPrec` otherwise.
  let precDefault  := if isAtomLikeSyntax syntaxParser then Parser.maxPrec else Parser.leadPrec
  let prec := (← liftMacroM (Term.expandOptPrecedence stx[2])).getD precDefault
  let (kind?, prio) ← elabKindPrio stx[3] cat
  let kind ← match kind? with
    | some kind => pure kind
    | none      => mkNameFromParserSyntax cat syntaxParser
  /-
    The declaration name and the syntax node kind should be the same.
    We are using `def $kind ...`. So, we must append the current namespace to create the name fo the Syntax `node`. -/
  let stxNodeKind := (← getCurrNamespace) ++ kind
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser")
  let (val, trailingParser) ← runTermElabM none fun _ => Term.toParserDescr syntaxParser cat
  let declName := mkIdentFrom stx kind
  let d ←
    match trailingParser, attrKind with
    | true, AttributeKind.global =>
      `(@[$catParserId:ident $(quote prio):numLit] def $declName : Lean.TrailingParserDescr :=
         ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $val)
    | false, AttributeKind.global =>
      `(@[$catParserId:ident $(quote prio):numLit] def $declName : Lean.ParserDescr :=
         ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
    | true, AttributeKind.scoped =>
      `(@[scoped $catParserId:ident $(quote prio):numLit] def $declName : Lean.TrailingParserDescr :=
         ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $val)
    | false, AttributeKind.scoped =>
      `(@[scoped $catParserId:ident $(quote prio):numLit] def $declName : Lean.ParserDescr :=
         ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
    | true, AttributeKind.local =>
      `(@[local $catParserId:ident $(quote prio):numLit] def $declName : Lean.TrailingParserDescr :=
         ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $val)
    | false, AttributeKind.local =>
      `(@[local $catParserId:ident $(quote prio):numLit] def $declName : Lean.ParserDescr :=
         ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
  trace `Elab fun _ => d
  withMacroExpansion stx d <| elabCommand d

/-
def syntaxAbbrev  := parser! "syntax " >> ident >> " := " >> many1 syntaxParser
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
  let alts ← alts.mapSepElemsM fun alt => do
    let lhs := alt[0]
    let pat := lhs[0]
    if !pat.isQuot then
      throwUnsupportedSyntax
    let quot := pat[1]
    let k' := quot.getKind
    if k' == k then
      pure alt
    else if k' == choiceKind then
       match quot.getArgs.find? fun quotAlt => quotAlt.getKind == k with
       | none      => throwErrorAt! alt "invalid macro_rules alternative, expected syntax node kind '{k}'"
       | some quot =>
         let pat := pat.setArg 1 quot
         let lhs := lhs.setArg 0 pat
         pure $ alt.setArg 0 lhs
    else
      throwErrorAt! alt "invalid macro_rules alternative, unexpected syntax node kind '{k'}'"
  `(@[macro $(Lean.mkIdent k)] def myMacro : Macro :=
     fun | $(SepArray.mk alts):matchAlt|* | _ => throw Lean.Macro.Exception.unsupportedSyntax)

def inferMacroRulesAltKind (alt : Syntax) : CommandElabM SyntaxNodeKind := do
  let lhs := alt[0]
  let pat := lhs[0]
  if !pat.isQuot then
    throwUnsupportedSyntax
  let quot := pat[1]
  pure quot.getKind

def elabNoKindMacroRulesAux (alts : Array Syntax) : CommandElabM Syntax := do
  let k ← inferMacroRulesAltKind (alts.get! 0)
  if k == choiceKind then
    throwErrorAt! alts[0]
      "invalid macro_rules alternative, multiple interpretations for pattern (solution: specify node kind using `macro_rules [<kind>] ...`)"
  else
    let altsK    ← alts.filterSepElemsM fun alt => do pure $ k == (← inferMacroRulesAltKind alt)
    let altsNotK ← alts.filterSepElemsM fun alt => do pure $ k != (← inferMacroRulesAltKind alt)
    let defCmd   ← elabMacroRulesAux k altsK
    if altsNotK.isEmpty then
      pure defCmd
    else
      `($defCmd:command macro_rules $(SepArray.mk altsNotK):matchAlt|*)

@[builtinCommandElab «macro_rules»] def elabMacroRules : CommandElab :=
  adaptExpander fun stx => match stx with
  | `(macro_rules $[|]? $alts:matchAlt|*)         => elabNoKindMacroRulesAux alts.elemsAndSeps
  | `(macro_rules [$kind] $[|]? $alts:matchAlt|*) => do elabMacroRulesAux ((← getCurrNamespace) ++ kind.getId) alts.elemsAndSeps
  | _                                             => throwUnsupportedSyntax

-- TODO: cleanup after we have support for optional syntax at `match_syntax`
@[builtinMacro Lean.Parser.Command.mixfix] def expandMixfix : Macro := fun stx =>
  withAttrKindGlobal stx fun stx => do
    match stx with
    | `(infix $[: $prec]? $[[$prio]]? $op => $f)   => `(infixl $[: $prec]? $[[$prio]]? $op => $f)
    | `(infixr $[: $prec]? $[[$prio]]? $op => $f)  => `(notation $[: $prec]? $[[$prio]]? lhs $op:strLit rhs $[: $prec]? => $f lhs rhs)
    | `(infixl $[: $prec]? $[[$prio]]? $op => $f)  =>
       let prec1 := quote <| (← evalOptPrec prec) + 1
       `(notation $[: $prec]? $[[$prio]]? lhs $op:strLit rhs:$prec1 => $f lhs rhs)
    | `(prefix $[: $prec]? $[[$prio]]? $op => $f)  => `(notation $[: $prec]? $[[$prio]]? $op:strLit arg $[: $prec]? => $f arg)
    | `(postfix $[: $prec]? $[[$prio]]? $op => $f) => `(notation $[: $prec]? $[[$prio]]? arg $op:strLit => $f arg)
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
def mkSimpleDelab (vars : Array Syntax) (pat qrhs : Syntax) : OptionT CommandElabM Syntax :=
  match qrhs with
  | `($c:ident $args*) => go c args
  | `($c:ident)        => go c #[]
  | _                  => failure
  where go c args := do
    let [(c, [])] ← resolveGlobalName c.getId | failure
    guard <| args.all (Syntax.isIdent ∘ getAntiquotTerm)
    guard <| args.allDiff
    -- replace head constant with fresh (unused) antiquotation so we're not dependent on the exact pretty printing of the head
    let qrhs ← `($(mkAntiquotNode (mkIdent "c")) $args*)
    `(@[appUnexpander $(mkIdent c):ident] def unexpand : Lean.PrettyPrinter.Unexpander := fun
       | `($qrhs) => `($pat)
       | _        => throw ())

private def expandNotationAux (ref : Syntax)
    (currNamespace : Name) (attrKind : AttributeKind) (prec? : Option Syntax) (prio? : Option Syntax) (items : Array Syntax) (rhs : Syntax) : CommandElabM Syntax := do
  let prio ← liftMacroM <| evalOptPrio prio?
  -- build parser
  let syntaxParts ← items.mapM expandNotationItemIntoSyntaxItem
  let cat := mkIdentFrom ref `term
  let kind ← mkNameFromParserSyntax `term (mkNullNode syntaxParts)
  -- build macro rules
  let vars := items.filter fun item => item.getKind == `Lean.Parser.Command.identPrec
  let vars := vars.map fun var => var[0]
  let qrhs := antiquote vars rhs
  let patArgs ← items.mapM expandNotationItemIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let fullKind := currNamespace ++ kind
  let pat := Syntax.node fullKind patArgs
  let stxDecl ← match attrKind with
    | AttributeKind.global => `(syntax $[: $prec?]? [$(mkIdentFrom ref kind):ident, $(quote prio):numLit] $[$syntaxParts]* : $cat)
    | AttributeKind.scoped => `(scoped syntax $[: $prec? ]? [$(mkIdentFrom ref kind):ident, $(quote prio):numLit] $[$syntaxParts]* : $cat)
    | AttributeKind.local  => `(local syntax $[: $prec? ]? [$(mkIdentFrom ref kind):ident, $(quote prio):numLit] $[$syntaxParts]* : $cat)
  let macroDecl ← `(macro_rules | `($pat) => `($qrhs))
  match (← mkSimpleDelab vars pat qrhs |>.run) with
  | some delabDecl => mkNullNode #[stxDecl, macroDecl, delabDecl]
  | none           => mkNullNode #[stxDecl, macroDecl]

@[builtinCommandElab «notation»] def expandNotation : CommandElab :=
  adaptExpander fun stx => do
    let attrKind ← toAttributeKind stx[0]
    let stx := stx.setArg 0 mkAttrKindGlobal
    let currNamespace ← getCurrNamespace
    match stx with
    | `(notation $[: $prec? ]? $[[ $prio? ]]? $items* => $rhs) => expandNotationAux stx currNamespace attrKind prec? prio? items rhs
    | _ => throwUnsupportedSyntax

/- Convert `macro` argument into a `syntax` command item -/
def expandMacroArgIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.macroArgSimple then
    pure stx[2]
  else if k == strLitKind then
    pure $ Syntax.node `Lean.Parser.Syntax.atom #[stx]
  else
    Macro.throwUnsupported

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
  | `(macroArg|$s:strLit)      => strLitToPattern s
  | _                          => Macro.throwUnsupported
  where mkSplicePat kind id suffix :=
    mkNullNode #[mkAntiquotSuffixSpliceNode kind (mkAntiquotNode id) suffix]

def expandOptPrio (stx : Syntax) : MacroM Nat :=
  if stx.isNone then
    return evalPrio! default
  else
    evalPrio stx[1]

def expandMacro (currNamespace : Name) (stx : Syntax) : CommandElabM Syntax := do
  let prec := stx[1].getOptional?
  let prio ← liftMacroM <| expandOptPrio stx[2]
  let head := stx[3]
  let args := stx[4].getArgs
  let cat  := stx[6]
  -- build parser
  let stxPart  ← liftMacroM <| expandMacroArgIntoSyntaxItem head
  let stxParts ← liftMacroM <| args.mapM expandMacroArgIntoSyntaxItem
  let stxParts := #[stxPart] ++ stxParts
  -- kind
  let kind ← mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
  -- build macro rules
  let patHead ← liftMacroM <| expandMacroArgIntoPattern head
  let patArgs ← liftMacroM <| args.mapM expandMacroArgIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let pat := Syntax.node (currNamespace ++ kind) (#[patHead] ++ patArgs)
  if stx.getArgs.size == 9 then
    -- `stx` is of the form `macro $head $args* : $cat => term`
    let rhs := stx[8]
    -- NOTE: can't use `$stxParts*` here because it would interpret as a single antiquotation with the `stx` star postfix operator
    `(syntax $(prec)? [$(mkIdentFrom stx kind):ident, $(quote prio):numLit] $[$stxParts]* : $cat
      macro_rules | `($pat) => $rhs)
  else
    -- `stx` is of the form `macro $head $args* : $cat => `( $body )`
    let rhsBody := stx[9]
    `(syntax $(prec)? [$(mkIdentFrom stx kind):ident, $(quote prio):numLit] $[$stxParts]* : $cat
      macro_rules | `($pat) => `($rhsBody))

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
parser! "elab " >> optPrecedence >> optPrio >> elabHead >> many elabArg >> elabTail
-/
def expandElab (currNamespace : Name) (stx : Syntax) : CommandElabM Syntax := do
  let ref := stx
  let prec    := stx[1].getOptional?
  let prio    ←  liftMacroM <| expandOptPrio stx[2]
  let head    := stx[3]
  let args    := stx[4].getArgs
  let cat     := stx[6]
  let expectedTypeSpec := stx[7]
  let rhs     := stx[9]
  let catName := cat.getId
  -- build parser
  let stxPart  ← liftMacroM <| expandMacroArgIntoSyntaxItem head
  let stxParts ← liftMacroM <| args.mapM expandMacroArgIntoSyntaxItem
  let stxParts := #[stxPart] ++ stxParts
  -- kind
  let kind ← mkNameFromParserSyntax cat.getId (mkNullNode stxParts)
  -- build pattern for `martch_syntax
  let patHead ← liftMacroM <| expandMacroArgIntoPattern head
  let patArgs ← liftMacroM <| args.mapM expandMacroArgIntoPattern
  let pat := Syntax.node (currNamespace ++ kind) (#[patHead] ++ patArgs)
  let kindId    := mkIdentFrom ref kind
  if expectedTypeSpec.hasArgs then
    if catName == `term then
      let expId := expectedTypeSpec[1]
      `(syntax $(prec)? [$kindId:ident, $(quote prio):numLit] $[$stxParts]* : $cat
        @[termElab $kindId:ident] def elabFn : Lean.Elab.Term.TermElab :=
        fun stx expectedType? => match stx with
          | `($pat) => Lean.Elab.Command.withExpectedType expectedType? fun $expId => $rhs
          | _ => throwUnsupportedSyntax)
    else
      throwErrorAt! expectedTypeSpec "syntax category '{catName}' does not support expected type specification"
  else if catName == `term then
    `(syntax $(prec)? [$kindId:ident, $(quote prio):numLit] $[$stxParts]* : $cat
      @[termElab $kindId:ident] def elabFn : Lean.Elab.Term.TermElab :=
      fun stx _ => match stx with
        | `($pat) => $rhs
        | _ => throwUnsupportedSyntax)
  else if catName == `command then
    `(syntax $(prec)? [$kindId:ident, $(quote prio):numLit] $[$stxParts]* : $cat
      @[commandElab $kindId:ident] def elabFn : Lean.Elab.Command.CommandElab :=
      fun
        | `($pat) => $rhs
        | _ => throwUnsupportedSyntax)
  else if catName == `tactic then
    `(syntax $(prec)? [$kindId:ident, $(quote prio):numLit] $[$stxParts]* : $cat
      @[tactic $kindId:ident] def elabFn : Lean.Elab.Tactic.Tactic :=
      fun
        | `(tactic|$pat) => $rhs
        | _ => throwUnsupportedSyntax)
  else
    -- We considered making the command extensible and support new user-defined categories. We think it is unnecessary.
    -- If users want this feature, they add their own `elab` macro that uses this one as a fallback.
    throwError! "unsupported syntax category '{catName}'"

@[builtinCommandElab «elab»] def elabElab : CommandElab :=
  adaptExpander fun stx => do
    expandElab (← getCurrNamespace) stx

end Lean.Elab.Command
