/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.Quotation

namespace Lean.Elab.Term
/-
Expand `optional «precedence»` where
 «precedence» := parser! " : " >> precedenceLit
 precedenceLit : Parser := numLit <|> maxSymbol
 maxSymbol := parser! nonReservedSymbol "max" -/
def expandOptPrecedence (stx : Syntax) : Option Nat :=
  if stx.isNone then
    none
  else match stx[0][1].isNatLit? with
    | some v => some v
    | _      => some Parser.maxPrec

private def mkParserSeq (ds : Array Syntax) : TermElabM Syntax := do
  if ds.size == 0 then
    throwUnsupportedSyntax
  else if ds.size == 1 then
    pure ds[0]
  else
    let r := ds[0]
    for d in ds[1:ds.size] do
      r ← `(ParserDescr.andthen $r $d)
    return r

structure ToParserDescrContext :=
  (catName              : Name)
  (first                : Bool)
  (leftRec              : Bool) -- true iff left recursion is allowed
  /- When `leadingIdentAsSymbol == true` we convert
     `Lean.Parser.Syntax.atom` into `Lean.ParserDescr.nonReservedSymbol`
     See comment at `Parser.ParserCategory`. -/
  (leadingIdentAsSymbol : Bool)

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateRefT Bool TermElabM)
private def markAsTrailingParser : ToParserDescrM Unit := set true

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with first := false }) x

@[inline] private def withoutLeftRec {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with leftRec := false }) x

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
  let ctx ← read
  if ctx.first && stx.getKind == `Lean.Parser.Syntax.cat then
    let cat := stx[0].getId.eraseMacroScopes
    if cat == ctx.catName then
      let prec? : Option Nat  := expandOptPrecedence stx[1]
      unless prec?.isNone do throwErrorAt stx[1] ("invalid occurrence of ':<num>' modifier in head")
      unless ctx.leftRec do
        throwErrorAt! stx[3] "invalid occurrence of '{cat}', parser algorithm does not allow this form of left recursion"
      markAsTrailingParser -- mark as trailing par
      pure true
    else
      pure false
  else
    pure false

partial def toParserDescrAux (stx : Syntax) : ToParserDescrM Syntax := do
  let kind := stx.getKind
  if kind == nullKind then
    let args := stx.getArgs
    if (← checkLeftRec stx[0]) then
      if args.size == 1 then throwErrorAt stx "invalid atomic left recursive syntax"
      let args := args.eraseIdx 0
      let args ← args.mapIdxM fun i arg => withNotFirst $ toParserDescrAux arg
      mkParserSeq args
    else
      let args ← args.mapIdxM fun i arg => withNotFirst $ toParserDescrAux arg
      mkParserSeq args
  else if kind == choiceKind then
    toParserDescrAux stx[0]
  else if kind == `Lean.Parser.Syntax.paren then
    toParserDescrAux stx[1]
  else if kind == `Lean.Parser.Syntax.cat then
    let cat := stx[0].getId.eraseMacroScopes
    let ctx ← read
    if ctx.first && cat == ctx.catName then
      throwErrorAt stx "invalid atomic left recursive syntax"
    else
      let prec? : Option Nat  := expandOptPrecedence stx[1]
      let env ← getEnv
      if Parser.isParserCategory env cat then
        let prec := prec?.getD 0
        `(ParserDescr.cat $(quote cat) $(quote prec))
      else
        -- `cat` is not a valid category name. Thus, we test whether it is a valid constant
        let candidates ← resolveGlobalConst cat
        let candidates := candidates.filter fun c =>
            match env.find? c with
            | none      => false
            | some info =>
              match info.type with
              | Expr.const `Lean.Parser.TrailingParser _ _ => true
              | Expr.const `Lean.Parser.Parser _ _         => true
              | Expr.const `Lean.ParserDescr _ _           => true
              | Expr.const `Lean.TrailingParserDescr _ _   => true
              | _                                          => false
         match candidates with
         | []  => throwErrorAt! stx[3] "unknown category '{cat}' or parser declaration"
         | [c] =>
           unless prec?.isNone do throwErrorAt stx[3] "unexpected precedence"
           `(ParserDescr.parser $(quote c))
         | cs  => throwErrorAt! stx[3] "ambiguous parser declaration {cs}"
  else if kind == `Lean.Parser.Syntax.atom then
    match stx[0].isStrLit? with
    | some atom =>
      if (← read).leadingIdentAsSymbol then
        `(ParserDescr.nonReservedSymbol $(quote atom) false)
      else
        `(ParserDescr.symbol $(quote atom))
    | none => throwUnsupportedSyntax
  else if kind == `Lean.Parser.Syntax.num then
    `(ParserDescr.numLit)
  else if kind == `Lean.Parser.Syntax.str then
    `(ParserDescr.strLit)
  else if kind == `Lean.Parser.Syntax.char then
    `(ParserDescr.charLit)
  else if kind == `Lean.Parser.Syntax.ident then
    `(ParserDescr.ident)
  else if kind == `Lean.Parser.Syntax.noWs then
    `(ParserDescr.noWs)
  else if kind == `Lean.Parser.Syntax.try then
    let d ← withoutLeftRec $ toParserDescrAux stx[1]
    `(ParserDescr.try $d)
  else if kind == `Lean.Parser.Syntax.notFollowedBy then
    let d ← withoutLeftRec $ toParserDescrAux stx[1]
    `(ParserDescr.notFollowedBy $d)
  else if kind == `Lean.Parser.Syntax.lookahead then
    let d ← withoutLeftRec $ toParserDescrAux stx[1]
    `(ParserDescr.lookahead $d)
  else if kind == `Lean.Parser.Syntax.interpolatedStr then
    let d ← withoutLeftRec $ toParserDescrAux stx[1]
    `(ParserDescr.interpolatedStr $d)
  else if kind == `Lean.Parser.Syntax.sepBy then
    let d₁ ← withoutLeftRec $ toParserDescrAux stx[1]
    let d₂ ← withoutLeftRec $ toParserDescrAux stx[2]
    `(ParserDescr.sepBy $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.sepBy1 then
    let d₁ ← withoutLeftRec $ toParserDescrAux stx[1]
    let d₂ ← withoutLeftRec $ toParserDescrAux stx[2]
    `(ParserDescr.sepBy1 $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.many then
    let d ← withoutLeftRec $ toParserDescrAux stx[0]
    `(ParserDescr.many $d)
  else if kind == `Lean.Parser.Syntax.many1 then
    let d ← withoutLeftRec $ toParserDescrAux stx[0]
    `(ParserDescr.many1 $d)
  else if kind == `Lean.Parser.Syntax.optional then
    let d ← withoutLeftRec $ toParserDescrAux stx[0]
    `(ParserDescr.optional $d)
  else if kind == `Lean.Parser.Syntax.orelse then
    let d₁ ← withoutLeftRec $ toParserDescrAux stx[0]
    let d₂ ← withoutLeftRec $ toParserDescrAux stx[2]
    `(ParserDescr.orelse $d₁ $d₂)
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
  let leadingIdentAsSymbol := Parser.leadingIdentAsSymbol env catName
  (toParserDescrAux stx { catName := catName, first := true, leftRec := true, leadingIdentAsSymbol := leadingIdentAsSymbol }).run false

end Term

namespace Command

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
        (Lean.ParserDescr.andthen (Lean.ParserDescr.symbol $(quote quotSymbol))
          (Lean.ParserDescr.andthen (Lean.ParserDescr.cat $(quote catName) 0) (Lean.ParserDescr.symbol ")"))))
  elabCommand cmd

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab := fun stx => do
  let catName  := stx[1].getId
  let attrName := catName.appendAfter "Parser"
  let env ← getEnv
  let env ← liftIO $ Parser.registerParserCategory env attrName catName
  setEnv env
  declareSyntaxCatQuotParser catName

def mkFreshKind (catName : Name) : MacroM Name :=
  Macro.addMacroScope (`_kind ++ catName.eraseMacroScopes)

private def elabKindPrio (stx : Syntax) (catName : Name) : CommandElabM (Name × Nat) := do
  if stx.isNone then
    let k ← liftMacroM $ mkFreshKind catName
    pure (k, 0)
  else
    let arg := stx[1]
    if arg.getKind == `Lean.Parser.Command.parserKind then
      let k := arg[0].getId
      pure (k, 0)
    else if arg.getKind == `Lean.Parser.Command.parserPrio then
      let k ← liftMacroM $ mkFreshKind catName
      let prio := arg[0].isNatLit?.getD 0
      pure (k, prio)
    else if arg.getKind == `Lean.Parser.Command.parserKindPrio then
      let k := arg[0].getId
      let prio := arg[2].isNatLit?.getD 0
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
def «syntax»      := parser! "syntax " >> optPrecedence >> optKindPrio >> many1 syntaxParser >> " : " >> ident
-/
@[builtinCommandElab «syntax»] def elabSyntax : CommandElab := fun stx => do
  let env ← getEnv
  let cat := stx[5].getId.eraseMacroScopes
  unless (Parser.isParserCategory env cat) do throwErrorAt stx[5] ("unknown category '" ++ cat ++ "'")
  let syntaxParser := stx[3]
  -- If the user did not provide an explicit precedence, we assign `maxPrec` to atom-like syntax and `leadPrec` otherwise.
  let precDefault  := if isAtomLikeSyntax syntaxParser then Parser.maxPrec else Parser.leadPrec
  let prec := (Term.expandOptPrecedence stx[1]).getD precDefault
  let (kind, prio) ← elabKindPrio stx[2] cat
  /-
    The declaration name and the syntax node kind should be the same.
    We are using `def $kind ...`. So, we must append the current namespace to create the name fo the Syntax `node`. -/
  let stxNodeKind := (← getCurrNamespace) ++ kind
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser")
  let (val, trailingParser) ← runTermElabM none fun _ => Term.toParserDescr syntaxParser cat
  let d ←
    if trailingParser then
      `(@[$catParserId:ident $(quote prio):numLit] def $(mkIdentFrom stx kind) : Lean.TrailingParserDescr :=
         ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $val)
    else
      `(@[$catParserId:ident $(quote prio):numLit] def $(mkIdentFrom stx kind) : Lean.ParserDescr :=
         ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)
  trace `Elab fun _ => d
  withMacroExpansion stx d $ elabCommand d

/-
def syntaxAbbrev  := parser! "syntax " >> ident >> " := " >> many1 syntaxParser
-/
@[builtinCommandElab «syntaxAbbrev»] def elabSyntaxAbbrev : CommandElab := fun stx => do
  let declName := stx[1]
  let (val, _) ← runTermElabM none $ fun _ => Term.toParserDescr stx[3] Name.anonymous
  let stx' ← `(def $declName : Lean.ParserDescr := $val)
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
     fun stx => match_syntax stx with $alts:matchAlt* | _ => throw Lean.Macro.Exception.unsupportedSyntax)

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
      `($defCmd:command macro_rules $altsNotK:matchAlt*)

@[builtinCommandElab «macro_rules»] def elabMacroRules : CommandElab :=
  adaptExpander fun stx => match_syntax stx with
  | `(macro_rules $alts:matchAlt*)           => elabNoKindMacroRulesAux alts
  | `(macro_rules | $alts:matchAlt*)         => elabNoKindMacroRulesAux alts
  | `(macro_rules [$kind] $alts:matchAlt*)   => do elabMacroRulesAux ((← getCurrNamespace) ++ kind.getId) alts
  | `(macro_rules [$kind] | $alts:matchAlt*) => do elabMacroRulesAux ((← getCurrNamespace) ++ kind.getId) alts
  | _                                        => throwUnsupportedSyntax

@[builtinMacro Lean.Parser.Command.mixfix] def expandMixfix : Macro :=
  fun stx => match_syntax stx with
  | `(infix:$prec $op => $f)   => `(infixl:$prec $op => $f)
  | `(infixr:$prec $op => $f)  => `(notation:$prec lhs $op:strLit rhs:$prec => $f lhs rhs)
  | `(infixl:$prec $op => $f)  =>  let prec1 : Syntax := quote (prec.toNat+1); `(notation:$prec lhs $op:strLit rhs:$prec1 => $f lhs rhs)
  | `(prefix:$prec $op => $f)  => `(notation:$prec $op:strLit arg:$prec => $f arg)
  | `(postfix:$prec $op => $f) => `(notation:$prec arg $op:strLit => $f arg)
  | _ => Macro.throwUnsupported

/- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
  | stx => match_syntax stx with
  | `($id:ident) =>
    if (vars.findIdx? (fun var => var.getId == id.getId)).isSome then
      Syntax.node `antiquot #[mkAtom "$", mkNullNode, id, mkNullNode, mkNullNode]
    else
      stx
  | _ => match stx with
    | Syntax.node k args => Syntax.node k (args.map (antiquote vars))
    | stx => stx

/- Convert `notation` command lhs item into a `syntax` command item -/
def expandNotationItemIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    pure $ Syntax.node `Lean.Parser.Syntax.cat #[mkIdentFrom stx `term,  stx[1]]
  else if k == strLitKind then
    pure $ Syntax.node `Lean.Parser.Syntax.atom #[stx]
  else
    Macro.throwUnsupported

def strLitToPattern (stx: Syntax) : MacroM Syntax :=
  match stx.isStrLit? with
  | some str => pure $ mkAtomFrom stx str
  | none     => Macro.throwUnsupported

/- Convert `notation` command lhs item a pattern element -/
def expandNotationItemIntoPattern (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    let item := stx[0]
    pure $ mkNode `antiquot #[mkAtom "$", mkNullNode, item, mkNullNode, mkNullNode]
  else if k == strLitKind then
    strLitToPattern stx
  else
    Macro.throwUnsupported

private def expandNotationAux (ref : Syntax) (currNamespace : Name) (prec? : Option Syntax) (items : Array Syntax) (rhs : Syntax) : MacroM Syntax := do
  let kind ← mkFreshKind `term
  -- build parser
  let syntaxParts ← items.mapM expandNotationItemIntoSyntaxItem
  let cat := mkIdentFrom ref `term
  -- build macro rules
  let vars := items.filter fun item => item.getKind == `Lean.Parser.Command.identPrec
  let vars := vars.map fun var => var[0]
  let rhs := antiquote vars rhs
  let patArgs ← items.mapM expandNotationItemIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let pat := Syntax.node (currNamespace ++ kind) patArgs
  match prec? with
  | none      => `(syntax [$(mkIdentFrom ref kind):ident] $syntaxParts* : $cat macro_rules | `($pat) => `($rhs))
  | some prec => `(syntax:$prec [$(mkIdentFrom ref kind):ident] $syntaxParts* : $cat macro_rules | `($pat) => `($rhs))

@[builtinCommandElab «notation»] def expandNotation : CommandElab :=
  adaptExpander fun stx => do
    let currNamespace ← getCurrNamespace
    match_syntax stx with
    | `(notation:$prec $items* => $rhs)        => liftMacroM $ expandNotationAux stx currNamespace prec items rhs
    | `(notation $items:notationItem* => $rhs) => liftMacroM $ expandNotationAux stx currNamespace none items rhs
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

/- Convert `macro` head into a `syntax` command item -/
def expandMacroHeadIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
  if stx.isIdent then
    let info := stx.getHeadInfo.getD {}
    let id   := stx.getId
    pure $ Syntax.node `Lean.Parser.Syntax.atom #[mkStxStrLit (toString id) info]
  else
    expandMacroArgIntoSyntaxItem stx

/- Convert `macro` arg into a pattern element -/
def expandMacroArgIntoPattern (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.macroArgSimple then
    let item := stx[0]
    pure $ mkNode `antiquot #[mkAtom "$", mkNullNode, item, mkNullNode, mkNullNode]
  else if k == strLitKind then
    strLitToPattern stx
  else
    Macro.throwUnsupported

/- Convert `macro` head into a pattern element -/
def expandMacroHeadIntoPattern (stx : Syntax) : MacroM Syntax :=
  if stx.isIdent then
    pure $ mkAtomFrom stx (toString stx.getId)
  else
    expandMacroArgIntoPattern stx

def expandOptPrio (stx : Syntax) : Nat :=
  if stx.isNone then
    0
  else
    stx[1].isNatLit?.getD 0

def expandMacro (currNamespace : Name) (stx : Syntax) : MacroM Syntax := do
  let prec := stx[1].getArgs
  let prio := expandOptPrio stx[2]
  let head := stx[3]
  let args := stx[4].getArgs
  let cat  := stx[6]
  let kind ← mkFreshKind cat.getId
  -- build parser
  let stxPart  ← expandMacroHeadIntoSyntaxItem head
  let stxParts ← args.mapM expandMacroArgIntoSyntaxItem
  let stxParts := #[stxPart] ++ stxParts
  -- build macro rules
  let patHead ← expandMacroHeadIntoPattern head
  let patArgs ← args.mapM expandMacroArgIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let pat := Syntax.node (currNamespace ++ kind) (#[patHead] ++ patArgs)
  if stx.getArgs.size == 9 then
    -- `stx` is of the form `macro $head $args* : $cat => term`
    let rhs := stx[8]
    `(syntax $prec* [$(mkIdentFrom stx kind):ident, $(quote prio):numLit] $stxParts* : $cat
      macro_rules | `($pat) => $rhs)
  else
    -- `stx` is of the form `macro $head $args* : $cat => `( $body )`
    let rhsBody := stx[9]
    `(syntax $prec* [$(mkIdentFrom stx kind):ident, $(quote prio):numLit] $stxParts* : $cat
      macro_rules | `($pat) => `($rhsBody))

@[builtinCommandElab «macro»] def elabMacro : CommandElab :=
  adaptExpander fun stx => do
    liftMacroM $ expandMacro (← getCurrNamespace) stx

builtin_initialize
  registerTraceClass `Elab.syntax

@[inline] def withExpectedType (expectedType? : Option Expr) (x : Expr → TermElabM Expr) : TermElabM Expr := do
  Term.tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← pure expectedType?
    | throwError "expected type must be known"
  x expectedType

/-
def elabTail := try (" : " >> ident) >> darrow >> termParser
parser! "elab " >> optPrecedence >> elabHead >> many elabArg >> elabTail
-/
def expandElab (currNamespace : Name) (stx : Syntax) : MacroM Syntax := do
  let ref := stx
  let prec    := stx[1].getArgs
  let prio    := expandOptPrio stx[2]
  let head    := stx[3]
  let args    := stx[4].getArgs
  let cat     := stx[6]
  let expectedTypeSpec := stx[7]
  let rhs     := stx[9]
  let catName := cat.getId
  let kind ← mkFreshKind catName
  -- build parser
  let stxPart  ← expandMacroHeadIntoSyntaxItem head
  let stxParts ← args.mapM expandMacroArgIntoSyntaxItem
  let stxParts := #[stxPart] ++ stxParts
  -- build pattern for `martch_syntax
  let patHead ← expandMacroHeadIntoPattern head
  let patArgs ← args.mapM expandMacroArgIntoPattern
  let pat := Syntax.node (currNamespace ++ kind) (#[patHead] ++ patArgs)
  let kindId    := mkIdentFrom ref kind
  if expectedTypeSpec.hasArgs then
    if catName == `term then
      let expId := expectedTypeSpec[1]
      `(syntax $prec* [$kindId:ident, $(quote prio):numLit] $stxParts* : $cat
        @[termElab $kindId:ident] def elabFn : Lean.Elab.Term.TermElab :=
        fun stx expectedType? => match_syntax stx with
          | `($pat) => Lean.Elab.Command.withExpectedType expectedType? fun $expId => $rhs
          | _ => throwUnsupportedSyntax)
    else
      Macro.throwError expectedTypeSpec s!"syntax category '{catName}' does not support expected type specification"
  else if catName == `term then
    `(syntax $prec* [$kindId:ident, $(quote prio):numLit] $stxParts* : $cat
      @[termElab $kindId:ident] def elabFn : Lean.Elab.Term.TermElab :=
      fun stx _ => match_syntax stx with
        | `($pat) => $rhs
        | _ => throwUnsupportedSyntax)
  else if catName == `command then
    `(syntax $prec* [$kindId:ident, $(quote prio):numLit] $stxParts* : $cat
      @[commandElab $kindId:ident] def elabFn : Lean.Elab.Command.CommandElab :=
      fun stx => match_syntax stx with
        | `($pat) => $rhs
        | _ => throwUnsupportedSyntax)
  else if catName == `tactic then
    `(syntax $prec* [$kindId:ident, $(quote prio):numLit] $stxParts* : $cat
      @[tactic $kindId:ident] def elabFn : Lean.Elab.Tactic.Tactic :=
      fun stx => match_syntax stx with
        | `(tactic|$pat) => $rhs
        | _ => throwUnsupportedSyntax)
  else
    -- We considered making the command extensible and support new user-defined categories. We think it is unnecessary.
    -- If users want this feature, they add their own `elab` macro that uses this one as a fallback.
    Macro.throwError ref s!"unsupported syntax category '{catName}'"

@[builtinCommandElab «elab»] def elabElab : CommandElab :=
  adaptExpander fun stx => do
    liftMacroM $ expandElab (← getCurrNamespace) stx

end Lean.Elab.Command
