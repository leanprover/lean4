/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Command
import Lean.Elab.Quotation

namespace Lean
namespace Elab

namespace Term

/-
Expand `optional «precedence»` where
 «precedence» := parser! " : " >> precedenceLit
 precedenceLit : Parser := numLit <|> maxSymbol
 maxSymbol := parser! nonReservedSymbol "max" -/
def expandOptPrecedence (stx : Syntax) : Option Nat :=
if stx.isNone then none
else match ((stx.getArg 0).getArg 1).isNatLit? with
  | some v => some v
  | _      => some Parser.maxPrec

private def mkParserSeq (ds : Array Syntax) : TermElabM Syntax :=
if ds.size == 0 then
  throwUnsupportedSyntax
else if ds.size == 1 then
  pure $ ds.get! 0
else
  ds.foldlFromM (fun r d => `(ParserDescr.andthen $r $d)) (ds.get! 0) 1

structure ToParserDescrContext :=
(catName              : Name)
(first                : Bool)
(leftRec              : Bool) -- true iff left recursion is allowed
/- When `leadingIdentAsSymbol == true` we convert
   `Lean.Parser.Syntax.atom` into `Lean.ParserDescr.nonReservedSymbol`
   See comment at `Parser.ParserCategory`. -/
(leadingIdentAsSymbol : Bool)

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateT Bool TermElabM)
private def markAsTrailingParser : ToParserDescrM Unit := set true

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
adaptReader (fun (ctx : ToParserDescrContext) => { ctx with first := false }) x

@[inline] private def withoutLeftRec {α} (x : ToParserDescrM α) : ToParserDescrM α :=
adaptReader (fun (ctx : ToParserDescrContext) => { ctx with leftRec := false }) x

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
ctx ← read;
if ctx.first && stx.getKind == `Lean.Parser.Syntax.cat then do
  let cat := (stx.getIdAt 0).eraseMacroScopes;
  if cat == ctx.catName then do
    let prec? : Option Nat  := expandOptPrecedence (stx.getArg 1);
    unless prec?.isNone $ liftM $ throwError (stx.getArg 1) ("invalid occurrence of ':<num>' modifier in head");
    unless ctx.leftRec $ liftM $
      throwError (stx.getArg 3) ("invalid occurrence of '" ++ cat ++ "', parser algorithm does not allow this form of left recursion");
    markAsTrailingParser; -- mark as trailing par
    pure true
  else
    pure false
else
  pure false

partial def toParserDescrAux : Syntax → ToParserDescrM Syntax
| stx =>
  let kind := stx.getKind;
  if kind == nullKind then do
    let args := stx.getArgs;
    condM (checkLeftRec (stx.getArg 0))
      (do
        when (args.size == 1) $ liftM $ throwError stx "invalid atomic left recursive syntax";
        let args := args.eraseIdx 0;
        args ← args.mapIdxM $ fun i arg => withNotFirst $ toParserDescrAux arg;
        liftM $ mkParserSeq args)
      (do
        args ← args.mapIdxM $ fun i arg => withNotFirst $ toParserDescrAux arg;
        liftM $ mkParserSeq args)
  else if kind == choiceKind then do
    toParserDescrAux (stx.getArg 0)
  else if kind == `Lean.Parser.Syntax.paren then
    toParserDescrAux (stx.getArg 1)
  else if kind == `Lean.Parser.Syntax.cat then do
    let cat := (stx.getIdAt 0).eraseMacroScopes;
    ctx ← read;
    if ctx.first && cat == ctx.catName then
      liftM $ throwError stx "invalid atomic left recursive syntax"
    else do
      let prec? : Option Nat  := expandOptPrecedence (stx.getArg 1);
      env ← liftM getEnv;
      if Parser.isParserCategory env cat then
        let prec := prec?.getD 0;
        `(ParserDescr.cat $(quote cat) $(quote prec))
      else do
        -- `cat` is not a valid category name. Thus, we test whether it is a valid constant
        candidates ← liftM $ resolveGlobalName cat;
        let candidates := candidates.filter fun ⟨c, ps⟩ =>
          ps.isEmpty &&
            match env.find? c with
            | none      => false
            | some info =>
              match info.type with
              | Expr.const `Lean.Parser.TrailingParser _ _ => true
              | Expr.const `Lean.Parser.Parser _ _         => true
              | Expr.const `Lean.ParserDescr _ _           => true
              | Expr.const `Lean.TrailingParserDescr _ _   => true
              | _                                          => false;
         let candidates := candidates.map fun ⟨c, _⟩ => c;
         match candidates with
         | []  => liftM $ throwError (stx.getArg 3) ("unknown category '" ++ cat ++ "' or parser declaration")
         | [c] => `(ParserDescr.parser $(quote c))
         | cs  => liftM $ throwError (stx.getArg 3) ("ambiguous parser declaration " ++ toString cs)
  else if kind == `Lean.Parser.Syntax.atom then do
    match (stx.getArg 0).isStrLit? with
    | some atom => do
      ctx ← read;
      if ctx.leadingIdentAsSymbol then
        `(ParserDescr.nonReservedSymbol $(quote atom) false)
      else
        `(ParserDescr.symbol $(quote atom))
    | none => liftM throwUnsupportedSyntax
  else if kind == `Lean.Parser.Syntax.num then
    `(ParserDescr.numLit)
  else if kind == `Lean.Parser.Syntax.str then
    `(ParserDescr.strLit)
  else if kind == `Lean.Parser.Syntax.char then
    `(ParserDescr.charLit)
  else if kind == `Lean.Parser.Syntax.ident then
    `(ParserDescr.ident)
  else if kind == `Lean.Parser.Syntax.try then do
    d ← withoutLeftRec $ toParserDescrAux (stx.getArg 1);
    `(ParserDescr.try $d)
  else if kind == `Lean.Parser.Syntax.lookahead then do
    d ← withoutLeftRec $ toParserDescrAux (stx.getArg 1);
    `(ParserDescr.lookahead $d)
  else if kind == `Lean.Parser.Syntax.sepBy then do
    d₁ ← withoutLeftRec $ toParserDescrAux (stx.getArg 1);
    d₂ ← withoutLeftRec $ toParserDescrAux (stx.getArg 2);
    `(ParserDescr.sepBy $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.sepBy1 then do
    d₁ ← withoutLeftRec $ toParserDescrAux (stx.getArg 1);
    d₂ ← withoutLeftRec $ toParserDescrAux (stx.getArg 2);
    `(ParserDescr.sepBy1 $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.many then do
    d ← withoutLeftRec $ toParserDescrAux (stx.getArg 0);
    `(ParserDescr.many $d)
  else if kind == `Lean.Parser.Syntax.many1 then do
    d ← withoutLeftRec $ toParserDescrAux (stx.getArg 0);
    `(ParserDescr.many1 $d)
  else if kind == `Lean.Parser.Syntax.optional then do
    d ← withoutLeftRec $ toParserDescrAux (stx.getArg 0);
    `(ParserDescr.optional $d)
  else if kind == `Lean.Parser.Syntax.orelse then do
    d₁ ← withoutLeftRec $ toParserDescrAux (stx.getArg 0);
    d₂ ← withoutLeftRec $ toParserDescrAux (stx.getArg 2);
    `(ParserDescr.orelse $d₁ $d₂)
  else
    liftM $ throwError stx $ "unexpected syntax kind of category `syntax`: " ++ kind

/--
  Given a `stx` of category `syntax`, return a pair `(newStx, trailingParser)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `trailingParser == true`, and `ParserDescr` otherwise. -/
def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Syntax × Bool) := do
env ← getEnv;
let leadingIdentAsSymbol := Parser.leadingIdentAsSymbol env catName;
(toParserDescrAux stx { catName := catName, first := true, leftRec := true, leadingIdentAsSymbol := leadingIdentAsSymbol }).run false

end Term

namespace Command

private def getCatSuffix (catName : Name) : String :=
match catName with
| Name.str _ s _ => s
| _              => unreachable!

private def declareSyntaxCatQuotParser (catName : Name) : CommandElabM Unit := do
let quotSymbol := "`(" ++ getCatSuffix catName ++ "|";
cmd ← `(@[termParser] def catStxQuot : Lean.ParserDescr := Lean.ParserDescr.node `Lean.Parser.Term.stxQuot $(quote Lean.Parser.maxPrec) (Lean.ParserDescr.andthen (Lean.ParserDescr.symbol $(quote quotSymbol)) (Lean.ParserDescr.andthen (Lean.ParserDescr.cat $(quote catName) 0) (Lean.ParserDescr.symbol ")"))));
elabCommand cmd

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab :=
fun stx => do
  let catName  := stx.getIdAt 1;
  let attrName := catName.appendAfter "Parser";
  env ← getEnv;
  env ← liftIO stx $ Parser.registerParserCategory env attrName catName;
  setEnv env;
  declareSyntaxCatQuotParser catName

def mkKindName (catName : Name) : Name :=
`_kind ++ catName

def mkFreshKind (catName : Name) : CommandElabM Name := do
scp ← getCurrMacroScope;
mainModule ← getMainModule;
pure $ Lean.addMacroScope mainModule (mkKindName catName) scp

def Macro.mkFreshKind (catName : Name) : MacroM Name :=
Macro.addMacroScope (mkKindName catName)

private def elabKind (stx : Syntax) (catName : Name) : CommandElabM Name := do
if stx.isNone then
  mkFreshKind catName
else
  let kind := stx.getIdAt 1;
  if kind.hasMacroScopes then
    pure kind
  else do
    currNamespace ← getCurrNamespace;
    pure (currNamespace ++ kind)

/-
def «syntax»      := parser! "syntax " >> optPrecedence >> optKind >> many1 syntaxParser >> " : " >> ident
-/
@[builtinCommandElab «syntax»] def elabSyntax : CommandElab :=
fun stx => do
  env ← getEnv;
  let cat := (stx.getIdAt 5).eraseMacroScopes;
  unless (Parser.isParserCategory env cat) $ throwError (stx.getArg 5) ("unknown category '" ++ cat ++ "'");
  let prec := (Term.expandOptPrecedence (stx.getArg 1)).getD Parser.maxPrec;
  kind ← elabKind (stx.getArg 2) cat;
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser");
  (val, trailingParser) ← runTermElabM none $ fun _ => Term.toParserDescr (stx.getArg 3) cat;
  d ←
    if trailingParser then
      `(@[$catParserId:ident] def myParser : Lean.TrailingParserDescr := ParserDescr.trailingNode $(quote kind) $(quote prec) $val)
    else
      `(@[$catParserId:ident] def myParser : Lean.ParserDescr := ParserDescr.node $(quote kind) $(quote prec) $val);
  trace `Elab stx $ fun _ => d;
  withMacroExpansion stx d $ elabCommand d

def elabMacroRulesAux (k : SyntaxNodeKind) (alts : Array Syntax) : CommandElabM Syntax := do
alts ← alts.mapSepElemsM $ fun alt => do {
  let lhs := alt.getArg 0;
  let pat := lhs.getArg 0;
  match_syntax pat with
  | `(`($quot)) =>
     let k' := quot.getKind;
     if k' == k then
       pure alt
     else if k' == choiceKind then do
        match quot.getArgs.find? $ fun quotAlt => quotAlt.getKind == k with
        | none      => throwError alt ("invalid macro_rules alternative, expected syntax node kind '" ++ k ++ "'")
        | some quot => do
          pat ← `(`($quot));
          let lhs := lhs.setArg 0 pat;
          pure $ alt.setArg 0 lhs
     else
       throwError alt ("invalid macro_rules alternative, unexpected syntax node kind '" ++ k' ++ "'")
  | stx => throwUnsupportedSyntax
};
`(@[macro $(Lean.mkIdent k)] def myMacro : Macro := fun stx => match_syntax stx with $alts:matchAlt* | _ => throw Lean.Macro.Exception.unsupportedSyntax)

def inferMacroRulesAltKind (alt : Syntax) : CommandElabM SyntaxNodeKind :=
match_syntax (alt.getArg 0).getArg 0 with
| `(`($quot)) => pure quot.getKind
| stx         => throwUnsupportedSyntax

def elabNoKindMacroRulesAux (alts : Array Syntax) : CommandElabM Syntax := do
k ← inferMacroRulesAltKind (alts.get! 0);
if k == choiceKind then
  throwError (alts.get! 0)
    "invalid macro_rules alternative, multiple interpretations for pattern (solution: specify node kind using `macro_rules [<kind>] ...`)"
else do
  altsK    ← alts.filterSepElemsM (fun alt => do k' ← inferMacroRulesAltKind alt; pure $ k == k');
  altsNotK ← alts.filterSepElemsM (fun alt => do k' ← inferMacroRulesAltKind alt; pure $ k != k');
  defCmd   ← elabMacroRulesAux k altsK;
  if altsNotK.isEmpty then
    pure defCmd
  else
    `($defCmd:command macro_rules $altsNotK:matchAlt*)

@[builtinCommandElab «macro_rules»] def elabMacroRules : CommandElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(macro_rules $alts:matchAlt*)           => elabNoKindMacroRulesAux alts
| `(macro_rules | $alts:matchAlt*)         => elabNoKindMacroRulesAux alts
| `(macro_rules [$kind] $alts:matchAlt*)   => elabMacroRulesAux kind.getId alts
| `(macro_rules [$kind] | $alts:matchAlt*) => elabMacroRulesAux kind.getId alts
| _                                        => throwUnsupportedSyntax

/- We just ignore Lean3 notation declaration commands. -/
@[builtinCommandElab «mixfix»] def elabMixfix : CommandElab := fun _ => pure ()
@[builtinCommandElab «reserve»] def elabReserve : CommandElab := fun _ => pure ()

/- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
| stx => match_syntax stx with
| `($id:ident) =>
  if (vars.findIdx? (fun var => var.getId == id.getId)).isSome then
    Syntax.node `antiquot #[mkAtom "$", mkNullNode, id, mkNullNode, mkNullNode]
  else
    stx
| _ => match stx with
  | Syntax.node k args => Syntax.node k (args.map antiquote)
  | stx => stx

/- Convert `notation` command lhs item into a `syntax` command item -/
def expandNotationItemIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
let k := stx.getKind;
if k == `Lean.Parser.Command.identPrec then
  pure $ Syntax.node `Lean.Parser.Syntax.cat #[mkIdentFrom stx `term,  stx.getArg 1]
else if k == quotedSymbolKind then
  match stx.getArg 1 with
  | Syntax.atom info val => pure $ Syntax.node `Lean.Parser.Syntax.atom #[mkStxStrLit val info]
  | _                    => Macro.throwUnsupported
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
let k := stx.getKind;
if k == `Lean.Parser.Command.identPrec then
  let item := stx.getArg 0;
  pure $ mkNode `antiquot #[mkAtom "$", mkNullNode, item, mkNullNode, mkNullNode]
else if k == quotedSymbolKind then
  pure $ stx.getArg 1
else if k == strLitKind then
  strLitToPattern stx
else
  Macro.throwUnsupported

private def expandNotationAux (ref : Syntax) (prec? : Option Syntax) (items : Array Syntax) (rhs : Syntax) : MacroM Syntax := do
kind ← Macro.mkFreshKind `term;
-- build parser
syntaxParts ← items.mapM expandNotationItemIntoSyntaxItem;
let cat := mkIdentFrom ref `term;
-- build macro rules
let vars := items.filter $ fun item => item.getKind == `Lean.Parser.Command.identPrec;
let vars := vars.map $ fun var => var.getArg 0;
let rhs := antiquote vars rhs;
patArgs ← items.mapM expandNotationItemIntoPattern;
let pat := Syntax.node kind patArgs;
match prec? with
| none      => `(syntax [$(mkIdentFrom ref kind)] $syntaxParts* : $cat macro_rules | `($pat) => `($rhs))
| some prec => `(syntax:$prec [$(mkIdentFrom ref kind)] $syntaxParts* : $cat macro_rules | `($pat) => `($rhs))

@[builtinMacro Lean.Parser.Command.notation] def expandNotation : Macro :=
fun stx =>
match_syntax stx with
| `(notation:$prec $items* => $rhs)    => expandNotationAux stx prec items rhs
| `(notation $items:notationItem* => $rhs) => expandNotationAux stx none items rhs
| _ => Macro.throwUnsupported

/- Convert `macro` argument into a `syntax` command item -/
def expandMacroArgIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
let k := stx.getKind;
if k == `Lean.Parser.Command.macroArgSimple then
  let argType := stx.getArg 2;
  match argType with
  | Syntax.atom _ "ident" => pure $ Syntax.node `Lean.Parser.Syntax.ident #[argType]
  | Syntax.atom _ "num"   => pure $ Syntax.node `Lean.Parser.Syntax.num #[argType]
  | Syntax.atom _ "str"   => pure $ Syntax.node `Lean.Parser.Syntax.str #[argType]
  | Syntax.atom _ "char"  => pure $ Syntax.node `Lean.Parser.Syntax.char #[argType]
  | Syntax.ident _ _ _ _  => pure $ Syntax.node `Lean.Parser.Syntax.cat #[stx.getArg 2,  stx.getArg 3]
  | _                     => Macro.throwUnsupported
else if k == strLitKind then
  pure $ Syntax.node `Lean.Parser.Syntax.atom #[stx]
else
  Macro.throwUnsupported

/- Convert `macro` head into a `syntax` command item -/
def expandMacroHeadIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
if stx.isIdent then
  let info := stx.getHeadInfo.getD {};
  let id   := stx.getId;
  pure $ Syntax.node `Lean.Parser.Syntax.atom #[mkStxStrLit (toString id) info]
else
  expandMacroArgIntoSyntaxItem stx

/- Convert `macro` arg into a pattern element -/
def expandMacroArgIntoPattern (stx : Syntax) : MacroM Syntax :=
let k := stx.getKind;
if k == `Lean.Parser.Command.macroArgSimple then
  let item := stx.getArg 0;
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

@[builtinMacro Lean.Parser.Command.macro] def expandMacro : Macro :=
fun stx => do
  let prec := (stx.getArg 1).getArgs;
  let head := stx.getArg 2;
  let args := (stx.getArg 3).getArgs;
  let cat  := stx.getArg 5;
  kind ← Macro.mkFreshKind (cat.getId).eraseMacroScopes;
  -- build parser
  stxPart  ← expandMacroHeadIntoSyntaxItem head;
  stxParts ← args.mapM expandMacroArgIntoSyntaxItem;
  let stxParts := #[stxPart] ++ stxParts;
  -- build macro rules
  patHead ← expandMacroHeadIntoPattern head;
  patArgs ← args.mapM expandMacroArgIntoPattern;
  let pat := Syntax.node kind (#[patHead] ++ patArgs);
  if stx.getArgs.size == 8 then
    -- `stx` is of the form `macro $head $args* : $cat => term`
    let rhs := stx.getArg 7;
    `(syntax $prec* [$(mkIdentFrom stx kind)] $stxParts* : $cat macro_rules | `($pat) => $rhs)
  else
    -- `stx` is of the form `macro $head $args* : $cat => `( $body )`
    let rhsBody := stx.getArg 8;
    `(syntax $prec* [$(mkIdentFrom stx kind)] $stxParts* : $cat macro_rules | `($pat) => `($rhsBody))

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.syntax;
pure ()

end Command
end Elab
end Lean
