/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Command
import Init.Lean.Elab.Quotation

namespace Lean
namespace Elab

namespace Term

-- optional (":" >> numLit)
private def getOptNum (stx : Syntax) : Option Nat :=
if stx.isNone then none
else (stx.getArg 1).isNatLit?

private def mkParserSeq (ds : Array Syntax) : TermElabM Syntax :=
if ds.size == 0 then
  throwUnsupportedSyntax
else if ds.size == 1 then
  pure $ ds.get! 0
else
  ds.foldlFromM (fun r d => `(ParserDescr.andthen $r $d)) (ds.get! 0) 1

/- The translator from `syntax` to `ParserDescr` syntax uses the following modes -/
inductive ToParserDescrMode
| anyCat -- Node kind `Lean.Parser.Syntax.cat` is allowed for any category
| noCat  -- Node kind `Lean.Parser.Syntax.cat` is not allowed for any category
| toPushLeading (catName : Name) -- Node kind `Lean.Parser.Syntax.cat` is allowed if the category is `catName`, and it is translated into `ParserDescr.pushLeading`

abbrev ToParserDescrM := ReaderT ToParserDescrMode (StateT Bool TermElabM)
private def getMode : ToParserDescrM ToParserDescrMode := read
private def markAsTrailingParser : ToParserDescrM Unit := set true

@[inline] private def withAnyIfNotFirst {α} (first : Bool) (x : ToParserDescrM α) : ToParserDescrM α :=
fun mode => match mode, first with
  | mode, true  => x mode
  | _,    false => x ToParserDescrMode.anyCat

@[inline] private def withNoPushLeading {α} (x : ToParserDescrM α) : ToParserDescrM α :=
fun mode => match mode with
  | ToParserDescrMode.toPushLeading _ => x ToParserDescrMode.noCat
  | mode                              => x mode

partial def toParserDescrAux : Syntax → ToParserDescrM Syntax
| stx =>
  let kind := stx.getKind;
  if kind == nullKind then do
     args ← stx.getArgs.mapIdxM $ fun i arg => withAnyIfNotFirst (i == 0) (toParserDescrAux arg);
     liftM $ mkParserSeq args
  else if kind == choiceKind then do
    toParserDescrAux (stx.getArg 0)
  else if kind == `Lean.Parser.Syntax.paren then
    toParserDescrAux (stx.getArg 1)
  else if kind == `Lean.Parser.Syntax.cat then do
    let cat : Name := stx.getIdAt 0;
    let rbp? : Option Nat  := getOptNum (stx.getArg 1);
    env ← liftM getEnv;
    unless (Parser.isParserCategory env cat) $ liftM $ throwError (stx.getArg 3) ("unknown category '" ++ cat ++ "'");
    mode ← getMode;
    match mode with
    | ToParserDescrMode.toPushLeading cat' =>
      if cat == cat' then do
        unless rbp?.isNone $ liftM $ throwError (stx.getArg 1) ("invalid occurrence of ':<num>' modifier in head");
        markAsTrailingParser; -- mark as trailing par
        `(ParserDescr.pushLeading)
      else
        liftM $ throwError (stx.getArg 3) ("invalid occurrence of '" ++ cat ++ "', '" ++ cat' ++ "', atom, or literal expected")
    | ToParserDescrMode.anyCat =>
      let rbp := rbp?.getD 0;
      `(ParserDescr.parser $(quote cat) $(quote rbp))
    | ToParserDescrMode.noCat  =>
      liftM $ throwError (stx.getArg 3) ("invalid occurrence of '" ++ cat ++ "', atom or literal expected")
  else if kind == `Lean.Parser.Syntax.atom then do
    match (stx.getArg 0).isStrLit? with
    | some atom =>
      let rbp : Option Nat  := getOptNum (stx.getArg 1);
      `(ParserDescr.symbol $(quote atom) $(quote rbp))
    | none => liftM throwUnsupportedSyntax
  else if kind == `Lean.Parser.Syntax.num then
    `(ParserDescr.num)
  else if kind == `Lean.Parser.Syntax.str then
    `(ParserDescr.str)
  else if kind == `Lean.Parser.Syntax.char then
    `(ParserDescr.char)
  else if kind == `Lean.Parser.Syntax.ident then
    `(ParserDescr.ident)
  else if kind == `Lean.Parser.Syntax.try then do
    d ← withNoPushLeading $ toParserDescrAux (stx.getArg 1);
    `(ParserDescr.try $d)
  else if kind == `Lean.Parser.Syntax.lookahead then do
    d ← withNoPushLeading $ toParserDescrAux (stx.getArg 1);
    `(ParserDescr.lookahead $d)
  else if kind == `Lean.Parser.Syntax.optional then do
    d ← withNoPushLeading $ toParserDescrAux (stx.getArg 1);
    `(ParserDescr.optional $d)
  else if kind == `Lean.Parser.Syntax.sepBy then do
    d₁ ← withNoPushLeading $ toParserDescrAux (stx.getArg 1);
    d₂ ← withNoPushLeading $ toParserDescrAux (stx.getArg 2);
    `(ParserDescr.sepBy $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.sepBy1 then do
    d₁ ← withNoPushLeading $ toParserDescrAux (stx.getArg 1);
    d₂ ← withNoPushLeading $ toParserDescrAux (stx.getArg 2);
    `(ParserDescr.sepBy1 $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.many then do
    d ← withNoPushLeading $ toParserDescrAux (stx.getArg 0);
    `(ParserDescr.many $d)
  else if kind == `Lean.Parser.Syntax.many1 then do
    d ← withNoPushLeading $ toParserDescrAux (stx.getArg 0);
    `(ParserDescr.many1 $d)
  else if kind == `Lean.Parser.Syntax.orelse then do
    d₁ ← withNoPushLeading $ toParserDescrAux (stx.getArg 0);
    d₂ ← withNoPushLeading $ toParserDescrAux (stx.getArg 2);
    `(ParserDescr.orelse $d₁ $d₂)
  else
    liftM $ throwUnsupportedSyntax

/--
  Given a `stx` of category `syntax`, return a pair `(newStx, trailingParser)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `trailingParser == true`, and `ParserDescr` otherwise. -/
def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Syntax × Bool) :=
(toParserDescrAux stx (ToParserDescrMode.toPushLeading catName)).run false

end Term

namespace Command

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab :=
fun stx => do
  let catName  := stx.getIdAt 1;
  let attrName := catName.appendAfter "Parser";
  env ← getEnv;
  env ← liftIO stx $ Parser.registerParserCategory env attrName catName;
  setEnv env

private def elabKind (stx : Syntax) (catName : Name) : CommandElabM Name := do
if stx.isNone then do
  env ← getEnv;
  let (env, kind) := Parser.mkFreshKind env catName;
  setEnv env;
  pure kind
else do
  let kind := stx.getIdAt 1;
  currNamespace ← getCurrNamespace;
  pure (currNamespace ++ kind)

@[builtinCommandElab syntax] def elabSyntax : CommandElab :=
fun stx => do
  env ← getEnv;
  let cat := stx.getIdAt 4;
  unless (Parser.isParserCategory env cat) $ throwError (stx.getArg 4) ("unknown category '" ++ cat ++ "'");
  kind ← elabKind (stx.getArg 1) cat;
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser");
  (val, trailingParser) ← runTermElabM none $ fun _ => Term.toParserDescr (stx.getArg 2) cat;
  type ← if trailingParser then `(Lean.TrailingParserDescr) else `(Lean.ParserDescr);
  -- TODO: meaningful, unhygienic def name for selective parser `open`ing?
  d ← `(@[$catParserId:ident] def myParser : $type := ParserDescr.node $(quote kind) $val);
  trace `Elab stx $ fun _ => d;
  withMacroExpansion stx $ elabCommand d

@[builtinCommandElab macro] def elabMacro : CommandElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(macro $alts*) => do
  -- TODO: clean up with matchAlt quotation
  k ← match_syntax ((alts.get! 0).getArg 1).getArg 0 with
  | `(`($quot)) => pure quot.getKind
  | stx         => throwUnsupportedSyntax;
  -- TODO: meaningful, unhygienic def name for selective macro `open`ing?
  `(@[macro $(Lean.mkSimpleIdent k)] def myMacro : Macro := fun stx => match_syntax stx with $alts* | _ => throw ())
| _ => throwUnsupportedSyntax

/- We just ignore Lean3 notation declaration commands. -/
@[builtinCommandElab «mixfix»] def elabMixfix : CommandElab := fun _ => pure ()
@[builtinCommandElab «reserve»] def elabReserve : CommandElab := fun _ => pure ()
@[builtinCommandElab «notation»] def elabNotation : CommandElab := fun _ => pure ()

end Command
end Elab
end Lean
