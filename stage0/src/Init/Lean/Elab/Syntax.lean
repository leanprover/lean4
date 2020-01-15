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

partial def toParserDescr : Syntax → TermElabM Syntax
| stx =>
  let kind := stx.getKind;
  if kind == nullKind then do
     args ← stx.getArgs.mapM toParserDescr;
     mkParserSeq args
  else if kind == choiceKind then do
    toParserDescr (stx.getArg 0)
  else if kind == `Lean.Parser.Syntax.paren then
    toParserDescr (stx.getArg 1)
  else if kind == `Lean.Parser.Syntax.cat then do
    let cat : Name := stx.getIdAt 0;
    let rbp : Nat  := (getOptNum (stx.getArg 1)).getD 0;
    env ← getEnv;
    unless (Parser.isParserCategory env cat) $ throwError (stx.getArg 3) ("unknown category '" ++ cat ++ "'");
    `(ParserDescr.parser $(quote cat) $(quote rbp))
  else if kind == `Lean.Parser.Syntax.atom then do
    match (stx.getArg 0).isStrLit? with
    | some atom =>
      let rbp : Option Nat  := getOptNum (stx.getArg 1);
      `(ParserDescr.symbol $(quote atom) $(quote rbp))
    | none => throwUnsupportedSyntax
  else if kind == `Lean.Parser.Syntax.num then
    `(ParserDescr.num)
  else if kind == `Lean.Parser.Syntax.str then
    `(ParserDescr.str)
  else if kind == `Lean.Parser.Syntax.char then
    `(ParserDescr.char)
  else if kind == `Lean.Parser.Syntax.ident then
    `(ParserDescr.ident)
  else if kind == `Lean.Parser.Syntax.try then do
    d ← toParserDescr $ stx.getArg 1;
    `(ParserDescr.try $d)
  else if kind == `Lean.Parser.Syntax.lookahead then do
    d ← toParserDescr $ stx.getArg 1;
    `(ParserDescr.lookahead $d)
  else if kind == `Lean.Parser.Syntax.optional then do
    d ← toParserDescr $ stx.getArg 1;
    `(ParserDescr.optional $d)
  else if kind == `Lean.Parser.Syntax.sepBy then do
    d₁ ← toParserDescr $ stx.getArg 1;
    d₂ ← toParserDescr $ stx.getArg 2;
    `(ParserDescr.sepBy $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.sepBy1 then do
    d₁ ← toParserDescr $ stx.getArg 1;
    d₂ ← toParserDescr $ stx.getArg 2;
    `(ParserDescr.sepBy1 $d₁ $d₂)
  else if kind == `Lean.Parser.Syntax.many then do
    d ← toParserDescr $ stx.getArg 0;
    `(ParserDescr.many $d)
  else if kind == `Lean.Parser.Syntax.many1 then do
    d ← toParserDescr $ stx.getArg 0;
    `(ParserDescr.many1 $d)
  else if kind == `Lean.Parser.Syntax.orelse then do
    d₁ ← toParserDescr $ stx.getArg 0;
    d₂ ← toParserDescr $ stx.getArg 2;
    `(ParserDescr.orelse $d₁ $d₂)
  else
    throwError stx ("ERROR " ++ toString stx)
    -- throwUnsupportedSyntax

end Term

namespace Command

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab :=
fun stx => do
  let catName  := stx.getIdAt 1;
  let attrName := catName.appendAfter "Parser";
  env ← getEnv;
  env ← liftIO stx $ Parser.registerParserCategory env attrName catName;
  setEnv env

@[builtinCommandElab syntax] def elabSyntax : CommandElab :=
fun stx => do
  env ← getEnv;
  let cat := stx.getIdAt 3;
  unless (Parser.isParserCategory env cat) $ throwError (stx.getArg 3) ("unknown category '" ++ cat ++ "'");
  let (env, kind) := Parser.mkFreshKind env cat;
  setEnv env;
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser");
  type ← `(Lean.ParserDescr);
  val  ← runTermElabM none $ fun _ => Term.toParserDescr (stx.getArg 1);
  d ← `(@[$catParserId:ident] private def $catParserId:ident : $type := ParserDescr.node $(quote kind) $val);
  trace `Elab stx $ fun _ => d;
  withMacroExpansion stx $ elabCommand d

end Command
end Elab
end Lean
