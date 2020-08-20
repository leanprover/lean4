/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-!
Set up pretty printer compilers for the next stage.
-/

import Lean.PrettyPrinter.Parenthesizer
import Lean.ParserCompiler

namespace Lean
namespace PrettyPrinter

open Lean.ParserCompiler

namespace Parenthesizer

--constant interpretParserDescr : ParserDescr → StateT Environment IO Parenthesizer := arbitrary _

def ctx (interp) : ParserCompiler.Context Parenthesizer :=
⟨`parenthesizer, parenthesizerAttribute, combinatorParenthesizerAttribute, interp⟩

unsafe def interpretParserDescr : ParserDescr → StateT Environment IO Parenthesizer
| ParserDescr.andthen d₁ d₂                       => andthen.parenthesizer <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.orelse d₁ d₂                        => orelse.parenthesizer <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.optional d                          => optional.parenthesizer <$> interpretParserDescr d
| ParserDescr.lookahead d                         => lookahead.parenthesizer <$> interpretParserDescr d
| ParserDescr.try d                               => try.parenthesizer <$> interpretParserDescr d
| ParserDescr.many d                              => many.parenthesizer <$> interpretParserDescr d
| ParserDescr.many1 d                             => many1.parenthesizer <$> interpretParserDescr d
| ParserDescr.sepBy d₁ d₂                         => sepBy.parenthesizer <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.sepBy1 d₁ d₂                        => sepBy1.parenthesizer <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.node k prec d                       => leadingNode.parenthesizer k prec <$> interpretParserDescr d
| ParserDescr.trailingNode k prec d               => trailingNode.parenthesizer k prec <$> interpretParserDescr d
| ParserDescr.symbol tk                           => pure $ symbol.parenthesizer
| ParserDescr.numLit                              => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "numLit" `numLit) numLitNoAntiquot.parenthesizer
| ParserDescr.strLit                              => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "strLit" `strLit) strLitNoAntiquot.parenthesizer
| ParserDescr.charLit                             => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "charLit" `charLit) charLitNoAntiquot.parenthesizer
| ParserDescr.nameLit                             => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "nameLit" `nameLit) nameLitNoAntiquot.parenthesizer
| ParserDescr.ident                               => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "ident" `ident) identNoAntiquot.parenthesizer
| ParserDescr.nonReservedSymbol tk includeIdent   => pure $ nonReservedSymbol.parenthesizer
| ParserDescr.parser constName                    => do
  env ← get;
  p ← match combinatorParenthesizerAttribute.getDeclFor env constName with
  | some p => pure p
  | none   => do {
    (Expr.const p _ _, env) ← liftM $ IO.runMeta (compileParserBody (ctx interpretParserDescr) (mkConst constName)) env
      | unreachable!;
    set env;
    pure p
  };
  env ← get;
  liftM $ IO.ofExcept $ env.evalConstCheck Parenthesizer `Lean.PrettyPrinter.Parenthesizer p
| ParserDescr.cat catName prec                    => pure $ categoryParser.parenthesizer catName prec

@[init] unsafe def regHook : IO Unit :=
ParserCompiler.registerParserCompiler (ctx interpretParserDescr)

end Parenthesizer

end PrettyPrinter
end Lean
