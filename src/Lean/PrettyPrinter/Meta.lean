/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-!
Set up pretty printer compilers for the next stage.
-/

import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter
import Lean.ParserCompiler

namespace Lean
namespace PrettyPrinter

open Lean.ParserCompiler

namespace Parenthesizer

def ctx (interp) : ParserCompiler.Context Parenthesizer :=
⟨`parenthesizer, parenthesizerAttribute, combinatorParenthesizerAttribute, interp⟩

unsafe def interpretParserDescr : ParserDescr → AttrM Parenthesizer
| ParserDescr.andthen d₁ d₂                       => andthen.parenthesizer <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.orelse d₁ d₂                        => orelse.parenthesizer <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.optional d                          => optional.parenthesizer <$> interpretParserDescr d
| ParserDescr.lookahead d                         => lookahead.parenthesizer <$> interpretParserDescr d
| ParserDescr.try d                               => try.parenthesizer <$> interpretParserDescr d
| ParserDescr.notFollowedBy d                     => notFollowedBy.parenthesizer <$> interpretParserDescr d
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
| ParserDescr.parser constName                    => interpretParser (ctx interpretParserDescr) constName
| ParserDescr.cat catName prec                    => pure $ categoryParser.parenthesizer catName prec

@[init] unsafe def regHook : IO Unit :=
ParserCompiler.registerParserCompiler (ctx interpretParserDescr)

end Parenthesizer

namespace Formatter

def ctx (interp) : ParserCompiler.Context Formatter :=
⟨`formatter, formatterAttribute, combinatorFormatterAttribute, interp⟩

unsafe def interpretParserDescr : ParserDescr → AttrM Formatter
| ParserDescr.andthen d₁ d₂                       => andthen.formatter <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.orelse d₁ d₂                        => orelse.formatter <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.optional d                          => optional.formatter <$> interpretParserDescr d
| ParserDescr.lookahead d                         => lookahead.formatter <$> interpretParserDescr d
| ParserDescr.try d                               => try.formatter <$> interpretParserDescr d
| ParserDescr.notFollowedBy d                     => notFollowedBy.formatter <$> interpretParserDescr d
| ParserDescr.many d                              => many.formatter <$> interpretParserDescr d
| ParserDescr.many1 d                             => many1.formatter <$> interpretParserDescr d
| ParserDescr.sepBy d₁ d₂                         => sepBy.formatter <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.sepBy1 d₁ d₂                        => sepBy1.formatter <$> interpretParserDescr d₁ <*> interpretParserDescr d₂
| ParserDescr.node k prec d                       => node.formatter k <$> interpretParserDescr d
| ParserDescr.trailingNode k prec d               => trailingNode.formatter k prec <$> interpretParserDescr d
| ParserDescr.symbol tk                           => pure $ symbol.formatter tk
| ParserDescr.numLit                              => pure $ withAntiquot.formatter (mkAntiquot.formatter' "numLit" `numLit) numLitNoAntiquot.formatter
| ParserDescr.strLit                              => pure $ withAntiquot.formatter (mkAntiquot.formatter' "strLit" `strLit) strLitNoAntiquot.formatter
| ParserDescr.charLit                             => pure $ withAntiquot.formatter (mkAntiquot.formatter' "charLit" `charLit) charLitNoAntiquot.formatter
| ParserDescr.nameLit                             => pure $ withAntiquot.formatter (mkAntiquot.formatter' "nameLit" `nameLit) nameLitNoAntiquot.formatter
| ParserDescr.ident                               => pure $ withAntiquot.formatter (mkAntiquot.formatter' "ident" `ident) identNoAntiquot.formatter
| ParserDescr.nonReservedSymbol tk includeIdent   => pure $ nonReservedSymbol.formatter tk
| ParserDescr.parser constName                    => interpretParser (ctx interpretParserDescr) constName
| ParserDescr.cat catName prec                    => pure $ categoryParser.formatter catName

@[init] unsafe def regHook : IO Unit :=
ParserCompiler.registerParserCompiler (ctx interpretParserDescr)

end Formatter

end PrettyPrinter
end Lean
