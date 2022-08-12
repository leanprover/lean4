/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Parser.Level
import Lean.Parser.Term
import Lean.Parser.Tactic
import Lean.Parser.Command
import Lean.Parser.Module
import Lean.Parser.Syntax
import Lean.Parser.Do

namespace Lean
namespace Parser
open Lean.PrettyPrinter
open Lean.PrettyPrinter.Parenthesizer
open Lean.PrettyPrinter.Formatter

builtin_initialize
  register_parser_alias "ws" checkWsBefore { stackSz? := some 0 }
  register_parser_alias "noWs" checkNoWsBefore { stackSz? := some 0 }
  register_parser_alias "linebreak" checkLinebreakBefore { stackSz? := some 0 }
  register_parser_alias (kind := numLitKind) "num" numLit
  register_parser_alias (kind := strLitKind) "str" strLit
  register_parser_alias (kind := charLitKind) "char" charLit
  register_parser_alias (kind := nameLitKind) "name" nameLit
  register_parser_alias (kind := scientificLitKind) "scientific" scientificLit
  register_parser_alias (kind := identKind) "ident" ident
  register_parser_alias "colGt" checkColGt { stackSz? := some 0 }
  register_parser_alias "colGe" checkColGe { stackSz? := some 0 }
  register_parser_alias "lineEq" checkLineEq { stackSz? := some 0 }
  register_parser_alias lookahead { stackSz? := some 0 }
  register_parser_alias atomic { stackSz? := none }
  register_parser_alias many
  register_parser_alias many1
  register_parser_alias manyIndent
  register_parser_alias many1Indent
  register_parser_alias optional { autoGroupArgs := false }
  register_parser_alias withPosition { stackSz? := none }
  register_parser_alias (kind := interpolatedStrKind) interpolatedStr
  register_parser_alias orelse
  register_parser_alias andthen { stackSz? := none }

  registerAlias "notFollowedBy" ``notFollowedBy (notFollowedBy · "element")
  Parenthesizer.registerAlias "notFollowedBy" notFollowedBy.parenthesizer
  Formatter.registerAlias "notFollowedBy" notFollowedBy.formatter

end Parser

namespace PrettyPrinter
namespace Parenthesizer

-- Close the mutual recursion loop; see corresponding `[extern]` in the parenthesizer.
@[export lean_mk_antiquot_parenthesizer]
def mkAntiquot.parenthesizer (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := true) : Parenthesizer :=
  Parser.mkAntiquot.parenthesizer name kind anonymous isPseudoKind

-- The parenthesizer auto-generated these instances correctly, but tagged them with the wrong kind, since the actual kind
-- (e.g. `ident`) is not equal to the parser name `Lean.Parser.Term.ident`.
@[builtinParenthesizer ident] def ident.parenthesizer : Parenthesizer := Parser.Term.ident.parenthesizer
@[builtinParenthesizer num] def numLit.parenthesizer : Parenthesizer := Parser.Term.num.parenthesizer
@[builtinParenthesizer scientific] def scientificLit.parenthesizer : Parenthesizer := Parser.Term.scientific.parenthesizer
@[builtinParenthesizer char] def charLit.parenthesizer : Parenthesizer := Parser.Term.char.parenthesizer
@[builtinParenthesizer str] def strLit.parenthesizer : Parenthesizer := Parser.Term.str.parenthesizer

open Lean.Parser

@[export lean_pretty_printer_parenthesizer_interpret_parser_descr]
unsafe def interpretParserDescr : ParserDescr → CoreM Parenthesizer
  | ParserDescr.const n                             => getConstAlias parenthesizerAliasesRef n
  | ParserDescr.unary n d                           => return (← getUnaryAlias parenthesizerAliasesRef n) (← interpretParserDescr d)
  | ParserDescr.binary n d₁ d₂                      => return (← getBinaryAlias parenthesizerAliasesRef n) (← interpretParserDescr d₁) (← interpretParserDescr d₂)
  | ParserDescr.node k prec d                       => return leadingNode.parenthesizer k prec (← interpretParserDescr d)
  | ParserDescr.nodeWithAntiquot _ k d              => return node.parenthesizer k (← interpretParserDescr d)
  | ParserDescr.sepBy p sep psep trail              => return sepBy.parenthesizer (← interpretParserDescr p) sep (← interpretParserDescr psep) trail
  | ParserDescr.sepBy1 p sep psep trail             => return sepBy1.parenthesizer (← interpretParserDescr p) sep (← interpretParserDescr psep) trail
  | ParserDescr.trailingNode k prec lhsPrec d       => return trailingNode.parenthesizer k prec lhsPrec (← interpretParserDescr d)
  | ParserDescr.symbol tk                           => return symbol.parenthesizer tk
  | ParserDescr.nonReservedSymbol tk includeIdent   => return nonReservedSymbol.parenthesizer tk includeIdent
  | ParserDescr.parser constName                    => combinatorParenthesizerAttribute.runDeclFor constName
  | ParserDescr.cat catName prec                    => return categoryParser.parenthesizer catName prec

end Parenthesizer

namespace Formatter

@[export lean_mk_antiquot_formatter]
def mkAntiquot.formatter (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := true) : Formatter :=
  Parser.mkAntiquot.formatter name kind anonymous isPseudoKind

@[builtinFormatter ident] def ident.formatter : Formatter := Parser.Term.ident.formatter
@[builtinFormatter num] def numLit.formatter : Formatter := Parser.Term.num.formatter
@[builtinFormatter scientific] def scientificLit.formatter : Formatter := Parser.Term.scientific.formatter
@[builtinFormatter char] def charLit.formatter : Formatter := Parser.Term.char.formatter
@[builtinFormatter str] def strLit.formatter : Formatter := Parser.Term.str.formatter

open Lean.Parser

@[export lean_pretty_printer_formatter_interpret_parser_descr]
unsafe def interpretParserDescr : ParserDescr → CoreM Formatter
  | ParserDescr.const n                             => getConstAlias formatterAliasesRef n
  | ParserDescr.unary n d                           => return (← getUnaryAlias formatterAliasesRef n) (← interpretParserDescr d)
  | ParserDescr.binary n d₁ d₂                      => return (← getBinaryAlias formatterAliasesRef n) (← interpretParserDescr d₁) (← interpretParserDescr d₂)
  | ParserDescr.node k _ d                          => return node.formatter k (← interpretParserDescr d)
  | ParserDescr.nodeWithAntiquot _ k d              => return node.formatter k (← interpretParserDescr d)
  | ParserDescr.sepBy p sep psep trail              => return sepBy.formatter (← interpretParserDescr p) sep (← interpretParserDescr psep) trail
  | ParserDescr.sepBy1 p sep psep trail             => return sepBy1.formatter (← interpretParserDescr p) sep (← interpretParserDescr psep) trail
  | ParserDescr.trailingNode k prec lhsPrec d       => return trailingNode.formatter k prec lhsPrec (← interpretParserDescr d)
  | ParserDescr.symbol tk                           => return symbol.formatter tk
  | ParserDescr.nonReservedSymbol tk _              => return nonReservedSymbol.formatter tk
  | ParserDescr.parser constName                    => combinatorFormatterAttribute.runDeclFor constName
  | ParserDescr.cat catName _                       => return categoryParser.formatter catName

end Formatter
end PrettyPrinter
end Lean
