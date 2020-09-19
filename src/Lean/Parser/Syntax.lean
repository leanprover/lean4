/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Command
import Lean.Parser.Tactic

namespace Lean
namespace Parser

@[init] def regBuiltinSyntaxParserAttr : IO Unit :=
let leadingIdentAsSymbol := true;
registerBuiltinParserAttribute `builtinSyntaxParser `stx leadingIdentAsSymbol

@[init] def regSyntaxParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `stxParser `stx

@[inline] def syntaxParser (rbp : Nat := 0) : Parser :=
categoryParser `stx rbp

-- TODO: `max` is a bad precedence name. Find a new one.
def maxSymbol := parser! nonReservedSymbol "max" true
def precedenceLit : Parser := numLit <|> maxSymbol
def «precedence» := parser! ":" >> precedenceLit
def optPrecedence := optional (try «precedence»)

namespace Syntax
@[builtinSyntaxParser] def paren     := parser! "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def cat       := parser! ident >> optPrecedence
@[builtinSyntaxParser] def atom      := parser! strLit
@[builtinSyntaxParser] def num       := parser! nonReservedSymbol "num"
@[builtinSyntaxParser] def str       := parser! nonReservedSymbol "str"
@[builtinSyntaxParser] def char      := parser! nonReservedSymbol "char"
@[builtinSyntaxParser] def ident     := parser! nonReservedSymbol "ident"
@[builtinSyntaxParser] def try       := parser! nonReservedSymbol "try " >> syntaxParser maxPrec
@[builtinSyntaxParser] def lookahead := parser! nonReservedSymbol "lookahead " >> syntaxParser maxPrec
@[builtinSyntaxParser] def sepBy     := parser! nonReservedSymbol "sepBy " >> syntaxParser maxPrec >> syntaxParser maxPrec
@[builtinSyntaxParser] def sepBy1    := parser! nonReservedSymbol "sepBy1 " >> syntaxParser maxPrec >> syntaxParser maxPrec

@[builtinSyntaxParser] def optional  := tparser! "?"
@[builtinSyntaxParser] def many      := tparser! "*"
@[builtinSyntaxParser] def many1     := tparser! "+"
@[builtinSyntaxParser] def orelse    := tparser!:2 " <|> " >> syntaxParser 1

end Syntax

namespace Command

def «prefix»   := parser! "prefix"
def «infix»    := parser! "infix"
def «infixl»   := parser! "infixl"
def «infixr»   := parser! "infixr"
def «postfix»  := parser! "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
-- TODO: after we remove old frontend
--  * remove " := "
--  * remove quotedSymbol and unquotedSymbol alternative
@[builtinCommandParser] def «mixfix»   := parser! mixfixKind >> optPrecedence >> (strLit <|> quotedSymbol <|> unquotedSymbol) >> (darrow <|> " := ") >> termParser

-- TODO: remove
@[builtinCommandParser] def «reserve»  := parser! "reserve " >> mixfixKind >> quotedSymbol >> optPrecedence

def identPrec  := parser! ident >> optPrecedence
def optKind : Parser := optional ("[" >> ident >> "]")
def notationItem := withAntiquot (mkAntiquot "notationItem" `Lean.Parser.Command.notationItem) (strLit <|> quotedSymbol <|> identPrec)
-- TODO: remove " := " after old frontend is gone
@[builtinCommandParser] def «notation»    := parser! "notation" >> optPrecedence >> many notationItem >> (" := " <|> darrow) >> termParser
@[builtinCommandParser] def «macro_rules» := parser! "macro_rules" >> optKind >> Term.matchAlts
@[builtinCommandParser] def «syntax»      := parser! "syntax " >> optPrecedence >> optKind >> many1 syntaxParser >> " : " >> ident
@[builtinCommandParser] def syntaxAbbrev  := parser! "syntax " >> ident >> " := " >> many1 syntaxParser
@[builtinCommandParser] def syntaxCat     := parser! "declare_syntax_cat " >> ident
def macroArgSimple := parser! ident >> checkNoWsBefore "no space before ':'" >> ":" >> syntaxParser maxPrec
def macroArg  := try strLit <|> try macroArgSimple
def macroHead := macroArg <|> try ident
def macroTailTactic   : Parser := try (" : " >> identEq "tactic") >> darrow >> ("`(" >> toggleInsideQuot Tactic.seq1Unbox >> ")" <|> termParser)
def macroTailCommand  : Parser := try (" : " >> identEq "command") >> darrow >> ("`(" >> toggleInsideQuot (many1Unbox commandParser) >> ")" <|> termParser)
def macroTailDefault  : Parser := try (" : " >> ident) >> darrow >> (("`(" >> toggleInsideQuot (categoryParserOfStack 2) >> ")") <|> termParser)
def macroTail := macroTailTactic <|> macroTailCommand <|> macroTailDefault
@[builtinCommandParser] def «macro»       := parser! "macro " >> optPrecedence >> macroHead >> many macroArg >> macroTail

@[builtinCommandParser] def «elab_rules» := parser! "elab_rules" >> optKind >> optional (" : " >> ident) >> Term.matchAlts
def elabHead := macroHead
def elabArg  := macroArg
def elabTail := try (" : " >> ident >> optional (" <= " >> ident)) >> darrow >> termParser
@[builtinCommandParser] def «elab»       := parser! "elab " >> optPrecedence >> elabHead >> many elabArg >> elabTail

end Command

end Parser
end Lean
