/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Command
import Lean.Parser.Tactic

namespace Lean
namespace Parser

@[init] def regBuiltinSyntaxParserAttr : IO Unit :=
let leadingIdentAsSymbol := true;
registerBuiltinParserAttribute `builtinSyntaxParser `syntax leadingIdentAsSymbol

@[inline] def syntaxParser (rbp : Nat := 0) : Parser :=
categoryParser `syntax rbp

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
-- TODO delete reserve after old frontend is gone
@[builtinCommandParser] def «reserve»  := parser! "reserve " >> mixfixKind >> quotedSymbol >> optPrecedence
def mixfixSymbol := (quotedSymbol >> optPrecedence /- TODO: remove precedence after we delete old precedence -/) <|> unquotedSymbol
def identPrec  := parser! ident >> optPrecedence
-- TODO: remove " := " after old frontend is gone
@[builtinCommandParser] def «mixfix»   := parser! mixfixKind >> optPrecedence >> mixfixSymbol >> (" := " <|> darrow) >> termParser

def optKind : Parser := optional ("[" >> ident >> "]")
def notationItem := withAntiquot (mkAntiquot "notationItem" `Lean.Parser.Command.notationItem) (strLit <|> quotedSymbol <|> identPrec)
-- TODO: remove " := " after old frontend is gone
@[builtinCommandParser] def «notation»    := parser! "notation" >> optPrecedence >> many notationItem >> (" := " <|> darrow) >> termParser
@[builtinCommandParser] def «macro_rules» := parser! "macro_rules" >> optKind >> Term.matchAlts
@[builtinCommandParser] def «syntax»      := parser! "syntax " >> optPrecedence >> optKind >> many1 syntaxParser >> " : " >> ident
@[builtinCommandParser] def syntaxAbbrev  := parser! "syntax " >> ident >> " := " >> many1 syntaxParser
@[builtinCommandParser] def syntaxCat     := parser! "declare_syntax_cat " >> ident
def macroArgType   := nonReservedSymbol "ident" <|> nonReservedSymbol "num" <|> nonReservedSymbol "str" <|> nonReservedSymbol "char" <|> (ident >> optPrecedence)
def macroArgSimple := parser! ident >> checkNoWsBefore "no space before ':'" >> ":" >> macroArgType
def macroArg  := try strLit <|> try macroArgSimple
def macroHead := macroArg <|> try ident
def macroTailTactic   : Parser := try (" : " >> identEq "tactic") >> darrow >> ("`(" >> sepBy1 tacticParser "; " true true >> ")" <|> termParser)
def macroTailCommand  : Parser := try (" : " >> identEq "command") >> darrow >> ("`(" >> many1 commandParser true >> ")" <|> termParser)
def macroTailDefault  : Parser := try (" : " >> ident) >> darrow >> (("`(" >> categoryParserOfStack 2 >> ")") <|> termParser)
def macroTail := macroTailTactic <|> macroTailCommand <|> macroTailDefault
@[builtinCommandParser] def «macro»       := parser! "macro " >> optPrecedence >> macroHead >> many macroArg >> macroTail

end Command

end Parser
end Lean
