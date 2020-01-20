/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Command
import Init.Lean.Parser.Tactic

namespace Lean
namespace Parser

@[init] def regBuiltinSyntaxParserAttr : IO Unit :=
let leadingIdentAsSymbol := true;
registerBuiltinParserAttribute `builtinSyntaxParser `syntax leadingIdentAsSymbol

@[inline] def syntaxParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `syntax rbp

def maxPrec := parser! nonReservedSymbol "max" true
def precedenceLit : Parser := numLit <|> maxPrec
def «precedence» := parser! ":" >> precedenceLit
def optPrecedence := optional (try «precedence»)

namespace Syntax
@[builtinSyntaxParser] def paren     := parser! "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def cat       := parser! ident >> optPrecedence
@[builtinSyntaxParser] def atom      := parser! strLit >> optPrecedence
@[builtinSyntaxParser] def num       := parser! nonReservedSymbol "num"
@[builtinSyntaxParser] def str       := parser! nonReservedSymbol "str"
@[builtinSyntaxParser] def char      := parser! nonReservedSymbol "char"
@[builtinSyntaxParser] def ident     := parser! nonReservedSymbol "ident"
@[builtinSyntaxParser] def try       := parser! nonReservedSymbol "try " >> syntaxParser
@[builtinSyntaxParser] def lookahead := parser! nonReservedSymbol "lookahead " >> syntaxParser
@[builtinSyntaxParser] def optional  := parser! nonReservedSymbol "optional " >> syntaxParser
@[builtinSyntaxParser] def sepBy     := parser! nonReservedSymbol "sepBy " >> syntaxParser >> syntaxParser
@[builtinSyntaxParser] def sepBy1    := parser! nonReservedSymbol "sepBy1 " >> syntaxParser >> syntaxParser

@[builtinSyntaxParser] def many      := tparser! pushLeading >> symbolAux "*" none
@[builtinSyntaxParser] def many1     := tparser! pushLeading >> symbolAux "+" none
@[builtinSyntaxParser] def orelse    := tparser! pushLeading >> " <|> " >> syntaxParser 1

end Syntax

namespace Command

def quotedSymbolPrec := parser! quotedSymbol >> optPrecedence
def «prefix»   := parser! "prefix"
def «infix»    := parser! "infix"
def «infixl»   := parser! "infixl"
def «infixr»   := parser! "infixr"
def «postfix»  := parser! "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
-- TODO delete reserve
@[builtinCommandParser] def «reserve»  := parser! "reserve " >> mixfixKind >> quotedSymbolPrec
def mixfixSymbol := quotedSymbolPrec <|> unquotedSymbol
-- TODO: remove " := " after old frontend is gone
@[builtinCommandParser] def «mixfix»   := parser! mixfixKind >> mixfixSymbol >> (" := " <|> darrow) >> termParser
def strLitPrec := parser! strLit >> optPrecedence
def identPrec  := parser! ident >> optPrecedence

-- TODO: remove " := " after old frontend is gone
@[builtinCommandParser] def «notation»    := parser! "notation" >> many (strLitPrec <|> quotedSymbolPrec <|> identPrec) >> (" := " <|> darrow) >> termParser
@[builtinCommandParser] def «macro_rules» := parser! "macro_rules" >> many1Indent Term.matchAlt "'match' alternatives must be indented"
@[builtinCommandParser] def «syntax»      := parser! "syntax " >> optional ("[" >> ident >> "]") >> many1 syntaxParser >> " : " >> ident
@[builtinCommandParser] def syntaxCat     := parser! "declare_syntax_cat " >> ident
def macroArgType   := nonReservedSymbol "ident" <|> nonReservedSymbol "num" <|> nonReservedSymbol "str" <|> nonReservedSymbol "char" <|> (ident >> optPrecedence)
def macroArgSimple := parser! ident >> checkNoWsBefore "no space before ':'" >> ":" >> macroArgType
def macroArg  := try strLitPrec <|> try macroArgSimple
def macroHead := macroArg <|> try identPrec
def macroTailTactic   : Parser := try (" : " >> identEq "tactic") >> darrow >> "`(" >> sepBy1 tacticParser "; " true true >> ")"
def macroTailCommand  : Parser := try (" : " >> identEq "command") >> darrow >> "`(" >> many1 commandParser true >> ")"
def macroTailDefault  : Parser := try (" : " >> ident) >> darrow >> "`(" >> categoryParserOfStack 2 >> ")"
def macroTail := macroTailTactic <|> macroTailCommand <|> macroTailDefault
@[builtinCommandParser] def «macro»       := parser! "macro " >> macroHead >> many macroArg >> macroTail

end Command

end Parser
end Lean
