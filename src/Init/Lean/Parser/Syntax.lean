/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Command

namespace Lean
namespace Parser

@[init] def regBuiltinSyntaxParserAttr : IO Unit :=
let leadingIdentAsSymbol := true;
registerBuiltinParserAttribute `builtinSyntaxParser `syntax leadingIdentAsSymbol

@[inline] def syntaxParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `syntax rbp

namespace Syntax
def maxPrec := parser! nonReservedSymbol "max" true
def precedenceLit : Parser := numLit <|> maxPrec
def «precedence» := parser! ":" >> precedenceLit
@[builtinSyntaxParser] def paren     := parser! "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def cat       := parser! ident >> optional (try «precedence»)
@[builtinSyntaxParser] def atom      := parser! strLit >> optional (try «precedence»)
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

def quotedSymbolPrec := parser! quotedSymbol >> optional Syntax.precedence
def «prefix»   := parser! "prefix"
def «infix»    := parser! "infix"
def «infixl»   := parser! "infixl"
def «infixr»   := parser! "infixr"
def «postfix»  := parser! "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
-- TODO delete reserve
@[builtinCommandParser] def «reserve»  := parser! "reserve " >> mixfixKind >> quotedSymbolPrec
def mixfixSymbol := quotedSymbolPrec <|> unquotedSymbol
@[builtinCommandParser] def «mixfix»   := parser! mixfixKind >> mixfixSymbol >> " := " >> termParser
def strLitPrec := parser! strLit >> optional Syntax.precedence
def identPrec  := parser! ident >> optional Syntax.precedence

@[builtinCommandParser] def «notation» := parser! "notation" >> many (strLitPrec <|> quotedSymbolPrec <|> identPrec) >> " := " >> termParser
@[builtinCommandParser] def «macro» := parser! "macro" >> many1Indent Term.matchAlt "'match' alternatives must be indented"
@[builtinCommandParser] def «syntax» := parser! "syntax " >> optional ("[" >> ident >> "]") >> many1 syntaxParser >> " : " >> ident

end Command

end Parser
end Lean
