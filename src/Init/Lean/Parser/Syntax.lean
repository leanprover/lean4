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

@[init] def regSyntaxParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `syntaxParser `syntax

@[inline] def syntaxParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `syntax rbp

namespace Syntax

@[builtinSyntaxParser] def paren     := parser! "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def cat       := parser! ident
@[builtinSyntaxParser] def atom      := parser! strLit
@[builtinSyntaxParser] def num       := parser! nonReservedSymbol "num"
@[builtinSyntaxParser] def str       := parser! nonReservedSymbol "str"
@[builtinSyntaxParser] def char      := parser! nonReservedSymbol "char"
@[builtinSyntaxParser] def ident     := parser! nonReservedSymbol "ident"
@[builtinSyntaxParser] def try       := parser! nonReservedSymbol "try " >> syntaxParser
@[builtinSyntaxParser] def lookahead := parser! nonReservedSymbol "lookahead " >> syntaxParser
@[builtinSyntaxParser] def optional  := parser! nonReservedSymbol "optional " >> syntaxParser
@[builtinSyntaxParser] def sepBy     := parser! nonReservedSymbol "sepBy " >> syntaxParser >> syntaxParser
@[builtinSyntaxParser] def sepBy1    := parser! nonReservedSymbol "sepBy1 " >> syntaxParser >> syntaxParser

@[builtinSyntaxParser] def many     := tparser! pushLeading >> symbolAux "*" none
@[builtinSyntaxParser] def many1    := tparser! pushLeading >> symbolAux "+" none
@[builtinSyntaxParser] def orelse   := tparser! infixR " <|> " 2

end Syntax

namespace Command

@[builtinCommandParser] def «syntax» := parser! "syntax " >> many1 syntaxParser >> " : " >> ident

end Command

end Parser
end Lean
