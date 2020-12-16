/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Command
import Lean.Parser.Tactic

namespace Lean
namespace Parser

builtin_initialize
  registerBuiltinParserAttribute `builtinSyntaxParser `stx LeadingIdentBehavior.both
  registerBuiltinDynamicParserAttribute `stxParser `stx

builtin_initialize
  registerBuiltinParserAttribute `builtinPrecParser `prec LeadingIdentBehavior.both
  registerBuiltinDynamicParserAttribute `precParser `prec

@[inline] def precedenceParser (rbp : Nat := 0) : Parser :=
  categoryParser `prec rbp

@[inline] def syntaxParser (rbp : Nat := 0) : Parser :=
  categoryParser `stx rbp

def «precedence» := parser! ":" >> precedenceParser maxPrec
def optPrecedence := optional (atomic «precedence»)

namespace Syntax
@[builtinPrecParser] def numPrec := checkPrec maxPrec >> numLit

@[builtinSyntaxParser] def paren           := parser! "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def cat             := parser! ident >> optPrecedence
@[builtinSyntaxParser] def unary           := parser! ident >> checkNoWsBefore >> "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def binary          := parser! ident >> checkNoWsBefore >> "(" >> many1 syntaxParser >> ", " >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def sepBy           := parser! "sepBy(" >> many1 syntaxParser >> ", " >> strLit >> optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep") >> ")"
@[builtinSyntaxParser] def sepBy1          := parser! "sepBy1(" >> many1 syntaxParser >> ", " >> strLit >> optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep") >> ")"
@[builtinSyntaxParser] def atom            := parser! strLit
@[builtinSyntaxParser] def nonReserved     := parser! "&" >> strLit

end Syntax

namespace Term

@[builtinTermParser] def stx.quot : Parser := parser! "`(stx|"  >> toggleInsideQuot syntaxParser >> ")"
@[builtinTermParser] def prec.quot : Parser := parser! "`(prec|"  >> toggleInsideQuot precedenceParser >> ")"
@[builtinTermParser] def prio.quot : Parser := parser! "`(prio|"  >> toggleInsideQuot priorityParser >> ")"

end Term

namespace Command

def optPrio   := optional ("[" >> priorityParser >> "]")

def «prefix»   := parser! "prefix"
def «infix»    := parser! "infix"
def «infixl»   := parser! "infixl"
def «infixr»   := parser! "infixr"
def «postfix»  := parser! "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
@[builtinCommandParser] def «mixfix»   := parser! Term.attrKind >> mixfixKind >> optPrecedence >> optPrio >> ppSpace >> strLit >> darrow >> termParser
-- NOTE: We use `suppressInsideQuot` in the following parsers because quotations inside them are evaluated in the same stage and
-- thus should be ignored when we use `checkInsideQuot` to prepare the next stage for a builtin syntax change
def identPrec  := parser! ident >> optPrecedence
def optKind : Parser := optional ("[" >> ident >> "]")
def notationItem := ppSpace >> withAntiquot (mkAntiquot "notationItem" `Lean.Parser.Command.notationItem) (strLit <|> identPrec)
@[builtinCommandParser] def «notation»    := parser! Term.attrKind >> "notation" >> optPrecedence >> optPrio >> many notationItem >> darrow >> termParser
@[builtinCommandParser] def «macro_rules» := suppressInsideQuot (parser! "macro_rules" >> optKind >> Term.matchAlts)
def parserKind     := parser! ident
def parserPrio     := parser! priorityParser
def parserKindPrio := parser! atomic (ident >> ", ") >> priorityParser
def optKindPrio : Parser := optional ("[" >> (parserKindPrio <|> parserPrio <|> parserKind) >> "]")
@[builtinCommandParser] def «syntax»      := parser! Term.attrKind >> "syntax " >> optPrecedence >> optKindPrio >> many1 syntaxParser >> " : " >> ident
@[builtinCommandParser] def syntaxAbbrev  := parser! "syntax " >> ident >> " := " >> many1 syntaxParser
@[builtinCommandParser] def syntaxCat     := parser! "declare_syntax_cat " >> ident
def macroArgSimple := parser! ident >> checkNoWsBefore "no space before ':'" >> ":" >> syntaxParser maxPrec
def macroArg  := strLit <|> atomic macroArgSimple
def macroHead := macroArg
def macroTailTactic   : Parser := atomic (" : " >> identEq "tactic") >> darrow >> ("`(" >> toggleInsideQuot Tactic.seq1 >> ")" <|> termParser)
def macroTailCommand  : Parser := atomic (" : " >> identEq "command") >> darrow >> ("`(" >> toggleInsideQuot (many1Unbox commandParser) >> ")" <|> termParser)
def macroTailDefault  : Parser := atomic (" : " >> ident) >> darrow >> (("`(" >> toggleInsideQuot (categoryParserOfStack 2) >> ")") <|> termParser)
def macroTail := macroTailTactic <|> macroTailCommand <|> macroTailDefault
@[builtinCommandParser] def «macro»       := parser! suppressInsideQuot ("macro " >> optPrecedence >> optPrio >> macroHead >> many macroArg >> macroTail)

@[builtinCommandParser] def «elab_rules» := parser! suppressInsideQuot ("elab_rules" >> optKind >> optional (" : " >> ident) >> Term.matchAlts)
def elabHead := macroHead
def elabArg  := macroArg
def elabTail := atomic (" : " >> ident >> optional (" <= " >> ident)) >> darrow >> termParser
@[builtinCommandParser] def «elab»       := parser! suppressInsideQuot ("elab " >> optPrecedence >> optPrio >> elabHead >> many elabArg >> elabTail)

end Command

end Parser
end Lean
