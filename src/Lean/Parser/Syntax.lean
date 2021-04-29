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

def «precedence» := leading_parser ":" >> precedenceParser maxPrec
def optPrecedence := optional (atomic «precedence»)

namespace Syntax
@[builtinPrecParser] def numPrec := checkPrec maxPrec >> numLit

@[builtinSyntaxParser] def paren           := leading_parser "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def cat             := leading_parser ident >> optPrecedence
@[builtinSyntaxParser] def unary           := leading_parser ident >> checkNoWsBefore >> "(" >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def binary          := leading_parser ident >> checkNoWsBefore >> "(" >> many1 syntaxParser >> ", " >> many1 syntaxParser >> ")"
@[builtinSyntaxParser] def sepBy           := leading_parser "sepBy(" >> many1 syntaxParser >> ", " >> strLit >> optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep") >> ")"
@[builtinSyntaxParser] def sepBy1          := leading_parser "sepBy1(" >> many1 syntaxParser >> ", " >> strLit >> optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep") >> ")"
@[builtinSyntaxParser] def atom            := leading_parser strLit
@[builtinSyntaxParser] def nonReserved     := leading_parser "&" >> strLit

end Syntax

namespace Term

@[builtinTermParser] def stx.quot : Parser := leading_parser "`(stx|"  >> incQuotDepth syntaxParser >> ")"
@[builtinTermParser] def prec.quot : Parser := leading_parser "`(prec|"  >> incQuotDepth precedenceParser >> ")"
@[builtinTermParser] def prio.quot : Parser := leading_parser "`(prio|"  >> incQuotDepth priorityParser >> ")"

end Term

namespace Command

def namedName := leading_parser (atomic ("(" >> nonReservedSymbol "name") >> " := " >> ident >> ")")
def optNamedName := optional namedName

def «prefix»   := leading_parser "prefix"
def «infix»    := leading_parser "infix"
def «infixl»   := leading_parser "infixl"
def «infixr»   := leading_parser "infixr"
def «postfix»  := leading_parser "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
@[builtinCommandParser] def «mixfix»   := leading_parser Term.attrKind >> mixfixKind >> optPrecedence >> optNamedName >> optNamedPrio >> ppSpace >> strLit >> darrow >> termParser
-- NOTE: We use `suppressInsideQuot` in the following parsers because quotations inside them are evaluated in the same stage and
-- thus should be ignored when we use `checkInsideQuot` to prepare the next stage for a builtin syntax change
def identPrec  := leading_parser ident >> optPrecedence

def optKind : Parser := optional ("(" >> nonReservedSymbol "kind" >> ":=" >> ident >> ")")

def notationItem := ppSpace >> withAntiquot (mkAntiquot "notationItem" `Lean.Parser.Command.notationItem) (strLit <|> identPrec)
@[builtinCommandParser] def «notation»    := leading_parser Term.attrKind >> "notation" >> optPrecedence >> optNamedName >> optNamedPrio >> many notationItem >> darrow >> termParser
@[builtinCommandParser] def «macro_rules» := suppressInsideQuot (leading_parser Term.attrKind >> "macro_rules" >>  optKind >> Term.matchAlts)
@[builtinCommandParser] def «syntax»      := leading_parser Term.attrKind >> "syntax " >> optPrecedence >> optNamedName >> optNamedPrio >> many1 syntaxParser >> " : " >> ident
@[builtinCommandParser] def syntaxAbbrev  := leading_parser "syntax " >> ident >> " := " >> many1 syntaxParser
@[builtinCommandParser] def syntaxCat     := leading_parser "declare_syntax_cat " >> ident
def macroArgSimple := leading_parser ident >> checkNoWsBefore "no space before ':'" >> ":" >> syntaxParser maxPrec
def macroArgSymbol := leading_parser strLit >> optional (atomic <| checkNoWsBefore >> "%" >> checkNoWsBefore >> ident)
def macroArg  := macroArgSymbol <|> atomic macroArgSimple
def macroHead := macroArg
def macroTailTactic   : Parser := atomic (" : " >> identEq "tactic") >> darrow >> ("`(" >> incQuotDepth Tactic.seq1 >> ")" <|> termParser)
def macroTailCommand  : Parser := atomic (" : " >> identEq "command") >> darrow >> ("`(" >> incQuotDepth (many1Unbox commandParser) >> ")" <|> termParser)
def macroTailDefault  : Parser := atomic (" : " >> ident) >> darrow >> (("`(" >> incQuotDepth (categoryParserOfStack 2) >> ")") <|> termParser)
def macroTail := macroTailTactic <|> macroTailCommand <|> macroTailDefault
@[builtinCommandParser] def «macro»       := leading_parser suppressInsideQuot (Term.attrKind >> "macro " >> optPrecedence >> optNamedName >> optNamedPrio >> macroHead >> many macroArg >> macroTail)

@[builtinCommandParser] def «elab_rules» := leading_parser suppressInsideQuot ("elab_rules" >> optKind >> optional (" : " >> ident) >> Term.matchAlts)
def elabHead := macroHead
def elabArg  := macroArg
def elabTail := atomic (" : " >> ident >> optional (" <= " >> ident)) >> darrow >> termParser
@[builtinCommandParser] def «elab»       := leading_parser suppressInsideQuot (Term.attrKind >> "elab " >> optPrecedence >> optNamedName >> optNamedPrio >> elabHead >> many elabArg >> elabTail)

end Command

end Parser
end Lean
