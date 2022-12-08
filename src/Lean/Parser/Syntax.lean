/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Command

namespace Lean
namespace Parser

builtin_initialize
  registerBuiltinParserAttribute `builtin_syntax_parser ``Category.stx .both
  registerBuiltinDynamicParserAttribute `stx_parser `stx

builtin_initialize
  registerBuiltinParserAttribute `builtin_prec_parser ``Category.prec .both
  registerBuiltinDynamicParserAttribute `prec_parser `prec

@[inline] def precedenceParser (rbp : Nat := 0) : Parser :=
  categoryParser `prec rbp

@[inline] def syntaxParser (rbp : Nat := 0) : Parser :=
  categoryParser `stx rbp

def «precedence» := leading_parser
  ":" >> precedenceParser maxPrec
def optPrecedence := optional (atomic «precedence»)

namespace Syntax
@[builtin_prec_parser] def numPrec := checkPrec maxPrec >> numLit

@[builtin_syntax_parser] def paren           := leading_parser
  "(" >> withoutPosition (many1 syntaxParser) >> ")"
@[builtin_syntax_parser] def cat             := leading_parser
  ident >> optPrecedence
@[builtin_syntax_parser] def unary           := leading_parser
  ident >> checkNoWsBefore >> "(" >> withoutPosition (many1 syntaxParser) >> ")"
@[builtin_syntax_parser] def binary          := leading_parser
  ident >> checkNoWsBefore >> "(" >> withoutPosition (many1 syntaxParser >> ", " >> many1 syntaxParser) >> ")"
@[builtin_syntax_parser] def sepBy           := leading_parser
  "sepBy(" >> withoutPosition (many1 syntaxParser >> ", " >> strLit >>
    optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep")) >> ")"
@[builtin_syntax_parser] def sepBy1          := leading_parser
  "sepBy1(" >> withoutPosition (many1 syntaxParser >> ", " >> strLit >>
    optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep")) >> ")"
@[builtin_syntax_parser] def atom            := leading_parser
  strLit
@[builtin_syntax_parser] def nonReserved     := leading_parser
  "&" >> strLit

end Syntax

namespace Command

def namedName := leading_parser
  atomic ("(" >> nonReservedSymbol "name") >> " := " >> ident >> ")"
def optNamedName := optional namedName

def «prefix»   := leading_parser "prefix"
def «infix»    := leading_parser "infix"
def «infixl»   := leading_parser "infixl"
def «infixr»   := leading_parser "infixr"
def «postfix»  := leading_parser "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
@[builtin_command_parser] def «mixfix»   := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >> mixfixKind >>
  precedence >> optNamedName >> optNamedPrio >> ppSpace >> strLit >> darrow >> termParser
-- NOTE: We use `suppressInsideQuot` in the following parsers because quotations inside them are evaluated in the same stage and
-- thus should be ignored when we use `checkInsideQuot` to prepare the next stage for a builtin syntax change
def identPrec  := leading_parser ident >> optPrecedence

def optKind : Parser := optional ("(" >> nonReservedSymbol "kind" >> ":=" >> ident >> ")")

def notationItem := ppSpace >> withAntiquot (mkAntiquot "notationItem" `Lean.Parser.Command.notationItem) (strLit <|> identPrec)
@[builtin_command_parser] def «notation»    := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "notation" >> optPrecedence >> optNamedName >> optNamedPrio >> many notationItem >> darrow >> termParser
@[builtin_command_parser] def «macro_rules» := suppressInsideQuot <| leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "macro_rules" >>  optKind >> Term.matchAlts
@[builtin_command_parser] def «syntax»      := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "syntax " >> optPrecedence >> optNamedName >> optNamedPrio >> many1 (syntaxParser argPrec) >> " : " >> ident
@[builtin_command_parser] def syntaxAbbrev  := leading_parser
  optional docComment >> "syntax " >> ident >> " := " >> many1 syntaxParser
def catBehaviorBoth   := leading_parser nonReservedSymbol "both"
def catBehaviorSymbol := leading_parser nonReservedSymbol "symbol"
def catBehavior := optional ("(" >> nonReservedSymbol "behavior" >> " := " >> (catBehaviorBoth <|> catBehaviorSymbol) >> ")")
@[builtin_command_parser] def syntaxCat := leading_parser
  optional docComment >> "declare_syntax_cat " >> ident >> catBehavior
def macroArg  := leading_parser
  optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> syntaxParser argPrec
def macroRhs : Parser := leading_parser withPosition termParser
def macroTail := leading_parser atomic (" : " >> ident) >> darrow >> macroRhs
@[builtin_command_parser] def «macro»       := leading_parser suppressInsideQuot <|
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "macro " >> optPrecedence >> optNamedName >> optNamedPrio >> many1 macroArg >> macroTail
@[builtin_command_parser] def «elab_rules» := leading_parser suppressInsideQuot <|
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "elab_rules" >> optKind >> optional (" : " >> ident)  >> optional (" <= " >> ident) >> Term.matchAlts
def elabArg  := macroArg
def elabTail := leading_parser atomic (" : " >> ident >> optional (" <= " >> ident)) >> darrow >> withPosition termParser
@[builtin_command_parser] def «elab»       := leading_parser suppressInsideQuot <|
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "elab " >> optPrecedence >> optNamedName >> optNamedPrio >> many1 elabArg >> elabTail

end Command

end Parser
end Lean
