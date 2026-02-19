/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Parser.Command

public section

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
/-! Parsers for the `syntax` DSL itself. -/
-- Keep docs short; these are primarily for hover/help in editors.

/-- Numeric literal for precedence expressions. -/
@[builtin_prec_parser] def numPrec := checkPrec maxPrec >> numLit

/-- Parenthesized syntax DSL expression, used for grouping. -/
@[builtin_syntax_parser] def paren           := leading_parser
  "(" >> withoutPosition (many1 syntaxParser) >> ")"
/-- Reference to a parser category or alias, optionally with precedence (e.g. `term` or `term:60`). -/
@[builtin_syntax_parser] def cat             := leading_parser
  ident >> optPrecedence
/-- Syntax DSL form `f(p)` for a unary parser alias. -/
@[builtin_syntax_parser] def unary           := leading_parser
  ident >> checkNoWsBefore >> "(" >> withoutPosition (many1 syntaxParser) >> ")"
/-- Syntax DSL form `f(p, q)` for a binary parser alias. -/
@[builtin_syntax_parser] def binary          := leading_parser
  ident >> checkNoWsBefore >> "(" >> withoutPosition (many1 syntaxParser >> ", " >> many1 syntaxParser) >> ")"
/-- Syntax DSL `sepBy(p, sep[, psep][, allowTrailingSep])` list parser. -/
@[builtin_syntax_parser] def sepBy           := leading_parser
  "sepBy(" >> withoutPosition (many1 syntaxParser >> ", " >> strLit >>
    optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep")) >> ")"
/-- Nonempty list variant of `sepBy`. -/
@[builtin_syntax_parser] def sepBy1          := leading_parser
  "sepBy1(" >> withoutPosition (many1 syntaxParser >> ", " >> strLit >>
    optional (", " >> many1 syntaxParser) >> optional (", " >> nonReservedSymbol "allowTrailingSep")) >> ")"
@[builtin_syntax_parser, inherit_doc ParserDescr.symbol]
def atom := leading_parser
  strLit
@[builtin_syntax_parser, inherit_doc ParserDescr.nonReservedSymbol]
def nonReserved := leading_parser
  "&" >> strLit
@[builtin_syntax_parser, inherit_doc ParserDescr.unicodeSymbol]
def unicodeAtom := leading_parser
  "unicode(" >> strLit >> ", " >> strLit >> optional (", " >> nonReservedSymbol "preserveForPP") >> ")"

end Syntax

namespace Command

def namedName := leading_parser
  atomic (" (" >> nonReservedSymbol "name") >> " := " >> ident >> ")"
def optNamedName := optional namedName

def identPrec  := leading_parser ident >> optPrecedence
def notationItem := withAntiquot (mkAntiquot "notationItem" decl_name% (isPseudoKind := true)) (strLit <|> Syntax.unicodeAtom <|> identPrec)
/--
`prefix:prec "op" => f` is equivalent to `notation:prec "op" x:prec => f x`.
-/
def «prefix»   := leading_parser "prefix"
/--
`infix:prec "op" => f` is equivalent to `notation:prec x:prec1 "op" y:prec1 => f x y`, where `prec1 := prec + 1`.
-/
def «infix»    := leading_parser "infix"
/--
`infixl:prec "op" => f` is equivalent to `notation:prec x:prec "op" y:prec1 => f x y`, where `prec1 := prec + 1`.
-/
def «infixl»   := leading_parser "infixl"
/--
`infixr:prec "op" => f` is equivalent to `notation:prec x:prec1 "op" y:prec => f x y`, where `prec1 := prec + 1`.
-/
def «infixr»   := leading_parser "infixr"
/--
`postfix:prec "op" => f` is equivalent to `notation:prec x:prec "op" => f x`.
-/
def «postfix»  := leading_parser "postfix"
def mixfixKind := «prefix» <|> «infix» <|> «infixl» <|> «infixr» <|> «postfix»
/-- Declare a `prefix`/`infix`/`postfix` notation. -/
@[builtin_command_parser] def «mixfix»   := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >> mixfixKind >>
  precedence >> optNamedName >> optNamedPrio >> ppSpace >> notationItem >> darrow >> termParser
/-- Declare a general notation. -/
@[builtin_command_parser] def «notation»    := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "notation" >> optPrecedence >> optNamedName >> optNamedPrio >> many (ppSpace >> notationItem) >> darrow >> termParser

-- NOTE: We use `suppressInsideQuot` in the following parsers because quotations inside them are evaluated in the same stage and
-- thus should be ignored when we use `checkInsideQuot` to prepare the next stage for a builtin syntax change
def optKind : Parser := optional (" (" >> nonReservedSymbol "kind" >> ":=" >> ident >> ")")
/-- Declare a family of macros by pattern (use `(kind := ...)` to disambiguate). -/
@[builtin_command_parser] def «macro_rules» := suppressInsideQuot <| leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "macro_rules" >> optKind >> Term.matchAlts
/-- Declare new syntax in a category, with optional precedence, name, and priority.
If the precedence is omitted, atom-like syntax defaults to `maxPrec` and other syntax to `leadPrec`.
If `name :=` is omitted, a name is generated from the syntax. -/
@[builtin_command_parser] def «syntax»      := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "syntax " >> optPrecedence >> optNamedName >> optNamedPrio >> many1 (ppSpace >> syntaxParser argPrec) >> " : " >> ident
/-- Declare a reusable syntax abbreviation `syntax <name> := ...` (no category), for use in other syntax rules. -/
@[builtin_command_parser] def syntaxAbbrev  := leading_parser
  optional docComment >> optional visibility >> "syntax " >> ident >> " := " >> many1 syntaxParser
def catBehaviorBoth   := leading_parser nonReservedSymbol "both"
def catBehaviorSymbol := leading_parser nonReservedSymbol "symbol"
def catBehavior := optional (" (" >> nonReservedSymbol "behavior" >> " := " >> (catBehaviorBoth <|> catBehaviorSymbol) >> ")")
/-- Declare a new syntax category. -/
@[builtin_command_parser] def syntaxCat := leading_parser
  optional docComment >> "declare_syntax_cat " >> ident >> catBehavior
def macroArg  := leading_parser
  optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> syntaxParser argPrec
def macroRhs : Parser := leading_parser withPosition termParser
def macroTail := leading_parser atomic (" : " >> ident) >> darrow >> macroRhs
/-- Declare a single macro with explicit arguments and expansion. -/
@[builtin_command_parser] def «macro»       := leading_parser suppressInsideQuot <|
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "macro" >> optPrecedence >> optNamedName >> optNamedPrio >> many1 (ppSpace >> macroArg) >> macroTail
/-- Declare elaborator rules for syntax (use `(kind := ...)` to disambiguate). -/
@[builtin_command_parser] def «elab_rules» := leading_parser suppressInsideQuot <|
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "elab_rules" >> optKind >> optional (" : " >> ident) >> optional (" <= " >> ident) >> Term.matchAlts
def elabArg  := macroArg
def elabTail := leading_parser atomic (" : " >> ident >> optional (" <= " >> ident)) >> darrow >> withPosition termParser
/-- Declare a single elaborator for syntax. -/
@[builtin_command_parser] def «elab»       := leading_parser suppressInsideQuot <|
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "elab" >> optPrecedence >> optNamedName >> optNamedPrio >> many1 (ppSpace >> elabArg) >> elabTail

/--
Declares a binder predicate.  For example:
```
binder_predicate x " > " y:term => `($x > $y)
```
-/
@[builtin_command_parser] def binderPredicate := leading_parser
   optional docComment >>  optional Term.attributes >> optional Term.attrKind >>
   "binder_predicate" >> optNamedName >> optNamedPrio >> ppSpace >> ident >> many (ppSpace >> macroArg) >> " => " >> termParser

end Command

end Parser
end Lean
