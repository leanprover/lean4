/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.parser.parser
import init.lean.parser.level

namespace Lean
namespace Parser

@[init mkBuiltinParsingTablesRef]
constant builtinTermParsingTable : IO.Ref ParsingTables := default _

@[init] def regBuiltinTermParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinTermParser `Lean.Parser.builtinTermParsingTable

def termParserFn {k : ParserKind} (rbp : Nat) : ParserFn k :=
fun _ => runBuiltinParser "term" builtinTermParsingTable rbp

@[inline] def termParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
{ fn := termParserFn rbp }

namespace Term
/- Helper functions for defining simple parsers -/

def unicodeInfixR (sym : String) (asciiSym : String) (lbp : Nat) : TrailingParser :=
pushLeading >> unicodeSymbol sym asciiSym lbp >> termParser (lbp - 1)

def infixR (sym : String) (lbp : Nat) : TrailingParser :=
pushLeading >> symbol sym lbp >> termParser (lbp - 1)

def unicodeInfixL (sym : String) (asciiSym : String) (lbp : Nat) : TrailingParser :=
pushLeading >> unicodeSymbol sym asciiSym lbp >> termParser lbp

def infixL (sym : String) (lbp : Nat) : TrailingParser :=
pushLeading >> symbol sym lbp >> termParser lbp

/- Builting parsers -/
@[builtinTermParser] def id := parser! ident >> optional (".{" >> sepBy1 levelParser ", " >> "}")
@[builtinTermParser] def num : Parser := numLit
@[builtinTermParser] def str : Parser := strLit
@[builtinTermParser] def type := parser! symbol "Type" appPrec
@[builtinTermParser] def sort := parser! symbol "Sort" appPrec
@[builtinTermParser] def hole := parser! symbol "_" appPrec
@[builtinTermParser] def «sorry» := parser! symbol "sorry" appPrec
@[builtinTermParser] def cdot := parser! symbol "·" appPrec
def typeAscription := parser! " : " >> termParser
def tupleTail      := parser! ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := parser! symbol "(" appPrec >> optional (termParser >> parenSpecial) >> ")"
@[builtinTermParser] def anonymousCtor := parser! symbol "⟨" appPrec >> sepBy1 termParser ", " >> "⟩"
def optIdent : Parser := optional (try (ident >> " : "))
@[builtinTermParser] def «if»  := parser! "if " >> optIdent >> termParser >> " then " >> termParser >> " else " >> termParser
def fromTerm   := parser! " from " >> termParser
def haveAssign := parser! " := " >> termParser
@[builtinTermParser] def «have» := parser! "have " >> optIdent >> termParser >> (haveAssign <|> fromTerm) >> "; " >> termParser
@[builtinTermParser] def «suffices» := parser! "suffices " >> optIdent >> termParser >> fromTerm >> "; " >> termParser
@[builtinTermParser] def «show»     := parser! "show " >> termParser >> fromTerm
@[builtinTermParser] def «fun»      := parser! unicodeSymbol "λ" "fun" >> many1 (termParser appPrec) >> unicodeSymbol "⇒" "=>" >> termParser
def structInstField  := parser! ident >> " := " >> termParser
def structInstSource := parser! ".." >> optional termParser
@[builtinTermParser] def structInst := parser! symbol "{" appPrec >> optional (try (ident >> " . ")) >> sepBy (structInstField <|> structInstSource) ", " true >> "}"
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def subtype := parser! "{" >> ident >> optType >> " // " >> termParser >> "}"
@[builtinTermParser] def list := parser! symbol "[" appPrec >> sepBy termParser "," true >> "]"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then " : " >> termParser else optional (" : " >> termParser)
def binderDefault := parser! " := " >> termParser
def binderTactic  := parser! " . " >> termParser
def explicitBinder (requireType := false) := parser! "(" >> many1 binderIdent >> binderType requireType >> optional (binderDefault <|> binderTactic) >> ")"
def implicitBinder (requireType := false) := parser! "{" >> many1 binderIdent >> binderType requireType >> "}"
def instBinder := parser! "[" >> optIdent >> termParser >> "]"
def bracktedBinder (requireType := false) := explicitBinder requireType <|> implicitBinder requireType <|> instBinder
@[builtinTermParser] def depArrow := parser! bracktedBinder true >> unicodeSymbolCheckPrec " → " " -> " 25 >> termParser
def simpleBinder := parser! many1 binderIdent
@[builtinTermParser] def «forall» := parser! unicodeSymbol "∀" "forall" >> many1 (simpleBinder <|> bracktedBinder) >> ", " >> termParser
def equation := parser! " | " >> sepBy1 termParser ", " >> " => " >> termParser
def equations : Parser := withPosition $ fun pos => many1 (checkColGe pos.column "'match' cases must be indented" >> equation)
@[builtinTermParser] def «match» := parser! "match " >> sepBy1 termParser ", " >> optType >> " with " >> equations
@[builtinTermParser] def «nomatch» := parser! "nomatch " >> termParser

def namedArgument  := tparser! try ("(" >> ident >> " := ") >> termParser >> ")"
@[builtinTermParser] def app   := tparser! pushLeading >> (namedArgument <|> termParser appPrec)
@[builtinTermParser] def proj  := tparser! pushLeading >> symbolNoWs "." (appPrec+1) >> (fieldIdx <|> ident)
@[builtinTermParser] def arrow := tparser! unicodeInfixR " → " " -> " 25
@[builtinTermParser] def array := tparser! pushLeading >> symbolNoWs "[" (appPrec+1) >> termParser >>"]"

@[builtinTermParser] def fcomp := tparser! infixR " ∘ " 90

@[builtinTermParser] def add   := tparser! infixL " + "  65
@[builtinTermParser] def sub   := tparser! infixL " - "  65
@[builtinTermParser] def mul   := tparser! infixL " * "  70
@[builtinTermParser] def div   := tparser! infixL " / "  70
@[builtinTermParser] def mod   := tparser! infixL " % "  70
@[builtinTermParser] def modN  := tparser! infixL " %ₙ " 70

@[builtinTermParser] def le    := tparser! unicodeInfixL " ≤ " " <= " 50
@[builtinTermParser] def ge    := tparser! unicodeInfixL " ≥ " " >= " 50
@[builtinTermParser] def lt    := tparser! infixL " < " 50
@[builtinTermParser] def gt    := tparser! infixL " > " 50
@[builtinTermParser] def eq    := tparser! infixL " = " 50
@[builtinTermParser] def beq   := tparser! infixL " == " 50

@[builtinTermParser] def and   := tparser! unicodeInfixR " ∧ " " /\\ " 35
@[builtinTermParser] def or    := tparser! unicodeInfixR " ∨ " " \\/ " 30
@[builtinTermParser] def iff   := tparser! unicodeInfixL " ↔ " " <-> " 20

end Term

end Parser
end Lean
