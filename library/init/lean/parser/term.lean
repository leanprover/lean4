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

def termParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
{ fn := fun _ => runBuiltinParser "term" builtinTermParsingTable rbp }

namespace Term

@[builtinTermParser] def ident := parser! ident >> optional (".{" >> sepBy1 levelParser ", " >> "}")
@[builtinTermParser] def num : Parser := numLit
@[builtinTermParser] def str : Parser := strLit
@[builtinTermParser] def type := parser! symbol "Type" maxPrec
@[builtinTermParser] def sort := parser! symbol "Sort" maxPrec
@[builtinTermParser] def hole := parser! symbol "_" maxPrec
@[builtinTermParser] def cdot := parser! symbol "·" maxPrec
@[inline] def parenSpecial : Parser := optional (", " >> sepBy termParser ", " <|> " : " >> termParser)
@[builtinTermParser] def paren := parser! symbol "(" maxPrec >> optional (termParser >> parenSpecial) >> ")"
@[builtinTermParser] def anonymousCtor := parser! symbol "⟨" maxPrec >> sepBy1 termParser ", " >> symbol "⟩"
@[inline] def optIdent : Parser := optional (try (ident >> " : "))
@[builtinTermParser] def «if»  := parser! "if " >> optIdent >> termParser >> " then " >> termParser >> " else " >> termParser
def fromTerm   := parser! " from " >> termParser
def haveAssign := parser! " := " >> termParser
@[builtinTermParser] def «have» := parser! "have " >> optIdent >> termParser >> (haveAssign <|> fromTerm) >> "; " >> termParser
@[builtinTermParser] def «suffices» := parser! "suffices " >> optIdent >> termParser >> fromTerm >> "; " >> termParser
@[builtinTermParser] def «show»     := parser! "show " >> termParser >> fromTerm
@[builtinTermParser] def «fun»      := parser! unicodeSymbol "λ" "fun" >> many1 (termParser maxPrec) >> unicodeSymbol "⇒" "=>" >> termParser
def structInstField  := parser! ident >> " := " >> termParser
def structInstSource := parser! ".." -- >> optional termParser
@[builtinTermParser] def structInst := parser! symbol "{" maxPrec >> optional (try (ident >> " . ")) >> sepBy (structInstField <|> structInstSource) ", " true >> "}"
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def subtype := parser! "{" >> ident >> optType >> " // " >> termParser >> "}"

@[builtinTermParser] def app := tparser! pushLeading >> termParser maxPrec

end Term

end Parser
end Lean
