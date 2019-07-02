/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.parser.parser

namespace Lean
namespace Parser

@[init mkBuiltinParsingTablesRef]
constant builtinLevelParsingTable : IO.Ref ParsingTables := default _

@[init] def regBuiltinLevelParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinLevelParser `Lean.Parser.builtinLevelParsingTable

def levelParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
{ fn := fun _ => runBuiltinParser "universe level" builtinLevelParsingTable rbp }

namespace Level

@[builtinLevelParser] def paren := parser! symbol "(" maxPrec >> levelParser >> ")"
@[builtinLevelParser] def max   := parser! "max" >> many1 (levelParser maxPrec)
@[builtinLevelParser] def imax  := parser! "imax" >> many1 (levelParser maxPrec)
@[builtinLevelParser] def hole  := parser! "_"
@[builtinLevelParser] def num   : Parser := numLit
@[builtinLevelParser] def ident : Parser := ident
@[builtinLevelParser] def addLit := tparser! pushLeading >> symbol "+" (65:Nat) >> numLit

end Level

end Parser
end Lean
