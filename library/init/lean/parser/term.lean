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
{ fn := λ _, runBuiltinParser "term" builtinTermParsingTable rbp }

namespace Term

@[builtinTermParser] def ident := parser! ident >> optional (".{" >> many1 levelParser >> "}")
@[builtinTermParser] def num : Parser := numLit
@[builtinTermParser] def str : Parser := strLit
@[builtinTermParser] def type := parser! symbol "Type" maxPrec
@[builtinTermParser] def sort := parser! symbol "Sort" maxPrec
@[builtinTermParser] def hole := parser! symbol "_" maxPrec

@[builtinTermParser] def app := tparser! pushLeading >> termParser maxPrec

end Term

end Parser
end Lean
