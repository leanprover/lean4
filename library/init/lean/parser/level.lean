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

def levelParser (rbp : Nat := 0) : Parser :=
{ fn := λ _, runBuiltinParser "universe level" builtinLevelParsingTable rbp }

end Parser
end Lean
