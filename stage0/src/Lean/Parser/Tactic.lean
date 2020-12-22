/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Term

namespace Lean
namespace Parser
namespace Tactic

builtin_initialize
  registerParserAlias! "tacticSeq"    tacticSeq

@[builtinTacticParser] def «unknown»    := parser! withPosition (ident >> errorAtSavedPos "unknown tactic" true)
@[builtinTacticParser] def nestedTactic := tacticSeqBracketed

def matchRhs      := Term.hole <|> Term.syntheticHole <|> tacticSeq
def matchAltsTemp := Term.matchAlts (rhsParser := matchRhs)

@[builtinTacticParser low] def «matchTemp» := parser!:leadPrec "match " >> sepBy1 Term.matchDiscr ", " >> Term.optType >> " with " >> matchAltsTemp

end Tactic
end Parser
end Lean
