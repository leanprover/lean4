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
  register_parser_alias tacticSeq

@[builtinTacticParser] def «unknown»    := leading_parser withPosition (ident >> errorAtSavedPos "unknown tactic" true)
@[builtinTacticParser] def nestedTactic := tacticSeqBracketed

def matchRhs  := Term.hole <|> Term.syntheticHole <|> tacticSeq
def matchAlts := Term.matchAlts (rhsParser := matchRhs)
@[builtinTacticParser] def «match» := leading_parser:leadPrec "match " >> optional Term.generalizingParam >> optional Term.motive >> sepBy1 Term.matchDiscr ", " >> " with " >> ppDedent matchAlts
@[builtinTacticParser] def introMatch := leading_parser nonReservedSymbol "intro " >> matchAlts

@[builtinTacticParser] def decide := leading_parser nonReservedSymbol "decide"
@[builtinTacticParser] def nativeDecide := leading_parser nonReservedSymbol "native_decide"

end Tactic
end Parser
end Lean
