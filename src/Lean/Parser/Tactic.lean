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

end Tactic
end Parser
end Lean
