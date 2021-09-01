/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Notation

namespace Lean.Parser.Tactic

declare_syntax_cat conv (behavior := both)

syntax convSeq1Indented := withPosition((colGe conv ";"?)+)
syntax convSeqBracketed := "{" (conv ";"?)+ "}"
syntax convSeq := convSeq1Indented <|> convSeqBracketed

syntax "skip " : conv
syntax "lhs"   : conv
syntax "rhs"   : conv
syntax "whnf"  : conv
syntax "congr" : conv
syntax "conv " (" at " ident)? (" in " term)? " => " convSeq : tactic

end Lean.Parser.Tactic
