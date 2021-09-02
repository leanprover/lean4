/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Notation

namespace Lean.Parser.Tactic.Conv

declare_syntax_cat conv (behavior := both)

syntax convSeq1Indented := withPosition((group(colGe conv ";"?))+)
syntax convSeqBracketed := "{" (group(conv ";"?))+ "}"
syntax convSeq := convSeq1Indented <|> convSeqBracketed

syntax (name := skip) "skip " : conv
syntax (name := lhs) "lhs" : conv
syntax (name := rhs) "rhs" : conv
syntax (name := whnf) "whnf" : conv
syntax (name := congr) "congr" : conv
syntax (name := nestedConv) convSeqBracketed : conv
syntax (name := paren) "(" convSeq ")" : conv

/-- `· conv` focuses on the main conv goal and tries to solve it using `s` -/
macro dot:("·" <|> ".") s:convSeq : conv => `({%$dot ($s:convSeq) })

syntax (name := conv) "conv " (" at " ident)? (" in " term)? " => " convSeq : tactic

end Lean.Parser.Tactic.Conv
