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

syntax (name := conv) "conv " (" at " ident)? (" in " term)? " => " convSeq : tactic

syntax (name := skip) "skip" : conv
syntax (name := done) "done" : conv
syntax (name := lhs) "lhs" : conv
syntax (name := rhs) "rhs" : conv
syntax (name := whnf) "whnf" : conv
syntax (name := congr) "congr" : conv
syntax (name := arg) "arg " num : conv
syntax (name := traceState) "traceState" : conv
syntax (name := funext) "funext" (colGt ident)* : conv
syntax (name := change) "change " term : conv
syntax (name := rewrite) "rewrite " rwRuleSeq : conv
syntax (name := erewrite) "erewrite " rwRuleSeq : conv
syntax (name := simp) "simp " ("(" &"config" " := " term ")")? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? : conv
syntax (name := nestedTactic) "tactic" " => " tacticSeq : conv
syntax (name := nestedConv) convSeqBracketed : conv
syntax (name := paren) "(" convSeq ")" : conv

/-- `· conv` focuses on the main conv goal and tries to solve it using `s` -/
macro dot:("·" <|> ".") s:convSeq : conv => `({%$dot ($s:convSeq) })
macro "rw " s:rwRuleSeq : conv => `(rewrite $s:rwRuleSeq)
macro "erw " s:rwRuleSeq : conv => `(erewrite $s:rwRuleSeq)
macro "args" : conv => `(congr)
macro "left" : conv => `(lhs)
macro "right" : conv => `(rhs)

end Lean.Parser.Tactic.Conv
