/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.NotationExtra

namespace Lean.Parser.Tactic.Conv

declare_syntax_cat conv (behavior := both)

syntax convSeq1Indented := withPosition((colGe conv ";"?)+)
syntax convSeqBracketed := "{" (conv ";"?)+ "}"
-- Order is important: a missing `conv` proof should not be parsed as `{ <missing> }`,
-- automatically closing goals
syntax convSeq := convSeqBracketed <|> convSeq1Indented

syntax (name := conv) "conv " (" at " ident)? (" in " term)? " => " convSeq : tactic

syntax (name := lhs) "lhs" : conv
syntax (name := rhs) "rhs" : conv
syntax (name := whnf) "whnf" : conv
/-- Expand let-declarations and let-variables. -/
syntax (name := zeta) "zeta" : conv
/-- Put term in normal form, this tactic is ment for debugging purposes only -/
syntax (name := reduce) "reduce" : conv
syntax (name := congr) "congr" : conv
syntax (name := arg) "arg " "@"? num : conv
syntax (name := ext) "ext " (colGt ident)* : conv
syntax (name := change) "change " term : conv
syntax (name := delta) "delta " ident : conv
syntax (name := unfold) "unfold " ident : conv
syntax (name := pattern) "pattern " term : conv
syntax (name := rewrite) "rewrite " (config)? rwRuleSeq : conv
syntax (name := simp) "simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? : conv
syntax (name := simpMatch) "simp_match " : conv

/-- Execute the given tactic block without converting `conv` goal into a regular goal -/
syntax (name := nestedTacticCore) "tactic'" " => " tacticSeq : conv
/-- Focus, convert the `conv` goal `⊢ lhs` into a regular goal `⊢ lhs = rhs`, and then execute the given tactic block. -/
syntax (name := nestedTactic) "tactic" " => " tacticSeq : conv
syntax (name := nestedConv) convSeqBracketed : conv
syntax (name := paren) "(" convSeq ")" : conv
syntax (name := convConvSeq) "conv " " => " convSeq : conv

/-- `· conv` focuses on the main conv goal and tries to solve it using `s` -/
macro dot:("·" <|> ".") s:convSeq : conv => `({%$dot ($s) })
macro "rw " c:(config)? s:rwRuleSeq : conv => `(rewrite $[$c]? $s)
macro "erw " s:rwRuleSeq : conv => `(rw (config := { transparency := Meta.TransparencyMode.default }) $s)

macro "args" : conv => `(congr)
macro "left" : conv => `(lhs)
macro "right" : conv => `(rhs)
macro "intro " xs:(colGt ident)* : conv => `(conv| ext $xs*)

syntax enterArg := ident <|> ("@"? num)
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))

macro "skip" : conv => `(tactic => rfl)
macro "done" : conv => `(tactic' => done)
macro "trace_state" : conv => `(tactic' => trace_state)
macro "apply " e:term : conv => `(tactic => apply $e)

/-- `first | conv | ...` runs each `conv` until one succeeds, or else fails. -/
syntax (name := first) "first " withPosition((colGe "|" convSeq)+) : conv

syntax "repeat " convSeq : conv
macro_rules
  | `(conv| repeat $seq) => `(conv| first | ($seq); repeat $seq | skip)

end Lean.Parser.Tactic.Conv
