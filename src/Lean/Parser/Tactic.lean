/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Term
import Lean.Parser.Tactic.Doc

namespace Lean
namespace Parser
namespace Tactic

builtin_initialize
  register_parser_alias tacticSeq
  register_parser_alias tacticSeqIndentGt

/- This is a fallback tactic parser for any identifier which exists only
to improve syntax error messages.
```
example : True := by foo -- unknown tactic
```
-/
@[builtin_tactic_parser] def «unknown»    := leading_parser
  withPosition (ident >> errorAtSavedPos "unknown tactic" true)

@[builtin_tactic_parser] def nestedTactic := tacticSeqBracketed

def matchRhs  := Term.hole <|> Term.syntheticHole <|> tacticSeq
def matchAlts := Term.matchAlts (rhsParser := matchRhs)

/-- `match` performs case analysis on one or more expressions.
See [Induction and Recursion][tpil4].
The syntax for the `match` tactic is the same as term-mode `match`, except that
the match arms are tactics instead of expressions.
```
example (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | i+1 => simp
```

[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html
-/
@[builtin_tactic_parser] def «match» := leading_parser:leadPrec
  "match " >> optional Term.generalizingParam >>
  optional Term.motive >> sepBy1 Term.matchDiscr ", " >>
  " with " >> ppDedent matchAlts

/--
The tactic
```
intro
| pat1 => tac1
| pat2 => tac2
```
is the same as:
```
intro x
match x with
| pat1 => tac1
| pat2 => tac2
```
That is, `intro` can be followed by match arms and it introduces the values while
doing a pattern match. This is equivalent to `fun` with match arms in term mode.
-/
@[builtin_tactic_parser] def introMatch := leading_parser
  nonReservedSymbol "intro" >> matchAlts

builtin_initialize
  register_parser_alias "matchRhsTacticSeq" matchRhs

end Tactic
end Parser
end Lean
