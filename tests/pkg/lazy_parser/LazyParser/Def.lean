import Lean
import LazyParser.Counter

/-!
Declares parsers of various shapes for use from `LazyParser.Use`, which imports them lazily.
-/

open Lean Parser

/-- A term parser that increments `forceCount` when its value is computed. -/
@[term_parser] def countedTerm : Parser :=
  let n := unsafe unsafeBaseIO (forceCount.modifyGet fun n => (n + 1, n + 1))
  leadingNode `countedTerm maxPrec (symbol (if n > 0 then "counted_term" else "never"))

@[macro countedTerm] def expandCountedTerm : Macro := fun _ => `(0)

syntax:65 term:65 " +++ " term:66 : term
macro_rules | `($a +++ $b) => `($a + $b)

declare_syntax_cat lazyCat
syntax "lc_one" : lazyCat
syntax "[lazyCat|" lazyCat "]" : term
macro_rules | `([lazyCat| lc_one]) => `(1)

syntax lazyAtom := "la_two" <|> "la_three"
syntax "use_atom " lazyAtom : term
macro_rules
  | `(use_atom la_two) => `(2)
  | `(use_atom la_three) => `(3)

namespace N
scoped syntax "zork_term" : term
macro_rules | `(zork_term) => `(4)
end N

syntax (name := lazyTac) "lazy_tac" : tactic
macro_rules | `(tactic| lazy_tac) => `(tactic| trivial)
