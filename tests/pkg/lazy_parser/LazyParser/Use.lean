import LazyParser.Def

/-!
Tests that imported parsers are evaluated only on first use, at most once, and otherwise behave as
before: trailing parsers, parsers in a user category, parsers referring to other parser decls,
scoped parsers, and tactic parsers as seen by `firstTacticTokens`.
-/

open Lean Elab Command

/-- info: 0 -/
#guard_msgs in
#eval forceCount.get

example : counted_term = 0 := rfl
example : counted_term = 0 := rfl

/-- info: 1 -/
#guard_msgs in
#eval forceCount.get

example : (1 +++ 2) = 3 := rfl
example : [lazyCat| lc_one] = 1 := rfl
example : use_atom la_three = 3 := rfl

/-- error: Unknown identifier `zork_term` -/
#guard_msgs in
example := zork_term

open N in
example : zork_term = 4 := rfl

example : True := by lazy_tac

/-- info: some "lazy_tac" -/
#guard_msgs in
#eval show CommandElabM _ from return (← Lean.Elab.Tactic.Doc.firstTacticTokens).find? `lazyTac
