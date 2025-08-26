/-!
Test the commands and attributes for interacting with tactic documentation.

Note that when the standard library starts shipping with actual tags, then this test will need to be
adjusted or rewritten, as it depends on the complete set of tags that are transitively accessible.
We don't expect to modify the default tactics often, and it should be a matter of accepting changes
from #guard_msgs.
-/

set_option guard_msgs.diff true

/-- Finishing tactics that are intended to completely close a goal -/
register_tactic_tag finishing "finishing"

/-- Tactics that are intended to be extensible -/
register_tactic_tag extensible "extensible"

/-- Tactics that sequence or arrange other tactics -/
register_tactic_tag ctrl "control flow"

/-- Another `trivial` tactic -/
@[tactic_tag finishing extensible]
syntax (name := my_trivial) "my_trivial" : tactic

@[tactic_alt my_trivial]
syntax (name := very_trivial) "very_trivial" : tactic

/-- It tries Lean's `trivial` -/
tactic_extension my_trivial

macro_rules
  | `(tactic|my_trivial) => `(tactic|trivial)

attribute [tactic_tag finishing] Lean.Parser.Tactic.omega

attribute [tactic_tag ctrl] Lean.Parser.Tactic.«tactic_<;>_»

/-!
# Error Handling

Test error handling. Non-tactics are not eligible to be the target of alternatives, to be
alternatives themselves, or to receive tags or doc extensions.
-/

/-! These tests check that non-tactics can't be alternative forms of tactics -/

/-- error: `nonTacticTm` is not a tactic -/
#guard_msgs in
@[tactic_alt my_trivial]
syntax (name := nonTacticTm) "nonTactic" : term

syntax (name := nonTacticTm') "nonTactic'" : term

/-- error: `nonTacticTm'` is not a tactic -/
#guard_msgs in
attribute [tactic_alt my_trivial] nonTacticTm'

/-! These tests check that non-tactics can't have tactic alternatives -/

/-- error: `nonTacticTm` is not a tactic -/
#guard_msgs in
@[tactic_alt nonTacticTm]
syntax (name := itsATactic) "yepATactic" : tactic

syntax (name := itsATactic') "yepATactic'" : tactic

/-- error: `nonTacticTm` is not a tactic -/
#guard_msgs in
attribute [tactic_alt nonTacticTm] itsATactic'


/-! These tests check that non-tactics can't receive tags -/

/-- error: `tm` is not a tactic -/
#guard_msgs in
@[tactic_tag finishing]
syntax (name := tm) "someTerm" : term


/-- error: `tm` is not a tactic -/
#guard_msgs in
attribute [tactic_tag ctrl] tm

/-! These tests check that only known tags may be applied -/

/-- error: Unknown tag `bogus` (expected one of `ctrl`, `extensible`, `finishing`) -/
#guard_msgs in
attribute [tactic_tag bogus] my_trivial

/-- error: Unknown tag `bogus` (expected one of `ctrl`, `extensible`, `finishing`) -/
#guard_msgs in
@[tactic_tag bogus]
syntax "someTactic" : tactic

/-! Check that only canonical tactics may receive doc extensions -/

/-- error: `nonTacticTm'` is not a tactic -/
#guard_msgs in
/-- Some docs that don't belong here -/
tactic_extension nonTacticTm'

/-- error: `very_trivial` is an alternative form of `my_trivial` -/
#guard_msgs in
/-- Some docs that don't belong here -/
tactic_extension very_trivial

/-! Check that warnings are issued if alternatives have their own docstrings -/

/-- warning: Docstring for `tacticAnother` will be ignored because it is an alternative -/
#guard_msgs in
/-- Docs -/
@[tactic_alt my_trivial]
syntax "another" : tactic

/-- Docs -/
syntax (name := yetAnother) "yetAnother" : tactic

/-- warning: Docstring for `yetAnother` will be ignored because it is an alternative -/
#guard_msgs in
attribute [tactic_alt my_trivial] «yetAnother»

/-! # Querying Tactic Docs -/
/--
info: Available tags: ⏎
  • `ctrl` — "control flow"
    Tactics that sequence or arrange other tactics ⏎
    '<;>'
  • `extensible`
    Tactics that are intended to be extensible ⏎
    'my_trivial'
  • `finishing`
    Finishing tactics that are intended to completely close a goal ⏎
    'omega', 'my_trivial', 'someTerm'
-/
#guard_msgs in
#print tactic tags
