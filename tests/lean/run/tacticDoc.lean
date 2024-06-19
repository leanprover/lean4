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

@[tactic_alias my_trivial]
syntax (name := very_trivial) "very_trivial" : tactic

/-- It tries Lean's `trivial` -/
tactic_extension my_trivial

macro_rules
  | `(tactic|my_trivial) => `(tactic|trivial)

attribute [tactic_tag finishing] Lean.Parser.Tactic.omega

attribute [tactic_tag ctrl] Lean.Parser.Tactic.«tactic_<;>_»

/-- error: unknown tag 'bogus' (expected one of 'ctrl', 'extensible', 'finishing') -/
#guard_msgs in
attribute [tactic_tag bogus] my_trivial

/--
info: Available tags: ⏎
  • 'ctrl' — "control flow"
    Tactics that sequence or arrange other tactics ⏎
    '<;>'
  • 'extensible'
    Tactics that are intended to be extensible ⏎
    'my_trivial'
  • 'finishing'
    Finishing tactics that are intended to completely close a goal ⏎
    'omega', 'my_trivial'
-/
#guard_msgs in
#print tactic tags
