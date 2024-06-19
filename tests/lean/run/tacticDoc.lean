import Lean.Parser.Tactic.Doc
import Lean.Elab.Tactic.Doc
import Lean.Elab.Command


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
info: Available tags:
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
