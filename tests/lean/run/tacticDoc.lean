import Lean.Parser.Tactic.Doc
import Lean.Elab.Tactic.Doc
import Lean.Elab.Command

open Lean Elab Command in
open Lean.Parser.Tactic.Doc in
elab "#tactic_tags" : command => do
  let all :=
    tacticTagExt.toEnvExtension.getState (← getEnv)
      |>.importedEntries |>.push (tacticTagExt.getState (← getEnv))
  let mut mapping : NameMap NameSet := {}
  for arr in all do
    for (tac, tag) in arr do
      mapping := mapping.insert tag (mapping.findD tag {} |>.insert tac)
  let mut str := ""
  for (tag, tacs) in mapping do
    str := str ++ s!"{tag}:\n   "
    for t in tacs do
      str := str ++ " " ++ t.toString
    str := str ++ "\n"
  logInfo str


/-- Finishing tactics that are intended to completely close a goal -/
register_tactic_tag finishing "finishing"

/-- Tactics that are intended to be extensible -/
register_tactic_tag extensible "extensible"

/-- Another `trivial` tactic -/
@[tactic_tag finishing extensible]
syntax (name := my_trivial) "my_trivial" : tactic

@[tactic_alias my_trivial]
syntax (name := very_trivial) "very_trivial" : tactic

/-- It tries Lean's `trivial` -/
tactic_extension my_trivial
macro_rules
  | `(tactic|my_trivial) => `(tactic|trivial)

/--
info: finishing:
    my_trivial
extensible:
    my_trivial
-/
#guard_msgs in
#tactic_tags
