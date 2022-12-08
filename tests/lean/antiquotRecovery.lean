syntax "foo " (" bar " ident)? : tactic

macro_rules
  -- should not complain about `$id` not being a valid command and create a snapshot for it
  | `(tactic| foo $[bar $id]) => sorry
