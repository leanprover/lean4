import Lean

open Lean Elab Tactic

syntax "Foo" (ident <|> num) : tactic

elab_rules : tactic 
  | `(tactic| Foo $x:num) => 
    logInfo "num"

macro_rules 
  | `(tactic| Foo $x:ident) => `(tactic| trace "ident")

example : True := by 
  Foo x -- should not fail
  trivial 
