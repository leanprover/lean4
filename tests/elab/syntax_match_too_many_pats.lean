import Lean

open Lean

/-! Malformed syntax `match` with more patterns than discriminants should error, not panic (#10171). -/

/--
error: unknown goal
---
error: too many patterns in 'match' (syntax)
-/
#guard_msgs in
def foo (stx : Syntax) : Unit :=
  match stx with
  | _, `(bar) => sorry
