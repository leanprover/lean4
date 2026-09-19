import Lean

open Lean

/-! Malformed syntax `match` with wrong pattern arity should error, not panic (#10171). -/

/--
error: unknown goal
---
error: too many patterns in 'match' (syntax)
-/
#guard_msgs in
def foo (stx : Syntax) : Unit :=
  match stx with
  | _, `(bar) => sorry

/--
error: unknown goal
---
error: not enough patterns in 'match' (syntax)
-/
#guard_msgs in
def bar (stx₁ stx₂ : Syntax) : Unit :=
  match stx₁, stx₂ with
  | _ => sorry
