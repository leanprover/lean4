import Lean

/-! Linters that exercise error handling. `counter` counts commands and reports the count; `preThrower`
throws in `pre`; `postThrower` throws in `post`. Each failure should be logged (as an error), isolated
from the other linters, and non-fatal: a `pre` failure leaves an absent pre-state (so `post` still
runs), a `post` failure freezes the previous state. The still-advancing `counter` proves the isolation
and that threading survives. -/

namespace LinterTest.Errors
open Lean Elab Command

/-- Running command count. -/
structure Counter where
  count : Nat

initialize counterLinter : StatefulLinter Counter Nat ←
  registerStatefulLinter (Counter.mk 0)
    (pre := fun stx self _ =>
      pure <| if Parser.isTerminalCommand stx then none else some (self.count + 1))
    (post := fun _ self preState _ _ => do
      match preState with
      | some n => logInfo m!"count: {n}"; pure { count := n }
      | none   => pure self)

initialize preThrower : StatefulLinter Unit Unit ←
  registerStatefulLinter ()
    (pre := fun stx _ _ => do
      unless Parser.isTerminalCommand stx do throwError "pre boom"
      pure none)
    (post := fun _ self _ _ _ => pure self)

initialize postThrower : StatefulLinter Unit Unit ←
  registerStatefulLinter ()
    (post := fun stx self _ _ _ => do
      unless Parser.isTerminalCommand stx do throwError "post boom"
      pure self)
