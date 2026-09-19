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
    (run := fun stx prev => do
      if Parser.isTerminalCommand stx then
        return ⟨prev, none⟩
      else
        let n := prev.count + 1
        logInfo m!"count: {n}"
        pure ⟨{ count := n }, n⟩)

initialize thrower : SimpleStatefulLinter Unit ←
  registerStatefulLinter ()
    (run := fun stx _ => do
      unless Parser.isTerminalCommand stx do throwError "boom"
      pure { final := () })
