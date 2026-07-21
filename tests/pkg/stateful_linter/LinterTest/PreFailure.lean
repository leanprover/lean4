import Lean

/-! Verifies the pre-failure → `none` handoff end-to-end. `thrower`'s `pre` throws, so its slot holds
an erased `none`; `producer`'s `pre` succeeds with a value; `observer`'s `post` reads both through
their handles and sees `none` for the thrower vs `some` for the producer — confirming a thrown `pre`
is read as an absent handoff (like a decline), not as a threaded previous state. -/

namespace LinterTest.PreFailure
open Lean Elab Command

initialize thrower : StatefulLinter Unit Nat ←
  registerStatefulLinter ()
    (pre := fun stx _ _ => do
      unless Parser.isTerminalCommand stx do throwError "thrower boom"
      pure none)
    (post := fun _ self _ _ _ => pure self)

initialize producer : StatefulLinter Unit Nat ←
  registerStatefulLinter ()
    (pre := fun stx _ _ =>
      pure <| if Parser.isTerminalCommand stx then none else some 42)
    (post := fun _ self _ _ _ => pure self)

initialize observer : StatefulLinter Unit Unit ←
  registerStatefulLinter ()
    (post := fun stx self _ _ readPre => do
      unless Parser.isTerminalCommand stx do
        logInfo m!"thrower: {readPre thrower}, producer: {readPre producer}"
      pure self)
