import Lean

/-! A counting linter used to check that per-command state threads correctly across `Elab.async` mode
changes within one file. Its `post` sleeps briefly: on an async→sync transition the sync command blocks
in `runStatefulLintersAsync` until the previous (async) command's linter task has resolved the state it
threads forward, so the sleep makes that blocking real (raise it to observe by hand). -/

namespace LinterTest.ModeSwitch
open Lean Elab Command

/-- Running command count. -/
structure Counter where
  count : Nat

initialize counterLinter : StatefulLinter Counter Nat ←
  registerStatefulLinter (Counter.mk 0)
    (run := fun stx prev => do
      if Parser.isTerminalCommand stx then
        return { final := prev }
      else
        let final := prev.count + 1
        -- brief sleep so an async→sync transition actually blocks the sync command here
        IO.sleep 20
        logInfo m!"count: {final}"
        return ⟨{ count := final }, final⟩)
