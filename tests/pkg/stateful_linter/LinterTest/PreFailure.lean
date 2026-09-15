import Lean

/-! Verifies the pre-failure → `none` handoff end-to-end. `thrower`'s `pre` throws, so its slot holds
an erased `none`; `producer`'s `pre` succeeds with a value; `observer`'s `post` reads both through
their handles and sees `none` for the thrower vs `some` for the producer — confirming a thrown `pre`
is read as an absent handoff (like a decline), not as a threaded previous state. -/

namespace LinterTest.PreFailure
open Lean Elab Command

initialize thrower : StatefulLinter Unit Nat ←
  registerStatefulLinter ()
    (run := fun stx prev => do
      unless Parser.isTerminalCommand stx do throwError "thrower boom"
      pure ⟨(), none⟩)

initialize producer : StatefulLinter Unit Nat ←
  registerStatefulLinter ()
    (run := fun stx prev => do
      if Parser.isTerminalCommand stx then return ⟨(), none⟩ else
        return ⟨(), some 42⟩)

initialize observer : SimpleStatefulLinter Unit ←
  registerSimpleStatefulLinter ()
    (run := fun stx prev => do
      unless Parser.isTerminalCommand stx do
        logInfo m!"thrower: {thrower.readIntermediate}, producer: {producer.readIntermediate}"
      pure prev)
