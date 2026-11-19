import Lean

/-! `emitter` counts commands: its `pre` produces a `Payload` handoff (declining on terminal commands),
its `post` folds that into a persistent `Counter`. `readerA`/`readerB`/`readerC` have no `pre` pass and
no state others read (handles discarded); their `post` reads `emitter`'s pre-phase `Payload` through
its handle — exercising several post phases consuming one pre phase, handle-based cross-linter reads,
`τ ≠ σ`, declining, and the default `pre`. -/

namespace LinterTest.Readers
open Lean Elab Command

/-- Persistent (`σ`) state of `emitter`: the running command count. -/
structure Counter where
  count : Nat

/-- Pre-phase handoff (`τ`) of `emitter`: the count computed for the current command. -/
structure Payload where
  current : Nat

/-- Registers a post-only linter that reports the count `emitter` staged this command, reading it
through `emitter`'s handle. Its own handoff type is irrelevant, so `τ := Unit` and the handle is
discarded (nobody reads this linter). -/
def registerReader (emitter : StatefulLinter Counter Payload) (label : String) :
    IO Unit := do
  let _ ← registerStatefulLinter (τ := Unit) (Counter.mk 0)
    (post := fun _ self _ _ readPre => do
      if let some p := readPre emitter then
        logInfo m!"{label} sees count {p.current}"
      pure self)

initialize emitter : StatefulLinter Counter Payload ←
  registerStatefulLinter (Counter.mk 0)
    (pre := fun stx self _ =>
      pure <| if Parser.isTerminalCommand stx then none else some { current := self.count + 1 })
    (post := fun _ self preState _ _ =>
      pure { count := (preState.map Payload.current).getD self.count })

initialize
  registerReader emitter "reader A"
  registerReader emitter "reader B"
  registerReader emitter "reader C"
