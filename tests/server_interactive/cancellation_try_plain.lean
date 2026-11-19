import Lean.Server.Test.Cancel
import Lean.Elab.Tactic.Try
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Lean.Server.Test.Cancel

/-!
Test cancellation propagation through plain `try?` (no `=>`, no
`wrapAsyncAsSnapshot` wrapping). Plain `try?` calls
`mkTryEvalSuggestStx`, which calls `expandUserTactic` for each
`[try_suggestion]` candidate. `expandUserTactic` runs the candidate via
`Tactic.run + evalTactic` on the *main* elaboration thread. Cancellation
must reach the candidate's body promptly via `Core.checkInterrupted`
embedded in `evalTactic` and inside the candidate.

We register a `[try_suggestion]` whose tactic is `wait_for_cancel_once_async`.
The first invocation (in the outer theorem body) spawns a snapshot task
that polls the cancel token; the second invocation (inside
`expandUserTactic`) waits on the first invocation's promise. On
re-elaboration the snapshot task observes its cancel token, resolves the
shared promise, and the inner `IO.wait` returns. After re-elaboration the
chain construction continues, the user attempt-all is built and run, and
the further nested invocations wait on the already-resolved promise. If
cancellation propagation is broken at any step, the test runner times out.
-/

namespace TestTryPlain

opaque UnsolvableProp : Prop

@[try_suggestion]
def waitSuggestion (_goal : MVarId) (_info : Try.Info) :
    MetaM (Array (TSyntax `tactic)) := do
  let stx ← `(tactic| wait_for_cancel_once_async)
  return #[stx]

end TestTryPlain

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : TestTryPlain.UnsolvableProp := by
  wait_for_cancel_once_async
  try?
