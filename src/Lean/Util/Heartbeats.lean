/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Lean.CoreM

/-!
# Lean.Heartbeats

This provides some utilities is the first file in the Lean import hierarchy. It is responsible for setting
up basic definitions, most of which Lean already has "built in knowledge" about,
so it is important that they be set up in exactly this way. (For example, Lean will
use `PUnit` in the desugaring of `do` notation, or in the pattern match compiler.)

-/

namespace Lean

/--
Counts the number of heartbeats used during a monadic function.

Remember that user facing heartbeats (e.g. as used in `set_option maxHeartbeats`)
differ from the internally tracked heartbeats by a factor of 1000,
so you need to divide the results here by 1000 before comparing with user facing numbers.
-/
-- See also `Lean.withSeconds`
def withHeartbeats [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Nat) := do
  let start ← IO.getNumHeartbeats
  let r ← x
  let finish ← IO.getNumHeartbeats
  return (r, finish - start)

/-- Returns the current `maxHeartbeats`. -/
def getMaxHeartbeats : CoreM Nat := do pure <| (← read).maxHeartbeats

/-- Returns the current `initHeartbeats`. -/
def getInitHeartbeats : CoreM Nat := do pure <| (← read).initHeartbeats

/-- Returns the remaining heartbeats available in this computation. -/
def getRemainingHeartbeats : CoreM Nat := do
  pure <| (← getMaxHeartbeats) - ((← IO.getNumHeartbeats) - (← getInitHeartbeats))

/--
Returns the percentage of the max heartbeats allowed
that have been consumed so far in this computation.
-/
def heartbeatsPercent : CoreM Nat := do
  pure <| ((← IO.getNumHeartbeats) - (← getInitHeartbeats)) * 100 / (← getMaxHeartbeats)

/-- Log a message if it looks like we ran out of time. -/
def reportOutOfHeartbeats (tac : Name) (stx : Syntax) (threshold : Nat := 90) : CoreM Unit := do
  if (← heartbeatsPercent) ≥ threshold then
    logInfoAt stx s!"\
      `{tac}` stopped because it was running out of time.\n\
      You may get better results using `set_option maxHeartbeats 0`."

end Lean
