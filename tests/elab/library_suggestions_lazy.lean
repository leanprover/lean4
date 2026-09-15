module

import Lean.LibrarySuggestions.Default
import all Lean.LibrarySuggestions.SymbolFrequency
import all Lean.LibrarySuggestions.SineQuaNon

/-!
Library suggestions build their imported indexes only when requested. Exporting a module must not
prepare or serialize these indexes, and local declarations must not enter the imported caches.
Cold initialization must leave the caller's heartbeat budget intact, including on errors and
cancellation.
-/

open Lean LibrarySuggestions SineQuaNon

run_meta do
  assert! (← symbolFrequencyMapRef.get).isNone
  assert! (← sineQuaNonTriggersRef.get).isNone
  let data ← mkModuleData (← getEnv)
  assert! !data.entries.any fun (name, _) => name == `symbolFrequency || name == `sineQueNon
  assert! (← symbolFrequencyMapRef.get).isNone
  assert! (← sineQuaNonTriggersRef.get).isNone

public def localPredicate (n : Nat) : Prop := n = 42
public theorem localTheorem : localPredicate 42 := by unfold localPredicate; rfl

set_option maxHeartbeats 10000 in
run_meta do
  IO.addHeartbeats 200000
  let before ← IO.getNumHeartbeats
  let frequency ← symbolFrequencyMap
  assert! frequency.getD `Nat 0 > 0
  assert! frequency.getD `localPredicate 0 == 0
  assert! (← symbolFrequencyMapRef.get).isSome
  assert! (← sineQuaNonTriggersRef.get).isNone
  let theorems ← sineQuaNonTheorems `HAppend.hAppend
  let after ← IO.getNumHeartbeats
  assert! before ≤ after
  assert! after - before < 100000
  Core.checkSystem "after cold library suggestion initialization"
  assert! theorems.any fun (name, _) => name == `List.append_assoc
  assert! (← sineQuaNonTheorems `localPredicate).isEmpty
  assert! (← sineQuaNonTriggersRef.get).isSome
  assert! (← symbolFrequencyMap).toList == frequency.toList
  assert! (← sineQuaNonTheorems `HAppend.hAppend) == theorems
  let data ← mkModuleData (← getEnv)
  assert! !data.entries.any fun (name, _) => name == `symbolFrequency || name == `sineQueNon

run_meta do
  for cancel in [false, true] do
    let tk ← IO.CancelToken.new
    let action : CoreM Unit := withUncountedHeartbeats do
      IO.addHeartbeats 1000000
      if cancel then
        tk.set
        Core.checkSystem "cancelled index preparation"
      else
        throwError "failed index preparation"
    let ctx ← readThe Core.Context
    let state ← getThe Core.State
    let before ← IO.getNumHeartbeats
    let result ← (action.run' { ctx with cancelTk? := some tk } state).toIO'
    let after ← IO.getNumHeartbeats
    assert! before ≤ after
    assert! after - before < 100000
    match result with
    | .error e => assert! e.isInterrupt == cancel
    | .ok _ => throwError "expected index preparation to fail"
  Core.checkSystem "after interrupted index preparation"

example : localPredicate 42 := by
  run_tac do
    let suggestions ← currentFile (← Elab.Tactic.getMainGoal) {}
    assert! suggestions.any (·.name == `localTheorem)
  exact localTheorem
