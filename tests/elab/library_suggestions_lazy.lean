module

import Lean.LibrarySuggestions.Default
import all Lean.LibrarySuggestions.SymbolFrequency
import all Lean.LibrarySuggestions.SineQuaNon

/-!
Library suggestions build their imported indexes only when requested. Exporting a module must not
prepare or serialize these indexes, and local declarations must not enter the imported caches.
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

run_meta do
  let frequency ← symbolFrequencyMap
  assert! frequency.getD `Nat 0 > 0
  assert! frequency.getD `localPredicate 0 == 0
  assert! (← symbolFrequencyMapRef.get).isSome
  assert! (← sineQuaNonTriggersRef.get).isNone
  let theorems ← sineQuaNonTheorems `HAppend.hAppend
  assert! theorems.any fun (name, _) => name == `List.append_assoc
  assert! (← sineQuaNonTheorems `localPredicate).isEmpty
  assert! (← sineQuaNonTriggersRef.get).isSome
  assert! (← symbolFrequencyMap).toList == frequency.toList
  assert! (← sineQuaNonTheorems `HAppend.hAppend) == theorems
  let data ← mkModuleData (← getEnv)
  assert! !data.entries.any fun (name, _) => name == `symbolFrequency || name == `sineQueNon

example : localPredicate 42 := by
  run_tac do
    let suggestions ← currentFile (← Elab.Tactic.getMainGoal) {}
    assert! suggestions.any (·.name == `localTheorem)
  exact localTheorem
