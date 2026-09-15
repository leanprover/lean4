/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Meta.Basic
import Lean.LibrarySuggestions.Basic

/-!
# Symbol frequency

Symbol frequencies for library suggestions are computed on first use, without storing any data in
olean files. The first query may be expensive for large imported libraries.
-/

namespace Lean.LibrarySuggestions

/-- Process-local cache for the imported symbol frequencies. -/
builtin_initialize symbolFrequencyMapRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

/--
The symbol frequency map for imported constants. This is computed and cached on first use, assuming
the imported environment remains fixed for the lifetime of the process. Local declarations are not
included.
-/
public def symbolFrequencyMap : CoreM (NameMap Nat) := do
  match ← symbolFrequencyMapRef.get with
  | some map => return map
  | none =>
    let map ← Meta.MetaM.run' <| withoutExporting do
      let env ← getEnv
      env.constants.map₁.foldM (init := ∅) fun acc name ci => do
        if isDeniedPremise env name || !wasOriginallyTheorem env name then
          return acc
        ci.type.foldRelevantConstants (init := acc) fun n acc =>
          return acc.alter n fun count => some (count.getD 0 + 1)
    symbolFrequencyMapRef.set (some map)
    return map

/--
Return the number of times a `Name` appears
in the signatures of (non-internal) theorems in the imported environment,
skipping instance arguments and proofs.
-/
public def symbolFrequency (n : Name) : CoreM Nat :=
  return (← symbolFrequencyMap) |>.getD n 0
