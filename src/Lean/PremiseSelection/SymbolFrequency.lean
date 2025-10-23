/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.CoreM

/-!
# Symbol frequency

This module provides a persistent environment extension for computing the frequency of symbols in the environment.
-/

namespace Lean.PremiseSelection

/--
The state is just an array of array of maps.
We don't assemble these on import for efficiency reasons: most modules will not query this extension.

Instead, we use an `IO.Ref` below so that within each module we can assemble the global `NameMap Nat` once.

Since we never modify the extension state except on export, the `IO.Ref` does not need updating after first access.
-/
builtin_initialize symbolFrequencyExt : PersistentEnvExtension (NameMap Nat) Empty (Array (Array (NameMap Nat))) ←
  registerPersistentEnvExtension {
    name            := `symbolFrequency
    mkInitial       := pure ∅
    addImportedFn   := fun mapss _ => pure mapss
    addEntryFn      := nofun
    exportEntriesFnEx := fun env _ _ =>
      let r := env.constants.map₂.foldl (init := (∅ : NameMap Nat)) (fun acc n ci =>
        if n.isInternalDetail then
          acc
        else
          -- It would be nice if we could discard all proof sub-terms here,
          -- but there doesn't seem to be a good way to do that.
          ci.type.foldConsts (init := acc) fun n' acc => acc.alter n' fun i? => some (i?.getD 0 + 1))
      #[r]
    statsFn         := fun _ => "symbol frequency extension"
  }

builtin_initialize symbolFrequencyMapRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

open Lean Core

private local instance : Zero (NameMap Nat) := ⟨∅⟩
private local instance : Add (NameMap Nat) where
  add x y := y.foldl (init := x) fun x' n c => x'.insert n (x'.getD n 0 + c)

def symbolFrequencyMap : CoreM (NameMap Nat) := do
  match ← symbolFrequencyMapRef.get with
  | some map => return map
  | none =>
    let mapss := symbolFrequencyExt.getState (← getEnv)
    let map := mapss.foldl (init := 0) fun acc maps => maps.foldl (init := acc) fun acc map => acc + map
    symbolFrequencyMapRef.set (some map)
    return map

/-- Return the number of times a `Name` appears in the signatures of (non-internal) declarations in the environment. -/
public def symbolFrequency (n : Name) : CoreM Nat :=
  return (← symbolFrequencyMap) |>.getD n 0
