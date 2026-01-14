/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.CoreM
public import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.FunInfo
import Lean.AddDecl
import Lean.LibrarySuggestions.Basic

/-!
# Symbol frequency

This module provides a persistent environment extension for computing the frequency of symbols in the environment.
-/

namespace Lean.LibrarySuggestions

/--
Collect the frequencies for constants occurring in declarations defined in the current module,
skipping instance arguments and proofs.
-/
public def localSymbolFrequencyMap : MetaM (NameMap Nat) := do
  let env := (← getEnv)
  env.constants.map₂.foldlM (init := ∅) (fun acc m ci => do
    if isDeniedPremise env m || !wasOriginallyTheorem env m then
      pure acc
    else
      ci.type.foldRelevantConstants (init := acc) fun n' acc => return acc.alter n' fun i? => some (i?.getD 0 + 1))

/--
A global `IO.Ref` containing the local symbol frequency map. This is initialized on first use.
-/
builtin_initialize localSymbolFrequencyMapRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

/--
A cached version of the local symbol frequency map.

Note that the local symbol frequency map changes during elaboration of a file,
so if this is called at different times it may give the wrong result.
The intended use case is that it is only called by environment extension export functions,
i.e. after all declarations have been elaborated.
-/
def cachedLocalSymbolFrequencyMap : MetaM (NameMap Nat) := do
  match ← localSymbolFrequencyMapRef.get with
  | some map => return map
  | none =>
    let map ← localSymbolFrequencyMap
    localSymbolFrequencyMapRef.set (some map)
    return map

/--
Return the number of times a `Name` appears
in the signatures of (non-internal) theorems in the current module,
skipping instance arguments and proofs.

Note that this is cached, and so returns the frequency within theorems that had been elaborated
when the function is first called (with any argument).
-/
public def localSymbolFrequency (n : Name) : MetaM Nat := do
  return (← cachedLocalSymbolFrequencyMap) |>.getD n 0

/--
Helper function for running `MetaM` code during module export, when there is nothing but an `Environment` available.
Panics on errors.
-/
unsafe def _root_.Lean.Environment.unsafeRunMetaM [Inhabited α] (env : Environment) (x : MetaM α) : α :=
   match unsafeEIO ((((withoutExporting x).run' {} {}).run' { fileName := "symbolFrequency", fileMap := default } { env })) with
   | Except.ok a => a
   | Except.error ex => panic! match unsafeIO ex.toMessageData.toString with
     | Except.ok s => s
     | Except.error ex => ex.toString

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
    exportEntriesFnEx := fun env _ _ => unsafe env.unsafeRunMetaM do return #[← cachedLocalSymbolFrequencyMap]
    statsFn         := fun _ => "symbol frequency extension"
  }

/-- A global `IO.Ref` containing the symbol frequency map. This is initialized on first use. -/
builtin_initialize symbolFrequencyMapRef : IO.Ref (Option (NameMap Nat)) ← IO.mkRef none

private local instance : Zero (NameMap Nat) := ⟨∅⟩
private local instance : Add (NameMap Nat) where
  add x y := y.foldl (init := x) fun x' n c => x'.insert n (x'.getD n 0 + c)

/-- The symbol frequency map for imported constants. This is initialized on first use. -/
public def symbolFrequencyMap : CoreM (NameMap Nat) := do
  match ← symbolFrequencyMapRef.get with
  | some map => return map
  | none =>
    let mapss := symbolFrequencyExt.getState (← getEnv)
    let map := mapss.foldl (init := 0) fun acc maps => maps.foldl (init := acc) fun acc map => acc + map
    symbolFrequencyMapRef.set (some map)
    return map

/--
Return the number of times a `Name` appears
in the signatures of (non-internal) theorems in the imported environment,
skipping instance arguments and proofs.
-/
public def symbolFrequency (n : Name) : CoreM Nat :=
  return (← symbolFrequencyMap) |>.getD n 0
