/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Ullrich
-/
import Lean.CoreM
import Lean.Replay
import LeanChecker.Replay
import Lake.Load.Manifest

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay' newConstants
  env'.freeRegions

unsafe def replayFromFresh (module : Name) : IO Unit := do
  Lean.withImportModules #[{module}] {} fun env => do
    discard <| (← mkEmptyEnvironment).replay' env.constants.map₁

/-- Read the name of the main module from the `lake-manifest`. -/
-- This has been copied from `ImportGraph.getCurrentModule` in the
-- https://github.com/leanprover-community/import-graph repository.
def getCurrentModule : IO Name := do
  match (← Lake.Manifest.load? ⟨"lake-manifest.json"⟩) with
  | none =>
    -- TODO: should this be caught?
    pure .anonymous
  | some manifest =>
    -- TODO: This assumes that the `package` and the default `lean_lib`
    -- have the same name up to capitalisation.
    -- Would be better to read the `.defaultTargets` from the
    -- `← getRootPackage` from `Lake`, but I can't make that work with the monads involved.
    return manifest.name.capitalize


/--
Run as e.g. `leanchecker` to check everything in the current project.
or e.g. `leanchecker Mathlib.Data.Nat` to check everything with module name
starting with `Mathlib.Data.Nat`.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `leanchecker --fresh Mathlib.Data.Nat.Prime.Basic`
to replay all the constants (both imported and defined in that file) into a fresh environment.
This can only be used on a single file.

This is not an external verifier, simply a tool to detect "environment hacking".
-/
unsafe def main (args : List String) : IO UInt32 := do
  -- Contributor's note: lean4lean is intended to have a CLI interface matching leanchecker,
  -- so if you want to make a change here please either make a sibling PR to
  -- https://github.com/digama0/lean4lean or ping @digama0 (Mario Carneiro) to go fix it.
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let verbose := "-v" ∈ flags || "--verbose" ∈ flags
  let fresh := "--fresh" ∈ flags
  let targets ← do
    match args with
    | [] => pure [← getCurrentModule]
    | args => args.mapM fun arg => do
      let mod := arg.toName
      if mod.isAnonymous then
        throw <| IO.userError s!"Could not resolve module: {arg}"
      else
        pure mod
  let mut targetModules := []
  let sp ← searchPathRef.get
  for target in targets do
    let mut found := false
    for path in (← SearchPath.findAllWithExt sp "olean") do
      if let some m := (← searchModuleNameOfFileName path sp) then
        if !fresh && target.isPrefixOf m || target == m then
          targetModules := targetModules.insert m
          found := true
    if not found then
      throw <| IO.userError s!"Could not find any oleans for: {target}"
  if fresh then
    if targetModules.length != 1 then
      throw <| IO.userError s!"--fresh flag is only valid when specifying a single module:\n\
        {targetModules}"
    for m in targetModules do
      if verbose then IO.println s!"replaying {m} with --fresh"
      replayFromFresh m
  else
    let mut tasks := #[]
    for m in targetModules do
      tasks := tasks.push (m, ← IO.asTask (replayFromImports m))
    for (m, t) in tasks do
      if verbose then IO.println s!"replaying {m}"
      if let .error e := t.get then
        IO.eprintln s!"leanchecker found a problem in {m}"
        throw e
  return 0
