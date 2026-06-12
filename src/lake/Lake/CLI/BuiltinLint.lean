/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.EnvLinter
public import Lean.Linter.PersistentLintLog
import Lean.CoreM
import Lake.Config.Workspace

open Lean Lean.Core Meta

namespace Lake.BuiltinLint

/-- Arguments for builtin linting via `lake lint --builtin-lint`. -/
public structure Args where
  /-- Explicit linter-option overrides, applied to the build of each module.

  Each entry sets a `Lean.Option Bool` to the given value. Later entries override earlier
  ones at the same name. Populated from `--linters=linter.X,-linter.Y,...` on the CLI. -/
  linterOverrides : Array (Name × Bool) := #[]
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]
  /-- Whether to only run the user provided linters -/
  lintOnly : Bool := false

/--
Turns the `lake lint` extra arguments into an array of `Lean.Option`, that needs to be enabled
for the rebuild of the package, in order to turn on the appropriate linters.
-/
public def leanOptOverrides (args : Args) : LeanOptions :=
  let merged : NameMap Bool := args.linterOverrides.foldl (init := {}) fun m (n, b) => m.insert n b
  LeanOptions.ofArray <| merged.toArray.map fun (n, b) =>
    ⟨`weak ++ n, .ofBool b⟩

private def collectTextLints
    (env : Environment) (pkgRoot : Name) :
    Array (Name × Array Linter.LintEntry) :=
  Linter.getAllLints env |>.foldl (init := #[]) fun acc (mod, entries) =>
    if pkgRoot.isPrefixOf mod && !entries.isEmpty then acc.push (mod, entries) else acc

@[noinline] private def getIsModule (modData : Lean.ModuleData) : BaseIO Bool :=
  return modData.isModule

public def run (args : Args) : IO UInt32 := do
  let mods := args.mods
  if mods.isEmpty then
    IO.eprintln "lake lint: no modules specified for builtin linting"
    return 1
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  let mut anyFailed := false
  for mod in mods do
    unsafe Lean.enableInitializersExecution
    -- Peek at the .olean header to learn whether `mod` participates in the module system.
    -- If so, import at the public (`exported`) level, mirroring `processHeaderCore`.
    let modFile ← findOLean mod
    let (modData, region) ← readModuleData modFile
    let isModule ← getIsModule modData
    let level := if isModule then OLeanLevel.exported else OLeanLevel.private
    unsafe region.free
    let env ← importModules #[{ module := mod }, envLinterModule] {}
      (trustLevel := 1024) (loadExts := true) (level := level)
    -- We create `LinterOptions` out of the passed overrides
    let linterOpts : Lean.Linter.LinterOptions := {
      toOptions := args.linterOverrides.foldl (init := {}) fun o (n, b) => o.setBool n b
      linterSets := (Lean.Linter.linterSetsExt.getState env).merged
    }

    let textGroups := collectTextLints env mod.getRoot
    let textGroups :=
      if args.lintOnly then
        textGroups.filterMap fun (m, entries) =>
          let entries := entries.filter fun e =>
            Lean.Linter.isLinterEnabledByOptions e.linter linterOpts
          if entries.isEmpty then none else some (m, entries)
      else textGroups
    let textFailed := !textGroups.isEmpty
    for (m, entries) in textGroups do
      IO.println s!"-- Text linter diagnostics in {m}:"
      for e in entries do
        IO.print e.message.toString

    let (declFailed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
      let decls ← Linter.EnvLinter.getDeclsInPackage mod.getRoot
      let linters ← Linter.EnvLinter.getEnvLinters (if args.lintOnly then some linterOpts else none)
      if linters.isEmpty then
        IO.println s!"-- No environment linters were run for {mod}."
        return false
      let results ← Linter.EnvLinter.lintCore decls linters
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          Linter.EnvLinter.formatLinterResults results decls
            (groupByFilename := true) (useErrorFormat := true)
            s!"in {mod}" .medium linters.size
        IO.print (← fmtResults.toString)
      else unless textFailed do
        IO.println s!"-- Linting passed for {mod}."
      return failed

    if textFailed || declFailed then
      anyFailed := true

  return if anyFailed then 1 else 0

end Lake.BuiltinLint
