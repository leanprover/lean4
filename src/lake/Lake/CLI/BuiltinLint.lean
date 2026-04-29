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
  /-- Which set of linters to run (set by `--clippy` / `--lint-all`; default if neither). -/
  scope : Linter.EnvLinter.LintScope := .default
  /-- Run only the specified linters. -/
  only : Array Name := #[]
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]

public def leanOptOverrides (args : Args) : LeanOptions :=
  let enableAll : Array LeanOption :=
    #[⟨`linter.clippy, .ofBool true⟩, ⟨`linter.all, .ofBool true⟩]
  if !args.only.isEmpty then
    LeanOptions.ofArray enableAll
  else
    match args.scope with
    | .default => {}
    | .clippy  => LeanOptions.ofArray #[⟨`linter.clippy, .ofBool true⟩]
    | .all     => LeanOptions.ofArray enableAll

private def collectTextLints
    (env : Environment) (args : Args) (pkgRoot : Name) : Array Linter.LintEntry :=
  let matchOnly (linter : Name) : Bool :=
    args.only.isEmpty || args.only.any (fun n => n.isSuffixOf linter)
  let matchScope (linter : Name) : Bool :=
    if !args.only.isEmpty then true
    else match args.scope with
      | .default => linter != `linter.clippy
      | .clippy  => linter == `linter.clippy
      | .all     => true
  Linter.getAllLints env |>.foldl (init := #[]) fun acc (mod, entries) =>
    if pkgRoot.isPrefixOf mod then
      entries.foldl (init := acc) fun acc e =>
        if matchOnly e.linter && matchScope e.linter then acc.push e else acc
    else
      acc

public def run (args : Args) : IO UInt32 := do
  let mods := args.mods
  if mods.isEmpty then
    IO.eprintln "lake lint: no modules specified for builtin linting"
    return 1

  let runOnly := if args.only.isEmpty then none else some args.only.toList
  let scope := args.scope
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  let mut anyFailed := false
  for mod in mods do
    unsafe Lean.enableInitializersExecution
    let env ← importModules #[{ module := mod }, envLinterModule] {} (trustLevel := 1024) (loadExts := true)

    let textEntries := collectTextLints env args mod.getRoot
    let textFailed := !textEntries.isEmpty
    if textFailed then
      IO.println s!"-- Text linter diagnostics in {mod}:"
      for e in textEntries do
        IO.print e.message.toString

    let (declFailed, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
      let decls ← Linter.EnvLinter.getDeclsInPackage mod.getRoot
      let linters ← Linter.EnvLinter.getChecks (scope := scope) (runOnly := runOnly)
      if linters.isEmpty then
        IO.println s!"-- No environment linters registered for {mod}."
        return false
      let results ← Linter.EnvLinter.lintCore decls linters
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ←
          Linter.EnvLinter.formatLinterResults results decls
            (groupByFilename := true) (useErrorFormat := true)
            s!"in {mod}" (scope := if args.only.isEmpty then scope else .all) .medium linters.size
        IO.print (← fmtResults.toString)
      else unless textFailed do
        IO.println s!"-- Linting passed for {mod}."
      return failed

    if textFailed || declFailed then
      anyFailed := true

  return if anyFailed then 1 else 0

end Lake.BuiltinLint
